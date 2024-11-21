// Copyright 2024 RisingWave Labs
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::collections::{BTreeSet, HashSet};
use std::fmt::Display;
use std::future::pending;
use std::iter::once;
use std::sync::Arc;
use std::time::Duration;

use anyhow::anyhow;
use await_tree::InstrumentAwait;
use futures::future::BoxFuture;
use futures::stream::{BoxStream, FuturesOrdered};
use futures::{FutureExt, StreamExt, TryFutureExt};
use itertools::Itertools;
use risingwave_common::error::tonic::extra::Score;
use risingwave_pb::stream_service::barrier_complete_response::PbLocalSstableInfo;
use risingwave_rpc_client::error::{ToTonicStatus, TonicStatusWrapper};
use thiserror_ext::AsReport;
use tokio::select;
use tokio::sync::mpsc::{unbounded_channel, UnboundedReceiver, UnboundedSender};
use tokio::sync::{mpsc, oneshot};
use tokio::task::JoinHandle;
use tonic::{Code, Status};

use self::managed_state::ManagedBarrierState;
use crate::error::{IntoUnexpectedExit, StreamError, StreamResult};
use crate::task::{
    ActorId, AtomicU64Ref, PartialGraphId, SharedContext, StreamEnvironment, UpDownActorIds,
};

mod managed_state;
mod progress;
#[cfg(test)]
mod tests;

pub use progress::CreateMviewProgressReporter;
use risingwave_common::util::epoch::EpochPair;
use risingwave_common::util::runtime::BackgroundShutdownRuntime;
use risingwave_hummock_sdk::table_stats::to_prost_table_stats_map;
use risingwave_hummock_sdk::{HummockEpoch, LocalSstableInfo, SyncResult};
use risingwave_pb::stream_service::streaming_control_stream_request::{
    InitRequest, InitialPartialGraph, Request,
};
use risingwave_pb::stream_service::streaming_control_stream_response::{
    InitResponse, ShutdownResponse,
};
use risingwave_pb::stream_service::{
    streaming_control_stream_response, BarrierCollectResponse, BarrierCompleteResponse,
    InjectBarrierRequest, StreamingControlStreamRequest, StreamingControlStreamResponse,
};

use crate::executor::exchange::permit::Receiver;
use crate::executor::monitor::StreamingMetrics;
use crate::executor::{Barrier, BarrierInner, StreamExecutorError};
use crate::task::barrier_manager::managed_state::{
    ManagedBarrierStateDebugInfo, PartialGraphManagedBarrierState,
};
use crate::task::barrier_manager::progress::BackfillState;

/// If enabled, all actors will be grouped in the same tracing span within one epoch.
/// Note that this option will significantly increase the overhead of tracing.
pub const ENABLE_BARRIER_AGGREGATION: bool = false;

/// Collect result of some barrier on current compute node. Will be reported to the meta service.
#[derive(Debug)]
pub struct BarrierCompleteResult {
    task_id: u64,
    /// The result returned from `sync` of `StateStore`.
    pub sync_result: SyncResult,
}

pub(super) struct ControlStreamHandle {
    #[expect(clippy::type_complexity)]
    pair: Option<(
        UnboundedSender<Result<StreamingControlStreamResponse, Status>>,
        BoxStream<'static, Result<StreamingControlStreamRequest, Status>>,
    )>,
}

impl ControlStreamHandle {
    fn empty() -> Self {
        Self { pair: None }
    }

    pub(super) fn new(
        sender: UnboundedSender<Result<StreamingControlStreamResponse, Status>>,
        request_stream: BoxStream<'static, Result<StreamingControlStreamRequest, Status>>,
    ) -> Self {
        Self {
            pair: Some((sender, request_stream)),
        }
    }

    pub(super) fn connected(&self) -> bool {
        self.pair.is_some()
    }

    fn reset_stream_with_err(&mut self, err: Status) {
        if let Some((sender, _)) = self.pair.take() {
            // Note: `TonicStatusWrapper` provides a better error report.
            let err = TonicStatusWrapper::new(err);
            warn!(error = %err.as_report(), "control stream reset with error");

            let err = err.into_inner();
            if sender.send(Err(err)).is_err() {
                warn!("failed to notify reset of control stream");
            }
        }
    }

    /// Send `Shutdown` message to the control stream and wait for the stream to be closed
    /// by the meta service.
    async fn shutdown_stream(&mut self) {
        if let Some((sender, _)) = self.pair.take() {
            if sender
                .send(Ok(StreamingControlStreamResponse {
                    response: Some(streaming_control_stream_response::Response::Shutdown(
                        ShutdownResponse::default(),
                    )),
                }))
                .is_err()
            {
                warn!("failed to notify shutdown of control stream");
            } else {
                tracing::info!("waiting for meta service to close control stream...");

                // Wait for the stream to be closed, to ensure that the `Shutdown` message has
                // been acknowledged by the meta service for more precise error report.
                //
                // This is because the meta service will reset the control stream manager and
                // drop the connection to us upon recovery. As a result, the receiver part of
                // this sender will also be dropped, causing the stream to close.
                sender.closed().await;
            }
        } else {
            debug!("control stream has been reset, ignore shutdown");
        }
    }

    fn send_response(&mut self, response: StreamingControlStreamResponse) {
        if let Some((sender, _)) = self.pair.as_ref() {
            if sender.send(Ok(response)).is_err() {
                self.pair = None;
                warn!("fail to send response. control stream reset");
            }
        } else {
            debug!(?response, "control stream has been reset. ignore response");
        }
    }

    async fn next_request(&mut self) -> StreamingControlStreamRequest {
        if let Some((_, stream)) = &mut self.pair {
            match stream.next().await {
                Some(Ok(request)) => {
                    return request;
                }
                Some(Err(e)) => self.reset_stream_with_err(
                    anyhow!(TonicStatusWrapper::new(e)) // wrap the status to provide better error report
                        .context("failed to get request")
                        .to_status_unnamed(Code::Internal),
                ),
                None => self.reset_stream_with_err(Status::internal("end of stream")),
            }
        }
        pending().await
    }
}

pub(super) enum LocalBarrierEvent {
    ReportActorCollected {
        actor_id: ActorId,
        epoch: EpochPair,
    },
    ReportCreateProgress {
        epoch: EpochPair,
        actor: ActorId,
        state: BackfillState,
    },
    RegisterBarrierSender {
        actor_id: ActorId,
        barrier_sender: mpsc::UnboundedSender<Barrier>,
    },
    #[cfg(test)]
    Flush(oneshot::Sender<()>),
}

#[derive(strum_macros::Display)]
pub(super) enum LocalActorOperation {
    NewControlStream {
        handle: ControlStreamHandle,
        init_request: InitRequest,
    },
    TakeReceiver {
        ids: UpDownActorIds,
        result_sender: oneshot::Sender<StreamResult<Receiver>>,
    },
    #[cfg(test)]
    GetCurrentSharedContext(oneshot::Sender<Arc<SharedContext>>),
    InspectState {
        result_sender: oneshot::Sender<String>,
    },
    Shutdown {
        result_sender: oneshot::Sender<()>,
    },
}

pub(crate) struct StreamActorManager {
    pub(super) env: StreamEnvironment,
    pub(super) streaming_metrics: Arc<StreamingMetrics>,

    /// Watermark epoch number.
    pub(super) watermark_epoch: AtomicU64Ref,

    /// Manages the await-trees of all actors.
    pub(super) await_tree_reg: Option<await_tree::Registry>,

    /// Runtime for the streaming actors.
    pub(super) runtime: BackgroundShutdownRuntime,
}

pub(super) struct LocalBarrierWorkerDebugInfo<'a> {
    running_actors: BTreeSet<ActorId>,
    managed_barrier_state: ManagedBarrierStateDebugInfo<'a>,
    has_control_stream_connected: bool,
}

impl Display for LocalBarrierWorkerDebugInfo<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "running_actors: ")?;
        for actor_id in &self.running_actors {
            write!(f, "{}, ", actor_id)?;
        }

        writeln!(
            f,
            "\nhas_control_stream_connected: {}",
            self.has_control_stream_connected
        )?;

        writeln!(f, "managed_barrier_state:\n{}", self.managed_barrier_state)?;
        Ok(())
    }
}

/// [`LocalBarrierWorker`] manages barrier control flow, used by local stream manager.
/// Specifically, [`LocalBarrierWorker`] serve barrier injection from meta server, send the
/// barriers to and collect them from all actors, and finally report the progress.
pub(super) struct LocalBarrierWorker {
    /// Current barrier collection state.
    pub(super) state: ManagedBarrierState,

    /// Futures will be finished in the order of epoch in ascending order.
    await_epoch_completed_futures: FuturesOrdered<AwaitEpochCompletedFuture>,

    control_stream_handle: ControlStreamHandle,

    pub(super) actor_manager: Arc<StreamActorManager>,

    pub(super) current_shared_context: Arc<SharedContext>,

    barrier_event_rx: UnboundedReceiver<LocalBarrierEvent>,

    actor_failure_rx: UnboundedReceiver<(ActorId, StreamError)>,
}

impl LocalBarrierWorker {
    pub(super) fn new(
        actor_manager: Arc<StreamActorManager>,
        initial_partial_graphs: Vec<InitialPartialGraph>,
    ) -> Self {
        let (event_tx, event_rx) = unbounded_channel();
        let (failure_tx, failure_rx) = unbounded_channel();
        let shared_context = Arc::new(SharedContext::new(
            &actor_manager.env,
            LocalBarrierManager {
                barrier_event_sender: event_tx,
                actor_failure_sender: failure_tx,
            },
        ));
        Self {
            state: ManagedBarrierState::new(
                actor_manager.clone(),
                shared_context.clone(),
                initial_partial_graphs,
            ),
            await_epoch_completed_futures: Default::default(),
            control_stream_handle: ControlStreamHandle::empty(),
            actor_manager,
            current_shared_context: shared_context,
            barrier_event_rx: event_rx,
            actor_failure_rx: failure_rx,
        }
    }

    fn to_debug_info(&self) -> LocalBarrierWorkerDebugInfo<'_> {
        LocalBarrierWorkerDebugInfo {
            running_actors: self.state.actor_states.keys().cloned().collect(),
            managed_barrier_state: self.state.to_debug_info(),
            has_control_stream_connected: self.control_stream_handle.connected(),
        }
    }

    async fn run(mut self, mut actor_op_rx: UnboundedReceiver<LocalActorOperation>) {
        loop {
            select! {
                biased;
                (partial_graph_id, barrier, create_mview_progress) = self.state.next_collected_epoch() => {
                    self.control_stream_handle.send_response(StreamingControlStreamResponse {
                        response: Some(
                            streaming_control_stream_response::Response::CollectBarrier(
                                BarrierCollectResponse {
                                    partial_graph_id: partial_graph_id.0,
                                    epoch: barrier.epoch.prev,
                                    create_mview_progress,
                                },
                            ),
                        ),
                    });
                }
                result = rw_futures_util::pending_on_none(self.await_epoch_completed_futures.next()) => {
                    match result {
                        Ok(result) => {
                            self.on_epoch_completed(result);
                        }
                        Err(err) => {
                            self.notify_other_failure(err, "failed to complete epoch").await;
                        }
                    }
                },
                event = self.barrier_event_rx.recv() => {
                    // event should not be None because the LocalBarrierManager holds a copy of tx
                    let result = self.handle_barrier_event(event.expect("should not be none"));
                    if let Err((actor_id, err)) = result {
                        self.notify_actor_failure(actor_id, err, "failed to handle barrier event").await;
                    }
                },
                failure = self.actor_failure_rx.recv() => {
                    let (actor_id, err) = failure.unwrap();
                    self.notify_actor_failure(actor_id, err, "recv actor failure").await;
                },
                actor_op = actor_op_rx.recv() => {
                    if let Some(actor_op) = actor_op {
                        match actor_op {
                            LocalActorOperation::NewControlStream { handle, init_request  } => {
                                self.control_stream_handle.reset_stream_with_err(Status::internal("control stream has been reset to a new one"));
                                self.reset(init_request.graphs).await;
                                self.control_stream_handle = handle;
                                self.control_stream_handle.send_response(StreamingControlStreamResponse {
                                    response: Some(streaming_control_stream_response::Response::Init(InitResponse {}))
                                });
                            }
                            LocalActorOperation::Shutdown { result_sender } => {
                                if !self.state.actor_states.is_empty() {
                                    tracing::warn!(
                                        "shutdown with running actors, scaling or migration will be triggered"
                                    );
                                }
                                self.control_stream_handle.shutdown_stream().await;
                                let _ = result_sender.send(());
                            }
                            actor_op => {
                                self.handle_actor_op(actor_op);
                            }
                        }
                    }
                    else {
                        break;
                    }
                },
                request = self.control_stream_handle.next_request() => {
                    let result = self.handle_streaming_control_request(request);
                    if let Err(err) = result {
                        self.notify_other_failure(err, "failed to inject barrier").await;
                    }
                },
            }
        }
    }

    fn handle_streaming_control_request(
        &mut self,
        request: StreamingControlStreamRequest,
    ) -> StreamResult<()> {
        match request.request.expect("should not be empty") {
            Request::InjectBarrier(req) => {
                let barrier = Barrier::from_protobuf(req.get_barrier().unwrap())?;
                self.update_actor_info(req.broadcast_info.iter().cloned())?;
                self.send_barrier(&barrier, req)?;
                Ok(())
            }
            Request::CompleteBarrier(req) => {
                self.complete_barrier(
                    req.task_id,
                    req.partial_graph_sync_epochs
                        .iter()
                        .map(|(partial_graph_id, epoch)| {
                            (PartialGraphId::new(*partial_graph_id), *epoch)
                        }),
                );
                Ok(())
            }
            Request::RemovePartialGraph(req) => {
                self.remove_partial_graphs(
                    req.partial_graph_ids.into_iter().map(PartialGraphId::new),
                );
                Ok(())
            }
            Request::CreatePartialGraph(req) => {
                self.add_partial_graph(PartialGraphId::new(req.partial_graph_id));
                Ok(())
            }
            Request::Init(_) => {
                unreachable!()
            }
        }
    }

    fn handle_barrier_event(
        &mut self,
        event: LocalBarrierEvent,
    ) -> Result<(), (ActorId, StreamError)> {
        match event {
            LocalBarrierEvent::ReportActorCollected { actor_id, epoch } => {
                self.collect(actor_id, epoch)
            }
            LocalBarrierEvent::ReportCreateProgress {
                epoch,
                actor,
                state,
            } => {
                self.update_create_mview_progress(epoch, actor, state);
            }
            LocalBarrierEvent::RegisterBarrierSender {
                actor_id,
                barrier_sender,
            } => {
                self.state
                    .register_barrier_sender(actor_id, barrier_sender)
                    .map_err(|e| (actor_id, e))?;
            }
            #[cfg(test)]
            LocalBarrierEvent::Flush(sender) => {
                use futures::FutureExt;
                while let Some(request) = self.control_stream_handle.next_request().now_or_never() {
                    self.handle_streaming_control_request(request).unwrap();
                }
                sender.send(()).unwrap()
            }
        }
        Ok(())
    }

    fn handle_actor_op(&mut self, actor_op: LocalActorOperation) {
        match actor_op {
            LocalActorOperation::NewControlStream { .. } | LocalActorOperation::Shutdown { .. } => {
                unreachable!("event {actor_op} should be handled separately in async context")
            }
            LocalActorOperation::TakeReceiver { ids, result_sender } => {
                let _ = result_sender.send(self.current_shared_context.take_receiver(ids));
            }
            #[cfg(test)]
            LocalActorOperation::GetCurrentSharedContext(sender) => {
                let _ = sender.send(self.current_shared_context.clone());
            }
            LocalActorOperation::InspectState { result_sender } => {
                let debug_info = self.to_debug_info();
                let _ = result_sender.send(debug_info.to_string());
            }
        }
    }
}

mod await_epoch_completed_future {
    use std::future::Future;

    use futures::future::BoxFuture;
    use futures::FutureExt;
    use risingwave_hummock_sdk::SyncResult;

    use crate::error::StreamResult;
    use crate::task::{await_tree_key, BarrierCompleteResult, PartialGraphId};

    pub(super) type AwaitEpochCompletedFuture =
        impl Future<Output = StreamResult<BarrierCompleteResult>> + 'static;

    pub(super) fn instrument_complete_barrier_future(
        task_id: u64,
        complete_barrier_future: BoxFuture<'static, StreamResult<SyncResult>>,
        sync_graph_epochs: Vec<(PartialGraphId, u64)>,
        barrier_await_tree_reg: Option<&await_tree::Registry>,
    ) -> AwaitEpochCompletedFuture {
        let future = complete_barrier_future.map(move |result| {
            result.map(|sync_result| BarrierCompleteResult {
                task_id,
                sync_result,
            })
        });
        if let Some(reg) = barrier_await_tree_reg {
            let span = format!("SyncEpoch({:?})", sync_graph_epochs);
            reg.register(await_tree_key::BarrierAwait { sync_graph_epochs }, span)
                .instrument(future)
                .left_future()
        } else {
            future.right_future()
        }
    }
}

use await_epoch_completed_future::*;
use risingwave_common::catalog::TableId;
use risingwave_storage::StateStoreImpl;

fn sync_epoch(
    state_store: &StateStoreImpl,
    streaming_metrics: &StreamingMetrics,
    sync_table_epochs: Vec<(HummockEpoch, HashSet<TableId>)>,
) -> BoxFuture<'static, StreamResult<SyncResult>> {
    let timer = streaming_metrics.barrier_sync_latency.start_timer();
    let hummock = state_store.as_hummock().cloned();
    let sync_table_epochs_clone = sync_table_epochs.clone();
    let future = async move {
        if let Some(hummock) = hummock {
            hummock.sync(sync_table_epochs_clone).await
        } else {
            Ok(SyncResult::default())
        }
    };
    future
        .instrument_await(format!("sync_epoch (epoch {:?})", sync_table_epochs))
        .inspect_ok(move |_| {
            timer.observe_duration();
        })
        .map_err(move |e| {
            tracing::error!(
                ?sync_table_epochs,
                error = %e.as_report(),
                "Failed to sync state store",
            );
            e.into()
        })
        .boxed()
}

impl LocalBarrierWorker {
    fn complete_barrier(
        &mut self,
        task_id: u64,
        sync_graph_epochs: impl Iterator<Item = (PartialGraphId, u64)>,
    ) {
        let sync_graph_epochs = sync_graph_epochs.collect_vec();
        {
            let complete_barrier_future = sync_epoch(
                &self.actor_manager.env.state_store(),
                &self.actor_manager.streaming_metrics,
                sync_graph_epochs
                    .iter()
                    .map(|(partial_graph_id, prev_epoch)| {
                        let (barrier, table_ids) = self
                            .state
                            .pop_barrier_to_complete(*partial_graph_id, *prev_epoch);
                        assert!(barrier.kind.is_checkpoint());
                        (barrier.epoch.prev, table_ids)
                    })
                    .collect_vec(),
            );

            self.await_epoch_completed_futures.push_back({
                instrument_complete_barrier_future(
                    task_id,
                    complete_barrier_future,
                    sync_graph_epochs,
                    self.actor_manager.await_tree_reg.as_ref(),
                )
            });
        }
    }

    fn on_epoch_completed(&mut self, result: BarrierCompleteResult) {
        let BarrierCompleteResult {
            task_id,
            sync_result,
        } = result;

        let (synced_sstables, table_watermarks, old_value_ssts) = (
            sync_result.uncommitted_ssts,
            sync_result.table_watermarks,
            sync_result.old_value_ssts,
        );

        let result = StreamingControlStreamResponse {
            response: Some(
                streaming_control_stream_response::Response::CompleteBarrier(
                    BarrierCompleteResponse {
                        task_id,
                        synced_sstables: synced_sstables
                            .into_iter()
                            .map(
                                |LocalSstableInfo {
                                     sst_info,
                                     table_stats,
                                     created_at,
                                 }| PbLocalSstableInfo {
                                    sst: Some(sst_info.into()),
                                    table_stats_map: to_prost_table_stats_map(table_stats),
                                    created_at,
                                },
                            )
                            .collect_vec(),
                        worker_id: self.actor_manager.env.worker_id(),
                        table_watermarks: table_watermarks
                            .into_iter()
                            .map(|(key, value)| (key.table_id, value.into()))
                            .collect(),
                        old_value_sstables: old_value_ssts
                            .into_iter()
                            .map(|sst| sst.sst_info.into())
                            .collect(),
                    },
                ),
            ),
        };

        self.control_stream_handle.send_response(result);
    }

    /// Broadcast a barrier to all senders. Save a receiver which will get notified when this
    /// barrier is finished, in managed mode.
    ///
    /// Note that the error returned here is typically a [`StreamError::barrier_send`], which is not
    /// the root cause of the failure. The caller should then call [`Self::try_find_root_failure`]
    /// to find the root cause.
    fn send_barrier(
        &mut self,
        barrier: &Barrier,
        request: InjectBarrierRequest,
    ) -> StreamResult<()> {
        debug!(
            target: "events::stream::barrier::manager::send",
            "send barrier {:?}, actor_ids_to_collect = {:?}",
            barrier,
            request.actor_ids_to_collect
        );

        self.state.transform_to_issued(barrier, request)?;
        Ok(())
    }

    fn remove_partial_graphs(&mut self, partial_graph_ids: impl Iterator<Item = PartialGraphId>) {
        for partial_graph_id in partial_graph_ids {
            if let Some(graph) = self.state.graph_states.remove(&partial_graph_id) {
                assert!(
                    graph.is_empty(),
                    "non empty graph to be removed: {}",
                    &graph
                );
            } else {
                warn!(
                    partial_graph_id = partial_graph_id.0,
                    "no partial graph to remove"
                );
            }
        }
    }

    pub(super) fn add_partial_graph(&mut self, partial_graph_id: PartialGraphId) {
        assert!(self
            .state
            .graph_states
            .insert(
                partial_graph_id,
                PartialGraphManagedBarrierState::new(&self.actor_manager)
            )
            .is_none());
    }

    /// Reset all internal states.
    pub(super) fn reset_state(&mut self, initial_partial_graphs: Vec<InitialPartialGraph>) {
        *self = Self::new(self.actor_manager.clone(), initial_partial_graphs);
    }

    /// When a [`crate::executor::StreamConsumer`] (typically [`crate::executor::DispatchExecutor`]) get a barrier, it should report
    /// and collect this barrier with its own `actor_id` using this function.
    fn collect(&mut self, actor_id: ActorId, epoch: EpochPair) {
        self.state.collect(actor_id, epoch)
    }

    /// When a actor exit unexpectedly, the error is reported using this function. The control stream
    /// will be reset and the meta service will then trigger recovery.
    async fn notify_actor_failure(
        &mut self,
        actor_id: ActorId,
        err: StreamError,
        err_context: &'static str,
    ) {
        let root_err = self.try_find_root_failure(err).await;

        if let Some(actor_state) = self.state.actor_states.get(&actor_id)
            && (!actor_state.inflight_barriers.is_empty() || actor_state.is_running())
        {
            self.control_stream_handle.reset_stream_with_err(
                anyhow!(root_err)
                    .context(err_context)
                    .to_status_unnamed(Code::Internal),
            );
        }
    }

    /// When some other failure happens (like failed to send barrier), the error is reported using
    /// this function. The control stream will be reset and the meta service will then trigger recovery.
    ///
    /// This is similar to [`Self::notify_actor_failure`], but since there's not always an actor failure,
    /// the given `err` will be used if there's no root failure found.
    async fn notify_other_failure(&mut self, err: StreamError, message: impl Into<String>) {
        let root_err = self.try_find_root_failure(err).await;

        self.control_stream_handle.reset_stream_with_err(
            anyhow!(root_err)
                .context(message.into())
                .to_status_unnamed(Code::Internal),
        );
    }

    /// Collect actor errors for a while and find the one that might be the root cause.
    ///
    /// Returns `None` if there's no actor error received.
    async fn try_find_root_failure(&mut self, first_err: StreamError) -> ScoredStreamError {
        let mut later_errs = vec![];
        // fetch more actor errors within a timeout
        let _ = tokio::time::timeout(Duration::from_secs(3), async {
            while let Some((_, error)) = self.actor_failure_rx.recv().await {
                later_errs.push(error);
            }
        })
        .await;

        once(first_err)
            .chain(later_errs.into_iter())
            .map(|e| ScoredStreamError::new(e.clone()))
            .max_by_key(|e| e.score)
            .expect("non-empty")
    }
}

#[derive(Clone)]
pub struct LocalBarrierManager {
    barrier_event_sender: UnboundedSender<LocalBarrierEvent>,
    actor_failure_sender: UnboundedSender<(ActorId, StreamError)>,
}

impl LocalBarrierWorker {
    /// Create a [`LocalBarrierWorker`] with managed mode.
    pub fn spawn(
        env: StreamEnvironment,
        streaming_metrics: Arc<StreamingMetrics>,
        await_tree_reg: Option<await_tree::Registry>,
        watermark_epoch: AtomicU64Ref,
        actor_op_rx: UnboundedReceiver<LocalActorOperation>,
    ) -> JoinHandle<()> {
        let runtime = {
            let mut builder = tokio::runtime::Builder::new_multi_thread();
            if let Some(worker_threads_num) = env.config().actor_runtime_worker_threads_num {
                builder.worker_threads(worker_threads_num);
            }
            builder
                .thread_name("rw-streaming")
                .enable_all()
                .build()
                .unwrap()
        };

        let actor_manager = Arc::new(StreamActorManager {
            env: env.clone(),
            streaming_metrics,
            watermark_epoch,
            await_tree_reg,
            runtime: runtime.into(),
        });
        let worker = LocalBarrierWorker::new(actor_manager, vec![]);
        tokio::spawn(worker.run(actor_op_rx))
    }
}

pub(super) struct EventSender<T>(pub(super) UnboundedSender<T>);

impl<T> Clone for EventSender<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T> EventSender<T> {
    pub(super) fn send_event(&self, event: T) {
        self.0.send(event).expect("should be able to send event")
    }

    pub(super) async fn send_and_await<RSP>(
        &self,
        make_event: impl FnOnce(oneshot::Sender<RSP>) -> T,
    ) -> StreamResult<RSP> {
        let (tx, rx) = oneshot::channel();
        let event = make_event(tx);
        self.send_event(event);
        rx.await
            .map_err(|_| anyhow!("barrier manager maybe reset").into())
    }
}

impl LocalBarrierManager {
    fn send_event(&self, event: LocalBarrierEvent) {
        // ignore error, because the current barrier manager maybe a stale one
        let _ = self.barrier_event_sender.send(event);
    }

    /// When a [`crate::executor::StreamConsumer`] (typically [`crate::executor::DispatchExecutor`]) get a barrier, it should report
    /// and collect this barrier with its own `actor_id` using this function.
    pub fn collect<M>(&self, actor_id: ActorId, barrier: &BarrierInner<M>) {
        self.send_event(LocalBarrierEvent::ReportActorCollected {
            actor_id,
            epoch: barrier.epoch,
        })
    }

    /// When a actor exit unexpectedly, it should report this event using this function, so meta
    /// will notice actor's exit while collecting.
    pub fn notify_failure(&self, actor_id: ActorId, err: StreamError) {
        let _ = self
            .actor_failure_sender
            .send((actor_id, err.into_unexpected_exit(actor_id)));
    }

    pub fn subscribe_barrier(&self, actor_id: ActorId) -> UnboundedReceiver<Barrier> {
        let (tx, rx) = mpsc::unbounded_channel();
        self.send_event(LocalBarrierEvent::RegisterBarrierSender {
            actor_id,
            barrier_sender: tx,
        });
        rx
    }
}

/// A [`StreamError`] with a score, used to find the root cause of actor failures.
#[derive(Debug, Clone)]
struct ScoredStreamError {
    error: StreamError,
    score: Score,
}

impl std::fmt::Display for ScoredStreamError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.error.fmt(f)
    }
}

impl std::error::Error for ScoredStreamError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.error.source()
    }

    fn provide<'a>(&'a self, request: &mut std::error::Request<'a>) {
        self.error.provide(request);
        // HIGHLIGHT: Provide the score to make it retrievable from meta service.
        request.provide_value(self.score);
    }
}

impl ScoredStreamError {
    /// Score the given error based on hard-coded rules.
    fn new(error: StreamError) -> Self {
        // Explicitly list all error kinds here to notice developers to update this function when
        // there are changes in error kinds.

        fn stream_executor_error_score(e: &StreamExecutorError) -> i32 {
            use crate::executor::error::ErrorKind;
            match e.inner() {
                // `ChannelClosed` or `ExchangeChannelClosed` is likely to be caused by actor exit
                // and not the root cause.
                ErrorKind::ChannelClosed(_) | ErrorKind::ExchangeChannelClosed(_) => 1,

                // Normal errors.
                ErrorKind::Uncategorized(_)
                | ErrorKind::Storage(_)
                | ErrorKind::ArrayError(_)
                | ErrorKind::ExprError(_)
                | ErrorKind::SerdeError(_)
                | ErrorKind::SinkError(_, _)
                | ErrorKind::RpcError(_)
                | ErrorKind::AlignBarrier(_, _)
                | ErrorKind::ConnectorError(_)
                | ErrorKind::DmlError(_)
                | ErrorKind::NotImplemented(_) => 999,
            }
        }

        fn stream_error_score(e: &StreamError) -> i32 {
            use crate::error::ErrorKind;
            match e.inner() {
                // `UnexpectedExit` wraps the original error. Score on the inner error.
                ErrorKind::UnexpectedExit { source, .. } => stream_error_score(source),

                // `BarrierSend` is likely to be caused by actor exit and not the root cause.
                ErrorKind::BarrierSend { .. } => 1,

                // Executor errors first.
                ErrorKind::Executor(ee) => 2000 + stream_executor_error_score(ee),

                // Then other errors.
                ErrorKind::Uncategorized(_)
                | ErrorKind::Storage(_)
                | ErrorKind::Expression(_)
                | ErrorKind::Array(_)
                | ErrorKind::Secret(_) => 1000,
            }
        }

        let score = Score(stream_error_score(&error));
        Self { error, score }
    }
}

#[cfg(test)]
impl LocalBarrierManager {
    fn spawn_for_test() -> EventSender<LocalActorOperation> {
        use std::sync::atomic::AtomicU64;
        let (tx, rx) = unbounded_channel();
        let _join_handle = LocalBarrierWorker::spawn(
            StreamEnvironment::for_test(),
            Arc::new(StreamingMetrics::unused()),
            None,
            Arc::new(AtomicU64::new(0)),
            rx,
        );
        EventSender(tx)
    }

    pub fn for_test() -> Self {
        let (tx, mut rx) = unbounded_channel();
        let (failure_tx, failure_rx) = unbounded_channel();
        let _join_handle = tokio::spawn(async move {
            let _failure_rx = failure_rx;
            while rx.recv().await.is_some() {}
        });
        Self {
            barrier_event_sender: tx,
            actor_failure_sender: failure_tx,
        }
    }

    pub async fn flush_all_events(&self) {
        let (tx, rx) = oneshot::channel();
        self.send_event(LocalBarrierEvent::Flush(tx));
        rx.await.unwrap()
    }
}

#[cfg(test)]
pub(crate) mod barrier_test_utils {
    use std::sync::Arc;

    use assert_matches::assert_matches;
    use futures::StreamExt;
    use risingwave_pb::stream_service::streaming_control_stream_request::{
        InitRequest, PbInitialPartialGraph,
    };
    use risingwave_pb::stream_service::{
        streaming_control_stream_request, streaming_control_stream_response, InjectBarrierRequest,
        StreamingControlStreamRequest, StreamingControlStreamResponse,
    };
    use tokio::sync::mpsc::{unbounded_channel, UnboundedReceiver, UnboundedSender};
    use tokio_stream::wrappers::UnboundedReceiverStream;
    use tonic::Status;

    use crate::executor::Barrier;
    use crate::task::barrier_manager::{ControlStreamHandle, EventSender, LocalActorOperation};
    use crate::task::{ActorId, LocalBarrierManager, SharedContext};

    pub(crate) struct LocalBarrierTestEnv {
        pub shared_context: Arc<SharedContext>,
        #[expect(dead_code)]
        pub(super) actor_op_tx: EventSender<LocalActorOperation>,
        pub request_tx: UnboundedSender<Result<StreamingControlStreamRequest, Status>>,
        pub response_rx: UnboundedReceiver<Result<StreamingControlStreamResponse, Status>>,
    }

    impl LocalBarrierTestEnv {
        pub(crate) async fn for_test() -> Self {
            let actor_op_tx = LocalBarrierManager::spawn_for_test();

            let (request_tx, request_rx) = unbounded_channel();
            let (response_tx, mut response_rx) = unbounded_channel();

            actor_op_tx.send_event(LocalActorOperation::NewControlStream {
                handle: ControlStreamHandle::new(
                    response_tx,
                    UnboundedReceiverStream::new(request_rx).boxed(),
                ),
                init_request: InitRequest {
                    graphs: vec![PbInitialPartialGraph {
                        partial_graph_id: u64::MAX,
                        subscriptions: vec![],
                    }],
                },
            });

            assert_matches!(
                response_rx.recv().await.unwrap().unwrap().response.unwrap(),
                streaming_control_stream_response::Response::Init(_)
            );

            let shared_context = actor_op_tx
                .send_and_await(LocalActorOperation::GetCurrentSharedContext)
                .await
                .unwrap();

            Self {
                shared_context,
                actor_op_tx,
                request_tx,
                response_rx,
            }
        }

        pub(crate) fn inject_barrier(
            &self,
            barrier: &Barrier,
            actor_to_collect: impl IntoIterator<Item = ActorId>,
        ) {
            self.request_tx
                .send(Ok(StreamingControlStreamRequest {
                    request: Some(streaming_control_stream_request::Request::InjectBarrier(
                        InjectBarrierRequest {
                            request_id: "".to_string(),
                            barrier: Some(barrier.to_protobuf()),
                            actor_ids_to_collect: actor_to_collect.into_iter().collect(),
                            table_ids_to_sync: vec![],
                            partial_graph_id: u64::MAX,
                            broadcast_info: vec![],
                            actors_to_build: vec![],
                            subscriptions_to_add: vec![],
                            subscriptions_to_remove: vec![],
                        },
                    )),
                }))
                .unwrap();
        }
    }
}
