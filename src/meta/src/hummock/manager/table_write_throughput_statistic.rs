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

use std::collections::{HashMap, VecDeque};

#[derive(Debug, Clone)]
pub struct TableWriteThroughputStatistic {
    pub throughput: u64,
    pub timestamp_secs: i64,
}

impl AsRef<TableWriteThroughputStatistic> for TableWriteThroughputStatistic {
    fn as_ref(&self) -> &TableWriteThroughputStatistic {
        self
    }
}

#[derive(Debug, Clone)]
pub struct TableWriteThroughputStatisticManager {
    table_throughput: HashMap<u32, VecDeque<TableWriteThroughputStatistic>>,
    max_statistic_expired_secs: i64,
}

impl TableWriteThroughputStatisticManager {
    pub fn new(max_statistic_expired_secs: i64) -> Self {
        Self {
            table_throughput: HashMap::new(),
            max_statistic_expired_secs,
        }
    }

    pub fn add_table_throughput_with_ts(
        &mut self,
        table_id: u32,
        throughput: u64,
        timestamp_secs: i64,
    ) {
        let table_throughput = self.table_throughput.entry(table_id).or_default();
        table_throughput.push_back(TableWriteThroughputStatistic {
            throughput,
            timestamp_secs,
        });

        Self::retain_vec_deque(
            table_throughput,
            self.max_statistic_expired_secs,
            timestamp_secs,
        );

        if table_throughput.is_empty() {
            self.table_throughput.remove(&table_id);
        }
    }

    pub fn get_table_throughput(
        &self,
        table_id: u32,
        window_secs: i64,
    ) -> VecDeque<&TableWriteThroughputStatistic> {
        let timestamp_secs = chrono::Utc::now().timestamp();
        if let Some(statistics) = self.table_throughput.get(&table_id) {
            let mut table_throughput_statistics = statistics.iter().collect();
            Self::retain_vec_deque(
                &mut table_throughput_statistics,
                window_secs,
                timestamp_secs,
            );

            table_throughput_statistics
        } else {
            VecDeque::new()
        }
    }

    /// Remove expired statistics.
    fn retain_vec_deque<T>(
        vec_deque: &mut VecDeque<T>,
        max_statistic_expired_secs: i64,
        timestamp_secs: i64,
    ) where
        T: AsRef<TableWriteThroughputStatistic>,
    {
        while let Some(statistic) = vec_deque.front() {
            if timestamp_secs - statistic.as_ref().timestamp_secs > max_statistic_expired_secs {
                vec_deque.pop_front();
            } else {
                break;
            }
        }
    }
}
