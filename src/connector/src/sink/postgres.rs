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

use std::collections::BTreeMap;
use std::sync::Arc;

use anyhow::{anyhow, Context};
use async_trait::async_trait;
use itertools::Itertools;
use risingwave_common::array::{Op, StreamChunk};
use risingwave_common::bitmap::Bitmap;
use risingwave_common::catalog::Schema;
use risingwave_common::row::{Row, RowExt};
use risingwave_common::types::DataType;
use serde_derive::Deserialize;
use serde_with::{serde_as, DisplayFromStr};
use simd_json::prelude::ArrayTrait;
use thiserror_ext::AsReport;
use tokio_postgres::Statement;
use with_options::WithOptions;

use super::{
    SinkError, SinkWriterMetrics, SINK_TYPE_APPEND_ONLY, SINK_TYPE_OPTION, SINK_TYPE_UPSERT,
};
use crate::sink::writer::{LogSinkerOf, SinkWriter, SinkWriterExt};
use crate::sink::{DummySinkCommitCoordinator, Result, Sink, SinkParam, SinkWriterParam};

pub const POSTGRES_SINK: &str = "postgres";

#[serde_as]
#[derive(Clone, Debug, Deserialize, WithOptions)]
pub struct PostgresConfig {
    pub host: String,
    #[serde_as(as = "DisplayFromStr")]
    pub port: u16,
    pub user: String,
    pub password: String,
    pub database: String,
    pub table: String,
    #[serde(default = "default_schema")]
    pub schema: String,
    #[serde(default = "default_max_batch_rows")]
    #[serde_as(as = "DisplayFromStr")]
    pub max_batch_rows: usize,
    pub r#type: String, // accept "append-only" or "upsert"
}

fn default_max_batch_rows() -> usize {
    1024
}

fn default_schema() -> String {
    "public".to_string()
}

impl PostgresConfig {
    pub fn from_btreemap(properties: BTreeMap<String, String>) -> Result<Self> {
        let config =
            serde_json::from_value::<PostgresConfig>(serde_json::to_value(properties).unwrap())
                .map_err(|e| SinkError::Config(anyhow!(e)))?;
        if config.r#type != SINK_TYPE_APPEND_ONLY && config.r#type != SINK_TYPE_UPSERT {
            return Err(SinkError::Config(anyhow!(
                "`{}` must be {}, or {}",
                SINK_TYPE_OPTION,
                SINK_TYPE_APPEND_ONLY,
                SINK_TYPE_UPSERT
            )));
        }
        Ok(config)
    }
}

#[derive(Debug)]
pub struct PostgresSink {
    pub config: PostgresConfig,
    schema: Schema,
    pk_indices: Vec<usize>,
    is_append_only: bool,
}

impl PostgresSink {
    pub fn new(
        config: PostgresConfig,
        schema: Schema,
        pk_indices: Vec<usize>,
        is_append_only: bool,
    ) -> Result<Self> {
        Ok(Self {
            config,
            schema,
            pk_indices,
            is_append_only,
        })
    }
}

impl TryFrom<SinkParam> for PostgresSink {
    type Error = SinkError;

    fn try_from(param: SinkParam) -> std::result::Result<Self, Self::Error> {
        let schema = param.schema();
        let config = PostgresConfig::from_btreemap(param.properties)?;
        PostgresSink::new(
            config,
            schema,
            param.downstream_pk,
            param.sink_type.is_append_only(),
        )
    }
}

impl Sink for PostgresSink {
    type Coordinator = DummySinkCommitCoordinator;
    type LogSinker = LogSinkerOf<PostgresSinkWriter>;

    const SINK_NAME: &'static str = POSTGRES_SINK;

    async fn validate(&self) -> Result<()> {
        if !self.is_append_only && self.pk_indices.is_empty() {
            return Err(SinkError::Config(anyhow!(
                "Primary key not defined for upsert Postgres sink (please define in `primary_key` field)")));
        }

        for field in self.schema.fields() {
            check_data_type_compatibility(field.data_type())?;
        }

        // Verify pg table schema matches rw table schema, and pk indices are valid
        let table_name = &self.config.table;
        let connection_string = format!(
            "host={} port={} user={} password={} dbname={}",
            self.config.host,
            self.config.port,
            self.config.user,
            self.config.password,
            self.config.database
        );
        let (client, connection) =
            tokio_postgres::connect(&connection_string, tokio_postgres::NoTls)
                .await
                .context("Failed to connect to Postgres for Sinking")?;
        tokio::spawn(async move {
            if let Err(error) = connection.await {
                tracing::error!(error = %error.as_report(), "postgres sink connection error");
            }
        });

        let result = client
            .query(
                "
                SELECT
                   column_name,
                   EXISTS (
                       SELECT 1
                       FROM pg_index i
                       WHERE i.indrelid = c.table_name::regclass
                       AND i.indisprimary
                       AND column_name = ANY(
                           SELECT a.attname
                           FROM pg_attribute a
                           WHERE a.attrelid = i.indrelid
                           AND a.attnum = ANY(i.indkey)
                       )
                   ) AS is_primary_key
                FROM
                   information_schema.columns c
                WHERE
                   table_name = $1
                ORDER BY
                   ordinal_position;",
                &[&table_name],
            )
            .await
            .context("Failed to query Postgres for Sinking")?;

        let mut pg_schema = BTreeMap::new();
        for row in result {
            let col_name: String = row.get(0);
            let is_pk: bool = row.get(1);
            pg_schema.insert(col_name, is_pk);
        }

        for (i, field) in self.schema.fields().iter().enumerate() {
            let col_name = &field.name;
            let is_pk = pg_schema.get(col_name);
            match is_pk {
                None => return Err(SinkError::Config(anyhow!(
                    "Column `{}` not found in Postgres table `{}`",
                    col_name,
                    table_name
                ))),
                Some(is_pk) =>
                    match (*is_pk, self.pk_indices.contains(&i)) {
                        (false, false) | (true, true) => continue,
                        (false, true) => return Err(SinkError::Config(anyhow!(
                            "Column `{}` in Postgres table `{}` is not a primary key, but RW schema defines it as a primary key",
                            col_name,
                            table_name
                        ))),
                        (true, false) => return Err(SinkError::Config(anyhow!(
                            "Column `{}` in Postgres table `{}` is a primary key, but RW schema does not define it as a primary key",
                            col_name,
                            table_name
                        ))),
                    }
            }
        }

        Ok(())
    }

    async fn new_log_sinker(&self, writer_param: SinkWriterParam) -> Result<Self::LogSinker> {
        Ok(PostgresSinkWriter::new(
            self.config.clone(),
            self.schema.clone(),
            self.pk_indices.clone(),
            self.is_append_only,
        )
        .await?
        .into_log_sinker(SinkWriterMetrics::new(&writer_param)))
    }
}

struct Buffer {
    buffer: Vec<StreamChunk>,
    size: usize,
}

impl Buffer {
    fn new() -> Self {
        Self {
            buffer: Vec::new(),
            size: 0,
        }
    }

    fn push(&mut self, chunk: StreamChunk) -> usize {
        self.size += chunk.cardinality();
        self.buffer.push(chunk);
        self.size
    }

    fn drain(&mut self) -> Vec<StreamChunk> {
        self.size = 0;
        std::mem::take(&mut self.buffer)
    }
}

pub struct PostgresSinkWriter {
    config: PostgresConfig,
    pk_indices: Vec<usize>,
    is_append_only: bool,
    client: tokio_postgres::Client,
    buffer: Buffer,
    insert_statement: Statement,
    delete_statement: Option<Statement>,
    merge_statement: Option<Statement>,
}

impl PostgresSinkWriter {
    async fn new(
        config: PostgresConfig,
        schema: Schema,
        pk_indices: Vec<usize>,
        is_append_only: bool,
    ) -> Result<Self> {
        let client = {
            let connection_string = format!(
                "host={} port={} user={} password={} dbname={}",
                config.host, config.port, config.user, config.password, config.database
            );
            let (client, connection) =
                tokio_postgres::connect(&connection_string, tokio_postgres::NoTls)
                    .await
                    .context("Failed to connect to Postgres for Sinking")?;
            tokio::spawn(async move {
                if let Err(error) = connection.await {
                    tracing::error!(error = %error.as_report(), "postgres sink connection error");
                }
            });
            client
        };

        let insert_statement = {
            let insert_types = schema
                .fields()
                .iter()
                .map(|field| field.data_type().to_pg_type())
                .collect_vec();
            let insert_sql = create_insert_sql(&schema, &config.table);
            client
                .prepare_typed(&insert_sql, &insert_types)
                .await
                .context("Failed to prepare insert statement")?
        };

        let delete_statement = if is_append_only {
            None
        } else {
            let delete_types = pk_indices
                .iter()
                .map(|i| schema.fields()[*i].data_type().to_pg_type())
                .collect_vec();
            let delete_sql = create_delete_sql(&schema, &config.table, &pk_indices);
            Some(
                client
                    .prepare_typed(&delete_sql, &delete_types)
                    .await
                    .context("Failed to prepare delete statement")?,
            )
        };

        let merge_statement = if is_append_only {
            None
        } else {
            let merge_types = schema
                .fields
                .iter()
                .map(|field| field.data_type().to_pg_type())
                .collect_vec();
            let merge_sql = create_upsert_sql(&schema, &config.table, &pk_indices);
            Some(
                client
                    .prepare_typed(&merge_sql, &merge_types)
                    .await
                    .context("Failed to prepare merge statement")?,
            )
        };

        let writer = Self {
            config,
            pk_indices,
            is_append_only,
            client,
            buffer: Buffer::new(),
            insert_statement,
            delete_statement,
            merge_statement,
        };
        Ok(writer)
    }

    async fn flush(&mut self) -> Result<()> {
        if self.is_append_only {
            for chunk in self.buffer.drain() {
                for (op, row) in chunk.rows() {
                    match op {
                        Op::Insert => {
                            self.client
                                .execute_raw(&self.insert_statement, row.iter())
                                .await?;
                        }
                        Op::UpdateInsert | Op::Delete | Op::UpdateDelete => {
                            debug_assert!(!self.is_append_only);
                        }
                    }
                }
            }
        } else {
            for chunk in self.buffer.drain() {
                for (op, row) in chunk.rows() {
                    match op {
                        Op::Insert => {
                            self.client
                                .execute_raw(&self.insert_statement, row.iter())
                                .await?;
                        }
                        Op::UpdateInsert => {
                            // NOTE(kwannoel): Here we use `MERGE` rather than `UPDATE/INSERT` directly.
                            // This is because the downstream db could have cleaned the old record,
                            // in that case it needs to be `INSERTED` rather than UPDATED.
                            // On the other hand, if the record is there, it should be `UPDATED`.
                            self.client
                                .execute_raw(self.merge_statement.as_ref().unwrap(), row.iter())
                                .await?;
                        }
                        Op::Delete => {
                            self.client
                                .execute_raw(
                                    self.delete_statement.as_ref().unwrap(),
                                    row.project(&self.pk_indices).iter(),
                                )
                                .await?;
                        }
                        Op::UpdateDelete => {}
                    }
                }
            }
        }

        Ok(())
    }
}

#[async_trait]
impl SinkWriter for PostgresSinkWriter {
    async fn begin_epoch(&mut self, _epoch: u64) -> Result<()> {
        Ok(())
    }

    async fn write_batch(&mut self, chunk: StreamChunk) -> Result<()> {
        let cardinality = self.buffer.push(chunk);
        if cardinality >= self.config.max_batch_rows {
            self.flush().await?;
        }
        Ok(())
    }

    async fn barrier(&mut self, is_checkpoint: bool) -> Result<Self::CommitMetadata> {
        if is_checkpoint {
            self.flush().await?;
        }
        Ok(())
    }

    async fn abort(&mut self) -> Result<()> {
        Ok(())
    }

    async fn update_vnode_bitmap(&mut self, _vnode_bitmap: Arc<Bitmap>) -> Result<()> {
        Ok(())
    }
}

fn data_type_not_supported(data_type_name: &str) -> SinkError {
    SinkError::Postgres(anyhow!(format!(
        "{data_type_name} is not supported in SQL Server"
    )))
}

fn check_data_type_compatibility(data_type: DataType) -> Result<()> {
    match data_type {
        DataType::Boolean
        | DataType::Int16
        | DataType::Int32
        | DataType::Int64
        | DataType::Float32
        | DataType::Float64
        | DataType::Decimal
        | DataType::Date
        | DataType::Varchar
        | DataType::Time
        | DataType::Timestamp
        | DataType::Timestamptz
        | DataType::Jsonb
        | DataType::Interval
        | DataType::Bytea => Ok(()),
        DataType::Struct(_) => Err(data_type_not_supported("Struct")),
        DataType::List(_) => Err(data_type_not_supported("List")),
        DataType::Serial => Err(data_type_not_supported("Serial")),
        DataType::Int256 => Err(data_type_not_supported("Int256")),
        DataType::Map(_) => Err(data_type_not_supported("Map")),
    }
}

fn create_insert_sql(schema: &Schema, table_name: &str) -> String {
    let columns: String = schema
        .fields()
        .iter()
        .map(|field| field.name.clone())
        .collect_vec()
        .join(", ");
    let parameters: String = (0..schema.fields().len())
        .map(|i| format!("${}", i + 1))
        .collect_vec()
        .join(", ");
    format!("INSERT INTO {table_name} ({columns}) VALUES ({parameters})")
}

fn create_upsert_sql(schema: &Schema, table_name: &str, pk_indices: &[usize]) -> String {
    let columns: String = schema
        .fields()
        .iter()
        .map(|field| field.name.clone())
        .collect_vec()
        .join(", ");
    let parameters: String = (0..schema.fields().len())
        .map(|i| format!("${}", i + 1))
        .collect_vec()
        .join(", ");
    let pk_columns = pk_indices
        .iter()
        .map(|i| schema.fields()[*i].name.clone())
        .collect_vec()
        .join(", ");
    let update_parameters: String = (0..schema.fields().len())
        .filter(|i| !pk_indices.contains(i))
        .map(|i| {
            let column = schema.fields()[i].name.clone();
            let param = format!("${}", i + 1);
            format!("{column} = {param}")
        })
        .collect_vec()
        .join(", ");
    format!("INSERT INTO {table_name} ({columns}) VALUES ({parameters}) on conflict ({pk_columns}) do update set {update_parameters}")
}

fn create_delete_sql(schema: &Schema, table_name: &str, pk_indices: &[usize]) -> String {
    let parameters: String = pk_indices
        .iter()
        .map(|i| format!("{} = ${}", schema.fields()[*i].name, i + 1))
        .collect_vec()
        .join(" AND ");
    format!("DELETE FROM {table_name} WHERE {parameters}")
}

#[cfg(test)]
mod tests {
    use std::fmt::Display;

    use expect_test::{expect, Expect};
    use risingwave_common::catalog::Field;

    use super::*;

    fn check(actual: impl Display, expect: Expect) {
        let actual = actual.to_string();
        expect.assert_eq(&actual);
    }

    #[test]
    fn test_create_insert_sql() {
        let schema = Schema::new(vec![
            Field {
                data_type: DataType::Int32,
                name: "a".to_string(),
                sub_fields: vec![],
                type_name: "".to_string(),
            },
            Field {
                data_type: DataType::Int32,
                name: "b".to_string(),
                sub_fields: vec![],
                type_name: "".to_string(),
            },
        ]);
        let table_name = "test_table";
        let sql = create_insert_sql(&schema, table_name);
        check(
            sql,
            expect!["INSERT INTO test_table (a, b) VALUES ($1, $2)"],
        );
    }

    #[test]
    fn test_create_delete_sql() {
        let schema = Schema::new(vec![
            Field {
                data_type: DataType::Int32,
                name: "a".to_string(),
                sub_fields: vec![],
                type_name: "".to_string(),
            },
            Field {
                data_type: DataType::Int32,
                name: "b".to_string(),
                sub_fields: vec![],
                type_name: "".to_string(),
            },
        ]);
        let table_name = "test_table";
        let sql = create_delete_sql(&schema, table_name, &[1]);
        check(sql, expect!["DELETE FROM test_table WHERE b = $2"]);
    }

    #[test]
    fn test_create_upsert_sql() {
        let schema = Schema::new(vec![
            Field {
                data_type: DataType::Int32,
                name: "a".to_string(),
                sub_fields: vec![],
                type_name: "".to_string(),
            },
            Field {
                data_type: DataType::Int32,
                name: "b".to_string(),
                sub_fields: vec![],
                type_name: "".to_string(),
            },
        ]);
        let table_name = "test_table";
        let sql = create_upsert_sql(&schema, table_name, &[1]);
        check(
            sql,
            expect![
                "INSERT INTO test_table (a, b) VALUES ($1, $2) on conflict do update set a = $1"
            ],
        );
    }
}
