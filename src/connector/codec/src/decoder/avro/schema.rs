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

use std::sync::{Arc, LazyLock};

use anyhow::Context;
use apache_avro::schema::{DecimalSchema, NamesRef, RecordSchema, ResolvedSchema, Schema};
use apache_avro::AvroResult;
use itertools::Itertools;
use risingwave_common::error::NotImplemented;
use risingwave_common::log::LogSuppresser;
use risingwave_common::types::{DataType, Decimal, MapType};
use risingwave_common::{bail, bail_not_implemented};
use risingwave_pb::plan_common::{AdditionalColumn, ColumnDesc, ColumnDescVersion};

use super::get_nullable_union_inner;

/// Avro schema with `Ref` inlined. The newtype is used to indicate whether the schema is resolved.
///
/// TODO: Actually most of the place should use resolved schema, but currently they just happen to work (Some edge cases are not met yet).
///
/// TODO: refactor avro lib to use the feature there.
#[derive(Debug)]
pub struct ResolvedAvroSchema {
    /// Should be used for parsing bytes into Avro value
    pub original_schema: Arc<Schema>,
    /// Should be used for type mapping from Avro value to RisingWave datum
    pub resolved_schema: Schema,
}

impl ResolvedAvroSchema {
    pub fn create(schema: Arc<Schema>) -> AvroResult<Self> {
        let resolver = ResolvedSchema::try_from(schema.as_ref())?;
        // todo: to_resolved may cause stackoverflow if there's a loop in the schema
        let resolved_schema = resolver.to_resolved(schema.as_ref())?;
        Ok(Self {
            original_schema: schema,
            resolved_schema,
        })
    }
}

/// This is a shallow lookup instead of recursive. It cannot mutate `Ref` in subtrees.
pub fn lookup_ref<'s>(original: &'s Schema, refs: &NamesRef<'s>) -> &'s Schema {
    match original {
        // `unwrap` is safe because errors already handled when generating `refs`.
        Schema::Ref { name } => refs.get(name).unwrap(),
        _ => original,
    }
}

/// How to convert the map type from the input encoding to RisingWave's datatype.
///
/// XXX: Should this be `avro.map.handling.mode`? Can it be shared between Avro and Protobuf?
#[derive(Debug, Copy, Clone)]
pub enum MapHandling {
    Jsonb,
    Map,
}

impl MapHandling {
    pub const OPTION_KEY: &'static str = "map.handling.mode";

    pub fn from_options(
        options: &std::collections::BTreeMap<String, String>,
    ) -> anyhow::Result<Option<Self>> {
        let mode = match options.get(Self::OPTION_KEY).map(std::ops::Deref::deref) {
            Some("jsonb") => Self::Jsonb,
            Some("map") => Self::Map,
            Some(v) => bail!("unrecognized {} value {}", Self::OPTION_KEY, v),
            None => return Ok(None),
        };
        Ok(Some(mode))
    }
}

/// This function expects resolved schema (no `Ref`).
/// FIXME: require passing resolved schema here.
/// TODO: change `map_handling` to some `Config`, and also unify debezium.
/// TODO: use `ColumnDesc` in common instead of PB.
pub fn avro_schema_to_column_descs(
    schema: &Schema,
    map_handling: Option<MapHandling>,
) -> anyhow::Result<Vec<ColumnDesc>> {
    let resolved: ResolvedSchema<'_> = schema.try_into()?;
    if let Schema::Record(RecordSchema { fields, .. }) = schema {
        let mut index = 0;
        let fields = fields
            .iter()
            .map(|field| {
                avro_field_to_column_desc(
                    &field.name,
                    &field.schema,
                    resolved.get_names(),
                    &mut index,
                    map_handling,
                )
            })
            .collect::<anyhow::Result<_>>()?;
        Ok(fields)
    } else {
        bail!("schema invalid, record type required at top level of the schema.");
    }
}

const DBZ_VARIABLE_SCALE_DECIMAL_NAME: &str = "VariableScaleDecimal";
const DBZ_VARIABLE_SCALE_DECIMAL_NAMESPACE: &str = "io.debezium.data";

fn avro_field_to_column_desc(
    name: &str,
    schema: &Schema,
    refs: &NamesRef<'_>,
    index: &mut i32,
    map_handling: Option<MapHandling>,
) -> anyhow::Result<ColumnDesc> {
    let data_type = avro_type_mapping(schema, refs, map_handling)?;
    match schema {
        Schema::Ref { .. } => {
            avro_field_to_column_desc(name, lookup_ref(schema, refs), refs, index, map_handling)
        }
        Schema::Record(RecordSchema {
            name: schema_name,
            fields,
            ..
        }) => {
            let vec_column = fields
                .iter()
                .map(|f| avro_field_to_column_desc(&f.name, &f.schema, refs, index, map_handling))
                .collect::<anyhow::Result<_>>()?;
            *index += 1;
            Ok(ColumnDesc {
                column_type: Some(data_type.to_protobuf()),
                column_id: *index,
                name: name.to_owned(),
                field_descs: vec_column,
                type_name: schema_name.to_string(),
                generated_or_default_column: None,
                description: None,
                additional_column_type: 0, // deprecated
                additional_column: Some(AdditionalColumn { column_type: None }),
                version: ColumnDescVersion::Pr13707 as i32,
            })
        }
        _ => {
            *index += 1;
            Ok(ColumnDesc {
                column_type: Some(data_type.to_protobuf()),
                column_id: *index,
                name: name.to_owned(),
                additional_column: Some(AdditionalColumn { column_type: None }),
                version: ColumnDescVersion::Pr13707 as i32,
                ..Default::default()
            })
        }
    }
}

/// This function expects resolved schema (no `Ref`).
fn avro_type_mapping(
    schema: &Schema,
    refs: &NamesRef<'_>,
    map_handling: Option<MapHandling>,
) -> anyhow::Result<DataType> {
    let data_type = match schema {
        Schema::String => DataType::Varchar,
        Schema::Int => DataType::Int32,
        Schema::Long => DataType::Int64,
        Schema::Boolean => DataType::Boolean,
        Schema::Float => DataType::Float32,
        Schema::Double => DataType::Float64,
        Schema::Decimal(DecimalSchema { precision, .. }) => {
            if *precision > Decimal::MAX_PRECISION.into() {
                static LOG_SUPPERSSER: LazyLock<LogSuppresser> =
                    LazyLock::new(LogSuppresser::default);
                if let Ok(suppressed_count) = LOG_SUPPERSSER.check() {
                    tracing::warn!(
                        suppressed_count,
                        "RisingWave supports decimal precision up to {}, but got {}. Will truncate.",
                        Decimal::MAX_PRECISION,
                        precision
                    );
                }
            }
            DataType::Decimal
        }
        Schema::Date => DataType::Date,
        Schema::LocalTimestampMillis => DataType::Timestamp,
        Schema::LocalTimestampMicros => DataType::Timestamp,
        Schema::TimestampMillis => DataType::Timestamptz,
        Schema::TimestampMicros => DataType::Timestamptz,
        Schema::Duration => DataType::Interval,
        Schema::Bytes => DataType::Bytea,
        Schema::Enum { .. } => DataType::Varchar,
        Schema::TimeMillis => DataType::Time,
        Schema::TimeMicros => DataType::Time,
        Schema::Record(RecordSchema { fields, name, .. }) => {
            if name.name == DBZ_VARIABLE_SCALE_DECIMAL_NAME
                && name.namespace == Some(DBZ_VARIABLE_SCALE_DECIMAL_NAMESPACE.into())
            {
                return Ok(DataType::Decimal);
            }

            let struct_fields = fields
                .iter()
                .map(|f| avro_type_mapping(&f.schema, refs, map_handling))
                .collect::<anyhow::Result<_>>()?;
            let struct_names = fields.iter().map(|f| f.name.clone()).collect_vec();
            DataType::new_struct(struct_fields, struct_names)
        }
        Schema::Array(item_schema) => {
            let item_type = avro_type_mapping(item_schema.as_ref(), refs, map_handling)?;
            DataType::List(Box::new(item_type))
        }
        Schema::Union(union_schema) => {
            // Note: Unions may not immediately contain other unions. So a `null` must represent a top-level null.
            // e.g., ["null", ["null", "string"]] is not allowed

            // Note: Unions may not contain more than one schema with the same type, except for the named types record, fixed and enum.
            // https://avro.apache.org/docs/1.11.1/specification/_print/#unions
            debug_assert!(
                union_schema
                    .variants()
                    .iter()
                    .map(Schema::canonical_form) // Schema doesn't implement Eq, but only PartialEq.
                    .duplicates()
                    .next()
                    .is_none(),
                "Union contains duplicate types: {union_schema:?}",
            );
            match get_nullable_union_inner(union_schema) {
                Some(inner) => avro_type_mapping(inner, refs, map_handling)?,
                None => {
                    // Convert the union to a struct, each field of the struct represents a variant of the union.
                    // Refer to https://github.com/risingwavelabs/risingwave/issues/16273#issuecomment-2179761345 to see why it's not perfect.
                    // Note: Avro union's variant tag is type name, not field name (unlike Rust enum, or Protobuf oneof).

                    // XXX: do we need to introduce union.handling.mode?
                    let (fields, field_names) = union_schema
                        .variants()
                        .iter()
                        // null will mean the whole struct is null
                        .filter(|variant| !matches!(variant, &&Schema::Null))
                        .map(|variant| {
                            avro_type_mapping(variant, refs, map_handling).and_then(|t| {
                                let name = avro_schema_to_struct_field_name(variant)?;
                                Ok((t, name))
                            })
                        })
                        .process_results(|it| it.unzip::<_, _, Vec<_>, Vec<_>>())
                        .context("failed to convert Avro union to struct")?;

                    DataType::new_struct(fields, field_names)
                }
            }
        }
        Schema::Ref { name } => {
            if name.name == DBZ_VARIABLE_SCALE_DECIMAL_NAME
                && name.namespace == Some(DBZ_VARIABLE_SCALE_DECIMAL_NAMESPACE.into())
            {
                DataType::Decimal
            } else {
                // bail_not_implemented!("Avro type: {:?}", schema);
                return avro_type_mapping(lookup_ref(schema, refs), refs, map_handling);
            }
        }
        Schema::Map(value_schema) => {
            // TODO: support native map type
            match map_handling {
                Some(MapHandling::Jsonb) => {
                    if supported_avro_to_json_type(value_schema) {
                        DataType::Jsonb
                    } else {
                        bail_not_implemented!(
                            issue = 16963,
                            "Avro map type to jsonb: {:?}",
                            schema
                        );
                    }
                }
                Some(MapHandling::Map) | None => {
                    let value = avro_type_mapping(value_schema.as_ref(), refs, map_handling)
                        .context("failed to convert Avro map type")?;
                    DataType::Map(MapType::from_kv(DataType::Varchar, value))
                }
            }
        }
        Schema::Uuid => DataType::Varchar,
        Schema::Null | Schema::Fixed(_) => {
            bail_not_implemented!("Avro type: {:?}", schema);
        }
    };

    Ok(data_type)
}

/// Check for [`super::avro_to_jsonb`]
fn supported_avro_to_json_type(schema: &Schema) -> bool {
    match schema {
        Schema::Null | Schema::Boolean | Schema::Int | Schema::String => true,

        Schema::Map(value_schema) | Schema::Array(value_schema) => {
            supported_avro_to_json_type(value_schema)
        }
        Schema::Record(RecordSchema { fields, .. }) => fields
            .iter()
            .all(|f| supported_avro_to_json_type(&f.schema)),
        Schema::Long
        | Schema::Float
        | Schema::Double
        | Schema::Bytes
        | Schema::Enum(_)
        | Schema::Fixed(_)
        | Schema::Decimal(_)
        | Schema::Uuid
        | Schema::Date
        | Schema::TimeMillis
        | Schema::TimeMicros
        | Schema::TimestampMillis
        | Schema::TimestampMicros
        | Schema::LocalTimestampMillis
        | Schema::LocalTimestampMicros
        | Schema::Duration
        | Schema::Ref { name: _ }
        | Schema::Union(_) => false,
    }
}

/// The field name when converting Avro union type to RisingWave struct type.
pub(super) fn avro_schema_to_struct_field_name(schema: &Schema) -> Result<String, NotImplemented> {
    Ok(match schema {
        Schema::Null => unreachable!(),
        Schema::Union(_) => unreachable!(),
        // Primitive types
        Schema::Boolean => "boolean".to_string(),
        Schema::Int => "int".to_string(),
        Schema::Long => "long".to_string(),
        Schema::Float => "float".to_string(),
        Schema::Double => "double".to_string(),
        Schema::Bytes => "bytes".to_string(),
        Schema::String => "string".to_string(),
        // Unnamed Complex types
        Schema::Array(_) => "array".to_string(),
        Schema::Map(_) => "map".to_string(),
        // Named Complex types
        Schema::Enum(_) | Schema::Ref { name: _ } | Schema::Fixed(_) | Schema::Record(_) => {
            // schema.name().unwrap().fullname(None)
            // See test_avro_lib_union_record_bug
            // https://github.com/risingwavelabs/risingwave/issues/17632
            bail_not_implemented!(issue=17632, "Avro named type used in Union type: {:?}", schema)

        }

        // Logical types are currently banned. See https://github.com/risingwavelabs/risingwave/issues/17616

/*
        Schema::Uuid => "uuid".to_string(),
        // Decimal is the most tricky. https://avro.apache.org/docs/1.11.1/specification/_print/#decimal
        // - A decimal logical type annotates Avro bytes _or_ fixed types.
        // - It has attributes `precision` and `scale`.
        //  "For the purposes of schema resolution, two schemas that are decimal logical types match if their scales and precisions match."
        // - When the physical type is fixed, it's a named type. And a schema containing 2 decimals is possible:
        //   [
        //     {"type":"fixed","name":"Decimal128","size":16,"logicalType":"decimal","precision":38,"scale":2},
        //     {"type":"fixed","name":"Decimal256","size":32,"logicalType":"decimal","precision":50,"scale":2}
        //   ]
        //   In this case (a logical type's physical type is a named type), perhaps we should use the physical type's `name`.
        Schema::Decimal(_) => "decimal".to_string(),
        Schema::Date => "date".to_string(),
        // Note: in Avro, the name style is "time-millis", etc.
        // But in RisingWave (Postgres), it will require users to use quotes, i.e.,
        // select (struct)."time-millis", (struct).time_millies from t;
        // The latter might be more user-friendly.
        Schema::TimeMillis => "time_millis".to_string(),
        Schema::TimeMicros => "time_micros".to_string(),
        Schema::TimestampMillis => "timestamp_millis".to_string(),
        Schema::TimestampMicros => "timestamp_micros".to_string(),
        Schema::LocalTimestampMillis => "local_timestamp_millis".to_string(),
        Schema::LocalTimestampMicros => "local_timestamp_micros".to_string(),
        Schema::Duration => "duration".to_string(),
*/
        Schema::Uuid
        | Schema::Decimal(_)
        | Schema::Date
        | Schema::TimeMillis
        | Schema::TimeMicros
        | Schema::TimestampMillis
        | Schema::TimestampMicros
        | Schema::LocalTimestampMillis
        | Schema::LocalTimestampMicros
        | Schema::Duration => {
            bail_not_implemented!(issue=17616, "Avro logicalType used in Union type: {:?}", schema)
        }
    })
}
