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

mod schema;

use apache_avro::schema::{DecimalSchema, NamesRef, RecordSchema, ResolvedSchema, UnionSchema};
use apache_avro::types::{Value, ValueKind};
use apache_avro::{Decimal as AvroDecimal, Schema};
use itertools::Itertools;
use num_bigint::{BigInt, Sign};
use risingwave_common::array::{ListValue, StructValue};
use risingwave_common::types::{
    DataType, Date, DatumCow, Interval, JsonbVal, MapValue, ScalarImpl, Time, Timestamp,
    Timestamptz, ToOwnedDatum,
};
use risingwave_common::util::iter_util::ZipEqFast;

pub use self::schema::{avro_schema_to_column_descs, MapHandling, ResolvedAvroSchema};
use super::utils::extract_decimal;
use super::{bail_uncategorized, uncategorized, Access, AccessError, AccessResult};
use crate::decoder::avro::schema::avro_schema_to_struct_field_name;

// #[derive(Clone)]
/// Options for parsing an `AvroValue` into Datum, with an optional avro schema.
pub struct AvroParseOptions<'a> {
    /// Currently, this schema is only used for decimal.
    ///
    /// FIXME: In theory we should use resolved schema.
    /// e.g., it's possible that a field is a reference to a decimal or a record containing a decimal field.
    names: ResolvedSchema<'a>,
    // Strict Mode
    // If strict mode is disabled, an int64 can be parsed from an `AvroInt` (int32) value.
    // relax_numeric: bool,
}

impl<'a> AvroParseOptions<'a> {
    pub fn create(root_schema: &'a Schema) -> Self {
        Self {
            names: root_schema.try_into().unwrap(),
            // relax_numeric: true,
        }
    }
}

impl<'a> AvroParseOptions<'a> {
    /// Parse an avro value into expected type.
    ///
    /// 3 kinds of type info are used to parsing:
    /// - `type_expected`. The type that we expect the value is.
    /// - value type. The type info together with the value argument.
    /// - schema. The `AvroSchema` provided in option.
    ///
    /// Cases: (FIXME: Is this precise?)
    /// - If both `type_expected` and schema are provided, it will check both strictly.
    /// - If only `type_expected` is provided, it will try to match the value type and the
    ///    `type_expected`, converting the value if possible.
    /// - If only value is provided (without schema and `type_expected`),
    ///     the `DataType` will be inferred.
    fn convert_to_datum<'b>(
        names: &NamesRef<'a>,
        mut schema: &'a Schema,
        value: &'b Value,
        type_expected: &DataType,
    ) -> AccessResult<DatumCow<'b>>
    where
        'b: 'a,
    {
        let create_error = || AccessError::TypeError {
            expected: format!("{:?}", type_expected),
            got: format!("{:?}", value),
            value: String::new(),
        };

        macro_rules! borrowed {
            ($v:expr) => {
                return Ok(DatumCow::Borrowed(Some($v.into())))
            };
        }

        macro_rules! try_match_expand {
            ($e:expr, $variant:path) => {
                match $e {
                    $variant(internal) => Ok(internal),
                    _ => Err(AccessError::TypeError {
                        expected: type_expected.to_string(),
                        got: format!("{:?}", apache_avro::schema::SchemaKind::from(schema)),
                        value: format!("{:?}", apache_avro::types::ValueKind::from(value)),
                    }),
                }
            };
        }

        if let Schema::Ref { name } = schema {
            schema = names.get(name).ok_or_else(|| todo!()).unwrap();
        }

        let v: ScalarImpl = match schema {
            Schema::Ref { .. } => unreachable!(),
            Schema::Null => return Ok(DatumCow::NULL),
            // ---- Union (with >=2 non null variants), and nullable Union ([null, record]) -----
            Schema::Union(u) => {
                let Value::Union(variant, v) = value else {
                    unreachable!()
                };

                if let Some(inner) = get_nullable_union_inner(u) {
                    // nullable Union ([null, record])
                    return Self::convert_to_datum(names, inner, v, type_expected);
                }

                let variant_schema = &u.variants()[*variant as usize];
                let struct_type_info = try_match_expand!(type_expected, DataType::Struct)?;

                if matches!(variant_schema, &Schema::Null) {
                    return Ok(DatumCow::NULL);
                }

                // Here we compare the field name, instead of using the variant idx to find the field idx.
                // The latter approach might also work, but might be more error-prone.
                // We will need to get the index of the "null" variant, and then re-map the variant index to the field index.
                // XXX: probably we can unwrap here (if self.schema is correctly used)
                let expected_field_name = avro_schema_to_struct_field_name(variant_schema)?;

                let mut fields = Vec::with_capacity(struct_type_info.len());
                for (field_name, field_type) in struct_type_info.iter() {
                    if field_name == expected_field_name {
                        let datum = Self::convert_to_datum(names, variant_schema, v, field_type)?
                            .to_owned_datum();

                        fields.push(datum)
                    } else {
                        fields.push(None)
                    }
                }
                StructValue::new(fields).into()
            }
            // ---- Boolean -----
            Schema::Boolean => {
                let b = try_match_expand!(value, Value::Boolean)?;
                // let st = try_match_expand!(type_expected, DataType::Boolean)?;
                (*b).into()
            }
            // ---- Int32 -----
            Schema::Int => {
                let i = try_match_expand!(value, Value::Int)?;
                // let st = try_match_expand!(type_expected, DataType::Int32)?;
                (*i).into()
            }
            // ---- Int64 -----
            Schema::Long => {
                let i = try_match_expand!(value, Value::Long)?;
                // let st = try_match_expand!(type_expected, DataType::Int64)?;
                (*i).into()
            }
            // ---- Float32 -----
            Schema::Float => {
                let i = try_match_expand!(value, Value::Float)?;
                // let st = try_match_expand!(type_expected, DataType::Float32)?;
                (*i).into()
            }
            // ---- Float64 -----
            Schema::Double => {
                let i = try_match_expand!(value, Value::Double)?;
                // let st = try_match_expand!(type_expected, DataType::Float64)?;
                (*i).into()
            }
            // ---- Decimal -----
            Schema::Decimal(DecimalSchema {
                precision, scale, ..
            }) => {
                let avro_decimal = try_match_expand!(value, Value::Decimal)?;
                // let st = try_match_expand!(type_expected, DataType::Decimal)?;

                let decimal =
                    avro_decimal_to_rust_decimal(avro_decimal.clone(), *precision, *scale)
                        .map_err(|_| create_error())?;
                ScalarImpl::Decimal(risingwave_common::types::Decimal::Normalized(decimal))
            }
            // ---- Time -----
            Schema::TimeMillis => {
                let ms = try_match_expand!(value, Value::TimeMillis)?;
                // let st = try_match_expand!(type_expected, DataType::Time)?;
                Time::with_milli(*ms as u32)
                    .map_err(|_| create_error())?
                    .into()
            }
            Schema::TimeMicros => {
                let us = try_match_expand!(value, Value::TimeMicros)?;
                // let st = try_match_expand!(type_expected, DataType::Time)?;
                Time::with_micro(*us as u64)
                    .map_err(|_| create_error())?
                    .into()
            }
            // ---- Date -----
            Schema::Date => {
                let days = try_match_expand!(value, Value::Date)?;
                // let st = try_match_expand!(type_expected, DataType::Date)?;
                Date::with_days_since_unix_epoch(*days)
                    .map_err(|_| create_error())?
                    .into()
            }
            // ---- Varchar -----
            Schema::String => {
                let s = try_match_expand!(value, Value::String)?;
                // let st = try_match_expand!(type_expected, DataType::Varchar)?;
                borrowed!(s.as_str())
            }
            Schema::Enum { .. } => {
                let Value::Enum(_, symbol) = value else {
                    unreachable!()
                };
                // let st = try_match_expand!(type_expected, DataType::Varchar)?;
                borrowed!(symbol.as_str())
            }
            Schema::Uuid => {
                let uuid = try_match_expand!(value, Value::Uuid)?;
                // let st = try_match_expand!(type_expected, DataType::Varchar)?;
                uuid.as_hyphenated().to_string().into_boxed_str().into()
            }
            // ---- Timestamp -----
            Schema::LocalTimestampMillis => {
                let ms = try_match_expand!(value, Value::LocalTimestampMillis)?;
                // let st = try_match_expand!(type_expected, DataType::Timestamp)?;
                Timestamp::with_millis(*ms)
                    .map_err(|_| create_error())?
                    .into()
            }
            Schema::LocalTimestampMicros => {
                let us = try_match_expand!(value, Value::LocalTimestampMicros)?;
                // let st = try_match_expand!(type_expected, DataType::Timestamp)?;
                Timestamp::with_micros(*us)
                    .map_err(|_| create_error())?
                    .into()
            }
            // ---- TimestampTz -----
            Schema::TimestampMillis => {
                let ms = try_match_expand!(value, Value::TimestampMillis)?;
                // let st = try_match_expand!(type_expected, DataType::Timestamptz)?;
                Timestamptz::from_millis(*ms)
                    .ok_or_else(|| {
                        uncategorized!("timestamptz with milliseconds {ms} * 1000 is out of range")
                    })?
                    .into()
            }
            Schema::TimestampMicros => {
                let us = try_match_expand!(value, Value::TimestampMicros)?;
                // let st = try_match_expand!(type_expected, DataType::Timestamptz)?;
                Timestamptz::from_micros(*us).into()
            }
            // ---- Interval -----
            Schema::Duration => {
                let duration = try_match_expand!(value, Value::Duration)?;
                // let st = try_match_expand!(type_expected, DataType::Interval)?;
                let months = u32::from(duration.months()) as i32;
                let days = u32::from(duration.days()) as i32;
                let usecs = (u32::from(duration.millis()) as i64) * 1000; // never overflows
                ScalarImpl::Interval(Interval::from_month_day_usec(months, days, usecs))
            }
            // ---- Struct -----
            Schema::Record(record_schema) => {
                let value_fields = try_match_expand!(value, Value::Record)?;
                match type_expected {
                    DataType::Decimal => {
                        let fields = value_fields;
                        // VariableScaleDecimal has fixed fields, scale(int) and value(bytes)
                        let find_in_records =
                            |field_name: &str| {
                                fields
                        .iter()
                        .find(|field| field.0 == field_name)
                        .map(|field| &field.1)
                        .ok_or_else(|| {
                            uncategorized!("`{field_name}` field not found in VariableScaleDecimal")
                        })
                            };
                        let scale = match find_in_records("scale")? {
                            Value::Int(scale) => *scale,
                            avro_value => bail_uncategorized!(
                                "scale field in VariableScaleDecimal is not int, got {:?}",
                                avro_value
                            ),
                        };

                        let value: BigInt = match find_in_records("value")? {
                            Value::Bytes(bytes) => BigInt::from_signed_bytes_be(bytes),
                            avro_value => bail_uncategorized!(
                                "value field in VariableScaleDecimal is not bytes, got {:?}",
                                avro_value
                            ),
                        };

                        let negative = value.sign() == Sign::Minus;
                        let (lo, mid, hi) = extract_decimal(value.to_bytes_be().1)?;
                        let decimal =
                            rust_decimal::Decimal::from_parts(lo, mid, hi, negative, scale as u32);
                        ScalarImpl::Decimal(risingwave_common::types::Decimal::Normalized(decimal))
                    }
                    DataType::Struct(struct_type_info) => {
                        let descs = value_fields;
                        StructValue::new(
                            struct_type_info
                                .names()
                                .zip_eq_fast(struct_type_info.types())
                                .map(|(field_name, field_type)| {
                                    let maybe_value = descs.iter().find(|(k, _v)| k == field_name);
                                    if let Some((_, value)) = maybe_value {
                                        let schema =
                                            avro_extract_field_schema(record_schema, field_name)
                                                .unwrap();
                                        Ok(Self::convert_to_datum(
                                            names, schema, value, field_type,
                                        )?
                                        .to_owned_datum())
                                    } else {
                                        Ok(None)
                                    }
                                })
                                .collect::<Result<_, AccessError>>()?,
                        )
                        .into()
                    }
                    _ => unreachable!(),
                }
            }
            // ---- List -----
            Schema::Array(schema) => {
                let array = try_match_expand!(value, Value::Array)?;
                let item_type = try_match_expand!(type_expected, DataType::List)?;
                ListValue::new({
                    use std::ops::Deref as _;
                    let schema = schema.deref();
                    let mut builder = item_type.create_array_builder(array.len());
                    for v in array {
                        let value = Self::convert_to_datum(names, schema, v, item_type)?;
                        builder.append(value);
                    }
                    builder.finish()
                })
                .into()
            }
            // ---- Bytea -----
            Schema::Bytes => {
                let value = try_match_expand!(value, Value::Bytes)?;
                // let st = try_match_expand!(type_expected, DataType::Bytea)?;
                borrowed!(value.as_slice())
            }
            // ---- Jsonb -----
            Schema::Map(schema) => {
                match type_expected {
                    DataType::Jsonb => {
                        let v = value;
                        let mut builder = jsonbb::Builder::default();
                        avro_to_jsonb(v, &mut builder)?;
                        let jsonb = builder.finish();
                        debug_assert!(jsonb.as_ref().is_object());
                        JsonbVal::from(jsonb).into()
                    }
                    DataType::Map(map_type) => {
                        let map = try_match_expand!(value, Value::Map)?;
                        let mut builder = map_type
                            .clone()
                            .into_struct()
                            .create_array_builder(map.len());
                        // Since the map is HashMap, we can ensure
                        // key is non-null and unique, keys and values have the same length.

                        // NOTE: HashMap's iter order is non-deterministic, but MapValue's
                        // order matters. We sort by key here to have deterministic order
                        // in tests. We might consider removing this, or make all MapValue sorted
                        // in the future.
                        for (k, v) in map.iter().sorted_by_key(|(k, _v)| *k) {
                            let value_datum =
                                Self::convert_to_datum(names, schema, v, map_type.value())?
                                    .to_owned_datum();
                            builder.append(
                                StructValue::new(vec![Some(k.as_str().into()), value_datum])
                                    .to_owned_datum(),
                            );
                        }
                        let list = ListValue::new(builder.finish());
                        MapValue::from_entries(list).into()
                    }
                    _ => unreachable!(),
                }
            }
            Schema::Fixed(_) => Err(create_error())?,
        };
        Ok(DatumCow::Owned(Some(v)))
    }
}

pub struct AvroAccess<'a> {
    root_value: &'a Value,
    options: AvroParseOptions<'a>,
}

impl<'a> AvroAccess<'a> {
    pub fn new(root_value: &'a Value, options: AvroParseOptions<'a>) -> Self {
        Self {
            root_value,
            options,
        }
    }
}

impl Access for AvroAccess<'_> {
    fn access<'a>(&'a self, path: &[&str], type_expected: &DataType) -> AccessResult<DatumCow<'a>> {
        let mut value = self.root_value;
        let mut schema = self.options.names.get_schemata()[0];

        debug_assert!(
            path.len() == 1
                || (path.len() == 2 && matches!(path[0], "before" | "after" | "source")),
            "unexpected path access: {:?}",
            path
        );
        let mut i = 0;
        while i < path.len() {
            let key = path[i];
            let create_error = || AccessError::Undefined {
                name: key.to_string(),
                path: path.iter().take(i).join("."),
            };
            match value {
                Value::Union(_, v) => {
                    // The debezium "before" field is a nullable union.
                    // "fields": [
                    // {
                    //     "name": "before",
                    //     "type": [
                    //         "null",
                    //         {
                    //             "type": "record",
                    //             "name": "Value",
                    //             "fields": [...],
                    //         }
                    //     ],
                    //     "default": null
                    // },
                    // {
                    //     "name": "after",
                    //     "type": [
                    //         "null",
                    //         "Value"
                    //     ],
                    //     "default": null
                    // },
                    // ...]
                    value = v;
                    schema = avro_schema_skip_nullable_union(schema).unwrap();
                    continue;
                }
                Value::Record(fields) => {
                    if let Some((_, v)) = fields.iter().find(|(k, _)| k == key) {
                        value = v;

                        let Schema::Record(record_schema) = schema else {
                            unreachable!()
                        };
                        schema = avro_extract_field_schema(record_schema, key).unwrap();
                        i += 1;
                        continue;
                    }
                }
                _ => (),
            }
            Err(create_error())?;
        }

        let names = self.options.names.get_names();
        AvroParseOptions::convert_to_datum(names, schema, value, type_expected)
    }
}

pub(crate) fn avro_decimal_to_rust_decimal(
    avro_decimal: AvroDecimal,
    _precision: usize,
    scale: usize,
) -> AccessResult<rust_decimal::Decimal> {
    let negative = !avro_decimal.is_positive();
    let bytes = avro_decimal.to_vec_unsigned();

    let (lo, mid, hi) = extract_decimal(bytes)?;
    Ok(rust_decimal::Decimal::from_parts(
        lo,
        mid,
        hi,
        negative,
        scale as u32,
    ))
}

/// If the union schema is `[null, T]` or `[T, null]`, returns `Some(T)`; otherwise returns `None`.
fn get_nullable_union_inner(union_schema: &UnionSchema) -> Option<&'_ Schema> {
    let variants = union_schema.variants();
    // Note: `[null, null] is invalid`, we don't need to worry about that.
    if variants.len() == 2 && variants.contains(&Schema::Null) {
        let inner_schema = variants
            .iter()
            .find(|s| !matches!(s, &&Schema::Null))
            .unwrap();
        Some(inner_schema)
    } else {
        None
    }
}

pub fn avro_schema_skip_nullable_union(schema: &Schema) -> anyhow::Result<&Schema> {
    match schema {
        Schema::Union(union_schema) => match get_nullable_union_inner(union_schema) {
            Some(s) => Ok(s),
            None => Err(anyhow::format_err!(
                "illegal avro union schema, expected [null, T], got {:?}",
                union_schema
            )),
        },
        other => Ok(other),
    }
}

pub fn avro_extract_field_schema<'a>(
    schema: &'a RecordSchema,
    name: &str,
) -> anyhow::Result<&'a Schema> {
    let RecordSchema { fields, lookup, .. } = schema;
    let index = lookup
        .get(name)
        .ok_or_else(|| anyhow::format_err!("no field named '{}' in record: {:?}", name, schema))?;
    let field = fields
        .get(*index)
        .ok_or_else(|| anyhow::format_err!("illegal avro record schema {:?}", schema))?;
    Ok(&field.schema)
}

pub(crate) fn avro_to_jsonb(avro: &Value, builder: &mut jsonbb::Builder) -> AccessResult<()> {
    match avro {
        Value::Null => builder.add_null(),
        Value::Boolean(b) => builder.add_bool(*b),
        Value::Int(i) => builder.add_i64(*i as i64),
        Value::String(s) => builder.add_string(s),
        Value::Map(m) => {
            builder.begin_object();
            for (k, v) in m {
                builder.add_string(k);
                avro_to_jsonb(v, builder)?;
            }
            builder.end_object()
        }
        // same representation as map
        Value::Record(r) => {
            builder.begin_object();
            for (k, v) in r {
                builder.add_string(k);
                avro_to_jsonb(v, builder)?;
            }
            builder.end_object()
        }
        Value::Array(a) => {
            builder.begin_array();
            for v in a {
                avro_to_jsonb(v, builder)?;
            }
            builder.end_array()
        }

        // TODO: figure out where the following encoding is reasonable before enabling them.
        // See discussions: https://github.com/risingwavelabs/risingwave/pull/16948

        // jsonbb supports int64, but JSON spec does not allow it. How should we handle it?
        // BTW, protobuf canonical JSON converts int64 to string.
        // Value::Long(l) => builder.add_i64(*l),
        // Value::Float(f) => {
        //     if f.is_nan() || f.is_infinite() {
        //         // XXX: pad null or return err here?
        //         builder.add_null()
        //     } else {
        //         builder.add_f64(*f as f64)
        //     }
        // }
        // Value::Double(f) => {
        //     if f.is_nan() || f.is_infinite() {
        //         // XXX: pad null or return err here?
        //         builder.add_null()
        //     } else {
        //         builder.add_f64(*f)
        //     }
        // }
        // // XXX: What encoding to use?
        // // ToText is \x plus hex string.
        // Value::Bytes(b) => builder.add_string(&ToText::to_text(&b.as_slice())),
        // Value::Enum(_, symbol) => {
        //     builder.add_string(&symbol);
        // }
        // Value::Uuid(id) => builder.add_string(&id.as_hyphenated().to_string()),
        // // For Union, one concern is that the avro union is tagged (like rust enum) but json union is untagged (like c union).
        // // When the union consists of multiple records, it is possible to distinguish which variant is active in avro, but in json they will all become jsonb objects and indistinguishable.
        // Value::Union(_, v) => avro_to_jsonb(v, builder)?
        // XXX: pad null or return err here?
        v @ (Value::Long(_)
        | Value::Float(_)
        | Value::Double(_)
        | Value::Bytes(_)
        | Value::Enum(_, _)
        | Value::Fixed(_, _)
        | Value::Date(_)
        | Value::Decimal(_)
        | Value::TimeMillis(_)
        | Value::TimeMicros(_)
        | Value::TimestampMillis(_)
        | Value::TimestampMicros(_)
        | Value::LocalTimestampMillis(_)
        | Value::LocalTimestampMicros(_)
        | Value::Duration(_)
        | Value::Uuid(_)
        | Value::Union(_, _)) => {
            bail_uncategorized!(
                "unimplemented conversion from avro to jsonb: {:?}",
                ValueKind::from(v)
            )
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use apache_avro::{from_avro_datum, Decimal as AvroDecimal};
    use expect_test::expect;
    use risingwave_common::types::{Datum, Decimal};

    use super::*;

    /// Test the behavior of the Rust Avro lib for handling union with logical type.
    #[test]
    fn test_avro_lib_union() {
        // duplicate types
        let s = Schema::parse_str(r#"["null", "null"]"#);
        expect![[r#"
            Err(
                Unions cannot contain duplicate types,
            )
        "#]]
        .assert_debug_eq(&s);
        let s = Schema::parse_str(r#"["int", "int"]"#);
        expect![[r#"
            Err(
                Unions cannot contain duplicate types,
            )
        "#]]
        .assert_debug_eq(&s);
        // multiple map/array are considered as the same type, regardless of the element type!
        let s = Schema::parse_str(
            r#"[
"null",
{
    "type": "map",
    "values" : "long",
    "default": {}
},
{
    "type": "map",
    "values" : "int",
    "default": {}
}
]
"#,
        );
        expect![[r#"
            Err(
                Unions cannot contain duplicate types,
            )
        "#]]
        .assert_debug_eq(&s);
        let s = Schema::parse_str(
            r#"[
"null",
{
    "type": "array",
    "items" : "long",
    "default": {}
},
{
    "type": "array",
    "items" : "int",
    "default": {}
}
]
"#,
        );
        expect![[r#"
        Err(
            Unions cannot contain duplicate types,
        )
    "#]]
        .assert_debug_eq(&s);
        // multiple named types
        let s = Schema::parse_str(
            r#"[
"null",
{"type":"fixed","name":"a","size":16},
{"type":"fixed","name":"b","size":32}
]
"#,
        );
        expect![[r#"
            Ok(
                Union(
                    UnionSchema {
                        schemas: [
                            Null,
                            Fixed(
                                FixedSchema {
                                    name: Name {
                                        name: "a",
                                        namespace: None,
                                    },
                                    aliases: None,
                                    doc: None,
                                    size: 16,
                                    attributes: {},
                                },
                            ),
                            Fixed(
                                FixedSchema {
                                    name: Name {
                                        name: "b",
                                        namespace: None,
                                    },
                                    aliases: None,
                                    doc: None,
                                    size: 32,
                                    attributes: {},
                                },
                            ),
                        ],
                        variant_index: {
                            Null: 0,
                        },
                    },
                ),
            )
        "#]]
        .assert_debug_eq(&s);

        // union in union
        let s = Schema::parse_str(r#"["int", ["null", "int"]]"#);
        expect![[r#"
            Err(
                Unions may not directly contain a union,
            )
        "#]]
        .assert_debug_eq(&s);

        // logical type
        let s = Schema::parse_str(r#"["null", {"type":"string","logicalType":"uuid"}]"#).unwrap();
        expect![[r#"
            Union(
                UnionSchema {
                    schemas: [
                        Null,
                        Uuid,
                    ],
                    variant_index: {
                        Null: 0,
                        Uuid: 1,
                    },
                },
            )
        "#]]
        .assert_debug_eq(&s);
        // Note: Java Avro lib rejects this (logical type unions with its physical type)
        let s = Schema::parse_str(r#"["string", {"type":"string","logicalType":"uuid"}]"#).unwrap();
        expect![[r#"
            Union(
                UnionSchema {
                    schemas: [
                        String,
                        Uuid,
                    ],
                    variant_index: {
                        String: 0,
                        Uuid: 1,
                    },
                },
            )
        "#]]
        .assert_debug_eq(&s);
        // Note: Java Avro lib rejects this (logical type unions with its physical type)
        let s = Schema::parse_str(r#"["int", {"type":"int", "logicalType": "date"}]"#).unwrap();
        expect![[r#"
            Union(
                UnionSchema {
                    schemas: [
                        Int,
                        Date,
                    ],
                    variant_index: {
                        Int: 0,
                        Date: 1,
                    },
                },
            )
        "#]]
        .assert_debug_eq(&s);
        // Note: Java Avro lib allows this (2 decimal with different "name")
        let s = Schema::parse_str(
            r#"[
{"type":"fixed","name":"Decimal128","size":16,"logicalType":"decimal","precision":38,"scale":2},
{"type":"fixed","name":"Decimal256","size":32,"logicalType":"decimal","precision":50,"scale":2}
]"#,
        );
        expect![[r#"
            Err(
                Unions cannot contain duplicate types,
            )
        "#]]
        .assert_debug_eq(&s);
    }

    #[test]
    fn test_avro_lib_union_record_bug() {
        // multiple named types (record)
        let s = Schema::parse_str(
            r#"
    {
      "type": "record",
      "name": "Root",
      "fields": [
        {
          "name": "unionTypeComplex",
          "type": [
            "null",
            {"type": "record", "name": "Email","fields": [{"name":"inner","type":"string"}]},
            {"type": "record", "name": "Fax","fields": [{"name":"inner","type":"int"}]},
            {"type": "record", "name": "Sms","fields": [{"name":"inner","type":"int"}]}
          ]
        }
      ]
    }
        "#,
        )
        .unwrap();

        let bytes = hex::decode("060c").unwrap();
        // Correct should be variant 3 (Sms)
        let correct_value = from_avro_datum(&s, &mut bytes.as_slice(), None);
        expect![[r#"
                Ok(
                    Record(
                        [
                            (
                                "unionTypeComplex",
                                Union(
                                    3,
                                    Record(
                                        [
                                            (
                                                "inner",
                                                Int(
                                                    6,
                                                ),
                                            ),
                                        ],
                                    ),
                                ),
                            ),
                        ],
                    ),
                )
            "#]]
        .assert_debug_eq(&correct_value);
        // Bug: We got variant 2 (Fax) here, if we pass the reader schema.
        let wrong_value = from_avro_datum(&s, &mut bytes.as_slice(), Some(&s));
        expect![[r#"
                Ok(
                    Record(
                        [
                            (
                                "unionTypeComplex",
                                Union(
                                    2,
                                    Record(
                                        [
                                            (
                                                "inner",
                                                Int(
                                                    6,
                                                ),
                                            ),
                                        ],
                                    ),
                                ),
                            ),
                        ],
                    ),
                )
            "#]]
        .assert_debug_eq(&wrong_value);

        // The bug below can explain what happened.
        // The two records below are actually incompatible: https://avro.apache.org/docs/1.11.1/specification/_print/#schema-resolution
        // > both schemas are records with the _same (unqualified) name_
        // In from_avro_datum, it first reads the value with the writer schema, and then
        // it just uses the reader schema to interpret the value.
        // The value doesn't have record "name" information. So it wrongly passed the conversion.
        // The correct way is that we need to use both the writer and reader schema in the second step to interpret the value.

        let s = Schema::parse_str(
            r#"
    {
      "type": "record",
      "name": "Root",
      "fields": [
        {
          "name": "a",
          "type": "int"
        }
      ]
    }
        "#,
        )
        .unwrap();
        let s2 = Schema::parse_str(
            r#"
{
  "type": "record",
  "name": "Root222",
  "fields": [
    {
      "name": "a",
      "type": "int"
    }
  ]
}
    "#,
        )
        .unwrap();

        let bytes = hex::decode("0c").unwrap();
        let value = from_avro_datum(&s, &mut bytes.as_slice(), Some(&s2));
        expect![[r#"
            Ok(
                Record(
                    [
                        (
                            "a",
                            Int(
                                6,
                            ),
                        ),
                    ],
                ),
            )
        "#]]
        .assert_debug_eq(&value);
    }

    #[test]
    fn test_convert_decimal() {
        // 280
        let v = vec![1, 24];
        let avro_decimal = AvroDecimal::from(v);
        let rust_decimal = avro_decimal_to_rust_decimal(avro_decimal, 28, 0).unwrap();
        assert_eq!(rust_decimal, rust_decimal::Decimal::from(280));

        // 28.1
        let v = vec![1, 25];
        let avro_decimal = AvroDecimal::from(v);
        let rust_decimal = avro_decimal_to_rust_decimal(avro_decimal, 28, 1).unwrap();
        assert_eq!(rust_decimal, rust_decimal::Decimal::try_from(28.1).unwrap());

        // 1.1234567891
        let value = BigInt::from(11234567891_i64);
        let negative = value.sign() == Sign::Minus;
        let (lo, mid, hi) = extract_decimal(value.to_bytes_be().1).unwrap();
        let decimal = rust_decimal::Decimal::from_parts(lo, mid, hi, negative, 10);
        assert_eq!(
            decimal,
            rust_decimal::Decimal::try_from(1.1234567891).unwrap()
        );

        // 1.123456789123456789123456789
        let v = vec![3, 161, 77, 58, 146, 180, 49, 220, 100, 4, 95, 21];
        let avro_decimal = AvroDecimal::from(v);
        let rust_decimal = avro_decimal_to_rust_decimal(avro_decimal, 28, 27).unwrap();
        assert_eq!(
            rust_decimal,
            rust_decimal::Decimal::from_str("1.123456789123456789123456789").unwrap()
        );
    }

    /// Convert Avro value to datum.For now, support the following [Avro type](https://avro.apache.org/docs/current/spec.html).
    ///  - boolean
    ///  - int : i32
    ///  - long: i64
    ///  - float: f32
    ///  - double: f64
    ///  - string: String
    ///  - Date (the number of days from the unix epoch, 1970-1-1 UTC)
    ///  - Timestamp (the number of milliseconds from the unix epoch,  1970-1-1 00:00:00.000 UTC)
    fn from_avro_value(
        value: Value,
        value_schema: &Schema,
        shape: &DataType,
    ) -> anyhow::Result<Datum> {
        Ok(
            AvroParseOptions::convert_to_datum(&Default::default(), value_schema, &value, shape)?
                .to_owned_datum(),
        )
    }

    #[test]
    fn test_avro_timestamptz_micros() {
        let v1 = Value::TimestampMicros(1620000000000000);
        let v2 = Value::TimestampMillis(1620000000000);
        let value_schema1 = Schema::TimestampMicros;
        let value_schema2 = Schema::TimestampMillis;
        let datum1 = from_avro_value(v1, &value_schema1, &DataType::Timestamptz).unwrap();
        let datum2 = from_avro_value(v2, &value_schema2, &DataType::Timestamptz).unwrap();
        assert_eq!(
            datum1,
            Some(ScalarImpl::Timestamptz(
                Timestamptz::from_str("2021-05-03T00:00:00Z").unwrap()
            ))
        );
        assert_eq!(
            datum2,
            Some(ScalarImpl::Timestamptz(
                Timestamptz::from_str("2021-05-03T00:00:00Z").unwrap()
            ))
        );
    }

    #[test]
    fn test_decimal_truncate() {
        let schema = Schema::parse_str(
            r#"
            {
                "type": "bytes",
                "logicalType": "decimal",
                "precision": 38,
                "scale": 18
            }
            "#,
        )
        .unwrap();
        let bytes = vec![0x3f, 0x3f, 0x3f, 0x3f, 0x3f, 0x3f, 0x3f];
        let value = Value::Decimal(AvroDecimal::from(bytes));
        let resp = AvroParseOptions::convert_to_datum(
            &Default::default(),
            &schema,
            &value,
            &DataType::Decimal,
        )
        .unwrap()
        .to_owned_datum();
        assert_eq!(
            resp,
            Some(ScalarImpl::Decimal(Decimal::Normalized(
                rust_decimal::Decimal::from_str("0.017802464409370431").unwrap()
            )))
        );
    }

    #[test]
    fn test_variable_scale_decimal() {
        let schema = Schema::parse_str(
            r#"
            {
                "type": "record",
                "name": "VariableScaleDecimal",
                "namespace": "io.debezium.data",
                "fields": [
                    {
                        "name": "scale",
                        "type": "int"
                    },
                    {
                        "name": "value",
                        "type": "bytes"
                    }
                ]
            }
            "#,
        )
        .unwrap();
        let value = Value::Record(vec![
            ("scale".to_string(), Value::Int(0)),
            ("value".to_string(), Value::Bytes(vec![0x01, 0x02, 0x03])),
        ]);

        let resp = AvroParseOptions::convert_to_datum(
            &Default::default(),
            &schema,
            &value,
            &DataType::Decimal,
        )
        .unwrap()
        .to_owned_datum();
        assert_eq!(resp, Some(ScalarImpl::Decimal(Decimal::from(66051))));
    }
}
