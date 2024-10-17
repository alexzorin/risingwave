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

use risingwave_pb::plan_common::JoinType;

use super::{BoxedRule, OResult, Rule};
use crate::optimizer::plan_node::{LogicalJoin, LogicalValues};
use crate::optimizer::PlanRef;

/// Eliminate trivial cross join generated by subquery unnesting.
///
/// Before:
///
/// ```text
///             LogicalJoin (join type: inner, on condition: true)
///             /      \
///          Input    Value (with one row but no columns)
/// ```
///
/// After:
///
///
/// ```text
///              Input
/// ```
pub struct CrossJoinEliminateRule {}
impl Rule for CrossJoinEliminateRule {
    fn apply(&self, plan: PlanRef) -> OResult<PlanRef> {
        let join: &LogicalJoin = plan.as_logical_join()?;
        let (left, right, on, join_type, _output_indices) = join.clone().decompose();
        let values: &LogicalValues = right.as_logical_values()?;
        if on.always_true() // cross join
            && join_type == JoinType::Inner
            && values.rows().len() == 1 // one row
            && values.rows()[0].is_empty() // no columns
            && join.output_indices_are_trivial()
        {
            OResult::Ok(left)
        } else {
            OResult::NotApplicable
        }
    }
}

impl CrossJoinEliminateRule {
    pub fn create() -> BoxedRule {
        Box::new(CrossJoinEliminateRule {})
    }
}
