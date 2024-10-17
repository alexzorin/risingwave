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

use super::super::plan_node::*;
use super::{BoxedRule, OResult, Rule};
use crate::expr::{ExprImpl, ExprRewriter, ExprVisitor};
use crate::optimizer::plan_expr_visitor::InputRefCounter;
use crate::utils::Substitute;

/// Merge contiguous [`LogicalProject`] nodes.
pub struct ProjectMergeRule {}
impl Rule for ProjectMergeRule {
    fn apply(&self, plan: PlanRef) -> OResult<PlanRef> {
        let outer_project: &LogicalProject = plan.as_logical_project()?;
        let input = outer_project.input();
        let inner_project: &LogicalProject = input.as_logical_project()?;

        let mut input_ref_counter = InputRefCounter::default();
        for expr in outer_project.exprs() {
            input_ref_counter.visit_expr(expr);
        }
        // bail out if it is a project generated by `CommonSubExprExtractRule`.
        for (index, count) in &input_ref_counter.counter {
            if *count > 1 && matches!(inner_project.exprs()[*index], ExprImpl::FunctionCall(_)) {
                return OResult::NotApplicable;
            }
        }

        let mut subst = Substitute {
            mapping: inner_project.exprs().clone(),
        };
        let exprs = outer_project
            .exprs()
            .iter()
            .cloned()
            .map(|expr| subst.rewrite_expr(expr))
            .collect();
        OResult::Ok(LogicalProject::new(inner_project.input(), exprs).into())
    }
}

impl ProjectMergeRule {
    pub fn create() -> BoxedRule {
        Box::new(ProjectMergeRule {})
    }
}
