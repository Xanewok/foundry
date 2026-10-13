//! Functional consistency of opaque storage reads and keccak hashes.

use super::*;
use std::collections::BTreeMap;

/// Returns `inputs_i == inputs_j => value_i == value_j` for every pair of applications of one
/// function reachable from `constraints`.
///
/// An application's symbol is named by its input expressions, so two expressions with the same
/// value would otherwise read independent values. Omitting an axiom only admits spurious models;
/// it cannot turn a failing path into a passing one.
pub(super) fn application_congruence(
    cx: &mut SymCx,
    constraints: &[SymBoolExpr],
) -> Vec<SymBoolExpr> {
    let mut vars = SymbolicVars::default();
    for constraint in constraints {
        constraint.collect_vars(&mut vars);
    }

    // Inputs can contain further applications, so close over the symbols they mention.
    let mut groups = BTreeMap::<ApplicationKind, Vec<(Symbol, Arc<[SymExpr]>)>>::new();
    let mut seen = SymbolicVars::default();
    let mut pending = vars.into_iter().collect::<Vec<_>>();
    while let Some(symbol) = pending.pop() {
        let Some((kind, inputs)) = cx.application(symbol).cloned() else { continue };
        if !seen.insert(symbol) {
            continue;
        }
        for input in inputs.iter() {
            let _ = input.visit(&mut |expr| {
                pending.extend(expr.kind().get_var());
                ControlFlow::<()>::Continue(())
            });
        }
        groups.entry(kind).or_default().push((symbol, inputs));
    }

    let mut axioms = Vec::new();
    for group in groups.values_mut() {
        group.sort_unstable_by_key(|(symbol, _)| symbol.id());
        for (i, (left_symbol, left_inputs)) in group.iter().enumerate() {
            for (right_symbol, right_inputs) in &group[i + 1..] {
                if left_inputs.len() != right_inputs.len() {
                    continue;
                }
                let same_inputs = left_inputs
                    .iter()
                    .zip(right_inputs.iter())
                    .map(|(left, right)| SymBoolExpr::eq(cx, left.clone(), right.clone()))
                    .collect();
                let same_inputs = SymBoolExpr::and(cx, same_inputs);
                if same_inputs.as_const() == Some(false) {
                    continue;
                }
                let left = SymExpr::get_var(cx, *left_symbol);
                let right = SymExpr::get_var(cx, *right_symbol);
                let same_value = SymBoolExpr::eq(cx, left, right);
                let different_inputs = same_inputs.not(cx);
                axioms.push(SymBoolExpr::or(cx, vec![different_inputs, same_value]));
            }
        }
    }
    axioms
}
