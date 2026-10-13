//! Functional consistency of opaque storage reads and keccak hashes.

use super::*;
use std::collections::BTreeMap;

/// Whether two inputs are unequal under collision-free hashing: unequal constants, a hash against a
/// constant, or hashes of different preimages. Skipping their axioms only admits spurious models.
fn differ(left: &SymExpr, right: &SymExpr) -> bool {
    match (left.kind(), right.kind()) {
        (SymExprKind::Const(l), SymExprKind::Const(r)) => l != r,
        (SymExprKind::Keccak { .. }, SymExprKind::Const(_))
        | (SymExprKind::Const(_), SymExprKind::Keccak { .. }) => true,
        (
            SymExprKind::Keccak { len: ll, bytes: lb, .. },
            SymExprKind::Keccak { len: rl, bytes: rb, .. },
        ) => match (ll.as_const(), rl.as_const()) {
            (Some(l), Some(r)) => {
                let len = usize::try_from(l).unwrap_or(usize::MAX);
                l != r || lb.iter().zip(rb.iter()).take(len).any(|(l, r)| differ(l, r))
            }
            _ => false,
        },
        _ => false,
    }
}

/// Whether `from`'s inputs mention `to`, directly or through other applications. Such a pair
/// never has equal inputs unless a hash collides, and hash chains would need quadratic axioms.
fn depends_on(deps: &HashMap<Symbol, Vec<Symbol>>, from: Symbol, to: Symbol) -> bool {
    let mut stack = vec![from];
    let mut visited = SymbolicVars::default();
    while let Some(symbol) = stack.pop() {
        for &next in deps.get(&symbol).into_iter().flatten() {
            if next == to {
                return true;
            }
            if visited.insert(next) {
                stack.push(next);
            }
        }
    }
    false
}

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
        constraint.visit_bool(|expr| {
            vars.extend(expr.kind().get_var());
            false
        });
    }

    // Inputs can contain further applications, so close over the symbols they mention.
    let mut groups = BTreeMap::<ApplicationKind, Vec<(Symbol, Arc<[SymExpr]>)>>::new();
    let mut seen = SymbolicVars::default();
    let mut deps = HashMap::<Symbol, Vec<Symbol>>::default();
    let mut pending = vars.into_iter().collect::<Vec<_>>();
    while let Some(symbol) = pending.pop() {
        let Some((kind, inputs)) = cx.application(symbol).cloned() else { continue };
        if !seen.insert(symbol) {
            continue;
        }
        let mentioned = deps.entry(symbol).or_default();
        for input in inputs.iter() {
            input.visit_bool(|expr| {
                mentioned.extend(expr.kind().get_var());
                false
            });
        }
        pending.extend(mentioned.iter().copied());
        groups.entry(kind).or_default().push((symbol, inputs));
    }

    let mut axioms = Vec::new();
    for group in groups.values_mut() {
        group.sort_unstable_by_key(|(symbol, _)| symbol.id());
        for (i, (left_symbol, left_inputs)) in group.iter().enumerate() {
            for (right_symbol, right_inputs) in &group[i + 1..] {
                if left_inputs.len() != right_inputs.len()
                    || depends_on(&deps, *right_symbol, *left_symbol)
                    || depends_on(&deps, *left_symbol, *right_symbol)
                    || left_inputs.iter().zip(right_inputs.iter()).any(|(l, r)| differ(l, r))
                {
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
