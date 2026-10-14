//! Counterexample-guided refinement of the uninterpreted non-linear abstraction.

use super::*;

const DEFAULT_ROUNDS: usize = 4;

/// Refinement rounds after the first query; zero unless the abstraction is on.
pub(super) fn refine_rounds() -> usize {
    if !uf_nonlinear_enabled() {
        return 0;
    }
    std::env::var("FOUNDRY_SYMBOLIC_UF_REFINE_ROUNDS")
        .ok()
        .and_then(|rounds| rounds.parse().ok())
        .unwrap_or(DEFAULT_ROUNDS)
}

/// Whether a model request whose abstract model is spurious is retried with exact arithmetic.
pub(super) fn exact_fallback_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    uf_nonlinear_enabled()
        && *ON.get_or_init(|| std::env::var_os("FOUNDRY_SYMBOLIC_UF_EXACT_FALLBACK").is_some())
}

/// Every abstracted `op(left, right)` reachable from `constraints`.
pub(super) fn uf_applications(constraints: &[SymBoolExpr]) -> Vec<(SymBinOp, SymExpr, SymExpr)> {
    let mut applications = Vec::new();
    for constraint in constraints {
        constraint.visit_bool(|expr| {
            if let SymExprKind::BinOp(op, left, right) = expr.kind()
                && op.abstracts(left, right)
            {
                applications.push((*op, left.clone(), right.clone()));
            }
            false
        });
    }
    applications
}

/// Returns `(= (__uf_op a b) (op a b))` assertions for the operand values `model` gives each
/// application not already in `seen`.
///
/// Each assertion holds for the real operator, and the right side is the solver's own bit-vector
/// operator, so adding them only removes models that the precise encoding also excludes.
pub(super) fn instantiation_lemmas(
    applications: &[(SymBinOp, SymExpr, SymExpr)],
    model: &SymbolicModel,
    seen: &mut HashSet<(SymBinOp, U256, U256)>,
) -> String {
    let mut lemmas = String::new();
    for (op, left, right) in applications {
        let Some(uf) = op.uf_name() else { continue };
        let (Ok(left), Ok(right)) = (left.eval_model(model), right.eval_model(model)) else {
            continue;
        };
        if !seen.insert((*op, left, right)) {
            continue;
        }
        let real = op.smt();
        let _ = writeln!(
            lemmas,
            "(assert (= ({uf} (_ bv{left} 256) (_ bv{right} 256)) \
             ({real} (_ bv{left} 256) (_ bv{right} 256))))"
        );
    }
    lemmas
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn collects_only_symbolic_applications() {
        let mut cx = SymCx::new();
        let x = SymExpr::var(&mut cx, "x");
        let y = SymExpr::var(&mut cx, "y");
        let three = SymExpr::constant(&mut cx, U256::from(3));

        let product = SymExpr::binop(&mut cx, SymBinOp::Mul, x.clone(), y);
        let scaled = SymExpr::binop(&mut cx, SymBinOp::Mul, x, three.clone());
        let constraints = [
            SymBoolExpr::eq(&mut cx, product, three.clone()),
            SymBoolExpr::eq(&mut cx, scaled, three),
        ];

        let applications = uf_applications(&constraints);
        assert_eq!(applications.len(), 1);
        assert_eq!(applications[0].0, SymBinOp::Mul);
    }

    #[test]
    fn exact_arithmetic_scope_nests_and_restores() {
        assert!(!exact_arithmetic_active());
        with_exact_arithmetic(|| {
            with_exact_arithmetic(|| assert!(exact_arithmetic_active()));
            assert!(exact_arithmetic_active());
        });
        assert!(!exact_arithmetic_active());
    }

    #[test]
    fn exact_arithmetic_query_text_has_no_uninterpreted_symbols() {
        let mut cx = SymCx::new();
        let x = SymExpr::var(&mut cx, "x");
        let y = SymExpr::var(&mut cx, "y");
        let six = SymExpr::constant(&mut cx, U256::from(6));
        let product = SymExpr::binop(&mut cx, SymBinOp::Mul, x, y);
        let constraint = SymBoolExpr::eq(&mut cx, product, six);

        let mut smt = String::new();
        with_exact_arithmetic(|| write_smt_assertions(&cx, &mut smt, &[constraint]).unwrap());
        assert!(smt.contains("bvmul") && !smt.contains("__uf_"), "{smt}");
    }

    #[test]
    fn lemmas_instantiate_the_model_once() {
        let mut cx = SymCx::new();
        let x = SymExpr::var(&mut cx, "x");
        let y = SymExpr::var(&mut cx, "y");
        let six = SymExpr::constant(&mut cx, U256::from(6));
        let product = SymExpr::binop(&mut cx, SymBinOp::Mul, x.clone(), y.clone());
        let constraints = [SymBoolExpr::eq(&mut cx, product, six)];
        let applications = uf_applications(&constraints);

        let mut model = SymbolicModel::default();
        model.insert(x.kind().get_var().unwrap(), U256::from(2));
        model.insert(y.kind().get_var().unwrap(), U256::from(2));

        let mut seen = HashSet::default();
        let lemmas = instantiation_lemmas(&applications, &model, &mut seen);
        assert_eq!(
            lemmas,
            "(assert (= (__uf_mul (_ bv2 256) (_ bv2 256)) (bvmul (_ bv2 256) (_ bv2 256))))\n"
        );
        assert!(instantiation_lemmas(&applications, &model, &mut seen).is_empty());

        model.insert(y.kind().get_var().unwrap(), U256::from(3));
        let lemmas = instantiation_lemmas(&applications, &model, &mut seen);
        assert!(lemmas.contains("__uf_mul") && lemmas.contains("bv3"), "{lemmas}");
    }
}
