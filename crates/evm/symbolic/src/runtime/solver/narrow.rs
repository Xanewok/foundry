//! Native-width SMT declarations for symbols bounded by a `Ult(var, 2^w)` conjunct.
//!
//! Contract: the narrow declaration plus the zero-extending alias must admit exactly the
//! 256-bit values the dropped range conjunct admitted, so satisfiability is unchanged.

use super::*;

pub(super) const NARROW_SUFFIX: &str = "__n";

pub(super) fn narrow_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("FOUNDRY_SYMBOLIC_NARROW").is_some_and(|v| v == "1"))
}

/// Only plain `Var` symbols qualify: keccak, hash and gasleft leaves share `collect_vars`.
fn range_fact(constraint: &SymBoolExpr) -> Option<(Symbol, usize)> {
    let SymBoolExprKind::Cmp(SymCmpOp::Ult, left, right) = constraint.kind() else { return None };
    let SymExprKind::Var(symbol) = left.kind() else { return None };
    let bound = right.as_const()?;
    // `Ult(x, 1)` would need a zero-width vector; leave it to the solver.
    (bound.count_ones() == 1 && bound != U256::ONE).then(|| (*symbol, bound.trailing_zeros()))
}

/// Smallest `w` per symbol, empty when `enabled` is false.
pub(super) fn narrow_widths(enabled: bool, constraints: &[SymBoolExpr]) -> HashMap<Symbol, usize> {
    let mut widths = HashMap::default();
    if enabled {
        for (symbol, width) in constraints.iter().filter_map(range_fact) {
            let slot = widths.entry(symbol).or_insert(width);
            *slot = (*slot).min(width);
        }
    }
    widths
}

/// True for the conjunct that the narrow declaration of its symbol makes redundant.
pub(super) fn is_implied_by_width(
    widths: &HashMap<Symbol, usize>,
    constraint: &SymBoolExpr,
) -> bool {
    range_fact(constraint).is_some_and(|(symbol, width)| widths.get(&symbol) == Some(&width))
}

pub(super) fn write_declaration(out: &mut String, name: &str, width: Option<usize>) {
    match width {
        None => {
            let _ = writeln!(out, "(declare-fun {name} () (_ BitVec 256))");
        }
        Some(width) => {
            let extend = 256 - width;
            let _ = writeln!(out, "(declare-fun {name}{NARROW_SUFFIX} () (_ BitVec {width}))");
            let _ = writeln!(
                out,
                "(define-fun {name} () (_ BitVec 256) ((_ zero_extend {extend}) {name}{NARROW_SUFFIX}))"
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture() -> ([Symbol; 2], Vec<SymBoolExpr>) {
        let mut cx = SymCx::new();
        let a = SymExpr::var(&mut cx, "a");
        let b = SymExpr::var(&mut cx, "b");
        let range = SymBoolExpr::cmp_word_const(&mut cx, SymCmpOp::Ult, &a, U256::ONE << 32);
        let other = SymBoolExpr::cmp_word_const(&mut cx, SymCmpOp::Ult, &b, U256::from(100));
        ([cx.intern("a"), cx.intern("b")], vec![range, other])
    }

    fn declarations(symbols: [Symbol; 2], widths: &HashMap<Symbol, usize>) -> String {
        let mut out = String::new();
        for (name, symbol) in ["a", "b"].into_iter().zip(symbols) {
            write_declaration(&mut out, name, widths.get(&symbol).copied());
        }
        out
    }

    #[test]
    fn flag_unset_declares_everything_at_256_bits() {
        let (symbols, constraints) = fixture();
        let widths = narrow_widths(false, &constraints);
        assert!(widths.is_empty());
        assert_eq!(
            declarations(symbols, &widths),
            "(declare-fun a () (_ BitVec 256))\n(declare-fun b () (_ BitVec 256))\n"
        );
        assert!(!constraints.iter().any(|c| is_implied_by_width(&widths, c)));
    }

    #[test]
    fn flag_set_declares_power_of_two_bound_at_native_width() {
        let (symbols, constraints) = fixture();
        let widths = narrow_widths(true, &constraints);
        assert_eq!(
            declarations(symbols, &widths),
            "(declare-fun a__n () (_ BitVec 32))\n\
             (define-fun a () (_ BitVec 256) ((_ zero_extend 224) a__n))\n\
             (declare-fun b () (_ BitVec 256))\n"
        );
        assert!(is_implied_by_width(&widths, &constraints[0]));
        assert!(!is_implied_by_width(&widths, &constraints[1]));
    }

    #[test]
    fn model_value_of_narrow_symbol_is_read_back_through_alias() {
        let mut cx = SymCx::new();
        let a = SymExpr::var(&mut cx, "a");
        let constraint = SymBoolExpr::cmp_word_const(&mut cx, SymCmpOp::Ult, &a, U256::ONE << 32);
        let symbol = cx.intern("a");
        let output = "sat\n(\n  (define-fun a__n () (_ BitVec 32) #x0000002a)\n)\n";

        let on = model_symbols_with_narrow(&cx, &[constraint.clone()], true);
        let model = parse_model_with_symbols(output, &on).unwrap();
        assert_eq!(model.get(&symbol), Some(&U256::from(42)));

        let off = model_symbols_with_narrow(&cx, &[constraint], false);
        assert!(parse_model_with_symbols(output, &off).unwrap().is_empty());
    }
}
