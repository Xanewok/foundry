//! Quantifier-free axioms for the uninterpreted non-linear functions.
//!
//! Every axiom holds for the EVM's `mul` and `div` (wrapping, `x / 0 == 0`) whatever the
//! operands, so adding them to a query removes no real execution. A fact that needs the true
//! product is guarded by a sufficient no-overflow condition built from comparisons only, never
//! from a multiplication.

use super::*;

/// Operands are "narrow" below this many bits: the product of two narrow values cannot wrap.
const NARROW_BITS: usize = 128;
/// Multiplications whose pairs are related by monotonicity; pairs grow with the square.
const MAX_MONOTONE_PRODUCTS: usize = 16;
/// Applications whose operand text is longer are skipped; unfolded DAGs can be exponential.
const MAX_OPERAND_BYTES: usize = 4096;

pub(super) fn uf_axioms_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    uf_nonlinear_enabled()
        && *ON.get_or_init(|| std::env::var_os("FOUNDRY_SYMBOLIC_UF_AXIOMS").is_some())
}

struct Product {
    left: String,
    right: String,
}

impl Product {
    fn app(&self) -> String {
        format!("(__uf_mul {} {})", self.left, self.right)
    }
}

fn bv(value: U256) -> String {
    format!("(_ bv{value} 256)")
}

fn below_pow2(term: &str, bits: usize) -> String {
    format!("(bvult {term} {})", bv(U256::ONE << bits))
}

fn narrow(term: &str) -> String {
    below_pow2(term, NARROW_BITS)
}

fn imply(premise: &str, conclusion: &str) -> String {
    format!("(assert (=> {premise} {conclusion}))\n")
}

/// Axioms for each application in `applications` and each pair of multiplications.
///
/// Per `__uf_mul a b`: commutativity; `a = 0 or b = 0` gives 0; `a = 1` gives `b` and `b = 1`
/// gives `a`; for `(s, 128 - s)` in `{(32, 96), (64, 64), (96, 32)}`, `a < 2^s and b < 2^(128-s)`
/// gives a product below 2^128 (no wrap, so the integer bound holds).
/// Per `__uf_udiv n d`: `d = 0` gives 0; `d = 1` gives `n`; the quotient is at most `n`.
/// Per `__uf_udiv (__uf_mul x y) d` over narrow `x`, `y`: `d = x` gives `y` (and `d = y` gives
/// `x`) when the other factor is nonzero; `y <= d` bounds the quotient by `x`, and `x <= d` by `y`.
/// Per ordered pair of multiplications `p`, `q` with `q`'s factors narrow: if `p`'s factors are
/// pointwise at most `q`'s, in either order, `p <= q`. Since `q` does not wrap and `p`'s integer
/// product is at most `q`'s, `p` does not wrap either.
pub(super) fn uf_axioms(cx: &SymCx, applications: &[(SymBinOp, SymExpr, SymExpr)]) -> String {
    let mut seen: HashSet<String> = HashSet::new();
    let mut out = String::new();
    let mut emit = |axiom: String| {
        if seen.insert(axiom.clone()) {
            out.push_str(&axiom);
        }
    };
    let mut products: Vec<Product> = Vec::new();

    for (op, left, right) in applications {
        let (l, r) = (left.smt(cx), right.smt(cx));
        if l.len() > MAX_OPERAND_BYTES || r.len() > MAX_OPERAND_BYTES {
            continue;
        }
        match op {
            SymBinOp::Mul => {
                let product = Product { left: l, right: r };
                mul_axioms(&product, &mut emit);
                if !products.iter().any(|p| p.left == product.left && p.right == product.right) {
                    products.push(product);
                }
            }
            SymBinOp::UDiv => {
                let (n, d) = (&l, &r);
                let q = format!("(__uf_udiv {n} {d})");
                let zero = bv(U256::ZERO);
                emit(imply(&format!("(= {d} {zero})"), &format!("(= {q} {zero})")));
                emit(imply(&format!("(= {d} {})", bv(U256::ONE)), &format!("(= {q} {n})")));
                emit(format!("(assert (bvule {q} {n}))\n"));
                if let SymExprKind::BinOp(SymBinOp::Mul, x, y) = left.kind()
                    && SymBinOp::Mul.abstracts(x, y)
                {
                    div_of_product_axioms(cx, &q, (x, y), (right, &r), &mut emit);
                }
            }
            _ => {}
        }
    }

    for (i, p) in products.iter().enumerate().take(MAX_MONOTONE_PRODUCTS) {
        for (j, q) in products.iter().enumerate().take(MAX_MONOTONE_PRODUCTS) {
            if i == j {
                continue;
            }
            let below = |a: &str, b: &str, c: &str, d: &str| {
                format!("(and (bvule {a} {b}) (bvule {c} {d}))")
            };
            let straight = below(&p.left, &q.left, &p.right, &q.right);
            let swapped = below(&p.left, &q.right, &p.right, &q.left);
            let premise = format!(
                "(and (or {straight} {swapped}) {} {})",
                narrow(&q.left),
                narrow(&q.right)
            );
            emit(imply(&premise, &format!("(bvule {} {})", p.app(), q.app())));
        }
    }
    out
}

fn mul_axioms(p: &Product, emit: &mut impl FnMut(String)) {
    let (a, b, app) = (&p.left, &p.right, p.app());
    let zero = bv(U256::ZERO);
    let one = bv(U256::ONE);
    if a != b {
        emit(format!("(assert (= {app} (__uf_mul {b} {a})))\n"));
    }
    emit(imply(&format!("(or (= {a} {zero}) (= {b} {zero}))"), &format!("(= {app} {zero})")));
    emit(imply(&format!("(= {a} {one})"), &format!("(= {app} {b})")));
    emit(imply(&format!("(= {b} {one})"), &format!("(= {app} {a})")));
    for bits in [32, 64, 96] {
        let premise =
            format!("(and {} {})", below_pow2(a, bits), below_pow2(b, NARROW_BITS - bits));
        emit(imply(&premise, &narrow(&app)));
    }
}

fn div_of_product_axioms(
    cx: &SymCx,
    quotient: &str,
    (x, y): (&SymExpr, &SymExpr),
    (divisor, d): (&SymExpr, &str),
    emit: &mut impl FnMut(String),
) {
    let (xs, ys) = (x.smt(cx), y.smt(cx));
    let zero = bv(U256::ZERO);
    let both = format!("{} {}", narrow(&xs), narrow(&ys));
    if divisor == x {
        let premise = format!("(and {both} (not (= {xs} {zero})))");
        emit(imply(&premise, &format!("(= {quotient} {ys})")));
    }
    if divisor == y {
        let premise = format!("(and {both} (not (= {ys} {zero})))");
        emit(imply(&premise, &format!("(= {quotient} {xs})")));
    }
    emit(imply(&format!("(and {both} (bvule {ys} {d}))"), &format!("(bvule {quotient} {xs})")));
    emit(imply(&format!("(and {both} (bvule {xs} {d}))"), &format!("(bvule {quotient} {ys})")));
}

#[cfg(test)]
mod tests {
    use super::*;

    fn symbols(cx: &mut SymCx) -> (SymExpr, SymExpr, SymExpr) {
        (SymExpr::var(cx, "x"), SymExpr::var(cx, "y"), SymExpr::var(cx, "z"))
    }

    #[test]
    fn product_axioms_are_guarded_and_bounded() {
        let mut cx = SymCx::new();
        let (x, y, _) = symbols(&mut cx);
        let apps = [(SymBinOp::Mul, x.clone(), y.clone())];
        let out = uf_axioms(&cx, &apps);
        let (xs, ys) = (x.smt(&cx), y.smt(&cx));

        assert!(out.contains(&format!("(= (__uf_mul {xs} {ys}) (__uf_mul {ys} {xs}))")), "{out}");
        assert!(out.contains("(=> (or (= "), "{out}");
        // Only comparisons: no multiplication besides the uninterpreted function.
        assert!(!out.contains("bvmul") && !out.contains("zero_extend"), "{out}");
        assert_eq!(out.lines().count(), 1 + 1 + 2 + 3, "{out}");
        // One application has no pair.
        assert!(!out.contains("bvule (__uf_mul"), "{out}");
    }

    #[test]
    fn division_and_pair_axioms() {
        let mut cx = SymCx::new();
        let (x, y, z) = symbols(&mut cx);
        let xy = SymExpr::binop(&mut cx, SymBinOp::Mul, x.clone(), y.clone());
        let apps = [
            (SymBinOp::Mul, x.clone(), y.clone()),
            (SymBinOp::Mul, x.clone(), z.clone()),
            (SymBinOp::UDiv, xy.clone(), x.clone()),
        ];
        let out = uf_axioms(&cx, &apps);
        let (xs, ys, zs) = (x.smt(&cx), y.smt(&cx), z.smt(&cx));
        let q = format!("(__uf_udiv {} {xs})", xy.smt(&cx));

        assert!(out.contains(&format!("(= {q} {ys}))")), "div(x*y, x) = y\n{out}");
        assert!(out.contains(&format!("(bvule {q} {xs})")), "{out}");
        // Ordered pairs of the two products: (x*y <= x*z) and (x*z <= x*y), each with narrow guard.
        let pairs = out.lines().filter(|l| l.contains("(bvule (__uf_mul")).count();
        assert_eq!(pairs, 2, "{out}");
        assert!(out.contains(&format!("(bvule {ys} {zs})")), "{out}");
    }
}
