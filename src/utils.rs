use crate::slang::ast::{Expr, ExprKind, Op, Name};
use crate::slang::{Span};




pub fn conj_or_true(it: impl Iterator<Item = Expr>) -> Expr {
    it.reduce(|a, b| a & b).unwrap_or(Expr::bool(true))
}


/// Collect all "safety" guards required to evaluate an expression.
/// Example: for `a / (b - 1)` we get one guard `(b - 1) != 0`.
pub fn expr_safety_guards(expr: &Expr) -> Vec<(Expr, Span, String)> {
    let mut out = Vec::new();
    collect_guards(expr, &mut out);
    out
}

fn collect_guards(e: &Expr, out: &mut Vec<(Expr, Span, String)>) {
    match &e.kind {
        ExprKind::Infix(lhs, op, rhs) => {
            use Op::*;
            // Add safety condition for divisions and modulo
            match op {
                Div | Mod => {
                    let zero = Expr::num(0).with_span(rhs.span);
                    let guard = Expr::op(&(**rhs).clone(), Op::Ne, &zero);
                    out.push((guard, rhs.span, "possible division by zero".into()));
                }
                _ => {}
            }

            // Continue recursively
            collect_guards(lhs, out);
            collect_guards(rhs, out);
        }

        ExprKind::Prefix(_, inner) => collect_guards(inner, out),
        ExprKind::Ite(cond, t, f) => {
            collect_guards(cond, out);
            collect_guards(t, out);
            collect_guards(f, out);
        }

        ExprKind::FunctionCall { args, .. } => {
            for arg in args {
                collect_guards(arg, out);
            }
        }

        ExprKind::Quantifier(_, _vars, body) => {
            collect_guards(body, out);
        }

        _ => {}
    }
}

// subst: replace free occurrences of variable named `x` with `v`
pub fn subst_var_in_expr(e: &Expr, x: &String, v: &Expr) -> Expr {
    return e.subst_ident(&x, v);
}

pub fn subst_result_in_expr(e: &Expr, v: &Expr) -> Expr {
    return e.subst_result(v);
    
}

