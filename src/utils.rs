use crate::slang::ast::{Expr, ExprKind, Op, Name};
use crate::slang::{Span};
use crate::slang::ast::{CmdKind, Cmd};



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
    match &e.kind {
        // ident -> v
        ExprKind::Ident(y) => {
            if y == x { v.clone().with_span(e.span) } else { e.clone() }
        }

        // (lhs op rhs)
        ExprKind::Infix(lhs, op, rhs) => {
            let l = subst_var_in_expr(lhs, x, v);
            let r = subst_var_in_expr(rhs, x, v);
            Expr::op(&l, op.clone(), &r).with_span(e.span)
        }

        // op e
        ExprKind::Prefix(op, inner) => {
            let i = subst_var_in_expr(inner, x, v);
            Expr::prefix(&i, op.clone()).with_span(e.span)
        }

        // ite(c, t, f)
        ExprKind::Ite(c, t, f) => {
            let c2 = subst_var_in_expr(c, x, v);
            let t2 = subst_var_in_expr(t, x, v);
            let f2 = subst_var_in_expr(f, x, v);
            Expr::ite(&c2, &t2, &f2).with_span(e.span)
        }

        // everything else unchanged for now (calls/quantifiers can be added next)
        _ => e.clone(),
    }
}

pub fn subst_result_in_expr(e: &Expr, v: &Expr) -> Expr {
    match &e.kind {
        ExprKind::Result => {
            v.clone().with_span(e.span)
        }

        // (lhs op rhs)
        ExprKind::Infix(lhs, op, rhs) => {
            let l = subst_result_in_expr(lhs, v);
            let r = subst_result_in_expr(rhs, v);
            Expr::op(&l, op.clone(), &r).with_span(e.span)
        }

        // op e
        ExprKind::Prefix(op, inner) => {
            let i = subst_result_in_expr(inner, v);
            Expr::prefix(&i, op.clone()).with_span(e.span)
        }

        // ite(c, t, f)
        ExprKind::Ite(c, t, f) => {
            let c2 = subst_result_in_expr(c, v);
            let t2 = subst_result_in_expr(t, v);
            let f2 = subst_result_in_expr(f, v);
            Expr::ite(&c2, &t2, &f2).with_span(e.span)
        }

        // everything else unchanged for now (calls/quantifiers can be added next)
        _ => e.clone(),
    }
}

/// Collect the syntactic write set of a command (variables that can be assigned in `c`).
pub fn modified_vars(c: &Cmd, out: &mut Vec<Name>) {
    match &c.kind {
        CmdKind::Assignment { name, .. } => {
            if !out.contains(name) { out.push(name.clone()); }
        }
        CmdKind::VarDefinition { name, .. } => {
            // if your IVL treats uninitialized var as write, include it; optional
            if !out.contains(name) { out.push(name.clone()); }
        }
        CmdKind::Seq(left,right) => {
            modified_vars(&left, out);
            modified_vars(&right, out);
        }
        CmdKind::MethodCall { name, .. } => {
            match name {
                None => {}
                Some(n) => {if !out.contains(n) { out.push(n.clone());}}
            }
        }
        CmdKind::For { name, range: _, invariants: _, variant: _, body } => {
            modified_vars(&body.cmd, out);
            out.push(name.clone());

        }
        CmdKind::Loop { invariants, variant, body } => {
            for case in &body.cases {
                modified_vars(&case.cmd, out);
            }
        }

        CmdKind::Match { body: b } => {
            for case in &b.cases {
                modified_vars(&case.cmd, out);
            }
        }
        // Add the rest of your writing constructs if any…
        _ => {}
    }
}
