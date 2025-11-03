use crate::slang::ast::{Expr};

pub fn conj_or_true(it: impl Iterator<Item = Expr>) -> Expr {
    it.reduce(|a, b| a & b).unwrap_or(Expr::bool(true))
}

// pub fn expr_safety_guards(e: &Expr) -> Vec<(Expr, Span, String)> {
//     let mut out = Vec::new();
//     fn walk(e: &Expr, out: &mut Vec<(Expr, Span, String)>) {
//         use slang::ast::BinOp::*;
//         if let Expr::Binary(op, lhs, rhs) = e {
//             match op {
//                 Div | Mod => {
//                     out.push((
//                         Expr::Binary(Ne, Box::new((**rhs).clone()), Box::new(Expr::int(0))),
//                         rhs.span(),
//                         "possible division by zero".to_string(),
//                     ));
//                 }
//                 _ => {}
//             }
//             walk(lhs, out);
//             walk(rhs, out);
//         }
//     }
//     walk(e, &mut out);
//     out
// }

// pub fn subst_var_in_expr(expr: &Expr, x: &Name, value: &Expr) -> Expr {
//     match expr {
//         Expr::Var(y) if y == x => value.clone(),
//         Expr::Unary(op, e1) => Expr::Unary(*op, Box::new(subst_var_in_expr(e1, x, value))),
//         Expr::Binary(op, e1, e2) => Expr::Binary(
//             *op,
//             Box::new(subst_var_in_expr(e1, x, value)),
//             Box::new(subst_var_in_expr(e2, x, value)),
//         ),
//         _ => expr.clone(),
//     }
// }
