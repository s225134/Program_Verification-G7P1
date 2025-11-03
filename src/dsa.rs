use crate::slang::ast::{Expr, ExprKind};
// use crate::slang::{Span};

#[derive(Default, Clone)]
struct DsaCtx {
    curr: std::collections::HashMap<String, String>,
    ctrs: std::collections::HashMap<String, u32>,
}

impl DsaCtx {
    fn cur(&self, x: &str) -> String {
        self.curr.get(x).cloned().unwrap_or_else(|| format!("{x}#0"))
    }
    fn fresh(&mut self, x: &str) -> String {
        let n = self.ctrs.entry(x.to_string()).and_modify(|k| *k += 1).or_insert(1);
        let v = format!("{x}#{n}");
        self.curr.insert(x.to_string(), v.clone());
        v
    }
}


fn rename_expr(e: &Expr, env: &DsaCtx) -> Expr {
    match &e.kind {
        ExprKind::Ident(x) => Expr::ident(&env.cur(x), &e.ty).with_span(e.span),
        ExprKind::Infix(l,o,r) => {
            let l2 = rename_expr(l, env);
            let r2 = rename_expr(r, env);
            Expr::op(&l2, o.clone(), &r2).with_span(e.span)
        }
        ExprKind::Prefix(o,i) => {
            let i2 = rename_expr(i, env);
            Expr::prefix(&i2, o.clone()).with_span(e.span)
        }
        ExprKind::Ite(c,t,f) => {
            let c2 = rename_expr(c, env);
            let t2 = rename_expr(t, env);
            let f2 = rename_expr(f, env);
            Expr::ite(&c2, &t2, &f2).with_span(e.span)
        }
        ExprKind::FunctionCall { fun_name, args, function } => {
            let args2 = args.iter().map(|a| rename_expr(a, env)).collect();
            Expr::call(fun_name.clone(), args2, function.clone()).with_span(e.span)
        }
        ExprKind::Quantifier(q, vars, body) => {
            // If you have quantifiers, extend env for bound vars (skip or alpha-rename)
            // For now, assume no conflicting binders in your IVL assertions.
            let b2 = rename_expr(body, env);
            Expr::quantifier(q.clone(), vars, &b2).with_span(e.span)
        }
        _ => e.clone(),
    }
}
