use crate::slang::ast::{Expr};
use crate::slang::Span;
use crate::ivl::{IVLCmd, IVLCmdKind};
use crate::utils::{expr_safety_guards, subst_var_in_expr};

#[derive(Debug, Clone)]
pub struct Obligation {
    pub formula: Expr,
    pub span: Span,
    pub message: String,
}

pub fn swp(cmd: &IVLCmd, goals: Vec<Obligation>) -> Vec<Obligation> {
    match &cmd.kind {
        IVLCmdKind::Assert { condition, message } => {
            let mut out = goals;
            out.push(Obligation { formula: condition.clone(), span: cmd.span, message: message.clone() });
            out
        }

        IVLCmdKind::Assume { condition } => goals
            .into_iter()
            .map(|g| Obligation {
                formula: condition.clone().imp(&g.formula),
                span: g.span,
                message: g.message,
            })
            .collect(),

        IVLCmdKind::Seq(c1, c2) => swp(c1, swp(c2, goals)),
        IVLCmdKind::NonDet(c1, c2) => {
            let mut a = swp(c1, goals.clone());
            let mut b = swp(c2, goals);
            a.append(&mut b);
            a
        },

        IVLCmdKind::Assignment { name, expr } => {
            let mut out = Vec::new();
            for (guard, sp, msg) in expr_safety_guards(expr) {
                out.push(Obligation { formula: guard, span: sp, message: msg });
            }
            for g in goals {
                let g_subst = subst_var_in_expr(&g.formula, &name.ident, expr);
                out.push(Obligation { formula: g_subst, span: g.span, message: g.message });
            }
            out
        },

        // IVLCmdKind::MethodCall { name, fun_name: _, args: _, method: _ } => {
        //     let mut out = Vec::new();
        //     for g in goals {
        //         let ret_var = Expr::ident(&name.ident, &Type::Bool).with_span(cmd.span);
        //         let g_subst = subst_var_in_expr(&g.formula, &name.ident, &ret_var);
        //         out.push(Obligation { formula: g_subst, span: g.span, message: g.message });
        //     }
        //     out
        // },
        
        // IVLCmdKind::Havoc { name, ty: _ } => {
        //     let mut out = Vec::new();
        //     for g in goals {
        //         // Create a fresh variable of the same name
        //         let havoc_var = Expr::ident(&name.ident, &Type::Bool).with_span(cmd.span);
        //         let g_subst = subst_var_in_expr(&g.formula, &name.ident, &havoc_var);
        //         out.push(Obligation { formula: g_subst, span: g.span, message: g.message });
        //     }
        //     out
        // }
        
        // IVLCmdKind::Havoc { name, ty } => {
        //     goals
        //     .into_iter()
        //     .map(|g| Obligation {
        //         formula: Expr::quantifier(
        //             Quantifier::Forall, 
        //             Var { span: g.span, }, 
        //             g.formula) condition.clone().imp(&g.formula),
        //         span: g.span,
        //         message: g.message,
        //     })
        //     .collect(),
        // }
        _ => {todo!("Not yet implemented")}

        // IVLCmdKind::Havoc { .. } => goals,
    }
}
