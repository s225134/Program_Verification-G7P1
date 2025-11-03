use crate::slang::ast::{Expr};
use crate::slang::Span;
use crate::ivl::{IVLCmd, IVLCmdKind};

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
        }

        _ => {todo!("Not yet implemented")}

        // IVLCmdKind::Assignment { name, expr } => {
        //     let mut out = Vec::new();
        //     for (guard, sp, msg) in expr_safety_guards(expr) {
        //         out.push(Obligation { formula: guard, span: sp, message: msg });
        //     }
        //     for g in goals {
        //         let g_subst = subst_var_in_expr(&g.formula, name, expr);
        //         out.push(Obligation { formula: g_subst, span: g.span, message: g.message });
        //     }
        //     out
        // }

        // IVLCmdKind::Havoc { .. } => goals,
    }
}
