pub mod ivl;
mod ivl_ext;

use ivl::{IVLCmd, IVLCmdKind};
use slang::ast::{Cmd, CmdKind, Expr};
use slang_ui::prelude::*;

pub struct App;

impl slang_ui::Hook for App {
    fn analyze(&self, cx: &slang_ui::Context, file: &slang::SourceFile) -> Result<()> {
        // Get reference to Z3 solver
        let mut solver = cx.solver()?;

        // Iterate methods
        for m in file.methods() {
            // Get method's preconditions;
            let pres = m.requires();
            // Merge them into a single condition
            let pre = pres
                .cloned()
                .reduce(|a, b| a & b)
                .unwrap_or(Expr::bool(true));
            // Convert the expression into an SMT expression
            let spre = pre.smt(cx.smt_st())?;
            // Assert precondition
            solver.assert(spre.as_bool()?)?;

            // Get method's body
            let cmd = &m.body.clone().unwrap().cmd;
            // Encode it in IVL
            let ivl = cmd_to_ivlcmd(cmd);
            // Calculate obligation and error message (if obligation is not verified)
            let (oblig, msg) = wp(&ivl, &Expr::bool(true));
            // Convert obligation to SMT expression
            let soblig = oblig.smt(cx.smt_st())?;

            // Run the following solver-related statements in a closed scope.
            // That is, after exiting the scope, all assertions are forgotten
            // from subsequent executions of the solver
            solver.scope(|solver| {
                // Check validity of obligation
                solver.assert(!soblig.as_bool()?)?;
                // Run SMT solver on all current assertions
                match solver.check_sat()? {
                    // If the obligations result not valid, report the error (on
                    // the span in which the error happens)
                    smtlib::SatResult::Sat => {
                        cx.error(oblig.span, msg.to_string());
                    }
                    smtlib::SatResult::Unknown => {
                        cx.warning(oblig.span, format!("{msg}: unknown sat result"));
                    }
                    smtlib::SatResult::Unsat => (),
                }
                Ok(())
            })?;
        }

        Ok(())
    }
}

// Encoding of (assert-only) statements into IVL (for programs comprised of only
// a single assertion)
fn cmd_to_ivlcmd(cmd: &Cmd) -> IVLCmd {
    match &cmd.kind {
        CmdKind::Assert { condition, .. } => IVLCmd::assert(condition, "Assert might fail!"),
        CmdKind::Assume { condition } => IVLCmd::assume(condition),
        CmdKind::Seq( c1, c2, ) => IVLCmd::seq(&cmd_to_ivlcmd(c1), &cmd_to_ivlcmd(c2)),
        CmdKind::Match { body } => {
            let cases : Vec<IVLCmd> = body
                .cases
                .iter()
                .map(|case| IVLCmd::seq(&IVLCmd::assume(&case.condition), &cmd_to_ivlcmd(&case.cmd)))
                .collect();
            IVLCmd::nondets(&cases)
        },
        // CmdKind::VarDefinition { name, ty, expr } => 
        other => todo!("cmd: Not supported (yet): {other:?}"),
    }
}

// Weakest precondition of (assert-only) IVL programs comprised of a single
// assertion
fn wp(ivl: &IVLCmd, post: &Expr) -> (Expr, String) {
    match &ivl.kind {
        IVLCmdKind::Assert { condition, message } => (condition.clone().and(post), message.clone()),
        IVLCmdKind::Assume { condition } => (condition.clone().imp(post), String::from("assume")),
        IVLCmdKind::Seq( c1, c2) => { 
            let (e, m) = wp(c2, post);
            let (e1,m1) = wp(c1,&e);
            (e1,m1)
        },
        IVLCmdKind::NonDet( c1, c2) => {
            let (e1,m1) = wp(c1, post);
            let (e2,m2) = wp(c2, post);
            (e1.and(&e2), m2)
        }
        other => todo!("wp: Not supported (yet): {other:?}"),
    }
}
