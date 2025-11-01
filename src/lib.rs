pub mod ivl;
mod ivl_ext;

use ivl::{IVLCmd, IVLCmdKind};
use slang::ast::{Cmd, CmdKind, Expr, Name};
use slang::Span;
use slang_ui::prelude::*;

/// A single verification obligation:
/// - `formula`: the condition that must be valid (under method `requires`)
/// - `span`: where to blame if this condition is not provable
/// - `message`: short human message
#[derive(Debug, Clone)]
struct Obligation {
    formula: Expr,
    span: Span,
    message: String,
}

pub struct App;

impl slang_ui::Hook for App {
    fn analyze(&self, cx: &slang_ui::Context, file: &slang::SourceFile) -> Result<()> {
        let mut solver = cx.solver()?;

        for m in file.methods() {
            // 1) Merge method requires into a single Expr
            let requires = m
                .requires()
                .cloned()
                .reduce(|a, b| a & b)
                .unwrap_or(Expr::bool(true));

            // 2) If no body, nothing to verify
            let Some(body) = m.body.clone() else { continue; };
            let cmd = &body.cmd;

            // 3) Lower slang Cmd -> IVL, preserving spans
            let ivl_root = cmd_to_ivlcmd(cmd);

            // 4) Initial goal set X0 (safety only for now: post = true)
            //    When you hook 'ensures' + 'return', change this to Ens[result := return_expr].
            let init_goal = Obligation {
                formula: Expr::bool(true),
                span: ivl_root.span,
                message: "postcondition".to_owned(),
            };
            let goals0 = vec![init_goal];

            // 5) Notes-style SWP: (Cmd, X) -> X'
            let obligations = swp(&ivl_root, goals0);

            // 6) Check each obligation independently under 'requires'
            for obl in obligations {
                // Translate to SMT outside the closure so '?' uses outer Result type
                let sreq = requires.smt(cx.smt_st())?;
                let sobl = obl.formula.smt(cx.smt_st())?;

                solver.scope(|solver| -> Result<(), smtlib::Error> {
                    solver.assert(sreq.as_bool()?)?;
                    solver.assert(!sobl.as_bool()?)?;

                    match solver.check_sat()? {
                        smtlib::SatResult::Sat => {
                            cx.error(obl.span, obl.message.clone());
                        }
                        smtlib::SatResult::Unknown => {
                            cx.warning(
                                obl.span,
                                format!("{}: solver returned unknown", obl.message),
                            );
                        }
                        smtlib::SatResult::Unsat => { /* ok */ }
                    }
                    Ok(())
                })?;
            }
        }

        Ok(())
    }
}

/// Translate a `slang::ast::Cmd` into `IVLCmd`, preserving source spans.
/// For now we handle: Assert, Assume, Seq, Match (as nondet), VarDefinition (-> Assign/Havoc).
fn cmd_to_ivlcmd(cmd: &Cmd) -> IVLCmd {
    match &cmd.kind {
        CmdKind::Assert { condition, .. } => IVLCmd {
            span: cmd.span,
            kind: IVLCmdKind::Assert {
                condition: condition.clone(),
                message: "assertion might fail".to_owned(),
            },
        },

        CmdKind::Assume { condition } => IVLCmd {
            span: cmd.span,
            kind: IVLCmdKind::Assume {
                condition: condition.clone(),
            },
        },

        CmdKind::Seq(c1, c2) => {
            let left = cmd_to_ivlcmd(c1);
            let right = cmd_to_ivlcmd(c2);
            IVLCmd {
                span: cmd.span,
                kind: IVLCmdKind::Seq(Box::new(left), Box::new(right)),
            }
        }

        // Encode 'match' as a nondet over guarded branches: assume g; branch_cmd
        // (Sound but possibly over-strict vs ordered semantics; refine later if needed.)
        CmdKind::Match { body } => {
            let mut cases_ivl: Vec<IVLCmd> = Vec::new();
            for case in &body.cases {
                let assume_g = IVLCmd {
                    span: case.condition.span,
                    kind: IVLCmdKind::Assume {
                        condition: case.condition.clone(),
                    },
                };
                let branch_cmd = cmd_to_ivlcmd(&case.cmd);
                let seq_case = IVLCmd {
                    span: case.cmd.span,
                    kind: IVLCmdKind::Seq(Box::new(assume_g), Box::new(branch_cmd)),
                };
                cases_ivl.push(seq_case);
            }
            // Fold cases into a binary NonDet tree
            let mut it = cases_ivl.into_iter();
            let first = it.next().unwrap_or(IVLCmd {
                span: cmd.span,
                kind: IVLCmdKind::Assume {
                    condition: Expr::bool(false),
                },
            });
            it.fold(first, |acc, nxt| IVLCmd {
                span: cmd.span,
                kind: IVLCmdKind::NonDet(Box::new(acc), Box::new(nxt)),
            })
        }

        // var x: T := e  ==> Assignment
        // var x: T       ==> Havoc x:T  (arbitrary value)
        CmdKind::VarDefinition { name, ty, expr } => match expr {
            Some(init_expr) => IVLCmd {
                span: cmd.span,
                kind: IVLCmdKind::Assignment {
                    name: name.clone(),
                    expr: init_expr.clone(),
                },
            },
            None => {
                let (_ty_span, ty_val) = ty; // ty is &(Span, Type)
                IVLCmd {
                    span: cmd.span,
                    kind: IVLCmdKind::Havoc {
                        name: name.clone(),
                        ty: ty_val.clone(),
                    },
                }
            }
        },

        _ => todo!("cmd_to_ivlcmd: unsupported CmdKind in this phase"),
    }
}

/// NOTES-STYLE SWP:
/// Given a command `cmd` and a set of goals `X`, compute the resulting set X':
///
///   swp(assert F, X)       =  {F} ∪ X
///   swp(assume F, X)       =  { F ⇒ G | G ∈ X }
///   swp(C1; C2, X)         =  swp(C1, swp(C2, X))
///   swp(nondet(C1,C2), X)  =  swp(C1, X) ∪ swp(C2, X)
///   swp(x := e, X)         =  { guard(e) ⇒ G[x := e] | G ∈ X }
///   swp(havoc x, X)        =  (approx) { G | G ∈ X }   // refine later if needed
fn swp(cmd: &IVLCmd, goals: Vec<Obligation>) -> Vec<Obligation> {
    match &cmd.kind {
        IVLCmdKind::Assert { condition, message } => {
            let mut out = goals;
            out.push(Obligation {
                formula: condition.clone(),
                span: cmd.span,
                message: message.clone(),
            });
            out
        }

        IVLCmdKind::Assume { condition } => {
            goals.into_iter().map(|g| Obligation {
                formula: condition.clone().imp(&g.formula),
                span: g.span,                 // keep original blame site
                message: g.message,           // keep original message
            }).collect()
        }


        IVLCmdKind::Seq(c1, c2) => {
            let x2 = swp(c2, goals);
            swp(c1, x2)
        }

        IVLCmdKind::NonDet(c1, c2) => {
            let mut a = swp(c1, goals.clone());
            let mut b = swp(c2, goals);
            a.append(&mut b);
            a
        }

        IVLCmdKind::Assignment { name, expr } => {
            // swp(x := e, X) = { guard(e) ⇒ G[x := e] | G ∈ X }
            let guards = expr_safety_guard(expr);
            goals
                .into_iter()
                .map(|g| {
                    let g_subst = subst_var_in_expr(&g.formula, name, expr);
                    Obligation {
                        formula: guards.clone().imp(&g_subst),
                        span: cmd.span,
                        message: "assignment might violate goal".to_owned(),
                    }
                })
                .collect()
        }

        IVLCmdKind::Havoc { .. } => {
            // Approximation: keep G unchanged. For stronger soundness one can freshen x (DSA)
            // and substitute x := x_fresh in every G.
            goals
        }
    }
}

/// Conjoin all safety guards required to evaluate `e`.
/// TODO: implement checks like (den != 0) for `/` and `%` by walking `e`.
fn expr_safety_guard(_e: &Expr) -> Expr {
    Expr::bool(true)
}

/// Substitute a variable by expression inside a goal formula (capture-avoiding).
/// TODO: replace with your template's real substitution helper when available.
fn subst_var_in_expr(goal: &Expr, _x: &Name, _e: &Expr) -> Expr {
    // Stub for now so things compile; implement properly later.
    goal.clone()
}
