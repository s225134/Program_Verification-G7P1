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

fn conj_or_true(it: impl Iterator<Item = Expr>) -> Expr {
    return it.reduce(|a, b| a & b)
                .unwrap_or(Expr::bool(true));
}

impl slang_ui::Hook for App {
    fn analyze(&self, cx: &slang_ui::Context, file: &slang::SourceFile) -> Result<()> {
        let mut solver = cx.solver()?;

        for m in file.methods() {
            // 1) Merge method requires and ensures into two single Expr
            let requires = conj_or_true(m.requires().cloned());
            let ensures = conj_or_true(m.ensures().cloned());

            // 2) If no body, nothing to verify
            let Some(body) = m.body.clone() else { continue; };
            let cmd = &body.cmd;

            // 3) Lower slang Cmd -> IVL, preserving spans
            let ivl_body = cmd_to_ivlcmd(cmd);

            let ivl_root = IVLCmd {
                span: ivl_body.span, // or a method-level span if you have one
                kind: IVLCmdKind::Seq(
                    Box::new(IVLCmd {
                        span: m.span, // or any span you store for the requires block
                        kind: IVLCmdKind::Assume { condition: requires.clone() },
                    }),
                    Box::new(ivl_body),
                ),
            };

            // 4) Initial goal set X0 (safety only for now: post = true)
            //    When you hook 'ensures' + 'return', change this to Ens[result := return_expr].
            let init_goal = Obligation {
                formula: ensures.clone(),      // G
                span: m.span,          // precise span to blame if post doesn’t follow
                message: "postcondition might not hold".to_owned(),
            };
            let goals0 = vec![init_goal];

            // 5) Notes-style SWP: (Cmd, X) -> X'
            let obligations = swp(&ivl_root, goals0);

            // 6) Check each obligation independently (they are *closed* now)
            for obl in obligations {
                // Translate to SMT outside the closure so '?' uses outer Result type
                let sobl = obl.formula.smt(cx.smt_st())?;

                // Ask if the negation is SAT
                solver.scope(|solver| -> Result<(), smtlib::Error> {
                    solver.assert(!sobl.as_bool()?)?;

                    match solver.check_sat()? {
                        smtlib::SatResult::Sat => {
                            // Counterexample exists -> obligation can fail
                            cx.error(obl.span, obl.message.clone());
                            // If you want "first failure only", early-exit here by returning an error you catch outside.
                        }
                        smtlib::SatResult::Unknown => {
                            cx.warning(obl.span, format!("{}: solver returned unknown", obl.message));
                        }
                        smtlib::SatResult::Unsat => {
                            // Obligation valid under all models -> OK
                        }
                    }
                    Ok(())
                }
            )?;
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
            kind: IVLCmdKind::Seq(
                Box::new(
                    IVLCmd { 
                        span: cmd.span, 
                        kind: IVLCmdKind::Assert {
                            condition: condition.clone(),
                            message: "assertion might fail".to_owned()},
                    }
                ),
                Box::new(
                    IVLCmd { 
                        span: cmd.span, 
                        kind: IVLCmdKind::Assume { 
                            condition: condition.clone() 
                        }
                    }
                )
            )        
        }
        ,
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
            // swp(assert R, X) = X ∪ { R }
            let mut out = goals;
            out.push(Obligation {
                formula: condition.clone(),
                span: cmd.span,
                message: message.clone(),
            });
            out
        },

        IVLCmdKind::Assume { condition } => {
            // swp(assume A, X) = { A ⇒ G | G ∈ X }
            goals.into_iter().map(|g| Obligation {
                formula: condition.clone().imp(&g.formula),
                span: g.span,                 // keep original blame site
                message: g.message,           // keep original message
            }).collect()
        }
        ,
        IVLCmdKind::Seq(c1, c2) => {
            // swp(S;T, X) = swp(S, swp(T, X))
            let x2 = swp(c2, goals);
            swp(c1, x2)
        }
        ,
        IVLCmdKind::NonDet(c1, c2) => {
            // swp(S ⫾ T, X) = swp(S, X) ∪ swp(T, X)
            let mut a = swp(c1, goals.clone());
            let mut b = swp(c2, goals);
            a.append(&mut b);
            a
        }
        
        _ => { todo!("Not implemented yet")},

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
