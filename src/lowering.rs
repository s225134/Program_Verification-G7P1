use std::{collections::HashSet, fmt, ops::Not};

use crate::ivl::{IVLCmd, IVLCmdKind};
use itertools::enumerate;
use slang::ast::{Cmd, CmdKind, Expr, Op, Type, Name};
use slang_ui::prelude::{slang::ast::MethodRef, *};
use crate::utils::{conj_or_true, modified_vars};

/// Translate a `slang::ast::Cmd` into `IVLCmd`, preserving source spans.
/// For now we handle: Assert, Assume, Seq, Match (as nondet), VarDefinition (-> Assign/Havoc).
pub fn cmd_to_ivlcmd(cmd: &Cmd) -> IVLCmd {
    match &cmd.kind { // take care of masked errors too
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
                IVLCmd::seq(
                    &IVLCmd {
                        span: cmd.span,
                        kind: IVLCmdKind::Havoc {
                            name: name.clone(),
                            ty: ty_val.clone(),
                        },
                    }, 
                    &IVLCmd {
                        span: cmd.span,
                        kind: IVLCmdKind::Assert { condition: 
                            Expr::ident(&name.ident, &ty.1).eq(&Expr::ident(&name.ident, &ty.1)), 
                            message: "Dummy assertion to fix smt library".to_string() 
                        }
                    }
            )
                
            }
        },

        CmdKind::Assignment { name, expr } => {
            IVLCmd {
                span: cmd.span,
                kind: IVLCmdKind::Assignment { name: name.clone(),  expr: expr.clone() }
            }
        },

        CmdKind::Return { expr } => {
            match expr {
                Some(e) => {
                    let res = 
                    Expr::ident("result", &e.ty)
                        .with_span(e.span);
                    let eq  = Expr::op(&res, Op::Eq, e).with_span(cmd.span);

                    IVLCmd { span: cmd.span, kind: IVLCmdKind::Assume { condition: eq } }
                }
                None => {
                    // void-style return; nothing to constrain
                    IVLCmd { span: cmd.span, kind: IVLCmdKind::Assume { condition: Expr::bool(true) } }
                }
            }
        }

        CmdKind::Loop { invariants, variant: _, body } => {
            // ----- Mod := union of writes in all guarded bodies -----
            let mut modset = HashSet::<_>::new();
            for case in &body.cases { modset.extend(case.cmd.clone().assigned_vars().clone()); }

            // ----- 1) Entry VC: one Assert per invariant (preserve spans) -----
            // Build a left-associated Seq of per-invariant asserts.
            let mut seq: Option<IVLCmd> = None;
            for inv in invariants {
                let a = IVLCmd {
                    span: inv.span, // <— precise blame location
                    kind: IVLCmdKind::Assert {
                        condition: inv.clone(),
                        message: "loop invariant might not hold on entry".to_owned(),
                    },
                };
                seq = Some(match seq {
                    None => a,
                    Some(acc) => IVLCmd { span: cmd.span, kind: IVLCmdKind::Seq(Box::new(acc), Box::new(a)) },
                });
            }
            let mut seq = seq.unwrap_or(IVLCmd::assert(&Expr::bool(true), "Skip"));

            // ----- 2) havoc Mod; then one Assume per invariant (keep spans) -----
            for x in &modset {
                let ty = &x.1;
                let h = IVLCmd { span: cmd.span, kind: IVLCmdKind::Havoc { name: x.0.clone(), ty: ty.clone() } };
                seq = IVLCmd { span: cmd.span, kind: IVLCmdKind::Seq(Box::new(seq), Box::new(h)) };
            }
            for inv in invariants {
                let as_inv = IVLCmd {
                    span: inv.span, // <— also attribute the assume to the invariant itself
                    kind: IVLCmdKind::Assume { condition: inv.clone() },
                };
                seq = IVLCmd { span: cmd.span, kind: IVLCmdKind::Seq(Box::new(seq), Box::new(as_inv)) };
            }

            // ----- 3) For each branch: { assume bi; enc(Ci); (assert each inv); assume false } ⫴ { assume !bi; skip } -----
            for (i,case) in enumerate(&body.cases) {
                let bi      = case.condition.clone();
                let enc_ci  = cmd_to_ivlcmd(&case.cmd);

                // then: assume bi; enc(Ci); assert I1; ...; assert Im; assume false
                let mut then_seq = IVLCmd {
                    span: bi.span,
                    kind: IVLCmdKind::Assume { condition: bi.clone() },
                };
                then_seq = IVLCmd { span: cmd.span, kind: IVLCmdKind::Seq(Box::new(then_seq), Box::new(enc_ci)) };

                // per-invariant preservation asserts, each with its own span
                for inv in invariants {
                    let assert_pres = IVLCmd {
                        span: inv.span, // <— blame the exact invariant that fails to be preserved
                        kind: IVLCmdKind::Assert {
                            condition: inv.clone(),
                            message: format!("loop invariant might not be preserved for branch {}", i),
                        },
                    };
                    then_seq = IVLCmd { span: cmd.span, kind: IVLCmdKind::Seq(Box::new(then_seq), Box::new(assert_pres)) };
                }

                let cut = IVLCmd { span: cmd.span, kind: IVLCmdKind::Assume { condition: Expr::bool(false) } };
                then_seq = IVLCmd { span: cmd.span, kind: IVLCmdKind::Seq(Box::new(then_seq), Box::new(cut)) };

                // else: assume !bi; skip   (this accumulates ¬bi for the survivor path)
                let else_branch = IVLCmd {
                    span: bi.span,
                    kind: IVLCmdKind::Assume { condition: Expr::not(bi) } 
                };

                // nondet between taken and not-taken guarded paths
                let nondet = IVLCmd { span: cmd.span, kind: IVLCmdKind::NonDet(Box::new(then_seq), Box::new(else_branch)) };
                seq = IVLCmd { span: cmd.span, kind: IVLCmdKind::Seq(Box::new(seq), Box::new(nondet)) };
            }

            // Done. The survivor path has all `Assume inv` plus every `assume !bi`.
            // That yields I ∧ ∧i ¬bi as the post fact for code after the loop.
            seq

        }

        // THIS IS WORK IN PROGRESS (should work for bounded loops)
        // CmdKind::For { name, range, invariants, variant: _, body } => {
        //     // for i in start..end { B } ≡ i := start; while (i < end) invariant I { B; i := i + 1 }
        //     let (start, end) = match range {
        //         slang::ast::Range::FromTo(start, end) => (start, end),
        //     };

        //     // i := start
        //     let init = IVLCmd {
        //         span: cmd.span,
        //         kind: IVLCmdKind::Assignment {
        //             name: name.clone(),
        //             expr: start.clone(),
        //         },
        //     };
        //     // while (i < end) { body; i := i + 1 }
        //     let i_expr = Expr::ident(name.as_str(), &Type::Int).with_span(name.span);
        //     let cond  = Expr::op(&i_expr, Op::Lt, end).with_span(cmd.span);

        //     let body_ivl = cmd_to_ivlcmd(&body.cmd); // Block → &Cmd
        //     let one      = Expr::num(1).with_span(cmd.span);
        //     let next_i   = Expr::op(&i_expr, Op::Add, &one).with_span(cmd.span);
        //     let incr     = IVLCmd {
        //         span: cmd.span,
        //         kind: IVLCmdKind::Assignment { name: name.clone(), expr: next_i },
        //     };
        //     let while_body = IVLCmd {
        //         span: cmd.span,
        //         kind: IVLCmdKind::Seq(Box::new(body_ivl), Box::new(incr)),
        //     };

        //     let while_cmd = IVLCmd {
        //         span: cmd.span,
        //         kind: IVLCmdKind::While {
        //             condition: cond,
        //             invariants: invariants.clone(),
        //             variant: None,
        //             body: Box::new(while_body),
        //         },
        //     };
        //     IVLCmd {
        //         span: cmd.span,
        //         kind: IVLCmdKind::Seq(Box::new(init), Box::new(while_cmd)),
        //     }
        // }
        CmdKind::MethodCall{ name, fun_name, args, method } => {
            let name = name.clone().expect("MethodCall without a result variable not supported yet");
            let method_name = method.get().map(|m| m.name.clone());
            IVLCmd {
                span: cmd.span,
                kind: IVLCmdKind::MethodCall { 
                    name,
                    fun_name: fun_name.clone(),
                    args: args.clone(),
                    method: method_name,
                }
            }
        }

        other => {
            // Keep this list in sync with the arms you *do* handle
            const SUPPORTED: &str = "Assert | Assume | Seq | Match | VarDefinition";

            // Discriminant prints a stable id even if Debug isn't available
            let discr = std::mem::discriminant(other);

            // Most AST enums derive Debug; if CmdKind doesn't, add #[derive(Debug)] to it.
            let found = format!("{other:#?}");

            todo!(
                "cmd_to_ivlcmd: unsupported CmdKind at {span:?}\n\
                ├─ found: {found}\n\
                ├─ discriminant: {discr:?}\n\
                └─ expected one of: {SUPPORTED}\n\
                help: add a new `match` arm in lowering.rs for this variant and return an `IVLCmdKind`.",
                span = cmd.span,
                found = found,
                discr = discr
            );
        }
    }
}

// missing break, continue, for, loop, return, methodcall