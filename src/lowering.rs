use std::{collections::HashSet, ops::Not};

use crate::{ivl::{IVLCmd, IVLCmdKind}, swp::Obligation};
use itertools::enumerate;
use slang::ast::{Cmd, CmdKind, Expr, Op, Range, Type};
use slang_ui::prelude::{slang::{ast::{Specification}}, *};
use crate::utils::{expr_safety_guards, subst_var_in_expr};


fn fresh_tmp(name: &str, _ty: &slang::ast::Type, span: slang::Span) -> slang::ast::Name {
    // Any freshening scheme; even suffixing a counter is fine for now.
    // If you don't have a global gensym, use a monotonic static or UUID.
    let ident = format!("__tmp_{}_{}", name, span.start()); 
    slang::ast::Name { span, ident }
}

pub fn cmd_to_ivlcmd_with_ensures(cmd: &Cmd, ensures: &Vec<Obligation>) -> IVLCmd {
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
            let left = cmd_to_ivlcmd_with_ensures(c1, ensures);
            let right = cmd_to_ivlcmd_with_ensures(c2, ensures);
            IVLCmd {
                span: cmd.span,
                kind: IVLCmdKind::Seq(Box::new(left), Box::new(right)),
            }
        }

        CmdKind::Match { body } => {
            let mut cases_ivl: Vec<IVLCmd> = Vec::new();
            for case in &body.cases {
                let assume_g = IVLCmd {
                    span: case.condition.span,
                    kind: IVLCmdKind::Assume {
                        condition: case.condition.clone(),
                    },
                };
                let branch_cmd = cmd_to_ivlcmd_with_ensures(&case.cmd, ensures);
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
            let mut seq: Option<IVLCmd> = None;

            if let Some(e) = expr {
                let res = Expr::ident("result", &e.ty).with_span(e.span);
                let eq  = Expr::op(&res, Op::Eq, e).with_span(cmd.span);
                let a   = IVLCmd { span: cmd.span, kind: IVLCmdKind::Assume { condition: eq } };
                seq = Some(a);
            }

            // (b) assert each method postcondition
            for phi in ensures {
                let a = IVLCmd {
                    span: phi.span,
                    kind: IVLCmdKind::Assert {
                        condition: phi.formula.clone(),
                        message: phi.message.clone(),
                    },
                };
                seq = Some(match seq {
                    None => a,
                    Some(acc) => IVLCmd { span: cmd.span, kind: IVLCmdKind::Seq(Box::new(acc), Box::new(a)) },
                });
            }

            // (c) cut the path
            let cut = IVLCmd { span: cmd.span, kind: IVLCmdKind::Assume { condition: Expr::bool(false) } };
            match seq {
                None => cut,
                Some(acc) => IVLCmd { span: cmd.span, kind: IVLCmdKind::Seq(Box::new(acc), Box::new(cut)) }
            }
        }

        CmdKind::Loop { invariants, variant, body } => {
            let mut modset = HashSet::<_>::new();
            for case in &body.cases { modset.extend(case.cmd.clone().assigned_vars().clone()); }

            // 1) Entry VC: one Assert per invariant
            // Build a left-associated Seq of per-invariant asserts.
            let mut seq: Option<IVLCmd> = None;
            for inv in invariants {
                let a = IVLCmd {
                    span: inv.span,
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
            // 1b) Entry: if variant exists, assert t >= 0
            if let Some(t) = variant {
                let ge0 = Expr::op(t, Op::Ge, &Expr::num(0).with_span(t.span)).with_span(t.span);
                let a = IVLCmd {
                    span: t.span,
                    kind: IVLCmdKind::Assert { condition: ge0, message: "loop variant must be non-negative on entry".to_owned() }
                };
                seq = Some(match seq { 
                    None => a, 
                    Some(acc) => IVLCmd { 
                        span: cmd.span, 
                        kind: IVLCmdKind::Seq(Box::new(acc), Box::new(a)) 
                    }
                }
            );
            }

            let mut seq = seq.unwrap_or(IVLCmd::assert(&Expr::bool(true), "Skip"));

            // 2) havoc Mod; then one Assume per invariant
            for x in &modset {
                let ty = &x.1;
                let h = IVLCmd { span: cmd.span, kind: IVLCmdKind::Havoc { name: x.0.clone(), ty: ty.clone() } };
                seq = IVLCmd { span: cmd.span, kind: IVLCmdKind::Seq(Box::new(seq), Box::new(h)) };
            }

            // 2b) assume each invariant
            for inv in invariants {
                let as_inv = IVLCmd {
                    span: inv.span, // <— also attribute the assume to the invariant itself
                    kind: IVLCmdKind::Assume { condition: inv.clone() },
                };
                seq = IVLCmd { span: cmd.span, kind: IVLCmdKind::Seq(Box::new(seq), Box::new(as_inv)) };
            }

            // 2c) After havocs, if variant exists, assume t >= 0 again 
            if let Some(t) = variant {
                let ge0 = Expr::op(t, Op::Ge, &Expr::num(0).with_span(t.span)).with_span(t.span);
                let asv = IVLCmd { span: t.span, kind: IVLCmdKind::Assume { condition: ge0 } };
                seq = IVLCmd { span: cmd.span, kind: IVLCmdKind::Seq(Box::new(seq), Box::new(asv)) };
            }

            // 3) For each branch: { assume bi; v := V(m); enc(Ci); (assert each inv); assert v < V(m);assume false } ⫴ { assume !bi; skip } -----
            for (i,case) in enumerate(&body.cases) {

                let bi = case.condition.clone(); // bi
                let mut then_seq = IVLCmd { 
                    span: bi.span, 
                    kind: IVLCmdKind::Assume { condition: bi.clone() }  // assume bi
                };

                // if variant exists, havoc tmp then assume tmp == variant;
                if let Some(t) = variant { 
                    // Make a fresh
                    let tmp = fresh_tmp("variant_old", &t.ty, t.span); // or t.ty if you track it
                    // Declare tmp by Havoc; then constrain it.
                    let decl = IVLCmd { span: t.span, kind: IVLCmdKind::Havoc { name: tmp.clone(), ty: slang::ast::Type::Int } };
                    //// let dummy_variant = IVLCmd::assert(&Expr::ident(&tmp.ident, &t.ty), "Dummy assertion variant");
                    let eq   = Expr::op(&Expr::ident(&tmp.ident, &slang::ast::Type::Int).with_span(t.span), Op::Eq, t).with_span(t.span);
                    let tie  = IVLCmd { span: t.span, kind: IVLCmdKind::Assume { condition: eq } };

                    then_seq = IVLCmd { span: cmd.span, kind: IVLCmdKind::Seq(Box::new(then_seq), Box::new(decl)) }; // havoc tmp
                    // then_seq = IVLCmd { span: cmd.span, kind: IVLCmdKind::Seq(Box::new(then_seq), Box::new(dummy_variant)) };
                    then_seq = IVLCmd { span: cmd.span, kind: IVLCmdKind::Seq(Box::new(then_seq), Box::new(tie)) }; // assume tmp = variant
                }

                // Body
                let enc_ci  = cmd_to_ivlcmd_with_ensures(&case.cmd, ensures);
                then_seq = IVLCmd { span: cmd.span, kind: IVLCmdKind::Seq(Box::new(then_seq), Box::new(enc_ci)) };

                // per-invariant preservation asserts
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

                // assert strict decrease t < t_old on taken iteration
                if let Some(t) = variant {
                    let tmp = fresh_tmp("variant_old", &t.ty, t.span);
                    let t_old = Expr::ident(&tmp.ident, &t.ty).with_span(t.span);
                    let dec   = Expr::op(t, Op::Lt, &t_old).with_span(t.span);
                    let assert_dec = IVLCmd {
                        span: t.span,
                        kind: IVLCmdKind::Assert {
                            condition: dec,
                            message: format!("loop variant must strictly decrease for branch {}", i),
                        },
                    };
                    then_seq = IVLCmd { span: cmd.span, kind: IVLCmdKind::Seq(Box::new(then_seq), Box::new(assert_dec)) };
                }

                let cut = IVLCmd { span: cmd.span, kind: IVLCmdKind::Assume { condition: Expr::bool(false) } };
                then_seq = IVLCmd { span: cmd.span, kind: IVLCmdKind::Seq(Box::new(then_seq), Box::new(cut)) };

                // else: assume !bi; skip
                let else_branch = IVLCmd {
                    span: bi.span,
                    kind: IVLCmdKind::Assume { condition: Expr::not(bi) } 
                };

                // nondet between taken and not-taken guarded paths
                let nondet = IVLCmd { span: cmd.span, kind: IVLCmdKind::NonDet(Box::new(then_seq), Box::new(else_branch)) };
                seq = IVLCmd { span: cmd.span, kind: IVLCmdKind::Seq(Box::new(seq), Box::new(nondet)) };
            }
            seq

        }

        CmdKind::For { name, range, invariants, variant: _, body } => {
            let (lo, hi) = match range {
                Range::FromTo(lo, hi) => (lo.clone(), hi.clone()),
            };
            let i_expr    = Expr::ident(&name.ident, &Type::Int).with_span(name.span);
            let i_plus_1  = Expr::op(&i_expr, Op::Add, &Expr::num(1).with_span(name.span)).with_span(name.span);
            let ge = Expr::op(&lo, Op::Le, &i_expr).with_span(cmd.span);
            let lt = Expr::op(&i_expr, Op::Lt, &hi).with_span(cmd.span);
            let guard = Expr::op(&ge, Op::And, &lt).with_span(cmd.span);

            // 1) Entry VC: assert I with i := L
            let mut seq: IVLCmd = IVLCmd::nop();
            for inv in invariants {
                let inv_at_L = subst_var_in_expr(inv, &name.ident, &lo);   // i -> L
                let a = IVLCmd {
                    span: inv.span,
                    kind: IVLCmdKind::Assert {
                        condition: inv_at_L,
                        message: "loop invariant might not be preserved".to_owned(),
                    },
                };
                seq = IVLCmd { span: cmd.span, kind: IVLCmdKind::Seq(Box::new(seq), Box::new(a)) };
            }

            // 2) Havoc loop-carried state and DECLARE i, then assume I
            let mut modset = body.cmd.clone().assigned_vars();
            modset.retain(|(n, _ty)| n.ident != name.ident);        // exclude i
            for (n, ty) in &modset {
                let h = IVLCmd { span: cmd.span, kind: IVLCmdKind::Havoc { name: n.clone(), ty: ty.clone() } };
                seq = IVLCmd { span: cmd.span, kind: IVLCmdKind::Seq(Box::new(seq), Box::new(h)) };
            }
            
            seq = IVLCmd {
                span: name.span,
                kind: IVLCmdKind::Seq(
                    Box::new(seq),
                    Box::new(IVLCmd { span: name.span, kind: IVLCmdKind::Havoc { name: name.clone(), ty: Type::Int } }),
                )
            };

            for inv in invariants {
                let as_inv = IVLCmd { span: inv.span, kind: IVLCmdKind::Assume { condition: inv.clone() } };
                seq = IVLCmd { span: cmd.span, kind: IVLCmdKind::Seq(Box::new(seq), Box::new(as_inv)) };
            }

            // 3) One-step: assume guard; C; assert I with i := i+1; assume false
            let mut then_seq = IVLCmd { span: guard.span, kind: IVLCmdKind::Assume { condition: guard.clone() } };
            let enc_body = cmd_to_ivlcmd_with_ensures(&body.cmd, ensures);
            then_seq = IVLCmd { span: cmd.span, kind: IVLCmdKind::Seq(Box::new(then_seq), Box::new(enc_body)) };

            // preservation at successor index
            for inv in invariants {
                // i -> i+1
                let inv_next = subst_var_in_expr(inv, &name.ident, &i_plus_1);
                let a = IVLCmd {
                    span: inv.span,
                    kind: IVLCmdKind::Assert {
                        condition: inv_next,
                        message: "loop invariant might not be preserved".to_owned(),
                    },
                };
                then_seq = IVLCmd { span: cmd.span, kind: IVLCmdKind::Seq(Box::new(then_seq), Box::new(a)) };
            }
            then_seq = IVLCmd { span: cmd.span, kind: IVLCmdKind::Seq(Box::new(then_seq), Box::new(IVLCmd { span: cmd.span, kind: IVLCmdKind::Assume { condition: Expr::bool(false) } })) };

            // else: assume !guard
            let else_branch = IVLCmd { span: guard.span, kind: IVLCmdKind::Assume { condition: Expr::op(&guard, Op::Imp, &Expr::bool(false)).with_span(guard.span) } };

            // 4) Nondet branch
            let nondet = IVLCmd { span: cmd.span, kind: IVLCmdKind::NonDet(Box::new(then_seq), Box::new(else_branch)) };
            IVLCmd { span: cmd.span, kind: IVLCmdKind::Seq(Box::new(seq), Box::new(nondet)) }
        }



        CmdKind::MethodCall { name, fun_name, args, method } => {
            // --- edge cases ---
            let var_name = if let Some(n) = name.clone() {
                n
            } else {
                return IVLCmd::assert(&Expr::bool(false),
                                    "Method calls without assignments are not supported yet.")
                        .with_span(&cmd.span);
            };

            let met = if let Some(m) = method.get() {
                m
            } else {
                return IVLCmd::assert(&Expr::bool(false),
                                    &format!("Method {} does not exist", fun_name.ident))
                        .with_span(&cmd.span);
            };

            if args.len() != met.args.len() {
                return IVLCmd::assert(&Expr::bool(false), "Wrong arity").with_span(&cmd.span);
            }
            if met.return_ty.is_none() {
                return IVLCmd::assert(&Expr::bool(false),
                                    "Method has no return but call assigns to a variable")
                        .with_span(&cmd.span);
            }

            let mut ivl = IVLCmd::nop();
            let mut tmps: Vec<Expr> = Vec::with_capacity(args.len());
            for (i, ei) in args.iter().enumerate() {
                let guards = expr_safety_guards(ei);
                let guards_assertions: Vec<_> = guards.iter().map(|(ex,sp,msg)| {
                    IVLCmd::seq(&IVLCmd::assert(ex, msg).with_span(sp), &IVLCmd::assume(ex).with_span(sp))
                }).collect();
                ivl = ivl.seq(&IVLCmd::seqs(&guards_assertions)); // check conditions

                let tmp_name = met.args[i].name.prefix(&format!("tmp{i}"));
                let tmp_ty   = met.args[i].ty.1.clone();
                let tmp_expr = Expr::ident(&tmp_name.ident, &tmp_ty);
                ivl = ivl.seq(&IVLCmd::assign(&tmp_name, ei));
                tmps.push(tmp_expr);
            }

            let subst_formals = |e: &Expr| {
                let mut r = e.clone();
                for (i, v) in met.args.iter().enumerate() {
                    r = r.subst_ident(&v.name.ident, &tmps[i]);
                }
                r
            };

            for spec in &met.specifications {
                if let Specification::Requires { span: _, expr } = spec {
                    let e_sub = subst_formals(expr);
                    let msg = format!("Precondition {} might not hold", expr); // or use attached message if your enum has one
                    ivl = ivl.seq(&IVLCmd::assert(&e_sub, &msg).with_span(&cmd.span));
                }
            }

            // --- total correctness for direct recursion (EF7): variant checks ---
            if fun_name.ident == met.name.ident {
                if let Some(v) = &met.variant {
                    // v_here: variant at the current frame (uses formals as-is)
                    let v_here = v.clone();

                    // v_call: variant at callee entry with actuals (use evaluated tmps)
                    let v_call = {
                        let mut r = v.clone();
                        for (i, formal) in met.args.iter().enumerate() {
                            r = r.subst_ident(&formal.name.ident, &tmps[i]);
                        }
                        r
                    };

                    // Well-foundedness on Int: both must be non-negative
                    let ge0_here = Expr::op(&v_here, Op::Ge, &Expr::num(0).with_span(v.span)).with_span(v.span);
                    ivl = ivl.seq(&IVLCmd::assert(&ge0_here, "variant must be non-negative in current frame").with_span(&cmd.span));

                    let ge0_call = Expr::op(&v_call, Op::Ge, &Expr::num(0).with_span(v.span)).with_span(v.span);
                    ivl = ivl.seq(&IVLCmd::assert(&ge0_call, "variant must be non-negative for recursive call").with_span(&cmd.span));

                    // Strict decrease across the recursive call
                    let dec = Expr::op(&v_here, Op::Gt, &v_call).with_span(v.span);
                    ivl = ivl.seq(&IVLCmd::assert(&dec, "variant must strictly decrease for recursive call").with_span(&cmd.span));
                }
            }

            // --- havoc the LHS (frame for caller) ---
            ivl = ivl.seq(&IVLCmd::havoc(&var_name, &met.return_ty.clone().unwrap().1));

            // --- assume every ensures separately (preserve span + message) ---
            // first, result -> lhs
            let rty = &met.return_ty.as_ref().unwrap().1;
            let lhs_expr = Expr::ident(&var_name.ident, rty);

            for spec in &met.specifications {
                if let Specification::Ensures { span: _, expr } = spec {
                    let e1 = subst_formals(expr);
                    let e2 = Expr::subst_result(&e1, &lhs_expr);
                    ivl = ivl.seq(&IVLCmd::assume(&e2).with_span(&expr.span));
                }
            }

            return ivl;
        }

        other => {
            // Keep this list in sync with the arms you *do* handle
            const SUPPORTED: &str = "Assert | Assume | Seq | Match | VarDefinition";

            // Discriminant prints a stable id even if Debug isn't available
            let discr = std::mem::discriminant(other);

            // Most AST enums derive Debug; if CmdKind doesn't, add #[derive(Debug)] to it.
            let found = format!("{other:#?}");

            todo!(
                "cmd_to_ivlcmd_with_ensures: unsupported CmdKind at {span:?}\n\
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