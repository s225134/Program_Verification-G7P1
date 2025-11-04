use std::fmt;

use crate::ivl::{IVLCmd, IVLCmdKind};
use slang::ast::{Cmd, CmdKind, Expr, Op, Type};
use slang_ui::prelude::{slang::ast::MethodRef, *};

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
                IVLCmd {
                    span: cmd.span,
                    kind: IVLCmdKind::Havoc {
                        name: name.clone(),
                        ty: ty_val.clone(),
                    },
                }
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