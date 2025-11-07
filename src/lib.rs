pub mod ivl;
mod ivl_ext;

use itertools::Itertools;
use ivl::{IVLCmd, IVLCmdKind};
use slang_ui::prelude::{miette::SourceOffset, slang::ast::{Cmd, Expr, FunctionRef}, smtlib::{Bool, and}, *};

pub mod swp;
pub mod utils;
pub mod lowering;
pub mod dsa;

use swp::swp;
use utils::{conj_or_true, subst_result_in_expr};
use lowering::cmd_to_ivlcmd;
use swp::Obligation;
use dsa::*;

use std::{collections::HashMap, env::vars};
use slang::ast::Type;

pub struct App;

// Your main verifier logic stays here
impl slang_ui::Hook for App { 
    fn analyze(&self, cx: &slang_ui::Context, file: &slang::SourceFile) -> Result<()> { 
        let mut solver = cx.solver()?; 
        
        for fun in file.functions(){
            let return_ty = match fun.return_ty.clone().1.smt(solver.st()) {
                    Ok(ty) => ty,
                    _ => panic!("Function return type must be a sort"),
                };
            let vars_ = fun.args.iter().map(|v| v.ty.1.smt(solver.st())).collect::<Result<Vec<_>, _>>()?;
            solver.declare_fun(&smtlib::funs::Fun::new(solver.st(), &fun.name.ident, vars_, return_ty))?;

            let pre = fun.requires();
            let post = fun.ensures();

            let pre = pre.cloned().reduce(|a,b| a.and(&b)).unwrap_or(Expr::bool(true));
            let post_expr = Expr::call(fun.name.clone(),fun.args.iter().map(|a| Expr::ident(&a.name.ident, &a.ty.1)).collect::<Vec<_>>(),file.get_function_ref(fun.name.ident.clone()));
            let post = post.cloned().reduce(|a,b| a.and(&b)).unwrap_or(Expr::bool(true)).subst_result(&post_expr);
        
            
            let x = match &fun.body{
                Some(b) => {
                    // if (fun.ensures().count()>0){
                    //     cx.error(fun.name.span, "we do not check post conditions for functions with bodies");
                    // }
                    // let eq = post_expr.eq(&b);
                    let post_sub = post.subst_result(b);
                    pre.imp(&post_sub)}
                _ => pre.imp(&post),
            };

            let quantifier = Expr::quantifier(slang::ast::Quantifier::Forall, &fun.args, &x);
            solver.assert(quantifier.smt(solver.st())?.as_bool()?)?;
                
        }

        for domain in file.domains() {
            for fun in domain.functions() {
                let return_ty = match fun.return_ty.clone().1.smt(solver.st()) {
                    Ok(ty) => ty,
                    _ => panic!("Function return type must be a sort"),
                };
                let vars_ = fun.args.iter().map(|v| v.ty.1.smt(solver.st())).collect::<Result<Vec<_>, _>>()?;
                solver.declare_fun(&smtlib::funs::Fun::new(solver.st(), &fun.name.ident, vars_, return_ty))?;

                let pre = fun.requires();
                let post = fun.ensures();

                let pre = pre.cloned().reduce(|a,b| a.and(&b)).unwrap_or(Expr::bool(true));
                let post_expr = Expr::call(fun.name.clone(),fun.args.iter().map(|a| Expr::ident(&a.name.ident, &a.ty.1)).collect::<Vec<_>>(),file.get_function_ref(fun.name.ident.clone()));
                let post = post.cloned().reduce(|a,b| a.and(&b)).unwrap_or(Expr::bool(true)).subst_result(&post_expr);

                let x = pre.imp(&post);
                let quantifier = Expr::quantifier(slang::ast::Quantifier::Forall, &fun.args, &x);
                solver.assert(quantifier.smt(solver.st())?.as_bool()?)?;
                

            }
            for ax in domain.axioms() {
                let expr_smt = ax.expr.smt(solver.st())?.as_bool()?; 
                solver.assert(expr_smt)?;
            }   
            
        }   

        for m in file.methods() { 
            // 1) Merge method requires and ensures into two single Expr 
            let requires = conj_or_true(m.requires().cloned()); 

            // Build initial goals: one per ensures clause, each with its own span.
            let mut goals0: Vec<Obligation> = Vec::new();

            for ens in m.ensures() {
                // 1) normalize `result` → Ident("result", ret_ty)
                let f = match &m.return_ty {
                    // m.return_ty: Option<(Span, Type)>
                    Some((_, ty)) => {
                        let res_id = Expr::ident("result", &ty).with_span(ens.span);
                        subst_result_in_expr(ens, &res_id)
                    }
                    None => ens.clone(),
                };

                // 2) push one obligation per ensures, preserving span
                goals0.push(Obligation {
                    formula: f,
                    span: ens.span,
                    message: "postcondition might not hold".to_owned(),
                });
            }

            // If there are no ensures, you can default to `true` (optional)
            if goals0.is_empty() {
                goals0.push(Obligation {
                    formula: Expr::bool(true).with_span(m.span),
                    span: m.span,
                    message: "postcondition (trivial)".to_owned(),
                });
            }
            
            // 2) If no body, nothing to verify 
            let Some(body) = m.body.clone() else { continue; }; 
            let cmd = &body.cmd; 
            
            // 3) Lower slang Cmd -> IVL, preserving spans 
            
            let ivl_body = cmd_to_ivlcmd(cmd); 
            let ivl_root = IVLCmd { 
                span: m.span, // or a method-level span if you have one 
                kind: IVLCmdKind::Seq( 
                    Box::new(IVLCmd { 
                        span: m.span, // or any span you store for the requires block 
                        kind: IVLCmdKind::Assume { 
                            condition: requires.clone() 
                        }, 
                    }), 
                    Box::new(ivl_body), ), 
                }; 
            
            
            // 5) Notes-style SWP: (Cmd, X) -> X' 
            let obligations = swp(&ivl_root, goals0); 
            
            // 6) Check each obligation independently (they are *closed* now) 
            for obl in obligations { 
                println!("{:?}", obl.formula);
                // Translate to SMT outside the closure so '?' uses outer Result type 
                let sobl = obl.formula.smt(cx.smt_st())?; 
                
                // Ask if the negation is SAT 
                solver.scope(|solver| -> Result<(), smtlib::Error> { 
                    solver.assert(!sobl.as_bool()?)?; 
                    
                    match solver.check_sat()? { 
                        smtlib::SatResult::Sat => { 
                            // Counterexample exists -> obligation can fail 
                            cx.error(obl.span, obl.message.clone()); 
                        },
                        smtlib::SatResult::Unknown => { 
                            cx.warning(obl.span, format!("{}: solver returned unknown", obl.message)); 
                        } smtlib::SatResult::Unsat => { 
                            // Obligation valid under all models -> OK 
                        } 
                    } 
                    Ok(()) 
                } )?; 
            } 
        } 
        Ok(()) 
    } 
}