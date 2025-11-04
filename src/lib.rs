pub mod ivl;
mod ivl_ext;

use ivl::{IVLCmd, IVLCmdKind};
use slang_ui::prelude::{slang::ast::{Cmd, Expr}, *};

pub mod swp;
pub mod utils;
pub mod lowering;
pub mod dsa;

use swp::swp;
use utils::{conj_or_true, subst_result_in_expr};
use lowering::cmd_to_ivlcmd;
use swp::Obligation;
use dsa::*;


pub struct App;

// Your main verifier logic stays here
impl slang_ui::Hook for App { 
    fn analyze(&self, cx: &slang_ui::Context, file: &slang::SourceFile) -> Result<()> { 
        let mut solver = cx.solver()?; 
        
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