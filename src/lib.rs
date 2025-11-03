pub mod ivl;
mod ivl_ext;

use ivl::{IVLCmd, IVLCmdKind};
use slang_ui::prelude::*;

pub mod swp;
pub mod utils;
pub mod lowering;
pub mod dsa;

use swp::swp;
use utils::{conj_or_true};
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
            let ensures = conj_or_true(m.ensures().cloned()); 
            
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
            
            // 4) Initial goal set X0 (safety only for now: post = true) 
            // When you hook 'ensures' + 'return', change this to Ens[result := return_expr]. 
            let init_goal = Obligation { 
                formula: ensures.clone(), // G 
                span: m.span, // precise span to blame if post doesn’t follow 
                message: "postcondition might not hold".to_owned(), }; 
            
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