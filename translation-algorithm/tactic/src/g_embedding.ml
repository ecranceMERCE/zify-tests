
# 1 "src/g_embedding.mlg"
 

open Ltac_plugin
open Stdarg
open Tacarg



let __coq_plugin_name = "embedding_plugin"
let _ = Mltop.add_known_module __coq_plugin_name
let () = Tacentries.tactic_extend __coq_plugin_name "EMBEDDING" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("find_embedding_opt", 
                            Tacentries.TyArg (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                            Tacentries.TyNil)), (fun t ist -> 
# 12 "src/g_embedding.mlg"
                                        Embedding.tac_find_opt t 
                                                )));
         (Tacentries.TyML (Tacentries.TyIdent ("add_embedding", Tacentries.TyArg (
                                                                Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                Tacentries.TyArg (
                                                                Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                Tacentries.TyNil))), 
          (fun t t' ist -> 
# 13 "src/g_embedding.mlg"
                                              Embedding.tac_add t t' 
          )))]

