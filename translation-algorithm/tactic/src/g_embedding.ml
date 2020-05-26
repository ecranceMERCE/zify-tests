
# 1 "src/g_embedding.mlg"
 

(* open Ltac_plugin *)
(* open Stdarg *)
(* open Tacarg *)

(*

VERNAC COMMAND EXTEND DECLAREEMBEDDING CLASSIFIED AS SIDEFF
| ["Add" "IntegerType" constr(t) ] -> { Embedding.IntegerType.register t }
END

TACTIC EXTEND EMBEDDING
| ["is_integertype" constr(t)] -> { Embedding.tac_is_integertype t }
END

*)



let __coq_plugin_name = "embedding_plugin"
let _ = Mltop.add_known_module __coq_plugin_name
