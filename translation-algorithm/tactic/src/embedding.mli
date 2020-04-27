open Constrexpr

val add_embedding : constr_expr -> unit Proofview.tactic
val find_embedding_opt : constr_expr -> constr_expr option