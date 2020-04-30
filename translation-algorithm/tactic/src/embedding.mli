module IntegerType : sig
  val register : Constrexpr.constr_expr -> unit
end

val tac_is_integertype : EConstr.t -> unit Proofview.tactic