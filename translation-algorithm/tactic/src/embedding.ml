open Pp
(* open Ltac_plugin *)

module ConstrSet = Set.Make (struct
  type t = Constrexpr.constr_expr
  let compare = Stdlib.compare
end)

module IntegerType = struct
  let integertypes = ref ConstrSet.empty
  let register t =
    integertypes := ConstrSet.add t !integertypes
end

let tac_is_integertype t =
  if ConstrSet.mem t !IntegerType.integertypes then Tacticals.New.tclIDTAC
  else Tacticals.New.tclFAIL 1 (str "")