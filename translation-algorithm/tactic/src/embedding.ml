(*

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

*)
[@@@ocaml.warning "-33"]
open Ltac_plugin
open Tacentries
open Geninterp

let () =
  (* let open EConstr in
  let open UnivGen in *)
  let t_O = snd @@ Evarutil.new_global Evd.empty @@ Coqlib.lib_ref "Coq.Init.Datatypes.O" in
  let open Val in
  let retval = inject (Base (create "nat")) t_O in
  ml_val_tactic_extend ~plugin:"embedding_plugin" ~name:"findv" ~local:true MLTyNil (Ftactic.return retval)