(* open Pp *)
(* open Ltac_plugin *)

let tac_add t t' = Tacticals.New.tclIDTAC
let tac_find_opt t = Proofview.tclUNIT None