From Coq Require Import ZArith Psatz ZifyClasses ZifyInst ZifyBool.

(* abstract integer type with a few operations *)

Variable int : Type.
Variable int_zero : int.
Variable addz : int -> int -> int.
Variable Z_of_int : int -> Z.

Goal forall x y : int, x = int_zero -> y = int_zero -> addz x y = int_zero.
Proof.
  zify.
  (* |- addz x y = int_zero *)
  (* no action *)
Abort.

(* instance to inject int into Z *)

Instance Inj_int_Z : InjTyp int Z :=
  mkinj int Z Z_of_int (fun _ => True) (fun _ => I).
Add InjTyp Inj_int_Z.

Canonical Inj_int_Z. (* Z_of_int =? inj _ *)

(* equality on int and injection into Z *)

Lemma Op_eq_int_subproof n m : n = m <-> Z_of_int n = Z_of_int m.
Proof. Admitted.

Instance Op_eq_int : BinRel (@eq int) :=
  { TR := @eq Z; TRInj := Op_eq_int_subproof }.
Add BinRel Op_eq_int.

Goal forall x y : int, x = int_zero -> y = int_zero -> addz x y = int_zero.
Proof.
  zify.
  (* |- Z_of_int (addz x y) = Z_of_int int_zero *)
  (* now, knowing the type and the head term @eq int, the goal is modified *)
Abort.

(* addition on int and injection into Z *)

Lemma Op_addz_subproof : forall n m : int,
  Z_of_int (addz n m) = (Z_of_int n + Z_of_int m)%Z.
Proof. Admitted.

Instance Op_addz : BinOp addz :=
  {| TBOp := Z.add; TBOpInj := Op_addz_subproof |}.
Add BinOp Op_addz.

Goal forall x y : int, x = int_zero -> y = int_zero -> addz x y = int_zero.
Proof.
  zify.
  (* |- (Z_of_int x + Z_of_int y)%Z = Z_of_int int_zero *)
  (* now the tactic knows addz  *)
Abort.

(* 0 constant and injection into Z *)

Lemma Op_int_zero_subproof : inj int_zero = 0%Z.
Proof. Admitted.

Instance Op_int_zero : CstOp int_zero :=
  {| TCst := 0%Z; TCstInj := Op_int_zero_subproof |}.
Add CstOp Op_int_zero.

Goal forall x y : int, x = int_zero -> y = int_zero -> addz x y = int_zero.
Proof.
  zify.
  (* |- (Z_of_int x + Z_of_int y)%Z = 0%Z *)
  (* we have everything we wanted from zify *)
Abort.