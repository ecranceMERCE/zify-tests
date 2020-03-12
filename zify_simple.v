From Coq Require Import ZArith Psatz ZifyClasses ZifyInst ZifyBool.
From mathcomp Require Import all_ssreflect.

Local Delimit Scope Z_scope with Z.

(* entier virtuel *)

Variable int : Type.
Variable int_zero : int.
Variable addz : int -> int -> int.
Variable Z_of_int : int -> Z.
Variable eqz : int -> int -> bool.

Goal forall x y : int, x = int_zero -> y = int_zero -> addz x y = int_zero.
Proof.
  zify.
  (* |- addz x y = int_zero *)
Abort.

(* instance définissant le type int et son injection dans Z *)

Instance Inj_int_Z : InjTyp int Z :=
  mkinj int Z Z_of_int (fun _ => True) (fun _ => I).
Add InjTyp Inj_int_Z.

Canonical Inj_int_Z. (* Z_of_int =? inj _ *)

(* égalité sur int et injection dans Z *)

Lemma Op_eq_int_subproof n m : n = m <-> Z_of_int n = Z_of_int m.
Proof. Admitted.

Instance Op_eq_int : BinRel (@eq int) :=
  { TR := @eq Z; TRInj := Op_eq_int_subproof }.
Add BinRel Op_eq_int.

Goal forall x y : int, x = int_zero -> y = int_zero -> addz x y = int_zero.
Proof.
  zify.
  (* |- Z_of_int (addz x y) = Z_of_int int_zero *)
Abort.

(* addition sur int et injection dans Z *)

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
Abort.

(* constante 0 dans int et injection dans Z *)

Lemma Op_int_zero_subproof : inj int_zero = 0%Z.
Proof. Admitted.

Instance Op_int_zero : CstOp int_zero :=
  {| TCst := 0%Z; TCstInj := Op_int_zero_subproof |}.
Add CstOp Op_int_zero.

Goal forall x y : int, x = int_zero -> y = int_zero -> addz x y = int_zero.
Proof.
  zify.
  (* |- (Z_of_int x + Z_of_int y)%Z = 0%Z *)
Abort.


(* Lemma Op_eqz_int_subproof : forall n m : int,
  eqz n m <-> Z_of_int n = Z_of_int m.
Proof. Admitted.

Instance Op_eqz_int : BinRel eqz :=
  {| TR := @eq Z; TRInj := Op_eqz_int_subproof |}.
Add BinRel Op_eqz_int. *)

(* égalité booléenne sur int et injection dans Z *)

Lemma Op_eqz_int_subproof : forall x y : int,
  inj (eqz x y) = Z_of_bool (Z.eqb (inj x) (inj y)).
Proof. Admitted.

Instance Op_eqz_int : BinOp eqz :=
  {| TBOp := fun x y => Z_of_bool (Z.eqb x y); TBOpInj := Op_eqz_int_subproof |}.
Add BinOp Op_eqz_int.

(* Goal forall x : int, is_true_eqz x x.
Proof.
  Set Printing All.
  zify.
Abort. *)

Goal forall x y : int, eqz x int_zero -> eqz y int_zero -> eqz (addz x y) int_zero.
Proof.
  Set Printing All.
  (* besoin d'un zify qui unfold les is_true *)
  zify.
Abort.

Ltac zify2 :=
  unfold is_true in *;
  do ?rewrite -> unfold_in in *;
  zify.

Goal forall x y : int, eqz x int_zero -> eqz y int_zero -> eqz (addz x y) int_zero.
Proof.
  zify2.
Abort.