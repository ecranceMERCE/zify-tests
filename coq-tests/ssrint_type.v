Module BaseZify. (* what zify processes without further imports or declarations *)

From Coq Require Import ZArith Psatz ZifyClasses ZifyInst ZifyBool.

Goal forall x y : nat, x = 0 -> y = 0 -> x + y = 0.
Proof.
  zify.
  (* |- (Z.of_nat x + Z.of_nat y)%Z = 0%Z *)
Abort.

Goal forall x y : nat, x = 13 -> y = 4 -> x + y = 17.
Proof.
  zify.
  (* |- (Z.of_nat x + Z.of_nat y)%Z = 17%Z *)
Abort.

Goal forall x y : nat, x = 13 -> y = 2 -> x + y = S (S x).
Proof.
  zify.
  (* |- (Z.of_nat x + Z.of_nat y)%Z = (Z.of_nat x + 1 + 1)%Z *)
  (* S constructor is translated to +1 in Z *)
Abort.

End BaseZify.

Module MCNatZify. (* now with nat operations from mathcomp *)

From Coq Require Import ZArith Psatz ZifyClasses ZifyInst ZifyBool.
From mathcomp Require Import all_ssreflect.

Goal forall x y : nat, x = 0 -> y = 0 -> x + y = 0.
Proof.
  zify.
  (* |- Z.of_nat (x + y) = 0%Z *)
  (* addition is not handled because it is addn instead of plus *)
Abort.

(* nat is known by zify, we only need to declare an instance for addn *)
(* Op_plus already exists and defines the same operation *)

Instance Op_addn : BinOp addn := Op_plus.
Add BinOp Op_addn.

Goal forall x y : nat, x = 0 -> y = 0 -> x + y = 0.
Proof.
  zify.
  (* |- (Z.of_nat x + Z.of_nat y)%Z = 0%Z *)
  (* now addn is translated *)
Abort.

Goal forall x y : nat, x = 13 -> y = 4 -> x + y = 17.
Proof.
  zify.
  (* |- (Z.of_nat x + Z.of_nat y)%Z = 17%Z *)
Abort.

Goal forall x y : nat, x = 13 -> y = 2 -> x + y = S (S x).
Proof.
  zify.
  (* |- (Z.of_nat x + Z.of_nat y)%Z = (Z.of_nat x + 1 + 1)%Z *)
Abort.

End MCNatZify.

Module SsrintZify. (* now with the ssrint type *)

From Coq Require Import ZArith Psatz ZifyClasses ZifyInst ZifyBool.
From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Delimit Scope Z_scope with Z.

Goal forall x y : int, x = 0 -> y = 0 -> intZmod.addz x y = 0.
Proof.
  zify.
  (* |- intZmod.addz x y = 0 *)
  (* zify knows nothing about this type and its operations *)
Abort.

(* we define this type for zify *)
(* code from mczify : https://github.com/pi8027/mczify/blob/master/theories/zify.v *)

Definition Z_of_int (n : int) : Z :=
  match n with
  | Posz n => Z.of_nat n
  | Negz n' => Z.opp (Z.of_nat (n' + 1))
  end.

Instance Inj_int_Z : InjTyp int Z :=
  mkinj int Z Z_of_int (fun => True) (fun => I).
Add InjTyp Inj_int_Z.

Canonical Inj_int_Z. (* Z_of_int =? inj _ *)

Lemma Op_addz_subproof n m :
  Z_of_int (intZmod.addz n m) = (Z_of_int n + Z_of_int m)%Z.
Proof. Admitted.

Instance Op_addz : BinOp intZmod.addz :=
  {| TBOp := Z.add; TBOpInj := Op_addz_subproof |}.
Add BinOp Op_addz.

Lemma Op_eq_int_subproof n m : n = m <-> Z_of_int n = Z_of_int m.
Proof. Admitted.

Instance Op_eq_int : BinRel (@eq int) :=
  { TR := @eq Z; TRInj := Op_eq_int_subproof }.
Add BinRel Op_eq_int.

Goal forall x y : int, x = 0 -> y = 0 -> intZmod.addz x y = 0.
Proof.
  zify.
  (* |- (Z_of_int x + Z_of_int y)%Z = Z_of_int 0 *)
  (* ok, but constants are not directly injected *)
Abort.

(* defining instances for the constructors of int is sufficient because the values below are in nat which zify already knows *)

Instance Op_Posz : UnOp Posz := mkuop _ _ _ Posz _ _ id (fun => erefl).
Add UnOp Op_Posz.

Lemma Op_Negz_subproof n : inj (Negz n) = (- (inj n + 1))%Z.
Proof. Admitted.

Instance Op_Negz : UnOp Negz :=
  {| TUOp := fun x => (- (x + 1))%Z; TUOpInj := Op_Negz_subproof |}.
Add UnOp Op_Negz.

Goal forall x y : int, x = 13 -> y = 4 -> intZmod.addz x y = 17.
Proof.
  zify.
  (* |- (Z_of_int x + Z_of_int y)%Z = 17%Z *)
  (* ok *)
Abort.

(* now what happens with boolean equality? *)

Lemma Op_eq_op_int_subproof (n m : int) :
  Z_of_bool (n == m) = isZero (Z_of_int n - Z_of_int m).
Proof. Admitted.

Instance Op_eq_op_int : BinOp (@eq_op int_eqType) :=
  mkbop int int bool Z (@eq_op _) Inj_int_Z Inj_int_Z Inj_bool_Z
        (fun x y : Z => isZero (Z.sub x y)) Op_eq_op_int_subproof.
Add BinOp Op_eq_op_int.

Goal forall x y : int, x == 0 -> y == 0 -> intZmod.addz x y == 0.
Proof.
  zify.
  (* does not work because of is_true coercion *)
Abort.

(* the way mczify handles this is an enriched tactic unfolding the coercions *)

Ltac zify2 :=
  unfold is_true in *;
  do ?rewrite -> unfold_in in *;
  zify.

Goal forall x y : int, x == 0 -> y == 0 -> intZmod.addz x y == 0.
Proof.
  zify2.
  (* works but creates a heavy context with a lot of hypotheses (due to bool to Z injection) *)
Abort.

End SsrintZify.