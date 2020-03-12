(* 4) utiliser les notations génériques GRing *)
Module RingZify.

From Coq Require Import ZArith Psatz ZifyClasses ZifyInst ZifyBool.
From Coq Require Export Lia.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import div choice fintype tuple finfun bigop finset prime.
From mathcomp Require Import binomial ssralg countalg ssrnum ssrint rat.
From mathcomp Require Import intdiv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

Open Scope ring_scope.

Local Delimit Scope Z_scope with Z.

Definition Z_of_int (n : int) : Z :=
  match n with
  | Posz n => Z.of_nat n
  | Negz n' => Z.opp (Z.of_nat (n' + 1))
  end.

Instance Inj_int_Z : InjTyp int Z :=
  mkinj int Z Z_of_int (fun => True) (fun => I).
Add InjTyp Inj_int_Z.

Canonical Inj_int_Z. (* Z_of_int =? inj _ *)

Lemma Op_eq_int_subproof n m : n = m <-> Z_of_int n = Z_of_int m.
Proof. Admitted.

Instance Op_eq_int : BinRel (@eq int) :=
  { TR := @eq Z; TRInj := Op_eq_int_subproof }.
Add BinRel Op_eq_int.

Instance Op_Posz : UnOp Posz := mkuop _ _ _ Posz _ _ id (fun => erefl).
Add UnOp Op_Posz.

Lemma Op_Negz_subproof n : inj (Negz n) = (- (inj n + 1))%Z.
Proof. Admitted.

Instance Op_Negz : UnOp Negz :=
  {| TUOp := fun x => (- (x + 1))%Z; TUOpInj := Op_Negz_subproof |}.
Add UnOp Op_Negz.

Lemma Op_GRing_add_int_subproof : forall n m : int,
  Z_of_int (@GRing.add int_ZmodType n m) = Z.add (Z_of_int n) (Z_of_int m).
Proof. Admitted.

Instance Op_GRing_add_int : BinOp (@GRing.add int_ZmodType) :=
  {| TBOp := Z.add; TBOpInj := Op_GRing_add_int_subproof |}.
Add BinOp Op_GRing_add_int.

Lemma Op_0_int_subproof : inj 0%R = 0%Z. Proof. Admitted.

Instance Op_0_int : CstOp 0%R :=
  {| TCst := 0%Z; TCstInj := Op_0_int_subproof |}.
Add CstOp Op_0_int.

Lemma Op_1_int_subproof : inj 1%R = 1%Z. Proof. Admitted.

Instance Op_1_int : CstOp 1%R :=
  {| TCst := 1%Z; TCstInj := Op_1_int_subproof |}.
Add CstOp Op_1_int.

Goal forall x y : int, x = 0 -> y = 0 -> x + y = 0.
Proof.
  zify.
  (* |- (Z_of_int x + Z_of_int y)%Z = 0%Z *)
Abort.

Goal forall x y : int, x = 1 -> y = 0 -> x + y = 1.
Proof.
  zify.
  (* |- (Z_of_int x + Z_of_int y)%Z = 1%Z *)
Abort.

Lemma Op_GRing_mul_int_subproof : forall n m : int,
  Z_of_int (@GRing.mul int_Ring n m) = Z.mul (Z_of_int n) (Z_of_int m).
Proof. Admitted.

Instance Op_GRing_mul_int : BinOp (@GRing.mul int_Ring) :=
  {| TBOp := Z.mul; TBOpInj := Op_GRing_mul_int_subproof |}.
Add BinOp Op_GRing_mul_int.

Goal forall x : int, 1 * x = x.
Proof.
  zify.
  (* |- (1 * Z_of_int x)%Z = Z_of_int x *)
Abort.

Goal forall x : int, x = x * 1.
Proof.
  zify.
  (* |- Z_of_int x = (Z_of_int x * 1)%Z *)
Abort.

Goal forall x y : int, 1 * x + y = y + x.
Proof.
  zify.
  (* |- (1 * Z_of_int x + Z_of_int y)%Z = (Z_of_int y + Z_of_int x)%Z *)
Abort.

Goal forall x y : int, x + y = 1 * y + x.
Proof.
  zify.
  (* |- (Z_of_int x + Z_of_int y)%Z = (1 * Z_of_int y + Z_of_int x)%Z *)
Abort.

Lemma Op_GRing_natmul_int_subproof : forall (n : nat),
  inj (@GRing.natmul (GRing.Ring.zmodType int_Ring) (GRing.one int_Ring) n) = id (inj n).
Proof. Admitted.

Instance Op_GRing_natmul_int : UnOp (@GRing.natmul (GRing.Ring.zmodType int_Ring) (GRing.one int_Ring)) :=
  {| TUOp := id : Z -> Z; TUOpInj := Op_GRing_natmul_int_subproof |}.
Add UnOp Op_GRing_natmul_int.

Goal forall x : int, (17%:R) * x = (3%:R) * x + (14%:R) * x.
Proof.
  zify.
  (* |- (17 * Z_of_int x)%Z = (3 * Z_of_int x + 14 * Z_of_int x)%Z *)
Abort.

Lemma Op_eq_op_int_subproof (n m : int) :
  Z_of_bool (n == m) = isZero (Z_of_int n - Z_of_int m).
Proof. Admitted.

Instance Op_eq_op_int : BinOp (@eq_op int_eqType) :=
  mkbop int int bool Z (@eq_op _) Inj_int_Z Inj_int_Z Inj_bool_Z
        (fun x y : Z => isZero (Z.sub x y)) Op_eq_op_int_subproof.
Add BinOp Op_eq_op_int.

Ltac zify2 :=
  unfold is_true in *;
  do ?rewrite -> unfold_in in *;
  zify.

Goal forall x y : int, x == 1 -> y == 0 -> x + y == 1.
Proof.
  zify2.
Abort.

(*

x, y: int
z1: Z
Heqz1: z1 = (Z_of_int x - 1)%Z
z2: Z
H: z2 = 1%Z
z: Z
Heqz: z = (Z_of_int y - 0)%Z
z0: Z
H0: z0 = 1%Z
cstr, cstr0, cstr1, cstr2: True
H1: (0 <= z0 <= 1)%Z /\ (z = 0%Z <-> z0 = 1%Z)
H2: (0 <= z2 <= 1)%Z /\ (z1 = 0%Z <-> z2 = 1%Z)
z3: Z
Heqz3: z3 = (Z_of_int x + Z_of_int y - 1)%Z
z4: Z
H3: (0 <= z4 <= 1)%Z /\ (z3 = 0%Z <-> z4 = 1%Z)
1/1
z4 = 1%Z

*)

Goal forall x : int, 1 * x == x.
Proof.
  zify2.
Abort.

(*
x: int
cstr, cstr0: True
z: Z
Heqz: z = (1 * Z_of_int x - Z_of_int x)%Z
z0: Z
H: (0 <= z0 <= 1)%Z /\ (z = 0%Z <-> z0 = 1%Z)
1/1
z0 = 1%Z
*)

Goal forall x y : int, x + y == 1 * y + x.
Proof.
  zify2.
Abort.

(*
x, y: int
cstr, cstr0, cstr1, cstr2: True
z: Z
Heqz: z = (Z_of_int x + Z_of_int y - (1 * Z_of_int y + Z_of_int x))%Z
z0: Z
H: (0 <= z0 <= 1)%Z /\ (z = 0%Z <-> z0 = 1%Z)
1/1
z0 = 1%Z
*)

Goal forall x : int, (17%:R) * x == (3%:R) * x + (14%:R) * x.
Proof.
  zify2.
Abort.

(*
x: int
cstr, cstr0, cstr1: True
z: Z
Heqz: z = (17 * Z_of_int x - (3 * Z_of_int x + 14 * Z_of_int x))%Z
z0: Z
H: (0 <= z0 <= 1)%Z /\ (z = 0%Z <-> z0 = 1%Z)
1/1
z0 = 1%Z
*)

End RingZify.

(* j'ai tenté les versions plus génériques mais zify les ignore *)
(* Lemma Op_GRing_add_subproof : forall n m,
  inj (n + m) = Z.add (inj n) (inj m).
Proof. Admitted.

Instance Op_GRing_add : BinOp (@GRing.add _) :=
  {| TBOp := Z.add; TBOpInj := Op_GRing_add_subproof |}.
Add BinOp Op_GRing_add. *)