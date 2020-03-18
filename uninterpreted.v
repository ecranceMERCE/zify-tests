(* Add Rec LoadPath "~/Desktop/smtcoq2/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import ZArith. *)

Require Import ZArith Psatz ZifyClasses ZifyInst.

(* booléen Z *)
Goal forall (x y : Z) (f : Z -> Z),
  Z.eqb x (y - 1)%Z = true -> Z.eqb (f (x + 1)%Z) (f y) = true.
Proof. Abort.
(* smt *)

(* Prop Z *)
Goal forall (x y : Z) (f : Z -> Z),
  x = (y - 1)%Z -> f (x + 1)%Z = f y.
Proof. Abort.
(* smt *)

Show Zify BinRel.
Show Zify BinOp.

Definition nat_eqb x y := Nat.eqb x y = true.

Lemma Op_Nat_eqb_subproof (n m : nat) :
  Nat.eqb n m = true <-> inj n = inj m.
Proof. Admitted.

Instance Op_Nat_eqb : BinRel nat_eqb :=
  {| TR := @eq Z; TRInj := Op_Nat_eqb_subproof |}.
Add BinRel Op_Nat_eqb.

(* booléen non Z *)
Goal forall (x y : nat) (f : nat -> nat),
  nat_eqb x (y - 1) -> nat_eqb (f (x + 1)) (f y).
Proof.
  zify.
(*
  but
  Z.of_nat (f (x + 1)) = Z.of_nat (f y)
  autoriser à aller sous f (?)
  Z.of_nat (f (natofZ (Zofnat x + 1)%Z))) = Z.of_nat (f (natofZ (Zofnat y)))
  Z.of_nat (f (natofZ (X + 1)%Z))) = Z.of_nat (f (natofZ Y))
  Z.of_nat (f (natofZ (X + 1)%Z))) = Z.of_nat (f (natofZ Y))
  substitution Zofnat . f . natofZ === g ?
  g (X + 1)%Z = g Y

  hypothèses
  Z.of_nat x = z0
  z = (Z.of_nat y - 1)%Z

  X = z0
  z = (Y - 1)%Z
*)
Abort.

Goal forall (X Y z z0 : Z) (g : Z -> Z),
  X = z0 -> z = (Y - 1)%Z ->
  (0 < z)%Z /\ z0 = z \/ (z <= 0)%Z /\ z0 = 0%Z ->
  g (X + 1)%Z = g Y.
Proof.
  (* smt *)
Abort.

Variable g : Z -> Z.

Lemma Op_f_subproof (f : nat -> nat) : forall (n : nat),
  inj (f n) = g (inj n).
Proof. Admitted.

Variable f : nat -> nat.

Instance Op_f : UnOp f :=
 {| TUOp := g; TUOpInj := Op_f_subproof f |}.
Add UnOp Op_f.

(* booléen non Z *)
Goal forall (x y : nat),
  nat_eqb x (y - 1) -> nat_eqb (f (x + 1)) (f y).
Proof.
  zify.
(*
  hypothèses
  z = (Y - 1)%Z
  X = z0
  (0 < z)%Z /\ z0 = z \/ (z <= 0)%Z /\ z0 = 0%Z

  but
  g (Z.of_nat x + 1) = g (Z.of_nat y)
  g (X + 1)%Z = g Y
*)
Abort.

(* Prop non Z *)
Goal forall (x y : nat) (f : nat -> nat),
  x = (y - 1) -> f (x + 1) = f y.
Proof.
  zify.
(* idem *)
Abort.