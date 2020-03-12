Add Rec LoadPath "~/Desktop/smtcoq2/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.

Require Import ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Goal forall x' y' : Z, x' = 0%Z -> y' = 0%Z -> (x' + y')%Z = 0%Z.
Proof.
  smt.
Qed.

Goal forall x' y' : Z, x' = 1%Z -> y' = 0%Z -> (x' + y')%Z = 1%Z.
Proof.
  smt.
Qed.

Goal forall x' : Z, (1 * x')%Z = x'.
Proof.
  smt.
Qed.

Goal forall x' : Z, x' = (x' * 1)%Z.
Proof.
  smt.
Qed.

Goal forall x' y' : Z, (1 * x' + y')%Z = (y' + x')%Z.
Proof.
  smt.
Qed.

Goal forall x' y' : Z, (x' + y')%Z = (1 * y' + x')%Z.
Proof.
  smt.
Qed.

Goal forall x' : Z, (17 * x')%Z = (3 * x' + 14 * x')%Z.
Proof.
  smt.
Qed.

Goal forall (x y z z0 z1 z2 z3 z4 : Z),
  z1 = (x - 1)%Z ->
  z2 = 1%Z ->
  z = (y - 0)%Z ->
  z0 = 1%Z ->
  (0 <= z0 <= 1)%Z /\ (z = 0%Z <-> z0 = 1%Z) ->
  (0 <= z2 <= 1)%Z /\ (z1 = 0%Z <-> z2 = 1%Z) ->
  z3 = (x + y - 1)%Z ->
  (0 <= z4 <= 1)%Z /\ (z3 = 0%Z <-> z4 = 1%Z) ->
  z4 = 1%Z.
Proof.
  smt.
Qed.

Goal forall (x z z0 : Z),
  z = (1 * x - x)%Z ->
  (0 <= z0 <= 1)%Z /\ (z = 0%Z <-> z0 = 1%Z) ->
  z0 = 1%Z.
Proof.
  smt.
Qed.

Goal forall (x y z z0 : Z),
  z = (x + y - (1 * y + x))%Z ->
  (0 <= z0 <= 1)%Z /\ (z = 0%Z <-> z0 = 1%Z) ->
  z0 = 1%Z.
Proof.
  smt.
Qed.

Goal forall (x z z0 : Z),
  z = (17 * x - (3 * x + 14 * x))%Z ->
  (0 <= z0 <= 1)%Z /\ (z = 0%Z <-> z0 = 1%Z) ->
  z0 = 1%Z.
Proof.
  smt.
Qed.