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