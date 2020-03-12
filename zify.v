(* 1) ce que zify doit savoir traiter sans aucune déclaration supplémentaire *)
Module ZeroZify.

From Coq Require Import ZArith Psatz ZifyClasses ZifyInst ZifyBool.
(* on prend le zify de Psatz (celui en OCaml) *)
(* si on importe Zify, la tactique est remplacée et ne fait plus rien *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Goal forall x y : nat, x = 0 -> y = 0 -> x + y = 0.
Proof.
  zify.
Abort.

(*
x, y: nat
H: Z.of_nat x = 0%Z
H0: Z.of_nat y = 0%Z
cstr, cstr0: (0 <= Z.of_nat y)%Z
cstr1, cstr2: (0 <= Z.of_nat x)%Z

1/1
(Z.of_nat x + Z.of_nat y)%Z = 0%Z
*)
(* il y a injection de tous les termes nat dans Z, et on utilise l'addition de Z *)

(* idem pour les constantes et les successeurs (sans réduction des chaînes de +1) *)
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

End ZeroZify.

(* 2) refaire le 1 en important mathcomp *)
Module SSRZify.

From Coq Require Import ZArith Psatz ZifyClasses ZifyInst ZifyBool.
From mathcomp Require Import all_ssreflect.
(* on définit une autre addition pour nat : la fonction addn *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Goal forall x y : nat, x = 0 -> y = 0 -> x + y = 0.
Proof.
  Unset Printing Notations.
  zify.
  (* |- Z.of_nat (x + y) = 0%Z *)
  (* l'addition addn n'est pas traitée *)
Abort.

(* on déclare addn comme opération binaire sur nat *)
(* https://github.com/coq/coq/blob/v8.11/plugins/micromega/ZifyClasses.v *)
(* https://github.com/coq/coq/blob/v8.11/plugins/micromega/ZifyInst.v *)

Instance Op_addn : BinOp addn := Op_plus.
Add BinOp Op_addn.
(* on reprend Op_plus qui existe déjà et qui décrit la même opération *)

Goal forall x y : nat, x = 0 -> y = 0 -> x + y = 0.
Proof.
  Unset Printing Notations.
  zify.
  (* |- (Z.of_nat x + Z.of_nat y)%Z = 0%Z *)
  (* ok *)
Abort.

(* traitement ok sur les 2 autres buts *)
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

End SSRZify.

(* 3) importer le type int et tenter de faire fonctionner la tactique *)

From Coq Require Import ZArith Psatz ZifyClasses ZifyInst ZifyBool.
From Coq Require Export Lia.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import div choice fintype tuple finfun bigop finset prime.
From mathcomp Require Import binomial ssralg countalg ssrnum ssrint rat.
From mathcomp Require Import intdiv.

(* ici, on va utiliser des instances / preuves écrites dans mczify *)
(* https://github.com/pi8027/mczify/blob/master/theories/zify.v *)

(* normalement zify est redéfinie pour être plus puissante, mais il y a un conflit de versions (zify_iter_specs inconnu) *)

(* Ltac zify ::=
  unfold is_true in *; do ?rewrite -> unfold_in in *;
  zify_op; (zify_iter_specs applySpec); zify_post_hook. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Delimit Scope Z_scope with Z.

Goal forall x y : int, x = 0 -> y = 0 -> intZmod.addz x y = 0.
Proof.
  zify.
  (* |- intZmod.addz x y = 0 *)
  (* l'addition n'est pas traitée mais le type int non plus *)
Abort.

(* on tente d'importer les instances définissant int depuis mczify *)
(* ... et toutes les instances qui peuvent être utiles ? (nat, bool, opérations sur nat, étant donné que int cache des opérations de nat) *)

Definition Z_of_int (n : int) : Z :=
  match n with
  | Posz n => Z.of_nat n
  | Negz n' => Z.opp (Z.of_nat (n' + 1))
  end.

(* instance définissant le type int et son injection dans Z *)
Instance Inj_int_Z : InjTyp int Z :=
  mkinj int Z Z_of_int (fun => True) (fun => I).
Add InjTyp Inj_int_Z.

Canonical Inj_int_Z. (* Z_of_int =? inj _ *)

Lemma Op_addz_subproof n m :
  Z_of_int (intZmod.addz n m) = (Z_of_int n + Z_of_int m)%Z.
Proof. Admitted.

(* instance définissant l'opération + sur int et son association avec Z.add *)
Instance Op_addz : BinOp intZmod.addz :=
  {| TBOp := Z.add; TBOpInj := Op_addz_subproof |}.
Add BinOp Op_addz.

Lemma Op_eq_int_subproof n m : n = m <-> Z_of_int n = Z_of_int m.
Proof. Admitted.

(* instance définissant l'égalité '=' sur int *)
Instance Op_eq_int : BinRel (@eq int) :=
  { TR := @eq Z; TRInj := Op_eq_int_subproof }.
Add BinRel Op_eq_int.

(* ici, normalement tout est défini pour que :
- le '=' sur int devienne le '=' sur Z ;
- addz devienne + dans Z ;
- x, y, et 0 deviennent respectivement Z_of_int x, Z_of_int y, et 0%Z. *)

Goal forall x y : int, x = 0 -> y = 0 -> intZmod.addz x y = 0.
Proof.
  zify.
  (* |- (Z_of_int x + Z_of_int y)%Z = Z_of_int 0 *)
  (* ok mais les constantes ne s'injectent pas *)
Abort.

(* instances pour les constructeurs de int, pour traiter les constantes *)

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
  (* maintenant les constantes sont traitées *)
Abort.

(* 5) avec des égalités booléennes *)

(*

Lemma Op_eqz_int_subproof : forall x y : int,
  inj (eqz x y) = Z_of_bool (Z.eqb (inj x) (inj y)).
Proof. Admitted.

Instance Op_eqz_int : BinOp eqz :=
  {| TBOp := fun x y => Z_of_bool (Z.eqb x y); TBOpInj := Op_eqz_int_subproof |}.
Add BinOp Op_eqz_int.

Ltac zify2 :=
  unfold is_true in *;
  do ?rewrite -> unfold_in in *;
  zify.

*)

Lemma Op_eq_op_int_subproof (n m : int) :
  Z_of_bool (n == m) = isZero (Z_of_int n - Z_of_int m).
Proof. Admitted.

Instance Op_eq_op_int : BinOp (@eq_op int_eqType) :=
  mkbop int int bool Z (@eq_op _) Inj_int_Z Inj_int_Z Inj_bool_Z
        (fun x y : Z => isZero (Z.sub x y)) Op_eq_op_int_subproof.
Add BinOp Op_eq_op_int.

Goal forall x y : int, x == 0 -> y == 0 -> intZmod.addz x y == 0.
Proof.
  Set Printing All.
  (* besoin des unfold is_true *)
  zify.
Abort.

Ltac zify2 :=
  unfold is_true in *;
  do ?rewrite -> unfold_in in *;
  zify.

Goal forall x y : int, x == 0 -> y == 0 -> intZmod.addz x y == 0.
Proof.
  zify2.
Abort.

(*

x, y: int
z1: Z
Heqz1: z1 = (Z_of_int x - 0)%Z
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
Heqz3: z3 = (Z_of_int x + Z_of_int y - 0)%Z
z4: Z
H3: (0 <= z4 <= 1)%Z /\ (z3 = 0%Z <-> z4 = 1%Z)
1/1
z4 = 1%Z

*)