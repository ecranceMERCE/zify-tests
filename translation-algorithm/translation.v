Ltac reverse_rec acc l :=
  match l with
  | nil => acc
  | cons ?hd ?tl =>
    reverse_rec (cons hd acc) tl
  end.

Ltac reverse l :=
  let t := type of l in
  match t with
  | list ?T => reverse_rec (@nil T) l
  | _ => fail "cannot reverse a non-list term"
  end.

Ltac uncurry_rec input_types t :=
  match t with
  | ?A -> ?B =>
    uncurry_rec (cons A input_types) B
  | ?OutputType =>
    let input_types' := reverse input_types in
    constr:((input_types', OutputType))
  end.

Ltac uncurry f :=
  let t := type of f in
  uncurry_rec (@nil Type) t.

Ltac input_types_of_function f :=
  let t := uncurry f in
  let t' := eval compute in (fst t) in
  t'.

Ltac output_type_of_function f :=
  let t := uncurry f in
  let t' := eval compute in (snd t) in
  t'.

(* Lemma and_andb : forall b1 b2 : bool,
  b1 && b2 = true -> b1 /\ b2 = true. *)

Class EmbeddableType (Source : Type) (Target : Type) := mk_emb_type {
  embed : Source -> Target;
  predicate : Target -> Prop;
  predicate_after_embedding : forall x, predicate (embed x)
}.

Class EmbeddableFunction1 (S1 S2 T : Type) (f1 : S1 -> S2) {Emb1 : EmbeddableType S1 T} {Emb2 : EmbeddableType S2 T} := mk_emb_func1 {
  g1 : T -> T;
  p1 : forall (x : S1), embed (f1 x) = g1 (embed x)
}.

Class EmbeddableFunction2 (S1 S2 S3 T : Type) (f2 : S1 -> S2 -> S3) {Emb1 : EmbeddableType S1 T} {Emb2 : EmbeddableType S2 T} {Emb3 : EmbeddableType S3 T} := mk_emb_func2 {
  g2 : T -> T -> T;
  p2 : forall (x : S1) (y : S2), embed (f2 x y) = g2 (embed x) (embed y)
}.

(* forall x y : int, x = y -> y = x.
x' == y' = true -> y' == x' = true.
x' == y' --> y' == x' = true

EmbeddableFunction2 Prop Prop Prop bool /\ _ _ _ =
  g2 := &&
  forall (x y : Prop), embed (x /\ y) = embed x && embed y *)

(* Class BinaryRelation {S:Type} {T:Type} (R : S -> S -> Prop) {I : InjTyp S T}  :=
mkbrel {
    TR : T -> T -> Prop;
    TRInj : forall n m : S, R n m <->  TR (@inj _ _ I n) (inj m)
  }. *)

Variable A : Type.
Variable x y z : A.
Axiom xeqy : x = y.
Axiom yeqz : y = z.

Ltac embed term :=
  match term with
  | y = z -> y = z => apply yeqz
  | ?A -> ?B => embed A; embed B
  | x = z => rewrite -> xeqy
  end.

Ltac embedp :=
  match goal with
  | |- ?g => embed g
  end.

Goal x = z -> x = z.
Proof.
  embedp.

Variable A B C : Type.
Variable g : A -> B -> (C -> A) -> B.

Goal True.
Proof.
  let u := uncurry g in
  let a := input_types_of_function g in
  let b := output_type_of_function g in
  pose u; pose a; pose b.


(*
forall (n : nat) (x y : int) (f : nat -> int) (g : int -> T) (h : T -> int) (k : int -> T) (P : Prop) (b1 b2 : bool),
  f (S (S (m n)) + S (S O)) = f (S n) * x -> ((is_true (x == y) /\ g (f n) = k y) \/ h (g (f O)) + y * x = 0) \/ (P /\ forall u:int, u = 0) -> is_true ((~~ ~~ ~~b1) && b2 || true).

*)

Require Import ZArith.



(* Variable f : nat -> Z. *)
(* Variable predNZ : Z -> Prop. *)
Axiom cstrNZ : forall x : nat, predNZ (f x).

Instance itNZ : InjTyp nat Z := {|
  inj := f;
  pred := predNZ;
  cstr := cstrNZ
|}.

(* tous les : if exists morphism t t' then create term Var (fresh x, t') *)
(* deviennent : *)

(* get_table v : tactique OCaml qui cherche dans la table des variables *)

Ltac embed_morph v := first [ embed_morph_table v | embed_morph_no_table v ].

Ltac embed_morph_table v :=
  let v' := get_table v in
  repeat
    match goal with
    | |- context[v] =>
      

Ltac embed_morph_no_table v := try
  let u := constr:(inj v) in
  repeat
    match goal with
    | |- context[v] =>
      let h := fresh in
      pose (h := u).


(* Ltac embed_morph i :=
  try let u := constr:(inj i) in
      let h := fresh in
      pose (h := u).

Goal forall x, x = 0.
Proof.
  embed_morph 2. *)

(*
let known_functions = Hashtbl.of_seq (List.to_seq
  [ (implb, impl);
    (negb, c_not);
    (andb, c_and);
    (orb, c_or);
    (ltb c_int, lt c_int);
    (eqb c_int, eq c_int);
    (eqb Tbool, eq Tbool);
    (eqb c_T, eq c_T);
    (mul c_int, mul TZ);
    (add c_int, add TZ);
    (lt c_int, lt TZ);
    (eq c_int, eq TZ) ])
*)

Class BinOp {S1 S2 S3:Type} {T:Type} (Op : S1 -> S2 -> S3) {I1 : InjTyp S1 T} {I2 : InjTyp S2 T} {I3 : InjTyp S3 T} :=
  mkbop {
      (* [TBOp] is the target operator after injection of operands. *)
      TBOp : T -> T -> T;
      (* [TBOpInj] states the correctness of the injection. *)
      TBOpInj : forall (n:S1) (m:S2), inj (Op n m) = TBOp (inj n) (inj m)
    }.

Class KnownFunction {S : Type} (f : _ -> S) (T : Type) :=
  mkkf {
    f' : _ -> T;
    kfinj : forall args : _, inj (f args) = f' (map inj args)
  }.

(* fonction Ltac (T1 -> ... -> Tn-1 -> Tn) -> ([T1; ...; Tn-1], Tn) ou alors changement de l'algo pour raisonner sur des fonctions *)

(* savoir quand c'est une constante et quand c'est une variable pour traiter le cas Const *)
(* CstOp peut être intéressant à garder pour injecter directement des constantes connues ? *)

(* est-ce qu'on reste en bool -> Prop, ou on fait un Prop -> bool ? *)
(* réussir à faire passer les opérateurs logiques dans les classes qui décrivent les fonctions connues *)

(* translation table = table construite à la volée, utilisable en Ltac ? *)
(* terminaison de repeat_opt (appeler f sur x tant qu'elle ne renvoie pas None) *)