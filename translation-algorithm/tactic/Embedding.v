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

Ltac map_rec f acc l :=
  match l with
  | nil => acc
  | cons ?hd ?tl =>
    let hd' := f hd in
    map_rec f (cons hd' acc) tl
  end.

Ltac map f l :=
  let l' := map_rec f uconstr:(nil) l in
  reverse l'.

Ltac uncurry_rec input_types t :=
  match t with
  | ?A -> ?B =>
    uncurry_rec (cons A input_types) B
  | ?OutputType =>
    let input_types' := reverse input_types in
    constr:((input_types', OutputType))
  end.

Ltac uncurry t := uncurry_rec (@nil Type) t.

Ltac input_types_of_function f :=
  let tf := type of f in
  let t := uncurry tf in
  let t' := eval compute in (fst t) in
  t'.

Ltac output_type_of_function f :=
  let tf := type of f in
  let t := uncurry tf in
  let t' := eval compute in (snd t) in
  t'.

  (*
Ltac get_head x := lazymatch x with ?x _ => get_head x | _ => x end.
Ltac inverse_tactic tactic := try (tactic; fail 1).
Ltac constr_neq t u := inverse_tactic ltac:(constr_eq t u).
Ltac is_not_constructor U sym :=
  let H := fresh in
  assert (U -> True) as H by
         (let x := fresh in
          let y := fresh in
          intro x;
          pose x as y;
          destruct x;
          let C := eval unfold y in y in
          let c := get_head C in
          constr_neq sym c;
          exact I); clear H.
Ltac is_constructor U sym := inverse_tactic ltac:(is_not_constructor U sym). *)

(* Lemma and_andb : forall b1 b2 : bool,
  b1 && b2 = true -> b1 /\ b2 = true. *)

Require Import ZArith.

Class IntegerType (T : Type) := {
  to_Z : T -> Z;
  of_Z : Z -> T;
  pred : Z -> Prop;
  id1 : forall x : T, of_Z (to_Z x) = x;
  id2 : forall z : Z, to_Z (of_Z z) = z;
  inj_to_Z : forall z : Z, exists x : T, z = to_Z x;
  inj_of_Z : forall x : T, exists z : Z, x = of_Z z;
  pred_in_Z : forall x : T, pred (to_Z x)
}.

Lemma forall_embedding : forall (T : Type) {IntT : IntegerType T} (P : T -> Prop),
  (forall x : T, P x) <-> (forall z : Z, P (of_Z z)).
Proof.
  split.
  - intros H z.
    pose proof (inj_to_Z z) as [x Hx].
    rewrite -> Hx.
    rewrite -> (id1 x).
    apply H.
  - intros H x.
    pose proof (inj_of_Z x) as [z Hz].
    rewrite -> Hz.
    apply H.
Qed.

(* Ltac is_integertype x :=
  let t := fresh in
  tryif pose (t := (to_Z x)) then clear t; idtac else fail. *)

Class IntegerFunc1 (T1 T2 : Type) (f1 : T1 -> T2) {IntT1 : IntegerType T1} {IntT2 : IntegerType T2} := {
  g1 : Z -> Z;
  f_to_g_1 : forall x : T1, to_Z (f1 x) = g1 (to_Z x)
}.

Class IntegerFunc2 (T1 T2 T3 : Type) (f2 : T1 -> T2 -> T3) {IntT1 : IntegerType T1} {IntT2 : IntegerType T2} {IntT3 : IntegerType T3} := {
  g2 : Z -> Z -> Z;
  f_to_g_2 : forall (x : T1) (y : T2), to_Z (f2 x y) = g2 (to_Z x) (to_Z y)
}.

Class IntegerBinaryRelation (T : Type) (rel : T -> T -> Prop) {IntT : IntegerType T} := {
  relb_Z : Z -> Z -> bool;
  rel_to_relb_Z : forall x y : T, rel x y <-> relb_Z (to_Z x) (to_Z y) = true
}.

Variable implb andb orb eqb : bool -> bool -> bool.
Definition istrue (b : bool) : Prop := b = true.

(* Axiom TrueB : True <-> true = true.
Axiom FalseB : False <-> false = true.
Axiom bfalse_negbtrue : forall b : bool, b = false <-> negb b = true.
Axiom eq_sym : forall (A : Type) (x y : A), x = y <-> y = x.
Axiom impl_implb : forall (b1 b2 : bool), (b1 = true -> b2 = true) <-> (implb b1 b2 = true).
Axiom and_andb : forall (b1 b2 : bool), (b1 = true /\ b2 = true) <-> (andb b1 b2 = true).
Axiom or_orb : forall (b1 b2 : bool), (b1 = true \/ b2 = true) <-> (orb b1 b2 = true).
Axiom equiv_eqb : forall (b1 b2 : bool), (b1 = true <-> b2 = true) <-> (eqb b1 b2 = true).
Axiom not_negb : forall b : bool, ~ b = true <-> negb b = true. *)

Ltac format_func f args :=
  match f with
  | ?f' ?arg => format_func f' (cons arg args)
  | ?f' => constr:((f', args))
  end.

(* 
Ltac manage_S_rec n t :=
  lazymatch t with
  | S ?t' => manage_S_rec (n + 1)%Z t'
  | O => eval compute in n
  | ?x =>
    let n' := eval compute in n in
    constr:((to_Z x + n')%Z)
  end.

Ltac manage_S t := manage_S_rec 0%Z t. *)

Ltac make_term t args :=
  match args with
  | nil => t
  | cons ?hd ?tl => make_term (t hd) tl
  end.

Ltac equals t t' :=
  match t with
  | ?u =>
    match t' with
    | u => constr:(true)
    | _ => constr:(false)
    end
  end.

Notation IsItEmbeddable := false.
Notation IsItABinaryRelation := false.
Notation Yes := false.
Notation No := false.
Notation Failure := false.

From Coq Require Import List.
Import ListNotations.

(* Ltac try_embed_id t :=
  match IsItEmbeddable with
  | Yes => constr:(inj_of_Z (inj_to_Z t))
  | No => constr:(Failure)
  end. *)

(* Ltac embeddable T target :=
  match target with
  | bool =>
    match T with
    | bool => constr:(true)
    | _ => constr:(false)
    end
  | Prop =>
    match T with
    | bool => constr:(true)
    | Prop => constr:(true)
    | _ => constr:(false)
    end
  | Z =>
    match IsItEmbeddable with
    | Yes =>
      let _ := constr:(@to_Z T _) in
      constr:(true)
    | No => constr:(false)
    end
  end. *)

(* Ltac try_g1 f1 :=
  match IsItEmbeddable with
  | Yes => constr:(@g1 _ _ f1 _ _ _)
  | No => constr:(Failure)
  end.

Ltac try_g2 f2 :=
  match IsItEmbeddable with
  | Yes => constr:(@g2 _ _ _ f2 _ _ _ _)
  | No => constr:(Failure)
  end.

Ltac try_relb_Z rel :=
  match IsItEmbeddable with
  | Yes => constr:(@relb_Z _ rel _)
  | No => constr:(Failure)
  end.

Ltac try_associated_func f args :=
  lazymatch args with
  | [?arg] => try_g1 f
  | [?arg1; ?arg2] => try_g2 f
  | _ => constr:(Failure)
  end. *)

Ltac iter f l :=
  match l with
  | nil => idtac
  | cons ?hd ?tl => f hd; iter f tl
  end.

Ltac get_fst p :=
  match p with
  | (?t, _) => t
  end.

Ltac get_snd p :=
  match p with
  | (_, ?t) => t
  end.

Ltac embed t :=
 lazymatch t with
  | True => (* idtac n "True" *) constr:(true = true)
  | False => (* idtac n "False" *) constr:(false = true)
  | ?t1 -> ?t2 => (* idtac n "impl"; embed (S n) t1; embed (S n) t2 *)
    let t1' := embed t1 in
    let t2' := embed t2 in
    match t1' with
    | ?t1'' = true =>
      match t2' with
      | ?t2'' = true => constr:(implb t1'' t2'' = true)
      end
    | _ => constr:(t1' -> t2')
    end
  | ?t1 /\ ?t2 => (* idtac n "and"; embed (S n) t1; embed (S n) t2 *)
    let t1' := embed t1 in
    let t2' := embed t2 in
    match t1' with
    | ?t1'' = true =>
      match t2' with
      | ?t2'' = true => constr:(andb t1'' t2'' = true)
      end
    | _ => constr:(t1' /\ t2')
    end
  | ?t1 \/ ?t2 => (* idtac n "or"; embed (S n) t1; embed (S n) t2 *)
    let t1' := embed t1 in
    let t2' := embed t2 in
    match t1' with
    | ?t1'' = true =>
      match t2' with
      | ?t2'' = true => constr:(orb t1'' t2'' = true)
      end
    | _ => constr:(t1' \/ t2')
    end
  | ?t1 <-> ?t2 => (* idtac n "equiv"; embed (S n) t1; embed (S n) t2 *)
    let t1' := embed t1 in
    let t2' := embed t2 in
    match t1' with
    | ?t1'' = true =>
      match t2' with
      | ?t2'' = true => constr:(eqb t1'' t2'' = true)
      end
    | _ => constr:(t1' <-> t2')
    end
  | forall (x : ?T), ?t' => (* idtac n "forall"; embed (S n) t' *)
    let t'' := embed t' in
    constr:(forall (x : T), t'')
  | istrue ?b => (* idtac n "istrue"; embed (S n) b *)
    let b' := embed b in
    constr:(b' = true)
  | true = ?b => (* idtac n "true="; embed (S n) b *)
    let b' := embed b in
    constr:(b' = true)
  | false = ?b => (* idtac n "false="; embed (S n) b *)
    let b' := embed b in
    constr:(negb b' = true)
  | ?b = false => (* idtac n "=false"; embed (S n) b *)
    let b' := embed b in
    constr:(negb b' = true)
  | ?f ?arg =>
    (* let p := format_func f [arg] in
    idtac n "pair" p;
    let f := get_fst p in
    let args := get_snd p in
    idtac n "f" f;
    iter ltac:(fun x => embed (S n) x) args *)
    let p := format_func f [arg] in
    let f := get_fst p in
    let args := get_snd p in
    let embedded_args := map embed args in
    let t' := make_term f embedded_args in
    let T := type of t' in
    match IsItEmbeddable with
    | Yes => constr:(@of_Z T _ (@to_Z T _ t'))
    | No => constr:(t')
    end
  | ?x => (* idtac n "autre" *)
    let T := type of x in
    match IsItEmbeddable with
    | Yes => constr:(@of_Z T _ (@to_Z T _ x))
    | No => constr:(x)
    end
  end.

(*
TODO tactique Ltac qui fait :
  @to_Z ?T _ x -> renommer en x' partout dans le goal
  f (of_Z x) (of_Z y) (fonction binaire) type de sortie Prop -> tenter relation binaire avec = true
  to_Z (f (of_Z x)) -> tenter g1
  to_Z (f (of_Z x) (of_Z y)) -> tenter g2
  connecteurs logiques avec = true des 2 côtés -> version booléenne

Ltac  *)


Variable int U : Type.
Variable Oi : int.
Variable mulint addint : int -> int -> int.
Variable eqbint : int -> int -> bool.
Instance integertype_nat : IntegerType nat. Admitted.
Instance integertype_int : IntegerType int. Admitted.
Instance integerfunc2_mulint : IntegerFunc2 int int int mulint. Admitted.
Instance integerfunc2_addint : IntegerFunc2 int int int addint. Admitted.

Goal forall (n : nat) (x y : int) (f : nat -> int) (g : int -> U) (h : U -> int) (k : int -> U) (m : nat -> nat) (P : Prop) (b1 b2 : bool),
  True.
Proof.
  intros n x y f g h k m P b1 b2.
  let G' := embed (f (S (S (m n)) + S (S O)) = mulint (f (S n)) x -> istrue (negb (negb (negb b1)) && b2 || true)) in
  pose (newgoal := G').
Abort.

Goal forall (n : nat) (x y : int) (f : nat -> int) (g : int -> U) (h : U -> int) (k : int -> U) (m : nat -> nat) (P : Prop) (b1 b2 : bool),
  True.
Proof.
  intros n x y f g h k m P b1 b2.
  let G' := embed (f (S (S (m n)) + S (S O)) = mulint (f (S n)) x -> ((istrue (eqbint x y) /\ g (f n) = k y) \/ addint (h (g (f O))) (mulint y x) = Oi) \/ (P /\ forall u:int, u = Oi) -> istrue (negb (negb (negb b1)) && b2 || true)) in
  pose (newgoal := G').

  (* 
  f args
  - f connue
    map embed args + change f en f'
  - f inconnue
    map embed args + embed résultat
  
  *)

Ltac make_embeddings :=
  repeat
    match goal with
    | |- context[True] => rewrite -> TrueB
    | |- context[False] => rewrite -> FalseB
    | |- context[?b = false] => rewrite -> (bfalse_negbtrue b)
    | |- context[false = ?b] => rewrite -> (eq_sym bool false b)
    | |- context[true = ?b] => rewrite -> (eq_sym bool true b)
    | |- context[?b1 = true -> ?b2 = true] => rewrite -> (impl_implb b1 b2)
    | |- context[?b1 = true /\ ?b2 = true] => rewrite -> (and_andb b1 b2)
    | |- context[?b1 = true \/ ?b2 = true] => rewrite -> (or_orb b1 b2)
    | |- context[?b1 = true <-> ?b2 = true] => rewrite -> (equiv_eqb b1 b2)
    | |- context[~ ?b = true] => rewrite -> (not_negb b)
    | |- context[istrue ?t] => unfold istrue
    | |- context[forall (x : ?T), ?t] => (* case : forall *)
      (* generalise, find ?P such that t = P x => forall z : Z, P (of_Z z) *)
      (* try rewrite -> (forall_embedding T P) *)
      idtac
    | |- context[?f ?arg] => (* case : binary relations *)
      let p := format_func f (cons arg nil) in
      let f := constr:(fst p) in
      let args := constr:(snd p) in
      match args with
      | cons ?x (cons ?y nil) =>
        (* rel x y => relb_Z (to_Z x) (to_Z y) = true *)
        try rewrite -> (rel_to_relb_Z x y)
      end
    | |- context[to_Z ?t] =>
      match t with
      | ?f ?arg =>
        let p := format_func f (cons arg nil) in
        let f := constr:(fst p) in
        let args := constr:(snd p) in
        tryif match args with
        | cons ?x nil => (* case : known functions with 1 argument *)
          (* forall x : T1, to_Z (f1 x) = g1 (to_Z x) *)
          rewrite -> (f_to_g_1 x)
        | cons ?x (cons ?y nil) => (* case : known functions with 2 arguments *)
          (* forall (x : T1) (y : T2), to_Z (f2 x y) = g2 (to_Z x) (to_Z y) *)
          rewrite -> (f_to_g_2 x y)
        end then
          idtac
        else (* case : unknown functions *)
          let args' := find_args_under_f args in
          let names := generate_names args' in
          let t' := make_term f args in
          let f' := make_function names (to_Z t') in
          (* change to_Z (f ...args) with f' ...args everywhere in the goal *)
          repeat
            match goal with
            | |- context[to_Z ?t''] =>
              match t'' with
              | ?f'' ?arg'' =>
                let p := format_func f'' (cons arg'' nil) in
                let f'' := constr:(fst p) in
                let args'' := constr:(snd p) in
                constr_eq f f'';
                let args := find_args_under_f args'' in
                let t'' := make_term f' args in
                change (to_Z t) with t''
              end
            end
      (* the rewritings make the embeddings go as down as possible, ending in this case where we just rename *)
      | ?x => (* case : variables *)
        (* rename z : Z := to_Z x and change every occurrence in the goal *)
        let z := fresh in
        pose (z := to_Z x);
        repeat
          match goal with
          | |- context[to_Z x] => change (to_Z x) with z
          end
      end
    end.
    (* TODO constructors *)

From mathcomp Require Import all_ssreflect.

(* Instance int_integertype : IntegerType int := {|
  to_Z := 
  of_Z :=
  pred :=
  id1 :=
  id2 :=

|}. *)

(*  *)

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

(* savoir quand c'est une constante et quand c'est une variable pour traiter le cas Const *)
(* CstOp peut être intéressant à garder pour injecter directement des constantes connues ? *)
*)