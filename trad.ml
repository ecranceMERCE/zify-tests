(* modelling simplified Coq types *)

type c_type =
  | TProp (* Coq's Prop type *)
  | Tarrow of { in_types: c_type list; out_type: c_type } (* function types with one or several inputs and an output *)
  | Tname of string (* other types *)

type c_formula =
  | App of c_formula * c_formula list (* function application *)
  | Var of string * c_type (* variable *)

(* utils *)

(* displaying a type *)
let rec string_of_c_type = function
  | TProp -> "Prop"
  | Tarrow { in_types; out_type } ->
    Printf.sprintf "(%s)"
      (String.concat " -> " (List.map string_of_c_type (in_types @ [out_type])))
  | Tname n -> n

(* checks that l and l' are equal; if not, gives the index of the first values that are different *)
let list_eq l l' =
  let rec list_eq' n = function
    | ([], []) -> Ok ()
    | (x :: xs, y :: ys) -> if x = y then list_eq' (n + 1) (xs, ys) else Error n
    | _ -> Error (-1)
  in list_eq' 0 (l, l')

let combine3 l1 l2 l3 =
  let rec combine3' acc l1 l2 l3 =
    match l1, l2, l3 with
    | [], [], [] -> List.rev acc
    | h1 :: t1, h2 :: t2, h3 :: t3 -> combine3' ((h1, h2, h3) :: acc) t1 t2 t3
    | _ -> raise (Invalid_argument "combine3")
  in
  combine3' [] l1 l2 l3

(* particular known types and values *)

let c_int = Tname "int"
let c_Z = Tname "Z"
let c_nat = Tname "nat"
let c_T = Tname "T"
let c_bool = Tname "bool"

let impl = Var ("->", Tarrow { in_types = [TProp; TProp]; out_type = TProp })
let c_and = Var ("/\\", Tarrow { in_types = [TProp; TProp]; out_type = TProp })
let c_or = Var ("\\/", Tarrow { in_types = [TProp; TProp]; out_type = TProp })
let c_not = Var ("~", Tarrow { in_types = [TProp]; out_type = TProp })

let implb = Var ("-->", Tarrow { in_types = [c_bool; c_bool]; out_type = c_bool })
let andb = Var ("&&", Tarrow { in_types = [c_bool; c_bool]; out_type = c_bool })
let orb = Var ("||", Tarrow { in_types = [c_bool; c_bool]; out_type = c_bool })
let negb = Var ("~~", Tarrow { in_types = [c_bool]; out_type = c_bool })

let eq t = Var ("=", Tarrow { in_types = [t; t]; out_type = TProp })
let lt t = Var ("<", Tarrow { in_types = [t; t]; out_type = TProp })

let eqb t = Var ("=?", Tarrow { in_types = [t; t]; out_type = c_bool })
let ltb t = Var ("<?", Tarrow { in_types = [t; t]; out_type = c_bool })

let mul t = Var ("*", Tarrow { in_types = [t; t]; out_type = t })
let add t = Var ("+", Tarrow { in_types = [t; t]; out_type = t })

let b_true = Var ("true", c_bool)
let b_false = Var ("false", c_bool)

(* pretty printing of formulas *)
(* - p: the function that outputs a string *)
(* - pt: a boolean indicating whether we need to print the types *)
(* - k: continuation *)

module StringSet = Set.Make(String)

(* operators that must be printed in infix notation *)
let infix = StringSet.of_list
  ["->"; "="; "<"; "*"; "+"; "-->"; "=?"; "<?"; "/\\"; "\\/"; "~"; "&&"; "||"; "~~"]

let rec pprint_list p pt k = function
  | [] -> k ()
  | [f] -> pprint p pt k f
  | f :: fs -> pprint p pt (fun () -> p " "; pprint_list p pt k fs) f

and pprint p pt k = function
  | App (Var (f, tf), [arg1; arg2]) when StringSet.mem f infix ->
    p "("; pprint p pt (fun () -> p (" " ^ f ^ " "); pprint p pt (fun () -> p ")"; k ()) arg2) arg1
  | App (f, args) -> begin
    p "(";
    pprint p pt (fun () -> p " "; pprint_list p pt (fun () -> p ")") args; k ()) f
  end
  | Var (x, tx) -> (p (x ^ (if pt then "[" ^ string_of_c_type tx ^ "]" else "")); k ())

let pprint_formula pt = pprint print_string pt (fun () -> ())
let pprint_endline pt = pprint print_string pt print_newline
let pprint_to_str pt form =
  let str = ref [] in
  pprint (fun s -> str := s :: !str) pt (fun () -> ()) form;
  String.concat "" (List.rev !str)

exception Type_error of string
(* formula typechecking function *)
(* formulas are really simple so there is no need for an environment parameter *)
(* (could make it CPS to typecheck big formulas) *)
let rec typecheck = function
  | Var (x, t) -> t (* a variable is well-typed *)
  | App (f, fs) ->
    (* a function application is well-typed if the types of the inputs of the function *)
    (* match the types of the arguments, which we check with mapM and list_eq *)
    match typecheck f with
    (* f typechecks and is a function *)
    | Tarrow { in_types; out_type } -> begin
      (* the arguments individually typecheck *)
      match list_eq (List.map typecheck fs) in_types with
      | Ok () -> out_type (* the input types match, the type of the application is the output type of the function *)
      | Error (-1) -> (* lists of different lengths, thus an invalid number of arguments *)
        raise (Type_error (Printf.sprintf "invalid number of arguments for %s" (pprint_to_str false f)))
      | Error n -> (* an input type does not match *)
        raise (Type_error (Printf.sprintf
          "argument %d is not well-typed for %s"
          (n + 1) (pprint_to_str false f)))
    end
    (* f typechecks but it is not a function *)
    | _ ->
      raise (Type_error (Printf.sprintf "%s is not a function, it cannot be applied" (pprint_to_str false f)))

let typecheck_function f =
  match typecheck f with
  | Tarrow { out_type; _ } -> out_type
  | t -> t

(* our algorithms *)

(* formula to formula map to store associations *)

module CFormula = struct
  type t = c_formula
  let compare = Stdlib.compare
end

module CFormulaMap = Map.Make(CFormula)
module CFormulaSet = Set.Make(CFormula)

(* logical connectors in bool and their equivalents in Prop *)
(* they all take bool arguments so translating them means translating the arguments *)
let logic_translations = CFormulaMap.of_seq (List.to_seq
  [ (implb, impl);
    (negb, c_not);
    (andb, c_and);
    (orb, c_or) ])

(* list of logical connectors in Prop *)
let logical_connectors =
  logic_translations
  |> CFormulaMap.to_seq
  |> Seq.map snd
  |> CFormulaSet.of_seq

(* boolean relations and their equivalents in Prop *)
let boolean_translations = CFormulaMap.of_seq (List.to_seq
  [ (ltb c_int, lt c_int);
    (eqb c_int, eq c_int);
    (eqb c_bool, eq c_bool);
    (eqb c_T, eq c_T) ])

(* describes an injection from a type to another, with morphism properties *)
type morphism =
  { from_type: c_type
  ; to_type: c_type
  ; name: string
  }

module Morphism = struct
  type t = morphism
  let compare = Stdlib.compare
end

module MorphismSet = Set.Make(Morphism)

(* known morphisms *)
let known_morphisms =
  [ { from_type = c_int; to_type = c_Z; name = "Z_of_int" };
    { from_type = c_Z; to_type = c_int; name = "int_of_Z" };
    { from_type = c_nat; to_type = c_Z; name = "Z_of_nat" };
    { from_type = c_Z; to_type = c_nat; name = "nat_of_Z" } ]

(* getting a function from a morphism type *)
let c_formula_of_morphism { from_type; to_type; name } =
  Var (name, Tarrow { in_types = [from_type]; out_type = to_type })

let known_morphisms_fun =
  known_morphisms
  |> List.to_seq
  |> Seq.map c_formula_of_morphism
  |> CFormulaSet.of_seq

(* known functions and their equivalents in Z *)
let arith_translations =
  let h = Hashtbl.create 17 in
  Hashtbl.add_seq h (List.to_seq
    [ (mul c_int, mul c_Z);
      (add c_int, add c_Z);
      (lt c_int, lt c_Z);
      (eq c_int, eq c_Z) ]
  );
  h

type uninterpreted_terms_internal = Lia of (c_formula, c_formula) Hashtbl.t * int ref | Full

let exists_morphism ~m_from:t ~m_to:t' = List.exists (fun m -> m.from_type = t && m.to_type = t') known_morphisms

exception Injection_error of string

(* injection function looking for a morphism from source_type to target_type and applying it to form *)
let inject_with_morphism ~source_type ~target_type formula =
  match List.find_opt (fun m -> m.from_type = source_type && m.to_type = target_type) known_morphisms with
  (* there is no morphism from source_type to target_type *)
  | None -> raise (Injection_error (Printf.sprintf
    "cannot inject %s into %s: no morphism found" (string_of_c_type source_type) (string_of_c_type target_type)))
  (* there is a morphism, we can apply it *)
  | Some m -> App (c_formula_of_morphism m, [formula])

let input_types_of_function = function
  | Var (_, Tarrow { in_types; _ }) -> in_types
  | formula -> raise (Type_error (Printf.sprintf "%s is not a function" (pprint_to_str false formula)))

let output_type_of_function = function
  | Var (_, Tarrow { out_type; _ }) -> out_type
  | formula -> raise (Type_error (Printf.sprintf "%s is not a function" (pprint_to_str false formula)))

(* tries to inject elements of a formula into the global target type *)
(* if nothing is possible, this does not fail *)
let rec try_inject_global ~global_target_type formula =
  let formula_type = typecheck formula in
  (* the formula already has the right type *)
  if formula_type = global_target_type then formula
  (* the formula does not have the right type, but it is injectable *)
  else if exists_morphism ~m_from:global_target_type ~m_to:formula_type then
    let injected_formula = inject ~global_target_type ~target_type:global_target_type formula in
    inject_with_morphism ~source_type:global_target_type ~target_type:formula_type injected_formula
  else
    (* we can do nothing on this formula, but we can try to inject its arguments, if it is a function application *)
    let walk_through ~global_target_type = function
    | Var _ as var -> var
    | App (f, args) ->
      let injected_arguments = List.map (try_inject_global ~global_target_type) args in
      App (f, injected_arguments)
    in
    walk_through ~global_target_type formula

(* injects the formula into the target_type, translating as much as possible below it too *)
(* this is stricter than the previous one, we need a term of type target_type as an output *)
and inject ~global_target_type ~target_type = function
  | Var (_, var_type) as var -> inject_with_morphism ~source_type:var_type ~target_type var
  | App (f, args) ->
    (* TODO: use target type in the table (we might want to translate to something else than Z) *)
    match Hashtbl.find_opt arith_translations f with
    (* f has an associated function f' in the target type, we change it and inject the arguments in their new types *)
    | Some f' ->
      let inject_argument (formula, target_type) = inject ~global_target_type ~target_type formula in
      let new_arg_types = input_types_of_function f' in
      let injected_args = List.map inject_argument (List.combine args new_arg_types) in
      App (f', injected_args)
    (* f is unknown but we know its output type is injectable into the target type *)
    (* we try to inject everything below f, making sure the types at the top of the AST below f have not changed *)
    | None ->
      let f_out_type = output_type_of_function f in
      let injected_args = List.map (try_inject_global ~global_target_type) args in
      inject_with_morphism ~source_type:f_out_type ~target_type:global_target_type (App (f, injected_args))

(* link between logic and arithmetic, translates predicates and uses inject / try_inject_global at the right time *)
let process_predicate ~target_arith_type (f, args) =
  let (f', inject_argument) =
    (* TODO: different table for predicates? *)
    match Hashtbl.find_opt arith_translations f with
    (* f is associated to another predicate taking arguments in the target type *)
    (* we inject them and replace f with f' *)
    | Some f' -> (f', inject ~global_target_type:target_arith_type ~target_type:target_arith_type)
    (* f is an unknown predicate, we do not change it and we try to inject its arguments into the global target type *)
    | None -> (f, try_inject_global ~global_target_type:target_arith_type)
  in
  let injected_args = List.map inject_argument args in
  App (f', injected_args)

(* first function called in the translation, handles logic and delegates the rest to process_predicate *)
let rec process_logic ~target_arith_type = function
  (* boolean variable, just add `= true` *)
  | Var (_, t) as var when t = c_bool -> App (eq c_bool, [var; b_true])
  (* Prop variable *)
  | Var _ as var -> var
  | App (f, args) ->
    if CFormulaSet.mem f logical_connectors then
      (* f is already a logical connector in Prop, we just process the logic of its arguments *)
      let processed_args = List.map (process_logic ~target_arith_type) args in
      App (f, processed_args)
    else match CFormulaMap.find_opt f logic_translations with
    (* f is a logical connector in bool, we translate it to its equivalent in Prop, as well as its arguments *)
    | Some f' ->
      let processed_args = List.map (process_logic ~target_arith_type) args in
      App (f', processed_args)
    (* f is not a logical connector, it is either a non-logical function or an unknown predicate *)
    | None ->
      let app' =
        match CFormulaMap.find_opt f boolean_translations with
        (* f is a boolean relation associated to f' in Prop, and its arguments are non-logical *)
        | Some f' -> (f', args)
        (* f is an unknown predicate, we change nothing *)
        | None -> (f, args)
      in
      (* now we process the predicate, injecting as much as we can below it into the target type *)
      process_predicate ~target_arith_type app'

(* TODO: lia mode with replacement of uninterpreted terms *)
let uninterpreted_terms_strategy = ref Full

let renaming formula =
  let rec mk_name_table_list s k = function
    | [] -> k s
    | f :: fs -> mk_name_table s (fun s' -> mk_name_table_list s' k fs) f
  and mk_name_table s k = function
    | Var (x, _) -> k (StringSet.add x s)
    | App (f, args) -> mk_name_table s (fun s' -> mk_name_table_list s' k args) f
  in
  let name_table = mk_name_table StringSet.empty (fun s -> s) formula in
  let rec fresh name = if StringSet.mem name name_table then fresh (name ^ "'") else name in
  let rec renaming' table name_table = function
    | Var _ as var -> var
    | App (f, args) as app ->
      match Hashtbl.find_opt table app with
      | Some var_alias -> var_alias
      | None ->
        let add_and_return formula = (Hashtbl.add table app formula; formula) in
        if not (CFormulaSet.mem f known_morphisms_fun) then
          let renamed_args = List.map (renaming' table name_table) args in
          add_and_return (App (f, renamed_args))
        else match args with
        | [Var (x, _)] ->
          let t = output_type_of_function f in
          add_and_return (Var (fresh x, t))
        | [App (g, args)] ->
          let t = output_type_of_function f in
          let find_type = function
            | Var (_, t) as var -> (t, var)
            | App (m, [formula]) when CFormulaSet.mem m known_morphisms_fun ->
              let formula' = renaming' table name_table formula in
              (typecheck formula', formula')
            | App (_, _) as app -> (typecheck app, app)
          in
          let arg_types = List.map find_type args in
          let g_name =
            match g with
            | Var (name, _) -> name
            | _ -> raise (Type_error "function is an application")
          in
          let g' = Var (fresh g_name, Tarrow { in_types = List.map fst arg_types; out_type = t }) in
          add_and_return (App (g', List.map snd arg_types))
        | _ ->
          let renamed_args = List.map (renaming' table name_table) args in
          add_and_return (App (f, renamed_args))
  in
  renaming' (Hashtbl.create 17) name_table formula

(* translation function from bool to Prop and from several arithmetic types to a single one *)
let translate ~lia_mode ~target_arith_type formula =
  if lia_mode then
    uninterpreted_terms_strategy := Lia (Hashtbl.create 17, ref 0)
  else
    uninterpreted_terms_strategy := Full;
  let formula' = process_logic ~target_arith_type formula in
  renaming formula'

(* test *)

(*
forall (x y z : int) (b1 b2 : bool) (f : int -> bool),
  ~~ (x <? z) --> 1 + y =? z || (b1 && f x =? b2).
*)
let f1 =
  let x = Var ("x", c_int) in
  let y = Var ("y", c_int) in
  let z = Var ("z", c_int) in
  let b1 = Var ("b1", c_bool) in
  let b2 = Var ("b2", c_bool) in
  let one = Var ("1", c_int) in
  let f = Var ("f", Tarrow { in_types = [c_int]; out_type = c_bool }) in
  App (implb, [
    App (negb, [App (ltb c_int, [x; z])]);
    App (orb, [
      App (eqb c_int, [App (add c_int, [one; y]); z]);
      App (andb, [b1; App (eqb c_bool, [App (f, [x]); b2])])])])

(*
forall x y : int, x * 1 + (y + 0) = 0.
*)
let f2 =
  let x = Var ("x", c_int) in
  let y = Var ("y", c_int) in
  let zero = Var ("0", c_int) in
  let one = Var ("1", c_int) in
  App (eq c_int, [
    App (add c_int, [
      App (mul c_int, [x; one]);
      App (add c_int, [y; zero])
    ]);
    zero
  ])

(*
forall (x y : int) (f : int -> int),
  x * 1 + y * 0 = f (x + y).
*)
let f3 =
  let x = Var ("x", c_int) in
  let y = Var ("y", c_int) in
  let zero = Var ("0", c_int) in
  let one = Var ("1", c_int) in
  let f = Var ("f", Tarrow { in_types = [c_int]; out_type = c_int }) in
  App (eq c_int, [
    App (add c_int, [
      App (mul c_int, [x; one]);
      App (add c_int, [y; zero])
    ]);
    App (f, [App (add c_int, [x; y])])
  ])

(*
forall (x y : T) (f : T -> U) (g : U -> int),
  g (f x) + g (f y) = g (f y) + g (f x).
*)
let f4 =
  let x = Var ("x", Tname "T") in
  let y = Var ("y", Tname "T") in
  let f = Var ("f", Tarrow { in_types = [Tname "T"]; out_type = Tname "U" }) in
  let g = Var ("g", Tarrow { in_types = [Tname "U"]; out_type = c_int }) in
  App (eq c_int, [
    App (add c_int, [
      App (g, [App (f, [x])]);
      App (g, [App (f, [y])])]);
    App (add c_int, [
      App (g, [App (f, [y])]);
      App (g, [App (f, [x])])])])

(*
forall (x y : T) (f : T -> int) (g : int -> V) (h : V -> int),
  h (g ((f x) + (f y))) + 0 = h (g ((f y) + (f x) + 0)).
*)
let f5 =
  let x = Var ("x", Tname "T") in
  let y = Var ("y", Tname "T") in
  let zero = Var ("0", c_int) in
  let f = Var ("f", Tarrow { in_types = [Tname "T"]; out_type = c_int }) in
  let g = Var ("g", Tarrow { in_types = [c_int]; out_type = Tname "V" }) in
  let h = Var ("h", Tarrow { in_types = [Tname "V"]; out_type = c_int }) in
  App (eq c_int, [
    App (add c_int, [
      App (h, [App (g, [App (add c_int, [App (f, [x]); App (f, [y])])])]);
      zero]);
    App (h, [App (g, [
      App (add c_int, [
        App (add c_int, [App (f, [y]); App (f, [x])]);
        zero])])])])

(*
forall (x y : int) (f : int -> U) (g : U -> V) (h : V -> int),
  0 + h (g (f (x + y))) = 0.
*)
let f6 =
  let x = Var ("x", c_int) in
  let y = Var ("y", c_int) in
  let zero = Var ("0", c_int) in
  let f = Var ("f", Tarrow { in_types = [c_int]; out_type = Tname "U" }) in
  let g = Var ("g", Tarrow { in_types = [Tname "U"]; out_type = Tname "V" }) in
  let h = Var ("h", Tarrow { in_types = [Tname "V"]; out_type = c_int }) in
  App (eq c_int, [
    App (add c_int, [
      zero;
      App (h, [App (g, [App (f, [App (add c_int, [x; y])])])])]);
    zero])

(*
forall (x y : int) (f : int -> int) (g : int -> int) (h : int -> nat) (w : nat -> T),
  x <? y * g (1 + f (x + y)) --> w (h x) =? w (h (f (y + 0))).
*)
let f7 =
  let x = Var ("x", c_int) in
  let y = Var ("y", c_int) in
  let zero = Var ("0", c_int) in
  let one = Var ("1", c_int) in
  let f = Var ("f", Tarrow { in_types = [c_int]; out_type = c_int }) in
  let g = Var ("g", Tarrow { in_types = [c_int]; out_type = c_int }) in
  let h = Var ("h", Tarrow { in_types = [c_int]; out_type = c_nat }) in
  let w = Var ("w", Tarrow { in_types = [c_nat]; out_type = c_T }) in
  App (implb, [
    App (ltb c_int, [
      x;
      App (mul c_int, [
        y;
        App (g, [
          App (add c_int, [
            one;
            App (f, [App (add c_int, [x; y])])])])])]);
    App (eqb c_T, [
      App (w, [App (h, [x])]);
      App (w, [App (h, [App (f, [App (add c_int, [y; zero])])])])])])

let f8 =
  let x = Var ("x", c_int) in
  let y = Var ("y", c_int) in
  let f = Var ("f", Tarrow { in_types = [c_int]; out_type = c_int }) in
  let g = Var ("g", Tarrow { in_types = [c_int]; out_type = c_int }) in
  App (eq c_int, [
    App (add c_int, [App (f, [App (g, [x])]); App (g, [y])]);
    App (add c_int, [App (g, [y]); App (f, [App (g, [x])])])
  ])

let test (name, form) =
  begin
    Printf.printf "=====*=====*===== TEST %s =====*=====*=====\n" name;

    pprint_formula false form;
    Printf.printf " : %s\n\n" (string_of_c_type (typecheck form));

    let form''' = translate ~lia_mode:false ~target_arith_type:c_Z form in
    pprint_formula false form''';
    Printf.printf " : %s\n\n" (string_of_c_type (typecheck form'''));
    Ok ()
  end
  |> Result.iter_error (Printf.printf "\nType error: %s\n")

let () =
  let test_cases = [f1; f2; f3; f4; f5; f6; f7; f8] in
  List.(iter test @@ combine (init (length test_cases) (fun i -> string_of_int (i + 1))) test_cases)