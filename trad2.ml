(* modelling simplified Coq types *)

type c_type =
  | TProp (* Coq's Prop type *)
  | Tbool
  | Tarrow of { in_types: c_type list; out_type: c_type } (* function types with one or several inputs and an output *)
  | Tname of string (* other types *)

type c_formula =
  | App of c_formula * c_formula list (* function application *)
  | Var of string * c_type (* variable *)
  | Const of string * c_type

(* utils *)

(* displaying a type *)
let rec string_of_c_type = function
  | TProp -> "Prop"
  | Tbool -> "bool"
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

let (<|>) o o' = if o = None then o' else o

(* particular known types and values *)

let c_int = Tname "int"
let c_Z = Tname "Z"
let c_nat = Tname "nat"
let c_T = Tname "T"

let impl = Var ("->", Tarrow { in_types = [TProp; TProp]; out_type = TProp })
let c_and = Var ("/\\", Tarrow { in_types = [TProp; TProp]; out_type = TProp })
let c_or = Var ("\\/", Tarrow { in_types = [TProp; TProp]; out_type = TProp })
let c_not = Var ("~", Tarrow { in_types = [TProp]; out_type = TProp })

let implb = Var ("-->", Tarrow { in_types = [Tbool; Tbool]; out_type = Tbool })
let andb = Var ("&&", Tarrow { in_types = [Tbool; Tbool]; out_type = Tbool })
let orb = Var ("||", Tarrow { in_types = [Tbool; Tbool]; out_type = Tbool })
let negb = Var ("~~", Tarrow { in_types = [Tbool]; out_type = Tbool })

let eq t = Var ("=", Tarrow { in_types = [t; t]; out_type = TProp })
let lt t = Var ("<", Tarrow { in_types = [t; t]; out_type = TProp })

let eqb t = Var ("=?", Tarrow { in_types = [t; t]; out_type = Tbool })
let ltb t = Var ("<?", Tarrow { in_types = [t; t]; out_type = Tbool })

let mul t = Var ("*", Tarrow { in_types = [t; t]; out_type = t })
let add t = Var ("+", Tarrow { in_types = [t; t]; out_type = t })

let b_true = Var ("true", Tbool)
let b_false = Var ("false", Tbool)

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
  | Var (x, tx)
  | Const (x, tx) -> (p (x ^ (if pt then "[" ^ string_of_c_type tx ^ "]" else "")); k ())

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
  | Const (_, t)
  | Var (_, t) -> t (* a variable or constant is well-typed *)
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
          "argument %d (%s) is not well-typed for %s"
          (n + 1) (pprint_to_str false (List.nth fs n)) (pprint_to_str false f)))
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

(* test *)
let known_functions = Hashtbl.of_seq (List.to_seq
  [ (implb, impl);
    (negb, c_not);
    (andb, c_and);
    (orb, c_or);
    (ltb c_int, lt c_int);
    (eqb c_int, eq c_int);
    (eqb Tbool, eq Tbool);
    (eqb c_T, eq c_T);
    (mul c_int, mul c_Z);
    (add c_int, add c_Z);
    (lt c_int, lt c_Z);
    (eq c_int, eq c_Z) ])

let repeat_opt f x =
  let rec repeat_opt' f x =
    match f x with
    | None -> Some x
    | Some x' -> repeat_opt' f x'
  in
  match f x with
  | None -> None
  | Some x' -> repeat_opt' f x'

exception Translation_error of string
let name_of_function = function
  | Var (x, Tarrow _) -> x
  | _ -> failwith "name_of_function"
let fresh x = x
let rec translate' target_type translation_compulsory translation_table = function
  | Const (c, Tbool) when target_type = TProp -> if c = "true" then Const ("True", TProp) else Const ("False", TProp)
  | Const (c, t) as const when t = target_type -> const
  | Const (c, t) as const -> if exists_morphism ~m_from:t ~m_to:target_type then Const (c, target_type) else const
  | Var (_, Tbool) as var when target_type = TProp -> App (eq Tbool, [var; b_true])
  | Var (x, t) as var when t = target_type -> var
  | Var (x, t) as var ->
    let var' = Option.value (Hashtbl.find_opt translation_table var) ~default:var in
    let t' = typecheck var' in
    if t' = target_type then var'
    else if exists_morphism ~m_from:t ~m_to:target_type then begin
      let var' = Var (fresh x, target_type) in
      Hashtbl.add translation_table var var';
      var'
    end
    else if translation_compulsory then raise (Translation_error "var cannot be translated")
    else var
  | App (f, args) ->
    let output_type = output_type_of_function f in
    match repeat_opt (Hashtbl.find_opt known_functions) f <|> Hashtbl.find_opt translation_table f with
    | Some f' ->
      let f_in_types, f'_in_types = input_types_of_function f, input_types_of_function f' in
      let translate_arg (arg, type_before, type_after) =
        if type_before = type_after then arg else translate' type_after true translation_table arg
      in
      let translated_args = List.map translate_arg (combine3 args f_in_types f'_in_types) in
      App (f', translated_args)
      (* TODO: check output type and throw *)
    | None ->
      let f_in_types = input_types_of_function f in
      let translate_arg arg type_before =
        if type_before = TProp || type_before = c_Z then arg
        else if type_before = Tbool then translate' TProp false translation_table arg
        else translate' c_Z false translation_table arg
      in
      let translated_args = List.map2 translate_arg args f_in_types in
      let translated_args_types = List.map typecheck translated_args in
      if target_type = output_type then
        if translated_args_types = f_in_types then
          (* f has the right type and the arguments haven't changed *)
          App (f, translated_args)
        else begin
          (* f has the right type but the arguments have been injected, we need to create an f' *)
          let f' =
            Var (fresh (name_of_function f), Tarrow { in_types = translated_args_types; out_type = output_type })
          in
          Hashtbl.add translation_table f f';
          App (f', translated_args)
        end
      else
        if exists_morphism ~m_from:output_type ~m_to:target_type then begin
          (* f does not have the right type, we need to create an f' *)
          let f' =
            Var (fresh (name_of_function f), Tarrow { in_types = translated_args_types; out_type = target_type })
          in
          Hashtbl.add translation_table f f';
          App (f', translated_args)
        end
        else if translation_compulsory then raise (Translation_error "app cannot be translated")
        else App (f, translated_args)

  (* if new_output_type = Tbool then App (eq Tbool, [new_app; b_true]) else new_app *)

(*
forall (x y z : int) (b1 b2 : bool) (f : int -> bool),
  ~~ (x <? z) --> 1 + y =? z || (b1 && f x =? b2).
*)
let f1 =
  let x = Var ("x", c_int) in
  let y = Var ("y", c_int) in
  let z = Var ("z", c_int) in
  let b1 = Var ("b1", Tbool) in
  let b2 = Var ("b2", Tbool) in
  let one = Const ("1", c_int) in
  let f = Var ("f", Tarrow { in_types = [c_int]; out_type = Tbool }) in
  App (implb, [
    App (negb, [App (ltb c_int, [x; z])]);
    App (orb, [
      App (eqb c_int, [App (add c_int, [one; y]); z]);
      App (andb, [b1; App (eqb Tbool, [App (f, [x]); b2])])])])

(*
forall x y : int, x * 1 + (y + 0) = 0.
*)
let f2 =
  let x = Var ("x", c_int) in
  let y = Var ("y", c_int) in
  let zero = Const ("0", c_int) in
  let one = Const ("1", c_int) in
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
  let zero = Const ("0", c_int) in
  let one = Const ("1", c_int) in
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
  let zero = Const ("0", c_int) in
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
  let zero = Const ("0", c_int) in
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
  let zero = Const ("0", c_int) in
  let one = Const ("1", c_int) in
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
    Printf.printf "=====*=====*===== TEST %s =====*=====*=====\n" name;

    pprint_formula false form;
    Printf.printf " : %s\n\n" (string_of_c_type (typecheck form));

    (* let form' = translate ~lia_mode:false ~target_arith_type:c_Z form in *)
    let form' = translate' TProp true (Hashtbl.create 17) form in
    pprint_endline false form';
    pprint_formula true form';
    Printf.printf " : %s\n\n" (string_of_c_type (typecheck form'))

let () =
  let test_cases = [f1; f2; f3; f4; f5; f6; f7; f8] in
  List.(iter test @@ combine (init (length test_cases) (fun i -> string_of_int (i + 1))) test_cases)