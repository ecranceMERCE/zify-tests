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

let (let*) r f = Result.bind r f

(* Haskell's mapM with ('a, 'b) result *)
(* ('a -> ('b, 'c) result) -> 'a list -> ('b list, 'c) result *)
(* generates a result from every 'a in the list, and returns the list of 'b wrapped in a result *)
(* stops on the first 'c error (if any) and returns it in the final result *)
let mapM f l =
  let rec mapM' acc = function
    | [] -> Ok (List.rev acc)
    | x :: xs ->
      let* a = f x in
      mapM' (a :: acc) xs
  in mapM' [] l

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

(* operators that must be printed in infix notation *)
let infix = ["->"; "="; "<"; "*"; "+"; "-->"; "=?"; "<?"; "/\\"; "\\/"; "~"; "&&"; "||"; "~~"]

let rec pprint_list p pt k = function
  | [] -> k ()
  | [f] -> pprint p pt k f
  | f :: fs -> pprint p pt (fun () -> p " "; pprint_list p pt k fs) f

and pprint p pt k = function
  | App (Var (f, tf), [arg1; arg2]) when List.mem f infix ->
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

(* formula typechecking function *)
(* formulas are really simple so there is no need for an environment parameter *)
(* (could make it CPS to typecheck big formulas) *)
let rec typecheck = function
  | Var (x, t) -> Ok t (* a variable is well-typed *)
  | App (f, fs) ->
    (* a function application is well-typed if the types of the inputs of the function *)
    (* match the types of the arguments, which we check with mapM and list_eq *)
    match typecheck f with
    (* f typechecks and is a function *)
    | Ok (Tarrow { in_types; out_type }) -> begin
      (* the arguments individually typecheck *)
      let* ts = mapM typecheck fs in
      match list_eq ts in_types with
      | Ok () -> Ok out_type (* the input types match, the type of the application is the output type of the function *)
      | Error (-1) -> (* lists of different lengths, thus an invalid number of arguments *)
        Error (Printf.sprintf "invalid number of arguments for %s" (pprint_to_str false f))
      | Error n -> (* an input type does not match *)
        Error (Printf.sprintf
          "argument %d is not well-typed for %s"
          (n + 1) (pprint_to_str false f))
    end
    (* f typechecks but it is not a function *)
    | Ok _ ->
      Error (Printf.sprintf "%s is not a function, it cannot be applied" (pprint_to_str false f))
    (* f does not typecheck *)
    | error -> error

let typecheck_function f =
  let* t = typecheck f in
  match t with
  | Tarrow { out_type; _ } -> Ok out_type
  | _ -> Ok t

(* our algorithms *)

(* formula to formula map to store associations *)
module CFormulaMap = Map.Make (
  struct
    type t = c_formula
    let compare = Stdlib.compare
  end)

(* logical connectors in bool and their equivalents in Prop *)
(* they all take bool arguments so translating them means translating the arguments *)
let logic_translations = CFormulaMap.of_seq (List.to_seq
  [ (implb, impl);
    (negb, c_not);
    (andb, c_and);
    (orb, c_or) ])

(* list of logical connectors in Prop *)
let logical_connectors = List.map snd (CFormulaMap.bindings logic_translations)

(* boolean relations and their equivalents in Prop *)
let boolean_translations = CFormulaMap.of_seq (List.to_seq
  [ (ltb c_int, lt c_int);
    (eqb c_int, eq c_int);
    (eqb c_bool, eq c_bool);
    (eqb c_T, eq c_T) ])

let rec bool_to_Prop = function
  (* boolean variable, just add `= true` *)
  | Var (_, t) as var when t = c_bool -> App (eq c_bool, [var; b_true])
  (* other variables *)
  | Var _ as var -> var
  (* function application *)
  | App (f, args) as app ->
    match CFormulaMap.find_opt f logic_translations with
    (* f is a logical connector, we translate it and its arguments *)
    | Some f' -> App (f', List.map bool_to_Prop args)
    (* f is not a logical connector, now we check if it is a boolean relation *)
    | None ->
      match CFormulaMap.find_opt f boolean_translations with
      (* f is a boolean relation associated to f' in Prop *)
      | Some f' -> App (f', args)
      (* f is an ordinary function, we change nothing *)
      | None -> app

(* describes an injection from a type to another, with morphism properties *)
type morphism =
  { from_type: c_type
  ; to_type: c_type
  ; name: string
  }

(* known morphisms *)
let known_morphisms =
  [ { from_type = c_int; to_type = c_Z; name = "Z_of_int" };
    { from_type = c_Z; to_type = c_int; name = "int_of_Z" };
    { from_type = c_nat; to_type = c_Z; name = "Z_of_nat" };
    { from_type = c_Z; to_type = c_nat; name = "nat_of_Z" } ]

(* getting a function from a morphism type *)
let c_formula_of_morphism { from_type; to_type; name } =
  Var (name, Tarrow { in_types = [from_type]; out_type = to_type })

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

(* injection function looking for a morphism from t_src to t_dest and applying it to form *)
let inject_with_morphism t_src t_dest form =
  match List.find_opt (fun m -> m.from_type = t_src && m.to_type = t_dest) known_morphisms with
  (* there is no morphism from t_src to t_dest *)
  | None -> Error (Printf.sprintf
    "cannot inject %s into %s: no morphism found" (string_of_c_type t_src) (string_of_c_type t_dest))
  (* there is a morphism, we can apply it *)
  | Some m ->
    let () = Printf.printf "injecting %s into %s by morphism %s\n" (pprint_to_str false form) (string_of_c_type t_dest) m.name in
    Ok (App (c_formula_of_morphism m, [form]))

(* injection function *)
let rec injection inject_unknown t = function
  (* the variable is already in t *)
  | Var (_, t') as var when t' = t -> Ok var
  (* the variable is not in t *)
  | Var (_, t') as var -> inject_with_morphism t' t var
  (* function application *)
  | App (f, fs) ->
    (* TODO : maybe use a graph data structure to allow several-step injections *)
    (* currently taking the first possible translation that has t as output_type... *)
    let type_filter f' =
      match typecheck_function f' with
      | Ok t' when t' = t || t' = TProp -> Some f'
      | _ -> None
    in
    match List.nth_opt (List.filter_map type_filter @@ Hashtbl.find_all arith_translations f) 0 with
    (* f is unknown *)
    | None -> (Printf.printf "unknown term %s\n" (pprint_to_str true f); inject_unknown t (f, fs))
    (* f is a relation between integers *)
    | Some f' ->
      let () = Printf.printf "%s is an integer relation\n" (pprint_to_str false f) in
      (* we need to check which injections must be done *)
      (* from the input and output types of f to the input and output types of f' *)
      match typecheck f, typecheck f' with
      | Ok (Tarrow tf), Ok (Tarrow tf') ->
        (* injecting only if needed *)
        let inject_arg (form, form_type, form_expected_type) =
          if form_type = form_expected_type then Ok form
          else injection inject_unknown form_expected_type form
        in
        (* injecting all the arguments *)
        let* injected_args = mapM inject_arg (combine3 fs tf.in_types tf'.in_types) in
        (* injecting the result if needed *)
        if tf'.out_type = t || tf'.out_type = TProp then Ok (App (f', injected_args))
        else inject_with_morphism tf'.out_type t (App (f', injected_args))
      | _ -> failwith "the formula to translate is not well-typed"

(* injection function for unknown applications, creating new variables to replace the whole sub-tree *)
let inject_unknown_lia (uninterpreted_table, fresh_counter) t (f, fs) =
  let app = App (f, fs) in
  let* t_app = typecheck app in
  match Hashtbl.find_opt uninterpreted_table app with
  (* the unknown function is in the table *)
  | Some form -> Ok form
  (* it is missing from the table *)
  | None ->
    (* new identifier *)
    let name = "v" ^ string_of_int !fresh_counter in
    incr fresh_counter;
    let* form =
      (* adding a morphism injection if needed before storing the translation in the table *)
      (* if the function to inject has output type Prop, then we are at the top of the subtree, *)
      (* thus we do not translate the output type *)
      if t_app = t || t_app = TProp then Ok (Var (name, t_app))
      else inject_with_morphism t_app t (Var (name, t_app))
    in
    (* memoisation before returning form *)
    Hashtbl.add uninterpreted_table app form;
    Ok form

let exists_morphism t t' = List.exists (fun m -> m.from_type = t && m.to_type = t') known_morphisms

(* injection function for unknown applications, looking for everything in the sub-tree that can be injected into type t *)
let rec inject_unknown_full t (f, fs) =
  let get_types = function
    | Tarrow { in_types; out_type } -> Ok (in_types, out_type)
    | _ -> Error "the unknown formula to inject is not a function"
  in
  let* tf = (typecheck f) in
  let* (in_types, out_type) = get_types tf in
  let inject_arg (form, form_type) =
    (* if the argument is already of type t, or if there isn't two morphisms between both types *)
    if form_type = t || not (exists_morphism form_type t && exists_morphism t form_type) then Ok form else
    (* we inject the argument, then inject it back with a morphism for f to typecheck correctly *)
    let* i = injection inject_unknown_full t form in
    inject_with_morphism t form_type i
  in
  let* injected_args = mapM inject_arg (List.combine fs in_types) in
  if out_type = t || out_type = TProp then
    (* the output type is already t, no further injection needed *)
    (* or the output type is Prop, we are at the top of the subtree, we do not translate anything *)
    Ok (App (f, injected_args))
  else inject_with_morphism out_type t (App (f, injected_args))

type uninterpreted_terms_internal = Lia of (c_formula, c_formula) Hashtbl.t * int ref | Full
type uninterpreted_terms_strategy = LiaStrategy | FullStrategy

(* translation function from integers to Z *)
let rec integers_to_Z uninterpreted_data = function
  (* if the formula is just a logical variable, we do nothing *)
  | Var _ as var -> var
  (* the formula is an application (we are in this case very often) *)
  | App (f, fs) as app ->
    if List.mem f logical_connectors then
      (* f is a logical connector, we just propagate the translation to the formulas below *)
      App (f, List.map (integers_to_Z uninterpreted_data) fs)
    else
    (* f is either a logical relation with integers or an unknown function *)
    (* that might take integers at the bottom of the AST *)
    (* in both cases, we arrived to the logical leaves, we switch to the arithmetic injection *)
    let inject_unknown =
      (* the injection function is different according to the strategy (handle uninterpreted terms or not) *)
      match uninterpreted_data with
      | Lia (table, counter) -> inject_unknown_lia (table, counter)
      | Full -> inject_unknown_full
    in
    match injection inject_unknown c_Z app with
    | Ok app' -> app'
    | Error e -> (print_endline e; app)

    (* TODO : predicates on unknown and non integer types? *)

(*
O -> 0
x -> TofZ ZofT x ->
op x y z -> op' (ZofT x) (ZofT y) (ZofT z)
f x y z -> f (TofZ ZofT x) (TofZ ZofT y) (TofZ ZofT z) -> 
*)

let translate uninterpreted_terms_strategy form =
  let uninterpreted_data =
    match uninterpreted_terms_strategy with
    | LiaStrategy -> Lia (Hashtbl.create 17, ref 0)
    | FullStrategy -> Full
  in
  form
  |> bool_to_Prop
  |> integers_to_Z uninterpreted_data

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

let test (name, form) =
  begin
    Printf.printf "=====*=====*===== TEST %s =====*=====*=====\n" name;

    pprint_formula false form;
    let* t = typecheck form in
    Printf.printf " : %s\n\n" (string_of_c_type t);

    print_endline "==[ bool_to_Prop ]==";
    let form' = bool_to_Prop form in
    pprint_formula false form';
    let* t' = typecheck form' in
    Printf.printf " : %s\n\n" (string_of_c_type t');

    print_endline "==[ translate_lia ]==";
    let form'' = translate LiaStrategy form in
    pprint_formula false form'';
    let* t'' = typecheck form'' in
    Printf.printf " : %s\n\n" (string_of_c_type t'');

    print_endline "==[ translate ]==";
    let form''' = translate FullStrategy form in
    pprint_formula false form''';
    let* t''' = typecheck form''' in
    Printf.printf " : %s\n\n" (string_of_c_type t''');

    print_endline "==[ with types ]==";
    pprint_endline true form''';
    Ok ()
  end
  |> Result.iter_error (Printf.printf "\nType error: %s\n")

let () =
  let test_cases = [f1; f2; f3; f4; f5; f6; f7] in
  List.(iter test @@ combine (init (length test_cases) (fun i -> string_of_int (i + 1))) test_cases)