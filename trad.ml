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

(* Haskell's mapM with ('a, 'b) result *)
(* ('a -> ('b, 'c) result) -> 'a list -> ('b list, 'c) result *)
(* generates a result from every 'a in the list, and returns the list of 'b wrapped in a result *)
(* stops on the first 'c error (if any) and returns it in the final result *)
let mapM f l =
  let rec mapM' acc = function
    | [] -> Ok (List.rev acc)
    | x :: xs ->
      match f x with
      | Ok a -> mapM' (a :: acc) xs
      | Error e -> Error e
  in mapM' [] l

(* checks that l and l' are equal; if not, gives the index of the first values that are different *)
let list_eq l l' =
  let rec list_eq' n = function
    | ([], []) -> Ok ()
    | (x :: xs, y :: ys) -> if x = y then list_eq' (n + 1) (xs, ys) else Error n
    | _ -> Error (-1)
  in list_eq' 0 (l, l')

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
(* - k: continuation *)

(* operators that must be printed in infix notation *)
let infix = ["->"; "="; "<"; "*"; "+"; "-->"; "=?"; "<?"; "/\\"; "\\/"; "~"; "&&"; "||"; "~~"]

let rec pprint_list p k = function
  | [] -> k ()
  | [f] -> pprint p k f
  | f :: fs -> pprint p (fun () -> p " "; pprint_list p k fs) f

and pprint p k = function
  | App (Var (f, tf), [arg1; arg2]) when List.mem f infix ->
    p "(";
    pprint p
      (fun () -> p (" " ^ f ^ " "); pprint p (fun () -> p ")"; k ()) arg2)
      arg1
  | App (f, args) -> begin
    p "(";
    pprint p (fun () -> p " "; pprint_list p (fun () -> p ")") args; k ()) f
  end
  | Var (x, _) -> (p x; k ())

let pprint = pprint print_string

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
      match mapM typecheck fs with
      (* the arguments individually typecheck *)
      | Ok ts -> begin
        match list_eq ts in_types with
        | Ok () -> Ok out_type (* the input types match, the type of the application is the output type of the function *)
        | Error (-1) -> (* lists of different lengths, thus an invalid number of arguments *)
          Error (fun () ->
            print_string "invalid number of arguments for "; pprint print_newline f)
        | Error n -> (* an input type does not match *)
          Error (fun () -> Printf.printf
            "argument %d is not well-typed for %a"
            (n + 1) (fun oc f -> pprint (fun () -> output_string oc "\n") f) f)
      end
      (* one of the arguments does not typecheck *)
      | Error e -> Error e
    end
    (* f typechecks but it is not a function *)
    | Ok _ ->
      Error (fun () ->
        pprint (fun () -> ()) f; print_string " is not a function, it cannot be applied")
    (* f does not typecheck *)
    | error -> error

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

let test_f1 () =
  print_string "f1 = ";
  pprint (fun () -> ()) f1;
  let () =
    match typecheck f1 with
    | Ok t -> Printf.printf " : %s\n" (string_of_c_type t)
    | Error f -> print_string "\nType error: "; f ()
  in
  let f1' = bool_to_Prop f1 in
  print_string "bool_to_Prop f1 = ";
  pprint (fun () -> ()) f1';
  match typecheck f1' with
  | Ok t -> Printf.printf " : %s\n" (string_of_c_type t)
  | Error f -> print_string "\nType error: "; f ()

type morphism =
  { morph_in_type: c_type
  ; morph_out_type: c_type
  ; morph_name: string
  }

let known_morphisms =
  [ { morph_in_type = c_int; morph_out_type = c_Z; morph_name = "Z_of_int" };
    { morph_in_type = c_Z; morph_out_type = c_int; morph_name = "int_of_Z" } ]

let c_formula_of_morphism { morph_in_type; morph_out_type; morph_name } =
  Var (morph_name, Tarrow { in_types = [morph_in_type]; out_type = morph_out_type })

let arith_translations = CFormulaMap.of_seq (List.to_seq
  [ (lt c_int, lt c_Z);
    (eq c_int, eq c_Z) ])
(* 
let inject t' = function
  | Var (x, t) as var -> begin
    match List.find_opt (fun m -> m.morph_in_type = t && m.morph_out_type = t') known_morphisms with
    | None -> Error (Printf.sprintf
      "cannot inject %s into %s: no morphism found" (string_of_c_type t) (string_of_c_type t'))
    | Some m -> Ok (App (c_formula_of_morphism m, [var]))
  end
  | App (f, fs) ->
    match CFormulaMap.find_opt f arith_translations with
    | None -> Error  (Printf.sprintf "cannot inject %s: "
    | Some f' ->
  
  
  Error "the term to inject is not a variable" *)

(*
O -> 0
x -> TofZ ZofT x ->
op x y z -> op' (ZofT x) (ZofT y) (ZofT z)
f x y z -> f (TofZ ZofT x) (TofZ ZofT y) (TofZ ZofT z) -> 
*)

let translate form = form

(* test *)

let () =
  test_f1 ();
  let form =
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
  in
  pprint (fun () -> ()) form;
  let () =
    match typecheck form with
    | Ok t -> Printf.printf " : %s\n" (string_of_c_type t)
    | Error f -> print_string "\nType error: "; f ()
  in
  let form' = translate form in
  pprint (fun () -> ()) form';
  match typecheck form' with
    | Ok t -> Printf.printf " : %s\n" (string_of_c_type t)
    | Error f -> print_string "\nType error: "; f ()