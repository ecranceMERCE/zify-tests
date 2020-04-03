(* simplified Coq types *)
type coq_type =
  | TProp
  | Tbool
  | TZ
  | Tarrow of { in_types: coq_type list; out_type: coq_type } (* function types *)
  | Tname of string (* other types *)

(* simplified Coq formulas *)
type coq_formula =
  | App of coq_formula * coq_formula list (* function application *)
  | Var of string * coq_type (* variable *)
  | Const of string * coq_type (* constant *)

(* ===== * ================= * ===== *)
(* ===== * ===== utils ===== * ===== *)
(* ===== * ================= * ===== *)

let identity = fun x -> x
let constantly x = fun _ -> x
let absurd_case () = failwith "absurd case"

(* displaying a type *)
let rec string_of_coq_type = function
  | TProp -> "Prop"
  | Tbool -> "bool"
  | TZ -> "Z"
  | Tarrow { in_types; out_type } ->
    Printf.sprintf "(%s)"
      (String.concat " -> " (List.map string_of_coq_type (in_types @ [out_type])))
  | Tname type_name -> type_name

(* checks that l and l' are equal; if not, gives the index of the first values that are different *)
let list_eq l l' =
  let rec list_eq' n = function
    | ([], []) -> Ok ()
    | (x :: xs, y :: ys) -> if x = y then list_eq' (n + 1) (xs, ys) else Error n
    | _ -> Error (-1)
  in list_eq' 0 (l, l')

(* computes the transposition of a list of lists, *)
(* stopping if a predicate p is true on one of the obtained sub-lists, and calling a function f on it *)
let transpose_find_and_apply ll p f =
  let extract_first lr =
    let head, tail = List.hd !lr, List.tl !lr in
    lr := tail;
    head
  in
  let rec step = function
    | [] -> failwith "transpose'"
    | (lr :: _) as lrl ->
      (* we arrived at the end of the list of list references *)
      if !lr = [] then None
      else
        (* take the first element of every list referenced in lrl *)
        let xs = List.map extract_first lrl in
        (* if the predicate is true on the list of first elements (i.e. the transposed row), apply f and return *)
        if p xs then Some (f xs)
        (* otherwise continue *)
        else step lrl
  in
  step (List.map ref ll)

(* tests whether all elements of a list are equal *)
let all_equal = function
  | x :: xs -> List.for_all (fun x' -> x' = x) xs
  | [] -> true

(* finds the index of x in l, if it exists *)
let list_index x l =
  let rec list_index' n = function
    | [] -> None
    | x' :: xs' -> if x' = x then Some n else list_index' (n + 1) xs'
  in
  list_index' 0 l

(* removes the element at index i in l *)
let list_remove_at i l =
  let rec list_remove_at' acc n = function
    | [] -> failwith "list_remove_at"
    | x :: xs -> if n = i then List.rev_append acc xs else list_remove_at' (x :: acc) (n + 1) xs
  in
  list_remove_at' [] 0 l

(* allows an "or" operation on options *)
let (<|>) opt opt' = if opt = None then opt' else opt

(* particular known types and values *)

let c_int = Tname "int"
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

module StringSet = Set.Make(String)

(* operators that must be printed in infix notation *)
let infix = StringSet.of_list
  ["->"; "="; "<"; "*"; "+"; "-->"; "=?"; "<?"; "/\\"; "\\/"; "~"; "&&"; "||"; "~~"]

let rec pprint_list print must_print_types formulas k =
  match formulas with
  | [] -> absurd_case ()
  | [formula] -> pprint print must_print_types formula k
  | formula :: fs ->
    pprint print must_print_types formula (fun () -> print " "; pprint_list print must_print_types fs k)

and pprint print must_print_types formula k =
  match formula with
  | App (Var (func, _), [arg1; arg2]) when StringSet.mem func infix ->
    print "(";
    pprint print must_print_types arg1 (fun () ->
      print (" " ^ func ^ " ");
      pprint print must_print_types arg2 (fun () -> print ")"; k ()))
  | App (func, args) ->
    print "(";
    pprint print must_print_types func (fun () ->
      print " ";
      pprint_list print must_print_types args (fun () -> print ")"; k ()))
  | Var (x, tx)
  | Const (x, tx) -> (print (x ^ (if must_print_types then "[" ^ string_of_coq_type tx ^ "]" else "")); k ())

let pprint_formula must_print_types formula = pprint print_string must_print_types formula identity
let pprint_endline must_print_types formula = pprint print_string must_print_types formula print_newline
let pprint_to_str must_print_types formula =
  let str = ref [] in
  pprint (fun s -> str := s :: !str) must_print_types formula identity;
  String.concat "" (List.rev !str)

(* ===== * ======================== * ===== *)
(* ===== * ===== typechecking ===== * ===== *)
(* ===== * ======================== * ===== *)

exception Type_error of string

(* formula typechecking function *)
(* formulas are really simple so there is no need for an environment parameter *)
(* TODO: make it CPS to typecheck big formulas? *)
let rec typecheck = function
  (* a variable or constant is well-typed *)
  | Const (_, t)
  | Var (_, t) -> t
  (* a function application is well-typed if the types of the inputs of the function *)
  (* match the types of the arguments *)
  | App (func, args) ->
    match typecheck func with
    | Tarrow { in_types; out_type } -> begin
      match list_eq (List.map typecheck args) in_types with
      (* the input types match, the type of the application is the output type of the function *)
      | Ok () -> out_type

      (* lists of different lengths, thus an invalid number of arguments *)
      | Error (-1) ->
        raise (Type_error (Printf.sprintf "invalid number of arguments for %s" (pprint_to_str false func)))

      (* an input type does not match *)
      | Error n ->
        raise (Type_error (Printf.sprintf
          "argument %d (%s) is not well-typed for %s"
          (n + 1) (pprint_to_str false (List.nth args n)) (pprint_to_str false func)))
    end
    | _ ->
      raise (Type_error (Printf.sprintf "%s is not a function, it cannot be applied" (pprint_to_str false func)))

(* ===== * ======================= * ===== *)
(* ===== * ===== translation ===== * ===== *)
(* ===== * ======================= * ===== *)

(* describes an injection from a type to another, with morphism properties *)
type morphism =
  { from_type: coq_type
  ; to_type: coq_type
  ; name: string
  }

(* the known morphisms are declared by the user *)
let known_morphisms =
  [ { from_type = c_int; to_type = TZ; name = "Z_of_int" };
    { from_type = TZ; to_type = c_int; name = "int_of_Z" };
    { from_type = c_nat; to_type = TZ; name = "Z_of_nat" };
    { from_type = TZ; to_type = c_nat; name = "nat_of_Z" } ]

let coq_formula_of_morphism { from_type; to_type; name } =
  Var (name, Tarrow { in_types = [from_type]; out_type = to_type })

let exists_morphism ~m_from:t ~m_to:t' = List.exists (fun m -> m.from_type = t && m.to_type = t') known_morphisms

let input_types_of_function = function
  | Var (_, Tarrow { in_types; _ }) -> in_types
  | formula -> raise (Type_error (Printf.sprintf "%s is not a function" (pprint_to_str false formula)))

let output_type_of_function = function
  | Var (_, Tarrow { out_type; _ }) -> out_type
  | formula -> raise (Type_error (Printf.sprintf "%s is not a function" (pprint_to_str false formula)))

(* functions that have an equivalent in another type *)
(* these are partly standard (logical connectors, etc) but can be declared by the user too  *)
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

(* calls f x until x is None, and returns x *)
(* useful to go through known_functions several times *)
let repeat_opt f x =
  let rec repeat_opt' f x =
    match f x with
    | None -> Some x
    | Some x' -> repeat_opt' f x'
  in
  match f x with
  | None -> None
  | Some x' -> repeat_opt' f x'

exception Injection_error of string

let name_of_function = function
  | Var (x, Tarrow _) -> x
  | _ -> failwith "name_of_function"

(* finds all variable and function names in the formula (to be able to generate fresh names) *)
let rec find_all_symbols = function
  | Const (x, _)
  | Var (x, _) -> StringSet.singleton x
  | App (func, args) ->
    List.fold_left
      (fun symbols arg -> StringSet.union symbols (find_all_symbols arg))
      (StringSet.singleton (name_of_function func))
      args

(* main injection function: *)
(* - target is the target type *)
(* - compulsory indicates if we MUST inject or if we are only trying *)
(* - translation_table is the hashtable saving all the generated associated values during the process *)
(* - fresh is the function generating fresh names for associated functions and variables *)
let rec inject ~target ~compulsory ~translation_table ~fresh = function
  (* boolean constants and their equivalent in Prop *)
  | Const (c, Tbool) when target = TProp -> if c = "true" then Const ("True", TProp) else Const ("False", TProp)

  (* if the type is already ok, do not change anything *)
  | Const (c, t) as const when t = target -> const

  (* otherwise look for a morphism *)
  | Const (c, t) as const ->
    if exists_morphism ~m_from:t ~m_to:target then Const (c, target)
    else if compulsory then raise (Injection_error (Printf.sprintf "cannot inject constant %s" c))
    else const
  
  (* boolean variables are injected into Prop by adding "= true" *)
  | Var (_, Tbool) as var when target = TProp -> App (eq Tbool, [var; b_true])

  (* if the type is already ok, do not change anything *)
  | Var (x, t) as var when t = target -> var

  (* here we need to look for a morphism, but variables are given a new name and saved in the table *)
  | Var (x, t) as var ->
    let var' = Option.value (Hashtbl.find_opt translation_table var) ~default:var in
    if typecheck var' = target then var'
    else if exists_morphism ~m_from:t ~m_to:target then begin
      let var' = Var (fresh x, target) in
      Hashtbl.add translation_table var var';
      var'
    end
    else if compulsory then raise (Injection_error (Printf.sprintf "var %s cannot be injected" x))
    else var

  | App (f, args) ->
    let output_type = output_type_of_function f in
    match repeat_opt (Hashtbl.find_opt known_functions) f <|> Hashtbl.find_opt translation_table f with
    (* f is known and has a translation, or has been encountered and given a translation in the table earlier *)
    | Some f' ->
      let output_type' = output_type_of_function f' in
      if output_type' <> target then
        (* the associated function is irrelevant because it does not give the right type *)
        raise (Injection_error (Printf.sprintf
          "associated function %s for %s does not have the right type"
          (pprint_to_str false f') (pprint_to_str false f)))
      else
        (* the associated function is right, we inject the arguments into their new types *)
        let f_in_types, f'_in_types = input_types_of_function f, input_types_of_function f' in
        let inject_arg arg target = inject ~target ~compulsory:true ~translation_table ~fresh arg in
        let injected_args = List.map2 inject_arg args f'_in_types in
        App (f', injected_args)
    
    (* f is unknown *)
    | None ->
      let f_in_types = input_types_of_function f in
      let inject_arg arg type_before =
        (* TODO: remove first case? *)
        if type_before = TProp || type_before = TZ then arg
        else if type_before = Tbool then inject ~target:TProp ~compulsory:false ~translation_table ~fresh arg
        else inject ~target:TZ ~compulsory:false ~translation_table ~fresh arg
      in
      let injected_args = List.map2 inject_arg args f_in_types in
      let injected_args_types = List.map typecheck injected_args in
      if target = output_type then
        if injected_args_types = f_in_types then
          (* f has the right type and the types of the arguments have not changed after trying an injection *)
          App (f, injected_args)
        else begin
          (* f has the right type but the arguments have been injected, we need to create an f' *)
          let f' =
            Var (fresh (name_of_function f), Tarrow { in_types = injected_args_types; out_type = output_type })
          in
          Hashtbl.add translation_table f f';
          App (f', injected_args)
        end
      else
        if exists_morphism ~m_from:output_type ~m_to:target then begin
          (* f does not have the right type, we need to create an f' *)
          let f' =
            Var (fresh (name_of_function f), Tarrow { in_types = injected_args_types; out_type = target })
          in
          Hashtbl.add translation_table f f';
          App (f', injected_args)
        end
        (* f does not have the right output type, and cannot be injected *)
        else if compulsory then
          raise (Injection_error (Printf.sprintf
            "application %s cannot be injected correctly"
            (pprint_to_str false f)))
        (* injection was not compulsory and the inputs have not changed, we can keep f *)
        else if injected_args_types = f_in_types then App (f, injected_args)
        else
        (* injection was not compulsory, but the inputs have changed, so we can change f with an f' *)
        let f' =
          Var (fresh (name_of_function f), Tarrow { in_types = injected_args_types; out_type = output_type })
        in
        Hashtbl.add translation_table f f';
        App (f', injected_args)

(* toplevel version with less arguments, for convenience *)
let inject ~fresh formula =
  inject ~target:TProp ~compulsory:true ~translation_table:(Hashtbl.create 17) ~fresh formula

module CoqFormulaSet = Set.Make(struct
  type t = coq_formula
  let compare = Stdlib.compare
end)

(* functions we do not want the renaming algorithm to change *)
let no_renaming_functions = CoqFormulaSet.of_list
  [impl; c_not; c_and; c_or; eq c_T; eq Tbool; eq TZ; lt TZ; mul TZ; add TZ]

(* finds occurrences of a function and returns the arguments found each time *)
let rec find_function ~func ~in_formula =
    match in_formula with
    | App (f, args) ->
      if f = func then [args]
      else List.concat @@ List.map (fun form -> find_function ~func ~in_formula:form) args
    | _ -> []

(* same with the occurrences of an argument, and returns the list of functions applied to it *)
let rec find_arg ~arg ~in_formula =
  match in_formula with
  | App (f, args) ->
    let occurrences_in_args = List.concat @@ List.map (fun form -> find_arg ~arg ~in_formula:form) args in
    if List.mem arg args then f :: occurrences_in_args else occurrences_in_args
  | _ -> []

(* replacement in a formula of any node with p node = true, with f node *)
let rec subst ~p ~f ~in_formula =
  if p in_formula then f in_formula
  else match in_formula with
  | App (func, args) -> App (func, List.map (fun arg -> subst ~p ~f ~in_formula:arg) args)
  | _ -> in_formula

let rename ~fresh formula =
  let rec rename_list full_formula seen_formulas formulas k =
    match formulas with
    | [] -> k (List.rev seen_formulas)
    | formula :: fs ->
      rename full_formula formula (fun formula' has_changed ->
        if has_changed then
          let full_formula' = subst ~p:(fun f -> f = formula) ~f:(constantly formula') ~in_formula:full_formula in
          rename full_formula' full_formula' constantly
        else
          rename_list full_formula (formula' :: seen_formulas) fs k)
  and rename full_formula formula k =
    match formula with
    | App (f, args) when CoqFormulaSet.mem f no_renaming_functions ->
      rename_list full_formula [] args (fun seen_formulas -> k (App (f, seen_formulas)) false)
    | App (f, args) -> begin
      let f_occurrences = find_function ~func:f ~in_formula:full_formula in
      match transpose_find_and_apply f_occurrences all_equal List.hd with
      (* the occurrences of f do not have a common argument *)
      | None ->
        rename_list full_formula [] args (fun seen_formulas -> k (App (f, seen_formulas)) false)

      (* x is a common argument at the same position everytime f is called *)
      | Some x ->
        let x_occurrences = find_arg ~arg:x ~in_formula:full_formula in
        (* x is only used as an argument for f, so we can ignore x and replace f x other_args with f' other_args *)
        if all_equal x_occurrences then
          match list_index x args with
          | None -> absurd_case ()
          | Some index ->
            let p = function
              | App (func, _) when func = f -> true
              | _ -> false
            in
            let f', replace =
              let f_in_types, f_out_type = input_types_of_function f, output_type_of_function f in
              let f'_in_types = list_remove_at index f_in_types in
              if f'_in_types = [] then
                (* f was a one-argument function so it becomes a variable *)
                let new_f = Var (fresh (name_of_function f), f_out_type) in
                let replace = function
                  | App (_, args) -> new_f
                  | form -> form
                in
                new_f, replace
              else
                (* f becomes a function with one less argument *)
                let new_f =
                  Var (fresh (name_of_function f), Tarrow { in_types = f'_in_types; out_type = f_out_type })
                in
                let replace = function
                  | App (_, args) -> App (new_f, list_remove_at index args)
                  | form -> form
                in
                new_f, replace                
            in
            let full_formula' = subst ~p ~f:replace ~in_formula:full_formula in
            k full_formula' true
        (* x is used somewhere else so we cannot replace the application *)
        else rename_list full_formula [] args (fun seen_formulas -> k (App (f, seen_formulas)) false)
    end
    | _ -> k formula false
  in
  rename formula formula constantly

(* general toplevel translation function : injection + renaming *)
let translate formula =
  let symbols = ref (find_all_symbols formula) in
  let rec fresh x =
    if StringSet.mem x !symbols then fresh (x ^ "'")
    else begin
      symbols := StringSet.add x !symbols;
      x
    end
  in
  formula
  |> inject ~fresh
  (* |> rename ~fresh *)

(* ===== * ================= * ===== *)
(* ===== * ===== tests ===== * ===== *)
(* ===== * ================= * ===== *)

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
  let x = Var ("x", c_T) in
  let y = Var ("y", c_T) in
  let f = Var ("f", Tarrow { in_types = [c_T]; out_type = Tname "U" }) in
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
  let x = Var ("x", c_T) in
  let y = Var ("y", c_T) in
  let zero = Const ("0", c_int) in
  let f = Var ("f", Tarrow { in_types = [c_T]; out_type = c_int }) in
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

let test (name, formula) =
    Printf.printf "=====*=====*===== TEST %s =====*=====*=====\n" name;
    pprint_formula false formula;
    Printf.printf " : %s\n\n" (string_of_coq_type (typecheck formula));
    let formula' = translate formula in
    pprint_endline false formula';
    pprint_formula true formula';
    Printf.printf " : %s\n\n" (string_of_coq_type (typecheck formula'))

let () =
  let test_cases = [f1; f2; f3; f4; f5; f6; f7; f8] in
  List.(iter test @@ combine (init (length test_cases) (fun i -> string_of_int (i + 1))) test_cases)