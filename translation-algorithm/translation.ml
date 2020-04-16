(* simplified Coq types *)
type coq_type =
  | TProp
  | Tbool
  | TZ
  | Tarrow of { in_types: coq_type list; out_type: coq_type } (* function types *)
  | Tname of string (* other types *)

(* simplified Coq terms *)
type coq_term =
  | App of coq_term * coq_term list (* function application *)
  | Var of string * coq_type (* variable *)
  | Const of string * coq_type (* constant *)
  | Forall of string * coq_type * coq_term (* universal quantifier with a body in Prop *)

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
let equiv = Var ("<->", Tarrow { in_types = [TProp; TProp]; out_type = TProp })

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

let b_true = Const ("true", Tbool)
let b_false = Const ("false", Tbool)
let p_True = Const ("True", TProp)
let p_False = Const ("False", TProp)

let is_true = Var ("is_true", Tarrow { in_types = [Tbool]; out_type = TProp })

let c_O = Const ("O", Tname "nat")
let c_S = Const ("S", Tarrow { in_types = [Tname "nat"]; out_type = Tname "nat" })

let rec mk_nat = function
  | 0 -> c_O
  | n -> App (c_S, [mk_nat (n - 1)])

(* pretty printing of terms *)

module StringSet = Set.Make(String)

(* operators that must be printed in infix notation *)
let infix = StringSet.of_list
  ["->"; "<->"; "="; "<"; "*"; "+"; "-->"; "=?"; "<?"; "/\\"; "\\/"; "~"; "&&"; "||"; "~~"]

let rec pprint_list print must_print_types terms k =
  match terms with
  | [] -> absurd_case ()
  | [term] -> pprint print must_print_types term k
  | term :: ts ->
    pprint print must_print_types term (fun () -> print " "; pprint_list print must_print_types ts k)

and pprint print must_print_types term k =
  match term with
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
  | Forall (x, tx, term') ->
    print "(forall ";
    print (x ^ (if must_print_types then " : " ^ string_of_coq_type tx else ""));
    print ", ";
    pprint print must_print_types term' (fun () -> print ")"; k ())

let pprint_term must_print_types term = pprint print_string must_print_types term identity
let pprint_endline must_print_types term = pprint print_string must_print_types term print_newline
let pprint_to_str must_print_types term =
  let str = ref [] in
  pprint (fun s -> str := s :: !str) must_print_types term identity;
  String.concat "" (List.rev !str)

(* ===== * ======================== * ===== *)
(* ===== * ===== typechecking ===== * ===== *)
(* ===== * ======================== * ===== *)

exception Type_error of string

let input_types_of_function = function
  | Const (_, Tarrow { in_types; _ })
  | Var (_, Tarrow { in_types; _ }) -> in_types
  | term -> raise (Type_error (Printf.sprintf "%s is not a function" (pprint_to_str false term)))

let output_type_of_function = function
  | Const (_, Tarrow { out_type; _ })
  | Var (_, Tarrow { out_type; _ }) -> out_type
  | term -> raise (Type_error (Printf.sprintf "%s is not a function" (pprint_to_str false term)))

let rec type_of = function
  | Const (_, t) | Var (_, t) -> t
  | Forall (_, _, term) -> type_of term
  | App (func, args) -> output_type_of_function func

module TypeEnv = Map.Make (String)

(* term typechecking function *)
let rec typecheck env = function
  (* a variable or constant is well-typed *)
  | Const (_, t) -> env
  | Var (x, t) -> begin
    match TypeEnv.find_opt x env with
    | None -> env
    | Some t' ->
      if t' = t then env
      else
        raise (Type_error (Printf.sprintf
          "variable %s has type %s, expected %s"
          x (string_of_coq_type t') (string_of_coq_type t)))
  end
  | Forall (x, t, term) -> (ignore (typecheck (TypeEnv.add x t env) term); env)
  (* a function application is well-typed if the types of the inputs of the function *)
  (* match the types of the arguments *)
  | App (func, args) ->
    ignore (typecheck env func);
    match type_of func with
    | Tarrow { in_types; out_type } -> begin
      match list_eq (List.map (fun arg -> ignore (typecheck env arg); type_of arg) args) in_types with
      (* the input types match, the type of the application is the output type of the function *)
      | Ok () -> env
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

let typecheck term = ignore (typecheck TypeEnv.empty term)

(* ===== * ======================= * ===== *)
(* ===== * ===== translation ===== * ===== *)
(* ===== * ======================= * ===== *)

(* describes an embedding from a type to another, with morphism properties *)
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

let coq_term_of_morphism { from_type; to_type; name } =
  Var (name, Tarrow { in_types = [from_type]; out_type = to_type })

let exists_morphism ~m_from:t ~m_to:t' = List.exists (fun m -> m.from_type = t && m.to_type = t') known_morphisms

(* functions that have an equivalent in another type *)
(* these are partly standard (logical connectors, etc) but can be declared by the user too  *)
let known_functions = Hashtbl.of_seq (List.to_seq
  [ (impl, implb);
    (c_not, negb);
    (c_and, andb);
    (c_or, orb);
    (equiv, eq Tbool);
    (lt c_int, ltb c_int);
    (eq c_int, eqb c_int);
    (eq c_nat, eqb c_nat);
    (eq c_T, eqb c_T);
    (eq Tbool, eqb Tbool);
    (mul c_int, mul TZ);
    (add c_int, add TZ);
    (add c_nat, add TZ);
    (ltb c_int, ltb TZ);
    (eqb c_int, eqb TZ);
    (eqb c_nat, eqb TZ) ])

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

exception Embedding_error of string

let name_of_function = function
  | Const (x, Tarrow _)
  | Var (x, Tarrow _) -> x
  | _ -> failwith "name_of_function"

(* finds all variable and function names in the term (to be able to generate fresh names) *)
let rec find_all_symbols = function
  | Const (x, _)
  | Var (x, _) -> StringSet.singleton x
  | App (func, args) ->
    List.fold_left
      (fun symbols arg -> StringSet.union symbols (find_all_symbols arg))
      (StringSet.singleton (name_of_function func))
      args
  | Forall (x, t, term) -> StringSet.union (StringSet.singleton x) (find_all_symbols term)

module CoqTermSet = Set.Make(struct
  type t = coq_term
  let compare = Stdlib.compare
end)

let logical_connectors = CoqTermSet.of_list [impl; c_or; c_and; c_not; equiv]

let constructors = Hashtbl.of_seq (List.to_seq
  [ (c_O, Const ("0", TZ));
    (c_S, Var ("add1", Tarrow { in_types = [TZ]; out_type = TZ })) ])

exception Eval_error

let rec eval_reduce = function
  | Const ("0", TZ) -> 0
  | App (Var ("add1", _), [arg]) -> eval_reduce arg + 1
  | _ -> raise Eval_error

let rec eval = function
  | App (Var ("add1", _), [arg]) -> App (add TZ, [eval arg; Const ("1", TZ)])
  | term -> term

let rec embed_constant ~translation_table ~fresh = function
  | Const (_, _) as const -> Hashtbl.find constructors const
  | App (Const _ as const, args) ->
    App (Hashtbl.find constructors const, List.map (embed_constant ~translation_table ~fresh) args)
  | term -> embed ~target:TZ ~compulsory:true ~translation_table ~fresh term

(* main embedding function: *)
(* - target is the target type *)
(* - compulsory indicates if we MUST embed or if we are only trying *)
(* - translation_table is the hashtable saving all the generated associated values during the process *)
(* - fresh is the function generating fresh names for associated functions and variables *)
and embed ~target ~compulsory ~translation_table ~fresh = function
  (* Prop constants and their equivalent in bool *)
  | Const (_, TProp) as const when target = Tbool -> if const = p_True then b_true else b_false

  (* if the type is already ok, do not change anything *)
  | Const (c, t) as const when t = target -> const

  (* otherwise look for a constructor equivalent or morphism *)
  | Const (c, t) as const -> begin
    match Hashtbl.find_opt constructors const with
    | Some (Const (_, t') as const') when t' = target -> const'
    | _ ->
      if exists_morphism ~m_from:t ~m_to:target then Const (c, target)
      else if compulsory then raise (Embedding_error (Printf.sprintf "cannot embed constant %s" c))
      else const
  end

  (* if the type is already ok, do not change anything *)
  | Var (x, t) as var when t = target -> var

  (* here we need to look for a morphism, but variables are given a new name and saved in the table *)
  | Var (x, t) as var ->
    let var' = Option.value (Hashtbl.find_opt translation_table var) ~default:var in
    if type_of var' = target then var'
    else if exists_morphism ~m_from:t ~m_to:target then begin
      let var' = Var (fresh x, target) in
      Hashtbl.add translation_table var var';
      var'
    end
    else if compulsory then raise (Embedding_error (Printf.sprintf "var %s cannot be embedded" x))
    else var
  
  (* universal quantifier, we just propagate the function to the argument in Prop and change the header if needed *)
  | Forall (x, t, term) ->
    if target <> TProp && compulsory then
      raise (Embedding_error (Printf.sprintf "a quantifier cannot be embedded into %s" (string_of_coq_type target)))
    else
      let embedded_term = embed ~target:TProp ~compulsory:true ~translation_table ~fresh term in
      let (x', t') =
        match Hashtbl.find_opt translation_table (Var (x, t)) with
        | Some (Var (x', t')) -> (x', t')
        | _ -> (x, t)
      in    
      Forall (x', t', embedded_term)
  
  (* constructor application *)
  | App (Const _, _) as const_app when target = TZ -> begin
    let embedded_const_app = embed_constant ~translation_table ~fresh const_app in
    try Const (string_of_int (eval_reduce embedded_const_app), TZ)
    with Eval_error -> eval embedded_const_app
  end
  
  (* logical connectors: try to propagate the embedding *)
  (* if everything changed to bool then we change the connector, and if the target is Prop, add `= true` *)
  (* if one of the arguments stayed in Prop, add `= true` to every argument in bool, but do not change the connector *)
  | App (f, args) when CoqTermSet.mem f logical_connectors ->
    let f' =
      match Hashtbl.find_opt known_functions f with
      | Some f' -> f'
      | None -> f
    in
    let embed_arg arg =
      let arg' = embed ~target:Tbool ~compulsory:false ~translation_table ~fresh arg in
      (arg', type_of arg')
    in
    let embedded_args = List.map embed_arg args in
    if List.exists (fun (_, t) -> t = TProp) embedded_args then
      App (f, List.map (fun (a, t) -> if t = Tbool then App (eq Tbool, [a; b_true]) else a) embedded_args)
    else if target = TProp then
      App (eq Tbool, [App (f', List.map fst embedded_args); b_true])
    else
      App (f', List.map fst embedded_args)

  (* boolean equalities with true or false constants values right or left must be embedded in a special way *)
  (* close to SMTCoq's Prop2bool tactic *)
  | App (f, [arg1; arg2]) when f = eq Tbool && arg1 = b_true ->
    let embedded_arg = embed ~target:Tbool ~compulsory:true ~translation_table ~fresh arg2 in
    if target = TProp && type_of embedded_arg = Tbool then
      App (eq Tbool, [embedded_arg; b_true])
    else
      embedded_arg
  | App (f, [arg1; arg2]) when f = eq Tbool && arg2 = b_true ->
    let embedded_arg = embed ~target:Tbool ~compulsory:true ~translation_table ~fresh arg1 in
    if target = TProp && type_of embedded_arg = Tbool then
      App (eq Tbool, [embedded_arg; b_true])
    else
      embedded_arg
  | App (f, [arg1; arg2]) when f = eq Tbool && arg1 = b_false ->
    let embedded_arg = embed ~target:Tbool ~compulsory:true ~translation_table ~fresh arg2 in
    if target = TProp && type_of embedded_arg = Tbool then
      App (eq Tbool, [embedded_arg; b_false])
    else
      App (negb, [embedded_arg])
  | App (f, [arg1; arg2]) when f = eq Tbool && arg2 = b_false ->
    let embedded_arg = embed ~target:Tbool ~compulsory:true ~translation_table ~fresh arg1 in
    if target = TProp && type_of embedded_arg = Tbool then
      App (eq Tbool, [embedded_arg; b_false])
    else
      App (negb, [embedded_arg])

  (* the is_true is already an embedding function, we must unfold it, or just remove it if the target is bool *)
  | App (f, [arg]) when f = is_true ->
    if target = TProp then App (eq Tbool, [embed ~target:Tbool ~compulsory:true ~translation_table ~fresh arg; b_true])
    else embed ~target:Tbool ~compulsory:true ~translation_table ~fresh arg

  (* general function application *)
  | App (f, args) ->
    let output_type = output_type_of_function f in
    match repeat_opt (Hashtbl.find_opt known_functions) f <|> Hashtbl.find_opt translation_table f with
    (* f is known and has a translation, or has been encountered and given a translation in the table earlier *)
    | Some f' ->
      let output_type' = output_type_of_function f' in
      if compulsory && output_type' <> target && not (target = TProp && output_type' = Tbool) then
        (* the associated function is irrelevant because it does not give the right type *)
        raise (Embedding_error (Printf.sprintf
          "associated function %s for %s does not have the right type"
          (pprint_to_str false f') (pprint_to_str false f)))
      else
        (* the associated function is right, we embed the arguments into their new types *)
        let f_in_types, f'_in_types = input_types_of_function f, input_types_of_function f' in
        let embed_arg arg target = embed ~target ~compulsory:true ~translation_table ~fresh arg in
        let embedded_args = List.map2 embed_arg args f'_in_types in
        (* if we got something in bool and the target is Prop, it is not lost, just add `= true` *)
        if target = TProp && output_type' = Tbool then
          App (eq Tbool, [App (f', embedded_args); b_true])
        else
          App (f', embedded_args)
    
    (* f is unknown *)
    | None ->
      let f_in_types = input_types_of_function f in
      let embed_arg arg type_before =
        if type_before = TProp then embed ~target:Tbool ~compulsory:false ~translation_table ~fresh arg
        else embed ~target:TZ ~compulsory:false ~translation_table ~fresh arg
      in
      let embedded_args = List.map2 embed_arg args f_in_types in
      let embedded_args_types = List.map type_of embedded_args in
      if target = output_type then
        if embedded_args_types = f_in_types then
          (* f has the right type and the types of the arguments have not changed after trying an embedding *)
          App (f, embedded_args)
        else begin
          (* f has the right type but the arguments have been embedded, we need to create an f' *)
          let f' =
            Var (fresh (name_of_function f), Tarrow { in_types = embedded_args_types; out_type = output_type })
          in
          Hashtbl.add translation_table f f';
          App (f', embedded_args)
        end
      else
        if exists_morphism ~m_from:output_type ~m_to:target then begin
          (* f does not have the right type, we need to create an f' *)
          let f' =
            Var (fresh (name_of_function f), Tarrow { in_types = embedded_args_types; out_type = target })
          in
          Hashtbl.add translation_table f f';
          App (f', embedded_args)
        end
        (* f does not have the right output type, and cannot be embedded *)
        else if compulsory then
          raise (Embedding_error (Printf.sprintf
            "application %s cannot be embedded correctly"
            (pprint_to_str false f)))
        (* embedding was not compulsory and the inputs have not changed, we can keep f *)
        else if embedded_args_types = f_in_types then App (f, embedded_args)
        else
        (* embedding was not compulsory, but the inputs have changed, so we can change f with an f' *)
        let f' =
          Var (fresh (name_of_function f), Tarrow { in_types = embedded_args_types; out_type = output_type })
        in
        Hashtbl.add translation_table f f';
        App (f', embedded_args)

let embed ~fresh term =
  embed ~target:TProp ~compulsory:true ~translation_table:(Hashtbl.create 17) ~fresh term

(* renaming algorithm, not finished *)

(* functions we do not want the renaming algorithm to change *)
let no_renaming_functions = CoqTermSet.of_list
  [impl; c_not; c_and; c_or; eq c_T; eq Tbool; eq TZ; lt TZ; mul TZ; add TZ]

(* finds occurrences of a function and returns the arguments found each time *)
let rec find_function ~func ~in_term =
    match in_term with
    | App (f, args) ->
      if f = func then [args]
      else List.concat @@ List.map (fun form -> find_function ~func ~in_term:form) args
    | _ -> []

(* same with the occurrences of an argument, and returns the list of functions applied to it *)
let rec find_arg ~arg ~in_term =
  match in_term with
  | App (f, args) ->
    let occurrences_in_args = List.concat @@ List.map (fun form -> find_arg ~arg ~in_term:form) args in
    if List.mem arg args then f :: occurrences_in_args else occurrences_in_args
  | _ -> []

(* replacement in a term of any node such that p node = true, with f node *)
let rec subst ~p ~f ~in_term =
  if p in_term then f in_term
  else match in_term with
  | App (func, args) -> App (func, List.map (fun arg -> subst ~p ~f ~in_term:arg) args)
  | _ -> in_term

let rename ~fresh term =
  let rec rename_list full_term seen_terms terms k =
    match terms with
    | [] -> k (List.rev seen_terms)
    | term :: ts ->
      rename full_term term (fun term' has_changed ->
        if has_changed then
          let full_term' = subst ~p:(fun f -> f = term) ~f:(constantly term') ~in_term:full_term in
          rename full_term' full_term' constantly
        else
          rename_list full_term (term' :: seen_terms) ts k)
  and rename full_term term k =
    match term with
    | App (f, args) when CoqTermSet.mem f no_renaming_functions ->
      rename_list full_term [] args (fun seen_terms -> k (App (f, seen_terms)) false)
    | App (f, args) -> begin
      let f_occurrences = find_function ~func:f ~in_term:full_term in
      match transpose_find_and_apply f_occurrences all_equal List.hd with
      (* the occurrences of f do not have a common argument *)
      | None ->
        rename_list full_term [] args (fun seen_terms -> k (App (f, seen_terms)) false)

      (* x is a common argument at the same position everytime f is called *)
      | Some x ->
        let x_occurrences = find_arg ~arg:x ~in_term:full_term in
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
            let full_term' = subst ~p ~f:replace ~in_term:full_term in
            k full_term' true
        (* x is used somewhere else so we cannot replace the application *)
        else rename_list full_term [] args (fun seen_terms -> k (App (f, seen_terms)) false)
    end
    | _ -> k term false
  in
  rename term term constantly

(* general toplevel translation function : embedding + renaming *)
let translate term =
  let symbols = ref (find_all_symbols term) in
  let rec fresh x =
    if StringSet.mem x !symbols then fresh (x ^ "'")
    else begin
      symbols := StringSet.add x !symbols;
      x
    end
  in
  term
  |> embed ~fresh
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
  App (is_true, [
    App (implb, [
      App (negb, [App (ltb c_int, [x; z])]);
      App (orb, [
        App (eqb c_int, [App (add c_int, [one; y]); z]);
        App (andb, [b1; App (eqb Tbool, [App (f, [x]); b2])])])])])

(*
forall x y : int,
  x * 1 + (y + 0) = 0.
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
forall (x y : int) (f g : int -> int) (h : int -> nat) (w : nat -> T),
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
  App (is_true, [
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
        App (w, [App (h, [App (f, [App (add c_int, [y; zero])])])])])])])

(*
forall (x y : int) (f g : int -> int),
  f (g x) + g y = g y + f (g x).
*)
let f8 =
  let x = Var ("x", c_int) in
  let y = Var ("y", c_int) in
  let f = Var ("f", Tarrow { in_types = [c_int]; out_type = c_int }) in
  let g = Var ("g", Tarrow { in_types = [c_int]; out_type = c_int }) in
  App (eq c_int, [
    App (add c_int, [App (f, [App (g, [x])]); App (g, [y])]);
    App (add c_int, [App (g, [y]); App (f, [App (g, [x])])])
  ])

(*
forall x y : int,
  x = y -> x = 0 -> y = 0.
*)
let f9 =
  let x = Var ("x", c_int) in
  let y = Var ("y", c_int) in
  let zero = Const ("0", c_int) in
  App (impl, [
    App (eq c_int, [x; y]);
    App (impl, [
      App (eq c_int, [x; zero]);
      App (eq c_int, [y; zero])
    ])
  ])

(*
forall x y : int,
  x = y -> is_true (x == 0) -> y = 0.
*)
let f10 =
  let x = Var ("x", c_int) in
  let y = Var ("y", c_int) in
  let zero = Const ("0", c_int) in
  App (impl, [
    App (eq c_int, [x; y]);
    App (impl, [
      App (is_true, [App (eqb c_int, [x; zero])]);
      App (eq c_int, [y; zero])
    ])
  ])

(*
forall (a : Prop) (b : bool),
  is_true b /\ ~ (is_true b) \/ a -> ~ (b = true) /\ b = false.
*)
let f11 =
  let a = Var ("a", TProp) in
  let b = Var ("b", Tbool) in
  App (impl, [
    App (c_or, [
      App (c_and, [
        App (is_true, [b]);
        App (c_not, [App (is_true, [b])])]);
      a]);
    App (c_and, [
      App (c_not, [App (eq Tbool, [b; b_true])]);
      App (eq Tbool, [b; b_false])])])

(*
forall (y : int) (f : int -> int),
  (forall x : int, f (x+1) = f x + 1) -> f (y + 2) = f y + 2.
*)
let f12 =
  let x = Var ("x", c_int) in
  let y = Var ("y", c_int) in
  let one = Const ("1", c_int) in
  let two = Const ("2", c_int) in
  let f = Var ("f", Tarrow { in_types = [c_int]; out_type = c_int }) in
  App (impl, [
    Forall ("x", c_int,
      App (eq c_int, [
        App (f, [App (add c_int, [x; one])]);
        App (add c_int, [App (f, [x]); one])]));
    App (eq c_int, [
      App (f, [App (add c_int, [y; two])]);
      App (add c_int, [App (f, [y]); two])])])

(*
forall x : nat,
  S x + 1 = S (x + 1).
*)
let f13 =
  let x = Var ("x", c_nat) in
  let one = Const ("1", c_nat) in
  App (eq c_nat, [
    App (add c_nat, [App (c_S, [x]); one]);
    App (c_S, [App (add c_nat, [x; one])])])

(*
1 + 3 + x = x + 4.
*)
let f14 =
  let x = Var ("x", c_nat) in
  let one = Const ("1", c_nat) in
  let three = mk_nat 3 in
  let four = mk_nat 4 in
  App (eq c_nat, [
    App (add c_nat, [one; App (add c_nat, [three; x])]);
    App (add c_nat, [x; four])])

let test (name, term) =
    Printf.printf "=====*=====*===== TEST %s =====*=====*=====\n" name;
    pprint_term false term;
    typecheck term;
    Printf.printf " : %s\n\n" (string_of_coq_type (type_of term));
    let term' = translate term in
    pprint_endline false term';
    pprint_term true term';
    typecheck term';
    Printf.printf " : %s\n\n" (string_of_coq_type (type_of term'))

let () =
  let test_cases = [f1; f2; f3; f4; f5; f6; f7; f8; f9; f10; f11; f12; f13; f14] in
  List.(iter test @@ combine (init (length test_cases) (fun i -> string_of_int (i + 1))) test_cases)