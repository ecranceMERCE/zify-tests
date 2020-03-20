(* types *)

type c_type =
  | TProp
  | Tarrow of { in_types: c_type list; out_type: c_type }
  | Tname of string  

type c_formula =
  | App of c_formula * c_formula list
  | Var of string * c_type

(* utils *)

let rec string_of_c_type = function
  | TProp -> "Prop"
  | Tarrow { in_types; out_type } ->
    Printf.sprintf "(%s)"
      (String.concat " -> " (List.map string_of_c_type (in_types @ [out_type])))
  | Tname n -> n

let mapM f l =
  let rec mapM' acc = function
    | [] -> Ok (List.rev acc)
    | x :: xs ->
      match f x with
      | Ok a -> mapM' (a :: acc) xs
      | Error e -> Error e
  in mapM' [] l

let list_eq l l' =
  let rec list_eq' n = function
    | ([], []) -> Ok ()
    | (x :: xs, y :: ys) -> if x = y then list_eq' (n + 1) (xs, ys) else Error n
    | _ -> Error (-1)
  in list_eq' 0 (l, l')

(* particular known types and functions *)

let c_int = Tname "int"
let c_Z = Tname "Z"
let c_nat = Tname "nat"
let c_T = Tname "T"

let impl = Var("->", Tarrow { in_types = [TProp; TProp]; out_type = TProp })
let eq t = Var("=", Tarrow { in_types = [t; t]; out_type = TProp })
let lt t = Var("<", Tarrow { in_types = [t; t]; out_type = TProp })
let mul t = Var("*", Tarrow { in_types = [t; t]; out_type = t })
let add t = Var("+", Tarrow { in_types = [t; t]; out_type = t })

(* pretty printing of formulas *)

let infix = ["->"; "="; "<"; "*"; "+"]

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

let rec typecheck = function
  | Var (x, t) -> Ok t
  | App (f, fs) ->
    match typecheck f with
    | Ok (Tarrow { in_types; out_type }) -> begin
      match mapM typecheck fs with
      | Ok ts -> begin
        match list_eq ts in_types with
        | Ok () -> Ok out_type
        | Error (-1) ->
          Error (fun () ->
            print_string "invalid number of arguments for "; pprint print_newline f)
        | Error n ->
          Error (fun () -> Printf.printf
            "argument %d is not well-typed for %a"
            (n + 1) (fun oc f -> pprint (fun () -> output_string oc "\n") f) f)
      end
      | Error e -> Error e
    end
    | Ok _ ->
      Error (fun () ->
        pprint (fun () -> ()) f; print_string " is not a function, it cannot be applied")
    | error -> error

(* our algorithm *)

let translate form = form

(* test *)

let () =
  let form =
    let x = Var ("x", c_int) in
    let y = Var ("y", c_int) in
    let zero = Var ("0", c_int) in
    let one = Var ("1", c_int) in
    let f = Var ("f", Tarrow { in_types = [c_int]; out_type = c_int }) in
    let g = Var ("g", Tarrow { in_types = [c_int]; out_type = c_int }) in
    let h = Var ("h", Tarrow { in_types = [c_int]; out_type = c_nat }) in
    let w = Var ("w", Tarrow { in_types = [c_nat]; out_type = c_T }) in
    App (impl, [
      App (lt c_int, [
        x;
        App (mul c_int, [
          y;
          App (g, [
            App (add c_int, [
              one;
              App (f, [App (add c_int, [x; y])])])])])]);
      App (eq c_T, [
        App (w, [App (h, [x])]);
        App (w, [App (h, [App (f, [App (add c_int, [y; zero])])])])])])
  in
  pprint (fun () -> ()) form;
  match typecheck form with
  | Ok t -> Printf.printf " : %s\n" (string_of_c_type t)
  | Error f -> print_endline "\nType error: "; f ()