exception Error of string
let err s = raise (Error s)

type id = string

type binOp = Plus | Mult | Lt

let string_of_op = function
    Plus -> "+"
  | Mult -> "*"
  | Lt   -> "<"

type exp =
    Var       of id
  | ILit      of int
  | BLit      of bool
  | BinOp     of binOp * exp * exp
  | IfExp     of exp * exp * exp
  | LetExp    of id * exp * exp
  | FunExp    of id * exp
  | AppExp    of exp * exp
  | LetRecExp of id * id * exp * exp
  | LoopExp   of id * exp * exp (* loop <id> = <exp> in <exp> *)
  | RecurExp  of exp            (* recur <exp> *)
  | TupleExp  of exp * exp      (* (<exp>, <exp>) *)
  | ProjExp   of exp * int      (* <exp> . <int> *)

type program = 
    Exp of exp

(* declare types *)
type tyvar = int

type ty = 
  | TyInt
  | TyBool
  | TyVar of tyvar
  | TyFun of ty * ty
  | TyTuple of ty * ty

(* print tyvar to temrinal *)
let tyvar_string_of_int n =
  (* 26 * block + offset *)
  let start_code = Char.code 'a' in
  let alphabet_of_int n = 
    (if n <= 26 then
       Char.escaped (Char.chr (n + start_code))
     else err "unexpected input") in
  let offset = n mod 26 in
  let block = (n - offset) / 26 in
  if block = 0 then "'" ^ alphabet_of_int offset
  else "'" ^ alphabet_of_int offset ^ string_of_int block

let rec string_of_ty = function
  | TyInt ->  "int"
  | TyBool ->  "bool"
  | TyTuple(a, b) -> "(" ^ string_of_ty a ^ ", " ^ string_of_ty b ^ ")"
  | TyVar id ->  tyvar_string_of_int id
  | TyFun(a, b) -> 
    (match a with
     | TyFun (_, _) -> "(" ^ string_of_ty a ^ ") -> " ^ string_of_ty b
     | _ ->  string_of_ty a ^ " -> " ^ string_of_ty b )

(* return fresh type variable *)
let fresh_tyvar = 
  let counter = ref 0 in
  let body () =
    let v = !counter in
    counter := v + 1; v
  in body

(* return all type variables in a given type *)
let freevar_ty ty_in = 
  let rec loop ty current = 
    (match ty with
     | TyVar a -> MySet.insert a current
     | TyFun(a, b) -> MySet.union (loop a current) (loop b current)
     | _ -> current) in
  loop ty_in MySet.empty
