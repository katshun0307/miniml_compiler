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

let rec string_of_exp e = 
  let make_paren l = 
    (List.fold_left (fun s n -> s ^ ", " ^ string_of_exp n) "(" l ) ^ ")" in
  match e with
  | Var id -> id
  | ILit i -> string_of_int i
  | BLit b -> string_of_bool b
  | BinOp(op, e1, e2) -> "BinOp" ^ make_paren [e1; e2]
  | IfExp(cond, e1, e2) -> "IfExp" ^ make_paren [cond; e1; e2]
  | LetExp(id, e1, e2) -> "LetExp" ^ make_paren [Var id; e1; e2]
  | FunExp(id, e) -> "FunExp" ^ make_paren [Var id; e]
  | AppExp(e1, e2) -> "AppExp" ^ make_paren [e1; e2]
  | LetRecExp(id, p, e1, e2) -> "LetRecExp" ^ make_paren[Var id; Var p; e1; e2]
  | LoopExp(id, e1, e2) -> "LoopExp" ^ make_paren[Var id; e1; e2]
  | RecurExp(e) -> "RecurExp" ^ make_paren [e]
  | TupleExp(e1, e2) -> "Tuple(" ^ string_of_exp e1 ^ ", " ^ string_of_exp e2 ^ ")"
  | ProjExp(e, i) -> "Proj(" ^ string_of_exp e ^ ", " ^ string_of_int i ^ ")"

let rec recur_app_exp folding e =
  (* recursive application of function fold to exp recursively *)
  let f = recur_app_exp folding in
  match e with
  | Var id -> f e
  | ILit i -> f e
  | BLit b -> f e
  | BinOp(op, e1, e2) -> BinOp(op, f e1, f e2)
  | IfExp(cond, e1, e2) -> IfExp(f cond, f e1, f e2)
  | LetExp(id, e1, e2) -> LetExp(id, f e1, f e2)
  | FunExp(id, e) -> FunExp(id, f e)
  | AppExp(e1, e2) -> AppExp(f e1, f e2)
  | LetRecExp(id, p, e1, e2) -> LetRecExp(id, p, f e1, f e2)
  | LoopExp(id, e1, e2) -> LoopExp(id, f e1, f e2)
  | RecurExp(e) -> RecurExp(f e)
  | TupleExp(e1, e2) -> TupleExp(f e1, f e2)
  | ProjExp(e, i) -> ProjExp(f e, i)
