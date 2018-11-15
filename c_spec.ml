exception Error of string
let err s = raise (Error s)

(* variable names *)
type id = string
type label = string
type imm = int
type binop = Syntax.binOp

type ty = 
  | Int
  | Closure 
  | Tuple 
  | Defined

type op =
  | Var of id
  | Imm of imm

type exp = 
  | Decl of ty * id * op (* int id = op *)
  | Exp of op (* operand *)
  | Bin of id * binop * exp * exp 
  | If of op * exp 
  | Write of id * int * op (* id[i] = op *)
  | Return of op (* return op *)
  | Print of op
  | Read of id * op * int (* id = op[int] *)
  | ReadClosure of id * id * int (* read out_of_scope vars in closure*)
  | Label of label
  | Goto of label
  | Call of ty * id * id * id * op (* id = id(id.vars, x) *)
  | DeclareTuple of id * int
  | SetTupleValue of id * int * op
  | DeclareClosure of id (* closure aru_closure; *)
  | GetPointerOfClosure of id * id
  | SetClosurePointer of id * label (* aru_cl osure.f = b__recf00 *)
  | SetClosureLength of id * int (* aru_closure.length = 2 *)
  | DeclareClosureParams of int (* int params[i]; *)
  | StoreClosureParams of int * op (* params[i] = op *)
  | SetClosureParams of id (* aru_closure.vars = params *)
  (* | GetPointer of id  *)
  (* | GetParams of id *)
  | DeclarePointer of id
  | AssignPointer of id * id (* id = id.f *)
  | Exit

type funct = Funct of id * (id list) * (exp list)

let string_of_ty = function
  | Int -> "int"
  | Closure -> "closure*"
  | Tuple -> "int*"
  | Defined -> ""

let string_of_id (id: id) = (id: string)

let string_of_op = function
  | Var id -> id
  | Imm i -> string_of_int i

(* create_string ["hoge"; "fuga"; "piyo"] = "hoge fuga piyo" *)
let create_string l = 
  let len = List.length l in
  (List.fold_left (fun accum s -> accum ^ s) "" (
      List.mapi (fun i s -> if i = len - 1 then s else s ^ " ") l)) ^ ";\n"

let rec string_of_exp exp = 
  let rec lst_of_exp = function
    | Decl(ty, id, id2) -> [string_of_ty ty; string_of_id id; "="; string_of_op id2]
    | Exp(op) -> [string_of_op op]
    | Bin(id, op, e1, e2) ->
      let op_string = Syntax.string_of_op op in
      ["int"; id; "="] @ lst_of_exp e1 @ [op_string] @ lst_of_exp e2
    | If(op, e) -> ["if(" ^ string_of_op op ^ "){\n" ^ string_of_exp e ^ "}"]
    | Write(id, i, op) -> [id ^ "[" ^ string_of_int i ^ "]"; "="; string_of_op op]
    | Return op -> ["return"; string_of_op op]
    | Print op -> ["printf(\"%d\\n\", " ^ string_of_op op ^ ")"]
    | Read(sid, rop, i) -> ["int"; string_of_id sid; "="; string_of_op rop ^ "[" ^  string_of_int i ^ "]"]
    | ReadClosure(id, id2, i) -> ["int"; id; "="; id2 ^ "->vars[" ^ string_of_int i ^ "]"]
    | Label(l) -> [l ^ ":"]
    | Goto(l) -> ["goto"; l]
    | Call(ty, dest, pointer, closure, x) -> [string_of_ty ty; dest; "="; pointer ^ "(" ^ closure ^ ","; string_of_op x ^ ")"]
    | DeclareTuple(id, i) -> ["int"; id ^ "[" ^ string_of_int i ^ "]"]
    | SetTupleValue(id, i, op) -> [id ^ "[" ^ string_of_int i ^ "]"; "="; string_of_op op]
    | DeclareClosure(id) -> ["closure"; id]
    | GetPointerOfClosure(id1, id2) -> ["closure*"; id1; "="; "&" ^ id2]
    | SetClosurePointer(id, l) -> [id ^ "->f"; "="; l]
    | SetClosureLength(id, i) -> [id ^ "->length"; "="; string_of_int i]
    | DeclareClosureParams(i) -> ["int"; "params[" ^ string_of_int i ^ "]"]
    | StoreClosureParams(i, op) -> ["params[" ^ string_of_int i ^ "]"; "="; string_of_op op]
    | SetClosureParams id -> [id ^ "->vars"; "="; "params"]
    | DeclarePointer(id) -> ["int (*" ^ id ^ ")(closure*, const int)"]
    | AssignPointer(id1, id2) -> [id1; "="; id2 ^ "->f"]
    | Exit -> ["return 0"]
    (* | SetClosureVars(id, opl) *)
    (* | _ -> err "not implemented" *)
    (* | Call(op, id1, op2) -> [string_of_op op ^ "(" ^ string_of_id id1 ^ "," ; string_of_op op2 ^ ")"] *)
  in create_string (lst_of_exp exp)

let string_of_exp_list el = List.fold_left (fun accum e -> accum ^ string_of_exp e) "\n" el

let string_of_funct (Funct(id, pl, el)) = 
  let string_of_pl = 
    match pl with
    | [] -> ""
    | [p0; p1] -> "closure *" ^ p0 ^ ", " ^ "const int " ^ p1
    | _ -> err "unexpected number of params" in
  "int " ^ id ^ "(" ^ string_of_pl ^ "){\n" ^ string_of_exp_list el ^ "}\n\n"

let string_of_funct_list = List.fold_left (fun accum f -> accum ^ string_of_funct f) "" 

let header_string = 
  let hic = open_in "backend.c" in
  let rec read_file accum = 
    try let l = input_line hic in
      read_file (accum ^ "\n" ^ l)
    with End_of_file -> accum
  in (read_file "") ^ "\n\n"
