open Syntax 

(* 値の定義 *)

(* exval は式を評価して得られる値．dnval は変数と紐付けられる値．今回
   の言語ではこの両者は同じになるが，この2つが異なる言語もある．教科書
   参照． *)
type exval =
  | IntV of int
  | BoolV of bool
  | TupleV of exval * exval
  | ProcV of id * exp * dnval Environment.t ref
and dnval = exval

exception Error of string

let err s = raise (Error s)

(* pretty printing *)
let rec string_of_exval = function
    IntV i -> string_of_int i
  | BoolV b -> string_of_bool b
  | TupleV(v1, v2) -> 
    "(" ^ string_of_exval v1 ^ ", " ^ string_of_exval v2 ^ ")"
  | ProcV _ -> "<fun(´･ω･｀* (⊃⌒＊⌒)>"

let pp_val v = print_string (string_of_exval v)

let rec apply_prim op arg1 arg2 = match op, arg1, arg2 with
    Plus, IntV i1, IntV i2 -> IntV (i1 + i2)
  | Plus, _, _ -> err ("Both arguments must be integer: +")
  | Mult, IntV i1, IntV i2 -> IntV (i1 * i2)
  | Mult, _, _ -> err ("Both arguments must be integer: *")
  | Lt, IntV i1, IntV i2 -> BoolV (i1 < i2)
  | Lt, _, _ -> err ("Both arguments must be integer: <")

let rec find l n = 
  match l with 
  | top :: rest -> if top = n then true else find rest n
  | [] -> false

let multiple_decls_sanity lst = 
  let rec loop l defined = 
    match l with 
    | (id, _) :: rest -> if find defined id then false else loop rest (id :: defined)
    | [] -> true
  in loop lst []

let rec eval_exp env = function
    Var x -> 
    (try Environment.lookup x env with 
       Environment.Not_bound -> err ("Variable not bound: " ^ x))
  | ILit i -> IntV i
  | BLit b -> BoolV b
  | BinOp (op, exp1, exp2) -> 
    let arg1 = eval_exp env exp1 in
    let arg2 = eval_exp env exp2 in
    apply_prim op arg1 arg2
  (* | LogicOp(op, e1, e2) -> 
     ( match op with 
      | And -> let arg1 = eval_exp env e1 in 
        if arg1 = BoolV(false) then BoolV(false) else 
          let arg2 = eval_exp env e2 in if (arg2 = BoolV(true)) || (arg2 = BoolV(false)) then arg2 else err("non boolean values supplied: &&")
      | Or -> let arg1 = eval_exp env e1 in
        if arg1 = BoolV(true) then BoolV(true) else
          let arg2 = eval_exp env e2 in if (arg2 = BoolV(true)) || (arg2 = BoolV(false)) then arg2 else err("non boolean values supplied: ||")) *)
  | IfExp (exp1, exp2, exp3) ->
    let test = eval_exp env exp1 in
    (match test with
     | BoolV true -> eval_exp env exp2 
     | BoolV false -> eval_exp env exp3
     | _ -> err ("Test expression must be boolean: if"))
  | FunExp (params, exp) -> let dummyenv = ref Environment.empty in dummyenv := env;
    ProcV(params, exp, dummyenv)
  | AppExp (exp1, exp2) -> (
      let funval = eval_exp env exp1 in
      let arg = eval_exp env exp2 in 
      (match funval with 
       (* recurisive function *)
       | ProcV(id, body, env_ref) -> let eval_env = Environment.extend id arg !env_ref in
         eval_exp eval_env body
       | e -> err ("Non function value is applied")))
  | LetExp(id, e1, e2) -> 
    let eval_e1 = eval_exp env e1 in
    let eval_env =  Environment.extend id eval_e1 env in
    eval_exp eval_env e2
  | LetRecExp (id, para, exp1, exp2) ->
    let dummyenv = ref Environment.empty in
    let newenv = Environment.extend id (ProcV(para, exp1, dummyenv)) env in
    dummyenv := newenv;
    eval_exp newenv exp2
  | LoopExp(id, e1, e2) -> err "not implemented"
  | RecurExp(e) -> err "not implemented"
  | TupleExp(e1, e2) -> 
    let v1 = eval_exp env e1 in
    let v2 = eval_exp env e2 in 
    TupleV(v1, v2)
  | ProjExp(e, i) -> 
    (match eval_exp env e with
     | TupleV(v1, v2) -> if i = 1 then v1
       else if i = 2 then v2 
       else err "ProjExp: index not valid"
     | _ -> err "error: projection of non-tuple")

let eval_decl env = function
    Exp e -> let v = eval_exp env e in ("-", env, v)
