open Pretty
module S = Syntax

exception Error of string
let err s = raise (Error s)

type id = S.id
type binOp = S.binOp

let fresh_id = Misc.fresh_id_maker "_"

(* ==== 値 ==== *)
type value =
    Var  of id
  | IntV of int

let int_of_bool b = 
  if b then 1 else 0

(* ==== 式 ==== *)
type cexp =
    ValExp    of value
  | BinOp     of binOp * value * value
  | AppExp    of value * value
  | IfExp     of value * exp * exp
  | TupleExp  of value * value
  | ProjExp   of value * int

and exp =
    CompExp   of cexp
  | LetExp    of id * cexp * exp
  | LetRecExp of id * id * exp * exp
  | LoopExp   of id * cexp * exp
  | RecurExp  of value

(* ==== Formatter ==== *)

let string_of_norm e =
  let pr_of_op = function
      S.Plus -> text "+"
    | S.Mult -> text "*"
    | S.Lt -> text "<" in
  let pr_of_value = function
      Var id -> text id
    | IntV i ->
      let s = text (string_of_int i) in
      if i < 0 then text "(" <*> s <*> text ")" else s
  in
  let rec pr_of_cexp p e =
    let enclose p' e = if p' < p then text "(" <*> e <*> text ")" else e in
    match e with
      ValExp v -> pr_of_value v
    | BinOp (op, v1, v2) ->
      enclose 2 (pr_of_value v1 <+> pr_of_op op <+> pr_of_value v2)
    | AppExp (f, v) ->
      enclose 3 (pr_of_value f <+> pr_of_value v)
    | IfExp (v, e1, e2) ->
      enclose 1
        (group ((nest 2
                   (group ((text "if 0 <")
                           <+> pr_of_value v
                           <+> text "then"
                           <|> pr_of_exp 1 e1))) <|>
                (nest 2
                   (group (text "else" <|> pr_of_exp 1 e2)))))
    | TupleExp (v1, v2) ->
      text "(" <*> pr_of_value v1 <*> text ","
      <+> pr_of_value v2 <*> text ")"
    | ProjExp (v, i) ->
      enclose 2 (pr_of_value v <*> text "." <*> text (string_of_int i))
  and pr_of_exp p e =
    let enclose p' e = if p' < p then text "(" <*> e <*> text ")" else e in
    match e with
      CompExp ce -> pr_of_cexp p ce
    | LetExp (id, ce, e) ->
      enclose 1
        ((nest 2 (group (text "let" <+> text id <+>
                         text "=" <|> pr_of_cexp 1 ce)))
         <+> text "in" <|> pr_of_exp 1 e)
    | LetRecExp (id, v, body, e) ->
      enclose 1
        ((nest 2 (group (text "let" <+> text "rec" <+>
                         text id <+> text v <+>
                         text "=" <|> pr_of_exp 1 body)))
         <+> text "in" <|> pr_of_exp 1 e)
    | LoopExp (id, ce, e) ->
      enclose 1
        ((nest 2 (group (text "loop" <+> text id <+>
                         text "=" <|> pr_of_cexp 1 ce)))
         <+> text "in" <|> pr_of_exp 1 e)
    | RecurExp v ->
      enclose 3 (text "recur" <+> pr_of_value v)
  in layout (pretty 30 (pr_of_exp 0 e))

(* ==== 正規形への変換 ==== *)
let rec norm_exp (e: Syntax.exp) (f: cexp -> exp) (sigma: id Environment.t) = 
  match e with
  | S.Var i -> 
    let maybe_fail i = 
      try f(ValExp(Var(Environment.lookup i sigma)))
      with Environment.Not_bound -> (* should not enter here *)
        f (ValExp(Var ("_" ^ i ^ "temp"))) 
    in maybe_fail i 
  | S.ILit i ->  f (ValExp (IntV i))
  | S.BLit b -> f (ValExp (IntV (int_of_bool b)))
  | BinOp(op, e1, e2) -> 
    let x1 = fresh_id "bin" in
    let x2 = fresh_id "bin" in
    (norm_exp e1 (fun x ->
         (norm_exp e2 (fun y ->
              (LetExp(x2, y, LetExp(x1, x, f (BinOp(op, Var x1, Var x2))))))) sigma) sigma)
  | IfExp(cond, e1, e2) -> 
    let x = fresh_id "if" in
    (* norm_exp e1 (fun y ->
        LetExp(x, y, f (IfExp(Var x, f y, norm_exp e2 f sigma)))) sigma *)
    norm_exp cond (fun condy -> 
        LetExp(x, condy, f (IfExp(Var x, norm_exp e1 (fun x -> CompExp x) sigma, norm_exp e2 (fun x -> CompExp x) sigma)))) sigma
  | LetExp(id, e1, e2) -> 
    let t1 = fresh_id "let" in
    let sigma' = Environment.extend id t1 sigma in
    norm_exp e1 (fun y1 -> 
        LetExp(t1, y1, norm_exp e2 f sigma')) sigma
  | FunExp(id, e) -> 
    let funf = fresh_id "funf" in
    let funx = fresh_id "funx" in
    (* let rec funf funx = e[id-> funx] in f *)
    let sigma' = Environment.extend id funx sigma in
    LetRecExp(funf, funx, norm_exp e (fun ce -> CompExp ce) sigma', f (ValExp(Var funf)))
  | AppExp(e1, e2) -> 
    let t1 = fresh_id "app" in
    let t2 = fresh_id "app" in
    norm_exp e1 (fun y1 -> 
        (norm_exp e2 (fun y2 -> 
             LetExp(t1, y1, LetExp(t2, y2, f (AppExp(Var t1, Var t2)))))) sigma) sigma
  | LetRecExp(funct, id, e1, e2) -> 
    let recf = fresh_id "recf" in
    let recx = fresh_id "recx" in
    let sigma' = Environment.extend funct recf (Environment.extend id recx sigma) in
    LetRecExp(recf, recx, norm_exp e1 (fun ce -> CompExp ce) sigma', norm_exp e2 f sigma')
  | LoopExp(id, e1, e2) -> 
    let loopvar = fresh_id "loopval" in
    let loopinit = fresh_id "loopinit" in
    let sigma' = Environment.extend id loopvar sigma in
    (* norm_exp e1 (fun y1 -> 
        norm_exp e2 (fun y2 -> 
            LetExp(loopinit, y1, LoopExp(loopvar, ValExp(Var loopinit), f y2))) sigma') sigma' *)
    norm_exp e1 (fun y1 -> 
        LetExp(loopinit, y1, LoopExp(loopvar, ValExp(Var loopinit), norm_exp e2 f sigma'))) sigma
  | RecurExp(e) -> 
    let t = fresh_id "recur" in
    norm_exp e (fun y1 -> 
        LetExp(t, y1, RecurExp(Var t))) sigma
  | TupleExp(e1, e2) -> 
    let t1 = fresh_id "tuple" in
    let t2 = fresh_id "tuple" in
    norm_exp e1 (fun y1 -> 
        norm_exp e2 (fun y2 -> 
            LetExp(t1, y1, LetExp(t2, y2, f (TupleExp(Var t1, Var t2))))) sigma) sigma
  | ProjExp(e, i) ->
    let t = fresh_id "proj" in
    norm_exp e (fun y -> 
        LetExp(t, y, f (ProjExp(Var t, i)))) sigma

and normalize e = norm_exp e (fun ce -> CompExp ce) Environment.empty


(* ==== recur式が末尾位置にのみ書かれていることを検査 ==== *)
(* task4: S.exp -> unit *)
let rec recur_check e is_tail: unit =   
  let recur_err () = err "illegal usage of recur" in
  S.(match e with
      | RecurExp _ -> 
        if is_tail then () 
        else recur_err ()
      | LoopExp (x, e1, e2) -> 
        recur_check e1 false; 
        recur_check e2 true
      | IfExp(e1, e2, e3) -> 
        recur_check e1 false;
        recur_check e2 is_tail;
        recur_check e3 is_tail
      | LetExp(x, e1, e2) -> 
        recur_check e1 false;
        recur_check e2 is_tail
      | LetRecExp(f, x, e1, e2) -> 
        recur_check e1 false;
        recur_check e2 is_tail
      | FunExp(_, e) | ProjExp(e, _) -> 
        recur_check e false
      | BinOp(_, e1, e2) | AppExp(e1, e2) | TupleExp(e1, e2) -> 
        recur_check e1 false;
        recur_check e2 false
      | _ -> () (* Var, ILit, BLit *)
    )

(* ==== entry point ==== *)
let rec convert prog =
  recur_check prog false;
  normalize prog
