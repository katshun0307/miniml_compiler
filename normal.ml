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
  | BoolV of bool (* added*)

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
    (* added for BoolV *)
    | BoolV b -> 
      let s = text (string_of_bool b) in s
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
and normalize (prog: S.exp) = (* CompExp (ValExp (IntV 1)) *)
  (* normal substitution for syntax.Exp *)
  let subst_exp_1 e_in id e_new =
    let rec subst_inner e = match e with
      | S.Var _ -> if id = e then e_new else e
      | _ -> e
    in S.recur_app_exp subst_inner e_in
  in
  (* special substitution for second step *)
  let rec subst_exp_2 x subster substee = 
    let recur_app = subst_exp_2 x subster in
    match substee with
    | CompExp ValExp var -> if var = x then subster else substee
    | CompExp _ -> substee
    | LetExp(i, c,  e) -> LetExp(i, c, recur_app e)
    | LetRecExp(i1, i2, e1, e2) -> LetRecExp(i1, i2, recur_app e1, recur_app e2)
    | LoopExp(i, c, e) -> LoopExp(i, c, recur_app e)
    | RecurExp(v) -> substee in
  let special_subst_1 ~substee ~x ~subster = 
    (* specal substitution for syntax.Exp *)
    let subst_app e = match e with
      | S.Var _ -> if e = x then subster else e
      | _ -> e in
    S.recur_app_exp subst_app substee
  in
  let rec special_subst_2 ~substee ~x ~subster = 
    (* special substitution for normal.Exp *)
    (match subster with
     | LetExp(a, e1, e2) -> LetExp(a, e1, special_subst_2 substee x e2)
     | _ -> subst_exp_2 substee x subster
    ) in
  let rec c_of_e e = 
    let variable_conversion = ref MySet.empty in
    let append_conv x _x = variable_conversion := (MySet.insert (x, _x) !variable_conversion) in
    S.(match e with 
        | S.Var x -> append_conv e x;
          Var x
        | S.ILit i -> ILit i
        | S.BLit b -> BLit b
        | S.BinOp(op, e1, e2) -> 
          let x1 = fresh_id "b" in
          let x2 = fresh_id "b" in
          let e1_eval = c_of_e e1 in
          let e2_eval = c_of_e e2 in
          append_conv e1 x1;
          append_conv e2 x2;
          LetExp(x1, e1_eval, LetExp(x2, e2_eval, BinOp(op, Var x1, Var x2)))
        | S.IfExp(cond, e1, e2) -> 
          let cond_eval = c_of_e cond in
          IfExp(cond_eval, e1, e2)
        | S.LetExp(id, e1, e2) -> 
          let t1 = fresh_id "t" in
          let e1_eval = c_of_e e1 in
          let ev = subst_exp_1 (c_of_e e2) (Var id) (Var t1) in
          append_conv e1 t1;
          LetExp(t1, e1_eval, ev)
        | S.FunExp(id, e) -> 
          (* reformat fun expression to recursive let *)
          let t1 = fresh_id "f" in
          LetRecExp(t1, t1, subst_exp_1 e (Var id) (Var t1), Var t1)
        | S.AppExp(e1, e2) -> 
          let x1 = fresh_id "a" in
          let x2 = fresh_id "a" in
          let e1_eval = c_of_e e1 in
          let e2_eval = c_of_e  e2 in 
          append_conv e1 x1;
          append_conv e2 x2;
          LetExp(x1, e1_eval, LetExp(x2, e2_eval, AppExp(Var x1, Var x2)))
        | S.LetRecExp(id, p, e1, e2) -> 
          let t1 = fresh_id "p" in
          let e1_eval = c_of_e e1 in
          append_conv e1 t1;
          LetRecExp(id, t1, subst_exp_1 e1_eval (Var p) (Var t1), c_of_e e2)
        | _ -> err "not implemented")
  in let rec norm_of_c = function
      (* val = x | n | true | false *)
      | S.Var x -> CompExp(ValExp (Var x))
      | S.ILit i -> CompExp(ValExp (IntV i))
      | S.BLit b -> CompExp(ValExp (BoolV b))
      | S.BinOp(op, e1, e2) -> (* bop * val * val *)
        (match e1, e2 with
         | S.ILit i, S.ILit j -> CompExp(BinOp (op, IntV i, IntV j))
         | _ -> err "norm_of_c: encountered non ILit at BinOp")
      | S.IfExp(cond, e1, e2) -> (* value * exp * exp *)
        (match cond with
         | S.BLit b -> 
           let e1' = norm_of_c e1 in
           let e2' = norm_of_c e2 in
           CompExp(IfExp(BoolV b, e1', e2'))
         | _ -> err "norm_of_c: encounterd non BLit at IfExp")
      | S.LetExp(id, e1, e2) -> (* id * exp * exp *)
        let x = Var (fresh_id "spsubst") in
        let subster = norm_of_c e1 in
        let substee = LetExp(id, ValExp x, norm_of_c e2) in
        subst_exp_2 x subster substee
      | S.FunExp(id, e) -> err "norm_of_c: FunExp should be removed in 1st conversion"
      | S.AppExp(e1, e2) -> (* val * val *)
        (match norm_of_c e1, norm_of_c e2 with
         | CompExp (ValExp e1'), CompExp (ValExp e2') -> 
           CompExp (AppExp (e1', e2'))
         | _ -> err "norm_of_c: AppExp should have value")
      | LetRecExp(_) -> err "norm_of_c: not implemented yet"
      | LoopExp(_) -> err "not implemented yet"
      | RecurExp(_) -> err "not implemented yet"
      | TupleExp(v1, v2) -> (* val * val ??? or Var * Var ? *)
        (match norm_of_c v1, norm_of_c v2 with
         | CompExp ValExp v1', CompExp ValExp v2' -> CompExp (TupleExp (v1', v2'))
         | _ -> err "norm_of_c: value should be in tuple")
      | ProjExp(v, i) -> (* val * int *)
        (match norm_of_c v with 
         | CompExp ValExp v' -> CompExp (ProjExp (v', i))
         | _ -> err "norm_of_c: value should be in projectee val")
        (* | _ -> err "not implemented (norm_of_c)" *)
  in norm_of_c (c_of_e prog)

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
        recur_check e2 is_tail
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
