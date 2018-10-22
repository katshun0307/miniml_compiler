open Pretty
module S = Syntax
module N = Normal

exception Error of string
let err s = raise (Error s)

type id = S.id
type binOp = S.binOp

let fresh_id = N.fresh_id

(* ==== 値 ==== *)
type value =
    Var  of id
  | IntV of int

(* ==== 式 ==== *)
type cexp =
    ValExp    of value
  | BinOp     of binOp * value * value
  | AppExp    of value * value list     (* NEW *)
  | IfExp     of value * exp * exp
  | TupleExp  of value list             (* NEW *)
  | ProjExp   of value * int

and exp =
    CompExp   of cexp
  | LetExp    of id * cexp * exp
  | LetRecExp of id * id list * exp * exp  (* NEW *)
  | LoopExp   of id * cexp * exp
  | RecurExp  of value

(* ==== Formatter ==== *)

let string_of_closure e =
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
  let pr_of_values = function
      [] -> text "()"
    | v :: vs' ->
      (text "(" <*>
       (List.fold_left
          (fun d v -> d <*> text "," <+> pr_of_value v)
          (pr_of_value v) vs')
       <*> (text ")"))
  in
  let pr_of_ids = function
      [] -> text "()"
    | id :: ids' ->
      (text "(" <*>
       (List.fold_left
          (fun d i -> d <*> text "," <+> text i)
          (text id) ids')
       <*> (text ")"))
  in
  let rec pr_of_cexp p e =
    let enclose p' e = if p' < p then text "(" <*> e <*> text ")" else e in
    match e with
      ValExp v -> pr_of_value v
    | BinOp (op, v1, v2) ->
      enclose 2 (pr_of_value v1 <+> pr_of_op op <+> pr_of_value v2)
    | AppExp (f, vs) ->
      enclose 3 (pr_of_value f <+> pr_of_values vs)
    | IfExp (v, e1, e2) ->
      enclose 1
        (group ((nest 2
                   (group ((text "if 0 <")
                           <+> pr_of_value v
                           <+> text "then"
                           <|> pr_of_exp 1 e1))) <|>
                (nest 2
                   (group (text "else" <|> pr_of_exp 1 e2)))))
    | TupleExp vs -> pr_of_values vs
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
    | LetRecExp (id, parms, body, e) ->
      enclose 1
        ((nest 2 (group (text "let" <+> text "rec" <+> text id <+>
                         pr_of_ids parms <+>
                         text "=" <|> pr_of_exp 1 body)))
         <+> text "in" <|> pr_of_exp 1 e)
    | LoopExp (id, ce, e) ->
      enclose 1
        ((nest 2 (group (text "loop" <+> text id <+>
                         text "=" <|> pr_of_cexp 1 ce)))
         <+> text "in" <|> pr_of_exp 1 e)
    | RecurExp v ->
      enclose 3 (text "recur" <+> pr_of_value v)
  in layout (pretty 40 (pr_of_exp 0 e))

(* == helper functions === *)
(* get all free variables in an expression *)
let convert_id (i: N.id): id = "_" ^ i

let convert_val = function
  | N.Var v -> Var ("_" ^ v)
  | N.IntV i -> IntV i

let get_out_of_scope_variables (e: N.exp) (included: N.id list): value list = 
  let rec loop_e ex accum incl = 
    let rec loop_ce cex caccum incl = 
      N.(match cex with
          | ValExp v | ProjExp(v, _) ->
            (match (List.find_opt (fun x -> Var x = v) incl), v with
             | Some x, _ -> caccum
             | None, Var _ -> MySet.insert v caccum
             | None, _ -> caccum)
          | BinOp(_, v1, v2) | AppExp(v1, v2) | TupleExp(v1, v2) -> 
            MySet.union (loop_ce (ValExp v1) caccum incl) (loop_ce (ValExp v2) caccum incl)
          | IfExp(v, e1, e2) ->
            MySet.union (loop_ce (ValExp v) caccum incl) (MySet.union (loop_e e1 accum incl) (loop_e e2 accum incl)))
    in 
    N.(match ex with
        | LetExp(i, cex, ex) -> 
          MySet.union (loop_ce cex accum incl) (loop_e ex accum (i::incl))
        | LoopExp(i, cex, ex) -> 
          MySet.union (loop_ce cex accum (i:: incl)) (loop_e ex accum (i:: incl))
        | LetRecExp(i1, i2, e1, e2) -> 
          MySet.union (loop_e e1 accum (i2::incl)) (loop_e e2 accum (i2::incl))
        | CompExp(ce) -> loop_ce ce accum incl
        | _ -> accum
      )
  in
  List.map convert_val (MySet.to_list (loop_e e MySet.empty included))

(* === conversion to closed normal form === *)
let rec closure_exp (e: N.exp) (f: cexp -> exp) (sigma: cexp Environment.t): exp = 
  match e with
  | N.CompExp(N.ValExp(Var v)) -> 
    let may_fail v = 
      try
        f (Environment.lookup ("_" ^ v) sigma)
      with _ -> f (ValExp(Var ("_" ^ v)))
    in may_fail v
  | N.CompExp(N.ValExp(IntV i)) -> f (ValExp(IntV i))
  | N.CompExp(N.BinOp(op, v1, v2)) -> f (BinOp(op, convert_val v1, convert_val v2))
  | N.CompExp(N.AppExp(v1, v2)) -> 
    let new_app0 = fresh_id "closure_app" in
    LetExp(new_app0, ProjExp(convert_val v1, 0), 
           f (AppExp(Var new_app0, [convert_val v1; convert_val v2])))
  | N.CompExp(N.IfExp(v, e1, e2)) -> 
    (* closure_exp e1 (fun y1 -> 
        closure_exp e2 (fun y2 -> 
            CompExp(IfExp(convert_val v, f y1, f y2))) sigma) sigma *)
    f (IfExp(convert_val v, closure_exp e1 (fun ce -> CompExp ce) sigma, closure_exp e2 (fun ce -> CompExp ce) sigma))
  | N.CompExp(N.TupleExp (v1, v2)) -> f(TupleExp([convert_val v1; convert_val v2]))
  | N.CompExp(N.ProjExp (v, i)) -> f(ProjExp(convert_val v, i-1)) (* {1, 2} -> {0, 1} *)
  | N.LetExp(id, ce1, e2) -> 
    closure_exp (CompExp ce1) (fun y1 -> 
        LetExp(convert_id id, y1, closure_exp e2 f sigma)) sigma
  | N.LetRecExp(funct, id, e1, e2) -> 
    let recpointer = fresh_id ("b_" ^ funct) in
    let out_of_scope_vars = get_out_of_scope_variables e1 [id] in
    let funct_tuple_list = (Var recpointer:: out_of_scope_vars) in
    let rec make_tuple_env l i env =  (* make environment from id to projection to var in closure *)
      match l with 
      | Var hd:: tl ->
        let env' =  Environment.extend hd (ProjExp(convert_val (Var funct), i)) env in
        make_tuple_env tl (i+1) env'
      | [] -> env
      | _ -> (match l with 
          | hd:: tl -> err ("unknown input in make_tuple_env" ^ "\n" ^ string_of_closure(CompExp(ValExp(hd))))
          | _ -> err "none valid match") in
    let sigma' = make_tuple_env out_of_scope_vars 1 Environment.empty in
    let closure_contents = TupleExp(funct_tuple_list) in
    let e1' = closure_exp e1 (fun ce -> CompExp(ce)) sigma' in
    let e2' = LetExp(convert_id funct, closure_contents, closure_exp e2 f sigma') in
    LetRecExp(recpointer, [convert_id funct; convert_id id], e1', e2')
  | N.LoopExp(id, ce1, e2) -> 
    closure_exp (CompExp ce1) (fun y1 -> 
        LoopExp(convert_id id, y1, closure_exp e2 f sigma)) sigma
  | N.RecurExp(v) -> RecurExp(convert_val v)

(* entry point *)
let convert e = closure_exp e (fun ce -> CompExp ce) Environment.empty
