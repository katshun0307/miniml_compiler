open Pretty
module S = Syntax
module C = Closure

exception Error of string
let err s = raise (Error s)

type id = S.id
type binOp = S.binOp

(* ==== 値 ==== *)
type value =
    Var  of id
  | Fun  of id   (* NEW *)
  | IntV of int

(* ==== 式 ==== *)
type cexp =
    ValExp    of value
  | BinOp     of binOp * value * value
  | AppExp    of value * value list
  | IfExp     of value * exp * exp
  | TupleExp  of value list
  | ProjExp   of value * int

and exp =
    CompExp   of cexp
  | LetExp    of id * cexp * exp
  | LoopExp   of id * cexp * exp
  | RecurExp  of value

(* ==== 関数宣言 ==== *)
type decl = RecDecl of id * id list * exp  (* NEW *)

(* ==== プログラム ==== *)
type prog = decl list  (* NEW *)

(* ==== Formatter ==== *)

let string_of_flat prog =
  let pr_of_op = function
      S.Plus -> text "+"
    | S.Mult -> text "*"
    | S.Lt -> text "<"
    | S.And -> text "&&" 
    | S.Or -> text "||" 
  in
  let pr_of_value = function
      Var id -> text id
    | Fun id -> text "#'" <*> text id
    | IntV i ->
      let s = text (string_of_int i) in
      if i < 0 then text "(" <*> s <*> text ")" else s
  in
  let pr_of_values = function
      [] -> text "()"
    | v :: vs' ->
      text "(" <*>
      (List.fold_left
         (fun d v -> d <*> text "," <+> pr_of_value v)
         (pr_of_value v) vs')
      <*> (text ")")
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
    | LoopExp (id, ce, e) ->
      enclose 1
        ((nest 2 (group (text "loop" <+> text id <+>
                         text "=" <|> pr_of_cexp 1 ce)))
         <+> text "in" <|> pr_of_exp 1 e)
    | RecurExp v ->
      enclose 3 (text "recur" <+> pr_of_value v)
  in
  let pr_of_decl = function
      RecDecl (id, params, body) ->
      let tparms = match params with
          [] -> text ""
        | param :: params' ->
          List.fold_left (fun t p -> t <*> text "," <+> text p)
            (text param) params'
      in
      (group (text "let" <+> text "rec" <+>
              (group
                 ((text id) <+> text "(" <*> tparms <*> text ")" <+>
                  nest 2 (text "=" <|> pr_of_exp 1 body)))))
  in
  layout
    (pretty 30 (List.fold_right (fun decl doc ->
         pr_of_decl decl <|> nil <|> doc) prog nil))

(* ==== フラット化：変数参照と関数参照の区別も同時に行う ==== *)
let convert_id (i: C.id): id = i 
let convert_id_list (il: C.id list): id list = il

let get_flat_exp ex = 
  (* === helper functions === *)
  let fun_list = ref (MySet.empty: C.id MySet.t) in
  let append_fun v = fun_list := MySet.insert v !fun_list in
  let search_fun v = MySet.member v !fun_list in
  let decl_list = ref ([]: decl list) in
  let append_decl d = decl_list := (d :: !decl_list) in 
  let convert_val (v: C.value): value = 
    match v with
    | C.Var id -> if search_fun id 
      then Fun(id) 
      else Var(convert_id id)
    | C.IntV i -> IntV(i) in
  let convert_val_list (vl: C.value list): value list = List.map convert_val vl in
  let rec flat_exp (e: C.exp) (f: cexp -> exp): exp = 
    match e with
    | C.CompExp(C.ValExp v) -> f (ValExp(convert_val v))
    | C.CompExp(C.BinOp(op, v1, v2)) -> 
      let v1' = convert_val v1 in
      let v2' = convert_val v2 in
      f (BinOp(op, v1', v2'))
    | C.CompExp(C.AppExp(v, vl)) ->  
      let v' = convert_val v in
      let vl' = convert_val_list vl in
      f (AppExp(v', vl'))
    | C.CompExp(C.IfExp(v, e1, e2)) -> 
      let v' = convert_val v in
      (* flat_exp e1 (fun y1 -> 
          flat_exp e2 (fun y2 -> 
              f (IfExp(v', f y1, f y2)))) *)
      f (IfExp(v', flat_exp e1 (fun ce -> CompExp ce), flat_exp e2 (fun ce -> CompExp ce)))
    | C.CompExp(C.TupleExp(vl)) -> f (TupleExp(convert_val_list vl))
    | C.CompExp(C.ProjExp(v, i)) -> f (ProjExp(convert_val v, i))
    | C.LetExp(id, ce, e) -> 
      flat_exp (CompExp ce) (fun cy1 ->  
          LetExp(convert_id id, cy1, flat_exp e f))
    | C.LetRecExp(funct, idl, e1, e2) -> 
      append_fun funct;
      let letrec' = RecDecl(convert_id funct, convert_id_list idl, flat_exp e1 (fun x -> CompExp x)) in
      append_decl letrec';
      flat_exp e2 f
    | C.LoopExp(id, ce, e) -> 
      let id' = convert_id id in
      flat_exp (CompExp ce) (fun cy1 -> 
          LoopExp(id', cy1, flat_exp e f))
    | C.RecurExp(v) -> RecurExp(convert_val v)
  in let converted = flat_exp ex (fun x -> CompExp x) in
  (converted, !decl_list)

let flatten exp = 
  let toplevel_content, decl_list = get_flat_exp exp in
  decl_list @ [RecDecl("_toplevel", [], toplevel_content)]
