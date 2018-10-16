open Syntax
open MySet

exception Error of string

let err s = raise (Error s)

(* type environment *)
type tyenv = ty Environment.t
type subst = (tyvar * ty) list

(* printing *)
let rec string_of_subst = function 
  | (id, ty) :: rest -> "(" ^ string_of_ty (TyVar(id)) ^ ", " ^ string_of_ty ty ^ ")" ^ string_of_subst rest
  | [] -> ""

let rec string_of_eqs = function 
  | (ty1, ty2) :: rest -> "(" ^ string_of_ty ty1 ^ ", " ^ string_of_ty ty2 ^ ")" ^ string_of_eqs rest
  | _ -> ""

(* apply subst:(substutution) to ty:(type) *)
let rec subst_type s ty = 
  let rec resolve_subst (subst_tyvar, subst_ty) ty = 
    let subst_pair = (subst_tyvar, subst_ty) in
    match ty with
    | TyVar id -> if id = subst_tyvar then subst_ty else TyVar id
    | TyFun(a, b) -> TyFun(resolve_subst subst_pair a, resolve_subst subst_pair b)
    | TyInt -> TyInt
    | TyBool -> TyBool 
    | TyTuple(a, b) -> TyTuple(resolve_subst subst_pair a, resolve_subst subst_pair b)
  in match s with 
  | top :: rest -> 
    subst_type rest (resolve_subst top ty)
  | [] -> ty

(* reform subst(substitution) to eql:(list of equal types) *)
let eqls_of_subst subst =  
  let reform sub = 
    let ((id: tyvar), (t: ty)) = sub in 
    (TyVar id, t) in
  List.map reform subst

(* apply subst:(substitution) to eql:(list of equal types) *)
let subst_eqs subst eql = 
  List.map (fun (t1, t2) -> (subst_type [subst] t1, subst_type [subst] t2)) eql

(* main unification algorithm *)
let rec unify eqs: (tyvar * ty) list  = 
  let rec loop lst current_subst = 
    (match lst with
     | (x, y) :: rest -> 
       if x = y then loop rest current_subst else
         (match x, y with
          | TyFun(a, b), TyFun(c, d) -> loop ((a, c) :: (b, d) :: rest) current_subst
          | TyTuple(a, b), TyTuple(c, d) -> loop((a, c) :: (b, d) :: rest) current_subst
          | TyVar(id), b -> 
            if not (MySet.member id (freevar_ty b)) then
              let mid = unify(subst_eqs (id, b) rest) in
              (id, b):: mid
            else err "unify: could not resolve type"
          | b, TyVar(id) -> 
            if not (MySet.member id (freevar_ty b)) then
              let mid = unify(subst_eqs (id, b) rest) in
              (id, b) :: mid
            else err "unify: could not resolve type"
          | _ -> err "unify: could not resolve type"
         )
     | _ -> current_subst) in 
  loop eqs []

let ty_prim op (ty1:ty) (ty2:ty) = match op with
  | Plus -> (TyInt, (ty1, TyInt) :: (ty2, TyInt) :: [])
  | Mult -> (TyInt, (ty1, TyInt) :: (ty2, TyInt) :: [])
  | Lt  -> (TyBool, (ty1, TyInt) :: (ty2, TyInt) :: [])

let get_type = function
  | TyVar _ -> "tyvar"
  | TyBool -> "tybool"
  | TyInt -> "tyint"
  | TyFun _ -> "tyfun" 
  | TyTuple _ -> "tytuple"   

let rec ty_exp tyenv = function
  | Var x -> 
    (try (Environment.lookup x tyenv, []) with 
       Environment.Not_bound -> err ("Variable not bound: " ^ x))
  | ILit _ -> (TyInt, [])
  | BLit _ -> (TyBool, [])
  | BinOp (op, exp1, exp2) -> 
    let tyarg1, tysubst1 = ty_exp tyenv exp1 in
    let tyarg2, tysubst2 = ty_exp tyenv exp2 in
    let ty3, eqs3 = ty_prim op tyarg1 tyarg2 in
    let eqs = (eqls_of_subst tysubst1) @ (eqls_of_subst tysubst2) @ eqs3 in
    let main_subst = unify eqs in
    (ty3, main_subst)
  | IfExp (exp1, exp2, exp3) -> 
    let tyarg1, tysubst1 = ty_exp tyenv exp1 in
    let cond_type = get_type tyarg1 in
    (* if condition part is valid *)
    if cond_type = "tybool" || cond_type = "tyvar" then
      let new_eqs = (tyarg1, TyBool) :: eqls_of_subst tysubst1 in
      let tyarg2, tysubst2 = ty_exp tyenv exp2 in
      let tyarg3, tysubst3 = ty_exp tyenv exp3 in
      let main_subst = unify ((eqls_of_subst tysubst2) @ (eqls_of_subst tysubst3) @ new_eqs @ [(tyarg2, tyarg3)]) in
      (subst_type main_subst tyarg2, main_subst)
    else err "condition must be boolean: if"
  | LetExp (id, e1, e2) -> 
    let e_type, e_subst = ty_exp tyenv e1 in
    let eval_tyenv = Environment.extend id e_type tyenv in
    let eval_subst = e_subst in
    let exp_ty, exp_subst = ty_exp eval_tyenv e2 in
    let main_subst = unify (eqls_of_subst eval_subst @ eqls_of_subst exp_subst) in
    (subst_type main_subst exp_ty, main_subst)
  | FunExp(id, exp) ->
    (* get environment with new tyvar for each params to evaluate the main function *)
    let new_tyvar = TyVar (fresh_tyvar()) in
    let eval_tyenv = Environment.extend id new_tyvar tyenv in
    (* evaluate main function in the created environment *)
    let res_ty, res_tysubst = ty_exp eval_tyenv exp in
    (* make output ( re-evaluate args ) *)
    let arg_tyvar = Environment.lookup id eval_tyenv in
    let arg_ty =  subst_type res_tysubst arg_tyvar in
    (TyFun(arg_ty, res_ty), res_tysubst)
  | AppExp(exp1, exp2) ->
    let ty_exp1, tysubst1 = ty_exp tyenv exp1 in
    let ty_exp2, tysubst2 = ty_exp tyenv exp2 in
    (* make new var *)
    let ty_x = TyVar(fresh_tyvar()) in
    let subst_main = unify([ty_exp1, TyFun(ty_exp2, ty_x)] @ eqls_of_subst tysubst1 @ eqls_of_subst tysubst2) in
    let ty_3 = subst_type subst_main ty_x in
    (ty_3, subst_main)
  | LetRecExp(id, para, e1, e2) -> 
    let ty_x = TyVar(fresh_tyvar()) in (* type of return value: f x *)
    let ty_para = TyVar(fresh_tyvar()) in (* type of parameter: x *)
    (* first formula *)
    let eval_tyenv1 = Environment.extend id (TyFun(ty_para, ty_x)) (Environment.extend para ty_para tyenv) in
    let e1_ty, e1_subst = ty_exp eval_tyenv1 e1 in
    (* second formula *)
    let eval_tyenv2 = Environment.extend id (TyFun(ty_para, ty_x)) tyenv in
    let e2_ty, e2_subst = ty_exp eval_tyenv2 e2 in
    (* unify all eqls *)
    let main_subst = unify( (e1_ty, ty_x) ::eqls_of_subst e1_subst @ eqls_of_subst e2_subst) in
    (subst_type main_subst e2_ty, main_subst)
  | TupleExp(e1, e2) -> 
    let tyarg1, tysubst1 = ty_exp tyenv e1 in
    let tyarg2, tysubst2 = ty_exp tyenv e2 in
    let main_subst = unify(eqls_of_subst tysubst1 @ eqls_of_subst tysubst2) in
    let ty1 = subst_type main_subst tyarg1 in
    let ty2 = subst_type main_subst tyarg2 in
    (TyTuple(ty1, ty2), main_subst)
  | ProjExp(e, i) -> 
    let tyarg, tysubst = ty_exp tyenv e in
    let t1 = TyVar(fresh_tyvar ()) in
    let t2 = TyVar(fresh_tyvar ()) in
    let main_subst = unify(eqls_of_subst tysubst @ [(tyarg, TyTuple(t1, t2))]) in
    if i = 1 then (subst_type main_subst t1, main_subst)
    else if i = 2 then (subst_type main_subst t2, main_subst)
    else err "fail"
  | _ -> err "ty_exp: not implemented"

let rec ty_decl tyenv = function
  | Exp e -> 
    let (type_, _) = ty_exp tyenv e in
    (type_, tyenv)
(* | _ -> err "not implemented" *)