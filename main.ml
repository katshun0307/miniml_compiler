open Syntax
open Eval
open Typing

let fresh_loopvar = 
  let counter = ref 0 in
  let body () =
    let v = !counter in
    counter := v + 1; 
    "f_" ^ string_of_int v
  in body

let recprog_of_loop p =
  let recur_subst newf e = 
    let rec recur_subst_loop = function
      | FunExp(id, e) -> FunExp(id, recur_subst_loop e) 
      | ProjExp(e, i) -> ProjExp(recur_subst_loop e, i)
      | BinOp(op, e1, e2) -> BinOp(op, recur_subst_loop e1, recur_subst_loop e2)
      | LetExp(id, e1, e2) -> LetExp(id, recur_subst_loop e1, recur_subst_loop e2)
      | AppExp(e1, e2) -> AppExp(recur_subst_loop e1, recur_subst_loop e2)
      | LetRecExp(i1, i2, e1, e2) -> LetRecExp(i1, i2, recur_subst_loop e1, recur_subst_loop e2)
      | LoopExp(id, e1, e2) -> LoopExp(id, recur_subst_loop e1, recur_subst_loop e2)
      | TupleExp(e1, e2) -> TupleExp(recur_subst_loop e1, recur_subst_loop e2)
      | IfExp(cond, e1, e2) -> IfExp(recur_subst_loop cond, recur_subst_loop e1, recur_subst_loop e2)
      | RecurExp(e) -> AppExp(newf, e)
      | _ as e -> e in
    recur_subst_loop e in
  let rec recexp_of_loop = function 
    | LoopExp(v, e1, e2) -> 
      let new_funct: id = fresh_loopvar () in
      let rece1 = recur_subst (Var new_funct) (recexp_of_loop e2) in
      let rece2 = AppExp(Var new_funct, e1) in
      LetRecExp(new_funct, v, rece1, rece2)
    | _ as e -> e in 
  match p with
  | Exp e -> Exp (recexp_of_loop e)

let rec read_eval_print env tyenv =
  print_string "# ";
  flush stdout;
  try
    let decl = Exp(Parser.toplevel Lexer.main (Lexing.from_channel stdin)) in
    let decl' = recprog_of_loop decl in
    (match decl' with
     | Exp e -> string_of_exp e |> print_endline);
    let ty, new_tyenv = ty_decl tyenv decl' in
    let (id, newenv, v) = eval_decl env decl' in
    Printf.printf "val %s : " id;
    print_string (string_of_ty ty);
    print_string " = ";
    pp_val v;
    print_newline();
    read_eval_print newenv new_tyenv
  with e ->
    let msg = Printexc.to_string e in
    print_string ("there was an error: " ^ msg ^ "\n");
    read_eval_print env tyenv;;

let initial_env = 
  Environment.extend "i" (IntV 1)
    (Environment.extend "v" (IntV 5) 
       (Environment.extend "x" (IntV 10) 
          (Environment.extend "uso" (BoolV false) Environment.empty)))

let initial_tyenv = 
  Environment.extend "i" TyInt
    ( Environment.extend "v" TyInt
        ( Environment.extend "x" TyInt
            ( Environment.extend "uso" TyBool Environment.empty)))

let _ = read_eval_print initial_env initial_tyenv
