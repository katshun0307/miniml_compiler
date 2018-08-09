open Syntax
open Eval
open Typing

let rec read_eval_print env tyenv =
  print_string "# ";
  flush stdout;
  try
    let decl = Exp(Parser.toplevel Lexer.main (Lexing.from_channel stdin)) in
    let ty, new_tyenv = ty_decl tyenv decl in
    let (id, newenv, v) = eval_decl env decl in
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
