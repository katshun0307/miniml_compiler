let debug = ref false
let dprint s = if !debug then (print_string (s ()) ; flush stdout)

let display_cfg = ref false
let optimize = ref false
let run = ref false

let outfile = ref "-"

let initial_decls = []

let rec compile prompt ichan cont =
  print_string prompt; flush stdout;

  (* このmain.ml自体の説明(コンパイラの全体構成) (1章後半) *)

  (* Parsing (2章) *)
  let prog = Parser.toplevel Lexer.main (Lexing.from_channel ichan) in
  dprint (fun () -> "(* [Parsed form] *)\n" ^ Syntax.string_of_exp prog ^ "\n");

  (* Normal form conversion (3章) *)
  let norm = Normal.convert prog in
  dprint (fun () -> "(* [Normal form] *)\n" ^ (Normal.string_of_norm norm));

  (* Closure conversion (4章) *)
  let closed = Closure.convert norm in
  dprint (fun () -> "\n(* [Closure] *)\n" ^ (Closure.string_of_closure closed));

  (* Flattening (5章前半) *)
  let flat = Flat.flatten closed in
  dprint (fun () -> "\n(* [Flat] *)\n" ^ (Flat.string_of_flat flat));

  (* Translate to VM (5章後半) *)
  let vmcode = Vm.trans flat in
  dprint (fun () -> "\n(* [VM code] *)\n" ^ (Vm.string_of_vm vmcode));

  (* 制御フローグラフを表示 *)
  if !display_cfg && not !optimize then
    Cfg.display_cfg (Cfg.build vmcode) None;

  let c_code = Backend.convert_c vmcode in
  let c_string = C_spec.header_string ^ C_spec.string_of_funct_list c_code ^ "\n" in

  (** Output to stdout/file *)
  let ochan = if !outfile = "-" then stdout else open_out !outfile in
  let () = output_string ochan (c_string ^ "\n") in
  if !outfile <> "-" then close_out ochan;

  (* run created c program *)
  if !run then
    if !outfile = "-" 
    then (let tmpchan = open_out "tmp.c" in
          let () = output_string tmpchan (c_string ^ "\n") in
          close_out tmpchan;
          print_string "compile c program in tmp.c...";
          let comp_int = Sys.command "gcc tmp.c" in
          if comp_int = 0 then print_string " => success\n"
          else print_string " => failure")
    else 
      (print_string ("compile c program in " ^ !outfile);
       let comp_int = Sys.command ("gcc " ^ !outfile) in
       if comp_int = 0 then print_string " => success\n"
       else print_string " => failure");

  (* continued... *)
  cont ()


(* ==== main ==== *)

let srcfile = ref "-"

let usage = "Usage: " ^ Sys.argv.(0) ^ " [-vOG] [-o ofile] [file]"

let aspec = Arg.align [
    ("-o", Arg.Set_string outfile,
     " Set output file (default: stdout)");
    ("-O", Arg.Unit (fun () -> optimize := true),
     " Perform optimization (default: " ^ (string_of_bool !optimize) ^ ")");
    ("-G", Arg.Unit (fun () -> display_cfg := true),
     " Display CFG (default: " ^ (string_of_bool !display_cfg) ^ ")");
    ("-v", Arg.Unit (fun () -> debug := true),
     " Print debug info (default: " ^ (string_of_bool !debug) ^ ")");
    ("-C", Arg.Unit (fun () -> run := true),
     " compile program (default: " ^ (string_of_bool !run) ^ ")");
  ]

let main () =
  Arg.parse aspec (fun s -> srcfile := s) usage;
  if !srcfile = "-" then
    let c = stdin in
    let rec k () = compile "# " c k in
    compile "# " c k
  else
    let c = open_in !srcfile in
    let rec k () = close_in c in
    compile "" c k

let () = main ()