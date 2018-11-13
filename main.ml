let debug = ref false
let detail = ref false

let src_file = ref "-"

let dprint s = if !debug then (print_string (s ()) ; flush stdout)

let display_cfg = ref false
let optimize = ref false
let compile_c = ref false
let backend = ref false
let simulation = ref false
let regcode = ref false

let optimize_options = ref ({
    dead = false;
    simple = false;
    fold = false
  }: Opt.opt_configs)

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

  (* generated optimized vmcode *)
  let vmcode' = if !optimize then 
      Opt.optimize !display_cfg Arm_spec.nreg vmcode !optimize_options
    else vmcode in

  if not !backend then
    (* if arm code *)
    let armcode =
      if !regcode then
        (* generate regcode *)
        (* Low-level opt. (7章 DFA & 最適化) *)
        let regcode = Opt.gen_regcode Arm_spec.nreg vmcode' !detail in
        dprint (fun () ->
            "\n(* [Reg code] *)\n" ^ (Reg.string_of_reg regcode) ^ "\n");
        (* Convert to ARM assembly (7章 コード生成(レジスタ利用版)) *)
        Arm_reg.codegen regcode
      else
        (* Convert to ARM assembly (6章 コード生成) *)
        Arm_noreg.codegen vmcode'
    in

    (* Output to stdout/file *)
    let ochan = if !outfile = "-" then stdout else open_out !outfile in
    let () = output_string ochan (Arm_spec.string_of armcode ^ "\n") in
    if !outfile <> "-" then close_out ochan;

    if !simulation
    then print_string "\n(* simulated statements *)\n";
    let state = Arm_simulator.simulate armcode !detail in
    (print_string ("\n(* [Simulation result] *)\n" ^
                   (Arm_simulator.string_of_state state) ^ "\n");
     flush stdout);

    (* if C code *)
  else
    (* Output to stdout/file *)
    let c_code = Backend.convert_c vmcode' in
    let c_string = C_spec.header_string ^ C_spec.string_of_funct_list c_code ^ "\n" in

    (** Output to stdout/file *)
    let ochan = if !outfile = "-" then stdout else open_out !outfile in
    let () = output_string ochan (c_string ^ "\n") in
    if !outfile <> "-" then close_out ochan;

    (* compile created c program *)
    if !compile_c then
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

let usage = "Usage: " ^ Sys.argv.(0) ^ " [-vOGs] [-os] [-of] [-od] [-o ofile] [file]"

let aspec = Arg.align [
    ("-o", Arg.Set_string outfile,
     " Set output file (default: stdout)");
    ("-i", Arg.Set_string src_file,
     " name of source file(default: " ^ !src_file ^ ")");
    ("-O", Arg.Unit (fun () -> optimize := true; !optimize_options.simple <- true; !optimize_options.fold <- true; !optimize_options.dead <- true),
     " perform all optimization and regcode (default: " ^ (string_of_bool false) ^ ")");
    ("-reg", Arg.Unit (fun () -> regcode := true),
     " generate regcode (default: " ^ (string_of_bool !regcode) ^ ")");
    ("-G", Arg.Unit (fun () -> display_cfg := true),
     " Display CFG (default: " ^ (string_of_bool !display_cfg) ^ ")");
    ("-v", Arg.Unit (fun () -> debug := true),
     " Print debug info (default: " ^ (string_of_bool !debug) ^ ")");
    ("-vv", Arg.Unit (fun () -> detail := true),
     " Print many many many debug info (default: " ^ (string_of_bool !detail) ^ ")");
    ("-s", Arg.Unit (fun () -> simulation := true),
     " Print simulation result (default: " ^ (string_of_bool !simulation) ^ ")");
    ("-os", Arg.Unit (fun () -> optimize := true; !optimize_options.simple <- true),
     " simple optimization (default: " ^ (string_of_bool !optimize_options.simple) ^ ")");
    ("-of", Arg.Unit (fun () -> optimize := true; !optimize_options.fold <- true),
     " fold optimization (default: " ^ (string_of_bool !optimize_options.fold) ^ ")");
    ("-od", Arg.Unit (fun () -> optimize := true; !optimize_options.dead <- true),
     " dead code elimination (default: " ^ (string_of_bool !optimize_options.dead) ^ ")");
    ("-b", Arg.Unit (fun () -> backend := true),
     " generate c program (default: " ^ (string_of_bool !backend) ^ ")");
    ("-C", Arg.Unit (fun () -> compile_c := true),
     " compile C program (default: " ^ (string_of_bool !compile_c) ^ ")");
  ]

let main () =
  Arg.parse aspec (fun s -> srcfile := s) usage;
  if !src_file = "-" then
    let c = stdin in
    let rec k () = compile "# " c k in
    compile "# " c k
  else
    let c = open_in !src_file in
    let rec k () = close_in c in
    compile "" c k

let () = main ()