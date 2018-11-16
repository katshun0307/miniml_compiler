module S = Syntax
module F = Flat

exception Error of string
let err s = raise (Error s)

type binOp = S.binOp

type id = int
type label = string

type operand =
    Param of int     (* param(n) *)
  | Local of id      (* local(ofs) *)
  | Proc  of label   (* labimm(l) *)
  | IntV  of int     (* imm(n) *)

type instr =
    Move of id * operand (* local(ofs) <- op *)
  | BinOp of id * S.binOp * operand * operand
  (* local(ofs) <- bop(op_1, op_2) *)
  | Label of label (* l: *)
  | BranchIf of operand * label (* if op then goto l *)
  | Goto of label (* goto l *)
  | Call of id * operand * operand list
  (* local(ofs) <- call op_f(op_1, ..., op_n) *)
  | Return of operand (* return(op) *)
  | Malloc of id * operand list (* new ofs [op_1, ..., op_n] *)
  | Read of id * operand * int (* read ofs #i(op) *)
  | BEGIN of label (* データフロー解析で内部的に使用 *)
  | END of label   (* データフロー解析で内部的に使用 *)

type decl =
    ProcDecl of label * int * instr list  (* int は局所変数の個数 *)

type prog = decl list

let is_label = function
  | Label _ -> true
  | _ -> false

let is_reg = function
  | Param _ | Local _ -> true
  | _ -> false

let type_of_operand = function
  | Param _ -> "param"
  | Local _ -> "local"
  | Proc _ -> "proc"
  | IntV _ -> "intv" 

(* ==== Formatter ==== *)

let string_of_binop = function
    S.Plus -> "add"
  | S.Mult -> "mul"
  | S.Lt   -> "lt"

let string_of_operand = function
    Param i -> "p" ^ string_of_int i
  | Local o -> (* -1 は生存変数解析で使われる特殊な値 *)
    if o = -1 then "*" else "t" ^ string_of_int o
  | Proc  l -> l
  | IntV  i -> string_of_int i

let string_of_instr idt tab = function
    Move (t, v) ->
    idt ^ "move" ^ tab ^ "t" ^ string_of_int t ^ ", " ^
    string_of_operand v
  | BinOp (t, op, v1, v2) ->
    idt ^ string_of_binop op ^ tab ^ "t" ^ string_of_int t ^ ", " ^
    string_of_operand v1 ^ ", " ^ string_of_operand v2
  | Label lbl -> lbl ^ ":"
  | BranchIf (v, lbl) ->
    idt ^ "bif" ^ tab ^ string_of_operand v ^ ", " ^ lbl
  | Goto lbl ->
    idt ^ "goto" ^ tab ^ lbl
  | Call (dst, tgt, [a0; a1]) ->
    idt ^ "call" ^ tab ^ "t" ^ string_of_int dst ^ ", " ^
    string_of_operand tgt ^
    "(" ^ string_of_operand a0 ^ ", " ^ string_of_operand a1 ^ ")"
  | Call (_, _, args) -> err ("Illegal number of arguments: " ^
                              string_of_int (List.length args))
  | Return v ->
    idt ^ "ret" ^ tab ^ string_of_operand v
  | Malloc (t, vs) ->
    idt ^ "new" ^ tab ^ "t" ^ string_of_int t ^ " [" ^
    (String.concat ", " (List.map string_of_operand vs)) ^ "]"
  | Read (t, v, i) ->
    idt ^ "read" ^ tab ^ "t" ^ string_of_int t ^ " #" ^
    string_of_int i ^ "(" ^ string_of_operand v ^ ")"
  | BEGIN lbl ->
    idt ^ "<BEGIN: " ^ lbl ^ ">"
  | END lbl ->
    idt ^ "<END: " ^ lbl ^ ">"

let string_of_decl (ProcDecl (lbl, n, instrs)) =
  "proc " ^ lbl ^ "(" ^ string_of_int n ^ ") =\n" ^
  (String.concat "\n"
     (List.map (fun i -> string_of_instr "  " "\t" i) instrs)) ^ "\n"

let string_of_vm prog =
  String.concat "\n" (List.map string_of_decl prog)

let string_of_alloc (alloc: (F.id, id) MyMap.t) = 
  let string_of_pair ((x: F.id), (y: id)) = "(" ^ (x: string) ^ ", " ^ string_of_int y ^ ") " in
  let string_list = List.map string_of_pair (MyMap.to_list alloc)
  in List.fold_left (fun x y -> x ^ y) "" string_list

(* ==== 仮想機械コードへの変換 ==== *)

let label_of_id (i: F.id): label = i

let trans_decl (F.RecDecl (proc_name, params, body)): decl =
  let is_toplevel = (proc_name = "_toplevel") in
  (* convert function names to label *)
  let proc_name' = label_of_id proc_name in
  (* generate new id *)
  let fresh_id_count = ref 0 in
  let fresh_id () = 
    let ret = !fresh_id_count in
    fresh_id_count := ret + 1;
    ret in
  (* >>> association between F.Var and local(id)s >>> *)
  let var_alloc = ref (MyMap.empty: (F.id, id) MyMap.t) in
  let append_local_var (id: F.id) (op: id) = var_alloc := MyMap.append id op !var_alloc in
  let convert_id i = 
    match MyMap.search i !var_alloc with
    | Some x -> x
    | None -> let new_id: id = fresh_id () in
      append_local_var i new_id;
      new_id in
  let operand_of_val v = 
    match v with
    | F.Var id -> 
      if not is_toplevel then 
        (let f_pointer = List.hd params in
         let f_arg = List.hd (List.tl params) in
         if id = f_pointer then Param 0
         else if id = f_arg then Param 1
         else Local(convert_id id))
      else Local(convert_id id)
    | F.Fun id -> Proc(id)
    | F.IntV i -> IntV i in
  (* get number of local var (that need to be allocated) *)
  let n_local_var () = 
    let rec loop l i = 
      match l with
      | (_, m):: tl -> if m < i then loop tl i else loop tl m 
      | [] -> i in
    (loop (MyMap.to_list !var_alloc) 0) + 1 in
  (* <<< association between F.Var and local(id)s <<< *)
  (* >>> remember loop >>> *)
  let loop_stack = ref ([]: (id * label) list) in
  let push_loop_stack (i, l) = loop_stack := (i, l) :: !loop_stack in
  let pop_loop_stack () = 
    match !loop_stack with
    | hd :: tl -> hd
    | [] -> err "reached bottom of loop stack" in
  (* <<< remember loop <<< *)
  let rec trans_cexp id ce: instr list = 
    match ce with
    | F.ValExp(v) -> [Move(convert_id id, operand_of_val v)]
    | F.BinOp(op, v1, v2) -> [BinOp(convert_id id, op, operand_of_val v1, operand_of_val v2)]
    | F.AppExp(v, vl) -> [Call(convert_id id, operand_of_val v, List.map operand_of_val vl)]
    | F.IfExp(v, e1, e2) -> 
      let new_label1 = "lab" ^ proc_name ^ string_of_int(fresh_id ()) in
      let new_label2 = "lab" ^ proc_name ^ string_of_int(fresh_id ()) in
      let e2' = trans_exp e2 [] ~ret:id in
      let e1' = trans_exp e1 [] ~ret:id in
      [BranchIf(operand_of_val v, new_label1)] @ e2' @ [Goto(new_label2); Label(new_label1)] @ e1' @ [Label(new_label2)]
    | F.TupleExp(vl) -> [Malloc(convert_id id, List.map operand_of_val vl)]
    | F.ProjExp(v, i) -> [Read(convert_id id, operand_of_val v, i)]
  and trans_exp (e: F.exp) (accum_instr: instr list) ?(ret="default"): instr list = 
    match e with
    | F.CompExp(ce) -> 
      if ret = "default" then
        (match ce with 
         | F.ValExp(Var id) -> accum_instr @ [Return(operand_of_val (F.Var id))]
         | _ -> let return_id: F.id = "ret" ^ (string_of_int (fresh_id())) in
           let ret_assign_instr = trans_cexp return_id ce in
           accum_instr @ ret_assign_instr @ [Return(operand_of_val (F.Var return_id))])
      else let ret_assign_instr = trans_cexp ret ce in
        accum_instr @ ret_assign_instr
    | F.LetExp(id, ce, e) ->
      let instr' = accum_instr @ trans_cexp id ce in
      instr' @ trans_exp e [] ~ret 
    | F.LoopExp(id, ce, e) -> 
      let loop_label = "loop" ^ (string_of_int (fresh_id ())) in
      push_loop_stack (convert_id id, loop_label);
      trans_cexp id ce @ [Label (loop_label)] @ trans_exp e [] ~ret:"default"
    | F.RecurExp(v) -> 
      let (id, loop_lab) = pop_loop_stack () in
      [Move(id, operand_of_val v); Goto(loop_lab)]
  in ProcDecl(proc_name', n_local_var (), trans_exp body [] ~ret:"default")

(* entry point *)
let trans = List.map trans_decl
