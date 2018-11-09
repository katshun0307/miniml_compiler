module V = Vm

exception Error of string
let err s = raise (Error s)

let debug = true

let debug_string s = 
  if debug 
  then print_string (s ^ "\n")

let select_random l =
  let len = List.length l in
  if len = 0 
  then err "select_random: got list with 0 length"
  else 
    let r  = Random.int len in
    List.nth l r

type binOp = Vm.binOp

type offset = int
type label = string

type reg = int       (* 汎用レジスタ．0以上の整数 *)

(* コード生成が swap に利用するための専用レジスタ．
   実際にどの物理レジスタを用いるかはアーキテクチャ依存 *)
let reserved_reg = -1

type dest =
    R of reg     (* レジスタ *)
  | L of offset  (* 局所領域の関数フレーム中の相対位置  *)

type operand =
    Param of int
  | Reg   of reg
  | Proc  of label
  | IntV  of int

type instr =
    Move     of reg * operand
  | Load     of reg * offset
  | Store    of reg * offset
  | BinOp    of reg * Vm.binOp * operand * operand
  | Label    of label
  | BranchIf of operand * label
  | Goto     of label
  | Call     of dest * operand * operand list
  | Return   of operand
  | Malloc   of dest * operand list
  | Read     of dest * operand * int
  | Save     of reg * offset
  | Restore  of reg * offset

type decl =
    ProcDecl of label * int * instr list (* int: 局所領域の個数 *)

type prog = decl list

(* Formatter *)

let string_of_binop = function
    Syntax.Plus -> "add"
  | Syntax.Mult -> "mul"
  | Syntax.Lt   -> "lt"

let string_of_dest = function
    R r -> "r" ^ string_of_int r
  | L oft -> "t" ^ string_of_int oft

let string_of_operand = function
    Param i -> "p" ^ string_of_int i
  | Reg r -> "r" ^ string_of_int r
  | Proc  l -> l
  | IntV  i -> string_of_int i

let string_of_instr idt tab = function
    Move (t, v) ->
    idt ^ "move" ^ tab ^ "r" ^ string_of_int t ^ ", " ^
    string_of_operand v
  | Load (r, oft) ->
    idt ^ "load" ^ tab ^ "r" ^ string_of_int r ^ ", t" ^
    string_of_int oft
  | Store (r, oft) ->
    idt ^ "store" ^ tab ^ "r" ^ string_of_int r ^ ", t" ^
    string_of_int oft
  | BinOp (t, op, v1, v2) ->
    idt ^ string_of_binop op ^ tab ^ "r" ^ string_of_int t ^ ", " ^
    string_of_operand v1 ^ ", " ^ string_of_operand v2
  | Label lbl -> lbl ^ ":"
  | BranchIf (v, lbl) ->
    idt ^ "bif" ^ tab ^ string_of_operand v ^ ", " ^ lbl
  | Goto lbl ->
    idt ^ "goto" ^ tab ^ lbl
  | Call (dst, tgt, [a0; a1]) ->
    idt ^ "call" ^ tab ^ string_of_dest dst ^ ", " ^
    string_of_operand tgt ^
    "(" ^ string_of_operand a0 ^ ", " ^ string_of_operand a1 ^ ")"
  | Call (_, _, args) -> err ("Illegal number of arguments: " ^
                              string_of_int (List.length args))
  | Return v ->
    idt ^ "ret" ^ tab ^ string_of_operand v
  | Malloc (t, vs) ->
    idt ^ "new" ^ tab ^ string_of_dest t ^ " [" ^
    (String.concat ", " (List.map string_of_operand vs)) ^ "]"
  | Read (t, v, i) ->
    idt ^ "read" ^ tab ^ string_of_dest t ^ " #" ^
    string_of_int i ^ "(" ^ string_of_operand v ^ ")"
  | Save (r, oft) ->
    idt ^ "save" ^ tab ^ "r" ^ string_of_int r ^ ", t" ^
    string_of_int oft
  | Restore (r, oft) ->
    idt ^ "restore" ^ tab ^ "r" ^ string_of_int r ^ ", t" ^
    string_of_int oft

let string_of_decl (ProcDecl (lbl, n, instrs)) =
  "proc " ^ lbl ^ "(" ^ string_of_int n ^ ") =\n" ^
  (String.concat "\n"
     (List.map (fun i -> string_of_instr "  " "\t" i) instrs)) ^ "\n"

let string_of_reg prog =
  String.concat "\n" (List.map string_of_decl prog)

(* ==== レジスタ割付け ==== *)
let is_register = function
  | R _ -> true
  | L _ -> false

let reg_of_dest = function
  | R r -> r
  | L _ -> err "is not reg: reg_of_dest"

let offset_of_dest = function
  | R _ -> err "is not offset"
  | L o -> o

let trans_decl nreg lives (Vm.ProcDecl (lbl, nlocal, instrs)) =
  debug_string ("converting decl: " ^ lbl);
  (* 生存変数解析を実施 *)
  let live_bblock = Cfg.vm_to_cfg lbl instrs in
  let live_result = Dfa.solve (Live.make ()) live_bblock in
  let get_property ins side = MySet.filter (fun x -> x <> (Vm.Local (-1))) (Dfa.get_property live_result ins side) in
  (* store generated instrs *)
  let instrs_list = ref ([]: instr list) in
  let append_instr d = instrs_list := (!instrs_list @ d) in
  (* manage local memory space *)
  let local_space = ref 0 in
  let update_save_space n = 
    if !local_space < n then local_space := n;
    debug_string ("updated save_spavce to " ^ string_of_int n )
  in
  (* allocation management >>> *)
  (* save allocations in other blocks *)
  let past_allocations = ref (Array.make (Array.length live_bblock) MyMap.empty: (V.id, dest) MyMap.t array) in
  let set_past_alloc alloc i = 
    Array.set !past_allocations i alloc in
  let get_past_alloc i = 
    Array.get !past_allocations i in
  (* manage offset of local *)
  let offset_counter = ref 0 in
  let get_new_offset () = 
    let r = !offset_counter in
    offset_counter := !offset_counter + 1;
    r in
  (* manage allocation of Vm.id to dest >>> *)
  let allocation = ref (MyMap.empty: (V.id, dest) MyMap.t) in
  let append_alloc (id, d) = allocation := MyMap.append id d !allocation in
  let search_alloc id = MyMap.search id !allocation in
  let string_of_alloc () = 
    String.concat ", "
      (List.sort String.compare
         (List.map (fun (id, ds) -> "(t" ^ string_of_int id  ^ ", " ^ string_of_dest ds ^ ")") 
            (MyMap.to_list !allocation))) in
  let alloc_status () = 
    let rec loop l raccum laccum =
      (match l with
       | (_, R i):: tl -> loop tl (i :: raccum) laccum
       | (_, L i):: tl -> loop tl raccum (i:: laccum)
       | [] -> (raccum, laccum)) in
    loop (MyMap.to_list !allocation) [] [] in
  let get_used_reg () = 
    let (r_usage, _) = alloc_status () in
    r_usage
  in
  let get_nlocal () = 
    let (_, l_usage) = alloc_status () in
    List.length l_usage 
  in
  let get_free_reg () = 
    let used = MySet.from_list (get_used_reg ()) in
    let all = MySet.from_list (List.init nreg (fun x -> x)) in
    MySet.to_list (MySet.diff all used) in
  (* >>> manage allocation of Vm.id to dest *)
  (* helper functions for converting statements >>> *)
  let convert_id id = 
    match search_alloc id with
    | Some d -> d
    | None -> 
      let free_reg = get_free_reg () in
      if List.length free_reg = 0 
      then let ret = get_new_offset () in
        (append_alloc (id, L ret);
         L ret)
      else let ret =  List.hd free_reg in
        (append_alloc (id, R ret);
         R ret)
  in
  (* swap allocation for given offset and dest *)
  let swap (off: offset) (r: reg) =
    (* === swap alloc data === *)
    let id_off' = MyMap.reverse_search (L off) !allocation in
    let id_reg' = MyMap.reverse_search (R r) !allocation in
    let (id_off, id_reg) = 
      match (id_off', id_reg') with
      | Some o, Some r -> (o, r)
      | _ -> err "failed to swap" in
    allocation := MyMap.assoc id_off (R r) !allocation;
    allocation := MyMap.assoc id_reg (L off) !allocation;
    (* === change data === *)
    (* move offset to reserved_reg *)
    append_instr [Load(reserved_reg, off)];
    (* move reg to offset *)
    append_instr [Store(r, off)];
    (* move reserved_reg to reg *)
    append_instr [Move(r, Reg reserved_reg)];
  in
  let convert_op op = 
    match op with
    | V.Param i -> Param i
    | V.Local id -> 
      let dest = (convert_id id) in
      (match dest with
       | R i -> Reg i
       | L o -> 
         (* swap offset with some register *)
         let swap_r = select_random (get_used_reg ()) in
         swap o swap_r;
         Reg swap_r)
    | V.Proc l -> Proc l
    | V.IntV i -> IntV i
  in
  (* move data in s to register d *)
  let move_to_reg (d: reg) (s: V.operand): instr list =
    match s with
    | V.Param i -> [Move(d, convert_op s)]
    | V.Local id -> 
      let dest = convert_id id in
      if is_register dest 
      then [Move(d, Reg (reg_of_dest dest))]
      else [Load(d, offset_of_dest dest)]
    | V.Proc l -> [Move(d, Proc l)]
    | V.IntV i -> [Move(d, IntV i)]
  in
  (* move data in register to dest (either reg or offset) *)
  let move_to_dest (d:dest) (s:reg) = 
    match d with
    | R r -> [Move(r, Reg s)]
    | L o -> [Store(s, o)]
  in
  (* convert block to reg code *)
  let process_block (blk: Cfg.bblock) (blk_id:int) =
    (* process label *)
    let is_proc_name s = 
      String.sub s 0 4 = "_b__" || s = "_toplevel" in
    (match MySet.to_list blk.labels with
     | [] -> ()
     | l :: [] -> if not (is_proc_name l)
       then append_instr [Label l]
     | _ -> err "expected only 1 label per block");
    (* load allocation of predecessor *)
    allocation := MyMap.from_list(
        MySet.to_list(
          List.fold_left (fun accum i -> 
              (MySet.union accum (MySet.from_list(MyMap.to_list(get_past_alloc i))))) 
            MySet.empty 
            (MySet.to_list (blk.preds)))); 
    (* decide allocation *)
    let decide_allocation instr =
      let before = get_property instr Cfg.BEFORE in
      debug_string ("before is " ^ String.concat ", " (List.map Vm.string_of_operand (MySet.to_list before)));
      let after = get_property instr Cfg.AFTER in
      debug_string ("after is " ^ String.concat ", " (List.map Vm.string_of_operand (MySet.to_list after)));
      let new_ops = MySet.diff after before in
      debug_string ("new ops is " ^ String.concat ", " (List.map Vm.string_of_operand (MySet.to_list new_ops)));
      (* make alloc containing only before and renew *)
      let same_allocs = 
        let rec loop op_list accum = 
          match op_list with
          | (Vm.Local id):: tl -> 
            (let dest' = search_alloc id in
             match dest' with
             | Some dest -> loop tl ((id, dest):: accum)
             | None -> err "unexpected failure in same_allocs")
          | _:: tl -> loop tl accum
          | [] -> accum in
        MyMap.from_list (loop (MySet.to_list before) []) in
      allocation := same_allocs;
      (* add new ops to alloc *)
      let get_dest op = 
        match op with
        | V.Local id -> 
          let id' = convert_id id in
          append_alloc (id, id')
        | Param _ -> () 
        | _ -> err "unexpected input: decide_allocation" in
      List.iter get_dest (MySet.to_list new_ops) in
    (* >>> decide allocation *)
    let reg_of_instr instr =
      if not (Vm.is_label instr)
      then decide_allocation instr;
      debug_string ("convert " ^ (Vm.string_of_instr "" "" instr) ^ " under the following allocation");
      debug_string (string_of_alloc ());
      match instr with
      | V.Move(id, op) -> 
        let id' = convert_id id in
        if is_register id' 
        then append_instr (move_to_reg (reg_of_dest id') op)
        else append_instr ((move_to_reg reserved_reg op) @ (move_to_dest id' reserved_reg))
      | V.BinOp(id, bop, op1, op2) ->
        let id' = convert_id id in
        if is_register id' 
        then append_instr [BinOp(reg_of_dest id', bop, convert_op op1, convert_op op2)]
        else append_instr [BinOp(reserved_reg, bop, convert_op op1, convert_op op2); Store(reserved_reg, offset_of_dest id')]
      | V.Label l -> append_instr [Label l]
      | V.BranchIf(op, l) -> append_instr [BranchIf(convert_op op, l)]
      | V.Goto l -> append_instr [Goto l]
      | V.Call(id, op, opl) as ins ->
        (* list of live operands after call *)
        let live_ops_after = MySet.to_list (get_property ins Cfg.AFTER) in
        let rec loop ops accum = 
          match ops with
          | (V.Local id'):: tl -> 
            if id <> id' then
              (match search_alloc id' with
               | Some (R x) -> loop tl (x::accum)
               | _ -> loop tl accum)
            else loop tl accum
          | _:: tl -> loop tl accum
          | [] -> accum
        in 
        let regs_to_save = loop live_ops_after [] in
        update_save_space (List.length regs_to_save);
        append_instr(List.mapi (fun i r -> Save(r, i)) regs_to_save);
        append_instr [Call(convert_id id, convert_op op, List.map convert_op opl)];
        append_instr(List.mapi (fun i r -> Restore(r, i)) regs_to_save);
      | V.Return op -> append_instr [Return (convert_op op)]
      | V.Malloc(id, opl) -> append_instr [Malloc(convert_id id, List.map convert_op opl)]
      | V.Read(id, op, i) -> append_instr [Read(convert_id id, convert_op op, i)]
      | _ -> append_instr [] (* begin, end *)
    in
    (* main of trans_block *)
    let stmts = blk.stmts in
    Array.iter reg_of_instr stmts;
    (* save allocation in this block *)
    set_past_alloc !allocation blk_id;
  in
  (* >>> end trans_block *)
  Array.iteri (fun i blk -> process_block blk i) live_bblock;
  ProcDecl(lbl, get_nlocal () + !local_space, !instrs_list)

(* entry point *)
let trans nreg lives = List.map (trans_decl nreg lives)
