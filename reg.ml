module V = Vm

exception Error of string
let err s = raise (Error s)

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
  (* store generated instrs *)
  let instrs_list = ref ([]: instr list) in
  let append_instr d = instrs_list := (!instrs_list @ d) in
  let old_ops = ref (MySet.empty: V.operand MySet.t) in
  (* manage offset *)
  let offset_counter = ref 0 in
  let get_new_offset () = 
    let r = !offset_counter in
    offset_counter := !offset_counter + 1;
    r in
  (* manage allocation of Vm.id to dest *)
  let dest_alloc = ref (MyMap.empty: (V.id, dest) MyMap.t) in
  let append_alloc (id, d) = dest_alloc := MyMap.append id d !dest_alloc in
  let free_alloc id = dest_alloc := MyMap.remove id !dest_alloc in
  let alloc_status () = 
    let rec loop l raccum laccum =
      (match l with
       | (_, R i):: tl -> loop tl (i :: raccum) laccum
       | (_, L i):: tl -> loop tl raccum (i:: laccum)
       | [] -> (raccum, laccum)) in
    loop (MyMap.to_list !dest_alloc) [] [] 
  in
  let get_used_reg () = 
    let (r_usage, _) = alloc_status () in
    r_usage
  in
  let get_nlocal () = 
    let (_, l_usage) = alloc_status () in
    List.length l_usage 
  in
  let get_free_reg () = 
    let used = get_used_reg () in
    List.filter (fun x -> not (List.exists (fun y -> y = x) used)) (List.init nreg (fun x -> x)) 
  in
  let convert_id id = 
    match MyMap.search id !dest_alloc with
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
    let id_off' = MyMap.reverse_search (L off) !dest_alloc in
    let id_reg' = MyMap.reverse_search (R r) !dest_alloc in
    let (id_off, id_reg) = 
      match (id_off', id_reg') with
      | Some o, Some r -> (o, r)
      | _ -> err "failed to swap" in
    dest_alloc := MyMap.assoc id_off (R r) !dest_alloc;
    dest_alloc := MyMap.assoc id_reg (L off) !dest_alloc;
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
  (* decide register allocation based on live analysis *)
  let live_bblock = Cfg.vm_to_cfg lbl instrs in
  let live_result = Dfa.solve (Live.make ()) live_bblock in
  let get_property = Dfa.get_property live_result in
  let decide_allocation instr =
    let before = get_property instr Cfg.BEFORE in
    let after = get_property instr Cfg.AFTER in
    (* transfer same allocations *)
    (* let same_ops = MySet.to_list(MySet.intersection before after) in
       let same_alloc = List.filter (fun (id, _) -> List.exists (fun y -> y = V.Local id) same_ops) (MyMap.to_list !dest_alloc) in
       dest_alloc := MyMap.from_list same_alloc; *)
    (* add new allocations *)
    let new_ops = MySet.diff after before in
    let get_dest op = 
      match op with
      | V.Local id -> 
        let id' = convert_id id in
        append_alloc (id, id')
      | _ -> ()
    in
    List.iter get_dest (MySet.to_list new_ops);
    (* save old ops for next *)
    let old_op = MySet.diff before after in
    old_ops := old_op;
    (* remove old ops in previous instr *)
    let remove_allocs op = 
      match op with
      | V.Local id -> free_alloc id;
      | _ -> ()
    in
    List.iter remove_allocs (MySet.to_list !old_ops); 
  in
  let reg_of_instr instr =
    decide_allocation instr;
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
      else append_instr [BinOp(reserved_reg, bop, convert_op op1, convert_op op2)]
    | V.Label l -> append_instr [Label l]
    | V.BranchIf(op, l) -> append_instr [BranchIf(convert_op op, l)]
    | V.Goto l -> append_instr [Goto l]
    | V.Call(id, op, opl) -> append_instr [Call(convert_id id, convert_op op, List.map convert_op opl)]
    | V.Return op -> append_instr [Return (convert_op op)]
    | V.Malloc(id, opl) -> append_instr [Malloc(convert_id id, List.map convert_op opl)]
    | V.Read(id, op, i) -> append_instr [Read(convert_id id, convert_op op, i)]
    | _ -> append_instr [] (* begin, end *)
  in
  List.iter reg_of_instr instrs;
  ProcDecl(lbl, get_nlocal (), !instrs_list)

(* entry point *)
let trans nreg lives = List.map (trans_decl nreg lives)
