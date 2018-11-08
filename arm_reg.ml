module S = Syntax
open Arm_spec

exception Error of string
let err s = raise (Error s)
let fresh_label = Misc.fresh_id_maker "_"

(* ==== メモリアクセス関連 ==== *)

(* Reg.reg -> reg *)
let reg_mappings = [
  (Reg.reserved_reg, Ip);
  (0, V1);
  (1, V2);
  (2, V3);
  (3, V4);
  (4, V5);
  (5, V6);
  (6, V7);
]

let normal_regs = List.filter (fun r -> r <> Ip) (List.map (fun (_, r) -> r) reg_mappings)

let reg_of r = List.assoc r reg_mappings

(* 「reg中のアドレスからoffsetワード目」をあらわすaddr *)
let mem_access reg offset = RI (reg, offset*4)

let local_access i = mem_access Fp (-i-2)

let param_to_reg = function
    0 -> A1
  | 1 -> A2
  | i -> err ("invalid parameter: " ^ string_of_int i)

let reg_of_operand op = 
  match op with
  | Reg.Param i -> param_to_reg i
  | Reg.Reg r -> reg_of r
  | Reg.Proc l -> err "cannot convert proc to reg"
  | Reg.IntV i -> err "cannot convert immediate to reg"

(* Reg.operand から値を取得し，レジスタrdに格納するような
   stmt listを生成 *)
let gen_operand rd = function
    Reg.Param i ->
    let rs = param_to_reg i in
    if rd = rs then [] else [Instr (Mov (rd, R rs))]
  | Reg.Reg r ->
    let rs = reg_of r in
    if rd = rs then [] else [Instr (Mov (rd, R rs))]
  | Reg.Proc lbl -> [Instr (Ldr (rd, L lbl))]
  | Reg.IntV i -> [Instr (Mov (rd, I i))]

(* create instrs to store register rs to destination *)
let gen_dest (rs: reg) = function
  | Reg.R r -> [Instr(Mov(reg_of r, R rs))]
  | Reg.L l -> [Instr(Str(rs, local_access l))]

let convert_op op = 
  match op with
  | Reg.Param i -> R (param_to_reg i)
  | Reg.Reg r -> R (reg_of r)
  | Reg.Proc l -> L l
  | Reg.IntV i -> I i

(* ==== Regマシンコード --> アセンブリコード ==== *)

let gen_decl (Reg.ProcDecl(name, nlocal, instrs)) =
  (* generated arm statements *)
  let arm_stmts = ref ([]: Arm_spec.stmt list) in
  let append_stmt st = arm_stmts := !arm_stmts @ st in
  let stmt_instr (instr: Reg.instr): unit = 
    match instr with
    | Reg.Move(r, op) -> 
      let r' = reg_of r in
      append_stmt (gen_operand r' op)
    | Reg.BinOp(r, binop, op1, op2) ->
      let r' = reg_of r in
      let op1'  = reg_of_operand op1 in (* op1 must be a register *)
      let op2' = convert_op op2 in (* op2 is an address *)
      (match binop with
       | S.Plus -> 
         append_stmt [Instr(Add(r', op1', op2'))]
       | S.Mult -> 
         append_stmt [Instr(Mul(r', op1', op2'))]
       | S.Lt -> 
         let label1: label = fresh_label "label" in
         let label2: label = fresh_label "label" in
         append_stmt [Instr(Cmp(op1', op2')); Instr(Blt(label1)); Instr(Mov(r', I 0)); Instr(B label2);
                      Label(label1); Instr(Mov(r', I 1)); Label(label2)]);
    | Reg.Goto l -> append_stmt [Instr(B l)]
    | Reg.Call(dest, op, opl) -> 
      let f = List.hd opl in
      let x = List.hd (List.tl opl) in 
      (* step1: save A1, A2 registers to memory, set new arguments to A1, A2 registers *)
      append_stmt([Instr(Str(A1, RI(Sp, 0))); Instr(Str(A2, RI(Sp, 4)));] @ (gen_operand A1 f) @ (gen_operand A2 x));
      (* save registers to local *)
      append_stmt(List.mapi (fun i reg -> Instr(Str(reg, local_access(nlocal-i-1)))) normal_regs);
      (* jump to label *)
      append_stmt([Instr(Blx(reg_of_operand op))]);
      (* return registers to regs *)
      append_stmt(List.mapi (fun i reg -> Instr(Ldr(reg, local_access(nlocal-i-1)))) normal_regs);
      (* Step12: store result *)
      append_stmt(gen_dest A1 dest);
      (* Step13: reset 2 arguments *)
      append_stmt[Instr(Ldr(A1, RI(Sp, 0))); Instr(Ldr(A2, RI(Sp, 4)))]
    | Reg.Label l -> append_stmt [Label l]
    | Reg.BranchIf(op, l) -> 
      append_stmt ([Instr(Cmp(reg_of_operand op, I 0)); Instr(Bne(l))])
    | Reg.Return op ->
      append_stmt ((gen_operand A1 op) @ [Instr (B (name ^ "_ret"))])
    | Reg.Malloc(dest, opl) -> 
      let alloc_size = List.length opl in
      append_stmt([ 
          Instr(Str(A1, RI(Sp, 0)));
          Instr(Str(A2, RI(Sp, 4)));
        ] @
          (gen_operand A1 (Reg.IntV alloc_size)));
      (* jump to function head *)
      append_stmt([Instr(Bl "mymalloc");]);
      (* store contents in allocated space *)
      let some_reg = reg_of Reg.reserved_reg in
      List.iteri (fun i  op -> append_stmt(gen_operand some_reg op @ [Instr(Str(some_reg, RI(A1, 4 * i)))])) opl;
      (* Step12: store result *)
      append_stmt (gen_dest A1 dest);
      (* Step13: reset 2 arguments  *)
      append_stmt([
          Instr(Ldr(A1, RI(Sp, 0)));
          Instr(Ldr(A2, RI(Sp, 4)));
        ]);
    | Reg.Read(dest, op, i) -> 
      if Reg.is_register dest 
      then append_stmt [Instr(Ldr(reg_of (Reg.reg_of_dest dest), mem_access (reg_of_operand op) i))]
      else append_stmt ([
          (* load to reserved reg *)
          Instr(Ldr(reg_of Reg.reserved_reg, mem_access (reg_of_operand op) i))]
          (* store to dest *)
          @ gen_dest (reg_of Reg.reserved_reg) dest
        )
    | Reg.Load(r, offset) -> append_stmt [Instr(Ldr(reg_of r, local_access offset))]
    | Reg.Store(r, offset) -> append_stmt [Instr(Str(reg_of r, local_access offset))]
  in
  (* convert main instrs (store to arm_stmts) *)
  List.iter stmt_instr instrs;
  [ Dir(D_align 2); Dir(D_global name);
    Label name;
  ] @
  [(* step3: save fp *)
    Instr(Str(Fp, RI(Sp, -4)));
    (* step4: save lr *)
    Instr(Str(Lr, RI(Sp, -8)));
    Instr(Sub(Fp, Sp, I 4)); Instr(Sub(Sp, Sp, I ((nlocal + 4) * 4)))] @
  !arm_stmts @
  [
    Label (name ^ "_ret");
    Instr(Add(Sp, Fp, I 4)); 
    (* step8: reset return address *)
    Instr(Ldr(Lr, RI(Fp, -4)));
    (* Step10: reset fp *)
    Instr(Ldr(Fp, RI(Fp, 0)));
    Instr(Bx(Lr))
  ]

let codegen regprog =
  Dir D_text :: List.concat (List.map gen_decl regprog)
