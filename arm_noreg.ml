module S = Syntax
module V = Vm
open Arm_spec

exception Error of string
let err s = raise (Error s)
let fresh_label = Misc.fresh_id_maker "_"

(* ==== メモリアクセス関連 ==== *)

(* 「reg中のアドレスからoffsetワード目」をあらわすaddr *)
let mem_access reg offset = RI (reg, offset * 4)

let local_access i = mem_access Fp (-i-2)

(* Vm.Param は 0 から数えるものと仮定 *)
let param_to_reg = function
    0 -> A1
  | 1 -> A2
  | i -> err ("invalid parameter: " ^ string_of_int i)

(* Vm.operandから値を取得し，レジスタrdに格納するような
   stmt listを生成 *)
let gen_operand rd = function
    Vm.Param i ->
    let rs = param_to_reg i in
    if rd = rs then [] else [Instr (Mov (rd, (R rs)))]
  | Vm.Local i -> [Instr (Ldr (rd, local_access i))]
  | Vm.Proc  lbl -> [Instr (Ldr (rd, L lbl))]
  | Vm.IntV  i -> [Instr (Mov (rd, I i))]

(* ==== 仮想マシンコード --> アセンブリコード ==== *)

(* V.decl -> loc list *)
let gen_decl (Vm.ProcDecl (name, nlocal, instrs)): Arm_spec.stmt list =
  (* generated arm statements *)
  let arm_stmts = ref ([]: Arm_spec.stmt list) in
  let append_stmt st = arm_stmts := !arm_stmts @ st in
  (* generated ssociation from var to reg *)
  let assoc_set = ref (MyMap.empty: (V.id, reg) MyMap.t) in
  (* append new association *)
  let append_assoc (k, v) = assoc_set := MyMap.append k v !assoc_set in
  (* search in association *)
  let search_assoc id = MyMap.search id !assoc_set in
  (* return new reg to use *)
  let get_new_reg () = V1 in 
  (* get reg or generate if not exists *)
  let reg_of_id id = 
    match search_assoc id with
    | Some r -> r
    | None -> let new_reg = get_new_reg () in
      append_assoc (id, new_reg);
      new_reg in
  (* get reg from operand (append to assoc set when needed) *)
  let reg_of_operand op: reg = 
    match op with
    | V.Param i -> param_to_reg i
    | V.Local id -> (match search_assoc id with
        | Some x -> x
        | None -> 
          let new_reg = get_new_reg () in
          append_assoc (id, new_reg);
          new_reg
      )
    | IntV i -> 
      let new_reg = get_new_reg () in 
      (* save immidiate to reg *)
      append_stmt [Instr(Mov (new_reg, I i))];
      new_reg
    | _ ->  err "not implemented" (* placeholder *)
  and addr_of_operand op: addr = 
    match op with
    | V.Param i -> R(param_to_reg i) 
    | V.Local id -> local_access id
    | V.Proc l -> L l
    | V.IntV i -> I i in
  let stmt_instr (instr: V.instr): unit = 
    match instr with
    | V.Move(id, op) -> 
      let r = reg_of_id id in
      append_stmt (gen_operand r op)
    | V.BinOp(id, binop, op1, op2) -> 
      let r1 = reg_of_operand op1 in
      let r2 = reg_of_operand op2 in
      (match binop with
       | S.Plus -> 
         append_stmt [Instr(Add(r1, r1, R r2)); Instr(Str(r1, addr_of_operand(V.Local(id))))]
       | S.Mult -> 
         append_stmt [Instr(Mul(r1, r1, R r2)); Instr(Str(r1, addr_of_operand(V.Local(id))))]
       | S.Lt -> 
         let label1: label = fresh_label "label" in
         let label2: label = fresh_label "label" in
         append_stmt [Instr(Cmp(r1, R r2)); Instr(Blt(label1)); Instr(Mov(r1, I 0)); Instr(B label2);
                      Label(label1); Instr(Mov(r1, I 1)); Label(label2)]);
    | V.Goto l -> append_stmt [Instr(B l)]
    | V.Call(id, op, opl) -> ()
    | V.Label l -> append_stmt [Label l]
    | V.BranchIf(op, l) -> 
      let new_reg = get_new_reg () in
      append_stmt ((gen_operand new_reg op) @ [Instr(Cmp(new_reg, I 0)); Instr(Bne(l))])
    | V.Return op ->
      append_stmt ((gen_operand A1 op) @ [Instr (B "(label of function tail comes here)")])
    | V.Malloc(id, opl) -> ()
    | V.Read(id, op, i) -> 
      let r = reg_of_id id in
      append_stmt ((gen_operand r op)@ [Instr(Ldr(r, mem_access r i)); Instr(Str(r, R (reg_of_id id)))])
    | _ -> () in
  let _ = List.map stmt_instr instrs in
  !arm_stmts
(* placeholder *)
(* [Dir (D_align 2);
   Dir (D_global name);
   Label name;
   Instr (Mov (A1, I 1));
   Label (name ^ "_ret");
   Instr (Bx Lr)] *)

(* entry point: Vm.decl list -> stmt list *)
let codegen (vmprog: V.decl list): stmt list =
  Dir D_text :: List.concat (List.map gen_decl vmprog)
