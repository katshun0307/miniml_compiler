module S = Syntax
module V = Vm
open Arm_spec

exception Error of string
let err s = raise (Error s)
let fresh_label = Misc.fresh_id_maker "_"

(* ==== メモリアクセス関連 ==== *)

(* 「reg中のアドレスからoffsetワード目」をあらわすaddr *)
let mem_access reg offset = RI (reg, offset * 4)

let local_access (i:V.id) = mem_access Fp (-i-2)

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
  let stmt_instr (instr: V.instr): unit = 
    match instr with
    | V.Move(id, op) -> 
      let r = V1 in
      append_stmt ((gen_operand r op) @ [Instr(Str(r, local_access id))])
    | V.BinOp(id, binop, op1, op2) -> 
      let r1 = V2 in
      let r2 = V3 in
      (match binop with
       | S.Plus -> 
         append_stmt [Instr(Add(r1, r1, R r2)); Instr(Str(r1, local_access id))]
       | S.Mult -> 
         append_stmt [Instr(Mul(r1, r1, R r2)); Instr(Str(r1, local_access id))]
       | S.Lt -> 
         let label1: label = fresh_label "label" in
         let label2: label = fresh_label "label" in
         append_stmt [Instr(Cmp(r1, R r2)); Instr(Blt(label1)); Instr(Mov(r1, I 0)); Instr(B label2);
                      Label(label1); Instr(Mov(r1, I 1)); Label(label2); Instr(Str(r1, local_access id))]);
    | V.Goto l -> append_stmt [Instr(B l)]
    | V.Call(id, op, opl) -> 
      let f = List.hd opl in
      let x = List.hd (List.tl opl) in
      let r = V6 in
      let pointer_r = V4 in
      append_stmt( 
        (* step1: save arguments and set new ones *)
        [Instr(Str(A1, RI(Sp, 0))); Instr(Str(A2, RI(Sp, 4)));] @ (gen_operand A1 f) @ (gen_operand A2 x) @ (gen_operand pointer_r op) @
        [ 
          (* step2: jump to function head *)
          Instr(Blx(pointer_r));
          (* === preprogrammed in function === *)
          (* step3: save fp *)
          (* step4: save lr *)
          (* step5: update fp ($fp <- $fp + 4) *)
          (* step6: move $sp (n+5) words down *)
          (* step7: run function *)
          (* step8: reset return address *)
          (* Step9: reset sp *)
          (* Step10: reset fp *)
          (* Step11: go back to main function *)
          (* === preprogrammed in function === *)

          (* Step12: store result *)
          Instr(Mov(r, R A1));
          (* Step13: reset 2 arguments *)
          Instr(Ldr(A1, RI(Sp, 0))); Instr(Ldr(A2, RI(Sp, -4)));
          (* move answer to specified local var *)
          Instr(Str(r, local_access id))
        ]
      );
    | V.Label l -> append_stmt [Label l]
    | V.BranchIf(op, l) -> 
      let r = V4 in
      append_stmt ((gen_operand r op) @ [Instr(Cmp(r, I 0)); Instr(Bne(l))])
    | V.Return op ->
      append_stmt ((gen_operand A1 op) @ [Instr (B (name ^ "_ret"))])
    | V.Malloc(id, opl) -> 
      let alloc_size = List.length opl in
      let r = V7 in
      append_stmt(
        [Instr(Str(A1, RI(Sp, 0))); Instr(Str(A2, RI(Sp, 4)));] @ (gen_operand A1 (V.IntV alloc_size)) @ 
        [
          (* jump to function head *)
          Instr(Bl "mymalloc");
          (* Step12: store result *)
          Instr(Mov(r, R A1));
          (* Step13: reset 2 arguments *)
          Instr(Ldr(A1, RI(Sp, 0))); Instr(Ldr(A2, RI(Sp, -4)));
          (* move answer to specified local var *)
          Instr(Str(r, local_access id))
        ]
      );
    | V.Read(id, op, i) -> 
      let r = V5 in
      append_stmt ((gen_operand r op)@ [Instr(Ldr(r, mem_access r i)); Instr(Str(r, local_access id))])
    | _ -> () (* BEGIN, END *) in
  (* convert main instrs (store to arm_stmts) *)
  let _ = List.map stmt_instr instrs in
  [ Dir(D_align 2); Dir(D_global name);
    Label name;
    (* step3: save fp *)
    Instr(Str(Fp, RI(Sp, 4)));
    (* step4: save lr *)
    Instr(Str(Lr, RI(Sp, 8)));
    Instr(Sub(Sp, Fp, I 4)); Instr(Sub(Sp, Sp, I ((nlocal + 4) * 4)))] @
  !arm_stmts @
  [
    Label (name ^ "_ret");
    Instr(Add(Sp, Fp, I 4)); 
    (* step8: reset return address *)
    Instr(Ldr(Lr, RI(Fp, 8)));
    (* Step10: reset fp *)
    Instr(Ldr(Fp, RI(Fp, 4)));
    Instr(Bx(Lr))
  ]
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
