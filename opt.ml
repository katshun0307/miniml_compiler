module Set = MySet
module Map = MyMap

exception Error of string
let err s = raise (Error s)

type opt_configs = {
  mutable dead: bool;
  mutable simple: bool;
  mutable fold: bool
}
(* 複数の CFG を解析し，結果を1つの結果にマージ
   結果は Vm.instr をキーとするマップ(の組)であり，各キーは
   (equalityではなく) identityにより比較されることに注意 *)
let analyze_cfg anlys cfgs =
  let results = List.map (fun (_, cfg) -> Dfa.solve anlys cfg) cfgs in
  { Dfa.before =
      Map.bigmerge (Set.from_list (List.map (fun r ->
          r.Dfa.before) results));
    Dfa.after =
      Map.bigmerge (Set.from_list (List.map (fun r ->
          r.Dfa.after) results)) }


(* 各種最適化をここに追加 *)
let simple_elim (Vm.ProcDecl(lbl, nlocal, instrs)) = 
  let ret_instrs = ref ([]: Vm.instr list) in
  let append_instr ins = ret_instrs := !ret_instrs @ [ins] in
  let elim_instr ins =
    match ins with
    | Vm.Move(id, op) -> 
      if Vm.Local id = op then ()
      else append_instr ins
    | _ -> append_instr ins
  in
  List.iter elim_instr instrs;
  Vm.ProcDecl(lbl, nlocal, !ret_instrs) 

(* constant folding  [-of] *)
let constant_folding (Vm.ProcDecl(lbl, nlocal, instrs)) = 
  let ret_instrs = ref ([]: Vm.instr list) in
  let append_instr ins = ret_instrs := !ret_instrs @ [ins] in
  let bblock = Cfg.vm_to_cfg lbl instrs in
  let reachability_result = Dfa.solve (Reachability.make ()) bblock in
  let get_property ins side = MyMap.from_list(MySet.to_list(MySet.filter (fun x -> x <> Reachability.dummy) (Dfa.get_property reachability_result ins side))) in
  let live_result = Dfa.solve (Live.make ()) bblock in
  let is_alive ins op = MySet.member op (Dfa.get_property live_result ins Cfg.AFTER) in
  let elim_instr ins = 
    let reach = if not (Vm.is_label ins) then get_property ins Cfg.BEFORE else MyMap.empty in
    let search_reach id = MyMap.search id reach in
    let rec convert_op op = 
      match op with
      | Vm.Local id -> (
          match search_reach id with
          | Some x -> if is_alive ins x then convert_op x else op
          | None -> op
        )
      | _ -> op in
    let rec convert_op_to_reg op = 
      match op with
      | Vm.Local id -> (
          match search_reach id with
          | Some x -> if Vm.is_reg x && is_alive ins op 
            then convert_op_to_reg x 
            else op
          | None -> op)
      | _ -> op in
    Vm.(match ins with
        | Move(id, op) -> append_instr ins
        | BinOp(id, bop, op1, op2) -> 
          append_instr (BinOp(id, bop, convert_op_to_reg op1, convert_op op2))
        | Call(id, op, opl) -> append_instr(Call(id, convert_op_to_reg op, List.map convert_op opl))
        | BranchIf(op, l) -> append_instr(BranchIf(convert_op op, l))
        | Return (op) -> append_instr(Return (convert_op op))
        | Malloc(id, opl) -> append_instr(Malloc(id, List.map convert_op opl))
        | Read(id, op, i) -> append_instr(Read(id, convert_op_to_reg op, i))
        | _ -> append_instr ins) in
  List.iter elim_instr instrs;
  Vm.ProcDecl(lbl, nlocal, !ret_instrs)

let dead_elim (Vm.ProcDecl(lbl, nlocal, instrs)) = 
  let ret_instrs = ref ([]: Vm.instr list) in
  let append_instr ins = ret_instrs := !ret_instrs @ [ins] in
  let bblock = Cfg.vm_to_cfg lbl instrs in
  let live_result = Dfa.solve (Live.make ()) bblock in
  let get_property ins side = 
    (MySet.filter (fun x -> x <> Live.dummy) (Dfa.get_property live_result ins side)) in
  let elim_instr ins =
    let live = if not (Vm.is_label ins) then get_property ins Cfg.AFTER else MySet.empty in
    let search_reach id = MySet.member id live in
    match ins with
    | Vm.Move(id, op) -> 
      if search_reach (Vm.Local id)
      then append_instr ins
      else ()
    | _ -> append_instr ins in
  List.iter elim_instr instrs;
  Vm.ProcDecl(lbl, nlocal, !ret_instrs)

let opt vmcode options = 
  let s' = if options.simple then List.map simple_elim vmcode else vmcode in
  let f' = if options.fold then List.map dead_elim (List.map constant_folding s') else s' in
  let d' = if options.dead then List.map constant_folding f' else f' in
  d'

(* レジスタ機械コードの生成．nregは利用可能な汎用物理レジスタの個数 *)
let gen_regcode nreg vmcode debug =
  Reg.trans nreg vmcode debug

let optimize is_disp_cfg nreg vmcode options  =
  let lv = Live.make () in
  (* その他，各種最適化 *)
  let vmcode' = opt vmcode options in
  print_string ("(* optimized vm code*)\n" ^ Vm.string_of_vm vmcode');
  (* 生存変数解析を実行 *)
  let cfgs = Cfg.build vmcode' in
  let lv_results = analyze_cfg lv cfgs in
  (* 解析結果を表示 *)
  if is_disp_cfg then (
    let string_of_prop stmt side =
      lv.Dfa.to_str (Dfa.get_property lv_results stmt side) in
    Cfg.display_cfg cfgs (Some string_of_prop));
  vmcode'
