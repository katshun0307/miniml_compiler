module S = Syntax
module V = Vm
open C_spec

let fresh_var = Misc.fresh_id_maker "var" 

let param0_name: id = "param_0"
let param1_name: id = "param_1"

let is_vm_proc = function
  | V.Proc _ -> true
  | _ -> false 

let label_of_proc proc = 
  match proc with
  | V.Proc l -> (l:label)
  | _ -> err "not implemented"

let c_of_decl (Vm.ProcDecl(lbl, local_var, instr_list)): funct =
  (* helper definitions and functions *)
  let var_assoc = ref (MyMap.empty: (V.id, id) MyMap.t) in
  let closure_var = ref (MySet.empty: id MySet.t) in
  let tuple_var = ref (MySet.empty: id MySet.t) in
  let defined_var = ref (MySet.empty: id MySet.t) in
  let id_is_closure (id: id) = MySet.member id !closure_var in
  let id_is_tuple (id: id) = MySet.member id !tuple_var in
  let id_is_defined (id:  id) = MySet.member id !defined_var in
  let op_is_closure = function
    | Var id -> id_is_closure id
    | Imm _ -> false in
  let op_is_tuple = function
    | Var id -> id_is_tuple id
    | Imm _ -> false in
  let append_closure id = closure_var := MySet.insert id !closure_var in
  let append_tuple id = tuple_var := MySet.insert id !tuple_var in
  let append_defined id = defined_var := MySet.insert id !defined_var in
  let convert_id id = 
    match MyMap.search id !var_assoc with
    | Some id' -> id'
    | None -> let id' = fresh_var (string_of_int id) in
      var_assoc := MyMap.append id id' !var_assoc;
      id' in
  let id_of_op op = 
    match op with 
    | V.Local id -> convert_id id
    | _ -> err "id_of_exp: unexpected input" in
  let convert_op op = 
    match op with
    | V.Param i -> if i = 0 then Var param0_name
      else Var param1_name
    | V.Local id -> Var (convert_id id)
    | V.IntV i -> Imm i
    | V.Proc l -> Var ("unexpected_" ^ l) in
  (* end helper definition and functions *)
  let rec c_of_instr instr = 
    match instr with 
    | V.Move(id, op) -> 
      let id' = convert_id id in
      let op' = convert_op op in
      let id_was_defined = id_is_defined id' in
      let is_closure = op_is_closure op' in
      let is_tuple = op_is_tuple op' in
      if is_closure then append_closure id';
      if is_tuple then append_tuple id';
      append_defined id';
      let ty = if id_was_defined then Defined 
        else (if is_closure then Closure else if is_tuple then Tuple else Int) in
      [Decl(ty, convert_id id, convert_op op)]
    | V.BinOp(id, binop, op1, op2) -> [Bin(convert_id id, binop, Exp(convert_op op1), Exp(convert_op op2))]
    | V.Label l -> [C_spec.Label l]
    | V.BranchIf(op, l) -> [If(convert_op op, Goto(l))]
    | V.Goto l -> [Goto l]
    | V.Call(dest, op, opl) -> 
      (match opl with
       | closure:: x:: [] -> [Call(convert_id dest, id_of_op op, id_of_op closure, convert_op x)]
       | _ -> err "unexpected function call")
    | V.Return op -> [Return(convert_op op)]
    | V.Malloc(id, opl) ->
      (match opl with
       | pointer:: vars ->
         if is_vm_proc pointer then (* if tuple is closure *)
           let closure_name = convert_id id in
           append_closure closure_name;
           append_defined closure_name;
           let funct_name = label_of_proc pointer in
           let var_len = List.length vars in
           [DeclareClosure closure_name; SetClosurePointer(closure_name, funct_name);
            SetClosureLength (closure_name, var_len + 1); DeclareClosureParams(var_len + 1)] @
           (List.mapi (fun i op -> StoreClosureParams(i+1, convert_op op)) vars) @
           [SetClosureParams closure_name;]
         else (* if tuple is not closure (a normal tuple) *)
           let len = List.length opl in
           let id' = convert_id id in
           append_tuple id';
           [DeclareTuple(id', len)] @
           List.mapi (fun i op -> SetTupleValue(id', i, convert_op op)) opl
       | _ -> err "undefined")
    | V.Read(id, op, i) -> 
      if op_is_closure (convert_op op) then 
        (if i = 0 
         then [DeclarePointer(convert_id id); AssignPointer(convert_id id, id_of_op op)]
         else [Read(convert_id id, convert_op op, i)])
      else [Read(convert_id id, convert_op op, i)]
    | V.BEGIN _ -> err "error"
    | V.END _ -> err "error" in
  let instrs = List.concat (List.map c_of_instr instr_list) in
  if lbl = "_toplevel" 
  then Funct("main", [], instrs)
  else Funct(lbl, [param0_name; param1_name], instrs)


let convert_c = List.map c_of_decl 
