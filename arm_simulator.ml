open Arm_spec

exception Error of string
let err s = raise (Error s)
let impl_err () = err "Implementation Error"

type reg_file = (reg * int) list
type label_table = (label * int) list

type machine_state = {
   reg_file : reg_file;
   stack : int array;
   heap : int array;
   cond_n : bool;
   cond_z : bool;
   label_table : label_table;
   pc : int;
 }

let heap_base_address = min_int

let stack_base_address = max_int

let get_heap_tail_address state = heap_base_address + (Array.length state.heap) * 4

let get_stack_index addr = (stack_base_address - addr) / 4

let get_heap_index addr = (addr - heap_base_address) / 4

let get_reg_val state reg = List.assoc reg state.reg_file

let get_stack_val state addr = Array.get state.stack (get_stack_index addr)

let get_heap_val state addr = Array.get state.heap (get_heap_index addr)

let get_mem_val state addr = (if addr >= 0 then get_stack_val else get_heap_val) state addr

let get_label_val state l = List.assoc l state.label_table

let get_addr_val state = function
  | I i -> i
  | R r -> get_reg_val state r
  | RI (r, i) -> (get_reg_val state r) + i
  | L l -> get_label_val state l

let get_A1 state = get_reg_val state A1

let set_reg_val state reg v =
  let rec update l k v = (match l with
     | [] -> []
     | (k', v') :: l' -> if k = k' then (k, v) :: l'
                         else (k', v') :: (update l' k v))
  in { state with reg_file = update state.reg_file reg v }

let extend_stack state addr =
  { state with stack = Array.append state.stack (Array.make (addr / 4) 0) }

let extend_heap state addr =
  { state with heap = Array.append state.heap (Array.make (addr / 4) 0) }

let set_stack_val state addr v =
  let i = get_stack_index addr in
  let state =
    if Array.length state.stack <= i
    then extend_stack state ((i - Array.length state.stack + 1) * 4)
    else state in
  Array.set state.stack i v; state

let set_heap_val state addr v =
  let i = get_heap_index addr in
  let state =
    if Array.length state.heap <= i
    then extend_heap state ((i - Array.length state.heap + 1) * 4)
    else state in
  Array.set state.heap i v; state

let set_mem_val state addr v = (if addr >= 0 then set_stack_val else set_heap_val) state addr v

let rec fetch_instr stmts addr =
  if addr = 0 then stmts else fetch_instr (List.tl stmts) (addr-1)

let inc_pc state = { state with pc = state.pc + 1 }

let set_pc state n = { state with pc = n }

let analyze_label =
  let f (tbl, n, stmts) = function
    | Dir _ -> (tbl, n, stmts)
    | Label l -> ((l, n) :: tbl, n, stmts)
    | Instr i -> (tbl, n+1, stmts @ [Instr i])
  in List.fold_left f ([], 0, [])

let run all_stmts initial_state =
  let rec step state = function
    | [] -> state
    | (Instr instr) :: rest ->
      (match instr with
       | Add (r1, r2, addr) ->
         let r2_val = get_reg_val state r2 in
         let addr_val = get_addr_val state addr in
         step (inc_pc (set_reg_val state r1 (r2_val + addr_val))) rest
       | B l -> let (state,  rest) = jump state l in step state rest
       | Bl l ->
         let state = set_reg_val state Lr (state.pc + 1) in
         let (state, rest) = jump state l in
         step state rest
       | Blt l ->
         if state.cond_n
         then let (state, rest) = jump state l in step state rest
         else step (inc_pc state) rest
       | Blx r ->
         let state = set_reg_val state Lr (state.pc + 1) in
         let r_val = get_reg_val state r in
         step (set_pc state r_val) (fetch_instr all_stmts r_val)
       | Bne l ->
         if not state.cond_z
         then let (state, rest) = jump state l in step state rest
         else step (inc_pc state) rest
       | Bx r ->
         let r_val = get_reg_val state r in
         step (set_pc state r_val) (fetch_instr all_stmts r_val)
       | Cmp (r, addr) ->
         let sub = (get_reg_val state r) - (get_addr_val state addr) in
         let cond_n = sub < 0 in
         let cond_z = sub = 0 in
         step (inc_pc { state with cond_n = cond_n; cond_z = cond_z }) rest
       | Ldr (r, addr) ->
         let mem_val = (match addr with
          | I i -> i
          | R r -> get_mem_val state (get_reg_val state r)
          | RI (r, i) -> get_mem_val state ((get_reg_val state r) + i)
          | L l -> get_label_val state l) in
         step (inc_pc (set_reg_val state r mem_val)) rest
       | Mov (r, addr) -> step (inc_pc (set_reg_val state r (get_addr_val state addr))) rest
       | Mul (r1, r2, addr) ->
         let r2_val = get_reg_val state r2 in
         let addr_val = get_addr_val state addr in
         step (inc_pc (set_reg_val state r1 (r2_val * addr_val))) rest
       | Str (r, addr) ->
         let r_val = get_reg_val state r in
         let address = get_addr_val state addr in
         step (inc_pc (set_mem_val state address r_val)) rest
       | Sub (r1, r2, addr) ->
         let r2_val = get_reg_val state r2 in
         let addr_val = get_addr_val state addr in
         step (inc_pc (set_reg_val state r1 (r2_val - addr_val))) rest)
    | _ -> impl_err ()
  and jump state l =
    if l = "_toplevel_ret" then (state, []) else
    if l = "mymalloc"
    then
      let a1_val = get_reg_val state A1 in
      let ret_val = get_heap_tail_address state in
      let pc = get_reg_val state Lr in
      let state = set_reg_val (extend_heap state a1_val) A1 ret_val in
      (set_pc state pc, fetch_instr all_stmts pc)
    else
      let pc = get_label_val state l in (set_pc state pc, fetch_instr all_stmts pc) in
  step initial_state (fetch_instr all_stmts initial_state.pc)

let simulate stmts =
  let (tbl, _, stmts) = analyze_label stmts in
  let initial_state = {
    reg_file =
        [(A1, 0); (A2, 0); (A3, 0); (A4, 0);
         (V1, 0); (V2, 0); (V3, 0); (V4, 0); (V5, 0); (V6, 0); (V7, 0);
         (Fp, stack_base_address); (Ip, 0); (Sp, stack_base_address); (Lr, 0)];
    stack = Array.make 0 0;
    heap = Array.make 0 0;
    cond_n = false;
    cond_z = false;
    label_table = tbl;
    pc = 0;
  } in
  run stmts (set_pc initial_state (get_label_val initial_state "_toplevel"))

let string_of_stack = Array.fold_left (fun acc n -> acc ^ (string_of_int n) ^ "\n") ""

let string_of_heap = string_of_stack

let string_of_regfile reg_file =
  List.fold_left (fun acc (reg, v) -> acc ^ string_of_reg reg ^ ": " ^ string_of_int v ^ "\n")
                 "" reg_file

let string_of_state state =
  "[Stack]\n" ^ string_of_stack state.stack ^
  "\n[Heap]\n" ^ string_of_heap state.heap ^
  "\n[Register file]\n" ^ string_of_regfile state.reg_file
