open Vm
open Cfg
open Dfa
module Set = MySet

type def = (Vm.id * Vm.operand)

let dummy: def = (-1, Local (-1))

(* compares which set is greater *)
let compare left right =
  if Set.is_empty (Set.diff left right) then
    (if Set.is_empty (Set.diff right left) then EQ else LT)
  else
    (if Set.is_empty (Set.diff right left) then GT else NO)

(* get string of Vm.op *)
let string_of_vars vs =
  String.concat ", "
    (List.sort String.compare
       (List.map (fun (id, op) -> "(t" ^ string_of_int id ^ ", " ^ Vm.string_of_operand op ^ ")" )
          (List.filter (fun v -> v <> dummy) (Set.to_list vs))))

let lub = Set.union 

let filter_vars vs =
  Set.from_list (List.filter (fun v ->
      match v with
        Param _ | Local _ -> true
      | Proc _ | IntV _ -> false
    ) (Set.to_list vs))

let transfer (entry_vars: def Set.t) (stmt: Vm.instr): def Set.t = 
  let gen vs =
    lub
      (match stmt with
       | Move (dst, src) -> if Vm.Local dst <> src then Set.singleton (dst, src) else Set.empty
       | _ -> Set.empty
      )
      vs in
  let kill vs =
    match stmt with
    | Move(dst, src) -> 
      (let map = Map.from_list (Set.to_list entry_vars) in
       match Map.search dst map with
       | Some _ -> MySet.remove (dst, src) vs
       | None -> vs)
    | _ -> vs in
  gen (kill entry_vars)

(* make reachability analyzer *)
let make (): def Set.t Dfa.analysis = 
  {
    direction = FORWARD;
    transfer = transfer;
    compare = compare;
    lub = lub;
    bottom = Set.empty;
    init = Set.singleton dummy;
    to_str = string_of_vars;
  }
