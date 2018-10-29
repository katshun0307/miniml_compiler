open Vm
open Cfg
open Dfa
module Set = MySet

type assignment = id * operand


let dummy: assignment = (-1, Local(-1))

(* compare *)
let compare left right =
  if Set.is_empty (Set.diff left right) then
    (if Set.is_empty (Set.diff right left) then EQ else LT)
  else
    (if Set.is_empty (Set.diff right left) then GT else NO)

let string_of_assignment ((id, op): assignment): string = 
  "(" ^ string_of_int id ^ " <- " ^ string_of_operand op ^ ")"

let string_of_assignments vs =
  String.concat ", "
    (List.sort String.compare
       (List.map string_of_assignment 
          (List.filter (fun v -> v <> dummy) (Set.to_list vs))))

(* TODO *)
let lub = Set.union 

(* TODO *)
let filter_vars vs =
  Set.from_list (List.filter (fun v ->
      match v with
        Param _ | Local _ -> true
      | Proc _ | IntV _ -> false
    ) (Set.to_list vs))

(* 
– gen(d:x=y)={x=y}
– gen(d:x=e)={}(e is not a variable)
– kill(d:x=e)={z=w|x is not x nor w} 
– fd(X) = gen(d) ∪ (X - kill(d)) 
*)
let transfer (entry_vars: assignment Set.t) (stmt: Vm.instr): assignment Set.t = 
  let gen asm = 
    match asm with
    | Move(dst, src) -> 
      (match src with
       | Local _ -> Set.singleton (dst, src)
       | _ -> Set.empty)
    | _ -> Set.empty in
  let kill asm = 
    match asm with
    | Move (dst, src) -> Set.empty (* todo *)
    | _ -> Set.empty in
  (* TODO *)
  Set.empty

(* make reachability analyzer *)
let make (): assignment Set.t Dfa.analysis = 
  {
    direction = FORWARD;
    transfer = transfer;
    compare = compare;
    lub = lub;
    bottom = Set.empty;
    init = Set.singleton dummy;
    to_str = string_of_assignments;
  }
