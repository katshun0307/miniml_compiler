open Vm
open Cfg
open Dfa
module Set = MySet
module Map = MyMap

type assignment = id * id

let dummy: assignment = (-1, -1)

(* compare *)
let compare left right =
  if Set.is_empty (Set.diff left right) then
    (if Set.is_empty (Set.diff right left) then EQ else LT)
  else
    (if Set.is_empty (Set.diff right left) then GT else NO)

let string_of_assignment ((id1, id2): assignment): string = 
  "(t" ^ string_of_int id1 ^ "<..t" ^ string_of_int id2 ^ ")"

let string_of_assignments vs =
  String.concat ", "
    (List.sort String.compare
       (List.map string_of_assignment 
          (List.filter (fun v -> v <> dummy) (Set.to_list vs))))

(* TODO *)
let lub = Set.union 

let transfer (entry_vars: assignment Set.t) (stmt: Vm.instr): assignment Set.t = 
  let gen asm = 
    (* return new assignment *)
    match asm with
    | Move(dst, src) -> 
      (match src with
       | Local src' -> Set.singleton (dst, src')
       | _ -> Set.empty)
    | _ -> Set.empty in
  let kill asm = 
    (* return assignments to be killed *)
    let generate_kill_filter dst' ((d, s): assignment) = 
      dst' = d || dst' = s in
    match asm with
    | Move (dst, src) -> 
      let kill_filter = generate_kill_filter dst in
      Set.filter kill_filter entry_vars
    | _ -> Set.empty
  in
  Set.union (gen stmt) (Set.remove_mult (kill stmt) entry_vars)

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
