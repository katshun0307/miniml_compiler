let equal = fun a -> fun b ->
  if a < b then
    false
  else if b < a then
    false
  else
    true in

let and = fun a -> fun b ->
    if a then
      if b then
        true
      else
        false
    else
      false in


let invoke = fun o -> fun m -> fun a ->
  (if equal m 1 then o.1
   else if equal m 2 then o.2.1
   else o.2.2) a in

let rec make = fun fld ->
  let get = fun d -> fld in
  let set = fun n -> make n in
  let eql = fun o -> equal (invoke o 1 -1) fld in
  (get, (set, eql)) in

let obj1 = make 100 in
let obj2 = invoke obj1 2 200 in

 and (equal (invoke obj1 1 -1) 100)
(and (equal (invoke obj2 1 -1) 200)
(and (invoke obj1 3 obj1)
     (equal (invoke obj1 3 obj2) false)));;
