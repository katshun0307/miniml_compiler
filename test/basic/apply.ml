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


let apply = fun f -> fun x -> f x in

 and (equal (apply (fun x -> x + 1) 3) 4)
(and (equal (apply (fun x -> x + x) 3) 6)
     (equal (apply (fun x -> x * x) 3) 9));;
