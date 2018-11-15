let and = fun a -> fun b ->
    if a then
      if b then
        true
      else
        false
    else
      false in


let rec ev = fun o -> fun n ->
  if n < 1 then true
  else o ev (n+-1) in

let rec od = fun e -> fun n ->
  if n < 1 then false
  else e od (n+-1) in

let even = ev od in
let odd = od ev in

and (even 8) (odd 9);;
