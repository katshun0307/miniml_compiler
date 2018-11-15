let equal = fun a -> fun b ->
  if a < b then
    false
  else if b < a then
    false
  else
    true in


let rec ack = fun x -> fun y ->
  if equal y 0 then 0
  else if equal x 0 then 2 * y
  else if equal y 1 then 2
  else ack (x+-1) (ack x (y+-1)) in

equal (ack 2 4) 65536;;
