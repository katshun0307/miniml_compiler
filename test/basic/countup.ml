let equal = fun a -> fun b ->
  if a < b then
    false
  else if b < a then
    false
  else
    true in


let countup = fun n ->
  loop i = 0 in
  if i < n then
    recur (i+1)
  else
    i in

equal (countup 32) 32;;
