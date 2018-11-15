let equal = fun a -> fun b ->
  if a < b then
    false
  else if b < a then
    false
  else
    true in


let rec is_even = fun n ->
  if n < 1 then
    true
  else if n < 2 then
    false
  else
    is_even (n + -2) in

let div2 = fun n ->
  loop x = (n, 0) in
  if x.1 < 2 then x.2
  else recur (x.1 + -2, x.2 + 1) in

let rec expt = fun b -> fun n ->
  if n < 1 then
    1
  else if is_even n then
    let n' = expt b (div2 n) in
    n' * n'
  else
    b * expt b (n + -1) in

equal (expt 2 13) 8192;;
