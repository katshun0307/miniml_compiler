let equal = fun a -> fun b ->
  if a < b then
    false
  else if b < a then
    false
  else
    true in

let rec fib = fun n ->
  if n < 2 then
    n
  else
    fib (n+-1) + fib (n+-2) in

let fib_iter = fun n ->
  loop c = ((0, 1), n) in
  let a = c.1.1 in
  let b = c.1.2 in
  let n = c.2 in
  if n < 1 then
    a
  else if n < 2 then
    b
  else
    recur ((b, a + b), n+-1) in
  
let n = 38 in
equal (fib n) (fib_iter n);;
