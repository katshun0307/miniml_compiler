let equal = fun a -> fun b ->
  if a < b then
    false
  else if b < a then
    false
  else
    true in

let extend = fun e -> fun k -> fun v ->
  fun k' ->
    if equal k k' then
      v
    else
      e k' in

let lookup = fun e -> fun k -> e k in

let empty_env = fun k -> -1 in

let nil = -1 in
let car = fun x -> x.1 in
let cdr = fun x -> x.2 in

let make_square_env = fun n ->
  loop c = (empty_env, n) in 
  if cdr c < 1 then
    car c
  else
    let a = cdr c in
    recur (extend (car c) a (a * a), a + -1) in

let n = 128 in
let env = make_square_env n in

let r =
  loop c = (0, (1, 100 * 5 + 99)) in
  if n < car (cdr c) then
    (if cdr (cdr c) < 1 then
       car c
     else
       recur (car c, (1, cdr (cdr c) + -1)))
  else
    recur (car c + lookup env (car (cdr c)),
           (car (cdr c) + 1, cdr (cdr c))) in

equal r (100 * n * (n + 1) * (2 * n + 1));;
