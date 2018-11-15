let equal = fun a -> fun b ->
  if a < b then
    false
  else if b < a then
    false
  else
    true in

let car = fun x -> x.1 in
let cdr = fun x -> x.2 in
let cadr = fun x -> x.2.1 in
let cddr = fun x -> x.2.2 in
let nil = -1 in

let rec insert = fun x -> fun xs ->
  if equal xs nil then
    (x, nil)
  else if x < car xs then
    (x, xs)
  else
    (car xs, insert x (cdr xs)) in

let rec sort = fun xs ->
  if equal xs nil then
    nil
  else insert (car xs) (sort (cdr xs)) in

let rec sorted = fun xs ->
  if equal xs nil then
    true
  else if equal (cdr xs) nil then
    true
  else if cadr xs < car xs then
    false
  else
     sorted (cdr xs) in

let count = 128 * 16 in
let l =
  loop c = (nil, 1) in
  let l = car c in
  let c = cdr c in
  if count < c then
    l
  else
    recur ((c, l), c + 1) in

sorted (sort l);;
