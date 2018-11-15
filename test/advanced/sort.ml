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

let car = fun x -> x.1 in
let cdr = fun x -> x.2 in
let cadr = fun x -> x.2.1 in
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
  else
    and (car xs < cadr xs) (sorted (cdr xs)) in

let l = (3, (1, (4, (5, (2, nil))))) in

sorted (sort l);;
