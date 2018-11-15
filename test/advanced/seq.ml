let equal = fun a -> fun b ->
  if a < b then
    false
  else if b < a then
    false
  else
    true in

let car = fun x -> x.1 in
let cdr = fun x -> x.2 in
let nil = -1 in


let rec map = fun f -> fun xs ->
  if equal xs nil then
    nil
  else
    (f (car xs), map f (cdr xs)) in

let reduce = fun f -> fun a -> fun xs ->
  let rec red = fun a -> fun xs ->
    if equal xs nil then
      a
    else
      red (f a (car xs)) (cdr xs) in
  red a xs in

let l = (1, (2, (3, (4, (5, nil))))) in

equal (reduce (fun x -> fun y -> x + y)
         0 (map (fun x -> x + x) l)) 30;;
