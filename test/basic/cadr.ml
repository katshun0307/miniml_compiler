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
let caddr = fun x -> x.2.2.1 in
let cdddr = fun x -> x.2.2.2 in

let l = (1, (2, (3, (4, 5)))) in

 and (equal (car l)          1)
(and (equal (cadr l)         2)
(and (equal (caddr l)        3)
(and (equal (car (cdddr l))  4)
     (equal (cdr (cdddr l))  5))));;
