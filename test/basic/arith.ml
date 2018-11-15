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


let ff = fun x -> fun y -> fun z ->
  x + y * z in
let gg = fun x ->
  x * ff x 2 3 in
let hh = fun x ->
  ff 1 x 3 + gg x in

 and (equal (ff 1 2 3) 7)
(and (equal (gg 10) 160)
     (equal (hh 3) 37));;
