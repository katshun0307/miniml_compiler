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


let sumsqr = fun a -> fun b -> fun c ->
  if b < a then
    a * a + (if c < b then b * b else c * c)
  else
    b * b + (if c < a then a * a else c * c) in

 and (equal (sumsqr 3 4 5) 41)
(and (equal (sumsqr 4 5 3) 41)
     (equal (sumsqr 5 3 4) 41));;
