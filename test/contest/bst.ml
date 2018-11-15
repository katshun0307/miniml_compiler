let equal = fun a -> fun b ->
  if a < b then
    false
  else if b < a then
    false
  else
    true in

let rec insert = fun t -> fun k ->
  if t < 0 then
    (-1, (k, -1))
  else if k < t.2.1 then
    ((insert t.1 k), (t.2.1, t.2.2))
  else if t.2.1 < k then
    (t.1, (t.2.1, (insert t.2.2 k)))
  else
    t in

let rec search = fun t -> fun k ->
  if t < 0 then
    0
  else if k < t.2.1 then
    search t.1 k
  else if t.2.1 < k then
    search t.2.2 k
  else
    1 in

let div2 = fun n ->
  loop x = (n, 0) in
  if x.1 < 2 then x.2
  else recur (x.1 + -2, x.2 + 1) in

let rec mk_tree = fun l -> fun u ->
  if l < u then
    let m = div2 (l + u) in
    let lt = mk_tree l m in
    let lt' = insert lt l in
    let ut = mk_tree (m+1) u in
    let ut' = insert ut u in
    (lt', (m, ut'))
  else
    -1 in

let count = 64 * 64 in
let t = mk_tree 1 count in

equal (loop c = (0, count * 2) in
       if c.2 < 0 then
         c.1
       else
         recur (c.1 + search t c.2, c.2 + -1)) count;;
