let equal = fun a -> fun b ->
  if a < b then
    false
  else if b < a then
    false
  else
    true in

let rec ev = fun o -> fun n ->
  if n < 1 then true
  else o ev (n+-1) in

let rec od = fun e -> fun n ->
  if n < 1 then false
  else e od (n+-1) in

let even = ev od in
let odd = od ev in

let rec minus = fun n -> fun m ->
  loop c = (n, m) in
  let n = c.1 in
  let m = c.2 in
  if m < 1 then
    n
  else
    recur (n + -1, m + -1) in

let mod = fun n -> fun m ->
  loop i = 0 in
  if n < i then
    minus (n + m) i
  else
    recur (i + m) in

let rec next = fun n ->
  let n' = mod (17 * n + 5) 128 in
  (fun d -> next n', even n') in

let count = 90 * 100 in
let rand = next 3 in
let walk = fun pos ->
  loop c = (pos, (rand, count)) in
  let p = c.1 in
  let r = c.2.1 in
  let c = c.2.2 in
  if c < 1 then
    p
  else
    let r' = r.1 0 in
    let d = r.2 in
    let p' = if d then p+1 else p + -1 in
    recur (p', (r', c + -1)) in

equal (walk 0) 0;;
