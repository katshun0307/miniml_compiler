let equal = fun a -> fun b ->
  if a < b then
    false
  else if b < a then
    false
  else
    true in

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

let seed = 3 in
let count = 100 * 10 in
let recurrence = fun n -> fun m ->
  loop c = (n, (m, (seed, count))) in
  let n = c.1 in
  let c' = c.2 in
  let m = c'.1 in
  let c'' = c'.2 in
  let s = c''.1 in
  let i = c''.2 in
  if 0 < i then
    let r   = mod (17 * s  + 5) 128 in
    let r'  = mod (17 * r  + 5) 128 in
    let r'' = mod (17 * r' + 5) 128 in
    recur (m, (mod (r * m + r' * n + r'') 128, (r'', i + -1)))
  else
    m in

equal (recurrence 3 5) 14;;
