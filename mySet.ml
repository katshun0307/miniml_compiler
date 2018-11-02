type 'a t = 'a list

let empty = []

let is_empty = function
    [] -> true
  | x::xs -> false

let singleton x = [x]

let from_list x = x
let to_list x = x

let rec insert x = function
    [] -> [x]
  | y::rest -> if x = y then y :: rest else y :: insert x rest

let union xs ys =
  List.fold_left (fun zs x -> insert x zs) ys xs

let rec remove x = function
    [] -> []
  | y::rest -> if x = y then rest else y :: remove x rest

let rec remove_mult xs self = 
  match xs with
  | hd:: tl -> remove_mult tl (remove hd self)
  | [] -> self

let diff xs ys = (* xs - ys *)
  List.fold_left (fun zs x -> remove x zs) xs ys

let member = List.mem

let rec map f = function
    [] -> []
  | x :: rest -> insert (f x) (map f rest)

let rec bigunion = function
    [] -> []
  | set1 :: rest -> union set1 (bigunion rest)

(* added *)
let rec filter f self = 
  let rec loop accum l = 
    match l with
    | hd:: tl -> if f hd then loop (hd::accum) tl else loop accum tl
    | [] -> accum
  in loop [] self

let rec exists x = function
  | hd:: tl -> if x = hd then true else exists x tl
  | [] -> false

let rec intersection s1 s2 = 
  match s1 with
  | hd:: tl -> if exists hd s2 then hd:: (intersection tl s2)
    else intersection tl s2
  | [] -> []
