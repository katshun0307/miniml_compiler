type 'a t

val empty : 'a t
val is_empty : 'a t -> bool
val singleton : 'a -> 'a t
val from_list : 'a list -> 'a t
val to_list : 'a t -> 'a list
val insert : 'a -> 'a t -> 'a t
val union : 'a t -> 'a t -> 'a t
val remove : 'a -> 'a t -> 'a t
val remove_mult : 'a t -> 'a t -> 'a t
val diff : 'a t -> 'a t -> 'a t
val member : 'a -> 'a t -> bool

val map : ('a -> 'b) -> 'a t -> 'b t
val bigunion : 'a t t -> 'a t
(* added *)
val filter : ('a -> bool) -> 'a t -> 'a t
val exists : 'a -> 'a t -> bool
val intersection : 'a t -> 'a t -> 'a t
