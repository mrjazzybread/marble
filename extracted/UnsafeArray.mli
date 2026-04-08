type uint63 = Uint63.t
type 'a t
val make    : uint63 -> 'a -> 'a t
val length  : 'a t -> uint63
val get     : 'a t -> uint63 -> 'a
val set     : 'a t -> uint63 -> 'a -> 'a t
val of_array: 'a array -> 'a -> 'a t
val map     : ('a -> 'b) -> 'a t -> 'b t
val blit    : 'a t -> uint63 -> 'a t -> uint63 -> uint63 -> 'a t
