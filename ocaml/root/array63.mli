(* This is essentially a fragment of the API offered by the file [Parray.mli]
   in Rocq's kernel. *)

(**[variant] identifies which implementation of this API is being used. *)
val variant    : string

(* The following are the basic axioms in Rocq's primitive array API. *)

type 'a t

val make       : Uint63.t -> 'a -> 'a t
val length     : 'a t -> Uint63.t
val get        : 'a t -> Uint63.t -> 'a
val set        : 'a t -> Uint63.t -> 'a -> 'a t

(* val max_length : Uint63.t *)

(* The following functions cannot be used by the code that we extract from
   Rocq. They can be useful in glue code, benchmarks, etc. *)

val of_array   : 'a array -> 'a -> 'a t
val map        : ('a -> 'b) -> ('a t -> 'b t)

(* The following functions are normally not used by the code that we extract
   from Rocq, but could be used if suitable [Extract Constant] commands are
   provided. They may also be used in benchmarks. *)

val blit       : 'a t -> Uint63.t -> 'a t -> Uint63.t -> Uint63.t -> 'a t
val blit'      : 'a t -> Uint63.t -> Uint63.t -> Uint63.t -> 'a t
