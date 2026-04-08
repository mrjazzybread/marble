module U = Uint63

type uint63 = U.t

type 'a t =
  'a array

let[@inline] to_int (i : uint63) : int =
  U.to_int_min i Sys.max_array_length

let make n x =
  Array.make (to_int n) x

let[@inline] get a i =
  Array.get a (to_int i)

let[@inline] set a i x =
  Array.set a (to_int i) x;
  a

let[@inline] length a =
  U.of_int (Array.length a)

let map =
  Array.map

let blit a i b j n =
  Array.blit a (to_int i) b (to_int j) (to_int n);
  b

(* The public version of [of_array] has an extra argument [inhabitant]. *)
let[@inline] of_array data _inhabitant =
  data
