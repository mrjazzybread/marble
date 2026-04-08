module U = Uint63

type uint63 = U.t

type 'a t =
  { mutable valid : bool; data : 'a array }

let[@inline] to_int (i : uint63) : int =
  assert (U.le i (U.of_int Sys.max_array_length));
  U.to_int_min i Sys.max_array_length

let[@inline] of_array data =
  { valid = true; data }

let make n x =
  Array.make (to_int n) x
  |> of_array

let[@inline] get a i =
  if not a.valid then failwith "get: stale array";
  Array.get a.data (to_int i)

let[@inline] set a i x =
  if not a.valid then failwith "set: stale array";
  a.valid <- false;
  let data = a.data in
  Array.set data (to_int i) x;
  of_array data

let[@inline] length a =
  if not a.valid then failwith "length: stale array";
  U.of_int (Array.length a.data)

let map f a =
  Array.map f a.data
  |> of_array

(* The public version of [of_array] has an extra argument [inhabitant]. *)
let[@inline] of_array data _inhabitant =
  of_array data
