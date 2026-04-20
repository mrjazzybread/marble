module U = Uint63

type uint63 = U.t

let variant =
  "defensive"

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

let blit a i b j n =
  if not a.valid then failwith "blit: stale source array";
  if not b.valid then failwith "blit: stale target array";
  b.valid <- false;
  let data = b.data in
  Array.blit a.data (to_int i) data (to_int j) (to_int n);
  of_array data

let blit' a i j n =
  if not a.valid then failwith "blit': stale array";
  a.valid <- false;
  let data = a.data in
  Array.blit data (to_int i) data (to_int j) (to_int n);
  of_array data

(* The public version of [of_array] has an extra argument [inhabitant]. *)
let[@inline] of_array data _inhabitant =
  of_array data
