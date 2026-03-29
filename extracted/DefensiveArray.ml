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
  if a.valid then
    Array.get a.data (to_int i)
  else
    failwith "get: stale array"

let[@inline] set a i x =
  if a.valid then begin
    a.valid <- false;
    let data = a.data in
    Array.set data (to_int i) x;
    of_array data
  end
  else
    failwith "set: stale array"

let[@inline] length a =
  if a.valid then
    U.of_int (Array.length a.data)
  else
    failwith "length: stale array"

let map f a =
  Array.map f a.data
  |> of_array

(* The public version of [of_array] has an extra argument [inhabitant]. *)
let[@inline] of_array data _inhabitant =
  of_array data
