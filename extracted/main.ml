open Printf
module B = Common.Benchmark
let run benchmarks =
  List.iter B.drive_and_display benchmarks
let quota = "5.0s"

type uint63 = Uint63.t
let uint63 = Uint63.of_int

let inhabitant =
  0

module Make (A : sig
  type 'a t
  val make : uint63 -> 'a -> 'a t
  val length : 'a t -> uint63
  val get : 'a t -> uint63 -> 'a
  val set : 'a t -> uint63 -> 'a -> 'a t
  val of_array : 'a array -> 'a -> 'a t
  val map : ('a -> 'b) -> 'a t -> 'b t
end) = struct

  let convert (a : int array) : uint63 A.t =
    A.of_array a inhabitant
    |> A.map uint63

  let equal equal (p1 : 'a A.t) (p2 : 'a A.t) =
    let n = A.length p1 in
    n = A.length p2 &&
    let rec ok i =
      Uint63.equal i n ||
      equal (A.get p1 i) (A.get p2 i) &&
      ok (Uint63.add i Uint63.one)
    in
    ok Uint63.zero

  (* The extracted code under test. *)

  open Extracted.Make(A)

  (* The benchmark: sorting an integer array of [n] random elements. *)

  let benchmark n name : B.benchmark =
    let basis = n
    and name = sprintf "sort (size %d) (%s)" n name
    and run () =
      (* Allocate a fresh mutable array of integers. *)
      let a : int array = Array.init n @@ fun _i -> Random.int 32768 in
      (* Convert it to a persistent array of unsigned integers. *)
      let p = convert a in
      (* The benchmark is to sort the persistent array [p]. *)
      fun () ->
        let p' = sort (uint63 inhabitant) Uint63.le p in
        ignore p'
    in
    B.benchmark ~name ~quota ~basis ~run

end (* ArrayExtra *)

(* The reference: sorting using OCaml's standard library. *)

let reference n : B.benchmark =
  let basis = n
  and name = sprintf "sort (size %d) (OCaml arrays)" n
  and run () =
    (* Allocate a fresh mutable array of integers. *)
    let a : int array = Array.init n @@ fun _i -> Random.int 32768 in
    (* The benchmark is to sort the array [a]. *)
    fun () ->
      Array.sort compare a
  in
  B.benchmark ~name ~quota ~basis ~run

(* A list of all sorting benchmarks. *)

let benchmarks n = [
  reference n;
  (let module M = Make(UnsafeArray) in M.benchmark n "UnsafeArray");
  (let module M = Make(DefensiveArray) in M.benchmark n "DefensiveArray");
  (let module M = Make(Parray) in M.benchmark n "Parray");
]

(* -------------------------------------------------------------------------- *)

(* Read the command line. *)

let sort =
  ref 0

let () =
  Arg.parse [
    "--sort", Arg.Set_int sort, " <n> Benchmark sort";
  ] (fun _ -> ()) "Invalid usage"

let sort =
  !sort

let possibly n (benchmarks : int -> B.benchmark list) =
  if n > 0 then run (benchmarks n)

(* -------------------------------------------------------------------------- *)

(* Main. *)

let () =
  possibly sort benchmarks
