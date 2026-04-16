open Printf
module B = Common.Benchmark

(* The time that we are willing to spend to run one benchmark.
   The benchmark is repeated as many times as possible during
   the allotted time. *)
let quota = "5.0s"

type uint63 = Uint63.t
let uint63 = Uint63.of_int

let inhabitant =
  0

(* -------------------------------------------------------------------------- *)

(* Several ways of constructing arrays of size [n]. *)

let random_array n : int array =
  Random.init 42;
  Array.init n @@ fun _i -> Random.int 32768

let sorted_array n : int array =
  Array.init n @@ fun i -> i

let reversed_array n : int array =
  Array.init n @@ fun i -> n - i

let zeroed_array n : int array =
  Array.make n 0

type construction =
  (int -> int array) * string

let random : construction =
  random_array, "random data"

let sorted : construction =
  sorted_array, "sorted data"

let reversed : construction =
  reversed_array, "reversed data"

(* -------------------------------------------------------------------------- *)

(* A benchmark of the code that I have extracted from Rocq, which is placed
   in the module [Extracted.Make]. The parameter [A] is an implementation of
   the module [Array]. We have several possible implementations; see below. *)

module Make (A : sig
  type 'a t
  val make : uint63 -> 'a -> 'a t
  val length : 'a t -> uint63
  val get : 'a t -> uint63 -> 'a
  val set : 'a t -> uint63 -> 'a -> 'a t
  val of_array : 'a array -> 'a -> 'a t
  val map : ('a -> 'b) -> 'a t -> 'b t
(*
  val blit : 'a t -> uint63 -> 'a t -> uint63 -> uint63 -> 'a t
  val blit' : 'a t -> uint63 -> uint63 -> uint63 -> 'a t
 *)
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

  include Extracted.Make(A)

  (* A benchmark: sorting an integer array of size [n]. *)

  let sort_benchmark n construction (array : string) : B.benchmark =
    let basis = n
    and name =
      sprintf "sorting %s (size %d) (sort/%s)"
        (snd construction) n array
    and run () =
      (* Construct a fresh mutable array of integers. *)
      let a : int array = (fst construction) n in
      (* Convert it to a persistent array of unsigned integers. *)
      let p = convert a in
      (* The benchmark is to sort the persistent array [p]. *)
      fun () ->
        let p' = sort (uint63 inhabitant) Uint63.le p in
        ignore p'
    in
    B.benchmark ~name ~quota ~basis ~run

  (* A benchmark: blitting between integer arrays. *)

  let blit_benchmark n blit (algorithm : string) (array : string) : B.benchmark =
    let basis = n
    and name =
      sprintf "blitting (size %d) (%s/%s)" n algorithm array
    and run () =
      (* Construct two arrays. *)
      let src : int array = sorted_array n
      and dst : int array = zeroed_array n in
      (* Convert them to persistent arrays of unsigned integers. *)
      let src, dst = convert src, convert dst in
      (* The benchmark is to blit from [src] to [dst]. *)
      fun () ->
        let dst' = blit src Uint63.zero dst Uint63.zero (Uint63.of_int n) in
        ignore dst'
    in
    B.benchmark ~name ~quota ~basis ~run

end (* Make *)

(* -------------------------------------------------------------------------- *)

(* The baseline: OCaml's standard [Array] module. *)

let sort_baseline n construction : B.benchmark =
  let basis = n
  and name =
    sprintf "sorting %s (size %d) (Stdlib.Array.sort)"
      (snd construction) n
  and run () =
    (* Allocate a fresh mutable array of integers. *)
    let a : int array = (fst construction) n in
    (* Convert it to an array of type [uint63 array]. *)
    let a : uint63 array = Array.map Uint63.of_int a in
    (* The benchmark is to sort the array [a]. *)
    fun () ->
      Array.sort Uint63.compare a
  in
  B.benchmark ~name ~quota ~basis ~run

let blit_baseline n : B.benchmark =
  let basis = n
  and name =
    sprintf "blitting (size %d) (Stdlib.Array.blit)" n
  and run () =
    (* Construct two arrays. *)
    let src : int array = sorted_array n
    and dst : int array = zeroed_array n in
    (* The benchmark is to blit from [src] to [dst]. *)
    fun () ->
      Array.blit src 0 dst 0 n
  in
  B.benchmark ~name ~quota ~basis ~run

(* -------------------------------------------------------------------------- *)

(* A list of the benchmarks of [blit]. *)

let blit_benchmarks n : B.benchmark list = [
  blit_baseline n;
  (let module M = Make(UnsafeArray) in M.blit_benchmark n M.blit "blit" "UnsafeArray");
  (let module M = Make(UnsafeArray) in M.blit_benchmark n M.simple_blit_aux "simple_blit" "UnsafeArray");
  (let module M = Make(DefensiveArray) in M.blit_benchmark n M.blit "blit" "DefensiveArray");
  (let module M = Make(Parray) in M.blit_benchmark n M.blit "blit" "Parray");
]

(* -------------------------------------------------------------------------- *)

(* A list of the benchmarks of [sort]. *)

let sort_benchmarks n construction : B.benchmark list = [
  sort_baseline n construction;
  (let module M = Make(UnsafeArray) in M.sort_benchmark n construction "UnsafeArray");
  (let module M = Make(DefensiveArray) in M.sort_benchmark n construction "DefensiveArray");
  (let module M = Make(Parray) in M.sort_benchmark n construction "Parray");
]

let sort_benchmarks n : B.benchmark list =
  [ random; sorted; reversed ]
  |> List.map (sort_benchmarks n)
  |> List.flatten

(* -------------------------------------------------------------------------- *)

(* Read the command line. *)

let blit, sort =
  ref 0, ref 0

let () =
  Arg.parse [
    "--blit", Arg.Set_int blit, " <n> Benchmark blit";
    "--sort", Arg.Set_int sort, " <n> Benchmark sort";
  ] (fun _ -> ()) "Invalid usage"

let blit, sort =
  !blit, !sort

let run benchmarks =
  List.iter B.drive_and_display benchmarks

let possibly n (benchmarks : int -> B.benchmark list) =
  if n > 0 then run (benchmarks n)

(* -------------------------------------------------------------------------- *)

(* Main. *)

let () =
  possibly blit blit_benchmarks;
  possibly sort sort_benchmarks;
  ()
