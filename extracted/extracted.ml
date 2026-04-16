module[@inline] Make (Parray : sig
  type 'a t
  val make    : Uint63.t -> 'a -> 'a t
  val length  : 'a t -> Uint63.t
  val get     : 'a t -> Uint63.t -> 'a
  val set     : 'a t -> Uint63.t -> 'a -> 'a t
(*
  val blit    : 'a t -> Uint63.t -> 'a t -> Uint63.t -> Uint63.t -> 'a t
    (* [blit] is not used by the code that we extract out of Rocq;
       this code contains its own [blit] function. Nevertheless we
       may provide [blit] in order to be able to plug it in and
       compare the performance of the two [blit] functions. *)
 *)
end) = struct

type 'a inhabited =
  'a
  (* singleton inductive, whose constructor was populate *)

(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val div : Uint63.t -> Uint63.t -> Uint63.t **)

let div = Uint63.div

(** val eqb : Uint63.t -> Uint63.t -> bool **)

let eqb = Uint63.equal

(** val ltb : Uint63.t -> Uint63.t -> bool **)

let ltb = Uint63.lt

(** val leb : Uint63.t -> Uint63.t -> bool **)

let leb = Uint63.le

(** val make : Uint63.t -> 'a1 -> 'a1 'a Parray.t **)

let make = Parray.make

(** val get : 'a1 'a Parray.t -> Uint63.t -> 'a1 **)

let get = Parray.get

(** val set : 'a1 'a Parray.t -> Uint63.t -> 'a1 -> 'a1 'a Parray.t **)

let set = Parray.set

(** val length : 'a1 'a Parray.t -> Uint63.t **)

let length = Parray.length

(** val simple_blit_aux :
    'a1 'a Parray.t -> Uint63.t -> 'a1 'a Parray.t -> Uint63.t ->
    Uint63.t -> 'a1 'a Parray.t **)

let rec simple_blit_aux a _i b _j _n =
  if eqb _n (Uint63.of_int (0))
  then b
  else simple_blit_aux a (add _i (Uint63.of_int (1)))
         (set b _j (get a _i)) (add _j (Uint63.of_int (1)))
         (sub _n (Uint63.of_int (1)))

(** val blit_aux :
    'a1 'a Parray.t -> Uint63.t -> 'a1 'a Parray.t -> Uint63.t ->
    Uint63.t -> 'a1 'a Parray.t **)

let rec blit_aux a _i b _j _n =
  if ltb _n (Uint63.of_int (8))
  then simple_blit_aux a _i b _j _n
  else blit_aux a (add _i (Uint63.of_int (8)))
         (set
           (set
             (set
               (set
                 (set
                   (set
                     (set
                       (set b (add _j (Uint63.of_int (0)))
                         (get a (add _i (Uint63.of_int (0)))))
                       (add _j (Uint63.of_int (1)))
                       (get a (add _i (Uint63.of_int (1)))))
                     (add _j (Uint63.of_int (2)))
                     (get a (add _i (Uint63.of_int (2)))))
                   (add _j (Uint63.of_int (3)))
                   (get a (add _i (Uint63.of_int (3)))))
                 (add _j (Uint63.of_int (4)))
                 (get a (add _i (Uint63.of_int (4)))))
               (add _j (Uint63.of_int (5)))
               (get a (add _i (Uint63.of_int (5)))))
             (add _j (Uint63.of_int (6)))
             (get a (add _i (Uint63.of_int (6)))))
           (add _j (Uint63.of_int (7)))
           (get a (add _i (Uint63.of_int (7)))))
         (add _j (Uint63.of_int (8))) (sub _n (Uint63.of_int (8)))

(** val blit :
    'a1 'a Parray.t -> Uint63.t -> 'a1 'a Parray.t -> Uint63.t ->
    Uint63.t -> 'a1 'a Parray.t **)

let blit =
  blit_aux

(** val simple_blit'_up_aux :
    'a1 'a Parray.t -> Uint63.t -> Uint63.t -> Uint63.t -> 'a1 'a Parray.t **)

let rec simple_blit'_up_aux a _i _j _n =
  if eqb _n (Uint63.of_int (0))
  then a
  else simple_blit'_up_aux (set a _j (get a _i))
         (add _i (Uint63.of_int (1))) (add _j (Uint63.of_int (1)))
         (sub _n (Uint63.of_int (1)))

(** val simple_blit'_down_aux :
    'a1 'a Parray.t -> Uint63.t -> Uint63.t -> Uint63.t -> 'a1 'a Parray.t **)

let rec simple_blit'_down_aux a _i _j _n =
  if eqb _n (Uint63.of_int (0))
  then a
  else simple_blit'_down_aux (set a _j (get a _i))
         (sub _i (Uint63.of_int (1))) (sub _j (Uint63.of_int (1)))
         (sub _n (Uint63.of_int (1)))

(** val blit'N_up :
    'a1 'a Parray.t -> Uint63.t -> Uint63.t -> 'a1 'a Parray.t **)

let blit'N_up a _i _j =
  let a0 =
    set a (add _j (Uint63.of_int (0)))
      (get a (add _i (Uint63.of_int (0))))
  in
  let a1 =
    set a0 (add _j (Uint63.of_int (1)))
      (get a0 (add _i (Uint63.of_int (1))))
  in
  let a2 =
    set a1 (add _j (Uint63.of_int (2)))
      (get a1 (add _i (Uint63.of_int (2))))
  in
  let a3 =
    set a2 (add _j (Uint63.of_int (3)))
      (get a2 (add _i (Uint63.of_int (3))))
  in
  let a4 =
    set a3 (add _j (Uint63.of_int (4)))
      (get a3 (add _i (Uint63.of_int (4))))
  in
  let a5 =
    set a4 (add _j (Uint63.of_int (5)))
      (get a4 (add _i (Uint63.of_int (5))))
  in
  let a6 =
    set a5 (add _j (Uint63.of_int (6)))
      (get a5 (add _i (Uint63.of_int (6))))
  in
  set a6 (add _j (Uint63.of_int (7)))
    (get a6 (add _i (Uint63.of_int (7))))

(** val blit'N_down :
    'a1 'a Parray.t -> Uint63.t -> Uint63.t -> 'a1 'a Parray.t **)

let blit'N_down a _i _j =
  let a0 =
    set a (add _j (Uint63.of_int (7)))
      (get a (add _i (Uint63.of_int (7))))
  in
  let a1 =
    set a0 (add _j (Uint63.of_int (6)))
      (get a0 (add _i (Uint63.of_int (6))))
  in
  let a2 =
    set a1 (add _j (Uint63.of_int (5)))
      (get a1 (add _i (Uint63.of_int (5))))
  in
  let a3 =
    set a2 (add _j (Uint63.of_int (4)))
      (get a2 (add _i (Uint63.of_int (4))))
  in
  let a4 =
    set a3 (add _j (Uint63.of_int (3)))
      (get a3 (add _i (Uint63.of_int (3))))
  in
  let a5 =
    set a4 (add _j (Uint63.of_int (2)))
      (get a4 (add _i (Uint63.of_int (2))))
  in
  let a6 =
    set a5 (add _j (Uint63.of_int (1)))
      (get a5 (add _i (Uint63.of_int (1))))
  in
  set a6 (add _j (Uint63.of_int (0)))
    (get a6 (add _i (Uint63.of_int (0))))

(** val blit'_up_aux :
    'a1 'a Parray.t -> Uint63.t -> Uint63.t -> Uint63.t -> 'a1 'a Parray.t **)

let rec blit'_up_aux a _i _j _n =
  if ltb _n (Uint63.of_int (8))
  then simple_blit'_up_aux a _i _j _n
  else blit'_up_aux (blit'N_up a _i _j) (add _i (Uint63.of_int (8)))
         (add _j (Uint63.of_int (8))) (sub _n (Uint63.of_int (8)))

(** val blit'_down_aux :
    'a1 'a Parray.t -> Uint63.t -> Uint63.t -> Uint63.t -> 'a1 'a Parray.t **)

let rec blit'_down_aux a _i _j _n =
  if ltb _n (Uint63.of_int (8))
  then simple_blit'_down_aux a (sub (add _i _n) (Uint63.of_int (1)))
         (sub (add _j _n) (Uint63.of_int (1))) _n
  else blit'_down_aux
         (blit'N_down a (sub (add _i _n) (Uint63.of_int (8)))
           (sub (add _j _n) (Uint63.of_int (8))))
         _i _j (sub _n (Uint63.of_int (8)))

(** val blit' :
    'a1 'a Parray.t -> Uint63.t -> Uint63.t -> Uint63.t -> 'a1 'a Parray.t **)

let blit' a _i _j _n =
  if eqb _j _i
  then a
  else if leb _j _i
       then blit'_up_aux a _i _j _n
       else blit'_down_aux a _i _j _n

type 'a leb0 =
  'a -> 'a -> bool
  (* singleton inductive, whose constructor was Build_Leb *)

(** val sortto_segment_3 :
    'a1 leb0 -> 'a1 'a Parray.t -> Uint63.t -> 'a1 'a Parray.t ->
    Uint63.t -> 'a1 'a Parray.t **)

let sortto_segment_3 h1 _src _i _dst _k =
  let x0 = get _src _i in
  let x1 = get _src (add _i (Uint63.of_int (1))) in
  let x2 = get _src (add _i (Uint63.of_int (2))) in
  if h1 x0 x1
  then if h1 x0 x2
       then if h1 x1 x2
            then set
                   (set (set _dst _k x0) (add _k (Uint63.of_int (1))) x1)
                   (add _k (Uint63.of_int (2))) x2
            else set
                   (set (set _dst _k x0) (add _k (Uint63.of_int (1))) x2)
                   (add _k (Uint63.of_int (2))) x1
       else set (set (set _dst _k x2) (add _k (Uint63.of_int (1))) x0)
              (add _k (Uint63.of_int (2))) x1
  else if h1 x1 x2
       then if h1 x0 x2
            then set
                   (set (set _dst _k x1) (add _k (Uint63.of_int (1))) x0)
                   (add _k (Uint63.of_int (2))) x2
            else set
                   (set (set _dst _k x1) (add _k (Uint63.of_int (1))) x2)
                   (add _k (Uint63.of_int (2))) x0
       else set (set (set _dst _k x2) (add _k (Uint63.of_int (1))) x1)
              (add _k (Uint63.of_int (2))) x0

(** val sortto_segment_4 :
    'a1 leb0 -> 'a1 'a Parray.t -> Uint63.t -> 'a1 'a Parray.t ->
    Uint63.t -> 'a1 'a Parray.t **)

let sortto_segment_4 h1 _src _i _dst _k =
  let x0 = get _src _i in
  let x1 = get _src (add _i (Uint63.of_int (1))) in
  let x2 = get _src (add _i (Uint63.of_int (2))) in
  let x3 = get _src (add _i (Uint63.of_int (3))) in
  if h1 x0 x1
  then if h1 x2 x3
       then if h1 x0 x2
            then if h1 x1 x2
                 then set
                        (set
                          (set (set _dst _k x0)
                            (add _k (Uint63.of_int (1))) x1)
                          (add _k (Uint63.of_int (2))) x2)
                        (add _k (Uint63.of_int (3))) x3
                 else if h1 x1 x3
                      then set
                             (set
                               (set (set _dst _k x0)
                                 (add _k (Uint63.of_int (1))) x2)
                               (add _k (Uint63.of_int (2))) x1)
                             (add _k (Uint63.of_int (3))) x3
                      else set
                             (set
                               (set (set _dst _k x0)
                                 (add _k (Uint63.of_int (1))) x2)
                               (add _k (Uint63.of_int (2))) x3)
                             (add _k (Uint63.of_int (3))) x1
            else if h1 x0 x3
                 then if h1 x1 x3
                      then set
                             (set
                               (set (set _dst _k x2)
                                 (add _k (Uint63.of_int (1))) x0)
                               (add _k (Uint63.of_int (2))) x1)
                             (add _k (Uint63.of_int (3))) x3
                      else set
                             (set
                               (set (set _dst _k x2)
                                 (add _k (Uint63.of_int (1))) x0)
                               (add _k (Uint63.of_int (2))) x3)
                             (add _k (Uint63.of_int (3))) x1
                 else set
                        (set
                          (set (set _dst _k x2)
                            (add _k (Uint63.of_int (1))) x3)
                          (add _k (Uint63.of_int (2))) x0)
                        (add _k (Uint63.of_int (3))) x1
       else if h1 x0 x3
            then if h1 x1 x3
                 then set
                        (set
                          (set (set _dst _k x0)
                            (add _k (Uint63.of_int (1))) x1)
                          (add _k (Uint63.of_int (2))) x3)
                        (add _k (Uint63.of_int (3))) x2
                 else if h1 x1 x2
                      then set
                             (set
                               (set (set _dst _k x0)
                                 (add _k (Uint63.of_int (1))) x3)
                               (add _k (Uint63.of_int (2))) x1)
                             (add _k (Uint63.of_int (3))) x2
                      else set
                             (set
                               (set (set _dst _k x0)
                                 (add _k (Uint63.of_int (1))) x3)
                               (add _k (Uint63.of_int (2))) x2)
                             (add _k (Uint63.of_int (3))) x1
            else if h1 x0 x2
                 then if h1 x1 x2
                      then set
                             (set
                               (set (set _dst _k x3)
                                 (add _k (Uint63.of_int (1))) x0)
                               (add _k (Uint63.of_int (2))) x1)
                             (add _k (Uint63.of_int (3))) x2
                      else set
                             (set
                               (set (set _dst _k x3)
                                 (add _k (Uint63.of_int (1))) x0)
                               (add _k (Uint63.of_int (2))) x2)
                             (add _k (Uint63.of_int (3))) x1
                 else set
                        (set
                          (set (set _dst _k x3)
                            (add _k (Uint63.of_int (1))) x2)
                          (add _k (Uint63.of_int (2))) x0)
                        (add _k (Uint63.of_int (3))) x1
  else if h1 x2 x3
       then if h1 x1 x2
            then if h1 x0 x2
                 then set
                        (set
                          (set (set _dst _k x1)
                            (add _k (Uint63.of_int (1))) x0)
                          (add _k (Uint63.of_int (2))) x2)
                        (add _k (Uint63.of_int (3))) x3
                 else if h1 x0 x3
                      then set
                             (set
                               (set (set _dst _k x1)
                                 (add _k (Uint63.of_int (1))) x2)
                               (add _k (Uint63.of_int (2))) x0)
                             (add _k (Uint63.of_int (3))) x3
                      else set
                             (set
                               (set (set _dst _k x1)
                                 (add _k (Uint63.of_int (1))) x2)
                               (add _k (Uint63.of_int (2))) x3)
                             (add _k (Uint63.of_int (3))) x0
            else if h1 x1 x3
                 then if h1 x0 x3
                      then set
                             (set
                               (set (set _dst _k x2)
                                 (add _k (Uint63.of_int (1))) x1)
                               (add _k (Uint63.of_int (2))) x0)
                             (add _k (Uint63.of_int (3))) x3
                      else set
                             (set
                               (set (set _dst _k x2)
                                 (add _k (Uint63.of_int (1))) x1)
                               (add _k (Uint63.of_int (2))) x3)
                             (add _k (Uint63.of_int (3))) x0
                 else set
                        (set
                          (set (set _dst _k x2)
                            (add _k (Uint63.of_int (1))) x3)
                          (add _k (Uint63.of_int (2))) x1)
                        (add _k (Uint63.of_int (3))) x0
       else if h1 x1 x3
            then if h1 x0 x3
                 then set
                        (set
                          (set (set _dst _k x1)
                            (add _k (Uint63.of_int (1))) x0)
                          (add _k (Uint63.of_int (2))) x3)
                        (add _k (Uint63.of_int (3))) x2
                 else if h1 x0 x2
                      then set
                             (set
                               (set (set _dst _k x1)
                                 (add _k (Uint63.of_int (1))) x3)
                               (add _k (Uint63.of_int (2))) x0)
                             (add _k (Uint63.of_int (3))) x2
                      else set
                             (set
                               (set (set _dst _k x1)
                                 (add _k (Uint63.of_int (1))) x3)
                               (add _k (Uint63.of_int (2))) x2)
                             (add _k (Uint63.of_int (3))) x0
            else if h1 x1 x2
                 then if h1 x0 x2
                      then set
                             (set
                               (set (set _dst _k x3)
                                 (add _k (Uint63.of_int (1))) x1)
                               (add _k (Uint63.of_int (2))) x0)
                             (add _k (Uint63.of_int (3))) x2
                      else set
                             (set
                               (set (set _dst _k x3)
                                 (add _k (Uint63.of_int (1))) x1)
                               (add _k (Uint63.of_int (2))) x2)
                             (add _k (Uint63.of_int (3))) x0
                 else set
                        (set
                          (set (set _dst _k x3)
                            (add _k (Uint63.of_int (1))) x2)
                          (add _k (Uint63.of_int (2))) x1)
                        (add _k (Uint63.of_int (3))) x0

(** val merge_aux_1 :
    'a1 leb0 -> 'a1 'a Parray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    'a1 -> Uint63.t -> 'a1 -> 'a1 'a Parray.t -> Uint63.t -> 'a1
    'a Parray.t **)

let rec merge_aux_1 h1 _src2 _j1 _j2 _i1 x1 _i2 x2 _dst _k =
  if h1 x1 x2
  then let _dst0 = set _dst _k x1 in
       let _i3 = add _i1 (Uint63.of_int (1)) in
       let _k0 = add _k (Uint63.of_int (1)) in
       if ltb _i3 _j1
       then merge_aux_1 h1 _src2 _j1 _j2 _i3 (get _dst0 _i3) _i2 x2 _dst0
              _k0
       else blit _src2 _i2 _dst0 _k0 (sub _j2 _i2)
  else let _i3 = add _i2 (Uint63.of_int (1)) in
       let _k0 = add _k (Uint63.of_int (1)) in
       if ltb _i3 _j2
       then merge_aux_1 h1 _src2 _j1 _j2 _i1 x1 _i3 (get _src2 _i3)
              (set _dst _k x2) _k0
       else set _dst _k x2

(** val merge_aux_2 :
    'a1 leb0 -> 'a1 'a Parray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    'a1 -> Uint63.t -> 'a1 -> 'a1 'a Parray.t -> Uint63.t -> 'a1
    'a Parray.t **)

let rec merge_aux_2 h1 _src1 _j1 _j2 _i1 x1 _i2 x2 _dst _k =
  if h1 x1 x2
  then let _i3 = add _i1 (Uint63.of_int (1)) in
       let _k0 = add _k (Uint63.of_int (1)) in
       if ltb _i3 _j1
       then merge_aux_2 h1 _src1 _j1 _j2 _i3 (get _src1 _i3) _i2 x2
              (set _dst _k x1) _k0
       else set _dst _k x1
  else let _dst0 = set _dst _k x2 in
       let _i3 = add _i2 (Uint63.of_int (1)) in
       let _k0 = add _k (Uint63.of_int (1)) in
       if ltb _i3 _j2
       then merge_aux_2 h1 _src1 _j1 _j2 _i1 x1 _i3 (get _dst0 _i3) _dst0
              _k0
       else blit _src1 _i1 _dst0 _k0 (sub _j1 _i1)

(** val merge_aux_12 :
    'a1 leb0 -> Uint63.t -> Uint63.t -> Uint63.t -> 'a1 -> Uint63.t ->
    'a1 -> 'a1 'a Parray.t -> Uint63.t -> 'a1 'a Parray.t **)

let rec merge_aux_12 h1 _j1 _j2 _i1 x1 _i2 x2 _dst _k =
  if h1 x1 x2
  then let _dst0 = set _dst _k x1 in
       let _i3 = add _i1 (Uint63.of_int (1)) in
       let _k0 = add _k (Uint63.of_int (1)) in
       if ltb _i3 _j1
       then merge_aux_12 h1 _j1 _j2 _i3 (get _dst0 _i3) _i2 x2 _dst0 _k0
       else _dst0
  else let _dst0 = set _dst _k x2 in
       let _i3 = add _i2 (Uint63.of_int (1)) in
       let _k0 = add _k (Uint63.of_int (1)) in
       if ltb _i3 _j2
       then merge_aux_12 h1 _j1 _j2 _i1 x1 _i3 (get _dst0 _i3) _dst0 _k0
       else blit' _dst0 _i1 _k0 (sub _j1 _i1)

(** val sortto' :
    'a1 leb0 -> 'a1 'a Parray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    'a1 'a Parray.t **)

let rec sortto' h1 _dst _i _k _n =
  if leb _n (Uint63.of_int (4))
  then if eqb _n (Uint63.of_int (4))
       then sortto_segment_4 h1 _dst _i _dst _k
       else if eqb _n (Uint63.of_int (3))
            then sortto_segment_3 h1 _dst _i _dst _k
            else let x0 = get _dst _i in
                 let x1 = get _dst (add _i (Uint63.of_int (1))) in
                 if h1 x0 x1
                 then set (set _dst _k x0) (add _k (Uint63.of_int (1))) x1
                 else set (set _dst _k x1) (add _k (Uint63.of_int (1))) x0
  else let _n1 = div _n (Uint63.of_int (2)) in
       let _n2 = sub _n _n1 in
       let _dm = add _k _n1 in
       let _sm = add _i _n2 in
       let _dst0 =
         sortto' h1 (sortto' h1 _dst (add _i _n1) _dm _n2) _i _sm _n1
       in
       let _j1 = add _sm _n1 in
       let x2 = get _dst0 _dm in
       if h1 (get _dst0 (sub _j1 (Uint63.of_int (1)))) x2
       then let _n3 = sub _j1 _sm in blit' _dst0 _sm _k _n3
       else merge_aux_12 h1 _j1 (add _dm _n2) _sm (get _dst0 _sm) _dm x2
              _dst0 _k

(** val sortto :
    'a1 leb0 -> 'a1 'a Parray.t -> 'a1 'a Parray.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> 'a1 'a Parray.t * 'a1 'a Parray.t **)

let rec sortto h1 _src _dst _i _k _n =
  if leb _n (Uint63.of_int (4))
  then if eqb _n (Uint63.of_int (4))
       then (_src, (sortto_segment_4 h1 _src _i _dst _k))
       else if eqb _n (Uint63.of_int (3))
            then (_src, (sortto_segment_3 h1 _src _i _dst _k))
            else (_src,
                   (let x0 = get _src _i in
                    let x1 = get _src (add _i (Uint63.of_int (1))) in
                    if h1 x0 x1
                    then set (set _dst _k x0)
                           (add _k (Uint63.of_int (1))) x1
                    else set (set _dst _k x1)
                           (add _k (Uint63.of_int (1))) x0))
  else let _n1 = div _n (Uint63.of_int (2)) in
       let _n2 = sub _n _n1 in
       let _dm = add _k _n1 in
       let (_src0, _dst0) = sortto h1 _src _dst (add _i _n1) _dm _n2 in
       let _sm = add _i _n2 in
       let _src1 = sortto' h1 _src0 _i _sm _n1 in
       (_src1,
       (let _j1 = add _sm _n1 in
        let x2 = get _dst0 _dm in
        if h1 (get _src1 (sub _j1 (Uint63.of_int (1)))) x2
        then let _n3 = sub _j1 _sm in blit _src1 _sm _dst0 _k _n3
        else merge_aux_2 h1 _src1 _j1 (add _dm _n2) _sm (get _src1 _sm)
               _dm x2 _dst0 _k))

(** val sort_seg_aux :
    'a1 inhabited -> 'a1 leb0 -> 'a1 'a Parray.t -> Uint63.t -> Uint63.t
    -> 'a1 'a Parray.t **)

let sort_seg_aux h h1 a _i _n =
  if leb _n (Uint63.of_int (4))
  then if eqb _n (Uint63.of_int (4))
       then sortto_segment_4 h1 a _i a _i
       else if eqb _n (Uint63.of_int (3))
            then sortto_segment_3 h1 a _i a _i
            else let x0 = get a _i in
                 let x1 = get a (add _i (Uint63.of_int (1))) in
                 if h1 x0 x1
                 then set (set a _i x0) (add _i (Uint63.of_int (1))) x1
                 else set (set a _i x1) (add _i (Uint63.of_int (1))) x0
  else let _n1 = div _n (Uint63.of_int (2)) in
       let _n2 = sub _n _n1 in
       let (a0, t) =
         sortto h1 a (make _n2 h) (add _i _n1) (Uint63.of_int (0)) _n2
       in
       let a1 = sortto' h1 a0 _i (add _i _n2) _n1 in
       let _i1 = add _i _n2 in
       let _j1 = add _i _n in
       let _i2 = (Uint63.of_int (0)) in
       let x2 = get t _i2 in
       if h1 (get a1 (sub _j1 (Uint63.of_int (1)))) x2
       then let _n3 = sub _j1 _i1 in
            let _n4 = sub _n2 _i2 in
            blit t _i2 (blit' a1 _i1 _i _n3) (add _i _n3) _n4
       else merge_aux_1 h1 t _j1 _n2 _i1 (get a1 _i1) _i2 x2 a1 _i

(** val sort_seg :
    'a1 inhabited -> 'a1 leb0 -> 'a1 'a Parray.t -> Uint63.t -> Uint63.t
    -> 'a1 'a Parray.t **)

let sort_seg h h1 a _i _n =
  if ltb _n (Uint63.of_int (2)) then a else sort_seg_aux h h1 a _i _n

(** val sort :
    'a1 inhabited -> 'a1 leb0 -> 'a1 'a Parray.t -> 'a1 'a Parray.t **)

let sort h h1 a =
  sort_seg h h1 a (Uint63.of_int (0)) (length a)

end (* Make *)
