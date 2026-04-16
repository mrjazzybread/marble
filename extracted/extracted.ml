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

(** val iter_down_aux :
    Uint63.t -> Uint63.t -> 'a1 -> (Uint63.t -> 'a1 -> 'a1) -> 'a1 **)

let rec iter_down_aux _i _k s body =
  if eqb _k _i
  then body _k s
  else iter_down_aux _i (sub _k (Uint63.of_int (1))) (body _k s) body

(** val iter_up_aux :
    Uint63.t -> Uint63.t -> 'a1 -> (Uint63.t -> 'a1 -> 'a1) -> 'a1 **)

let rec iter_up_aux _i _k s body =
  if ltb _i _k
  then iter_up_aux (add _i (Uint63.of_int (1))) _k (body _i s) body
  else s

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

(** val simple_blit :
    'a1 'a Parray.t -> Uint63.t -> 'a1 'a Parray.t -> Uint63.t ->
    Uint63.t -> 'a1 'a Parray.t **)

let simple_blit =
  simple_blit_aux

(** val equations_blit :
    'a1 'a Parray.t -> Uint63.t -> 'a1 'a Parray.t -> Uint63.t ->
    Uint63.t -> 'a1 'a Parray.t **)

let equations_blit a a0 a1 a2 b =
  let rec fix_F x =
    let a3 = let pr1,_ = x in pr1 in
    let _i = let pr1,_ = let _,pr2 = x in pr2 in pr1 in
    let _j =
      let pr1,_ =
        let _,pr2 = let _,pr2 = let _,pr2 = x in pr2 in pr2 in pr2
      in
      pr1
    in
    let _n =
      let _,pr2 =
        let _,pr2 = let _,pr2 = let _,pr2 = x in pr2 in pr2 in pr2
      in
      pr2
    in
    if eqb _n (Uint63.of_int (0))
    then let pr1,_ = let _,pr2 = let _,pr2 = x in pr2 in pr2 in pr1
    else let y =
           a3,((add _i (Uint63.of_int (1))),((set
                                               (let pr1,_ =
                                                  let _,pr2 =
                                                    let _,pr2 = x in pr2
                                                  in
                                                  pr2
                                                in
                                                pr1)
                                               _j (get a3 _i)),((add _j
                                                                (Uint63.of_int (1))),
           (sub _n (Uint63.of_int (1))))))
         in
         fix_F y
  in fix_F (a,(a0,(a1,(a2,b))))

(** val ni : Uint63.t **)

let ni =
  (Uint63.of_int (8))

(** val blitN :
    'a1 'a Parray.t -> Uint63.t -> 'a1 'a Parray.t -> Uint63.t -> 'a1
    'a Parray.t **)

let blitN a _i b _j =
  set
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
        (add _j (Uint63.of_int (5))) (get a (add _i (Uint63.of_int (5)))))
      (add _j (Uint63.of_int (6))) (get a (add _i (Uint63.of_int (6)))))
    (add _j (Uint63.of_int (7))) (get a (add _i (Uint63.of_int (7))))

(** val blit_underN :
    'a1 'a Parray.t -> Uint63.t -> 'a1 'a Parray.t -> Uint63.t ->
    Uint63.t -> 'a1 'a Parray.t **)

let blit_underN a _i b _j _n =
  if ltb _n (Uint63.of_int (4))
  then if ltb _n (Uint63.of_int (2))
       then if ltb _n (Uint63.of_int (1))
            then b
            else set b (add _j (Uint63.of_int (0)))
                   (get a (add _i (Uint63.of_int (0))))
       else if ltb _n (Uint63.of_int (3))
            then set
                   (set b (add _j (Uint63.of_int (0)))
                     (get a (add _i (Uint63.of_int (0)))))
                   (add _j (Uint63.of_int (1)))
                   (get a (add _i (Uint63.of_int (1))))
            else set
                   (set
                     (set b (add _j (Uint63.of_int (0)))
                       (get a (add _i (Uint63.of_int (0)))))
                     (add _j (Uint63.of_int (1)))
                     (get a (add _i (Uint63.of_int (1)))))
                   (add _j (Uint63.of_int (2)))
                   (get a (add _i (Uint63.of_int (2))))
  else if ltb _n (Uint63.of_int (6))
       then if ltb _n (Uint63.of_int (5))
            then set
                   (set
                     (set
                       (set b (add _j (Uint63.of_int (0)))
                         (get a (add _i (Uint63.of_int (0)))))
                       (add _j (Uint63.of_int (1)))
                       (get a (add _i (Uint63.of_int (1)))))
                     (add _j (Uint63.of_int (2)))
                     (get a (add _i (Uint63.of_int (2)))))
                   (add _j (Uint63.of_int (3)))
                   (get a (add _i (Uint63.of_int (3))))
            else set
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
                   (get a (add _i (Uint63.of_int (4))))
       else if ltb _n (Uint63.of_int (7))
            then set
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
                   (get a (add _i (Uint63.of_int (5))))
            else set
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
                   (get a (add _i (Uint63.of_int (6))))

(** val blit_aux :
    'a1 'a Parray.t -> Uint63.t -> 'a1 'a Parray.t -> Uint63.t ->
    Uint63.t -> 'a1 'a Parray.t **)

let rec blit_aux a _i b _j _n =
  if ltb _n ni
  then blit_underN a _i b _j _n
  else blit_aux a (add _i ni) (blitN a _i b _j) (add _j ni) (sub _n ni)

(** val blit :
    'a1 'a Parray.t -> Uint63.t -> 'a1 'a Parray.t -> Uint63.t ->
    Uint63.t -> 'a1 'a Parray.t **)

let blit =
  blit_aux

(** val blit' :
    'a1 'a Parray.t -> Uint63.t -> Uint63.t -> Uint63.t -> 'a1 'a Parray.t **)

let blit' a _i _j _n =
  if eqb _j _i
  then a
  else if leb _j _i
       then iter_up_aux _i (add _i _n) a (fun _k a0 ->
              set a0 (add _k (sub _j _i)) (get a0 _k))
       else let _k = add _i _n in
            if leb _k _i
            then a
            else iter_down_aux _i (sub _k (Uint63.of_int (1))) a
                   (fun _k0 a0 ->
                   set a0 (add _k0 (sub _j _i)) (get a0 _k0))

type 'a leb0 =
  'a -> 'a -> bool
  (* singleton inductive, whose constructor was Build_Leb *)

(** val sortto_segment_2 :
    'a1 leb0 -> 'a1 'a Parray.t -> Uint63.t -> 'a1 'a Parray.t ->
    Uint63.t -> 'a1 'a Parray.t **)

let sortto_segment_2 h1 _src _i _dst _k =
  let x0 = get _src _i in
  let x1 = get _src (add _i (Uint63.of_int (1))) in
  if h1 x0 x1
  then set (set _dst _k x0) (add _k (Uint63.of_int (1))) x1
  else set (set _dst _k x1) (add _k (Uint63.of_int (1))) x0

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

(** val optimistic_merge_1 :
    'a1 leb0 -> Uint63.t -> Uint63.t -> 'a1 'a Parray.t -> Uint63.t ->
    Uint63.t -> 'a1 'a Parray.t -> Uint63.t -> 'a1 'a Parray.t **)

let optimistic_merge_1 h1 _i1 _j1 _src2 _i2 _j2 _dst _k =
  let x2 = get _src2 _i2 in
  if h1 (get _dst (sub _j1 (Uint63.of_int (1)))) x2
  then let _n1 = sub _j1 _i1 in
       let _n2 = sub _j2 _i2 in
       blit _src2 _i2 (blit' _dst _i1 _k _n1) (add _k _n1) _n2
  else merge_aux_1 h1 _src2 _j1 _j2 _i1 (get _dst _i1) _i2 x2 _dst _k

(** val optimistic_merge_2 :
    'a1 leb0 -> 'a1 'a Parray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> 'a1 'a Parray.t -> Uint63.t -> 'a1 'a Parray.t **)

let optimistic_merge_2 h1 _src1 _i1 _j1 _i2 _j2 _dst _k =
  let x2 = get _dst _i2 in
  if h1 (get _src1 (sub _j1 (Uint63.of_int (1)))) x2
  then let _n1 = sub _j1 _i1 in blit _src1 _i1 _dst _k _n1
  else merge_aux_2 h1 _src1 _j1 _j2 _i1 (get _src1 _i1) _i2 x2 _dst _k

(** val optimistic_merge_12 :
    'a1 leb0 -> 'a1 'a Parray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> 'a1 'a Parray.t **)

let optimistic_merge_12 h1 _dst _i1 _j1 _i2 _j2 _k =
  let x2 = get _dst _i2 in
  if h1 (get _dst (sub _j1 (Uint63.of_int (1)))) x2
  then let _n1 = sub _j1 _i1 in blit' _dst _i1 _k _n1
  else merge_aux_12 h1 _j1 _j2 _i1 (get _dst _i1) _i2 x2 _dst _k

(** val sortto' :
    'a1 leb0 -> 'a1 'a Parray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    'a1 'a Parray.t **)

let rec sortto' h1 _dst _i _k _n =
  if leb _n (Uint63.of_int (4))
  then if eqb _n (Uint63.of_int (4))
       then sortto_segment_4 h1 _dst _i _dst _k
       else if eqb _n (Uint63.of_int (3))
            then sortto_segment_3 h1 _dst _i _dst _k
            else sortto_segment_2 h1 _dst _i _dst _k
  else let _n1 = div _n (Uint63.of_int (2)) in
       let _n2 = sub _n _n1 in
       let _dm = add _k _n1 in
       let _sm = add _i _n2 in
       optimistic_merge_12 h1
         (sortto' h1 (sortto' h1 _dst (add _i _n1) _dm _n2) _i _sm _n1)
         _sm (add _sm _n1) _dm (add _dm _n2) _k

(** val sortto :
    'a1 leb0 -> 'a1 'a Parray.t -> 'a1 'a Parray.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> 'a1 'a Parray.t * 'a1 'a Parray.t **)

let rec sortto h1 _src _dst _i _k _n =
  if leb _n (Uint63.of_int (4))
  then if eqb _n (Uint63.of_int (4))
       then (_src, (sortto_segment_4 h1 _src _i _dst _k))
       else if eqb _n (Uint63.of_int (3))
            then (_src, (sortto_segment_3 h1 _src _i _dst _k))
            else (_src, (sortto_segment_2 h1 _src _i _dst _k))
  else let _n1 = div _n (Uint63.of_int (2)) in
       let _n2 = sub _n _n1 in
       let _dm = add _k _n1 in
       let (_src0, _dst0) = sortto h1 _src _dst (add _i _n1) _dm _n2 in
       let _sm = add _i _n2 in
       let _src1 = sortto' h1 _src0 _i _sm _n1 in
       (_src1,
       (optimistic_merge_2 h1 _src1 _sm (add _sm _n1) _dm (add _dm _n2)
         _dst0 _k))

(** val sort_seg_aux :
    'a1 inhabited -> 'a1 leb0 -> 'a1 'a Parray.t -> Uint63.t -> Uint63.t
    -> 'a1 'a Parray.t **)

let sort_seg_aux h h1 a _i _n =
  if leb _n (Uint63.of_int (4))
  then if eqb _n (Uint63.of_int (4))
       then sortto_segment_4 h1 a _i a _i
       else if eqb _n (Uint63.of_int (3))
            then sortto_segment_3 h1 a _i a _i
            else sortto_segment_2 h1 a _i a _i
  else let _n1 = div _n (Uint63.of_int (2)) in
       let _n2 = sub _n _n1 in
       let (a0, t) =
         sortto h1 a (make _n2 h) (add _i _n1) (Uint63.of_int (0)) _n2
       in
       optimistic_merge_1 h1 (add _i _n2) (add _i _n) t
         (Uint63.of_int (0)) _n2 (sortto' h1 a0 _i (add _i _n2) _n1) _i

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
