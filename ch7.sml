(** 7.2 Real Time Queue **)

(* Exercise 7.1 *)
structure BankersQueue' : QUEUE =
struct
  type 'a Queue = int * 'a Stream * int * 'a Stream

  val empty = (0, $ NIL, 0, $ NIL)
  fun isEmpty (lenf, _, _, _) = (lenf = 0)

  fun rotate ($ NIL, $ CONS (y, _), a) = $ CONS (y, a)
    | rotate ($ CONS (x, xs), $ CONS (y, ys), a) =
    $ CONS (x, rotate (xs, ys, $ CONS (y, a)))

  fun check (q as (lenf, f, lenr, r)) =
    if lenr <= lenf then q else (lenf + lenr, rotate (f, r, $ NIL), 0, $ NIL)

  fun snoc ((lenf, f, lenr, r), x) = check (lenf, f, lenr + 1, $ CONS (x, r))

  fun head (lenf, $ NIL, lenr, r) = raise EMPTY
    | head (lenf, $ CONS (x, f), lenr, r) = x
  fun tail (lenf, $ NIL, lenr, r) = raise EMPTY
    | tail (lenf, $ CONS (x, f), lenr, r) = check (lenf - 1, f, lenr, r)

  (** One rotate enable to exist unless f is NIL. Then the lifetime of one
    * rotate is f's head to f's last, where f is the one when rotate is created.
    * Because f grows only back, lifetimes of existing rotate overlap on f's
    * front. In addition, rotates created later are located in front of f than
    * ones created earlier.
    * Given that k rotates exists in a lifetime m, the length n of queue is at
    * least,
    *   n = 2m + 2 * 2m + 2^2 * 2m + 2^(k - 1) * 2m
    *     = 2m * sum_(i=1)^(k){2^(i-1)}
    *     = 2m * (2^k - 1).
    * Given a lifetime m',
    *   n >= 2m' * (2^k - 1)
    *   log(n/2m' + 1) >= k.
    * Therefore, the length of rotate's chain is also at most O(log(n)).
    *
    * *)
end

structure RealTimeQueue : QUEUE =
struct
  type 'a Queue = 'a Stream * 'a list * 'a Stream

  val empty = ($ NIL, [], $ NIL)
  fun isEmpty ($ NIL, _, _) = true
    | isEmpty _ = false

  fun rotate ($ NIL, y::_, a) = $ CONS (y, a)
    | rotate ($ CONS (x, xs), y::ys, a) =
    $ CONS (x, rotate (xs, ys, $ CONS (y, a)))

  fun exec (f, r, $ CONS (x, s)) = (f, r, s)
    | exec (f, r, $ NIL) = let val f' = rotate (f, r, $ NIL) in (f', r, f') end

  fun snoc ((f, r, s), x) = exec (f, x::r, s)

  fun head ($ NIL, r, s) = raise EMPTY
    | head ($ CONS (x, f), r, s) = x
  fun tail ($ NIL, r, s) = raise EMPTY
    | tail ($ CONS (x, f), r, s) = exec (f, r, s)

  (* Exercise 7.2 *)
  fun size (f, r, s) =
    let
      fun len ($ NIL) = 0
        | len ($ CONS (x, xs)) = 1 + len xs
    in len s + 2 * length r end
  (** According to |s| = |f| - |r| => |f| = |s| + |r|, the length of queue is
    * |s| + 2|r|. Because |s| <= |f|, the step of this size may be less than
    * the one calculating |f| and |r| length. Because forcing suspension cost
    * is relatively high, this difference is large.
    *
    * *)
end

(** 7.3 Binomial Heap **)

(* Exercise 7.3 *)
(** Hypothesize there is at least three completed zero in front of first
  * schedule range, and there is at least two completed zero between neighbor
  * ranges in a schedule.
  *
  * Let r1 and r2 be the first two ranges in a schedule, and z1, z2, z3 be the
  * completed zeros in front of r1. Let z4 and z5 be the two completed zeros
  * between r1 and r2. r0 is the new range created by insert.
  *
  * If lazy is removed from insTree, suspension is forced three times.
  *
  * m=0 => If both r1 and r2 are removed, z2, z3, z4 are the three completed
  * zeros. If r1 is only removed, then z4, z5 and a zero switched in r2 are the
  * three completed zeros. If r1 is not removed, z2, z3, and a zero switch in r1
  * are the three completed zeros.
  * m=1 => If r1 is removed, a zero switched in r0, z2 and z3 are the three
  * completed zeros.
  * m=2 => Two zeros switched in r0 and z2 are the tree completed zeros.
  * m>=3 => Three zeros switch in r0 are the three completed zeros, and z2 and
  * z3 are the two completed zeros.
  *
  * *)

functor ScheduledBinomialHeap (Element : ORDERED) : HEAP =
struct
  structure Elem = Element

  datatype Tee = NODE of Elem.T * Tree list
  datatype Digit = ZERO | ONE of Tree
  type Schedule = Digit Stream list
  type Heap = Digit Stream * Schedule

  val emptn = ($ NIL, [])
  fun isEmpty ($ NIL, _) = true | isEmpty _ = false

  fun link (t1 as NODE (x1, c1), t2 as NODE (x2, c2)) =
    if Elem.leq (x1, x2) then NODE (x1, t2::c1) else NODE (x2, t1::c2)
  fun insTree (t, $ NIL) = $ CONS (ONE t, $ NIL)
    | insTree (t, $ CONS (ZERO, ds)) = $ CONS (ONE t, ds)
    | insTree (t, $ CONS (ONE t', ds)) =
    $ CONS (ZERO, insTree (link (t, t'), ds))
  fun mrg (ds1, $ NIL) = ds1
    | mrg ($ NIL, ds2) = ds2
    | mrg ($ CONS (ZERO, ds1), $ CONS (d, ds2)) = $ CONS (d, mrg (ds1, ds2))
    | mrg ($ CONS (d, ds1), $ CONS (ZERO, ds2)) = $ CONS (d, mrg (ds1, ds2))
    | mrg ($ CONS (ONE t1, ds1), $ CONS (ONE t2, ds2)) =
    $ CONS (ZERO, insTree (link (t1, t2), mrg (ds1, ds2)))

  fun normalize (ds as $ NIL) = ds
    | normalize (ds as $ CONS (_, ds')) = (normalize ds'; ds)
  fun exec [] = []
    | exec ($ CONS (ZERO, job)::sched) = job::sched
    | exec (_::sched) = sched

  fun insert (x, (ds, sched)) =
    let val ds' = insTree (NODE (x, []), ds)
    in (ds', exec (exec (ds'::sched))) end
  fun merge ((ds1, _), (ds2, _)) =
    let val ds = normalize (mrg (ds1, ds2)) in (ds, []) end

  fun removeMinTree ($ NIL) = raise EMPTY
    | removeMinTree ($ CONS (ONE t, $ NIL)) = (t, $ NIL)
    | removeMinTree ($ CONS (ZERO, ds)) =
    let val (t', ds') = removeMinTree ds in (t', $ CONS (ZERO, ds')) end
    | removeMinTree ($ CONS (ONE (t as NODE (x, _)), ds)) =
    case removeMinTree ds of
         (t' as NODE (x', _), ds') =>
         if Elem.leq (x, x') then (t, $ CONS (ZERO, ds'))
         else (t', $ CONS (ONE t, ds'))
  fun findMin (ds, _) =
    let val (NODE (x, _), _) = removeMinTree ds in x end
  fun deleteMin (ds, _) =
    let
      val (NODE (x, c), ds') = removeMinTree ds
      val ds'' = mrg (listToHeap (map ONE (rev c)), ds')
    in (normalize ds'', []) end

  (* Exercise 7.4 *)
  fun mrgWithList ([], ds) = ds
    (* It is guaranteed that list length is always less than or equal to
      * stream length *)
    | mrgWithList (t::ts, $ CONS (ZERO, ds)) =
    $ CONS (ONE t, mrgWithList (ts, ds))
    | mrgWithList (t::ts, $ CONS (ONE t', ds)) =
    $ CONS (ZERO, insTree (link (t, t'), mrgWithList (ts, ds)))
end

(** 7.4 Bottom Up Merge Sort With Sharing **)

functor ScheduledBottomUpMergeSort (Element : ORDERED) : HEAP =
struct
  structure Elem = Element

  type Schedule = Elem.T Stream list
  type Sortable = int * (Elem.T Stream * Schedule) list

  fun lazy mrg ($ NIL, ys) = ys
         | mrg (xs, $ NIL) = xs
         | mrg (xs as $ CONS (x, xs'), ys as $ CONS (y, ys')) =
         if Elem.leq (x, y) then $ CONS (x, mrg (xs', ys))
         else $ CONS (y, mrg (xs, ys'))

  fun exec1 [] = []
    | exec1 (($ NIL)::sched) = exec1 sched
    | exec1 (($ CONS (x, xs))::sched) = xs::sched
  fun exec2 (xs, sched) = (xs, exec1 (exec1 sched))

  val empty = (0, [])
  fun add (x, (size, segs)) =
    let
      fun addSeg (xs, segs, size, rsched) =
        if size mod 2 = 0 then (xs, rev rsched)::segs
        else
          let
            val ((xs', [])::segs') = segs
            val xs'' = mrg (xs, xs')
          in addSeg (xs'', segs', size div 2, xs''::rsched) end
      val segs' = addSeg ($ CONS (x, $ NIL), segs, size, [])
    in (size + 1, map exec2 segs) end
  fun sort (size, segs) =
    let
      fun mrgAll (xs, []) = xs
        | mrgAll (xs, (xs', _)::segs) = mrgAll (mrg (xs, xs'), segs)
    in streamToList (mrgAll ($ NIL, segs)) end
end

