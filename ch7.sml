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

