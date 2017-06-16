(** 5.2 Queue **)
signature QUEUE =
sig
  type 'a Queue

  val empty : 'a Queue
  val isEmpty : 'a Queue -> bool

  val snoc : 'a Queue * 'a -> 'a Queue
  val head : 'a Queue -> 'a
  val tail : 'a Queue -> 'q Queue
end

structure BatchedQueue : QUEUE =
struct
  type 'a Queue = 'a list * 'a list

  val empty = ([], [])
  val isEmpty (f, r) = null f

  fun checkf ([], r) = (rev r, [])
    | checkf q = q

  fun snoc ((f, r), x) = checkf (f, x::r)

  fun head ([], _) = raise EMPTY
    | head (x::f, r) = x
  fun tail ([], _) = raise EMPTY
    | tail (x::f, r) = checkf (f, r)
end

signature DEQUE =
sig
  type 'a Queue

  val empty : 'a Queue
  val isEmpty : 'a Queue -> bool

  val cons : 'a * 'a Queue -> 'a Queue
  val head : 'a Queue -> 'a
  val tail : 'a Queue -> 'a Queue

  val snoc : 'a Queue * 'a -> 'a Queue
  val last : 'a Queue -> 'a
  val init : 'a Queue -> 'a Queue
end

(* Exercise 5.1 *)
structure Deque : DEQUE =
struct
  type 'a Queue = 'a list * 'a list

  val empty = ([], [])
  val isEmpty ([], []) = true | isEmpty _ = false

  fun checkf ([], xs) =
    let
      fun split (n, []) = (n, [], [])
      fun split (n, x::xs) =
        let
          val (len, f, r) = split (n + 1, xs)
        in
          if n <= len / 2 then (len, f, x::r) else (len, x::f, r)
        end
      val (_, f, r) = split (0, xs)
    in (rev f, r) end
    | checkf q = q
  fun checkr (f, r) = let val (r', f') = checkf (r, f) in (f', r') end

  fun cons (x, (f, r)) = checkr (x::f, r)
  fun head ([], []) = raise EMPTY
    | head ([], x::[]) = x
    | head (x::f, r) = x
  fun tail ([], []) = raise EMPTY
    | tail ([], x::[]) = empty
    | tail (x::f, r) = checkf (f, r)

  fun snoc ((f, r), x) = checkf (f, x::r)
  fun last ([], []) = raise EMPTY
    | last (x::[], []) = x
    | last (f, x::r) = x
  fun init ([], []) = raise EMPTY
    | init (x::[], []) = empty
    | init (f, x::r) = checkr (f, r)
end
(** When |f| = 1 and |r| = 0, cons decrements potential by 1 and needs 2 steps.
  * The amortized cost is 1.
  * Otherwise, When  |f| >= |r|, cons increments potential by 1, then the
  * amortized cost is 2.
  * When  |f| < |r|, cons decrements potential by 1, then the amortized cost
  * is 0.
  *
  * When |f| = 0 and |r| = 1, or |f| = 1 and |r| = 0, or |f| > |r| > 1, tail
  * decrements potential by 1, then the amortized cost is 0.
  * When |r| >= |f| > 1, tail increments potential by 1, then the amortized
  * cost is 2.
  * When |r| >= 1 and |f| = 1, the potential before tail is |r| - 1 and the
  * after tail is 0 (when |r| is even) or 1, so the tail decrements potential
  * by at least |r| - 1. The tail needs 1 + |r| steps, then the amortized cost
  * is (1 + |r|) - (|r| - 1) = 2.
  *
  * snoc and init cost is same as cons and tail respectively.
  * *)

(** 5.3 Binomial Heap **)

(* Exercise 5.2 *)
(** Each tree in a heap is related to a credit. Let k the number of link,
  * insert decrements credit by k and increments that by 1. Then the amortized
  * cost of insert is 1 + k + 1 - k = 2.
  * *)

