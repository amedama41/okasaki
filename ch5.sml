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
(** Each tree in a heap is related to a credit. Let k be the number of link,
  * insert decrements credit by k and increments that by 1. Then the amortized
  * cost of insert is 1 + k + 1 - k = 2.
  * *)

(* Exercise 5.3 *)
(** Let t1 be the number of trees in one heap to be merged, t2 the number of
  * trees in another, and k the number of calls of link in the merge.
  * The total potential of two heaps is t1 + t2, and the potential of merged
  * heap is t1 + t2 - k.
  * The amortized cost is log(n) + k + (t1 + t2 - k) - (t1 + t2) = log(n).
  *
  * Let t be the number of trees in a heap, r be the rank of tree with minimum
  * value, and k be the number of calls of link in the deleteMin.
  * The potential after deleteMin is (t - 1 + r - k), and in deleteMin findMin
  * needs t steps and merge needs r + k steps.
  * Then the amortized cost is
  *     t + r + k + (t - 1 + r - k) - t = t + 2r = log(n) + 2r.
  * Because 0 <= r <= log(n + 1), the amortized cost of deleteMin is O(log(n)).
  * *)

(** 5.4 Splay Tree **)

functor SplayHeap (Element : ORDERED) : HEAP =
struct
  structure Elem = Element

  datatype Heap = E | T of Heap * Elem.T * Heap

  val empty = E
  fun isEmpty E = true | isEmpty _ = false

  fun partition (pivot, E) = (E, E)
    | partition (pivot, T (a, x, b)) =
    if x <= pivot then
      case b of
           E => (T (a, x, E), E)
         | T (b1, y, b2) =>
             if y <= pivot then
               let val (small, big) = partition (pivot, b2)
               in (T (T (a, x, b1), y, small), big) end
             else
               let val (samll, big) = partition (pivot, b1)
               in (T (a, x, small), T (big, y, b2)) end
    else
      case a of
           E => (E, T (E, x, b))
         | T (a1, y, a2) =>
             if y <= pivot then
               let val (small, big) = partition (pivot, a2)
               in (T (a1, y, small), T (big, x, b)) end
             else
               let val (small, big) = partition (pivot, a1)
               in (small, T (big, y, T (a2, x, b))) end

  fun insert (x, t) = let val (a, b) = partition (x, t) in T (a, x, b) end
  fun merge (E, t) = t
    | merge (T (a, x, b), t) =
    let val (ta, tb) = partition (x, t)
    in T (merge (ta, a), x, merge (tb, b)) end

  fun findMin E = raise EMPTY
    | findMin (T (E, x, b)) = x
    | findMin (T (a, x, b)) = findMin a
  fun deleteMin E = raise EMPTY
    | deleteMin (T (E, x, b)) = b
    | deleteMin (T (T (E, x, b), y, c)) = T (b, y, c)
    | deleteMin (T (T (a, x, b), y, c)) = T (deleteMin a, x, T (b, y, c))

  fun bigger (pivot, E) = E
    | bigger (pivot, T (a, x, b)) =
    if x <= pivot then bigger (pivot, b)
    else case a of
              E => T (E, x, b)
            | T (a1, y, a2) =>
                if y <= pivot then T (bigger (pivot, a2), x, b)
                else T (bigger (pivot, a1), y, T (a2, x, b))

(* Exercise 5.4 *)
  fun smaller (pivot, E) = E
    | smaller (pivot, T (a, x, b)) =
    if x > pivot then smaller (pivot, a)
    else case b of
              E => T (a, x, E)
            | T (a1, y, a2) =>
                if y > pivot then T (a, x, smaller (pivot, a1))
                else T (T (a, x, a1), y, smaller (pivot, a2))

end

(* Exercise 5.5 *)
(** T (T (c, t, u), s, d) => (T (c, t', a), T (b, s', d)) (u => (a, b))
  *
  * Α(s)
  *     = Γ(s) + Φ(s') + Φ(t') + Φ(s') - Φ(s)
  *     = 1 + Γ(u) + Φ(s') + Φ(t') + Φ(s') - Φ(s)
  *     = 1 + Α(u) - Φ(a) - Φ(b) + Φ(u) + Φ(s') + Φ(t') + Φ(s') - Φ(s)
  *     = 1 + Α(u) - Φ(a) - Φ(b) + Φ(u)
  *         + φ(s') + Φ(b) + Φ(d)
  *         + φ(t') + Φ(c) + Φ(a)
  *         - (φ(s) + φ(t) + Φ(c) + Φ(u) + Φ(d))
  *     = 1 + Α(u) + φ(s') - φ(s) + φ(t') - φ(t)
  *     <= 2 + 2φ(u) + φ(s') - φ(s) + φ(t') - φ(t)
  *     < 2 + φ(s') + φ(t')       (φ(s) > φ(u), φ(t) > φ(u))
  *     < 1 + 2φ(s)
  * *)

(* Exercise 5.6 *)
(** Let Α(t) be amortized cost of deleteMin, Γ(t) be real cost of deleteMin.
  * Hypothesize Α(t) <= 1 + 2φ(t) = 1 + 2log(#t).
  *
  * Where deleteMin T (T (u, t, c), s, d) results in  T (u', t', T (c, s', d)),
  * Α(s)
  *     = Γ(s) + Φ(t') - Φ(s)
  *     = 1 + Γ(u) + Φ(t') - Φ(s)
  *     = 1 + Α(u) - Φ(u') + Φ(u) + Φ(t') - Φ(s)
  *     = 1 + Α(u) - Φ(u') + Φ(u)
  *         + φ(t') + Φ(u') + φ(s') + Φ(c) + Φ(d)
  *         - (φ(s) + φ(t) + Φ(u) + Φ(c) + Φ(d))
  *     = 1 + Α(u) + φ(t') - φ(t) + φ(s') - φ(s)
  *     <= 2 + 2φ(u) + φ(s') - φ(s) + φ(t') - φ(t)
  *     < 2 + φ(s') + φ(t')       (φ(s) > φ(u), φ(t) > φ(u))
  *     < 1 + 2φ(s) = 1 + 2log(#t).
  * *)

(* Exercise 5.7 *)
fun sort xs =
let
  fun listToHeap (h, []) = h
    | listToHeap (h, x::xs) = listToHeap (SplayHeap.insert (x, h), xs)
  fun heapToList (xs, E) = xs
    | heapToList (xs, T (a, x, b)) = heapToList (x::heapToList (xs, a), b)
in heapToList listToHeap xs end
(** If xs is sorted by ascending order, the heap after fist insert is
  * T (E, x1, E). After second, that is T (T (E, x1, E), x2, E).
  * Because xs is sorted by ascending, x <= pivot is always true and b is E.
  * Then following insert returns E as bigger tree.
  * Therefore, the cost of each insert is constant, so the cost of listToHeap
  * for sorted list is O(n).
  * heapToList is called only one time on each node in heap, so the cost of
  * heapToList is O(n).
  * *)

(** 5.5 Pairing Heap **)

functor PairingHeap (Element : ORDERED) : HEAP =
struct
  structure Elem = Element

  datatype Heap = E | T of Elem.T * Heap list

  val empty = E
  fun isEmpty E = true | isEmpty _ = false

  fun merge (h, E) = h
    | merge (E, h) = h
    | merge (h1 as T (x, hs1), h2 as T (y, hs2)) =
    if Elem.leq (x, y) then T (x, h2::hs1) else T (y, h1::hs2)
  fun insert (x, h) = merge (T (x, []), h)

  fun mergePairs [] = E
    | mergePairs [h] = h
    | mergePairs (h1::h2::hs) = merge (merge (h1, h2), mergePairs hs)

  fun findMin E = raise EMPTY
    | findMin (T (x, hs)) = x
  fun deleteMin E = raise EMPTY
    | deleteMin (T (x, hs)) = mergePairs hs

(* Exercise 5.8 *)
  datatype BinTree = E' | T' of Elem.T * BinTree * BinTree

  fun toBinary E = E'
    | toBinary h =
    let
      fun aux (T (x, []), []) = T' (x, E', E')
        | aux (T (x, []), h2::hs2) = T' (x, E', aux (h2, hs2))
        | aux (T (x, h1::hs1), []) = T' (x, aux (h1, hs2), E')
        | aux (T (x, h1::hs1), h2::hs2) = T' (x, aux (h1, hs1), aux (h2, hs2))
    in aux (h, []) end

  fun merge' (h, E') = h
    | merge' (E', h) = h
    | merge' (T' (x, a1, E'), T' (y, a2, E')) =
    if Elem.leq (x, y) then T' (x, T' (y, a2, a1), E')
    else T' (y, T' (x, a1, a2), E')
  fun insert' (x, h) = merge' (T' (x, E', E'), h)

  fun mergePairs' E' = E'
    | mergePairs' (t as T' (x, a, E')) = t
    | mergePairs' (T' (x, a, T' (y, b, c))) =
    merge' (merge' (T' (x, a, E'), T' (y, b, E')), mergePairs' c)

  fun findMin' E' = raise EMPTY
    | findMin' (T' (x, a, E')) = x
  fun deleteMin' E' = raise EMPTY
    | deleteMin' (T' (x, a, E')) = mergePairs a

(** merge': T' (x, a, E'), T' (y, b, E') => T' (x', T' (y', b, a), E')
  *     Α(x, y) = 1 + Φ(x') - Φ(x) - Φ(y)
  *              = 1 + φ(x') + φ(y') + Φ(a) + Φ(b)
  *                 - φ(x) - Φ(a) - φ(y) - Φ(b)
  *              = 1 + φ(x') + φ(y') - φ(x) - φ(y)
  *              = 1 + log(n1 + n2 + 1) + log(n1 + n2 - 1 + 1)
  *                 - log(n1 + 1) - log(n2 + 1)
  *              = 1 + log(n1 + n2 + 1) + log(n1 + n2)
  *                 - log((n1 + 1) * (n2 + 1))
  *              = 1 + log(n1 + n2 + 1) + log(n1 + n2) - log(nm + n1 + n2 + 1)
  *              < 1 + log(n1 + n2) = 1 + log(n)
  *
  * mergePairs': T' (s, a, T' (t, b, u))
  *         => T' (s', T' (u', v, T' (t', a, b)), E')
  *     Hypothesize Α(s) <= 3φ(s)
  *     Α(s)
  *         = Γ(s) + Φ(s') - Φ(s)
  *         = 1 + Γ(u) + Φ(s') - Φ(s)        (Γ(s) = 2 + Γ(u))
  *         = 1 + Α(u) - Φ(u'') + Φ(u) + Φ(s') - Φ(s)
  *         = 1 + Α(u) - (φ(u) + Φ(v)) + Φ(u) + Φ(s') - Φ(s)
  *         = 1 + Α(u) - (φ(u) + Φ(v)) + Φ(u)
  *             + (φ(s') + φ(t') + Φ(a) + Φ(b) + φ(u') + Φ(v))
  *             - (φ(s) + φ(t) + Φ(a) + Φ(b) + Φ(u))
  *         = 1 + Α(u) - φ(u) + φ(u') + φ(s') - φ(s) + φ(t') - φ(t)
  *         = 1 + Α(u) - φ(u) + φ(u') + φ(t') - φ(t)
  *                                             (φ(s') = φ(s) = log(n))
  *         = 1 + 3φ(u) - φ(u) + φ(u') + φ(t') - φ(t)  (Hypothesis)
  *         = 1 + 2φ(u) + φ(u') + φ(t') - φ(t)
  *         <= 1 + φ(u) + φ(u') + φ(t')
  *         <= 2φ(s) + φ(u')                  (#u + #t' <= #s)
  *         < 3φ(s) = 3log(#s)                 (#u < #s)
  *
  * The amortized cost of deleteMin is
  *     Α(h)
  *         = 1 + Γ_(mergePairs)(s) + Φ(s') - Φ(s) - φ(h)
  *         = 1 + 3log(#s) - φ(h)
  *         <= 1 + 2log(n)
  * *)
end

