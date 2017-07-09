(** 6.1 Execution Traces and Logical Time **)

(* Exercise 6.1 *)
(** snoc (empty, 0)
  *  |  4
  *  V
  * snoc (a, 1) -> snoc (b, 2) -> snoc (d, 3)
  *  |  4           |  2              1
  *  V              V
  * tail b ------> c ++ d
  *  |  2           1
  *  V
  * tail c
  *     1
  *
  * *)

(** 6.3 Banker's Method **)

structure BankersQueue : QUEUE =
struct
  type 'a Queue = int * 'a Stream * int * 'a Stream

  val empty = (0, $ NIL, 0, $ NIL)
  fun isEmpty (lenf, _, _, _) = (lenf = 0)

  fun check (q as (lenf, f, lenr, r)) =
    if lenr <= lenf then q else (lenf + lenr, f ++ reverse r, 0, $ NIL)

  fun snoc ((lenf, f, lenr, r), x) = check (lenf, f, lenr + 1, $ CONS (x, r))

  fun head (lenf, $ NIL, lenr, r) = raise EMPTY
    | head (lenf, $ CONS (x, f), lenr, r) = x
  fun tail (lenf, $ NIL, lenr, r) = raise EMPTY
    | tail (lenf, $ CONS (x, f), lenr, r) = check (lenf - 1, f, lenr, r)
end

(* Exercise 6.2 *)
(** Hypothesize D(i) <= min(3i, 2|f| - |r|).
  *
  * snoc repays 1 debt. tail repays 3 debts.
  * snoc decrements 2|f| - |r| by 1. If snoc repays debt for first node for f,
  * the hypothesize holds.
  * tail decrements 3i by 3, and 2|f| - |r| by 2. If tail repays debt for first
  * three nodes, the hypothesize holds.
  * If snoc or tail calls reverse, |f| is m, and |r| is 2m + 1, then ++ create
  * m debts for first m nodes in f, and reverse create 2m debts for node m.
  * Then,
  *     d(i) = 1 (i < m) | 2m (i = m) | 0 (i > m)
  *     D(i) = i + 1 (i < m) | 3m + 1 (i >= m).
  * Because snoc or tail repays debt for at least first node in f, the
  * hypothesize holds.
  *
  *
  * When the invariant condition is |f| >= |r|, 1st, 3rd, 7th, 15th, 31th, 63th
  * snoc and 27 th tail call reverse, so reverse is called 7 times.
  * When the invariant condition is 2|f| >= |r|, 1st, 4th, 13th, 40th snocs and
  * 11th tail call reverse, so reverse is called 5 times.
  * Therefore, the number of reverse calls of the later implementation is less
  * than that of the former. While the average cost of reverse is bigger.
  * The later cost is 100 / 5 = 20, and the former is 100 / 7 = 14.28.
  *
  * *)

(** Physicist's Method **)

functor LazyBinomialHeap (Element : ORDERED) : HEAP =
struct
  structure Elem = Element

  datatype Tree = NODE of int * Elem.T * Tree list
  type Heap = Tree list susp

  val empty = $ []
  fun isEmpty ($ ts) = null ts

  fun rank (NODE (r, x, c)) = r
  fun root (NODE (r, x, c)) = x
  fun link (t1 as NODE (r, x1, c1), t2 as NODE (_, x2, c2)) =
    if Elem.leq (x1, x2) then NODE (r + 1, x1, t2::c1)
    else NODE (r + 1, x2, t1::c2)
  fun insTree (t, []) = [t]
    | insTree (t, ts as t'::ts') =
    if rank t < rank t' then t::ts else insTree (link (t t'), ts')

  fun mrg (ts1, $ []) = ts1
    | mrg ($ [], ts2) = ts2
    | mrg (ts1 as t1::ts1', ts2 as t2::ts2') =
    if rank t1 < rank t2 then t1::mrg (ts1', ts2)
    else if rank t2 < rank t1 then t2::mrg (ts2', ts1)
    else insTree (link (t1, t2), mrg (ts1', ts2'))

  fun lazy insert (x, $ ts) = $ insTree (NODE (0, x, []), ts)
  fun lazy merge ($ ts1, $ ts2) = $ mrg (ts1, ts2)

  fun removeMinTree [] = raise EMPTY
    | removeMinTree [t] = (t, [])
    | removeMinTree [t::ts] =
    let val (t', ts) = removeMinTree ts
    in if Elem.leq (root t, root t') then (t, ts) else (t', t::ts) end

  fun findMin ($ ts) = let val (t, _) = removeMinTree ts in root t end
  fun lazy deleteMin ($ ts) =
    let val (NODE (_, x, ts1), ts2) = removeMinTree ts
    in $ mrg (rev ts1, ts2) end

end

(* Exercise 6.3 *)
(** The complete cost of findMin is k. findMin does not change the
  * potential, but findMin may force suspension for a object which potential is
  * not 0. So, the amortized cost is k + Ψ(h) <= log(n) + log(n) = O(log(n)).
  *
  * Let t be the number of trees in a heap, r be the rank of tree with minimum
  * value, and k be the number of link calls in the deleteMin.
  * The complete cost of deleteMin is t + r + k.
  * The amortized cost is
  *     t + r + k - ((log(n - 1) - (t - 1 + r - k)) - (log(n) - t))
  *     = t + r + k - (log(n - 1) - log(n) + 1 - r + k)
  *     = t + 2r - log(n - 1) + log(n) - 1
  *     <= t + 2r       (log(n) - 1 <= log(n - 1) <= log(n))
  *     <= 3log(n)      (t <= log(n), r <= log(n))
  *
  * Let n1, k1 be the number of trees, the number of nodes in one heap
  * respectively. Let n2 (<= n1), k2 be the number of trees, the number of
  * nodes in another heap. Let k be the number of link calls in the merge.
  * The complete cost of merge is log(n1) + k.
  * The amortized cost is
  *     log(n2) + 1 + k - (
  *         (log(n1 + n2) - (k1 + k2 - k)) - (log(n1) - k1 + log(n2) - k2))
  *     = log(n2) + 1 + k - (log(n1 + n2) + k - log(n1) - log(n2))
  *     = log(n1) + 1 + 2log(n2) - log(n1 + n2)
  *     <= log(n1) + 1 + 2log(n2) - log(2n1) = 2log(n2)
  *
  * *)

(* Exercise 6.4 *)
(** If lazy is removed from the definitions of merge and deleteMin, each
  * function may forces suspension. So the each amortized cost is added its
  * potential to. Because the potential is at most log(n), the each amortized
  * cost is O(log(n)).
  *
  * *)

(* Exercise 6.5 *)
functor SizedHeap (H : HEAP) : HEAP =
struct
  structure Elem = H.Elem
  datatype Heap = NE of int * H.Heap

  val empty = NE (0, H.empty)
  fun isEmpty NE (n, h) = (n = 0)

  fun insert (x, NE (n, h)) = NE (n + 1, H.insert (x, h))
  fun merge (NE (n1, h1), NE (n2, h2)) = NE (n1 + n2, H.merge (h1, h2))

  fun findMin NE (n, h) = H.findMin h

  fun deleteMin NE (n, h) = NE (n - 1, H.deleteMin h)

end

structure PhysicistQueue : QUEUE =
struct
  type 'a Queue = 'a list * int * 'a list susp * int * list

  val empty = ([], 0, $ [], 0, [])
  fun isEmpty (_, lenf, _, _, _) = (lenf = 0)

  fun checkw ([], lenf, f, lenr, r) = (force f, lenf, f, lenr, r)
    | checkw q = q
  fun check (q as (w, lenf, f, lenr, r)) =
    if lenr <= lenf then checkw q
    else let val f' = force f
         in checkw (f', lenf + lenr, $ (f' @ rev r), 0, []) end

  fun snoc ((w, lenf, f, lenr, r), x) = check (w, lenf, f, lenr + 1, x::r)

  fun head ([], lenf, f, lenr, r) = raise EMPTY
    | head (x::w, lenf, $ f, lenr, r) = x
  fun tail ([], lenf, f, lenr, r) = raise EMPTY
    | tail (x::w, lenf, f, lenr, r)
    = check (w, lenf - 1, $ tl (force f), lenr, r)
end

(* Exercise 6.6 *)
(** (a) snoc rotates r only if the queue is empty, which means the potential is
  * zero. So, the amortized cost of snoc is still O(1).
  * On the one hand, tail may rotate r when the potential is not zero.
  * Therefore, the amortized cost of tail is not O(1) but O(n).
  * For example, when calling 2^(n + 1) snocs, first snoc rotates r and set w
  * to a list with one element, and f has 2^(n) and 2^(n) elements respectively.
  * For this queue, tail creates suspension which rotates r, and snoc force the
  * suspension by making w empty. This cost is 2^n.
  * Reuse same queue, and apply the same operations. Because another snoc
  * creates an other suspension, the cost of another tail is also 2^n.
  *
  * (b) If tail does not create suspension ($ tl (force f)), checkw and check
  * must extract some head elements when forcing f. This cost is not shared cost
  * but unshared cost, so the tail cost is added O(|f|).
  * For example, when there is a queue with n elements in f and 0 elements in r,
  * and calling n tails, nth tail forces f, which cost is n. Reuse the queue
  * which is called n - 1 tail and another tail calling also forces f. Because
  * the operation extracting head elements is not suspension, the another
  * tail's cost is also n.
  * *)

signature SORTABLE =
sig
  structure Elem : ORDERED

  type Sortable

  val empty : Sortable
  val add : Elem.T * Sortable -> Sortable
  val sort : Sortable -> Elem.T list
end

functor BottomUpMergeSort (Element : ORDERED) : SORTABLE =
struct
  structure Elem = Element

  type Sortable = int * Elem.T list list susp

  fun mrg ([], ys) = ys
    | mrg (xs, []) = xs
    | mrg (xs as x::xs', ys as y::ys') =
    if Elem.leq (x, y) then x::mrg (xs', ys) else y::mrg (xs, ys')

  val empty = (0, $ [])
  fun add (x, (size, segs)) =
    let
      fun addSeg (seg, segs, size) =
        if size mod 2 = 0 then seg::segs
        else addSeg (mrg (seg, hd segs), tl segs, size div 2)
    in (size + 1, $ addSeg ([x], force segs, size)) end
  fun sort (size, segs) =
    let
      fun mrgAll (xs, []) = xs
        | mrgAll (xs, seg::segs) = mrgAll (mrg (xs, seg), segs)
    in mrgAll ([], force segs) end
end

(* Exercise 6.7 *)
functor BankersBottomUpMergeSort (Element : ORDERED) : SORTABLE =
struct
  structure Elem = Element

  type Sortable = int * Elem.T Stream list

  fun lazy mrg ($ NIL, ys) = ys
         | mrg (xs, $ NIL) = xs
         | mrg (xs as $ CONS (x, xs'), ys as $ CONS (y, ys')) =
         if Elem.leq (x, y) then $ CONS (x, mrg (xs', ys))
         else $ CONS (y, mrg (xs, ys'))

  val empty : (0, [])

  fun add (x, (size, segs)) =
    let
      fun addSeg (seg, segs, size) =
        if size mod 2 = 0 then seg::segs
        else addSeg (mrg (seg, hd segs), tl segs, size div 2)
    in (size + 1, addSeg ($ CONS (x, $ NIL), segs, size)) end

  fun mrgAll (xs, []) = xs
    | mrgAll (xs, seg::segs) = mrgAll (mrg (xs, seg), segs)

  fun sort (size, segs) =
    let
      fun toList ($ NIL) = []
        | toList ($ CONS (x, xs)) = x::toList (xs)
    in toList (mrgAll ([], segs)) end

  fun take (k) =
    let
      fun toList (k, $ NIL) = []
        | toList (0, xs) = []
        | toList (k, $ CONS (x, xs)) = x::toList (k - 1, xs)
    in toList (k, mrgAll ([], segs)) end

(** (a) Hypothesize D(n) is at most 2n, when add and sort repay log(n) + 1 and
  * n debts respectively.
  * When n = 2^k and given i (i < 2^k), total shared cost by add is
  *     2 * [i / 2] + 4 * [i / 4] + ... + 2^(k - 1) * [i / 2^(k - 1)]
  *     <= 2 * i / 2 + 4 * i /4 + ... + 2^(k - 1) * i / 2^(k - 1) = (k - 1)i.
  * If one add repays log(n) + 1 = k + 1 debts, then
  *     D(n + i) = D(n) + (k - 1)i - i * (k + 1) = D(n) - 2i.
  * So, i = 2^k, D(2^(k + 1)) excluding the debt which this add increments is 0.
  * This add adds 2 * 2^(k + 1) - 2 debts, then D(2^(k + 1) = 2n) <= 2 * 2n.
  *
  * The unshared cost of sort at worst case (when n = 2^k - 1) is
  *     1 + (1 + 2) + ... + (1 + 2 + ... + 2^(k - 1)) + n + 1 = 3n - k + 2
  * (mrg created by mrgAll is not unshared).
  * If sort repays 2n debts, because D(n) is 0 sort can force suspension created
  * by add.
  *
  * The amortized cost of add is k + 1 + k + 1 = 2log(n) + 2.
  * The amortized cost of sort is k + 1 + 2n + 2n - k + 1 + n + 1 = 3 + 5n.
  *
  * (b) Unshared cost of take is at most
  *     log(n) + sum_(i=1)^k{log(n) - i + 1) + k
  *     = (k + 1)log(n) - k(k + 1)/2 + 2k
  *     = (k + 1)log(n) - k(k - 3)/2.
  * The cost of taking one element from list is at most O(log(n)).
  * Therefore, if take repays klog(n) debts, take can force suspension.
  * Then the amortized cost of take is (2k + 1)log(n) - k(k - 3)/2.
  *
  * *)
end

functor LazyParingHeap (Element : ORDERED) : HEAP =
struct
  structure Elem = Element

  datatype Heap = E | T of Elem.T *  Heap * Heap susp

  val empty = E
  fun isEmpty E = true | isEmpty _ = false

  fun merge (a, E) = a
    | merge (E, b) = b
    | merge (a as T (x, _, _), b as T (y, _, _)) =
    if Elem.leq (x, y) then link (a, b) else link (b, a)
  and link (T (x, E, m), a) = T (x, a, m)
    | link (T (x, b, m), a) = T (x, E $ merge (merge (a, b), force m))

  fun insert (x, a) = merge (T (x, E, $ E), a)

  fun findMin E = raise EMPTY
    | findMin (T (x, a, m)) = x
  fun deleteMin E = raise EMPTY
    | deleteMin (T (x, a, $ b)) = merge (a, b)
end

