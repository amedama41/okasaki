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
    if lenr <= lenf then q else (lenf + lenr, f ++ reverse r, 0 $ NIL)

  fun snoc ((lenf, f, lenr, r), x) = check (lenf, f, lenr + 1, $ CONS (x, r))

  fun head (lenf, $ NIL, lenr, r) = raise EMPTY
    | head (lenf, $ CONS (x, f), lenr, r) = x
  fun tail (lenf, $ NIL, lenr, r) = raise EMPTY
    | tail (lenf, $ CONS (x, f), lenr, r) = check (lenf - 1, f, lenr, r)
end

(* Exercise 6.2 *)
(** Hypothesize D(i) <= min(3i, 2|f| - |r|).
  *
  * snoc repays 1 dept. tail repays 3 dept.
  * snoc decrements 2|f| - |r| by 1. If snoc repays dept for first node for f,
  * the hypothesize holds.
  * tail decrements 3i by 3, and 2|f| - |r| by 2. If tail repays dept for first
  * three nodes, the hypothesize holds.
  * If snoc or tail calls reverse, |f| is m, and |r| is 2m + 1, then ++ create
  * m dept for first m nodes in f, and reverse create 2m dept for node m.
  * Then,
  *     d(i) = 1 (i < m) | 2m (i = m) | 0 (i > m)
  *     D(i) = i + 1 (i < m) | 3m + 1 (i >= m).
  * Because snoc or tail repays dept for at least first node in f, the
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

