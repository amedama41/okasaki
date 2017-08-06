(** 10.1 Structural Decomposition **)

(* Exercise 10.1 *)
(** fun update (0, e, ONE (x, ps)) = ONE (e, ps)
  *   | update (i, e, ONE (x, ps)) = cons (x, update (i - 1, e ZERO ps))
  *   | update (i, e, ZERO ps) =
  *   let val (x, y) = lookup (i div 2, ps)
  *       val p = if i mod 2 = 0 then (e, y) else (x, e)
  *   in ZERO (update i div 2, p, ps) end
  *
  * Let k = log(i + 1). The cost of update is
  *     k + (k - 1) + (k - 2) + ... + 1
  *     = k(k + 1)/2 = ((log(i + 1))^2 + log(i + 1)) / 2 = O((log(n))^2).
  * *)

structure AltBinaryRandomAccessList : RANDOMACCESSLIST =
struct
  datatype 'a RList =
    NIL | ZERO of ('a * 'a) RList | ONE of 'a * ('a * 'a) RList

  val empty = NIL
  fun isEmpty NIL = true | isEmpty _ = false

  fun cons (x, NIL) = ONE (a, NIL)
    | cons (x, ZERO ps) = ONE (x, ps)
    | cons (x, ONE (y, ps)) = ZERO (cons ((x, y), ps))

  fun uncons NIL = raise EMPTY
    | uncons (ONE (x, ps)) = (x, ZERO ps)
    | uncons (ZERO ps) = let val ((x, y), ps') = uncons ps
                         in (x, ONE (y, ps')) end

  fun head xs = let val (x, _) = uncons xs in x end
  fun tail xs = let val (_, xs') = uncons xs in xs' end

  fun lookup (i, NIL) = raise SUBSCRIPT
    | lookup (0, ONE (x, ps)) = x
    | lookup (i, ONE (x, ps)) = lookup (i - 1, ZERO ps)
    | lookup (i, ZERO ps) = let val (x, y) = lookup (i div 2, ps)
                            in if i mod 2 = 0 then x else y end

  fun fupdate (f, i, NIL) = raise SUBSCRIPT
    | fupdate (f, 0, ONE (x, ps)) = ONE (f x, ps)
    | fupdate (f, i, ONE (x, ps)) = cons (x, fupdate (f, i - 1, ZERO ps))
    | fupdate (f, i, ZERO ps) =
    let fun f' (x, y) = if i mod 2 = 0 then (f x, y) else (x, f y)
    in ZERO (fupdate (f', i div 2, ps)) end

  fun update (i, y, xs) = fupdate (fn x => y, i, xs)
end

(* Exercise 10.2 *)
structure LazyAltBinaryRandomAccessList : RANDOMACCESSLIST =
struct
  datatype 'a RList = NIL
                    | ONE of 'a * ('a * 'a) RList susp
                    | TWO of 'a * 'a * ('a * 'a) RList susp
                    | THREE of 'a * 'a * 'a * ('a * 'a) RList susp

  val empty = NIL
  fun isEmpty NIL = true | isEmpty _ = false

  fun cons (x, NIL) = ONE (x, $ NIL)
    | cons (x, ONE (y, ps)) = TWO (x, y, ps)
    | cons (x, TWO (y, z, ps)) = THREE (x, y, z, ps)
    | cons (x1, THREE (x2, y, z, ps)) = TWO (x1, x2, $ cons ((y, z), ps))

  fun uncons NIL = raise EMPTY
    | uncons (ONE (x, $ NIL)) = (x, NIL)
    | uncons (ONE (x, $ ps)) =
    let val ((y, z), ps') = uncons ps in (x, TWO (y, z, $ ps')) end
    | uncons (TWO (x, y, ps)) = (x, ONE (y, ps))
    | uncons (THREE (x, y, z, ps)) = (x, TWO (y, z, ps))

  fun head NIL = raise EMPTY
    | head (ONE (x, ps)) = x
    | head (TWO (x, y, ps)) = x
    | head (THREE (x, y, z, ps)) = x
  fun tail xs = let val (_, xs') = uncons xs in xs' end

  fun lookup (i, NIL) = raise SUBSCRIPT
    | lookup (i, ONE (x, ps)) =
    if i = 0 then x
    else let val (x', y') = lookup ((i - 1) div 2, force ps)
         in if (i - 1) mod 2 = 0 then x' else y' end
    | lookup (i, TWO (x, y, ps)) =
    if i = 0 then x else lookup (i - 1, ONE (y, ps))
    | lookup (i, THREE (x, y, z, ps)) =
    if i = 0 then x else lookup (i - 1, TWO (y, z, ps))

  fun fupdate (f, i, ONE (x, ps)) =
    if i = 0 then ONE (f x, ps)
    else
      let
        fun f' (x, y) = if i mod 2 = 0 then (f x, y) else (x, f y)
        val ps' = fupdate (f', i div 2, force ps)
      in ONE (x, $ ps') end
    | fupdate (f, i, TWO (x, y, ps)) =
    if i = 0 then TWO (f x, y, ps)
    else cons (x, fupdate (f, i - 1, ONE (y, ps)))
    | fupdate (f, i, THREE (x, y, z, ps)) =
    if i = 0 then THREE (f x, y, z, ps)
    else cons (x, fupdate (f, i - 1, TWO (y, z, ps)))

  fun update (i, y, xs) = fupdate (fn x => y, i, xs)

  (** Proof is same as exercise 9.9 *)
end

structure BootstrappedQueue : QUEUE =
struct
  datatype 'a Queue = E
                    | Q of int * 'a list * 'a list susp Queue * int * 'a list

  val empty = E
  fun isEmpty E = true | isEmpty _ = false

  fun checkQ (q as (lenfm, f, m, lenr, r)) =
    if lenr <= lenfm then checkF q
    else checkF (lenfm + lenr, f, snoc (m, $ rev r), 0, [])
  and checkF (lenfm, [], E, lenr, r) = E
    | checkF (lenfm, [], m, lenr, r) =
    Q (lenfm, force (head m), tail m, lenr, r)
    | checkF q = q
  and snoc (E, x) = (1, [x], E, 0, [])
    | snoc (Q (lenfm, f, m, lenr, r), x) = checkQ (lenfm, f, m, lenr + 1, x::r)
  and head E = raise EMPTY
    | head (Q (lenfm, x::f', m, lenr, r)) = x
  and tail E = raise EMPTY
    | tail (Q (lenfm, x::f', m, lenr, r)) = checkQ (lenfm - 1, f', m, lenr, r)
end

(* Exercise 10.3 *)
(** tail(snoc(q, x))
  * If snoc (q, x) calls snoc recursively, lenfm and lenr after the call is
  * lenfm + lenr (>= 2) and 0 respectively. Just because tail  subtracts 1 from
  * the lenfm, lenfm is still larger than lenr and snoc is not called.
  *
  * *)

(* Exercise 10.4 *)
structure BootstrappedQueue' : QUEUE =
struct
  datatype 'a EL = ELEM of 'a | LIST of 'a EL list susp
  datatype 'a Queue = E | Q of int * 'a EL list * 'a Queue * int * 'a EL list

  val empty = E
  fun isEmpty E = true | isEmpty _ = false

  fun checkQ (q as (lenfm, f, m, lenr, r)) =
    if lenr <= lenfm then checkF q
    else checkF (lenfm + lenr, f, snocList (m, $ rev r), 0)
  and checkF (lenfm, [], E, lenr, r) = E
    | checkF (lenfm, [], m, lenr, r) =
    Q (lenfm, force (headList f), checkQ (tailList m), lenr, r)
    | checkF q = q
  and snocList (E, x) = checkQ (1, [LIST x], E, 0, [])
    | snocList (Q (lenfm, f, m, lenr, r)) =
    checkQ (lenfm, f, m, lenr + 1, LIST x::r)
  and headList (Q (lenfm, LIST x::f, m, lenr, r)) = x
  and tailList (Q (lenfm, LIST x::f, m, lenr, r)) =
    checkQ (lenfm - 1, f, m, lenr, r)

  fun snoc (E, x) = Q (1, [ELEM x], E, 0, [])
    | snoc (Q (lenfm, f, m, lenr, r)) = checkQ (lenfm, f, m, lenr + 1, x::r)
  fun head E = raise EMPTY
    | head (Q (lenfm, ELEM x::f, m, lenr, r)) = x
  fun tail E = raise EMPTY
    | tail (Q (lenfm, ELEM x::f, m, lenr, r)) =
    checkQ (lenfm - 1, f, m, lenr, r)
end

(* Exercise 10.5 *)
functor BootstrapQueue (PrimQ : QUEUE) : QUEUE =
struct
  datatype 'a Queue = E
                    | Q of int * 'a list * 'a list susp PrimQ * int * 'a list

  val empty = E
  fun isEmpty E = true | isEmpty _ = false

  fun checkQ (q as (lenfm, f, m, lenr, r)) =
    if lenr <= lenfm then checkF q
    else checkF (lenfm + lenr, f, PrimQ.snoc (m, $ rev r), 0, [])
  and checkF (lenfm, [], PrimQ.empty, lenr, r) = E
    | checkF (lenfm, [], m, lenr, r) =
    Q (lenfm, force (PrimQ.head m), PrimQ.tail m, lenr, r)

  fun snoc (E, x) = Q (1, [x], PrimQ.empty, 0, [])
    | snoc (Q (lenfm, f, m, lenr, r), x) = checkQ (lenfm, f, m, lenr + 1, x::r)
  fun head E = raise EMPTY
    | head (Q (lenfm, x::f, m, lenr, r)) = x
  fun tail E = raise EMPTY
    | tail (Q (lenfm, x::f, m, lenr, r)) = checkQ (lenfm - 1, f, m, lenr, r)
end
(** Let D(i) = min(2i, |f| + |m| - |r|), hypothesize the total cost until ith
  * element is not greater than D(i).
  *
  * Though snoc increments |r| by 1, the invariant is hold if snoc repays 1
  * debt. Though tail decrements i by 1, the invariant is hold if tail repays
  * 2 debts.
  * When snoc results in rotation, the (|f| + |m| - 1)th element is assigned
  * |f| + |m| + 1 debts. Then d(i) = 0 (i < |f| + |m| - 1 or i >= |f| + |m|) or
  * |f| + |m| + 1 (i = |f| + |m| - 1), and D(i) = 0 (i < |f| + |m| - 1) or
  * |f| + |m| + 1 (i >= |f| + |m| - 1). If this snoc repays 3 debt, the
  * invariant is hold.
  * When tail results in rotation, the invariant is hold if the tail repays 3
  * debt.
  *
  * If PrimQ is RealTimeQueue, the complexity of PrimQ.snoc, PrimQ.head, and
  * PrimQ.tail is O(1). Therefore, the amortized cost of snoc, head, and tail
  * of BootstrapQueue is O(1).
  *
  * *)

(** 10.2 Structural Abstraction **)

signature CATENABLELIST =
sig
  type 'a Cat

  val empty : 'a Cat
  val isEmpty : 'a Cat -> bool

  val cons : 'a * 'a Cat -> 'a Cat
  val snoc : 'a Cat * 'a -> 'a Cat
  val ++ : 'a Cat * 'a Cat -> 'a Cat

  val head : 'a Cat -> 'a
  val tail : 'a Cat -> 'a Cat
end

functor CatanableList (Q : QUEUE) : CATENABLELIST =
struct
  datatype 'a Cat = E | C of 'a * 'a Cat susp Q.Queue

  val empty = E
  fun isEmpty E = true | isEmpty _ = false

  fun link (C (x, q), s) = C (x, Q.snoc (q, s))
  fun linkAll (q) =
    let
      val $ t = Q.head q
      val q' = Q.tail q
    in if Q.isEmpty q' then E else link (t, $ linkAll q') end

  fun xs ++ E = xs
    | E ++ xs = xs
    | xs ++ ys = link (xs, & ys)
  fun cons (x, xs) = C (x, Q.empty) ++ xs
    | snoc (xs, x) = xs ++ C (x, Q.empty)

  fun head E = raise EMPTY
    | head C (x, q) = x
  fun tail E = raise EMPTY
    | tail (C (x, q)) = if Q.isEmpty q then E else linkAll q

  (* Exercise 10.6 *)
  fun flatten [] = E
    | flatten (E::xs) = flatten xs
    | flatten (x::xs) = link (x, $ flatten xs)
  (** Let n be sum_(j=0){|t_j|}. Assign one debt for each non-empty t_j, and
    * repays the last non-empty t's debt. Therefore,
    *
    *   D(n + i)
    *       = n + D_(t_(j+1))(i) + j
    *       = n + i + depth_(t_(j+1))(i) + j
    *       = n + i + depth_t(n + i) - j + j
    *       = (n + i) + depth_t(n + i).
    *
    * Because the unshared cost of flatten is O(1 + e), then the amortized cost
    * is O(1 + e).
    *
    * *)
end

functor Bootstrap (functor MakeH (Element : ORDERED)
                              : HEAP where type Elem.T = Element.T)
                  (Element : ORDERED) : HEAP =
struct
  structure Elem = Element

  structure rec BootstrapedElem =
  struct
    datatype T = E | H of Elem.T * PrimH.Heap
    fun leq (H (x, _), H (y, _)) = Elem.leq (x, y)
    fun eq (H (x, _), H (y, _)) = Elem.eq (x, y)
    fun lt (H (x, _), H (y, _)) = Elem.lt (x, y)
  end
  and PrimH = MakeH (BootstrapedElem)

  open BootstrapedElem

  type Heap = BootstrapedElem.T

  val empty = E
  fun isEmpty E = true | isEmpty _ = false

  fun merge (E, h) = h
    | merge (h, E) = h
    | merge (h1 as H (x, p1), h2 as H (y, p2)) =
    if Elem.leq (x, y) then H (x, PrimH.insert (h2, p1))
    else H (y, PrimH.insert (h1, p2))
  fun insert (x, h) = merge (H (x, PrimH.empty), h)

  fun findMin E = raise EMPTY
    | findMin (H (x, _)) = x
  fun deleteMin E = raise EMPTY
    | deleteMin (H (x, p)) =
    if PrimH.isEmpty p then E
    else
      let
        val (H (y, p1)) = PrimH.findMin p
        val p2 = PrimH.deleteMin p
      in H (y, PrimH.merge (p1, p2)) end
end

(* Exercise 10.7 *)
functor BootstrappedLazyBinomialHeap (Element : ORDERED) : HEAP =
struct
  structure Element = Element

  datatype Tree = NODE of int * Heap * Tree list
  datatype Heap = E | H of Elem.T * Tree list susp

  val empty = E
  fun isEmpty E = true | isEmpty _ = false

  fun rank (NODE (r, x, c)) = r
  fun root (NODE (r, H (x, p), c)) = x
  fun link (t1 as NODE (r, H (x1, p1), c1), t2 as NODE (_, H (x2, p2), c2)) =
    if Elem.leq (x1, x2) then NODE (r + 1, H (x1, p1), t2::c1)
    else NODE (r + 1, H (x2, p2), t1::c2)
  fun insTree (t, []) = [t]
    | insTree (t, ts as t'::ts') =
    if rank t < rank t' then t::ts else insTree (link (t, t'), ts')

  fun mrg (ts1, $ []) = ts1
    | mrg ($ [], ts2) = ts2
    | mrg (ts1 as t1::ts1', ts2 as t2::ts2') =
    if rank t1 < rank t2 then t1::mrg (ts1', ts2)
    else if rank t2 < rank t1 then t2::mrg (ts1, ts2')
    else insTree (link (t1, t2), mrg (ts1', ts2'))

  fun merge (E, h) = h
    | merge (h, E) = h
    | merge (h1 as H (x, p1), h2 as H (y, p2)) =
    if Elem.leq (x, y) then H (x, $ insTree (NODE (0, h2, []), force p1))
    else H (y, $ insTree (NODE (0, h1, []), force p2))
  fun insert (x, h) = merge (H (x, $ []), h)

  fun removeMinTree [t] = (t, [])
    | removeMinTree [t::ts] =
    let val (t', ts') = removeMinTree ts'
    in if Elem.leq (root t, root t') then (t, ts) else (t', t::ts') end

  fun findMin E = raise
    | findMin (H (x, _)) = x
  fun deleteMin E = raise EMPTY
    | deleteMin (H (x, $ [])) = E
    | deleteMin (H (x, $ p)) =
    let val (H (y, p1), p2) = removeMinTree p in H (y, $ mrg (p1, p2)) end
end

