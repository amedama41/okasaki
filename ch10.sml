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

signature HEAPWITHINFO =
sig
  structure Priority : ORDERED

  type 'a Heap

  val empty : 'a Heap
  val isEmpty : 'a Heap -> bool

  val insert : Priority.T * 'a * 'a Heap -> 'a Heap
  val merge : 'a Heap * 'a Heap -> 'a Heap

  val findMin : 'a Heap -> Priority.T * 'a
  val deleteMin : 'a Heap -> 'a Heap
end

(* Exercise 10.8 *)
functor LazyBinomialHeapWithInfo (PriorityElement : ORDERED) : HEAPWITHINFO =
struct
  structure Priority = PriorityElement

  datatype 'a Tree = NODE of int * Priority.T * 'a * Tree list
  type Heap = 'a Tree list susp

  val empty = $ []
  fun isEmpty ($ ts) = null ts

  fun rank (NODE (r, p, x, c)) = r
  fun priority (NODE (r, p, x, c)) = p
  fun root (NODE (r, p, x, c)) = (p, x)
  fun link (t1 as NODE (r, p1, x1, c1), t2 as NODE (_, p2, x2, c2)) =
    if Priority.leq (p1, p2) then NODE (r + 1, p1, x1, t2::c1)
    else NODE (r + 1, p2, x2, t1::c2)
  fun insTree (t, []) = [t]
    | insTree (t, ts as t'::ts') =
    if rank t < rank t' then t::ts else insTree (link (t, t'), ts')

  fun mrg (ts1, $ []) = ts1
    | mrg ($ [], ts2) = ts2
    | mrg (ts1 as t1::ts1', ts2 as t2::ts2') =
    if rank t1 < rank t2 then t1::mrg (ts1', ts2)
    else if rank t2 < rank t1 then t2::mrg (ts1, ts2')
    else insTree (link (t1, t2), mrg (ts1', ts2'))

  fun lazy insert (p, x, $ ts) = $ insTree (NODE (0, p, x, []), ts)
  fun lazy merge ($ ts1, $ ts2) = $ mrg (ts1, ts2)

  fun removeMinTree [] = raise EMPTY
    | removeMinTree [t] = (t, [])
    | removeMinTree [t::ts] =
    let val (t', ts') = removeMinTree ts
    in if Elem.leq (priority t, priority t') then (t, ts) else (t', t::ts') end

  fun findMin ($ ts) = let val (t, _) = removeMinTree ts in root t end
  fun lazy deleteMin ($ ts) =
    let val (NODE (_, p, x, ts1), ts2) = removeMinTree ts
    in $ mrg (rev ts1, ts2) end
end

functor SkewBinomialHeapWithInfo (PriorityElement : ORDERED) : HEAPWITHINFO =
struct
  structure Priority = PriorityElement
  datatype 'a Tree =
    NODE of int * Priority.T * 'a * (Priority.T * 'a) list * Tree list
  type Heap = Tree list

  val empty = []
  fun isEmpty ts = null ts

  fun rank (NODE (r, xp, x, xs, c)) = r
  fun priority (NODE (r, xp, x, xs, c)) = xp
  fun root (NODE (r, xp, x, xs, c)) = (xp, x)
  fun link (t1 as NODE (r, p1, x1, xs1, c1), t2 as NODE (_, p2, x2, xs2, c2)) =
    if Priority.leq (p1, p2) then NODE (r + 1, p1, x1, xs1, t2::c1)
    else NODE (r + 1, p2, x2, xs2, t1::c2)
  fun skewLink (xp, x, t1, t2) =
    let val NODE (r, yp, y, ys, c) = link (t1, t2)
    in
      if Priority.leq (xp, yp) then NODE (r, xp, x, (yp, y)::ys, c)
      else NODE (r, y, (xp, x)::ys, c)
    end

  fun insTree (t, []) = [t]
    | insTree (t1, t2::ts) =
    if rankd t1 < rank t2 then t1::t2::ts else insTree (link (t1, t2), ts)
  fun mergeTrees (ts1, []) = ts1
    | mergeTrees ([], ts2) = ts2
    | mergeTrees (ts1 as t1::ts1', ts2 as t2::ts2') =
    if rank t1 < rank t2 then t1::mergeTrees (ts1', ts2)
    else if rank t2 < rank t1 then t2::mergeTrees (ts1, ts2')
    else insTree (link (t1, t2), mergeTrees (ts1', ts2'))
  fun normalize [] = []
    | normalize (t::ts) = insTree (t, ts)

  fun insert (xp, x, ts as t1::t2::rest) =
    if rank t1 = rank t2 then skewLink (xp, x, t1, t2)::rest
    else NODE (0, xp, x, [], [])::ts
    | insert (xp, x, ts) = NODE (0, xp, x, [], [])::ts
  fun merge (ts1, ts2) = mergeTrees (normalize ts1, normalize ts2)

  fun removeMinTree [] = raise EMPTY
    | removeMinTree [t] = (t, [])
    | removeMinTree (t::ts) = 
    let val (t', ts') = removeMinTree ts
    in if Priority.leq (priority t, priority t') then (t, ts)
       else (t', t::ts') end

  fun findMin ts = let val (t, _) = removeMinTree ts in root t end
  fun deleteMin ts =
    let
      val (NODE (_, xp, x, xs, ts1), ts2) = removeMinTree ts
      fun insertAll ([], ts) = ts
        | insertAll ((xp, x)::xs, ts) = insert (xp, x, ts)
    in
      insertAll (xs, merge (rev ts1, ts2))
    end
end

functor Bootstrap' (PrimH : HEAPWITHINFO) : HEAPWITHINFO =
struct
  type Priority = PrimH.Priority

  datatype 'a T = E | H of Priority.T * 'a * 'a T PrimH.Heap
  type 'a Heap = 'a T

  val empty = E
  fun isEmpty E = true | isEmpty _ = false

  fun merge (E, h) = h
    | merge (h, E) = h
    | merge (h1 as H (xp, x, p1), h2 as H (yp, y, p2)) =
    if Priority.leq (xp, yp) then H (xp, x, PrimH.insert (h2, p1))
    else H (yp, y, PrimH.insert (h1, p2))
  fun insert (xp, x, h) = merge (H (xp, x, PrimH.empty), h)

  fun findMin E = raise EMPTY
    | findMin (H (xp, x, _)) = (xp, x)
  fun deleteMin E = raise EMPTY
    | deleteMin (H (xp, x, p)) =
    if PrimH.isEmpty p then E
    else
      let
        val (H (yp, y, p1)) = PrimH.findMin p
        val p2 = PrimH.deleteMin p
      in H (yp, y, PrimH.merge (p1, p2)) end
end

(** 10.3 Bootstrapping To Aggregate Types **)

signature FINITEMAP =
sig
  type Key
  type 'a Map

  val empty : 'a Map
  val bind : Key * 'a * 'a Map -> 'a Map
  val lookup : Key * 'a Map -> 'a
end

functor Trie (M : FINITEMAP) : FINITEMAP =
struct
  type Key = M.Key list

  datatype 'a Map = TRIE of 'a option * 'a Map M.Map

  val empty = TRIE (NONE, M.empty)

  fun lookup ([], TRIE (NONE, m)) = raise NOTFOUND
    | lookup ([], TRIE (SOME x, m)) = x
    | lookup (k::ks, TRIE (v, m)) = lookup (ks, M.lookup (k, m))

  fun bind ([], x, TRIE (_, m)) = TRIE (SOME x, m)
    | bind (k::ks, x, TRIE (v, m)) =
    let
      val t = M.lookup (k, m) handle NOTFOUND => empty
      val t' = bind (ks, x, t)
    in TRIE (v, M.bind (k, t', m)) end
end

(* Exercise 10.9 *)
functor Trie10_9 (M : FINITEMAP) : FINITEMAP =
struct
  type Key = M.Key list

  datatype 'a Map = ENTRY of 'a | TRIE of 'a Map M.Map

  val empty = TRIE M.empty

  fun lookup ([], ENTRY x) = x
    | lookup (k::ks, TRIE m) = lookup (ks, M.lookup (k, m))

  fun bind ([k], x, TRIE m) = TRIE (M.bind (k, ENTRY x, m))
    | bind (k::ks, x, TRIE m) =
    let val t = M.lookup (k, m) handle NOTFOUND => empty
    in TRIE (M.bind (k, bind (ks, x, t), m)) end
end

(* Exercise 10.10 *)
functor Trie10_10 (M : FINITEMAP) : FINITEMAP =
struct
  type Key = M.Key list

  datatype 'a Map = TRIE of M.Key list * 'a option * 'a Map M.Map

  val empty = TRIE ([], NONE, M.empty)

  fun eq (k1, k2) =
    let
      val v = M.lookup (k1, M.bind (k2, true, M.empty))
      handle NOTFOUND => false
    in v end

  fun lookup ([], TRIE ([], SOME x, m)) = x
    | lookup ([], TRIE (p, v, m)) = raise NOTFOUND
    | lookup (k::ks, TRIE ([], v, m)) = lookup (ks, M.lookup (k, m))
    | lookup (k, TRIE (p, v, m)) =
    let
      fun removePrefix (k, []) = (k, [])
        | removePrefix ([], p) = ([], p)
        | removePrefix (k::ks, p::ps) =
        if eq (k, p) then removePrefix (ks, ps) else (ks, ps)
      val (k', p') = removePrefix (k, p)
    in if null p' then lookup (k', TRIE ([], v, m)) else raise NOTFOUND end

  fun bind (k, x, m) =
    let
      fun aux (c, [], x, TRIE ([], v, m)) = TRIE (rev c, SOME x, m)
        | aux (c, [], x, TRIE (p::ps, v, m)) =
        TRIE (rev c, SOME x, M.bind (p, TRIE (ps, v, m), M.empty))
        | aux (c, k::ks, TRIE ([], v, m)) =
        let
          val t = aux ([], ks, x, M.lookup (k, m))
          handle NOTFOUND => TRIE (ks, SOME x, M.empty)
        in TRIE (rev c, v, M.bind (k, t, m)) end
        | aux (c, k::ks, x, TRIE (p::ps, v, m)) =
        if eq (k, p) then aux (k::c, ks, x, TRIE (ps, v, m))
        else TRIE (rev c, NONE,
          M.bind (k, TRIE (ks, SOME x, M.bind (p, TRIE (ps, v, m), M.empty))))
    in aux ([], k, x, m) end
end

(* Exercise 10.11 *)
functor HashTable (structure Approx : FINITEMAP
                   structure Exact : FINITEMAP
                   val hash : Exact.Key -> Approx.Key) : FINITEMAP =
struct
  type Key = Exact.Key
  type 'a Map = 'a Exact.Map Approx.Map

  val empty = Approx.empty

  fun lookup (k, m) = Exact.lookup (k, Approx.lookup (hash k, m))

  fun bind (k, x, m) =
    let
      val h = hash k
      val em = Approx.lookup (h, m) handle NOTFOUND => Exact.empty
    in Approx.bind (h, Exact.bind (k, x, em)) end
end

datatype 'a Tree = E | T of 'a * 'a Tree * 'a Tree

functor TrieOfTrees (M : FINITEMAP) : FINITEMAP
struct
  type Key = M.Key Tree

  datatype 'a Map = TRIE of 'a option * 'a Map Map M.Map

  val empty = TRIE (NONE, M.empty)

  fun lookup (E, TRIE (NONE, m)) = raise NOTFOUND
    | lookup (E, TRIE (SOME x, m)) = x
    | lookup (T (k, a, b), TRIE (v, m)) =
    lookup (b, lookup (a, M.lookup (k, m)))

  fun bind (E, x, TRIE (_, m)) = TRIE (SOME x, m)
    | bind (T (k, a, b), x, TRIE (v, m)) =
    let
      val tt = M.lookup (k, m) handle NOTFOUND => empty
      val t = lookup (a, tt) handle NOTFOUND => empty
      val t' = bind (b, x, t)
      val tt' = bind (a, t', tt)
    in TRIE (v, M.bind (k, tt', m)) end
end

(* Exercise 10.12 *)
functor TrieOfTrees10_12 (M : FINITEMAP) : FINITEMAP =
struct
  type Key = M.Key Tree

  datatype 'a Map = TRIE of 'a EM option * 'a Map M.Map
  and 'a EM = ELEM of 'a | MAP of 'a Map

  val empty = TRIE (NONE, M.empty)

  fun lookupMap (E, TRIE (NONE, m)) = raise NOTFOUND
    | lookupMap (E, TRIE (SOME (MAP x), m)) = x
    | lookupMap (T (k, a, b), TRIE (v, m)) =
    lookupMap (a, M.lookup (k, v))
  fun lookup (E, TRIE (NONE, m)) = raise NOTFOUND
    | lookup (E, TRIE (SOME (ELEM x), m)) = x
    | lookup (T (k, a, b), TRIE (v, m)) =
    lookup (b, lookupMap (a, M.lookup (k, m)))

  fun bindMap (E, x, TRIE (_, m)) = TRIE (SOME (MAP x), m)
    | bindMap (T (k, a, b), x, TRIE (v, m)) =
    let
      val tt = M.lookup (k, m) handle NOTFOUND => empty
      val t = lookupMap (a, tt) handle NOTFOUND => empty
      val t' = bindMap (b, x, t)
      val tt' = bindMap (a, t', tt)
    in TRIE (v, M.bind (k, tt', m)) end
  fun bind (E, TRIE (_, m)) = TRIE (SOME (ELEM x), m)
    | bind (T (k, a, b), x, TRIE (v, m)) =
    let
      val tt = M.lookup (k, m) handle NOTFOUND => empty
      val t = lookupMap (a, tt) handle NOTFOUND => empty
      val t' = bind (b, x, t)
      val tt' = bindMap (a, t', tt)
    in TRIE (v, M.bind (k, tt', m)) end
end

