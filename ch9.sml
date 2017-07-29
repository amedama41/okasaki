(** 9.1 Positional Number System **)

structure Dense =
struct
  datatype Digit = ZERO | ONE
  type Nat = Digit list

  fun inc [] = [ONE]
    | inc (ZERO::ds) = ONE::ds
    | inc (ONE::ds) = ZERO::inc ds

  fun dec [ONE] = []
    | dec (ONE::ds) = ZERO::ds
    | dec (ZERO::ds) = ONE::dec ds

  fun add (ds, []) = ds
    | add ([], ds) = ds
    | add (d::ds1, ZERO::ds2) = d::add(ds1, ds2)
    | add (ZERO::ds1, d::ds2) = d::add(ds1, ds2)
    | add (ONE::ds1, ONE::ds2) = ZERO::inc (add (ds1, ds2))
end

struct SparseByWeight =
struct
  type Nat = int list

  fun carry (w, []) = [w]
    | carry (w, ws as w'::ws') =
    if w < w' then w::ws else carry (2 * w, ws')

  fun borrow (w, ws as w'::ws') =
    if w = w' then ws' else w::borrow (w * 2, ws)

  fun inc ws = carry (1, ws)
  fun dec ws = borrow (1, ws)

  fun add (ws, []) = ws
    | add ([], ws) = ws
    | add (m as w1::ws1, n as ws2::ws2) =
    if w1 < w2 then w1::add (ws1, n)
    else if w2 < w1 then w2::add (m, ws2)
    else carry (2 * w1, add (ws1, ws2))
end

(** 9.2 Binary Numbers **)

signature RANDOMACCESSLIST =
sig
  type 'a RList

  val empty : 'a RList
  val isEmpty : 'a RList -> bool

  val cons : 'a * 'a RList -> 'a RList
  val head : 'a RList -> 'a
  val tail : 'a RList -> 'a RList

  val lookup : int * 'a RList -> 'a
  val update : int * 'a * 'a RList -> 'a RList
end

structure BinaryRandomAccessList : RANDOMACCESSLIST =
struct
  datatype 'a Tree = LEAF of 'a | NODE of int * 'a Tree * 'a Tree
  datatype 'a Digit = ZERO | ONE of 'a Tree
  type 'a RList = 'a Digit list

  val empty = []
  fun isEmpty ts = null ts

  fun size (LEAF x) = 1
    | size (NODE (w, t1, t2)) = w
  fun link (t1, t2) = NODE (size t1 + size t2, t1, t2)
  fun consTree (t, []) = [ONE t]
    | consTree (t, ZERO::ts) = ONE t::ts
    | consTree (t1, ONE t2::ts) = ZERO::consTree (link (t1, t2), ts)
  fun unconsTree [] = raise EMPTY
    | unconsTree [ONE t] = (t, [])
    | unconsTree (ONE t::ts) = (t, ZERO::ts)
    | unconsTree (ZERO::ts) =
    let
      val (NODE (_, t1, t2), ts') = unconsTree ts'
    in (t1, ONE t2::ts') end

  fun cons (x, ts) = consTree (LEAF x, ts)
  fun head ts = let val (LEAF x, _) = unconsTree ts in x end
  fun tail ts = let val (_, ts') = unconsTree ts in ts' end

  fun lookupTree (0, LEAF x) = x
    | lookupTree (i, LEAF x) = raise SUBSCRIPT
    | lookupTree (i, NODE (w, t1, t2)) =
    if i < w div 2 then lookupTree (i, t1)
    else lookupTree (i - w div 2, t2)
  fun updateTree (0, y, LEAF x) = LEAF y
    | updateTree (i, y, LEAF x) = raise SUBSCRIPT
    | updateTree (i, y, NODE (w, t1, t2)) =
    if i < w div 2 then NODE (w, updateTree (i, y, t1), t2)
    else NODE (w, t1, updateTree (i - w div 2, y, t2))

  fun lookup (i, []) = raise SUBSCRIPT
    | lookup (i, ZERO::ts) = lookup (i, ts)
    | lookup (i, ONE t::ts) =
    if i < size t then lookupTree (i, t) else lookup (i - size t, ts)
  fun update (i, y, []) = raise SUBSCRIPT
    | update (i, y, ZERO::ts) = ZERO::update (i, y, ts)
    | update (i, y, ONE t::ts) =
    if i < size t then One (updateTree (i, y, t))::ts
    else ONE t::update (i - size t, y, ts)

  (* Exercise 9.1 *)
  fun dropTree (k, LEAF x, ts) = ts
    | dropTree (k, NODE (w, t1, t2), ts) =
    if k <= w div 2 then dropTree (k, t1, ONE t2::ts)
    else dropTree (k - w div 2, t1, ZERO::ts)
  fun drop (0, ts) = ts
    | drop (k, []) = []
    | drop (k, ZERO::ts) = drop (k, ts)
    | drop (k, [ONE t]) = if k > size t then [] else dropTree (k, t, [])
    | drop (k, ONE t::ts) =
    if k > size t then drop (k - size t, ts) else dropTree (k, t, ZERO::ts)

  (* Exercise 9.2 *)
  fun create (n, x) =
    let
      fun aux (0, t) = []
        | aux (n, t) =
        if n mod 2 = 1 then ONE t::aux (n div 2, NODE (2 * size t, t, t))
        else ZERO::aux (n div 2, NODE (2 * size t, t, t))
  in aux (n, LEAF x) end
end

(* Exercise 9.3 *)
structure SparseBinaryRandomAccessList : RANDOMACCESSLIST =
struct
  datatype 'a Tree = LEAF of 'a | NODE of int * 'a Tree * 'a Tree
  type 'a RList = 'a Tree list

  val empty = []
  fun isEmpty ts = null ts

  fun size (LEAF x) = 1
    | size (NODE (w, t1, t2)) = w
  fun link (t1, t2) = NODE (size t1 + size t2, t1, t2)
  fun consTree (t, []) = [t]
    | consTree (t, ts as t'::ts') =
    if size t < size t' then t::ts else consTree (link (t, t'), ts)
  fun unconsTree [] = raise EMPTY
    | unconsTree (t::ts) =
    let
      fun aux (LEAF x, ts) = (x, ts)
        | aux (NODE (w, t1, t2), ts) = aux (t1, t2::ts)
    in aux (t, ts) end

  fun cons (x, ts) = consTree (LEAF x, ts)
  fun head ts = let val (LEAF x, _) = unconsTree ts in x end
  fun tail ts = let val (_, ts') = unconsTree ts in ts' end

  fun lookupTree (0, LEAF x) = x
    | lookupTree (i, NODE (w, t1, t2)) =
    if i < w div 2 then lookupTree (i, t1)
    else lookupTree (i - w div 2, t2)
  fun updateTree (0, y, LEAF x) = LEAF y
    | updateTree (i, y, NODE (w, t1, t2)) =
    if i < w div 2 then NODE (w, updateTree (i, y, t1), t2)
    else NODE (w, t1, updateTree (i - w div 2, y, t2))

  fun lookup (i, []) = raise SUBSCRIPT
    | lookup (i, t::ts) =
    if i < size t then lookupTree (i, t) else lookup (i - size t, ts)
  fun update (i, y, []) = raise SUBSCRIPT
    | update (i, y, t::ts) =
    if i < size t then updateTree (i, t)::ts else t::update (i - size t, ts)
end

(* Exercise 9.4 *)
structure ZeroLessDense =
struct
  datatype Digit = ONE | TWO
  type Nat = Digit list

  fun inc [] = [ONE]
    | inc (ONE::ds) = TWO::ds
    | inc (TWO::ds) = ONE::inc ds

  fun dec [ONE] = []
    | dec (TWO::ds) = ONE::ds
    | dec (ONE::ds) = TWO::dec ds

  fun add (ds, []) = ds
    | add ([], ds) = ds
    | add (ONE::ds1, ONE::ds2) = TWO::add(ds1, ds2)
    | add (TWO::ds1, TWO::ds2) = TWO::inc (inc (add(ds1, ds2)))
    | add (d1::ds1, d2::ds2) = ONE::inc (add(ds1, ds2))
end

(* Exercise 9.5 *)
structure ZeroLessBinaryRandomAccessList : RANDOMACCESSLIST =
struct
  datatype 'a Tree = LEAF of 'a | NODE of int * 'a Tree * 'a Tree
  datatype 'a Digit = ONE of 'a Tree | TWO of 'a Tree * 'a Tree
  type 'a RList = 'a Digit list

  val empty = []
  fun isEmpty ts = null ts

  fun size (LEAF x) = 1
    | size (NODE (w, t1, t2)) = w
  fun link (t1, t2) = NODE (size t1 + size t2, t1, t2)
  fun consTree (t, []) = [ONE t]
    | consTree (t, ONE (t1)::ts) = TWO (t, t1)::ts
    | consTree (t, TWO (t1, t2)::ts) = ONE t::consTree (link (t1, t2), ts)
  fun unconsTree [] = raise EMPTY
    | unconsTree [ONE t] = (t, [])
    | unconsTree (TWO (t1, t2)::ts) = t1, ONE t2::ts
    | unconsTree (ONE t::ts) =
    let
      val (NODE (_, t1, t2), ts') = unconsTree ts
    in (t, TWO (t1, t2)::ts') end

  fun cons (x, ts) = consTree (LEAF x, ts)
  fun head [] = raise EMPTY
    | head (ONE (LEAF x)::_) = x
    | head (TWO (LEAF x, LEAF y)::_) = x
  fun tail ts = let val (_, ts') = unconsTree ts in ts' end

  fun lookupTree (0, LEAF x) = x
    | lookupTree (i, NODE (w, t1, t2)) =
    if i < w div 2 then lookupTree (i, t1)
    else lookupTree (i - w div 2, t2)
  fun updateTree (0, y, LEAF x) = LEAF y
    | updateTree (i, y, NODE (w, t1, t2)) =
    if i < w div 2 then NODE (w, updateTree (i, y, t1), t2)
    else NODE (w, t1, updateTree (i - w div 2, y, t2))

  fun lookup (i, []) = raise SUBSCRIPT
    | lookup (i, ONE t::ts) =
    if i < size t then lookupTree (i, t) else lookup (i - size t, ts)
    | lookup (i, TWO (t1, t2)::ts) =
    if i < size t1 then lookupTree (i, t1)
    else if i - size t1 < size t2 then lookupTree (i - size t1, t2)
    else lookup (i - size t1 - size t2, ts)
  fun update (i, y, []) = raise SUBSCRIPT
    | update (i, ONE t::ts) =
    if i < size t then updateTree(i, y, t)::ts else t::update (i, y, ts)
  fun update (i, (t' as TWO (t1, t2))::ts) =
    if i < size t1 then TWO (updateTree (i, y, t1), t2)::ts
    else if i - size t1 < size t2
    then TWO (t1, updateTree (i - size t1, y, t2))::ts
    else t'::update (i - size t1 - size t2, y, ts)
end

(* Exercise 9.6 *)
(** Let k be the step for look for the tree including target element.
  * 1 + 2 + ... + 2^(k - 1) < i => 2^k - 1 < i => k < log(i + 1).
  * Because the size of the tree is 2^k - 1, which depth is k, the total cost
  * is at most 2log(i + 1).
  *
  * *)

(* Exercise 9.7 *)
functor RedBlackSet (Element : ORDERED) : SET =
struct
  type Elem = Element.T

  datatype Tree = E | T of Tree * Elem * Tree
  (* B and RB corresponds to ONE and TWO respectively. *)
  datatype Node = B of Elem * Tree | RB of Elem * Tree * Elem * Tree
  type Set = Node list

  val empty = E
  fun isEmpty ts = null ts

  fun insTree ((x1, t1), B (x2, t2)::ts) = RB (x1, t1, x2, t2)
    | insTree ((x1, t1), RB (x2, t2, x3, t4)::ts) =
    B (x1, t1)::insTree ((x2, T (t2, x3, t3)), ts)

  fun insert (x, ts) = insTree ((x, E), ts)
end

(* Exercise 9.8 *)
(** If x has first continuous k TWOs, inc changes the k TWOs to the k ONEs.
  * inc assigns 1 debt to the each ONE, and repays 1 debt for the ONE just after
  * the TWOs if any.
  * If y has first continuous k ZEROs, dec changes the k ZERO to the k ONES.
  * dec assigns 1 debt to the each ONE and repays 1 debt for the ONE just after
  * the ZEROs if any.
  * Therefore, the invariant (only ONE has only one debt) holds, and the cost of
  * inc and dec is O(1).
  * *)

(* Exercise 9.9 *)
structure RedundantZeroLessBinaryRandomAccessList : RANDOMACCESSLIST =
struct
  datatype 'a Tree = LEAF of 'a | NODE of int * 'a Tree * 'a Tree
  datatype 'a Digit = ONE of 'a Tree
                    | TWO of 'a Tree * 'a Tree
                    | THREE of 'a Tree * 'a Tree * 'a Tree
  type 'a RList = Digit Stream

  val empty = $ NIL
  fun isEmpty ($ NIL) = true | isEmpty _ = false

  fun size (LEAF x) = 1
    | size (NODE (w, t1, t2)) = w
  fun link (t1, t2) = NODE (size t1 + size t2, t1, t2)
  fun consTree (t1, $ NIL) = $ CONS (ONE t, $ NIL)
    | consTree (t1, $ CONS (ONE t2, ts)) = $ CONS (TWO (t1, t2), ts)
    | consTree (t1, $ CONS (TWO (t2, t3), ts)) =
    $ CONS (THREE (t1, t2, t3), ts)
    | consTree (t1, $ CONS (THREE (t2, t3, t4), ts)) =
    $ CONS (TWO (t1, t2), consTree (link (t3, t4), ts))
  fun unconsTree ($ NIL) = raise EMPTY
    | unconsTree ($ CONS (ONE t, ts)) =
    let
      val (NODE (_, t1, t2), ts') = unconsTree ts
    in (t, $ CONS (TWO (t1, t2), ts')) end
    | unconsTree ($ CONS (TWO (t1, t2), ts)) = (t1, $ CONS (ONE t2, ts))
    | unconsTree ($ CONS (THREE (t1, t2, t3), ts)) =
    (t1, $ CONS (TWO (t2, t3), ts))

  fun cons (x, ts) = consTree (LEAF x, ts)
  fun head ($ NIL) = raise EMPTY
    | head ($ CONS (ONE (LEAF x), ts)) = x
    | head ($ CONS (TWO (LEAF x, LEAF y), ts)) = x
    | head ($ CONS (THREE (LEAF x, LEAF y, LEAF z), ts)) = x
  fun tail ts = let val (_, ts') = unconsTree ts in ts' end
end
(** Hypothesize TWO has a debt, and ONE and THREE has no debt.
  * If x has first continuous k THREEs, cons changes the k THREEs to the k TWOs.
  * cons assigns 1 debt to the each TWO, and repays 1 debt for the TWO just
  * after the THREEs if any.
  * If y has first continuous k ONEs, tail changes the k ONE to the k TWOS.
  * tail assigns 1 debt to the each TWO and repays 1 debt for the TWO just after
  * the ONEs if any.
  * Therefore, the invariant holds, and the cost of cons and tail is O(1).
  * head does not change a list, then the cost of head is also O(1).
  * *)

(* Exercise 9.10 *)
structure ScheduledRedundantZeroLessBinaryRandomAccessList : RANDOMACCESSLIST =
struct
  datatype 'a Tree = LEAF of 'a | NODE of int * 'a Tree * 'a Tree
  datatype 'a Digit = ONE of 'a Tree
                    | TWO of 'a Tree * 'a Tree
                    | THREE of 'a Tree * 'a Tree * 'a Tree
  type Schedule = Digit Stream list
  type 'a RList = Digit Stream * Schedule

  val empty = ($ NIL, [])
  fun isEmpty ($ NIL, _) = true | isEmpty _ = false

  fun size (LEAF x) = 1
    | size (NODE (w, t1, t2)) = w
  fun link (t1, t2) = NODE (size t1 + size t2, t1, t2)
  fun consTree (t1, $ NIL) = $ CONS (ONE t, $ NIL)
    | consTree (t1, $ CONS (ONE t2, ts)) = $ CONS (TWO (t1, t2), ts)
    | consTree (t1, $ CONS (TWO (t2, t3), ts)) =
    $ CONS (THREE (t1, t2, t3), ts)
    | consTree (t1, $ CONS (THREE (t2, t3, t4), ts)) =
    $ CONS (TWO (t1, t2), consTree (link (t3, t4), ts))
  fun unconsTree ($ NIL) = raise EMPTY
    | unconsTree ($ CONS (ONE t, ts)) =
    let
      val (NODE (_, t1, t2), ts') = unconsTree ts
    in (t, $ CONS (TWO (t1, t2), ts')) end
    | unconsTree ($ CONS (TWO (t1, t2), ts)) = (t1, $ CONS (ONE t2, ts))
    | unconsTree ($ CONS (THREE (t1, t2, t3), ts)) =
    (t1, $ CONS (TWO (t2, t3), ts))

  fun exec [] = []
    | exec ($ CONS (TWO (t1, t2), ts)) = ts::sched
    | exec (_::sched) = sched

  fun cons (x, (ts, sched)) =
    let val ts' = consTree (LEAF x, ts)
    in (ts', exec (exec (ts'::sched))) end
  fun head ($ NIL, []) = raise EMPTY
    | head ($ CONS (ONE (LEAF x), ts), _) = x
    | head ($ CONS (TWO (LEAF x, LEAF y), ts), _) = x
    | head ($ CONS (THREE (LEAF x, LEAF y, LEAF z), ts), _) = x
  fun tail (ts, sched) =
    let val (_, ts') = unconsTree ts
    in (ts', exec (exec (ts'::sched))) end

(** Hypothesize there are two TWO elements before first range in schedule, and
  * there is one TWO element between any neighbor schedule ranges.
  *
  * Let r1, r2 be the first two schedule range, and x1, x2 be the TWO elements,
  * and x3 be the one TWO element between r1 and r2, and r0 is the new range
  * created by cons or tail, and m be the number of TWO created by the cons or
  * the tal.
  * m=0: If first element of r1 is not TWO, the element becomes TWO, and x2 and
  * the element are the two TWO elements. Otherwise, x2 and x3 are the TWO
  * elements.
  * m=1: The first element of r0 and x2 are the two TWO elements.
  * m>=2: The first two element of r0 are the two TWO elements, and x2 is the
  * one TWO element.
  * *)
end

(* Exercise 9.11 *)
functor SegmentedBinomialHeap (Element : ORDERED) : HEAP =
struct
  structure Elem = Element

  datatype Tree = NODE of Elem.T * Tree list
  datatype Digit = ZERO | ONES of Tree list | TWO of Tree * Tree
  type Heap = Digit list

  val empty = []
  fun isEmpty ds = null ds

  fun root (NODE (x, ts)) = x
  fun link (t1 as NODE (x1, c1), t2 as NODE (x2, c2)) =
    if Elem.leq (x1, x2) then NODE (x1, t2::c1) else NODE (x2, t1::c2)
  fun ones ([], ds) = ds
    | ones ([t], ONES ts::ds) = ONES (t::ts)::ds
    | ones (ts, ds) = ONES ts::ds

  fun insHeap (t, []) = [ONES [t]]
    | insHeap (t, ZERO::ds) = ones ([t], ds)
    | insHeap (t, ONES (t'::ts)::ds) = TWO (t, t')::ones (ts, ds)
  fun fixup (TWO (t1, t2)::ds) = ZERO::insHeap (link (t1, t2), ds)
    | fixup (ONES ts::TWO (t1, t2)::ds) =
    ONES ts::ZERO::insHeap (link (t1, t2), ds)
    | fixup ds = ds

  fun insert (x, ds) = fixup (insHeap (NODE (x, []), ds))

  fun insHeap' (t, []) = [ONES [t]]
    | insHeap' (t, ZERO::ds) = ones ([t], ds)
    | insHeap' (t, ONES (t'::ts)::ds) =
    ZERO::insHeap' (link (t, t'), ones (ts, ds))
  fun normalize [] = []
    | normalize (ZERO::ds) = ZERO::normalize ds
    | normalize (ONES ts::ds) = ONES ts::normalize ds
    | normalize (TWO (t1, t2)::ds) =
    ZERO::insHeap' (link (t1, t2), normalize ds)

  fun merge (ds, []) = normalize ds
    | merge ([], ds) = normalize ds
    | merge (TWO (t1, t2)::ds1, TWO (t3, t4)::ds2) =
    ZERO::insHeap' (link (t1, t2), insHeap' (link (t3, t4), merge (ds1, ds2)))
    | merge (TWO (t1, t2)::ds1, d::ds2) =
    d::insHeap' (link (t1, t2), merge (ds1, ds2))
    | merge (d::ds1, TWO (t1, t2)::ds2) =
    d::insHeap' (link (t1, t2), merge (ds1, ds2))
    | merge (ONES (t1::ts1)::ds1, ONES (t2::ts2)::ds2) =
    ZERO::insHeap' (link (t1, t2), merge (ones (ts1, ds1), ones (ts2, ds2)))
    | merge (ZERO::ds1, ONES (t::ts)::ds2) = ones ([t], merge (ds1, ds2))
    | merge (ONES (t::ts)::ds1, ZERO::ds2) = ones ([t], merge (ds1, ds2))
    | merge (ZERO::ds1, ZERO::ds2) = ZERO::merge (ds1, ds2)

  fun removeMinTree (ONES [t]) = (t, [ZERO])
    | removeMinTree (ONES (t::ts)) =
    let val (t', ts') = removeMinTree (ONES ts)
    in if Elem.leq (root t, root t') then (t, ZERO::ONES ts)
       else (t', ones ([t], ts'))
    end
  fun removeMinDigit [] = raise EMPTY
    | removeMinDigit [d as (ONES ts)] = removeMinTree d
    | removeMinDigit [TWO (t1, t2)] = (link (t1, t2), [])
    | removeMinDigit ZERO::ds =
    let val (t', ds') = removeMinDigit ds in (t', ZERO::ds') end
    | removeMinDigit ((d as ONES ts)::ds) =
    let
      val (t, ds') = removeMinTree d
      val (t', ds'') = removeMinDigit ds
    in if Elem.leq (t, t') then (t, ZERO::ds'::ds) else (t', d::ds'') end
    | removeMinDigit (TWO (t1, t2)::ds) =
    let
      val t3 = link (t1, t2)
      val (t4, ds') = removeMinDigit ds
    in if Elem.leq (root t3, root t4)
       then (t3, ZERO::ds) else (t4, TWO (t1, t2)::ds')
    end

  fun findMin ds = let val (t, _) = removeMinDigit ds in root t end
  fun deleteMin ds =
  let
    val (NODE (_, ts), ds') = removeMinDigit ds
  in merge (ONES (rev ts), ds') end
end

(* Exercise 9.12 *)
structure Segmented =
struct
  datatype DigitBlock = ONES of int | THREES of int
  datatype Digits = ZERO | TWO | FOUR | BLOCK of DigitBlock list
  type Nat = Digits list

  fun ones (0, [], ds) = ds
    | ones (0, bs, ds) = BLOCK bs::ds
    | ones (i, [], BLOCK bs::ds) = BLOCK (ONES i::bs)::ds
    | ones (i, bs, ds) = BLOCK (ONES i::bs)::ds
  fun threes (0, [], ds) = ds
    | threes (0, bs, ds) = BLOCK bs::ds
    | threes (i, [], BLOCK bs::ds) = BLOCK (THREES i::bs)::ds
    | threes (i, bs, ds) = BLOCK (THREES i::bs)::ds

  fun simpleinc [] = [BLOCK [ONES 1]]
    | simpleinc (BLOCK (ONES i::bs)::ds) = TWO::ones (i - 1, bs, ds)
    | simpleinc (TWO::ds) = threes (1, [], ds)
    | simpleinc (BLOCK (THREES i::bs)::ds) = FOUR::threes (i - 1, bs, ds)
  fun simpledec [BLOCK [ONES 1]] = []
    | simpledec (BLOCK (ONES i::bs)::ds) = ZERO::ones (i - 1, bs, ds)
    | simpledec (TWO::ds) = ones (1, [], ds)
    | simpledec (BLOCK (THREES i::bs)::ds) = TWO::threes (i - 1, bs, ds)
  fun fixup (FOUR::ds) = TWO::simpleinc ds
    | fixup (BLOCK bs::FOUR::ds) = BLOCK bs::TWO::simpleinc ds
    | fixup (ZERO::ds) = TWO::simpledec ds
    | fixup (BLOCK bs::ZERO::ds) = BLOCK bs::TWO::simpledec ds
    | fixup ds = ds

  fun inc ds = fixup (simpleinc ds)
  fun dec ds = fixup (simpledec ds)
end

(* Exercise 9.13 *)
structure SegmentedBinaryRandomAccessList : RANDOMACCESSLIST =
struct
  datatype 'a Tree = LEAF of 'a | NODE of int * 'a Tree * 'a Tree
  datatype 'a DigitBlock = ONES of 'a Tree list
                         | THREES of ('a Tree * 'a Tree * 'a Tree) list
  datatype 'a Digits = ZERO
                     | TWO of 'a Tree * 'a Tree
                     | FOUR of 'a Tree * 'a Tree * 'a Tree * 'a Tree
                     | BLOCK of 'a DigitBlock list
  type 'a RList = 'a Digits list

  val empty = []
  fun isEmpty ts = null ts

  fun size (LEAF x) = 1
    | size (NODE (w, t1, t2)) = w
  fun link (t1, t2) = NODE (size t1 + size t2, t1, t2)

  fun ones ([], [], ds) = ds
    | ones ([], bs, ds) = BLOCK bs::ds
    | ones (ts, [], BLOCK bs::ds) = BLOCK (ONES ts::bs)::ds
    | ones (ts, bs, ds) = BLOCK (ONES ts::bs)::ds
  fun threes ([], [], ds) = ds
    | threes ([], bs, ds) = BLOCK bs::ds
    | threes (ts, [], BLOCK bs::ds) = BLOCK (THREES ts::bs)::ds
    | threes (ts, bs, ds) = BLOCK (THREES ts::bs)::ds

  fun consTree (t, []) = [BLOCK [ONES [t]]]
    | consTree (t1, BLOCK (ONES (t2::ts)::bs)::ds) =
    TWO (t1, t2)::ones (ts, bs, ds)
    | consTree (t1, TWO (t2, t3)::ds) = threes ((t1, t2, t3), [], ds)
    | consTree (t1, BLOCK (THREES ((t2, t3, t4)::ts)::bs)::ds) =
    FOUR (t1, t2, t3, t4)::threes (ts, bs, ds)
  fun unconsTree ([BLOCK [ONES [t]]]) = (t, [])
    | unconsTree (BLOCK (ONES (t::ts)::bs)::ds) = (t, ZERO::ones (ts, bs, ds))
    | unconsTree (TWO (t1, t2)::ds) = (t1, ones ([t2], [], ds))
    | unconsTree (BLOCK (THREES ((t1, t2, t3)::ts)::bs)::ds) =
    (t1, TWO (t2, t3)::threes (ts, bs, ds))
  fun fixup (FOUR (t1, t2, t3, t4)::ds) =
    TWO (t1, t2)::consTree (link (t3, t4), ds)
    | fixup ((bs as BLOCK bs')::FOUR (t1, t2, t3, t4)::ds) =
    bs::TWO (t1, t2)::consTree (link (t3, t4), ds)
    | fixup (ZERO::ds) =
    let val (NODE (_, t1, t2), ds') = unconsTree ds in TWO (t1, t2)::ds' end
    | fixup ((bs as BLOCK bs')::ZERO::ds) =
    let val (NODE (_, t1, t2), ds') = unconsTree ds in bs::TWO (t1, t2)::ds' end
    | fixup ds = ds

  fun cons (x, ds) = fixup (consTree (LEAF x, ds))
  fun head (x, ds) = let val (LEAF x, _) = unconsTree ts in x end
  fun tail ts = let val (_, ts') = unconsTree ts in fixup ts' end

  fun lookupTree (0, LEAF x) = x
    | lookupTree (i, NODE (w, t1, t2)) =
    if i < w div 2 then lookupTree (i, t1)
    else lookupTree (i - w div 2, t2)
  fun lookupTwo (i, t1, t2) =
    if i < size t1 then lookupTree (i, t1) else lookupTree (i - size t1, t2)
  fun lookupThree (i, t1, t2, t3) =
    if i < size t1 then lookupTree (i, t1) else lookupTwo (i - size t1, t2, t3)
  fun lookupFour (i, t1, t2, t3, t4) =
    if i < size t1 then lookupTree (i, t1)
    else lookupTree (i - size t1, t2, t3, t4)

  fun lookup (i, []) = raise SUBSCRIPT
    | lookup (i, ZERO::ds) = lookup (i, ds)
    | lookup (i, BLOCK (ONES (t::ts)::bs)::ds) =
    if i < size t then lookupTree (i, t)
    else lookup (i - size t, ones (ts, bs, ds))
    | lookup (i, TWO (t1, t2)::ds) =
    if i < 2 * size t1 then lookupTwo (i, t1, t2)
    else lookup (i - size t1 - size t2, ds)
    | lookup (i, BLOCK (THREES ((t1, t2, t3)::ts)::bs)::ds) =
    if i < 3 * size t1 then lookupThree (i, t1, t2, t3)
    else lookup (i - size t1 - size t2 - size t3, threes (ts, bs, ds))
    | lookup (i, FOUR (t1, t2, t3, t4)::ds) =
    if i < 4 * size t1 then lookupFour (i, t1, t2, t3, t4)
    else lookup (i - size t1 - size t2 - size t3 - size t4, ds)

  fun updateTree (0, y, LEAF x) = LEAF y
    | updateTree (i, y, NODE (w, t1, t2)) =
    if i < w div 2 then NODE (w, updateTree (i, y, t1), t2)
    else NODE (w, t1, updateTree (i - w div 2, y, t2))
  fun updateTwo (i, y, t1, t2) =
    if i < size t1 then (updateTree (i, y, t1), t2)
    else (t1, updateTree (i - size t1, y, t2))
  fun updateThree (i, y, t1, t2, t3) =
    if i < size t1 then (updateTree (i, y, t1), t2, t3)
    else let val (t2', t3') = updateTwo (i - size t1, y, t2, t3)
         in (t1, t2', t3') end
  fun updateFour (i, y, t1, t2, t3, t4) =
    if i < size t1 then (updateTree (i, y, t1), t2, t3, t4)
    else let val (t2', t3', t4') = updateThree (i - size t1, y, t2, t3, t4)
         in (t1, t2', t3', t4') end

  fun update (i, y, []) = raise SUBSCRIPT
    | update (i, y, ZERO::ds) = ZERO::update (i, y, ds)
    | update (i, y, BLOCK (ONES (t::ts)::bs)::ds) =
    if i < size t then ones (updateTree (i, y, t), bs, ds)
    else ones ([t], [], update (i - size t, y, ones (ts, bs, ds)))
    | update (i, y, (d as TWO (t1, t2))::ds) =
    if i < 2 * size t1 then TWO (updateTwo (i, y, t1, t2))::ds
    else d::update (i - size t1 - size t2, y, ds)
    | update (i, y, BLOCK (THREES ((t as (t1, t2, t3))::ts)::bs)::ds) =
    if i < 3 * size t1 then threes ([updateThree (i, y, t1, t2, t3)], bs, ds)
    else threes ([t], [], update (i - 3 * size t1, y, threes (ts, bs, ds)))
    | update (i, y, (d as FOUR (t1, t2, t3, t4))::ds) =
    if i < 4 * size t1 then FOUR (updateFour (i, t1, t2, t3, t4))::ds
    else d::update (i - size t1 - size t2 - size t3 - size t4, y, ds)
end

(** 9.3 Skew Binary Numbers **)

structure SkewBinaryRandomAccessList : RANDOMACCESSLIST =
struct
  datatype 'a Tree = LEAF of 'a | NODE of 'a * 'a Tree * 'a Tree
  type 'a RList = (int * 'a Tree) list

  val empty = []
  fun isEmpty ts = null ts

  fun cons (x, ts as (w1, t1)::(w2, t2)::ts') =
    if w1 = w2 then (1 + w1 + w2, NODE (x, t1, t2))::ts'
    else (1, LEAF x)::ts
  fun head [] = raise EMPTY
    | head ((1, LEAF x)::ts) = x
    | head ((w, NODE (x, t1, t2))::ts) = x
  fun tail [] = raise EMPTY
    | tail ((1, LEAF x)::ts) = ts
    | tail ((w, NODE (x, t1, t2))::ts) = (w div 2, t1)::(w div 2, ts)::ts

  fun lookupTree (1, 0, LEAF x) = x
    | lookupTree (w, 0, NODE (x, t1, t2)) = x
    | lookupTree (w, i, NODE (x, t1, t2)) =
    if i <= w div 2 then lookupTree (w div 2, i - 1, t1)
    else lookupTree (w div 2, i - w div 2 - 1, t2)
  fun updateTree (1, 0, y, LEAF x) = LEAF y
    | updateTree (w, 0, y, NODE (x, t1, t2)) = NODE (x, t1, t2)
    | updateTree (w, i, y, NODE (x, t1, t2)) =
    if i <= w div 2 then updateTree (w div 2, i - 1, y, t1)
    else updateTree (w div 2, i - w div - 1, y, t2)

  fun lookup (i, []) = raise SUBSCRIPT
    | lookup (i, (w, t)::ts) =
    if i < w then lookupTree (w, i, t) else lookup (i - w, ts)
  fun update (i, y, []) = raise SUBSCRIPT
    | update (i, y, (w, t)::ts) =
    if i < w then (w, updateTree (w, i, y, t))::ts
    else (w, t)::update (i - w, y, ts)
end

(* Exercise 9.14 *)
structure HoodMelvileQueueBySkewBinaryRandomAccessList : QUEUE =
struct
  type 'a L = 'a SkewBinaryRandomAccessList

  datatype 'a RotationState =
      IDLE
    | REVERSING of int * 'a L.RList * 'a L.RList * int * 'a L.RList * 'a L.RList
    | APPENDING of int * 'a L.RList * 'a L.RList
    | DONE of 'a L.RList
  type 'a Queue = int * int * 'a L * 'a RotationState * int * 'a L

  val empty = (0, 0, L.empty, IDLE, 0, L.empty)
  fun isEmpty (lenf1, lenf2, f, state, lenr, r) = (lenf1 = 0)

  fun exec (REVERSING (ok, f, f', lenr, r, r')) = REVERSING (
    ok + 1, L.tail f, L.cons (L.head f, f'),
    lenr - 1, L.tail r, L.cons (L.head r, r'))
    | exec (REVERSING (ok, L.empty, f', lenr, r, r')) =
    APPENDING (ok, f', L.cons (L.head r, r'))
    | exec (APPENDING (0, f', r')) = DONE r'
    | exec (APPENDING (ok, f', r')) =
    APPENDING (ok - 1, L.tail f', L.cons (L.head f', r'))
    | exec state = state

  fun invalidate (REVERSING (ok, f, f', lenr, r, r')) =
    REVERSING (ok - 1, f, f', lenr, r, r')
    | invalidate (APPENDING (0, f', r')) = DONE (L.tail r')
    | invalidate (APPENDING (ok, f', r')) = APPENDING (ok - 1, f', r')
    | invalidate state = state

  fun exec2 (lenf1, lenf2, f, state, lenr, r) =
    case exec (exec state) of
         DONE newf => (lenf1, lenf1, newf, IDLE, lenr, r)
       | newstate => (lenf1, lenf2, f, newstate, lenr, r)

  fun check (q as (lenf1, lenf2, f, state, lenr, r)) =
    if lenr <= lenf1 then exec2 q
    else let val newstate = REVERSING (0, f, [], lenr, r, L.empty)
         in exec2 (lenf1 + lenr, lenf2, f, newstate, 0, L.empty) end

  fun snoc ((lenf1, lenf2, f, state, lenr, r), x) =
    check (lenf1, lenf2, f, state, lenr + 1, L.cons (x, r))
  fun head (lenf1, lenf2, f, state, lenr, r) = L.head f
  fun tail (lenf1, lenf2, f, state, lenr, r) =
    check (lenf - 1, lenf2 - 1, L.tail f, invalidate state, lenr, r)

  fun lookupState (i, lenf, REVERSING (ok, f, f', lenr, r, r')) =
    if i - lenf < lenr then L.lookup (lenr - (i - lenf) - 1, r)
    else L.lookup (i - lenf - lenr, r')
    | lookupState (i, lenf, APPENDING (ok, f', r')) = L.lookup (i - ok, r')
    | lookupState (i, lenf, DONE newf) = L.lookup (i, newf)
  fun updateState (i, y, lenf, IDLE) = IDLE
    | updateState (i, y, lenf, REVERSING (ok, f, f', lenr, r, r')) =
    if i < ok then REVERSING (ok, f, L.update (ok - i - 1, y, f'), lenr, r, r')
    else if i < lenf
    then REVERSING (ok, L.update (i - ok, y, f), f', lenr, r, r')
    else if i - lenf < lenr
    then REVERSING (ok, f, f', lenr, L.update (lenr - (i - lenf) - 1, y, r), r')
    else REVERSING (ok, f, f', lenr, r, L.update (i - lenf - lenr, y, r'))
    | updateState (i, y, lenf, APPENDING (ok, f', r')) =
    if i < ok then APPENDING (ok, L.update (ok - i - 1, y, f'), r')
    else APPENDING (ok, f', L.update (i - ok, y, r'))
    | updateState (i, y, lenf, DONE newf) = DONE (L.update (i, y, newf))

  fun lookup (i, (lenf1, lenf2, f, state, lenr, r)) =
    if i < lenf2 then lookup (i, lenf2, f)
    if i < lenf1 then lookupState (i, lenf1, state)
    else if i - lenf1 < lenr then L.lookup (lenr - (i - lenf1) - 1, r)
    else raise SUBSCRIPT
  fun update (i, y, (lenf1, lenf2, f, state, lenr, r)) =
    if i < lenf1
    then (lenf1, lenf2, L.update (i, y, f), updateState (i, y, state), lenr, r)
    else if i < lenf2
    then (lenf1, lenf2, f, updateState (i, y, state), lenr, r)
    else if i - lenf1 < lenr
    then (lenf1, lenf2, f, state, lenr, L.update (lenr - (i - lenf1) - 1, y, r))
    else raise SUBSCRIPT
end

(* Exercise 9.15 *)
(** Let E(r) be the upper of the element numbers. When r=0, E(r)=|t|=1.
  * E(r) = 2E(r - 1) + 1
  * E(r) + 1 = 2(E(r - 1) + 1)
  *          = 2^r(E(0) + 1)
  *          = 2^(r + 1)
  * E(r) = 2^(r + 1) + 1
  * *)

functor SkewBinomialHeap (Element : ORDERED) : HEAP =
struct
  structure Elem = Element
  datatype Tree = NODE of int * Elem.T * Elem.T list * Tree list
  type Heap = Tree list

  val empty = []
  fun isEmpty ts = null ts

  fun rank (NODE (r, x, xs, c)) = r
  fun root (NODE (r, x, xs, c)) = x
  fun link (t1 as NODE (r, x1, xs1, c1), t2 as NODE (_, x2, xs2, c2)) =
    if Elem.leq (x, y) then NODE (r + 1, x1, xs1, t2::c1)
    else NODE (r + 1, x2, xs2, t1::c2)
  fun skewLink (x, t1, t2) =
    let val NODE (r, y, ys, c) = link (t1, t2)
    in
      if Elem.leq (x, y) then NODE (r, x, y::ys, c)
      else NODE (r, y, x::ys, c)
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

  fun insert (x, ts as t1::t2::rest) =
    if rank t1 = rank t2 then skewLink (x, t1, t2)::rest
    else NODE (0, x, [], [])::ts
    | insert (x, ts) = NODE (0, x, [], [])::ts
  fun merge (ts1, ts2) = mergeTrees (normalize ts1, normalize ts2)

  fun removeMinTree [] = raise EMPTY
    | removeMinTree [t] = (t, [])
    | removeMinTree (t::ts) = 
    let val (t', ts') = removeMinTree ts
    in if Elem.leq (root t, root t') then (t, ts) else (t', t::ts') end

  fun findMin ts = let val (t, _) = removeMinTree ts in root t end
  fun deleteMin ts =
    let
      val (NODE (_, x, xs, ts1), ts2) = removeMinTree ts
      fun insertAll ([], ts) = ts
        | insertAll (x::xs, ts) = insert (x, ts)
    in
      insertAll (xs, merge (rev ts1, ts2))
    end
end

(* Exercise 9.16 *)
functor DeleteableHeap (H : HEAP) : HEAP =
struct
  type Heap = H.Heap * H.Heap

  val empty = (H.empty, H.empty)
  fun isEmpty (h1, h2) = H.isEmpty h1

  fun insert (x, (h1, h2)) = (H.insert (x, h1), h2)
  fun merge ((h1, h2), (h1', h2')) = (H.merge (h1, h1'), H.merge (h2, h2'))

  fun normalize (h1, h2) =
    let
      val x1 = H.findMin h1, x2 = H.findMin h2
    in if Elem.eq (x1, x2) then normalize (H.deleteMin h1, H.deleteMin h2)
       else if Elem.lt (x1, x2) then (h1, h2)
       else normalize (h1, H.deleteMin h2)
    end

  fun findMin ((h1, h2)) = H.findMin h1
  fun deleteMin ((h1, h2)) = normalize (H.deleteMin h1, h2)

  fun delete (x, (h1, h2)) = normalize (h1, H.insert (x, h2))
end

(** 9.4 Trinary and Quaternary Numbers **)

(* Exercise 9.17 *)
functor TrinomialHeap (Element: ORDERED) : HEAP =
struct
  structure Elem = Element

  datatype Tree = NODE of Elem.T * (Tree * Tree) list
  datatype Digit = ZERO | ONE of Tree | TWO of Tree * Tree
  type Heap = Digit list

  val empty = []
  fun isEmpty ts = null ts

  fun root (NODE (x, c1, c2)) = x
  fun link (t1 as NODE (x1, c1, c2), t2, t3) =
    let
      val (t2' as NODE (x2, c3, c4), t3') =
        if Elem.leq (root t2, root t3) then (t2, t3) else (t3, t2)
    in if Elem.leq (x1, x2) then NODE (x1, t2'::c1, t3'::c2)
       else NODE (x2, t1::c3, t3'::c4)
    end
  fun insTree (t, []) = [ONE t]
    | insTree (t, ZERO::ts) = ONE t::ts
    | insTree (t1, ONE t2::ts) = TWO (t1, t2)::ts
    | insTree (t1, TWO (t2, t3)::ts) = ZERO::insTree (link (t1, t2, t3), ts)

  fun insert (x, ts) = insTree (NODE (x, [], []), ts)
  fun merge (ts1, []) = ts1
    | merge ([], ts2) = ts2
    | merge (TWO (t1, t2)::ts1, TWO (t3, t4)::ts2) =
    ONE t1::insTree (link (t2, t3, t4), merge (ts1, ts2))
    | merge (ONE t1::ts1, TWO (t2, t3)::ts2) =
    ZERO::insTree (link (t1, t2, t3), merge (ts1, ts2))
    | merge (TWO (t1, t2)::ts1, ONE t3::ts) =
    ZERO::insTree (link (t1, t2, t3), merge (ts1, ts2))
    | merge (ONE t1::ts1, ONE t2::ts2) = TWO (t1, t2)::merge (ts1, ts2)
    | merge (ZERO::ts1, t::ts2) = t::merge (ts1, ts2)
    | merge (t::ts1, ZERO::ts2) = t::merge (ts1, ts2)

  fun removeMinTree [] = raise EMPTY
    | removeMinTree [ONE t] = (t, [])
    | removeMinTree [TWO (t1, t2)] =
    if Elem.leq (root t1, root t2) then (t1, ONE t2) else (t2, ONE t1)
    | removeMinTree (ZERO::ts) =
    let val (t', ts') = removeMinTree ts in (t', ZERO::ts') end
    | removeMinTree (ONE t::ts) =
    let val (t', ts') = removeMinTree ts
    in if Elem.leq (t, t') then (t, ZERO::ts) else (t', ONE t::ts') end
    | removeMinDigit ((t as TWO (t1, t2))::ts) =
    let
      val (t', ts') = removeMinTree ts
      val (t1', t2') = if Elem.leq (t1, t2) then (t1, t2) else (t2, t1)
    in if Elem.leq (t1', t') then (t1', ONE t2'::ts) else (t', t::ts') end
  fun toHeap ([], [], ts) = ts
    | toHeap (t1::ts1, t2::ts2, ts) = toHeap (ts1, ts2, TWO (t1, t2)::ts)

  fun findMin ts = let val (t, _) = removeMinTree ts in root t end
  fun deleteMin ts =
    let val (NODE (_, x, ts1, ts2), ts3) = removeMinTree ts
    in merge (toHeap (ts1, ts2, empty), ts3) end
end

(* Exercise 9.18 *)
structure ZeroLessQuaternaryRandomAccessList : RANDOMACCESSLIST =
struct
  datatype 'a Tree = LEAF of 'a | NODE of 'a Tree vector
  type 'a RList = 'a Tree vector list

  val empty = []
  fun isEmpty vs = null vs

  fun consTree (t, []) = [#[t]]
    | consTree (t, v::vs) =
    if Vector.length v = 4 then #[t]::consTree (NODE v, vs)
    else Vector.concat ([#[t], v])::vs
  fun unconsTree [] = raise EMPTY
    | unconsTree (v::vs) =
    if Vector.length v = 1
    then let (t, vs') = unconsTree vs in (Vector.sub (v, 0), #[t]::vs) end
    else (Vector.sub (v, 0), Vector.extract (v, 1, NONE)::vs)

  fun cons (x, vs) = consTree (LEAF x, ts)
  fun head [] = raise EMPTY
    | head (v::vs) = Vector.sub (v, 0)
  fun tail vs = let val (_, vs') = unconsTree vs in vs' end

  fun lookupVec (v, i) = let (NODE v') = Vector.sub (v, i) in v' end
  fun lookupTree (1, i, v) = let val (LEAF x) = Vector.sub (v, i) in x end
    | lookupTree (w, i, v) =
    if i < w then lookupTree (w div 4, i, lookupVec (v, 0))
    else if i < 2 * w then lookupTree (w div 4, i - w, lookupVec (v, 1))
    else if i < 3 * w then lookupTree (w div 4, i - 2 * w, lookupVec (v, 2))
    else lookupTree (w div 4, i - 3 * w, lookupVec (v, 3))
  fun updateVec (v, i, x) =
    Vector.mapi (fn (j, y) => if j = i then x else y) (v, 0, NONE)
  fun updateTree (1, i, y, v) = Vector.update (v, i, x)
    | updateTree (w, i, y, v) =
    if i < w
    then updateVec (v, 0, updateTree (w div 4, i, lookupVec (v, 0)))
    if i < 2 * w
    then updateVec (v, 1, updateTree (w div 4, i - w, lookupVec (v, 1)))
    if i < 3 * w
    then updateVec (v, 2, updateTree (w div 4, i - 2 * w, lookupVec (v, 2)))
    else updateVec (v, 3, updateTree (w div 4, i - 3 * w, lookupVec (v, 3)))

  fun lookup (i, vs) =
    let
      fun aux (w, i, []) = raise SUBSCRIPT
    | fun aux (w, i, v::vs) =
    if i < w * Vector.length v then lookupTree (w, i, v)
    else lookup (4 * w, i - w * Vector.length v, vs)
    in aux (1, i, vs) end
  fun update (i, y, vs) =
    let
      fun aux (w, i, y, []) = raise SUBSCRIPT
    | fun aux (w, i, y, v::vs) =
    if i < w * Vector.length v then updateTree (w, i, y, v)::vs
    else v::update (4 * w, i - w * Vector.length v, y, vs)
    in aux (1, i, y, vs) end
end

