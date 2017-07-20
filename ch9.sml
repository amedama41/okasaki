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

