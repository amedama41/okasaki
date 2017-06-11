(** 3.1 Leftist Heap **)

signature HEAP =
sig
  structure Elem : ORDERED

  type Heap

  val empty : Heap
  val isEmpty : Heap -> bool

  val insert : Elem.T * Heap -> Heap
  val merge: Heap * Heap -> Heap

  val findMin : Heap -> Elem.T
  val deleteMin : Heap -> Heap
end

(* Exercise 3.1 *)
(** First, we prove "If a heap has rank r, it contains at least 2^r - 1 node".
  * x has rank r, L(x) is left sub tree, R(x) is right sub tree.
  * r = rank(R(x)) + 1 by the definition,
  * r' >= r  =>  N(r') >= N(r) by N(r) = N(r'') + N(r-1) and N(r'') >= 0,
  * rank(L(x)) >= rank(R(x)) by the definition,
  * then N(rank(L(x))) >= N(rank(R(x)),
  * then N(r) >= N(rank(L(x))) + N(rank(R(x))) + 1
  *     >= 2N(rank(R(x))) + 1 = 2N(r-1) + 1.
  * Then N(r) = 2^r - 1.
  *
  * x has n nodes and rank r, then
  *     n >= 2^r - 1  => log(n + 1) >= r.
  **)

functor LeftistHeap (Element : ORDERED) : HEAP =
struct
  structure Elem = Element

  datatype Heap = E | T of int * Elem.T * Heap * Heap

  fun rank E = 0
    | rank T (r, _, _, _) = r
  fun makeT (x, a, b) =
    if rank a >= rank b then T (rank b + 1, x, a, b)
    else T (rank a + 1, x, b, a)

  val empty = E
  fun isEmpty E = true | isEmpty _ = false

  fun merge (h, E) = h
    | merge (E, h) = h
    | merge (h1 as T (_, x, a1, b1), h2 as T (_, y, a2, b2)) =
    if Elem.leq (x, y) then makeT (x, a1, merge (b1, h2))
    else makeT (y, a2, merge (h1, b2))
  fun insert (x, h) = merge (T (1, x, E, E), h)

  fun findMin E = raise EMPTY
    | findMin T (_, x, _, _) = x
  fun deleteMin E = raise EMPTY
    | deleteMin T (_, _, a, b) = merge (a, b)

(* Exercise 3.2 *)
  fun insert' (x, E) = T (1, x, E, E)
    | insert' (x, h as T (r, y, a, b)) =
    if Elem.leq (x, y) then T (1, x, h, E)
    else makeT (y, a, insert' (x, b))

(* Exercise 3.3 *)
  fun fromList xs =
    let
      fun mergeList (h::[], []) = h
        | mergeList (hs, []) = mergeList ([], hs)
        | mergeList (hs, x::[]) = x::hs
        | mergeList (hs, x1::x2::xs) = mergeList (merge (x1, x2)::hs, xs)
      fun toTreeList [] = E::[]
        | toTreeList x::xs = T (1, x, E, E)::toTreeList (xs)
    in mergeList  ([], toTreeList (xs))
    end
    (** The complexity of toTreeList is O(n).
      * The first mergeList call takes at most n/2 + 1 time.
      * The second takes at most n/4 + 1 time.
      * The last takes n/2^log(n) + 1 time.
      * Then the total time is
      *     (n/2 + 1) + (n/4 + 1) + ... + n/2^log(n) + 1
      *     <= sum^log(n)_{x=0}(n/2 * (1/2)^x + 1) = n + log(n) <= 2n.
      **)
end

(* Exercise 3.4 *)
(** First, we prove "If a heap has rank r, it contains at least 2^r - 1 node".
  * When r = 0, it is true.
  * Hypothesize true. A heap x has rank r + 1 and rank(x) = rank(R(x)) + 1,
  * then |R(x)| >= 2^r - 1.
  * By definition, |L(x)| >= |R(x)|, so |x| >= 2|R(x)| >= 2^(r+1) - 1.
  * The remain is same as Exercise 3.1.
  **)
functor WeightBasedLeftistHeap (Element : ORDERED) : HEAP =
struct
  structure Elem = Element

  datatype Heap = E | T of int * Elem.T * Heap * Heap

  fun weight E = 0
    | weight T (r, _, _, _) = r
  fun makeT (x, a, b) =
    if weight a >= weight b then T (weight a + weight b + 1, x, a, b)
    else T (weight a + weight b + 1, x, b, a)

  val empty = E
  fun isEmpty E = true | isEmpty _ = false

  fun merge (h, E) = h
    | merge (E, h) = h
    | merge (h1 as T (_, x, a1, b1), h2 as T (_, y, a2, b2)) =
    if Elem.leq (x, y) then makeT (x, a1, merge (b1, h2))
    else makeT (y, a2, merge (h1, b2))
  fun insert (x, h) = merge (T (1, x, E, E), h)

  fun findMin E = raise EMPTY
    | findMin T (_, x, _, _) = x
  fun deleteMin E = raise EMPTY
    | deleteMin T (_, _, a, b) = merge (a, b)

  fun merge' (h, E) = h
    | merge' (E, h) = h
    | merge' (h1 as T (w1, x, a1, b1), h2 as T (w2, y, a2, b2)) =
    if Elem.leq (x, y) then
      if weight a1 >= weight b1 + w2 then T (w1 + w2, x, a1, merge' (b1, h2))
      else T (w1 + w2, x, merge' (b1, h2), a1)
    else
      if weight a2 >= w1 + weight b2 then T (w1 + w2, y, a2, merge' (h1, b2))
      else T (w1 + w2, y, merge' (h1, b2), a2)

  (** makeT needs the result of merge to calculate weight, by contrast merge'
    * can calculate weight without merge' sub-call. Then the evaluation of
    * merge' sub-call is enable to be delayed.
    * In concurrent system, we can merge multiple heaps in the way as pipeline.
    **)
end

(** 3.2 Binomial Heap **)

functor BinomialHeap (Element : ORDERED) : HEAP =
struct
  structure Elem = Element

  datatype Tree = NODE of int * Elem.T * Tree list
  type Heap = Tree list

  val empty = []
  fun isEmpty ts = null ts

  fun rank (NODE (r, x, c)) = r
  fun root (NODE (r, x, c)) = x
  fun link (t1 as NODE (r, x1, c1), t2 as NODE (_, x2, c2)) =
    if Elem.leq (x1, x2) then NODE (r + 1, x1, t2::c1)
    else NODE (r + 1, x2, t1::c2)
  fun insTree (t, []) = [t]
    | insTree (t, ts as t'::ts') =
    if rank t < rank t' then t::ts else insTree (link (t t'), ts')

  fun insert (x, ts) = insTree (NODE (0, x, []), ts)
  fun merge (ts1, []) = ts1
    | merge ([], ts2) = ts2
    | merge (ts1 as t1::ts1', ts2 as t2::ts2') =
    if rank t1 < rank t2 then t1::merge (ts1', ts2)
    else if rank t2 < rank t1 then t2::merge (ts2', ts1)
    else insTree (link (t1, t2), merge (ts1', ts2'))

  fun removeMinTree [] = raise EMPTY
    | removeMinTree [t] = (t, [])
    | removeMinTree [t::ts] =
    let val (t', ts) = removeMinTree ts
    in if Elem.leq (root t, root t') then (t, ts) else (t', t::ts) end

  fun findMin ts = let val (t, _) = removeMinTree ts in root t end
  fun deleteMin ts = let val (NODE (_, x, ts1), ts2) = removeMinTree ts
  in merge (rev ts1, ts2) end

(* Exercise 3.5 *)
  fun findMin' [] = raise EMPTY
    | findMin' [t] = root t
    | findMin' [t::ts] =
    if Elem.leq (root t, findMin' ts) then root t else findMin' ts

end

(* Exercise 3.6 *)
functor BinomialHeap2 (Element : ORDERED) : HEAP =
struct
  structure Elem = Element

  datatype Tree = NODE of Elem.T * Tree list
  type HEAP = (int * Tree) list

  val empty = []
  fun isEmpty ts = null ts

  fun root (_, (NODE (x, c))) = x
  fun link (t1 as NODE (x1, c1), t2 as NODE (x2, c2)) =
    (* t1 and t2 must have same rank *)
    if Elem.leq (x1, x2) then NODE (x1, t2::c1) else NODE (x2, t1::c2)
  fun insHeap (t, []) = [t]
    | insHeap ((r1, t1), ts as (r2, t2)::ts') =
    (* r1 must not be greater than r2 *)
    if r1 < r2 then (r1, t1)::ts
    else insHeap ((r1 + 1, link (t1, t2)), ts')

  fun insert (x, ts) = insHeap ((0, NODE (x, [])), ts)
  fun merge (ts1, []) = ts1
    | merge ([], ts2) = ts2
    | merge (ts1 as (r1, t1)::ts1', ts2 as (r2, t2)::ts2') =
    if r1 < r2 then (r1, t1)::merge (ts1', ts2)
    else if r2 < r1 then (r2, t2)::merge (ts2', ts1)
    else insHeap ((r1 + 1, link (t1, t2)), merge (ts1', ts2'))

  fun removeMinTree [] = raise EMPTY
    | removeMinTree [t] = (t, [])
    | removeMinTree [t::ts] =
    let val (t', ts') = removeMinTree ts
    in if Elem.leq (root t, root t') then (t, ts) else (t', t::ts') end

  fun findMin ts = let val (t, _) = removeMinTree ts in root t end
  fun deleteMin ts =
    let
      fun toHeap (r, []) = []
        | toHeap (r, n::ns) = (r, n)::toHeap (r - 1, ns)
      val ((r, NODE (_, ts1)), ts2) = removeMinTree ts
    in merge (toHeap (r - 1, rev ts1), ts2) end
end

(* Exercise 3.7 *)
functor ExplicitHeap (H : HEAP) : HEAP =
struct
  structure Elem = H.Elem
  datatype Heap = E | NE of Elem.T * H.Heap

  val empty = E
  fun isEmpty E = true | isEmpty _ = false

  fun insert (x, E) = (x, H.insert (x, []))
    | insert (x, NE (y, h)) =
    if Elem.leq (x, y) then (x, H.insert (x, h)) else (y, H.insert (x, h))
    (* O(log(n)) if H.insert is O(log(n)) *)

  fun merge (h1, E) = h1
    | merge (E, h2) = h2
    | merge (NE (x1, h1), NE (x2, h2)) =
    if Elem.leq (x1, x2) then (x1, H.merge (h1, h2))
    else (x2, H.merge (h1, h2))
    (* O(log(n)) if H.merge is O(log(n)) *)

  fun findMin E = raise EMPTY
    | findMin NE (x, _) = x
    (* O(1) *)

  fun deleteMin NE (_, h) =
    let
      val h' = H.deleteMin h in (H.findMin h', h') end
      (* O(log(n)) if H.deleteMin and H.findMin is O(log(n)) *)
end

(** 3.3 Red-Black Tree **)

(* Exercise 3.8 *)
(** d is the shortest path length.
  * Then n >= d^2 - 1 => [log(n + 1)] >= d
  * By the definition, the length of max path is at most 2*d = 2[log(n + 1)].
  * *)

functor RedBlackSet (Element : ORDERED) : SET =
struct
  type Elem = Element.T

  datatype Color = R | B
  datatype Tree = E | T of Color * Tree * Elem * Tree
  type Set = Tree

  val empty = E

  fun member (x, E) = false
    | member (x, (_, a, y, b)) =
    if Elem.lt (x, y) then member (x, a)
    else if Elem.lt (y, x) then member (x, b)
    else true

  fun balance (B,T(R,T(R,a,x,b),y,c),z,d) = T(R,T(B,a,x,b),y,T(B,c,z,d))
    | balance (B,T(R,a,x,T(R,b,y,c)),z,d) = T(R,T(B,a,x,b),y,T(B,c,z,d))
    | balance (B,a,x,T(R,T(R,b,y,c),z,d)) = T(R,T(B,a,x,b),y,T(B,c,z,d))
    | balance (B,a,x,T(R,b,y,T(R,c,z,d))) = T(R,T(B,a,x,b),y,T(B,c,z,d))
    | balance body = T body

  fun insert (x, s) =
    let
      fun ins E = T (B, E, x, E)
        | ins (s as T (color, a, y, b)) =
        if Elem.lt (x, y) then balance (color, ins a, y, b)
        else if Elem.lt (y, x) then balance (color, a, y, ins b)
        else s
      val T (_, a, y, b) = ins s
      in T (B, a, y, b)
    end

(* Exercise 3.9 *)
  fun fromOrdList xs =
    (** Use the list of (color, value, left sub-tree) in order to avoid
      * to search insertion node. This list represents the right spine
      * of the Red-Black tree from bottom to top.
      * *)
    let
      fun balance' ((R, v1, t1)::(R, v2, t2)::(B, v3, t3)::xs) =
        (B, v1, t1)::(balance' ((R, v2, T (B, t3, v3, t2))::xs))
        | balance' xs = xs
      fun ins (ts, []) = ts
        | ins (ts, x::xs) = ins (balance' ((R, x, E)::ts), xs)
      fun toTree (t, []) = t
        | toTree (t, (color, v, t')::ts) = toTree (T (color, t', v, t), ts)
    in toTree (E, ins ([], ts))
    end
    (** The amortized cost of ins is O(1), and ins is called n times.
      * The complexity of toTree is O(log(n)).
      * The total complexity is n*O(1) + O(log(n)) = O(n).
      * *)
end

