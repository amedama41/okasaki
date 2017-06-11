(** 2.1 List **)
signature STACK =
sig
  type 'a Stack

  val empty : 'a Stack
  val isEmpty : 'a Stack -> bool

  val cons : 'a * 'a Stack -> 'a Stack
  val head : 'a Stack -> 'a
  val tail : 'a Stack -> 'a Stack
end

structure List : STACK =
struct
  type 'a Stack = 'a List

  val empty = []
  fun isEmpty s = null s

  fun cons (x, s) = x :: s
  fun head s = hd s
  fun tail s = tl s
end

structure CustomStack : STACK =
struct
  datatype 'a Stack = NIL | CONS of 'a * 'a Stack

  val empty = NIL
  fun isEmpty NIL = true | isEmpty _ = false

  fun cons (x, s) = CONS (x, s)
  fun head NIL = raise EMPTY
    | head (CONS (x, s)) = x
  fun tail NIL = raise EMPTY
    | tail (CONS (x, s)) = s
end

fun xs ++ ys = if isEmpty xs then ys else cons (head xs, tail xs ++ ys)

fun update ([], i, y) = raise SUBSCRIPT
  | update (x :: xs, 0, y) = y :: xs
  | update (x :: xs, i, y) = x :: update (xs, i - 1, y)

(* Exercise 2.1 *)
fun suffixes [] = [[]]
  | suffixes xs as _::xs' = xs::suffixes xs'
(* Time complexity of each call is O(1) and the number of call is n,
** then total time complexity is O(n).
** The length of the result list is n and each element of the list
** shares the list with the next element.
** Then each element needs O(1) space complexity.
** Total space complexity is O(n) + n * O(1) = 2O(n) = O(n).
*)

(** 2.2 binary tree **)
signature SET =
sig
  type Elem
  type Set

  val empty : Set
  val insert : Elem * Set -> Set
  val member : Elem * Set -> bool
end

signature ORDERED =
sig
  type T

  val eq : T * T -> bool
  val lt : T * T -> bool
  val leq : T * T -> bool
end

functor UnbalancedSet (Element : ORDERED) : SET =
struct
  type Elem = Element.T
  datatype Tree = E | T of Tree * Elem * Tree
  type Set = Tree

  val empty = E

  fun member (x, E) = false
    | member (x, T (a, y, b)) =
    if Element.lt (x, y) then member (x, a)
    else if Element.lt (y, x) then member (x, b)
    else true

  fun insert (x, E) = T (E, x, E)
    | insert (x, s as T (a, y, b)) =
    if Element.lt (x, y) then T (insert (x, a), y, b)
    else if Element.lt (y, x) then T (a, y, insert (x, b))
    else s

(* Exercise 2.2 *)
  fun member2 (x, E) = false
    | member2 (x, s as T (_, y, _)) =
    let
      fun aux (c, E) = (x = c)
        | aux (c, T (a, y, b)) =
        if Element.lt (x, y) then aux (c, a) else aux (y, b)
    in aux (y, s) end

(* Exercise 2.3 *)
  exception SAMEVALUE
  fun insert2 (x, s) =
    let
      fun aux (E) = T (E, x, E)
        | aux (T (a, y, b)) =
        if Element.lt (x, y) then T (aux a, y, b)
        else if Element.lt (y, x) then T (a, y, aux b)
        else raise SAMEVALUE
    in aux (s) handle SAMEVALUE => s end

(* Exercise 2.4 *)
  fun insert3 (x, E) = T (E, x, E)
    | insert3 (x, s as T (_, y, _)) =
    let
      fun aux (c, E) = if c = x then raise SAMEVALUE else T (E, x, E)
        | aux (c, T (a, y, b)) =
        if Element.lt (x, y) then T (aux (c, a), y, b)
        else T (a, y, aux (y, b))
    in aux (y, s) handle SAMEVALUE => s end

(* Exercise 2.5 *)
  fun complete (x, 0) = E
    | complete (x, d) =
    let
      val t = complete (x, d - 1)
    in T (t, x, t) end
    (** The complexity of each call is O(1) and there are d calls, then
      * the total complexity is O(d). **)

  fun create (x, 0) = E
    | create (x, n) =
    let
      fun create2 (x, m) = (create (x, m), create (x, m + 1))
    in
      if (n - 1) mod 2 = 0 then
        let
          val t = create (x, (n - 1) div 2) in T (t, x, t) end
      else
        let
          val (l, r) = create2 (x, (n - 1) div 2) in T (l, x, r) end
    end
    (** The complexity of each call is O(1). and there are log(n) calls, then
      * the total complexity is O(log(n)). **)

end

signature FINITEMAP =
sig
  type Key
  type 'a Map

  val empty : 'a Map
  val bind : Key * 'a * 'a Map -> 'a Map
  val lookup : Key * 'a Map -> 'a
end

(* Exercise 2.6 *)
exception NOTFOUND
functor UnbalancedFiniteMap (Element : ORDERED) : FINITEMAP =
struct
  type Key = Element.T
  datatype 'a Tree = E | T of Tree * Key * 'a * Tree
  type 'a Map = 'a Tree

  val empty = E

  fun bind (k, v, E) = T (E, k, v, E)
    | bind (k, v, t as T (a, k', v', b)) =
    if Element.lt (k, k') then T (bind (k, v, a), k', v', b)
    else if Element.lt (k', k) then T (a, k', v', bind (k, v, b))
    else t

  fun lookup (k, E) = raise NOTFOUND
    | member (k, T (a, k', v', b)) =
    if Element.lt (k, k') then member (k, a)
    else if Element.lt (k', k) then member (k, b)
    else v'
end

