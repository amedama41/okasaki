(** 8.1 Batched Rebuilding **)

(* Exercise 8.1 *)
functor BatchedRedBlackSet (Element : ORDERED) : SET =
struct
  type Elem = Element.T

  datatype Color = R | B
  datatype Tree = E | T of Color * Tree * bool * Elem * Tree
  type Set = int * int * Tree

  val empty = (0, 0, E)

  fun member (x, (_, _, s)) =
    let
      fun mem (E) = false
        | mem (T (_, a, _, y, b)) =
        if Elem.lt (x, y) then mem (x, a)
        else if Elem.lt (y, x) then mem (x, b)
        else true
    in mem s end

  fun balance (B,T(R,T(R,a,xl,x,b),yl,y,c),zl,z,d) =
    T(R,T(B,a,xl,x,b),yl,y,T(B,c,zl,z,d))
    | balance (B,T(R,a,xl,x,T(R,b,yl,y,c)),zl,z,d)
    = T(R,T(B,a,xl,x,b),yl,y,T(B,c,zl,z,d))
    | balance (B,a,xl,x,T(R,T(R,b,yl,y,c),zl,z,d))
    = T(R,T(B,a,xl,x,b),yl,y,T(B,c,zl,z,d))
    | balance (B,a,xl,x,T(R,b,yl,y,T(R,c,zl,z,d)))
    = T(R,T(B,a,xl,x,b),yl,y,T(B,c,zl,z,d))
    | balance body = T body

  fun insert (x, (i, d, s)) =
    let
      fun ins E = T (B, true, E, x, E)
        | ins (s as T (color, l, a, y, b)) =
        if Elem.lt (x, y) then balance (color, l, ins a, y, b)
        else if Elem.lt (y, x) then balance (color, l, a, y, ins b)
        else s
      val T (_, a, yl, y, b) = ins s
    in (i + 1, d, T (B, true, a, yl, y, b)) end

  fun rebuild (ts) =
    let
      fun balance' ((R, v1, t1)::(R, v2, t2)::(B, v3, t3)::xs) =
        (B, v1, t1)::(balance' ((R, v2, T (B, t3, true, v3, t2))::xs))
        | balance' xs = xs
      fun ins (n, ts, E) = (n, ts)
        | ins (n, ts, T (_, a, xl, x, b)) =
        let val (n', ts') = ins (n, ts, a)
        in
          if xl then ins (n' + 1, balance' (R, x, E)::ts', b)
          else ins (n', ts', b) end
      fun toTree (t, []) = t
        | toTree (t, (color, v, t')::ts) =
        toTree (T (color, t', true, v, t), ts)
      val (n, ts') = ins (0, [], ts)
    in (n, 0, toTree (E, ts')) end

  fun delete (x, (i, d, s)) =
    let
      fun del E = E
        | del (T (c, a, yl, y, b)) =
        if Elem.lt (x, y) then T (c, del a, yl, y, b)
        else if Elem.lt (y, x) then T (c, a, yl, y, del b)
        else T (c, a, false, y, b)
      val s' = del s
    in
      if d + 1 >= i - 1 then rebuild s' else (i - 1, d + 1, s')
    end
end

(** 8.2 Global Rebuilding **)

structure HoodMelvileQueue : QUEUE =
struct
  datatype 'a RotationState =
      IDLE
    | REVERSING of int * 'a list * 'a list * 'a list * 'a list
    | APPENDING of int * 'a list * 'a list
    | DONE of 'a list

  type 'a Queue = int * 'a list * 'a RotationState * int * 'a list

  val empty = (0, [], IDLE, 0, [])
  fun isEmpty (lenf, f, state, lenr, r) = (lenf = 0)

  fun exec (REVERSING (ok, x::f, f', y::r, r')) =
    REVERSING (ok, f, x::f', r, y::r')
    | exec (REVERSING (ok, [], f', [y], r')) = APPENDING (ok, f', y::r')
    | exec (APPENDING (0, f', r')) = DONE r'
    | exec (APPENDING (ok, x::f', r')) = APPENDING (ok - 1, f', x::r')
    | exec state = state

  fun invalidate (REVERSING (ok, f, f', r, r')) =
    REVERSING (ok - 1, f, f', r, r')
    | invalidate (APPENDING (0, f', x::r')) = DONE r'
    | invalidate (APPENDING (ok, f', r')) = APPENDING (ok - 1, f', r')
    | invalidate state = state

  fun exec2 (lenf, f, state, lenr, r) =
    case exec (exec state) of
         DONE newf => (lenf, newf, IDLE, lenr, r)
       | newstate => (lenf, f, newstate, lenr, r)

  fun check (q as (lenf, f, state, lenr, r)) =
    if lenr <= lenf then exec2 q
    else let val newstate = REVERSING (0, f, [], r, [])
         in exec2 (lenf + lenr, f, newstate, 0, []) end

  fun snoc ((lenf, f, state, lenr, r), x) =
    check (lenf, f, state, lenr + 1, x::r)
  fun head (lenf, [], state, lenr, r) = raise EMPTY
    | head (lenf, x::f, state, lenr, r) = x
  fun tail (lenf, [], state, lenr, r) = raise EMPTY
    | tail (lenf, x::f, state, lenr, r) =
    check (lenf - 1, f, invalidate state, lenr, r)
end

(* Exercise 8.2 *)
(** Because a tail reduce APPENDING steps by one, a tail can decrease rotation
  * steps by 2 even if a tail calls only one exec.
  * When creating a rotation state, because two execs are called, the remaining
  * steps is 2m. Therefore, it is sufficient that snoc and tails calls at least
  * one exec.
  * *)
structure HoodMelvileQueue2 : QUEUE =
struct
  datatype 'a RotationState =
      IDLE
    | REVERSING of int * 'a list * 'a list * 'a list * 'a list
    | APPENDING of int * 'a list * 'a list
    | DONE of 'a list

  type 'a Queue = int * 'a list * 'a RotationState * int * 'a list

  val empty = (0, [], IDLE, 0, [])
  fun isEmpty (lenf, f, state, lenr, r) = (lenf = 0)

  fun exec (REVERSING (ok, x::f, f', y::r, r')) =
    REVERSING (ok + 1, f, x::f', r, y::r')
    | exec (REVERSING (ok, [], f', [y], r')) = APPENDING (ok, f', y::r')
    | exec (APPENDING (0, f', r')) = DONE r'
    | exec (APPENDING (ok, x::f', r')) = APPENDING (ok - 1, f', x::r')
    | exec state = state

  fun invalidate (REVERSING (ok, f, f', r, r')) =
    REVERSING (ok - 1, f, f', r, r')
    | invalidate (APPENDING (0, f', x::r')) = DONE r'
    | invalidate (APPENDING (ok, f', r')) = APPENDING (ok - 1, f', r')
    | invalidate state = state

  fun exec2 (lenf, f, state, lenr, r) =
    case exec state of
         DONE newf => (lenf, newf, IDLE, lenr, r)
       | newstate => (lenf, f, newstate, lenr, r)

  fun check (q as (lenf, f, state, lenr, r)) =
    if lenr <= lenf then exec2 q
    else let val newstate = REVERSING (0, f, [], r, [])
         in exec2 (exec2 (lenf + lenr, f, newstate, 0, [])) end

  fun snoc ((lenf, f, state, lenr, r), x) =
    check (lenf, f, state, lenr + 1, x::r)
  fun head (lenf, [], state, lenr, r) = raise EMPTY
    | head (lenf, x::f, state, lenr, r) = x
  fun tail (lenf, [], state, lenr, r) = raise EMPTY
    | tail (lenf, x::f, state, lenr, r) =
    check (lenf - 1, f, invalidate state, lenr, r)
end

(* Exercise 8.3 *)
structure HoodMelvileQueue3 : QUEUE =
struct
  datatype 'a RotationState =
      IDLE
    | REVERSING of int * 'a list * 'a list * 'a list * 'a list
    | APPENDING of int * 'a list * 'a list
    | DONE of int * 'a list

  type 'a Queue = int * 'a list * 'a RotationState * 'a list

  val empty = (0, [], IDLE, [])
  fun isEmpty (diff, [], state, r) = true | isEmpty _ = false

  fun exec (REVERSING (ok, x::f, f', y::r, r')) =
    (1, REVERSING (ok + 1, f, x::f', r, y::r'))
    | exec (REVERSING (ok, [], f', [y], r')) = (1, APPENDING (ok, f', y::r'))
    | exec (APPENDING (0, f', r')) = (0, DONE r')
    | exec (APPENDING (ok, x::f', r')) = (1, APPENDING (ok - 1, f', x::r'))
    | exec state = (0, state)

  fun invalidate (REVERSING (ok, f, f', r, r')) =
    REVERSING (ok - 1, f, f', r, r')
    | invalidate (APPENDING (0, f', x::r')) = DONE r'
    | invalidate (APPENDING (ok, f', r')) = APPENDING (ok - 1, f', r')
    | invalidate state = state

  fun exec2 (diff, f, state, r) =
    case exec state of
         (0, DONE newf) => (diff, newf, IDLE, r)
       | (d, newstate) => (diff + d, f, newstate, r)

  fun check (q as (diff, f, state, r)) =
    if diff >= 0 then exec2 q
    else let val newstate = REVERSING (0, f, [], r, [])
         in exec2 (exec2 (0, f, newstate, 0, [])) end

  fun snoc ((diff, f, state, r), x) = check (diff - 1, f, state, x::r)
  fun head (diff, [], state, r) = raise EMPTY
    | head (diff, x::f, state, r) = x
  fun tail (diff, [], state, r) = raise EMPTY
    | tail (diff, x::f, state, r) = check (diff - 1, f, invalidate state, r)
end

(** 8.4 Deque **)
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

(* Exercise 8.4 *)
functor QueueWithCons (Q : QUEUE) : QUEUE =
struct
  type 'a Queue = 'a list * 'a Q.Queue

  val empty = ([], Q.empty)
  fun isEmpty ([], q) = Q.isEmpty q | isEmpty _ = false

  fun cons (x, (xs, q)) = (x::xs, q)
  fun snoc ((xs, q), x) = (h, Q.snoc (q, x))
  fun head ([], q) = Q.head q
    | head (x::xs, q) = x
  fun tail ([], q) = Q.tail q
    | tail (x::xs, q) = (xs, q)
end

functor BankersDeque (val c : int) : DEQUE =
struct
  type 'a Queue = int * 'a Stream * int * 'a Stream

  val emtpy = (0, $ NIL, 0, $ NIL)
  fun isEmpty (lenf, f, lenr, r) = (lenf + lenr = 0)

  fun check (q as (lenf, f, lenr, r)) =
    if lenf > c * lenr + 1 then
      let
        val i = (lenf + lenr) div 2
        val j = lenf + lenr - i
        val f' = take (f, i)
        val r' = r' ++ reverse (drop (f, i))
      in (i, f', j, r')
    else if lenr > c * lenf + 1 then
      let
        val j = (lenf + lenr) div 2
        val i = lenf + lenr - i
        val r' = take (r, i)
        val f' = f' ++ reverse (drop (r, i))
      in (i, f', j, r')
    else q

  fun cons (x, (lenf, f, lenr, r)) = check (lenf + 1, $ CONS (x, f), lenr, r)
  fun head (lenf, $ NIL, lenr, $ NIL) = raise EMPTY
    | head (lenf, $ NIL, lenr, $ CONS (x, _)) = x
    | head (lenf, $ CONS (x, f'), lenr, r) = x
  fun tail (lenf, $ NIL, lenr, $ NIL) = raise EMPTY
    | tail (lenf, $ NIL, lenr, $ CONS (x, _)) = empty
    | tail (lenf, $ CONS (x, f'), lenr, r) = check (lenf - 1, f', lenr, r)

  fun snoc ((lenf, f, lenr, r), x) = check (lenf, f, lenr + 1, $ CONS (x, r))
  fun last (lenf, $ NIL, lenr, $ NIL) = raise EMPTY
    | last (lenf, $ CONS (x, _), lenr, $ NIL) = x
    | last (lenf, f, lenr, $ CONS (x, r')) = x
  fun init (lenf, $ NIL, lenr, $ NIL) = raise EMPTY
    | init (lenf, $ CONS (x, _), lenr, $ NIL) = empty
    | init (lenf, f, lenr, $ CONS (x, r')) = check (lenf, f, lenr - 1, r')
end

(* Exercise 8.5 *)
(** When |f| > |r|, cons decrements t. If cons repays 1 debt, the invariant is
  * sustained.
  *
  * tail decrements index i. If tail repays c + 1 debt, the invariant is
  * sustained.
  *
  * When cons causes rotation, that is |f| = c|r| + 1 before cons, the rotation
  * create one debt for each element in f', and one debt for each element in
  * first |r| elements in r', |f| + 1 = c|r| + 2 debts for |r|th element in r'.
  * Therefore d(i) = 1 for f', and d(i) = 1 (i < |r|) or c|r| + 2 (i = |r|) or
  * 0 (i > |r|) for r'. And, D(i) = i + 1 for f', D(i) = i + 1 (i < |r|) or
  * c|r| + |r| + 1 (i >= |r|) for r'. Then the invariant is sustained as long as
  * cons repays 1 debt for first elements in f' and r' respectively.
  *
  * When tail causes rotation, that is |r| = c|f| + 1 before tail, the rotation
  * create one debt for each element in r', and one debt for each element in
  * first f's |f| elements excluding first removed element, |r| = c|f| + 1 debts
  * for (|f| - 1)th element in f'. Therefore, d(i) = 1 (i < |f| - 1) or c|f| + 1
  * (i = |f| - 1) or 0 (i > |f| - 1) for f', and d(i) = 1 for r'. And, D(i) =
  * i + 1 (i < |f| - 1) or c|f| + |f| (i >= |f| - 1) for f', and D(i) = i + 1
  * for r'. Then the invariant is sustained as long as tail repays 1 debt for
  * first elements in f' and r' respectively, and c debts for (|f| - 1|)th
  * element in f'.
  *
  * This proof is not correct when c=2. However, if the invariant is changed
  * to min(ci + i, 2(cs + 1 - t)) and tail repays 2c + 2 debts, the new
  * invariant is sustained even if c=2.
  *
  * *)

(* Exercise 8.6 *)
(** When cons 22 times, then last 4 times, c=4 is faster than c=2.
  * In this case, 2 pairs of reverse and drop are forced, and each cost is
  * 1 and 6 respectively for c=4. While for c=2, 3 pairs are forced and each
  * cost is 1, 4, 8. So total cost when c=4 is 5 steps less than when c=2.
  *
  * But one more last, c=2 is faster than c=4. The cost when c=2 is as same as
  * before. When c=4, however, addition reverse and drop are forced. It results
  * in more 18 steps.
  *
  * *)

functor RealTimeDeque (val c : int) : DEQUE =
struct
  type 'a Queue = int * 'a Stream * 'a Stream * int * 'a Stream * 'a Stream

  val empty = (0, $ NIL, $ NIL, 0, $ NIL, $ NIL)
  fun isEmpty (lenf, f, sf, lenr, r, sr) = (lenf + lenr = 0)

  fun exec1 ($ CONS (x, s)) = s
    | exec1 s = s
  fun exec2 s = exec1 (exec1 s)

  fun rotateRev ($ NIL, r, a) = reverse r ++ a
    | rotateRev ($ CONS (x, f), r, a) =
    $ CONS (x, rotateRev (f, drop (c, r), reverse (take (c, r)) ++ a))
  fun rotateDrop (f, j, r) =
    if j < c then rotateRev (f, drop (j, r), $ NIL)
    else let val ($ CONS (x, f')) = f
         in $ CONS (x, rotateDrop (f', j - c, drop (c, r))) end

  fun check (q as (lenf, f, sf, lenr, r, sr)) =
    if lenf > c * lenr + 1 then
      let
        val i = (lenf + lenr) div 2
        val j = lenf + lenr - i
        val f' = take (f, i)
        val r' = rotateDrop (r, i, f)
      in (i, f', f', j, r', r') end
    else if lenr > c * lenf + 1 then
      let
        val j = (lenf + lenr) div 2
        val i = lenf + lenr - i
        val r' = take (j, r)
        val f' = rotateDrop (f, j, r)
      in (i, f', f', j, r', r') end
    else q

  fun cons (x, (lenf, f, sf, lenr, r, sr)) =
    check (lenf + 1, $ CONS (x, f), exec1 sf, lenr, r, exec1 sr)
  fun head (lenf, $ NIL, sf, lenr, $ NIL, sr) = raise EMPTY
    | head (lenf, $ NIL, sf, lenr, $ CONS (x, _), sr) = x
    | head (lenf, $ CONS (x, f'), sf, lenr, r, sr) = x
  fun tail (lenf, $ NIL, sf, lenr, $ NIL, sr) = raise EMPTY
    | tail (lenf, $ NIL, sf, lenr, $ CONS (x, _), sr) = empty
    | tail (lenf, $ CONS (x, f'), sf, lenr, r, sr) =
    check (lenf - 1, f', exec2 sf, lenr, r, exec2 sr)

  fun sonc ((lenf, f, sf, lenr, r, sr), x) =
    check (lenf, f, exec1 sf, lenr + 1, $ CONS (x, r), exec1 sr)
  fun last (lenf, $ NIL, sf, lenr, $ NIL, sr) = raise EMPTY
    | last (lenf, $ CONS (x, _), sf, lenr, $ NIL, sr) = x
    | last (lenf, f, sf, lenr, $ CONS (x, _), sr) = x
  fun init (lenf, $ NIL, sf, lenr, $ NIL, sr) = raise EMPTY
    | init (lenf, $ CONS (x, _), sf, lenr, $ NIL, sr) = empty
    | init (lenf, f, sf, lenr, $ CONS (x, r'), sr) =
    check (lenf, f, exec2 sf, lenr - 1, r', exec2 sr)
end

(* Exercise 8.7 *)
(** Let x the length of a stream f in rotateDrop/rotateRev. Hypothesize
  * x <= 2(cs + 1 - t) / c until first rotateRev is created, and
  * x <= 2(cs + 1 - t) / c + 1 since the rotateRev is created. When rotation
  * is occurred, x is |r| and 2(cs + 1 - t) >= (c - 1)|r| + 1. Then the
  * invariant holds.
  * When the first rotateRev is created, the length of the f is not changed but
  * the right hand side value is decreased by 1. Then by adding the right hand
  * size expression by 1, the invariant holds.
  * cons and tail may decrease the right hand value by 1 or 2 respectively, by
  * calling exec1 and exec2, the invariant holds.
  * When calling a operation which occurs the next rotation, x <= 1 and this
  * operation calls exec1 or exec2, then all suspensions are forced before the
  * next rotation (These suspensions exclude ones created by ++. Because the
  * chain length of ++ is at most 2, the cost of each operation is still
  * constant.
  *
  * *)

