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

