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

