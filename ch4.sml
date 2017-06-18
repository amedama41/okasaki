(** 4.1 $-notation **)

open Lazy

fun force ($ x) = x

fun lazy plus ($ m, $ n) = $ m + n

(** 4.2 Stream **)

signature STREAM =
sig
  datatype 'a StreamCell = NIL | CONS of 'a * 'a Stream
  withtype 'a Stream = 'a StreamCell susp

  val ++ : 'a Stream * 'a Stream -> 'a Stream
  val take : int * 'a Stream -> 'a Stream
  val drop : int * 'a Stream -> 'a Stream
  val reverse : 'a Stream -> 'a Stream
end

structure Stream : STREAM =
struct
  datatype 'a StreamCell = NIL | CONS of 'a * 'a Stream
  withtype 'a Stream = 'a StreamCell susp

  fun lazy ($ NIL) ++ t = t
         | ($ CONS (x, s)) ++ t = $ CONS (x, s ++ t)
  fun lazy take (0, s) = $ NIL
         | take (n, $ NIL) = $ NIL
         | take (n, $ CONS (x, s)) = $ CONS (x, take (n - 1, s))
  fun lazy drop' (0, s) = s
         | drop' (n, $ NIL) = $ NIL
         | drop' (n, $ CONS (_, s)) = drop' (n - 1, s)
  fun lazy drop (n, s) =
    let
      fun drop' (0, s) = s
        | drop' (n, $ NIL) = $ NIL
        | drop' (n, $ CONS (_, s)) = drop' (n - 1, s)
    in drop' (n, s) end
  fun lazy reverse s =
    let
      fun reverse' ($ NIL, r) = r
        | reverse' ($ CONS (x, s), r) = reverse' (s, $ CONS (x, r))
    in reverse' (s, $ NIL) end

end

(* Exercise 4.1 *)
(** drop' (n, s) = case (n, s) of (n, s) => force drop' (n-1, s)
  *     = drop' (n-1, s) = case (n-1, s) of (n-1, s) => force drop' (n-2, s)
  *     = ...
  *     = drop' (0, s)
  *     = force s
  * drop (n, s) = case (n, s) of (n, s) => force drop' (n, s)
  *     = force drop' (n-1, s) = ... = force drop' (0, s)
  *     = force s
  * *)

(* Exercise 4.2 *)
fun sort $ NIL = $ NIL
  | sort $ CONS (x, xs) =
  let
    fun lazy insert (x, $ NIL) = $ CONS (x, $ NIL)
           | insert (x, s as $ CONS (y, s'))
      if x < y then $ CONS (x, s) else $ CONS (y, insert (x, s'))
    in insert (x, sort xs) end
(** Each insert compare with only the first sorted list element y, and
  * comparison with the rest are delayed. When taking one element, the
  * insert is called at most n times. Then the time of taking k element
  * is O(kn).
  * *)

