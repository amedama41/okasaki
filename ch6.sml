(** 6.1 Execution Traces and Logical Time **)

(* Exercise 6.1 *)
(** snoc (empty, 0)
  *  |  4
  *  V
  * snoc (a, 1) -> snoc (b, 2) -> snoc (d, 3)
  *  |  4           |  2              1
  *  V              V
  * tail b ------> c ++ d
  *  |  2           1
  *  V
  * tail c
  *     1
  *
  * *)

