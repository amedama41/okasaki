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

(** 6.3 Banker's Method **)

structure BankersQueue : QUEUE =
struct
  type 'a Queue = int * 'a Stream * int * 'a Stream

  val empty = (0, $ NIL, 0, $ NIL)
  fun isEmpty (lenf, _, _, _) = (lenf = 0)

  fun check (q as (lenf, f, lenr, r)) =
    if lenr <= lenf then q else (lenf + lenr, f ++ reverse r, 0 $ NIL)

  fun snoc ((lenf, f, lenr, r), x) = check (lenf, f, lenr + 1, $ CONS (x, r))

  fun head (lenf, $ NIL, lenr, r) = raise EMPTY
    | head (lenf, $ CONS (x, f), lenr, r) = x
  fun tail (lenf, $ NIL, lenr, r) = raise EMPTY
    | tail (lenf, $ CONS (x, f), lenr, r) = check (lenf - 1, f, lenr, r)
end

(* Exercise 6.2 *)
(** Hypothesize D(i) <= min(3i, 2|f| - |r|).
  *
  * snoc repays 1 dept. tail repays 3 dept.
  * snoc decrements 2|f| - |r| by 1. If snoc repays dept for first node for f,
  * the hypothesize holds.
  * tail decrements 3i by 3, and 2|f| - |r| by 2. If tail repays dept for first
  * three nodes, the hypothesize holds.
  * If snoc or tail calls reverse, |f| is m, and |r| is 2m + 1, then ++ create
  * m dept for first m nodes in f, and reverse create 2m dept for node m.
  * Then,
  *     d(i) = 1 (i < m) | 2m (i = m) | 0 (i > m)
  *     D(i) = i + 1 (i < m) | 3m + 1 (i >= m).
  * Because snoc or tail repays dept for at least first node in f, the
  * hypothesize holds.
  *
  *
  * When the invariant condition is |f| >= |r|, 1st, 3rd, 7th, 15th, 31th, 63th
  * snoc and 27 th tail call reverse, so reverse is called 7 times.
  * When the invariant condition is 2|f| >= |r|, 1st, 4th, 13th, 40th snocs and
  * 11th tail call reverse, so reverse is called 5 times.
  * Therefore, the number of reverse calls of the later implementation is less
  * than that of the former. While the average cost of reverse is bigger.
  * The later cost is 100 / 5 = 20, and the former is 100 / 7 = 14.28.
  *
  * *)

