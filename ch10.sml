(** 10.1 Structural Decomposition **)

(* Exercise 10.1 *)
(** fun update (0, e, ONE (x, ps)) = ONE (e, ps)
  *   | update (i, e, ONE (x, ps)) = cons (x, update (i - 1, e ZERO ps))
  *   | update (i, e, ZERO ps) =
  *   let val (x, y) = lookup (i div 2, ps)
  *       val p = if i mod 2 = 0 then (e, y) else (x, e)
  *   in ZERO (update i div 2, p, ps) end
  *
  * Let k = log(i + 1). The cost of update is
  *     k + (k - 1) + (k - 2) + ... + 1
  *     = k(k + 1)/2 = ((log(i + 1))^2 + log(i + 1)) / 2 = O((log(n))^2).
  * *)

