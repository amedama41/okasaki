(** 7.2 Real Time Queue **)

(* Exercise 7.1 *)
structure BankersQueue' : QUEUE =
struct
  type 'a Queue = int * 'a Stream * int * 'a Stream

  val empty = (0, $ NIL, 0, $ NIL)
  fun isEmpty (lenf, _, _, _) = (lenf = 0)

  fun rotate ($ NIL, $ CONS (y, _), a) = $ CONS (y, a)
    | rotate ($ CONS (x, xs), $ CONS (y, ys), a) =
    $ CONS (x, rotate (xs, ys, $ CONS (y, a)))

  fun check (q as (lenf, f, lenr, r)) =
    if lenr <= lenf then q else (lenf + lenr, rotate (f, r, $ NIL), 0, $ NIL)

  fun snoc ((lenf, f, lenr, r), x) = check (lenf, f, lenr + 1, $ CONS (x, r))

  fun head (lenf, $ NIL, lenr, r) = raise EMPTY
    | head (lenf, $ CONS (x, f), lenr, r) = x
  fun tail (lenf, $ NIL, lenr, r) = raise EMPTY
    | tail (lenf, $ CONS (x, f), lenr, r) = check (lenf - 1, f, lenr, r)

  (** One rotate enable to exist unless f is NIL. Then the lifetime of one
    * rotate is f's head to f's last, where f is the one when rotate is created.
    * Because f grows only back, lifetimes of existing rotate overlap on f's
    * front. In addition, rotates created later are located in front of f than
    * ones created earlier.
    * Given that k rotates exists in a lifetime m, the length n of queue is at
    * least,
    *   n = 2m + 2 * 2m + 2^2 * 2m + 2^(k - 1) * 2m
    *     = 2m * sum_(i=1)^(k){2^(i-1)}
    *     = 2m * (2^k - 1).
    * Given a lifetime m',
    *   n >= 2m' * (2^k - 1)
    *   log(n/2m' + 1) >= k.
    * Therefore, the length of rotate's chain is also at most O(log(n)).
    *
    * *)
end

