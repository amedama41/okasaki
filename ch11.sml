(** 11.1 Queue and Deque **)

structure ImplicitQueue : QUEUE =
struct
  datatype 'a Digit = ZERO | ONE of 'a | TWO of 'a * 'a
  datatype 'a Queue = SHALLOW of 'a Digit
                    | DEEP of 'a Digit * ('a * 'a) Queue susp * 'a Digit

  val empty = SHALLOW ZERO
  fun isEmpty (SHALLOW ZERO) = true | isEmpty _ = false

  fun snoc (SHALLOW ZERO, y) = SHALLOW (ONE y)
    | snoc (SHALLOW (ONE x), y) = DEEP (TWO (x, y), $ empty, ZERO)
    | snoc (DEEP (f, m, ZERO), y) = DEEP (f, m, ONE y)
    | snoc (DEEP (f, m, ONE x), y) = DEEP (f, $ snoc (m, (x, y)), ZERO)

  fun head (SHALLOW ZERO) = raise EMPTY
    | head (SHALLOW (ONE x)) = x
    | head (DEEP (ONE x, m, r)) = x
    | head (DEEP (TWO (x, y), m, r)) = x
  fun tail (SHALLOW ZERO) = raise EMPTY
    | tail (SHALLOW (ONE x)) = empty
    | tail (DEEP (TWO (x, y), m, r)) = DEEP (ONE y, m, r)
    | tail (DEEP (ONE x, $ q, r)) =
    if isEmpty q then SHALLOW r
    else let val (y, z) = head q
         in DEEP (TWO (y, z), $ tail q, r) end
end

(* Exercise 11.1 *)
structure ImplicitQueue11_1 : QUEUE =
struct
  datatype 'a Digit = ZERO | ONE of 'a | TWO of 'a * 'a
  datatype 'a Queue = SHALLOW of 'a Digit
                    | DEEP of int * 'a Digit * ('a * 'a) Queue susp * 'a Digit

  val empty = SHALLOW ZERO
  fun isEmpty (SHALLOW ZERO) = true | isEmpty _ = false

  fun snoc (SHALLOW ZERO, y) = SHALLOW (ONE y)
    | snoc (SHALLOW (ONE x), y) = DEEP (1, TWO (x, y), $ empty, ZERO)
    | snoc (DEEP (n, f, m, ZERO), y) = DEEP (n + 1, f, m, ONE y)
    | snoc (DEEP (n, f, m, ONE x), y) =
    DEEP (n + 1, f, $ snoc (force m, (x, y)), ZERO)

  fun head (SHALLOW ZERO) = raise EMPTY
    | head (SHALLOW (ONE x)) = x
    | head (DEEP (n, ONE x, m, r)) = x
    | head (DEEP (n, TWO (x, y), m, r)) = x
  fun tail (SHALLOW ZERO) = raise EMPTY
    | tail (SHALLOW (ONE x)) = empty
    | tail (DEEP (n, TWO (x, y), m, r)) = DEEP (n - 1, ONE y, m, r)
    | tail (DEEP (n, ONE x, $ q, r)) =
    if isEmpty q then SHALLOW r
    else let val (y, z) = head q
         in DEEP (n - 1, TWO (y, z), $ tail q, r) end

  fun lookup (0, SHALLOW (ONE x)) = x
    | lookup (i, SHALLOW _)  = raise SUBSCRIPT
    | lookup (i, DEEP (n, ONE x, m, ZERO)) =
    if i = 0 then x
    else let val (x, y) = lookup ((i - 1) div 2, m)
         in if (i - 1) mod 2 = 0 then x else y end
    | lookup (i, DEEP (n, TWO (x, y), m, ZERO)) =
    if i = 0 then x else lookup (i - 1, DEEP (n - 1, ONE y, m, ZERO))
    | lookup (i, DEEP (n, f, m, ONE x)) =
    if i = n - 1 then x else looup (i, DEEP (n - 1, f, m, ZERO))

  fun makeF (i, f) =
    let fun f'(x, y) = if i mod 2 = 0 then (f x, y) else (x, f y) in f' end
  fun fupdate (f, i, SHALLOW (ONE x)) = SHALLOW (ONE (f x))
    | fupdate (f, i, SHALLOW _) = raise SUBSCRIPT
    | fupdate (f, i, DEEP (n, ONE x, m, ZERO)) =
    if i = 0 then DEEP (n, ONE (f x), m, ZERO)
    else DEEP (n, ONE x, fupdate (makeF (i - 1, f), (i - 1) div 2, m), ZERO)
    | fupdate (f, i, DEEP (n, TWO (x, y), m, ZERO)) =
    if i = 0 then DEEP (n, TWO (f x, y), m, ZERO)
    else if i = 1 then DEEP (n, TWO (x, f y), m, ZERO)
    else
      DEEP (n, TWO (x, y), fupdate (makeF (i - 2, f), (i - 2) div 2, m), ZERO)
    | fupdate (f, i, DEEP (n, f', m, ONE x)) =
    if i = n - 1 then DEEP (n, f', m, ONE (f x))
    else snoc (fupdate (f, i, DEEP (n - 1, f', m, ZERO)), x)
  fun update (i, y, q) = fupdate (fn x => y, i, q)

end

