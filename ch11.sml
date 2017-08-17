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

(* Exercise 11.2 *)
structure ImplicitDeque : DEQUE =
struct
  datatype 'a Digit = ZERO | ONE of 'a | TWO of 'a * 'a | THREE of 'a * 'a * 'a
  datatype 'a Queue = SHALLOW of 'a Digit
                    | DEEP of 'a Digit * ('a * 'a) Queue susp * 'a Digit

  val empty = SHALLOW ZERO
  fun isEmpty (SHALLOW ZERO) = true | isEmpty _ = false

  fun digitToQueue (ONE x) = SHALLOW (ONE x)
    | digitToQueue (TWO (x, y)) = DEEP (ONE x, $ empty, ONE y)
    | digitToQueue (THREE (x, y, z)) = DEEP (TWO (x, y), $ empty, ONE z)

  fun cons (x, SHALLOW ZERO) = SHALLOW (ONE x)
    | cons (x, SHALLOW (ONE y)) = DEEP (ONE x, $ empty, ONE y)
    | cons (x, DEEP (ONE y, m, r)) = DEEP (TWO (x, y), m, r)
    | cons (x, DEEP (TWO (y, z), m, r)) = DEEP (THREE (x, y, z), m, r)
    | cons (x, DEEP (THREE (y, a, b), m, r)) =
    DEEP (TWO (x, y), $ cons ((a, b), force m), r)
  fun head (SHALLOW ZERO) = raise EMPTY
    | head (SHALLOW (ONE x)) = x
    | head (DEEP (ONE x, m, r)) = x
    | head (DEEP (TWO (x, y), m, r)) = x
    | head (DEEP (THREE (x, y, z), m, r)) = x
  fun tail (SHALLOW ZERO) = raise EMPTY
    | tail (SHALLOW (ONE x)) = SHALLOW ZERO
    | tail (DEEP (TWO (x, y), m, r)) = DEEP (ONE y, m, r)
    | tail (DEEP (THREE (x, y, z), m, r)) = DEEP (TWO (y, z), m, r)
    | tail (DEEP (ONE x, $ q, r)) =
    if isEmpty q then digitToQueue r
    else let val (y, z) = head q in DEEP (TWO (y, z), $ tail q, r) end

  fun snoc (SHALLOW, x) = SHALLOW (ONE x)
    | snoc (SHALLOW (ONE x), y) = DEEP (ONE x, $ empty, ONE y)
    | snoc (DEEP (f, m, ONE x), y) = DEEP (f, m, TWO (x, y))
    | snoc (DEEP (f, m, TWO (x, y)), z) = DEEP (f, m, THREE (x, y, z))
    | snoc (DEEP (f, m, THREE (a, b, x)), y) =
    DEEP (f, $ snoc (force m, (a, b)), TWO (x, y))
  fun last (SHALLOW ZERO) = raise EMPTY
    | last (SHALLOW (ONE x)) = x
    | last (DEEP (f, m, ONE x)) = x
    | last (DEEP (f, m, TWO (x, y))) = y
    | last (DEEP (f, m, THREE (x, y, z))) = z
  fun init (SHALLOW ZERO) = raise EMPTY
    | init (SHALLOW (ONE x)) = SHALLOW ZERO
    | init (DEEP (f, m, TWO (x, y))) = DEEP (f, m, ONE x)
    | init (DEEP (f, m, THREE (x, y, z))) = DEEP (f, m, TWO (x, y))
    | init (DEEP (f, $ q, ONE z)) =
    if isEmpty q then digitToQueue f
    else let val (x, y) = last q in DEEP (f, $ tail q, TWO (x, y)) end
end

(** 11.2 Catenable Double-Ended Queue **)

signature CATENABLEDEQUE =
sig
  type 'a Cat

  val empty : 'a Cat
  val isEmpty : 'a Cat -> bool

  val cons : 'a * 'a Cat -> 'a Cat
  val head : 'a Cat -> 'a
  val tail : 'a Cat -> 'a Cat

  val snoc : 'a Cat * 'a -> 'a Cat
  val last : 'a Cat -> 'a
  val init : 'a Cat -> 'a Cat

  val ++ : 'a Cat * 'a Cat -> 'a Cat
end

(* Exercise 11.3 *)
(** Hypothesize m is assigned at most 2 debts when |f| > 2 and |r| > 2, at most
  * 1 debt when either |f| = 2 or |r| = 2, or 0 debt when |f| = 2 and |r| = 2.
  *
  * tail: If |f| > 2, the debt upper limit may be decreased. Then 1 debt is
  * repaid or delegated to higher. Otherwise, when |r| = 2, m has no debt. tail
  * is received 1 debt from recursive tail and created other 1 debt for new m.
  * Because the new m is enable to be assigned to 1 debt, either 1 debt is
  * delegated to the higher.
  * When |r| > 2, m has 1 debt. So the 1 debt must be repaid or delegated. tail
  * is received 1 debt from recursive tail and created other 1 debt for new m.
  * Because the new m is enable to be assigned at most 2 debts, some 1 debt is
  * delegated to the higher.
  * Therefore tail repaid 1 debt and unshared cost is O(1), the amortized cost
  * is O(1).
  * The proof for init is same as tail.
  *
  * *)

functor SimpleCatenableDeque (D: DEQUE) : CATENABLEDEQUE =
struct
  datatype 'a Cat = SHALLOW of 'a D.Queue
                  | DEEP of 'a D.Queue * 'a D.Queue Cat susp * 'a D.Queue

  fun tooSmall d = D.isEmpty d orelse D.isEmpty (D.tail d)

  fun dappendL (d1, d2) =
    if D.isEmpty d1 then d2 else (D.cons (D.head d1, d2))
  fun dappendR (d1, d2) =
    if D.isEmpty d2 then d1 else (D.snoc (d1, D.head d2))

  val empty = SHALLOW D.empty
  fun isEmpty (SHALLOW d) = D.isEmpty d
    | isEmpty _ = false

  fun cons (x, SHALLOW d) = SHALLOW (D.cons (x, d))
    | cons (x, DEEP (f, m, r)) = DEEP (D.cons (x, f), m, r)
  fun head (SHALLOW d) = D.head d
    | head (DEEP (f, m, r)) = D.head f
  fun tail (SHALLOW d) = SHALLOW (D.tail d)
    | tail (DEEP (f, m, r)) =
    let val f' = D.tail f
    in
      if not (tooSmall f') then DEEP (f', m, r)
      else if isEmpty (force m) then SHALLOW (dappendL (f', r))
      else DEEP (dappendL (f', head (force m)), $ tail (force m), r)
    end

  fun snoc (SHALLOW d, x) = SHALLOW (D.snoc (d, x))
    | snoc (DEEP (f, m, r), x) = DEEP (f, m, D.snoc (r, x))
  fun last (SHALLOW d) = D.last d
    | last (DEEP (f, m, r)) = D.last r
  fun init (SHALLOW d) = SHALLOW (D.init d)
    | last (DEEP (f, m, r)) =
    let val r' = D.init r
    in
      if not (tooSmall r') then DEEP (f, m, r')
      else if isEmpty (force m) then SHALLOW (dappendR (f, r'))
      else DEEP (f, init (force m), dappendR (last (force m), r'))
    end

  fun (SHALLOW d1) ++ (SHALLOW d2) =
    if tooSmall d1 then SHALLOW (dappendL (d1, d2))
    else if tooSmall d2 then SHALLOW (dappendR (d1, d2))
    else DEEP (d1, $ empty, d2)
    | (SHALLOW d) ++ (DEEP (f, m, r)) =
    if tooSmall d then DEEP (dappendL (d, f), m, r)
    else DEEP (d, $ cons (f, force m), r)
    | (DEEP (f, m, r)) ++ (SHALLOW d) =
    if tooSmall d then DEEP (f, m, dappendR (r, d))
    else DEEP (f, $ sonc (force m, r), d)
    | (DEEP (f1, m1, r1)) ++ (DEEP (f2, m2, r2)) =
    DEEP (f1, $ (snoc (force m1, r1) ++ cons (f2, force m2)), r2)
end

