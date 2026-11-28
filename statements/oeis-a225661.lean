import Mathlib

/-!
# A225661: nonrepeating vectors of a counting procedure, base 3

Source: https://oeis.org/A225661
Credit: @avivorly

A225661 is the number of nonrepeating vectors in a counting procedure that starts with the digits of (n base 3).

The counting procedure (A225660, Clark Kimberling), quoted: "Suppose that S = (x(1),..,x(h)) is a vector of
nonnegative integers. Let m = max(S) and F(S) = (f(0),..,f(m)), where f(i) is the number of occurrences of i in S.
Define H(0) = S, H(1) = F(S), and H(q) = H(H(q-1)) for q>=2." and "The result is a sequence of vectors, of which the
first a(n) are distinct and the rest repeat with period 6."

Conjecture (Clark Kimberling, in the entry): "Conjecture:  if a(n) > 6, then a(n) is odd."

Conventions:
- A vector is a `List ℕ`. `F s` has length `max s + 1` (the maximum of the empty list is `0`), and its entry `i` is
  `s.count i`.
- `digs n` is the vector of base-3 digits of `n`, most significant digit first (as `IntegerDigits[n, 3]` in the
  entry's Mathematica program), with `digs 0 = [0]`.
- The entry's `H(q) = H(H(q-1))` is read as `H(q) = F(H(q-1))`, as in the entry's examples and in its Mathematica
  program. So `H n q = F^[q] (digs n)`.
- `a n` is the least `i` such that `H n i = H n j` for some `j > i`: the vectors `H n 0, ..., H n (a n - 1)` are
  distinct and all later vectors repeat. A225660 proves that every such sequence of vectors is eventually periodic, so
  this set is nonempty. The entry's Mathematica program returns the same number: the index of the first occurrence of
  the first vector that appears twice.
-/

namespace OMA.S_oeis_a225661

/-- One counting step: `F s = (f(0), ..., f(m))`, where `m = max s` and `f(i)` is the number of occurrences of `i`
in `s`. -/
def F (s : List ℕ) : List ℕ := (List.range (s.foldr max 0 + 1)).map (fun i => s.count i)

/-- The base-3 digits of `n`, most significant digit first; `digs 0 = [0]`. -/
def digs (n : ℕ) : List ℕ := if n = 0 then [0] else (Nat.digits 3 n).reverse

/-- `H n q` is the vector `H(q)` of the procedure started at the base-3 digits of `n`. -/
def H (n q : ℕ) : List ℕ := F^[q] (digs n)

/-- `a n` (A225661): the number of nonrepeating vectors, i.e. the least `i` such that `H n i = H n j` for some
`j > i`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {i | ∃ j, i < j ∧ H n i = H n j}

/-- Kimberling's conjecture in A225661: if `a n > 6`, then `a n` is odd. -/
theorem main : ∀ n : ℕ, 6 < a n → Odd (a n) := by
  sorry

end OMA.S_oeis_a225661
