import Mathlib

/-!
# A211480: Number of ordered triples (w,x,y) with all terms in {-n,...,0,...,n} and w + 2x + 3y = 1.

Source: https://oeis.org/A211480
Credit: @bnb9001

Offset 0: 0, 3, 8, 16, 27, 40, 56, ...

Conjecture (George Beck, Mar 23 2023): a(n) is the number of partitions of 4n+2 into 3 parts.
A partition of m into 3 parts is a triple a <= b <= c of positive integers with a + b + c = m.
-/

namespace OMA.S_oeis_a211480

open Finset

/-- A211480: ordered triples `(w,x,y)` in `{-n,...,n}^3` with `w + 2x + 3y = 1`. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Icc (-(n : ℤ)) n ×ˢ Icc (-(n : ℤ)) n ×ˢ Icc (-(n : ℤ)) n).filter
    (fun t => t.1 + 2 * t.2.1 + 3 * t.2.2 = 1)).card

/-- The number of partitions of `m` into exactly 3 (positive) parts `a ≤ b ≤ c`. -/
def p3 (m : ℕ) : ℕ :=
  ((Icc 1 m ×ˢ Icc 1 m ×ˢ Icc 1 m).filter
    (fun t => t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ t.1 + t.2.1 + t.2.2 = m)).card

/-- Beck's conjecture: `a(n)` equals the number of partitions of `4n+2` into 3 parts. -/
theorem main : ∀ n : ℕ, a n = p3 (4 * n + 2) := by
  sorry

end OMA.S_oeis_a211480
