import Mathlib

/-!
# OEIS A320447: n with n - p prime for every prime p with n/2 ≤ p < n

Source: https://oeis.org/A320447
Credit: @unserus

OEIS: "By conjecture there are only 6 terms and this has been checked for n up to
10^8."

The terms 5, 7, 10, 16, 36, 210 are the `n` such that `n - p` is prime for every
prime `p` with `n/2 ≤ p < n` (real division, written `n ≤ 2 * p`). For
`n ≤ 2` there is no prime in the range and the condition holds vacuously; these
`n` are not terms (the sequence starts at 5), so `3 ≤ n` is required. The
conjecture is that the six listed terms are the only ones.
-/

namespace OMA.S_oeis_a320447

/-- The terms of A320447. -/
def a320447Set : Set ℕ :=
  {n | 3 ≤ n ∧ ∀ p : ℕ, p.Prime → n ≤ 2 * p → p < n → (n - p).Prime}

/-- A320447 consists of exactly 5, 7, 10, 16, 36 and 210. -/
theorem main : a320447Set = {5, 7, 10, 16, 36, 210} := by
  sorry

end OMA.S_oeis_a320447
