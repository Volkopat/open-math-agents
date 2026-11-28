import Mathlib

/-!
# OEIS A088502: Numbers k such that (k^2 - 5)/4 is prime.

Source: https://oeis.org/A088502
Credit: @unserus

OEIS comment (C. R. Greathouse IV): "Under Bunyakovsky's conjecture this sequence is infinite."
The open statement is that the sequence is infinite. "(k^2 - 5)/4 is prime" is read as exact
division (as in the listed terms 5, 7, 9, 11, ...): `k^2 - 5 = 4 * p` for a prime `p`, computed in `ℤ`
to avoid truncated subtraction in `ℕ`.
-/

namespace OMA.S_oeis_a088502

/-- The terms of A088502: numbers `k` such that `(k^2 - 5)/4` is a prime. -/
def a088502Set : Set ℕ := {k : ℕ | ∃ p : ℕ, p.Prime ∧ (k : ℤ) ^ 2 - 5 = 4 * p}

/-- A088502 is infinite. -/
theorem main : a088502Set.Infinite := by
  sorry

end OMA.S_oeis_a088502
