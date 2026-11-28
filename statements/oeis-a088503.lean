import Mathlib

/-!
# OEIS A088503: Numbers k such that (k^2 + 3)/4 is prime.

Source: https://oeis.org/A088503
Credit: @unserus

OEIS comment (C. R. Greathouse IV): "Under Bunyakovsky's conjecture this sequence is infinite."
The open statement is that the sequence is infinite. "(k^2 + 3)/4 is prime" is read as exact
division (as in the listed terms 3, 5, 7, 11, ...): `k^2 + 3 = 4 * p` for a prime `p`.
-/

namespace OMA.S_oeis_a088503

/-- The terms of A088503: numbers `k` such that `(k^2 + 3)/4` is a prime. -/
def a088503Set : Set ℕ := {k : ℕ | ∃ p : ℕ, p.Prime ∧ k ^ 2 + 3 = 4 * p}

/-- A088503 is infinite. -/
theorem main : a088503Set.Infinite := by
  sorry

end OMA.S_oeis_a088503
