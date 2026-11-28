import Mathlib

/-!
# OEIS A341669: Primes p such that p^7 - 1 has 8 divisors.

Source: https://oeis.org/A341669
Credit: @unserus

OEIS: "Conjecture: sequence is infinite."
-/

namespace OMA.S_oeis_a341669

/-- The terms of A341669: primes `p` such that `p^7 - 1` has exactly 8 divisors (subtraction in `ℕ` is exact, as `p ≥ 2`). -/
def a341669Set : Set ℕ := {p : ℕ | p.Prime ∧ (p ^ 7 - 1).divisors.card = 8}

/-- A341669 is infinite. -/
theorem main : a341669Set.Infinite := by
  sorry

end OMA.S_oeis_a341669
