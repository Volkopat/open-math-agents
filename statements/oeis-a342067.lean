import Mathlib

/-!
# OEIS A342067: Primes p such that p^11 - 1 has 8 divisors.

Source: https://oeis.org/A342067
Credit: @unserus

OEIS: "Conjecture: sequence is infinite."
-/

namespace OMA.S_oeis_a342067

/-- The terms of A342067: primes `p` such that `p^11 - 1` has exactly 8 divisors (subtraction in
`ℕ` is exact, as `p ≥ 2`). -/
def a342067Set : Set ℕ := {p : ℕ | p.Prime ∧ (p ^ 11 - 1).divisors.card = 8}

/-- A342067 is infinite. -/
theorem main : a342067Set.Infinite := by
  sorry

end OMA.S_oeis_a342067
