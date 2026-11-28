import Mathlib

/-!
# OEIS A341662: Primes p such that p^4 - 1 has 160 divisors.

Source: https://oeis.org/A341662
Credit: @unserus

OEIS: "Conjecture: sequence is infinite."
-/

namespace OMA.S_oeis_a341662

/-- The terms of A341662: primes `p` such that `p^4 - 1` has exactly 160 divisors (subtraction in
`ℕ` is exact, as `p ≥ 2`). -/
def a341662Set : Set ℕ := {p : ℕ | p.Prime ∧ (p ^ 4 - 1).divisors.card = 160}

/-- A341662 is infinite. -/
theorem main : a341662Set.Infinite := by
  sorry

end OMA.S_oeis_a341662
