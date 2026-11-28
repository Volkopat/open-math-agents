import Mathlib

/-!
# OEIS A342066: Primes p such that p^10 - 1 has 256 divisors.

Source: https://oeis.org/A342066
Credit: @unserus

OEIS: "Conjecture: sequence is infinite."
-/

namespace OMA.S_oeis_a342066

/-- The terms of A342066: primes `p` such that `p^10 - 1` has exactly 256 divisors (subtraction in
`ℕ` is exact, as `p ≥ 2`). -/
def a342066Set : Set ℕ := {p : ℕ | p.Prime ∧ (p ^ 10 - 1).divisors.card = 256}

/-- A342066 is infinite. -/
theorem main : a342066Set.Infinite := by
  sorry

end OMA.S_oeis_a342066
