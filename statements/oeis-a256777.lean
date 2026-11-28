import Mathlib

/-!
# OEIS A256777: Primes of form n^2 + 625.

Source: https://oeis.org/A256777
Credit: @unserus

OEIS: "Conjecture: sequence is infinite."
-/

namespace OMA.S_oeis_a256777

/-- The terms of A256777: primes of the form `n^2 + 625`. -/
def a256777Set : Set ℕ := {p : ℕ | p.Prime ∧ ∃ n : ℕ, p = n ^ 2 + 625}

/-- A256777 is infinite. -/
theorem main : a256777Set.Infinite := by
  sorry

end OMA.S_oeis_a256777
