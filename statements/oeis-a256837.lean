import Mathlib

/-!
# OEIS A256837: Primes of form n^2 + 6561.

Source: https://oeis.org/A256837
Credit: @unserus

OEIS: "Conjecture: sequence is infinite."
-/

namespace OMA.S_oeis_a256837

/-- The terms of A256837: primes of the form `n^2 + 6561`. -/
def a256837Set : Set ℕ := {p : ℕ | p.Prime ∧ ∃ n : ℕ, p = n ^ 2 + 6561}

/-- A256837 is infinite. -/
theorem main : a256837Set.Infinite := by
  sorry

end OMA.S_oeis_a256837
