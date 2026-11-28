import Mathlib

/-!
# OEIS A256835: Primes of form n^2 + 2401.

Source: https://oeis.org/A256835
Credit: @unserus

OEIS: "Conjecture: sequence is infinite."
-/

namespace OMA.S_oeis_a256835

/-- The terms of A256835: primes of the form `n^2 + 2401`. -/
def a256835Set : Set ℕ := {p : ℕ | p.Prime ∧ ∃ n : ℕ, p = n ^ 2 + 2401}

/-- A256835 is infinite. -/
theorem main : a256835Set.Infinite := by
  sorry

end OMA.S_oeis_a256835
