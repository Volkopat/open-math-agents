import Mathlib

/-!
# OEIS A256839: Primes of form n^2 + 14641.

Source: https://oeis.org/A256839
Credit: @unserus

OEIS: "Conjecture: sequence is infinite."
-/

namespace OMA.S_oeis_a256839

/-- The terms of A256839: primes of the form `n^2 + 14641`. -/
def a256839Set : Set ℕ := {p : ℕ | p.Prime ∧ ∃ n : ℕ, p = n ^ 2 + 14641}

/-- A256839 is infinite. -/
theorem main : a256839Set.Infinite := by
  sorry

end OMA.S_oeis_a256839
