import Mathlib

/-!
# OEIS A144953: Primes of form n^3 + 2.

Source: https://oeis.org/A144953
Credit: @unserus

OEIS (C. R. Greathouse IV): "The Hardy-Littlewood conjecture K (p. 51) suggests that this
sequence is infinite".
The open statement is that the sequence is infinite. `n` ranges over the natural numbers
(the first terms are `2 = 0^3 + 2` and `3 = 1^3 + 2`; negative `n` give no further primes).
-/

namespace OMA.S_oeis_a144953

/-- The terms of A144953: primes of the form `n^3 + 2`. -/
def a144953Set : Set ℕ := {p : ℕ | p.Prime ∧ ∃ n : ℕ, p = n ^ 3 + 2}

/-- A144953 is infinite. -/
theorem main : a144953Set.Infinite := by
  sorry

end OMA.S_oeis_a144953
