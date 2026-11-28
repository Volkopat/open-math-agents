import Mathlib

/-!
# A263977: Integers k > 0 such that k^2 + p^2 is prime for some prime p.

Source: https://oeis.org/A263977
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A263977 (Jonathan Sondow and Robert G. Wilson v, Oct 30
2015): Every even number k is a member.

Conventions:
* The sequence has offset 1 (data 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 13, 14, ...).
* The members are the integers k > 0 such that k^2 + p^2 is prime for some prime p; the conjecture
  is stated for every positive even k.
-/

namespace OMA.S_oeis_a263977

/-- The conjecture recorded in A263977. -/
theorem main : ∀ k : ℕ, 0 < k → Even k → ∃ p : ℕ, p.Prime ∧ (k ^ 2 + p ^ 2).Prime := by
  sorry

end OMA.S_oeis_a263977
