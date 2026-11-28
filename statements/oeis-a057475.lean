import Mathlib

/-!
# Jon Perry's conjecture on counts of common coprimes

Source: https://oeis.org/A057475
Credit: @pyaf
-/

namespace OMA.S_oeis_a057475

/-- Number of integers from 1 through n coprime to both n and n+1. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter fun k => n.Coprime k ∧ (n + 1).Coprime k).card

theorem main : ∀ m : ℕ, 0 < m → ∃ n : ℕ, 0 < n ∧ a n = m := by
  sorry

end OMA.S_oeis_a057475
