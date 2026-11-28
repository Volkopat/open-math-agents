import Mathlib

/-!
# A299110: Consecutive prime gaps of 2 followed by 12

Source: https://oeis.org/A299110
Formalization: @pyaf

The sequence records the largest prime of each triple.
-/

namespace OMA.S_oeis_a299110

def hasGaps (p : ℕ) : Prop :=
  14 ≤ p ∧ ((Finset.Icc (p - 14) p).filter Nat.Prime) = {p - 14, p - 12, p}

theorem main : {p : ℕ | hasGaps p}.Infinite := by
  sorry

end OMA.S_oeis_a299110
