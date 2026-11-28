import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Choose.Basic

namespace OMA.S_mo_304251

/-- The finite Racah sum after translating the summation index by k+m. -/
def racahSum (k m : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (k + 1),
    (-1 : ℤ) ^ (k + m + j) * (Nat.choose (k + m + j + 1) (3 * k + 1) : ℤ) *
      (Nat.choose k j : ℤ) ^ 3

/-- The stated Racah sum vanishes only in the exceptional case. -/
theorem main :
    ∀ (k m : ℕ), 2 ≤ k → k ≤ m →
      (racahSum k m = 0 ↔ k = 2 ∧ m = 3) := by
  sorry

end OMA.S_mo_304251
