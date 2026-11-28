import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Lattice

/-! Source: https://mathoverflow.net/questions/338963 -/

namespace OMA.S_mo_338963

def degreeSet (n i : ℕ) : Set ℚ :=
  {x | ∃ k : ℕ, i ≤ k ∧ k ≤ n - i ∧
    x = ((n : ℚ) - i + 1 - k) / ((n : ℚ) - i + 1) * n.choose k * (k - 1).choose (i - 1)}

theorem main : ∀ n : ℕ, 8 ≤ n → ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ 3 →
    Disjoint (degreeSet n i) (degreeSet n j) := by
  sorry

end OMA.S_mo_338963
