import Mathlib

/-!
# Unbounded lengths of constant runs in the rectangular brownie problem

Source: https://oeis.org/A386316 (Ben Orlin, 2025).
Credit: @asher-lanzone
-/

namespace OMA.S_oeis_a386316

/-- Minimum total size of a rectangle with at least `n` interior cells. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {v : ℕ | ∃ x y : ℕ, n ≤ x*y ∧ v = (x+2)*(y+2)}

theorem main : ∀ L : ℕ, ∃ n : ℕ, ∀ i : ℕ, i < L → a (n+i) = a n := by
  sorry

end OMA.S_oeis_a386316
