import Mathlib

/-!
# A058188 and the gap after a prime

Source: https://oeis.org/A058188
Credit: @ZedingZhang

The OEIS uses one-based prime indices. Its example excludes the starting prime.
The upper endpoint cannot be an integer because a prime is never a square.
-/

namespace OMA.S_oeis_a058188

theorem main : ∀ n : ℕ, 1 ≤ n →
    let p := Nat.nth Nat.Prime (n - 1)
    127 ≤ p → ∃ q : ℕ, q.Prime ∧ p < q ∧ (q : ℝ) < (p : ℝ) + Real.sqrt (p : ℝ) := by
  sorry

end OMA.S_oeis_a058188
