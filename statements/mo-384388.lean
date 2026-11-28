import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Uniform bounds for a weighted Catalan recurrence

Source: https://mathoverflow.net/questions/384388/upper-bounds-for-a-sequence-of-integers
Credit: @etaubman

For every real parameter α ≥ 0, the recurrence C₀ = 1 and
Cₖ = k^α ∑ⱼ₌₀ᵏ⁻¹ Cⱼ Cₖ₋₁₋ⱼ is bounded above by Catalanₖ (k!)^α.
-/

namespace OMA.S_mo_384388

noncomputable def weightedCatalan (α : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => ((n + 1 : ℕ) : ℝ) ^ α *
      ∑ i : Fin (n + 1), weightedCatalan α i * weightedCatalan α (n - i)

/-- Uniform bounds, valid for every real nonnegative parameter and every index. -/
theorem main : ∀ (α : ℝ), 0 ≤ α →
    (∀ n : ℕ, 0 ≤ weightedCatalan α n ∧
      weightedCatalan α n ≤ (catalan n : ℝ) * (n.factorial : ℝ) ^ α ∧
      (catalan n : ℝ) * (n.factorial : ℝ) ^ α ≤
        ((4 : ℝ) ^ n / (n + 1)) * (n.factorial : ℝ) ^ α) ∧
    (∀ n : ℕ, (2 : ℝ) ^ n * ((n + 1).factorial : ℝ) ^ α ≤
      weightedCatalan α (n + 1)) ∧
    (∀ n : ℕ, weightedCatalan 0 n = (catalan n : ℝ)) := by
  sorry

end OMA.S_mo_384388
