import Mathlib

namespace OMA.S_mse_4075523

/-- The Gauss map iterates `α_m` of the simple continued fraction of `x : ℝ`:
`α_0 = x`, `α_{m+1} = 1 / (α_m - ⌊α_m⌋)`. -/
noncomputable def cfTail (x : ℝ) : ℕ → ℝ
  | 0 => x
  | m + 1 => 1 / (cfTail x m - (⌊cfTail x m⌋ : ℝ))

/-- The `m`-th partial quotient `a_m = ⌊α_m⌋` of the simple continued fraction of `x : ℝ`. -/
noncomputable def cfCoeff (x : ℝ) (m : ℕ) : ℤ :=
  ⌊cfTail x m⌋

theorem main :
    ∀ k : ℕ, 1 ≤ k →
      ∃ n : ℕ, ¬ IsSquare n ∧
        (∀ m : ℕ, 1 ≤ m → cfCoeff (Real.sqrt (n : ℝ)) (m + k) = cfCoeff (Real.sqrt (n : ℝ)) m) ∧
        (∀ d : ℕ, 1 ≤ d → d < k →
          ∃ m : ℕ, 1 ≤ m ∧ cfCoeff (Real.sqrt (n : ℝ)) (m + d) ≠ cfCoeff (Real.sqrt (n : ℝ)) m) := by
  sorry

end OMA.S_mse_4075523
