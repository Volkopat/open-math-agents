import Mathlib

/-!
# MathOverflow 319691

Source: https://mathoverflow.net/questions/319691
-/

namespace OMA.S_mo_319691

noncomputable def inputFraction (n k : ℕ) : ℝ :=
  ((k : ℝ)+(n : ℝ)^2)/((n : ℝ)^3+(n : ℝ)^2)

theorem main : ∃ (C₁ C₂ C₃ : ℝ) (i : ℕ),
    0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧
    ∀ (n k : ℕ), 0 < n → k ≤ n →
      ∃ p q : ℕ, 0 < q ∧ Nat.Coprime p q ∧
        C₁/(n : ℝ)^i ≤ 1/(q : ℝ) ∧ 1/(q : ℝ) ≤ C₂/(n : ℝ)^3 ∧
        |inputFraction n k - (p : ℝ)/(q : ℝ)| ≤ C₃/(n : ℝ)^3 := by
  sorry

end OMA.S_mo_319691
