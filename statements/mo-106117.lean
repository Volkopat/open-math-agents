import Mathlib

/-! Source: https://mathoverflow.net/questions/106117 -/

open Filter

namespace OMA.S_mo_106117

/-- The summand with upper endpoint k = j + t in Dehan's series. -/
noncomputable def dehanTerm (f : ℕ → ℝ) (j t : ℕ) : ℝ :=
  let A := ∏ l ∈ Finset.Icc j (j + t), (1 - f l)
  A / (1 - A) ^ 2

/-- Is the sum eventually of order f(j)⁻² under the stated bounds? -/
theorem main :
    ∀ (f : ℕ → ℝ) (α c : ℝ), 1 < α → c < 1 →
      (∀ᶠ j : ℕ in atTop, α / (j : ℝ) ≤ f j ∧ f j ≤ c) →
      ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
        ∀ᶠ j : ℕ in atTop, ∃ π : ℝ, HasSum (dehanTerm f j) π ∧
          C₁ / (f j) ^ 2 ≤ π ∧ π ≤ C₂ / (f j) ^ 2 := by
  sorry

end OMA.S_mo_106117
