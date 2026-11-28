import Mathlib

/-!
# A prime-cube exclusion from OEIS A397789

Source: https://oeis.org/A397789 (OEIS Foundation, CC BY-SA 4.0).
Formalization: @sturdy4days.

Use Jianing Song's consecutive-prime formulation from the formula section.
Multiply the lower and upper inequalities by 4 and 2, respectively.
-/

namespace OMA.S_oeis_a397789

theorem main : ∀ p₁ p₂ q : ℕ, p₁.Prime → p₂.Prime → q.Prime → p₁ < p₂ →
    (¬ ∃ p : ℕ, p.Prime ∧ p₁ < p ∧ p < p₂) →
    ¬ ((p₁ + p₂) ^ 2 < 4 * q ^ 3 ∧ 2 * q ^ 3 < p₁ ^ 2 + p₂ ^ 2) := by
  sorry

end OMA.S_oeis_a397789
