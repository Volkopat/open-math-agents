import Mathlib

/-! Source: https://mathoverflow.net/questions/104197 -/

namespace OMA.S_mo_104197

/-- The supremum in Yanqi Qiu's MathOverflow question 104197. -/
noncomputable def QiuRatioSup (α : ℝ) : ℝ :=
  sSup {c : ℝ | ∃ a b δ : ℝ, 0 < a ∧ 0 < b ∧ 0 < δ ∧ δ < 1 ∧
    c = ((1 + a) ^ (1 + α) + (1 + b) ^ (1 + α)) /
      ((1 + δ ^ 2 + 2 * δ + a) ^ (1 + α) +
        (1 + δ ^ 2 - 2 * δ + b) ^ (1 + α))}

/-- Does the supremum admit a linear lower bound for sufficiently small positive α? -/
theorem main :
    ∃ M ε : ℝ, 0 < M ∧ 0 < ε ∧
      ∀ α : ℝ, 0 < α → α < ε → 1 + M * α ≤ QiuRatioSup α := by
  sorry

end OMA.S_mo_104197
