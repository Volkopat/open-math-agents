import FormalConjectures.OptimizationConstants.«7a»
import Mathlib

-- Reduction Constant7a.c7a_lt_14_797075.R2 of c7a lt 14.797075
-- Credit: @arindale
-- Rhin-Viola's effective irrationality measure for ζ(2) is the deep input;
-- the transfer from π to π²/6 is the elementary part.

namespace OMA.R_Constant7a_c7a_lt_14_797075_R2
open Real ENNReal Set NNReal

/-- Rhin-Viola's effective irrationality measure: the irrationality exponent of
`ζ(2) = π²/6` is at most `7.398537`. -/
def H1 : Prop :=
  ∀ μ : ℝ, 7.398537 < μ → ¬ LiouvilleWith μ (π ^ 2 / 6)

/-- A rational approximation to `π` at exponent `p` gives one to `π²/6` at exponent `p / 2`. -/
def H2 : Prop :=
  ∀ p : ℝ, 0 ≤ p → LiouvilleWith p π → LiouvilleWith (p / 2) (π ^ 2 / 6)

theorem main : H1 → H2 → type_of% @Constant7a.c7a_lt_14_797075 := by
  intro h1 h2
  unfold Constant7a.C7a Constant7a.irrationalityExponent
  have hle : sSup ((↑) '' {p : ℝ≥0 | LiouvilleWith (p : ℝ) π}) ≤
      ((14.797074 : ℝ≥0) : ℝ≥0∞) := by
    rw [sSup_le_iff]
    rintro x ⟨p, hp, rfl⟩
    have hpbound : (p : ℝ) ≤ 2 * 7.398537 := by
      by_contra hlt
      push Not at hlt
      have hgt : 7.398537 < (p : ℝ) / 2 := by linarith
      exact h1 ((p : ℝ) / 2) hgt (h2 (p : ℝ) p.coe_nonneg hp)
    have hpNN : p ≤ (14.797074 : ℝ≥0) := by
      rw [← NNReal.coe_le_coe]
      push_cast
      linarith
    exact ENNReal.coe_le_coe.mpr hpNN
  refine lt_of_le_of_lt hle ?_
  change ((14.797074 : ℝ≥0) : ℝ≥0∞) < ((14.797075 : ℝ≥0) : ℝ≥0∞)
  rw [ENNReal.coe_lt_coe]
  norm_num

end OMA.R_Constant7a_c7a_lt_14_797075_R2
