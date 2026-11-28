import OMAStatements.S_wp_marshall_hall_s_conjecture
import Mathlib

namespace OMA.R_wp_marshall_hall_s_conjecture_R1

def H1 : Prop :=
  ∀ k y : ℤ, 0 < k → y^2 ≠ (k^2)^3 →
    k^3 ≤ |y^2 - (k^2)^3|

def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ x y : ℤ,
    (¬ ∃ k : ℤ, 0 < k ∧ x = k^2) → y^2 ≠ x^3 → c * |(x : ℝ)| ^ ((1 : ℝ)/2 - ε) < |(y : ℝ)^2 - (x : ℝ)^3|

theorem main : H1 → H2 → type_of% @OMA.S_wp_marshall_hall_s_conjecture.main := by
  intro gap rest ε hε
  obtain ⟨c, hc, h⟩ := rest ε hε
  refine ⟨min c (1/2), lt_min hc (by norm_num), ?_⟩
  intro x y hxy
  by_cases hs : ∃ k : ℤ, 0 < k ∧ x = k^2
  · obtain ⟨k, hk, rfl⟩ := hs
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show (1 : ℤ) ≤ k by omega)
    have hg := gap k y hk hxy
    have hg' : (k : ℝ)^3 ≤ |(y : ℝ)^2 - ((k : ℝ)^2)^3| := by exact_mod_cast hg
    push_cast
    rw [abs_of_nonneg (sq_nonneg _)]
    have hbase : (1 : ℝ) ≤ (k : ℝ)^2 := by nlinarith
    have hpow : ((k : ℝ)^2)^((1 : ℝ)/2-ε) ≤ (k : ℝ)^2 := by
      simpa using Real.rpow_le_rpow_of_exponent_le hbase (show (1 : ℝ)/2-ε ≤ 1 by linarith)
    calc
      _ ≤ (1/2 : ℝ) * ((k : ℝ)^2)^((1 : ℝ)/2-ε) := by gcongr; exact min_le_right _ _
      _ ≤ (1/2 : ℝ) * (k : ℝ)^2 := by gcongr
      _ < (k : ℝ)^3 := by nlinarith [mul_nonneg (sq_nonneg (k : ℝ)) (sub_nonneg.mpr hk1)]
      _ ≤ _ := hg'
  · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)) (h x y hs hxy)

end OMA.R_wp_marshall_hall_s_conjecture_R1
