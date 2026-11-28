import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2
import Mathlib

-- Credit: @eolo12
-- A quantitative bound with stretched-exponential decay in log N separates
-- the combinatorial estimate from the analytic summability argument.
-- H1 is a hypothesis, not a claim that the estimate has been proved.

namespace OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R2

open Erdos142 Filter

def H1 : Prop :=
  ∀ k : ℕ, 5 ≤ k → ∃ C c e : ℝ, 0 < C ∧ 0 < c ∧ 0 < e ∧
    ∀ᶠ N : ℕ in atTop,
      (r k N : ℝ) / (N : ℝ) ≤ C * Real.exp (-c * Real.log (N : ℝ) ^ e)

def H2 : Prop :=
  ∀ C c e : ℝ, 0 < C → 0 < c → 0 < e →
    Summable (fun j : ℕ ↦ C * Real.exp (-c * ((j : ℝ) * Real.log 4) ^ e))

theorem main :
    H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2.H3 := by
  intro h1 h2 k hk
  obtain ⟨C, c, e, hC, hc, he, hb⟩ := h1 k hk
  have hs := h2 C c e hC hc he
  have hT : Tendsto (fun j : ℕ ↦ (4 : ℕ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  refine Summable.of_norm_bounded_eventually_nat hs ?_
  filter_upwards [hT.eventually hb] with j hj
  rw [Real.norm_of_nonneg (by positivity)]
  have hx : ((4 ^ j : ℕ) : ℝ) = (4 : ℝ) ^ j := by norm_num
  have hL : Real.log ((4 ^ j : ℕ) : ℝ) = (j : ℝ) * Real.log 4 := by
    rw [hx, Real.log_pow]
  rw [hL, hx] at hj
  exact hj

end OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R2
