import OMAReductions.R_Erdos687_erdos_687_variants_iwaniec_R1_H1_R2
import Mathlib

/-! Chebyshev lower bound from `Chebyshev.pi_ge`, using `log (x + 1) ≤ 2 (√(x + 1) - 1)` and
`log 2 > 0.6931`. -/

namespace OMA.Step_Erdos687_erdos_687_variants_iwaniec_R1_H1_R2_H3

theorem pi_lower (x : ℕ) (hx : 64 ≤ x) :
    (x : ℝ) / Real.log x ≤ 4 * (Nat.primeCounting x : ℝ) := by
  have h := Chebyshev.pi_ge x
  have hx' : (64 : ℝ) ≤ x := by exact_mod_cast hx
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hl2 := Real.log_two_gt_d9
  set s := Real.sqrt ((x : ℝ) + 1) with hs
  have hs2 : s ^ 2 = (x : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hs8 : 8 ≤ s := by
    rw [hs, show (8 : ℝ) = Real.sqrt 64 by
      rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hlogs : Real.log ((x : ℝ) + 1) ≤ 2 * (s - 1) := by
    have h1 : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos (by linarith)
    have h2 : Real.log ((x : ℝ) + 1) = 2 * Real.log s := by
      rw [← hs2, Real.log_pow]
      push_cast
      ring
    linarith
  rw [div_le_iff₀ hlogpos] at h ⊢
  have key : (x : ℝ) ≤ 4 * ((x : ℝ) * Real.log 2 - Real.log ((x : ℝ) + 1)) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs8) (by linarith : (0 : ℝ) ≤ s)]
  nlinarith

end OMA.Step_Erdos687_erdos_687_variants_iwaniec_R1_H1_R2_H3

theorem OMA.solution : OMA.R_Erdos687_erdos_687_variants_iwaniec_R1_H1_R2.H3 :=
  OMA.Step_Erdos687_erdos_687_variants_iwaniec_R1_H1_R2_H3.pi_lower
