import OMAReductions.R_Erdos4_erdos_4_variants_rankin_R1
import Mathlib.NumberTheory.Chebyshev
-- Credit: @kofls (shorter proof: 1021 characters against 2030; same route via Chebyshev.pi_ge)
theorem OMA.solution : OMA.R_Erdos4_erdos_4_variants_rankin_R1.H2 := by
  refine ⟨4096, fun x hx => ?_⟩
  have hX : (4096 : ℝ) ≤ x := by exact_mod_cast hx
  set t := √√(x : ℝ)
  have h8 : 8 ≤ t := by
    rw [Real.le_sqrt' (by norm_num), Real.le_sqrt' (by norm_num)]; norm_num; linarith
  have e : (x : ℝ) = t ^ 4 := by
    rw [show t ^ 4 = (t ^ 2) ^ 2 by ring, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  have hl : Real.log x ≤ 4 * t - 4 := by
    rw [e, Real.log_pow]; push_cast; linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < t)]
  have hp : 0 < Real.log x := Real.log_pos (by linarith)
  have h1 : Real.log (x + 1) ≤ Real.log 2 + Real.log x := by
    rw [← Real.log_mul (by norm_num) (by linarith)]; exact Real.log_le_log (by linarith) (by linarith)
  have h2 : 0.69 * t ^ 4 ≤ x * Real.log 2 := by
    rw [e]; nlinarith [Real.log_two_gt_d9, pow_nonneg (by linarith : (0:ℝ) ≤ t) 4]
  have hs : t ^ 2 ≤ Nat.primeCounting x := ((le_div_iff₀ hp).2 (by
    nlinarith [Real.log_two_lt_d9, mul_le_mul_of_nonneg_left hl (sq_nonneg t)])).trans (Chebyshev.pi_ge x)
  have : (x : ℝ) ≤ Nat.primeCounting x ^ 2 := by rw [e]; nlinarith [sq_nonneg t]
  exact_mod_cast this
