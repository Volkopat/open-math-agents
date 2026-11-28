import OMAStatements.S_mo_370909
import Mathlib

/-!
Shortens @caa1982's proof from lefttosolve2/open-math-agents#26753
(commit e6bec840a932f6e3cfe4e7dc9a695b53a9d7d668), retaining its pointwise
logarithm estimate and Jensen argument. A standard inverse-power comparison
replaces the manual integral-power calculation. Original question: Daniel Li,
https://mathoverflow.net/questions/370909.
-/

open OMA.S_mo_370909 MeasureTheory

lemma pointwise (t p : ℝ) (ht : 0 ≤ t) (hp : 1 < p) :
    t * Real.log t ≤ 2 * |t - 1| + 2 / (p - 1) * |t - 1| ^ p := by
  have hs : 0 < p - 1 := by linarith
  have hR : 0 ≤ 2 / (p - 1) * |t - 1| ^ p := by positivity
  rcases le_or_gt t 1 with h1 | h1
  · exact (mul_nonpos_of_nonneg_of_nonpos ht (Real.log_nonpos ht h1)).trans
      (by positivity)
  · let x := t - 1
    have hx : 0 < x := by dsimp [x]; linarith
    rw [abs_of_pos hx]
    change t * Real.log t ≤ 2 * x + 2 / (p - 1) * x ^ p
    rcases le_or_gt x 1 with hx1 | hx1
    · have hl := Real.log_le_sub_one_of_pos (by linarith : 0 < t)
      have hm := mul_le_mul_of_nonneg_left hl ht
      rw [abs_of_pos (sub_pos.mpr h1)] at hR
      dsimp [x] at hx hx1 ⊢
      nlinarith
    · have hl : Real.log t ≤ 1 + x ^ (p - 1) / (p - 1) := by
        calc
          Real.log t ≤ Real.log (2 * x) := Real.log_le_log (by linarith)
            (by dsimp [x] at hx1 ⊢; linarith)
          _ = Real.log 2 + Real.log x := Real.log_mul (by norm_num) hx.ne'
          _ ≤ 1 + x ^ (p - 1) / (p - 1) := add_le_add
            (by linarith [Real.log_two_lt_d9]) (Real.log_le_rpow_div hx.le hs)
      calc
        t * Real.log t ≤ 2 * x * (1 + x ^ (p - 1) / (p - 1)) :=
          mul_le_mul (by dsimp [x] at hx1 ⊢; linarith) hl
            (Real.log_nonneg h1.le) (by positivity)
        _ = 2 * x + 2 / (p - 1) * x ^ p := by
          rw [show x ^ p = x * x ^ (p - 1) by
            rw [← Real.rpow_one_add' hx.le (by linarith)]; congr 1; ring]
          ring

theorem OMA.solution : type_of% @OMA.S_mo_370909.main := by
  intro Ω _ μ _ f p hp hfm hf0 hf1 hint
  have hfi : Integrable f μ := by
    by_contra h
    rw [integral_undef h] at hf1
    norm_num at hf1
  have hgi : Integrable (fun x => |f x - 1|) μ := (hfi.sub (integrable_const 1)).abs
  have hIp : 0 ≤ ∫ x, |f x - 1| ^ p ∂μ :=
    integral_nonneg (fun x => Real.rpow_nonneg (abs_nonneg _) _)
  have hI1 : 0 ≤ ∫ x, |f x - 1| ∂μ := integral_nonneg (fun x => abs_nonneg _)
  have hJ : (∫ x, |f x - 1| ∂μ) ^ p ≤ ∫ x, |f x - 1| ^ p ∂μ :=
    (convexOn_rpow hp.le).map_integral_le
      ((Real.continuous_rpow_const (by linarith : 0 ≤ p)).continuousOn) isClosed_Ici
      (ae_of_all _ (fun x => Set.mem_Ici.mpr (abs_nonneg _))) hgi hint
  have hL1 : ∫ x, |f x - 1| ∂μ ≤ (∫ x, |f x - 1| ^ p ∂μ) ^ (1 / p) := by
    simpa only [one_div] using
      (Real.le_rpow_inv_iff_of_pos hI1 hIp (by linarith : 0 < p)).2 hJ
  have hRnn : 0 ≤ 2 * (∫ x, |f x - 1| ^ p ∂μ) ^ (1 / p) + 2 / (p - 1) * ∫ x, |f x - 1| ^ p ∂μ := by
    have hs : 0 < p - 1 := by linarith
    have := Real.rpow_nonneg hIp (1 / p)
    positivity
  by_cases hfl : Integrable (fun x => f x * Real.log (f x)) μ
  · have hb : Integrable (fun x => 2 * |f x - 1| + 2 / (p - 1) * |f x - 1| ^ p) μ :=
      (hgi.const_mul 2).add (hint.const_mul _)
    calc ∫ x, f x * Real.log (f x) ∂μ
        ≤ ∫ x, (2 * |f x - 1| + 2 / (p - 1) * |f x - 1| ^ p) ∂μ :=
          integral_mono hfl hb (fun x => pointwise (f x) p (hf0 x) hp)
      _ = 2 * ∫ x, |f x - 1| ∂μ + 2 / (p - 1) * ∫ x, |f x - 1| ^ p ∂μ := by
          rw [integral_add (hgi.const_mul 2) (hint.const_mul _), integral_const_mul,
            integral_const_mul]
      _ ≤ _ := by linarith
  · rw [integral_undef hfl]
    exact hRnn
