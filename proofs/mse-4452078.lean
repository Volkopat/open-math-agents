import OMAStatements.S_mse_4452078
import Mathlib

open Filter Set in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_4452078.main) := by
  rintro ⟨f, x₀, hd, hm, hl⟩
  obtain ⟨a, ha⟩ := eventually_atTop.1 (hl.eventually_ge_atTop 1)
  set t := max a x₀ + 1
  have := le_max_left a x₀
  have := le_max_right a x₀
  have h0 : ∀ x ≥ t, f x ≠ 0 := fun x hx e => by have := ha x (by linarith); simp [e] at this; linarith
  have hD : ∀ x ∈ Ici t, HasDerivAt (fun x => (f x)⁻¹) (-(deriv f x) / f x ^ 2) x := fun x hx =>
    (hd x (by linarith [hx.out])).hasDerivAt.inv (h0 x hx)
  set x := t + |(f t)⁻¹| + |(f t)⁻¹| + 1
  obtain ⟨c, hc, e⟩ := exists_hasDerivAt_eq_slope (fun x => (f x)⁻¹) _ (by linarith [abs_nonneg (f t)⁻¹] : t < x)
    (fun y hy => (hD y hy.1).continuousAt.continuousWithinAt) fun y hy => hD y (le_of_lt hy.1)
  have := mul_le_mul_of_nonneg_right (ha c (by linarith [hc.1])) (by linarith [abs_nonneg (f t)⁻¹, hc.1, hc.2] : 0 ≤ x - t)
  have hx : x - t = 2 * |(f t)⁻¹| + 1 := by simp only [x]; ring
  have := neg_abs_le (f x)⁻¹
  have : |(f x)⁻¹| ≤ |(f t)⁻¹| := by
    rw [abs_inv, abs_inv]; exact inv_anti₀ (abs_pos.2 (h0 t le_rfl)) (hm (by linarith [abs_nonneg (f t)⁻¹]))
  rw [eq_div_iff (by linarith [abs_nonneg (f t)⁻¹]), neg_div] at e
  linarith [le_abs_self (f t)⁻¹]
