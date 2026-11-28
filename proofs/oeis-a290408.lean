import OMAStatements.S_oeis_a290408
import Mathlib

namespace OMA.A290408Proof

/-- A fixed point `z = (i + z)^(-i)` with `Re z > 1` lies on the spiral: `z = e^((1+i)t) - i` with
`t ∈ (0, π/2)` and `e^t sin t = 1/2`. -/
theorem core (z : ℂ) (hz : (Complex.I + z) ^ (-Complex.I) = z) (h1 : 1 < z.re) :
    ∃ t : ℝ, 0 < t ∧ t < Real.pi / 2 ∧ Real.exp t * Real.sin t = 1 / 2 ∧
      z.re = Real.exp t * Real.cos t ∧ z.im = -(Real.exp t * Real.sin t) := by
  obtain ⟨w, hw⟩ : ∃ w, w = Complex.I + z := ⟨_, rfl⟩
  rw [← hw] at hz
  have hwre : w.re = z.re := by rw [hw, Complex.add_re, Complex.I_re, zero_add]
  have hwim : w.im = z.im + 1 := by rw [hw, Complex.add_im, Complex.I_im]; ring
  have hw0 : w ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    rw [hwre, Complex.zero_re] at h'
    linarith
  rw [Complex.cpow_def_of_ne_zero hw0] at hz
  have hre : z.re = Real.exp (Complex.arg w) * Real.cos (Real.log ‖w‖) := by
    rw [← hz, Complex.exp_re]
    simp [Complex.log_re, Complex.log_im]
  have him : z.im = -(Real.exp (Complex.arg w) * Real.sin (Real.log ‖w‖)) := by
    rw [← hz, Complex.exp_im]
    simp [Complex.log_re, Complex.log_im]
  have hr : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hexpl : Real.exp (Real.log ‖w‖) = ‖w‖ := Real.exp_log hr
  have hℓpos : 0 < Real.log ‖w‖ := Real.log_pos (by linarith [Complex.re_le_norm w])
  have hnorm_le := Complex.norm_le_abs_re_add_abs_im w
  have hcosθ := Complex.norm_mul_cos_arg w
  have hsinθ := Complex.norm_mul_sin_arg w
  have hθpi := Complex.arg_le_pi w
  rw [← hexpl] at hcosθ hsinθ hnorm_le
  obtain ⟨θ, hθ⟩ : ∃ θ, Complex.arg w = θ := ⟨_, rfl⟩
  rw [hθ] at hre him hcosθ hsinθ hθpi
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, Real.log ‖w‖ = ℓ := ⟨_, rfl⟩
  rw [hℓ] at hre him hcosθ hsinθ hnorm_le hℓpos hexpl
  -- now: z.re = e^θ cos ℓ = e^ℓ cos θ, z.im = -e^θ sin ℓ, z.im + 1 = e^ℓ sin θ
  have heθ := Real.exp_pos θ
  have heℓ := Real.exp_pos ℓ
  have hcosℓ : 0 < Real.cos ℓ := by
    by_contra h
    push_neg at h
    have h' := mul_le_mul_of_nonneg_left h heθ.le
    rw [mul_zero] at h'
    linarith
  have hcosθpos : 0 < Real.cos θ := by
    by_contra h
    push_neg at h
    have h' := mul_le_mul_of_nonneg_left h heℓ.le
    rw [mul_zero] at h'
    linarith
  have hθpos : 0 < θ := by
    have h2 : Real.exp θ * Real.cos ℓ ≤ Real.exp θ :=
      mul_le_of_le_one_right heθ.le (Real.cos_le_one ℓ)
    have h3 : 1 < Real.exp θ := by linarith
    by_contra h
    push_neg at h
    have h4 := Real.exp_le_exp.mpr h
    rw [Real.exp_zero] at h4
    linarith
  -- bound ℓ < 3π/2 through |w| ≤ |Re w| + |Im w| ≤ 1 + 2 e^θ ≤ 1 + 2 e^π < e^(3π/2)
  have hX : 5 / 2 < Real.exp (Real.pi / 2) := by
    have := Real.add_one_le_exp (Real.pi / 2)
    linarith [Real.pi_gt_three]
  have hpi : Real.exp Real.pi = Real.exp (Real.pi / 2) * Real.exp (Real.pi / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h3pi : Real.exp (3 * Real.pi / 2) =
      Real.exp (Real.pi / 2) * Real.exp (Real.pi / 2) * Real.exp (Real.pi / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have heθle : Real.exp θ ≤ Real.exp Real.pi := Real.exp_le_exp.mpr hθpi
  have hre_abs : |w.re| ≤ Real.exp θ := by
    rw [hwre, hre, abs_mul, abs_of_pos heθ]
    exact mul_le_of_le_one_right heθ.le (Real.abs_cos_le_one ℓ)
  have him_abs : |w.im| ≤ 1 + Real.exp θ := by
    rw [hwim, him, abs_le]
    have hs1 := mul_nonneg heθ.le (by linarith [Real.neg_one_le_sin ℓ] : (0 : ℝ) ≤ Real.sin ℓ + 1)
    have hs2 := mul_nonneg heθ.le (by linarith [Real.sin_le_one ℓ] : (0 : ℝ) ≤ 1 - Real.sin ℓ)
    constructor <;> nlinarith
  have hX2 : 25 / 4 < Real.exp (Real.pi / 2) * Real.exp (Real.pi / 2) := by nlinarith
  have hX3 : Real.exp (Real.pi / 2) * Real.exp (Real.pi / 2) * (5 / 2) <
      Real.exp (Real.pi / 2) * Real.exp (Real.pi / 2) * Real.exp (Real.pi / 2) :=
    mul_lt_mul_of_pos_left hX (by positivity)
  have hℓ3 : ℓ < 3 * Real.pi / 2 := by
    apply Real.exp_lt_exp.mp
    rw [h3pi]
    linarith
  have hℓhalf : ℓ < Real.pi / 2 := by
    by_contra h
    push_neg at h
    have := Real.cos_nonpos_of_pi_div_two_le_of_le h (by linarith)
    linarith
  -- injectivity of x ↦ e^(-x) cos x: θ = ℓ
  have hθℓ : θ = ℓ := by
    rcases lt_trichotomy θ ℓ with h | h | h
    · exfalso
      have hc : Real.cos ℓ < Real.cos θ :=
        Real.cos_lt_cos_of_nonneg_of_le_pi hθpos.le (by linarith [Real.pi_pos]) h
      have he : Real.exp θ < Real.exp ℓ := Real.exp_lt_exp.mpr h
      have h1' := mul_lt_mul_of_pos_right he hcosℓ
      have h2' := mul_lt_mul_of_pos_left hc heℓ
      linarith
    · exact h
    · exfalso
      have hc : Real.cos θ < Real.cos ℓ := Real.cos_lt_cos_of_nonneg_of_le_pi hℓpos.le hθpi h
      have he : Real.exp ℓ < Real.exp θ := Real.exp_lt_exp.mpr h
      have h1' := mul_lt_mul_of_pos_left hc heℓ
      have h2' := mul_lt_mul_of_pos_right he hcosℓ
      linarith
  rw [hθℓ] at hre him hsinθ
  refine ⟨ℓ, hℓpos, hℓhalf, ?_, hre, him⟩
  linarith

/-- `t ↦ e^t sin t` is injective on `(0, π/2)`. -/
theorem g_inj {t s : ℝ} (ht0 : 0 < t) (ht1 : t < Real.pi / 2) (hs0 : 0 < s) (hs1 : s < Real.pi / 2)
    (hgt : Real.exp t * Real.sin t = 1 / 2) (hgs : Real.exp s * Real.sin s = 1 / 2) : t = s := by
  have key : ∀ a b : ℝ, 0 < a → b < Real.pi / 2 → a < b →
      Real.exp a * Real.sin a < Real.exp b * Real.sin b := by
    intro a b ha hb hab
    have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha (by linarith [Real.pi_pos])
    have hs : Real.sin a < Real.sin b :=
      Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos]) hb.le hab
    have he : Real.exp a < Real.exp b := Real.exp_lt_exp.mpr hab
    have h1 := mul_lt_mul_of_pos_right he hsa
    have h2 := mul_lt_mul_of_pos_left hs (Real.exp_pos b)
    linarith
  rcases lt_trichotomy t s with h | h | h
  · have := key t s ht0 hs1 h
    linarith
  · exact h
  · have := key s t hs0 ht1 h
    linarith

/-- Two fixed points with real part `> 1` coincide. -/
theorem fix_unique {z y : ℂ} (hz : (Complex.I + z) ^ (-Complex.I) = z) (hz1 : 1 < z.re)
    (hy : (Complex.I + y) ^ (-Complex.I) = y) (hy1 : 1 < y.re) : z = y := by
  obtain ⟨t, ht0, ht1, hgt, hzre, hzim⟩ := core z hz hz1
  obtain ⟨s, hs0, hs1, hgs, hyre, hyim⟩ := core y hy hy1
  have hts := g_inj ht0 ht1 hs0 hs1 hgt hgs
  subst hts
  exact Complex.ext (hzre.trans hyre.symm) (hzim.trans hyim.symm)

/-- Existence: `z₀ = e^((1+i)t₀) - i` with `e^t₀ sin t₀ = 1/2`, `t₀ ∈ (0, 1/2]`. -/
theorem exists_fix : ∃ z : ℂ, (Complex.I + z) ^ (-Complex.I) = z ∧ 1 < z.re := by
  have hcont : ContinuousOn (fun t : ℝ => Real.exp t * Real.sin t) (Set.Icc 0 (1 / 2)) :=
    (Real.continuous_exp.mul Real.continuous_sin).continuousOn
  have hhalf : 1 / 2 < Real.exp (1 / 2) * Real.sin (1 / 2) := by
    have h1 : (1 / 2 : ℝ) - (1 / 2) ^ 3 / 6 < Real.sin (1 / 2) := Real.sin_gt_sub_cube (by norm_num)
    have h2 : (1 / 2 : ℝ) + 1 ≤ Real.exp (1 / 2) := Real.add_one_le_exp (1 / 2)
    nlinarith
  have hmem : (1 / 2 : ℝ) ∈ Set.Icc ((fun t : ℝ => Real.exp t * Real.sin t) 0)
      ((fun t : ℝ => Real.exp t * Real.sin t) (1 / 2)) := by
    simp only [Set.mem_Icc, Real.sin_zero, mul_zero]
    exact ⟨by norm_num, hhalf.le⟩
  obtain ⟨t, ⟨ht0, ht1⟩, hgt⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2) hcont hmem
  have hgt' : Real.exp t * Real.sin t = 1 / 2 := hgt
  have htpos : 0 < t := by
    rcases ht0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hgt'
      norm_num at hgt'
  have harg : (↑t + ↑t * Complex.I) * -Complex.I = (↑t - ↑t * Complex.I : ℂ) := by
    linear_combination (-(t : ℂ)) * Complex.I_sq
  refine ⟨Complex.exp (↑t + ↑t * Complex.I) - Complex.I, ?_, ?_⟩
  · have hI : Complex.I + (Complex.exp (↑t + ↑t * Complex.I) - Complex.I) =
        Complex.exp (↑t + ↑t * Complex.I) := by ring
    rw [hI, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _), Complex.log_exp, harg]
    · apply Complex.ext
      · simp [Complex.exp_re]
      · simp [Complex.exp_im] <;> linarith
    · simp
      linarith [Real.pi_pos]
    · simp
      linarith [Real.pi_gt_three]
  · have hc : 1 - t ^ 2 / 2 ≤ Real.cos t := Real.one_sub_sq_div_two_le_cos
    have he : t + 1 ≤ Real.exp t := Real.add_one_le_exp t
    have hcpos : 0 < Real.cos t :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_gt_three]⟩
    have hq : 0 < 1 - t / 2 - t ^ 2 / 2 := by nlinarith
    have hre : (Complex.exp (↑t + ↑t * Complex.I) - Complex.I).re = Real.exp t * Real.cos t := by
      simp [Complex.exp_re]
    rw [hre]
    nlinarith [mul_le_mul_of_nonneg_right he hcpos.le,
      mul_le_mul_of_nonneg_left hc (by linarith : (0 : ℝ) ≤ t + 1), mul_pos htpos hq]

end OMA.A290408Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a290408.main := by
  refine ⟨?_, ?_⟩
  · obtain ⟨z, hz, hz1⟩ := OMA.A290408Proof.exists_fix
    exact ⟨z, ⟨hz, hz1⟩, fun y hy => OMA.A290408Proof.fix_unique hy.1 hy.2 hz hz1⟩
  · intro z hz hz1
    obtain ⟨t, -, -, hgt, -, hzim⟩ := OMA.A290408Proof.core z hz hz1
    linarith [hzim, hgt]
