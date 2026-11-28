import OMAStatements.S_oeis_a088538

/-!
In Aktar's iteration both the imaginary part and the argument halve at
each step. Writing θₙ = (π/4) 2⁻ⁿ, the real part is 2⁻ⁿ cos θₙ / sin θₙ.
-/

namespace AktarIteration

open Real Filter Topology OMA.S_oeis_a088538

private noncomputable def y (n : ℕ) : ℝ := (1 / 2 : ℝ)^n
private noncomputable def angle (n : ℕ) : ℝ := (π / 4) * y n

private theorem y_pos (n : ℕ) : 0 < y n := by unfold y; positivity
private theorem y_next (n : ℕ) : y (n + 1) = y n / 2 := by simp [y, pow_succ, div_eq_mul_inv]
private theorem double_angle (n : ℕ) : angle n = 2 * angle (n + 1) := by
  unfold angle
  rw [y_next]
  ring

private theorem angle_pos (n : ℕ) : 0 < angle n := by
  exact mul_pos (by positivity) (y_pos n)

private theorem angle_le (n : ℕ) : angle n ≤ π / 4 := by
  have hy : y n ≤ 1 := pow_le_one₀ (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num)
  exact (mul_le_mul_of_nonneg_left hy (by positivity : 0 ≤ π / 4)).trans_eq (mul_one _)

private theorem sin_pos' (n : ℕ) : 0 < sin (angle n) :=
  Real.sin_pos_of_pos_of_lt_pi (angle_pos n) (by linarith [angle_le n, pi_pos])

private theorem norm_from_coords (z : ℂ) (t b : ℝ) (hs : 0 < sin t) (hb : 0 < b)
    (hr : z.re = b * cos t / sin t) (hi : z.im = b) : ‖z‖ = b / sin t := by
  have hsq : ‖z‖^2 = (b / sin t)^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hr, hi]
    field_simp
    linear_combination Real.sin_sq_add_cos_sq t
  nlinarith [norm_nonneg z, div_pos hb hs]

private theorem coords (n : ℕ) :
    (u n).re = y n * cos (angle n) / sin (angle n) ∧ (u n).im = y n := by
  induction n with
  | zero =>
    norm_num [u, y, angle, Real.cos_pi_div_four, Real.sin_pi_div_four]
  | succ n ih =>
    obtain ⟨hr,hi⟩ := ih
    have hnorm := norm_from_coords (u n) (angle n) (y n) (sin_pos' n) (y_pos n) hr hi
    constructor
    · rw [u, Complex.div_ofNat_re, Complex.add_re, Complex.ofReal_re, hr, hnorm, y_next]
      rw [double_angle n, Real.cos_two_mul, Real.sin_two_mul]
      have hs := sin_pos' (n + 1)
      have hc : 0 < cos (angle (n + 1)) :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [angle_pos (n + 1), pi_pos],
          by linarith [angle_le (n + 1), pi_pos]⟩
      field_simp
      ring
    · simp [u, Complex.div_ofNat_im, hi, y_next]

end AktarIteration

open Real Filter Topology OMA.S_oeis_a088538 AktarIteration

theorem OMA.solution : type_of% @OMA.S_oeis_a088538.main := by
  have ht : Tendsto angle atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => (π / 4) * (1 / 2 : ℝ)^n) atTop (𝓝 0)
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num)).const_mul (π / 4)
  have hc : Tendsto (fun n => cos (angle n)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.cos_zero] using Real.continuous_cos.continuousAt.tendsto.comp ht
  have hs : Tendsto (fun n => sinc (angle n)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.sinc_zero] using Real.continuous_sinc.continuousAt.tendsto.comp ht
  have hlim := (hc.div hs (by norm_num)).const_mul (4 / π)
  simp only [div_one, mul_one] at hlim
  apply hlim.congr
  intro n
  change 4 / π * (cos (angle n) / sinc (angle n)) = _
  rw [(coords n).1, sinc_of_ne_zero (angle_pos n).ne']
  field_simp [pi_ne_zero, (sin_pos' n).ne', (angle_pos n).ne']
  unfold angle
  ring
