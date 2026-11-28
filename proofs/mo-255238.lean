import OMAStatements.S_mo_255238
import Mathlib

open Set Complex Metric OMA.S_mo_255238

noncomputable section

private def circle : Set ℂ := sphere 0 (1/2)

private def chart (w : ℂ) : ℂ := (2*I)/(1-w)-I

private def coord (z : ℂ) : ℂ := 1-(2*I)/(z+I)

private def frequency (r : ℝ) : ℂ := 2*I*(r : ℂ)

private theorem circleNorm {w : ℂ} (hw : w ∈ circle) : ‖w‖ = 1/2 := by
  simpa [circle, mem_sphere, dist_zero_right] using hw

private theorem circleNeZero {w : ℂ} (hw : w ∈ circle) : w ≠ 0 := by
  intro h
  have hn := circleNorm hw
  rw [h, norm_zero] at hn
  norm_num at hn

private theorem circleDenom {w : ℂ} (hw : w ∈ circle) : 1-w ≠ 0 := by
  intro h
  have hn := circleNorm hw
  rw [← sub_eq_zero.mp h, norm_one] at hn
  norm_num at hn

private theorem chartPlus {w : ℂ} (_hw : w ∈ circle) : chart w + I = 2*I/(1-w) := by
  unfold chart
  ring

private theorem chartDenom {w : ℂ} (hw : w ∈ circle) : chart w + I ≠ 0 := by
  rw [chartPlus hw]
  exact div_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) (circleDenom hw)

private theorem coordChart {w : ℂ} (hw : w ∈ circle) : coord (chart w) = w := by
  unfold coord
  rw [chartPlus hw, div_div_eq_mul_div, mul_comm (2*I), mul_div_cancel_right₀ _ (mul_ne_zero (by norm_num) I_ne_zero)]
  ring

private theorem chartField {w : ℂ} (hw : w ∈ circle) :
    (chart w)^2+1 = -(4*w)/(1-w)^2 := by
  unfold chart
  field_simp [circleDenom hw]
  ring_nf
  simp only [Complex.I_sq] <;> ring

private theorem derivChart {w : ℂ} (hw : w ∈ circle) :
    HasDerivAt chart (2*I/(1-w)^2) w := by
  have hd : HasDerivAt (fun v : ℂ => 1-v) (-1) w :=
    (hasDerivAt_id w).const_sub (1 : ℂ)
  change HasDerivAt (fun v : ℂ => 2*I/(1-v)-I) (2*I/(1-w)^2) w
  simpa using (((hasDerivAt_const w (2*I : ℂ)).fun_div hd (circleDenom hw)).sub_const I)

private theorem derivCoord {z : ℂ} (hz : z+I ≠ 0) :
    HasDerivAt coord (2*I/(z+I)^2) z := by
  have hd : HasDerivAt (fun v : ℂ => v+I) 1 z := (hasDerivAt_id z).add_const I
  change HasDerivAt (fun v : ℂ => 1-2*I/(v+I)) (2*I/(z+I)^2) z
  simpa [neg_div] using (((hasDerivAt_const z (2*I : ℂ)).fun_div hd hz).const_sub (1 : ℂ))

private theorem derivExpScale (a : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => exp (a * (s : ℂ))) (a * exp (a * (t : ℂ))) t := by
  have h : HasDerivAt (fun s : ℂ => a*s) a (t : ℂ) := by
    simpa using (hasDerivAt_id (t : ℂ)).const_mul a
  simpa only [mul_comm] using h.comp_ofReal.cexp

private theorem rotMem (r : ℝ) {w : ℂ} (hw : w ∈ circle) (t : ℝ) :
    w * exp (frequency r * (t : ℂ)) ∈ circle := by
  rw [circle, mem_sphere, dist_zero_right, norm_mul, circleNorm hw, Complex.norm_exp]
  simp [frequency, Complex.mul_re, Complex.mul_im]

private theorem derivOrbit (r : ℝ) {w : ℂ} (hw : w ∈ circle) (t : ℝ) :
    let z := fun s : ℝ => chart (w * exp (frequency r * (s : ℂ)))
    HasDerivAt z ((r : ℂ)*((z t)^2+1)) t := by
  dsimp only
  let v := w * exp (frequency r * (t : ℂ))
  have hv : v ∈ circle := rotMem r hw t
  have hrot := (derivExpScale (frequency r) t).const_mul w
  have h := (derivChart hv).comp t hrot
  have he : (2*I/(1-v)^2) * (w*(frequency r*exp (frequency r*(t:ℂ)))) =
      (r : ℂ) * (chart v ^ 2 + 1) := by
    have hv' : w*(frequency r*exp (frequency r*(t:ℂ))) = frequency r*v := by
      dsimp only [v]
      ring
    rw [hv', chartField hv, frequency]
    ring_nf
    simp only [Complex.I_sq] <;> ring
  rw [he] at h
  exact h

private theorem coordField {z : ℂ} (hz : z + I ≠ 0) (r : ℝ) :
    (2*I/(z+I)^2) * ((r : ℂ)*(z^2+1)) = frequency r * coord z := by
  unfold frequency coord
  field_simp [hz]
  ring_nf
  simp only [Complex.I_sq] <;> ring

private theorem periodRestriction (r τ : ℝ) (u : ℝ → ℂ)
    (hu : ∀ t, HasDerivAt u ((r : ℂ)*((u t)^2+1)) t)
    (hm : ∀ t, u t ∈ chart '' circle)
    (hper : u τ = u 0) :
    exp (frequency r * (τ : ℂ)) = 1 := by
  let rate := frequency r
  let f := fun t : ℝ => coord (u t) * exp ((-rate) * (t : ℂ))
  have df (t : ℝ) : HasDerivAt f 0 t := by
    have hn : u t + I ≠ 0 := by
      obtain ⟨w, hw, he⟩ := hm t
      rw [← he]
      exact chartDenom hw
    have hd := (derivCoord hn).comp t (hu t)
    rw [coordField hn] at hd
    convert! hd.fun_mul (derivExpScale (-rate) t) using 1 <;> dsimp [rate] <;> ring
  have he := is_const_of_deriv_eq_zero (fun t => (df t).differentiableAt)
    (fun t => (df t).deriv) τ 0
  have hn : coord (u 0) ≠ 0 := by
    obtain ⟨w, hw, hew⟩ := hm 0
    rw [← hew, coordChart hw]
    exact circleNeZero hw
  have himp : exp ((-rate)*(τ : ℂ)) = 1 := by
    apply mul_left_cancel₀ hn
    simpa [f, hper] using he
  change exp (rate * (τ : ℂ)) = 1
  rw [show rate*(τ:ℂ) = -((-rate)*(τ:ℂ)) by ring, Complex.exp_neg, himp, inv_one]

private theorem periodMultiple {r τ : ℝ} (h : exp (frequency r * (τ : ℂ)) = 1) :
    ∃ m : ℤ, r*τ = Real.pi * m := by
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp h
  have hi := congrArg Complex.im hm
  refine ⟨m, ?_⟩
  simp [frequency, Complex.mul_im, Complex.mul_re] at hi
  linarith

theorem OMA.solution : type_of% @OMA.S_mo_255238.main := by
  let P : MvPolynomial (Fin 2) ℝ := MvPolynomial.X 0 ^ 2 + 1
  let Q : MvPolynomial (Fin 2) ℝ := MvPolynomial.C (Real.sqrt 2) * (MvPolynomial.X 1 ^ 2 + 1)
  let C := chart '' circle
  have evalP (z : ℂ × ℂ) : complexEval P z = z.1^2+1 := by
    simp [P, complexEval]
  have evalQ (z : ℂ × ℂ) : complexEval Q z = ((Real.sqrt 2 : ℝ) : ℂ) * (z.2^2+1) := by
    simp [Q, complexEval, show (1 : Fin 2) ≠ 0 by decide]
  have hC : IsCompact C := by
    have hc : ContinuousOn chart circle :=
      (continuousOn_const.div (continuousOn_const.sub continuousOn_id) (fun _ hw => circleDenom hw)).sub continuousOn_const
    exact (isCompact_sphere (0 : ℂ) (1/2)).image_of_continuousOn hc
  have nonempty : C.Nonempty := by
    refine ⟨chart (1/2), 1/2, ?_, rfl⟩
    have h : (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) := by push_cast; rfl
    rw [h]
    simp [circle]
  refine ⟨P, Q, C ×ˢ C, nonempty.prod nonempty, hC.prod hC, ?_, ?_, ?_⟩
  · rintro z ⟨⟨w, hw, hwz⟩, ⟨v, hv, hvz⟩⟩
    let u : ℝ → ℂ × ℂ := fun t =>
      (chart (w*exp (frequency 1*(t:ℂ))), chart (v*exp (frequency (Real.sqrt 2)*(t:ℂ))))
    refine ⟨u, Prod.ext (by simpa [u] using hwz) (by simpa [u] using hvz), ?_, ?_⟩
    · intro t
      rw [evalP, evalQ]
      exact ⟨by simpa using derivOrbit 1 hw t, derivOrbit (Real.sqrt 2) hv t⟩
    · intro t
      exact ⟨⟨_, rotMem 1 hw t, rfl⟩, ⟨_, rotMem (Real.sqrt 2) hv t, rfl⟩⟩
  · rintro z ⟨⟨w, hw, h⟩, _⟩
    left
    rw [evalP, ← h, chartField hw]
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (by norm_num) (circleNeZero hw))) (pow_ne_zero _ (circleDenom hw))
  · rintro u hu hmem ⟨τ, hτ, hper⟩
    have hper' : u τ = u 0 := by simpa using hper 0
    have h₁ (t : ℝ) : HasDerivAt (fun s => (u s).1) ((1 : ℂ)*((u t).1^2+1)) t := by
      simpa [evalP] using (hu t).1
    have h₂ (t : ℝ) : HasDerivAt (fun s => (u s).2) (((Real.sqrt 2 : ℝ) : ℂ)*((u t).2^2+1)) t := by
      simpa [evalQ] using (hu t).2
    obtain ⟨m, hm⟩ := periodMultiple (periodRestriction 1 τ _ h₁ (fun t => (hmem t).1) (congrArg Prod.fst hper'))
    obtain ⟨n, hn⟩ := periodMultiple (periodRestriction (Real.sqrt 2) τ _ h₂
      (fun t => (hmem t).2) (congrArg Prod.snd hper'))
    simp only [one_mul] at hm
    have hm0 : m ≠ 0 := by
      intro e
      simp [e] at hm
      linarith
    have hh : Real.pi * (Real.sqrt 2 * (m : ℝ)) = Real.pi * (n : ℝ) := by
      rw [hm] at hn
      linear_combination hn
    have hr : Real.sqrt 2 = (n : ℝ) / (m : ℝ) :=
      (eq_div_iff (by exact_mod_cast hm0)).mpr (mul_left_cancel₀ Real.pi_ne_zero hh)
    exact (irrational_iff_ne_rational _).mp irrational_sqrt_two n m hm0 hr