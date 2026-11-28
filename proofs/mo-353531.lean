import OMAStatements.S_mo_353531

-- Retains @caa1982's sine-sequence counterexample from PR #26558.
-- Commute imaginary part with the complex integral directly.

open OMA.S_mo_353531

lemma lt_sin (lam : ℝ) (hl : 0 < lam) (n : ℝ) :
    laplace (fun t => Real.sin (n * t)) lam = n / (lam ^ 2 + n ^ 2) := by
  set a : ℂ := ⟨-lam, n⟩ with ha
  have hre : a.re < 0 := by simp [ha]; linarith
  have hint := integrableOn_exp_mul_complex_Ioi hre 0
  have h := congrArg Complex.im (integral_exp_mul_complex_Ioi hre 0)
  have him : (∫ x : ℝ in Set.Ioi 0, Complex.exp (a * x)).im =
      ∫ x : ℝ in Set.Ioi 0, (Complex.exp (a * x)).im := (integral_im hint).symm
  rw [him] at h
  simpa [laplace, Complex.exp_im, ha, Complex.mul_re, Complex.mul_im,
    Complex.div_im, Complex.normSq_apply, pow_two, neg_div] using h

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_353531.main) := by
  intro h
  have hcb : ∀ n : ℕ, IsCb (fun t => Real.sin (n * t)) := fun n =>
    ⟨(Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn,
      1, fun t _ => Real.abs_sin_le_one _⟩
  have hcb0 : IsCb (fun _ => (0 : ℝ)) := ⟨continuousOn_const, 0, fun t _ => by simp⟩
  have hLT0 : ∀ lam, laplace (fun _ => (0 : ℝ)) lam = 0 := fun lam => by simp [laplace]
  have hb : ∀ lam : ℝ, 0 < lam → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      |laplace (fun t => Real.sin (n * t)) lam - laplace (fun _ => (0 : ℝ)) lam| ≤ C / n := by
    intro lam hl
    refine ⟨1, one_pos, fun n hn => ?_⟩
    rw [hLT0, sub_zero, lt_sin lam hl]
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hpos : 0 < (n : ℝ) := by linarith
    rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) hpos]
    nlinarith [sq_nonneg lam]
  have ht := h (fun n t => Real.sin (n * t)) (fun _ => 0) hcb hcb0 hb (Real.pi / 2)
    (by positivity)
  have hsub : Filter.Tendsto (fun k : ℕ => 4 * k + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun k => by simp only [id]; omega) Filter.tendsto_id
  have h2 := ht.comp hsub
  have hval : ∀ k : ℕ, ((fun n : ℕ => Real.sin (n * (Real.pi / 2))) ∘ (fun k : ℕ => 4 * k + 1)) k = 1 := by
    intro k
    show Real.sin (((4 * k + 1 : ℕ) : ℝ) * (Real.pi / 2)) = 1
    have : ((4 * k + 1 : ℕ) : ℝ) * (Real.pi / 2) = Real.pi / 2 + k * (2 * Real.pi) := by
      push_cast; ring
    rw [this, Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two]
  have h3 : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 0) := h2.congr hval
  have := tendsto_nhds_unique h3 tendsto_const_nhds
  norm_num at this
