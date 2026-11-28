import OMAReductions.R_RiemannHypothesis_robin_criterion_R1_H1_R1_H2_R1_H2_R1_H1_R1

-- Step RiemannHypothesis.robin_criterion.R1.H1.R1.H2.R1.H2.R1.H1.R1.H3: hypothesis H3 of reduction RiemannHypothesis.robin_criterion.R1.H1.R1.H2.R1.H2.R1.H1.R1
-- Credit: @swaymun
-- H3 := ∀ s b : ℝ, 1<s → s ≤ b →   Chebyshev.theta s/(s^2*log s) +     (∑ p ∈ (Ioc ⌊s⌋₊ ⌊b⌋₊).filter Nat.Prime, (p:ℝ)⁻¹^2) =   Chebyshev.theta b/(b^2*log b) + (∫ t in Set.Ioc s b, ((2*log t+1)/(t^3*(log t)^2))*Chebyshev.theta t)

open Real Finset MeasureTheory

theorem OMA.solution : OMA.R_RiemannHypothesis_robin_criterion_R1_H1_R1_H2_R1_H2_R1_H1_R1.H3 := by
  unfold OMA.R_RiemannHypothesis_robin_criterion_R1_H1_R1_H2_R1_H2_R1_H1_R1.H3
  intro s b hs hsb
  have hs0 : (0:ℝ) ≤ s := by linarith
  have hderiv : ∀ t : ℝ, 1 < t →
      HasDerivAt (fun t : ℝ => (t ^ 2 * log t)⁻¹)
        (-((2 * log t + 1) / (t ^ 3 * (log t) ^ 2))) t := by
    intro t ht
    have ht0 : t ≠ 0 := by positivity
    have hl : log t ≠ 0 := (Real.log_pos ht).ne'
    have h1 : HasDerivAt (fun t : ℝ => t ^ 2 * log t) (2 * t * log t + t ^ 2 * t⁻¹) t :=
      ((hasDerivAt_pow 2 t).mul (Real.hasDerivAt_log ht0)).congr_deriv (by norm_num)
    have h2 := h1.inv (mul_ne_zero (pow_ne_zero 2 ht0) hl)
    refine h2.congr_deriv ?_
    field_simp
  have hdiff : ∀ t ∈ Set.Icc s b, DifferentiableAt ℝ (fun t : ℝ => (t ^ 2 * log t)⁻¹) t :=
    fun t ht => (hderiv t (lt_of_lt_of_le hs ht.1)).differentiableAt
  have hcont : ContinuousOn (fun t : ℝ => -((2 * log t + 1) / (t ^ 3 * (log t) ^ 2)))
      (Set.Icc s b) := by
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le hs ht.1
    have ht0 : t ≠ 0 := by positivity
    have hl : log t ≠ 0 := (Real.log_pos ht1).ne'
    have : t ^ 3 * (log t) ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero 3 ht0) (pow_ne_zero 2 hl)
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))
  have hint : IntegrableOn (deriv fun t : ℝ => (t ^ 2 * log t)⁻¹) (Set.Icc s b) := by
    refine (hcont.integrableOn_Icc).congr_fun (fun t ht => ?_) measurableSet_Icc
    exact (hderiv t (lt_of_lt_of_le hs ht.1)).deriv.symm
  have key := sum_mul_eq_sub_sub_integral_mul
    (fun n : ℕ => if n.Prime then log (n:ℝ) else 0) hs0 hsb hdiff hint
  have hθ : ∀ t : ℝ, ∑ k ∈ Icc 0 ⌊t⌋₊, (if k.Prime then log (k:ℝ) else 0) = Chebyshev.theta t := by
    intro t
    rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  simp only [hθ] at key
  have hsum : ∑ k ∈ Ioc ⌊s⌋₊ ⌊b⌋₊, ((k:ℝ) ^ 2 * log (k:ℝ))⁻¹ * (if k.Prime then log (k:ℝ) else 0)
      = ∑ p ∈ (Ioc ⌊s⌋₊ ⌊b⌋₊).filter Nat.Prime, (p:ℝ)⁻¹^2 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hk
    · have hk1 : (1:ℝ) < k := by exact_mod_cast hk.one_lt
      have hl : log (k:ℝ) ≠ 0 := (Real.log_pos hk1).ne'
      have hk0 : (k:ℝ) ≠ 0 := by positivity
      field_simp
    · simp
  rw [hsum] at key
  have hI : ∫ t in Set.Ioc s b, deriv (fun t : ℝ => (t ^ 2 * log t)⁻¹) t * Chebyshev.theta t
      = -∫ t in Set.Ioc s b, ((2*log t+1)/(t^3*(log t)^2))*Chebyshev.theta t := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have := (hderiv t (lt_trans hs ht.1)).deriv
    simp only [this]
    ring
  rw [hI] at key
  rw [key]
  simp only [div_eq_mul_inv]
  ring
