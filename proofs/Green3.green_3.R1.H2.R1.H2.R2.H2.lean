import OMAReductions.R_Green3_green_3_R1_H2_R1_H2_R2

/-!
Laplace transform of a translated positive part. On (a, infinity) the integrand exp(-u) (u - a) is the derivative
of -exp(-u) (u - a + 1), which tends to 0 at infinity and equals -exp(-a) at a. On (0, a] the integrand vanishes.
-/

namespace OMA.Green3Hinge

open MeasureTheory Set Filter Real
open scoped Topology

/-- `∫_0^∞ e^{-u} (u - a)_+ du = e^{-a}` for `a ≥ 0`. -/
theorem hinge (a : ℝ) (ha : 0 ≤ a) :
    IntegrableOn (fun u : ℝ => exp (-u) * max (u - a) 0) (Set.Ioi 0) ∧
      (∫ u in Set.Ioi (0 : ℝ), exp (-u) * max (u - a) 0) = exp (-a) := by
  -- antiderivative on `[a, ∞)`
  have hderiv : ∀ x ∈ Ici a, HasDerivAt (fun u : ℝ => -(exp (-u) * (u - a + 1)))
      (exp (-x) * (x - a)) x := by
    intro x _
    have h1 : HasDerivAt (fun u : ℝ => exp (-u)) (-exp (-x)) x := by
      simpa using (hasDerivAt_neg x).exp
    have h2 : HasDerivAt (fun u : ℝ => u - a + 1) 1 x := by
      simpa using ((hasDerivAt_id x).sub_const a).add_const 1
    have h3 : HasDerivAt (fun u : ℝ => -(exp (-u) * (u - a + 1)))
        (-(-exp (-x) * (x - a + 1) + exp (-x) * 1)) x := (h1.mul h2).neg
    have e : exp (-x) * (x - a) = -(-exp (-x) * (x - a + 1) + exp (-x) * 1) := by ring
    rw [e]
    exact h3
  have htend : Tendsto (fun u : ℝ => -(exp (-u) * (u - a + 1))) atTop (𝓝 0) := by
    have t1 := tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have t0 := tendsto_pow_mul_exp_neg_atTop_nhds_zero 0
    have t2 : Tendsto (fun u : ℝ => -(u ^ 1 * exp (-u) + (1 - a) * (u ^ 0 * exp (-u))))
        atTop (𝓝 (-(0 + (1 - a) * 0))) := (t1.add (t0.const_mul (1 - a))).neg
    have e : (fun u : ℝ => -(exp (-u) * (u - a + 1))) =
        fun u : ℝ => -(u ^ 1 * exp (-u) + (1 - a) * (u ^ 0 * exp (-u))) := by
      funext u
      ring
    rw [e]
    simpa using t2
  have hint : IntegrableOn (fun u : ℝ => exp (-u) * (u - a)) (Ioi a) :=
    integrableOn_Ioi_deriv_of_nonneg' hderiv
      (fun x hx => mul_nonneg (exp_pos _).le (by linarith [hx.out])) htend
  have hval : ∫ u in Ioi a, exp (-u) * (u - a) = exp (-a) := by
    rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend]
    simp
  -- the integrand vanishes on `(0, a]` and is `e^{-u} (u - a)` on `(a, ∞)`
  have hIoi : ∀ u ∈ Ioi a, exp (-u) * max (u - a) 0 = exp (-u) * (u - a) := by
    intro u hu
    rw [max_eq_left (by linarith [hu.out])]
  have hIoc : ∀ u ∈ Ioc 0 a, exp (-u) * max (u - a) 0 = 0 := by
    intro u hu
    rw [max_eq_right (by linarith [hu.2]), mul_zero]
  have hint1 : IntegrableOn (fun u : ℝ => exp (-u) * max (u - a) 0) (Ioi a) :=
    hint.congr_fun (fun u hu => (hIoi u hu).symm) measurableSet_Ioi
  have hint0 : IntegrableOn (fun u : ℝ => exp (-u) * max (u - a) 0) (Ioc 0 a) :=
    (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioc 0 a) volume).congr_fun
      (fun u hu => (hIoc u hu).symm) measurableSet_Ioc
  have hunion : Ioc 0 a ∪ Ioi a = Ioi 0 := Ioc_union_Ioi_eq_Ioi ha
  have hdisj : Disjoint (Ioc 0 a) (Ioi a) := by
    rw [Set.disjoint_left]
    intro u hu hu'
    exact absurd hu.2 (not_le.mpr hu'.out)
  refine ⟨by rw [← hunion]; exact hint0.union hint1, ?_⟩
  rw [← hunion, setIntegral_union hdisj measurableSet_Ioi hint0 hint1,
    setIntegral_congr_fun measurableSet_Ioc hIoc, setIntegral_congr_fun measurableSet_Ioi hIoi,
    hval]
  simp

end OMA.Green3Hinge

theorem OMA.solution : OMA.R_Green3_green_3_R1_H2_R1_H2_R2.H2 := OMA.Green3Hinge.hinge
