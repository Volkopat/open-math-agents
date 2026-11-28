import OMAReductions.R_mo_195959_R1

-- Step mo-195959.R1.H2: hypothesis H2 of reduction mo-195959.R1
-- Credit: @JamesSlash. Dominated convergence: for t > 0 and x >= 0 the integrand exp (-x t) lies in (0, 1], the
-- constant 1 is integrable for a finite measure, and exp (-x t) tends to 1 as t tends to 0.

open MeasureTheory Filter Set
open scoped Topology NNReal

theorem OMA.solution : OMA.R_mo_195959_R1.H2 := by
  intro μ hμ
  have hlim : ∀ x : ℝ≥0, Tendsto (fun t : ℝ => Real.exp (-(x : ℝ) * t)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    intro x
    have hc : Continuous (fun t : ℝ => Real.exp (-(x : ℝ) * t)) := by fun_prop
    have h0 := hc.tendsto 0
    simp only [mul_zero, Real.exp_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
  · exact Eventually.of_forall (fun t =>
      (by fun_prop : Continuous (fun x : ℝ≥0 => Real.exp (-(x : ℝ) * t))).aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    refine Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have hx : (0 : ℝ) ≤ x := x.2
    have htp : (0 : ℝ) < t := ht
    nlinarith
  · exact integrable_const 1
  · exact Eventually.of_forall hlim
