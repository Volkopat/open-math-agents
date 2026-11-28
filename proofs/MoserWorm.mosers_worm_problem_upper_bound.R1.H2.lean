import OMAReductions.R_MoserWorm_mosers_worm_problem_upper_bound_R1

/-! The rational triangle in the reduction has affine horizontal slice length. -/

open EuclideanGeometry MeasureTheory Set
open scoped ENNReal

namespace OMA.MoserWormTriangleArea

theorem area : OMA.R_MoserWorm_mosers_worm_problem_upper_bound_R1.H2 := by
  let a : ℝ := 129 / 500
  let b : ℝ := 501 / 500
  have ha : 0 < a := by norm_num [a]
  have hb : 0 < b := by norm_num [b]
  let T : Set (ℝ × ℝ) := {p | 0 ≤ p.2 ∧ |p.1| / a + p.2 / b ≤ 1}
  let height : Set ℝ := Icc 0 b
  let width (y : ℝ) : ℝ := 2 * a * (1 - y / b)
  have hTm : MeasurableSet T := by
    have hineq : Continuous (fun p : ℝ × ℝ => |p.1| / a + p.2 / b) := by fun_prop
    exact ((isClosed_le continuous_const continuous_snd).inter
      (isClosed_le hineq continuous_const)).measurableSet
  let coord : ℝ² → ℝ × ℝ := fun x => (x 0, x 1)
  have hcoord : MeasurePreserving coord (volume : Measure ℝ²) volume :=
    (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
  have hslices :
      (fun y => (volume : Measure ℝ) ((fun x => (x, y)) ⁻¹' T)) =
        height.indicator (fun y => ENNReal.ofReal (width y)) := by
    funext y
    by_cases hy : y ∈ height
    · have h0 : 0 ≤ y := hy.1
      rw [indicator_of_mem hy]
      have hset : (fun x => (x, y)) ⁻¹' T =
          Icc (-(a * (1 - y / b))) (a * (1 - y / b)) := by
        ext x
        change (0 ≤ y ∧ |x| / a + y / b ≤ 1) ↔
          -(a * (1 - y / b)) ≤ x ∧ x ≤ a * (1 - y / b)
        rw [← abs_le]
        constructor
        · intro hx
          have hle : |x| / a ≤ 1 - y / b := by linarith [hx.2]
          simpa [mul_comm] using (div_le_iff₀ ha).mp hle
        · intro hx
          have hle : |x| / a ≤ 1 - y / b := (div_le_iff₀ ha).mpr (by simpa [mul_comm] using hx)
          exact ⟨h0, by linarith⟩
      rw [hset, Real.volume_Icc]
      congr 1
      dsimp [width]
      ring
    · rw [indicator_of_notMem hy]
      have hset : (fun x => (x, y)) ⁻¹' T = ∅ := by
        refine eq_empty_iff_forall_notMem.mpr fun x hx => hy ?_
        change 0 ≤ y ∧ |x| / a + y / b ≤ 1 at hx
        have hpos := div_nonneg (abs_nonneg x) ha.le
        have hle : y / b ≤ 1 := by linarith [hx.2]
        exact ⟨hx.1, by simpa using (div_le_iff₀ hb).mp hle⟩
      simp [hset]
  have hcont : Continuous width := by
    unfold width
    fun_prop
  have hint : Integrable width ((volume : Measure ℝ).restrict height) :=
    hcont.continuousOn.integrableOn_Icc
  have hnonneg : 0 ≤ᵐ[(volume : Measure ℝ).restrict height] width := by
    refine (ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ fun y hy => ?_)
    have hle : y / b ≤ 1 := (div_le_iff₀ hb).mpr (by simpa using hy.2)
    exact mul_nonneg (by positivity) (sub_nonneg.mpr hle)
  change (volume : Measure ℝ²) (coord ⁻¹' T) = _
  rw [hcoord.measure_preimage hTm.nullMeasurableSet]
  change ((volume : Measure ℝ).prod volume) T = _
  rw [Measure.prod_apply_symm hTm, hslices, lintegral_indicator measurableSet_Icc,
    ← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  congr 1
  change ∫ y in Icc 0 b, width y = 64629 / 250000
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hb.le]
  have hdiv : (fun y : ℝ => y / b) = fun y => y * b⁻¹ := funext fun y => div_eq_mul_inv y b
  have hconst : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 b :=
    continuous_const.intervalIntegrable 0 b
  have hlinear : IntervalIntegrable (fun y : ℝ => y / b) volume 0 b :=
    (continuous_id.div_const b).intervalIntegrable 0 b
  unfold width
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hconst hlinear,
    intervalIntegral.integral_const, hdiv, intervalIntegral.integral_mul_const, integral_id]
  norm_num [a, b]

end OMA.MoserWormTriangleArea

theorem OMA.solution : OMA.R_MoserWorm_mosers_worm_problem_upper_bound_R1.H2 :=
  OMA.MoserWormTriangleArea.area
