import OMAStatements.S_mse_3578846

/-!
Problem source: https://math.stackexchange.com/questions/3578846/is-there-a-well-defined-uniform-distribution-on-c0-1
The translation-invariance interpretation follows Nate Eldredge's discussion
on Math Stack Exchange. The affine example follows the formal problem statement.
Solver: @grp06
-/

open MeasureTheory Set

private theorem noInvariantProbabilityReal (ν : Measure ℝ)
    [IsProbabilityMeasure ν] [ν.IsAddLeftInvariant] : False := by
  letI : Measure.Regular ν := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure ν
  letI : Measure.IsOpenPosMeasure ν := inferInstance
  have hinfinite : ν univ = ⊤ := measure_univ_of_isAddLeftInvariant ν
  have hone : ν univ = 1 := measure_univ
  exact ENNReal.one_ne_top (hone.symm.trans hinfinite)

open OMA.S_mse_3578846

theorem OMA.solution : type_of% @OMA.S_mse_3578846.main := by
  constructor
  · rintro ⟨μ, hprob, hinvariant⟩
    letI : IsProbabilityMeasure μ := hprob
    letI : μ.IsAddLeftInvariant := hinvariant
    letI : MeasurableAdd Paths :=
      { measurable_const_add := fun f => (continuous_const.add continuous_id).measurable
        measurable_add_const := fun f => (continuous_id.add continuous_const).measurable }
    let zeroPoint : Interval := ⟨0, le_rfl, zero_le_one⟩
    let evaluate : AddHom Paths ℝ :=
      { toFun := fun f => f zeroPoint
        map_add' := fun _ _ => rfl }
    have hevaluate : Measurable evaluate := (continuous_eval_const zeroPoint).measurable
    have hsurjective : Function.Surjective evaluate := by
      intro x
      exact ⟨ContinuousMap.const Interval x, rfl⟩
    let ν : Measure ℝ := μ.map evaluate
    letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hevaluate.aemeasurable
    letI : ν.IsAddLeftInvariant := isAddLeftInvariant_map evaluate hevaluate hsurjective
    exact noInvariantProbabilityReal ν
  · letI : IsProbabilityMeasure uniform01 := by
      constructor
      change (volume.restrict (Icc (0 : ℝ) 1)) univ = 1
      rw [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]
    have hcontinuous : Continuous affine := by
      apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun p : (ℝ × ℝ) × Interval => p.1.1 + p.1.2 * (p.2 : ℝ))
      exact (continuous_fst.comp continuous_fst).add
        ((continuous_snd.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd))
    change IsProbabilityMeasure ((uniform01.prod uniform01).map affine)
    exact Measure.isProbabilityMeasure_map hcontinuous.measurable.aemeasurable
