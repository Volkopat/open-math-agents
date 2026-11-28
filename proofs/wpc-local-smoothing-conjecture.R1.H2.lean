import OMAReductions.R_wpc_local_smoothing_conjecture_R1

open MeasureTheory OMA.S_wpc_local_smoothing_conjecture
open scoped RealInnerProductSpace

private lemma measurable_scale {X : Type*} [MeasurableSpace X] (c : ℝ)
    {g : X → ℂ} (hg : Measurable g) : Measurable (fun x => c • g x) := hg.const_smul c

theorem OMA.solution : OMA.R_wpc_local_smoothing_conjecture_R1.H2 := by
  intro n α f
  have hf : Measurable (angularFourier f) := by
    unfold angularFourier
    apply StronglyMeasurable.measurable
    apply StronglyMeasurable.integral_prod_right
    apply Continuous.stronglyMeasurable
    unfold Function.uncurry
    fun_prop
  constructor
  · unfold besselPotential angularInverse
    apply measurable_scale
    apply StronglyMeasurable.measurable
    apply StronglyMeasurable.integral_prod_right
    apply Measurable.stronglyMeasurable
    unfold Function.uncurry
    fun_prop
  · unfold halfWaveIntegral angularInverse
    apply measurable_scale
    apply StronglyMeasurable.measurable
    apply StronglyMeasurable.integral_prod_right
    apply Measurable.stronglyMeasurable
    unfold Function.uncurry
    fun_prop
