import OMAStatements.S_mo_455319
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Set Filter OMA.S_mo_455319
open scoped ProbabilityTheory Topology ENNReal

private noncomputable def block (a : ℝ) : Measure ℝ := volume.restrict (Ioc a (a+1))
private noncomputable def law (a : ℝ) : Measure ℝ := (2 : ℝ≥0∞)⁻¹ • (block a + block 4)
private noncomputable abbrev model (a : ℝ) : MeasureSpace ℝ where volume := law a
private def obs (_ : Fin 1) (x : ℝ) : ℝ := |x|

private theorem blockMass (a : ℝ) : block a univ = 1 := by
  simp [block, Real.volume_Ioc]

private instance blockProb (a : ℝ) : IsProbabilityMeasure (block a) := ⟨blockMass a⟩

private instance lawProb (a : ℝ) : IsProbabilityMeasure (law a) where
  measure_univ := by
    norm_num [law, Measure.smul_apply, Measure.add_apply, blockMass, ENNReal.inv_two_add_inv_two]

private theorem bInt (a : ℝ) (t : ℕ) : Integrable (fun x : ℝ => |x|^t) (block a) :=
  ((continuous_abs.pow t).continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self

private theorem bPos {a : ℝ} (ha : 0 ≤ a) : ∀ᵐ x ∂block a, 0 ≤ x := by
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioc] with x hx
  exact ha.trans hx.1.le

private theorem valid (a : ℝ) (ha : 0 ≤ a) : @ValidTuple ℝ (model a) 1 obs := by
  refine ⟨fun _ _ => abs_nonneg _, fun _ => ?_, fun n m => ?_⟩
  · change HasPDF (fun x : ℝ => |x|) (law a) (volume : Measure ℝ)
    refine Real.hasPDF_iff.2 ⟨continuous_abs.aemeasurable, ?_⟩
    have hpos : ∀ᵐ x ∂law a, 0 ≤ x := Measure.ae_smul_measure
      (ae_add_measure_iff.2 ⟨bPos ha, bPos (by norm_num : (0:ℝ) ≤ 4)⟩) _
    have eqid : (fun x : ℝ => |x|) =ᵐ[law a] id := hpos.mono fun x hx => abs_of_nonneg hx
    rw [Measure.map_congr eqid, Measure.map_id]
    exact (Measure.AbsolutelyContinuous.add_left_iff.2
      ⟨Measure.absolutelyContinuous_restrict, Measure.absolutelyContinuous_restrict⟩).smul_left _
  · change Integrable (fun x : ℝ => (∑ i : Fin 1, obs i x ^ n) ^ m) (law a)
    simp only [Fin.sum_univ_one, obs, ← pow_mul]
    exact ((bInt a _).add_measure (bInt 4 _)).smul_measure (by norm_num)

private noncomputable def moment (a : ℝ) (t : ℕ) : ℝ := ∫ x : ℝ, |x|^t ∂block a

private theorem moment_bounds (a : ℝ) (ha : 0 ≤ a) (t : ℕ) :
    a^t ≤ moment a t ∧ moment a t ≤ (a+1)^t := by
  have hx : ∀ᵐ x ∂block a, x ∈ Ioc a (a+1) := ae_restrict_mem measurableSet_Ioc
  constructor
  · calc
      a^t = ∫ _ : ℝ, a^t ∂block a := by simp
      _ ≤ _ := integral_mono_ae (integrable_const _) (bInt a t) (hx.mono fun x h => by
        change a^t ≤ |x|^t
        rw [abs_of_nonneg (ha.trans h.1.le)]
        exact pow_le_pow_left₀ ha h.1.le t)
  · calc
      _ ≤ ∫ _ : ℝ, (a+1)^t ∂block a := integral_mono_ae (bInt a t) (integrable_const _)
        (hx.mono fun x h => by
          change |x|^t ≤ (a+1)^t
          rw [abs_of_nonneg (ha.trans h.1.le)]
          exact pow_le_pow_left₀ (ha.trans h.1.le) h.2 t)
      _ = _ := by simp

private theorem moment_one (a : ℝ) (ha : 0 ≤ a) : moment a 1 = a + 1/2 := by
  unfold moment block
  have e : (∫ x in Ioc a (a+1), |x|^1) = ∫ x in Ioc a (a+1), x^1 := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    change |x|^1 = x^1
    rw [abs_of_nonneg (ha.trans hx.1.le)]
  rw [e, ← intervalIntegral.integral_of_le (show a ≤ a+1 by linarith), integral_pow]
  push_cast
  ring

private theorem table (a : ℝ) (n m : ℕ) : @powerSumMoment ℝ (model a) 1 obs n m =
    (moment a (n*m) + moment 4 (n*m))/2 := by
  change (∫ x : ℝ, (∑ i : Fin 1, obs i x ^ n)^m ∂law a) = _
  simp only [Fin.sum_univ_one, obs, ← pow_mul, law, integral_smul_measure,
    integral_add_measure (bInt a _) (bInt 4 _), ENNReal.toReal_inv, ENNReal.toReal_ofNat,
    smul_eq_mul, moment]
  ring

private theorem target (a : ℝ) (ha : 0 ≤ a) : @maxMoment ℝ (model a) 1 (by decide) obs 1 =
    (a + 5)/2 := by
  have e : @maxMoment ℝ (model a) 1 (by decide) obs 1 =
      @powerSumMoment ℝ (model a) 1 obs 1 1 := by
    simp [maxMoment, powerSumMoment, obs, Finset.univ_unique]
  rw [e, table, one_mul, moment_one a ha, moment_one 4 (by norm_num)]
  ring

private noncomputable def approxTable (n m : ℕ) : ℝ :=
  if m = 0 then 1 else moment 4 (n*m)/2

private theorem works (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    @UniformRelativeApprox ℝ (model a) 1 obs approxTable := by
  intro ε hε
  have lim := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1/2:ℝ)) (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (lim.eventually_lt_const hε)
  refine ⟨N, fun n hn m => ?_⟩
  rw [table]
  by_cases hm : m = 0
  · subst m
    simpa [approxTable, moment] using hε
  · rw [approxTable, if_neg hm]
    let t := n*m
    have hnt : n ≤ t := by exact Nat.le_mul_of_pos_right _ (by omega)
    have lo : 0 ≤ moment a t := (pow_nonneg ha _).trans (moment_bounds a ha t).1
    have hi : moment a t ≤ (2:ℝ)^t := (moment_bounds a ha t).2.trans
      (pow_le_pow_left₀ (by linarith) (by linarith) _)
    have big := (moment_bounds 4 (by norm_num) t).1
    have pos : 0 < moment a t + moment 4 t := by linarith [show 0 < (4:ℝ)^t by positivity]
    change |moment 4 t/2 - (moment a t+moment 4 t)/2| * ((moment a t+moment 4 t)/2)⁻¹ < ε
    rw [show moment 4 t/2 - (moment a t+moment 4 t)/2 = -(moment a t/2) by ring,
      abs_neg, abs_of_nonneg (by positivity), ← div_eq_mul_inv]
    have hr : (1/2:ℝ)^t * (4:ℝ)^t = (2:ℝ)^t := by rw [← mul_pow]; norm_num
    calc
      _ ≤ (1/2:ℝ)^t := (div_le_iff₀ (by positivity)).2 (by
        have hb : (4:ℝ)^t ≤ moment a t + moment 4 t := by linarith
        have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ (1/2:ℝ)^t by positivity)
        linarith)
      _ < ε := hN t (hn.trans hnt)

-- The two absolutely continuous laws share the upper half of their mass. It
-- dominates all positive m at large n, but shifting the lower half changes the mean.
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_455319.main) := by
  intro h
  obtain ⟨F, hF⟩ := h.2 1 (by decide) 1
  have eqn (a : ℝ) (ha : 0 ≤ a) (hb : a ≤ 1) : F approxTable = (a + 5)/2 := by
    have hm := @hF ℝ (model a) (lawProb a) obs (valid a ha) approxTable (works a ha hb)
    exact hm.trans (target a ha)
  linarith [eqn 0 (by norm_num) (by norm_num), eqn 1 (by norm_num) (by norm_num)]
