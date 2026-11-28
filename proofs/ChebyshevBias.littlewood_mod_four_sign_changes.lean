import FormalConjectures.Wikipedia.ChebyshevBias
import Mathlib

/-! Direct analytic proof of Littlewood sign changes for Chebyshev bias mod 4. -/

open Complex Real Filter Finset MeasureTheory Topology
open scoped ComplexConjugate

namespace StrategyA

noncomputable abbrev χ₄c : DirichletCharacter ℂ 4 :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

noncomputable abbrev L₄ : ℂ → ℂ := DirichletCharacter.LFunction χ₄c

lemma χ₄c_apply_nat (n : ℕ) : χ₄c n = (ZMod.χ₄ (n : ZMod 4) : ℂ) := by
  simp [χ₄c]

lemma χ₄c_ne_one : χ₄c ≠ 1 := by
  intro h
  have h3 : χ₄c (3 : ZMod 4) = (1 : DirichletCharacter ℂ 4) (3 : ZMod 4) := by rw [h]
  have hu : IsUnit (3 : ZMod 4) := by decide
  rw [MulChar.one_apply hu] at h3
  have hval : χ₄c (3 : ZMod 4) = -1 := by
    have : ZMod.χ₄ (3 : ZMod 4) = -1 := by decide
    simp [χ₄c, this]
  rw [hval] at h3
  norm_num at h3

lemma χ₄c_odd : χ₄c.Odd := by
  change χ₄c (-1 : ZMod 4) = -1
  have : ZMod.χ₄ (-1 : ZMod 4) = -1 := by decide
  simp [χ₄c, this]

lemma χ₄c_inv : χ₄c⁻¹ = χ₄c := by
  ext x
  have hinv : χ₄c⁻¹ (x : ZMod 4) = (χ₄c (x : ZMod 4))⁻¹ := by
    simp [MulChar.inv_apply_eq_inv]
  rw [hinv]
  have hq : ZMod.χ₄ (x : ZMod 4) = 0 ∨ ZMod.χ₄ (x : ZMod 4) = 1 ∨ ZMod.χ₄ (x : ZMod 4) = -1 := by
    fin_cases x <;> decide
  rcases hq with h | h | h <;> simp [χ₄c, h]

lemma χ₄c_isPrimitive : χ₄c.IsPrimitive := by
  rw [DirichletCharacter.IsPrimitive]
  have hdvd : χ₄c.conductor ∣ 4 := DirichletCharacter.conductor_dvd_level χ₄c
  have hpos : 0 < χ₄c.conductor := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  have hne1 : χ₄c.conductor ≠ 1 := by
    intro h1
    exact χ₄c_ne_one ((DirichletCharacter.eq_one_iff_conductor_eq_one).mpr h1)
  have hne2 : χ₄c.conductor ≠ 2 := by
    intro h2
    have hfac := DirichletCharacter.factorsThrough_conductor χ₄c
    rw [h2] at hfac
    obtain ⟨hd, ψ, hψ⟩ := hfac
    have h13 : χ₄c (3 : ZMod 4) = χ₄c (1 : ZMod 4) := by
      have hu3 : IsUnit (3 : ZMod 4) := by decide
      have hu1 : IsUnit (1 : ZMod 4) := by decide
      rw [hψ, ← hu3.unit_spec, ← hu1.unit_spec,
          DirichletCharacter.changeLevel_eq_cast_of_dvd ψ hd hu3.unit,
          DirichletCharacter.changeLevel_eq_cast_of_dvd ψ hd hu1.unit]
      congr 1
      rw [hu3.unit_spec, hu1.unit_spec]
      decide
    have h3 : χ₄c (3 : ZMod 4) = -1 := by
      have : ZMod.χ₄ (3 : ZMod 4) = -1 := by decide
      simp [χ₄c, this]
    have h1 : χ₄c (1 : ZMod 4) = 1 := by simp
    rw [h3, h1] at h13
    norm_num at h13
  have hle : χ₄c.conductor ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases h : χ₄c.conductor <;> omega

lemma differentiable_L₄ : Differentiable ℂ L₄ :=
  DirichletCharacter.differentiable_LFunction χ₄c_ne_one

def Sχ₄ (n : ℕ) : ℝ :=
  if n % 4 = 1 ∨ n % 4 = 2 then 1 else 0

lemma sum_χ₄_eq_Sχ₄ (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, (χ₄c k : ℂ)) = (Sχ₄ n : ℂ) := by
  induction n with
  | zero => simp [Sχ₄]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, χ₄c_apply_nat, ZMod.χ₄_nat_eq_if_mod_four]
    unfold Sχ₄
    have hmod : (n + 1) % 4 = (n % 4 + 1) % 4 := by omega
    have h4 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases h4 with h | h | h | h <;> simp [h, hmod, show (n + 1) % 2 = (n + 1) % 4 % 2 by omega]

lemma Sχ₄_nonneg (n : ℕ) : 0 ≤ Sχ₄ n := by
  unfold Sχ₄; split_ifs <;> norm_num

lemma Sχ₄_le_one (n : ℕ) : Sχ₄ n ≤ 1 := by
  unfold Sχ₄; split_ifs <;> norm_num

lemma aestronglyMeasurable_ofReal_cpow_Ioi (w : ℂ) :
    AEStronglyMeasurable (fun t : ℝ ↦ (t : ℂ) ^ w) (volume.restrict (Set.Ioi (1 : ℝ))) := by
  refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
  intro t ht
  exact (Complex.continuousAt_ofReal_cpow_const t w (Or.inr (zero_lt_one.trans ht).ne')).continuousWithinAt

lemma measurable_Sχ₄_floor : Measurable (fun t : ℝ ↦ (Sχ₄ ⌊t⌋₊ : ℂ)) :=
  (measurable_of_countable (fun n : ℕ ↦ (Sχ₄ n : ℂ))).comp Nat.measurable_floor

lemma L₄_eq_mul_integral {s : ℂ} (hs : 0 < s.re) :
    L₄ s = s * ∫ t in Set.Ioi (1 : ℝ), (Sχ₄ ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  have hU_open : IsOpen U := isOpen_lt continuous_const continuous_re
  have hU_conn : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  let I : ℂ → ℂ := fun z ↦ ∫ t in Set.Ioi (1 : ℝ), (Sχ₄ ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(z + 1))
  have hI_diff : DifferentiableOn ℂ I U := by
    intro z hz
    have hzre : 0 < z.re := hz
    let δ : ℝ := z.re / 2
    have hδ : 0 < δ := half_pos hzre
    have hbound_int : IntegrableOn (fun t : ℝ ↦ Real.log t * t ^ (-(δ + 1))) (Set.Ioi (1 : ℝ)) := by
      have h1 : LocallyIntegrableOn (fun t : ℝ ↦ Real.log t * t ^ (-(δ + 1))) (Set.Ici (1 : ℝ)) := by
        refine ContinuousOn.locallyIntegrableOn (fun t ht ↦ ?_) measurableSet_Ici
        have ht0 : t ≠ 0 := (zero_lt_one.trans_le ht).ne'
        exact (Real.continuousAt_log ht0).continuousWithinAt.mul
          (Real.continuousAt_rpow_const t _ (Or.inl ht0)).continuousWithinAt
      rw [← integrableOn_Ici_iff_integrableOn_Ioi]
      refine h1.integrableOn_of_isBigO_atTop (g := fun t : ℝ ↦ t ^ (-(δ / 2 + 1))) ?_ ?_
      · have hlog := (isLittleO_log_rpow_atTop (half_pos hδ)).isBigO
        refine (hlog.mul (Asymptotics.isBigO_refl (fun t : ℝ ↦ t ^ (-(δ + 1))) atTop)).trans ?_
        refine Asymptotics.IsBigO.of_bound 1 ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
        rw [one_mul, ← Real.rpow_add ht]
        have heq : δ / 2 + -(δ + 1) = -(δ / 2 + 1) := by ring
        rw [heq]
      · rw [integrableAtFilter_rpow_atTop_iff]
        linarith
    have hderiv : HasDerivAt I
        (∫ t in Set.Ioi (1 : ℝ), (Sχ₄ ⌊t⌋₊ : ℂ) * (-(Real.log t : ℂ) * (t : ℂ) ^ (-(z + 1)))) z := by
      refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ)
        (F := fun w t ↦ (Sχ₄ ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(w + 1)))
        (F' := fun w t ↦ (Sχ₄ ⌊t⌋₊ : ℂ) * (-(Real.log t : ℂ) * (t : ℂ) ^ (-(w + 1))))
        (bound := fun t ↦ Real.log t * t ^ (-(δ + 1)))
        (Metric.ball_mem_nhds z hδ) ?_ ?_ ?_ ?_ hbound_int ?_).2
      · refine Eventually.of_forall fun w ↦ ?_
        exact measurable_Sχ₄_floor.aestronglyMeasurable.mul
          (aestronglyMeasurable_ofReal_cpow_Ioi (-(w + 1)))
      · refine Integrable.mono' (integrableOn_Ioi_rpow_of_lt (by linarith : -(z.re + 1) < -1) zero_lt_one) ?_ ?_
        · exact measurable_Sχ₄_floor.aestronglyMeasurable.mul
            (aestronglyMeasurable_ofReal_cpow_Ioi (-(z + 1)))
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          have ht0 : 0 < t := zero_lt_one.trans ht
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Sχ₄_nonneg _),
            Complex.norm_cpow_eq_rpow_re_of_pos ht0]
          simpa using mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) (Sχ₄_le_one ⌊t⌋₊)
      · exact measurable_Sχ₄_floor.aestronglyMeasurable.mul
          (((Complex.continuous_ofReal.measurable.comp Real.measurable_log).neg.aestronglyMeasurable).mul
            (aestronglyMeasurable_ofReal_cpow_Ioi (-(z + 1))))
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
        have ht0 : 0 < t := zero_lt_one.trans ht
        have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht.le
        have hwre : δ < w.re := by
          have habs := Complex.abs_re_le_norm (w - z)
          rw [Metric.mem_ball, dist_eq_norm] at hw
          simp only [sub_re] at habs
          have h1 := (abs_lt.mp (habs.trans_lt hw)).1
          dsimp only [δ] at h1 ⊢
          linarith
        rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg (Sχ₄_nonneg _), Real.norm_of_nonneg hlog0,
          Complex.norm_cpow_eq_rpow_re_of_pos ht0]
        calc Sχ₄ ⌊t⌋₊ * (Real.log t * t ^ (-(w + 1)).re)
            ≤ 1 * (Real.log t * t ^ (-(w + 1)).re) := by
              gcongr; exact Sχ₄_le_one _
          _ = Real.log t * t ^ (-(w.re + 1)) := by simp
          _ ≤ Real.log t * t ^ (-(δ + 1)) :=
              mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht.le (by linarith)) hlog0
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w _
        have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zero_lt_one.trans ht).ne'
        have hcpow : HasDerivAt (fun u : ℂ ↦ (t : ℂ) ^ (-(u + 1)))
            ((t : ℂ) ^ (-(w + 1)) * Complex.log (t : ℂ) * (-1)) w := by
          have h1 : HasDerivAt (fun u : ℂ ↦ -(u + 1)) (-1) w :=
            ((hasDerivAt_id w).add_const (1 : ℂ)).neg
          simpa [mul_assoc] using h1.const_cpow (Or.inl ht0)
        have hlogt : Complex.log (t : ℂ) = (Real.log t : ℂ) :=
          (Complex.ofReal_log (zero_lt_one.trans ht).le).symm
        have hmul := hcpow.const_mul (Sχ₄ ⌊t⌋₊ : ℂ)
        simpa only [hlogt, neg_mul, mul_neg, mul_one, one_mul, mul_comm, mul_left_comm, mul_assoc] using hmul
    exact hderiv.differentiableAt.differentiableWithinAt
  have hEq : Set.EqOn L₄ (fun z ↦ z * I z) U := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (differentiable_L₄.differentiableOn.analyticOnNhd hU_open)
      ((differentiableOn_id.mul hI_diff).analyticOnNhd hU_open)
      hU_conn (show (2 : ℂ) ∈ U by simp [U]) ?_
    have hnbhd : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by simp)
    filter_upwards [hnbhd] with z hz
    rw [L₄, DirichletCharacter.LFunction_eq_LSeries χ₄c hz]
    have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (χ₄c k : ℂ)) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (0 : ℝ) := by
      refine Asymptotics.isBigO_iff.mpr ⟨1, Eventually.of_forall fun n ↦ ?_⟩
      rw [sum_χ₄_eq_Sχ₄, Complex.norm_real, Real.norm_of_nonneg (Sχ₄_nonneg _), Real.rpow_zero]
      simpa using Sχ₄_le_one n
    have hrep := LSeries_eq_mul_integral (fun n ↦ (χ₄c n : ℂ)) le_rfl (by linarith : (0 : ℝ) < z.re)
      (DirichletCharacter.LSeriesSummable_of_one_lt_re χ₄c hz) hO
    rw [hrep]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
    rw [sum_χ₄_eq_Sχ₄]
  exact hEq hs

lemma integrableOn_Sχ₄_rpow {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun t : ℝ ↦ Sχ₄ ⌊t⌋₊ * t ^ (-(σ + 1))) (Set.Ioi (1 : ℝ)) := by
  refine Integrable.mono' (integrableOn_Ioi_rpow_of_lt (by linarith : -(σ + 1) < -1) (by norm_num : (0 : ℝ) < 1)) ?_ ?_
  · refine ((measurable_of_countable Sχ₄).comp Nat.measurable_floor).aestronglyMeasurable.mul ?_
    refine ContinuousOn.aestronglyMeasurable (fun t ht ↦ ?_) measurableSet_Ioi
    exact (Real.continuousAt_rpow_const t _ (Or.inl (zero_lt_one.trans ht).ne')).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_of_nonneg (mul_nonneg (Sχ₄_nonneg _) (Real.rpow_nonneg (zero_lt_one.trans ht).le _))]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (zero_lt_one.trans ht).le _) (Sχ₄_le_one _)

lemma L₄_ofReal_eq_integral {σ : ℝ} (hσ : 0 < σ) :
    L₄ (σ : ℂ) = Complex.ofReal (σ * ∫ t in Set.Ioi (1 : ℝ), Sχ₄ ⌊t⌋₊ * t ^ (-(σ + 1))) := by
  have hrep := L₄_eq_mul_integral (s := (σ : ℂ)) (by simpa using hσ)
  have hcast : ∀ t ∈ Set.Ioi (1 : ℝ),
      (Sχ₄ ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-((σ : ℂ) + 1)) = ((Sχ₄ ⌊t⌋₊ * t ^ (-(σ + 1)) : ℝ) : ℂ) := by
    intro t ht
    rw [show -((σ : ℂ) + 1) = ((-(σ + 1) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (zero_lt_one.trans ht).le, Complex.ofReal_mul]
  have hint : ∫ t in Set.Ioi (1 : ℝ), Complex.ofReal (Sχ₄ ⌊t⌋₊ * t ^ (-(σ + 1))) =
      Complex.ofReal (∫ t in Set.Ioi (1 : ℝ), Sχ₄ ⌊t⌋₊ * t ^ (-(σ + 1))) :=
    Complex.ofRealCLM.integral_comp_comm (integrableOn_Sχ₄_rpow hσ)
  rw [setIntegral_congr_fun measurableSet_Ioi hcast] at hrep
  change L₄ ↑σ = ↑σ * ∫ t in Set.Ioi (1 : ℝ), Complex.ofReal (Sχ₄ ⌊t⌋₊ * t ^ (-(σ + 1))) at hrep
  rw [hint, ← Complex.ofReal_mul] at hrep
  exact hrep

lemma L₄_real_pos {σ : ℝ} (hσ : 0 < σ) : 0 < (L₄ (σ : ℂ)).re ∧ (L₄ (σ : ℂ)).im = 0 := by
  rw [L₄_ofReal_eq_integral hσ]
  refine ⟨?_, Complex.ofReal_im _⟩
  rw [Complex.ofReal_re]
  refine mul_pos hσ ?_
  have hint_all := integrableOn_Sχ₄_rpow hσ
  have hsub : Set.Ioo (1 : ℝ) 3 ⊆ Set.Ioi (1 : ℝ) := fun _ ht ↦ ht.1
  have hpos_sub : 0 < ∫ t in Set.Ioo (1 : ℝ) 3, Sχ₄ ⌊t⌋₊ * t ^ (-(σ + 1)) := by
    have h_eq : Set.EqOn (fun t : ℝ ↦ Sχ₄ ⌊t⌋₊ * t ^ (-(σ + 1)))
        (fun t : ℝ ↦ t ^ (-(σ + 1))) (Set.Ioo (1 : ℝ) 3) := by
      intro t ht
      have hf : ⌊t⌋₊ = 1 ∨ ⌊t⌋₊ = 2 := by
        have h1 : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by simpa using ht.1.le)
        have h3 : ⌊t⌋₊ < 3 := (Nat.floor_lt (by linarith [ht.1])).mpr ht.2
        omega
      have hs1 : Sχ₄ ⌊t⌋₊ = 1 := by
        unfold Sχ₄
        rcases hf with h | h <;> simp [h]
      simp [hs1]
    rw [setIntegral_congr_fun measurableSet_Ioo h_eq]
    rw [setIntegral_pos_iff_support_of_nonneg_ae]
    · have hsupp : Set.Ioo (1 : ℝ) 3 ⊆ Function.support (fun t : ℝ ↦ t ^ (-(σ + 1))) := by
        intro t ht
        exact (Real.rpow_pos_of_pos (zero_lt_one.trans ht.1) _).ne'
      have hmeas : volume (Set.Ioo (1 : ℝ) 3) = ENNReal.ofReal (3 - 1) := Real.volume_Ioo
      calc (0 : ENNReal) < ENNReal.ofReal (3 - 1) := by norm_num
        _ = volume (Set.Ioo (1 : ℝ) 3) := hmeas.symm
        _ ≤ volume (Function.support (fun t : ℝ ↦ t ^ (-(σ + 1))) ∩ Set.Ioo (1 : ℝ) 3) := by
            apply measure_mono; intro t ht; exact ⟨hsupp ht, ht⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact Real.rpow_nonneg (zero_lt_one.trans ht.1).le _
    · exact (integrableOn_Ioi_rpow_of_lt (by linarith : -(σ + 1) < -1) zero_lt_one).mono_set hsub
  refine lt_of_lt_of_le hpos_sub ?_
  refine setIntegral_mono_set hint_all ?_ hsub.eventuallyLE
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_nonneg (Sχ₄_nonneg _) (Real.rpow_nonneg (zero_lt_one.trans ht).le _)

lemma L₄_real_ne_zero {σ : ℝ} (hσ : 0 < σ) : L₄ (σ : ℂ) ≠ 0 := by
  intro h
  have := (L₄_real_pos hσ).1
  rw [h, zero_re] at this
  linarith

lemma norm_L₄_le {s : ℂ} (hs : 1 / 2 ≤ s.re) : ‖L₄ s‖ ≤ 2 * ‖s‖ := by
  have hs0 : 0 < s.re := by linarith
  rw [L₄_eq_mul_integral hs0, norm_mul]
  have hint_le : ‖∫ t in Set.Ioi (1 : ℝ), (Sχ₄ ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))‖ ≤ 2 := by
    have hint_f : IntegrableOn (fun t : ℝ ↦ (Sχ₄ ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi (1 : ℝ)) := by
      refine Integrable.mono'
        (integrableOn_Ioi_rpow_of_lt (by linarith : -(s.re + 1) < -1) zero_lt_one) ?_ ?_
      · exact measurable_Sχ₄_floor.aestronglyMeasurable.mul
          (aestronglyMeasurable_ofReal_cpow_Ioi (-(s + 1)))
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0 < t := zero_lt_one.trans ht
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Sχ₄_nonneg _),
          Complex.norm_cpow_eq_rpow_re_of_pos ht0]
        simpa using mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) (Sχ₄_le_one _)
    calc ‖∫ t in Set.Ioi (1 : ℝ), (Sχ₄ ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))‖
        ≤ ∫ t in Set.Ioi (1 : ℝ), ‖(Sχ₄ ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ t in Set.Ioi (1 : ℝ), t ^ (-(s.re + 1)) := by
          refine setIntegral_mono_on hint_f.integrable.norm
            (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one)
            measurableSet_Ioi fun t ht ↦ ?_
          have ht0 : 0 < t := zero_lt_one.trans ht
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Sχ₄_nonneg _),
            Complex.norm_cpow_eq_rpow_re_of_pos ht0]
          simpa using mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) (Sχ₄_le_one _)
      _ = 1 / s.re := by
          rw [integral_Ioi_rpow_of_lt (by linarith : -(s.re + 1) < -1) zero_lt_one]
          simp [neg_div, one_div]
      _ ≤ 2 := by
          rw [div_le_iff₀ hs0]; linarith
  calc ‖s‖ * ‖∫ t in Set.Ioi (1 : ℝ), (Sχ₄ ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))‖
      ≤ ‖s‖ * 2 := mul_le_mul_of_nonneg_left hint_le (norm_nonneg _)
    _ = 2 * ‖s‖ := mul_comm _ _

lemma L₄_real_ge_half {σ : ℝ} (hσ : 2 ≤ σ) : (1 : ℝ) / 2 ≤ (L₄ (σ : ℂ)).re := by
  have hσ0 : 0 < σ := by linarith
  rw [L₄_ofReal_eq_integral hσ0, Complex.ofReal_re]
  have hint_all := integrableOn_Sχ₄_rpow hσ0
  have hsub : Set.Ioo (1 : ℝ) 3 ⊆ Set.Ioi (1 : ℝ) := fun _ ht ↦ ht.1
  have hge : ∫ t in Set.Ioo (1 : ℝ) 3, Sχ₄ ⌊t⌋₊ * t ^ (-(σ + 1)) ≤
      ∫ t in Set.Ioi (1 : ℝ), Sχ₄ ⌊t⌋₊ * t ^ (-(σ + 1)) := by
    refine setIntegral_mono_set hint_all ?_ hsub.eventuallyLE
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Sχ₄_nonneg _) (Real.rpow_nonneg (zero_lt_one.trans ht).le _)
  have heq : ∫ t in Set.Ioo (1 : ℝ) 3, Sχ₄ ⌊t⌋₊ * t ^ (-(σ + 1)) =
      ∫ t in (1 : ℝ)..3, t ^ (-(σ + 1)) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 3),
      ← MeasureTheory.setIntegral_congr_set Ioo_ae_eq_Ioc]
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht ↦ ?_
    have hf : ⌊t⌋₊ = 1 ∨ ⌊t⌋₊ = 2 := by
      have h1 : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by simpa using ht.1.le)
      have h3 : ⌊t⌋₊ < 3 := (Nat.floor_lt (by linarith [ht.1])).mpr ht.2
      omega
    have hs1 : Sχ₄ ⌊t⌋₊ = 1 := by unfold Sχ₄; rcases hf with h | h <;> simp [h]
    simp [hs1]
  have hval : ∫ t in (1 : ℝ)..3, t ^ (-(σ + 1)) = (1 - (3 : ℝ) ^ (-σ)) / σ := by
    rw [integral_rpow (Or.inr ⟨by linarith, fun h ↦ by
      rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at h; linarith [h.1]⟩)]
    have h1 : -(σ + 1) + 1 = -σ := by ring
    rw [h1, Real.one_rpow]
    field_simp
    ring
  have h3 : (3 : ℝ) ^ (-σ) ≤ 1 / 2 := by
    calc (3 : ℝ) ^ (-σ) ≤ (3 : ℝ) ^ (-(2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1 / 9 := by norm_num
      _ ≤ 1 / 2 := by norm_num
  have hmul : σ * ((1 - (3 : ℝ) ^ (-σ)) / σ) = 1 - (3 : ℝ) ^ (-σ) := by
    field_simp
  nlinarith [mul_le_mul_of_nonneg_left (heq.symm.le.trans hge) hσ0.le]

lemma L₄_conj (s : ℂ) : L₄ (conj s) = conj (L₄ s) := by
  let g : ℂ → ℂ := fun z ↦ conj (L₄ (conj z))
  have hg_diff : Differentiable ℂ g := by
    intro z
    have hL := (differentiable_L₄ (conj z)).hasDerivAt
    have h1 : HasDerivAt g (conj (deriv L₄ (conj z))) z := by
      rw [hasDerivAt_iff_tendsto_slope]
      have hL' := hasDerivAt_iff_tendsto_slope.mp hL
      have hconj_cont : Continuous (fun w : ℂ ↦ conj w) := Complex.continuous_conj
      have hcomp : Tendsto (fun w : ℂ ↦ slope L₄ (conj z) (conj w)) (𝓝[≠] z) (𝓝 (deriv L₄ (conj z))) := by
        refine hL'.comp ?_
        rw [tendsto_nhdsWithin_iff]
        refine ⟨(hconj_cont.tendsto z).mono_left nhdsWithin_le_nhds, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with w hw
        exact fun heq ↦ hw (by simpa using congrArg (fun u : ℂ ↦ conj u) heq)
      have h2 := (hconj_cont.tendsto _).comp hcomp
      refine h2.congr fun w ↦ ?_
      simp [g, slope_def_field, map_div₀, map_sub]
    exact h1.differentiableAt
  have hEq : Set.EqOn L₄ g Set.univ := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (differentiable_L₄.differentiableOn.analyticOnNhd isOpen_univ)
      (hg_diff.differentiableOn.analyticOnNhd isOpen_univ)
      isPreconnected_univ (Set.mem_univ (2 : ℂ)) ?_
    have hnbhd : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by simp)
    filter_upwards [hnbhd] with z hz
    have hzc : 1 < (conj z).re := by simpa using hz
    simp only [g, L₄, DirichletCharacter.LFunction_eq_LSeries χ₄c hz,
      DirichletCharacter.LFunction_eq_LSeries χ₄c hzc, LSeries]
    rw [Complex.conj_tsum]
    congr 1; ext n
    by_cases hn : n = 0
    · simp [hn]
    · simp only [LSeries.term_of_ne_zero hn, map_div₀, χ₄c_apply_nat, map_intCast]
      congr 1
      have harg : Complex.arg (n : ℂ) ≠ Real.pi := by
        rw [show (n : ℂ) = ((n : ℝ) : ℂ) by simp, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
        exact Real.pi_pos.ne
      have hcp := Complex.cpow_conj (n : ℂ) (conj z) harg
      simpa using hcp
  have := hEq (Set.mem_univ (conj s))
  simpa [g] using this

noncomputable def ξ₄ (s : ℂ) : ℂ :=
  (2 : ℂ) ^ s * DirichletCharacter.completedLFunction χ₄c s

lemma differentiable_ξ₄ : Differentiable ℂ ξ₄ := by
  unfold ξ₄
  exact (Differentiable.const_cpow differentiable_id (by norm_num)).mul
    (DirichletCharacter.differentiable_completedLFunction χ₄c_ne_one)

lemma ξ₄_eq_mul_L₄ (s : ℂ) (hs : ∀ n : ℕ, s + 1 ≠ -(2 * (n : ℂ))) :
    ξ₄ s = (2 : ℂ) ^ s * Complex.Gammaℝ (s + 1) * L₄ s := by
  have hL := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ₄c s (Or.inr (by norm_num))
  rw [χ₄c_odd.gammaFactor_def] at hL
  have hG : Complex.Gammaℝ (s + 1) ≠ 0 := by
    intro h0
    rw [Complex.Gammaℝ_eq_zero_iff] at h0
    obtain ⟨n, hn⟩ := h0
    exact hs n hn
  unfold ξ₄ L₄
  rw [hL]
  field_simp [hG]

lemma ξ₄_eq_mul_L₄_of_re_gt {s : ℂ} (hs : -1 < s.re) :
    ξ₄ s = (2 : ℂ) ^ s * Complex.Gammaℝ (s + 1) * L₄ s := by
  refine ξ₄_eq_mul_L₄ s fun n hn ↦ ?_
  have := congrArg Complex.re hn
  simp at this
  linarith

lemma ξ₄_half_ne_zero : ξ₄ (1 / 2 : ℂ) ≠ 0 := by
  rw [ξ₄_eq_mul_L₄_of_re_gt (by norm_num)]
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  · exact Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)
  · convert L₄_real_ne_zero (by norm_num : (0 : ℝ) < 1 / 2)
    norm_num

lemma ξ₄_one_sub (s : ℂ) : ξ₄ (1 - s) = ξ₄ s := by
  have hfe : ∀ z : ℂ, ξ₄ (1 - z) = DirichletCharacter.rootNumber χ₄c * ξ₄ z := by
    intro z
    unfold ξ₄
    rw [χ₄c_isPrimitive.completedLFunction_one_sub z, χ₄c_inv]
    have h4 : (4 : ℂ) ^ (z - 1 / 2) = (2 : ℂ) ^ (2 * z - 1) := by
      rw [Complex.cpow_def_of_ne_zero (by norm_num : (4 : ℂ) ≠ 0),
        Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
      have hlog4 : Complex.log (4 : ℂ) = 2 * Complex.log (2 : ℂ) := by
        rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
          ← Complex.ofReal_log (by norm_num), ← Complex.ofReal_log (by norm_num),
          show Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring]
        push_cast; ring
      rw [hlog4]; congr 1; ring
    have hpow : (2 : ℂ) ^ (1 - z) * (4 : ℂ) ^ (z - 1 / 2) = (2 : ℂ) ^ z := by
      rw [h4, ← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
      congr 1; ring
    calc (2 : ℂ) ^ (1 - z) * ((4 : ℂ) ^ (z - 1 / 2) * DirichletCharacter.rootNumber χ₄c *
          DirichletCharacter.completedLFunction χ₄c z)
        = ((2 : ℂ) ^ (1 - z) * (4 : ℂ) ^ (z - 1 / 2)) * DirichletCharacter.rootNumber χ₄c *
          DirichletCharacter.completedLFunction χ₄c z := by ring
      _ = (2 : ℂ) ^ z * DirichletCharacter.rootNumber χ₄c *
          DirichletCharacter.completedLFunction χ₄c z := by rw [hpow]
      _ = DirichletCharacter.rootNumber χ₄c *
          ((2 : ℂ) ^ z * DirichletCharacter.completedLFunction χ₄c z) := by ring
  have hroot : DirichletCharacter.rootNumber χ₄c = 1 := by
    have h12 := hfe (1 / 2 : ℂ)
    have hsub : (1 : ℂ) - 1 / 2 = 1 / 2 := by ring
    rw [hsub] at h12
    have hmul : DirichletCharacter.rootNumber χ₄c * ξ₄ (1 / 2 : ℂ) = 1 * ξ₄ (1 / 2 : ℂ) := by
      rw [one_mul]; exact h12.symm
    exact mul_right_cancel₀ ξ₄_half_ne_zero hmul
  rw [hfe s, hroot, one_mul]

noncomputable def J_sum (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (Nat.log 2 n),
    ∑ p ∈ (Nat.primesLE n).filter (fun p => p ^ (j + 1) ≤ n),
      (ZMod.χ₄ (p : ZMod 4) : ℝ) ^ (j + 1) / (j + 1 : ℕ)

lemma J_sum_eq_sum_vonMangoldt (n : ℕ) :
    (J_sum n : ℂ) = ∑ k ∈ Finset.Icc 1 n,
      χ₄c k * (ArithmeticFunction.vonMangoldt k : ℂ) / (Real.log k : ℂ) := by
  let f : ℕ → ℂ := fun k ↦ χ₄c k * (ArithmeticFunction.vonMangoldt k : ℂ) / (Real.log k : ℂ)
  have hsupp : ∑ k ∈ Finset.Icc 1 n, f k =
      ∑ k ∈ (Finset.Icc 1 n).filter IsPrimePow, f k := by
    rw [Finset.sum_filter_of_ne]
    intro k _ hne
    by_contra hnp
    exact hne (by simp [f, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnp])
  rw [hsupp]
  let S : Finset (Σ _ : ℕ, ℕ) :=
    (Finset.range (Nat.log 2 n)).sigma fun j ↦ (Nat.primesLE n).filter (fun p ↦ p ^ (j + 1) ≤ n)
  have hLHS : (J_sum n : ℂ) = ∑ x ∈ S, f (x.2 ^ (x.1 + 1)) := by
    unfold J_sum
    push_cast
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun p hp ↦ ?_
    obtain ⟨hp', _⟩ := Finset.mem_filter.mp hp
    obtain ⟨_, hprime⟩ := Nat.mem_primesLE.mp hp'
    have hlogp : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hprime.one_lt)).ne'
    have hlogpC : Complex.log (p : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg p)]
      exact Complex.ofReal_ne_zero.mpr hlogp
    have hΛ : ArithmeticFunction.vonMangoldt (p ^ (j + 1)) = Real.log p := by
      rw [ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero j),
        ArithmeticFunction.vonMangoldt_apply_prime hprime]
    have hlogpow : Real.log ((p ^ (j + 1) : ℕ) : ℝ) = ((j + 1 : ℕ) : ℝ) * Real.log p := by
      rw [Nat.cast_pow, Real.log_pow]
    dsimp only [f]
    rw [hΛ, hlogpow, Nat.cast_pow, map_pow, χ₄c_apply_nat]
    push_cast
    field_simp [hlogpC]
  rw [hLHS]
  refine Finset.sum_bij (fun x _ ↦ x.2 ^ (x.1 + 1)) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [S, Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, Nat.mem_primesLE] at hx
    obtain ⟨_, ⟨⟨_, hprime⟩, hpow⟩⟩ := hx
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.one_le_pow _ _ hprime.pos, hpow⟩, hprime.isPrimePow.pow (Nat.succ_ne_zero _)⟩
  · intro x hx y hy hxy
    simp only [S, Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, Nat.mem_primesLE] at hx hy
    have hpx : x.2.Prime := hx.2.1.2
    have hpy : y.2.Prime := hy.2.1.2
    have hp_eq : x.2 = y.2 := by
      have hdvd : x.2 ∣ y.2 ^ (y.1 + 1) := by
        rw [← hxy]; exact dvd_pow_self _ (Nat.succ_ne_zero _)
      exact (Nat.prime_dvd_prime_iff_eq hpx hpy).mp (hpx.dvd_of_dvd_pow hdvd)
    have hj_eq : x.1 = y.1 := by
      rw [hp_eq] at hxy
      have := Nat.pow_right_injective hpy.two_le hxy
      omega
    cases x; cases y; simp_all
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨_, hkn⟩, hpp⟩ := hk
    rw [isPrimePow_nat_iff] at hpp
    obtain ⟨p, a, hp, ha, rfl⟩ := hpp
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
    refine ⟨⟨j, p⟩, ?_, rfl⟩
    simp only [S, Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, Nat.mem_primesLE]
    have hjlt : j < Nat.log 2 n := by
      have h2le : 2 ^ (j + 1) ≤ n := (Nat.pow_le_pow_left hp.two_le (j + 1)).trans hkn
      have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) h2le
      omega
    have hpn : p ≤ n := (Nat.le_self_pow (Nat.succ_ne_zero j) p).trans hkn
    exact ⟨hjlt, ⟨⟨hpn, hp⟩, hkn⟩⟩
  · intro _ _; rfl

/- Section 2: Pillar 1 (Landau's theorem and holomorphic logarithm of `L₄` on `Re(s) > 1/2`) -/

lemma exists_holomorphic_log_on_convex {U : Set ℂ} (hUo : IsOpen U) (hUc : Convex ℝ U)
    (hUne : U.Nonempty) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hf0 : ∀ z ∈ U, f z ≠ 0) :
    ∃ ℓ : ℂ → ℂ, DifferentiableOn ℂ ℓ U ∧ ∀ z ∈ U, Complex.exp (ℓ z) = f z := by
  have hsc : IsSimplyConnected U := by
    have : ContractibleSpace U := hUc.contractibleSpace hUne
    exact SimplyConnectedSpace.ofContractible U
  have h0 : (0 : ℂ) ∉ f '' U := by
    rintro ⟨z, hz, hfz⟩
    exact hf0 z hz hfz
  obtain ⟨ℓ, hℓc, hℓexp⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsc hUo hf.continuousOn h0
  have hℓexp' : ∀ z ∈ U, Complex.exp (ℓ z) = f z := fun z hz ↦ hℓexp hz
  refine ⟨ℓ, ?_, hℓexp'⟩
  intro z hz
  have hU_nhds : U ∈ 𝓝 z := hUo.mem_nhds hz
  have hcont_at : ContinuousAt ℓ z := hℓc.continuousAt hU_nhds
  have hball : {w : ℂ | ‖ℓ w - ℓ z‖ < Real.pi} ∈ 𝓝 z := by
    have hcont_sub : ContinuousAt (fun w ↦ ℓ w - ℓ z) z := hcont_at.sub continuousAt_const
    have hmem : Metric.ball (0 : ℂ) Real.pi ∈ 𝓝 (ℓ z - ℓ z) := by
      rw [sub_self]; exact Metric.ball_mem_nhds 0 Real.pi_pos
    have hpre := hcont_sub.preimage_mem_nhds hmem
    filter_upwards [hpre] with w hw
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  have heq_nhds : ℓ =ᶠ[𝓝 z] fun w ↦ ℓ z + Complex.log (f w / f z) := by
    filter_upwards [hU_nhds, hball] with w hwU hwb
    have hexp_sub : Complex.exp (ℓ w - ℓ z) = f w / f z := by
      rw [Complex.exp_sub, hℓexp' w hwU, hℓexp' z hz]
    have him : |(ℓ w - ℓ z).im| < Real.pi :=
      lt_of_le_of_lt (Complex.abs_im_le_norm _) hwb
    have hlog : Complex.log (Complex.exp (ℓ w - ℓ z)) = ℓ w - ℓ z := by
      apply Complex.log_exp
      · linarith [(abs_lt.mp him).1]
      · linarith [(abs_lt.mp him).2]
    rw [← hexp_sub, hlog]
    ring
  have hdiff_at : DifferentiableAt ℂ (fun w ↦ ℓ z + Complex.log (f w / f z)) z := by
    have hfz : f z ≠ 0 := hf0 z hz
    have hdiv : DifferentiableAt ℂ (fun w ↦ f w / f z) z :=
      (hf.differentiableAt hU_nhds).div_const (f z)
    have h1 : f z / f z ∈ Complex.slitPlane := by
      rw [div_self hfz]; exact Complex.one_mem_slitPlane
    have hclog : DifferentiableAt ℂ (fun w ↦ Complex.log (f w / f z)) z :=
      DifferentiableAt.clog hdiv h1
    exact (differentiableAt_const (ℓ z)).add hclog
  exact (hdiff_at.congr_of_eventuallyEq heq_nhds).differentiableWithinAt

lemma eqOn_of_exp_eqOn_convex {U : Set ℂ} (hUo : IsOpen U) (hUc : Convex ℝ U)
    {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hexp : ∀ z ∈ U, Complex.exp (f z) = Complex.exp (g z))
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (heq₀ : f z₀ = g z₀) :
    Set.EqOn f g U := by
  have hsub_diff : DifferentiableOn ℂ (fun w ↦ f w - g w) U := hf.sub hg
  have hfderiv0 : ∀ z ∈ U, fderivWithin ℂ (fun w ↦ f w - g w) U z = 0 := by
    intro z hz
    have hUn : U ∈ 𝓝 z := hUo.mem_nhds hz
    have hfd := (hf.differentiableAt hUn).hasDerivAt
    have hgd := (hg.differentiableAt hUn).hasDerivAt
    have hsubd : HasDerivAt (fun w ↦ f w - g w) (deriv f z - deriv g z) z := hfd.sub hgd
    have hexp_eq : (fun w ↦ Complex.exp (f w - g w)) =ᶠ[𝓝 z] fun _ ↦ (1 : ℂ) := by
      filter_upwards [hUn] with w hw
      rw [Complex.exp_sub, hexp w hw, div_self (Complex.exp_ne_zero _)]
    have hd_exp : HasDerivAt (fun w ↦ Complex.exp (f w - g w))
        (Complex.exp (f z - g z) * (deriv f z - deriv g z)) z := by
      have hc := (Complex.hasDerivAt_exp (f z - g z)).comp z hsubd
      exact hc
    have hd_one : HasDerivAt (fun w ↦ Complex.exp (f w - g w)) 0 z :=
      (hasDerivAt_const z (1 : ℂ)).congr_of_eventuallyEq hexp_eq
    have hsub0 : deriv f z - deriv g z = 0 :=
      (mul_eq_zero.mp (hd_exp.unique hd_one)).resolve_left (Complex.exp_ne_zero _)
    rw [hsub0] at hsubd
    rw [fderivWithin_of_isOpen hUo hz, hsubd.hasFDerivAt.fderiv]
    ext
    simp
  have hconst : ∀ z ∈ U, f z - g z = f z₀ - g z₀ := fun z hz ↦
    hUc.is_const_of_fderivWithin_eq_zero hsub_diff hfderiv0 hz hz₀
  intro z hz
  exact sub_eq_zero.mp ((hconst z hz).trans (sub_eq_zero.mpr heq₀))

lemma exists_bound_log_pow_mul_rpow_neg (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ, 1 ≤ t → (Real.log t) ^ k * t ^ (-δ) ≤ B := by
  rcases eq_or_ne k 0 with rfl | hk
  · refine ⟨1, zero_lt_one, fun t ht ↦ ?_⟩
    rw [pow_zero, one_mul]
    exact Real.rpow_le_one_of_one_le_of_nonpos ht (by linarith)
  · have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
    refine ⟨((k : ℝ) / δ) ^ k, by positivity, fun t ht ↦ ?_⟩
    have ht0 : 0 < t := zero_lt_one.trans_le ht
    have hlog_nonneg : 0 ≤ Real.log t := Real.log_nonneg ht
    have hstep : (δ / k) * Real.log t ≤ t ^ (δ / (k : ℝ)) := by
      have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos ht0 (δ / (k : ℝ)))
      rw [Real.log_rpow ht0] at h1
      linarith
    have hpow : ((δ / k) * Real.log t) ^ k ≤ (t ^ (δ / (k : ℝ))) ^ k :=
      pow_le_pow_left₀ (by positivity) hstep k
    rw [mul_pow, ← Real.rpow_natCast (t ^ (δ / (k : ℝ))) k, ← Real.rpow_mul ht0.le,
      div_mul_cancel₀ δ hkpos.ne'] at hpow
    have hmul : (Real.log t) ^ k ≤ ((k : ℝ) / δ) ^ k * t ^ δ := by
      have hinv : ((k : ℝ) / δ) ^ k * ((δ / (k : ℝ)) ^ k * (Real.log t) ^ k) = (Real.log t) ^ k := by
        rw [← mul_assoc, ← mul_pow]
        have : ((k : ℝ) / δ) * (δ / (k : ℝ)) = 1 := by field_simp
        rw [this, one_pow, one_mul]
      calc (Real.log t) ^ k
          = ((k : ℝ) / δ) ^ k * ((δ / (k : ℝ)) ^ k * (Real.log t) ^ k) := hinv.symm
        _ ≤ ((k : ℝ) / δ) ^ k * t ^ δ := mul_le_mul_of_nonneg_left hpow (by positivity)
    calc (Real.log t) ^ k * t ^ (-δ)
        ≤ (((k : ℝ) / δ) ^ k * t ^ δ) * t ^ (-δ) :=
          mul_le_mul_of_nonneg_right hmul (Real.rpow_nonneg ht0.le _)
      _ = ((k : ℝ) / δ) ^ k * (t ^ δ * t ^ (-δ)) := by ring
      _ = ((k : ℝ) / δ) ^ k := by rw [← Real.rpow_add ht0, add_neg_cancel, Real.rpow_zero, mul_one]

lemma integrableOn_mellin_log_pow {A : ℝ → ℝ} (hAm : Measurable A) (hAnn : ∀ t, 1 < t → 0 ≤ A t)
    {σ₀ : ℝ} (hAint : IntegrableOn (fun t : ℝ ↦ A t * t ^ (-(σ₀ + 1))) (Set.Ioi (1 : ℝ)))
    (k : ℕ) {σ : ℝ} (hσ : σ₀ < σ) :
    IntegrableOn (fun t : ℝ ↦ A t * (Real.log t) ^ k * t ^ (-(σ + 1))) (Set.Ioi (1 : ℝ)) := by
  obtain ⟨B, hBpos, hB⟩ := exists_bound_log_pow_mul_rpow_neg k (sub_pos.mpr hσ)
  refine Integrable.mono' (hAint.const_mul B) ?_ ?_
  · refine ((hAm.mul (Real.measurable_log.pow_const k)).aestronglyMeasurable).mul ?_
    refine ContinuousOn.aestronglyMeasurable (fun t ht ↦ ?_) measurableSet_Ioi
    exact (Real.continuousAt_rpow_const t _ (Or.inl (zero_lt_one.trans ht).ne')).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht.le
    rw [Real.norm_of_nonneg (by positivity [hAnn t ht])]
    have hsplit : t ^ (-(σ + 1)) = t ^ (-(σ - σ₀)) * t ^ (-(σ₀ + 1)) := by
      rw [← Real.rpow_add ht0]; congr 1; ring
    rw [hsplit]
    calc A t * Real.log t ^ k * (t ^ (-(σ - σ₀)) * t ^ (-(σ₀ + 1)))
        = (Real.log t ^ k * t ^ (-(σ - σ₀))) * (A t * t ^ (-(σ₀ + 1))) := by ring
      _ ≤ B * (A t * t ^ (-(σ₀ + 1))) :=
          mul_le_mul_of_nonneg_right (hB t ht.le) (mul_nonneg (hAnn t ht) (Real.rpow_nonneg ht0.le _))

lemma iteratedDeriv_mellin_nonneg {A : ℝ → ℝ} (hAm : Measurable A) (hAnn : ∀ t, 1 < t → 0 ≤ A t)
    {σ₀ : ℝ} (hAint : IntegrableOn (fun t : ℝ ↦ A t * t ^ (-(σ₀ + 1))) (Set.Ioi (1 : ℝ))) :
    ∀ k : ℕ, ∀ s : ℂ, σ₀ < s.re →
      HasDerivAt
        (fun z ↦ ∫ t in Set.Ioi (1 : ℝ), (A t : ℂ) * (-(Real.log t : ℂ)) ^ k * (t : ℂ) ^ (-(z + 1)))
        (∫ t in Set.Ioi (1 : ℝ), (A t : ℂ) * (-(Real.log t : ℂ)) ^ (k + 1) * (t : ℂ) ^ (-(s + 1))) s ∧
      iteratedDeriv k (fun z ↦ ∫ t in Set.Ioi (1 : ℝ), (A t : ℂ) * (t : ℂ) ^ (-(z + 1))) s =
        ∫ t in Set.Ioi (1 : ℝ), (A t : ℂ) * (-(Real.log t : ℂ)) ^ k * (t : ℂ) ^ (-(s + 1)) := by
  have hstep : ∀ k : ℕ, ∀ s : ℂ, σ₀ < s.re →
      HasDerivAt
        (fun z ↦ ∫ t in Set.Ioi (1 : ℝ), (A t : ℂ) * (-(Real.log t : ℂ)) ^ k * (t : ℂ) ^ (-(z + 1)))
        (∫ t in Set.Ioi (1 : ℝ), (A t : ℂ) * (-(Real.log t : ℂ)) ^ (k + 1) * (t : ℂ) ^ (-(s + 1))) s := by
    intro k s hs
    let δ : ℝ := (s.re - σ₀) / 2
    have hδ : 0 < δ := half_pos (sub_pos.mpr hs)
    have hσ' : σ₀ < σ₀ + δ := by linarith
    have hbound := integrableOn_mellin_log_pow hAm hAnn hAint (k + 1) hσ'
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ)
      (F := fun w t ↦ (A t : ℂ) * (-(Real.log t : ℂ)) ^ k * (t : ℂ) ^ (-(w + 1)))
      (F' := fun w t ↦ (A t : ℂ) * (-(Real.log t : ℂ)) ^ (k + 1) * (t : ℂ) ^ (-(w + 1)))
      (bound := fun t ↦ A t * (Real.log t) ^ (k + 1) * t ^ (-((σ₀ + δ) + 1)))
      (Metric.ball_mem_nhds s hδ) ?_ ?_ ?_ ?_ hbound ?_).2
    · refine Eventually.of_forall fun w ↦ ?_
      have hm1 : Measurable (fun t : ℝ ↦ (A t : ℂ) * (-(Real.log t : ℂ)) ^ k) :=
        (Complex.continuous_ofReal.measurable.comp hAm).mul
          (((Complex.continuous_ofReal.measurable.comp Real.measurable_log).neg).pow_const k)
      exact hm1.aestronglyMeasurable.mul (aestronglyMeasurable_ofReal_cpow_Ioi (-(w + 1)))
    · refine Integrable.mono' (integrableOn_mellin_log_pow hAm hAnn hAint k hs) ?_ ?_
      · have hm1 : Measurable (fun t : ℝ ↦ (A t : ℂ) * (-(Real.log t : ℂ)) ^ k) :=
          (Complex.continuous_ofReal.measurable.comp hAm).mul
            (((Complex.continuous_ofReal.measurable.comp Real.measurable_log).neg).pow_const k)
        exact hm1.aestronglyMeasurable.mul (aestronglyMeasurable_ofReal_cpow_Ioi (-(s + 1)))
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0 < t := zero_lt_one.trans ht
        rw [norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg (hAnn t ht), Real.norm_of_nonneg (Real.log_nonneg ht.le),
          Complex.norm_cpow_eq_rpow_re_of_pos ht0]
        simp
    · have hm1 : Measurable (fun t : ℝ ↦ (A t : ℂ) * (-(Real.log t : ℂ)) ^ (k + 1)) :=
        (Complex.continuous_ofReal.measurable.comp hAm).mul
          (((Complex.continuous_ofReal.measurable.comp Real.measurable_log).neg).pow_const (k + 1))
      exact hm1.aestronglyMeasurable.mul (aestronglyMeasurable_ofReal_cpow_Ioi (-(s + 1)))
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
      have ht0 : 0 < t := zero_lt_one.trans ht
      have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht.le
      have hwre : σ₀ + δ < w.re := by
        have habs := Complex.abs_re_le_norm (w - s)
        rw [Metric.mem_ball, dist_eq_norm] at hw
        simp only [sub_re] at habs
        have h1 := (abs_lt.mp (habs.trans_lt hw)).1
        dsimp only [δ] at h1 ⊢
        linarith
      rw [norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (hAnn t ht), Real.norm_of_nonneg hlog0,
        Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      simp only [neg_re, add_re, one_re]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le ht.le (by linarith))
        (mul_nonneg (hAnn t ht) (pow_nonneg hlog0 _))
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w _
      have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zero_lt_one.trans ht).ne'
      have hcpow : HasDerivAt (fun u : ℂ ↦ (t : ℂ) ^ (-(u + 1)))
          ((t : ℂ) ^ (-(w + 1)) * Complex.log (t : ℂ) * (-1)) w := by
        have h1 : HasDerivAt (fun u : ℂ ↦ -(u + 1)) (-1) w :=
          ((hasDerivAt_id w).add_const (1 : ℂ)).neg
        simpa [mul_assoc] using h1.const_cpow (Or.inl ht0)
      have hlogt : Complex.log (t : ℂ) = (Real.log t : ℂ) :=
        (Complex.ofReal_log (zero_lt_one.trans ht).le).symm
      have hmul := hcpow.const_mul ((A t : ℂ) * (-(Real.log t : ℂ)) ^ k)
      have heq_val : (A t : ℂ) * (-(Real.log t : ℂ)) ^ k *
          ((t : ℂ) ^ (-(w + 1)) * Complex.log (t : ℂ) * (-1)) =
          (A t : ℂ) * (-(Real.log t : ℂ)) ^ (k + 1) * (t : ℂ) ^ (-(w + 1)) := by
        rw [hlogt, pow_succ]; ring
      rwa [heq_val] at hmul
  intro k
  induction k with
  | zero =>
    intro s hs
    exact ⟨hstep 0 s hs, by simp⟩
  | succ k ih =>
    intro s hs
    refine ⟨hstep (k + 1) s hs, ?_⟩
    rw [iteratedDeriv_succ]
    have heq_nbhd : iteratedDeriv k
        (fun z ↦ ∫ t in Set.Ioi (1 : ℝ), (A t : ℂ) * (t : ℂ) ^ (-(z + 1))) =ᶠ[𝓝 s]
        fun z ↦ ∫ t in Set.Ioi (1 : ℝ), (A t : ℂ) * (-(Real.log t : ℂ)) ^ k * (t : ℂ) ^ (-(z + 1)) := by
      filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
      exact (ih z hz).2
    rw [heq_nbhd.deriv_eq, (hstep k s hs).deriv]

lemma differentiableAt_mellin_nonneg {A : ℝ → ℝ} (hAm : Measurable A) (hAnn : ∀ t, 1 < t → 0 ≤ A t)
    {σ₀ : ℝ} (hAint : IntegrableOn (fun t : ℝ ↦ A t * t ^ (-(σ₀ + 1))) (Set.Ioi (1 : ℝ)))
    {s : ℂ} (hs : σ₀ < s.re) :
    DifferentiableAt ℂ (fun z ↦ ∫ t in Set.Ioi (1 : ℝ), (A t : ℂ) * (t : ℂ) ^ (-(z + 1))) s := by
  have hd := (iteratedDeriv_mellin_nonneg hAm hAnn hAint 0 s hs).1.differentiableAt
  simpa using hd

lemma landau_push_integrable {A : ℝ → ℝ} (hAm : Measurable A) (hAnn : ∀ t, 1 < t → 0 ≤ A t)
    {σ₁ c R r : ℝ} (hAint : IntegrableOn (fun t : ℝ ↦ A t * t ^ (-(σ₁ + 1))) (Set.Ioi (1 : ℝ)))
    (hc : σ₁ < c) (hr0 : 0 < r) (hrR : r < R)
    {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G (Metric.ball (c : ℂ) R))
    (hGeq : G =ᶠ[𝓝 (c : ℂ)] fun z ↦ ∫ t in Set.Ioi (1 : ℝ), (A t : ℂ) * (t : ℂ) ^ (-(z + 1))) :
    IntegrableOn (fun t : ℝ ↦ A t * t ^ (-(c - r + 1))) (Set.Ioi (1 : ℝ)) := by
  have hmem : ((c - r : ℝ) : ℂ) ∈ Metric.ball (c : ℂ) R := by
    rw [Metric.mem_ball, dist_eq_norm]
    have : ((c - r : ℝ) : ℂ) - (c : ℂ) = ((-r : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hr0]
    exact hrR
  have htaylor := Complex.hasSum_taylorSeries_on_ball hG hmem
  let f : ℕ → ℝ → ℝ := fun k t ↦ A t * ((r * Real.log t) ^ k / (k.factorial : ℝ)) * t ^ (-(c + 1))
  let termR : ℕ → ℝ := fun k ↦ ∫ t in Set.Ioi (1 : ℝ), f k t
  have hf_int : ∀ k : ℕ, IntegrableOn (f k) (Set.Ioi (1 : ℝ)) := by
    intro k
    have hk : IntegrableOn
        (fun t : ℝ ↦ (r ^ k / (k.factorial : ℝ)) * (A t * (Real.log t) ^ k * t ^ (-(c + 1))))
        (Set.Ioi (1 : ℝ)) :=
      (integrableOn_mellin_log_pow hAm hAnn hAint k hc).const_mul (r ^ k / (k.factorial : ℝ))
    exact hk.congr_fun (fun t _ ↦ by dsimp only [f]; rw [mul_pow]; ring) measurableSet_Ioi
  have hterm_eq : ∀ k : ℕ,
      (((k.factorial : ℂ)⁻¹ * (((c - r : ℝ) : ℂ) - (c : ℂ)) ^ k) • iteratedDeriv k G (c : ℂ)) =
      (termR k : ℂ) := by
    intro k
    rw [smul_eq_mul, hGeq.iteratedDeriv_eq k,
      (iteratedDeriv_mellin_nonneg hAm hAnn hAint k (c : ℂ) (by simpa using hc)).2]
    have hsub : ((c - r : ℝ) : ℂ) - (c : ℂ) = ((-r : ℝ) : ℂ) := by push_cast; ring
    rw [hsub, ← integral_const_mul]
    have hcast : ∀ t ∈ Set.Ioi (1 : ℝ),
        ((k.factorial : ℂ)⁻¹ * ((-r : ℝ) : ℂ) ^ k) *
          ((A t : ℂ) * (-(Real.log t : ℂ)) ^ k * (t : ℂ) ^ (-((c : ℂ) + 1))) =
        Complex.ofReal (f k t) := by
      intro t ht
      have ht0 : 0 < t := zero_lt_one.trans ht
      rw [show -((c : ℂ) + 1) = ((-(c + 1) : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow ht0.le]
      dsimp only [f]
      simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow,
        Complex.ofReal_natCast, Complex.ofReal_neg]
      have hneg : (-(r : ℂ)) ^ k * (-(Real.log t : ℂ)) ^ k = ((r : ℂ) * (Real.log t : ℂ)) ^ k := by
        rw [← mul_pow]; ring_nf
      calc (↑k.factorial)⁻¹ * (-(r : ℂ)) ^ k *
            ((A t : ℂ) * (-(Real.log t : ℂ)) ^ k * ((t ^ (-(c + 1)) : ℝ) : ℂ))
          = (A t : ℂ) * (((-(r : ℂ)) ^ k * (-(Real.log t : ℂ)) ^ k) / (k.factorial : ℂ)) *
              ((t ^ (-(c + 1)) : ℝ) : ℂ) := by ring
        _ = (A t : ℂ) * (((r : ℂ) * (Real.log t : ℂ)) ^ k / (k.factorial : ℂ)) *
              ((t ^ (-(c + 1)) : ℝ) : ℂ) := by rw [hneg]
    rw [setIntegral_congr_fun measurableSet_Ioi hcast]
    exact Complex.ofRealCLM.integral_comp_comm (hf_int k)
  have hsumR : Summable termR := by
    have h1 := (Complex.reCLM.hasSum htaylor).summable
    refine h1.congr fun k ↦ ?_
    have hsm : ((k.factorial : ℂ)⁻¹ • ((((c - r : ℝ) : ℂ) - (c : ℂ)) ^ k • iteratedDeriv k G (c : ℂ))) =
        (((k.factorial : ℂ)⁻¹ * (((c - r : ℝ) : ℂ) - (c : ℂ)) ^ k) • iteratedDeriv k G (c : ℂ)) := by
      simp only [smul_eq_mul, mul_assoc]
    show (Complex.reCLM ((k.factorial : ℂ)⁻¹ • ((((c - r : ℝ) : ℂ) - (c : ℂ)) ^ k • iteratedDeriv k G (c : ℂ)))) = termR k
    rw [hsm, hterm_eq k]
    simp
  have htermR_nn : ∀ k : ℕ, 0 ≤ termR k := by
    intro k
    refine setIntegral_nonneg measurableSet_Ioi fun t ht ↦ ?_
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht.le
    exact mul_nonneg (mul_nonneg (hAnn t ht) (by positivity)) (Real.rpow_nonneg ht0.le _)
  have hf_meas : ∀ k : ℕ, AEMeasurable (fun t ↦ ENNReal.ofReal (f k t)) (volume.restrict (Set.Ioi (1 : ℝ))) := by
    intro k
    have h1 : Measurable (fun t : ℝ ↦ A t * ((r * Real.log t) ^ k / (k.factorial : ℝ))) :=
      hAm.mul (((measurable_const.mul Real.measurable_log).pow_const k).div_const _)
    have h2 : AEStronglyMeasurable (fun t : ℝ ↦ t ^ (-(c + 1))) (volume.restrict (Set.Ioi (1 : ℝ))) :=
      ContinuousOn.aestronglyMeasurable (fun t ht ↦
        (Real.continuousAt_rpow_const t _ (Or.inl (zero_lt_one.trans ht).ne')).continuousWithinAt)
        measurableSet_Ioi
    exact (h1.aestronglyMeasurable.mul h2).aemeasurable.ennreal_ofReal
  have hlint_eq : ∀ k : ℕ,
      ∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal (f k t) = ENNReal.ofReal (termR k) := by
    intro k
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hf_int k)]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht.le
    exact mul_nonneg (mul_nonneg (hAnn t ht) (by positivity)) (Real.rpow_nonneg ht0.le _)
  have htonelli : ∫⁻ t in Set.Ioi (1 : ℝ), ∑' k : ℕ, ENNReal.ofReal (f k t) < ⊤ := by
    rw [MeasureTheory.lintegral_tsum hf_meas]
    simp_rw [hlint_eq]
    rw [← ENNReal.ofReal_tsum_of_nonneg htermR_nn hsumR]
    exact ENNReal.ofReal_lt_top
  have hpoint : ∀ᵐ t ∂(volume.restrict (Set.Ioi (1 : ℝ))),
      ENNReal.ofReal (A t * t ^ (-(c - r + 1))) = ∑' k : ℕ, ENNReal.ofReal (f k t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht.le
    have hfk_nn : ∀ k : ℕ, 0 ≤ f k t := fun k ↦
      mul_nonneg (mul_nonneg (hAnn t ht) (by positivity)) (Real.rpow_nonneg ht0.le _)
    have hexp_sum : HasSum (fun k : ℕ ↦ (r * Real.log t) ^ k / (k.factorial : ℝ))
        (Real.exp (r * Real.log t)) := by
      rw [Real.exp_eq_exp_ℝ]
      exact NormedSpace.expSeries_div_hasSum_exp (r * Real.log t)
    have hfk_sum : HasSum (fun k ↦ f k t) (A t * t ^ (-(c - r + 1))) := by
      have h1 := (hexp_sum.mul_left (A t)).mul_right (t ^ (-(c + 1)))
      have h2 : A t * Real.exp (r * Real.log t) * t ^ (-(c + 1)) = A t * t ^ (-(c - r + 1)) := by
        rw [mul_comm r, ← Real.rpow_def_of_pos ht0, mul_assoc, ← Real.rpow_add ht0]
        congr 2; ring
      rwa [h2] at h1
    rw [← ENNReal.ofReal_tsum_of_nonneg hfk_nn hfk_sum.summable, hfk_sum.tsum_eq]
  have hfin : HasFiniteIntegral (fun t : ℝ ↦ A t * t ^ (-(c - r + 1)))
      (volume.restrict (Set.Ioi (1 : ℝ))) := by
    rw [HasFiniteIntegral]
    have h_ae : ∀ᵐ t ∂(volume.restrict (Set.Ioi (1 : ℝ))),
        ‖A t * t ^ (-(c - r + 1))‖ₑ = ∑' k : ℕ, ENNReal.ofReal (f k t) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi, hpoint] with t ht hpt
      have hnn : 0 ≤ A t * t ^ (-(c - r + 1)) :=
        mul_nonneg (hAnn t ht) (Real.rpow_nonneg (zero_lt_one.trans ht).le _)
      rw [Real.enorm_eq_ofReal hnn, hpt]
    rw [MeasureTheory.lintegral_congr_ae h_ae]
    exact htonelli
  refine ⟨?_, hfin⟩
  refine hAm.aestronglyMeasurable.mul ?_
  refine ContinuousOn.aestronglyMeasurable (fun t ht ↦ ?_) measurableSet_Ioi
  exact (Real.continuousAt_rpow_const t _ (Or.inl (zero_lt_one.trans ht).ne')).continuousWithinAt

lemma abs_J_sum_le (n : ℕ) : |J_sum n| ≤ (n : ℝ) := by
  have h := J_sum_eq_sum_vonMangoldt n
  have hnorm : |J_sum n| = ‖(J_sum n : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm, h]
  calc ‖∑ k ∈ Finset.Icc 1 n, χ₄c k * (ArithmeticFunction.vonMangoldt k : ℂ) / (Real.log k : ℂ)‖
      ≤ ∑ k ∈ Finset.Icc 1 n, ‖χ₄c k * (ArithmeticFunction.vonMangoldt k : ℂ) / (Real.log k : ℂ)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.Icc 1 n, (1 : ℝ) := by
        refine Finset.sum_le_sum fun k hk ↦ ?_
        by_cases hk1 : k = 1
        · simp [hk1]
        · have h1k : 1 < k := by have := (Finset.mem_Icc.mp hk).1; omega
          have hlogpos : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast h1k)
          rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
            Real.norm_of_nonneg hlogpos.le, div_le_one hlogpos]
          calc ‖χ₄c k‖ * ArithmeticFunction.vonMangoldt k
              ≤ 1 * ArithmeticFunction.vonMangoldt k :=
                mul_le_mul_of_nonneg_right (χ₄c.norm_le_one k) ArithmeticFunction.vonMangoldt_nonneg
            _ = ArithmeticFunction.vonMangoldt k := one_mul _
            _ ≤ Real.log k := ArithmeticFunction.vonMangoldt_le_log
    _ = (n : ℝ) := by simp

noncomputable def logL₄Series (s : ℂ) : ℂ :=
  LSeries (fun n ↦ χ₄c n * (ArithmeticFunction.vonMangoldt n : ℂ) / (Real.log n : ℂ)) s

lemma exp_logL₄Series {s : ℂ} (hs : 1 < s.re) : Complex.exp (logL₄Series s) = L₄ s := by
  rw [L₄, DirichletCharacter.LFunction_eq_LSeries χ₄c hs, logL₄Series,
    DirichletCharacter.LSeries_eq_exp_LSeries χ₄c hs]

lemma logL₄Series_eq_mul_integral {s : ℂ} (hs : 1 < s.re) :
    logL₄Series s = s * ∫ t in Set.Ioi (1 : ℝ), (J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  let f : ℕ → ℂ := fun n ↦ χ₄c n * (ArithmeticFunction.vonMangoldt n : ℂ) / (Real.log n : ℂ)
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, ‖f k‖) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ) := by
    refine Asymptotics.isBigO_iff.mpr ⟨1, Eventually.of_forall fun n ↦ ?_⟩
    rw [Real.rpow_one, one_mul, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _),
      Real.norm_of_nonneg (Nat.cast_nonneg n)]
    calc ∑ k ∈ Finset.Icc 1 n, ‖f k‖
        ≤ ∑ _k ∈ Finset.Icc 1 n, (1 : ℝ) := by
          refine Finset.sum_le_sum fun k hk ↦ ?_
          by_cases hk1 : k = 1
          · simp [f, hk1]
          · have h1k : 1 < k := by have := (Finset.mem_Icc.mp hk).1; omega
            have hlogpos : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast h1k)
            simp only [f, norm_div, norm_mul, Complex.norm_real,
              Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
              Real.norm_of_nonneg hlogpos.le]
            rw [div_le_one hlogpos]
            calc ‖χ₄c k‖ * ArithmeticFunction.vonMangoldt k
                ≤ 1 * ArithmeticFunction.vonMangoldt k :=
                  mul_le_mul_of_nonneg_right (χ₄c.norm_le_one k) ArithmeticFunction.vonMangoldt_nonneg
              _ = ArithmeticFunction.vonMangoldt k := one_mul _
              _ ≤ Real.log k := ArithmeticFunction.vonMangoldt_le_log
      _ = (n : ℝ) := by simp
  have hrep := LSeries_eq_mul_integral' f zero_le_one hs hO
  rw [logL₄Series, hrep]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  rw [J_sum_eq_sum_vonMangoldt]

lemma differentiable_finite_mellin {B : ℝ → ℝ} (hBm : Measurable B) {M N₀ : ℝ}
    (hN₀ : 1 ≤ N₀) (hB : ∀ t ∈ Set.Ioo (1 : ℝ) N₀, |B t| ≤ M) :
    Differentiable ℂ (fun s : ℂ ↦ ∫ t in Set.Ioo (1 : ℝ) N₀, (B t : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
  intro s
  have hM0 : 0 ≤ max M 0 := le_max_right M 0
  let R : ℝ := |s.re| + 2
  have hbound_int : IntegrableOn (fun _ : ℝ ↦ max M 0 * Real.log N₀ * N₀ ^ (R + 1)) (Set.Ioo (1 : ℝ) N₀) :=
    integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top.ne)
  have hderiv := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ)
    (F := fun w t ↦ (B t : ℂ) * (t : ℂ) ^ (-(w + 1)))
    (F' := fun w t ↦ (B t : ℂ) * (-(Real.log t : ℂ) * (t : ℂ) ^ (-(w + 1))))
    (bound := fun _ ↦ max M 0 * Real.log N₀ * N₀ ^ (R + 1))
    (Metric.ball_mem_nhds s zero_lt_one) ?_ ?_ ?_ ?_ hbound_int ?_).2
  · exact hderiv.differentiableAt
  · refine Eventually.of_forall fun w ↦ ?_
    refine (Complex.continuous_ofReal.measurable.comp hBm).aestronglyMeasurable.mul ?_
    refine ContinuousOn.aestronglyMeasurable (fun t ht ↦ ?_) measurableSet_Ioo
    exact (Complex.continuousAt_ofReal_cpow_const t _ (Or.inr (zero_lt_one.trans ht.1).ne')).continuousWithinAt
  · refine Integrable.mono'
      (integrableOn_const (C := max M 0 * N₀ ^ (R + 1)) (s := Set.Ioo (1 : ℝ) N₀)
        (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top.ne)) ?_ ?_
    · refine (Complex.continuous_ofReal.measurable.comp hBm).aestronglyMeasurable.mul ?_
      refine ContinuousOn.aestronglyMeasurable (fun t ht ↦ ?_) measurableSet_Ioo
      exact (Complex.continuousAt_ofReal_cpow_const t _ (Or.inr (zero_lt_one.trans ht.1).ne')).continuousWithinAt
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have ht0 : 0 < t := zero_lt_one.trans ht.1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      simp only [neg_re, add_re, one_re]
      have hpow : t ^ (-(s.re + 1)) ≤ N₀ ^ (R + 1) := by
        calc t ^ (-(s.re + 1)) ≤ t ^ (R + 1) :=
              Real.rpow_le_rpow_of_exponent_le ht.1.le (by dsimp [R]; linarith [neg_abs_le s.re])
          _ ≤ N₀ ^ (R + 1) :=
              Real.rpow_le_rpow ht0.le ht.2.le (by dsimp [R]; positivity)
      exact mul_le_mul ((hB t ht).trans (le_max_left M 0)) hpow (Real.rpow_nonneg ht0.le _) hM0
  · refine (Complex.continuous_ofReal.measurable.comp hBm).aestronglyMeasurable.mul ?_
    refine ((Complex.continuous_ofReal.measurable.comp Real.measurable_log).neg.aestronglyMeasurable).mul ?_
    refine ContinuousOn.aestronglyMeasurable (fun t ht ↦ ?_) measurableSet_Ioo
    exact (Complex.continuousAt_ofReal_cpow_const t _ (Or.inr (zero_lt_one.trans ht.1).ne')).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht w hw
    have ht0 : 0 < t := zero_lt_one.trans ht.1
    have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht.1.le
    have hlogN : Real.log t ≤ Real.log N₀ := Real.log_le_log ht0 ht.2.le
    have hwre : -(w.re + 1) ≤ R + 1 := by
      have habs := Complex.abs_re_le_norm (w - s)
      rw [Metric.mem_ball, dist_eq_norm] at hw
      simp only [sub_re] at habs
      have h1 := (abs_lt.mp (habs.trans_lt hw)).1
      dsimp only [R]
      linarith [neg_abs_le s.re]
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_of_nonneg hlog0,
      Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    simp only [neg_re, add_re, one_re]
    have hpow : t ^ (-(w.re + 1)) ≤ N₀ ^ (R + 1) := by
      calc t ^ (-(w.re + 1)) ≤ t ^ (R + 1) := Real.rpow_le_rpow_of_exponent_le ht.1.le hwre
        _ ≤ N₀ ^ (R + 1) := Real.rpow_le_rpow ht0.le ht.2.le (by dsimp [R]; positivity)
    calc |B t| * (Real.log t * t ^ (-(w.re + 1)))
        ≤ max M 0 * (Real.log N₀ * N₀ ^ (R + 1)) :=
          mul_le_mul ((hB t ht).trans (le_max_left M 0))
            (mul_le_mul hlogN hpow (Real.rpow_nonneg ht0.le _) (Real.log_nonneg hN₀))
            (mul_nonneg hlog0 (Real.rpow_nonneg ht0.le _)) hM0
      _ = max M 0 * Real.log N₀ * N₀ ^ (R + 1) := by ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht w _
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zero_lt_one.trans ht.1).ne'
    have hcpow : HasDerivAt (fun u : ℂ ↦ (t : ℂ) ^ (-(u + 1)))
        ((t : ℂ) ^ (-(w + 1)) * Complex.log (t : ℂ) * (-1)) w := by
      have h1 : HasDerivAt (fun u : ℂ ↦ -(u + 1)) (-1) w :=
        ((hasDerivAt_id w).add_const (1 : ℂ)).neg
      simpa [mul_assoc] using h1.const_cpow (Or.inl ht0)
    have hlogt : Complex.log (t : ℂ) = (Real.log t : ℂ) :=
      (Complex.ofReal_log (zero_lt_one.trans ht.1).le).symm
    have hmul := hcpow.const_mul (B t : ℂ)
    simpa only [hlogt, neg_mul, mul_neg, mul_one, one_mul, mul_comm, mul_left_comm, mul_assoc] using hmul

lemma integral_Ioi_sqrt_cpow {s : ℂ} (hs : (1 : ℝ) / 2 < s.re) :
    ∫ t in Set.Ioi (1 : ℝ), (Real.sqrt t : ℂ) * (t : ℂ) ^ (-(s + 1)) = 1 / (s - 1 / 2) := by
  have heq : ∀ t ∈ Set.Ioi (1 : ℝ),
      (Real.sqrt t : ℂ) * (t : ℂ) ^ (-(s + 1)) = (t : ℂ) ^ (-(s + 1 / 2)) := by
    intro t ht
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ht0.le,
      ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht0.ne')]
    congr 1; push_cast; ring
  rw [setIntegral_congr_fun measurableSet_Ioi heq]
  have hre : (-(s + (1 : ℂ) / 2)).re < -1 := by
    simp only [neg_re, add_re, one_re, div_ofNat_re]; linarith
  rw [integral_Ioi_cpow_of_lt hre zero_lt_one]
  have h1 : ((1 : ℝ) : ℂ) ^ (-(s + 1 / 2) + 1) = 1 := by simp
  rw [h1]
  have hne : s - 1 / 2 ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this; linarith
  have hden : -(s + 1 / 2) + 1 = -(s - 1 / 2) := by ring
  rw [hden]
  field_simp [hne]

lemma integrableOn_sqrt_cpow {s : ℂ} (hs : (1 : ℝ) / 2 < s.re) :
    IntegrableOn (fun t : ℝ ↦ (Real.sqrt t : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi (1 : ℝ)) := by
  refine Integrable.mono' (integrableOn_Ioi_rpow_of_lt (by linarith : -(s.re + 1 / 2) < -1)
    (by norm_num : (0 : ℝ) < 1)) ?_ ?_
  · exact ((Complex.continuous_ofReal.measurable.comp Real.continuous_sqrt.measurable).aestronglyMeasurable).mul
      (aestronglyMeasurable_ofReal_cpow_Ioi (-(s + 1)))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Complex.norm_cpow_eq_rpow_re_of_pos ht0, Real.sqrt_eq_rpow, ← Real.rpow_add ht0]
    simp only [neg_re, add_re, one_re]
    exact le_of_eq (by congr 1; ring)

/-- Helper connecting `B = ε_sign * J_sum + C * √t` and its tail `A = if t < N₀ then 0 else B t`. -/
lemma mellin_tail_split {ε_sign C : ℝ} (hε : ε_sign = 1 ∨ ε_sign = -1) (hC : 0 < C)
    {N₀ : ℕ} (hN₀ : 1 < (N₀ : ℝ))
    {s : ℂ} (hs : (1 : ℝ) / 2 < s.re)
    (hAint : IntegrableOn (fun t : ℝ ↦ (if t < (N₀ : ℝ) then (0 : ℝ) else
      ε_sign * J_sum ⌊t⌋₊ + C * Real.sqrt t) * t ^ (-(s.re + 1))) (Set.Ioi (1 : ℝ)))
    (hAnn : ∀ t : ℝ, 1 < t → 0 ≤ if t < (N₀ : ℝ) then (0 : ℝ) else
      ε_sign * J_sum ⌊t⌋₊ + C * Real.sqrt t) :
    IntegrableOn (fun t : ℝ ↦ (J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi (1 : ℝ)) ∧
    (∫ t in Set.Ioi (1 : ℝ), Complex.ofReal (if t < (N₀ : ℝ) then (0 : ℝ) else
      ε_sign * J_sum ⌊t⌋₊ + C * Real.sqrt t) * (t : ℂ) ^ (-(s + 1))) =
      (ε_sign : ℂ) * (∫ t in Set.Ioi (1 : ℝ), (J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) +
      (C : ℂ) / (s - 1 / 2) -
      ∫ t in Set.Ioo (1 : ℝ) (N₀ : ℝ), Complex.ofReal (ε_sign * J_sum ⌊t⌋₊ + C * Real.sqrt t) * (t : ℂ) ^ (-(s + 1)) := by
  have hε_sq : ε_sign * ε_sign = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hε_abs : |ε_sign| = 1 := by rcases hε with rfl | rfl <;> norm_num
  let B : ℝ → ℝ := fun t ↦ ε_sign * J_sum ⌊t⌋₊ + C * Real.sqrt t
  let A : ℝ → ℝ := fun t ↦ if t < (N₀ : ℝ) then 0 else B t
  have hBm : Measurable B :=
    (measurable_const.mul ((measurable_of_countable J_sum).comp Nat.measurable_floor)).add
      (measurable_const.mul Real.continuous_sqrt.measurable)
  have hAm : Measurable A :=
    Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const hBm
  have hB_bdd : ∀ t ∈ Set.Ioo (1 : ℝ) (N₀ : ℝ), |B t| ≤ (N₀ : ℝ) + C * Real.sqrt N₀ := by
    intro t ht
    dsimp only [B]
    have hfl : (⌊t⌋₊ : ℝ) ≤ N₀ := (Nat.floor_le (zero_lt_one.trans ht.1).le).trans ht.2.le
    calc |ε_sign * J_sum ⌊t⌋₊ + C * Real.sqrt t|
        ≤ |ε_sign * J_sum ⌊t⌋₊| + |C * Real.sqrt t| := abs_add_le _ _
      _ = |ε_sign| * |J_sum ⌊t⌋₊| + C * Real.sqrt t := by
          rw [abs_mul, abs_mul, abs_of_pos hC, abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ 1 * (⌊t⌋₊ : ℝ) + C * Real.sqrt N₀ := by
          rw [hε_abs, one_mul, one_mul]
          exact add_le_add (abs_J_sum_le ⌊t⌋₊) (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ht.2.le) hC.le)
      _ ≤ (N₀ : ℝ) + C * Real.sqrt N₀ := by linarith
  have hMA_int : IntegrableOn (fun t : ℝ ↦ (A t : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi (1 : ℝ)) := by
    refine Integrable.mono' hAint ?_ ?_
    · exact (Complex.continuous_ofReal.measurable.comp hAm).aestronglyMeasurable.mul
        (aestronglyMeasurable_ofReal_cpow_Ioi (-(s + 1)))
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := zero_lt_one.trans ht
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hAnn t ht),
        Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      simp
  have hUnion : Set.Ioi (1 : ℝ) = Set.Ioo (1 : ℝ) (N₀ : ℝ) ∪ Set.Ici (N₀ : ℝ) := by
    ext t; simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioo, Set.mem_Ici]
    constructor
    · intro ht; by_cases h : t < (N₀ : ℝ); exact Or.inl ⟨ht, h⟩; exact Or.inr (le_of_not_gt h)
    · rintro (⟨ht, _⟩ | ht); exact ht; exact hN₀.trans_le ht
  have hdisj : Disjoint (Set.Ioo (1 : ℝ) (N₀ : ℝ)) (Set.Ici (N₀ : ℝ)) :=
    Set.disjoint_left.mpr fun _ h1 h2 ↦ not_le_of_gt h1.2 h2
  have hI1 : IntegrableOn (fun t : ℝ ↦ (B t : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioo (1 : ℝ) (N₀ : ℝ)) := by
    refine Integrable.mono' (integrableOn_const (C := ((N₀ : ℝ) + C * Real.sqrt N₀) * (N₀ : ℝ) ^ (|s.re| + 2))
      (s := Set.Ioo (1 : ℝ) (N₀ : ℝ)) (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top.ne)) ?_ ?_
    · refine (Complex.continuous_ofReal.measurable.comp hBm).aestronglyMeasurable.mul ?_
      refine ContinuousOn.aestronglyMeasurable (fun t ht ↦ ?_) measurableSet_Ioo
      exact (Complex.continuousAt_ofReal_cpow_const t _ (Or.inr (zero_lt_one.trans ht.1).ne')).continuousWithinAt
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have ht0 : 0 < t := zero_lt_one.trans ht.1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      simp only [neg_re, add_re, one_re]
      have hpow : t ^ (-(s.re + 1)) ≤ (N₀ : ℝ) ^ (|s.re| + 2) := by
        calc t ^ (-(s.re + 1)) ≤ t ^ (|s.re| + 2) :=
              Real.rpow_le_rpow_of_exponent_le ht.1.le (by linarith [neg_abs_le s.re])
          _ ≤ (N₀ : ℝ) ^ (|s.re| + 2) := Real.rpow_le_rpow ht0.le ht.2.le (by positivity)
      exact mul_le_mul (hB_bdd t ht) hpow (Real.rpow_nonneg ht0.le _) (by positivity)
  have hI2 : IntegrableOn (fun t : ℝ ↦ (B t : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ici (N₀ : ℝ)) :=
    (hMA_int.mono_set (fun _ ht ↦ hN₀.trans_le ht)).congr_fun
      (fun t ht ↦ by simp [A, not_lt_of_ge (Set.mem_Ici.mp ht)]) measurableSet_Ici
  have hint_B : IntegrableOn (fun t : ℝ ↦ (B t : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi (1 : ℝ)) := by
    rw [hUnion, integrableOn_union]; exact ⟨hI1, hI2⟩
  have hint_sq := integrableOn_sqrt_cpow hs
  have hint_J : IntegrableOn (fun t : ℝ ↦ (J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi (1 : ℝ)) := by
    have h1 : IntegrableOn
        (fun t : ℝ ↦ (ε_sign : ℂ) * ((B t : ℂ) * (t : ℂ) ^ (-(s + 1)) -
          (C : ℂ) * ((Real.sqrt t : ℂ) * (t : ℂ) ^ (-(s + 1)))))
        (Set.Ioi (1 : ℝ)) :=
      (hint_B.sub (hint_sq.const_mul (C : ℂ))).const_mul (ε_sign : ℂ)
    refine h1.congr_fun (fun t _ ↦ ?_) measurableSet_Ioi
    have hεC : (ε_sign : ℂ) * (ε_sign : ℂ) = 1 := by exact_mod_cast hε_sq
    dsimp only [B]; push_cast
    calc (ε_sign : ℂ) * (((ε_sign : ℂ) * (J_sum ⌊t⌋₊ : ℂ) + (C : ℂ) * (Real.sqrt t : ℂ)) *
          (t : ℂ) ^ (-(s + 1)) - (C : ℂ) * ((Real.sqrt t : ℂ) * (t : ℂ) ^ (-(s + 1))))
        = ((ε_sign : ℂ) * (ε_sign : ℂ)) * ((J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) := by ring
      _ = (J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)) := by rw [hεC, one_mul]
  refine ⟨hint_J, ?_⟩
  have hB_split : ∫ t in Set.Ioi (1 : ℝ), (B t : ℂ) * (t : ℂ) ^ (-(s + 1)) =
      (∫ t in Set.Ioo (1 : ℝ) (N₀ : ℝ), (B t : ℂ) * (t : ℂ) ^ (-(s + 1))) +
      (∫ t in Set.Ioi (1 : ℝ), (A t : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
    conv_lhs => rw [hUnion]
    rw [MeasureTheory.setIntegral_union hdisj measurableSet_Ici hI1 hI2]
    congr 1
    have hMA_split : ∫ t in Set.Ioi (1 : ℝ), (A t : ℂ) * (t : ℂ) ^ (-(s + 1)) =
        (∫ t in Set.Ioo (1 : ℝ) (N₀ : ℝ), (A t : ℂ) * (t : ℂ) ^ (-(s + 1))) +
        (∫ t in Set.Ici (N₀ : ℝ), (A t : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
      rw [hUnion, MeasureTheory.setIntegral_union hdisj measurableSet_Ici
        (hMA_int.mono_set (fun _ ht ↦ ht.1)) (hMA_int.mono_set (fun _ ht ↦ hN₀.trans_le ht))]
    rw [hMA_split]
    have hzero : ∫ t in Set.Ioo (1 : ℝ) (N₀ : ℝ), (A t : ℂ) * (t : ℂ) ^ (-(s + 1)) = 0 := by
      rw [setIntegral_congr_fun (g := fun _ ↦ (0 : ℂ)) measurableSet_Ioo (fun t ht ↦ by simp [A, ht.2])]
      simp
    rw [hzero, zero_add]
    exact setIntegral_congr_fun measurableSet_Ici fun t ht ↦ by
      simp [A, not_lt_of_ge (Set.mem_Ici.mp ht)]
  have hB_decomp : ∫ t in Set.Ioi (1 : ℝ), (B t : ℂ) * (t : ℂ) ^ (-(s + 1)) =
      (ε_sign : ℂ) * (∫ t in Set.Ioi (1 : ℝ), (J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) +
      (C : ℂ) / (s - 1 / 2) := by
    have hfun : ∀ t ∈ Set.Ioi (1 : ℝ),
        (B t : ℂ) * (t : ℂ) ^ (-(s + 1)) =
        (ε_sign : ℂ) * ((J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) +
        (C : ℂ) * ((Real.sqrt t : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
      intro t _; dsimp only [B]; push_cast; ring
    rw [setIntegral_congr_fun measurableSet_Ioi hfun,
      MeasureTheory.integral_add (hint_J.const_mul _) (hint_sq.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      integral_Ioi_sqrt_cpow hs]
    ring
  linear_combination hB_decomp - hB_split

/-- **Pillar 1 (Unified Landau Theorem)**: If `ε_sign * J_sum n ≥ -C √n / log n` eventually,
then `L₄` has no zeros in `{s | 1/2 < s.re}`, and `L₄` has a holomorphic logarithm `ℓ` there
given by the absolutely convergent Mellin integral of `J_sum`. -/
theorem pillar1_landau {ε_sign C : ℝ} (hε : ε_sign = 1 ∨ ε_sign = -1) (hC : 0 < C)
    (hbound : ∀ᶠ n : ℕ in atTop, -C * (Real.sqrt n / Real.log n) ≤ ε_sign * J_sum n) :
    (∀ s : ℂ, 1 / 2 < s.re → L₄ s ≠ 0) ∧
    ∃ ℓ : ℂ → ℂ, DifferentiableOn ℂ ℓ {s : ℂ | 1 / 2 < s.re} ∧
      (∀ s : ℂ, 1 / 2 < s.re → Complex.exp (ℓ s) = L₄ s) ∧
      (∀ s : ℂ, 1 / 2 < s.re →
        IntegrableOn (fun t : ℝ ↦ (J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi (1 : ℝ))) ∧
      (∀ s : ℂ, 1 / 2 < s.re →
        ℓ s / s = ∫ t in Set.Ioi (1 : ℝ), (J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
  have hε_sq : ε_sign * ε_sign = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hε_abs : |ε_sign| = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hε_ne : (ε_sign : ℂ) ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  obtain ⟨N₀', hN₀'⟩ := Filter.eventually_atTop.mp hbound
  let N₀ : ℕ := max N₀' 3
  have hN₀_ge3 : 3 ≤ N₀ := le_max_right _ _
  have hN₀_real : (1 : ℝ) < (N₀ : ℝ) := by exact_mod_cast (show 1 < N₀ by omega)
  let B : ℝ → ℝ := fun t ↦ ε_sign * J_sum ⌊t⌋₊ + C * Real.sqrt t
  let A : ℝ → ℝ := fun t ↦ if t < (N₀ : ℝ) then 0 else B t
  have hBm : Measurable B :=
    (measurable_const.mul ((measurable_of_countable J_sum).comp Nat.measurable_floor)).add
      (measurable_const.mul Real.continuous_sqrt.measurable)
  have hAm : Measurable A :=
    Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const hBm
  have hAnn : ∀ t : ℝ, 1 < t → 0 ≤ A t := by
    intro t _
    dsimp only [A]
    split_ifs with hlt
    · exact le_rfl
    · push Not at hlt
      have hfl : N₀ ≤ ⌊t⌋₊ := Nat.le_floor hlt
      have h3fl : 3 ≤ ⌊t⌋₊ := hN₀_ge3.trans hfl
      have hge := hN₀' ⌊t⌋₊ ((le_max_left _ _).trans hfl)
      have hlog1 : 1 ≤ Real.log (⌊t⌋₊ : ℝ) := by
        have h3 : Real.exp 1 ≤ (3 : ℝ) := by linarith [Real.exp_one_lt_d9]
        have hle3 : (3 : ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast h3fl
        rw [← Real.log_exp 1]
        exact Real.log_le_log (Real.exp_pos 1) (h3.trans hle3)
      have hsq : Real.sqrt (⌊t⌋₊ : ℝ) / Real.log (⌊t⌋₊ : ℝ) ≤ Real.sqrt t := by
        calc Real.sqrt (⌊t⌋₊ : ℝ) / Real.log (⌊t⌋₊ : ℝ)
            ≤ Real.sqrt (⌊t⌋₊ : ℝ) / 1 :=
              div_le_div_of_nonneg_left (Real.sqrt_nonneg _) zero_lt_one hlog1
          _ = Real.sqrt (⌊t⌋₊ : ℝ) := div_one _
          _ ≤ Real.sqrt t := Real.sqrt_le_sqrt (Nat.floor_le (by linarith))
      dsimp only [B]
      nlinarith
  have hB_bdd : ∀ t ∈ Set.Ioo (1 : ℝ) (N₀ : ℝ), |B t| ≤ (N₀ : ℝ) + C * Real.sqrt N₀ := by
    intro t ht
    dsimp only [B]
    have hfl : (⌊t⌋₊ : ℝ) ≤ N₀ := (Nat.floor_le (zero_lt_one.trans ht.1).le).trans ht.2.le
    calc |ε_sign * J_sum ⌊t⌋₊ + C * Real.sqrt t|
        ≤ |ε_sign * J_sum ⌊t⌋₊| + |C * Real.sqrt t| := abs_add_le _ _
      _ = |ε_sign| * |J_sum ⌊t⌋₊| + C * Real.sqrt t := by
          rw [abs_mul, abs_mul, abs_of_pos hC, abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ 1 * (⌊t⌋₊ : ℝ) + C * Real.sqrt N₀ := by
          rw [hε_abs, one_mul, one_mul]
          exact add_le_add (abs_J_sum_le ⌊t⌋₊) (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ht.2.le) hC.le)
      _ ≤ (N₀ : ℝ) + C * Real.sqrt N₀ := by linarith
  have hAint_gt1 : ∀ {σ : ℝ}, 1 < σ →
      IntegrableOn (fun t : ℝ ↦ A t * t ^ (-(σ + 1))) (Set.Ioi (1 : ℝ)) := by
    intro σ hσ
    refine Integrable.mono'
      ((integrableOn_Ioi_rpow_of_lt (by linarith : -σ < -1) (by norm_num : (0 : ℝ) < 1)).const_mul (1 + C))
      ?_ ?_
    · refine hAm.aestronglyMeasurable.mul ?_
      refine ContinuousOn.aestronglyMeasurable (fun t ht ↦ ?_) measurableSet_Ioi
      exact (Real.continuousAt_rpow_const t _ (Or.inl (zero_lt_one.trans ht).ne')).continuousWithinAt
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := zero_lt_one.trans ht
      rw [Real.norm_of_nonneg (mul_nonneg (hAnn t ht) (Real.rpow_nonneg ht0.le _))]
      have hAle : A t ≤ (1 + C) * t := by
        dsimp only [A]
        split_ifs
        · positivity
        · dsimp only [B]
          have hsqt : Real.sqrt t ≤ t := by
            rw [Real.sqrt_le_left ht0.le]; nlinarith [ht]
          have hJ : ε_sign * J_sum ⌊t⌋₊ ≤ t := by
            calc ε_sign * J_sum ⌊t⌋₊ ≤ |ε_sign * J_sum ⌊t⌋₊| := le_abs_self _
              _ = |J_sum ⌊t⌋₊| := by rw [abs_mul, hε_abs, one_mul]
              _ ≤ (⌊t⌋₊ : ℝ) := abs_J_sum_le ⌊t⌋₊
              _ ≤ t := Nat.floor_le ht0.le
          nlinarith
      calc A t * t ^ (-(σ + 1))
          ≤ ((1 + C) * t) * t ^ (-(σ + 1)) :=
            mul_le_mul_of_nonneg_right hAle (Real.rpow_nonneg ht0.le _)
        _ = (1 + C) * (t ^ (1 : ℝ) * t ^ (-(σ + 1))) := by rw [Real.rpow_one]; ring
        _ = (1 + C) * t ^ (-σ) := by rw [← Real.rpow_add ht0]; congr 2; ring
  let M_A : ℂ → ℂ := fun s ↦ ∫ t in Set.Ioi (1 : ℝ), (A t : ℂ) * (t : ℂ) ^ (-(s + 1))
  let H_fin : ℂ → ℂ := fun s ↦ ∫ t in Set.Ioo (1 : ℝ) (N₀ : ℝ), (B t : ℂ) * (t : ℂ) ^ (-(s + 1))
  have hH_diff : Differentiable ℂ H_fin :=
    differentiable_finite_mellin hBm hN₀_real.le hB_bdd
  have hMA_eq_gt1 : ∀ s : ℂ, 1 < s.re →
      M_A s = (ε_sign : ℂ) * (logL₄Series s / s) + (C : ℂ) / (s - 1 / 2) - H_fin s := by
    intro s hs
    have hsne : s ≠ 0 := by intro h0; rw [h0, zero_re] at hs; linarith
    have hsp := (mellin_tail_split hε hC hN₀_real (by linarith) (hAint_gt1 hs) hAnn).2
    rw [logL₄Series_eq_mul_integral hs, mul_div_cancel_left₀ _ hsne]
    exact hsp
  let Zre : Set ℝ := {1 / 2} ∪ {x : ℝ | ∃ s : ℂ, s.re = x ∧ 1 / 2 < s.re ∧ L₄ s = 0}
  have hZre_ne : Zre.Nonempty := ⟨1 / 2, Or.inl rfl⟩
  have hZre_bdd : BddAbove Zre := by
    refine ⟨1, fun x hx ↦ ?_⟩
    rcases hx with rfl | ⟨s, rfl, _, hs0⟩
    · norm_num
    · by_contra hgt
      push Not at hgt
      exact Complex.exp_ne_zero _ (hs0 ▸ exp_logL₄Series hgt)
  let σ₀ : ℝ := sSup Zre
  have hσ₀_ge : (1 : ℝ) / 2 ≤ σ₀ := le_csSup hZre_bdd (Or.inl rfl)
  have hσ₀_le : σ₀ ≤ 1 := csSup_le hZre_ne (fun x hx ↦ by
    rcases hx with rfl | ⟨s, rfl, _, hs0⟩
    · norm_num
    · by_contra hgt; push Not at hgt
      exact Complex.exp_ne_zero _ (hs0 ▸ exp_logL₄Series hgt))
  have hL₄_ne_zero_gt : ∀ s : ℂ, σ₀ < s.re → L₄ s ≠ 0 := by
    intro s hs hs0
    exact not_le_of_gt hs (le_csSup hZre_bdd (Or.inr ⟨s, rfl, lt_of_le_of_lt hσ₀_ge hs, hs0⟩))
  let Ω : Set ℂ := {s : ℂ | σ₀ < s.re}
  have hΩ_open : IsOpen Ω := isOpen_lt continuous_const continuous_re
  have hΩ_conv : Convex ℝ Ω := convex_halfSpace_re_gt σ₀
  have h2_mem : (2 : ℂ) ∈ Ω := by show σ₀ < (2 : ℂ).re; simp; linarith
  obtain ⟨ℓ₁_raw, hℓ₁_raw_diff, hℓ₁_raw_exp⟩ :=
    exists_holomorphic_log_on_convex hΩ_open hΩ_conv ⟨2, h2_mem⟩
      (differentiable_L₄.differentiableOn.mono (Set.subset_univ _)) hL₄_ne_zero_gt
  let c₁ : ℂ := logL₄Series 2 - ℓ₁_raw 2
  let ℓ₁ : ℂ → ℂ := fun s ↦ ℓ₁_raw s + c₁
  have hℓ₁_diff : DifferentiableOn ℂ ℓ₁ Ω := hℓ₁_raw_diff.add_const c₁
  have hℓ₁_exp : ∀ s ∈ Ω, Complex.exp (ℓ₁ s) = L₄ s := by
    intro s hs
    have hc1_exp : Complex.exp c₁ = 1 := by
      dsimp only [c₁]
      rw [Complex.exp_sub, exp_logL₄Series (by simp), hℓ₁_raw_exp 2 h2_mem,
        div_self (hL₄_ne_zero_gt 2 h2_mem)]
    dsimp only [ℓ₁]
    rw [Complex.exp_add, hc1_exp, mul_one, hℓ₁_raw_exp s hs]
  have hℓ₁_eq_series : ∀ s : ℂ, 1 < s.re → ℓ₁ s = logL₄Series s := by
    let Ω₁ : Set ℂ := {s : ℂ | 1 < s.re}
    have hΩ₁_open : IsOpen Ω₁ := isOpen_lt continuous_const continuous_re
    have hΩ₁_conv : Convex ℝ Ω₁ := convex_halfSpace_re_gt 1
    have hΩ₁_sub : Ω₁ ⊆ Ω := fun z hz ↦ lt_of_le_of_lt hσ₀_le hz
    have hlogS_diff : DifferentiableOn ℂ logL₄Series Ω₁ := by
      intro z hz
      have hre : 1 < z.re := hz
      let σm : ℝ := (1 + z.re) / 2
      have hσm1 : 1 < σm := by dsimp only [σm]; linarith
      have hσmz : σm < z.re := by dsimp only [σm]; linarith
      have hMA_d : DifferentiableAt ℂ M_A z :=
        differentiableAt_mellin_nonneg hAm hAnn (hAint_gt1 hσm1) hσmz
      have hneh : z - 1 / 2 ≠ 0 := by intro h0; have := congrArg Complex.re h0; simp at this; linarith
      have hrhs_d : DifferentiableAt ℂ
          (fun w ↦ (ε_sign : ℂ) * w * (M_A w - (C : ℂ) / (w - 1 / 2) + H_fin w)) z :=
        ((differentiableAt_id.const_mul _).mul
          ((hMA_d.sub ((differentiableAt_const _).div (differentiableAt_id.sub_const _) hneh)).add
            (hH_diff z)))
      have heq_nhds : logL₄Series =ᶠ[𝓝 z]
          fun w ↦ (ε_sign : ℂ) * w * (M_A w - (C : ℂ) / (w - 1 / 2) + H_fin w) := by
        filter_upwards [hΩ₁_open.mem_nhds hz] with w hw
        have hwre : 1 < w.re := hw
        have hwne : w ≠ 0 := by intro h0; rw [h0, zero_re] at hwre; linarith
        have hεC : (ε_sign : ℂ) * (ε_sign : ℂ) = 1 := by exact_mod_cast hε_sq
        rw [hMA_eq_gt1 w hwre]
        calc logL₄Series w = 1 * (w * (logL₄Series w / w)) := by rw [one_mul, mul_div_cancel₀ _ hwne]
          _ = ((ε_sign : ℂ) * (ε_sign : ℂ)) * (w * (logL₄Series w / w)) := by rw [hεC]
          _ = (ε_sign : ℂ) * w * (((ε_sign : ℂ) * (logL₄Series w / w) + (C : ℂ) / (w - 1 / 2) - H_fin w) -
                (C : ℂ) / (w - 1 / 2) + H_fin w) := by ring
      exact (hrhs_d.congr_of_eventuallyEq heq_nhds).differentiableWithinAt
    exact fun s hs ↦ eqOn_of_exp_eqOn_convex hΩ₁_open hΩ₁_conv (hℓ₁_diff.mono hΩ₁_sub) hlogS_diff
      (fun z hz ↦ by rw [hℓ₁_exp z (hΩ₁_sub hz), exp_logL₄Series hz])
      (show (1 : ℝ) < (2 : ℂ).re by simp) (by dsimp [ℓ₁, c₁]; ring) hs
  let G₁ : ℂ → ℂ := fun s ↦ (ε_sign : ℂ) * (ℓ₁ s / s) + (C : ℂ) / (s - 1 / 2) - H_fin s
  have hG₁_diff : DifferentiableOn ℂ G₁ Ω := by
    have hne0 : ∀ s ∈ Ω, s ≠ 0 := fun s hs h0 ↦ by
      have hsre : σ₀ < s.re := hs; rw [h0, zero_re] at hsre; linarith
    have hneh : ∀ s ∈ Ω, s - 1 / 2 ≠ 0 := fun s hs h0 ↦ by
      have hsre : σ₀ < s.re := hs; have := congrArg Complex.re h0; simp at this; linarith
    exact (((hℓ₁_diff.div differentiableOn_id hne0).const_mul _).add
      ((differentiableOn_const _).div (differentiableOn_id.sub_const _) hneh)).sub
      hH_diff.differentiableOn
  have hG₁_eq_MA : ∀ s : ℂ, 1 < s.re → G₁ s = M_A s := by
    intro s hs; rw [hMA_eq_gt1 s hs]; dsimp only [G₁]; rw [hℓ₁_eq_series s hs]
  -- PUSH 1: Integrability for all σ > σ₀
  have hAint_gt_σ₀ : ∀ {σ : ℝ}, σ₀ < σ →
      IntegrableOn (fun t : ℝ ↦ A t * t ^ (-(σ + 1))) (Set.Ioi (1 : ℝ)) := by
    intro σ hσ
    by_cases h1 : 1 < σ
    · exact hAint_gt1 h1
    · push Not at h1
      have hball_sub : Metric.ball (2 : ℂ) (2 - σ₀) ⊆ Ω := by
        intro z hz
        rw [Metric.mem_ball, dist_eq_norm] at hz
        have habs := Complex.abs_re_le_norm (z - 2)
        simp only [sub_re, re_ofNat] at habs
        have hlow := (abs_lt.mp (habs.trans_lt hz)).1
        show σ₀ < z.re; linarith
      have hG₁_nbhd : G₁ =ᶠ[𝓝 (2 : ℂ)] M_A := by
        filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds (by simp : (1 : ℝ) < (2 : ℂ).re)]
          with z hz
        exact hG₁_eq_MA z hz
      have hpush := landau_push_integrable hAm hAnn (hAint_gt1 (by norm_num : (1 : ℝ) < 3 / 2))
        (by norm_num : (3 : ℝ) / 2 < 2) (by linarith : 0 < 2 - σ) (by linarith : 2 - σ < 2 - σ₀)
        (hG₁_diff.mono hball_sub) hG₁_nbhd
      simpa [show (2 : ℝ) - (2 - σ) = σ by ring] using hpush
  -- Prove σ₀ = 1/2 by contradiction (PUSH 2)
  have hσ₀_eq_half : σ₀ = 1 / 2 := by
    by_contra hne
    have hσ₀_gt : (1 : ℝ) / 2 < σ₀ := lt_of_le_of_ne hσ₀_ge (Ne.symm hne)
    have hopen_ne : IsOpen {z : ℂ | L₄ z ≠ 0} := isOpen_ne.preimage differentiable_L₄.continuous
    obtain ⟨δ₀, hδ₀_pos, hδ₀_ball⟩ := Metric.isOpen_iff.mp hopen_ne (σ₀ : ℂ) (L₄_real_ne_zero (by linarith))
    let δ : ℝ := min (δ₀ / 3) (min ((σ₀ - 1 / 2) / 4) (1 / 4))
    have hδ_pos : 0 < δ := by positivity
    have h2δ_lt : 2 * δ < δ₀ := by linarith [min_le_left (δ₀ / 3) (min ((σ₀ - 1 / 2) / 4) (1 / 4))]
    have hδ_half : 2 * δ < σ₀ - 1 / 2 := by
      have : δ ≤ (σ₀ - 1 / 2) / 4 := (min_le_right _ _).trans (min_le_left _ _)
      linarith
    have hδ_q : δ ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
    have hball_ne : ∀ z ∈ Metric.ball (σ₀ : ℂ) (2 * δ), L₄ z ≠ 0 :=
      fun z hz ↦ hδ₀_ball (Metric.ball_subset_ball h2δ_lt.le hz)
    let c : ℝ := σ₀ + δ / 2
    have hc_mem_B : (c : ℂ) ∈ Metric.ball (σ₀ : ℂ) (2 * δ) := by
      rw [Metric.mem_ball, dist_eq_norm,
        show (c : ℂ) - (σ₀ : ℂ) = ((δ / 2 : ℝ) : ℂ) by dsimp [c]; push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      linarith
    have hc_mem_Ω : (c : ℂ) ∈ Ω := by show σ₀ < (c : ℂ).re; simp [c]; linarith
    obtain ⟨ℓ₂_raw, hℓ₂_raw_diff, hℓ₂_raw_exp⟩ :=
      exists_holomorphic_log_on_convex Metric.isOpen_ball (convex_ball _ _) ⟨(c : ℂ), hc_mem_B⟩
        (differentiable_L₄.differentiableOn.mono (Set.subset_univ _)) hball_ne
    let c₂ : ℂ := ℓ₁ (c : ℂ) - ℓ₂_raw (c : ℂ)
    let ℓ₂ : ℂ → ℂ := fun z ↦ ℓ₂_raw z + c₂
    have hℓ₂_diff : DifferentiableOn ℂ ℓ₂ (Metric.ball (σ₀ : ℂ) (2 * δ)) :=
      hℓ₂_raw_diff.add_const c₂
    have hℓ₂_exp : ∀ z ∈ Metric.ball (σ₀ : ℂ) (2 * δ), Complex.exp (ℓ₂ z) = L₄ z := by
      intro z hz
      have hc2_exp : Complex.exp c₂ = 1 := by
        dsimp only [c₂]
        rw [Complex.exp_sub, hℓ₁_exp (c : ℂ) hc_mem_Ω, hℓ₂_raw_exp (c : ℂ) hc_mem_B,
          div_self (hball_ne (c : ℂ) hc_mem_B)]
      dsimp only [ℓ₂]
      rw [Complex.exp_add, hc2_exp, mul_one, hℓ₂_raw_exp z hz]
    have hℓ₂_eq_ℓ₁ : Set.EqOn ℓ₂ ℓ₁ (Ω ∩ Metric.ball (σ₀ : ℂ) (2 * δ)) :=
      eqOn_of_exp_eqOn_convex (hΩ_open.inter Metric.isOpen_ball) (hΩ_conv.inter (convex_ball _ _))
        (hℓ₂_diff.mono Set.inter_subset_right) (hℓ₁_diff.mono Set.inter_subset_left)
        (fun z hz ↦ by rw [hℓ₂_exp z hz.2, hℓ₁_exp z hz.1])
        ⟨hc_mem_Ω, hc_mem_B⟩ (by dsimp [ℓ₂, c₂]; ring)
    let G₂ : ℂ → ℂ := fun z ↦ (ε_sign : ℂ) * (ℓ₂ z / z) + (C : ℂ) / (z - 1 / 2) - H_fin z
    have hG₂_diff : DifferentiableOn ℂ G₂ (Metric.ball (σ₀ : ℂ) (2 * δ)) := by
      have hre_gt : ∀ z ∈ Metric.ball (σ₀ : ℂ) (2 * δ), (1 : ℝ) / 2 < z.re := by
        intro z hz
        rw [Metric.mem_ball, dist_eq_norm] at hz
        have habs := Complex.abs_re_le_norm (z - (σ₀ : ℂ))
        simp only [sub_re, ofReal_re] at habs
        linarith [(abs_lt.mp (habs.trans_lt hz)).1]
      have hne0 : ∀ z ∈ Metric.ball (σ₀ : ℂ) (2 * δ), z ≠ 0 := fun z hz h0 ↦ by
        have := hre_gt z hz; rw [h0, zero_re] at this; linarith
      have hneh : ∀ z ∈ Metric.ball (σ₀ : ℂ) (2 * δ), z - 1 / 2 ≠ 0 := fun z hz h0 ↦ by
        have := hre_gt z hz; have h1 := congrArg Complex.re h0; simp at h1; linarith
      exact (((hℓ₂_diff.div differentiableOn_id hne0).const_mul _).add
        ((differentiableOn_const _).div (differentiableOn_id.sub_const _) hneh)).sub
        hH_diff.differentiableOn
    let σ₁ : ℝ := σ₀ + δ / 4
    have hMA_diff_σ₁ : DifferentiableOn ℂ M_A {z : ℂ | σ₁ < z.re} := fun z hz ↦
      (differentiableAt_mellin_nonneg hAm hAnn (hAint_gt_σ₀ (by dsimp [σ₁]; linarith)) hz).differentiableWithinAt
    have hG₁_eq_MA_σ₁ : Set.EqOn G₁ M_A {z : ℂ | σ₁ < z.re} := by
      refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
        ((hG₁_diff.mono (fun z (hz : σ₁ < z.re) ↦ show σ₀ < z.re by dsimp [σ₁] at hz; linarith)).analyticOnNhd
          (isOpen_lt continuous_const continuous_re))
        (hMA_diff_σ₁.analyticOnNhd (isOpen_lt continuous_const continuous_re))
        (convex_halfSpace_re_gt σ₁).isPreconnected
        (show σ₁ < (2 : ℂ).re by simp [σ₁]; linarith) ?_
      filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds (by simp : (1 : ℝ) < (2 : ℂ).re)]
        with z hz
      exact hG₁_eq_MA z hz
    have hG₂_eq_MA_nhds : G₂ =ᶠ[𝓝 (c : ℂ)] M_A := by
      have hnbhd : ({z : ℂ | σ₁ < z.re} ∩ Metric.ball (σ₀ : ℂ) (2 * δ)) ∈ 𝓝 (c : ℂ) :=
        Filter.inter_mem ((isOpen_lt continuous_const continuous_re).mem_nhds
          (show σ₁ < (c : ℂ).re by simp [σ₁, c]; linarith))
          (Metric.isOpen_ball.mem_nhds hc_mem_B)
      filter_upwards [hnbhd] with z hz
      have hz1 : σ₁ < z.re := hz.1
      have hzΩ : z ∈ Ω := show σ₀ < z.re by dsimp only [σ₁] at hz1; linarith
      have hG21 : G₂ z = G₁ z := by dsimp only [G₂, G₁]; rw [hℓ₂_eq_ℓ₁ ⟨hzΩ, hz.2⟩]
      rw [hG21, hG₁_eq_MA_σ₁ hz.1]
    have hball_c : Metric.ball (c : ℂ) δ ⊆ Metric.ball (σ₀ : ℂ) (2 * δ) := by
      intro z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
      have hcs : ‖(c : ℂ) - (σ₀ : ℂ)‖ = δ / 2 := by
        rw [show (c : ℂ) - (σ₀ : ℂ) = ((δ / 2 : ℝ) : ℂ) by dsimp [c]; push_cast; ring,
          Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      calc ‖z - (σ₀ : ℂ)‖ = ‖(z - (c : ℂ)) + ((c : ℂ) - (σ₀ : ℂ))‖ := by ring_nf
        _ ≤ ‖z - (c : ℂ)‖ + ‖(c : ℂ) - (σ₀ : ℂ)‖ := norm_add_le _ _
        _ < δ + δ / 2 := by rw [hcs]; linarith
        _ < 2 * δ := by linarith
    have hAint_past : IntegrableOn (fun t : ℝ ↦ A t * t ^ (-((σ₀ - δ / 4) + 1))) (Set.Ioi (1 : ℝ)) := by
      have hpush := landau_push_integrable hAm hAnn (hAint_gt_σ₀ (by dsimp [σ₁]; linarith))
        (show σ₁ < c by dsimp [σ₁, c]; linarith)
        (show 0 < 3 * δ / 4 by linarith) (show 3 * δ / 4 < δ by linarith)
        (hG₂_diff.mono hball_c) hG₂_eq_MA_nhds
      simpa [show c - 3 * δ / 4 = σ₀ - δ / 4 by dsimp [c]; ring] using hpush
    let σ_ext : ℝ := σ₀ - δ / 4
    have hσ_ext_gt : (1 : ℝ) / 2 < σ_ext := by dsimp [σ_ext]; linarith
    let U_ext : Set ℂ := {z : ℂ | σ_ext < z.re}
    have hMA_diff_ext : DifferentiableOn ℂ M_A U_ext := fun z hz ↦
      (differentiableAt_mellin_nonneg hAm hAnn hAint_past hz).differentiableWithinAt
    let ℓ_ext : ℂ → ℂ := fun z ↦ (ε_sign : ℂ) * z * (M_A z - (C : ℂ) / (z - 1 / 2) + H_fin z)
    have hℓ_ext_diff : DifferentiableOn ℂ ℓ_ext U_ext := by
      have hneh : ∀ z ∈ U_ext, z - 1 / 2 ≠ 0 := fun z hz h0 ↦ by
        have := congrArg Complex.re h0; simp at this; linarith [show σ_ext < z.re from hz]
      exact (differentiableOn_id.const_mul _).mul
        ((hMA_diff_ext.sub ((differentiableOn_const _).div (differentiableOn_id.sub_const _) hneh)).add
          hH_diff.differentiableOn)
    have hexp_ext : Set.EqOn (fun z ↦ Complex.exp (ℓ_ext z)) L₄ U_ext := by
      refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
        ((Complex.differentiable_exp.comp_differentiableOn hℓ_ext_diff).analyticOnNhd
          (isOpen_lt continuous_const continuous_re))
        (differentiable_L₄.differentiableOn.analyticOnNhd (isOpen_lt continuous_const continuous_re))
        (convex_halfSpace_re_gt σ_ext).isPreconnected
        (show σ_ext < (2 : ℂ).re by simp [σ_ext]; linarith) ?_
      filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds (by simp : (1 : ℝ) < (2 : ℂ).re)]
        with z hz
      have hzne : z ≠ 0 := by intro h0; rw [h0, zero_re] at hz; linarith
      have hval : ℓ_ext z = logL₄Series z := by
        dsimp only [ℓ_ext]
        rw [hMA_eq_gt1 z hz]
        have hεC : (ε_sign : ℂ) * (ε_sign : ℂ) = 1 := by exact_mod_cast hε_sq
        calc (ε_sign : ℂ) * z *
              (((ε_sign : ℂ) * (logL₄Series z / z) + (C : ℂ) / (z - 1 / 2) - H_fin z) -
                (C : ℂ) / (z - 1 / 2) + H_fin z)
            = ((ε_sign : ℂ) * (ε_sign : ℂ)) * (z * (logL₄Series z / z)) := by ring
          _ = 1 * logL₄Series z := by rw [hεC, mul_div_cancel₀ _ hzne]
          _ = logL₄Series z := one_mul _
      rw [hval, exp_logL₄Series hz]
    have hub : ∀ x ∈ Zre, x ≤ σ_ext := by
      rintro x (rfl | ⟨s, rfl, _, hs0⟩)
      · exact hσ_ext_gt.le
      · by_contra hgt; push Not at hgt
        exact Complex.exp_ne_zero _ (hs0 ▸ hexp_ext hgt)
    have hle : σ₀ ≤ σ_ext := csSup_le hZre_ne hub
    dsimp only [σ_ext] at hle
    linarith
  -- Assemble all conclusions now that σ₀ = 1/2
  have hzero_free : ∀ s : ℂ, 1 / 2 < s.re → L₄ s ≠ 0 := fun s hs ↦
    hL₄_ne_zero_gt s (hσ₀_eq_half.symm ▸ hs)
  have hMA_diff_half : DifferentiableOn ℂ M_A {z : ℂ | 1 / 2 < z.re} := by
    intro z hz
    have hzre : (1 : ℝ) / 2 < z.re := hz
    let σm : ℝ := (1 / 2 + z.re) / 2
    have hσm1 : σ₀ < σm := by rw [hσ₀_eq_half]; dsimp only [σm]; linarith
    have hσmz : σm < z.re := by dsimp only [σm]; linarith
    exact (differentiableAt_mellin_nonneg hAm hAnn (hAint_gt_σ₀ hσm1) hσmz).differentiableWithinAt
  have hG₁_diff_half : DifferentiableOn ℂ G₁ {z : ℂ | 1 / 2 < z.re} := by
    simpa [Ω, hσ₀_eq_half] using hG₁_diff
  have hG₁_eq_MA_half : Set.EqOn G₁ M_A {z : ℂ | 1 / 2 < z.re} := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (hG₁_diff_half.analyticOnNhd (isOpen_lt continuous_const continuous_re))
      (hMA_diff_half.analyticOnNhd (isOpen_lt continuous_const continuous_re))
      (convex_halfSpace_re_gt (1 / 2)).isPreconnected
      (show (1 : ℝ) / 2 < (2 : ℂ).re by simp; norm_num) ?_
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds (by simp : (1 : ℝ) < (2 : ℂ).re)]
      with z hz
    exact hG₁_eq_MA z hz
  refine ⟨hzero_free, ℓ₁, ?_, ?_, ?_, ?_⟩
  · simpa [Ω, hσ₀_eq_half] using hℓ₁_diff
  · intro s hs; exact hℓ₁_exp s (by simpa [Ω, hσ₀_eq_half] using hs)
  · intro s hs
    exact (mellin_tail_split hε hC hN₀_real hs (hAint_gt_σ₀ (hσ₀_eq_half.symm ▸ hs)) hAnn).1
  · intro s hs
    have hsp := (mellin_tail_split hε hC hN₀_real hs (hAint_gt_σ₀ (hσ₀_eq_half.symm ▸ hs)) hAnn).2
    have hGeq : G₁ s = M_A s := hG₁_eq_MA_half hs
    have h_eq1 : (ε_sign : ℂ) * (ℓ₁ s / s) =
        (ε_sign : ℂ) * ∫ t in Set.Ioi (1 : ℝ), (J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
      dsimp only [G₁, M_A, A, H_fin, B] at hGeq
      linear_combination hGeq + hsp
    exact mul_left_cancel₀ hε_ne h_eq1


/- Section 3: Pillar 2 (Zero counting and `∑ m(γ)/(1/4 + γ²) < ∞` via even `ξ₄` and Blaschke + Harnack) -/

lemma one_le_norm_canonicalFactor {ρ : ℝ} {u w : ℂ} (hu : u ∈ Metric.ball (0 : ℂ) ρ)
    (hw : w ∈ Metric.closedBall (0 : ℂ) ρ) (hwu : w ≠ u) :
    1 ≤ ‖Complex.canonicalFactor ρ u w‖ := by
  have hρ : 0 < ρ := Metric.pos_of_mem_ball hu
  rw [mem_ball_zero_iff] at hu
  rw [mem_closedBall_zero_iff] at hw
  have hden : 0 < ‖(ρ : ℂ) * (w - u)‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    exact mul_pos hρ (norm_pos_iff.mpr (sub_ne_zero.mpr hwu))
  rw [Complex.canonicalFactor_apply, norm_div, one_le_div hden]
  have hsq : ‖(ρ : ℂ) * (w - u)‖ ^ 2 ≤ ‖(ρ : ℂ) ^ 2 - conj u * w‖ ^ 2 := by
    have h1 : ‖(ρ : ℂ) ^ 2 - conj u * w‖ ^ 2 =
        ρ ^ 4 - 2 * ρ ^ 2 * (conj u * w).re + ‖u‖ ^ 2 * ‖w‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, map_pow Complex.normSq,
        Complex.normSq_ofReal, Complex.normSq_mul, Complex.normSq_conj,
        Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
      have hre : ((ρ : ℂ) ^ 2 * conj (conj u * w)).re = ρ ^ 2 * (conj u * w).re := by
        rw [show (ρ : ℂ) ^ 2 = ((ρ ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul,
          Complex.conj_re]
      rw [hre]; ring
    have h2 : ‖(ρ : ℂ) * (w - u)‖ ^ 2 =
        ρ ^ 2 * (‖w‖ ^ 2 - 2 * (conj u * w).re + ‖u‖ ^ 2) := by
      rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg hρ.le,
        ← Complex.normSq_eq_norm_sq, Complex.normSq_sub,
        Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
      have hre : (w * conj u).re = (conj u * w).re := by rw [mul_comm]
      rw [hre]; ring
    rw [h1, h2]
    have hdiff : (ρ ^ 4 - 2 * ρ ^ 2 * (conj u * w).re + ‖u‖ ^ 2 * ‖w‖ ^ 2) -
        ρ ^ 2 * (‖w‖ ^ 2 - 2 * (conj u * w).re + ‖u‖ ^ 2) =
        (ρ ^ 2 - ‖u‖ ^ 2) * (ρ ^ 2 - ‖w‖ ^ 2) := by ring
    have hnn1 : 0 ≤ ρ ^ 2 - ‖u‖ ^ 2 := by nlinarith [norm_nonneg u]
    have hnn2 : 0 ≤ ρ ^ 2 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
    linarith [mul_nonneg hnn1 hnn2]
  nlinarith [norm_nonneg ((ρ : ℂ) * (w - u)), norm_nonneg ((ρ : ℂ) ^ 2 - conj u * w)]

lemma re_herglotzRieszKernel_ge {ρ : ℝ} {w z : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) ρ)
    (hz : z ∈ Metric.sphere (0 : ℂ) ρ) :
    (ρ - ‖w‖) / (ρ + ‖w‖) ≤ (herglotzRieszKernel 0 w z).re := by
  have hρ : 0 < ρ := Metric.pos_of_mem_ball hw
  rw [mem_ball_zero_iff] at hw
  rw [mem_sphere_zero_iff_norm] at hz
  have hzw : z - w ≠ 0 := by
    intro h0; have : z = w := sub_eq_zero.mp h0; rw [this] at hz; linarith
  have hden_pos : 0 < ‖z - w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hzw)
  have hre : (herglotzRieszKernel 0 w z).re = (ρ ^ 2 - ‖w‖ ^ 2) / ‖z - w‖ ^ 2 := by
    rw [herglotzRieszKernel_def, sub_zero, sub_zero, Complex.div_re, Complex.normSq_eq_norm_sq]
    have hnum : (z + w).re * (z - w).re + (z + w).im * (z - w).im = ρ ^ 2 - ‖w‖ ^ 2 := by
      have hz2 : z.re ^ 2 + z.im ^ 2 = ρ ^ 2 := by
        rw [sq, sq, ← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hz]
      have hw2 : w.re ^ 2 + w.im ^ 2 = ‖w‖ ^ 2 := by
        rw [sq, sq, ← Complex.normSq_apply, Complex.normSq_eq_norm_sq]
      simp only [add_re, sub_re, add_im, sub_im]
      linarith
    rw [← add_div, hnum]
  rw [hre]
  have htri : ‖z - w‖ ≤ ρ + ‖w‖ := by
    calc ‖z - w‖ ≤ ‖z‖ + ‖w‖ := norm_sub_le z w
      _ = ρ + ‖w‖ := by rw [hz]
  have htri2 : ‖z - w‖ ^ 2 ≤ (ρ + ‖w‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hnum_nn : 0 ≤ ρ ^ 2 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  calc (ρ - ‖w‖) / (ρ + ‖w‖)
      = (ρ ^ 2 - ‖w‖ ^ 2) / (ρ + ‖w‖) ^ 2 := by
        have hpos : 0 < ρ + ‖w‖ := by linarith [norm_nonneg w]
        field_simp; ring
    _ ≤ (ρ ^ 2 - ‖w‖ ^ 2) / ‖z - w‖ ^ 2 := div_le_div_of_nonneg_left hnum_nn hden_pos htri2

lemma harnack_zero_lower_bound {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hF0 : F 0 ≠ 0)
    {ρ r M : ℝ} (hr0 : 0 < r) (hrρ : r < ρ) {w : ℂ} (hw_norm : ‖w‖ = r) (hFw : F w ≠ 0)
    (hFsphere : ∀ z ∈ Metric.sphere (0 : ℂ) ρ, F z ≠ 0)
    (_hM1 : 1 ≤ M) (hFM : ∀ z ∈ Metric.sphere (0 : ℂ) ρ, ‖F z‖ ≤ M) :
    ((ρ + r) / (ρ - r)) * Real.log ‖F w‖ - (2 * r / (ρ - r)) * Real.log M ≤
      Real.log ‖F 0‖ +
        ∑ᶠ u, (MeromorphicOn.divisor F (Metric.ball (0 : ℂ) ρ) u : ℝ) * Real.log (ρ / ‖u‖) := by
  have hρ : 0 < ρ := hr0.trans hrρ
  have hF_an : AnalyticOnNhd ℂ F (Metric.closedBall (0 : ℂ) ρ) :=
    (hF.differentiableOn.analyticOnNhd isOpen_univ).mono (Set.subset_univ _)
  have hF_ord_ne_top : ∀ u : Metric.closedBall (0 : ℂ) ρ, meromorphicOrderAt F u ≠ ⊤ := by
    have h0_mem : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) ρ := Metric.mem_closedBall_self hρ.le
    have hnot : ∃ u : Metric.closedBall (0 : ℂ) ρ, meromorphicOrderAt F u ≠ ⊤ :=
      ⟨⟨0, h0_mem⟩, by
        rw [(hF_an 0 h0_mem).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hF0]
        exact WithTop.coe_ne_top⟩
    exact (hF_an.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall
      (Metric.isConnected_closedBall hρ.le)).mp hnot
  obtain ⟨h, D⟩ := hF_an.meromorphicOn.exists_ecanonicalDecomp hF_ord_ne_top
  have hdiv_sph : MeromorphicOn.divisor F (Metric.sphere (0 : ℂ) ρ) = 0 := by
    ext z
    by_cases hz : z ∈ Metric.sphere (0 : ℂ) ρ
    · rw [MeromorphicOn.divisor_apply (hF_an.meromorphicOn.mono_set Metric.sphere_subset_closedBall) hz,
        (hF_an z (Metric.sphere_subset_closedBall hz)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr (hFsphere z hz)]
      simp
    · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]
  have hlog_h_sph : ∀ z ∈ Metric.sphere (0 : ℂ) ρ, Real.log ‖h z‖ = Real.log ‖F z‖ := by
    intro z hz
    have hord : meromorphicOrderAt F z = 0 :=
      (hF_an z (Metric.sphere_subset_closedBall hz)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr (hFsphere z hz)
    have heq := D.log_norm_eq (Metric.sphere_subset_closedBall hz) hord hρ
    rw [hdiv_sph] at heq
    have hsum0 : ∑ᶠ i, (MeromorphicOn.divisor F (Metric.ball (0 : ℂ) ρ) i : ℝ) *
        Real.log ‖Complex.canonicalFactor ρ i z‖ = 0 := by
      refine finsum_eq_zero_of_forall_eq_zero fun i ↦ ?_
      by_cases hi : MeromorphicOn.divisor F (Metric.ball (0 : ℂ) ρ) i = 0
      · simp [hi]
      · have hi_mem : i ∈ Metric.ball (0 : ℂ) ρ :=
          (MeromorphicOn.divisor F (Metric.ball (0 : ℂ) ρ)).supportWithinDomain hi
        rw [Complex.norm_canonicalFactor_eval_circle_eq_one hi_mem hz, Real.log_one, mul_zero]
    rw [hsum0, (hF_an z (Metric.sphere_subset_closedBall hz)).meromorphicTrailingCoeffAt_of_ne_zero
      (hFsphere z hz)] at heq
    simpa using heq
  let u : ℂ → ℝ := fun z ↦ Real.log M - Real.log ‖h z‖
  have hu_harm : InnerProductSpace.HarmonicOnNhd u (Metric.closedBall (0 : ℂ) ρ) := by
    intro z hz
    have h1 : InnerProductSpace.HarmonicAt (fun _ : ℂ ↦ Real.log M) z :=
      InnerProductSpace.harmonicAt_const (Real.log M)
    have h2 : InnerProductSpace.HarmonicAt (fun x ↦ Real.log ‖h x‖) z :=
      (D.analyticOnNhd z hz).harmonicAt_log_norm (D.ne_zero z hz)
    exact h1.sub h2
  have hu_sph_nn : ∀ z ∈ Metric.sphere (0 : ℂ) ρ, 0 ≤ u z := by
    intro z hz
    dsimp only [u]
    rw [hlog_h_sph z hz]
    exact sub_nonneg.mpr (Real.log_le_log (norm_pos_iff.mpr (hFsphere z hz)) (hFM z hz))
  have hw_ball : w ∈ Metric.ball (0 : ℂ) ρ := by rw [mem_ball_zero_iff, hw_norm]; exact hrρ
  have hpois := hu_harm.circleAverage_re_herglotzRieszKernel_smul hw_ball
  have hmvp : Real.circleAverage u (0 : ℂ) ρ = u 0 := by
    have hu_harm' : InnerProductSpace.HarmonicOnNhd u (Metric.closedBall (0 : ℂ) |ρ|) := by
      rwa [abs_of_pos hρ]
    exact hu_harm'.circleAverage_eq
  have hu_cont : ContinuousOn u (Metric.sphere (0 : ℂ) |ρ|) := by
    rw [abs_of_pos hρ]
    exact fun z hz ↦ (hu_harm z (Metric.sphere_subset_closedBall hz)).1.continuousAt.continuousWithinAt
  have hkern_cont : ContinuousOn (Complex.re ∘ herglotzRieszKernel 0 w) (Metric.sphere (0 : ℂ) |ρ|) := by
    rw [abs_of_pos hρ]
    intro z hz
    have hzw : z - w ≠ 0 := by
      intro h0
      have : z = w := sub_eq_zero.mp h0
      rw [this, mem_sphere_zero_iff_norm, hw_norm] at hz; linarith
    have hc : ContinuousAt (fun x ↦ ((x + w) / (x - w)).re) z :=
      Complex.continuous_re.continuousAt.comp
        ((continuousAt_id.add continuousAt_const).div (continuousAt_id.sub continuousAt_const) hzw)
    simpa [Function.comp_def, herglotzRieszKernel_def] using hc.continuousWithinAt
  have hharnack : ((ρ - r) / (ρ + r)) * u 0 ≤ u w := by
    rw [← hpois, ← hmvp, ← smul_eq_mul, ← Real.circleAverage_smul]
    refine Real.circleAverage_mono ((hu_cont.circleIntegrable').smul _)
      ((hkern_cont.smul hu_cont).circleIntegrable') fun z hz ↦ ?_
    rw [abs_of_pos hρ] at hz
    simp only [Pi.smul_apply, smul_eq_mul]
    have hk := re_herglotzRieszKernel_ge hw_ball hz
    rw [hw_norm] at hk
    exact mul_le_mul_of_nonneg_right hk (hu_sph_nn z hz)
  have hrear : ((ρ + r) / (ρ - r)) * Real.log ‖h w‖ - (2 * r / (ρ - r)) * Real.log M ≤ Real.log ‖h 0‖ := by
    have hpos1 : 0 < ρ - r := sub_pos.mpr hrρ
    have hpos2 : 0 < ρ + r := by linarith
    have hmul : u 0 ≤ ((ρ + r) / (ρ - r)) * u w := by
      have h1 := mul_le_mul_of_nonneg_left hharnack (show 0 ≤ (ρ + r) / (ρ - r) by positivity)
      have hcancel : ((ρ + r) / (ρ - r)) * (((ρ - r) / (ρ + r)) * u 0) = u 0 := by field_simp
      rwa [hcancel] at h1
    dsimp only [u] at hmul
    have hcoef : ((ρ + r) / (ρ - r)) - 1 = 2 * r / (ρ - r) := by field_simp; ring
    linarith [show ((ρ + r) / (ρ - r)) * (Real.log M - Real.log ‖h w‖) =
      (1 + 2 * r / (ρ - r)) * Real.log M - ((ρ + r) / (ρ - r)) * Real.log ‖h w‖ by
      rw [← hcoef]; ring]
  have hhw_ge : Real.log ‖F w‖ ≤ Real.log ‖h w‖ := by
    have hordw : meromorphicOrderAt F w = 0 :=
      (hF_an w (Metric.ball_subset_closedBall hw_ball)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hFw
    have heq := D.log_norm_eq (Metric.ball_subset_closedBall hw_ball) hordw hρ
    rw [hdiv_sph,
      (hF_an w (Metric.ball_subset_closedBall hw_ball)).meromorphicTrailingCoeffAt_of_ne_zero hFw] at heq
    have hsum_nn : 0 ≤ ∑ᶠ i, (MeromorphicOn.divisor F (Metric.ball (0 : ℂ) ρ) i : ℝ) *
        Real.log ‖Complex.canonicalFactor ρ i w‖ := by
      refine finsum_nonneg fun i ↦ ?_
      by_cases hi : MeromorphicOn.divisor F (Metric.ball (0 : ℂ) ρ) i = 0
      · simp [hi]
      · have hi_mem : i ∈ Metric.ball (0 : ℂ) ρ :=
          (MeromorphicOn.divisor F (Metric.ball (0 : ℂ) ρ)).supportWithinDomain hi
        have hwi : w ≠ i := by
          rintro rfl
          have : MeromorphicOn.divisor F (Metric.ball (0 : ℂ) ρ) w = 0 := by
            rw [MeromorphicOn.divisor_apply (hF_an.meromorphicOn.mono_set Metric.ball_subset_closedBall) hw_ball,
              hordw]; simp
          exact hi this
        have hdiv_nn : (0 : ℤ) ≤ MeromorphicOn.divisor F (Metric.ball (0 : ℂ) ρ) i :=
          MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hF_an.mono Metric.ball_subset_closedBall) i
        have hdiv_nnR : (0 : ℝ) ≤ (MeromorphicOn.divisor F (Metric.ball (0 : ℂ) ρ) i : ℝ) := by
          exact_mod_cast hdiv_nn
        have hlog_nn : 0 ≤ Real.log ‖Complex.canonicalFactor ρ i w‖ :=
          Real.log_nonneg (one_le_norm_canonicalFactor hi_mem (Metric.ball_subset_closedBall hw_ball) hwi)
        exact mul_nonneg hdiv_nnR hlog_nn
    simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, Int.cast_zero, zero_mul,
      finsum_zero, sub_zero] at heq
    linarith
  have hh0_eq : Real.log ‖h 0‖ =
      Real.log ‖F 0‖ +
        ∑ᶠ i, (MeromorphicOn.divisor F (Metric.ball (0 : ℂ) ρ) i : ℝ) * Real.log (ρ / ‖i‖) := by
    have hord0 : meromorphicOrderAt F 0 = 0 :=
      (hF_an 0 (Metric.mem_closedBall_self hρ.le)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hF0
    have heq := D.log_norm_eq (Metric.mem_closedBall_self hρ.le) hord0 hρ
    rw [hdiv_sph,
      (hF_an 0 (Metric.mem_closedBall_self hρ.le)).meromorphicTrailingCoeffAt_of_ne_zero hF0] at heq
    simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, Int.cast_zero, zero_mul,
      finsum_zero, sub_zero] at heq
    rw [heq, add_comm]
    congr 1
    refine finsum_congr fun i ↦ ?_
    by_cases hi : MeromorphicOn.divisor F (Metric.ball (0 : ℂ) ρ) i = 0
    · simp [hi]
    · have hi_ne0 : i ≠ 0 := by
        rintro rfl
        have : MeromorphicOn.divisor F (Metric.ball (0 : ℂ) ρ) 0 = 0 := by
          rw [MeromorphicOn.divisor_apply (hF_an.meromorphicOn.mono_set Metric.ball_subset_closedBall)
            (Metric.mem_ball_self hρ), hord0]; simp
        exact hi this
      have hcf0 : ‖Complex.canonicalFactor ρ i 0‖ = ρ / ‖i‖ := by
        rw [Complex.canonicalFactor_apply, mul_zero, sub_zero, zero_sub, mul_neg, norm_div,
          norm_neg, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hρ.le]
        have hi0 : ‖i‖ ≠ 0 := norm_ne_zero_iff.mpr hi_ne0
        field_simp [hρ.ne', hi0]
      rw [hcf0]
  have hpos_coef : 0 ≤ (ρ + r) / (ρ - r) := by
    have : 0 < ρ - r := sub_pos.mpr hrρ
    positivity
  linarith [mul_le_mul_of_nonneg_left hhw_ge hpos_coef, hh0_eq]

noncomputable def g₄ (s : ℂ) : ℂ := ξ₄ (1 / 2 + s)

lemma differentiable_g₄ : Differentiable ℂ g₄ :=
  differentiable_ξ₄.comp (differentiable_const _ |>.add differentiable_id)

lemma g₄_neg (s : ℂ) : g₄ (-s) = g₄ s := by
  dsimp only [g₄]
  rw [show (1 : ℂ) / 2 + -s = 1 - (1 / 2 + s) by ring, ξ₄_one_sub]

lemma g₄_zero_ne_zero : g₄ 0 ≠ 0 := by simpa [g₄] using ξ₄_half_ne_zero

lemma iteratedDeriv_g₄_odd (k : ℕ) : iteratedDeriv (2 * k + 1) g₄ 0 = 0 := by
  have hcomp : (fun s ↦ g₄ (-s)) = g₄ := funext g₄_neg
  have h := congrArg (fun f ↦ iteratedDeriv (2 * k + 1) f 0) hcomp
  rw [iteratedDeriv_comp_neg (2 * k + 1) g₄ 0, neg_zero] at h
  have hneg : ((-1 : ℂ) ^ (2 * k + 1)) = -1 := by simp [pow_add, pow_mul]
  rw [smul_eq_mul, hneg, neg_one_mul] at h
  exact CharZero.eq_neg_self_iff.mp h.symm

noncomputable def F_half (z : ℂ) : ℂ :=
  ∑' n : ℕ, (((2 * n).factorial : ℂ)⁻¹ * iteratedDeriv (2 * n) g₄ 0) * z ^ n

lemma F_half_sq (s : ℂ) : F_half (s ^ 2) = g₄ s := by
  have htsum := Complex.hasSum_taylorSeries_on_ball (c := (0 : ℂ)) (r := ‖s‖ + 1)
    differentiable_g₄.differentiableOn (by rw [mem_ball_zero_iff]; linarith)
  let a : ℕ → ℂ := fun m ↦ ((m.factorial : ℂ)⁻¹ * iteratedDeriv m g₄ 0) * s ^ m
  have hsum : HasSum a (g₄ s) := by
    refine htsum.congr_fun fun m ↦ ?_
    simp only [a, sub_zero, smul_eq_mul]; ring
  have heven : Summable (fun n : ℕ ↦ a (2 * n)) :=
    hsum.summable.comp_injective (fun _ _ h ↦ by omega)
  have hpartial : ∀ N : ℕ, ∑ m ∈ Finset.range (2 * N), a m = ∑ n ∈ Finset.range N, a (2 * n) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [show 2 * (N + 1) = 2 * N + 1 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
        ih, Finset.sum_range_succ]
      have hodd0 : a (2 * N + 1) = 0 := by simp [a, iteratedDeriv_g₄_odd]
      rw [hodd0, add_zero]
  have hlim1 : Tendsto (fun N : ℕ ↦ ∑ m ∈ Finset.range (2 * N), a m) atTop (𝓝 (g₄ s)) :=
    hsum.tendsto_sum_nat.comp (tendsto_atTop_atTop_of_monotone (fun _ _ h ↦ by omega) (fun b ↦ ⟨b, by omega⟩))
  have hlim2 : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N, a (2 * n)) atTop (𝓝 (∑' n : ℕ, a (2 * n))) :=
    heven.hasSum.tendsto_sum_nat
  have heq : ∑' n : ℕ, a (2 * n) = g₄ s := tendsto_nhds_unique hlim2 (hlim1.congr hpartial)
  unfold F_half
  simpa [a, pow_mul] using heq

lemma differentiable_F_half : Differentiable ℂ F_half := by
  intro z
  let R : ℝ := ‖z‖ + 2
  have hR_pos : 0 < R := by dsimp [R]; positivity
  let s₀ : ℂ := ((Real.sqrt (2 * R) : ℝ) : ℂ)
  have htsum := Complex.hasSum_taylorSeries_on_ball (c := (0 : ℂ)) (r := ‖s₀‖ + 1)
    differentiable_g₄.differentiableOn (by rw [mem_ball_zero_iff]; linarith)
  have hbdd : ∃ M : ℝ, 0 ≤ M ∧ ∀ m : ℕ, ‖((m.factorial : ℂ)⁻¹ * iteratedDeriv m g₄ 0) * s₀ ^ m‖ ≤ M := by
    have hsum : HasSum (fun m : ℕ ↦ ((m.factorial : ℂ)⁻¹ * iteratedDeriv m g₄ 0) * s₀ ^ m) (g₄ s₀) := by
      refine htsum.congr_fun fun m ↦ ?_
      simp only [sub_zero, smul_eq_mul]; ring
    have hnorm : Tendsto (fun m : ℕ ↦ ‖((m.factorial : ℂ)⁻¹ * iteratedDeriv m g₄ 0) * s₀ ^ m‖) atTop (𝓝 0) := by
      simpa using hsum.summable.tendsto_atTop_zero.norm
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hnorm.eventually (Metric.ball_mem_nhds 0 zero_lt_one))
    let a : ℕ → ℝ := fun m ↦ ‖((m.factorial : ℂ)⁻¹ * iteratedDeriv m g₄ 0) * s₀ ^ m‖
    let M₀ : ℝ := (Finset.range (N + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩ a
    refine ⟨max 1 M₀, by positivity, fun m ↦ ?_⟩
    by_cases hm : m ≤ N
    · exact (Finset.le_sup' a (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))).trans (le_max_right 1 M₀)
    · have hlt := hN m (by omega)
      rw [dist_zero_right, Real.norm_of_nonneg (norm_nonneg _)] at hlt
      exact hlt.le.trans (le_max_left 1 M₀)
  obtain ⟨M, hM0, hM⟩ := hbdd
  have hdiff_ball : DifferentiableOn ℂ F_half (Metric.ball (0 : ℂ) R) := by
    refine differentiableOn_tsum_of_summable_norm (u := fun n : ℕ ↦ M * (1 / 2 : ℝ) ^ n)
      ((summable_geometric_two).mul_left M) (fun n ↦ ?_) Metric.isOpen_ball (fun n w hw ↦ ?_)
    · exact ((differentiable_pow n).const_mul _).differentiableOn
    · rw [mem_ball_zero_iff] at hw
      have hs0_sq : ‖s₀‖ ^ 2 = 2 * R := by
        dsimp only [s₀]
        rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]
      have hpow_eq : ‖s₀ ^ (2 * n)‖ = (2 * R) ^ n := by rw [norm_pow, pow_mul, hs0_sq]
      have h2R_pos : 0 < (2 * R) ^ n := by positivity
      have hMn := hM (2 * n)
      rw [norm_mul, hpow_eq] at hMn
      rw [norm_mul, norm_pow]
      have hcoef : ‖((2 * n).factorial : ℂ)⁻¹ * iteratedDeriv (2 * n) g₄ 0‖ ≤ M / (2 * R) ^ n :=
        (le_div_iff₀ h2R_pos).mpr hMn
      calc ‖((2 * n).factorial : ℂ)⁻¹ * iteratedDeriv (2 * n) g₄ 0‖ * ‖w‖ ^ n
          ≤ (M / (2 * R) ^ n) * R ^ n :=
            mul_le_mul hcoef (pow_le_pow_left₀ (norm_nonneg _) hw.le n) (pow_nonneg (norm_nonneg _) n) (by positivity)
        _ = M * (R / (2 * R)) ^ n := by rw [div_pow]; ring
        _ = M * (1 / 2 : ℝ) ^ n := by congr 2; field_simp [hR_pos.ne']
  exact hdiff_ball.differentiableAt (Metric.isOpen_ball.mem_nhds (by
    rw [mem_ball_zero_iff]; dsimp [R]; linarith))

lemma F_half_zero_ne_zero : F_half 0 ≠ 0 := by
  have := F_half_sq 0
  rw [zero_pow two_ne_zero] at this
  rw [this]; exact g₄_zero_ne_zero

lemma norm_complex_Gamma_le_real_Gamma {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Real.Gamma_eq_integral hz]
  calc ‖∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) • (x : ℂ) ^ (z - 1)‖
      ≤ ∫ x in Set.Ioi (0 : ℝ), ‖Real.exp (-x) • (x : ℂ) ^ (z - 1)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * x ^ (z.re - 1) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
        have hx0 : 0 < x := hx
        rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le,
          Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        simp

lemma real_Gamma_le_four_add_factorial {x : ℝ} {N : ℕ} (hx1 : (3 : ℝ) / 4 ≤ x) (hx2 : x ≤ (N : ℝ) + 1) :
    Real.Gamma x ≤ 4 + (N.factorial : ℝ) := by
  have hx0 : 0 < x := by linarith
  rw [Real.Gamma_eq_integral hx0]
  have hint := Real.GammaIntegral_convergent hx0
  have hsub1 : Set.Ioc (0 : ℝ) 1 ⊆ Set.Ioi (0 : ℝ) := fun _ ht ↦ ht.1
  have hsub2 : Set.Ioi (1 : ℝ) ⊆ Set.Ioi (0 : ℝ) := Set.Ioi_subset_Ioi zero_le_one
  have hUnion : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) := by
    ext t; simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro ht; by_cases h : t ≤ 1; exact Or.inl ⟨ht, h⟩; exact Or.inr (lt_of_not_ge h)
    · rintro (⟨ht, _⟩ | ht); exact ht; exact zero_lt_one.trans ht
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi (1 : ℝ)) :=
    Set.disjoint_left.mpr fun _ h1 h2 ↦ not_lt_of_ge h1.2 h2
  rw [hUnion, MeasureTheory.setIntegral_union hdisj measurableSet_Ioi
    (hint.mono_set hsub1) (hint.mono_set hsub2)]
  have hI1 : ∫ t in Set.Ioc (0 : ℝ) 1, Real.exp (-t) * t ^ (x - 1) ≤ 4 := by
    have hdom : IntegrableOn (fun t : ℝ ↦ t ^ (-(1 : ℝ) / 4)) (Set.Ioc (0 : ℝ) 1) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
      exact intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    calc ∫ t in Set.Ioc (0 : ℝ) 1, Real.exp (-t) * t ^ (x - 1)
        ≤ ∫ t in Set.Ioc (0 : ℝ) 1, t ^ (-(1 : ℝ) / 4) := by
          refine setIntegral_mono_on (hint.mono_set hsub1) hdom measurableSet_Ioc fun t ht ↦ ?_
          have hexp : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [ht.1])
          have hrpow : t ^ (x - 1) ≤ t ^ (-(1 : ℝ) / 4) :=
            Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2 (by linarith)
          calc Real.exp (-t) * t ^ (x - 1) ≤ 1 * t ^ (x - 1) :=
                mul_le_mul_of_nonneg_right hexp (Real.rpow_nonneg ht.1.le _)
            _ = t ^ (x - 1) := one_mul _
            _ ≤ t ^ (-(1 : ℝ) / 4) := hrpow
      _ = ∫ t in (0 : ℝ)..1, t ^ (-(1 : ℝ) / 4) := (intervalIntegral.integral_of_le zero_le_one).symm
      _ = 4 / 3 := by rw [integral_rpow (Or.inl (by norm_num))]; norm_num
      _ ≤ 4 := by norm_num
  have hI2 : ∫ t in Set.Ioi (1 : ℝ), Real.exp (-t) * t ^ (x - 1) ≤ (N.factorial : ℝ) := by
    have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hintN := Real.GammaIntegral_convergent hNpos
    have hGe : Real.Gamma ((N : ℝ) + 1) = (N.factorial : ℝ) := Real.Gamma_nat_eq_factorial N
    rw [← hGe, Real.Gamma_eq_integral hNpos]
    calc ∫ t in Set.Ioi (1 : ℝ), Real.exp (-t) * t ^ (x - 1)
        ≤ ∫ t in Set.Ioi (1 : ℝ), Real.exp (-t) * t ^ (((N : ℝ) + 1) - 1) := by
          refine setIntegral_mono_on (hint.mono_set hsub2)
            (hintN.mono_set hsub2) measurableSet_Ioi fun t ht ↦ ?_
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le ht.le (by linarith)) (Real.exp_pos _).le
      _ ≤ ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * t ^ (((N : ℝ) + 1) - 1) := by
          refine setIntegral_mono_set hintN ?_ hsub2.eventuallyLE
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ht.le _)
  linarith

lemma real_Gamma_ge_half_factorial {x : ℝ} {k : ℕ} (hk : 2 ≤ k) (hx : (k : ℝ) + 1 ≤ x) :
    (k.factorial : ℝ) / 2 ≤ Real.Gamma x := by
  have hx0 : 0 < x := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hint_x := Real.GammaIntegral_convergent hx0
  have hint_k := Real.GammaIntegral_convergent hk0
  have hsub1 : Set.Ioc (0 : ℝ) 1 ⊆ Set.Ioi (0 : ℝ) := fun _ ht ↦ ht.1
  have hsub2 : Set.Ioi (1 : ℝ) ⊆ Set.Ioi (0 : ℝ) := Set.Ioi_subset_Ioi zero_le_one
  have hUnion : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) := by
    ext t; simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro ht; by_cases h : t ≤ 1; exact Or.inl ⟨ht, h⟩; exact Or.inr (lt_of_not_ge h)
    · rintro (⟨ht, _⟩ | ht); exact ht; exact zero_lt_one.trans ht
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi (1 : ℝ)) :=
    Set.disjoint_left.mpr fun _ h1 h2 ↦ not_lt_of_ge h1.2 h2
  have hsplit_k : (k.factorial : ℝ) =
      (∫ t in Set.Ioc (0 : ℝ) 1, Real.exp (-t) * t ^ (((k : ℝ) + 1) - 1)) +
      (∫ t in Set.Ioi (1 : ℝ), Real.exp (-t) * t ^ (((k : ℝ) + 1) - 1)) := by
    rw [← Real.Gamma_nat_eq_factorial k, Real.Gamma_eq_integral hk0, hUnion,
      MeasureTheory.setIntegral_union hdisj measurableSet_Ioi
        (hint_k.mono_set hsub1) (hint_k.mono_set hsub2)]
  have hI1_le : ∫ t in Set.Ioc (0 : ℝ) 1, Real.exp (-t) * t ^ (((k : ℝ) + 1) - 1) ≤ 1 := by
    calc ∫ t in Set.Ioc (0 : ℝ) 1, Real.exp (-t) * t ^ (((k : ℝ) + 1) - 1)
        ≤ ∫ _t in Set.Ioc (0 : ℝ) 1, (1 : ℝ) := by
          refine setIntegral_mono_on (hint_k.mono_set hsub1)
            (integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top.ne))
            measurableSet_Ioc fun t ht ↦ ?_
          have h1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [ht.1])
          have h2 : t ^ (((k : ℝ) + 1) - 1) ≤ 1 :=
            Real.rpow_le_one ht.1.le ht.2 (by linarith [Nat.cast_nonneg (α := ℝ) k])
          nlinarith [Real.exp_pos (-t), Real.rpow_nonneg ht.1.le (((k : ℝ) + 1) - 1)]
      _ = 1 := by simp
  have hI2_le : ∫ t in Set.Ioi (1 : ℝ), Real.exp (-t) * t ^ (((k : ℝ) + 1) - 1) ≤ Real.Gamma x := by
    rw [Real.Gamma_eq_integral hx0]
    calc ∫ t in Set.Ioi (1 : ℝ), Real.exp (-t) * t ^ (((k : ℝ) + 1) - 1)
        ≤ ∫ t in Set.Ioi (1 : ℝ), Real.exp (-t) * t ^ (x - 1) := by
          refine setIntegral_mono_on (hint_k.mono_set hsub2)
            (hint_x.mono_set hsub2) measurableSet_Ioi fun t ht ↦ ?_
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le ht.le (by linarith)) (Real.exp_pos _).le
      _ ≤ ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * t ^ (x - 1) := by
          refine setIntegral_mono_set hint_x ?_ hsub2.eventuallyLE
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ht.le _)
  have hfac2 : (2 : ℝ) ≤ (k.factorial : ℝ) := by
    have : 2 ≤ k.factorial := (show 2 = Nat.factorial 2 by decide) ▸ Nat.factorial_le hk
    exact_mod_cast this
  linarith

lemma norm_F_half_upper :
    ∃ C_up : ℝ, 0 < C_up ∧ ∀ ρ : ℝ, 16 ≤ ρ → ∀ z ∈ Metric.closedBall (0 : ℂ) ρ,
      ‖F_half z‖ ≤ Real.exp ((Real.sqrt ρ / 2) * Real.log (Real.sqrt ρ) + C_up * Real.sqrt ρ) := by
  refine ⟨10, by norm_num, fun ρ hρ z hz ↦ ?_⟩
  have hρ_pos : 0 < ρ := by linarith
  let r₀ : ℝ := Real.sqrt ρ
  have hr₀_ge4 : 4 ≤ r₀ := by
    have : (4 : ℝ) = Real.sqrt 16 := by norm_num
    rw [this]; exact Real.sqrt_le_sqrt hρ
  have hr₀_pos : 0 < r₀ := by linarith
  obtain ⟨s₀, hs₀⟩ := IsAlgClosed.exists_eq_mul_self z
  let s : ℂ := if 0 ≤ s₀.re then s₀ else -s₀
  have hs_sq : s ^ 2 = z := by
    dsimp only [s]; split_ifs <;> [simpa [sq] using hs₀.symm; simpa [sq] using hs₀.symm]
  have hs_re_nn : 0 ≤ s.re := by dsimp only [s]; split_ifs with h; exact h; simp; linarith
  have hs_norm : ‖s‖ ≤ r₀ := by
    rw [mem_closedBall_zero_iff] at hz
    have hsq : ‖s‖ ^ 2 ≤ r₀ ^ 2 := by rw [← norm_pow, hs_sq, Real.sq_sqrt hρ_pos.le]; exact hz
    nlinarith [norm_nonneg s, hr₀_pos]
  have hs_re_le : s.re ≤ r₀ := (Complex.re_le_norm s).trans hs_norm
  rw [← hs_sq, F_half_sq, g₄, ξ₄_eq_mul_L₄_of_re_gt (by simp; linarith), Complex.Gammaℝ_def]
  have h2_bd : ‖(2 : ℂ) ^ ((1 : ℂ) / 2 + s)‖ ≤ Real.exp r₀ := by
    have h2eq : (2 : ℂ) ^ ((1 : ℂ) / 2 + s) = ((2 : ℝ) : ℂ) ^ ((1 : ℂ) / 2 + s) := by norm_num
    rw [h2eq, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
    simp only [add_re, div_ofNat_re, one_re]
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    have hlog2 : Real.log 2 ≤ 7 / 10 := by linarith [Real.log_two_lt_d9]
    nlinarith
  have hpi_bd : ‖(Real.pi : ℂ) ^ (-((1 : ℂ) / 2 + s + 1) / 2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have hexp_le : (-((1 : ℂ) / 2 + s + 1) / 2).re ≤ 0 := by
      simp only [div_ofNat_re, neg_re, add_re, one_re]; linarith
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) hexp_le
  have hL_bd : ‖L₄ (1 / 2 + s)‖ ≤ 3 * r₀ := by
    have h1 := norm_L₄_le (s := 1 / 2 + s) (by simp; linarith)
    have hnorm : ‖(1 : ℂ) / 2 + s‖ ≤ 1 / 2 + r₀ := by
      calc ‖(1 : ℂ) / 2 + s‖ ≤ ‖(1 : ℂ) / 2‖ + ‖s‖ := norm_add_le _ _
        _ ≤ 1 / 2 + r₀ := by norm_num; linarith
    linarith
  let N : ℕ := ⌈r₀ / 2 + 3 / 4⌉₊
  have hN_ge : r₀ / 2 + 3 / 4 ≤ (N : ℝ) := Nat.le_ceil _
  have hN_le : (N : ℝ) ≤ r₀ / 2 + 2 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ r₀ / 2 + 3 / 4 by positivity)
    linarith
  have hN_pos : 1 ≤ N := by exact_mod_cast (show (1 : ℝ) ≤ (N : ℝ) by linarith)
  have hG_re : ((1 / 2 + s + 1) / 2 : ℂ).re = (3 / 2 + s.re) / 2 := by
    simp only [div_ofNat_re, add_re, one_re]; ring
  have hG_bd : ‖Complex.Gamma (((1 : ℂ) / 2 + s + 1) / 2)‖ ≤ 5 * (N : ℝ) ^ N := by
    have hre1 : (3 : ℝ) / 4 ≤ (((1 : ℂ) / 2 + s + 1) / 2).re := by rw [hG_re]; linarith
    have hre2 : (((1 : ℂ) / 2 + s + 1) / 2).re ≤ (N : ℝ) + 1 := by rw [hG_re]; linarith
    calc ‖Complex.Gamma (((1 : ℂ) / 2 + s + 1) / 2)‖
        ≤ Real.Gamma (((1 : ℂ) / 2 + s + 1) / 2).re := norm_complex_Gamma_le_real_Gamma (by linarith)
      _ ≤ 4 + (N.factorial : ℝ) := real_Gamma_le_four_add_factorial hre1 hre2
      _ ≤ 4 + (N : ℝ) ^ N := by
          have : N.factorial ≤ N ^ N := Nat.factorial_le_pow N
          linarith [show (N.factorial : ℝ) ≤ (N : ℝ) ^ N by exact_mod_cast this]
      _ ≤ 5 * (N : ℝ) ^ N := by
          have h1 : (1 : ℝ) ≤ (N : ℝ) ^ N := one_le_pow₀ (by exact_mod_cast hN_pos)
          linarith
  have hprod : ‖(2 : ℂ) ^ ((1 : ℂ) / 2 + s) *
      ((Real.pi : ℂ) ^ (-((1 : ℂ) / 2 + s + 1) / 2) * Complex.Gamma (((1 : ℂ) / 2 + s + 1) / 2)) *
      L₄ (1 / 2 + s)‖ ≤ Real.exp r₀ * (5 * (N : ℝ) ^ N) * (3 * r₀) := by
    rw [norm_mul, norm_mul, norm_mul]
    have hmid : ‖(Real.pi : ℂ) ^ (-((1 : ℂ) / 2 + s + 1) / 2)‖ *
        ‖Complex.Gamma (((1 : ℂ) / 2 + s + 1) / 2)‖ ≤ 5 * (N : ℝ) ^ N := by
      calc _ ≤ 1 * (5 * (N : ℝ) ^ N) := mul_le_mul hpi_bd hG_bd (norm_nonneg _) zero_le_one
        _ = 5 * (N : ℝ) ^ N := one_mul _
    exact mul_le_mul (mul_le_mul h2_bd hmid (by positivity) (Real.exp_pos _).le) hL_bd
      (norm_nonneg _) (by positivity)
  refine hprod.trans ?_
  have hlogN : Real.log (N : ℝ) ≤ Real.log r₀ := Real.log_le_log (by positivity) (by linarith)
  have hlog_r₀_le : Real.log r₀ ≤ r₀ := by linarith [Real.log_le_sub_one_of_pos hr₀_pos]
  have h15 : 15 * r₀ ≤ Real.exp (4 * r₀) := by
    have h2 : (4 * r₀) ^ 2 / 2 ≤ Real.exp (4 * r₀) := by
      have := Real.sum_le_exp_of_nonneg (show 0 ≤ 4 * r₀ by positivity) 3
      simp [Finset.sum_range_succ, Nat.factorial] at this
      linarith
    nlinarith
  have hpowN : (N : ℝ) ^ N ≤ Real.exp ((r₀ / 2) * Real.log r₀ + 2 * r₀) := by
    rw [← Real.exp_log (show 0 < (N : ℝ) ^ N by positivity), Real.log_pow]
    apply Real.exp_le_exp.mpr
    calc (N : ℝ) * Real.log (N : ℝ)
        ≤ (r₀ / 2 + 2) * Real.log r₀ :=
          mul_le_mul hN_le hlogN (Real.log_nonneg (by exact_mod_cast hN_pos)) (by positivity)
      _ = (r₀ / 2) * Real.log r₀ + 2 * Real.log r₀ := by ring
      _ ≤ (r₀ / 2) * Real.log r₀ + 2 * r₀ := by linarith
  calc Real.exp r₀ * (5 * (N : ℝ) ^ N) * (3 * r₀)
      = Real.exp r₀ * (15 * r₀) * (N : ℝ) ^ N := by ring
    _ ≤ Real.exp r₀ * Real.exp (4 * r₀) * Real.exp ((r₀ / 2) * Real.log r₀ + 2 * r₀) := by gcongr
    _ = Real.exp ((r₀ / 2) * Real.log r₀ + 7 * r₀) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp ((r₀ / 2) * Real.log r₀ + 10 * r₀) := by apply Real.exp_le_exp.mpr; linarith

lemma log_norm_F_half_lower :
    ∃ C_lo : ℝ, 0 < C_lo ∧ ∀ R : ℝ, 10 ≤ R →
      F_half ((R ^ 2 : ℝ) : ℂ) ≠ 0 ∧
      (R / 2) * Real.log R - C_lo * R ≤ Real.log ‖F_half ((R ^ 2 : ℝ) : ℂ)‖ := by
  refine ⟨10, by norm_num, fun R hR ↦ ?_⟩
  have hR_pos : 0 < R := by linarith
  have hsq : ((R ^ 2 : ℝ) : ℂ) = (R : ℂ) ^ 2 := by push_cast; rfl
  rw [hsq, F_half_sq, g₄, ξ₄_eq_mul_L₄_of_re_gt (by simp; linarith), Complex.Gammaℝ_def]
  have hL_ge : (1 : ℝ) / 2 ≤ ‖L₄ (1 / 2 + (R : ℂ))‖ := by
    have h1 := L₄_real_ge_half (σ := 1 / 2 + R) (by linarith)
    have hcast : ((1 / 2 + R : ℝ) : ℂ) = 1 / 2 + (R : ℂ) := by push_cast; rfl
    rw [hcast] at h1
    exact h1.trans (Complex.re_le_norm _)
  have hL_ne : L₄ (1 / 2 + (R : ℂ)) ≠ 0 := by intro h0; rw [h0, norm_zero] at hL_ge; linarith
  have h2_ge : (1 : ℝ) ≤ ‖(2 : ℂ) ^ ((1 : ℂ) / 2 + (R : ℂ))‖ := by
    have h2eq : (2 : ℂ) ^ ((1 : ℂ) / 2 + (R : ℂ)) = ((2 : ℝ) : ℂ) ^ ((1 : ℂ) / 2 + (R : ℂ)) := by norm_num
    rw [h2eq, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
    simp only [add_re, div_ofNat_re, one_re, ofReal_re]
    exact Real.one_le_rpow (by norm_num) (by linarith)
  have hpi_eq : ‖(Real.pi : ℂ) ^ (-((1 : ℂ) / 2 + (R : ℂ) + 1) / 2)‖ =
      Real.pi ^ (-(3 / 2 + R) / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1; simp only [div_ofNat_re, neg_re, add_re, one_re, ofReal_re]; ring
  have hG_real : ‖Complex.Gamma (((1 : ℂ) / 2 + (R : ℂ) + 1) / 2)‖ =
      Real.Gamma ((3 / 2 + R) / 2) := by
    have hcast : (((1 : ℂ) / 2 + (R : ℂ) + 1) / 2) = (((3 / 2 + R) / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.Gamma_ofReal, Complex.norm_real,
      Real.norm_of_nonneg (Real.Gamma_pos_of_pos (by linarith)).le]
  let k : ℕ := ⌊R / 2⌋₊ - 1
  have hk_ge2 : 2 ≤ k := by
    have h5 : 5 ≤ ⌊R / 2⌋₊ := Nat.le_floor (by norm_num; linarith)
    omega
  have hk_ge_R : R / 2 - 2 ≤ (k : ℝ) := by
    have hfl : R / 2 - 1 < (⌊R / 2⌋₊ : ℝ) := Nat.sub_one_lt_floor (R / 2)
    have h1 : 1 ≤ ⌊R / 2⌋₊ := by have : 5 ≤ ⌊R / 2⌋₊ := Nat.le_floor (by norm_num; linarith); omega
    have hsub : (k : ℝ) = (⌊R / 2⌋₊ : ℝ) - 1 := by dsimp [k]; rw [Nat.cast_sub h1]; simp
    linarith
  have hk_le_R : (k : ℝ) + 1 ≤ (3 / 2 + R) / 2 := by
    have hfl : (⌊R / 2⌋₊ : ℝ) ≤ R / 2 := Nat.floor_le (by positivity)
    have h1 : 1 ≤ ⌊R / 2⌋₊ := by have : 5 ≤ ⌊R / 2⌋₊ := Nat.le_floor (by norm_num; linarith); omega
    have hsub : (k : ℝ) = (⌊R / 2⌋₊ : ℝ) - 1 := by dsimp [k]; rw [Nat.cast_sub h1]; simp
    linarith
  have hG_ge : (k.factorial : ℝ) / 2 ≤ ‖Complex.Gamma (((1 : ℂ) / 2 + (R : ℂ) + 1) / 2)‖ := by
    rw [hG_real]; exact real_Gamma_ge_half_factorial hk_ge2 hk_le_R
  have hG_ne : Complex.Gamma (((1 : ℂ) / 2 + (R : ℂ) + 1) / 2) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hG_ge
    have : (0 : ℝ) < (k.factorial : ℝ) / 2 := by positivity
    linarith
  refine ⟨?_, ?_⟩
  · refine mul_ne_zero (mul_ne_zero ?_ (mul_ne_zero ?_ hG_ne)) hL_ne
    · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
    · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'))
  · have hnorm_ge : Real.pi ^ (-(3 / 2 + R) / 2) * ((k.factorial : ℝ) / 2) * (1 / 2) ≤
        ‖(2 : ℂ) ^ ((1 : ℂ) / 2 + (R : ℂ)) *
          ((Real.pi : ℂ) ^ (-((1 : ℂ) / 2 + (R : ℂ) + 1) / 2) *
            Complex.Gamma (((1 : ℂ) / 2 + (R : ℂ) + 1) / 2)) *
          L₄ (1 / 2 + (R : ℂ))‖ := by
      rw [norm_mul, norm_mul, norm_mul, hpi_eq]
      have hmid : Real.pi ^ (-(3 / 2 + R) / 2) * ((k.factorial : ℝ) / 2) ≤
          ‖(2 : ℂ) ^ ((1 : ℂ) / 2 + (R : ℂ))‖ *
            (Real.pi ^ (-(3 / 2 + R) / 2) * ‖Complex.Gamma (((1 : ℂ) / 2 + (R : ℂ) + 1) / 2)‖) := by
        calc Real.pi ^ (-(3 / 2 + R) / 2) * ((k.factorial : ℝ) / 2)
            = 1 * (Real.pi ^ (-(3 / 2 + R) / 2) * ((k.factorial : ℝ) / 2)) := (one_mul _).symm
          _ ≤ ‖(2 : ℂ) ^ ((1 : ℂ) / 2 + (R : ℂ))‖ *
                (Real.pi ^ (-(3 / 2 + R) / 2) * ‖Complex.Gamma (((1 : ℂ) / 2 + (R : ℂ) + 1) / 2)‖) :=
              mul_le_mul h2_ge (mul_le_mul_of_nonneg_left hG_ge (Real.rpow_nonneg Real.pi_pos.le _))
                (by positivity) (by positivity)
      exact mul_le_mul hmid hL_ge (by positivity) (by positivity)
    have hlog_ge := Real.log_le_log (by positivity) hnorm_ge
    refine le_trans ?_ hlog_ge
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_rpow Real.pi_pos, Real.log_div (by positivity) (by norm_num),
      Real.log_div (by norm_num) (by norm_num), Real.log_one]
    have hstirl := Stirling.le_log_factorial_stirling (n := k) (by omega)
    have hlog_k_nn : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
    have hlog_2pi_nn : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
    have hk_stirl : (k : ℝ) * Real.log (k : ℝ) - (k : ℝ) ≤ Real.log (k.factorial : ℝ) := by linarith
    have hk_ge_quarter : R / 4 ≤ (k : ℝ) := by linarith
    have hlogk_ge : Real.log R - Real.log 4 ≤ Real.log (k : ℝ) := by
      have h1 := Real.log_le_log (by positivity) hk_ge_quarter
      rw [Real.log_div hR_pos.ne' (by norm_num)] at h1
      exact h1
    have hlogR_le : Real.log R ≤ R := by linarith [Real.log_le_sub_one_of_pos hR_pos]
    have hlogR_nn : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
    have hlog2_le : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hlog4_le : Real.log 4 ≤ 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
    have hlogpi_le : Real.log Real.pi ≤ 2 :=
      (Real.log_le_log Real.pi_pos Real.pi_lt_four.le).trans hlog4_le
    have hlogpi_nn : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
    have hklogk : (R / 2) * Real.log R - 4 * R ≤ (k : ℝ) * Real.log (k : ℝ) := by
      have h1 : (R / 2 - 2) * (Real.log R - Real.log 4) ≤ (k : ℝ) * Real.log (k : ℝ) := by
        by_cases hneg : Real.log R - Real.log 4 ≤ 0
        · exact (mul_nonpos_of_nonneg_of_nonpos (by linarith) hneg).trans (mul_nonneg (by positivity) hlog_k_nn)
        · push Not at hneg
          exact mul_le_mul hk_ge_R hlogk_ge hneg.le (by positivity)
      nlinarith
    have hk_le : (k : ℝ) ≤ R / 2 := by linarith
    nlinarith

lemma F_half_zeros_equiv (hzf : ∀ s : ℂ, 1 / 2 < s.re → L₄ s ≠ 0) :
    (∀ u : ℂ, F_half u = 0 ↔ ∃ γ : ℝ, 0 < γ ∧ u = -((γ ^ 2 : ℝ) : ℂ) ∧ L₄ (1 / 2 + (γ : ℂ) * Complex.I) = 0) ∧
    (∀ γ : ℝ, 0 < γ →
      analyticOrderAt F_half (-((γ ^ 2 : ℝ) : ℂ)) = analyticOrderAt L₄ (1 / 2 + (γ : ℂ) * Complex.I)) := by
  have hξ_zero_iff : ∀ s : ℂ, ξ₄ s = 0 ↔ s.re = 1 / 2 ∧ L₄ s = 0 := by
    intro s
    constructor
    · intro h0
      have hre : s.re = 1 / 2 := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have h1s : 1 / 2 < (1 - s).re := by simp; linarith
          have hξ1 : ξ₄ (1 - s) = 0 := by rw [ξ₄_one_sub, h0]
          rw [ξ₄_eq_mul_L₄_of_re_gt (by linarith)] at hξ1
          have h2 : (2 : ℂ) ^ (1 - s) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
          have hG : Complex.Gammaℝ (1 - s + 1) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
          exact hzf (1 - s) h1s ((mul_eq_zero.mp hξ1).resolve_left (mul_ne_zero h2 hG))
        · rw [ξ₄_eq_mul_L₄_of_re_gt (by linarith)] at h0
          have h2 : (2 : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
          have hG : Complex.Gammaℝ (s + 1) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
          exact hzf s hgt ((mul_eq_zero.mp h0).resolve_left (mul_ne_zero h2 hG))
      refine ⟨hre, ?_⟩
      rw [ξ₄_eq_mul_L₄_of_re_gt (by linarith)] at h0
      have h2 : (2 : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
      have hG : Complex.Gammaℝ (s + 1) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
      exact (mul_eq_zero.mp h0).resolve_left (mul_ne_zero h2 hG)
    · rintro ⟨hre, hL0⟩
      rw [ξ₄_eq_mul_L₄_of_re_gt (by linarith), hL0, mul_zero]
  constructor
  · intro u
    constructor
    · intro hu0
      obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self u
      have hs2 : s ^ 2 = u := by simpa [sq] using hs.symm
      rw [← hs2, F_half_sq, g₄, hξ_zero_iff] at hu0
      have hsre : s.re = 0 := by have := hu0.1; simp at this; linarith
      have hs_eq : s = (s.im : ℂ) * Complex.I := by apply Complex.ext <;> simp [hsre]
      have hsim_ne : s.im ≠ 0 := by
        intro him0
        have hs0 : s = 0 := by rw [hs_eq, him0, Complex.ofReal_zero, zero_mul]
        rw [hs0, add_zero] at hu0
        exact ξ₄_half_ne_zero ((hξ_zero_iff _).mpr hu0)
      refine ⟨|s.im|, abs_pos.mpr hsim_ne, ?_, ?_⟩
      · have hsq1 : s ^ 2 = -((s.im ^ 2 : ℝ) : ℂ) := by
          conv_lhs => rw [hs_eq]
          rw [mul_pow, Complex.I_sq]; push_cast; ring
        rw [← hs2, hsq1, sq_abs]
      · rcases le_or_gt 0 s.im with hge | hlt
        · rw [abs_of_nonneg hge, ← hs_eq]; exact hu0.2
        · rw [abs_of_neg hlt]
          have hconj : (1 : ℂ) / 2 + ((-s.im : ℝ) : ℂ) * Complex.I = conj (1 / 2 + s) := by
            apply Complex.ext <;> simp [hsre]
          rw [hconj, L₄_conj, hu0.2, map_zero]
    · rintro ⟨γ, _, rfl, hL0⟩
      have hsq : ((γ : ℂ) * Complex.I) ^ 2 = -((γ ^ 2 : ℝ) : ℂ) := by
        rw [mul_pow, Complex.I_sq]; push_cast; ring
      rw [← hsq, F_half_sq, g₄, hξ_zero_iff]
      exact ⟨by simp, hL0⟩
  · intro γ hγ
    let u₀ : ℂ := -((γ ^ 2 : ℝ) : ℂ)
    let s₀ : ℂ := (γ : ℂ) * Complex.I
    have hs₀_sq : s₀ ^ 2 = u₀ := by dsimp [s₀, u₀]; rw [mul_pow, Complex.I_sq]; push_cast; ring
    have h1 : analyticOrderAt g₄ s₀ = analyticOrderAt L₄ (1 / 2 + s₀) := by
      let W : ℂ → ℂ := fun s ↦ (2 : ℂ) ^ (1 / 2 + s) * Complex.Gammaℝ (1 / 2 + s + 1)
      have hW_an : AnalyticAt ℂ W s₀ := by
        have hdiff : DifferentiableOn ℂ W {s : ℂ | -1 < s.re} := by
          intro z hz
          have hre : -1 < z.re := hz
          have hd1 : DifferentiableAt ℂ (fun w : ℂ ↦ (2 : ℂ) ^ (1 / 2 + w)) z :=
            (differentiableAt_const _ |>.add differentiableAt_id).const_cpow (Or.inl (by norm_num))
          have hG_re : 0 < ((1 / 2 + z + 1) / 2 : ℂ).re := by
            simp only [div_ofNat_re, add_re, one_re]; linarith
          have hd2 : DifferentiableAt ℂ (fun w : ℂ ↦ Complex.Gammaℝ (1 / 2 + w + 1)) z := by
            have hGamma : DifferentiableAt ℂ Complex.Gamma ((1 / 2 + z + 1) / 2) :=
              Complex.differentiableAt_Gamma _ (fun m hm ↦ by
                have := congrArg Complex.re hm; simp at this; linarith)
            have hlin : DifferentiableAt ℂ (fun w : ℂ ↦ (1 / 2 + w + 1) / 2) z := by fun_prop
            have hpi : DifferentiableAt ℂ (fun w : ℂ ↦ (Real.pi : ℂ) ^ (-(1 / 2 + w + 1) / 2)) z :=
              (((differentiableAt_const _ |>.add differentiableAt_id |>.add_const _).neg.div_const _).const_cpow
                (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')))
            have hcomp : DifferentiableAt ℂ (fun w : ℂ ↦ Complex.Gamma ((1 / 2 + w + 1) / 2)) z :=
              DifferentiableAt.comp z hGamma hlin
            have hmul := hpi.mul hcomp
            exact hmul
          exact (hd1.mul hd2).differentiableWithinAt
        exact (hdiff.analyticOnNhd (isOpen_lt continuous_const continuous_re)) s₀ (by simp [s₀])
      have hW_ne : W s₀ ≠ 0 :=
        mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num)))
          (Complex.Gammaℝ_ne_zero_of_re_pos (by simp [s₀]; norm_num))
      have hge : g₄ =ᶠ[𝓝 s₀] fun s ↦ W s * L₄ (1 / 2 + s) := by
        filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds (by simp [s₀] : (-1 : ℝ) < s₀.re)]
          with s hs
        dsimp only [g₄, W]
        exact ξ₄_eq_mul_L₄_of_re_gt (by simp; linarith)
      have hLshift_an : AnalyticAt ℂ (fun s ↦ L₄ (1 / 2 + s)) s₀ :=
        ((differentiable_L₄.comp (differentiable_const _ |>.add differentiable_id)).differentiableOn.analyticOnNhd
          isOpen_univ) s₀ (Set.mem_univ _)
      have hmul_ord : analyticOrderAt (fun s ↦ W s * L₄ (1 / 2 + s)) s₀ =
          analyticOrderAt W s₀ + analyticOrderAt (fun s ↦ L₄ (1 / 2 + s)) s₀ :=
        analyticOrderAt_mul hW_an hLshift_an
      rw [analyticOrderAt_congr hge, hmul_ord, hW_an.analyticOrderAt_eq_zero.mpr hW_ne, zero_add]
      have hL_an : AnalyticAt ℂ L₄ (1 / 2 + s₀) :=
        (differentiable_L₄.differentiableOn.analyticOnNhd isOpen_univ) _ (Set.mem_univ _)
      have hL_ne_top : analyticOrderAt L₄ (1 / 2 + s₀) ≠ ⊤ := by
        intro htop
        have h0 := (differentiable_L₄.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
          isPreconnected_univ (Set.mem_univ _) (analyticOrderAt_eq_top.mp htop)
        exact L₄_real_ne_zero zero_lt_one (h0 (Set.mem_univ 1))
      lift analyticOrderAt L₄ (1 / 2 + s₀) to ℕ using hL_ne_top with m hm
      rw [hLshift_an.analyticOrderAt_eq_natCast]
      have hm' := hL_an.analyticOrderAt_eq_natCast.mp hm.symm
      obtain ⟨q, hq_an, hq_ne, hq_eq⟩ := hm'
      refine ⟨fun s ↦ q (1 / 2 + s), hq_an.comp (by fun_prop), hq_ne, ?_⟩
      have hcont : ContinuousAt (fun s : ℂ ↦ 1 / 2 + s) s₀ := by fun_prop
      filter_upwards [hcont.tendsto.eventually hq_eq] with s hs
      simpa [add_sub_add_left_eq_sub] using hs
    have hF_an : AnalyticAt ℂ F_half u₀ :=
      (differentiable_F_half.differentiableOn.analyticOnNhd isOpen_univ) u₀ (Set.mem_univ _)
    have hF_ne_top : analyticOrderAt F_half u₀ ≠ ⊤ := by
      intro htop
      have h0 := (differentiable_F_half.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (Set.mem_univ _) (analyticOrderAt_eq_top.mp htop)
      exact F_half_zero_ne_zero (h0 (Set.mem_univ 0))
    lift analyticOrderAt F_half u₀ to ℕ using hF_ne_top with m hm
    have h2 : analyticOrderAt g₄ s₀ = (m : ℕ∞) := by
      obtain ⟨q, hq_an, hq_ne, hq_eq⟩ := hF_an.analyticOrderAt_eq_natCast.mp hm.symm
      have hg_an : AnalyticAt ℂ g₄ s₀ :=
        (differentiable_g₄.differentiableOn.analyticOnNhd isOpen_univ) s₀ (Set.mem_univ _)
      rw [hg_an.analyticOrderAt_eq_natCast]
      refine ⟨fun s ↦ (s + s₀) ^ m * q (s ^ 2), ?_, ?_, ?_⟩
      · have hsq_an : AnalyticAt ℂ (fun s : ℂ ↦ s ^ 2) s₀ := by fun_prop
        have hq_comp : AnalyticAt ℂ (fun s : ℂ ↦ q (s ^ 2)) s₀ := by
          rw [← hs₀_sq] at hq_an
          exact AnalyticAt.comp (g := q) (f := fun s : ℂ ↦ s ^ 2) hq_an hsq_an
        exact ((by fun_prop : AnalyticAt ℂ (fun s : ℂ ↦ (s + s₀) ^ m) s₀).mul hq_comp)
      · refine mul_ne_zero (pow_ne_zero m ?_) (by rw [hs₀_sq]; exact hq_ne)
        dsimp only [s₀]; intro h0; have := congrArg Complex.im h0; simp at this; linarith
      · have hcont : ContinuousAt (fun s : ℂ ↦ s ^ 2) s₀ := by fun_prop
        rw [← hs₀_sq] at hq_eq
        filter_upwards [hcont.tendsto.eventually hq_eq] with s hs
        rw [← F_half_sq s, hs]
        have hfact : s ^ 2 - s₀ ^ 2 = (s - s₀) * (s + s₀) := by ring
        rw [hfact, mul_pow, smul_eq_mul, smul_eq_mul]; ring
    rw [← hm, ← h1, h2]

/- Helper lemmas for Pillar 2 (kept modular so compilation stays fast) -/

lemma F_half_an_closedBall (R : ℝ) : AnalyticOnNhd ℂ F_half (Metric.closedBall (0 : ℂ) R) :=
  (differentiable_F_half.differentiableOn.analyticOnNhd isOpen_univ).mono (Set.subset_univ _)

lemma F_half_analyticOrderAt_ne_top (u : ℂ) : analyticOrderAt F_half u ≠ ⊤ := by
  intro htop
  have h0 := (differentiable_F_half.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ _) (analyticOrderAt_eq_top.mp htop)
  exact F_half_zero_ne_zero (h0 (Set.mem_univ 0))

lemma enat_map_cast_untop₀ (n : ℕ) : (ENat.map Nat.cast (n : ℕ∞)).untop₀ = (n : ℤ) := by
  simp

lemma exists_zero_finset (hzf : ∀ s : ℂ, 1 / 2 < s.re → L₄ s ≠ 0) {T : ℝ} (hT : 0 < T) :
    ∃ Z : Finset ℝ, ∀ g : ℝ, g ∈ Z ↔ 0 < g ∧ g ≤ T ∧ L₄ (1 / 2 + (g : ℂ) * Complex.I) = 0 := by
  classical
  obtain ⟨hz_iff, _⟩ := F_half_zeros_equiv hzf
  have hfin := (MeromorphicOn.divisor F_half (Metric.closedBall (0 : ℂ) (T ^ 2))).finiteSupport
    (isCompact_closedBall (0 : ℂ) (T ^ 2))
  refine ⟨hfin.toFinset.image (fun u ↦ Real.sqrt ‖u‖) |>.filter
    (fun g ↦ 0 < g ∧ g ≤ T ∧ L₄ (1 / 2 + (g : ℂ) * Complex.I) = 0), fun g ↦ ?_⟩
  simp only [Finset.mem_filter, Finset.mem_image, Set.Finite.mem_toFinset, Function.mem_support]
  constructor
  · exact fun h ↦ h.2
  · rintro ⟨hg0, hgT, hL0⟩
    refine ⟨⟨-((g ^ 2 : ℝ) : ℂ), ?_, ?_⟩, hg0, hgT, hL0⟩
    · have hmem : -((g ^ 2 : ℝ) : ℂ) ∈ Metric.closedBall (0 : ℂ) (T ^ 2) := by
        rw [mem_closedBall_zero_iff, norm_neg, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg g)]
        nlinarith
      have hF0 : F_half (-((g ^ 2 : ℝ) : ℂ)) = 0 := (hz_iff _).mpr ⟨g, hg0, rfl, hL0⟩
      have hne0 : analyticOrderAt F_half (-((g ^ 2 : ℝ) : ℂ)) ≠ 0 :=
        fun h0 ↦ ((F_half_an_closedBall (T ^ 2) _ hmem).analyticOrderAt_eq_zero.mp h0) hF0
      rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (F_half_an_closedBall (T ^ 2)) hmem]
      cases h : analyticOrderAt F_half (-((g ^ 2 : ℝ) : ℂ)) with
      | top => exact absurd h (F_half_analyticOrderAt_ne_top _)
      | coe n =>
        rw [enat_map_cast_untop₀]
        exact_mod_cast (fun hn : n = 0 ↦ hne0 (by rw [h, hn]; rfl))
    · rw [norm_neg, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg g), Real.sqrt_sq hg0.le]

lemma F_half_divisor_weighted_sum (hzf : ∀ s : ℂ, 1 / 2 < s.re → L₄ s ≠ 0)
    {t : ℝ} (ht : 0 < t) {Z : Finset ℝ}
    (hZ : ∀ g : ℝ, g ∈ Z ↔ 0 < g ∧ g ≤ t ∧ L₄ (1 / 2 + (g : ℂ) * Complex.I) = 0)
    (φ : ℝ → ℝ) :
    (∑ᶠ u, (MeromorphicOn.divisor F_half (Metric.closedBall (0 : ℂ) (t ^ 2)) u : ℝ) * φ ‖u‖) =
      ∑ g ∈ Z, ((analyticOrderAt L₄ (1 / 2 + (g : ℂ) * Complex.I)).toNat : ℝ) * φ (g ^ 2) := by
  classical
  obtain ⟨hz_iff, hord_eq⟩ := F_half_zeros_equiv hzf
  have hfin := (MeromorphicOn.divisor F_half (Metric.closedBall (0 : ℂ) (t ^ 2))).finiteSupport
    (isCompact_closedBall (0 : ℂ) (t ^ 2))
  rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (fun u hu ↦ by
    rw [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
    intro h0
    rw [Function.mem_support, h0, Int.cast_zero, zero_mul] at hu
    exact hu rfl)]
  symm
  refine Finset.sum_bij (fun g _ ↦ -((g ^ 2 : ℝ) : ℂ)) ?_ ?_ ?_ ?_
  · intro g hg
    obtain ⟨hg0, hgt, hL0⟩ := (hZ g).mp hg
    simp only [Set.Finite.mem_toFinset, Function.mem_support]
    have hmem : -((g ^ 2 : ℝ) : ℂ) ∈ Metric.closedBall (0 : ℂ) (t ^ 2) := by
      rw [mem_closedBall_zero_iff, norm_neg, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg g)]
      nlinarith
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (F_half_an_closedBall (t ^ 2)) hmem]
    have hF0 : F_half (-((g ^ 2 : ℝ) : ℂ)) = 0 := (hz_iff _).mpr ⟨g, hg0, rfl, hL0⟩
    have hne0 : analyticOrderAt F_half (-((g ^ 2 : ℝ) : ℂ)) ≠ 0 :=
      fun h0 ↦ ((F_half_an_closedBall (t ^ 2) _ hmem).analyticOrderAt_eq_zero.mp h0) hF0
    cases h : analyticOrderAt F_half (-((g ^ 2 : ℝ) : ℂ)) with
    | top => exact absurd h (F_half_analyticOrderAt_ne_top _)
    | coe n =>
      rw [enat_map_cast_untop₀]
      exact_mod_cast (fun hn : n = 0 ↦ hne0 (by rw [h, hn]; rfl))
  · intro g₁ hg₁ g₂ hg₂ heq
    have h1 := ((hZ g₁).mp hg₁).1
    have h2 := ((hZ g₂).mp hg₂).1
    have hre := congrArg Complex.re heq
    simp only [neg_re, ofReal_re, neg_inj] at hre
    nlinarith
  · intro u hu
    simp only [Set.Finite.mem_toFinset, Function.mem_support] at hu
    have hu_mem : u ∈ Metric.closedBall (0 : ℂ) (t ^ 2) :=
      (MeromorphicOn.divisor F_half (Metric.closedBall (0 : ℂ) (t ^ 2))).supportWithinDomain hu
    have hFu0 : F_half u = 0 := by
      by_contra hne
      rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (F_half_an_closedBall (t ^ 2)) hu_mem,
        (F_half_an_closedBall (t ^ 2) u hu_mem).analyticOrderAt_eq_zero.mpr hne] at hu
      simp at hu
    obtain ⟨g, hg0, rfl, hL0⟩ := (hz_iff u).mp hFu0
    refine ⟨g, (hZ g).mpr ⟨hg0, ?_, hL0⟩, rfl⟩
    rw [mem_closedBall_zero_iff, norm_neg, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg g)] at hu_mem
    nlinarith
  · intro g hg
    obtain ⟨hg0, hgt, _⟩ := (hZ g).mp hg
    have hmem : -((g ^ 2 : ℝ) : ℂ) ∈ Metric.closedBall (0 : ℂ) (t ^ 2) := by
      rw [mem_closedBall_zero_iff, norm_neg, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg g)]
      nlinarith
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (F_half_an_closedBall (t ^ 2)) hmem,
      norm_neg, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg g)]
    cases h : analyticOrderAt F_half (-((g ^ 2 : ℝ) : ℂ)) with
    | top => exact absurd h (F_half_analyticOrderAt_ne_top _)
    | coe n =>
      rw [enat_map_cast_untop₀, ← hord_eq g hg0, h]
      simp

lemma summable_succ_mul_half_pow : Summable (fun j : ℕ ↦ ((j + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ j) := by
  refine Summable.of_nonneg_of_le (fun j ↦ by positivity) (fun j ↦ ?_)
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num)).mul_left 2)
  have h1 : (1 : ℝ) + (j : ℝ) * (1 / 2 : ℝ) ≤ (1 + (1 / 2 : ℝ)) ^ j :=
    one_add_mul_le_pow (by norm_num) j
  have h2 : ((j + 1 : ℕ) : ℝ) ≤ 2 * (3 / 2 : ℝ) ^ j := by
    push_cast; norm_num at h1; linarith
  calc ((j + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ j
      ≤ (2 * (3 / 2 : ℝ) ^ j) * (1 / 2 : ℝ) ^ j :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = 2 * ((3 / 2 : ℝ) * (1 / 2 : ℝ)) ^ j := by rw [mul_pow]; ring
    _ = 2 * (3 / 4 : ℝ) ^ j := by norm_num

lemma pillar2_zero_sum_bound (hzf : ∀ s : ℂ, 1 / 2 < s.re → L₄ s ≠ 0) :
    ∃ C_sum : ℝ, ∀ (T : ℝ) (Z : Finset ℝ), 2 ≤ T →
      (∀ g : ℝ, g ∈ Z ↔ 0 < g ∧ g ≤ T ∧ L₄ (1 / 2 + (g : ℂ) * Complex.I) = 0) →
      ∑ g ∈ Z, ((analyticOrderAt L₄ (1 / 2 + (g : ℂ) * Complex.I)).toNat : ℝ) / (1 / 4 + g ^ 2) ≤ C_sum := by
  classical
  obtain ⟨C_up, hCup_pos, hF_upper⟩ := norm_F_half_upper
  let c₀ : ℝ := max 0 (-Real.log ‖F_half 0‖)
  let C₁ : ℝ := (2 + 4 * C_up + 2 * c₀ + 10) / Real.log 4
  have hc0_nn : 0 ≤ c₀ := le_max_left _ _
  have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hC₁_pos : 0 < C₁ := by dsimp [C₁]; positivity
  have hN_up : ∀ (t : ℝ) (Z : Finset ℝ), 2 ≤ t →
      (∀ g : ℝ, g ∈ Z ↔ 0 < g ∧ g ≤ t ∧ L₄ (1 / 2 + (g : ℂ) * Complex.I) = 0) →
      (∑ g ∈ Z, ((analyticOrderAt L₄ (1 / 2 + (g : ℂ) * Complex.I)).toNat : ℝ)) ≤ C₁ * t * Real.log t := by
    intro t Z ht hZ
    have ht0 : 0 < t := by linarith
    have h4t2 : 16 ≤ 4 * t ^ 2 := by nlinarith
    have hsqrt4 : Real.sqrt (4 * t ^ 2) = 2 * t := by
      rw [show 4 * t ^ 2 = (2 * t) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    let M : ℝ := Real.exp (t * Real.log (2 * t) + C_up * (2 * t))
    have hM1 : 1 ≤ M := Real.one_le_exp (by
      have : 0 ≤ Real.log (2 * t) := Real.log_nonneg (by linarith); positivity)
    have hFM : ∀ z ∈ Metric.sphere (0 : ℂ) |4 * t ^ 2|, ‖F_half z‖ ≤ M := by
      intro z hz
      rw [abs_of_pos (by positivity)] at hz
      have hle := hF_upper (4 * t ^ 2) h4t2 z (Metric.sphere_subset_closedBall hz)
      rw [hsqrt4] at hle
      simpa [M, show 2 * t / 2 = t by ring] using hle
    have hjens := (F_half_an_closedBall |4 * t ^ 2|).sum_divisor_le (c := 0) (r := t ^ 2) (R := 4 * t ^ 2) (M := M)
      (by rw [abs_of_pos (by positivity)]; positivity)
      (by rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]; nlinarith)
      hM1 F_half_zero_ne_zero hFM
    rw [abs_of_pos (by positivity)] at hjens
    have hdiv_cast : ((∑ᶠ u, MeromorphicOn.divisor F_half (Metric.closedBall (0 : ℂ) (t ^ 2)) u : ℤ) : ℝ) =
        ∑ᶠ u, (MeromorphicOn.divisor F_half (Metric.closedBall (0 : ℂ) (t ^ 2)) u : ℝ) :=
      map_finsum (Int.castRingHom ℝ)
        ((MeromorphicOn.divisor F_half (Metric.closedBall (0 : ℂ) (t ^ 2))).finiteSupport
          (isCompact_closedBall _ _))
    have hsum_eq := F_half_divisor_weighted_sum hzf ht0 hZ (fun _ ↦ 1)
    simp only [mul_one] at hsum_eq
    rw [← hsum_eq, ← hdiv_cast]
    refine hjens.trans ?_
    have h4rat : 4 * t ^ 2 / t ^ 2 = 4 := by field_simp
    rw [h4rat, Real.log_div (by positivity) (norm_pos_iff.mpr F_half_zero_ne_zero).ne', Real.log_exp]
    dsimp only [C₁]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hlog4_pos.le
    have hlog2t : Real.log (2 * t) ≤ 2 * Real.log t := by
      rw [Real.log_mul (by norm_num) ht0.ne']
      linarith [Real.log_le_log (by norm_num) ht]
    have hlogt_ge : (1 : ℝ) / 2 ≤ Real.log t := by
      linarith [Real.log_le_log (by norm_num) ht, Real.log_two_gt_d9]
    have hc0_ge : -Real.log ‖F_half 0‖ ≤ c₀ := le_max_right _ _
    have htlog_ge1 : 1 ≤ t * Real.log t := by nlinarith
    have hbd1 : t * Real.log (2 * t) ≤ 2 * t * Real.log t := by nlinarith
    have hbd2 : C_up * (2 * t) ≤ 4 * C_up * t * Real.log t := by
      have : 2 * t ≤ 4 * t * Real.log t := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this hCup_pos.le]
    have hbd3 : c₀ ≤ 2 * c₀ * t * Real.log t := by
      nlinarith [mul_le_mul_of_nonneg_left htlog_ge1 hc0_nn]
    nlinarith
  obtain ⟨Z₁, hZ₁⟩ := exists_zero_finset hzf (by norm_num : (0 : ℝ) < 2)
  let C_small : ℝ := ∑ g ∈ Z₁, ((analyticOrderAt L₄ (1 / 2 + (g : ℂ) * Complex.I)).toNat : ℝ) / (1 / 4 + g ^ 2)
  have hsum_dyad : Summable (fun j : ℕ ↦ (C₁ * (2 ^ (j + 1) : ℝ) * (((j + 1 : ℕ) : ℝ) * Real.log 2)) / (2 ^ j : ℝ) ^ 2) := by
    refine (summable_succ_mul_half_pow.mul_left (2 * C₁ * Real.log 2)).congr fun j ↦ ?_
    have hpow : (2 ^ (j + 1) : ℝ) / (2 ^ j : ℝ) ^ 2 = 2 * (1 / 2 : ℝ) ^ j := by
      rw [pow_succ, sq, one_div, inv_pow]; field_simp
    calc (2 * C₁ * Real.log 2) * (((j + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ j)
        = C₁ * (2 * (1 / 2 : ℝ) ^ j) * (((j + 1 : ℕ) : ℝ) * Real.log 2) := by ring
      _ = C₁ * ((2 ^ (j + 1) : ℝ) / (2 ^ j : ℝ) ^ 2) * (((j + 1 : ℕ) : ℝ) * Real.log 2) := by rw [← hpow]
      _ = (C₁ * (2 ^ (j + 1) : ℝ) * (((j + 1 : ℕ) : ℝ) * Real.log 2)) / (2 ^ j : ℝ) ^ 2 := by ring
  refine ⟨C_small + ∑' j : ℕ, (C₁ * (2 ^ (j + 1) : ℝ) * (((j + 1 : ℕ) : ℝ) * Real.log 2)) / (2 ^ j : ℝ) ^ 2,
    fun T Z hT hZ ↦ ?_⟩
  let w (g : ℝ) : ℝ := ((analyticOrderAt L₄ (1 / 2 + (g : ℂ) * Complex.I)).toNat : ℝ)
  have hw_nn : ∀ g, 0 ≤ w g := fun _ ↦ Nat.cast_nonneg _
  rw [← Finset.sum_filter_add_sum_filter_not Z (fun g ↦ g ≤ 2)]
  have hpart1 : ∑ g ∈ Z.filter (fun g ↦ g ≤ 2), w g / (1 / 4 + g ^ 2) ≤ C_small := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun g _ _ ↦ div_nonneg (hw_nn g) (by positivity))
    intro g hg
    obtain ⟨hgZ, hg2⟩ := Finset.mem_filter.mp hg
    exact (hZ₁ g).mpr ⟨((hZ g).mp hgZ).1, hg2, ((hZ g).mp hgZ).2.2⟩
  let K : ℕ := Nat.log 2 ⌈T⌉₊ + 2
  have hpart2 : ∑ g ∈ Z.filter (fun g ↦ ¬ g ≤ 2), w g / (1 / 4 + g ^ 2) ≤
      ∑ j ∈ Finset.range K, (C₁ * (2 ^ (j + 1) : ℝ) * (((j + 1 : ℕ) : ℝ) * Real.log 2)) / (2 ^ j : ℝ) ^ 2 := by
    have hcover : Z.filter (fun g ↦ ¬ g ≤ 2) ⊆
        (Finset.range K).biUnion (fun j ↦ Z.filter (fun g ↦ (2 ^ j : ℝ) < g ∧ g ≤ (2 ^ (j + 1) : ℝ))) := by
      intro g hg
      obtain ⟨hgZ, hng2⟩ := Finset.mem_filter.mp hg
      push Not at hng2
      obtain ⟨_, hgT, _⟩ := (hZ g).mp hgZ
      rw [Finset.mem_biUnion]
      let j : ℕ := Nat.log 2 ⌊g⌋₊
      have hfl_ge2 : 2 ≤ ⌊g⌋₊ := Nat.le_floor (by norm_num; linarith)
      have hj_lt : j < K := by
        have hfl_le : ⌊g⌋₊ ≤ ⌈T⌉₊ := Nat.floor_le_of_le (hgT.trans (Nat.le_ceil T))
        have := Nat.log_mono_right (b := 2) hfl_le
        dsimp [j, K]; omega
      have hpow1 : (2 ^ j : ℝ) ≤ (⌊g⌋₊ : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 (by omega : ⌊g⌋₊ ≠ 0)
      have hpow2 : (⌊g⌋₊ : ℝ) + 1 ≤ (2 ^ (j + 1) : ℝ) := by
        have : ⌊g⌋₊ < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) ⌊g⌋₊
        exact_mod_cast this
      by_cases heq : (2 ^ j : ℝ) = g
      · have hj1 : 1 ≤ j := by
          by_contra h0; push Not at h0
          have : j = 0 := by omega
          rw [this, pow_zero] at heq; linarith
        refine ⟨j - 1, Finset.mem_range.mpr (by omega), Finset.mem_filter.mpr ⟨hgZ, ?_, ?_⟩⟩
        · rw [← heq]
          exact_mod_cast Nat.pow_lt_pow_right (by norm_num) (by omega : j - 1 < j)
        · rw [show j - 1 + 1 = j by omega, heq]
      · refine ⟨j, Finset.mem_range.mpr hj_lt, Finset.mem_filter.mpr ⟨hgZ, ?_, ?_⟩⟩
        · exact lt_of_le_of_ne (hpow1.trans (Nat.floor_le (by linarith))) heq
        · linarith [Nat.lt_floor_add_one g]
    have hdisj_shells : Set.PairwiseDisjoint (Finset.range K : Set ℕ)
        (fun j ↦ Z.filter (fun g ↦ (2 ^ j : ℝ) < g ∧ g ≤ (2 ^ (j + 1) : ℝ))) := by
      intro j₁ _ j₂ _ hne
      show Disjoint _ _
      rw [Finset.disjoint_left]
      intro g h1 h2
      have ha := (Finset.mem_filter.mp h1).2
      have hb := (Finset.mem_filter.mp h2).2
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have : (2 ^ (j₁ + 1) : ℝ) ≤ (2 ^ j₂ : ℝ) := by
          exact_mod_cast Nat.pow_le_pow_right (by norm_num) (by omega)
        linarith
      · have : (2 ^ (j₂ + 1) : ℝ) ≤ (2 ^ j₁ : ℝ) := by
          exact_mod_cast Nat.pow_le_pow_right (by norm_num) (by omega)
        linarith
    calc ∑ g ∈ Z.filter (fun g ↦ ¬ g ≤ 2), w g / (1 / 4 + g ^ 2)
        ≤ ∑ g ∈ (Finset.range K).biUnion (fun j ↦ Z.filter (fun g ↦ (2 ^ j : ℝ) < g ∧ g ≤ (2 ^ (j + 1) : ℝ))),
            w g / (1 / 4 + g ^ 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg hcover (fun g _ _ ↦ div_nonneg (hw_nn g) (by positivity))
      _ = ∑ j ∈ Finset.range K, ∑ g ∈ Z.filter (fun g ↦ (2 ^ j : ℝ) < g ∧ g ≤ (2 ^ (j + 1) : ℝ)),
            w g / (1 / 4 + g ^ 2) := Finset.sum_biUnion hdisj_shells
      _ ≤ ∑ j ∈ Finset.range K, (C₁ * (2 ^ (j + 1) : ℝ) * (((j + 1 : ℕ) : ℝ) * Real.log 2)) / (2 ^ j : ℝ) ^ 2 := by
          refine Finset.sum_le_sum fun j _ ↦ ?_
          obtain ⟨Zj, hZj⟩ := exists_zero_finset hzf (show (0 : ℝ) < (2 ^ (j + 1) : ℝ) by positivity)
          have hsub_Zj : Z.filter (fun g ↦ (2 ^ j : ℝ) < g ∧ g ≤ (2 ^ (j + 1) : ℝ)) ⊆ Zj := by
            intro g hg
            obtain ⟨hgZ, _, hgle⟩ := Finset.mem_filter.mp hg
            exact (hZj g).mpr ⟨((hZ g).mp hgZ).1, hgle, ((hZ g).mp hgZ).2.2⟩
          have hstep1 : ∑ g ∈ Z.filter (fun g ↦ (2 ^ j : ℝ) < g ∧ g ≤ (2 ^ (j + 1) : ℝ)),
              w g / (1 / 4 + g ^ 2) ≤ (∑ g ∈ Zj, w g) / (2 ^ j : ℝ) ^ 2 := by
            rw [Finset.sum_div]
            calc _ ≤ ∑ g ∈ Z.filter (fun g ↦ (2 ^ j : ℝ) < g ∧ g ≤ (2 ^ (j + 1) : ℝ)),
                  w g / (2 ^ j : ℝ) ^ 2 := by
                  refine Finset.sum_le_sum fun g hg ↦ ?_
                  have hgt := (Finset.mem_filter.mp hg).2.1
                  refine div_le_div_of_nonneg_left (hw_nn g) (by positivity) ?_
                  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) j]
              _ ≤ ∑ g ∈ Zj, w g / (2 ^ j : ℝ) ^ 2 :=
                  Finset.sum_le_sum_of_subset_of_nonneg hsub_Zj (fun g _ _ ↦ div_nonneg (hw_nn g) (by positivity))
          have h2j1 : (2 : ℝ) ≤ (2 ^ (j + 1) : ℝ) := by
            have : 2 ≤ 2 ^ (j + 1) := (show 2 = 2 ^ 1 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) (by omega)
            exact_mod_cast this
          have hup := hN_up (2 ^ (j + 1) : ℝ) Zj h2j1 hZj
          rw [Real.log_pow] at hup
          exact hstep1.trans (div_le_div_of_nonneg_right hup (by positivity))
  have htail : ∑ j ∈ Finset.range K, (C₁ * (2 ^ (j + 1) : ℝ) * (((j + 1 : ℕ) : ℝ) * Real.log 2)) / (2 ^ j : ℝ) ^ 2 ≤
      ∑' j : ℕ, (C₁ * (2 ^ (j + 1) : ℝ) * (((j + 1 : ℕ) : ℝ) * Real.log 2)) / (2 ^ j : ℝ) ^ 2 :=
    hsum_dyad.sum_le_tsum (Finset.range K) (fun j _ ↦ by
      have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num); positivity)
  linarith

lemma pillar2_zero_count_lower (hzf : ∀ s : ℂ, 1 / 2 < s.re → L₄ s ≠ 0) (A : ℝ) :
    ∃ (T : ℝ) (Z : Finset ℝ), 2 ≤ T ∧
      (∀ g : ℝ, g ∈ Z ↔ 0 < g ∧ g ≤ T ∧ L₄ (1 / 2 + (g : ℂ) * Complex.I) = 0) ∧
      A * T < ∑ g ∈ Z.filter (fun g ↦ 1 ≤ g ∧ g ≤ T / 2),
        ((analyticOrderAt L₄ (1 / 2 + (g : ℂ) * Complex.I)).toNat : ℝ) := by
  classical
  obtain ⟨C_up, hCup_pos, hF_upper⟩ := norm_F_half_upper
  obtain ⟨C_lo, hClo_pos, hF_lower⟩ := log_norm_F_half_lower
  by_contra hno
  push Not at hno
  let A' : ℝ := max A 1
  have hA'_pos : 0 < A' := lt_of_lt_of_le zero_lt_one (le_max_right A 1)
  have hN_lin : ∀ (t : ℝ) (Z : Finset ℝ), 1 ≤ t →
      (∀ g : ℝ, g ∈ Z ↔ 0 < g ∧ g ≤ t ∧ L₄ (1 / 2 + (g : ℂ) * Complex.I) = 0) →
      ∑ g ∈ Z.filter (fun g ↦ 1 ≤ g), ((analyticOrderAt L₄ (1 / 2 + (g : ℂ) * Complex.I)).toNat : ℝ) ≤
        2 * A' * t := by
    intro t Z ht hZ
    obtain ⟨Z2, hZ2⟩ := exists_zero_finset hzf (by linarith : (0 : ℝ) < 2 * t)
    have hle := hno (2 * t) Z2 (by linarith) hZ2
    have hsub : Z.filter (fun g ↦ 1 ≤ g) ⊆ Z2.filter (fun g ↦ 1 ≤ g ∧ g ≤ 2 * t / 2) := by
      intro g hg
      obtain ⟨hgZ, hg1⟩ := Finset.mem_filter.mp hg
      obtain ⟨hg0, hgt, hL0⟩ := (hZ g).mp hgZ
      exact Finset.mem_filter.mpr ⟨(hZ2 g).mpr ⟨hg0, by linarith, hL0⟩, hg1, by linarith⟩
    calc _ ≤ ∑ g ∈ Z2.filter (fun g ↦ 1 ≤ g ∧ g ≤ 2 * t / 2),
            ((analyticOrderAt L₄ (1 / 2 + (g : ℂ) * Complex.I)).toNat : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ Nat.cast_nonneg _)
      _ ≤ A * (2 * t) := hle
      _ ≤ A' * (2 * t) := mul_le_mul_of_nonneg_right (le_max_left A 1) (by linarith)
      _ = 2 * A' * t := by ring
  obtain ⟨Z_small, hZ_small⟩ := exists_zero_finset hzf zero_lt_one
  let w (g : ℝ) : ℝ := ((analyticOrderAt L₄ (1 / 2 + (g : ℂ) * Complex.I)).toNat : ℝ)
  have hw_nn : ∀ g, 0 ≤ w g := fun _ ↦ Nat.cast_nonneg _
  let N_small : ℝ := ∑ g ∈ Z_small, w g
  let L_small : ℝ := ∑ g ∈ Z_small, w g * |Real.log g|
  have hsum_k : Summable (fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ) / (2 ^ k : ℝ)) := by
    refine summable_succ_mul_half_pow.congr fun k ↦ ?_
    rw [one_div, inv_pow, div_eq_mul_inv]
  let S_dyad : ℝ := ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) / (2 ^ k : ℝ)
  have hcontra : ∀ R : ℝ, 10 ≤ R →
      (1 / 5) * R * Real.log R ≤
        (2 * C_lo + C_up + 1 + 12 * A' * Real.log 2 * S_dyad) * R +
        (2 * N_small) * Real.log (3 * R) + (Real.log ‖F_half 0‖ + 2 * L_small) := by
    intro R hR
    have hR_pos : 0 < R := by linarith
    have hfin_supp := (MeromorphicOn.divisor F_half (Metric.closedBall (0 : ℂ) (9 * R ^ 2))).finiteSupport
      (isCompact_closedBall (0 : ℂ) (9 * R ^ 2))
    have hinf_Ioo : (Set.Ioo (89 / 10 * R ^ 2) (9 * R ^ 2)).Infinite := Set.Ioo_infinite (by nlinarith)
    have hfin_norms : ((fun u : ℂ ↦ ‖u‖) '' (MeromorphicOn.divisor F_half (Metric.closedBall (0 : ℂ) (9 * R ^ 2))).support).Finite :=
      hfin_supp.image _
    obtain ⟨ρ, hρ_mem, hρ_avoid⟩ := (hinf_Ioo.sdiff hfin_norms).nonempty
    have hρ_gt : 89 / 10 * R ^ 2 < ρ := hρ_mem.1
    have hρ_lt : ρ < 9 * R ^ 2 := hρ_mem.2
    have hρ_pos : 0 < ρ := by nlinarith
    have hρ_ge16 : 16 ≤ ρ := by nlinarith
    have hsqrt_le : Real.sqrt ρ ≤ 3 * R := by rw [Real.sqrt_le_left (by positivity)]; nlinarith
    have hFsph : ∀ z ∈ Metric.sphere (0 : ℂ) ρ, F_half z ≠ 0 := by
      intro z hz hFz0
      rw [mem_sphere_zero_iff_norm] at hz
      have hmem_cb : z ∈ Metric.closedBall (0 : ℂ) (9 * R ^ 2) := by
        rw [mem_closedBall_zero_iff, hz]; linarith
      have hne0 : analyticOrderAt F_half z ≠ 0 :=
        fun h0 ↦ ((F_half_an_closedBall (9 * R ^ 2) z hmem_cb).analyticOrderAt_eq_zero.mp h0) hFz0
      have hsupp : z ∈ (MeromorphicOn.divisor F_half (Metric.closedBall (0 : ℂ) (9 * R ^ 2))).support := by
        rw [Function.mem_support, MeromorphicOn.AnalyticOnNhd.divisor_apply (F_half_an_closedBall (9 * R ^ 2)) hmem_cb]
        cases h : analyticOrderAt F_half z with
        | top => exact absurd h (F_half_analyticOrderAt_ne_top _)
        | coe n =>
          rw [enat_map_cast_untop₀]
          exact_mod_cast (fun hn : n = 0 ↦ hne0 (by rw [h, hn]; rfl))
      exact hρ_avoid ⟨z, hsupp, hz⟩
    let M : ℝ := Real.exp ((3 * R / 2) * Real.log (3 * R) + C_up * (3 * R))
    have hM1 : 1 ≤ M := Real.one_le_exp (by
      have : 0 ≤ Real.log (3 * R) := Real.log_nonneg (by linarith); positivity)
    have hFM : ∀ z ∈ Metric.sphere (0 : ℂ) ρ, ‖F_half z‖ ≤ M := by
      intro z hz
      have hle := hF_upper ρ hρ_ge16 z (Metric.sphere_subset_closedBall hz)
      refine hle.trans (Real.exp_le_exp.mpr ?_)
      have h1 : Real.log (Real.sqrt ρ) ≤ Real.log (3 * R) :=
        Real.log_le_log (Real.sqrt_pos.mpr hρ_pos) hsqrt_le
      have hnn : 0 ≤ Real.log (Real.sqrt ρ) := Real.log_nonneg (by
        rw [Real.le_sqrt zero_le_one hρ_pos.le]; nlinarith)
      nlinarith [mul_le_mul hsqrt_le h1 hnn (by positivity)]
    obtain ⟨hFR_ne, hFR_lo⟩ := hF_lower R hR
    have hharn := harnack_zero_lower_bound differentiable_F_half F_half_zero_ne_zero
      (r := R ^ 2) (ρ := ρ) (M := M) (by positivity) (by nlinarith)
      (w := ((R ^ 2 : ℝ) : ℂ)) (by rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg R)])
      hFR_ne hFsph hM1 hFM
    have hLHS : (1 / 5) * R * Real.log R - (2 * C_lo + C_up + 1) * R ≤
        ((ρ + R ^ 2) / (ρ - R ^ 2)) * Real.log ‖F_half ((R ^ 2 : ℝ) : ℂ)‖ -
          (2 * R ^ 2 / (ρ - R ^ 2)) * Real.log M := by
      have hden_pos : 0 < ρ - R ^ 2 := by nlinarith
      have hcoef1_ge : (5 : ℝ) / 4 ≤ (ρ + R ^ 2) / (ρ - R ^ 2) := by
        rw [div_le_div_iff₀ (by norm_num) hden_pos]; nlinarith
      have hcoef1_le : (ρ + R ^ 2) / (ρ - R ^ 2) ≤ 2 := by rw [div_le_iff₀ hden_pos]; nlinarith
      have hcoef2_le : 2 * R ^ 2 / (ρ - R ^ 2) ≤ 26 / 100 := by rw [div_le_iff₀ hden_pos]; nlinarith
      have hlogM_eq : Real.log M = (3 * R / 2) * Real.log (3 * R) + C_up * (3 * R) := Real.log_exp _
      have hlog3R : Real.log (3 * R) ≤ Real.log R + 2 := by
        rw [Real.log_mul (by norm_num) hR_pos.ne']
        linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
      have hlogM_le : Real.log M ≤ (3 / 2) * R * Real.log R + (3 + 3 * C_up) * R := by
        rw [hlogM_eq]; nlinarith
      have hlogM_nn : 0 ≤ Real.log M := Real.log_nonneg hM1
      have hlogR_nn : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
      have hterm1 : (5 / 4) * ((R / 2) * Real.log R) - 2 * C_lo * R ≤
          ((ρ + R ^ 2) / (ρ - R ^ 2)) * Real.log ‖F_half ((R ^ 2 : ℝ) : ℂ)‖ := by
        have h1 := mul_le_mul_of_nonneg_left hFR_lo (show 0 ≤ (ρ + R ^ 2) / (ρ - R ^ 2) by positivity)
        nlinarith [mul_le_mul_of_nonneg_right hcoef1_ge (show 0 ≤ (R / 2) * Real.log R by positivity),
          mul_le_mul_of_nonneg_right hcoef1_le (show 0 ≤ C_lo * R by positivity)]
      have hterm2 : (2 * R ^ 2 / (ρ - R ^ 2)) * Real.log M ≤
          (26 / 100) * ((3 / 2) * R * Real.log R + (3 + 3 * C_up) * R) :=
        mul_le_mul hcoef2_le hlogM_le hlogM_nn (by norm_num)
      nlinarith
    obtain ⟨Zρ, hZρ⟩ := exists_zero_finset hzf (Real.sqrt_pos.mpr hρ_pos)
    have hzero_sum_eq : ∑ᶠ u, (MeromorphicOn.divisor F_half (Metric.ball (0 : ℂ) ρ) u : ℝ) * Real.log (ρ / ‖u‖) =
        2 * ∑ g ∈ Zρ, w g * Real.log (Real.sqrt ρ / g) := by
      have hdiv_eq : ∀ u : ℂ, MeromorphicOn.divisor F_half (Metric.ball (0 : ℂ) ρ) u =
          MeromorphicOn.divisor F_half (Metric.closedBall (0 : ℂ) (Real.sqrt ρ ^ 2)) u := by
        intro u
        rw [Real.sq_sqrt hρ_pos.le]
        by_cases hub : u ∈ Metric.ball (0 : ℂ) ρ
        · rw [MeromorphicOn.AnalyticOnNhd.divisor_apply ((F_half_an_closedBall ρ).mono Metric.ball_subset_closedBall) hub,
            MeromorphicOn.AnalyticOnNhd.divisor_apply (F_half_an_closedBall ρ) (Metric.ball_subset_closedBall hub)]
        · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hub]
          by_cases hucb : u ∈ Metric.closedBall (0 : ℂ) ρ
          · have husph : u ∈ Metric.sphere (0 : ℂ) ρ := by
              rw [mem_ball_zero_iff, not_lt] at hub
              rw [mem_closedBall_zero_iff] at hucb
              rw [mem_sphere_zero_iff_norm]; linarith
            rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (F_half_an_closedBall ρ) hucb,
              (F_half_an_closedBall ρ u hucb).analyticOrderAt_eq_zero.mpr (hFsph u husph)]
            simp
          · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hucb]
      simp_rw [hdiv_eq]
      rw [F_half_divisor_weighted_sum hzf (Real.sqrt_pos.mpr hρ_pos) hZρ (fun x ↦ Real.log (ρ / x)),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun g hg ↦ ?_
      have hg0 := ((hZρ g).mp hg).1
      have hlog2 : Real.log (ρ / g ^ 2) = 2 * Real.log (Real.sqrt ρ / g) := by
        rw [show ρ / g ^ 2 = (Real.sqrt ρ / g) ^ 2 by rw [div_pow, Real.sq_sqrt hρ_pos.le], Real.log_pow]
        norm_num
      rw [hlog2]; ring
    have hRHS : ∑ᶠ u, (MeromorphicOn.divisor F_half (Metric.ball (0 : ℂ) ρ) u : ℝ) * Real.log (ρ / ‖u‖) ≤
        2 * (N_small * Real.log (3 * R) + L_small) + 12 * A' * Real.log 2 * S_dyad * R := by
      rw [hzero_sum_eq, ← Finset.sum_filter_add_sum_filter_not Zρ (fun g ↦ 1 ≤ g)]
      have hsmall_bd : ∑ g ∈ Zρ.filter (fun g ↦ ¬ 1 ≤ g), w g * Real.log (Real.sqrt ρ / g) ≤
          N_small * Real.log (3 * R) + L_small := by
        have hsub_sm : Zρ.filter (fun g ↦ ¬ 1 ≤ g) ⊆ Z_small := by
          intro g hg
          obtain ⟨hgZ, hng1⟩ := Finset.mem_filter.mp hg
          push Not at hng1
          exact (hZ_small g).mpr ⟨((hZρ g).mp hgZ).1, hng1.le, ((hZρ g).mp hgZ).2.2⟩
        have hlog3R_nn : 0 ≤ Real.log (3 * R) := Real.log_nonneg (by linarith)
        calc ∑ g ∈ Zρ.filter (fun g ↦ ¬ 1 ≤ g), w g * Real.log (Real.sqrt ρ / g)
            ≤ ∑ g ∈ Zρ.filter (fun g ↦ ¬ 1 ≤ g), (w g * Real.log (3 * R) + w g * |Real.log g|) := by
              refine Finset.sum_le_sum fun g hg ↦ ?_
              have hg0 := ((hZρ g).mp (Finset.mem_filter.mp hg).1).1
              rw [Real.log_div (Real.sqrt_pos.mpr hρ_pos).ne' hg0.ne']
              have h1 := Real.log_le_log (Real.sqrt_pos.mpr hρ_pos) hsqrt_le
              have h2 : -Real.log g ≤ |Real.log g| := neg_le_abs _
              nlinarith [hw_nn g]
          _ ≤ ∑ g ∈ Z_small, (w g * Real.log (3 * R) + w g * |Real.log g|) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub_sm (fun g _ _ ↦ by positivity [hw_nn g])
          _ = N_small * Real.log (3 * R) + L_small := by rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      let K : ℕ := Nat.log 2 ⌈Real.sqrt ρ⌉₊ + 2
      have hbig_bd : ∑ g ∈ Zρ.filter (fun g ↦ 1 ≤ g), w g * Real.log (Real.sqrt ρ / g) ≤
          6 * A' * Real.log 2 * S_dyad * R := by
        let shell (k : ℕ) := Zρ.filter (fun g ↦ 1 ≤ g ∧ Real.sqrt ρ / (2 ^ (k + 1) : ℝ) < g ∧ g ≤ Real.sqrt ρ / (2 ^ k : ℝ))
        have hcover : Zρ.filter (fun g ↦ 1 ≤ g) ⊆ (Finset.range K).biUnion shell := by
          intro g hg
          obtain ⟨hgZ, hg1⟩ := Finset.mem_filter.mp hg
          obtain ⟨hg0, hg_le, _⟩ := (hZρ g).mp hgZ
          rw [Finset.mem_biUnion]
          let q : ℝ := Real.sqrt ρ / g
          have hq1 : 1 ≤ q := (one_le_div hg0).mpr hg_le
          let k : ℕ := Nat.log 2 ⌊q⌋₊
          have hfl_ge1 : 1 ≤ ⌊q⌋₊ := Nat.le_floor (by simpa using hq1)
          have hk_lt : k < K := by
            have hq_le : q ≤ Real.sqrt ρ := div_le_self (Real.sqrt_nonneg _) hg1
            have hfl_le : ⌊q⌋₊ ≤ ⌈Real.sqrt ρ⌉₊ := Nat.floor_le_of_le (hq_le.trans (Nat.le_ceil _))
            have := Nat.log_mono_right (b := 2) hfl_le
            dsimp [k, K]; omega
          have hpow1 : (2 ^ k : ℝ) ≤ q :=
            (show (2 ^ k : ℝ) ≤ (⌊q⌋₊ : ℝ) by exact_mod_cast Nat.pow_log_le_self 2 (by omega)).trans
              (Nat.floor_le (by linarith))
          have hpow2 : q < (2 ^ (k + 1) : ℝ) := by
            have h1 : ⌊q⌋₊ < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) ⌊q⌋₊
            have h2 : (⌊q⌋₊ : ℝ) + 1 ≤ (2 ^ (k + 1) : ℝ) := by exact_mod_cast h1
            linarith [Nat.lt_floor_add_one q]
          refine ⟨k, Finset.mem_range.mpr hk_lt, Finset.mem_filter.mpr ⟨hgZ, hg1, ?_, ?_⟩⟩
          · rw [div_lt_iff₀ (by positivity)]
            have := (div_lt_iff₀ hg0).mp hpow2
            linarith
          · rw [le_div_iff₀ (by positivity)]
            have := (le_div_iff₀ hg0).mp hpow1
            linarith
        have hdisj : Set.PairwiseDisjoint (Finset.range K : Set ℕ) shell := by
          intro k₁ _ k₂ _ hne
          show Disjoint _ _
          rw [Finset.disjoint_left]
          intro g hg1 hg2
          have h1 := (Finset.mem_filter.mp hg1).2
          have h2 := (Finset.mem_filter.mp hg2).2
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have hpow : (2 ^ (k₁ + 1) : ℝ) ≤ (2 ^ k₂ : ℝ) := by
              exact_mod_cast Nat.pow_le_pow_right (by norm_num) (by omega)
            have hdiv : Real.sqrt ρ / (2 ^ k₂ : ℝ) ≤ Real.sqrt ρ / (2 ^ (k₁ + 1) : ℝ) :=
              div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity) hpow
            linarith
          · have hpow : (2 ^ (k₂ + 1) : ℝ) ≤ (2 ^ k₁ : ℝ) := by
              exact_mod_cast Nat.pow_le_pow_right (by norm_num) (by omega)
            have hdiv : Real.sqrt ρ / (2 ^ k₁ : ℝ) ≤ Real.sqrt ρ / (2 ^ (k₂ + 1) : ℝ) :=
              div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity) hpow
            linarith
        calc ∑ g ∈ Zρ.filter (fun g ↦ 1 ≤ g), w g * Real.log (Real.sqrt ρ / g)
            ≤ ∑ g ∈ (Finset.range K).biUnion shell, w g * Real.log (Real.sqrt ρ / g) :=
              Finset.sum_le_sum_of_subset_of_nonneg hcover (fun g hg _ ↦ by
                obtain ⟨k, _, hgk⟩ := Finset.mem_biUnion.mp hg
                have ⟨hg0, hgle, _⟩ := (hZρ g).mp (Finset.mem_filter.mp hgk).1
                exact mul_nonneg (hw_nn g) (Real.log_nonneg ((one_le_div hg0).mpr hgle)))
          _ = ∑ k ∈ Finset.range K, ∑ g ∈ shell k, w g * Real.log (Real.sqrt ρ / g) :=
              Finset.sum_biUnion hdisj
          _ ≤ ∑ k ∈ Finset.range K, (6 * A' * Real.log 2 * R) * (((k + 1 : ℕ) : ℝ) / (2 ^ k : ℝ)) := by
              refine Finset.sum_le_sum fun k _ ↦ ?_
              by_cases hk_ne : (shell k).Nonempty
              · obtain ⟨g₀, hg₀⟩ := hk_ne
                have ht1 : 1 ≤ Real.sqrt ρ / (2 ^ k : ℝ) := by
                  have h := (Finset.mem_filter.mp hg₀).2; linarith
                obtain ⟨Zk, hZk⟩ := exists_zero_finset hzf (by linarith : (0 : ℝ) < Real.sqrt ρ / (2 ^ k : ℝ))
                have hsub_Zk : shell k ⊆ Zk.filter (fun g ↦ 1 ≤ g) := by
                  intro g hg
                  obtain ⟨hgZ, hg1, _, hgle⟩ := Finset.mem_filter.mp hg
                  exact Finset.mem_filter.mpr ⟨(hZk g).mpr ⟨((hZρ g).mp hgZ).1, hgle, ((hZρ g).mp hgZ).2.2⟩, hg1⟩
                have hlog_bd : ∀ g ∈ shell k, Real.log (Real.sqrt ρ / g) ≤ ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
                  intro g hg
                  obtain ⟨hgZ, _, hglt, _⟩ := Finset.mem_filter.mp hg
                  have hg0 := ((hZρ g).mp hgZ).1
                  have hrat : Real.sqrt ρ / g ≤ (2 ^ (k + 1) : ℝ) := by
                    rw [div_le_iff₀ hg0]
                    have := (div_lt_iff₀ (show (0 : ℝ) < 2 ^ (k + 1) by positivity)).mp hglt
                    linarith
                  calc Real.log (Real.sqrt ρ / g) ≤ Real.log ((2 ^ (k + 1) : ℝ)) :=
                        Real.log_le_log (div_pos (Real.sqrt_pos.mpr hρ_pos) hg0) hrat
                    _ = ((k + 1 : ℕ) : ℝ) * Real.log 2 := Real.log_pow 2 (k + 1)
                have hlog2_nn : 0 ≤ ((k + 1 : ℕ) : ℝ) * Real.log 2 :=
                  mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
                calc ∑ g ∈ shell k, w g * Real.log (Real.sqrt ρ / g)
                    ≤ ∑ g ∈ shell k, w g * (((k + 1 : ℕ) : ℝ) * Real.log 2) :=
                      Finset.sum_le_sum fun g hg ↦ mul_le_mul_of_nonneg_left (hlog_bd g hg) (hw_nn g)
                  _ ≤ ∑ g ∈ Zk.filter (fun g ↦ 1 ≤ g), w g * (((k + 1 : ℕ) : ℝ) * Real.log 2) :=
                      Finset.sum_le_sum_of_subset_of_nonneg hsub_Zk (fun g _ _ ↦ mul_nonneg (hw_nn g) hlog2_nn)
                  _ = (∑ g ∈ Zk.filter (fun g ↦ 1 ≤ g), w g) * (((k + 1 : ℕ) : ℝ) * Real.log 2) :=
                      (Finset.sum_mul ..).symm
                  _ ≤ (2 * A' * (Real.sqrt ρ / (2 ^ k : ℝ))) * (((k + 1 : ℕ) : ℝ) * Real.log 2) :=
                      mul_le_mul_of_nonneg_right (hN_lin _ Zk ht1 hZk) hlog2_nn
                  _ ≤ (2 * A' * (3 * R / (2 ^ k : ℝ))) * (((k + 1 : ℕ) : ℝ) * Real.log 2) := by gcongr
                  _ = (6 * A' * Real.log 2 * R) * (((k + 1 : ℕ) : ℝ) / (2 ^ k : ℝ)) := by ring
              · rw [Finset.not_nonempty_iff_eq_empty.mp hk_ne, Finset.sum_empty]
                have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num); positivity
          _ = (6 * A' * Real.log 2 * R) * ∑ k ∈ Finset.range K, ((k + 1 : ℕ) : ℝ) / (2 ^ k : ℝ) :=
              (Finset.mul_sum ..).symm
          _ ≤ (6 * A' * Real.log 2 * R) * S_dyad :=
              mul_le_mul_of_nonneg_left (hsum_k.sum_le_tsum (Finset.range K) (fun k _ ↦ by positivity))
                (by have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num); positivity)
          _ = 6 * A' * Real.log 2 * S_dyad * R := by ring
      linarith
    linarith
  let K₁ : ℝ := 2 * C_lo + C_up + 1 + 12 * A' * Real.log 2 * S_dyad
  let K₂ : ℝ := 2 * N_small
  let K₃ : ℝ := Real.log ‖F_half 0‖ + 2 * L_small
  let R : ℝ := max 10 (Real.exp (5 * (|K₁| + |K₂| + |K₃| + 10)))
  have hR10 : 10 ≤ R := le_max_left _ _
  have hR_pos : 0 < R := by linarith
  have hlogR_ge : 5 * (|K₁| + |K₂| + |K₃| + 10) ≤ Real.log R := by
    rw [← Real.log_exp (5 * (|K₁| + |K₂| + |K₃| + 10))]
    exact Real.log_le_log (Real.exp_pos _) (le_max_right _ _)
  have hhc := hcontra R hR10
  have hlog3R_le : Real.log (3 * R) ≤ R := by
    have h1 : Real.log (3 * R) = Real.log 3 + Real.log R := Real.log_mul (by norm_num) hR_pos.ne'
    have h2 : Real.log 3 ≤ 2 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
    have h4 : Real.log R ≤ R / 2 := by
      have := Real.log_le_sub_one_of_pos (show 0 < R / 2 by positivity)
      rw [Real.log_div hR_pos.ne' (by norm_num)] at this
      linarith [Real.log_two_lt_d9]
    linarith
  have hK₂_nn : 0 ≤ K₂ := by dsimp [K₂, N_small]; exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun g _ ↦ hw_nn g)
  have hK₁_le : K₁ * R ≤ |K₁| * R := mul_le_mul_of_nonneg_right (le_abs_self K₁) hR_pos.le
  have hK₂_le : K₂ * Real.log (3 * R) ≤ |K₂| * R :=
    (mul_le_mul_of_nonneg_left hlog3R_le hK₂_nn).trans (mul_le_mul_of_nonneg_right (le_abs_self K₂) hR_pos.le)
  have hK₃_le : K₃ ≤ |K₃| * R := (le_abs_self K₃).trans (le_mul_of_one_le_right (abs_nonneg K₃) (by linarith))
  nlinarith


/- Section 4: Pillar 3 (Fejér explicit-formula bound) -/

open scoped FourierTransform

/- Part 4A: Fejér kernel and Fourier inversion -/

noncomputable def fejerKernel (T v : ℝ) : ℝ :=
  if v = 0 then T / (2 * Real.pi) else (1 - Real.cos (T * v)) / (Real.pi * T * v ^ 2)

lemma fejerKernel_nonneg {T : ℝ} (hT : 0 < T) (v : ℝ) : 0 ≤ fejerKernel T v := by
  unfold fejerKernel
  split_ifs with hv
  · positivity
  · exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (by positivity)

lemma fejerKernel_even (T v : ℝ) : fejerKernel T (-v) = fejerKernel T v := by
  unfold fejerKernel
  by_cases hv : v = 0
  · simp [hv]
  · simp [hv, Real.cos_neg]

lemma fejerKernel_le_const {T : ℝ} (hT : 0 < T) (v : ℝ) :
    fejerKernel T v ≤ T / (2 * Real.pi) := by
  unfold fejerKernel
  split_ifs with hv
  · exact le_rfl
  · have hsin_sq : 1 - Real.cos (T * v) = 2 * (Real.sin (T * v / 2)) ^ 2 := by
      have h1 := Real.cos_two_mul' (T * v / 2)
      have h2 := Real.sin_sq_add_cos_sq (T * v / 2)
      have h3 : 2 * (T * v / 2) = T * v := by ring
      rw [h3] at h1
      linarith
    have hsin_le : (Real.sin (T * v / 2)) ^ 2 ≤ (T * v / 2) ^ 2 := by
      have h := Real.abs_sin_le_abs (x := T * v / 2)
      nlinarith [sq_abs (Real.sin (T * v / 2)), sq_abs (T * v / 2), abs_nonneg (Real.sin (T * v / 2))]
    have hnum : 1 - Real.cos (T * v) ≤ T ^ 2 * v ^ 2 / 2 := by
      rw [hsin_sq]; nlinarith
    have hden : 0 < Real.pi * T * v ^ 2 := by positivity
    rw [div_le_div_iff₀ hden (by positivity)]
    nlinarith [Real.pi_pos]

lemma fejerKernel_le_inv_sq {T : ℝ} (hT : 0 < T) {v : ℝ} (hv : v ≠ 0) :
    fejerKernel T v ≤ 2 / (Real.pi * T * v ^ 2) := by
  unfold fejerKernel
  rw [if_neg hv]
  exact div_le_div_of_nonneg_right (by linarith [Real.neg_one_le_cos (T * v)]) (by positivity)

lemma measurable_fejerKernel (T : ℝ) : Measurable (fejerKernel T) := by
  unfold fejerKernel
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    ((measurable_const.sub (Real.continuous_cos.measurable.comp (measurable_const.mul measurable_id))).div
      (measurable_const.mul (measurable_id.pow_const 2)))

lemma integrable_fejerKernel {T : ℝ} (hT : 0 < T) : Integrable (fejerKernel T) := by
  let Ck : ℝ := T / Real.pi + 4 / (Real.pi * T)
  have hdom : Integrable (fun v : ℝ ↦ Ck * (1 + v ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul Ck
  refine hdom.mono' (measurable_fejerKernel T).aestronglyMeasurable (Filter.Eventually.of_forall fun v ↦ ?_)
  rw [Real.norm_of_nonneg (fejerKernel_nonneg hT v)]
  have h1v : 0 < 1 + v ^ 2 := by positivity
  by_cases hv : |v| ≤ 1
  · have hv2 : 1 + v ^ 2 ≤ 2 := by
      have : v ^ 2 ≤ 1 := by nlinarith [sq_abs v, abs_nonneg v]
      linarith
    have hinv : (1 : ℝ) / 2 ≤ (1 + v ^ 2)⁻¹ := by
      rw [one_div]; exact (inv_le_inv₀ zero_lt_two h1v).mpr hv2
    calc fejerKernel T v
        ≤ T / (2 * Real.pi) := fejerKernel_le_const hT v
      _ = (T / Real.pi) * (1 / 2) := by ring
      _ ≤ (T / Real.pi) * (1 + v ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ ≤ Ck * (1 + v ^ 2)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          dsimp [Ck]; linarith [show (0 : ℝ) ≤ 4 / (Real.pi * T) by positivity]
  · push Not at hv
    have hvne : v ≠ 0 := by intro h; simp [h] at hv; linarith
    have hv2 : 1 + v ^ 2 ≤ 2 * v ^ 2 := by nlinarith [sq_abs v]
    have hinv : (2 * v ^ 2)⁻¹ ≤ (1 + v ^ 2)⁻¹ :=
      (inv_le_inv₀ (by positivity) h1v).mpr hv2
    calc fejerKernel T v
        ≤ 2 / (Real.pi * T * v ^ 2) := fejerKernel_le_inv_sq hT hvne
      _ = (4 / (Real.pi * T)) * (2 * v ^ 2)⁻¹ := by field_simp; ring
      _ ≤ (4 / (Real.pi * T)) * (1 + v ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ ≤ Ck * (1 + v ^ 2)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          dsimp [Ck]; linarith [show (0 : ℝ) ≤ T / Real.pi by positivity]

lemma integral_tent_cos_eq {T : ℝ} (hT : 0 < T) (v : ℝ) :
    ∫ t in (0 : ℝ)..T, (1 - t / T) * Real.cos (t * v) = Real.pi * fejerKernel T v := by
  by_cases hv : v = 0
  · subst hv
    simp only [mul_zero, Real.cos_zero, mul_one, fejerKernel, ↓reduceIte]
    have hder : ∀ t ∈ Set.uIcc (0 : ℝ) T,
        HasDerivAt (fun x : ℝ ↦ x - x ^ 2 / (2 * T)) (1 - t / T) t := by
      intro t _
      have h1 : HasDerivAt (fun x : ℝ ↦ x) 1 t := hasDerivAt_id t
      have h2 : HasDerivAt (fun x : ℝ ↦ x ^ 2 / (2 * T)) (2 * t / (2 * T)) t := by
        simpa using (hasDerivAt_pow 2 t).div_const (2 * T)
      have hsub := h1.fun_sub h2
      have hTne : T ≠ 0 := hT.ne'
      have heq : (1 : ℝ) - 2 * t / (2 * T) = 1 - t / T := by field_simp
      rwa [heq] at hsub
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder
      (Continuous.intervalIntegrable (by fun_prop) 0 T)]
    have hTne : T ≠ 0 := hT.ne'
    field_simp
    ring
  · unfold fejerKernel
    rw [if_neg hv]
    let G : ℝ → ℝ := fun x ↦ (1 - x / T) * Real.sin (x * v) / v - Real.cos (x * v) / (T * v ^ 2)
    have hder : ∀ t ∈ Set.uIcc (0 : ℝ) T, HasDerivAt G ((1 - t / T) * Real.cos (t * v)) t := by
      intro t _
      have h1 : HasDerivAt (fun x : ℝ ↦ 1 - x / T) (-(1 / T)) t := by
        have h := (hasDerivAt_const t (1 : ℝ)).fun_sub ((hasDerivAt_id t).div_const T)
        simpa using h
      have h2 : HasDerivAt (fun x : ℝ ↦ Real.sin (x * v)) (Real.cos (t * v) * v) t := by
        have hm : HasDerivAt (fun x : ℝ ↦ x * v) v t := by simpa using (hasDerivAt_id t).mul_const v
        exact (Real.hasDerivAt_sin (t * v)).comp t hm
      have h3 : HasDerivAt (fun x : ℝ ↦ Real.cos (x * v)) (-Real.sin (t * v) * v) t := by
        have hm : HasDerivAt (fun x : ℝ ↦ x * v) v t := by simpa using (hasDerivAt_id t).mul_const v
        exact (Real.hasDerivAt_cos (t * v)).comp t hm
      have hprod := ((h1.fun_mul h2).div_const v).fun_sub (h3.div_const (T * v ^ 2))
      have hTne : T ≠ 0 := hT.ne'
      have heq : (-(1 / T) * Real.sin (t * v) + (1 - t / T) * (Real.cos (t * v) * v)) / v -
          -Real.sin (t * v) * v / (T * v ^ 2) = (1 - t / T) * Real.cos (t * v) := by
        field_simp
        ring
      rwa [heq] at hprod
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder
      (Continuous.intervalIntegrable (by fun_prop) 0 T)]
    dsimp [G]
    have hTT : 1 - T / T = 0 := by rw [div_self hT.ne', sub_self]
    rw [hTT]
    simp only [zero_mul, zero_div, zero_sub, Real.sin_zero, Real.cos_zero]
    have hTne : T ≠ 0 := hT.ne'
    field_simp
    ring

lemma integral_tent_exp_eq_fejerKernel {T : ℝ} (hT : 0 < T) (v : ℝ) :
    (1 / (2 * (Real.pi : ℂ))) *
      ∫ t in (-T)..T, ((1 - |t| / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * (v : ℂ) * Complex.I) =
      (fejerKernel T v : ℂ) := by
  have hint_neg : IntervalIntegrable
      (fun t : ℝ ↦ ((1 - |t| / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * (v : ℂ) * Complex.I))
      volume (-T) 0 := Continuous.intervalIntegrable (by fun_prop) (-T) 0
  have hint_pos : IntervalIntegrable
      (fun t : ℝ ↦ ((1 - |t| / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * (v : ℂ) * Complex.I))
      volume 0 T := Continuous.intervalIntegrable (by fun_prop) 0 T
  rw [← intervalIntegral.integral_add_adjacent_intervals hint_neg hint_pos]
  have hneg_eq :
      ∫ t in (-T)..0, ((1 - |t| / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * (v : ℂ) * Complex.I) =
        ∫ t in (0 : ℝ)..T, ((1 - |t| / T : ℝ) : ℂ) * Complex.exp (-(t : ℂ) * (v : ℂ) * Complex.I) := by
    have hcomp := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := T)
      (fun t : ℝ ↦ ((1 - |t| / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * (v : ℂ) * Complex.I))
    simp only [neg_zero, abs_neg, Complex.ofReal_neg, neg_mul] at hcomp
    convert hcomp.symm using 2
    ext t
    ring_nf
  rw [hneg_eq, ← intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 T) hint_pos]
  have hcongr :
      ∫ t in (0 : ℝ)..T,
        (((1 - |t| / T : ℝ) : ℂ) * Complex.exp (-(t : ℂ) * (v : ℂ) * Complex.I) +
          ((1 - |t| / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * (v : ℂ) * Complex.I)) =
      (2 : ℂ) * (((∫ t in (0 : ℝ)..T, (1 - t / T) * Real.cos (t * v)) : ℝ) : ℂ) := by
    have h1 : ∀ t ∈ Set.uIcc (0 : ℝ) T,
        ((1 - |t| / T : ℝ) : ℂ) * Complex.exp (-(t : ℂ) * (v : ℂ) * Complex.I) +
          ((1 - |t| / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * (v : ℂ) * Complex.I) =
        (2 : ℂ) * (((1 - t / T) * Real.cos (t * v) : ℝ) : ℂ) := by
      intro t ht
      rw [Set.uIcc_of_le hT.le] at ht
      rw [abs_of_nonneg ht.1]
      have hcos : Complex.exp (-(t : ℂ) * (v : ℂ) * Complex.I) +
          Complex.exp ((t : ℂ) * (v : ℂ) * Complex.I) = 2 * (Real.cos (t * v) : ℂ) := by
        have ha : (t : ℂ) * (v : ℂ) * Complex.I = ((t * v : ℝ) : ℂ) * Complex.I := by push_cast; ring
        have hb : -(t : ℂ) * (v : ℂ) * Complex.I = ((-(t * v) : ℝ) : ℂ) * Complex.I := by push_cast; ring
        rw [ha, hb, Complex.exp_mul_I, Complex.exp_mul_I, Complex.ofReal_neg,
          Complex.cos_neg, Complex.sin_neg, Complex.ofReal_cos]
        ring
      rw [Complex.ofReal_mul]
      linear_combination ((1 - t / T : ℝ) : ℂ) * hcos
    rw [intervalIntegral.integral_congr h1, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_ofReal]
  rw [hcongr, integral_tent_cos_eq hT v]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

lemma integral_fejerKernel_exp_eq_tent {T : ℝ} (hT : 0 < T) (γ : ℝ) :
    ∫ v : ℝ, Complex.exp ((γ : ℂ) * (v : ℂ) * Complex.I) * (fejerKernel T v : ℂ) =
      ((max (1 - |γ| / T) 0 : ℝ) : ℂ) := by
  let tentFn : ℝ → ℂ := fun w ↦ ((max (1 - |2 * Real.pi * w| / T) 0 : ℝ) : ℂ)
  have htent_cont : Continuous tentFn := by dsimp [tentFn]; fun_prop
  have htent_supp : HasCompactSupport tentFn := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -T / (2 * Real.pi)) (b := T / (2 * Real.pi)))
    intro w hw
    rw [Function.mem_support] at hw
    have hpos : 0 < 1 - |2 * Real.pi * w| / T := by
      by_contra hle
      push Not at hle
      apply hw
      dsimp [tentFn]
      rw [max_eq_right hle, Complex.ofReal_zero]
    have habs : |2 * Real.pi * w| < T := by
      have : |2 * Real.pi * w| / T < 1 := by linarith
      exact (div_lt_one hT).mp this
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)] at habs
    have hw_abs : |w| < T / (2 * Real.pi) := by
      rw [lt_div_iff₀ (by positivity : 0 < 2 * Real.pi)]
      linarith
    rw [neg_div]
    exact ⟨by linarith [(abs_lt.mp hw_abs).1], by linarith [(abs_lt.mp hw_abs).2]⟩
  have htent_int : Integrable tentFn := htent_cont.integrable_of_hasCompactSupport htent_supp
  have hF_eq : 𝓕 tentFn = fun v : ℝ ↦ (fejerKernel T v : ℂ) := by
    ext v
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp only [smul_eq_mul]
    have hscale :
        ∫ w : ℝ, Complex.exp (↑(-2 * Real.pi * w * v) * Complex.I) * tentFn w =
          (2 * Real.pi)⁻¹ •
            ∫ t : ℝ, Complex.exp (↑(-t * v) * Complex.I) * ((max (1 - |t| / T) 0 : ℝ) : ℂ) := by
      have h := Measure.integral_comp_mul_left
        (fun t : ℝ ↦ Complex.exp (↑(-t * v) * Complex.I) * ((max (1 - |t| / T) 0 : ℝ) : ℂ))
        (2 * Real.pi)
      rw [abs_of_pos (inv_pos.mpr (by positivity : 0 < 2 * Real.pi))] at h
      convert h using 2
      ext w
      dsimp [tentFn]
      congr 1
      push_cast
      ring_nf
    rw [hscale, Complex.real_smul]
    have hzero : ∀ t : ℝ, t ∉ Set.Ioc (-T) T →
        Complex.exp (↑(-t * v) * Complex.I) * ((max (1 - |t| / T) 0 : ℝ) : ℂ) = 0 := by
      intro t ht
      have habs : T ≤ |t| := by
        by_contra hlt
        push Not at hlt
        exact ht ⟨(abs_lt.mp hlt).1, (abs_lt.mp hlt).2.le⟩
      have hle : 1 - |t| / T ≤ 0 := by
        have : 1 ≤ |t| / T := (one_le_div hT).mpr habs
        linarith
      rw [max_eq_right hle, Complex.ofReal_zero, mul_zero]
    have hind : ∫ t : ℝ, Complex.exp (↑(-t * v) * Complex.I) * ((max (1 - |t| / T) 0 : ℝ) : ℂ) =
        ∫ t in Set.Ioc (-T) T,
          Complex.exp (↑(-t * v) * Complex.I) * ((max (1 - |t| / T) 0 : ℝ) : ℂ) := by
      rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
      congr 1
      ext t
      by_cases ht : t ∈ Set.Ioc (-T) T
      · simp only [Set.indicator_of_mem ht]
      · simp only [Set.indicator_of_notMem ht]
        exact hzero t ht
    rw [hind, ← intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
    have hcongr :
        ∫ t in (-T)..T, Complex.exp (↑(-t * v) * Complex.I) * ((max (1 - |t| / T) 0 : ℝ) : ℂ) =
        ∫ t in (-T)..T, ((1 - |t| / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * ((-v : ℝ) : ℂ) * Complex.I) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by linarith : -T ≤ T)] at ht
      have habs : |t| ≤ T := abs_le.mpr ⟨ht.1, ht.2⟩
      have hnn : 0 ≤ 1 - |t| / T := sub_nonneg.mpr ((div_le_one hT).mpr habs)
      dsimp only
      rw [max_eq_left hnn, mul_comm]
      congr 1
      push_cast
      ring_nf
    rw [hcongr]
    have hfe := integral_tent_exp_eq_fejerKernel hT (-v)
    rw [fejerKernel_even] at hfe
    convert hfe using 1
    push_cast
    ring
  have hF_int : Integrable (𝓕 tentFn) := by
    rw [hF_eq]
    exact (integrable_fejerKernel hT).ofReal
  have hinv := congr_fun (htent_cont.fourierInv_fourier_eq htent_int hF_int) (γ / (2 * Real.pi))
  rw [hF_eq, Real.fourierInv_eq'] at hinv
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have harg : 2 * Real.pi * (γ / (2 * Real.pi)) = γ := mul_div_cancel₀ γ hpi
  convert hinv using 1
  · congr 1
    ext v
    simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial]
    congr 2
    have hmul : 2 * Real.pi * (γ / (2 * Real.pi) * v) = γ * v := by field_simp
    rw [hmul]
    push_cast
    ring
  · dsimp [tentFn]
    rw [harg]

lemma integral_fejerKernel_eq_one {T : ℝ} (hT : 0 < T) :
    ∫ v : ℝ, fejerKernel T v = 1 := by
  have h := integral_fejerKernel_exp_eq_tent hT 0
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, abs_zero, zero_div,
    sub_zero, max_eq_left zero_le_one, Complex.ofReal_one] at h
  have hre := congr_arg Complex.re h
  have hc := Complex.ofRealCLM.integral_comp_comm (integrable_fejerKernel hT)
  change (∫ v : ℝ, Complex.ofRealCLM (fejerKernel T v)).re = (1 : ℂ).re at hre
  rw [hc] at hre
  simpa using hre

lemma fejerKernel_tail_le {T : ℝ} (hT : 0 < T) {x : ℝ} (hx : 0 < x) :
    ∫ v in Set.Ici x, fejerKernel T v ≤ 2 / (Real.pi * T * x) := by
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  have hint_rpow : IntegrableOn (fun v : ℝ ↦ (2 / (Real.pi * T)) * v ^ (-2 : ℝ)) (Set.Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hx).const_mul (2 / (Real.pi * T))
  have hle : ∫ v in Set.Ioi x, fejerKernel T v ≤
      ∫ v in Set.Ioi x, (2 / (Real.pi * T)) * v ^ (-2 : ℝ) := by
    apply MeasureTheory.setIntegral_mono_on (integrable_fejerKernel hT).integrableOn hint_rpow
      measurableSet_Ioi
    intro v hv
    have hvpos : 0 < v := hx.trans hv
    calc fejerKernel T v
        ≤ 2 / (Real.pi * T * v ^ 2) := fejerKernel_le_inv_sq hT hvpos.ne'
      _ = (2 / (Real.pi * T)) * v ^ (-2 : ℝ) := by
          rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hvpos.le,
            Real.rpow_natCast]
          ring
  refine hle.trans (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hx]
  have hx1 : x ^ ((-2 : ℝ) + 1) = x⁻¹ := by
    rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  rw [hx1]
  field_simp
  ring

/- Part 4B: Mellin differentiation & Laplace transform in `u` -/

noncomputable def g_u (u : ℝ) : ℝ :=
  u * J_sum ⌊Real.exp u⌋₊ * Real.exp (-u / 2)

lemma measurable_g_u : Measurable g_u := by
  unfold g_u
  have hJ : Measurable (fun u : ℝ ↦ J_sum ⌊Real.exp u⌋₊) :=
    (Measurable.of_discrete (f := J_sum)).comp
      (Nat.measurable_floor.comp Real.continuous_exp.measurable)
  exact (measurable_id.mul hJ).mul
    (Real.continuous_exp.measurable.comp (measurable_id.neg.div_const 2))

lemma measurable_J_sum_floor : Measurable (fun t : ℝ ↦ (J_sum ⌊t⌋₊ : ℂ)) :=
  Complex.continuous_ofReal.measurable.comp
    ((Measurable.of_discrete (f := J_sum)).comp Nat.measurable_floor)

lemma integrableOn_mellin_log_J
    (hℓ_int : ∀ s : ℂ, 1 / 2 < s.re →
      IntegrableOn (fun t : ℝ ↦ (J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1))
    {s : ℂ} (hs : 1 / 2 < s.re) :
    IntegrableOn (fun t : ℝ ↦ (Real.log t : ℂ) * (J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)))
      (Set.Ioi 1) := by
  let δ : ℝ := (s.re - 1 / 2) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let σ' : ℝ := s.re - δ
  have hσ' : 1 / 2 < σ' := by dsimp [σ', δ]; linarith
  obtain ⟨B, hBpos, hB⟩ := exists_bound_log_pow_mul_rpow_neg 1 hδ
  have hint' := (hℓ_int (σ' : ℂ) (by simpa using hσ')).norm.const_mul B
  refine hint'.mono' ?_ ?_
  · have hm1 : AEStronglyMeasurable (fun t : ℝ ↦ (Real.log t : ℂ) * (J_sum ⌊t⌋₊ : ℂ))
        (volume.restrict (Set.Ioi 1)) :=
      ((Complex.continuous_ofReal.measurable.comp Real.measurable_log).mul
        measurable_J_sum_floor).aestronglyMeasurable
    exact hm1.mul (aestronglyMeasurable_ofReal_cpow_Ioi (-(s + 1)))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hlog_nn : 0 ≤ Real.log t := Real.log_nonneg ht.le
    have hnorm_s : ‖(t : ℂ) ^ (-(s + 1))‖ = t ^ (-(s.re + 1)) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]; simp
    have hnorm_σ' : ‖(t : ℂ) ^ (-((σ' : ℂ) + 1))‖ = t ^ (-(σ' + 1)) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]; simp
    have hlogB : Real.log t * t ^ (-δ) ≤ B := by
      simpa [pow_one] using hB t ht.le
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hlog_nn,
      hnorm_s, hnorm_σ']
    have hrpow : t ^ (-(s.re + 1)) = t ^ (-δ) * t ^ (-(σ' + 1)) := by
      rw [← Real.rpow_add ht0]
      congr 1; dsimp [σ']; ring
    rw [hrpow]
    have : Real.log t * ‖(J_sum ⌊t⌋₊ : ℂ)‖ * (t ^ (-δ) * t ^ (-(σ' + 1))) =
        (Real.log t * t ^ (-δ)) * (‖(J_sum ⌊t⌋₊ : ℂ)‖ * t ^ (-(σ' + 1))) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hlogB (by positivity)

lemma deriv_ℓ_eq
    (hzf : ∀ s : ℂ, 1 / 2 < s.re → L₄ s ≠ 0)
    (ℓ : ℂ → ℂ)
    (hℓ_diff : DifferentiableOn ℂ ℓ {s : ℂ | 1 / 2 < s.re})
    (hℓ_exp : ∀ s : ℂ, 1 / 2 < s.re → Complex.exp (ℓ s) = L₄ s)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    deriv ℓ s = deriv L₄ s / L₄ s := by
  have hopen : IsOpen {z : ℂ | 1 / 2 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hnhds : {z : ℂ | 1 / 2 < z.re} ∈ 𝓝 s := hopen.mem_nhds hs
  have hdℓ : HasDerivAt ℓ (deriv ℓ s) s := (hℓ_diff.differentiableAt hnhds).hasDerivAt
  have hdexp : HasDerivAt (fun z ↦ Complex.exp (ℓ z)) (Complex.exp (ℓ s) * deriv ℓ s) s :=
    (Complex.hasDerivAt_exp (ℓ s)).comp s hdℓ
  have heq : (fun z ↦ Complex.exp (ℓ z)) =ᶠ[𝓝 s] L₄ := by
    filter_upwards [hnhds] with z hz
    exact hℓ_exp z hz
  have hdL : HasDerivAt (fun z ↦ Complex.exp (ℓ z)) (deriv L₄ s) s :=
    (differentiable_L₄ s).hasDerivAt.congr_of_eventuallyEq heq
  have huniq : Complex.exp (ℓ s) * deriv ℓ s = deriv L₄ s := hdexp.unique hdL
  rw [hℓ_exp s hs] at huniq
  exact eq_div_of_mul_eq (hzf s hs) (by rw [mul_comm]; exact huniq)

lemma phi_eq_mellin_log
    (hzf : ∀ s : ℂ, 1 / 2 < s.re → L₄ s ≠ 0)
    (ℓ : ℂ → ℂ)
    (hℓ_diff : DifferentiableOn ℂ ℓ {s : ℂ | 1 / 2 < s.re})
    (hℓ_exp : ∀ s : ℂ, 1 / 2 < s.re → Complex.exp (ℓ s) = L₄ s)
    (hℓ_int : ∀ s : ℂ, 1 / 2 < s.re →
      IntegrableOn (fun t : ℝ ↦ (J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1))
    (hℓ_eq : ∀ s : ℂ, 1 / 2 < s.re →
      ℓ s / s = ∫ t : ℝ in Set.Ioi (1 : ℝ), (J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)))
    {s : ℂ} (hs : 1 / 2 < s.re) :
    -(deriv L₄ s / L₄ s) / s + ℓ s / s ^ 2 =
      ∫ t : ℝ in Set.Ioi (1 : ℝ), (Real.log t : ℂ) * (J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  have hopen : IsOpen {z : ℂ | 1 / 2 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hnhds : {z : ℂ | 1 / 2 < z.re} ∈ 𝓝 s := hopen.mem_nhds hs
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  -- Derivative of LHS `z ↦ ℓ z / z` at `s`
  have hd_lhs : HasDerivAt (fun z ↦ ℓ z / z) ((deriv ℓ s) / s - ℓ s / s ^ 2) s := by
    have hdℓ := (hℓ_diff.differentiableAt hnhds).hasDerivAt
    have hdiv := hdℓ.fun_div (hasDerivAt_id s) hs0
    simp only [id_eq] at hdiv
    have heq : (deriv ℓ s * s - ℓ s * 1) / s ^ 2 = deriv ℓ s / s - ℓ s / s ^ 2 := by
      field_simp
    rwa [heq] at hdiv
  -- Derivative of RHS `z ↦ ∫ t in Ioi 1, J_sum ⌊t⌋₊ * t ^ (-(z + 1))` at `s`
  let r : ℝ := (s.re - 1 / 2) / 2
  have hr : 0 < r := by dsimp [r]; linarith
  let σ₀ : ℝ := s.re - r
  have hσ₀ : 1 / 2 < σ₀ := by dsimp [σ₀, r]; linarith
  have hd_rhs :
      HasDerivAt
        (fun z : ℂ ↦ ∫ t : ℝ in Set.Ioi (1 : ℝ), (J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(z + 1)))
        (∫ t : ℝ in Set.Ioi (1 : ℝ), -((Real.log t : ℂ) * (J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)))) s := by
    have hball_mem : Metric.ball s r ∈ 𝓝 s := Metric.ball_mem_nhds s hr
    have hF_meas : ∀ᶠ z in 𝓝 s, AEStronglyMeasurable
        (fun t : ℝ ↦ (J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(z + 1))) (volume.restrict (Set.Ioi 1)) :=
      Filter.Eventually.of_forall fun z ↦
        measurable_J_sum_floor.aestronglyMeasurable.mul
          (aestronglyMeasurable_ofReal_cpow_Ioi (-(z + 1)))
    have hF_int : IntegrableOn (fun t : ℝ ↦ (J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1) :=
      hℓ_int s hs
    have hF'_meas : AEStronglyMeasurable
        (fun t : ℝ ↦ -((Real.log t : ℂ) * (J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))))
        (volume.restrict (Set.Ioi 1)) :=
      (((Complex.continuous_ofReal.measurable.comp Real.measurable_log).mul
        measurable_J_sum_floor).aestronglyMeasurable.mul
          (aestronglyMeasurable_ofReal_cpow_Ioi (-(s + 1)))).neg
    have hbound_int : IntegrableOn
        (fun t : ℝ ↦ ‖(Real.log t : ℂ) * (J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-((σ₀ : ℂ) + 1))‖)
        (Set.Ioi 1) := (integrableOn_mellin_log_J hℓ_int (by simpa using hσ₀)).norm
    have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioi (1 : ℝ))), ∀ z ∈ Metric.ball s r,
        ‖-((Real.log t : ℂ) * (J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(z + 1)))‖ ≤
          ‖(Real.log t : ℂ) * (J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-((σ₀ : ℂ) + 1))‖ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
      have ht0 : 0 < t := zero_lt_one.trans ht
      have hre_ge : σ₀ ≤ z.re := by
        have hdist : |z.re - s.re| < r :=
          lt_of_le_of_lt (Complex.abs_re_le_norm (z - s)) (by simpa [Metric.mem_ball, dist_eq_norm] using hz)
        dsimp [σ₀]; linarith [(abs_lt.mp hdist).1]
      rw [norm_neg, norm_mul, norm_mul, norm_mul, norm_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      simp only [Complex.neg_re, Complex.add_re, Complex.one_re, Complex.ofReal_re]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le ht.le (by linarith)) (by positivity)
    have hdiff : ∀ᵐ (t : ℝ) ∂(volume.restrict (Set.Ioi (1 : ℝ))), ∀ z ∈ Metric.ball s r,
        HasDerivAt (fun w : ℂ ↦ (J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(w + 1)))
          (-((Real.log t : ℂ) * (J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(z + 1)))) z := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z _
      have ht0 : 0 < t := zero_lt_one.trans ht
      have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
      have hpow : HasDerivAt (fun w : ℂ ↦ (t : ℂ) ^ (-(w + 1)))
          ((t : ℂ) ^ (-(z + 1)) * Complex.log (t : ℂ) * (-1)) z := by
        have h1 : HasDerivAt (fun w : ℂ ↦ -(w + 1)) (-1 : ℂ) z := by
          simpa using ((hasDerivAt_id z).fun_add (hasDerivAt_const z (1 : ℂ))).fun_neg
        exact h1.const_cpow (Or.inl ht_ne)
      have hmul := hpow.const_mul (J_sum ⌊t⌋₊ : ℂ)
      have heq : (J_sum ⌊t⌋₊ : ℂ) * ((t : ℂ) ^ (-(z + 1)) * Complex.log (t : ℂ) * (-1)) =
          -((Real.log t : ℂ) * (J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(z + 1))) := by
        rw [← Complex.ofReal_log ht0.le]
        ring
      rwa [heq] at hmul
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ) hball_mem hF_meas hF_int
      hF'_meas hbound hbound_int hdiff).2
  have heq_nhds : (fun z : ℂ ↦ ℓ z / z) =ᶠ[𝓝 s]
      fun z : ℂ ↦ ∫ t : ℝ in Set.Ioi (1 : ℝ), (J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(z + 1)) := by
    filter_upwards [hnhds] with z hz
    exact hℓ_eq z hz
  have huniq := (hd_lhs.congr_of_eventuallyEq heq_nhds.symm).unique hd_rhs
  rw [MeasureTheory.integral_neg, deriv_ℓ_eq hzf ℓ hℓ_diff hℓ_exp hs] at huniq
  have hneg := congr_arg Neg.neg huniq
  simpa [sub_eq_add_neg, neg_add, neg_neg, add_comm, neg_div] using hneg

lemma real_exp_image_Ioi_zero : Real.exp '' Set.Ioi (0 : ℝ) = Set.Ioi (1 : ℝ) := by
  ext t
  simp only [Set.mem_image, Set.mem_Ioi]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact Real.one_lt_exp_iff.mpr hu
  · intro ht
    exact ⟨Real.log t, Real.log_pos ht, Real.exp_log (zero_lt_one.trans ht)⟩

lemma integrableOn_g_u_exp
    (hℓ_int : ∀ s : ℂ, 1 / 2 < s.re →
      IntegrableOn (fun t : ℝ ↦ (J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1))
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    IntegrableOn
      (fun u : ℝ ↦ (g_u u : ℂ) * Complex.exp (-((ε : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ)))
      (Set.Ioi 0) := by
  let s : ℂ := 1 / 2 + (ε : ℂ) + (t : ℂ) * Complex.I
  have hs : 1 / 2 < s.re := by simp [s]; linarith
  have hint_t := integrableOn_mellin_log_J hℓ_int hs
  rw [← real_exp_image_Ioi_zero] at hint_t
  rw [MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun u _ ↦ (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn] at hint_t
  refine hint_t.congr_fun (fun u _ ↦ ?_) measurableSet_Ioi
  dsimp only
  rw [abs_of_pos (Real.exp_pos u), Complex.real_smul, Real.log_exp]
  have hexp_cpow : ((Real.exp u : ℝ) : ℂ) ^ (-(s + 1)) = Complex.exp (-(s + 1) * (u : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos u).ne'),
      ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]
    ring_nf
  rw [hexp_cpow]
  dsimp [g_u, s]
  push_cast
  have hcomb : Complex.exp (u : ℂ) * Complex.exp (-(1 / 2 + (ε : ℂ) + (t : ℂ) * Complex.I + 1) * (u : ℂ)) =
      Complex.exp (-(u : ℂ) / 2) * Complex.exp (-((ε : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  linear_combination (u : ℂ) * (J_sum ⌊Real.exp u⌋₊ : ℂ) * hcomb

lemma phi_eq_laplace_g_u
    (hzf : ∀ s : ℂ, 1 / 2 < s.re → L₄ s ≠ 0)
    (ℓ : ℂ → ℂ)
    (hℓ_diff : DifferentiableOn ℂ ℓ {s : ℂ | 1 / 2 < s.re})
    (hℓ_exp : ∀ s : ℂ, 1 / 2 < s.re → Complex.exp (ℓ s) = L₄ s)
    (hℓ_int : ∀ s : ℂ, 1 / 2 < s.re →
      IntegrableOn (fun t : ℝ ↦ (J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1))
    (hℓ_eq : ∀ s : ℂ, 1 / 2 < s.re →
      ℓ s / s = ∫ t : ℝ in Set.Ioi (1 : ℝ), (J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)))
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    let s : ℂ := 1 / 2 + (ε : ℂ) + (t : ℂ) * Complex.I;
    -(deriv L₄ s / L₄ s) / s + ℓ s / s ^ 2 =
      ∫ u in Set.Ioi 0, (g_u u : ℂ) * Complex.exp (-((ε : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ)) := by
  intro s
  have hs : 1 / 2 < s.re := by simp [s]; linarith
  rw [phi_eq_mellin_log hzf ℓ hℓ_diff hℓ_exp hℓ_int hℓ_eq hs, ← real_exp_image_Ioi_zero,
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun u _ ↦ (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_
  rw [abs_of_pos (Real.exp_pos u), Complex.real_smul, Real.log_exp]
  have hexp_cpow : ((Real.exp u : ℝ) : ℂ) ^ (-(s + 1)) = Complex.exp (-(s + 1) * (u : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos u).ne'),
      ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]
    ring_nf
  rw [hexp_cpow]
  dsimp [g_u, s]
  push_cast
  have hcomb : Complex.exp (u : ℂ) * Complex.exp (-(1 / 2 + (ε : ℂ) + (t : ℂ) * Complex.I + 1) * (u : ℂ)) =
      Complex.exp (-(u : ℂ) / 2) * Complex.exp (-((ε : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  linear_combination (u : ℂ) * (J_sum ⌊Real.exp u⌋₊ : ℂ) * hcomb

/- Part 4C: Fubini identity and uniform time-side lower bound -/

lemma fubini_fejer_phi
    (hzf : ∀ s : ℂ, 1 / 2 < s.re → L₄ s ≠ 0)
    (ℓ : ℂ → ℂ)
    (hℓ_diff : DifferentiableOn ℂ ℓ {s : ℂ | 1 / 2 < s.re})
    (hℓ_exp : ∀ s : ℂ, 1 / 2 < s.re → Complex.exp (ℓ s) = L₄ s)
    (hℓ_int : ∀ s : ℂ, 1 / 2 < s.re →
      IntegrableOn (fun t : ℝ ↦ (J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1))
    (hℓ_eq : ∀ s : ℂ, 1 / 2 < s.re →
      ℓ s / s = ∫ t : ℝ in Set.Ioi (1 : ℝ), (J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)))
    {T : ℝ} (hT : 0 < T) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    (1 / (2 * (Real.pi : ℂ))) *
      ∫ t in (-T)..T,
        (let s : ℂ := 1 / 2 + (ε : ℂ) + (t : ℂ) * Complex.I;
        ((1 - |t| / T : ℝ) : ℂ) * (-(deriv L₄ s / L₄ s) / s + ℓ s / s ^ 2) *
          Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) =
      ∫ u in Set.Ioi 0,
        (g_u u : ℂ) * (Real.exp (-ε * u) : ℂ) * (fejerKernel T (x - u) : ℂ) := by
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  -- Replace Φ(s) with Laplace integral of g_u
  have hsub :
      ∫ t in Set.Ioc (-T) T,
        (let s : ℂ := 1 / 2 + (ε : ℂ) + (t : ℂ) * Complex.I;
        ((1 - |t| / T : ℝ) : ℂ) * (-(deriv L₄ s / L₄ s) / s + ℓ s / s ^ 2) *
          Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) =
      ∫ t in Set.Ioc (-T) T, ∫ u in Set.Ioi 0,
        ((1 - |t| / T : ℝ) : ℂ) * (g_u u : ℂ) * (Real.exp (-ε * u) : ℂ) *
          Complex.exp ((t : ℂ) * ((x - u : ℝ) : ℂ) * Complex.I) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t _ ↦ ?_
    dsimp only
    rw [phi_eq_laplace_g_u hzf ℓ hℓ_diff hℓ_exp hℓ_int hℓ_eq hε t]
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_mul_const]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_
    have hexp : Complex.exp (-((ε : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ)) *
        Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) =
        (Real.exp (-ε * u) : ℂ) * Complex.exp ((t : ℂ) * ((x - u : ℝ) : ℂ) * Complex.I) := by
      rw [show (Real.exp (-ε * u) : ℂ) = Complex.exp (-(ε : ℂ) * (u : ℂ)) by
        rw [Complex.ofReal_exp]; congr 1; push_cast; ring]
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1; push_cast; ring
    linear_combination ((1 - |t| / T : ℝ) : ℂ) * (g_u u : ℂ) * hexp
  rw [hsub]
  -- Check joint integrability on Ioc (-T) T ×ˢ Ioi 0
  have hint_u : IntegrableOn (fun u : ℝ ↦ |g_u u| * Real.exp (-ε * u)) (Set.Ioi (0 : ℝ)) := by
    have h : IntegrableOn
        (fun u : ℝ ↦ ‖(g_u u : ℂ) * Complex.exp (-((ε : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) * (u : ℂ))‖)
        (Set.Ioi (0 : ℝ)) := (integrableOn_g_u_exp hℓ_int hε 0).norm
    refine h.congr_fun (fun u _ ↦ ?_) measurableSet_Ioi
    dsimp only
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    simp [mul_comm]
  have hint_t : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Set.Ioc (-T) T) :=
    integrableOn_const (by simp)
  have hprod_bound : Integrable (fun p : ℝ × ℝ ↦ (1 : ℝ) * (|g_u p.2| * Real.exp (-ε * p.2)))
      ((volume.restrict (Set.Ioc (-T) T)).prod (volume.restrict (Set.Ioi (0 : ℝ)))) :=
    Integrable.mul_prod hint_t hint_u
  have hjoint_meas : Measurable (fun p : ℝ × ℝ ↦
      ((1 - |p.1| / T : ℝ) : ℂ) * (g_u p.2 : ℂ) * (Real.exp (-ε * p.2) : ℂ) *
        Complex.exp ((p.1 : ℂ) * ((x - p.2 : ℝ) : ℂ) * Complex.I)) := by
    have hm1 : Measurable (fun p : ℝ × ℝ ↦ ((1 - |p.1| / T : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp
        (measurable_const.sub ((continuous_abs.measurable.comp measurable_fst).div_const T))
    have hm2 : Measurable (fun p : ℝ × ℝ ↦ (g_u p.2 : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp (measurable_g_u.comp measurable_snd)
    have hm3 : Measurable (fun p : ℝ × ℝ ↦ (Real.exp (-ε * p.2) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp
        (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_snd))
    have hm4 : Measurable (fun p : ℝ × ℝ ↦ Complex.exp ((p.1 : ℂ) * ((x - p.2 : ℝ) : ℂ) * Complex.I)) := by
      have : Measurable (fun p : ℝ × ℝ ↦ (p.1 : ℂ) * ((x - p.2 : ℝ) : ℂ) * Complex.I) :=
        ((Complex.continuous_ofReal.measurable.comp measurable_fst).mul
          (Complex.continuous_ofReal.measurable.comp (measurable_const.sub measurable_snd))).mul
          measurable_const
      exact Complex.continuous_exp.measurable.comp this
    exact ((hm1.mul hm2).mul hm3).mul hm4
  have hjoint_int : Integrable (Function.uncurry fun t u : ℝ ↦
      ((1 - |t| / T : ℝ) : ℂ) * (g_u u : ℂ) * (Real.exp (-ε * u) : ℂ) *
        Complex.exp ((t : ℂ) * ((x - u : ℝ) : ℂ) * Complex.I))
      ((volume.restrict (Set.Ioc (-T) T)).prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    refine hprod_bound.mono' hjoint_meas.aestronglyMeasurable ?_
    have hae : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Set.Ioc (-T) T)).prod (volume.restrict (Set.Ioi (0 : ℝ)))),
        p.1 ∈ Set.Ioc (-T) T :=
      MeasureTheory.Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [hae] with p hp
    dsimp [Function.uncurry]
    have habs_t : |p.1| ≤ T := abs_le.mpr ⟨hp.1.le, hp.2⟩
    have htent_le : |1 - |p.1| / T| ≤ 1 := by
      have h1 : 0 ≤ |p.1| / T := by positivity
      have h2 : |p.1| / T ≤ 1 := (div_le_one hT).mpr habs_t
      rw [abs_of_nonneg (by linarith)]
      linarith
    have hexp_norm : ‖Complex.exp ((p.1 : ℂ) * ((x - p.2 : ℝ) : ℂ) * Complex.I)‖ = 1 := by
      rw [show (p.1 : ℂ) * ((x - p.2 : ℝ) : ℂ) * Complex.I =
        ((p.1 * (x - p.2) : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    rw [norm_mul, norm_mul, norm_mul, hexp_norm, mul_one, Complex.norm_real, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      Real.norm_of_nonneg (Real.exp_pos _).le, one_mul, mul_assoc]
    exact mul_le_of_le_one_left (by positivity) htent_le
  rw [MeasureTheory.integral_integral_swap hjoint_int, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_
  have hpull :
      ∫ t in Set.Ioc (-T) T,
        ((1 - |t| / T : ℝ) : ℂ) * (g_u u : ℂ) * (Real.exp (-ε * u) : ℂ) *
          Complex.exp ((t : ℂ) * ((x - u : ℝ) : ℂ) * Complex.I) =
      (g_u u : ℂ) * (Real.exp (-ε * u) : ℂ) *
        ∫ t in (-T)..T,
          ((1 - |t| / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * ((x - u : ℝ) : ℂ) * Complex.I) := by
    rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T), ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t _ ↦ ?_
    ring
  rw [hpull]
  have hfe := integral_tent_exp_eq_fejerKernel hT (x - u)
  linear_combination (g_u u : ℂ) * (Real.exp (-ε * u) : ℂ) * hfe

lemma time_side_lower_bound
    {ε_sign C : ℝ} (hε : ε_sign = 1 ∨ ε_sign = -1) (hC : 0 < C)
    (hbound : ∀ᶠ n : ℕ in Filter.atTop, -C * (Real.sqrt n / Real.log n) ≤ ε_sign * J_sum n)
    (hℓ_int : ∀ s : ℂ, 1 / 2 < s.re →
      IntegrableOn (fun t : ℝ ↦ (J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1))
    {T : ℝ} (hT : 0 < T) :
    ∃ X₀ : ℝ, ∀ x : ℝ, X₀ ≤ x → ∀ ε : ℝ, 0 < ε →
      -(C + 1 / 5) ≤
        ε_sign * (∫ u in Set.Ioi 0,
          (g_u u : ℂ) * (Real.exp (-ε * u) : ℂ) * (fejerKernel T (x - u) : ℂ)).re := by
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hbound
  let u₀ : ℝ := max (Real.log ((N₀ : ℝ) + 2)) (max 3 (10 * C + 2))
  have hu₀_ge3 : 3 ≤ u₀ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hu₀_pos : 0 < u₀ := by linarith
  -- For u ≥ u₀, ε_sign * g_u u ≥ -(C + 1/10)
  have htail_ge : ∀ u : ℝ, u₀ ≤ u → -(C + 1 / 10) ≤ ε_sign * g_u u := by
    intro u hu
    have hu3 : 3 ≤ u := hu₀_ge3.trans hu
    have huC : 10 * C + 2 ≤ u := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hu
    have huN : Real.log ((N₀ : ℝ) + 2) ≤ u := (le_max_left _ _).trans hu
    have hexp_geN : (N₀ : ℝ) + 2 ≤ Real.exp u := by
      have h1 := Real.exp_le_exp.mpr huN
      rwa [Real.exp_log (by positivity : (0 : ℝ) < (N₀ : ℝ) + 2)] at h1
    let n : ℕ := ⌊Real.exp u⌋₊
    have hn_ge : N₀ ≤ n := by
      have h1 : (N₀ : ℝ) + 1 ≤ (n : ℝ) := by
        have hlt := Nat.lt_floor_add_one (Real.exp u)
        linarith
      exact_mod_cast (show (N₀ : ℝ) ≤ (n : ℝ) by linarith)
    have hn_le : (n : ℝ) ≤ Real.exp u := Nat.floor_le (Real.exp_pos u).le
    have hn_gt_sub : Real.exp u - 1 < (n : ℝ) := by
      have hlt := Nat.lt_floor_add_one (Real.exp u)
      linarith
    have hexp_sub : Real.exp (u - 1) ≤ Real.exp u - 1 := by
      have he1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      have h2 : Real.exp (u - 1) ≥ 2 := by
        have h1 : (u - 1) + 1 ≤ Real.exp (u - 1) := Real.add_one_le_exp (u - 1)
        linarith
      have h3 : 2 * Real.exp (u - 1) ≤ Real.exp u := by
        rw [show Real.exp u = Real.exp 1 * Real.exp (u - 1) by
          rw [← Real.exp_add]; congr 1; ring]
        have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        nlinarith [Real.exp_pos (u - 1)]
      linarith
    have hn_ge_exp : Real.exp (u - 1) ≤ (n : ℝ) := hexp_sub.trans hn_gt_sub.le
    have hlog_ge : u - 1 ≤ Real.log (n : ℝ) := by
      have h1 := Real.log_le_log (Real.exp_pos (u - 1)) hn_ge_exp
      rwa [Real.log_exp] at h1
    have hlog_pos : 0 < Real.log (n : ℝ) := by linarith
    have hsqrt_le : Real.sqrt (n : ℝ) ≤ Real.exp (u / 2) := by
      rw [← Real.sqrt_sq (Real.exp_pos (u / 2)).le]
      apply Real.sqrt_le_sqrt
      rw [← Real.exp_nat_mul, show (2 : ℕ) * (u / 2) = u by ring]
      exact hn_le
    have hJ : -C * (Real.sqrt n / Real.log n) ≤ ε_sign * J_sum n := hN₀ n hn_ge
    have hg_eq : ε_sign * g_u u = u * Real.exp (-u / 2) * (ε_sign * J_sum n) := by
      dsimp [g_u, n]; ring
    rw [hg_eq]
    have hmul := mul_le_mul_of_nonneg_left hJ (by positivity : 0 ≤ u * Real.exp (-u / 2))
    have hprod_le : u * Real.exp (-u / 2) * (Real.sqrt n / Real.log n) ≤ 1 + 1 / (10 * C) := by
      have h1 : Real.exp (-u / 2) * Real.sqrt n ≤ 1 := by
        calc Real.exp (-u / 2) * Real.sqrt n
            ≤ Real.exp (-u / 2) * Real.exp (u / 2) :=
              mul_le_mul_of_nonneg_left hsqrt_le (Real.exp_pos _).le
          _ = 1 := by rw [← Real.exp_add, show -u / 2 + u / 2 = 0 by ring, Real.exp_zero]
      have h2 : u / Real.log n ≤ u / (u - 1) :=
        div_le_div_of_nonneg_left (by linarith) (by linarith) hlog_ge
      have h3 : u / (u - 1) ≤ 1 + 1 / (10 * C) := by
        rw [div_le_iff₀ (by linarith : 0 < u - 1)]
        have : (1 + 1 / (10 * C)) * (u - 1) = u - 1 + (u - 1) / (10 * C) := by ring
        rw [this]
        have : 1 ≤ (u - 1) / (10 * C) := (one_le_div (by positivity)).mpr (by linarith)
        linarith
      calc u * Real.exp (-u / 2) * (Real.sqrt n / Real.log n)
          = (u / Real.log n) * (Real.exp (-u / 2) * Real.sqrt n) := by ring
        _ ≤ (u / Real.log n) * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = u / Real.log n := mul_one _
        _ ≤ 1 + 1 / (10 * C) := h2.trans h3
    calc -(C + 1 / 10)
        = -C * (1 + 1 / (10 * C)) := by field_simp
      _ ≤ -C * (u * Real.exp (-u / 2) * (Real.sqrt n / Real.log n)) := by nlinarith
      _ = u * Real.exp (-u / 2) * (-C * (Real.sqrt n / Real.log n)) := by ring
      _ ≤ u * Real.exp (-u / 2) * (ε_sign * J_sum n) := hmul
  -- On (0, u₀), |g_u u| ≤ M₀
  let M₀ : ℝ := u₀ * Real.exp u₀
  have hM₀_pos : 0 < M₀ := by positivity
  have hhead_le : ∀ u : ℝ, u ∈ Set.Ioc 0 u₀ → |g_u u| ≤ M₀ := by
    intro u hu
    dsimp [g_u]
    rw [abs_mul, abs_mul, abs_of_pos hu.1, abs_of_pos (Real.exp_pos _)]
    have h1 : |J_sum ⌊Real.exp u⌋₊| ≤ Real.exp u :=
      (abs_J_sum_le _).trans (Nat.floor_le (Real.exp_pos u).le)
    have h2 : Real.exp u ≤ Real.exp u₀ := Real.exp_le_exp.mpr hu.2
    have h3 : Real.exp (-u / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hu.1])
    calc u * |J_sum ⌊Real.exp u⌋₊| * Real.exp (-u / 2)
        ≤ u₀ * Real.exp u₀ * 1 := by
          apply mul_le_mul _ h3 (Real.exp_pos _).le (by positivity)
          exact mul_le_mul hu.2 (h1.trans h2) (abs_nonneg _) hu₀_pos.le
      _ = M₀ := mul_one _
  -- Choose X₀ large enough that head error ≤ 1/10
  let X₀ : ℝ := u₀ + Real.sqrt (20 * u₀ * M₀ / (Real.pi * T)) + 1
  refine ⟨X₀, fun x hx ε hε_pos ↦ ?_⟩
  -- Real part equals real integral
  have hint_c : IntegrableOn
      (fun u : ℝ ↦ (g_u u : ℂ) * (Real.exp (-ε * u) : ℂ) * (fejerKernel T (x - u) : ℂ))
      (Set.Ioi 0) := by
    have hbase := (integrableOn_g_u_exp hℓ_int hε_pos 0).norm.const_mul (T / (2 * Real.pi))
    refine hbase.mono' ?_ ?_
    · exact (((Complex.continuous_ofReal.measurable.comp measurable_g_u).mul
        (Complex.continuous_ofReal.measurable.comp
          (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)))).mul
        (Complex.continuous_ofReal.measurable.comp
          ((measurable_fejerKernel T).comp (measurable_const.sub measurable_id)))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), abs_of_nonneg (fejerKernel_nonneg hT _), Complex.norm_exp,
        Complex.ofReal_zero, zero_mul, add_zero, neg_mul, Complex.neg_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      have hfk := fejerKernel_le_const hT (x - u)
      calc |g_u u| * Real.exp (-(ε * u)) * fejerKernel T (x - u)
          ≤ |g_u u| * Real.exp (-(ε * u)) * (T / (2 * Real.pi)) :=
            mul_le_mul_of_nonneg_left hfk (by positivity)
        _ = T / (2 * Real.pi) * (|g_u u| * Real.exp (-(ε * u))) := by ring
  have hint_r : IntegrableOn
      (fun u : ℝ ↦ g_u u * Real.exp (-ε * u) * fejerKernel T (x - u)) (Set.Ioi 0) := by
    have hre : IntegrableOn
        (fun u : ℝ ↦ Complex.reCLM ((g_u u : ℂ) * (Real.exp (-ε * u) : ℂ) * (fejerKernel T (x - u) : ℂ)))
        (Set.Ioi 0) := Complex.reCLM.integrable_comp hint_c
    refine hre.congr_fun (fun u _ ↦ ?_) measurableSet_Ioi
    simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
  have hre_eq :
      (∫ u in Set.Ioi 0, (g_u u : ℂ) * (Real.exp (-ε * u) : ℂ) * (fejerKernel T (x - u) : ℂ)).re =
        ∫ u in Set.Ioi 0, g_u u * Real.exp (-ε * u) * fejerKernel T (x - u) := by
    have h := (Complex.reCLM.integral_comp_comm hint_c).symm
    refine h.trans (MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_)
    simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
  rw [hre_eq, ← MeasureTheory.integral_const_mul]
  -- Split Ioi 0 = Ioc 0 u₀ ∪ Ioi u₀
  have hunion : Set.Ioi (0 : ℝ) = Set.Ioc 0 u₀ ∪ Set.Ioi u₀ :=
    (Set.Ioc_union_Ioi_eq_Ioi hu₀_pos.le).symm
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) u₀) (Set.Ioi u₀) := Set.Ioc_disjoint_Ioi_same
  have hint_s : IntegrableOn (fun u : ℝ ↦ ε_sign * (g_u u * Real.exp (-ε * u) * fejerKernel T (x - u)))
      (Set.Ioi 0) := hint_r.const_mul ε_sign
  rw [hunion, MeasureTheory.setIntegral_union hdisj measurableSet_Ioi
    (hint_s.mono_set (Set.Ioc_subset_Ioi_self))
    (hint_s.mono_set (Set.Ioi_subset_Ioi hu₀_pos.le))]
  -- Bound head integral ≥ -1/10
  have hhead_bound : -(1 / 10 : ℝ) ≤
      ∫ u in Set.Ioc 0 u₀, ε_sign * (g_u u * Real.exp (-ε * u) * fejerKernel T (x - u)) := by
    have hxu : Real.sqrt (20 * u₀ * M₀ / (Real.pi * T)) + 1 ≤ x - u₀ := by dsimp [X₀] at hx; linarith
    have hxu_pos : 0 < x - u₀ := by linarith [Real.sqrt_nonneg (20 * u₀ * M₀ / (Real.pi * T))]
    have hfk_bd : ∀ u ∈ Set.Ioc 0 u₀, fejerKernel T (x - u) ≤ 2 / (Real.pi * T * (x - u₀) ^ 2) := by
      intro u hu
      have hge : x - u₀ ≤ x - u := by linarith [hu.2]
      have hpos : 0 < x - u := hxu_pos.trans_le hge
      calc fejerKernel T (x - u)
          ≤ 2 / (Real.pi * T * (x - u) ^ 2) := fejerKernel_le_inv_sq hT hpos.ne'
        _ ≤ 2 / (Real.pi * T * (x - u₀) ^ 2) := by
            apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hxu_pos.le hge 2) (by positivity)
    have hpt : ∀ u ∈ Set.Ioc 0 u₀,
        -(M₀ * (2 / (Real.pi * T * (x - u₀) ^ 2))) ≤
          ε_sign * (g_u u * Real.exp (-ε * u) * fejerKernel T (x - u)) := by
      intro u hu
      have hε1 : |ε_sign| = 1 := by rcases hε with rfl | rfl <;> norm_num
      have habs : |ε_sign * (g_u u * Real.exp (-ε * u) * fejerKernel T (x - u))| ≤
          M₀ * (2 / (Real.pi * T * (x - u₀) ^ 2)) := by
        rw [abs_mul, hε1, one_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
          abs_of_nonneg (fejerKernel_nonneg hT _)]
        have hexp1 : Real.exp (-ε * u) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hu.1])
        calc |g_u u| * Real.exp (-ε * u) * fejerKernel T (x - u)
            ≤ M₀ * 1 * (2 / (Real.pi * T * (x - u₀) ^ 2)) := by
              apply mul_le_mul _ (hfk_bd u hu) (fejerKernel_nonneg hT _) (by positivity)
              exact mul_le_mul (hhead_le u hu) hexp1 (Real.exp_pos _).le hM₀_pos.le
          _ = M₀ * (2 / (Real.pi * T * (x - u₀) ^ 2)) := by ring
      linarith [(abs_le.mp habs).1]
    have hmono := MeasureTheory.setIntegral_mono_on
      (integrableOn_const (by simp : volume (Set.Ioc (0 : ℝ) u₀) ≠ ⊤))
      (hint_s.mono_set Set.Ioc_subset_Ioi_self) measurableSet_Ioc hpt
    rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le hu₀_pos.le, sub_zero,
      smul_eq_mul] at hmono
    have hsq : 20 * u₀ * M₀ / (Real.pi * T) ≤ (x - u₀) ^ 2 := by
      have h1 : Real.sqrt (20 * u₀ * M₀ / (Real.pi * T)) ≤ x - u₀ := by linarith
      calc 20 * u₀ * M₀ / (Real.pi * T)
          = (Real.sqrt (20 * u₀ * M₀ / (Real.pi * T))) ^ 2 :=
            (Real.sq_sqrt (by positivity)).symm
        _ ≤ (x - u₀) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    have hsmall : u₀ * (M₀ * (2 / (Real.pi * T * (x - u₀) ^ 2))) ≤ 1 / 10 := by
      have : u₀ * (M₀ * (2 / (Real.pi * T * (x - u₀) ^ 2))) =
          (2 * u₀ * M₀) / (Real.pi * T * (x - u₀) ^ 2) := by ring
      rw [this, div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 10)]
      have hmul := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ Real.pi * T)
      rw [mul_div_cancel₀ _ (by positivity : Real.pi * T ≠ 0)] at hmul
      linarith
    linarith
  -- Bound tail integral ≥ -(C + 1/10)
  have htail_bound : -(C + 1 / 10) ≤
      ∫ u in Set.Ioi u₀, ε_sign * (g_u u * Real.exp (-ε * u) * fejerKernel T (x - u)) := by
    have hshift : Integrable (fun u : ℝ ↦ fejerKernel T (x - u)) := by
      have h1 : Integrable (fun u : ℝ ↦ fejerKernel T (u - x)) :=
        (integrable_fejerKernel hT).comp_sub_right x
      refine h1.congr (Filter.Eventually.of_forall fun u ↦ ?_)
      dsimp only
      rw [← fejerKernel_even T (u - x)]
      congr 1; ring
    have hfk_int : IntegrableOn (fun u : ℝ ↦ -(C + 1 / 10) * fejerKernel T (x - u)) (Set.Ioi u₀) :=
      (hshift.const_mul (-(C + 1 / 10))).integrableOn
    have hpt : ∀ u ∈ Set.Ioi u₀,
        -(C + 1 / 10) * fejerKernel T (x - u) ≤
          ε_sign * (g_u u * Real.exp (-ε * u) * fejerKernel T (x - u)) := by
      intro u hu
      have hu_gt : u₀ < u := hu
      have hg := htail_ge u hu_gt.le
      have hexp_pos : 0 < Real.exp (-ε * u) := Real.exp_pos _
      have hexp_le1 : Real.exp (-ε * u) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      have hprod : -(C + 1 / 10) ≤ (ε_sign * g_u u) * Real.exp (-ε * u) := by
        calc -(C + 1 / 10)
            ≤ -(C + 1 / 10) * Real.exp (-ε * u) := by nlinarith
          _ ≤ (ε_sign * g_u u) * Real.exp (-ε * u) :=
              mul_le_mul_of_nonneg_right hg hexp_pos.le
      calc -(C + 1 / 10) * fejerKernel T (x - u)
          ≤ ((ε_sign * g_u u) * Real.exp (-ε * u)) * fejerKernel T (x - u) :=
            mul_le_mul_of_nonneg_right hprod (fejerKernel_nonneg hT _)
        _ = ε_sign * (g_u u * Real.exp (-ε * u) * fejerKernel T (x - u)) := by ring
    have hmono := MeasureTheory.setIntegral_mono_on hfk_int
      (hint_s.mono_set (Set.Ioi_subset_Ioi hu₀_pos.le)) measurableSet_Ioi hpt
    rw [MeasureTheory.integral_const_mul] at hmono
    have hfk_le1 : ∫ u in Set.Ioi u₀, fejerKernel T (x - u) ≤ 1 := by
      have hle_all : ∫ u in Set.Ioi u₀, fejerKernel T (x - u) ≤
          ∫ u : ℝ, fejerKernel T (x - u) :=
        MeasureTheory.setIntegral_le_integral hshift
          (Filter.Eventually.of_forall fun u ↦ fejerKernel_nonneg hT _)
      have heq_one : ∫ u : ℝ, fejerKernel T (x - u) = 1 := by
        have h1 : ∫ u : ℝ, fejerKernel T (x - u) = ∫ u : ℝ, fejerKernel T (u - x) := by
          congr 1; ext u; rw [← fejerKernel_even T (u - x)]; congr 1; ring
        rw [h1, MeasureTheory.integral_sub_right_eq_self (fejerKernel T) x,
          integral_fejerKernel_eq_one hT]
      exact hle_all.trans_eq heq_one
    nlinarith
  linarith

/- Part 4D: Local factorization of `L₄` and `ℓ` on `ball (1/2) (T + 1)` -/

lemma analyticOrderAt_L₄_ne_top (z : ℂ) : analyticOrderAt L₄ z ≠ ⊤ := by
  intro htop
  have h0 := (differentiable_L₄.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ z) (analyticOrderAt_eq_top.mp htop)
  exact L₄_real_ne_zero zero_lt_one (by simpa using h0 (Set.mem_univ (1 : ℂ)))

lemma hasDerivAt_conj_comp_conj {g : ℂ → ℂ} {w g' : ℂ} (hg : HasDerivAt g g' (conj w)) :
    HasDerivAt (fun z : ℂ ↦ conj (g (conj z))) (conj g') w := by
  rw [hasDerivAt_iff_tendsto_slope_zero] at hg ⊢
  have hconj_nhds : Filter.Tendsto (fun h : ℂ ↦ conj h) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : Filter.Tendsto (fun h : ℂ ↦ conj h) (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
        simpa using (Complex.continuous_conj.tendsto (0 : ℂ))
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h hh
      simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hh
  have hcomp := (Complex.continuous_conj.tendsto g').comp (hg.comp hconj_nhds)
  refine hcomp.congr fun h ↦ ?_
  simp only [Function.comp_apply, smul_eq_mul, map_mul, map_inv₀, map_sub, map_add,
    Complex.conj_conj]

lemma analyticAt_conj_comp_conj {g : ℂ → ℂ} {z₀ : ℂ} (hg : AnalyticAt ℂ g z₀) :
    AnalyticAt ℂ (fun w : ℂ ↦ conj (g (conj w))) (conj z₀) := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hg.eventually_analyticAt
  have hdiff : DifferentiableOn ℂ (fun w : ℂ ↦ conj (g (conj w))) (Metric.ball (conj z₀) r) := by
    intro w hw
    have hcw : conj w ∈ Metric.ball z₀ r := by
      rw [Metric.mem_ball, dist_eq_norm] at hw ⊢
      have heq : conj w - z₀ = conj (w - conj z₀) := by simp [map_sub]
      rw [heq, Complex.norm_conj]
      exact hw
    have hd : DifferentiableAt ℂ g (conj w) := (hball hcw).differentiableAt
    exact (hasDerivAt_conj_comp_conj hd.hasDerivAt).differentiableAt.differentiableWithinAt
  exact (hdiff.analyticOnNhd Metric.isOpen_ball) (conj z₀) (Metric.mem_ball_self hr)

lemma analyticOrderAt_L₄_conj (z : ℂ) : analyticOrderAt L₄ (conj z) = analyticOrderAt L₄ z := by
  have hne : analyticOrderAt L₄ z ≠ ⊤ := analyticOrderAt_L₄_ne_top z
  set m : ℕ := (analyticOrderAt L₄ z).toNat
  have hm : analyticOrderAt L₄ z = (m : ℕ∞) := (ENat.natCast_toNat hne).symm
  have hL_an : AnalyticAt ℂ L₄ z :=
    (differentiable_L₄.differentiableOn.analyticOnNhd isOpen_univ) z (Set.mem_univ z)
  obtain ⟨g, hg_an, hgz, hfeq⟩ := (hL_an.analyticOrderAt_eq_natCast.mp hm)
  have hL_an_c : AnalyticAt ℂ L₄ (conj z) :=
    (differentiable_L₄.differentiableOn.analyticOnNhd isOpen_univ) (conj z) (Set.mem_univ _)
  rw [hm, hL_an_c.analyticOrderAt_eq_natCast]
  refine ⟨fun w ↦ conj (g (conj w)), analyticAt_conj_comp_conj hg_an, ?_, ?_⟩
  · simpa [Complex.conj_conj] using hgz
  · have hcont : Filter.Tendsto (fun w : ℂ ↦ conj w) (𝓝 (conj z)) (𝓝 z) := by
      simpa [Complex.conj_conj] using Complex.continuous_conj.tendsto (conj z)
    filter_upwards [hcont.eventually hfeq] with w hw
    have hLw : L₄ w = conj (L₄ (conj w)) := by
      rw [L₄_conj, Complex.conj_conj]
    rw [hLw, hw]
    simp [smul_eq_mul, map_mul, map_pow, map_sub]

lemma extract_L₄_zeros
    (hzf : ∀ s : ℂ, 1 / 2 < s.re → L₄ s ≠ 0)
    (ℓ : ℂ → ℂ)
    (hℓ_diff : DifferentiableOn ℂ ℓ {s : ℂ | 1 / 2 < s.re})
    (hℓ_exp : ∀ s : ℂ, 1 / 2 < s.re → Complex.exp (ℓ s) = L₄ s)
    {T : ℝ} (hT : 2 ≤ T) :
    ∃ (S_all : Finset ℂ) (ℓ_H : ℂ → ℂ) (c₀ : ℂ),
      (∀ ρ ∈ S_all, ρ ∈ Metric.closedBall (1 / 2 : ℂ) (T + 1) ∧ ρ.re ≤ 1 / 2 ∧ L₄ ρ = 0) ∧
      (∀ ρ ∈ Metric.closedBall (1 / 2 : ℂ) (T + 1), L₄ ρ = 0 → ρ ∈ S_all) ∧
      DifferentiableOn ℂ ℓ_H (Metric.ball (1 / 2 : ℂ) (T + 1)) ∧
      (∀ s ∈ Metric.ball (1 / 2 : ℂ) (T + 1), 1 / 2 < s.re →
        ℓ s = c₀ + ℓ_H s +
          ∑ ρ ∈ S_all, ((analyticOrderAt L₄ ρ).toNat : ℂ) * Complex.log (s - ρ)) ∧
      (∀ s ∈ Metric.ball (1 / 2 : ℂ) (T + 1), 1 / 2 < s.re →
        deriv L₄ s / L₄ s = deriv ℓ_H s +
          ∑ ρ ∈ S_all, ((analyticOrderAt L₄ ρ).toNat : ℂ) / (s - ρ)) := by
  classical
  let U : Set ℂ := Metric.closedBall (1 / 2 : ℂ) (T + 1)
  let B : Set ℂ := Metric.ball (1 / 2 : ℂ) (T + 1)
  have hL_an : AnalyticOnNhd ℂ L₄ U :=
    (differentiable_L₄.differentiableOn.analyticOnNhd isOpen_univ).mono (Set.subset_univ _)
  have hL_mer : MeromorphicOn L₄ U := hL_an.meromorphicOn
  let D := MeromorphicOn.divisor L₄ U
  have hD_fin : D.support.Finite := D.finiteSupport (isCompact_closedBall (1 / 2 : ℂ) (T + 1))
  let S_all : Finset ℂ := hD_fin.toFinset
  have hD_eq_nat : ∀ ρ ∈ U, D ρ = ((analyticOrderAt L₄ ρ).toNat : ℤ) := by
    intro ρ hρ
    have h1 := MeromorphicOn.AnalyticOnNhd.divisor_apply hL_an hρ
    have hne : analyticOrderAt L₄ ρ ≠ ⊤ := analyticOrderAt_L₄_ne_top ρ
    have hm : analyticOrderAt L₄ ρ = ((analyticOrderAt L₄ ρ).toNat : ℕ∞) := (ENat.natCast_toNat hne).symm
    change D ρ = _
    dsimp [D]
    rw [h1, hm]
    simp
  have hS_mem : ∀ ρ ∈ S_all, ρ ∈ U ∧ ρ.re ≤ 1 / 2 ∧ L₄ ρ = 0 := by
    intro ρ hρ
    have hsupp : D ρ ≠ 0 := by simpa [S_all] using hρ
    have hρU : ρ ∈ U := by
      by_contra hnot
      exact hsupp (D.apply_eq_zero_of_notMem hnot)
    have hpos : (0 : ℕ) < (analyticOrderAt L₄ ρ).toNat := by
      rw [hD_eq_nat ρ hρU] at hsupp
      omega
    have hord_ne : analyticOrderAt L₄ ρ ≠ 0 := by
      intro h0; rw [h0] at hpos; simp at hpos
    have hL0 : L₄ ρ = 0 := by
      by_contra hne0
      exact hord_ne ((hL_an ρ hρU).analyticOrderAt_eq_zero.mpr hne0)
    have hre : ρ.re ≤ 1 / 2 := by
      by_contra hgt
      push Not at hgt
      exact hzf ρ hgt hL0
    exact ⟨hρU, hre, hL0⟩
  have hS_complete : ∀ ρ ∈ U, L₄ ρ = 0 → ρ ∈ S_all := by
    intro ρ hρU hL0
    have hne : analyticOrderAt L₄ ρ ≠ ⊤ := analyticOrderAt_L₄_ne_top ρ
    have hord_ne : analyticOrderAt L₄ ρ ≠ 0 := by
      intro h0
      exact ((hL_an ρ hρU).analyticOrderAt_eq_zero.mp h0) hL0
    have hpos : (0 : ℕ) < (analyticOrderAt L₄ ρ).toNat := by
      have hm : ((analyticOrderAt L₄ ρ).toNat : ℕ∞) = analyticOrderAt L₄ ρ := ENat.natCast_toNat hne
      by_contra h0
      have h0' : (analyticOrderAt L₄ ρ).toNat = 0 := by omega
      rw [h0', Nat.cast_zero] at hm
      exact hord_ne hm.symm
    have hsupp : D ρ ≠ 0 := by
      rw [hD_eq_nat ρ hρU]
      exact_mod_cast hpos.ne'
    simpa [S_all] using hsupp
  -- Extract zeros via MeromorphicOn.extract_zeros_poles
  have hmer_ne_top : ∀ u : U, meromorphicOrderAt L₄ u ≠ ⊤ := fun u ↦ by
    rw [(hL_an u.1 u.2).meromorphicOrderAt_eq]
    intro htop
    have hne := analyticOrderAt_L₄_ne_top u.1
    rw [← ENat.natCast_toNat hne] at htop
    simp at htop
  obtain ⟨H, hH_an, hH_ne, hL_codisc⟩ :=
    MeromorphicOn.extract_zeros_poles hL_mer hmer_ne_top hD_fin
  -- Upgrade codiscrete equality to every point of open ball B
  let P : ℂ → ℂ := fun z ↦ ∏ ρ ∈ S_all, (z - ρ) ^ (analyticOrderAt L₄ ρ).toNat
  have hfinprod_eq : ∀ z : ℂ, (∏ᶠ u : ℂ, (fun w : ℂ ↦ w - u) ^ D u) z = P z := by
    intro z
    have hfin_fn : (Function.mulSupport fun u : ℂ ↦ (fun w : ℂ ↦ w - u) ^ D u) ⊆ (S_all : Set ℂ) := by
      intro u hu
      simp only [Function.mem_mulSupport] at hu
      have hDu : D u ≠ 0 := by
        intro h0; apply hu; ext w; simp [h0]
      simpa [S_all] using hDu
    have hsub : (Function.mulSupport fun u : ℂ ↦ (z - u) ^ D u) ⊆ (S_all : Set ℂ) := by
      intro u hu
      simp only [Function.mem_mulSupport] at hu
      have hDu : D u ≠ 0 := by intro h0; rw [h0, zpow_zero] at hu; exact hu rfl
      simpa [S_all] using hDu
    rw [finprod_apply (S_all.finite_toSet.subset hfin_fn)]
    change (∏ᶠ i : ℂ, (z - i) ^ D i) = P z
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
    refine Finset.prod_congr rfl fun ρ hρ ↦ ?_
    rw [hD_eq_nat ρ (hS_mem ρ hρ).1, zpow_natCast]
  have hL_eq_B : ∀ z ∈ B, L₄ z = P z * H z := by
    intro z hzB
    have hzU : z ∈ U := Metric.ball_subset_closedBall hzB
    have hS_cod : {w : ℂ | L₄ w = P w * H w} ∈ Filter.codiscreteWithin U := by
      filter_upwards [hL_codisc] with w hw
      have hw' : L₄ w = (∏ᶠ u : ℂ, (fun x : ℂ ↦ x - u) ^ D u) w * H w := by
        simpa [D, Pi.smul_apply', smul_eq_mul] using hw
      rwa [hfinprod_eq w] at hw'
    have hmem_nhdsNE : {w : ℂ | L₄ w = P w * H w} ∈ 𝓝[≠] z := by
      have h1 := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hS_cod z hzU
      have hU_nhds : U ∈ 𝓝[≠] z :=
        nhdsWithin_le_nhds (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hzB)
          Metric.ball_subset_closedBall)
      filter_upwards [h1, hU_nhds] with w hw1 hwU
      rcases hw1 with h | h
      · exact h
      · exact absurd hwU h
    have hc1 : ContinuousAt L₄ z := differentiable_L₄.continuous.continuousAt
    have hc2 : ContinuousAt (fun w ↦ P w * H w) z := by
      have hPc : Continuous P := by dsimp [P]; fun_prop
      exact hPc.continuousAt.mul (hH_an z hzU).continuousAt
    have hneBot : (𝓝[≠] z).NeBot := inferInstance
    exact tendsto_nhds_unique (hc1.tendsto.mono_left nhdsWithin_le_nhds)
      ((hc2.tendsto.mono_left nhdsWithin_le_nhds).congr'
        (Filter.Eventually.mono hmem_nhdsNE fun w hw ↦ hw.symm))
  -- Holomorphic logarithm ℓ_H of H on open convex ball B
  have hH_diff_B : DifferentiableOn ℂ H B :=
    (hH_an.mono Metric.ball_subset_closedBall).differentiableOn
  have hH_ne_B : ∀ z ∈ B, H z ≠ 0 := fun z hz ↦ hH_ne ⟨z, Metric.ball_subset_closedBall hz⟩
  obtain ⟨ℓ_H, hℓH_diff, hℓH_exp⟩ := exists_holomorphic_log_on_convex Metric.isOpen_ball
    (convex_ball (1 / 2 : ℂ) (T + 1)) ⟨1 / 2, Metric.mem_ball_self (by linarith)⟩
    hH_diff_B hH_ne_B
  -- Compare ℓ and ℓ_H + ∑ m(ρ) log(s - ρ) on open convex W = B ∩ {1/2 < re}
  let W : Set ℂ := B ∩ {s : ℂ | 1 / 2 < s.re}
  have hWo : IsOpen W := Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hWc : Convex ℝ W := (convex_ball _ _).inter (convex_halfSpace_re_gt (1 / 2 : ℝ))
  let z₀ : ℂ := 3 / 4
  have hz₀W : z₀ ∈ W := by
    refine ⟨?_, by simp [z₀]; norm_num⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have : z₀ - (1 / 2 : ℂ) = ((1 / 4 : ℝ) : ℂ) := by dsimp [z₀]; norm_num
    rw [this, Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
    linarith
  let logSum : ℂ → ℂ := fun s ↦
    ℓ_H s + ∑ ρ ∈ S_all, ((analyticOrderAt L₄ ρ).toNat : ℂ) * Complex.log (s - ρ)
  have hlogSum_diff : DifferentiableOn ℂ logSum W := by
    refine (hℓH_diff.mono Set.inter_subset_left).add ?_
    refine DifferentiableOn.fun_sum fun ρ hρ ↦ ?_
    refine DifferentiableOn.const_mul ?_ _
    intro s hsW
    have hsre : (1 : ℝ) / 2 < s.re := hsW.2
    have hslit : s - ρ ∈ Complex.slitPlane := by
      left
      simp only [Complex.sub_re]
      linarith [(hS_mem ρ hρ).2.1]
    exact (DifferentiableAt.clog ((differentiableAt_id).sub (differentiableAt_const ρ)) hslit).differentiableWithinAt
  have hlogSum_exp : ∀ s ∈ W, Complex.exp (logSum s) = L₄ s := by
    intro s hsW
    have hsre : (1 : ℝ) / 2 < s.re := hsW.2
    dsimp [logSum]
    rw [Complex.exp_add, hℓH_exp s hsW.1, Complex.exp_sum, hL_eq_B s hsW.1, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun ρ hρ ↦ ?_
    have hne : s - ρ ≠ 0 := by
      intro h0
      have hre := congr_arg Complex.re h0
      simp only [Complex.sub_re, Complex.zero_re] at hre
      linarith [(hS_mem ρ hρ).2.1]
    rw [Complex.exp_nat_mul, Complex.exp_log hne]
  let c₀ : ℂ := ℓ z₀ - logSum z₀
  have hc₀_exp : Complex.exp c₀ = 1 := by
    dsimp [c₀]
    rw [Complex.exp_sub, hℓ_exp z₀ hz₀W.2, hlogSum_exp z₀ hz₀W, div_self (hzf z₀ hz₀W.2)]
  have hEqW : Set.EqOn ℓ (fun s ↦ c₀ + logSum s) W := by
    refine eqOn_of_exp_eqOn_convex hWo hWc (hℓ_diff.mono Set.inter_subset_right)
      ((differentiableOn_const c₀).add hlogSum_diff) (fun s hsW ↦ ?_) hz₀W (by dsimp [c₀]; ring)
    rw [hℓ_exp s hsW.2, Complex.exp_add, hc₀_exp, one_mul, hlogSum_exp s hsW]
  refine ⟨S_all, ℓ_H, c₀, hS_mem, hS_complete, hℓH_diff, ?_, ?_⟩
  · intro s hsB hsre
    have h := hEqW ⟨hsB, hsre⟩
    dsimp [logSum] at h
    rw [h]; ring
  · intro s hsB hsre
    have hsW : s ∈ W := ⟨hsB, hsre⟩
    have hW_nhds : W ∈ 𝓝 s := hWo.mem_nhds hsW
    have hd1 : HasDerivAt ℓ (deriv L₄ s / L₄ s) s := by
      rw [← deriv_ℓ_eq hzf ℓ hℓ_diff hℓ_exp hsre]
      exact (hℓ_diff.differentiableAt (Filter.mem_of_superset hW_nhds Set.inter_subset_right)).hasDerivAt
    have hd2 : HasDerivAt (fun z ↦ c₀ + logSum z)
        (deriv ℓ_H s + ∑ ρ ∈ S_all, ((analyticOrderAt L₄ ρ).toNat : ℂ) / (s - ρ)) s := by
      have hd_H : HasDerivAt ℓ_H (deriv ℓ_H s) s :=
        (hℓH_diff.differentiableAt (Metric.isOpen_ball.mem_nhds hsB)).hasDerivAt
      have hd_sum : HasDerivAt
          (fun z ↦ ∑ ρ ∈ S_all, ((analyticOrderAt L₄ ρ).toNat : ℂ) * Complex.log (z - ρ))
          (∑ ρ ∈ S_all, ((analyticOrderAt L₄ ρ).toNat : ℂ) / (s - ρ)) s := by
        have hterm : ∀ ρ ∈ S_all,
            HasDerivAt (fun z : ℂ ↦ ((analyticOrderAt L₄ ρ).toNat : ℂ) * Complex.log (z - ρ))
              (((analyticOrderAt L₄ ρ).toNat : ℂ) / (s - ρ)) s := by
          intro ρ hρ
          have hslit : s - ρ ∈ Complex.slitPlane := by
            left; simp only [Complex.sub_re]; linarith [hsre, (hS_mem ρ hρ).2.1]
          have hsub : HasDerivAt (fun z : ℂ ↦ z - ρ) 1 s := by
            simpa using (hasDerivAt_id s).fun_sub (hasDerivAt_const s ρ)
          have hlog : HasDerivAt (fun z : ℂ ↦ Complex.log (z - ρ)) (1 / (s - ρ)) s := by
            simpa using hsub.clog hslit
          have hmul := hlog.const_mul ((analyticOrderAt L₄ ρ).toNat : ℂ)
          have heq : ((analyticOrderAt L₄ ρ).toNat : ℂ) * (1 / (s - ρ)) =
              ((analyticOrderAt L₄ ρ).toNat : ℂ) / (s - ρ) := mul_one_div _ _
          rwa [heq] at hmul
        exact HasDerivAt.fun_sum hterm
      have htot := (hasDerivAt_const s c₀).fun_add (hd_H.fun_add hd_sum)
      simpa using htot
    have heq_nhds : ℓ =ᶠ[𝓝 s] fun z ↦ c₀ + logSum z := by
      filter_upwards [hW_nhds] with z hz
      exact hEqW hz
    exact (hd1.congr_of_eventuallyEq heq_nhds.symm).unique hd2

/- Part 4E: Limits as ε → 0⁺ and x → ∞, and Pillar 3 -/

lemma pole_integral_eq_fejer {T : ℝ} (hT : 0 < T) (γ x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (1 / (2 * (Real.pi : ℂ))) *
      ∫ t in (-T)..T,
        ((1 - |t| / T : ℝ) : ℂ) * (1 / ((ε : ℂ) + ((t - γ : ℝ) : ℂ) * Complex.I)) *
          Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) =
      ∫ u in Set.Ioi (0 : ℝ),
        (Real.exp (-ε * u) : ℂ) * Complex.exp ((γ : ℂ) * (u : ℂ) * Complex.I) *
          (fejerKernel T (x - u) : ℂ) := by
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  have hsub :
      ∫ t in Set.Ioc (-T) T,
        ((1 - |t| / T : ℝ) : ℂ) * (1 / ((ε : ℂ) + ((t - γ : ℝ) : ℂ) * Complex.I)) *
          Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) =
      ∫ t in Set.Ioc (-T) T, ∫ u in Set.Ioi (0 : ℝ),
        ((1 - |t| / T : ℝ) : ℂ) * (Real.exp (-ε * u) : ℂ) *
          Complex.exp ((γ : ℂ) * (u : ℂ) * Complex.I) *
          Complex.exp ((t : ℂ) * ((x - u : ℝ) : ℂ) * Complex.I) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t _ ↦ ?_
    let a : ℂ := -((ε : ℂ) + ((t - γ : ℝ) : ℂ) * Complex.I)
    have ha_re : a.re < 0 := by simp [a]; linarith
    have hint_a := integral_exp_mul_complex_Ioi ha_re 0
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero] at hint_a
    have hinv : (1 : ℂ) / ((ε : ℂ) + ((t - γ : ℝ) : ℂ) * Complex.I) =
        ∫ u in Set.Ioi (0 : ℝ), Complex.exp (a * (u : ℂ)) := by
      rw [hint_a]
      dsimp [a]
      rw [div_neg, neg_div, neg_neg]
    rw [hinv, ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_mul_const]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_
    have hexp : Complex.exp (a * (u : ℂ)) * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) =
        (Real.exp (-ε * u) : ℂ) * Complex.exp ((γ : ℂ) * (u : ℂ) * Complex.I) *
          Complex.exp ((t : ℂ) * ((x - u : ℝ) : ℂ) * Complex.I) := by
      rw [show (Real.exp (-ε * u) : ℂ) = Complex.exp (-(ε : ℂ) * (u : ℂ)) by
        rw [Complex.ofReal_exp]; congr 1; push_cast; ring]
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      dsimp [a]
      push_cast
      ring
    linear_combination ((1 - |t| / T : ℝ) : ℂ) * hexp
  rw [hsub]
  have hint_t : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Set.Ioc (-T) T) :=
    integrableOn_const (by simp)
  have hint_u : IntegrableOn (fun u : ℝ ↦ Real.exp (-ε * u)) (Set.Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_Ioi (by linarith : -ε < 0) 0
  have hprod_bound : Integrable (fun p : ℝ × ℝ ↦ (1 : ℝ) * Real.exp (-ε * p.2))
      ((volume.restrict (Set.Ioc (-T) T)).prod (volume.restrict (Set.Ioi (0 : ℝ)))) :=
    Integrable.mul_prod hint_t hint_u
  have hjoint_cont : Continuous (fun p : ℝ × ℝ ↦
      ((1 - |p.1| / T : ℝ) : ℂ) * (Real.exp (-ε * p.2) : ℂ) *
        Complex.exp ((γ : ℂ) * (p.2 : ℂ) * Complex.I) *
        Complex.exp ((p.1 : ℂ) * ((x - p.2 : ℝ) : ℂ) * Complex.I)) := by fun_prop
  have hjoint_int : Integrable (Function.uncurry fun t u : ℝ ↦
      ((1 - |t| / T : ℝ) : ℂ) * (Real.exp (-ε * u) : ℂ) *
        Complex.exp ((γ : ℂ) * (u : ℂ) * Complex.I) *
        Complex.exp ((t : ℂ) * ((x - u : ℝ) : ℂ) * Complex.I))
      ((volume.restrict (Set.Ioc (-T) T)).prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    refine hprod_bound.mono' hjoint_cont.aestronglyMeasurable ?_
    have hae : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Set.Ioc (-T) T)).prod (volume.restrict (Set.Ioi (0 : ℝ)))),
        p.1 ∈ Set.Ioc (-T) T :=
      MeasureTheory.Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [hae] with p hp
    dsimp [Function.uncurry]
    have habs_t : |p.1| ≤ T := abs_le.mpr ⟨hp.1.le, hp.2⟩
    have htent_le : |1 - |p.1| / T| ≤ 1 := by
      have h1 : 0 ≤ |p.1| / T := by positivity
      have h2 : |p.1| / T ≤ 1 := (div_le_one hT).mpr habs_t
      rw [abs_of_nonneg (by linarith)]; linarith
    have he1 : ‖Complex.exp ((γ : ℂ) * (p.2 : ℂ) * Complex.I)‖ = 1 := by
      rw [show (γ : ℂ) * (p.2 : ℂ) * Complex.I = ((γ * p.2 : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    have he2 : ‖Complex.exp ((p.1 : ℂ) * ((x - p.2 : ℝ) : ℂ) * Complex.I)‖ = 1 := by
      rw [show (p.1 : ℂ) * ((x - p.2 : ℝ) : ℂ) * Complex.I =
        ((p.1 * (x - p.2) : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    rw [norm_mul, norm_mul, norm_mul, he1, he2, mul_one, mul_one, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le, one_mul]
    exact mul_le_of_le_one_left (Real.exp_pos _).le htent_le
  rw [MeasureTheory.integral_integral_swap hjoint_int, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_
  have hpull :
      ∫ t in Set.Ioc (-T) T,
        ((1 - |t| / T : ℝ) : ℂ) * (Real.exp (-ε * u) : ℂ) *
          Complex.exp ((γ : ℂ) * (u : ℂ) * Complex.I) *
          Complex.exp ((t : ℂ) * ((x - u : ℝ) : ℂ) * Complex.I) =
      (Real.exp (-ε * u) : ℂ) * Complex.exp ((γ : ℂ) * (u : ℂ) * Complex.I) *
        ∫ t in (-T)..T,
          ((1 - |t| / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * ((x - u : ℝ) : ℂ) * Complex.I) := by
    rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T), ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t _ ↦ ?_
    ring
  rw [hpull]
  have hfe := integral_tent_exp_eq_fejerKernel hT (x - u)
  linear_combination (Real.exp (-ε * u) : ℂ) * Complex.exp ((γ : ℂ) * (u : ℂ) * Complex.I) * hfe

lemma integrable_fejerKernel_sub {T : ℝ} (hT : 0 < T) (x : ℝ) :
    Integrable (fun u : ℝ ↦ fejerKernel T (x - u)) := by
  have h1 : Integrable (fun u : ℝ ↦ fejerKernel T (u - x)) :=
    (integrable_fejerKernel hT).comp_sub_right x
  refine h1.congr (Filter.Eventually.of_forall fun u ↦ ?_)
  dsimp only
  rw [← fejerKernel_even T (u - x)]
  congr 1; ring

lemma pole_integral_tendsto {T : ℝ} (hT : 0 < T) {γ : ℝ} (hγ : |γ| ≤ T) (x : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ ↦
        (1 / (2 * (Real.pi : ℂ))) *
          ∫ t in (-T)..T,
            ((1 - |t| / T : ℝ) : ℂ) * (1 / ((ε : ℂ) + ((t - γ : ℝ) : ℂ) * Complex.I)) *
              Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))
      (𝓝[>] (0 : ℝ))
      (nhds
        (Complex.exp ((γ : ℂ) * (x : ℂ) * Complex.I) * ((1 - |γ| / T : ℝ) : ℂ) -
          ∫ u in Set.Iic (0 : ℝ),
            Complex.exp ((γ : ℂ) * (u : ℂ) * Complex.I) * (fejerKernel T (x - u) : ℂ))) := by
  have heq_ev :
      (fun ε : ℝ ↦
        (1 / (2 * (Real.pi : ℂ))) *
          ∫ t in (-T)..T,
            ((1 - |t| / T : ℝ) : ℂ) * (1 / ((ε : ℂ) + ((t - γ : ℝ) : ℂ) * Complex.I)) *
              Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) =ᶠ[𝓝[>] (0 : ℝ)]
      fun ε : ℝ ↦
        ∫ u in Set.Ioi (0 : ℝ),
          (Real.exp (-ε * u) : ℂ) * Complex.exp ((γ : ℂ) * (u : ℂ) * Complex.I) *
            (fejerKernel T (x - u) : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact pole_integral_eq_fejer hT γ x hε
  rw [Filter.tendsto_congr' heq_ev]
  have hdct :
      Filter.Tendsto
        (fun ε : ℝ ↦
          ∫ u in Set.Ioi (0 : ℝ),
            (Real.exp (-ε * u) : ℂ) * Complex.exp ((γ : ℂ) * (u : ℂ) * Complex.I) *
              (fejerKernel T (x - u) : ℂ))
        (𝓝[>] (0 : ℝ))
        (nhds
          (∫ u in Set.Ioi (0 : ℝ),
            Complex.exp ((γ : ℂ) * (u : ℂ) * Complex.I) * (fejerKernel T (x - u) : ℂ))) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun u : ℝ ↦ fejerKernel T (x - u)) ?_ ?_ (integrable_fejerKernel_sub hT x).integrableOn ?_
    · refine Filter.Eventually.of_forall fun ε ↦ ?_
      have hm : Measurable (fun u : ℝ ↦
          (Real.exp (-ε * u) : ℂ) * Complex.exp ((γ : ℂ) * (u : ℂ) * Complex.I) *
            (fejerKernel T (x - u) : ℂ)) :=
        (((Complex.continuous_ofReal.measurable.comp
          (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id))).mul
          (Complex.continuous_exp.measurable.comp
            ((measurable_const.mul Complex.continuous_ofReal.measurable).mul measurable_const))).mul
          (Complex.continuous_ofReal.measurable.comp
            ((measurable_fejerKernel T).comp (measurable_const.sub measurable_id))))
      exact hm.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hεpos : 0 < ε := hε
      have hupos : 0 < u := hu
      have he1 : ‖Complex.exp ((γ : ℂ) * (u : ℂ) * Complex.I)‖ = 1 := by
        rw [show (γ : ℂ) * (u : ℂ) * Complex.I = ((γ * u : ℝ) : ℂ) * Complex.I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I]
      rw [norm_mul, norm_mul, he1, mul_one, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (fejerKernel_nonneg hT _)]
      have hexp1 : Real.exp (-ε * u) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      exact mul_le_of_le_one_left (fejerKernel_nonneg hT _) hexp1
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _
      have ht1 : Filter.Tendsto (fun ε : ℝ ↦ (Real.exp (-ε * u) : ℂ)) (𝓝[>] (0 : ℝ)) (nhds (1 : ℂ)) := by
        have hc : Continuous (fun ε : ℝ ↦ (Real.exp (-ε * u) : ℂ)) := by fun_prop
        simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
      have hmul : Filter.Tendsto
          (fun ε : ℝ ↦ (Real.exp (-ε * u) : ℂ) * Complex.exp ((γ : ℂ) * (u : ℂ) * Complex.I) *
            (fejerKernel T (x - u) : ℂ))
          (𝓝[>] (0 : ℝ))
          (nhds ((1 : ℂ) * Complex.exp ((γ : ℂ) * (u : ℂ) * Complex.I) *
            (fejerKernel T (x - u) : ℂ))) :=
        (ht1.mul tendsto_const_nhds).mul tendsto_const_nhds
      simpa using hmul
  -- Evaluate ∫ u in Ioi 0 = (∫ u : ℝ) - (∫ u in Iic 0)
  have hint_full : Integrable
      (fun u : ℝ ↦ Complex.exp ((γ : ℂ) * (u : ℂ) * Complex.I) * (fejerKernel T (x - u) : ℂ)) := by
    refine (integrable_fejerKernel_sub hT x).mono' ?_ (Filter.Eventually.of_forall fun u ↦ ?_)
    · exact ((Complex.continuous_exp.measurable.comp
        ((measurable_const.mul Complex.continuous_ofReal.measurable).mul measurable_const)).mul
        (Complex.continuous_ofReal.measurable.comp
          ((measurable_fejerKernel T).comp (measurable_const.sub measurable_id)))).aestronglyMeasurable
    · have he1 : ‖Complex.exp ((γ : ℂ) * (u : ℂ) * Complex.I)‖ = 1 := by
        rw [show (γ : ℂ) * (u : ℂ) * Complex.I = ((γ * u : ℝ) : ℂ) * Complex.I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I]
      rw [norm_mul, he1, one_mul, Complex.norm_real, Real.norm_of_nonneg (fejerKernel_nonneg hT _)]
  have hsplit :
      ∫ u in Set.Ioi (0 : ℝ),
        Complex.exp ((γ : ℂ) * (u : ℂ) * Complex.I) * (fejerKernel T (x - u) : ℂ) =
      (∫ u : ℝ, Complex.exp ((γ : ℂ) * (u : ℂ) * Complex.I) * (fejerKernel T (x - u) : ℂ)) -
        ∫ u in Set.Iic (0 : ℝ),
          Complex.exp ((γ : ℂ) * (u : ℂ) * Complex.I) * (fejerKernel T (x - u) : ℂ) := by
    have hunion :
        (∫ u in Set.Iic (0 : ℝ),
          Complex.exp ((γ : ℂ) * (u : ℂ) * Complex.I) * (fejerKernel T (x - u) : ℂ)) +
        (∫ u in Set.Ioi (0 : ℝ),
          Complex.exp ((γ : ℂ) * (u : ℂ) * Complex.I) * (fejerKernel T (x - u) : ℂ)) =
        ∫ u : ℝ, Complex.exp ((γ : ℂ) * (u : ℂ) * Complex.I) * (fejerKernel T (x - u) : ℂ) := by
      rw [← MeasureTheory.setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
        hint_full.integrableOn hint_full.integrableOn, Set.Iic_union_Ioi, MeasureTheory.setIntegral_univ]
    exact eq_sub_of_add_eq' hunion
  have hfull_eq :
      ∫ u : ℝ, Complex.exp ((γ : ℂ) * (u : ℂ) * Complex.I) * (fejerKernel T (x - u) : ℂ) =
        Complex.exp ((γ : ℂ) * (x : ℂ) * Complex.I) * ((1 - |γ| / T : ℝ) : ℂ) := by
    have hshift := MeasureTheory.integral_sub_left_eq_self
      (fun v : ℝ ↦ Complex.exp ((γ : ℂ) * ((x - v : ℝ) : ℂ) * Complex.I) * (fejerKernel T v : ℂ))
      volume x
    have hsimp :
        ∫ u : ℝ, Complex.exp ((γ : ℂ) * ((x - (x - u) : ℝ) : ℂ) * Complex.I) * (fejerKernel T (x - u) : ℂ) =
        ∫ u : ℝ, Complex.exp ((γ : ℂ) * (u : ℂ) * Complex.I) * (fejerKernel T (x - u) : ℂ) := by
      congr 1; ext u; simp
    rw [← hsimp, hshift]
    have hpull :
        ∫ v : ℝ, Complex.exp ((γ : ℂ) * ((x - v : ℝ) : ℂ) * Complex.I) * (fejerKernel T v : ℂ) =
        Complex.exp ((γ : ℂ) * (x : ℂ) * Complex.I) *
          ∫ v : ℝ, Complex.exp (((-γ : ℝ) : ℂ) * (v : ℂ) * Complex.I) * (fejerKernel T v : ℂ) := by
      rw [← MeasureTheory.integral_const_mul]
      congr 1; ext v
      rw [← mul_assoc, ← Complex.exp_add]
      congr 2; push_cast; ring
    rw [hpull, integral_fejerKernel_exp_eq_tent hT (-γ), abs_neg]
    have hnn : 0 ≤ 1 - |γ| / T := sub_nonneg.mpr ((div_le_one hT).mpr hγ)
    rw [max_eq_left hnn]
  rwa [hsplit, hfull_eq] at hdct

lemma tendsto_pole_tail_zero {T : ℝ} (hT : 0 < T) (γ : ℝ) :
    Filter.Tendsto
      (fun x : ℝ ↦
        ∫ u in Set.Iic (0 : ℝ),
          Complex.exp ((γ : ℂ) * (u : ℂ) * Complex.I) * (fejerKernel T (x - u) : ℂ))
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  refine ⟨max 1 (4 / (Real.pi * T * δ)), fun x hx ↦ ?_⟩
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hx)
  have hxbd : 4 / (Real.pi * T * δ) ≤ x := (le_max_right _ _).trans hx
  rw [dist_zero_right]
  have hnorm_le :
      ‖∫ u in Set.Iic (0 : ℝ),
          Complex.exp ((γ : ℂ) * (u : ℂ) * Complex.I) * (fejerKernel T (x - u) : ℂ)‖ ≤
        ∫ u in Set.Iic (0 : ℝ), fejerKernel T (x - u) := by
    refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Iic fun u _ ↦ ?_
    have he1 : ‖Complex.exp ((γ : ℂ) * (u : ℂ) * Complex.I)‖ = 1 := by
      rw [show (γ : ℂ) * (u : ℂ) * Complex.I = ((γ * u : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    rw [norm_mul, he1, one_mul, Complex.norm_real, Real.norm_of_nonneg (fejerKernel_nonneg hT _)]
  have hchg : ∫ u in Set.Iic (0 : ℝ), fejerKernel T (x - u) = ∫ v in Set.Ici x, fejerKernel T v := by
    have himg : (fun u : ℝ ↦ x - u) '' Set.Iic (0 : ℝ) = Set.Ici x := by
      ext v
      simp only [Set.mem_image, Set.mem_Iic, Set.mem_Ici]
      constructor
      · rintro ⟨u, hu, rfl⟩; linarith
      · intro hv; exact ⟨x - v, by linarith, by ring⟩
    have hderiv_sub : ∀ u ∈ Set.Iic (0 : ℝ), HasDerivWithinAt (fun u : ℝ ↦ x - u) (-1) (Set.Iic 0) u := by
      intro u _
      have h : HasDerivAt (fun u : ℝ ↦ x - u) (-1) u := by
        simpa using (hasDerivAt_const u x).fun_sub (hasDerivAt_id u)
      exact h.hasDerivWithinAt
    rw [← himg, MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Iic
      hderiv_sub (fun u₁ _ u₂ _ h ↦ by linarith)]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Iic fun u _ ↦ ?_
    simp
  have htail := fejerKernel_tail_le hT hxpos
  have hlt : 2 / (Real.pi * T * x) < δ := by
    rw [div_lt_iff₀ (by positivity)]
    have hmul := mul_le_mul_of_nonneg_left hxbd (by positivity : 0 ≤ Real.pi * T * δ)
    rw [mul_div_cancel₀ _ (by positivity : Real.pi * T * δ ≠ 0)] at hmul
    linarith
  exact lt_of_le_of_lt (hnorm_le.trans (hchg ▸ htail)) hlt

lemma smooth_integral_tendsto {T : ℝ} (hT : 0 < T) {F : ℝ × ℝ → ℂ}
    (hFc : ContinuousOn F (Set.Icc (0 : ℝ) (1 / 2) ×ˢ Set.Icc (-T) T)) :
    IntervalIntegrable (fun t : ℝ ↦ F (0, t)) volume (-T) T ∧
    ∀ x : ℝ, Filter.Tendsto
      (fun ε : ℝ ↦ ∫ t in (-T)..T, F (ε, t) * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))
      (𝓝[>] (0 : ℝ))
      (nhds (∫ t in (-T)..T, F (0, t) * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))) := by
  have hK : IsCompact (Set.Icc (0 : ℝ) (1 / 2) ×ˢ Set.Icc (-T) T) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hFc
  have hF0_cont : ContinuousOn (fun t : ℝ ↦ F (0, t)) (Set.uIcc (-T) T) := by
    rw [Set.uIcc_of_le (by linarith : -T ≤ T)]
    refine hFc.comp (continuous_const.prodMk continuous_id).continuousOn ?_
    intro t ht
    exact ⟨⟨le_rfl, by norm_num⟩, ht⟩
  refine ⟨hF0_cont.intervalIntegrable, fun x ↦ ?_⟩
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ : ℝ ↦ max M 0) ?_ ?_ intervalIntegrable_const ?_
  · have hIoo : Set.Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [hIoo] with ε hε
    have hc : ContinuousOn (fun t : ℝ ↦ F (ε, t) * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))
        (Set.Icc (-T) T) := by
      have h1 : ContinuousOn (fun t : ℝ ↦ F (ε, t)) (Set.Icc (-T) T) :=
        hFc.comp (continuous_const.prodMk continuous_id).continuousOn fun t ht ↦
          ⟨⟨hε.1.le, hε.2.le⟩, ht⟩
      exact h1.mul (by fun_prop : Continuous (fun t : ℝ ↦ Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))).continuousOn
    have hu : Set.uIoc (-T) T ⊆ Set.Icc (-T) T := by
      rw [Set.uIoc_of_le (by linarith : -T ≤ T)]
      exact Set.Ioc_subset_Icc_self
    exact (hc.mono hu).aestronglyMeasurable measurableSet_uIoc
  · have hIoo : Set.Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [hIoo] with ε hε
    refine Filter.Eventually.of_forall fun t ht ↦ ?_
    rw [Set.uIoc_of_le (by linarith : -T ≤ T)] at ht
    have he1 : ‖Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)‖ = 1 := by
      rw [show (t : ℂ) * (x : ℂ) * Complex.I = ((t * x : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    rw [norm_mul, he1, mul_one]
    exact (hM (ε, t) ⟨⟨hε.1.le, hε.2.le⟩, ⟨ht.1.le, ht.2⟩⟩).trans (le_max_left M 0)
  · refine Filter.Eventually.of_forall fun t ht ↦ ?_
    rw [Set.uIoc_of_le (by linarith : -T ≤ T)] at ht
    have htIcc : t ∈ Set.Icc (-T) T := ⟨ht.1.le, ht.2⟩
    have hmap : Filter.Tendsto (fun ε : ℝ ↦ (ε, t)) (𝓝[>] (0 : ℝ))
        (𝓝[Set.Icc (0 : ℝ) (1 / 2) ×ˢ Set.Icc (-T) T] (0, t)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · exact ((continuous_id.prodMk (continuous_const (y := t))).tendsto 0).mono_left nhdsWithin_le_nhds
      · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with ε hε
        exact ⟨⟨hε.1.le, hε.2.le⟩, htIcc⟩
    have hF_lim : Filter.Tendsto (fun ε : ℝ ↦ F (ε, t)) (𝓝[>] (0 : ℝ)) (nhds (F (0, t))) :=
      (hFc (0, t) ⟨⟨le_rfl, by norm_num⟩, htIcc⟩).tendsto.comp hmap
    exact hF_lim.mul tendsto_const_nhds

lemma log_integral_tendsto {T : ℝ} (hT : 2 ≤ T) {ρ : ℂ}
    (hρB : ρ ∈ Metric.closedBall (1 / 2 : ℂ) (T + 1)) (hρre : ρ.re ≤ 1 / 2) :
    let Lterm : ℝ → ℝ → ℂ := fun ε t ↦
      ((1 - |t| / T : ℝ) : ℂ) *
        (Complex.log ((1 / 2 + (ε : ℂ)) + (t : ℂ) * Complex.I - ρ) /
          ((1 / 2 + (ε : ℂ)) + (t : ℂ) * Complex.I) ^ 2)
    IntervalIntegrable (fun t : ℝ ↦ Lterm 0 t) volume (-T) T ∧
    ∀ x : ℝ, Filter.Tendsto
      (fun ε : ℝ ↦ ∫ t in (-T)..T, Lterm ε t * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))
      (𝓝[>] (0 : ℝ))
      (nhds (∫ t in (-T)..T, Lterm 0 t * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))) := by
  intro Lterm
  have hTpos : 0 < T := by linarith
  let bound : ℝ → ℝ := fun t ↦ 4 * (|Real.log (t - ρ.im)| + Real.log (2 * T + 2) + Real.pi)
  have hbound_int : IntervalIntegrable bound volume (-T) T := by
    have hlog_int : IntervalIntegrable (fun t : ℝ ↦ |Real.log (t - ρ.im)|) volume (-T) T := by
      have h1 : IntervalIntegrable (fun u : ℝ ↦ Real.log u) volume (-T - ρ.im) (T - ρ.im) :=
        intervalIntegral.intervalIntegrable_log'
      simpa [Real.norm_eq_abs] using (h1.comp_sub_right ρ.im).norm
    exact ((hlog_int.add intervalIntegrable_const).add intervalIntegrable_const).const_mul 4
  have hLterm_bd : ∀ ε ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ t ∈ Set.Icc (-T) T, t ≠ ρ.im →
      ‖Lterm ε t‖ ≤ bound t := by
    intro ε hε t ht hne
    dsimp [Lterm, bound]
    have habs_t : |t| ≤ T := abs_le.mpr ⟨ht.1, ht.2⟩
    have htent_le : |1 - |t| / T| ≤ 1 := by
      have h1 : 0 ≤ |t| / T := by positivity
      have h2 : |t| / T ≤ 1 := (div_le_one hTpos).mpr habs_t
      rw [abs_of_nonneg (by linarith)]; linarith
    let s : ℂ := 1 / 2 + (ε : ℂ) + (t : ℂ) * Complex.I
    let z : ℂ := s - ρ
    have hs_norm : (1 / 2 : ℝ) ≤ ‖s‖ := by
      have hre : (1 / 2 : ℝ) ≤ s.re := by simp [s]; linarith [hε.1]
      exact hre.trans (Complex.re_le_norm s)
    have hs2_ge : (1 / 4 : ℝ) ≤ ‖s ^ 2‖ := by
      rw [norm_pow]; nlinarith
    have hz_upper : ‖z‖ ≤ 2 * T + 2 := by
      have h1 : z = ((ε : ℂ) + (t : ℂ) * Complex.I) + ((1 / 2 : ℂ) - ρ) := by dsimp [z, s]; ring
      rw [h1]
      have h2 : ‖(1 / 2 : ℂ) - ρ‖ ≤ T + 1 := by
        rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] at hρB
        exact hρB
      have h3 : ‖(ε : ℂ) + (t : ℂ) * Complex.I‖ ≤ 1 / 2 + T := by
        calc ‖(ε : ℂ) + (t : ℂ) * Complex.I‖
            ≤ ‖(ε : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
          _ = |ε| + |t| := by simp [Complex.norm_real, Real.norm_eq_abs]
          _ ≤ 1 / 2 + T := by linarith [abs_of_nonneg hε.1, hε.2, habs_t]
      linarith [norm_add_le ((ε : ℂ) + (t : ℂ) * Complex.I) ((1 / 2 : ℂ) - ρ)]
    have hz_lower : |t - ρ.im| ≤ ‖z‖ := by
      have him : z.im = t - ρ.im := by simp [z, s]
      rw [← him]; exact Complex.abs_im_le_norm z
    have htim_pos : 0 < |t - ρ.im| := abs_pos.mpr (sub_ne_zero.mpr hne)
    have hz_pos : 0 < ‖z‖ := htim_pos.trans_le hz_lower
    have hlog_norm : ‖Complex.log z‖ ≤ |Real.log (t - ρ.im)| + Real.log (2 * T + 2) + Real.pi := by
      have h1 : ‖Complex.log z‖ ≤ |(Complex.log z).re| + |(Complex.log z).im| :=
        Complex.norm_le_abs_re_add_abs_im (Complex.log z)
      rw [Complex.log_re, Complex.log_im] at h1
      have harg : |Complex.arg z| ≤ Real.pi := Complex.abs_arg_le_pi z
      have hlog_bd : |Real.log ‖z‖| ≤ |Real.log (t - ρ.im)| + Real.log (2 * T + 2) := by
        have hlog2T : 0 ≤ Real.log (2 * T + 2) := Real.log_nonneg (by linarith)
        by_cases hge1 : 1 ≤ ‖z‖
        · rw [abs_of_nonneg (Real.log_nonneg hge1)]
          have : Real.log ‖z‖ ≤ Real.log (2 * T + 2) := Real.log_le_log hz_pos hz_upper
          linarith [abs_nonneg (Real.log (t - ρ.im))]
        · push Not at hge1
          have hneg : Real.log ‖z‖ ≤ 0 := Real.log_nonpos hz_pos.le hge1.le
          rw [abs_of_nonpos hneg]
          have hle1 : Real.log |t - ρ.im| ≤ Real.log ‖z‖ := Real.log_le_log htim_pos hz_lower
          rw [Real.log_abs] at hle1
          have hle2 : -Real.log (t - ρ.im) ≤ |Real.log (t - ρ.im)| := neg_le_abs _
          linarith
      linarith
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs]
    have hdiv_le : ‖Complex.log z‖ / ‖s ^ 2‖ ≤ 4 * (|Real.log (t - ρ.im)| + Real.log (2 * T + 2) + Real.pi) := by
      rw [div_le_iff₀ (by linarith : 0 < ‖s ^ 2‖)]
      have hnn : 0 ≤ |Real.log (t - ρ.im)| + Real.log (2 * T + 2) + Real.pi := by
        linarith [abs_nonneg (Real.log (t - ρ.im)), Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * T + 2),
          Real.pi_pos]
      nlinarith
    exact (mul_le_of_le_one_left (by positivity) htent_le).trans hdiv_le
  have hae_ne : ∀ᵐ t : ℝ ∂volume, t ≠ ρ.im := by
    rw [MeasureTheory.ae_iff]
    simp
  have hlim_pt : ∀ t : ℝ, t ≠ ρ.im →
      Filter.Tendsto (fun ε : ℝ ↦ Lterm ε t) (𝓝[>] (0 : ℝ)) (nhds (Lterm 0 t)) := by
    intro t hne
    have hslit : (1 / 2 : ℂ) + (t : ℂ) * Complex.I - ρ ∈ Complex.slitPlane := by
      right
      simp only [Complex.sub_im, Complex.add_im, Complex.div_ofNat_im, Complex.one_im, zero_div,
        Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re,
        mul_zero, add_zero, zero_add]
      exact sub_ne_zero.mpr hne
    have hcont_log : ContinuousAt
        (fun ε : ℝ ↦ Complex.log ((1 / 2 + (ε : ℂ)) + (t : ℂ) * Complex.I - ρ)) 0 := by
      have h1 : Continuous (fun ε : ℝ ↦ (1 / 2 + (ε : ℂ)) + (t : ℂ) * Complex.I - ρ) := by fun_prop
      exact (continuousAt_clog (by simpa using hslit)).comp h1.continuousAt
    have hs0_ne : ((1 / 2 + ((0 : ℝ) : ℂ)) + (t : ℂ) * Complex.I) ^ 2 ≠ 0 := by
      apply pow_ne_zero 2
      intro h0
      have hre := congr_arg Complex.re h0
      simp at hre
    have hcont_den : ContinuousAt
        (fun ε : ℝ ↦ ((1 / 2 + (ε : ℂ)) + (t : ℂ) * Complex.I) ^ 2) 0 := by fun_prop
    have hcont_all : ContinuousAt (fun ε : ℝ ↦ Lterm ε t) 0 :=
      continuousAt_const.mul (hcont_log.div hcont_den hs0_ne)
    exact hcont_all.tendsto.mono_left nhdsWithin_le_nhds
  have hLterm_meas : ∀ ε : ℝ, 0 < ε → AEStronglyMeasurable (Lterm ε) (volume.restrict (Set.uIoc (-T) T)) := by
    intro ε hε
    have hc : Continuous (Lterm ε) := by
      refine Continuous.mul (by fun_prop) (Continuous.div ?_ (by fun_prop) ?_)
      · refine continuous_iff_continuousAt.mpr fun t ↦ ?_
        have hslit : (1 / 2 + (ε : ℂ)) + (t : ℂ) * Complex.I - ρ ∈ Complex.slitPlane := by
          left; simp; linarith
        have hlin : Continuous (fun u : ℝ ↦ (1 / 2 + (ε : ℂ)) + (u : ℂ) * Complex.I - ρ) := by fun_prop
        exact ContinuousAt.comp (g := Complex.log)
          (f := fun u : ℝ ↦ (1 / 2 + (ε : ℂ)) + (u : ℂ) * Complex.I - ρ)
          (continuousAt_clog hslit) hlin.continuousAt
      · intro t
        apply pow_ne_zero 2
        intro h0
        have hre := congr_arg Complex.re h0
        simp at hre; linarith
    exact hc.aestronglyMeasurable
  have hL0_int : IntervalIntegrable (fun t : ℝ ↦ Lterm 0 t) volume (-T) T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : -T ≤ T)]
    have hbound_Ioc : IntegrableOn bound (Set.Ioc (-T) T) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : -T ≤ T)).mp hbound_int
    have hmeas0 : AEStronglyMeasurable (fun t : ℝ ↦ Lterm 0 t) (volume.restrict (Set.Ioc (-T) T)) := by
      have hseq : ∀ n : ℕ, AEStronglyMeasurable (fun t : ℝ ↦ Lterm (1 / ((n : ℝ) + 1)) t)
          (volume.restrict (Set.Ioc (-T) T)) := fun n ↦ by
        have h := hLterm_meas (1 / ((n : ℝ) + 1)) (by positivity)
        rwa [Set.uIoc_of_le (by linarith : -T ≤ T)] at h
      refine aestronglyMeasurable_of_tendsto_ae Filter.atTop hseq ?_
      filter_upwards [ae_restrict_of_ae hae_ne] with t hne
      have hinv : Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 1)) Filter.atTop (𝓝[>] (0 : ℝ)) := by
        rw [tendsto_nhdsWithin_iff]
        exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
          Filter.Eventually.of_forall fun n ↦ show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity⟩
      exact (hlim_pt t hne).comp hinv
    refine hbound_Ioc.mono' hmeas0 ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hae_ne] with t ht hne
    exact hLterm_bd 0 ⟨le_rfl, by norm_num⟩ t ⟨ht.1.le, ht.2⟩ hne
  refine ⟨hL0_int, fun x ↦ ?_⟩
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence bound ?_ ?_ hbound_int ?_
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with ε hε
    exact (hLterm_meas ε hε.1).mul
      (by fun_prop : Continuous (fun t : ℝ ↦ Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with ε hε
    filter_upwards [hae_ne] with t hne ht
    rw [Set.uIoc_of_le (by linarith : -T ≤ T)] at ht
    have he1 : ‖Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)‖ = 1 := by
      rw [show (t : ℂ) * (x : ℂ) * Complex.I = ((t * x : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    rw [norm_mul, he1, mul_one]
    exact hLterm_bd ε ⟨hε.1.le, hε.2.le⟩ t ⟨ht.1.le, ht.2⟩ hne
  · filter_upwards [hae_ne] with t hne _
    exact (hlim_pt t hne).mul tendsto_const_nhds

lemma tendsto_fourier_interval_zero {T : ℝ} (hT : 0 < T) {F : ℝ → ℂ}
    (_hF : IntervalIntegrable F volume (-T) T) :
    Filter.Tendsto
      (fun x : ℝ ↦ ∫ t in (-T)..T, F t * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))
      Filter.atTop (nhds 0) := by
  let g : ℝ → ℂ := Set.indicator (Set.Ioc (-T) T) F
  have hrl : Filter.Tendsto (𝓕 g) (Filter.cocompact ℝ) (nhds 0) :=
    Real.zero_at_infty_fourier g
  have hscale : Filter.Tendsto (fun x : ℝ ↦ -x / (2 * Real.pi)) Filter.atTop (Filter.cocompact ℝ) := by
    have hneg : Filter.Tendsto (fun x : ℝ ↦ -x / (2 * Real.pi)) Filter.atTop Filter.atBot := by
      have h1 : Filter.Tendsto (fun x : ℝ ↦ -x) Filter.atTop Filter.atBot :=
        Filter.tendsto_neg_atTop_atBot
      exact h1.atBot_div_const (by positivity : 0 < 2 * Real.pi)
    exact hneg.mono_right _root_.atBot_le_cocompact
  refine (hrl.comp hscale).congr fun x ↦ ?_
  simp only [Function.comp_apply, Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T),
    ← MeasureTheory.integral_indicator measurableSet_Ioc]
  congr 1
  ext t
  dsimp [g]
  by_cases ht : t ∈ Set.Ioc (-T) T
  · simp only [Set.indicator_of_mem ht]
    rw [mul_comm]
    congr 2
    have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have h1 : -2 * Real.pi * t * (-x / (2 * Real.pi)) = t * x := by field_simp
    rw [h1]
    push_cast
    ring
  · simp [Set.indicator_of_notMem ht]

lemma sum_S_seg_re
    {T : ℝ} (_hT : 2 ≤ T) (S_all : Finset ℂ) (Z : Finset ℝ)
    (hS_mem : ∀ ρ ∈ S_all, ρ ∈ Metric.closedBall (1 / 2 : ℂ) (T + 1) ∧ ρ.re ≤ 1 / 2 ∧ L₄ ρ = 0)
    (hS_complete : ∀ ρ ∈ Metric.closedBall (1 / 2 : ℂ) (T + 1), L₄ ρ = 0 → ρ ∈ S_all)
    (hZ : ∀ g : ℝ, g ∈ Z ↔ 0 < g ∧ g ≤ T ∧ L₄ (1 / 2 + (g : ℂ) * Complex.I) = 0)
    (x : ℝ) :
    let S_seg := S_all.filter (fun ρ ↦ ρ.re = 1 / 2 ∧ |ρ.im| ≤ T)
    (∑ ρ ∈ S_seg,
      ((analyticOrderAt L₄ ρ).toNat : ℂ) / ρ *
        (Complex.exp ((ρ.im : ℂ) * (x : ℂ) * Complex.I) * ((1 - |ρ.im| / T : ℝ) : ℂ))).re =
      2 * ∑ g ∈ Z,
        let v : ℂ := Complex.exp ((g : ℂ) * (x : ℂ) * Complex.I)
        ((analyticOrderAt L₄ (1 / 2 + (g : ℂ) * Complex.I)).toNat : ℝ) *
          ((1 - g / T) * (v.re / 2 + g * v.im) / (1 / 4 + g ^ 2)) := by
  classical
  intro S_seg
  let fpos : ℝ → ℂ := fun g ↦ (1 / 2 : ℂ) + (g : ℂ) * Complex.I
  let fneg : ℝ → ℂ := fun g ↦ (1 / 2 : ℂ) - (g : ℂ) * Complex.I
  have hS_eq : S_seg = Z.image fpos ∪ Z.image fneg := by
    ext ρ
    simp only [S_seg, Finset.mem_filter, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨hρS, hre, him⟩
      have hL0 : L₄ ρ = 0 := (hS_mem ρ hρS).2.2
      have him_ne : ρ.im ≠ 0 := by
        intro h0
        have hρ_eq : ρ = ((1 / 2 : ℝ) : ℂ) := Complex.ext (by simpa using hre) (by simpa using h0)
        rw [hρ_eq] at hL0
        exact L₄_real_ne_zero (by norm_num : (0 : ℝ) < 1 / 2) hL0
      rcases lt_or_gt_of_ne him_ne with hlt | hgt
      · right
        refine ⟨-ρ.im, (hZ (-ρ.im)).mpr ⟨by linarith, by linarith [(abs_le.mp him).1], ?_⟩, ?_⟩
        · have hconj : (1 / 2 : ℂ) + ((-ρ.im : ℝ) : ℂ) * Complex.I = conj ρ :=
            Complex.ext (by simp [hre]) (by simp)
          rw [hconj, L₄_conj, hL0, map_zero]
        · exact Complex.ext (by simp [fneg, hre]) (by simp [fneg])
      · left
        refine ⟨ρ.im, (hZ ρ.im).mpr ⟨hgt, (abs_le.mp him).2, ?_⟩, ?_⟩
        · have heq : (1 / 2 : ℂ) + (ρ.im : ℂ) * Complex.I = ρ :=
            Complex.ext (by simp [hre]) (by simp)
          rw [heq]; exact hL0
        · exact Complex.ext (by simp [fpos, hre]) (by simp [fpos])
    · rintro (⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩)
      · obtain ⟨hg0, hgT, hL0⟩ := (hZ g).mp hg
        have hmemU : fpos g ∈ Metric.closedBall (1 / 2 : ℂ) (T + 1) := by
          rw [Metric.mem_closedBall, dist_eq_norm]
          have : fpos g - 1 / 2 = (g : ℂ) * Complex.I := by dsimp [fpos]; ring
          rw [this, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_of_nonneg hg0.le]
          linarith
        refine ⟨hS_complete _ hmemU hL0, by simp [fpos], ?_⟩
        simp [fpos, abs_of_pos hg0, hgT]
      · obtain ⟨hg0, hgT, hL0⟩ := (hZ g).mp hg
        have hL0c : L₄ (fneg g) = 0 := by
          have : fneg g = conj (fpos g) := Complex.ext (by simp [fneg, fpos]) (by simp [fneg, fpos])
          rw [this, L₄_conj, hL0, map_zero]
        have hmemU : fneg g ∈ Metric.closedBall (1 / 2 : ℂ) (T + 1) := by
          rw [Metric.mem_closedBall, dist_eq_norm]
          have : fneg g - 1 / 2 = -((g : ℂ) * Complex.I) := by dsimp [fneg]; ring
          rw [this, norm_neg, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
            Real.norm_of_nonneg hg0.le]
          linarith
        refine ⟨hS_complete _ hmemU hL0c, by simp [fneg], ?_⟩
        simp [fneg, abs_of_pos hg0, hgT]
  have hdisj : Disjoint (Z.image fpos) (Z.image fneg) := by
    rw [Finset.disjoint_left]
    intro ρ h1 h2
    obtain ⟨g1, hg1, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨g2, hg2, hEq⟩ := Finset.mem_image.mp h2
    have him := congr_arg Complex.im hEq
    simp [fpos, fneg] at him
    linarith [((hZ g1).mp hg1).1, ((hZ g2).mp hg2).1]
  have hinj_pos : Set.InjOn fpos (Z : Set ℝ) := fun a _ b _ h ↦ by
    have := congr_arg Complex.im h; simpa [fpos] using this
  have hinj_neg : Set.InjOn fneg (Z : Set ℝ) := fun a _ b _ h ↦ by
    have := congr_arg Complex.im h; simpa [fneg] using this
  rw [hS_eq, Finset.sum_union hdisj, Finset.sum_image hinj_pos, Finset.sum_image hinj_neg,
    Complex.add_re, Complex.re_sum, Complex.re_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g hg ↦ ?_
  obtain ⟨hg0, _, _⟩ := (hZ g).mp hg
  have hconj_eq : fneg g = conj (fpos g) :=
    Complex.ext (by simp [fneg, fpos]) (by simp [fneg, fpos])
  have hord_eq : (analyticOrderAt L₄ (fneg g)).toNat = (analyticOrderAt L₄ (fpos g)).toNat := by
    rw [hconj_eq, analyticOrderAt_L₄_conj]
  have hterm_conj :
      ((analyticOrderAt L₄ (fneg g)).toNat : ℂ) / fneg g *
          (Complex.exp (((fneg g).im : ℂ) * (x : ℂ) * Complex.I) * ((1 - |(fneg g).im| / T : ℝ) : ℂ)) =
      conj (((analyticOrderAt L₄ (fpos g)).toNat : ℂ) / fpos g *
          (Complex.exp (((fpos g).im : ℂ) * (x : ℂ) * Complex.I) * ((1 - |(fpos g).im| / T : ℝ) : ℂ))) := by
    rw [hord_eq, hconj_eq]
    have him1 : (fpos g).im = g := by simp [fpos]
    have him2 : (conj (fpos g)).im = -g := by simp [fpos]
    rw [him1, him2, abs_neg]
    simp only [map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_natCast, ← Complex.exp_conj]
    congr 2
    simp only [Complex.conj_I]
    push_cast
    ring
  rw [hterm_conj, Complex.conj_re, ← two_mul]
  congr 1
  -- Compute real part of m / (1/2 + i g) * (v * (1 - g/T))
  have him1 : (fpos g).im = g := by simp [fpos]
  rw [him1, abs_of_pos hg0]
  let v : ℂ := Complex.exp ((g : ℂ) * (x : ℂ) * Complex.I)
  have hden_pos : (0 : ℝ) < 1 / 4 + g ^ 2 := by positivity
  have hinv_eq : (1 : ℂ) / fpos g = ((1 / 2 : ℂ) - (g : ℂ) * Complex.I) / ((1 / 4 + g ^ 2 : ℝ) : ℂ) := by
    have hne1 : fpos g ≠ 0 := by intro h0; have := congr_arg Complex.re h0; simp [fpos] at this
    have hne2 : ((1 / 4 + g ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hden_pos.ne'
    rw [div_eq_div_iff hne1 hne2]
    dsimp [fpos]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hprod_eq :
      ((analyticOrderAt L₄ (fpos g)).toNat : ℂ) / fpos g * (v * ((1 - g / T : ℝ) : ℂ)) =
      (((analyticOrderAt L₄ (fpos g)).toNat : ℝ) * (1 - g / T) / (1 / 4 + g ^ 2) : ℝ) *
        (v * ((1 / 2 : ℂ) - (g : ℂ) * Complex.I)) := by
    rw [div_eq_mul_one_div, hinv_eq]
    push_cast
    ring
  rw [hprod_eq]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.sub_re, Complex.sub_im, Complex.div_ofNat_re, Complex.one_re,
    Complex.div_ofNat_im, Complex.one_im, zero_div, Complex.I_re, Complex.I_im, mul_zero,
    mul_one]
  dsimp only [fpos, v]
  ring

theorem pillar3_fejer_bound
    {ε_sign C : ℝ} (hε : ε_sign = 1 ∨ ε_sign = -1) (hC : 0 < C)
    (hbound : ∀ᶠ n : ℕ in Filter.atTop, -C * (Real.sqrt n / Real.log n) ≤ ε_sign * J_sum n)
    (hzf : ∀ s : ℂ, 1 / 2 < s.re → L₄ s ≠ 0)
    (ℓ : ℂ → ℂ)
    (hℓ_diff : DifferentiableOn ℂ ℓ {s : ℂ | 1 / 2 < s.re})
    (hℓ_exp : ∀ s : ℂ, 1 / 2 < s.re → Complex.exp (ℓ s) = L₄ s)
    (hℓ_int : ∀ s : ℂ, 1 / 2 < s.re →
      IntegrableOn (fun t : ℝ ↦ (J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1))
    (hℓ_eq : ∀ s : ℂ, 1 / 2 < s.re →
      ℓ s / s = ∫ t : ℝ in Set.Ioi (1 : ℝ), (J_sum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)))
    {T : ℝ} (hT : 2 ≤ T) (Z : Finset ℝ)
    (hZ : ∀ g : ℝ, g ∈ Z ↔ 0 < g ∧ g ≤ T ∧ L₄ (1 / 2 + (g : ℂ) * Complex.I) = 0)
    (δ_shift : ℝ) :
    ∀ᶠ k : ℕ in Filter.atTop,
      ε_sign * (∑ g ∈ Z,
        let v := (((Circle.exp g : Circle) ^ k : Circle) : ℂ) * (Circle.exp (g * δ_shift) : ℂ)
        ((analyticOrderAt L₄ (1 / 2 + (g : ℂ) * Complex.I)).toNat : ℝ) *
          ((1 - g / T) * (v.re / 2 + g * v.im) / (1 / 4 + g ^ 2))) ≤ C + 1 := by
  classical
  have hTpos : 0 < T := by linarith
  -- Step 1: Time-side uniform lower bound
  obtain ⟨X₀, hX₀⟩ := time_side_lower_bound hε hC hbound hℓ_int hTpos
  -- Step 2: Local zero extraction on ball (1/2) (T + 1)
  obtain ⟨S_all, ℓ_H, c₀, hS_mem, hS_complete, hℓH_diff, hℓ_decomp, hderiv_decomp⟩ :=
    extract_L₄_zeros hzf ℓ hℓ_diff hℓ_exp hT
  let S_seg : Finset ℂ := S_all.filter (fun ρ ↦ ρ.re = 1 / 2 ∧ |ρ.im| ≤ T)
  let S_off : Finset ℂ := S_all.filter (fun ρ ↦ ¬(ρ.re = 1 / 2 ∧ |ρ.im| ≤ T))
  -- Step 3: Smooth part F_sm(ε, t)
  let F_sm : ℝ × ℝ → ℂ := fun p ↦
    let s : ℂ := 1 / 2 + (p.1 : ℂ) + (p.2 : ℂ) * Complex.I
    (1 / (2 * (Real.pi : ℂ))) * ((1 - |p.2| / T : ℝ) : ℂ) *
      ((-deriv ℓ_H s - ∑ ρ ∈ S_off, ((analyticOrderAt L₄ ρ).toNat : ℂ) / (s - ρ) +
          ∑ ρ ∈ S_seg, ((analyticOrderAt L₄ ρ).toNat : ℂ) / ρ) / s +
        (c₀ + ℓ_H s) / s ^ 2)
  have hFsm_cont : ContinuousOn F_sm (Set.Icc (0 : ℝ) (1 / 2) ×ˢ Set.Icc (-T) T) := by
    let smap : ℝ × ℝ → ℂ := fun p ↦ 1 / 2 + (p.1 : ℂ) + (p.2 : ℂ) * Complex.I
    have hsmap_cont : Continuous smap := by dsimp [smap]; fun_prop
    have hsmap_ball : ∀ p ∈ Set.Icc (0 : ℝ) (1 / 2) ×ˢ Set.Icc (-T) T,
        smap p ∈ Metric.ball (1 / 2 : ℂ) (T + 1) := by
      intro p hp
      rw [Metric.mem_ball, dist_eq_norm]
      have hsub : smap p - 1 / 2 = (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by dsimp [smap]; ring
      rw [hsub]
      calc ‖(p.1 : ℂ) + (p.2 : ℂ) * Complex.I‖
          ≤ ‖(p.1 : ℂ)‖ + ‖(p.2 : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = |p.1| + |p.2| := by simp [Complex.norm_real, Real.norm_eq_abs]
        _ ≤ 1 / 2 + T := by
            have h1 : |p.1| ≤ 1 / 2 := by rw [abs_of_nonneg hp.1.1]; exact hp.1.2
            have h2 : |p.2| ≤ T := abs_le.mpr hp.2
            linarith
        _ < T + 1 := by linarith
    have hsmap_ne0 : ∀ p ∈ Set.Icc (0 : ℝ) (1 / 2) ×ˢ Set.Icc (-T) T, smap p ≠ 0 := by
      intro p hp h0
      have hre := congr_arg Complex.re h0
      simp [smap] at hre
      linarith [hp.1.1]
    have hℓH_cont : ContinuousOn (fun p ↦ ℓ_H (smap p)) (Set.Icc (0 : ℝ) (1 / 2) ×ˢ Set.Icc (-T) T) :=
      hℓH_diff.continuousOn.comp hsmap_cont.continuousOn hsmap_ball
    have hdℓH_cont : ContinuousOn (fun p ↦ deriv ℓ_H (smap p))
        (Set.Icc (0 : ℝ) (1 / 2) ×ˢ Set.Icc (-T) T) :=
      (hℓH_diff.deriv Metric.isOpen_ball).continuousOn.comp hsmap_cont.continuousOn hsmap_ball
    have hoff_cont : ContinuousOn
        (fun p ↦ ∑ ρ ∈ S_off, ((analyticOrderAt L₄ ρ).toNat : ℂ) / (smap p - ρ))
        (Set.Icc (0 : ℝ) (1 / 2) ×ˢ Set.Icc (-T) T) := by
      refine continuousOn_finsetSum _ fun ρ hρ ↦ continuousOn_const.div
        (hsmap_cont.continuousOn.sub continuousOn_const) fun p hp h0 ↦ ?_
      have hρ_mem := Finset.mem_filter.mp hρ
      have hρre : ρ.re ≤ 1 / 2 := (hS_mem ρ hρ_mem.1).2.1
      have heq_re := congr_arg Complex.re (sub_eq_zero.mp h0)
      have heq_im := congr_arg Complex.im (sub_eq_zero.mp h0)
      simp [smap] at heq_re heq_im
      have hre_eq : ρ.re = 1 / 2 := by linarith [hp.1.1]
      have him_le : |ρ.im| ≤ T := by rw [← heq_im]; exact abs_le.mpr hp.2
      exact hρ_mem.2 ⟨hre_eq, him_le⟩
    dsimp only [F_sm]
    refine ((continuousOn_const.mul (by fun_prop : Continuous _).continuousOn).mul ?_)
    refine (((hdℓH_cont.neg.sub hoff_cont).add continuousOn_const).div
      hsmap_cont.continuousOn hsmap_ne0).add ?_
    exact (continuousOn_const.add hℓH_cont).div (hsmap_cont.continuousOn.pow 2)
      (fun p hp ↦ pow_ne_zero 2 (hsmap_ne0 p hp))
  obtain ⟨hFsm_int0, hFsm_lim⟩ := smooth_integral_tendsto hTpos hFsm_cont
  -- Step 4: Log part L_term(ρ, ε, t)
  let Lterm : ℂ → ℝ → ℝ → ℂ := fun ρ ε t ↦
    ((1 - |t| / T : ℝ) : ℂ) *
      (Complex.log ((1 / 2 + (ε : ℂ)) + (t : ℂ) * Complex.I - ρ) /
        ((1 / 2 + (ε : ℂ)) + (t : ℂ) * Complex.I) ^ 2)
  have hLog_int0 : ∀ ρ ∈ S_all, IntervalIntegrable (fun t : ℝ ↦ Lterm ρ 0 t) volume (-T) T :=
    fun ρ hρ ↦ (log_integral_tendsto hT (hS_mem ρ hρ).1 (hS_mem ρ hρ).2.1).1
  have hLog_lim : ∀ ρ ∈ S_all, ∀ x : ℝ,
      Filter.Tendsto
        (fun ε : ℝ ↦ ∫ t in (-T)..T, Lterm ρ ε t * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))
        (𝓝[>] (0 : ℝ))
        (nhds (∫ t in (-T)..T, Lterm ρ 0 t * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))) :=
    fun ρ hρ x ↦ (log_integral_tendsto hT (hS_mem ρ hρ).1 (hS_mem ρ hρ).2.1).2 x
  -- Step 5: Spectral limit as ε → 0⁺ for fixed x ≥ X₀
  let E_FT : ℝ → ℂ := fun x ↦
    (∫ t in (-T)..T, F_sm (0, t) * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) +
      (1 / (2 * (Real.pi : ℂ))) *
        ∑ ρ ∈ S_all, ((analyticOrderAt L₄ ρ).toNat : ℂ) *
          ∫ t in (-T)..T, Lterm ρ 0 t * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)
  let E_tail : ℝ → ℂ := fun x ↦
    ∑ ρ ∈ S_seg, ((analyticOrderAt L₄ ρ).toNat : ℂ) / ρ *
      ∫ u in Set.Iic (0 : ℝ),
        Complex.exp ((ρ.im : ℂ) * (u : ℂ) * Complex.I) * (fejerKernel T (x - u) : ℂ)
  let MainSum : ℝ → ℂ := fun x ↦
    ∑ ρ ∈ S_seg, ((analyticOrderAt L₄ ρ).toNat : ℂ) / ρ *
      (Complex.exp ((ρ.im : ℂ) * (x : ℂ) * Complex.I) * ((1 - |ρ.im| / T : ℝ) : ℂ))
  have hspectral_lim : ∀ x : ℝ,
      Filter.Tendsto
        (fun ε : ℝ ↦
          ∫ u in Set.Ioi (0 : ℝ),
            (g_u u : ℂ) * (Real.exp (-ε * u) : ℂ) * (fejerKernel T (x - u) : ℂ))
        (𝓝[>] (0 : ℝ))
        (nhds (E_FT x - MainSum x + E_tail x)) := by
    intro x
    -- Algebraic split for ε ∈ (0, 1/2)
    have hsplit_ev :
        (fun ε : ℝ ↦
          ∫ u in Set.Ioi (0 : ℝ),
            (g_u u : ℂ) * (Real.exp (-ε * u) : ℂ) * (fejerKernel T (x - u) : ℂ)) =ᶠ[𝓝[>] (0 : ℝ)]
        fun ε : ℝ ↦
          (∫ t in (-T)..T, F_sm (ε, t) * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) +
          ((1 / (2 * (Real.pi : ℂ))) *
            ∑ ρ ∈ S_all, ((analyticOrderAt L₄ ρ).toNat : ℂ) *
              ∫ t in (-T)..T, Lterm ρ ε t * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) -
          ∑ ρ ∈ S_seg, ((analyticOrderAt L₄ ρ).toNat : ℂ) / ρ *
            ((1 / (2 * (Real.pi : ℂ))) *
              ∫ t in (-T)..T,
                ((1 - |t| / T : ℝ) : ℂ) * (1 / ((ε : ℂ) + ((t - ρ.im : ℝ) : ℂ) * Complex.I)) *
                  Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) := by
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with ε hε_ioo
      rw [← fubini_fejer_phi hzf ℓ hℓ_diff hℓ_exp hℓ_int hℓ_eq hTpos hε_ioo.1 x]
      -- Integrability of each piece on (-T)..T for fixed ε ∈ (0, 1/2)
      have hint_sm : IntervalIntegrable
          (fun t : ℝ ↦ F_sm (ε, t) * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) volume (-T) T := by
        have hc : ContinuousOn (fun t : ℝ ↦ F_sm (ε, t) * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))
            (Set.uIcc (-T) T) := by
          rw [Set.uIcc_of_le (by linarith : -T ≤ T)]
          exact (hFsm_cont.comp (continuous_const.prodMk continuous_id).continuousOn fun t ht ↦
            ⟨⟨hε_ioo.1.le, hε_ioo.2.le⟩, ht⟩).mul
            (by fun_prop : Continuous _).continuousOn
        exact hc.intervalIntegrable
      have hint_log : ∀ ρ ∈ S_all, IntervalIntegrable
          (fun t : ℝ ↦ (1 / (2 * (Real.pi : ℂ))) * (((analyticOrderAt L₄ ρ).toNat : ℂ) *
            (Lterm ρ ε t * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)))) volume (-T) T := by
        intro ρ hρ
        have hc : Continuous (fun t : ℝ ↦ Lterm ρ ε t * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) := by
          refine (Continuous.mul (by fun_prop) (Continuous.div ?_ (by fun_prop) ?_)).mul (by fun_prop)
          · refine continuous_iff_continuousAt.mpr fun t ↦ ?_
            have hslit : (1 / 2 + (ε : ℂ)) + (t : ℂ) * Complex.I - ρ ∈ Complex.slitPlane := by
              left; simp; linarith [(hS_mem ρ hρ).2.1, hε_ioo.1]
            have hlin : Continuous (fun u : ℝ ↦ (1 / 2 + (ε : ℂ)) + (u : ℂ) * Complex.I - ρ) := by fun_prop
            exact ContinuousAt.comp (g := Complex.log)
              (f := fun u : ℝ ↦ (1 / 2 + (ε : ℂ)) + (u : ℂ) * Complex.I - ρ)
              (continuousAt_clog hslit) hlin.continuousAt
          · intro t; apply pow_ne_zero 2; intro h0
            have hre := congr_arg Complex.re h0; simp at hre; linarith [hε_ioo.1]
        exact ((hc.intervalIntegrable (-T) T).const_mul _).const_mul _
      have hint_pole : ∀ ρ ∈ S_seg, IntervalIntegrable
          (fun t : ℝ ↦ ((analyticOrderAt L₄ ρ).toNat : ℂ) / ρ *
            ((1 / (2 * (Real.pi : ℂ))) *
              (((1 - |t| / T : ℝ) : ℂ) * (1 / ((ε : ℂ) + ((t - ρ.im : ℝ) : ℂ) * Complex.I)) *
                Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)))) volume (-T) T := by
        intro ρ _
        have hc : Continuous (fun t : ℝ ↦
            ((1 - |t| / T : ℝ) : ℂ) * (1 / ((ε : ℂ) + ((t - ρ.im : ℝ) : ℂ) * Complex.I)) *
              Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) := by
          refine (Continuous.mul (by fun_prop) (continuous_const.div (by fun_prop) ?_)).mul (by fun_prop)
          intro t h0; have hre := congr_arg Complex.re h0; simp at hre; linarith [hε_ioo.1]
        exact ((hc.intervalIntegrable (-T) T).const_mul _).const_mul _
      -- Combine RHS integrals into a single intervalIntegral
      have hint_log_sum : IntervalIntegrable
          (fun t : ℝ ↦ ∑ ρ ∈ S_all, (1 / (2 * (Real.pi : ℂ))) * (((analyticOrderAt L₄ ρ).toNat : ℂ) *
            (Lterm ρ ε t * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)))) volume (-T) T := by
        have heq : (fun t : ℝ ↦ ∑ ρ ∈ S_all, (1 / (2 * (Real.pi : ℂ))) *
            (((analyticOrderAt L₄ ρ).toNat : ℂ) *
              (Lterm ρ ε t * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)))) =
            ∑ ρ ∈ S_all, fun t : ℝ ↦ (1 / (2 * (Real.pi : ℂ))) *
              (((analyticOrderAt L₄ ρ).toNat : ℂ) *
                (Lterm ρ ε t * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))) := by
          ext t; simp [Finset.sum_apply]
        rw [heq]
        exact IntervalIntegrable.sum S_all hint_log
      have hint_pole_sum : IntervalIntegrable
          (fun t : ℝ ↦ ∑ ρ ∈ S_seg, ((analyticOrderAt L₄ ρ).toNat : ℂ) / ρ *
            ((1 / (2 * (Real.pi : ℂ))) *
              (((1 - |t| / T : ℝ) : ℂ) * (1 / ((ε : ℂ) + ((t - ρ.im : ℝ) : ℂ) * Complex.I)) *
                Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)))) volume (-T) T := by
        have heq : (fun t : ℝ ↦ ∑ ρ ∈ S_seg, ((analyticOrderAt L₄ ρ).toNat : ℂ) / ρ *
            ((1 / (2 * (Real.pi : ℂ))) *
              (((1 - |t| / T : ℝ) : ℂ) * (1 / ((ε : ℂ) + ((t - ρ.im : ℝ) : ℂ) * Complex.I)) *
                Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)))) =
            ∑ ρ ∈ S_seg, fun t : ℝ ↦ ((analyticOrderAt L₄ ρ).toNat : ℂ) / ρ *
              ((1 / (2 * (Real.pi : ℂ))) *
                (((1 - |t| / T : ℝ) : ℂ) * (1 / ((ε : ℂ) + ((t - ρ.im : ℝ) : ℂ) * Complex.I)) *
                  Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))) := by
          ext t; simp [Finset.sum_apply]
        rw [heq]
        exact IntervalIntegrable.sum S_seg hint_pole
      have hlog_comb :
          (1 / (2 * (Real.pi : ℂ))) *
            ∑ ρ ∈ S_all, ((analyticOrderAt L₄ ρ).toNat : ℂ) *
              ∫ t in (-T)..T, Lterm ρ ε t * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) =
          ∫ t in (-T)..T,
            ∑ ρ ∈ S_all, (1 / (2 * (Real.pi : ℂ))) * (((analyticOrderAt L₄ ρ).toNat : ℂ) *
              (Lterm ρ ε t * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))) := by
        rw [intervalIntegral.integral_finsetSum hint_log, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ρ _ ↦ ?_
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      have hpole_comb :
          ∑ ρ ∈ S_seg, ((analyticOrderAt L₄ ρ).toNat : ℂ) / ρ *
            ((1 / (2 * (Real.pi : ℂ))) *
              ∫ t in (-T)..T,
                ((1 - |t| / T : ℝ) : ℂ) * (1 / ((ε : ℂ) + ((t - ρ.im : ℝ) : ℂ) * Complex.I)) *
                  Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) =
          ∫ t in (-T)..T,
            ∑ ρ ∈ S_seg, ((analyticOrderAt L₄ ρ).toNat : ℂ) / ρ *
              ((1 / (2 * (Real.pi : ℂ))) *
                (((1 - |t| / T : ℝ) : ℂ) * (1 / ((ε : ℂ) + ((t - ρ.im : ℝ) : ℂ) * Complex.I)) *
                  Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))) := by
        rw [intervalIntegral.integral_finsetSum hint_pole]
        refine Finset.sum_congr rfl fun ρ _ ↦ ?_
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      rw [hlog_comb, hpole_comb, ← intervalIntegral.integral_add hint_sm hint_log_sum,
        ← intervalIntegral.integral_sub (hint_sm.add hint_log_sum) hint_pole_sum,
        ← intervalIntegral.integral_const_mul]
      -- Now match integrands pointwise on [-T, T]
      refine intervalIntegral.integral_congr fun t ht ↦ ?_
      rw [Set.uIcc_of_le (by linarith : -T ≤ T)] at ht
      let s : ℂ := 1 / 2 + (ε : ℂ) + (t : ℂ) * Complex.I
      have hsB : s ∈ Metric.ball (1 / 2 : ℂ) (T + 1) := by
        rw [Metric.mem_ball, dist_eq_norm]
        have hsub : s - 1 / 2 = (ε : ℂ) + (t : ℂ) * Complex.I := by dsimp [s]; ring
        rw [hsub]
        calc ‖(ε : ℂ) + (t : ℂ) * Complex.I‖
            ≤ ‖(ε : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
          _ = |ε| + |t| := by simp [Complex.norm_real, Real.norm_eq_abs]
          _ ≤ 1 / 2 + T := by
              rw [abs_of_pos hε_ioo.1]
              linarith [hε_ioo.2, abs_le.mpr ht]
          _ < T + 1 := by linarith
      have hsre : 1 / 2 < s.re := by simp [s]; linarith [hε_ioo.1]
      have hs0 : s ≠ 0 := by intro h0; have := congr_arg Complex.re h0; simp [s] at this; linarith [hε_ioo.1]
      have hℓs := hℓ_decomp s hsB hsre
      have hds := hderiv_decomp s hsB hsre
      -- Split ∑_{S_all} = ∑_{S_seg} + ∑_{S_off}
      have hsum_split :
          ∑ ρ ∈ S_all, ((analyticOrderAt L₄ ρ).toNat : ℂ) / (s - ρ) =
          (∑ ρ ∈ S_seg, ((analyticOrderAt L₄ ρ).toNat : ℂ) / (s - ρ)) +
          (∑ ρ ∈ S_off, ((analyticOrderAt L₄ ρ).toNat : ℂ) / (s - ρ)) := by
        simpa [S_seg, S_off] using (Finset.sum_filter_add_sum_filter_not S_all
          (fun ρ ↦ ρ.re = 1 / 2 ∧ |ρ.im| ≤ T)
          (fun ρ ↦ ((analyticOrderAt L₄ ρ).toNat : ℂ) / (s - ρ))).symm
      -- Partial fractions for each ρ ∈ S_seg
      have hpf :
          (∑ ρ ∈ S_seg, ((analyticOrderAt L₄ ρ).toNat : ℂ) / (s - ρ)) / s =
          (∑ ρ ∈ S_seg, ((analyticOrderAt L₄ ρ).toNat : ℂ) / ρ *
              (1 / ((ε : ℂ) + ((t - ρ.im : ℝ) : ℂ) * Complex.I))) -
          (∑ ρ ∈ S_seg, ((analyticOrderAt L₄ ρ).toNat : ℂ) / ρ) / s := by
        rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
        have hρ_re : ρ.re = 1 / 2 := (Finset.mem_filter.mp hρ).2.1
        have hρ0 : ρ ≠ 0 := by intro h0; rw [h0] at hρ_re; simp at hρ_re
        have hsρ_eq : s - ρ = (ε : ℂ) + ((t - ρ.im : ℝ) : ℂ) * Complex.I := by
          apply Complex.ext <;> simp [s, hρ_re]
        have hsρ0 : s - ρ ≠ 0 := by
          intro h0; have := congr_arg Complex.re h0; rw [hsρ_eq] at this; simp at this; linarith [hε_ioo.1]
        rw [← hsρ_eq]
        field_simp
        ring
      -- Assemble algebra
      have hphi_eq :
          -(deriv L₄ s / L₄ s) / s + ℓ s / s ^ 2 =
          ((-deriv ℓ_H s - ∑ ρ ∈ S_off, ((analyticOrderAt L₄ ρ).toNat : ℂ) / (s - ρ) +
              ∑ ρ ∈ S_seg, ((analyticOrderAt L₄ ρ).toNat : ℂ) / ρ) / s +
            (c₀ + ℓ_H s) / s ^ 2) +
          (∑ ρ ∈ S_all, ((analyticOrderAt L₄ ρ).toNat : ℂ) * Complex.log (s - ρ)) / s ^ 2 -
          ∑ ρ ∈ S_seg, ((analyticOrderAt L₄ ρ).toNat : ℂ) / ρ *
            (1 / ((ε : ℂ) + ((t - ρ.im : ℝ) : ℂ) * Complex.I)) := by
        rw [hds, hℓs, hsum_split]
        linear_combination -hpf
      dsimp only [F_sm, Lterm]
      change (1 / (2 * (Real.pi : ℂ))) *
          (((1 - |t| / T : ℝ) : ℂ) * (-(deriv L₄ s / L₄ s) / s + ℓ s / s ^ 2) *
            Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) = _
      rw [hphi_eq]
      have hlog_alg :
          ∑ ρ ∈ S_all, (1 / (2 * (Real.pi : ℂ))) * (((analyticOrderAt L₄ ρ).toNat : ℂ) *
            (((1 - |t| / T : ℝ) : ℂ) * (Complex.log (s - ρ) / s ^ 2) *
              Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))) =
          (1 / (2 * (Real.pi : ℂ))) * (((1 - |t| / T : ℝ) : ℂ) *
            ((∑ ρ ∈ S_all, ((analyticOrderAt L₄ ρ).toNat : ℂ) * Complex.log (s - ρ)) / s ^ 2) *
            Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) := by
        rw [Finset.sum_div, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ρ _ ↦ ?_
        ring
      have hpole_alg :
          ∑ ρ ∈ S_seg, ((analyticOrderAt L₄ ρ).toNat : ℂ) / ρ *
            ((1 / (2 * (Real.pi : ℂ))) *
              (((1 - |t| / T : ℝ) : ℂ) * (1 / ((ε : ℂ) + ((t - ρ.im : ℝ) : ℂ) * Complex.I)) *
                Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))) =
          (1 / (2 * (Real.pi : ℂ))) * (((1 - |t| / T : ℝ) : ℂ) *
            (∑ ρ ∈ S_seg, ((analyticOrderAt L₄ ρ).toNat : ℂ) / ρ *
              (1 / ((ε : ℂ) + ((t - ρ.im : ℝ) : ℂ) * Complex.I))) *
            Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) := by
        rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ρ _ ↦ ?_
        ring
      rw [hlog_alg, hpole_alg]
      ring
    rw [Filter.tendsto_congr' hsplit_ev]
    -- Take limit as ε → 0⁺ of each of the 3 pieces
    have hlim1 := hFsm_lim x
    have hlim2 :
        Filter.Tendsto
          (fun ε : ℝ ↦ (1 / (2 * (Real.pi : ℂ))) *
            ∑ ρ ∈ S_all, ((analyticOrderAt L₄ ρ).toNat : ℂ) *
              ∫ t in (-T)..T, Lterm ρ ε t * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))
          (𝓝[>] (0 : ℝ))
          (nhds ((1 / (2 * (Real.pi : ℂ))) *
            ∑ ρ ∈ S_all, ((analyticOrderAt L₄ ρ).toNat : ℂ) *
              ∫ t in (-T)..T, Lterm ρ 0 t * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))) := by
      refine tendsto_const_nhds.mul (tendsto_finsetSum _ fun ρ hρ ↦ tendsto_const_nhds.mul ?_)
      exact hLog_lim ρ hρ x
    have hlim3 :
        Filter.Tendsto
          (fun ε : ℝ ↦
            ∑ ρ ∈ S_seg, ((analyticOrderAt L₄ ρ).toNat : ℂ) / ρ *
              ((1 / (2 * (Real.pi : ℂ))) *
                ∫ t in (-T)..T,
                  ((1 - |t| / T : ℝ) : ℂ) * (1 / ((ε : ℂ) + ((t - ρ.im : ℝ) : ℂ) * Complex.I)) *
                    Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)))
          (𝓝[>] (0 : ℝ))
          (nhds (MainSum x - E_tail x)) := by
      have heq_sub : MainSum x - E_tail x =
          ∑ ρ ∈ S_seg, ((analyticOrderAt L₄ ρ).toNat : ℂ) / ρ *
            (Complex.exp ((ρ.im : ℂ) * (x : ℂ) * Complex.I) * ((1 - |ρ.im| / T : ℝ) : ℂ) -
              ∫ u in Set.Iic (0 : ℝ),
                Complex.exp ((ρ.im : ℂ) * (u : ℂ) * Complex.I) * (fejerKernel T (x - u) : ℂ)) := by
        dsimp [MainSum, E_tail]
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun ρ _ ↦ by ring
      rw [heq_sub]
      refine tendsto_finsetSum _ fun ρ hρ ↦ tendsto_const_nhds.mul ?_
      exact pole_integral_tendsto hTpos (Finset.mem_filter.mp hρ).2.2 x
    have htot := (hlim1.add hlim2).sub hlim3
    have hlim_eq :
        ((∫ t in (-T)..T, F_sm (0, t) * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) +
          (1 / (2 * (Real.pi : ℂ))) *
            ∑ ρ ∈ S_all, ((analyticOrderAt L₄ ρ).toNat : ℂ) *
              ∫ t in (-T)..T, Lterm ρ 0 t * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) -
          (MainSum x - E_tail x) = E_FT x - MainSum x + E_tail x := by
      dsimp [E_FT]
      ring
    rwa [hlim_eq] at htot
  -- Step 6: Pass ε → 0⁺ into the uniform lower bound for all x ≥ X₀
  have hineq_x : ∀ x : ℝ, X₀ ≤ x →
      -(C + 1 / 5) ≤ ε_sign * (E_FT x - MainSum x + E_tail x).re := by
    intro x hx
    have hlim_re :
        Filter.Tendsto
          (fun ε : ℝ ↦
            ε_sign * (∫ u in Set.Ioi (0 : ℝ),
              (g_u u : ℂ) * (Real.exp (-ε * u) : ℂ) * (fejerKernel T (x - u) : ℂ)).re)
          (𝓝[>] (0 : ℝ))
          (nhds (ε_sign * (E_FT x - MainSum x + E_tail x).re)) :=
      tendsto_const_nhds.mul ((Complex.continuous_re.tendsto _).comp (hspectral_lim x))
    have hge_ev : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        -(C + 1 / 5) ≤
          ε_sign * (∫ u in Set.Ioi (0 : ℝ),
            (g_u u : ℂ) * (Real.exp (-ε * u) : ℂ) * (fejerKernel T (x - u) : ℂ)).re := by
      filter_upwards [self_mem_nhdsWithin] with ε hε_pos
      exact hX₀ x hx ε hε_pos
    exact ge_of_tendsto hlim_re hge_ev
  -- Step 7: Show E_FT x + E_tail x → 0 as x → ∞
  have hEFT_lim : Filter.Tendsto E_FT Filter.atTop (nhds 0) := by
    have h1 := tendsto_fourier_interval_zero hTpos hFsm_int0
    have h2 : Filter.Tendsto
        (fun x : ℝ ↦ (1 / (2 * (Real.pi : ℂ))) *
          ∑ ρ ∈ S_all, ((analyticOrderAt L₄ ρ).toNat : ℂ) *
            ∫ t in (-T)..T, Lterm ρ 0 t * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))
        Filter.atTop (nhds 0) := by
      have hs : Filter.Tendsto
          (fun x : ℝ ↦ ∑ ρ ∈ S_all, ((analyticOrderAt L₄ ρ).toNat : ℂ) *
            ∫ t in (-T)..T, Lterm ρ 0 t * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))
          Filter.atTop (nhds 0) := by
        have hsum0 : (0 : ℂ) = ∑ _ρ ∈ S_all, (0 : ℂ) := by simp
        rw [hsum0]
        refine tendsto_finsetSum S_all fun ρ hρ ↦ ?_
        have hterm := (tendsto_const_nhds (x := ((analyticOrderAt L₄ ρ).toNat : ℂ))).mul
          (tendsto_fourier_interval_zero hTpos (hLog_int0 ρ hρ))
        simpa using hterm
      have hmul := (tendsto_const_nhds (x := (1 / (2 * (Real.pi : ℂ))))).mul hs
      simpa using hmul
    simpa [E_FT] using h1.add h2
  have hEtail_lim : Filter.Tendsto E_tail Filter.atTop (nhds 0) := by
    have hsum0 : (0 : ℂ) = ∑ _ρ ∈ S_seg, (0 : ℂ) := by simp
    dsimp [E_tail]
    rw [hsum0]
    refine tendsto_finsetSum S_seg fun ρ _ ↦ ?_
    have hterm := (tendsto_const_nhds (x := ((analyticOrderAt L₄ ρ).toNat : ℂ) / ρ)).mul
      (tendsto_pole_tail_zero hTpos ρ.im)
    simpa using hterm
  have herr_lim : Filter.Tendsto (fun x : ℝ ↦ E_FT x + E_tail x) Filter.atTop (nhds 0) := by
    simpa using hEFT_lim.add hEtail_lim
  obtain ⟨X₁, hX₁⟩ := (Metric.tendsto_atTop.mp herr_lim) (1 / 5) (by norm_num)
  -- Step 8: Specialize to x = k + δ_shift for sufficiently large k : ℕ
  have hev_k : ∀ᶠ k : ℕ in Filter.atTop, max X₀ X₁ ≤ (k : ℝ) + δ_shift := by
    have hten : Filter.Tendsto (fun k : ℕ ↦ (k : ℝ) + δ_shift) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    exact hten.eventually (Filter.eventually_ge_atTop (max X₀ X₁))
  filter_upwards [hev_k] with k hk
  let x : ℝ := (k : ℝ) + δ_shift
  have hx0 : X₀ ≤ x := (le_max_left _ _).trans hk
  have hx1 : X₁ ≤ x := (le_max_right _ _).trans hk
  have hin := hineq_x x hx0
  have herr_small : ‖E_FT x + E_tail x‖ < 1 / 5 := by
    simpa [dist_zero_right] using hX₁ x hx1
  have herr_re : |ε_sign * (E_FT x + E_tail x).re| < 1 / 5 := by
    have hε1 : |ε_sign| = 1 := by rcases hε with rfl | rfl <;> norm_num
    rw [abs_mul, hε1, one_mul]
    exact lt_of_le_of_lt (Complex.abs_re_le_norm _) herr_small
  have hre_split : (E_FT x - MainSum x + E_tail x).re = (E_FT x + E_tail x).re - (MainSum x).re := by
    simp; ring
  rw [hre_split] at hin
  have hmain_eq := sum_S_seg_re hT S_all Z hS_mem hS_complete hZ x
  have hv_eq : ∀ g : ℝ,
      (((Circle.exp g : Circle) ^ k : Circle) : ℂ) * (Circle.exp (g * δ_shift) : ℂ) =
        Complex.exp ((g : ℂ) * (x : ℂ) * Complex.I) := by
    intro g
    rw [Circle.coe_pow, Circle.coe_exp, Circle.coe_exp, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    dsimp [x]
    push_cast
    ring
  have hS_eq :
      (∑ g ∈ Z,
        let v := (((Circle.exp g : Circle) ^ k : Circle) : ℂ) * (Circle.exp (g * δ_shift) : ℂ)
        ((analyticOrderAt L₄ (1 / 2 + (g : ℂ) * Complex.I)).toNat : ℝ) *
          ((1 - g / T) * (v.re / 2 + g * v.im) / (1 / 4 + g ^ 2))) =
      (MainSum x).re / 2 := by
    have h1 : (MainSum x).re = 2 * ∑ g ∈ Z,
        let v := (((Circle.exp g : Circle) ^ k : Circle) : ℂ) * (Circle.exp (g * δ_shift) : ℂ)
        ((analyticOrderAt L₄ (1 / 2 + (g : ℂ) * Complex.I)).toNat : ℝ) *
          ((1 - g / T) * (v.re / 2 + g * v.im) / (1 / 4 + g ^ 2)) := by
      rw [hmain_eq]
      congr 1
      refine Finset.sum_congr rfl fun g _ ↦ ?_
      dsimp only
      rw [hv_eq g]
    linarith
  rw [hS_eq]
  have herr_ub : ε_sign * (E_FT x + E_tail x).re < 1 / 5 := (abs_lt.mp herr_re).2
  linarith


/- Section 5: Unified contradiction (both signs) + prime-power reduction + final theorem -/

lemma trig_sin_bound {g T : ℝ} (hg : 0 < g) (hT : 0 < T) (hle : g ≤ T) :
    0 ≤ (1 - g / T) * (g * Real.sin (g / T)) / (1 / 4 + g ^ 2) ∧
    (1 ≤ g → g ≤ T / 2 →
      1 / (8 * T) ≤ (1 - g / T) * (g * Real.sin (g / T)) / (1 / 4 + g ^ 2)) := by
  have h0 : 0 ≤ g / T := div_nonneg hg.le hT.le
  have h1 : g / T ≤ 1 := (div_le_one hT).mpr hle
  have hp : g / T ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hsin : (g / T) / 2 ≤ Real.sin (g / T) := by
    have hcoef : (1 : ℝ) / 2 ≤ 2 / Real.pi :=
      (le_div_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_lt_four])
    exact (show (g / T) / 2 ≤ 2 / Real.pi * (g / T) by
      nlinarith [mul_le_mul_of_nonneg_right hcoef h0]).trans (Real.mul_le_sin h0 hp)
  have hden : 0 < (1 : ℝ) / 4 + g ^ 2 := by positivity
  have hsin_nn : 0 ≤ Real.sin (g / T) := by linarith
  refine ⟨div_nonneg (mul_nonneg (by linarith) (mul_nonneg hg.le hsin_nn)) hden.le, ?_⟩
  intro hg1 hhalf
  apply (le_div_iff₀ hden).mpr
  calc 1 / (8 * T) * (1 / 4 + g ^ 2)
      ≤ (1 / 2) * (g * ((g / T) / 2)) := by
        field_simp
        nlinarith [sq_nonneg (g - 1)]
    _ ≤ (1 - g / T) * (g * Real.sin (g / T)) := by
        apply mul_le_mul _ _ (by positivity) (by linarith)
        · have ht : g / T ≤ 1 / 2 := (div_le_iff₀ hT).mpr (by linarith)
          linarith
        · exact mul_le_mul_of_nonneg_left hsin hg.le

theorem unified_contradiction {ε_sign C : ℝ} (hε : ε_sign = 1 ∨ ε_sign = -1) (hC : 0 < C)
    (hbound : ∀ᶠ n : ℕ in Filter.atTop, -C * (Real.sqrt n / Real.log n) ≤ ε_sign * J_sum n) :
    False := by
  classical
  have hε_sq : ε_sign * ε_sign = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hε_abs : |ε_sign| = 1 := by rcases hε with rfl | rfl <;> norm_num
  obtain ⟨hzf, ℓ, hℓ_diff, hℓ_exp, hℓ_int, hℓ_eq⟩ := pillar1_landau hε hC hbound
  obtain ⟨C_sum, hCsum⟩ := pillar2_zero_sum_bound hzf
  let C_sum' : ℝ := max C_sum 0
  let A : ℝ := 8 * (C + 2 + C_sum' / 2)
  obtain ⟨T, Z, hT, hZ, hmass⟩ := pillar2_zero_count_lower hzf A
  have hTpos : 0 < T := by linarith
  let δ_shift : ℝ := ε_sign / T
  let w : ℝ → ℝ := fun g ↦ ((analyticOrderAt L₄ (1 / 2 + (g : ℂ) * Complex.I)).toNat : ℝ)
  let phase : (ℝ → Circle) → ℝ := fun z ↦
    ε_sign * ∑ g ∈ Z,
      let v := (z g : ℂ) * (Circle.exp (g * δ_shift) : ℂ)
      w g * ((1 - g / T) * (v.re / 2 + g * v.im) / (1 / 4 + g ^ 2))
  have hc : Continuous phase := by dsimp only [phase]; fun_prop
  have hatOne : C + 1 < phase 1 := by
    have hr (r : ℝ) : (Circle.exp r : ℂ).re = Real.cos r := Complex.exp_ofReal_mul_I_re r
    have hi (r : ℝ) : (Circle.exp r : ℂ).im = Real.sin r := Complex.exp_ofReal_mul_I_im r
    have hphase1 : phase 1 = ∑ g ∈ Z,
        w g * ((1 - g / T) * (g * Real.sin (g / T) + ε_sign * Real.cos (g / T) / 2) /
          (1 / 4 + g ^ 2)) := by
      dsimp only [phase]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun g _ ↦ ?_
      simp only [Pi.one_apply, Circle.coe_one, one_mul, hr, hi]
      have hcos : Real.cos (g * δ_shift) = Real.cos (g / T) := by
        dsimp [δ_shift]
        rcases hε with rfl | rfl
        · congr 1; ring
        · rw [show g * (-1 / T) = -(g / T) by ring, Real.cos_neg]
      have hsin : Real.sin (g * δ_shift) = ε_sign * Real.sin (g / T) := by
        dsimp [δ_shift]
        rcases hε with rfl | rfl
        · rw [one_mul]; congr 1; ring
        · rw [show g * (-1 / T) = -(g / T) by ring, Real.sin_neg]; ring
      rw [hcos, hsin]
      have hlin : ε_sign * (Real.cos (g / T) / 2 + g * (ε_sign * Real.sin (g / T))) =
          g * Real.sin (g / T) + ε_sign * Real.cos (g / T) / 2 := by
        calc ε_sign * (Real.cos (g / T) / 2 + g * (ε_sign * Real.sin (g / T)))
            = (ε_sign * ε_sign) * (g * Real.sin (g / T)) + ε_sign * Real.cos (g / T) / 2 := by ring
          _ = g * Real.sin (g / T) + ε_sign * Real.cos (g / T) / 2 := by rw [hε_sq, one_mul]
      calc ε_sign * (w g * ((1 - g / T) * (Real.cos (g / T) / 2 + g * (ε_sign * Real.sin (g / T))) /
              (1 / 4 + g ^ 2)))
          = w g * ((1 - g / T) * (ε_sign * (Real.cos (g / T) / 2 + g * (ε_sign * Real.sin (g / T)))) /
              (1 / 4 + g ^ 2)) := by ring
        _ = w g * ((1 - g / T) * (g * Real.sin (g / T) + ε_sign * Real.cos (g / T) / 2) /
              (1 / 4 + g ^ 2)) := by rw [hlin]
    rw [hphase1]
    have hpt : ∀ g ∈ Z,
        w g * ((1 - g / T) * (g * Real.sin (g / T)) / (1 / 4 + g ^ 2)) -
          (1 / 2) * (w g / (1 / 4 + g ^ 2)) ≤
        w g * ((1 - g / T) * (g * Real.sin (g / T) + ε_sign * Real.cos (g / T) / 2) /
          (1 / 4 + g ^ 2)) := by
      intro g hg
      obtain ⟨hg0, hgle, _⟩ := (hZ g).mp hg
      have hw_nn : 0 ≤ w g := by dsimp [w]; positivity
      have hden_pos : 0 < (1 : ℝ) / 4 + g ^ 2 := by positivity
      have h1_nn : 0 ≤ 1 - g / T := sub_nonneg.mpr ((div_le_one hTpos).mpr hgle)
      have h1_le : 1 - g / T ≤ 1 := by linarith [div_nonneg hg0.le hTpos.le]
      have hcos_ge : -1 / 2 ≤ ε_sign * Real.cos (g / T) / 2 := by
        have h1 : |ε_sign * Real.cos (g / T)| ≤ 1 := by
          rw [abs_mul, hε_abs, one_mul]; exact Real.abs_cos_le_one _
        linarith [(abs_le.mp h1).1]
      have hterm_ge : -(1 / 2 : ℝ) ≤ (1 - g / T) * (ε_sign * Real.cos (g / T) / 2) := by
        calc -(1 / 2 : ℝ)
            ≤ (1 - g / T) * (-1 / 2) := by nlinarith
          _ ≤ (1 - g / T) * (ε_sign * Real.cos (g / T) / 2) :=
              mul_le_mul_of_nonneg_left hcos_ge h1_nn
      have hdiv_ge := div_le_div_of_nonneg_right hterm_ge hden_pos.le
      have hmul_ge := mul_le_mul_of_nonneg_left hdiv_ge hw_nn
      have halg :
          w g * ((1 - g / T) * (g * Real.sin (g / T) + ε_sign * Real.cos (g / T) / 2) /
            (1 / 4 + g ^ 2)) =
          w g * ((1 - g / T) * (g * Real.sin (g / T)) / (1 / 4 + g ^ 2)) +
          w g * ((1 - g / T) * (ε_sign * Real.cos (g / T) / 2) / (1 / 4 + g ^ 2)) := by ring
      rw [halg]
      have hneg_alg : -(1 / 2) * (w g / (1 / 4 + g ^ 2)) = w g * (-(1 / 2) / (1 / 4 + g ^ 2)) := by ring
      linarith
    have hsum_ge :
        (∑ g ∈ Z, w g * ((1 - g / T) * (g * Real.sin (g / T)) / (1 / 4 + g ^ 2))) -
          (1 / 2) * (∑ g ∈ Z, w g / (1 / 4 + g ^ 2)) ≤
        ∑ g ∈ Z, w g * ((1 - g / T) * (g * Real.sin (g / T) + ε_sign * Real.cos (g / T) / 2) /
          (1 / 4 + g ^ 2)) := by
      have h1 := Finset.sum_le_sum hpt
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at h1
      exact h1
    let Z_mid : Finset ℝ := Z.filter (fun g ↦ 1 ≤ g ∧ g ≤ T / 2)
    have hpos_ge : (∑ g ∈ Z_mid, w g) / (8 * T) ≤
        ∑ g ∈ Z, w g * ((1 - g / T) * (g * Real.sin (g / T)) / (1 / 4 + g ^ 2)) := by
      have h1 : (∑ g ∈ Z_mid, w g) / (8 * T) ≤
          ∑ g ∈ Z_mid, w g * ((1 - g / T) * (g * Real.sin (g / T)) / (1 / 4 + g ^ 2)) := by
        rw [Finset.sum_div]
        refine Finset.sum_le_sum fun g hg ↦ ?_
        obtain ⟨hgZ, hg1, hg2⟩ := Finset.mem_filter.mp hg
        obtain ⟨hg0, hgle, _⟩ := (hZ g).mp hgZ
        have hh := (trig_sin_bound hg0 hTpos hgle).2 hg1 hg2
        simpa only [div_eq_mul_inv, one_mul] using
          mul_le_mul_of_nonneg_left hh (by dsimp [w]; positivity : 0 ≤ w g)
      have h2 : ∑ g ∈ Z_mid, w g * ((1 - g / T) * (g * Real.sin (g / T)) / (1 / 4 + g ^ 2)) ≤
          ∑ g ∈ Z, w g * ((1 - g / T) * (g * Real.sin (g / T)) / (1 / 4 + g ^ 2)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro g hg _
        obtain ⟨hg0, hgle, _⟩ := (hZ g).mp hg
        exact mul_nonneg (by dsimp [w]; positivity) (trig_sin_bound hg0 hTpos hgle).1
      exact h1.trans h2
    have hneg_le : ∑ g ∈ Z, w g / (1 / 4 + g ^ 2) ≤ C_sum' :=
      (hCsum T Z hT hZ).trans (le_max_left _ _)
    have hmass_div : C + 2 + C_sum' / 2 < (∑ g ∈ Z_mid, w g) / (8 * T) := by
      rw [lt_div_iff₀ (by positivity : 0 < 8 * T)]
      dsimp [A, Z_mid, w] at hmass ⊢
      linarith
    linarith
  let a : ℝ → Circle := fun g ↦ Circle.exp g
  have hrec := mapClusterPt_one_atTop_pow a
  have hnear : {z : ℝ → Circle | C + 1 < phase z} ∈ 𝓝 (1 : ℝ → Circle) :=
    hc.continuousAt.eventually (lt_mem_nhds hatOne)
  have hoften := (mapClusterPt_iff_frequently.mp hrec) _ hnear
  have htail := pillar3_fejer_bound hε hC hbound hzf ℓ hℓ_diff hℓ_exp hℓ_int hℓ_eq hT Z hZ δ_shift
  obtain ⟨k, hlo, hhi⟩ := (hoften.and_eventually htail).exists
  have hphase_eq : phase (a ^ k) =
      ε_sign * ∑ g ∈ Z,
        let v := (((Circle.exp g : Circle) ^ k : Circle) : ℂ) * (Circle.exp (g * δ_shift) : ℂ)
        ((analyticOrderAt L₄ (1 / 2 + (g : ℂ) * Complex.I)).toNat : ℝ) *
          ((1 - g / T) * (v.re / 2 + g * v.im) / (1 / 4 + g ^ 2)) := by
    dsimp only [phase, a, w]
    simp only [Pi.pow_apply]
  change C + 1 < phase (a ^ k) at hlo
  rw [hphase_eq] at hlo
  exact not_lt_of_ge hhi hlo

lemma weighted_prime_power_race (n : ℕ) :
    let oddSquares := (Nat.primesLE n.sqrt).filter (fun p ↦ p % 2 = 1)
    |J_sum n - ((n.primeCountingMod 4 1 : ℝ) - n.primeCountingMod 4 3) - (oddSquares.card : ℝ) / 2|
      ≤ (⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ : ℝ) * (Nat.log 2 n : ℝ) := by
  let S (a : ℕ) := (Nat.primesLE n).filter fun p ↦ p ^ a ≤ n
  let w (a : ℕ) := ∑ p ∈ S a, (ZMod.χ₄ (p : ZMod 4) : ℝ) ^ a / a
  let L := Nat.log 2 n
  let U := (Nat.primesLE n.sqrt).filter fun p ↦ p % 2 = 1
  let R := ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊
  change |(∑ j ∈ Finset.range L, w (j + 1)) -
    ((n.primeCountingMod 4 1 : ℝ) - n.primeCountingMod 4 3) - (U.card : ℝ) / 2| ≤ (R : ℝ) * L
  have hχ (p : ℕ) : (ZMod.χ₄ (p : ZMod 4) : ℝ) =
      (if p % 4 = 1 then 1 else 0) - (if p % 4 = 3 then 1 else 0) := by
    rw [ZMod.χ₄_nat_eq_if_mod_four]
    split_ifs <;> norm_num <;> omega
  have hcount (r : ℕ) : (n.primeCountingMod 4 (r : ZMod 4) : ℝ) =
      ∑ p ∈ Nat.primesLE n, if p % 4 = r % 4 then 1 else 0 := by
    rw [Nat.primeCountingMod_natCast_eq_card_filter_mod,
      Nat.primesLE_eq_filter_Icc_one, Finset.sum_boole, Finset.filter_filter]
  have h₁ : w 1 = (n.primeCountingMod 4 1 : ℝ) - n.primeCountingMod 4 3 := by
    have hs : S 1 = Nat.primesLE n := by
      ext p
      simp [S, Nat.mem_primesLE]
      tauto
    have hc₁ := hcount 1
    have hc₃ := hcount 3
    norm_num at hc₁ hc₃
    simp only [w, hs, pow_one, Nat.cast_one, div_one, hχ, Finset.sum_sub_distrib]
    rw [hc₁, hc₃]
    simp
  have h₂ : w 2 = (U.card : ℝ) / 2 := by
    have hs : S 2 = Nat.primesLE n.sqrt := by
      ext p
      simp only [S, Finset.mem_filter, Nat.mem_primesLE, Nat.le_sqrt']
      constructor
      · rintro ⟨⟨_, hprime⟩, hpow⟩
        exact ⟨hpow, hprime⟩
      · rintro ⟨hpow, hprime⟩
        exact ⟨⟨(Nat.le_sqrt'.mpr hpow).trans (Nat.sqrt_le_self n), hprime⟩, hpow⟩
    dsimp only [w, U]
    rw [hs, ← Finset.sum_div]
    congr 1
    rw [← Finset.sum_boole (R := ℝ)]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [hχ]
    split_ifs <;> norm_num <;> omega
  have vanish (a : ℕ) (ha : L < a) : w a = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    obtain ⟨hp, hpow⟩ := Finset.mem_filter.mp hp
    obtain ⟨_, hprime⟩ := Nat.mem_primesLE.mp hp
    have hh := Nat.le_log_of_pow_le (by decide : 1 < 2)
      ((Nat.pow_le_pow_left hprime.two_le a).trans hpow)
    exact (not_lt_of_ge hh ha).elim
  have splitSum : (∑ j ∈ Finset.range L, w (j + 1)) =
      w 1 + w 2 + ∑ j ∈ Finset.range L, w (2 + j + 1) := by
    calc _ = ∑ j ∈ Finset.range (L + 2), w (j + 1) := by
          rw [Finset.sum_range_add]
          have hz : ∑ j ∈ Finset.range 2, w (L + j + 1) = 0 :=
            Finset.sum_eq_zero fun j _ ↦ vanish _ (by omega)
          rw [hz, add_zero]
      _ = _ := by
          rw [Nat.add_comm L 2, Finset.sum_range_add]
          simp [Finset.sum_range_succ]
  have tail (a : ℕ) (ha : 3 ≤ a) : |w a| ≤ (R : ℝ) := by
    have hsize : (S a).card ≤ R := by
      calc (S a).card ≤ (Finset.Icc 1 R).card := by
            apply Finset.card_le_card
            intro p hp
            obtain ⟨hp, hpow⟩ := Finset.mem_filter.mp hp
            obtain ⟨_, prime⟩ := Nat.mem_primesLE.mp hp
            have cube : p ^ 3 ≤ n := (Nat.pow_le_pow_right prime.pos ha).trans hpow
            have hc : (p : ℝ) ^ 3 ≤ (n : ℝ) := by exact_mod_cast cube
            have hc' := Real.rpow_le_rpow (by positivity) hc (by norm_num : 0 ≤ (1 / 3 : ℝ))
            rw [← Real.rpow_natCast_mul (by positivity)] at hc'
            norm_num at hc'
            exact Finset.mem_Icc.mpr ⟨prime.one_le, (Nat.le_floor_iff (by positivity)).2 hc'⟩
        _ = R := by simp
    calc |w a| ≤ ∑ p ∈ S a, |(ZMod.χ₄ (p : ZMod 4) : ℝ) ^ a / a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p ∈ S a, (1 : ℝ) := by
          refine Finset.sum_le_sum fun p _ ↦ ?_
          have hz : 0 < (a : ℝ) := by exact_mod_cast (show 0 < a by omega)
          rw [abs_div, abs_pow, abs_of_pos hz, div_le_iff₀ hz, one_mul]
          have hh : |(ZMod.χ₄ (p : ZMod 4) : ℝ)| ≤ 1 := by
            rw [hχ]
            split_ifs <;> norm_num
          have ht := pow_le_pow_left₀ (abs_nonneg _) hh a
          simpa using ht.trans (by simpa using (show (1 : ℝ) ≤ a by exact_mod_cast (show 1 ≤ a by omega)))
      _ ≤ (R : ℝ) := by simpa using (show ((S a).card : ℝ) ≤ R by exact_mod_cast hsize)
  rw [splitSum, ← h₁, ← h₂]
  have he : w 1 + w 2 + ∑ j ∈ Finset.range L, w (2 + j + 1) - w 1 - w 2 =
      ∑ j ∈ Finset.range L, w (2 + j + 1) := by abel
  rw [he]
  calc _ ≤ ∑ j ∈ Finset.range L, |w (2 + j + 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range L, (R : ℝ) := Finset.sum_le_sum fun j _ ↦ tail _ (by omega)
    _ = (R : ℝ) * L := by simp [mul_comm]

lemma prime_race_budget :
    ∀ᶠ n : ℕ in Filter.atTop, 1 < n ∧
      (n.sqrt.primeCounting : ℝ) / 2 ≤ 3 * (Real.sqrt n / Real.log n) ∧
      (n : ℝ) ^ (1 / 3 : ℝ) * (Nat.log 2 n : ℝ) ≤ Real.sqrt n / Real.log n := by
  have hn := tendsto_natCast_atTop_atTop (R := ℝ)
  have hp := (Real.tendsto_sqrt_atTop.comp hn).eventually
    (Chebyshev.eventually_primeCounting_le (ε := 1) (by norm_num))
  have ht := hn.eventually
    ((isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0 : ℝ) < 1 / 6)).bound
       (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
  filter_upwards [hp, ht, eventually_gt_atTop 1] with n hp ht hn'
  have n0 : (0 : ℝ) ≤ n := by positivity
  have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn')
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs := Real.sqrt_nonneg (n : ℝ)
  have h4 : Real.log 4 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have hr : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  refine ⟨hn', ?_, ?_⟩
  · change (Nat.primeCounting ⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) ≤
      (Real.log 4 + 1) * Real.sqrt n / Real.log (Real.sqrt n) at hp
    rw [Real.nat_floor_real_sqrt_eq_nat_sqrt, Real.log_sqrt n0] at hp
    have hh := (le_div_iff₀ (half_pos hl)).mp hp
    rw [← mul_div_assoc, le_div_iff₀ hl]
    nlinarith [mul_nonneg (sub_nonneg.mpr h4) hs]
  · have hp3 : 0 ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by positivity
    have h16 : 0 ≤ (n : ℝ) ^ (1 / 6 : ℝ) := by positivity
    change ‖Real.log (n : ℝ) ^ (2 : ℝ)‖ ≤ Real.log 2 * ‖(n : ℝ) ^ (1 / 6 : ℝ)‖ at ht
    rw [Real.rpow_two, Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg h16] at ht
    have hlog := Real.natLog_le_logb n 2
    rw [Real.logb] at hlog
    push_cast at hlog
    rw [le_div_iff₀ hl2] at hlog
    have hprod : (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (1 / 6 : ℝ) = Real.sqrt n := by
      rw [← Real.rpow_add (by positivity : (0 : ℝ) < n), show (1 / 3 : ℝ) + 1 / 6 = 1 / 2 by norm_num,
        ← Real.sqrt_eq_rpow]
    apply (le_div_iff₀ hl).mpr
    apply (mul_le_mul_iff_left₀ hl2).mp
    nlinarith only [mul_le_mul_of_nonneg_right ht hp3,
      mul_le_mul_of_nonneg_right hlog (mul_nonneg hp3 hl.le), hprod,
      congrArg (fun x : ℝ ↦ x * Real.log 2) hprod]

lemma prime_race_correction :
    ∀ᶠ n : ℕ in Filter.atTop,
      let D := (n.primeCountingMod 4 1 : ℝ) - n.primeCountingMod 4 3
      let s := Real.sqrt n / Real.log n;
      -s ≤ J_sum n - D ∧ J_sum n - D ≤ 4 * s := by
  filter_upwards [prime_race_budget] with n hn
  obtain ⟨_, hs, ht⟩ := hn
  let D := (n.primeCountingMod 4 1 : ℝ) - n.primeCountingMod 4 3
  let s := Real.sqrt n / Real.log n
  let Q := (Nat.primesLE n.sqrt).filter (fun p ↦ p % 2 = 1)
  change -s ≤ J_sum n - D ∧ J_sum n - D ≤ 4 * s
  change (_ : ℝ) ≤ 3 * s at hs
  change _ ≤ s at ht
  have hb := weighted_prime_power_race n
  change |J_sum n - D - (Q.card : ℝ) / 2| ≤ (⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ : ℝ) * Nat.log 2 n at hb
  have hf := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) (1 / 3 : ℝ))
  have he := hb.trans ((mul_le_mul_of_nonneg_right hf (Nat.cast_nonneg (Nat.log 2 n))).trans ht)
  have hq : (Q.card : ℝ) ≤ n.sqrt.primeCounting := by
    exact_mod_cast (Finset.card_filter_le _ _).trans (Nat.primesLE_card_eq_primeCounting n.sqrt).le
  have ⟨hlo, hhi⟩ := abs_le.mp he
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) Q.card]

lemma J_sum_neg_frequently :
    ∀ N : ℕ, ∃ n ≥ N, J_sum n < -(Real.sqrt n / Real.log n) := by
  intro N
  by_contra h
  have hbound : ∀ᶠ n : ℕ in Filter.atTop,
      -(1 : ℝ) * (Real.sqrt n / Real.log n) ≤ (1 : ℝ) * J_sum n := by
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hge : -(Real.sqrt n / Real.log n) ≤ J_sum n := le_of_not_gt fun hlt ↦ h ⟨n, hn, hlt⟩
    linarith
  exact unified_contradiction (Or.inl rfl) zero_lt_one hbound

lemma J_sum_pos_frequently :
    ∀ N : ℕ, ∃ n ≥ N, 4 * (Real.sqrt n / Real.log n) < J_sum n := by
  intro N
  by_contra h
  have hbound : ∀ᶠ n : ℕ in Filter.atTop,
      -(4 : ℝ) * (Real.sqrt n / Real.log n) ≤ (-1 : ℝ) * J_sum n := by
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hle : J_sum n ≤ 4 * (Real.sqrt n / Real.log n) := le_of_not_gt fun hgt ↦ h ⟨n, hn, hgt⟩
    linarith
  exact unified_contradiction (Or.inr rfl) (by norm_num) hbound

end StrategyA

theorem OMA.solution : type_of% @ChebyshevBias.littlewood_mod_four_sign_changes := by
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp StrategyA.prime_race_correction
  constructor
  · apply Set.infinite_of_forall_exists_gt
    intro m
    obtain ⟨n, hn, h⟩ := StrategyA.J_sum_neg_frequently (max K (m + 1))
    have hc := (hK n (le_trans (le_max_left ..) hn)).1
    refine ⟨n, ?_, by omega⟩
    change n.primeCountingMod 4 1 < n.primeCountingMod 4 3
    exact_mod_cast (by linarith : (n.primeCountingMod 4 1 : ℝ) < n.primeCountingMod 4 3)
  · apply Set.infinite_of_forall_exists_gt
    intro m
    obtain ⟨n, hn, h⟩ := StrategyA.J_sum_pos_frequently (max K (m + 1))
    have hc := (hK n (le_trans (le_max_left ..) hn)).2
    refine ⟨n, ?_, by omega⟩
    change n.primeCountingMod 4 3 < n.primeCountingMod 4 1
    exact_mod_cast (by linarith : (n.primeCountingMod 4 3 : ℝ) < n.primeCountingMod 4 1)
