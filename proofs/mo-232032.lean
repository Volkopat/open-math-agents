import OMAStatements.S_mo_232032

/-!
# A binary counterexample to the ordering of JS and KL divergence

Keep the first coin at 9/10 and change the second from 7/10 to 99/100.
All three coins assign positive mass to both outcomes. The measure-theoretic
divergences reduce to binary logarithm formulas. Multiplying by a common
denominator converts each strict comparison to one between rational products.
-/

namespace MODivergenceProof

open MeasureTheory ProbabilityTheory InformationTheory OMA.S_mo_232032 unitInterval
open scoped ENNReal NNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def binaryKL (p q : ℝ) : ℝ :=
  p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))

noncomputable def binaryJS (p q : ℝ) : ℝ :=
  (binaryKL p ((p + q) / 2) + binaryKL q ((p + q) / 2)) / 2

/-- On an atom of positive mass the likelihood ratio is the ratio of masses. -/
theorem llr_atom [MeasurableSingletonClass Ω] (μ ν : Measure Ω)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hac : μ ≪ ν) (x : Ω) (hx : 0 < ν.real {x}) :
    llr μ ν x = Real.log (μ.real {x} / ν.real {x}) := by
  have h := congrArg (fun m : Measure Ω => m {x}) (Measure.withDensity_rnDeriv_eq μ ν hac)
  change ν.withDensity (μ.rnDeriv ν) {x} = μ {x} at h
  rw [withDensity_apply _ (measurableSet_singleton x), lintegral_singleton] at h
  unfold llr
  apply congrArg Real.log
  apply (eq_div_iff hx.ne').mpr
  simpa only [measureReal_def, ENNReal.toReal_mul] using congrArg ENNReal.toReal h

theorem coin_ac (x y : Ω) (p q : unitInterval)
    (hq₀ : 0 < (q : ℝ)) (hq₁ : (q : ℝ) < 1) : Ber(x, y, p) ≪ Ber(x, y, q) := by
  classical
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hz
  have hreal : Ber(x, y, q).real s = 0 := by rw [measureReal_def, hz, ENNReal.toReal_zero]
  by_cases hx : x ∈ s <;> by_cases hy : y ∈ s
  · simp [hs, hx, hy] at hz
  · simp [hs, hx, hy] at hreal
    have heq : (q : ℝ) = 0 := congrArg Subtype.val hreal
    exact (hq₀.ne' heq).elim
  · simp [hs, hx, hy] at hreal
    linarith
  · simp [hs, hx, hy]

theorem eval_kl [MeasurableSingletonClass Ω] (x y : Ω) (hxy : x ≠ y) (p q : unitInterval)
    (hq₀ : 0 < (q : ℝ)) (hq₁ : (q : ℝ) < 1) :
    (klDiv Ber(x, y, p) Ber(x, y, q)).toReal = binaryKL p q ∧
      klDiv Ber(x, y, p) Ber(x, y, q) ≠ ⊤ := by
  have hac := coin_ac x y p q hq₀ hq₁
  constructor
  · rw [toReal_klDiv_of_measure_eq hac (by simp), integral_bernoulliMeasure]
    rw [llr_atom _ _ hac x (by simpa [hxy.symm] using hq₀),
      llr_atom _ _ hac y (by simpa [hxy] using sub_pos.mpr hq₁)]
    simp [binaryKL, hxy, hxy.symm, smul_eq_mul]
  · exact klDiv_ne_top hac (integrable_bernoulliMeasure _ _ _ _)

theorem mixture_coin (x y : Ω) (p q m : unitInterval)
    (hm : (m : ℝ) = ((p : ℝ) + q) / 2) :
    mixture Ber(x, y, p) Ber(x, y, q) = Ber(x, y, m) := by
  have half_weight (a b c : ℝ≥0) (hc : (c : ℝ) = ((a : ℝ) + b) / 2) :
      (2 : ℝ≥0)⁻¹ * (a + b) = c := by
    apply Subtype.ext
    change (2 : ℝ)⁻¹ * ((a : ℝ) + b) = (c : ℝ)
    rw [hc]
    ring
  have heads := half_weight (toNNReal p) (toNNReal q) (toNNReal m) (by simpa using hm)
  have tails := half_weight (toNNReal (σ p)) (toNNReal (σ q)) (toNNReal (σ m)) (by
    simp only [coe_toNNReal, coe_symm_eq]
    linarith)
  simp only [mixture, bernoulliMeasure_def]
  rw [← heads, ← tails, ← smul_smul, ← smul_smul, ← smul_add]
  congr 1
  rw [add_smul, add_smul]
  abel

theorem eval_js [MeasurableSingletonClass Ω] (x y : Ω) (hxy : x ≠ y)
    (p q m : unitInterval) (hm : (m : ℝ) = ((p : ℝ) + q) / 2)
    (hm₀ : 0 < (m : ℝ)) (hm₁ : (m : ℝ) < 1) :
    (jsDiv Ber(x, y, p) Ber(x, y, q)).toReal = binaryJS p q ∧
      jsDiv Ber(x, y, p) Ber(x, y, q) ≠ ⊤ := by
  rw [jsDiv, mixture_coin x y p q m hm]
  obtain ⟨hp, hpfin⟩ := eval_kl x y hxy p m hm₀ hm₁
  obtain ⟨hq, hqfin⟩ := eval_kl x y hxy q m hm₀ hm₁
  constructor
  · rw [ENNReal.toReal_div, ENNReal.toReal_add hpfin hqfin, hp, hq, binaryJS, ← hm]
    norm_num
  · exact ENNReal.div_ne_top (ENNReal.add_ne_top.mpr ⟨hpfin, hqfin⟩) (by norm_num)

theorem kl_increases : binaryKL (9 / 10) (7 / 10) < binaryKL (9 / 10) (99 / 100) := by
  have cert : Real.log ((9 / 7 : ℝ) ^ 9 * (1 / 3)) <
      Real.log ((10 / 11 : ℝ) ^ 9 * 10) := Real.log_lt_log (by positivity) (by norm_num)
  simp (disch := positivity) only [Real.log_mul, Real.log_pow, Nat.cast_ofNat] at cert
  norm_num [binaryKL] at cert ⊢
  linarith only [cert]

theorem js_decreases : binaryJS (9 / 10) (99 / 100) < binaryJS (9 / 10) (7 / 10) := by
  have cert :
      Real.log ((20 / 21 : ℝ) ^ 90 * (20 / 11) ^ 10 * (22 / 21) ^ 99 * (2 / 11)) <
      Real.log ((9 / 8 : ℝ) ^ 90 * (1 / 2) ^ 10 * (7 / 8) ^ 70 * (3 / 2) ^ 30) :=
    Real.log_lt_log (by positivity) (by norm_num)
  simp (disch := positivity) only [Real.log_mul, Real.log_pow, Nat.cast_ofNat] at cert
  norm_num [binaryJS, binaryKL] at cert ⊢
  linarith only [cert]

universe u

theorem binary_counterexample :
    ∃ P Q R : ProbabilityMeasure (ULift.{u} Bool),
      jsDiv (P : Measure (ULift.{u} Bool)) R < jsDiv (P : Measure (ULift.{u} Bool)) Q ∧
      klDiv (P : Measure (ULift.{u} Bool)) Q < klDiv (P : Measure (ULift.{u} Bool)) R := by
  let : MeasurableSingletonClass (ULift.{u} Bool) := ⟨fun _ => trivial⟩
  let x : ULift.{u} Bool := ⟨true⟩
  let y : ULift.{u} Bool := ⟨false⟩
  have hxy : x ≠ y := by decide
  let p : unitInterval := ⟨9 / 10, by constructor <;> norm_num⟩
  let q : unitInterval := ⟨7 / 10, by constructor <;> norm_num⟩
  let r : unitInterval := ⟨99 / 100, by constructor <;> norm_num⟩
  let m : unitInterval := ⟨4 / 5, by constructor <;> norm_num⟩
  let m' : unitInterval := ⟨189 / 200, by constructor <;> norm_num⟩
  refine ⟨⟨Ber(x, y, p), inferInstance⟩, ⟨Ber(x, y, q), inferInstance⟩,
    ⟨Ber(x, y, r), inferInstance⟩, ?_, ?_⟩
  · obtain ⟨hs, hsfin⟩ := eval_js x y hxy p q m (by norm_num [p, q, m])
      (by norm_num [m]) (by norm_num [m])
    obtain ⟨ht, htfin⟩ := eval_js x y hxy p r m' (by norm_num [p, r, m'])
      (by norm_num [m']) (by norm_num [m'])
    apply (ENNReal.toReal_lt_toReal htfin hsfin).mp
    rw [ht, hs]
    exact js_decreases
  · obtain ⟨hs, hsfin⟩ := eval_kl x y hxy p q (by norm_num [q]) (by norm_num [q])
    obtain ⟨ht, htfin⟩ := eval_kl x y hxy p r (by norm_num [r]) (by norm_num [r])
    apply (ENNReal.toReal_lt_toReal hsfin htfin).mp
    rw [hs, ht]
    exact kl_increases

end MODivergenceProof

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_232032.main) := by
  intro h
  obtain ⟨P, Q, R, hjs, hkl⟩ := MODivergenceProof.binary_counterexample
  exact (not_lt_of_gt hkl) (h _ P Q P R hjs)
