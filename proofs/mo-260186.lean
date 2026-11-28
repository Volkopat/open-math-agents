import OMAStatements.S_mo_260186
import Mathlib

-- Retains the three-atom variance construction of @AkiRA-COM-FP (PR #17670).
-- Standard real-measure addition and scaling replace manual ENNReal expansion.

open Set MeasureTheory
open scoped ENNReal

open OMA.S_mo_260186

private noncomputable def mixture (t : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1-t) • Measure.dirac 0 +
    ENNReal.ofReal (t/2) • Measure.dirac 1 +
    ENNReal.ofReal (t/2) • Measure.dirac (-1)

private theorem mixture_probability {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    IsProbabilityMeasure (mixture t) := by
  constructor
  have h0 : 0 ≤ 1-t := sub_nonneg.mpr ht'
  have h1 : 0 ≤ t/2 := by positivity
  have h2 : 0 ≤ 1-t+t/2 := add_nonneg h0 h1
  simp only [mixture,Measure.add_apply,Measure.smul_apply,smul_eq_mul,
    Measure.dirac_apply_of_mem (mem_univ _),mul_one]
  rw [←ENNReal.ofReal_add h0 h1,←ENNReal.ofReal_add h2 h1]
  norm_num [show 1-t+t/2+t/2 = 1 by ring]

private theorem mixture_integrable (g : ℝ → ℝ) (t : ℝ) : Integrable g (mixture t) := by
  have hD (x : ℝ) : Integrable g (Measure.dirac x) := integrable_dirac (by simp)
  exact (((hD 0).smul_measure ENNReal.ofReal_ne_top).add_measure
    ((hD 1).smul_measure ENNReal.ofReal_ne_top)).add_measure
    ((hD (-1)).smul_measure ENNReal.ofReal_ne_top)

private theorem mixture_integral (g : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    ∫ x, g x ∂(mixture t) = (1-t)*g 0 + (t/2)*g 1 + (t/2)*g (-1) := by
  have hD (x : ℝ) : Integrable g (Measure.dirac x) := integrable_dirac (by simp)
  have h0 := (hD 0).smul_measure (c := ENNReal.ofReal (1-t)) ENNReal.ofReal_ne_top
  have h1 := (hD 1).smul_measure (c := ENNReal.ofReal (t/2)) ENNReal.ofReal_ne_top
  have hm := (hD (-1)).smul_measure (c := ENNReal.ofReal (t/2)) ENNReal.ofReal_ne_top
  unfold mixture
  rw [integral_add_measure (h0.add_measure h1) hm,integral_add_measure h0 h1]
  simp [integral_smul_measure,smul_eq_mul,ENNReal.toReal_ofReal (sub_nonneg.mpr ht'),
    ENNReal.toReal_ofReal (show 0 ≤ t/2 by positivity)]

private theorem tv_of_mixture_le {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    probabilityTV (Measure.dirac (0 : ℝ)) (mixture t) ≤ t := by
  unfold probabilityTV
  apply csSup_le
  · exact ⟨0,⟨∅,MeasurableSet.empty,by simp⟩⟩
  · rintro r ⟨s,hs,rfl⟩
    let P := Measure.dirac (0 : ℝ)
    let A := Measure.dirac (1 : ℝ)
    let B := Measure.dirac (-1 : ℝ)
    let x := P.real s
    let y := A.real s
    let z := B.real s
    have hx : 0 ≤ x ∧ x ≤ 1 := ⟨ENNReal.toReal_nonneg,measureReal_le_one⟩
    have hy : 0 ≤ y ∧ y ≤ 1 := ⟨ENNReal.toReal_nonneg,measureReal_le_one⟩
    have hz : 0 ≤ z ∧ z ≤ 1 := ⟨ENNReal.toReal_nonneg,measureReal_le_one⟩
    have h1 : 0 ≤ 1-t := sub_nonneg.mpr ht'
    have h2 : 0 ≤ t/2 := by positivity
    have hQ : (mixture t).real s = (1-t)*x + (t/2)*y + (t/2)*z := by
      rw [mixture, measureReal_add_apply ?_ ?_, measureReal_add_apply ?_ ?_]
      · simp only [measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal h1,
          ENNReal.toReal_ofReal h2]
        rfl
      all_goals simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]; finiteness
    change |x-(mixture t).real s| ≤ t
    rw [hQ,show x-((1-t)*x+(t/2)*y+(t/2)*z) = t*(x-(y+z)/2) by ring,
      abs_mul,abs_of_nonneg ht]
    apply (mul_le_mul_of_nonneg_left _ ht).trans_eq (mul_one _)
    apply abs_le.mpr
    constructor <;> linarith [hx.1,hx.2,hy.1,hy.2,hz.1,hz.2]

theorem OMA.solution : type_of% @OMA.S_mo_260186.main := by
  intro C δ hC hδ
  let t := min (δ/2) (1/2)
  have ht : 0 < t := lt_min (by positivity) (by norm_num)
  have ht' : t ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hδ' : t < δ := (min_le_left _ _).trans_lt (by linarith)
  let a := Real.sqrt (C/t)
  have ha2 : a^2 = C/t := Real.sq_sqrt (div_nonneg hC.le ht.le)
  let f : ℝ → ℝ := fun x => a*x
  let P := Measure.dirac (0 : ℝ)
  let Q := mixture t
  have hMeanP : testExpectation P f = 0 := by simp [testExpectation,P,f]
  have hMeanQ : testExpectation Q f = 0 := by
    rw [testExpectation,mixture_integral f ht.le ht']
    dsimp [f]
    ring
  refine ⟨P,Q,f,inferInstance,mixture_probability ht.le ht',
    continuous_const.mul continuous_id,integrable_dirac (by simp),mixture_integrable f t,
    integrable_dirac (by simp),mixture_integrable (fun x => (f x)^2) t,
    hMeanP.trans hMeanQ.symm,?_,?_,(tv_of_mixture_le ht.le ht').trans_lt hδ'⟩
  · rw [testVariance,hMeanP]
    simp [P,f]
  · rw [testVariance,hMeanQ,mixture_integral _ ht.le ht']
    calc
      _ = t*a^2 := by dsimp [f]; ring
      _ = C := by rw [ha2]; field_simp
