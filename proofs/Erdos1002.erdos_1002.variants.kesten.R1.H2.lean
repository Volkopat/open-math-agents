import OMAReductions.R_Erdos1002_erdos_1002_variants_kesten_R1
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Distributions.Cauchy

/-! The centered Cauchy characteristic function by Fourier inversion. -/

namespace OMA.Erdos1002Cauchy

open MeasureTheory ProbabilityTheory Set
open scoped FourierTransform NNReal

private theorem integral_exp_abs (a b : ℝ) (ha : 0 < a) :
    let f := fun x : ℝ => Complex.exp (↑(b * x) * Complex.I) * Complex.exp ↑(-(a * |x|))
    Integrable f ∧ (∫ x, f x) = ↑(2 * a / (a ^ 2 + b ^ 2) : ℝ) := by
  let L : ℂ := ↑a + ↑b * Complex.I
  let R : ℂ := -↑a + ↑b * Complex.I
  let f := fun x : ℝ => Complex.exp (↑(b * x) * Complex.I) * Complex.exp ↑(-(a * |x|))
  have hL : 0 < L.re := by simpa [L] using ha
  have hR : R.re < 0 := by simpa [R] using ha
  have hLn : L ≠ 0 := fun h => hL.ne' (congrArg Complex.re h)
  have hRn : R ≠ 0 := fun h => hR.ne (congrArg Complex.re h)
  have hleft (x : ℝ) (hx : x ∈ Iic (0 : ℝ)) : f x = Complex.exp (L * x) := by
    dsimp only [f, L]
    rw [← Complex.exp_add, abs_of_nonpos hx]
    congr 1
    push_cast
    ring
  have hright (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) : f x = Complex.exp (R * x) := by
    dsimp only [f, R]
    rw [← Complex.exp_add, abs_of_pos hx]
    congr 1
    push_cast
    ring
  have hIL : IntegrableOn f (Iic (0 : ℝ)) :=
    (integrableOn_exp_mul_complex_Iic hL 0).congr_fun
      (fun x hx => (hleft x hx).symm) measurableSet_Iic
  have hIR : IntegrableOn f (Ioi (0 : ℝ)) :=
    (integrableOn_exp_mul_complex_Ioi hR 0).congr_fun
      (fun x hx => (hright x hx).symm) measurableSet_Ioi
  have hdis : Disjoint (Iic (0 : ℝ)) (Ioi 0) :=
    Set.disjoint_left.mpr (fun x hx hy =>
      not_lt_of_ge (show x ≤ (0 : ℝ) from hx) (show (0 : ℝ) < x from hy))
  change Integrable f ∧ _
  refine ⟨?_,?_⟩
  · rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
    exact hIL.union hIR
  · rw [← setIntegral_univ, ← Iic_union_Ioi (a := (0 : ℝ)),
      setIntegral_union hdis measurableSet_Ioi hIL hIR,
      setIntegral_congr_fun measurableSet_Iic hleft,
      setIntegral_congr_fun measurableSet_Ioi hright,
      integral_exp_mul_complex_Iic hL, integral_exp_mul_complex_Ioi hR]
    have hprod : L * R = -↑(a ^ 2 + b ^ 2 : ℝ) := by
      dsimp [L, R]
      push_cast
      linear_combination (b : ℂ) ^ 2 * Complex.I_sq
    have hdiff : R - L = -(2 * (a : ℂ)) := by dsimp [L,R]; ring
    calc
      _ = (R - L) / (L * R) := by
        simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
        field_simp
        ring
      _ = _ := by
        rw [hprod, hdiff, neg_div_neg_eq]
        push_cast
        rfl

private theorem fourier_exp_abs (γ : ℝ) (hγ : 0 < γ) :
    𝓕 (fun x : ℝ => Complex.exp (↑(-(2 * Real.pi * γ * |x|)) : ℂ)) =
      fun t : ℝ => (cauchyPDFReal 0 ⟨γ, hγ.le⟩ t : ℂ) := by
  ext t : 1
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hA : 0 < 2 * Real.pi * γ := by positivity
  calc
    _ = ↑(2 * (2 * Real.pi * γ) / ((2 * Real.pi * γ)^2 + (-2 * Real.pi * t)^2) : ℝ) := by
      rw [← (integral_exp_abs (2 * Real.pi * γ) (-2 * Real.pi * t) hA).2]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [smul_eq_mul]
      congr 2
      push_cast
      ring
    _ = _ := by
      have hpdf : cauchyPDFReal 0 (⟨γ, hγ.le⟩ : ℝ≥0) t =
          Real.pi⁻¹ * γ * (t ^ 2 + γ ^ 2)⁻¹ := by
        change Real.pi⁻¹ * γ * ((t - 0) ^ 2 + γ ^ 2)⁻¹ = _
        rw [sub_zero]
      apply congrArg Complex.ofReal
      calc
        _ = Real.pi⁻¹ * γ * (t ^ 2 + γ ^ 2)⁻¹ := by
          have hp := Real.pi_ne_zero
          have h1 : (2 * Real.pi * γ)^2 + (-2 * Real.pi * t)^2 ≠ 0 := by positivity
          have h2 : t^2 + γ^2 ≠ 0 := by positivity
          field_simp
          ring
        _ = _ := hpdf.symm

/-- The characteristic function of a centered Cauchy distribution. -/
theorem cauchy_charFun (γ : ℝ) (hγ : 0 < γ) (t : ℝ) :
    charFun (cauchyMeasure 0 ⟨γ, hγ.le⟩) t = Complex.exp (↑(-(γ * |t|)) : ℂ) := by
  let δ : ℝ≥0 := ⟨γ, hγ.le⟩
  let f := fun x : ℝ => Complex.exp (↑(-(2 * Real.pi * γ * |x|)) : ℂ)
  have hδ : δ ≠ 0 := fun h => hγ.ne' (congrArg (fun z : ℝ≥0 => (z : ℝ)) h)
  have hC : Continuous f := by unfold f; fun_prop
  have hA : 0 < 2 * Real.pi * γ := by positivity
  have hI : Integrable f := by
    simpa [f] using (integral_exp_abs (2 * Real.pi * γ) 0 hA).1
  have hFourier : 𝓕 f = fun x : ℝ => (cauchyPDFReal 0 δ x : ℂ) := fourier_exp_abs γ hγ
  have hIF : Integrable (𝓕 f) := by rw [hFourier]; exact (integrable_cauchyPDFReal 0).ofReal
  have hInv := congrFun (hC.fourierInv_fourier_eq hI hIF) (t / (2 * Real.pi))
  rw [hFourier] at hInv
  change charFun (cauchyMeasure 0 δ) t = _
  rw [charFun_apply_real, cauchyMeasure_of_scale_ne_zero 0 hδ,
      integral_withDensity_eq_integral_toReal_smul (measurable_cauchyPDF 0 δ)
        (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  calc
    _ = 𝓕⁻ (fun x : ℝ => (cauchyPDFReal 0 δ x : ℂ)) (t / (2 * Real.pi)) := by
      rw [Real.fourierInv_eq']
      apply integral_congr_ae
      filter_upwards [] with x
      rw [Real.inner_apply, cauchyPDF_def, ENNReal.toReal_ofReal (cauchyPDF_pos 0 hδ x).le,
        Complex.real_smul, smul_eq_mul, mul_comm]
      congr 2
      push_cast
      field_simp [Real.pi_ne_zero]
    _ = _ := by
      rw [hInv]
      unfold f
      rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      congr 2
      field_simp [Real.pi_ne_zero]

end OMA.Erdos1002Cauchy

open scoped NNReal

theorem OMA.solution : OMA.R_Erdos1002_erdos_1002_variants_kesten_R1.H2 := by
  intro γ hγ t
  have hγreal : 0 < (γ : ℝ) := by exact_mod_cast hγ
  rw [Complex.ofReal_exp]
  have he : (⟨(γ : ℝ), hγreal.le⟩ : ℝ≥0) = γ := Subtype.ext rfl
  have hc := OMA.Erdos1002Cauchy.cauchy_charFun (γ : ℝ) hγreal t
  rw [he] at hc
  simpa only [neg_mul] using hc
