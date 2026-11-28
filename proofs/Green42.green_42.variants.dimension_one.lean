import FormalConjectures.GreensOpenProblems.«42»
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The one-dimensional certificate is the overlap length of two unit-radius intervals. -/

open MeasureTheory
open scoped EuclideanGeometry FourierTransform Convolution

noncomputable def OMA.box : ℝ → ℂ :=
  (Set.Icc (-1 : ℝ) 1).indicator fun _ => 1

noncomputable def OMA.tent (x : ℝ) : ℝ := max 0 (2 - |x|)

lemma OMA.box_integrable : Integrable OMA.box := by
  unfold OMA.box
  exact (integrableOn_const (isCompact_Icc.measure_ne_top)).integrable_indicator measurableSet_Icc

lemma OMA.tent_convolution :
    (fun x : ℝ => (OMA.tent x : ℂ)) =
      OMA.box ⋆[ContinuousLinearMap.mul ℂ ℂ] OMA.box := by
  classical
  funext x
  have hoverlap (y : ℝ) : y ∈ Set.Icc (max (-1) (x - 1)) (min 1 (x + 1)) ↔
      y ∈ Set.Icc (-1 : ℝ) 1 ∧ x - y ∈ Set.Icc (-1 : ℝ) 1 := by
    simp only [Set.mem_Icc, max_le_iff, le_min_iff]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
      exact ⟨⟨h₁, h₃⟩, ⟨by linarith, by linarith⟩⟩
    · rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
      exact ⟨⟨h₁, by linarith⟩, ⟨h₂, by linarith⟩⟩
  have hind : (fun y : ℝ => OMA.box y * OMA.box (x - y)) =
      (Set.Icc (max (-1) (x - 1)) (min 1 (x + 1))).indicator (fun _ => (1 : ℂ)) := by
    funext y
    by_cases hy : y ∈ Set.Icc (-1 : ℝ) 1 <;> by_cases hxy : x - y ∈ Set.Icc (-1 : ℝ) 1 <;>
      simp [OMA.box, hy, hxy, hoverlap]
  rw [MeasureTheory.convolution_mul, hind, integral_indicator measurableSet_Icc,
    setIntegral_const, Real.volume_real_Icc, Complex.real_smul, mul_one]
  congr 1
  unfold OMA.tent
  rw [max_comm 0]
  congr 1
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, max_eq_right (by linarith : (-1 : ℝ) ≤ x - 1),
      min_eq_left (by linarith : (1 : ℝ) ≤ x + 1)]
    ring
  · rw [abs_of_neg (lt_of_not_ge hx), max_eq_left (by linarith : x - 1 ≤ (-1 : ℝ)),
      min_eq_right (by linarith : x + 1 ≤ (1 : ℝ))]
    ring

lemma OMA.box_fourier (t : ℝ) :
    𝓕 OMA.box t = ((2 * Real.sinc (-2 * Real.pi * t) : ℝ) : ℂ) := by
  classical
  let k : ℝ := -2 * Real.pi * t
  rw [Real.fourier_eq']
  have hind : (fun x : ℝ => Complex.exp ((↑(-2 * Real.pi * inner ℝ x t) : ℂ) *
      Complex.I) • OMA.box x) = (Set.Icc (-1 : ℝ) 1).indicator
        (fun x : ℝ => Complex.exp ((↑(k * x) : ℂ) * Complex.I)) := by
    funext x
    by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
    · simp only [OMA.box, Set.indicator_of_mem hx, smul_eq_mul, mul_one, Real.inner_apply]
      have heq : -2 * Real.pi * (x * t) = k * x := by dsimp [k]; ring
      rw [heq]
    · simp [OMA.box, hx]
  rw [hind, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  change (∫ x in (-1 : ℝ)..1, Complex.exp ((↑(k * x) : ℂ) * Complex.I)) =
    ((2 * Real.sinc k : ℝ) : ℂ)
  by_cases hk : k = 0
  · norm_num [hk, intervalIntegral.integral_const, Complex.real_smul, Real.sinc_zero]
  · have hscale := intervalIntegral.integral_comp_mul_left
      (fun r : ℝ => Complex.exp ((r : ℂ) * Complex.I)) (a := -1) (b := 1) hk
    rw [hscale, mul_neg_one, mul_one, integral_exp_mul_I_eq_sinc, Complex.real_smul]
    have hc : (k : ℂ) ≠ 0 := by exact_mod_cast hk
    push_cast
    field_simp [hc]

lemma OMA.tent_fourier (t : ℝ) :
    Green42.fHat OMA.tent t = (2 * Real.sinc (-2 * Real.pi * t)) ^ 2 := by
  unfold Green42.fHat
  rw [OMA.tent_convolution, Real.fourier_mul_convolution_eq OMA.box_integrable OMA.box_integrable,
    OMA.box_fourier, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

lemma OMA.tent_decay (x : ℝ) : |OMA.tent x| ≤ 18 / (1 + |x|) ^ 2 := by
  rw [OMA.tent, abs_of_nonneg (le_max_left _ _), max_le_iff]
  refine ⟨by positivity, (le_div_iff₀ (by positivity)).mpr ?_⟩
  nlinarith [sq_nonneg (|x| - 1), mul_nonneg (abs_nonneg x) (sq_nonneg (|x| - 1))]

lemma OMA.sinc_decay (t : ℝ) : |Real.sinc (-2 * Real.pi * t)| ≤ 2 / (1 + |t|) := by
  let u := -2 * Real.pi * t
  have h : |Real.sinc u| * |u| ≤ 1 := by
    by_cases hu : u = 0
    · simp [hu]
    rw [Real.sinc_of_ne_zero hu, abs_div, div_mul_cancel₀ _ (abs_ne_zero.mpr hu)]
    exact Real.abs_sin_le_one u
  have ht : |t| ≤ |u| := by
    simp only [u, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_pos Real.pi_pos]
    exact le_mul_of_one_le_left (abs_nonneg _) (by linarith [Real.pi_gt_three])
  apply (le_div_iff₀ (by positivity)).mpr
  change |Real.sinc u| * (1 + |t|) ≤ 2
  linarith [Real.abs_sinc_le_one u, mul_le_mul_of_nonneg_left ht (abs_nonneg (Real.sinc u))]

lemma OMA.tent_hat_decay (t : ℝ) : |Green42.fHat OMA.tent t| ≤ 18 / (1 + |t|) ^ 2 := by
  rw [OMA.tent_fourier, abs_sq]
  have hs := pow_le_pow_left₀ (abs_nonneg (Real.sinc (-2 * Real.pi * t)))
    (OMA.sinc_decay t) 2
  rw [sq_abs, div_pow] at hs
  have hd : 0 < (1 + |t|) ^ 2 := by positivity
  have hs' := (le_div_iff₀ hd).mp hs
  apply (le_div_iff₀ hd).mpr
  nlinarith

noncomputable def OMA.coordinate : EuclideanSpace ℝ (Fin 1) ≃ₗᵢ[ℝ] ℝ where
  toFun x := x 0
  invFun y := WithLp.toLp 2 (fun _ => y)
  left_inv x := by ext i; fin_cases i; rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' x := by
    change ‖x 0‖ = ‖x‖
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.sqrt_sq (norm_nonneg _)]

theorem OMA.solution : type_of% @Green42.green_42.variants.dimension_one := by
  let f : EuclideanSpace ℝ (Fin 1) → ℝ := OMA.tent ∘ OMA.coordinate
  have hHat (t : EuclideanSpace ℝ (Fin 1)) :
      Green42.fHat f t = Green42.fHat OMA.tent (OMA.coordinate t) := by
    unfold Green42.fHat
    change (𝓕 ((fun x : ℝ => (OMA.tent x : ℂ)) ∘ OMA.coordinate) t).re = _
    rw [Real.fourier_comp_linearIsometry]
  have hnorm (x : EuclideanSpace ℝ (Fin 1)) : |OMA.coordinate x| = ‖x‖ := by
    rw [← Real.norm_eq_abs, OMA.coordinate.norm_map]
  have h0 : f 0 = 2 := by norm_num [f, OMA.tent]
  have hh0 : Green42.fHat f 0 = 4 := by
    rw [hHat, OMA.coordinate.map_zero, OMA.tent_fourier]
    norm_num [Real.sinc_zero]
  refine ⟨f, ⟨?_, ?_, ?_, ?_, by rw [hh0]; norm_num, by rw [h0]; norm_num⟩, ?_⟩
  · have hc : Continuous OMA.tent := by unfold OMA.tent; fun_prop
    refine ⟨hc.comp OMA.coordinate.continuous, 18, by norm_num, 1, by norm_num, ?_, ?_⟩
    · intro x
      simpa only [f, Function.comp_apply, hnorm, finrank_euclideanSpace_fin, Nat.cast_one,
        one_add_one_eq_two, Real.rpow_two] using OMA.tent_decay (OMA.coordinate x)
    · intro t
      simpa only [hHat, hnorm, finrank_euclideanSpace_fin, Nat.cast_one, one_add_one_eq_two,
        Real.rpow_two] using OMA.tent_hat_decay (OMA.coordinate t)
  · intro x y h
    change OMA.tent (OMA.coordinate x) = OMA.tent (OMA.coordinate y)
    simp only [OMA.tent, hnorm, h]
  · intro x hx
    change OMA.tent (OMA.coordinate x) ≤ 0
    rw [OMA.tent, hnorm, max_eq_left (by linarith)]
  · intro t
    rw [hHat, OMA.tent_fourier]
    positivity
  · rw [h0, hh0]
    norm_num
