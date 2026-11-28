import OMAReductions.R_Bloch_landauConstant_lower_bound_R1
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Quantitative lower bound for Landau's constant (locally univalent step H2)

We prove that every locally univalent holomorphic function `g : ℂ → ℂ` on the open unit disk
with `g 0 = 0` and `deriv g 0 = 1` contains an open disk of radius `0.5 + 10 ^ (-335 : ℤ)`
in its image `g '' ball 0 1` (in fact we obtain `0.5 + 10 ^ (-44 : ℤ)`).

The proof is completely elementary and self-contained, organized into six sections:
1. `LandauNorm`: Disk automorphism reduction to normalized locally univalent Bloch functions
   satisfying `(1 - ‖z‖ ^ 2) * ‖deriv g z‖ ≤ 1`, plus rotation invariance.
2. `LandauLog`: Construction of the holomorphic logarithm `h` of `deriv g` via primitives on
   the disk, Borel-Caratheodory coefficient bounds, rotation normalization making `c₂ ∈ [0, 1]`
   and `Im c₃ ≥ 0`, and quadratic rigidity for `Re c₃` near `c₂ = 1`.
3. `LandauLiuMinda`: Sharp Liu-Minda distortion lower bound `‖deriv g z‖ ≥ ell ‖z‖` via the
   Julia-Caratheodory boundary inequality (adapted from the Bloch distortion setup).
4. `LandauEscape`: Escaping ray lifts using the inverse function theorem and a smoothed-norm
   integral lower bound along maximal lifts.
5. `LandauAngle`: Angular proximity of lifted rays near the origin.
6. `LandauMain`: Two-case excess bound on `Re h - log ell`, center shift for the extremal
   case, and the final theorem `OMA.solution`.
-/

open Metric Set Filter
open scoped ComplexConjugate Topology NNReal ENNReal BigOperators

/- ## Section 1: Normalization via disk automorphisms -/

namespace LandauNorm

noncomputable def mobius (a z : ℂ) : ℂ := (z + a) / (1 + conj a * z)

theorem denom_ne {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    1 + conj a * z ≠ 0 := by
  intro h
  have he : conj a * z = -1 := eq_neg_of_add_eq_zero_right h
  have hn : ‖a‖ * ‖z‖ = 1 := by
    simpa [norm_mul] using congrArg norm he
  nlinarith [norm_nonneg a, norm_nonneg z, mul_pos (sub_pos.mpr ha) (sub_pos.mpr hz)]

theorem norm_identity (a z : ℂ) :
    ‖1 + conj a * z‖ ^ 2 - ‖z + a‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im]
  ring

theorem maps_mobius {a : ℂ} (ha : ‖a‖ < 1) :
    MapsTo (mobius a) (ball 0 1) (ball 0 1) := by
  intro z hz
  rw [mem_ball_zero_iff] at hz ⊢
  rw [mobius, norm_div, div_lt_one (norm_pos_iff.mpr (denom_ne ha hz))]
  have hap : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hzp : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  nlinarith [norm_identity a z, mul_pos hap hzp, norm_nonneg (z + a),
    norm_nonneg (1 + conj a * z)]

theorem mobius_zero {a : ℂ} : mobius a 0 = a := by simp [mobius]

theorem mobius_inverse {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    mobius (-a) (mobius a z) = z := by
  have hd := denom_ne ha hz
  have hza : ‖mobius a z‖ < 1 := mem_ball_zero_iff.mp
    (maps_mobius ha (mem_ball_zero_iff.mpr hz))
  have hdi := denom_ne (a := -a) (by simpa using ha) hza
  unfold mobius at *
  simp only [map_neg] at hdi ⊢
  apply (div_eq_iff hdi).mpr
  have hnum : z + a - a * (1 + conj a * z) =
      z * ((1 + conj a * z) - conj a * (z + a)) := by ring
  have hleft : (z + a) / (1 + conj a * z) + -a =
      (z + a - a * (1 + conj a * z)) / (1 + conj a * z) := by
    apply (eq_div_iff hd).mpr
    rw [add_mul, div_mul_cancel₀ _ hd]
    ring
  have hright : 1 + -conj a * ((z + a) / (1 + conj a * z)) =
      ((1 + conj a * z) - conj a * (z + a)) / (1 + conj a * z) := by
    apply (eq_div_iff hd).mpr
    rw [add_mul, mul_assoc, div_mul_cancel₀ _ hd]
    ring
  rw [hleft, hright, hnum, mul_div_assoc]

theorem hasDerivAt_mobius {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    HasDerivAt (mobius a)
      ((1 - (‖a‖ ^ 2 : ℝ) : ℂ) / (1 + conj a * z) ^ 2) z := by
  have hd := denom_ne ha hz
  have h := ((hasDerivAt_id z).add_const a).div
    (((hasDerivAt_id z).const_mul (conj a)).const_add 1) hd
  have he : conj a * a = (‖a‖ ^ 2 : ℝ) := by
    rw [mul_comm, Complex.mul_conj, Complex.sq_norm]
  have hv : 1 * (1 + conj a * id z) - (id z + a) * (conj a * 1) =
      1 - ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [← he]
    simp only [id_eq]
    ring
  rw [hv] at h
  exact h

theorem deriv_mobius_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    deriv (mobius a) z ≠ 0 := by
  rw [(hasDerivAt_mobius ha hz).deriv]
  have hap : (1 : ℝ) - ‖a‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg a]
  have hnum : (1 : ℂ) - ((‖a‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    rw [show (1 : ℂ) - ((‖a‖ ^ 2 : ℝ) : ℂ) = ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) by push_cast; rfl]
    exact Complex.ofReal_ne_zero.mpr hap
  exact div_ne_zero hnum (pow_ne_zero 2 (denom_ne ha hz))

theorem mobius_weight {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    (1 - ‖z‖ ^ 2) * ‖deriv (mobius a) z‖ = 1 - ‖mobius a z‖ ^ 2 := by
  have hn := norm_pos_iff.mpr (denom_ne ha hz)
  have hap : 0 ≤ 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have he : ‖(1 - ((‖a‖ ^ 2 : ℝ) : ℂ))‖ = 1 - ‖a‖ ^ 2 := by
    rw [show (1 : ℂ) - ↑(‖a‖ ^ 2) = ↑(1 - ‖a‖ ^ 2 : ℝ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hap]
  rw [(hasDerivAt_mobius ha hz).deriv, mobius, norm_div, norm_pow, norm_div, div_pow, he]
  field_simp
  nlinarith [norm_identity a z]

theorem norm_mobius_sq {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    1 - ‖mobius a z‖ ^ 2 =
      (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) / ‖1 + conj a * z‖ ^ 2 := by
  have hd : 1 + conj a * z ≠ 0 := denom_ne ha hz
  rw [mobius, norm_div, div_pow]
  apply (eq_div_iff (pow_ne_zero _ (norm_ne_zero_iff.mpr hd))).mpr
  rw [sub_mul, one_mul, div_mul_cancel₀ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hd))]
  exact norm_identity a z

theorem normalized_reduction {B R : ℝ} (hB : 0 < B) (hBR : B < R)
    (hNorm : ∀ g : ℂ → ℂ, DifferentiableOn ℂ g (ball 0 1) → g 0 = 0 →
      deriv g 0 = 1 → (∀ z ∈ ball (0 : ℂ) 1, deriv g z ≠ 0) →
      (∀ z ∈ ball (0 : ℂ) 1, (1 - ‖z‖ ^ 2) * ‖deriv g z‖ ≤ 1) →
      ∃ c, ball c R ⊆ g '' ball 0 1) :
    ∀ F : ℂ → ℂ, DifferentiableOn ℂ F (ball 0 1) → F 0 = 0 → deriv F 0 = 1 →
      (∀ z ∈ ball (0 : ℂ) 1, deriv F z ≠ 0) →
      ∃ c, ball c B ⊆ F '' ball 0 1 := by
  intro F hF _hF0 hF1 hFne
  have hR : 0 < R := hB.trans hBR
  obtain ⟨s, hsB, hs1⟩ := exists_between ((div_lt_one hR).mpr hBR)
  have hs0 : 0 < s := (div_pos hB hR).trans hsB
  have hsB' : B < s * R := (div_lt_iff₀ hR).mp hsB
  let f : ℂ → ℂ := fun z => F ((s : ℂ) * z)
  have hsf : 1 < 1 / s := (lt_div_iff₀ hs0).mpr (by simpa using hs1)
  have hlin (z : ℂ) : HasDerivAt (fun w : ℂ => (s : ℂ) * w) (s : ℂ) z := by
    simpa using (hasDerivAt_id z).const_mul (s : ℂ)
  have hfderiv (z : ℂ) (hz : z ∈ ball (0 : ℂ) (1 / s)) :
      HasDerivAt f (deriv F ((s : ℂ) * z) * (s : ℂ)) z := by
    have hsz : (s : ℂ) * z ∈ ball (0 : ℂ) 1 := by
      simp only [mem_ball_zero_iff] at hz ⊢
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
      nlinarith [(lt_div_iff₀ hs0).mp hz]
    have hFd := (hF.differentiableAt (isOpen_ball.mem_nhds hsz)).hasDerivAt
    exact hFd.comp z (hlin z)
  have hf : DifferentiableOn ℂ f (ball 0 (1 / s)) :=
    fun z hz => (hfderiv z hz).differentiableAt.differentiableWithinAt
  have h0mem : (0 : ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
  have hf0 : deriv f 0 = (s : ℂ) := by
    rw [(hfderiv 0 (ball_subset_ball hsf.le h0mem)).deriv]
    simp [hF1]
  have hfne (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : deriv f z ≠ 0 := by
    have hz' : z ∈ ball (0 : ℂ) (1 / s) := ball_subset_ball hsf.le hz
    rw [(hfderiv z hz').deriv]
    have hsz : (s : ℂ) * z ∈ ball (0 : ℂ) 1 := by
      simp only [mem_ball_zero_iff] at hz ⊢
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
      nlinarith
    exact mul_ne_zero (hFne _ hsz) (Complex.ofReal_ne_zero.mpr hs0.ne')
  let W : ℂ → ℝ := fun z => (1 - ‖z‖ ^ 2) * ‖deriv f z‖
  have hW : ContinuousOn W (closedBall 0 1) := by
    have hc : ContinuousOn (deriv f) (closedBall 0 1) :=
      ((hf.deriv isOpen_ball).continuousOn).mono (closedBall_subset_ball hsf)
    exact ((continuous_const.sub (continuous_norm.pow 2)).continuousOn).mul hc.norm
  obtain ⟨a, ha, hmax⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_isMaxOn
    ⟨0, mem_closedBall_self zero_le_one⟩ hW
  have hwa : s ≤ W a := by
    have hm := hmax (mem_closedBall_self (x := (0 : ℂ)) zero_le_one)
    simpa [W, hf0, abs_of_pos hs0] using hm
  have ha' : ‖a‖ < 1 := by
    have ham : ‖a‖ ≤ 1 := mem_closedBall_zero_iff.mp ha
    apply lt_of_le_of_ne ham
    intro he
    simp [W, he, hs0.not_ge] at hwa
  let d : ℂ := deriv f a * (1 - (‖a‖ ^ 2 : ℝ))
  have hdn : ‖d‖ = W a := by
    have hap : 0 ≤ 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
    dsimp [d, W]
    rw [show (1 : ℂ) - ↑(‖a‖ ^ 2) = ↑(1 - ‖a‖ ^ 2 : ℝ) by push_cast; rfl,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hap, mul_comm]
  have hd0 : d ≠ 0 := norm_pos_iff.mp (by rw [hdn]; exact hs0.trans_le hwa)
  let g : ℂ → ℂ := fun z => (f (mobius a z) - f a) / d
  have hgd (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) :
      HasDerivAt g ((deriv f (mobius a z) * deriv (mobius a) z) / d) z := by
    have hp := hasDerivAt_mobius ha' (mem_ball_zero_iff.mp hz)
    have hza := maps_mobius ha' hz
    have hfd := hf.differentiableAt
      (isOpen_ball.mem_nhds (ball_subset_ball hsf.le hza))
    exact (((hfd.hasDerivAt.comp z (hp.deriv ▸ hp)).sub_const (f a)).div_const d)
  have hgD : DifferentiableOn ℂ g (ball 0 1) :=
    fun z hz => (hgd z hz).differentiableAt.differentiableWithinAt
  have hg0 : g 0 = 0 := by simp [g, mobius_zero]
  have hgD0 : deriv g 0 = 1 := by
    rw [(hgd 0 h0mem).deriv, mobius_zero,
      (hasDerivAt_mobius ha' (by simp : ‖(0 : ℂ)‖ < 1)).deriv]
    simpa [d] using div_self hd0
  have hgne (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : deriv g z ≠ 0 := by
    rw [(hgd z hz).deriv]
    exact div_ne_zero
      (mul_ne_zero (hfne _ (maps_mobius ha' hz))
        (deriv_mobius_ne_zero ha' (mem_ball_zero_iff.mp hz))) hd0
  have hgW (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) :
      (1 - ‖z‖ ^ 2) * ‖deriv g z‖ ≤ 1 := by
    have hz' := maps_mobius ha' hz
    rw [(hgd z hz).deriv, norm_div, norm_mul, mul_comm ‖deriv f (mobius a z)‖,
      ← mul_div_assoc, ← mul_assoc, mobius_weight ha' (mem_ball_zero_iff.mp hz),
      div_le_one (norm_pos_iff.mpr hd0), hdn]
    exact hmax (ball_subset_closedBall hz')
  obtain ⟨c, hc⟩ := hNorm g hgD hg0 hgD0 hgne hgW
  let c' := d * c + f a
  refine ⟨c', ?_⟩
  intro w hw
  have hw' : (w - f a) / d ∈ ball c R := by
    rw [mem_ball_iff_norm] at hw ⊢
    have he : (w - f a) / d - c = (w - c') / d := by
      dsimp [c']
      field_simp [hd0]
      ring
    rw [he, norm_div, div_lt_iff₀ (norm_pos_iff.mpr hd0), hdn]
    exact hw.trans (hsB'.trans_le (by nlinarith))
  obtain ⟨z, hz, he⟩ := hc hw'
  refine ⟨(s : ℂ) * mobius a z, ?_, ?_⟩
  · have hm := mem_ball_zero_iff.mp (maps_mobius ha' hz)
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
    nlinarith
  · change f (mobius a z) = w
    have h1 : (f (mobius a z) - f a) / d = (w - f a) / d := he
    have h2 : f (mobius a z) - f a = w - f a := (div_left_inj' hd0).mp h1
    exact sub_left_inj.mp h2

end LandauNorm

/- ## Section 2: Holomorphic logarithm, coefficient bounds, and normalization -/

namespace LandauLog

theorem deriv_zero_of_weight {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hf0 : f 0 = 1)
    (hW : ∀ z ∈ ball (0 : ℂ) 1, (1 - ‖z‖ ^ 2) * ‖f z‖ ≤ 1) : deriv f 0 = 0 := by
  let a := deriv f 0
  let g : ℂ → ℂ := fun z => ((1 : ℂ) - z ^ 2 * (↑‖a‖ : ℂ) ^ 2) * f (conj a * z)
  have hfd : HasDerivAt f a (conj a * 0) := by
    simpa [a] using (hf.differentiableAt (ball_mem_nhds (0 : ℂ) zero_lt_one)).hasDerivAt
  have hgd : HasDerivAt g (a * conj a) 0 := by
    have hh := hfd.comp 0 ((hasDerivAt_id (0 : ℂ)).const_mul (conj a))
    have hp : HasDerivAt (fun z : ℂ => (1 : ℂ) - z ^ 2 * (↑‖a‖ : ℂ) ^ 2) 0 0 := by
      simpa using (((hasDerivAt_id (0 : ℂ)).fun_pow 2).mul_const ((↑‖a‖ : ℂ) ^ 2)).const_sub 1
    simpa [g, Function.comp_def] using! hp.mul hh
  have hr := hgd.real_of_complex (z := (0 : ℝ))
  have hloc : IsLocalMax (fun t : ℝ => (g t).re) 0 := by
    change ∀ᶠ t : ℝ in 𝓝 0, (g t).re ≤ (g 0).re
    have hc : Continuous (fun t : ℝ => conj a * (t : ℂ)) := by fun_prop
    have hh : ∀ᶠ t : ℝ in 𝓝 0, conj a * (t : ℂ) ∈ ball (0 : ℂ) 1 := by
      have he : Tendsto (fun t : ℝ => conj a * (t : ℂ)) (𝓝 0) (𝓝 (0 : ℂ)) := by
        simpa using hc.tendsto (0 : ℝ)
      exact he.eventually (ball_mem_nhds (0 : ℂ) zero_lt_one)
    filter_upwards [hh] with t ht
    have hn : ‖conj a * (t : ℂ)‖ ^ 2 = t ^ 2 * ‖a‖ ^ 2 := by
      rw [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    have hp : 0 ≤ 1 - t ^ 2 * ‖a‖ ^ 2 := by
      have hh' := mem_ball_zero_iff.mp ht
      nlinarith [norm_nonneg (conj a * (t : ℂ))]
    have hwt := hW _ ht
    rw [hn] at hwt
    have hle := mul_le_mul_of_nonneg_left (Complex.re_le_norm (f (conj a * (t : ℂ)))) hp
    simpa [g, hf0, ← Complex.ofReal_sub, ← Complex.ofReal_mul, ← Complex.ofReal_pow]
      using hle.trans hwt
  have hzero := hloc.hasDerivAt_eq_zero hr
  have hh : ‖a‖ ^ 2 = 0 := by
    simpa [Complex.mul_conj, Complex.sq_norm] using hzero
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hh)

theorem exists_holo_log {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1))
    (hg1 : deriv g 0 = 1) (hgne : ∀ z ∈ ball (0 : ℂ) 1, deriv g z ≠ 0) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (ball 0 1) ∧ h 0 = 0 ∧
      ∀ z ∈ ball (0 : ℂ) 1, Complex.exp (h z) = deriv g z := by
  have hg' : DifferentiableOn ℂ (deriv g) (ball 0 1) := hg.deriv isOpen_ball
  have hq : DifferentiableOn ℂ (fun z => deriv (deriv g) z / deriv g z) (ball 0 1) :=
    (hg'.deriv isOpen_ball).div hg' hgne
  obtain ⟨h, hh0, hhd⟩ := hq.isExactOn_ball.with_val_at 0 0
  have hhD : DifferentiableOn ℂ h (ball 0 1) :=
    fun z hz => (hhd z hz).differentiableAt.differentiableWithinAt
  let k : ℂ → ℂ := fun z => Complex.exp (-h z) * deriv g z
  have hkd (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : HasDerivAt k 0 z := by
    have h1 : HasDerivAt (fun w => Complex.exp (-h w))
        (Complex.exp (-h z) * -(deriv (deriv g) z / deriv g z)) z :=
      (hhd z hz).neg.cexp
    have h2 : HasDerivAt (deriv g) (deriv (deriv g) z) z :=
      (hg'.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    have h3 := h1.mul h2
    have hzero : Complex.exp (-h z) * -(deriv (deriv g) z / deriv g z) * deriv g z +
        Complex.exp (-h z) * deriv (deriv g) z = 0 := by
      have hne := hgne z hz
      field_simp [hne]
      ring
    rwa [hzero] at h3
  have hkD : DifferentiableOn ℂ k (ball 0 1) :=
    fun z hz => (hkd z hz).differentiableAt.differentiableWithinAt
  have hk0 : EqOn (deriv k) 0 (ball 0 1) := fun z hz => (hkd z hz).deriv
  refine ⟨h, hhD, hh0, ?_⟩
  intro z hz
  have hconst := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) 1).isPreconnected
    hkD hk0 hz (mem_ball_self zero_lt_one)
  have hkval : Complex.exp (-h z) * deriv g z = 1 := by
    simpa [k, hh0, hg1] using hconst
  calc
    Complex.exp (h z) = Complex.exp (h z) * (Complex.exp (-h z) * deriv g z) := by
      rw [hkval, mul_one]
    _ = (Complex.exp (h z) * Complex.exp (-h z)) * deriv g z := by ring
    _ = deriv g z := by rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]

theorem re_log_le {g h : ℂ → ℂ}
    (hW : ∀ z ∈ ball (0 : ℂ) 1, (1 - ‖z‖ ^ 2) * ‖deriv g z‖ ≤ 1)
    (hexp : ∀ z ∈ ball (0 : ℂ) 1, Complex.exp (h z) = deriv g z)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    (h z).re ≤ -Real.log (1 - ‖z‖ ^ 2) := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hp : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hnorm : Real.exp (h z).re = ‖deriv g z‖ := by
    rw [← hexp z hz, Complex.norm_exp]
  have hle : Real.exp (h z).re ≤ (1 - ‖z‖ ^ 2)⁻¹ := by
    rw [hnorm, ← one_div, le_div_iff₀ hp, mul_comm]
    exact hW z hz
  have hlog := Real.log_le_log (Real.exp_pos _) hle
  rwa [Real.log_exp, Real.log_inv] at hlog

theorem deriv_log_zero {g h : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball 0 1)) (hg1 : deriv g 0 = 1)
    (hW : ∀ z ∈ ball (0 : ℂ) 1, (1 - ‖z‖ ^ 2) * ‖deriv g z‖ ≤ 1)
    (hh : DifferentiableOn ℂ h (ball 0 1)) (hh0 : h 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) 1, Complex.exp (h z) = deriv g z) :
    deriv h 0 = 0 := by
  have hg'0 : deriv (deriv g) 0 = 0 :=
    deriv_zero_of_weight (hg.deriv isOpen_ball) hg1 hW
  have h0 : (0 : ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
  have hhd : HasDerivAt h (deriv h 0) 0 :=
    (hh.differentiableAt (isOpen_ball.mem_nhds h0)).hasDerivAt
  have he : HasDerivAt (fun z => Complex.exp (h z)) (Complex.exp (h 0) * deriv h 0) 0 :=
    hhd.cexp
  have heq : (fun z => Complex.exp (h z)) =ᶠ[𝓝 (0 : ℂ)] deriv g :=
    Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds h0) (fun z hz => hexp z hz)
  have hd : deriv (fun z => Complex.exp (h z)) 0 = deriv (deriv g) 0 := heq.deriv_eq
  rw [he.deriv, hh0, Complex.exp_zero, one_mul, hg'0] at hd
  exact hd

theorem cauchy_bound {f : ℂ → ℂ} {R M : ℝ}
    (hR : 0 < R) (hc : ContinuousOn f (sphere 0 R))
    (hM : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ M) (k : ℕ) :
    ‖(cauchyPowerSeries f 0 R).coeff k‖ ≤ M * R⁻¹ ^ k := by
  have hi : IntervalIntegrable (fun θ : ℝ => ‖f (circleMap 0 R θ)‖)
      MeasureTheory.volume 0 (2 * Real.pi) := by
    have hmaps : MapsTo (circleMap 0 R) (uIcc 0 (2 * Real.pi)) (sphere 0 R) :=
      fun θ _ => circleMap_mem_sphere 0 hR.le θ
    exact (hc.comp (continuous_circleMap 0 R).continuousOn hmaps).norm.intervalIntegrable
  have hI : (∫ θ in (0 : ℝ)..2 * Real.pi, ‖f (circleMap 0 R θ)‖) ≤ (2 * Real.pi) * M := by
    calc
      _ ≤ ∫ _θ in (0 : ℝ)..2 * Real.pi, M :=
        intervalIntegral.integral_mono_on Real.two_pi_pos.le hi intervalIntegrable_const
          (fun θ _ => hM _ (circleMap_mem_sphere 0 hR.le θ))
      _ = _ := by simp
  have hn : ‖(cauchyPowerSeries f 0 R).coeff k‖ = ‖cauchyPowerSeries f 0 R k‖ := by
    rw [← ContinuousMultilinearMap.mkPiRing_apply_one_eq_self (cauchyPowerSeries f 0 R k),
      ContinuousMultilinearMap.norm_mkPiRing]
    rfl
  calc
    _ = _ := hn
    _ ≤ _ := norm_cauchyPowerSeries_le f 0 R k
    _ ≤ ((2 * Real.pi)⁻¹ * ((2 * Real.pi) * M)) * R⁻¹ ^ k := by
      rw [abs_of_pos hR]
      gcongr
    _ = _ := by rw [inv_mul_cancel_left₀ Real.two_pi_pos.ne']

theorem hasSum_coeff (f : ℂ → ℂ) {R : ℝ≥0} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (closedBall 0 R)) {z : ℂ} (hz : ‖z‖ < R) :
    HasSum (fun k => (cauchyPowerSeries f 0 R).coeff k * z ^ k) (f z) := by
  have hs := hf.hasFPowerSeriesOnBall (c := 0) hR
  have he : ∀ k, ((cauchyPowerSeries f 0 R).coeff k) * z ^ k =
      cauchyPowerSeries f 0 R k (fun _ => z) := by
    intro k
    rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff]
    simp [smul_eq_mul, mul_comm]
  simp only [he]
  simpa only [zero_add] using hs.hasSum (y := z) (by
    rw [mem_eball_zero_iff]
    exact_mod_cast hz)

theorem coeff_eq_iteratedDeriv {f : ℂ → ℂ} {R : ℝ≥0} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (closedBall 0 R)) (n : ℕ) :
    (n.factorial : ℂ) * (cauchyPowerSeries f 0 R).coeff n = iteratedDeriv n f 0 := by
  have hs := (hf.hasFPowerSeriesOnBall (c := 0) hR).factorial_smul (1 : ℂ) n
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const_one, one_smul] at hs
  simpa only [FormalMultilinearSeries.coeff, nsmul_eq_mul, Pi.one_def] using hs

theorem truncation {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {u : ℕ → E} {S : E} (hs : HasSum u S)
    {C q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hu : ∀ n, ‖u n‖ ≤ C * q ^ n) (N : ℕ) :
    ‖S - ∑ n ∈ Finset.range N, u n‖ ≤ C * q ^ N / (1 - q) := by
  have hm (k : ℕ) : ‖u (k + N)‖ ≤ (C * q ^ N) * q ^ k := by
    have h := hu (k + N)
    rw [pow_add] at h
    convert h using 1
    ring
  have hg := (summable_geometric_of_lt_one hq0 hq1).mul_left (C * q ^ N)
  have hh := Summable.of_nonneg_of_le (fun k => norm_nonneg (u (k + N))) hm hg
  have htail : (∑ n ∈ Finset.range N, u n) + ∑' n, u (n + N) = S := by
    simpa only [hs.tsum_eq] using hs.summable.sum_add_tsum_nat_add N
  rw [← htail, add_sub_cancel_left]
  calc
    _ ≤ ∑' n, ‖u (n + N)‖ := norm_tsum_le_tsum_norm hh
    _ ≤ ∑' n, (C * q ^ N) * q ^ n := hh.tsum_le_tsum hm hg
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1, div_eq_mul_inv]

theorem coeff_bound_six {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (ball 0 1))
    (hh0 : h 0 = 0)
    (hre : ∀ z ∈ ball (0 : ℂ) 1, (h z).re ≤ -Real.log (1 - ‖z‖ ^ 2))
    (k : ℕ) :
    ‖(cauchyPowerSeries h 0 (1 / 2)).coeff k‖ ≤ 6 * (2 : ℝ) ^ k := by
  have hsub34 : ball (0 : ℂ) (3 / 4) ⊆ ball 0 1 := ball_subset_ball (by norm_num)
  have hmaps : MapsTo h (ball 0 (3 / 4)) {w : ℂ | w.re ≤ 9 / 7} := by
    intro z hz
    have hz' : ‖z‖ < 3 / 4 := mem_ball_zero_iff.mp hz
    have h1 : (7 / 16 : ℝ) ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have h2 : -Real.log (1 - ‖z‖ ^ 2) ≤ Real.log (16 / 7) := by
      have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 7 / 16) h1
      have hinv : -Real.log (7 / 16 : ℝ) = Real.log (16 / 7 : ℝ) := by
        rw [← Real.log_inv]
        norm_num
      linarith
    have h3 : Real.log (16 / 7 : ℝ) ≤ 9 / 7 := by
      have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 16 / 7)
      linarith
    exact (hre z (hsub34 hz)).trans (h2.trans h3)
  have hbound : ∀ z ∈ sphere (0 : ℂ) (1 / 2), ‖h z‖ ≤ 6 := by
    intro z hz
    have hzn : ‖z‖ = 1 / 2 := mem_sphere_zero_iff_norm.mp hz
    have hz34 : z ∈ ball (0 : ℂ) (3 / 4) := by
      rw [mem_ball_zero_iff, hzn]
      norm_num
    have hbc := Complex.borelCaratheodory_zero (by norm_num : (0 : ℝ) < 9 / 7)
      (hh.mono hsub34) hmaps (by norm_num : (0 : ℝ) < 3 / 4) hz34 hh0
    rw [hzn] at hbc
    linarith
  have hsub12 : sphere (0 : ℂ) (1 / 2) ⊆ ball 0 1 :=
    sphere_subset_closedBall.trans (closedBall_subset_ball (by norm_num))
  have hc := cauchy_bound (f := h) (R := 1 / 2) (M := 6) (by norm_num)
    (hh.continuousOn.mono hsub12) hbound k
  convert hc using 2
  norm_num

theorem tail_bound_192 {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (ball 0 1))
    (hh0 : h 0 = 0) (hh1 : deriv h 0 = 0)
    (hre : ∀ z ∈ ball (0 : ℂ) 1, (h z).re ≤ -Real.log (1 - ‖z‖ ^ 2))
    {z : ℂ} (hz : ‖z‖ ≤ 1 / 4) :
    ‖h z - ((cauchyPowerSeries h 0 (1 / 2)).coeff 2 * z ^ 2 +
      (cauchyPowerSeries h 0 (1 / 2)).coeff 3 * z ^ 3)‖ ≤ 192 * ‖z‖ ^ 4 := by
  let R : ℝ≥0 := ⟨1 / 2, by norm_num⟩
  have hR : 0 < R := by exact_mod_cast (by norm_num : (0 : ℝ) < 1 / 2)
  have hRval : (R : ℝ) = 1 / 2 := rfl
  have hhR : DifferentiableOn ℂ h (closedBall 0 R) :=
    hh.mono (closedBall_subset_ball (by exact_mod_cast (by norm_num : (1 / 2 : ℝ) < 1)))
  have hsum : HasSum (fun k => (cauchyPowerSeries h 0 (1 / 2)).coeff k * z ^ k) (h z) := by
    simpa only [hRval] using hasSum_coeff h hR hhR (z := z) (by
      change ‖z‖ < (1 / 2 : ℝ)
      linarith)
  have hc0 : (cauchyPowerSeries h 0 (1 / 2)).coeff 0 = 0 := by
    have := coeff_eq_iteratedDeriv hR hhR 0
    rw [hRval] at this
    simpa [hh0] using this
  have hc1 : (cauchyPowerSeries h 0 (1 / 2)).coeff 1 = 0 := by
    have := coeff_eq_iteratedDeriv hR hhR 1
    rw [hRval] at this
    simpa [hh1] using this
  have hq0 : 0 ≤ 2 * ‖z‖ := by positivity
  have hq1 : 2 * ‖z‖ < 1 := by linarith
  have hu (n : ℕ) : ‖(cauchyPowerSeries h 0 (1 / 2)).coeff n * z ^ n‖ ≤
      6 * (2 * ‖z‖) ^ n := by
    rw [norm_mul, norm_pow, mul_pow]
    have hb := coeff_bound_six hh hh0 hre n
    calc
      ‖(cauchyPowerSeries h 0 (1 / 2)).coeff n‖ * ‖z‖ ^ n
        ≤ (6 * (2 : ℝ) ^ n) * ‖z‖ ^ n := by gcongr
      _ = 6 * ((2 : ℝ) ^ n * ‖z‖ ^ n) := by ring
  have htr := truncation hsum hq0 hq1 hu 4
  have hsum4 : (∑ n ∈ Finset.range 4, (cauchyPowerSeries h 0 (1 / 2)).coeff n * z ^ n) =
      (cauchyPowerSeries h 0 (1 / 2)).coeff 2 * z ^ 2 +
      (cauchyPowerSeries h 0 (1 / 2)).coeff 3 * z ^ 3 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero, hc0, hc1]
    ring
  rw [hsum4] at htr
  refine htr.trans ?_
  have hden : (1 / 2 : ℝ) ≤ 1 - 2 * ‖z‖ := by linarith
  have hnum : 6 * (2 * ‖z‖) ^ 4 = 96 * ‖z‖ ^ 4 := by ring
  rw [hnum, div_le_iff₀ (by linarith)]
  nlinarith [pow_nonneg (norm_nonneg z) 4]

theorem neg_log_one_sub_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    -Real.log (1 - t) ≤ t + t ^ 2 := by
  let φ : ℝ → ℝ := fun x => x + x ^ 2 + Real.log (1 - x)
  have hcont : ContinuousOn φ (Icc 0 (1 / 2)) := by
    refine ContinuousOn.add (by fun_prop) ?_
    refine ContinuousOn.log (by fun_prop) ?_
    intro x hx
    linarith [hx.2]
  have hderiv : ∀ x ∈ interior (Icc (0 : ℝ) (1 / 2)),
      HasDerivWithinAt φ (1 + 2 * x - 1 / (1 - x)) (interior (Icc (0 : ℝ) (1 / 2))) x := by
    intro x hx
    rw [interior_Icc] at hx
    have h1 : HasDerivAt (fun y : ℝ => y + y ^ 2) (1 + 2 * x) x := by
      have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
        simpa using hasDerivAt_pow 2 x
      exact (hasDerivAt_id x).add hsq
    have h2 : HasDerivAt (fun y : ℝ => Real.log (1 - y)) (-(1 - x)⁻¹) x := by
      have hsub : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
        simpa using (hasDerivAt_id x).const_sub 1
      have hne : 1 - x ≠ 0 := by linarith [hx.2]
      simpa [div_eq_mul_inv] using hsub.log hne
    refine (h1.add h2).hasDerivWithinAt.congr_deriv ?_
    rw [one_div]
    ring
  have hnonneg : ∀ x ∈ interior (Icc (0 : ℝ) (1 / 2)), 0 ≤ 1 + 2 * x - 1 / (1 - x) := by
    intro x hx
    rw [interior_Icc] at hx
    have hpos : 0 < 1 - x := by linarith [hx.2]
    have heq : 1 + 2 * x - 1 / (1 - x) = x * (1 - 2 * x) / (1 - x) := by
      field_simp [hpos.ne']
      ring
    rw [heq]
    exact div_nonneg (mul_nonneg hx.1.le (by linarith [hx.2])) hpos.le
  have hmono : MonotoneOn φ (Icc 0 (1 / 2)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 (1 / 2)) hcont hderiv hnonneg
  have h0le := hmono ⟨le_rfl, by norm_num⟩ ⟨ht0, ht1⟩ ht0
  simp only [φ, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    sub_zero, Real.log_one] at h0le
  linarith

private theorem iteratedDeriv_holo_ball {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1)) :
    ∀ n : ℕ, DifferentiableOn ℂ (iteratedDeriv n f) (ball 0 1)
  | 0 => by simpa [iteratedDeriv_zero] using hf
  | n + 1 => by
    rw [iteratedDeriv_succ]
    exact (iteratedDeriv_holo_ball hf n).deriv isOpen_ball

private theorem iteratedDeriv_comp_rot {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1))
    {α : ℂ} (hα : ‖α‖ = 1) :
    ∀ n : ℕ, ∀ z ∈ ball (0 : ℂ) 1,
      iteratedDeriv n (fun w => f (α * w)) z = α ^ n * iteratedDeriv n f (α * z)
  | 0, z, _ => by simp
  | n + 1, z, hz => by
    have hmaps : MapsTo (fun w : ℂ => α * w) (ball 0 1) (ball 0 1) := by
      intro w hw
      rw [mem_ball_zero_iff] at hw ⊢
      simpa [norm_mul, hα] using hw
    have heq : iteratedDeriv n (fun w => f (α * w)) =ᶠ[𝓝 z]
        fun w => α ^ n * iteratedDeriv n f (α * w) :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz)
        (fun w hw => iteratedDeriv_comp_rot hf hα n w hw)
    rw [iteratedDeriv_succ, heq.deriv_eq]
    have hd1 : HasDerivAt (iteratedDeriv n f) (deriv (iteratedDeriv n f) (α * z)) (α * z) :=
      ((iteratedDeriv_holo_ball hf n).differentiableAt
        (isOpen_ball.mem_nhds (hmaps hz))).hasDerivAt
    have hd2 : HasDerivAt (fun w : ℂ => α * w) α z := by
      simpa using (hasDerivAt_id z).const_mul α
    have hd3 : HasDerivAt (fun w => α ^ n * iteratedDeriv n f (α * w))
        (α ^ n * (deriv (iteratedDeriv n f) (α * z) * α)) z :=
      (hd1.comp z hd2).const_mul (α ^ n)
    rw [hd3.deriv, iteratedDeriv_succ]
    ring

theorem coeff_rot {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (ball 0 1))
    {α : ℂ} (hα : ‖α‖ = 1) (n : ℕ) :
    (cauchyPowerSeries (fun z => h (α * z)) 0 (1 / 2)).coeff n =
      α ^ n * (cauchyPowerSeries h 0 (1 / 2)).coeff n := by
  let R : ℝ≥0 := ⟨1 / 2, by norm_num⟩
  have hR : 0 < R := by exact_mod_cast (by norm_num : (0 : ℝ) < 1 / 2)
  have hRval : (R : ℝ) = 1 / 2 := rfl
  have hmaps : MapsTo (fun z : ℂ => α * z) (ball 0 1) (ball 0 1) := by
    intro z hz
    rw [mem_ball_zero_iff] at hz ⊢
    simpa [norm_mul, hα] using hz
  have hhα : DifferentiableOn ℂ (fun z => h (α * z)) (ball 0 1) :=
    hh.comp ((differentiable_const α).mul differentiable_id).differentiableOn hmaps
  have hRsub : closedBall (0 : ℂ) R ⊆ ball 0 1 :=
    closedBall_subset_ball (by exact_mod_cast (by norm_num : (1 / 2 : ℝ) < 1))
  have h1 := coeff_eq_iteratedDeriv hR (hhα.mono hRsub) n
  have h2 := coeff_eq_iteratedDeriv hR (hh.mono hRsub) n
  rw [hRval] at h1 h2
  have h3 := iteratedDeriv_comp_rot hh hα n 0 (mem_ball_self zero_lt_one)
  rw [mul_zero] at h3
  have hfac : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  apply mul_left_cancel₀ hfac
  calc
    (n.factorial : ℂ) * (cauchyPowerSeries (fun z => h (α * z)) 0 (1 / 2)).coeff n
      = iteratedDeriv n (fun z => h (α * z)) 0 := h1
    _ = α ^ n * iteratedDeriv n h 0 := h3
    _ = α ^ n * ((n.factorial : ℂ) * (cauchyPowerSeries h 0 (1 / 2)).coeff n) := by rw [← h2]
    _ = (n.factorial : ℂ) * (α ^ n * (cauchyPowerSeries h 0 (1 / 2)).coeff n) := by ring

theorem rotation_normalization {g h : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball 0 1)) (hg0 : g 0 = 0) (hg1 : deriv g 0 = 1)
    (hgne : ∀ z ∈ ball (0 : ℂ) 1, deriv g z ≠ 0)
    (hW : ∀ z ∈ ball (0 : ℂ) 1, (1 - ‖z‖ ^ 2) * ‖deriv g z‖ ≤ 1)
    (hh : DifferentiableOn ℂ h (ball 0 1)) (hh0 : h 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) 1, Complex.exp (h z) = deriv g z) :
    ∃ α : ℂ, ‖α‖ = 1 ∧
      let gα : ℂ → ℂ := fun z => α⁻¹ * g (α * z)
      let hα : ℂ → ℂ := fun z => h (α * z)
      DifferentiableOn ℂ gα (ball 0 1) ∧ gα 0 = 0 ∧ deriv gα 0 = 1 ∧
      (∀ z ∈ ball (0 : ℂ) 1, deriv gα z ≠ 0) ∧
      (∀ z ∈ ball (0 : ℂ) 1, (1 - ‖z‖ ^ 2) * ‖deriv gα z‖ ≤ 1) ∧
      DifferentiableOn ℂ hα (ball 0 1) ∧ hα 0 = 0 ∧
      (∀ z ∈ ball (0 : ℂ) 1, Complex.exp (hα z) = deriv gα z) ∧
      ((cauchyPowerSeries hα 0 (1 / 2)).coeff 2).im = 0 ∧
      0 ≤ ((cauchyPowerSeries hα 0 (1 / 2)).coeff 2).re ∧
      0 ≤ ((cauchyPowerSeries hα 0 (1 / 2)).coeff 3).im := by
  let c2 := (cauchyPowerSeries h 0 (1 / 2)).coeff 2
  let c3 := (cauchyPowerSeries h 0 (1 / 2)).coeff 3
  let α₁ : ℂ := if c2 = 0 then 1 else Complex.exp (-(Complex.arg c2 / 2 : ℝ) * Complex.I)
  have hα₁_norm : ‖α₁‖ = 1 := by
    dsimp [α₁]
    split_ifs
    · simp
    · simpa [Complex.ofReal_neg] using
        Complex.norm_exp_ofReal_mul_I (-(Complex.arg c2 / 2))
  have hα₁_c2 : α₁ ^ 2 * c2 = (‖c2‖ : ℂ) := by
    dsimp [α₁]
    split_ifs with hc
    · simp [hc]
    · have hexp2 : Complex.exp (-(Complex.arg c2 / 2 : ℝ) * Complex.I) ^ 2 =
          Complex.exp (-(Complex.arg c2 : ℂ) * Complex.I) := by
        rw [sq, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [hexp2]
      nth_rw 2 [← Complex.norm_mul_exp_arg_mul_I c2]
      calc
        Complex.exp (-(Complex.arg c2 : ℂ) * Complex.I) *
            ((‖c2‖ : ℂ) * Complex.exp ((Complex.arg c2 : ℂ) * Complex.I))
          = (‖c2‖ : ℂ) * (Complex.exp (-(Complex.arg c2 : ℂ) * Complex.I) *
            Complex.exp ((Complex.arg c2 : ℂ) * Complex.I)) := by ring
        _ = (‖c2‖ : ℂ) := by
            rw [← Complex.exp_add, show -(Complex.arg c2 : ℂ) * Complex.I +
              (Complex.arg c2 : ℂ) * Complex.I = 0 by ring, Complex.exp_zero, mul_one]
  let α : ℂ := if 0 ≤ (α₁ ^ 3 * c3).im then α₁ else -α₁
  have hα_norm : ‖α‖ = 1 := by
    dsimp [α]
    split_ifs <;> simp [hα₁_norm]
  have hα_ne : α ≠ 0 := norm_pos_iff.mp (by linarith)
  have hα_c2 : α ^ 2 * c2 = (‖c2‖ : ℂ) := by
    dsimp [α]
    split_ifs
    · exact hα₁_c2
    · simpa [neg_sq] using hα₁_c2
  have hα_c3 : 0 ≤ (α ^ 3 * c3).im := by
    dsimp [α]
    split_ifs with h
    · exact h
    · have : (-α₁) ^ 3 * c3 = -(α₁ ^ 3 * c3) := by ring
      rw [this, Complex.neg_im]
      linarith
  refine ⟨α, hα_norm, ?_⟩
  dsimp only
  have hmaps : MapsTo (fun z : ℂ => α * z) (ball 0 1) (ball 0 1) := by
    intro z hz
    rw [mem_ball_zero_iff] at hz ⊢
    simpa [norm_mul, hα_norm] using hz
  have hgα_deriv (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) :
      HasDerivAt (fun w => α⁻¹ * g (α * w)) (deriv g (α * z)) z := by
    have h1 := (hg.differentiableAt (isOpen_ball.mem_nhds (hmaps hz))).hasDerivAt
    have h2 : HasDerivAt (fun w : ℂ => α * w) α z := by
      simpa using (hasDerivAt_id z).const_mul α
    have h3 : HasDerivAt (fun w => α⁻¹ * g (α * w)) (α⁻¹ * (deriv g (α * z) * α)) z :=
      (h1.comp z h2).const_mul α⁻¹
    refine h3.congr_deriv ?_
    rw [mul_comm (deriv g (α * z)) α, ← mul_assoc, inv_mul_cancel₀ hα_ne, one_mul]
  refine ⟨fun z hz => (hgα_deriv z hz).differentiableAt.differentiableWithinAt,
    by simp [hg0], by rw [(hgα_deriv 0 (mem_ball_self zero_lt_one)).deriv]; simp [hg1],
    fun z hz => by rw [(hgα_deriv z hz).deriv]; exact hgne _ (hmaps hz),
    fun z hz => by
      rw [(hgα_deriv z hz).deriv]
      have hz' := hmaps hz
      have := hW (α * z) hz'
      simpa [norm_mul, hα_norm] using this,
    hh.comp ((differentiable_const α).mul differentiable_id).differentiableOn hmaps,
    by simp [hh0],
    fun z hz => by rw [(hgα_deriv z hz).deriv]; exact hexp _ (hmaps hz),
    ?_, ?_, ?_⟩
  · rw [coeff_rot hh hα_norm 2]
    change (α ^ 2 * c2).im = 0
    rw [hα_c2, Complex.ofReal_im]
  · rw [coeff_rot hh hα_norm 2]
    change 0 ≤ (α ^ 2 * c2).re
    rw [hα_c2, Complex.ofReal_re]
    exact norm_nonneg c2
  · rw [coeff_rot hh hα_norm 3]
    exact hα_c3

theorem a_le_one {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (ball 0 1))
    (hh0 : h 0 = 0) (hh1 : deriv h 0 = 0)
    (hre : ∀ z ∈ ball (0 : ℂ) 1, (h z).re ≤ -Real.log (1 - ‖z‖ ^ 2))
    (hc2_im : ((cauchyPowerSeries h 0 (1 / 2)).coeff 2).im = 0) :
    ((cauchyPowerSeries h 0 (1 / 2)).coeff 2).re ≤ 1 := by
  set a := ((cauchyPowerSeries h 0 (1 / 2)).coeff 2).re
  set p := ((cauchyPowerSeries h 0 (1 / 2)).coeff 3).re
  have hc2 : (cauchyPowerSeries h 0 (1 / 2)).coeff 2 = (a : ℂ) :=
    Complex.ext rfl hc2_im
  have hstep : ∀ r : ℝ, 0 < r → r ≤ 1 / 4 → a ≤ 1 + 193 * r ^ 2 := by
    intro r hr0 hr4
    have hpos_r : ‖(r : ℂ)‖ = r := by simp [abs_of_pos hr0]
    have hneg_r : ‖(-(r : ℂ))‖ = r := by simp [abs_of_pos hr0]
    have ht1 := tail_bound_192 hh hh0 hh1 hre (z := (r : ℂ)) (by rw [hpos_r]; exact hr4)
    have ht2 := tail_bound_192 hh hh0 hh1 hre (z := -(r : ℂ)) (by rw [hneg_r]; exact hr4)
    rw [hpos_r] at ht1
    rw [hneg_r] at ht2
    have hre1 : (h (r : ℂ)).re ≤ r ^ 2 + r ^ 4 := by
      have h1 := hre (r : ℂ) (by rw [mem_ball_zero_iff, hpos_r]; linarith)
      rw [hpos_r] at h1
      have h2 := neg_log_one_sub_le (t := r ^ 2) (sq_nonneg r) (by nlinarith)
      linarith
    have hre2 : (h (-(r : ℂ))).re ≤ r ^ 2 + r ^ 4 := by
      have h1 := hre (-(r : ℂ)) (by rw [mem_ball_zero_iff, hneg_r]; linarith)
      rw [hneg_r] at h1
      have h2 := neg_log_one_sub_le (t := r ^ 2) (sq_nonneg r) (by nlinarith)
      linarith
    have he1 : ((cauchyPowerSeries h 0 (1 / 2)).coeff 2 * (r : ℂ) ^ 2 +
        (cauchyPowerSeries h 0 (1 / 2)).coeff 3 * (r : ℂ) ^ 3).re = a * r ^ 2 + p * r ^ 3 := by
      rw [hc2, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        mul_zero, sub_zero]
      rfl
    have he2 : ((cauchyPowerSeries h 0 (1 / 2)).coeff 2 * (-(r : ℂ)) ^ 2 +
        (cauchyPowerSeries h 0 (1 / 2)).coeff 3 * (-(r : ℂ)) ^ 3).re = a * r ^ 2 - p * r ^ 3 := by
      rw [hc2]
      have hsq : (-(r : ℂ)) ^ 2 = ((r ^ 2 : ℝ) : ℂ) := by push_cast; ring
      have hcb : (-(r : ℂ)) ^ 3 = ((-(r ^ 3) : ℝ) : ℂ) := by push_cast; ring
      rw [hsq, hcb, ← Complex.ofReal_mul]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        mul_zero, sub_zero]
      dsimp [p]
      ring
    have hd1 := (neg_le_abs _).trans (Complex.abs_re_le_norm _) |>.trans ht1
    have hd2 := (neg_le_abs _).trans (Complex.abs_re_le_norm _) |>.trans ht2
    simp only [Complex.sub_re, he1] at hd1
    simp only [Complex.sub_re, he2] at hd2
    have hsum : 2 * a * r ^ 2 ≤ 2 * (r ^ 2 + 193 * r ^ 4) := by linarith
    have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr0
    nlinarith
  by_contra! hgt
  let r : ℝ := min (1 / 4) ((a - 1) / 400)
  have hr0 : 0 < r := lt_min (by norm_num) (by linarith)
  have hr4 : r ≤ 1 / 4 := min_le_left _ _
  have hr2 : r ≤ (a - 1) / 400 := min_le_right _ _
  have hle := hstep r hr0 hr4
  nlinarith

theorem abs_p_le_of_a_close {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (ball 0 1))
    (hh0 : h 0 = 0) (hh1 : deriv h 0 = 0)
    (hre : ∀ z ∈ ball (0 : ℂ) 1, (h z).re ≤ -Real.log (1 - ‖z‖ ^ 2))
    (hc2_im : ((cauchyPowerSeries h 0 (1 / 2)).coeff 2).im = 0)
    (ha : 1 - 1 / (10 : ℝ) ^ 8 < ((cauchyPowerSeries h 0 (1 / 2)).coeff 2).re) :
    |((cauchyPowerSeries h 0 (1 / 2)).coeff 3).re| ≤ 1 / 50 := by
  set a := ((cauchyPowerSeries h 0 (1 / 2)).coeff 2).re
  set p := ((cauchyPowerSeries h 0 (1 / 2)).coeff 3).re
  have hc2 : (cauchyPowerSeries h 0 (1 / 2)).coeff 2 = (a : ℂ) :=
    Complex.ext rfl hc2_im
  let r : ℝ := 1 / 10000
  have hr0 : 0 < r := by norm_num [r]
  have hr4 : r ≤ 1 / 4 := by norm_num [r]
  have hpos_r : ‖(r : ℂ)‖ = r := by simp [abs_of_pos hr0]
  have hneg_r : ‖(-(r : ℂ))‖ = r := by simp [abs_of_pos hr0]
  have ht1 := tail_bound_192 hh hh0 hh1 hre (z := (r : ℂ)) (by rw [hpos_r]; exact hr4)
  have ht2 := tail_bound_192 hh hh0 hh1 hre (z := -(r : ℂ)) (by rw [hneg_r]; exact hr4)
  rw [hpos_r] at ht1
  rw [hneg_r] at ht2
  have hre1 : (h (r : ℂ)).re ≤ r ^ 2 + r ^ 4 := by
    have h1 := hre (r : ℂ) (by rw [mem_ball_zero_iff, hpos_r]; norm_num [r])
    rw [hpos_r] at h1
    have h2 := neg_log_one_sub_le (t := r ^ 2) (sq_nonneg r) (by norm_num [r])
    linarith
  have hre2 : (h (-(r : ℂ))).re ≤ r ^ 2 + r ^ 4 := by
    have h1 := hre (-(r : ℂ)) (by rw [mem_ball_zero_iff, hneg_r]; norm_num [r])
    rw [hneg_r] at h1
    have h2 := neg_log_one_sub_le (t := r ^ 2) (sq_nonneg r) (by norm_num [r])
    linarith
  have he1 : ((cauchyPowerSeries h 0 (1 / 2)).coeff 2 * (r : ℂ) ^ 2 +
      (cauchyPowerSeries h 0 (1 / 2)).coeff 3 * (r : ℂ) ^ 3).re = a * r ^ 2 + p * r ^ 3 := by
    rw [hc2, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    rfl
  have he2 : ((cauchyPowerSeries h 0 (1 / 2)).coeff 2 * (-(r : ℂ)) ^ 2 +
      (cauchyPowerSeries h 0 (1 / 2)).coeff 3 * (-(r : ℂ)) ^ 3).re = a * r ^ 2 - p * r ^ 3 := by
    rw [hc2]
    have hsq : (-(r : ℂ)) ^ 2 = ((r ^ 2 : ℝ) : ℂ) := by push_cast; ring
    have hcb : (-(r : ℂ)) ^ 3 = ((-(r ^ 3) : ℝ) : ℂ) := by push_cast; ring
    rw [hsq, hcb, ← Complex.ofReal_mul]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    dsimp [p]
    ring
  have hd1 := (neg_le_abs _).trans (Complex.abs_re_le_norm _) |>.trans ht1
  have hd2 := (neg_le_abs _).trans (Complex.abs_re_le_norm _) |>.trans ht2
  simp only [Complex.sub_re, he1] at hd1
  simp only [Complex.sub_re, he2] at hd2
  norm_num at ha
  have hrval : r = 1 / 10000 := rfl
  rw [hrval] at hre1 hre2 hd1 hd2
  rw [abs_le]
  constructor <;> linarith

end LandauLog

/- ## Section 3: Sharp Liu-Minda distortion bound -/

namespace LandauLiuMinda

noncomputable def ell (r : ℝ) : ℝ := Real.exp (-2 * r / (1 - r)) / (1 - r) ^ 2

noncomputable def E_fn (r : ℝ) : ℝ := (1 - Real.exp (-2 * r / (1 - r))) / 2

theorem ell_pos {r : ℝ} (hr : r < 1) : 0 < ell r :=
  div_pos (Real.exp_pos _) (sq_pos_of_pos (sub_pos.mpr hr))

theorem ell_zero : ell 0 = 1 := by simp [ell]

theorem E_fn_zero : E_fn 0 = 0 := by simp [E_fn]

theorem hasDerivAt_E_fn {r : ℝ} (hr : r < 1) : HasDerivAt E_fn (ell r) r := by
  have hne : 1 - r ≠ 0 := (sub_pos.mpr hr).ne'
  have hq : HasDerivAt (fun t : ℝ => -2 * t / (1 - t)) (-2 / (1 - r) ^ 2) r := by
    have hnum : HasDerivAt (fun t : ℝ => -2 * t) (-2) r := by
      simpa using (hasDerivAt_id r).const_mul (-2 : ℝ)
    have hden : HasDerivAt (fun t : ℝ => 1 - t) (-1) r := by
      simpa using (hasDerivAt_id r).const_sub (1 : ℝ)
    refine (hnum.div hden hne).congr_deriv ?_
    field_simp [hne]
    ring
  have hexp := hq.exp
  refine ((hexp.const_sub (1 : ℝ)).div_const (2 : ℝ)).congr_deriv ?_
  dsimp [ell]
  ring

theorem tendsto_E_fn : Tendsto E_fn (𝓝[<] (1 : ℝ)) (𝓝 (1 / 2)) := by
  have hdiv : Tendsto (fun r : ℝ => (1 - r)⁻¹) (𝓝[<] (1 : ℝ)) atTop := by
    have hsub : Tendsto (fun r : ℝ => 1 - r) (𝓝[<] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have hc : Continuous (fun r : ℝ => (1 : ℝ) - r) := by fun_prop
        simpa using (hc.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact sub_pos.mpr (mem_Iio.mp hr)
    exact tendsto_inv_nhdsGT_zero.comp hsub
  have hexp_arg : Tendsto (fun r : ℝ => -2 * r / (1 - r)) (𝓝[<] (1 : ℝ)) atBot := by
    have h1 : Tendsto (fun r : ℝ => -2 * r) (𝓝[<] (1 : ℝ)) (𝓝 (-2 : ℝ)) := by
      have hc : Continuous (fun r : ℝ => (-2 : ℝ) * r) := by fun_prop
      simpa using hc.tendsto 1 |>.mono_left nhdsWithin_le_nhds
    have h2 := Filter.Tendsto.neg_mul_atTop (by norm_num : (-2 : ℝ) < 0) h1 hdiv
    simpa [div_eq_mul_inv] using h2
  have hexp : Tendsto (fun r : ℝ => Real.exp (-2 * r / (1 - r))) (𝓝[<] (1 : ℝ)) (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hexp_arg
  change Tendsto (fun r : ℝ => (1 - Real.exp (-2 * r / (1 - r))) / 2) (𝓝[<] (1 : ℝ)) (𝓝 (1 / 2))
  simpa only [sub_zero] using ((tendsto_const_nhds (x := (1 : ℝ))).sub hexp).div_const 2

theorem log_ell_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Real.log (ell r) ≤ -r ^ 2 - (4 / 3) * r ^ 3 := by
  have hpos : 0 < 1 - r := sub_pos.mpr hr1
  have hlog : Real.log (ell r) = -2 * r / (1 - r) - 2 * Real.log (1 - r) := by
    rw [ell, Real.log_div (Real.exp_pos _).ne' (sq_pos_of_pos hpos).ne',
      Real.log_exp, Real.log_pow]
    push_cast
    ring
  rw [hlog]
  let φ : ℝ → ℝ := fun t => -2 * t / (1 - t) - 2 * Real.log (1 - t) + t ^ 2 + (4 / 3) * t ^ 3
  have hcont : ContinuousOn φ (Icc 0 r) := by
    have hne : ∀ t ∈ Icc 0 r, 1 - t ≠ 0 := fun t ht => by linarith [ht.2]
    refine (((ContinuousOn.div (by fun_prop) (by fun_prop) hne).sub
      (ContinuousOn.mul continuousOn_const
        (ContinuousOn.log (by fun_prop) hne))).add (by fun_prop)).add (by fun_prop)
  have hderiv : ∀ t ∈ interior (Icc 0 r),
      HasDerivWithinAt φ (2 * t ^ 3 * (2 * t - 3) / (1 - t) ^ 2) (interior (Icc 0 r)) t := by
    intro t ht
    rw [interior_Icc] at ht
    have hne : 1 - t ≠ 0 := by linarith [ht.2]
    have h1 : HasDerivAt (fun x : ℝ => -2 * x / (1 - x)) (-2 / (1 - t) ^ 2) t := by
      have ha : HasDerivAt (fun x : ℝ => -2 * x) (-2) t := by
        simpa using (hasDerivAt_id t).const_mul (-2 : ℝ)
      have hb : HasDerivAt (fun x : ℝ => 1 - x) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
      refine (ha.div hb hne).congr_deriv ?_
      field_simp [hne]
      ring
    have h2 : HasDerivAt (fun x : ℝ => 2 * Real.log (1 - x)) (-2 / (1 - t)) t := by
      have hb : HasDerivAt (fun x : ℝ => 1 - x) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
      refine ((hb.log hne).const_mul (2 : ℝ)).congr_deriv ?_
      ring
    have h3 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h4 : HasDerivAt (fun x : ℝ => (4 / 3 : ℝ) * x ^ 3) (4 * t ^ 2) t := by
      refine ((hasDerivAt_pow 3 t).const_mul (4 / 3 : ℝ)).congr_deriv ?_
      ring
    refine (((h1.sub h2).add h3).add h4).hasDerivWithinAt.congr_deriv ?_
    field_simp [hne]
    ring
  have hnonpos : ∀ t ∈ interior (Icc 0 r), 2 * t ^ 3 * (2 * t - 3) / (1 - t) ^ 2 ≤ 0 := by
    intro t ht
    rw [interior_Icc] at ht
    refine div_nonpos_of_nonpos_of_nonneg ?_ (sq_nonneg _)
    have ht0 : 0 ≤ t ^ 3 := pow_nonneg ht.1.le 3
    have ht1 : 2 * t - 3 ≤ 0 := by linarith [ht.2]
    nlinarith
  have hanti := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 r) hcont hderiv hnonpos
  have hle := hanti ⟨le_rfl, hr0⟩ ⟨hr0, le_rfl⟩ hr0
  simp only [φ, mul_zero, sub_zero, zero_div, Real.log_one, sub_self, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at hle
  linarith

theorem half_le_ell {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 5) : 1 / 2 ≤ ell r := by
  have h1 : 0 < 1 - r := by linarith
  have h2 : (1 - r) ^ 2 ≤ 1 := by nlinarith
  have hexp : 1 - 2 * r / (1 - r) ≤ Real.exp (-2 * r / (1 - r)) := by
    have hle := Real.add_one_le_exp (-2 * r / (1 - r))
    have heq : -2 * r / (1 - r) = -(2 * r / (1 - r)) := by ring
    linarith
  have h3 : (1 / 2 : ℝ) ≤ 1 - 2 * r / (1 - r) := by
    have hq : 2 * r / (1 - r) ≤ 1 / 2 := by
      rw [div_le_iff₀ h1]
      linarith
    linarith
  have h4 : (1 / 2 : ℝ) ≤ Real.exp (-2 * r / (1 - r)) := h3.trans hexp
  dsimp [ell]
  rw [le_div_iff₀ (sq_pos_of_pos h1)]
  nlinarith

private theorem schwarzPick_cross {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1))
    (hgmap : MapsTo g (ball 0 1) (ball 0 1))
    {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    (1 - ‖g x‖ ^ 2) * (1 - ‖g y‖ ^ 2) * ‖1 - conj x * y‖ ^ 2 ≥
      (1 - ‖x‖ ^ 2) * (1 - ‖y‖ ^ 2) * ‖1 - conj (g x) * g y‖ ^ 2 := by
  have hx' : ‖g x‖ < 1 := mem_ball_zero_iff.mp (hgmap (mem_ball_zero_iff.mpr hx))
  have hy' : ‖g y‖ < 1 := mem_ball_zero_iff.mp (hgmap (mem_ball_zero_iff.mpr hy))
  let G : ℂ → ℂ := fun z => LandauNorm.mobius (-(g x)) (g (LandauNorm.mobius x z))
  have hd : DifferentiableOn ℂ G (ball 0 1) := by
    intro z hz
    have ht := LandauNorm.hasDerivAt_mobius hx (mem_ball_zero_iff.mp hz)
    have htm := LandauNorm.maps_mobius hx hz
    have hgt := hg.differentiableAt (isOpen_ball.mem_nhds htm)
    have hM := LandauNorm.hasDerivAt_mobius (a := -(g x)) (by simpa using hx')
      (mem_ball_zero_iff.mp (hgmap htm))
    exact (hM.differentiableAt.comp z (hgt.comp z ht.differentiableAt)).differentiableWithinAt
  have hmap : MapsTo G (ball 0 1) (closedBall 0 1) :=
    fun z hz => ball_subset_closedBall
      (LandauNorm.maps_mobius (a := -(g x)) (by simpa using hx')
        (hgmap (LandauNorm.maps_mobius hx hz)))
  have h0 : G 0 = 0 := by simp [G, LandauNorm.mobius]
  let u := LandauNorm.mobius (-x) y
  have hu : u ∈ ball 0 1 := LandauNorm.maps_mobius (a := -x) (by simpa using hx)
    (mem_ball_zero_iff.mpr hy)
  have hcomp : LandauNorm.mobius x u = y := by
    simpa only [u, neg_neg] using
      LandauNorm.mobius_inverse (a := -x) (by simpa using hx) hy
  have hn := Complex.norm_le_norm_of_mapsTo_ball hd hmap h0 (mem_ball_zero_iff.mp hu)
  have hs : 1 - ‖u‖ ^ 2 ≤ 1 - ‖LandauNorm.mobius (-(g x)) (g y)‖ ^ 2 := by
    change ‖LandauNorm.mobius (-(g x)) (g (LandauNorm.mobius x u))‖ ≤ ‖u‖ at hn
    rw [hcomp] at hn
    nlinarith [norm_nonneg u, norm_nonneg (LandauNorm.mobius (-(g x)) (g y))]
  dsimp [u] at hs
  rw [LandauNorm.norm_mobius_sq (by simpa using hx) hy,
    LandauNorm.norm_mobius_sq (by simpa using hx') hy'] at hs
  simp only [norm_neg, map_neg, neg_mul, ← sub_eq_add_neg] at hs
  have hp₁ : 0 < ‖1 - conj x * y‖ := norm_pos_iff.mpr <| by
    simpa [sub_eq_add_neg] using LandauNorm.denom_ne (a := -x) (by simpa using hx) hy
  have hp₂ : 0 < ‖1 - conj (g x) * g y‖ := norm_pos_iff.mpr <| by
    simpa [sub_eq_add_neg] using LandauNorm.denom_ne (a := -(g x)) (by simpa using hx') hy'
  exact (div_le_div_iff₀ (sq_pos_of_pos hp₁) (sq_pos_of_pos hp₂)).mp hs

private theorem julia_cross {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1))
    (hgmap : MapsTo g (ball 0 1) (ball 0 1)) (hg1 : g 1 = 1)
    (hgd : HasDerivAt g 1 1) {w : ℂ} (hw : ‖w‖ < 1) :
    (1 - ‖g w‖ ^ 2) * ‖1 - w‖ ^ 2 ≥ (1 - ‖w‖ ^ 2) * ‖1 - g w‖ ^ 2 := by
  have hre : HasDerivAt (fun t : ℝ => (g (t : ℂ)).re) 1 1 := by
    simpa using hgd.real_of_complex (z := (1 : ℝ))
  have him : HasDerivAt (fun t : ℝ => (g (t : ℂ)).im) 0 1 := by
    simpa [Complex.mul_re] using (hgd.const_mul (-Complex.I)).real_of_complex (z := (1 : ℝ))
  have hn : HasDerivAt (fun t : ℝ => ‖g (t : ℂ)‖ ^ 2) 2 1 := by
    have he : (fun t : ℝ => ‖g (t : ℂ)‖ ^ 2) =
        (fun t : ℝ => (g (t : ℂ)).re) ^ 2 + (fun t : ℝ => (g (t : ℂ)).im) ^ 2 := by
      funext t
      change ‖g (t : ℂ)‖ ^ 2 = (g t).re ^ 2 + (g t).im ^ 2
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply, pow_two]
    rw [he]
    simpa [hg1] using (hre.pow 2).add (him.pow 2)
  have hlim : Tendsto (fun t : ℝ => (1 - ‖g (t : ℂ)‖ ^ 2) / (1 - t ^ 2))
      (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    have h₂ : HasDerivAt (fun t : ℝ => t ^ 2) 2 1 := by
      simpa using! (hasDerivAt_id (1 : ℝ)).pow 2
    have h : Tendsto (fun t : ℝ => slope (fun t : ℝ => ‖g (t : ℂ)‖ ^ 2) 1 t /
        slope (fun t : ℝ => t ^ 2) 1 t) (𝓝[<] (1 : ℝ)) (𝓝 (2 / 2)) :=
      (hn.tendsto_slope.mono_left (nhdsLT_le_nhdsNE (1 : ℝ))).div
        (h₂.tendsto_slope.mono_left (nhdsLT_le_nhdsNE (1 : ℝ))) (by norm_num)
    rw [div_self (by norm_num : (2 : ℝ) ≠ 0)] at h
    refine h.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ⟨ht0, ht1⟩
    have htne : t - 1 ≠ 0 := sub_ne_zero.mpr ht1.ne
    have htt : t ^ 2 < 1 := by nlinarith [mul_pos ht0 (sub_pos.mpr ht1)]
    have htpos : 1 - t ^ 2 ≠ 0 := (sub_pos.mpr htt).ne'
    have hn' : t ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr htt.ne
    simp only [slope_def_field, Complex.ofReal_one, hg1, norm_one, one_pow]
    field_simp [htne, htpos, hn']
    ring
  have hcont : Tendsto (fun t : ℝ => g (t : ℂ)) (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    have hhh := hgd.continuousAt.tendsto.comp (Complex.continuous_ofReal.tendsto (1 : ℝ))
    simpa [hg1, Function.comp_def] using hhh.mono_left nhdsWithin_le_nhds
  have hinj1 : Tendsto (fun t : ℝ => ‖1 - conj (t : ℂ) * w‖ ^ 2)
      (𝓝[<] (1 : ℝ)) (𝓝 (‖1 - w‖ ^ 2)) := by
    have h : Continuous (fun t : ℝ => ‖1 - conj (t : ℂ) * w‖ ^ 2) := by fun_prop
    simpa using (h.tendsto 1).mono_left nhdsWithin_le_nhds
  have hinj2 : Tendsto (fun t : ℝ => ‖1 - conj (g (t : ℂ)) * g w‖ ^ 2)
      (𝓝[<] (1 : ℝ)) (𝓝 (‖1 - g w‖ ^ 2)) := by
    have h : Continuous (fun z : ℂ => ‖1 - conj z * g w‖ ^ 2) := by fun_prop
    simpa [Function.comp_def] using (h.tendsto (1 : ℂ)).comp hcont
  have hL : Tendsto (fun t : ℝ => (1 - ‖g (t : ℂ)‖ ^ 2) / (1 - t ^ 2) *
      (1 - ‖g w‖ ^ 2) * ‖1 - conj (t : ℂ) * w‖ ^ 2) (𝓝[<] (1 : ℝ))
      (𝓝 (1 * (1 - ‖g w‖ ^ 2) * ‖1 - w‖ ^ 2)) := (hlim.mul tendsto_const_nhds).mul hinj1
  have hR : Tendsto (fun t : ℝ => (1 - ‖w‖ ^ 2) * ‖1 - conj (g (t : ℂ)) * g w‖ ^ 2)
      (𝓝[<] (1 : ℝ)) (𝓝 ((1 - ‖w‖ ^ 2) * ‖1 - g w‖ ^ 2)) := tendsto_const_nhds.mul hinj2
  have he : ∀ᶠ t in 𝓝[<] (1 : ℝ), t ∈ Ioo 0 1 := Ioo_mem_nhdsLT zero_lt_one
  have h := le_of_tendsto_of_tendsto hR hL ?_
  · simpa using h
  filter_upwards [he] with t ⟨ht0, ht1⟩
  have ht : ‖(t : ℂ)‖ < 1 := by simpa [abs_of_pos ht0] using ht1
  have hs := schwarzPick_cross hg hgmap ht hw
  have htp : 0 < 1 - t ^ 2 := by nlinarith
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0] at hs
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  exact (le_div_iff₀ htp).mpr (by simpa only [mul_assoc, mul_left_comm, mul_comm] using hs)

private theorem liu_minda_real_m {f h : ℂ → ℂ}
    (_hf : DifferentiableOn ℂ f (ball 0 1)) (_hf0 : f 0 = 1)
    (hW : ∀ z ∈ ball (0 : ℂ) 1, (1 - ‖z‖ ^ 2) * ‖f z‖ ≤ 1)
    (hh : DifferentiableOn ℂ h (ball 0 1)) (hh0 : h 0 = 0) (hh1 : deriv h 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) 1, Complex.exp (h z) = f z)
    {r m : ℝ} (hr0 : 0 < r) (hrm : r < m) (hm1 : m < 1) :
    -Real.log ((1 - m * r) ^ 2 * ‖f (r : ℂ)‖) ≤
      4 * m ^ 2 * r / (2 * m - r * (1 + m ^ 2)) := by
  have hm0 : 0 < m := hr0.trans hrm
  have hmC : ‖(m : ℂ)‖ = m := by simp [abs_of_pos hm0]
  have hmC1 : ‖(m : ℂ)‖ < 1 := hmC.symm ▸ hm1
  have hmCN : ‖-(m : ℂ)‖ < 1 := by rwa [norm_neg]
  have hmq : 0 < 1 - m ^ 2 := by nlinarith
  have hmr : 0 < 1 - m * r := by nlinarith
  let Z : ℂ → ℂ := fun w => LandauNorm.mobius (m : ℂ) (-(m : ℂ) * w)
  let G : ℂ → ℂ := fun w => (1 - (m : ℂ) * Z w) ^ 2 * f (Z w)
  let P : ℂ → ℂ := fun w => -h (Z w) - 2 * Complex.log (1 - (m : ℂ) * Z w)
  let c : ℝ := 2 * m ^ 2 / (1 - m ^ 2)
  have hc0 : 0 < c := div_pos (by positivity) hmq
  have hin (w : ℂ) (hw : ‖w‖ < 1) : ‖-(m : ℂ) * w‖ < 1 := by
    rw [norm_mul, norm_neg, hmC]
    exact (mul_lt_mul_of_pos_left hw hm0).trans (by simpa using hm1)
  have hZ (w : ℂ) (hw : ‖w‖ < 1) : ‖Z w‖ < 1 :=
    mem_ball_zero_iff.mp (LandauNorm.maps_mobius hmC1
      (mem_ball_zero_iff.mpr (hin w hw)))
  have hZdiff (w : ℂ) (hw : ‖-(m : ℂ) * w‖ < 1) : DifferentiableAt ℂ Z w :=
    (LandauNorm.hasDerivAt_mobius hmC1 hw).differentiableAt.comp w (by fun_prop)
  have hslit (w : ℂ) (hw : ‖w‖ < 1) : 1 - (m : ℂ) * Z w ∈ Complex.slitPlane := by
    left
    have h1 : ‖(m : ℂ) * Z w‖ < 1 := by
      rw [norm_mul, hmC]
      nlinarith [hZ w hw, norm_nonneg (Z w)]
    have h2 : ((m : ℂ) * Z w).re ≤ ‖(m : ℂ) * Z w‖ := Complex.re_le_norm _
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hGlt1 (w : ℂ) (hw : ‖w‖ < 1) : ‖G w‖ < 1 := by
    have hz := hZ w hw
    have hinv : LandauNorm.mobius (-(m : ℂ)) (Z w) = -(m : ℂ) * w :=
      LandauNorm.mobius_inverse hmC1 (hin w hw)
    have hd : 1 - (m : ℂ) * Z w ≠ 0 := Complex.slitPlane_ne_zero (hslit w hw)
    have hfwt := hW _ (mem_ball_zero_iff.mpr hz)
    have hN := LandauNorm.norm_mobius_sq (a := -(m : ℂ)) (z := Z w) hmCN hz
    rw [hinv, norm_mul, norm_neg, hmC] at hN
    simp only [map_neg, Complex.conj_ofReal, neg_mul, ← sub_eq_add_neg] at hN
    have hN' := (eq_div_iff (pow_ne_zero 2 (norm_ne_zero_iff.mpr hd))).mp hN
    have hwp : 0 < 1 - (m * ‖w‖) ^ 2 := by
      have hn := hin w hw
      rw [norm_mul, norm_neg, hmC] at hn
      nlinarith [show 0 ≤ m * ‖w‖ by positivity]
    have hwt : 1 - m ^ 2 < 1 - (m * ‖w‖) ^ 2 := by
      have hn := mul_lt_mul_of_pos_left hw hm0
      nlinarith [show 0 ≤ m * ‖w‖ by positivity]
    have hle : ‖1 - (m : ℂ) * Z w‖ ^ 2 * ‖f (Z w)‖ ≤ (1 - m ^ 2) / (1 - (m * ‖w‖) ^ 2) := by
      apply (le_div_iff₀ hwp).mpr
      calc
        _ = ((1 - (m * ‖w‖) ^ 2) * ‖1 - (m : ℂ) * Z w‖ ^ 2) * ‖f (Z w)‖ := by ring
        _ = (1 - m ^ 2) * ((1 - ‖Z w‖ ^ 2) * ‖f (Z w)‖) := by rw [hN']; ring
        _ ≤ 1 - m ^ 2 := by simpa using mul_le_mul_of_nonneg_left hfwt hmq.le
    simpa only [G, norm_mul, norm_pow] using hle.trans_lt ((div_lt_one hwp).mpr hwt)
  have hPexp (w : ℂ) (hw : ‖w‖ < 1) : Complex.exp (-P w) = G w := by
    have hd : 1 - (m : ℂ) * Z w ≠ 0 := Complex.slitPlane_ne_zero (hslit w hw)
    have hneg : -P w = h (Z w) + (Complex.log (1 - (m : ℂ) * Z w) +
        Complex.log (1 - (m : ℂ) * Z w)) := by dsimp [P]; ring
    rw [hneg, Complex.exp_add, Complex.exp_add, hexp _ (mem_ball_zero_iff.mpr (hZ w hw)),
      Complex.exp_log hd]
    dsimp [G]
    ring
  have hPre (w : ℂ) (hw : ‖w‖ < 1) : 0 < (P w).re := by
    have h1 : Real.exp (-(P w).re) = ‖G w‖ := by
      rw [← hPexp w hw, Complex.norm_exp, Complex.neg_re]
    have h2 : Real.exp (-(P w).re) < Real.exp 0 := by
      rw [h1, Real.exp_zero]
      exact hGlt1 w hw
    linarith [Real.exp_lt_exp.mp h2]
  have hPdiff : DifferentiableOn ℂ P (ball 0 1) := by
    intro w hw
    have hw' := mem_ball_zero_iff.mp hw
    have hZ' := hZdiff w (hin w hw')
    have h1 : DifferentiableAt ℂ (fun u => -h (Z u)) w :=
      ((hh.differentiableAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr (hZ w hw')))).comp
        w hZ').neg
    have h2 : DifferentiableAt ℂ (fun u => 1 - (m : ℂ) * Z u) w := by fun_prop
    have h3 : DifferentiableAt ℂ (fun u => 2 * Complex.log (1 - (m : ℂ) * Z u)) w :=
      ((Complex.differentiableAt_log (hslit w hw')).comp w h2).const_mul 2
    exact (h1.sub h3).differentiableWithinAt
  have hZ1 : Z 1 = 0 := by simp [Z, LandauNorm.mobius]
  have hP1 : P 1 = 0 := by simp [P, hZ1, hh0]
  have hPderiv : HasDerivAt P (-(c : ℂ)) 1 := by
    have hmul : HasDerivAt (fun w : ℂ => -(m : ℂ) * w) (-(m : ℂ)) 1 := by
      simpa using (hasDerivAt_id (1 : ℂ)).const_mul (-(m : ℂ))
    have hM := LandauNorm.hasDerivAt_mobius (z := -(m : ℂ) * 1)
      hmC1 (by simpa only [mul_one] using hmCN)
    have hmqC : (1 : ℂ) - (m : ℂ) ^ 2 ≠ 0 := by
      rw [show (1 : ℂ) - (m : ℂ) ^ 2 = ((1 - m ^ 2 : ℝ) : ℂ) by push_cast; rfl]
      exact Complex.ofReal_ne_zero.mpr hmq.ne'
    have hZ' : HasDerivAt Z (-(m : ℂ) / (1 - (m : ℂ) ^ 2)) 1 := by
      have h := hM.comp 1 hmul
      have he : (1 - ((m ^ 2 : ℝ) : ℂ)) / (1 + conj (m : ℂ) * (-(m : ℂ) * 1)) ^ 2 *
          (-(m : ℂ)) = -(m : ℂ) / (1 - (m : ℂ) ^ 2) := by
        simp only [Complex.conj_ofReal, mul_one, mul_neg, ← pow_two, ← sub_eq_add_neg]
        push_cast
        field_simp [hmqC]
      simpa only [Z, Function.comp_def, hmC, he] using h
    have hhZ : HasDerivAt (fun w => h (Z w)) 0 1 := by
      have hh0' : HasDerivAt h 0 (Z 1) := by
        rw [hZ1]
        simpa [hh1] using (hh.differentiableAt (ball_mem_nhds (0 : ℂ) zero_lt_one)).hasDerivAt
      simpa only [zero_mul, Function.comp_def] using hh0'.comp 1 hZ'
    have hsub : HasDerivAt (fun w => 1 - (m : ℂ) * Z w)
        ((m : ℂ) ^ 2 / (1 - (m : ℂ) ^ 2)) 1 := by
      refine ((hZ'.const_mul (m : ℂ)).const_sub 1).congr_deriv ?_
      field_simp [hmqC]
    have hlog1 : HasDerivAt (fun w => Complex.log (1 - (m : ℂ) * Z w))
        ((m : ℂ) ^ 2 / (1 - (m : ℂ) ^ 2)) 1 := by
      have hl : HasDerivAt Complex.log (1 : ℂ)⁻¹ (1 - (m : ℂ) * Z 1) := by
        rw [hZ1, mul_zero, sub_zero]
        exact Complex.hasDerivAt_log Complex.one_mem_slitPlane
      simpa [Function.comp_def] using hl.comp 1 hsub
    refine (hhZ.neg.sub (hlog1.const_mul 2)).congr_deriv ?_
    dsimp [c]
    push_cast
    ring
  let Φ : ℂ → ℂ := fun w => (2 * (c : ℂ) - P w) / (2 * (c : ℂ) + P w)
  have hden_ne (w : ℂ) (hw : ‖w‖ < 1) : 2 * (c : ℂ) + P w ≠ 0 := by
    intro h0
    have hre0 := congrArg Complex.re h0
    simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
      Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re] at hre0
    linarith [hPre w hw]
  have hΦdiff : DifferentiableOn ℂ Φ (ball 0 1) :=
    (hPdiff.const_sub _).div (hPdiff.const_add _) (fun w hw => hden_ne w (mem_ball_zero_iff.mp hw))
  have hΦmap : MapsTo Φ (ball 0 1) (ball 0 1) := by
    intro w hw
    have hw' := mem_ball_zero_iff.mp hw
    have hdn := hden_ne w hw'
    rw [mem_ball_zero_iff]
    dsimp only [Φ]
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hdn)]
    have hsq : ‖2 * (c : ℂ) + P w‖ ^ 2 - ‖2 * (c : ℂ) - P w‖ ^ 2 = 8 * c * (P w).re := by
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im]
      ring
    nlinarith [hPre w hw', norm_nonneg (2 * (c : ℂ) + P w), norm_nonneg (2 * (c : ℂ) - P w)]
  have hΦ1 : Φ 1 = 1 := by
    dsimp [Φ]
    rw [hP1, sub_zero, add_zero]
    exact div_self (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hc0.ne'))
  have hΦderiv : HasDerivAt Φ 1 1 := by
    have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc0.ne'
    have h2c : (2 : ℂ) * (c : ℂ) ≠ 0 := mul_ne_zero (by norm_num) hcC
    have hnum : HasDerivAt (fun w => 2 * (c : ℂ) - P w) (c : ℂ) 1 := by
      simpa using hPderiv.const_sub (2 * (c : ℂ))
    have hden : HasDerivAt (fun w => 2 * (c : ℂ) + P w) (-(c : ℂ)) 1 := by
      simpa using hPderiv.const_add (2 * (c : ℂ))
    refine (hnum.div hden (by simpa [hP1] using h2c)).congr_deriv ?_
    rw [hP1, sub_zero, add_zero]
    field_simp [hcC]
    ring
  let v : ℝ := (m - r) / (m * (1 - m * r))
  have hv0 : 0 < v := div_pos (sub_pos.mpr hrm) (mul_pos hm0 hmr)
  have hv1 : v < 1 := by
    apply (div_lt_one (mul_pos hm0 hmr)).mpr
    nlinarith [mul_pos hr0 hmq]
  have hvC : ‖(v : ℂ)‖ < 1 := by simpa [abs_of_pos hv0] using hv1
  have hZv : Z (v : ℂ) = (r : ℂ) := by
    have hpre : -(m : ℂ) * (v : ℂ) = LandauNorm.mobius (-(m : ℂ)) (r : ℂ) := by
      have hmN : (m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm0.ne'
      have hdN : 1 - (m : ℂ) * (r : ℂ) ≠ 0 := by exact_mod_cast hmr.ne'
      unfold v LandauNorm.mobius
      push_cast
      simp only [map_neg, Complex.conj_ofReal, neg_mul, ← sub_eq_add_neg]
      field_simp [hmN, hdN]
      ring
    have hrC : ‖(r : ℂ)‖ < 1 := by simpa [abs_of_pos hr0] using hrm.trans hm1
    simpa only [Z, hpre, neg_neg] using
      LandauNorm.mobius_inverse (a := -(m : ℂ)) hmCN hrC
  have hJ := julia_cross hΦdiff hΦmap hΦ1 hΦderiv hvC
  have hPv_re : (P (v : ℂ)).re ≤ 2 * c * (1 - v) / (1 + v) := by
    have hdn := hden_ne (v : ℂ) hvC
    have hdn_pos : 0 < ‖2 * (c : ℂ) + P (v : ℂ)‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hdn)
    have h1sub : 1 - Φ (v : ℂ) = 2 * P (v : ℂ) / (2 * (c : ℂ) + P (v : ℂ)) := by
      dsimp [Φ]
      field_simp [hdn]
      ring
    have h1norm : 1 - ‖Φ (v : ℂ)‖ ^ 2 =
        8 * c * (P (v : ℂ)).re / ‖2 * (c : ℂ) + P (v : ℂ)‖ ^ 2 := by
      dsimp [Φ]
      rw [norm_div, div_pow, one_sub_div hdn_pos.ne']
      congr 1
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im]
      ring
    have hvnorm : ‖(v : ℂ)‖ = v := by simp [abs_of_pos hv0]
    have h1vnorm : ‖1 - (v : ℂ)‖ ^ 2 = (1 - v) ^ 2 := by
      rw [show (1 : ℂ) - (v : ℂ) = ((1 - v : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [h1norm, h1sub, norm_div, norm_mul, Complex.norm_ofNat, div_pow, mul_pow,
      hvnorm, h1vnorm] at hJ
    have hJ' : 8 * c * (P (v : ℂ)).re * (1 - v) ^ 2 ≥
        (1 - v ^ 2) * (4 * ‖P (v : ℂ)‖ ^ 2) := by
      have hmul := mul_le_mul_of_nonneg_right hJ hdn_pos.le
      have hL : 8 * c * (P (v : ℂ)).re / ‖2 * (c : ℂ) + P (v : ℂ)‖ ^ 2 * (1 - v) ^ 2 *
          ‖2 * (c : ℂ) + P (v : ℂ)‖ ^ 2 = 8 * c * (P (v : ℂ)).re * (1 - v) ^ 2 := by
        field_simp [hdn_pos.ne']
      have hR : (1 - v ^ 2) * (2 ^ 2 * ‖P (v : ℂ)‖ ^ 2 / ‖2 * (c : ℂ) + P (v : ℂ)‖ ^ 2) *
          ‖2 * (c : ℂ) + P (v : ℂ)‖ ^ 2 = (1 - v ^ 2) * (4 * ‖P (v : ℂ)‖ ^ 2) := by
        field_simp [hdn_pos.ne']
        ring
      linarith
    have hre_le : (P (v : ℂ)).re ^ 2 ≤ ‖P (v : ℂ)‖ ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2
    have h1v2 : 0 < 1 - v ^ 2 := by nlinarith
    have hJ'' : 4 * (1 - v ^ 2) * (P (v : ℂ)).re ^ 2 ≤ 8 * c * (P (v : ℂ)).re * (1 - v) ^ 2 := by
      nlinarith
    have hPre_v := hPre (v : ℂ) hvC
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 + v)]
    nlinarith [mul_pos (sub_pos.mpr hv1) hPre_v]
  have hlog_eq : (P (v : ℂ)).re = -Real.log ((1 - m * r) ^ 2 * ‖f (r : ℂ)‖) := by
    have h1 : Real.exp (-(P (v : ℂ)).re) = ‖G (v : ℂ)‖ := by
      rw [← hPexp (v : ℂ) hvC, Complex.norm_exp, Complex.neg_re]
    have h2 : ‖G (v : ℂ)‖ = (1 - m * r) ^ 2 * ‖f (r : ℂ)‖ := by
      dsimp [G]
      rw [hZv, norm_mul, norm_pow,
        show (1 : ℂ) - (m : ℂ) * (r : ℂ) = ((1 - m * r : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmr]
    rw [h2] at h1
    have h3 := congrArg Real.log h1
    rw [Real.log_exp] at h3
    linarith
  have hrhs : 2 * c * (1 - v) / (1 + v) = 4 * m ^ 2 * r / (2 * m - r * (1 + m ^ 2)) := by
    have hden_pos : 0 < 2 * m - r * (1 + m ^ 2) := by
      nlinarith [mul_pos (sub_pos.mpr hrm) (sub_pos.mpr hm1)]
    have hden1 : 1 + v = (2 * m - r * (1 + m ^ 2)) / (m * (1 - m * r)) := by
      dsimp [v]
      field_simp [hm0.ne', hmr.ne']
      ring
    have hnum1 : 1 - v = r * (1 - m ^ 2) / (m * (1 - m * r)) := by
      dsimp [v]
      field_simp [hm0.ne', hmr.ne']
      ring
    rw [hnum1, hden1]
    dsimp [c]
    field_simp [hmq.ne', hm0.ne', hmr.ne', hden_pos.ne']
    ring
  rw [← hlog_eq, ← hrhs]
  exact hPv_re

theorem liu_minda_real {f h : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hf0 : f 0 = 1)
    (hW : ∀ z ∈ ball (0 : ℂ) 1, (1 - ‖z‖ ^ 2) * ‖f z‖ ≤ 1)
    (hh : DifferentiableOn ℂ h (ball 0 1)) (hh0 : h 0 = 0) (hh1 : deriv h 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) 1, Complex.exp (h z) = f z)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ell r ≤ ‖f (r : ℂ)‖ := by
  rcases hr0.eq_or_lt with rfl | hr0
  · simp [ell, hf0]
  have hfr_pos : 0 < ‖f (r : ℂ)‖ := by
    rw [← hexp (r : ℂ) (by rw [mem_ball_zero_iff]; simpa [abs_of_pos hr0] using hr1),
      Complex.norm_exp]
    exact Real.exp_pos _
  have h1r : 0 < 1 - r := sub_pos.mpr hr1
  have hL : Tendsto (fun m : ℝ => -Real.log ((1 - m * r) ^ 2 * ‖f (r : ℂ)‖))
      (𝓝[<] (1 : ℝ)) (𝓝 (-Real.log ((1 - r) ^ 2 * ‖f (r : ℂ)‖))) := by
    have hcont : ContinuousAt (fun m : ℝ => -Real.log ((1 - m * r) ^ 2 * ‖f (r : ℂ)‖)) 1 := by
      refine ContinuousAt.neg (ContinuousAt.log ?_ ?_)
      · fun_prop
      · simp only [one_mul]
        exact (mul_pos (sq_pos_of_pos h1r) hfr_pos).ne'
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hR : Tendsto (fun m : ℝ => 4 * m ^ 2 * r / (2 * m - r * (1 + m ^ 2)))
      (𝓝[<] (1 : ℝ)) (𝓝 (2 * r / (1 - r))) := by
    have hden : (2 : ℝ) * 1 - r * (1 + 1 ^ 2) ≠ 0 := by linarith
    have hcont : ContinuousAt (fun m : ℝ => 4 * m ^ 2 * r / (2 * m - r * (1 + m ^ 2))) 1 := by
      exact (Continuous.continuousAt (by fun_prop)).div
        (Continuous.continuousAt (by fun_prop)) hden
    have heq : 4 * (1 : ℝ) ^ 2 * r / (2 * 1 - r * (1 + 1 ^ 2)) = 2 * r / (1 - r) := by
      have hden' : (2 : ℝ) * 1 - r * (1 + 1 ^ 2) = 2 * (1 - r) := by ring
      rw [hden']
      field_simp [h1r.ne']
      ring
    rw [← heq]
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hlim : -Real.log ((1 - r) ^ 2 * ‖f (r : ℂ)‖) ≤ 2 * r / (1 - r) := by
    refine le_of_tendsto_of_tendsto hL hR ?_
    filter_upwards [Ioo_mem_nhdsLT hr1] with m ⟨hrm, hm1⟩
    exact liu_minda_real_m hf hf0 hW hh hh0 hh1 hexp hr0 hrm hm1
  have hexp_le : Real.exp (-2 * r / (1 - r)) ≤ (1 - r) ^ 2 * ‖f (r : ℂ)‖ := by
    have hneg : -2 * r / (1 - r) ≤ Real.log ((1 - r) ^ 2 * ‖f (r : ℂ)‖) := by
      have : -2 * r / (1 - r) = -(2 * r / (1 - r)) := by ring
      linarith
    have := Real.exp_le_exp.mpr hneg
    rwa [Real.exp_log (mul_pos (sq_pos_of_pos h1r) hfr_pos)] at this
  dsimp [ell]
  rwa [div_le_iff₀' (sq_pos_of_pos h1r)]

theorem liu_minda {g h : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball 0 1)) (hg1 : deriv g 0 = 1)
    (hW : ∀ z ∈ ball (0 : ℂ) 1, (1 - ‖z‖ ^ 2) * ‖deriv g z‖ ≤ 1)
    (hh : DifferentiableOn ℂ h (ball 0 1)) (hh0 : h 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) 1, Complex.exp (h z) = deriv g z)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    ell ‖z‖ ≤ ‖deriv g z‖ := by
  have hh1 := LandauLog.deriv_log_zero hg hg1 hW hh hh0 hexp
  rcases eq_or_ne z 0 with rfl | hne
  · simp [ell, hg1]
  let d := z / (‖z‖ : ℂ)
  have hp : 0 < ‖z‖ := norm_pos_iff.mpr hne
  have hd : ‖d‖ = 1 := by
    dsimp [d]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp, div_self hp.ne']
  have hD (w : ℂ) : ‖d * w‖ = ‖w‖ := by rw [norm_mul, hd, one_mul]
  have he : d * (‖z‖ : ℂ) = z := div_mul_cancel₀ z (by exact_mod_cast hp.ne')
  have hmaps : MapsTo (fun w : ℂ => d * w) (ball 0 1) (ball 0 1) := by
    intro w hw; simpa only [mem_ball_zero_iff, hD] using hw
  have hf_diff : DifferentiableOn ℂ (fun w => deriv g (d * w)) (ball 0 1) :=
    (hg.deriv isOpen_ball).comp ((differentiable_const d).mul differentiable_id).differentiableOn
      hmaps
  have hh_diff : DifferentiableOn ℂ (fun w => h (d * w)) (ball 0 1) :=
    hh.comp ((differentiable_const d).mul differentiable_id).differentiableOn hmaps
  have hB (w : ℂ) (hw : w ∈ ball (0 : ℂ) 1) : (1 - ‖w‖ ^ 2) * ‖deriv g (d * w)‖ ≤ 1 := by
    simpa only [hD] using hW _ (hmaps hw)
  have hh_d0 : deriv (fun w => h (d * w)) 0 = 0 := by
    have h1 : HasDerivAt h 0 (d * 0) := by
      rw [mul_zero]
      simpa [hh1] using (hh.differentiableAt (ball_mem_nhds (0 : ℂ) zero_lt_one)).hasDerivAt
    have h2 : HasDerivAt (fun w : ℂ => d * w) d 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul d
    have h3 : HasDerivAt (fun w => h (d * w)) (0 * d) 0 := h1.comp 0 h2
    simpa using h3.deriv
  have hres := liu_minda_real hf_diff (by simpa using hg1) hB hh_diff (by simpa using hh0)
    hh_d0 (fun w hw => hexp _ (hmaps hw)) (norm_nonneg z) (mem_ball_zero_iff.mp hz)
  simpa [he] using hres

end LandauLiuMinda

/- ## Section 4: Escaping ray lifts and smoothed-norm integral lower bound -/

namespace LandauEscape

def IsLift (g : ℂ → ℂ) (u : ℂ) (T : ℝ) (γ : ℝ → ℂ) : Prop :=
  0 ≤ T ∧ ContinuousOn γ (Icc 0 T) ∧ γ 0 = 0 ∧
    ∀ t ∈ Icc 0 T, γ t ∈ ball (0 : ℂ) 1 ∧ g (γ t) = (t : ℂ) * u

private theorem hasStrictDerivAt_of_holo {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    HasStrictDerivAt g (deriv g z) z :=
  ((hg.analyticAt (isOpen_ball.mem_nhds hz)).contDiffAt (n := (1 : ℕ))).hasStrictDerivAt
    (by simp)

private theorem local_inv_at {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1))
    (hgne : ∀ z ∈ ball (0 : ℂ) 1, deriv g z ≠ 0) {z₀ : ℂ} (hz₀ : z₀ ∈ ball (0 : ℂ) 1) :
    ∃ (U : Set ℂ) (δ : ℝ) (φ : ℂ → ℂ),
      IsOpen U ∧ z₀ ∈ U ∧ U ⊆ ball (0 : ℂ) 1 ∧ 0 < δ ∧
      ContinuousOn φ (ball (g z₀) δ) ∧ φ (g z₀) = z₀ ∧
      MapsTo φ (ball (g z₀) δ) U ∧
      (∀ w ∈ ball (g z₀) δ, g (φ w) = w) ∧
      (∀ z ∈ U, g z ∈ ball (g z₀) δ → φ (g z) = z) := by
  have hsd := hasStrictDerivAt_of_holo hg hz₀
  have hne := hgne z₀ hz₀
  let e := (hsd.hasStrictFDerivAt_equiv hne).toOpenPartialHomeomorph g
  have hmemS : z₀ ∈ e.source := (hsd.hasStrictFDerivAt_equiv hne).mem_toOpenPartialHomeomorph_source
  have hcoe : (e : ℂ → ℂ) = g :=
    (hsd.hasStrictFDerivAt_equiv hne).toOpenPartialHomeomorph_coe
  have hmemT : g z₀ ∈ e.target := by
    have := e.map_source hmemS
    rwa [hcoe] at this
  let U : Set ℂ := e.source ∩ ball 0 1
  have hUopen : IsOpen U := e.open_source.inter isOpen_ball
  have hz₀U : z₀ ∈ U := ⟨hmemS, hz₀⟩
  have hsymm_cont : ContinuousAt e.symm (g z₀) :=
    e.continuousOn_symm.continuousAt (e.open_target.mem_nhds hmemT)
  have hsymm_val : e.symm (g z₀) = z₀ := by
    have := e.left_inv hmemS
    rwa [hcoe] at this
  have hpre : e.symm ⁻¹' U ∈ 𝓝 (g z₀) :=
    hsymm_cont.preimage_mem_nhds (by rw [hsymm_val]; exact hUopen.mem_nhds hz₀U)
  have hinter : e.target ∩ e.symm ⁻¹' U ∈ 𝓝 (g z₀) :=
    Filter.inter_mem (e.open_target.mem_nhds hmemT) hpre
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hinter
  refine ⟨U, δ, e.symm, hUopen, hz₀U, inter_subset_right, hδ,
    e.continuousOn_symm.mono (fun w hw => (hball hw).1), hsymm_val,
    fun w hw => (hball hw).2, ?_, ?_⟩
  · intro w hw
    have := e.right_inv (hball hw).1
    rwa [hcoe] at this
  · intro z hz _
    have := e.left_inv hz.1
    rwa [hcoe] at this

theorem lift_unique {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1))
    (hgne : ∀ z ∈ ball (0 : ℂ) 1, deriv g z ≠ 0) {u : ℂ} {T : ℝ} {γ₁ γ₂ : ℝ → ℂ}
    (h1 : IsLift g u T γ₁) (h2 : IsLift g u T γ₂) :
    EqOn γ₁ γ₂ (Icc 0 T) := by
  let S : Set (Icc (0 : ℝ) T) := {t | γ₁ t.1 = γ₂ t.1}
  have hS_closed : IsClosed S := by
    have hc1 : Continuous (fun t : Icc (0 : ℝ) T => γ₁ t.1) :=
      continuousOn_iff_continuous_domRestrict.mp h1.2.1
    have hc2 : Continuous (fun t : Icc (0 : ℝ) T => γ₂ t.1) :=
      continuousOn_iff_continuous_domRestrict.mp h2.2.1
    exact isClosed_eq hc1 hc2
  have hS_open : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have hz₀ : γ₁ t.1 ∈ ball (0 : ℂ) 1 := (h1.2.2.2 t.1 t.2).1
    obtain ⟨U, δ, φ, hUopen, hz₀U, _, hδ, _, _, _, _, hleft⟩ := local_inv_at hg hgne hz₀
    have hc1 : Continuous (fun s : Icc (0 : ℝ) T => γ₁ s.1) :=
      continuousOn_iff_continuous_domRestrict.mp h1.2.1
    have hc2 : Continuous (fun s : Icc (0 : ℝ) T => γ₂ s.1) :=
      continuousOn_iff_continuous_domRestrict.mp h2.2.1
    have hnh1 : (fun s : Icc (0 : ℝ) T => γ₁ s.1) ⁻¹' U ∈ 𝓝 t :=
      hc1.continuousAt.preimage_mem_nhds (hUopen.mem_nhds hz₀U)
    have hnh2 : (fun s : Icc (0 : ℝ) T => γ₂ s.1) ⁻¹' U ∈ 𝓝 t :=
      hc2.continuousAt.preimage_mem_nhds (by rw [← ht]; exact hUopen.mem_nhds hz₀U)
    have hc3 : Continuous (fun s : Icc (0 : ℝ) T => (s.1 : ℂ) * u) := by fun_prop
    have hnh3 : (fun s : Icc (0 : ℝ) T => (s.1 : ℂ) * u) ⁻¹' ball (g (γ₁ t.1)) δ ∈ 𝓝 t :=
      hc3.continuousAt.preimage_mem_nhds (by
        rw [(h1.2.2.2 t.1 t.2).2]
        exact Metric.ball_mem_nhds _ hδ)
    filter_upwards [Filter.inter_mem (Filter.inter_mem hnh1 hnh2) hnh3] with s ⟨⟨hs1, hs2⟩, hs3⟩
    have hg1 : g (γ₁ s.1) = (s.1 : ℂ) * u := (h1.2.2.2 s.1 s.2).2
    have hg2 : g (γ₂ s.1) = (s.1 : ℂ) * u := (h2.2.2.2 s.1 s.2).2
    have h1eq : φ (g (γ₁ s.1)) = γ₁ s.1 := hleft (γ₁ s.1) hs1 (hg1.symm ▸ hs3)
    have h2eq : φ (g (γ₂ s.1)) = γ₂ s.1 := hleft (γ₂ s.1) hs2 (hg2.symm ▸ hs3)
    change γ₁ s.1 = γ₂ s.1
    rw [← h1eq, ← h2eq, hg1, hg2]
  have : PreconnectedSpace (Icc (0 : ℝ) T) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hne : S.Nonempty := ⟨⟨0, left_mem_Icc.mpr h1.1⟩, by simp [S, h1.2.2.1, h2.2.2.1]⟩
  have huniv : S = univ := IsClopen.eq_univ ⟨hS_closed, hS_open⟩ hne
  intro t ht
  have : (⟨t, ht⟩ : Icc (0 : ℝ) T) ∈ S := by rw [huniv]; trivial
  exact this

theorem lift_extend {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1))
    (hgne : ∀ z ∈ ball (0 : ℂ) 1, deriv g z ≠ 0) {u : ℂ} (hu : ‖u‖ = 1)
    {T : ℝ} {γ : ℝ → ℂ} (hγ : IsLift g u T γ) :
    ∃ δ > 0, ∃ γ', IsLift g u (T + δ) γ' ∧ EqOn γ' γ (Icc 0 T) := by
  have hTmem : T ∈ Icc 0 T := right_mem_Icc.mpr hγ.1
  have hz₀ : γ T ∈ ball (0 : ℂ) 1 := (hγ.2.2.2 T hTmem).1
  have hgz₀ : g (γ T) = (T : ℂ) * u := (hγ.2.2.2 T hTmem).2
  obtain ⟨U, δ, φ, _, _, hUsub, hδ, hφcont, hφval, hφmaps, hφright, _⟩ :=
    local_inv_at hg hgne hz₀
  let δ' : ℝ := δ / 2
  have hδ' : 0 < δ' := half_pos hδ
  let γ' : ℝ → ℂ := fun t => if t ≤ T then γ t else φ ((t : ℂ) * u)
  have hseg : ∀ t ∈ Icc T (T + δ'), (t : ℂ) * u ∈ ball (g (γ T)) δ := by
    intro t ht
    rw [hgz₀, mem_ball_iff_norm, show (t : ℂ) * u - (T : ℂ) * u = ((t - T : ℝ) : ℂ) * u by
      push_cast; ring, norm_mul, hu, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ht.1)]
    have hle : t ≤ T + δ / 2 := ht.2
    linarith
  have hcont_right : ContinuousOn (fun t : ℝ => φ ((t : ℂ) * u)) (Icc T (T + δ')) :=
    hφcont.comp (by fun_prop) hseg
  have hcont : ContinuousOn γ' (Icc 0 (T + δ')) := by
    have hunion : Icc 0 (T + δ') = Icc 0 T ∪ Icc T (T + δ') :=
      (Icc_union_Icc_eq_Icc hγ.1 (by linarith)).symm
    rw [hunion]
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
    · exact hγ.2.1.congr (fun t ht => by simp [γ', ht.2])
    · refine hcont_right.congr (fun t ht => ?_)
      dsimp [γ']
      split_ifs with hle
      · have hteq : t = T := le_antisymm hle ht.1
        subst hteq
        rw [← hgz₀, hφval]
      · rfl
  refine ⟨δ', hδ', γ', ⟨by linarith [hγ.1], hcont, by simp [γ', hγ.1, hγ.2.2.1], ?_⟩,
    fun t ht => by simp [γ', ht.2]⟩
  intro t ht
  dsimp [γ']
  split_ifs with hle
  · exact hγ.2.2.2 t ⟨ht.1, hle⟩
  · have hmem : (t : ℂ) * u ∈ ball (g (γ T)) δ := hseg t ⟨le_of_not_ge hle, ht.2⟩
    exact ⟨hUsub (hφmaps hmem), hφright _ hmem⟩

theorem lift_hasDerivAt {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1))
    (hgne : ∀ z ∈ ball (0 : ℂ) 1, deriv g z ≠ 0) {u : ℂ} {T : ℝ} {γ : ℝ → ℂ}
    (hγ : IsLift g u T γ) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt γ (u / deriv g (γ t)) t := by
  have htIcc : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
  have hz₀ : γ t ∈ ball (0 : ℂ) 1 := (hγ.2.2.2 t htIcc).1
  have hsd := hasStrictDerivAt_of_holo hg hz₀
  have hne := hgne (γ t) hz₀
  let φ := hsd.localInverse g (deriv g (γ t)) (γ t) hne
  have hφd : HasDerivAt φ (deriv g (γ t))⁻¹ (g (γ t)) := (hsd.to_localInverse hne).hasDerivAt
  have hleft : ∀ᶠ z in 𝓝 (γ t), φ (g z) = z := hsd.eventually_left_inverse hne
  have hcont_at : ContinuousAt γ t :=
    hγ.2.1.continuousAt (Icc_mem_nhds ht.1 ht.2)
  have hev1 : ∀ᶠ s in 𝓝 t, φ (g (γ s)) = γ s := hcont_at.eventually hleft
  have hev2 : ∀ᶠ s in 𝓝 t, s ∈ Icc 0 T := Icc_mem_nhds ht.1 ht.2
  have heq : γ =ᶠ[𝓝 t] fun s : ℝ => φ ((s : ℂ) * u) := by
    filter_upwards [hev1, hev2] with s hs1 hs2
    rw [← hs1, (hγ.2.2.2 s hs2).2]
  have hlin : HasDerivAt (fun s : ℝ => (s : ℂ) * u) u t := by
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t :=
      Complex.ofRealCLM.hasDerivAt
    simpa using h1.mul_const u
  have hcomp : HasDerivAt (fun s : ℝ => φ ((s : ℂ) * u)) (u / deriv g (γ t)) t := by
    have hφ' : HasDerivAt φ (deriv g (γ t))⁻¹ ((t : ℂ) * u) := by
      rwa [(hγ.2.2.2 t htIcc).2] at hφd
    have h := (hφ'.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hlin
    refine h.congr_deriv ?_
    simp [div_eq_mul_inv]
  exact hcomp.congr_of_eventuallyEq heq

theorem ray_lift_or_escape {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1))
    (hg0 : g 0 = 0) (hgne : ∀ z ∈ ball (0 : ℂ) 1, deriv g z ≠ 0)
    {u : ℂ} (hu : ‖u‖ = 1) {R_target : ℝ} (hR : 0 < R_target) :
    (∃ γ, IsLift g u R_target γ) ∨
    (∃ T₀ ∈ Ioc 0 R_target, ∃ γ : ℝ → ℂ,
      (∀ T ∈ Ico 0 T₀, IsLift g u T γ) ∧
      Tendsto (fun t => ‖γ t‖) (𝓝[<] T₀) (𝓝 1)) := by
  by_cases hfull : ∃ γ, IsLift g u R_target γ
  · exact Or.inl hfull
  right
  let A : Set ℝ := {T ∈ Icc 0 R_target | ∃ γ, IsLift g u T γ}
  have h0A : (0 : ℝ) ∈ A := by
    refine ⟨⟨le_rfl, hR.le⟩, fun _ => 0, le_rfl, continuousOn_const, rfl, ?_⟩
    intro t ht
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst ht0
    exact ⟨mem_ball_self zero_lt_one, by simp [hg0]⟩
  have hbdd : BddAbove A := ⟨R_target, fun T hT => hT.1.2⟩
  let T₀ := sSup A
  have hT₀_le : T₀ ≤ R_target := csSup_le ⟨0, h0A⟩ (fun T hT => hT.1.2)
  have hT₀_pos : 0 < T₀ := by
    obtain ⟨γ₀, hγ₀⟩ := h0A.2
    obtain ⟨δ, hδ, γ₁, hγ₁, _⟩ := lift_extend hg hgne hu hγ₀
    let ε := min δ R_target
    have hε0 : 0 < ε := lt_min hδ hR
    have hεA : ε ∈ A := by
      refine ⟨⟨hε0.le, min_le_right _ _⟩, γ₁, hε0.le,
        hγ₁.2.1.mono (Icc_subset_Icc_right (by linarith [min_le_left δ R_target])),
        hγ₁.2.2.1, fun t ht => hγ₁.2.2.2 t ⟨ht.1, by linarith [ht.2, min_le_left δ R_target]⟩⟩
    exact hε0.trans_le (le_csSup hbdd hεA)
  have hT₀_notA : T₀ ∉ A := by
    intro hmem
    obtain ⟨γT, hγT⟩ := hmem.2
    rcases hT₀_le.eq_or_lt with heq | hlt
    · rw [heq] at hγT
      exact hfull ⟨γT, hγT⟩
    · obtain ⟨δ, hδ, γ', hγ', _⟩ := lift_extend hg hgne hu hγT
      let ε := min δ (R_target - T₀)
      have hε0 : 0 < ε := lt_min hδ (sub_pos.mpr hlt)
      have hTε : T₀ + ε ∈ A := by
        refine ⟨⟨by linarith, by linarith [min_le_right δ (R_target - T₀)]⟩, γ',
          by linarith, hγ'.2.1.mono (Icc_subset_Icc_right (by linarith [min_le_left δ (R_target - T₀)])),
          hγ'.2.2.1, fun t ht => hγ'.2.2.2 t ⟨ht.1, by linarith [ht.2, min_le_left δ (R_target - T₀)]⟩⟩
      linarith [le_csSup hbdd hTε]
  have hex_lift : ∀ T ∈ Ico 0 T₀, ∃ γ, IsLift g u T γ := by
    intro T hT
    obtain ⟨S, hSA, hTS⟩ := exists_lt_of_lt_csSup ⟨0, h0A⟩ hT.2
    obtain ⟨γS, hγS⟩ := hSA.2
    exact ⟨γS, hT.1, hγS.2.1.mono (Icc_subset_Icc_right hTS.le), hγS.2.2.1,
      fun t ht => hγS.2.2.2 t ⟨ht.1, ht.2.trans hTS.le⟩⟩
  classical
  let γ : ℝ → ℂ := fun t =>
    if ht : t ∈ Ico 0 T₀ then (hex_lift t ht).choose t else 0
  have hγ_lift : ∀ T ∈ Ico 0 T₀, IsLift g u T γ := by
    intro T hT
    obtain ⟨γT, hγT⟩ := hex_lift T hT
    have heq : EqOn γ γT (Icc 0 T) := by
      intro t ht
      have ht' : t ∈ Ico 0 T₀ := ⟨ht.1, ht.2.trans_lt hT.2⟩
      simp only [γ, dif_pos ht']
      have h1 := (hex_lift t ht').choose_spec
      have h2 : IsLift g u t γT :=
        ⟨ht.1, hγT.2.1.mono (Icc_subset_Icc_right ht.2), hγT.2.2.1,
          fun s hs => hγT.2.2.2 s ⟨hs.1, hs.2.trans ht.2⟩⟩
      exact lift_unique hg hgne h1 h2 (right_mem_Icc.mpr ht.1)
    exact ⟨hγT.1, hγT.2.1.congr heq, by rw [heq (left_mem_Icc.mpr hγT.1), hγT.2.2.1],
      fun t ht => by rw [heq ht]; exact hγT.2.2.2 t ht⟩
  refine ⟨T₀, ⟨hT₀_pos, hT₀_le⟩, γ, hγ_lift, ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  suffices hge : ∀ᶠ t in 𝓝[<] T₀, 1 - ε < ‖γ t‖ by
    filter_upwards [hge, Ioo_mem_nhdsLT hT₀_pos] with t ht1 ht2
    have hlt1 : ‖γ t‖ < 1 :=
      mem_ball_zero_iff.mp ((hγ_lift t ⟨ht2.1.le, ht2.2⟩).2.2.2 t (right_mem_Icc.mpr ht2.1.le)).1
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  by_contra hnot
  have hfreq : ∀ n : ℕ, ∃ t ∈ Ioo (max 0 (T₀ - 1 / ((n : ℝ) + 1))) T₀, ‖γ t‖ ≤ 1 - ε := by
    intro n
    have hlo : max 0 (T₀ - 1 / ((n : ℝ) + 1)) < T₀ := by
      apply max_lt hT₀_pos
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    have hmem : Ioo (max 0 (T₀ - 1 / ((n : ℝ) + 1))) T₀ ∈ 𝓝[<] T₀ := Ioo_mem_nhdsLT hlo
    by_contra hnone
    push Not at hnone
    exact hnot (Filter.mem_of_superset hmem hnone)
  choose seq hseq_mem hseq_le using hfreq
  have hseq_tendsto : Tendsto seq atTop (𝓝 T₀) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    refine ⟨N, fun n hn => ?_⟩
    have h1 := (hseq_mem n).1
    have h2 := (hseq_mem n).2
    have h3 : T₀ - 1 / ((n : ℝ) + 1) < seq n := lt_of_le_of_lt (le_max_right _ _) h1
    have h4 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      gcongr
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  let r₀ : ℝ := max 0 (1 - ε)
  have hr₀_lt : r₀ < 1 := max_lt zero_lt_one (by linarith)
  have hseq_ball : ∀ n, γ (seq n) ∈ closedBall (0 : ℂ) r₀ := fun n =>
    mem_closedBall_zero_iff.mpr ((hseq_le n).trans (le_max_right _ _))
  obtain ⟨z₀, hz₀_cl, φ_idx, hφ_mono, hφ_lim⟩ :=
    (isCompact_closedBall (0 : ℂ) r₀).tendsto_subseq hseq_ball
  have hz₀_ball : z₀ ∈ ball (0 : ℂ) 1 :=
    mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hz₀_cl).trans_lt hr₀_lt)
  have hgz₀ : g z₀ = (T₀ : ℂ) * u := by
    have h1 : Tendsto (fun k => g (γ (seq (φ_idx k)))) atTop (𝓝 (g z₀)) :=
      (hg.continuousOn.continuousAt (isOpen_ball.mem_nhds hz₀_ball)).tendsto.comp hφ_lim
    have h2 : Tendsto (fun k => g (γ (seq (φ_idx k)))) atTop (𝓝 ((T₀ : ℂ) * u)) := by
      have heq : (fun k => g (γ (seq (φ_idx k)))) = fun k => (seq (φ_idx k) : ℂ) * u := by
        funext k
        have hmem := hseq_mem (φ_idx k)
        have h0le : 0 ≤ seq (φ_idx k) := (le_max_left _ _).trans hmem.1.le
        exact ((hγ_lift (seq (φ_idx k)) ⟨h0le, hmem.2⟩).2.2.2 _ (right_mem_Icc.mpr h0le)).2
      rw [heq]
      have hc : Continuous (fun t : ℝ => (t : ℂ) * u) := by fun_prop
      exact (hc.tendsto T₀).comp (hseq_tendsto.comp hφ_mono.tendsto_atTop)
    exact tendsto_nhds_unique h1 h2
  obtain ⟨U, δ, φ, hUopen, hz₀U, hUsub, hδ, hφcont, hφval, hφmaps, hφright, hφleft⟩ :=
    local_inv_at hg hgne hz₀_ball
  have hevU : ∀ᶠ k in atTop, γ (seq (φ_idx k)) ∈ U :=
    hφ_lim.eventually (hUopen.mem_nhds hz₀U)
  have hevδ : ∀ᶠ k in atTop, T₀ - seq (φ_idx k) < δ := by
    have hsub := hseq_tendsto.comp hφ_mono.tendsto_atTop
    have hlim : Tendsto (fun k => T₀ - seq (φ_idx k)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := T₀)).sub hsub
    exact hlim.eventually (Iio_mem_nhds hδ)
  obtain ⟨k, hkU, hkδ⟩ := (hevU.and hevδ).exists
  let t₁ := seq (φ_idx k)
  have ht₁_mem := hseq_mem (φ_idx k)
  have ht₁_0 : 0 ≤ t₁ := (le_max_left _ _).trans ht₁_mem.1.le
  have ht₁_lt : t₁ < T₀ := ht₁_mem.2
  have hseg : ∀ s ∈ Icc t₁ T₀, (s : ℂ) * u ∈ ball (g z₀) δ := by
    intro s hs
    rw [hgz₀, mem_ball_iff_norm, show (s : ℂ) * u - (T₀ : ℂ) * u = ((s - T₀ : ℝ) : ℂ) * u by
      push_cast; ring, norm_mul, hu, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr hs.2)]
    linarith [hs.1]
  have hγt₁_eq : φ ((t₁ : ℂ) * u) = γ t₁ := by
    have hlift1 := hγ_lift t₁ ⟨ht₁_0, ht₁_lt⟩
    have hgt₁ := (hlift1.2.2.2 t₁ (right_mem_Icc.mpr ht₁_0)).2
    rw [← hgt₁]
    exact hφleft (γ t₁) hkU (hgt₁.symm ▸ hseg t₁ ⟨le_rfl, ht₁_lt.le⟩)
  let γ_full : ℝ → ℂ := fun s => if s ≤ t₁ then γ s else φ ((s : ℂ) * u)
  have hlift1 := hγ_lift t₁ ⟨ht₁_0, ht₁_lt⟩
  have hcont_full : ContinuousOn γ_full (Icc 0 T₀) := by
    rw [(Icc_union_Icc_eq_Icc ht₁_0 ht₁_lt.le).symm]
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
    · exact hlift1.2.1.congr (fun s hs => by simp [γ_full, hs.2])
    · refine (hφcont.comp (by fun_prop) hseg).congr (fun s hs => ?_)
      dsimp [γ_full]
      split_ifs with hle
      · have hseq_eq : s = t₁ := le_antisymm hle hs.1
        subst hseq_eq
        exact hγt₁_eq.symm
      · rfl
  have hfull_T₀ : IsLift g u T₀ γ_full := by
    refine ⟨hT₀_pos.le, hcont_full, by simp [γ_full, ht₁_0, hlift1.2.2.1], ?_⟩
    intro s hs
    dsimp [γ_full]
    split_ifs with hle
    · exact hlift1.2.2.2 s ⟨hs.1, hle⟩
    · have hmem := hseg s ⟨le_of_not_ge hle, hs.2⟩
      exact ⟨hUsub (hφmaps hmem), hφright _ hmem⟩
  exact hT₀_notA ⟨⟨hT₀_pos.le, hT₀_le⟩, γ_full, hfull_T₀⟩

theorem escape_integral_bound {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1))
    (hgne : ∀ z ∈ ball (0 : ℂ) 1, deriv g z ≠ 0)
    {u : ℂ} (hu : ‖u‖ = 1) {T₀ : ℝ} (hT₀ : 0 < T₀) {γ : ℝ → ℂ}
    (hγ : ∀ T ∈ Ico 0 T₀, IsLift g u T γ)
    (hlim : Tendsto (fun t => ‖γ t‖) (𝓝[<] T₀) (𝓝 1))
    {ω : ℝ → ℝ} (hω_cont : ContinuousOn ω (Iio 1))
    (hω_nonneg : ∀ s < 1, 0 ≤ ω s)
    (hω_le : ∀ t ∈ Ico 0 T₀, ω ‖γ t‖ ≤ ‖deriv g (γ t)‖)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∫ s in (0 : ℝ)..r, ω s) ≤ T₀ := by
  have hev_gt : ∀ᶠ t in 𝓝[<] T₀, r < ‖γ t‖ := hlim.eventually (Ioi_mem_nhds hr1)
  have hev_in : ∀ᶠ t in 𝓝[<] T₀, t ∈ Ioo 0 T₀ := Ioo_mem_nhdsLT hT₀
  obtain ⟨T, hTr, hT0, hTT₀⟩ := (hev_gt.and hev_in).exists
  have hlift := hγ T ⟨hT0.le, hTT₀⟩
  have hnorm_cont : ContinuousOn (fun t => ‖γ t‖) (Icc 0 T) := hlift.2.1.norm
  obtain ⟨tM, htM, hMmax⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_isMaxOn
    ⟨0, left_mem_Icc.mpr hT0.le⟩ hnorm_cont
  let M : ℝ := ‖γ tM‖
  have hMlt : M < 1 := mem_ball_zero_iff.mp (hlift.2.2.2 tM htM).1
  have hM0 : 0 ≤ M := norm_nonneg _
  have hdg_cont : ContinuousOn (fun t => ‖deriv g (γ t)‖) (Icc 0 T) :=
    ((hg.deriv isOpen_ball).continuousOn.comp hlift.2.1
      (fun t ht => (hlift.2.2.2 t ht).1)).norm
  obtain ⟨tc, htc, hcmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_isMinOn
    ⟨0, left_mem_Icc.mpr hT0.le⟩ hdg_cont
  let c₀ : ℝ := ‖deriv g (γ tc)‖
  have hc₀_pos : 0 < c₀ := norm_pos_iff.mpr (hgne _ (hlift.2.2.2 tc htc).1)
  have hω_M : ContinuousOn ω (Icc 0 M) :=
    hω_cont.mono (fun s hs => hs.2.trans_lt hMlt)
  obtain ⟨sC, hsC, hCmax⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := M)).exists_isMaxOn
    ⟨0, left_mem_Icc.mpr hM0⟩ hω_M
  let Cω : ℝ := ω sC
  have hCω_nn : 0 ≤ Cω := hω_nonneg sC (hsC.2.trans_lt hMlt)
  let Ψ : ℝ → ℝ := fun s => ∫ x in (0 : ℝ)..s, ω x
  have hΨ_deriv : ∀ s < 1, HasDerivAt Ψ (ω s) s := by
    intro s hs
    have hint : IntervalIntegrable ω MeasureTheory.volume 0 s := by
      refine (hω_cont.mono ?_).intervalIntegrable
      intro x hx
      rcases le_total 0 s with h0s | hs0
      · rw [uIcc_of_le h0s] at hx
        exact hx.2.trans_lt hs
      · rw [uIcc_of_ge hs0] at hx
        exact hx.2.trans_lt zero_lt_one
    have hsm : StronglyMeasurableAtFilter ω (𝓝 s) MeasureTheory.volume :=
      hω_cont.stronglyMeasurableAtFilter isOpen_Iio s hs
    have hca : ContinuousAt ω s := hω_cont.continuousAt (isOpen_Iio.mem_nhds hs)
    exact intervalIntegral.integral_hasDerivAt_right hint hsm hca
  have hΨ_T_le : Ψ ‖γ T‖ ≤ T := by
    have huc := (isCompact_Icc (a := (0 : ℝ)) (b := M)).uniformContinuousOn_of_continuous hω_M
    suffices hstep : ∀ ε > 0, Ψ ‖γ T‖ ≤ T + (T / c₀ + Cω) * ε by
      by_contra! hgt
      have hpos : 0 < T / c₀ + Cω := by positivity
      let ε := (Ψ ‖γ T‖ - T) / (2 * (T / c₀ + Cω))
      have hε : 0 < ε := div_pos (by linarith) (by positivity)
      have h := hstep ε hε
      have : (T / c₀ + Cω) * ε = (Ψ ‖γ T‖ - T) / 2 := by
        dsimp [ε]
        field_simp [hpos.ne']
      linarith
    intro ε hε
    rw [Metric.uniformContinuousOn_iff] at huc
    obtain ⟨δ₀, hδ₀, hδ₀_prop⟩ := huc ε hε
    let δ : ℝ := min (δ₀ / 2) ε
    have hδ_pos : 0 < δ := lt_min (half_pos hδ₀) hε
    have hδ_lt : δ < δ₀ := (min_le_left _ _).trans_lt (half_lt_self hδ₀)
    have hδ_le_ε : δ ≤ ε := min_le_right _ _
    let ρ : ℝ → ℝ := fun t => Real.sqrt (‖γ t‖ ^ 2 + δ ^ 2) - δ
    have hρ0 : ρ 0 = 0 := by
      simp [ρ, hlift.2.2.1, Real.sqrt_sq hδ_pos.le]
    have hρ_bounds : ∀ t ∈ Icc 0 T, 0 ≤ ρ t ∧ ρ t ≤ ‖γ t‖ ∧ ‖γ t‖ - ρ t ≤ δ := by
      intro t _
      have hsq1 : δ ^ 2 ≤ ‖γ t‖ ^ 2 + δ ^ 2 := le_add_of_nonneg_left (sq_nonneg _)
      have hsq2 : ‖γ t‖ ^ 2 ≤ ‖γ t‖ ^ 2 + δ ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
      have hsq3 : ‖γ t‖ ^ 2 + δ ^ 2 ≤ (‖γ t‖ + δ) ^ 2 := by
        nlinarith [norm_nonneg (γ t)]
      have hr1 : δ ≤ Real.sqrt (‖γ t‖ ^ 2 + δ ^ 2) := by
        simpa [Real.sqrt_sq hδ_pos.le] using Real.sqrt_le_sqrt hsq1
      have hr2 : ‖γ t‖ ≤ Real.sqrt (‖γ t‖ ^ 2 + δ ^ 2) := by
        simpa [Real.sqrt_sq (norm_nonneg (γ t))] using Real.sqrt_le_sqrt hsq2
      have hr3 : Real.sqrt (‖γ t‖ ^ 2 + δ ^ 2) ≤ ‖γ t‖ + δ := by
        simpa [Real.sqrt_sq (by positivity : 0 ≤ ‖γ t‖ + δ)] using Real.sqrt_le_sqrt hsq3
      exact ⟨by linarith, by linarith, by linarith⟩
    have hρ_lt1 : ∀ t ∈ Icc 0 T, ρ t < 1 := fun t ht =>
      (hρ_bounds t ht).2.1.trans_lt ((hMmax ht).trans_lt hMlt)
    have hρ_cont : ContinuousOn ρ (Icc 0 T) :=
      (((hlift.2.1.norm.pow 2).add continuousOn_const).sqrt).sub continuousOn_const
    let F : ℝ → ℝ := fun t => Ψ (ρ t) - (1 + ε / c₀) * t
    have hF_cont : ContinuousOn F (Icc 0 T) := by
      have hΨ_cont : ContinuousOn Ψ (Iio 1) :=
        fun s hs => (hΨ_deriv s hs).continuousAt.continuousWithinAt
      exact (hΨ_cont.comp hρ_cont hρ_lt1).sub (by fun_prop)
    have hF_deriv : ∀ t ∈ interior (Icc 0 T),
        ∃ f', HasDerivWithinAt F f' (interior (Icc 0 T)) t ∧ f' ≤ 0 := by
      intro t ht
      rw [interior_Icc] at ht
      have htIcc : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
      have hγd := lift_hasDerivAt hg hgne hlift ht
      set v := u / deriv g (γ t)
      have hre_d : HasDerivAt (fun s => (γ s).re) v.re t :=
        Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hγd
      have him_d : HasDerivAt (fun s => (γ s).im) v.im t :=
        Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hγd
      have hsq_eq : (fun s => ‖γ s‖ ^ 2 + δ ^ 2) =
          fun s => (γ s).re ^ 2 + (γ s).im ^ 2 + δ ^ 2 := by
        funext s
        rw [Complex.sq_norm, Complex.normSq_apply]
        ring
      have hsq_d : HasDerivAt (fun s => ‖γ s‖ ^ 2 + δ ^ 2)
          (2 * ((γ t).re * v.re + (γ t).im * v.im)) t := by
        rw [hsq_eq]
        refine (((hre_d.fun_pow 2).add (him_d.fun_pow 2)).add_const (δ ^ 2)).congr_deriv ?_
        ring
      have hrad_pos : 0 < ‖γ t‖ ^ 2 + δ ^ 2 := by positivity
      have hρ_d : HasDerivAt ρ
          (((γ t).re * v.re + (γ t).im * v.im) / Real.sqrt (‖γ t‖ ^ 2 + δ ^ 2)) t := by
        refine (((Real.hasDerivAt_sqrt hrad_pos.ne').comp t hsq_d).sub_const δ).congr_deriv ?_
        have hsq_pos : Real.sqrt (‖γ t‖ ^ 2 + δ ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hrad_pos).ne'
        field_simp [hsq_pos]
      have hΨ_d : HasDerivAt (fun s => Ψ (ρ s))
          (ω (ρ t) * (((γ t).re * v.re + (γ t).im * v.im) /
            Real.sqrt (‖γ t‖ ^ 2 + δ ^ 2))) t :=
        (hΨ_deriv (ρ t) (hρ_lt1 t htIcc)).comp t hρ_d
      have hlin_d : HasDerivAt (fun s => (1 + ε / c₀) * s) (1 + ε / c₀) t := by
        simpa using (hasDerivAt_id t).const_mul (1 + ε / c₀)
      refine ⟨ω (ρ t) * (((γ t).re * v.re + (γ t).im * v.im) /
          Real.sqrt (‖γ t‖ ^ 2 + δ ^ 2)) - (1 + ε / c₀),
        (hΨ_d.sub hlin_d).hasDerivWithinAt, ?_⟩
      set num := (γ t).re * v.re + (γ t).im * v.im
      set den := Real.sqrt (‖γ t‖ ^ 2 + δ ^ 2)
      have hden_pos : 0 < den := Real.sqrt_pos.mpr hrad_pos
      have hcs : num ≤ den * ‖v‖ := by
        have h1 : num ^ 2 ≤ ((γ t).re ^ 2 + (γ t).im ^ 2) * (v.re ^ 2 + v.im ^ 2) := by
          dsimp [num]
          nlinarith [sq_nonneg ((γ t).re * v.im - (γ t).im * v.re)]
        have h2 : (γ t).re ^ 2 + (γ t).im ^ 2 = ‖γ t‖ ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]; ring
        have h3 : v.re ^ 2 + v.im ^ 2 = ‖v‖ ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]; ring
        rw [h2, h3] at h1
        have h4 : num ^ 2 ≤ (den * ‖v‖) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hrad_pos.le]
          nlinarith [sq_nonneg ‖v‖]
        nlinarith [sq_nonneg (den * ‖v‖ - num), mul_nonneg hden_pos.le (norm_nonneg v)]
      have hquot_le : num / den ≤ 1 / ‖deriv g (γ t)‖ := by
        have hv_norm : ‖v‖ = 1 / ‖deriv g (γ t)‖ := by
          dsimp [v]
          rw [norm_div, hu]
        rw [div_le_iff₀ hden_pos, ← hv_norm]
        linarith
      have hω_ρ_nn : 0 ≤ ω (ρ t) := hω_nonneg (ρ t) (hρ_lt1 t htIcc)
      have hω_close : ω (ρ t) ≤ ‖deriv g (γ t)‖ + ε := by
        have hrb := hρ_bounds t htIcc
        have hdist : dist (ρ t) ‖γ t‖ < δ₀ := by
          rw [Real.dist_eq, abs_of_nonpos (by linarith)]
          linarith
        have hdiff := hδ₀_prop (ρ t) ⟨hrb.1, hrb.2.1.trans (hMmax htIcc)⟩
          ‖γ t‖ ⟨norm_nonneg _, hMmax htIcc⟩ hdist
        rw [Real.dist_eq, abs_lt] at hdiff
        have hωt := hω_le t ⟨ht.1.le, ht.2.trans hTT₀⟩
        linarith
      have hdg_pos : 0 < ‖deriv g (γ t)‖ :=
        norm_pos_iff.mpr (hgne _ (hlift.2.2.2 t htIcc).1)
      have hc₀_le : c₀ ≤ ‖deriv g (γ t)‖ := hcmin htIcc
      have hmul1 : ω (ρ t) * (num / den) ≤ ω (ρ t) * (1 / ‖deriv g (γ t)‖) :=
        mul_le_mul_of_nonneg_left hquot_le hω_ρ_nn
      have hmul2 : ω (ρ t) * (1 / ‖deriv g (γ t)‖) ≤ 1 + ε / ‖deriv g (γ t)‖ := by
        have h1 := mul_le_mul_of_nonneg_right hω_close (by positivity : 0 ≤ 1 / ‖deriv g (γ t)‖)
        have h2 : (‖deriv g (γ t)‖ + ε) * (1 / ‖deriv g (γ t)‖) = 1 + ε / ‖deriv g (γ t)‖ := by
          field_simp [hdg_pos.ne']
        linarith
      have hdiv_le : ε / ‖deriv g (γ t)‖ ≤ ε / c₀ :=
        div_le_div_of_nonneg_left hε.le hc₀_pos hc₀_le
      linarith
    have hanti : AntitoneOn F (Icc 0 T) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hF_cont ?_ ?_
      · intro t ht
        obtain ⟨f', hf', _⟩ := hF_deriv t ht
        exact hf'.differentiableWithinAt
      · intro t ht
        obtain ⟨f', hf', hle⟩ := hF_deriv t ht
        have : deriv F t = f' := (hf'.hasDerivAt (isOpen_interior.mem_nhds ht)).deriv
        linarith
    have hFT_le : F T ≤ F 0 := hanti ⟨le_rfl, hT0.le⟩ ⟨hT0.le, le_rfl⟩ hT0.le
    have hF0 : F 0 = 0 := by simp [F, hρ0, Ψ]
    have hΨ_ρT : Ψ (ρ T) ≤ (1 + ε / c₀) * T := by
      dsimp [F] at hFT_le
      linarith
    have hT_Icc : T ∈ Icc 0 T := right_mem_Icc.mpr hT0.le
    have hrbT := hρ_bounds T hT_Icc
    have hint1 : IntervalIntegrable ω MeasureTheory.volume 0 (ρ T) :=
      (hω_cont.mono (fun x hx => by
        rw [uIcc_of_le hrbT.1] at hx
        exact hx.2.trans_lt (hρ_lt1 T hT_Icc))).intervalIntegrable
    have hint2 : IntervalIntegrable ω MeasureTheory.volume (ρ T) ‖γ T‖ :=
      (hω_cont.mono (fun x hx => by
        rw [uIcc_of_le hrbT.2.1] at hx
        exact hx.2.trans_lt ((hMmax hT_Icc).trans_lt hMlt))).intervalIntegrable
    have hΨ_diff : Ψ ‖γ T‖ - Ψ (ρ T) = ∫ x in (ρ T)..‖γ T‖, ω x := by
      dsimp [Ψ]
      have hadd := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
      linarith
    have htail_le : (∫ x in (ρ T)..‖γ T‖, ω x) ≤ Cω * δ := by
      calc
        ∫ x in (ρ T)..‖γ T‖, ω x
          ≤ ∫ _x in (ρ T)..‖γ T‖, Cω :=
            intervalIntegral.integral_mono_on hrbT.2.1 hint2 intervalIntegrable_const
              (fun x hx => hCmax ⟨hrbT.1.trans hx.1, hx.2.trans (hMmax hT_Icc)⟩)
        _ = (‖γ T‖ - ρ T) * Cω := by simp
        _ ≤ δ * Cω := mul_le_mul_of_nonneg_right hrbT.2.2 hCω_nn
        _ = Cω * δ := mul_comm _ _
    have hCδ : Cω * δ ≤ Cω * ε := mul_le_mul_of_nonneg_left hδ_le_ε hCω_nn
    have hcomb : Ψ ‖γ T‖ ≤ (1 + ε / c₀) * T + Cω * ε := by linarith
    calc
      Ψ ‖γ T‖ ≤ (1 + ε / c₀) * T + Cω * ε := hcomb
      _ = T + (T / c₀ + Cω) * ε := by ring
  have hΨ_r_le : Ψ r ≤ Ψ ‖γ T‖ := by
    have hint1 : IntervalIntegrable ω MeasureTheory.volume 0 r :=
      (hω_cont.mono (fun x hx => by
        rw [uIcc_of_le hr0] at hx
        exact hx.2.trans_lt hr1)).intervalIntegrable
    have hγT_lt : ‖γ T‖ < 1 := (hMmax (right_mem_Icc.mpr hT0.le)).trans_lt hMlt
    have hint2 : IntervalIntegrable ω MeasureTheory.volume r ‖γ T‖ :=
      (hω_cont.mono (fun x hx => by
        rw [uIcc_of_le hTr.le] at hx
        exact hx.2.trans_lt hγT_lt)).intervalIntegrable
    have hadd := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
    have hnn : 0 ≤ ∫ x in r..‖γ T‖, ω x :=
      intervalIntegral.integral_nonneg hTr.le (fun x hx => hω_nonneg x (hx.2.trans_lt hγT_lt))
    dsimp [Ψ]
    linarith
  exact hΨ_r_le.trans (hΨ_T_le.trans hTT₀.le)

end LandauEscape

/- ## Section 5: Angular proximity near the origin -/

namespace LandauAngle

theorem norm_g_sub_id_le {g h : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball 0 1)) (hg0 : g 0 = 0) (hg1 : deriv g 0 = 1)
    (hW : ∀ z ∈ ball (0 : ℂ) 1, (1 - ‖z‖ ^ 2) * ‖deriv g z‖ ≤ 1)
    (hh : DifferentiableOn ℂ h (ball 0 1)) (hh0 : h 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) 1, Complex.exp (h z) = deriv g z)
    (hc2_le : ‖(cauchyPowerSeries h 0 (1 / 2)).coeff 2‖ ≤ 1)
    {z : ℂ} (hz : ‖z‖ ≤ 1 / 500) :
    ‖g z - z‖ ≤ 4 * ‖z‖ ^ 3 := by
  have hh1 := LandauLog.deriv_log_zero hg hg1 hW hh hh0 hexp
  have hre : ∀ w ∈ ball (0 : ℂ) 1, (h w).re ≤ -Real.log (1 - ‖w‖ ^ 2) :=
    fun w hw => LandauLog.re_log_le hW hexp hw
  have hc3_le : ‖(cauchyPowerSeries h 0 (1 / 2)).coeff 3‖ ≤ 48 := by
    have := LandauLog.coeff_bound_six hh hh0 hre 3
    norm_num at this
    exact this
  let k : ℂ → ℂ := fun w => g w - w
  have hk_diff : ∀ w ∈ closedBall (0 : ℂ) ‖z‖, DifferentiableAt ℂ k w := by
    intro w hw
    have hw1 : w ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff]
      exact (mem_closedBall_zero_iff.mp hw).trans_lt (by linarith)
    exact (hg.differentiableAt (isOpen_ball.mem_nhds hw1)).sub differentiableAt_id
  have hk_bound : ∀ w ∈ closedBall (0 : ℂ) ‖z‖, ‖deriv k w‖ ≤ 4 * ‖z‖ ^ 2 := by
    intro w hw
    have hwz : ‖w‖ ≤ ‖z‖ := mem_closedBall_zero_iff.mp hw
    have hw500 : ‖w‖ ≤ 1 / 500 := hwz.trans hz
    have hw1 : w ∈ ball (0 : ℂ) 1 := by rw [mem_ball_zero_iff]; linarith
    have hdk : deriv k w = deriv g w - 1 := by
      have h1 := (hg.differentiableAt (isOpen_ball.mem_nhds hw1)).hasDerivAt
      exact (h1.sub (hasDerivAt_id w)).deriv
    rw [hdk, ← hexp w hw1]
    have ht := LandauLog.tail_bound_192 hh hh0 hh1 hre (z := w) (by linarith)
    have hhw : ‖h w‖ ≤ 2 * ‖w‖ ^ 2 := by
      set c2 := (cauchyPowerSeries h 0 (1 / 2)).coeff 2
      set c3 := (cauchyPowerSeries h 0 (1 / 2)).coeff 3
      have htri : ‖h w‖ ≤ ‖h w - (c2 * w ^ 2 + c3 * w ^ 3)‖ + ‖c2 * w ^ 2 + c3 * w ^ 3‖ :=
        norm_le_norm_sub_add (h w) (c2 * w ^ 2 + c3 * w ^ 3)
      have hmain : ‖c2 * w ^ 2 + c3 * w ^ 3‖ ≤ 1 * ‖w‖ ^ 2 + 48 * ‖w‖ ^ 3 := by
        calc
          ‖c2 * w ^ 2 + c3 * w ^ 3‖ ≤ ‖c2 * w ^ 2‖ + ‖c3 * w ^ 3‖ := norm_add_le _ _
          _ = ‖c2‖ * ‖w‖ ^ 2 + ‖c3‖ * ‖w‖ ^ 3 := by simp [norm_pow]
          _ ≤ 1 * ‖w‖ ^ 2 + 48 * ‖w‖ ^ 3 := by gcongr
      have hwn : 0 ≤ ‖w‖ := norm_nonneg w
      have hrem : 48 * ‖w‖ ^ 3 + 192 * ‖w‖ ^ 4 ≤ ‖w‖ ^ 2 := by
        have h1 : 48 * ‖w‖ + 192 * ‖w‖ ^ 2 ≤ 1 := by nlinarith
        nlinarith [sq_nonneg ‖w‖]
      linarith
    have hhw1 : ‖h w‖ ≤ 1 := by nlinarith [norm_nonneg w]
    have hexp_b := Complex.norm_exp_sub_one_le hhw1
    nlinarith [norm_nonneg w]
  have hmvt := (convex_closedBall (0 : ℂ) ‖z‖).norm_image_sub_le_of_norm_deriv_le
    (x := 0) (y := z) hk_diff hk_bound (mem_closedBall_self (norm_nonneg z))
    (by rw [mem_closedBall_zero_iff])
  have hk0 : k 0 = 0 := by simp [k, hg0]
  calc
    ‖g z - z‖ ≤ 4 * ‖z‖ ^ 2 * ‖z‖ := by simpa [k, hk0] using hmvt
    _ = 4 * ‖z‖ ^ 3 := by ring

theorem im_unit_close {g h : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball 0 1)) (hg0 : g 0 = 0) (hg1 : deriv g 0 = 1)
    (hW : ∀ z ∈ ball (0 : ℂ) 1, (1 - ‖z‖ ^ 2) * ‖deriv g z‖ ≤ 1)
    (hh : DifferentiableOn ℂ h (ball 0 1)) (hh0 : h 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) 1, Complex.exp (h z) = deriv g z)
    (hc2_le : ‖(cauchyPowerSeries h 0 (1 / 2)).coeff 2‖ ≤ 1)
    {z u : ℂ} {t : ℝ} (hz0 : 0 < ‖z‖) (hz500 : ‖z‖ ≤ 1 / 500)
    (hu : ‖u‖ = 1) (ht : 0 ≤ t) (hgz : g z = (t : ℂ) * u) :
    |(z / (‖z‖ : ℂ)).im - u.im| < 1 / 100 := by
  have hdiff := norm_g_sub_id_le hg hg0 hg1 hW hh hh0 hexp hc2_le hz500
  rw [hgz] at hdiff
  have ht_norm : ‖(t : ℂ) * u‖ = t := by
    rw [norm_mul, hu, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
  have htr : |t - ‖z‖| ≤ 4 * ‖z‖ ^ 3 := by
    rw [← ht_norm]
    exact (abs_norm_sub_norm_le ((t : ℂ) * u) z).trans hdiff
  have hzu : ‖z - (‖z‖ : ℂ) * u‖ ≤ 8 * ‖z‖ ^ 3 := by
    have hsplit : z - (‖z‖ : ℂ) * u = (z - (t : ℂ) * u) + ((t - ‖z‖ : ℝ) : ℂ) * u := by
      push_cast; ring
    rw [hsplit]
    calc
      ‖(z - (t : ℂ) * u) + ((t - ‖z‖ : ℝ) : ℂ) * u‖
        ≤ ‖z - (t : ℂ) * u‖ + ‖((t - ‖z‖ : ℝ) : ℂ) * u‖ := norm_add_le _ _
      _ = ‖(t : ℂ) * u - z‖ + |t - ‖z‖| := by
        rw [norm_sub_rev, norm_mul, hu, mul_one, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 4 * ‖z‖ ^ 3 + 4 * ‖z‖ ^ 3 := add_le_add hdiff htr
      _ = 8 * ‖z‖ ^ 3 := by ring
  have hunit : ‖z / (‖z‖ : ℂ) - u‖ ≤ 8 * ‖z‖ ^ 2 := by
    have hrC : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz0.ne'
    have heq : z / (‖z‖ : ℂ) - u = (z - (‖z‖ : ℂ) * u) / (‖z‖ : ℂ) := by
      field_simp [hrC]
    rw [heq, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz0, div_le_iff₀ hz0]
    nlinarith
  have him : |(z / (‖z‖ : ℂ)).im - u.im| ≤ ‖z / (‖z‖ : ℂ) - u‖ := by
    simpa [Complex.sub_im] using Complex.abs_im_le_norm (z / (‖z‖ : ℂ) - u)
  nlinarith

end LandauAngle

/- ## Section 6: Excess bounds, center shift, and final theorem -/

namespace LandauMain

private theorem baseline_ray_bound {g h : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball 0 1)) (hg0 : g 0 = 0) (hg1 : deriv g 0 = 1)
    (hgne : ∀ z ∈ ball (0 : ℂ) 1, deriv g z ≠ 0)
    (hW : ∀ z ∈ ball (0 : ℂ) 1, (1 - ‖z‖ ^ 2) * ‖deriv g z‖ ≤ 1)
    (hh : DifferentiableOn ℂ h (ball 0 1)) (hh0 : h 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) 1, Complex.exp (h z) = deriv g z)
    {u : ℂ} (hu : ‖u‖ = 1) {R_target : ℝ} (hR0 : 0 < R_target) (hR : R_target < 1 / 2) :
    (R_target : ℂ) * u ∈ g '' ball 0 1 := by
  rcases LandauEscape.ray_lift_or_escape hg hg0 hgne hu hR0 with
    ⟨γ, hγ⟩ | ⟨T₀, ⟨hT₀_pos, hT₀_le⟩, γ, hγ, hlim⟩
  · have hmem := hγ.2.2.2 R_target (right_mem_Icc.mpr hR0.le)
    exact ⟨γ R_target, hmem.1, hmem.2⟩
  · exfalso
    let ω : ℝ → ℝ := fun s => LandauLiuMinda.ell (max 0 s)
    have hω_cont : ContinuousOn ω (Iio 1) := by
      have hmax_lt : ∀ s ∈ Iio (1 : ℝ), 1 - max 0 s ≠ 0 := by
        intro s hs
        have : max 0 s < 1 := max_lt zero_lt_one hs
        linarith
      refine ContinuousOn.div ?_ ?_ (fun s hs => pow_ne_zero 2 (hmax_lt s hs))
      · refine ContinuousOn.rexp (ContinuousOn.div ?_ ?_ hmax_lt)
        · exact continuousOn_const.mul (continuous_const.max continuous_id).continuousOn
        · exact continuousOn_const.sub (continuous_const.max continuous_id).continuousOn
      · exact (continuousOn_const.sub (continuous_const.max continuous_id).continuousOn).pow 2
    have hω_nn : ∀ s < 1, 0 ≤ ω s := fun s hs =>
      (LandauLiuMinda.ell_pos (max_lt zero_lt_one hs)).le
    have hω_le : ∀ t ∈ Ico 0 T₀, ω ‖γ t‖ ≤ ‖deriv g (γ t)‖ := by
      intro t ht
      have hzt := ((hγ t ht).2.2.2 t (right_mem_Icc.mpr ht.1)).1
      simpa [ω, max_eq_right (norm_nonneg (γ t))] using
        LandauLiuMinda.liu_minda hg hg1 hW hh hh0 hexp hzt
    have hE_le : ∀ r ∈ Ioo (0 : ℝ) 1, LandauLiuMinda.E_fn r ≤ T₀ := by
      intro r ⟨hr0, hr1⟩
      have hint := LandauEscape.escape_integral_bound hg hgne hu hT₀_pos hγ hlim
        hω_cont hω_nn hω_le hr0.le hr1
      have hftc : (∫ s in (0 : ℝ)..r, ω s) = LandauLiuMinda.E_fn r := by
        have hcongr : (∫ s in (0 : ℝ)..r, ω s) = ∫ s in (0 : ℝ)..r, LandauLiuMinda.ell s := by
          refine intervalIntegral.integral_congr (fun s hs => ?_)
          rw [uIcc_of_le hr0.le] at hs
          simp [ω, max_eq_right hs.1]
        rw [hcongr]
        have h1 : ∀ s ∈ uIcc (0 : ℝ) r,
            HasDerivAt LandauLiuMinda.E_fn (LandauLiuMinda.ell s) s := by
          intro s hs
          rw [uIcc_of_le hr0.le] at hs
          exact LandauLiuMinda.hasDerivAt_E_fn (hs.2.trans_lt hr1)
        have h2 : IntervalIntegrable LandauLiuMinda.ell MeasureTheory.volume 0 r := by
          refine (hω_cont.mono (fun s hs => ?_)).congr (fun s hs => ?_) |>.intervalIntegrable
          · rw [uIcc_of_le hr0.le] at hs
            exact hs.2.trans_lt hr1
          · rw [uIcc_of_le hr0.le] at hs
            simp [ω, max_eq_right hs.1]
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h1 h2, LandauLiuMinda.E_fn_zero,
          sub_zero]
      linarith
    have hhalf : (1 / 2 : ℝ) ≤ T₀ :=
      le_of_tendsto LandauLiuMinda.tendsto_E_fn
        (Filter.mem_of_superset (Ioo_mem_nhdsLT zero_lt_one) hE_le)
    linarith

private theorem excess_ray_bound {g h : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball 0 1)) (hg0 : g 0 = 0) (hg1 : deriv g 0 = 1)
    (hgne : ∀ z ∈ ball (0 : ℂ) 1, deriv g z ≠ 0)
    (hW : ∀ z ∈ ball (0 : ℂ) 1, (1 - ‖z‖ ^ 2) * ‖deriv g z‖ ≤ 1)
    (hh : DifferentiableOn ℂ h (ball 0 1)) (hh0 : h 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) 1, Complex.exp (h z) = deriv g z)
    {u : ℂ} (hu : ‖u‖ = 1) {A r₁ : ℝ} {k : ℕ}
    (hA : 0 < A) (hr₁0 : 0 < r₁) (hr₁5 : r₁ ≤ 1 / 5) (hk : 1 ≤ k)
    (hexcess : ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 ≤ t → g z = (t : ℂ) * u →
      0 < ‖z‖ → ‖z‖ < r₁ → A * ‖z‖ ^ k ≤ (h z).re - Real.log (LandauLiuMinda.ell ‖z‖))
    {R_target : ℝ} (hR0 : 0 < R_target)
    (hR : R_target < 1 / 2 + A * r₁ ^ (k + 1) / (4 : ℝ) ^ (k + 2)) :
    (R_target : ℂ) * u ∈ g '' ball 0 1 := by
  rcases LandauEscape.ray_lift_or_escape hg hg0 hgne hu hR0 with
    ⟨γ, hγ⟩ | ⟨T₀, ⟨hT₀_pos, hT₀_le⟩, γ, hγ, hlim⟩
  · have hmem := hγ.2.2.2 R_target (right_mem_Icc.mpr hR0.le)
    exact ⟨γ R_target, hmem.1, hmem.2⟩
  · exfalso
    let bump : ℝ → ℝ := fun s =>
      LandauLiuMinda.ell (max 0 s) * (A * (max 0 s) ^ k * max 0 (1 - max 0 s / r₁))
    let ω : ℝ → ℝ := fun s => LandauLiuMinda.ell (max 0 s) + bump s
    have hell_cont : ContinuousOn (fun s => LandauLiuMinda.ell (max 0 s)) (Iio 1) := by
      have hmax_lt : ∀ s ∈ Iio (1 : ℝ), 1 - max 0 s ≠ 0 := by
        intro s hs
        have : max 0 s < 1 := max_lt zero_lt_one hs
        linarith
      refine ContinuousOn.div ?_ ?_ (fun s hs => pow_ne_zero 2 (hmax_lt s hs))
      · refine ContinuousOn.rexp (ContinuousOn.div ?_ ?_ hmax_lt)
        · exact continuousOn_const.mul (continuous_const.max continuous_id).continuousOn
        · exact continuousOn_const.sub (continuous_const.max continuous_id).continuousOn
      · exact (continuousOn_const.sub (continuous_const.max continuous_id).continuousOn).pow 2
    have hbump_cont : ContinuousOn bump (Iio 1) := by
      refine hell_cont.mul ?_
      have hmax_c : Continuous (fun s : ℝ => max 0 s) := continuous_const.max continuous_id
      exact ((continuous_const.mul (hmax_c.pow k)).mul
        (continuous_const.max (continuous_const.sub (hmax_c.div_const r₁)))).continuousOn
    have hω_cont : ContinuousOn ω (Iio 1) := hell_cont.add hbump_cont
    have hbump_nn : ∀ s < 1, 0 ≤ bump s := fun s hs =>
      mul_nonneg (LandauLiuMinda.ell_pos (max_lt zero_lt_one hs)).le
        (mul_nonneg (mul_nonneg hA.le (pow_nonneg (le_max_left 0 s) k)) (le_max_left _ _))
    have hω_nn : ∀ s < 1, 0 ≤ ω s := fun s hs =>
      add_nonneg (LandauLiuMinda.ell_pos (max_lt zero_lt_one hs)).le (hbump_nn s hs)
    have hω_le : ∀ t ∈ Ico 0 T₀, ω ‖γ t‖ ≤ ‖deriv g (γ t)‖ := by
      intro t ht
      have hmem := (hγ t ht).2.2.2 t (right_mem_Icc.mpr ht.1)
      have hzt : γ t ∈ ball (0 : ℂ) 1 := hmem.1
      have hgt : g (γ t) = (t : ℂ) * u := hmem.2
      set s := ‖γ t‖
      have hs0 : 0 ≤ s := norm_nonneg _
      have hs1 : s < 1 := mem_ball_zero_iff.mp hzt
      have hlm := LandauLiuMinda.liu_minda hg hg1 hW hh hh0 hexp hzt
      by_cases hs_ge : r₁ ≤ s
      · have h0 : max 0 (1 - s / r₁) = 0 := max_eq_left (by
          rw [sub_nonpos, le_div_iff₀ hr₁0]; linarith)
        simpa [ω, bump, max_eq_right hs0, h0] using hlm
      · push Not at hs_ge
        rcases hs0.eq_or_lt with hs_eq | hs_pos
        · have hk0 : s ^ k = 0 := by
            rw [← hs_eq]
            exact zero_pow (by omega)
          simpa [ω, bump, max_eq_right hs0, hk0] using hlm
        · have hex := hexcess (γ t) hzt t ht.1 hgt hs_pos hs_ge
          have hfac : max 0 (1 - s / r₁) ≤ 1 := by
            refine max_le zero_le_one ?_
            have : 0 ≤ s / r₁ := div_nonneg hs0 hr₁0.le
            linarith
          have h1 : 1 + A * s ^ k * max 0 (1 - s / r₁) ≤ 1 + A * s ^ k := by
            have : 0 ≤ A * s ^ k := mul_nonneg hA.le (pow_nonneg hs0 k)
            nlinarith
          have h2 : 1 + A * s ^ k ≤ Real.exp (A * s ^ k) := by
            linarith [Real.add_one_le_exp (A * s ^ k)]
          have h3 : Real.exp (A * s ^ k) ≤
              Real.exp ((h (γ t)).re - Real.log (LandauLiuMinda.ell s)) :=
            Real.exp_le_exp.mpr hex
          have h4 : Real.exp ((h (γ t)).re - Real.log (LandauLiuMinda.ell s)) =
              ‖deriv g (γ t)‖ / LandauLiuMinda.ell s := by
            rw [Real.exp_sub, Real.exp_log (LandauLiuMinda.ell_pos hs1),
              ← hexp (γ t) hzt, Complex.norm_exp]
          have h5 := (h1.trans (h2.trans h3)).trans_eq h4
          have h6 := mul_le_mul_of_nonneg_left h5 (LandauLiuMinda.ell_pos hs1).le
          rw [mul_div_cancel₀ _ (LandauLiuMinda.ell_pos hs1).ne'] at h6
          have heq : ω s = LandauLiuMinda.ell s * (1 + A * s ^ k * max 0 (1 - s / r₁)) := by
            dsimp [ω, bump]
            rw [max_eq_right hs0]
            ring
          rwa [heq]
    have hE_le : ∀ r ∈ Ioo r₁ 1,
        LandauLiuMinda.E_fn r + A * r₁ ^ (k + 1) / (4 : ℝ) ^ (k + 2) ≤ T₀ := by
      intro r ⟨hr_gt, hr1⟩
      have hr0 : 0 ≤ r := hr₁0.le.trans hr_gt.le
      have hint_all := LandauEscape.escape_integral_bound hg hgne hu hT₀_pos hγ hlim
        hω_cont hω_nn hω_le hr0 hr1
      have hint_ell : IntervalIntegrable (fun s => LandauLiuMinda.ell (max 0 s))
          MeasureTheory.volume 0 r :=
        (hell_cont.mono (fun s hs => by
          rw [uIcc_of_le hr0] at hs; exact hs.2.trans_lt hr1)).intervalIntegrable
      have hint_bump : IntervalIntegrable bump MeasureTheory.volume 0 r :=
        (hbump_cont.mono (fun s hs => by
          rw [uIcc_of_le hr0] at hs; exact hs.2.trans_lt hr1)).intervalIntegrable
      have hsplit : (∫ s in (0 : ℝ)..r, ω s) =
          (∫ s in (0 : ℝ)..r, LandauLiuMinda.ell (max 0 s)) +
          (∫ s in (0 : ℝ)..r, bump s) :=
        intervalIntegral.integral_add hint_ell hint_bump
      have hftc : (∫ s in (0 : ℝ)..r, LandauLiuMinda.ell (max 0 s)) =
          LandauLiuMinda.E_fn r := by
        have hcongr : (∫ s in (0 : ℝ)..r, LandauLiuMinda.ell (max 0 s)) =
            ∫ s in (0 : ℝ)..r, LandauLiuMinda.ell s :=
          intervalIntegral.integral_congr (fun s hs => by
            rw [uIcc_of_le hr0] at hs; simp [max_eq_right hs.1])
        rw [hcongr]
        have h1 : ∀ s ∈ uIcc (0 : ℝ) r,
            HasDerivAt LandauLiuMinda.E_fn (LandauLiuMinda.ell s) s := fun s hs => by
          rw [uIcc_of_le hr0] at hs
          exact LandauLiuMinda.hasDerivAt_E_fn (hs.2.trans_lt hr1)
        have h2 : IntervalIntegrable LandauLiuMinda.ell MeasureTheory.volume 0 r :=
          (hell_cont.mono (fun s hs => by
            rw [uIcc_of_le hr0] at hs; exact hs.2.trans_lt hr1)).congr
            (fun s hs => by rw [uIcc_of_le hr0] at hs; simp [max_eq_right hs.1])
            |>.intervalIntegrable
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h1 h2, LandauLiuMinda.E_fn_zero,
          sub_zero]
      have hbump_lb : A * r₁ ^ (k + 1) / (4 : ℝ) ^ (k + 2) ≤ ∫ s in (0 : ℝ)..r, bump s := by
        have hq1 : 0 ≤ r₁ / 4 := by linarith
        have hq2 : r₁ / 4 ≤ r₁ / 2 := by linarith
        have hq3 : r₁ / 2 ≤ r := by linarith
        have hi1 : IntervalIntegrable bump MeasureTheory.volume 0 (r₁ / 4) :=
          hint_bump.mono_set (uIcc_subset_uIcc_left (by rw [uIcc_of_le hr0]; exact ⟨hq1, hq2.trans hq3⟩))
        have hi2 : IntervalIntegrable bump MeasureTheory.volume (r₁ / 4) (r₁ / 2) :=
          hint_bump.mono_set (by
            rw [uIcc_of_le hq2, uIcc_of_le hr0]
            exact Icc_subset_Icc hq1 hq3)
        have hi3 : IntervalIntegrable bump MeasureTheory.volume (r₁ / 2) r :=
          hint_bump.mono_set (by
            rw [uIcc_of_le hq3, uIcc_of_le hr0]
            exact Icc_subset_Icc (hq1.trans hq2) le_rfl)
        have hadd1 := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
        have hi12 : IntervalIntegrable bump MeasureTheory.volume 0 (r₁ / 2) := hi1.trans hi2
        have hadd2 := intervalIntegral.integral_add_adjacent_intervals hi12 hi3
        have hnn1 : 0 ≤ ∫ s in (0 : ℝ)..(r₁ / 4), bump s :=
          intervalIntegral.integral_nonneg hq1 (fun s hs => hbump_nn s (by linarith [hs.2]))
        have hnn3 : 0 ≤ ∫ s in (r₁ / 2)..r, bump s :=
          intervalIntegral.integral_nonneg hq3 (fun s hs => hbump_nn s (hs.2.trans_lt hr1))
        have hmid : (r₁ / 4) * ((1 / 2) * (A * (r₁ / 4) ^ k * (1 / 2))) ≤
            ∫ s in (r₁ / 4)..(r₁ / 2), bump s := by
          have hconst : (∫ _s in (r₁ / 4)..(r₁ / 2),
              (1 / 2 : ℝ) * (A * (r₁ / 4) ^ k * (1 / 2))) =
              (r₁ / 4) * ((1 / 2) * (A * (r₁ / 4) ^ k * (1 / 2))) := by
            simp
            ring
          rw [← hconst]
          refine intervalIntegral.integral_mono_on hq2 intervalIntegrable_const hi2 ?_
          intro s ⟨hs_lo, hs_hi⟩
          have hs0 : 0 ≤ s := hq1.trans hs_lo
          dsimp [bump]
          rw [max_eq_right hs0]
          have h_ell : 1 / 2 ≤ LandauLiuMinda.ell s :=
            LandauLiuMinda.half_le_ell hs0 (by linarith)
          have h_pow : (r₁ / 4) ^ k ≤ s ^ k := pow_le_pow_left₀ hq1 hs_lo k
          have h_lin : 1 / 2 ≤ max 0 (1 - s / r₁) := by
            refine le_max_of_le_right ?_
            have : s / r₁ ≤ 1 / 2 := by
              rw [div_le_iff₀ hr₁0]
              linarith
            linarith
          have hfac_ge : A * (r₁ / 4) ^ k * (1 / 2) ≤
              A * s ^ k * max 0 (1 - s / r₁) := by
            have h1 : A * (r₁ / 4) ^ k ≤ A * s ^ k :=
              mul_le_mul_of_nonneg_left h_pow hA.le
            exact mul_le_mul h1 h_lin (by norm_num) (mul_nonneg hA.le (pow_nonneg hs0 k))
          exact mul_le_mul h_ell hfac_ge (by positivity) (LandauLiuMinda.ell_pos (by linarith)).le
        have hmid_eq : (r₁ / 4) * ((1 / 2) * (A * (r₁ / 4) ^ k * (1 / 2))) =
            A * r₁ ^ (k + 1) / (4 : ℝ) ^ (k + 2) := by
          rw [div_pow, pow_succ r₁ k, pow_add (4 : ℝ) k 2]
          ring
        linarith
      linarith
    have hr₁_lt1 : r₁ < 1 := by linarith
    have hlim_sum : Tendsto (fun r : ℝ =>
        LandauLiuMinda.E_fn r + A * r₁ ^ (k + 1) / (4 : ℝ) ^ (k + 2))
        (𝓝[<] (1 : ℝ)) (𝓝 (1 / 2 + A * r₁ ^ (k + 1) / (4 : ℝ) ^ (k + 2))) :=
      LandauLiuMinda.tendsto_E_fn.add tendsto_const_nhds
    have hbound : 1 / 2 + A * r₁ ^ (k + 1) / (4 : ℝ) ^ (k + 2) ≤ T₀ :=
      le_of_tendsto hlim_sum (Filter.mem_of_superset (Ioo_mem_nhdsLT hr₁_lt1) hE_le)
    linarith

private theorem re_h_sub_log_ell {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (ball 0 1))
    (hh0 : h 0 = 0) (hh1 : deriv h 0 = 0)
    (hre : ∀ z ∈ ball (0 : ℂ) 1, (h z).re ≤ -Real.log (1 - ‖z‖ ^ 2))
    (hc2_im : ((cauchyPowerSeries h 0 (1 / 2)).coeff 2).im = 0)
    {z : ℂ} (hz0 : 0 < ‖z‖) (hz4 : ‖z‖ ≤ 1 / 4) :
    let a := ((cauchyPowerSeries h 0 (1 / 2)).coeff 2).re
    let p := ((cauchyPowerSeries h 0 (1 / 2)).coeff 3).re
    let v := ((cauchyPowerSeries h 0 (1 / 2)).coeff 3).im
    let w := z / (‖z‖ : ℂ)
    let y := w.im
    (1 + a * (1 - 2 * y ^ 2)) * ‖z‖ ^ 2 +
      (4 / 3 + p * (w ^ 3).re - v * (3 * y - 4 * y ^ 3)) * ‖z‖ ^ 3 - 192 * ‖z‖ ^ 4 ≤
      (h z).re - Real.log (LandauLiuMinda.ell ‖z‖) := by
  dsimp only
  set c2 := (cauchyPowerSeries h 0 (1 / 2)).coeff 2
  set c3 := (cauchyPowerSeries h 0 (1 / 2)).coeff 3
  set a := c2.re
  set p := c3.re
  set v := c3.im
  set r := ‖z‖
  set w := z / (r : ℂ)
  set y := w.im
  have hc2 : c2 = (a : ℂ) := Complex.ext rfl hc2_im
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz0.ne'
  have hzw : z = (r : ℂ) * w := by
    dsimp [w]
    exact (mul_div_cancel₀ z hrC).symm
  have hw_norm : ‖w‖ = 1 := by
    dsimp [w]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz0, div_self hz0.ne']
  have hxy : w.re ^ 2 + y ^ 2 = 1 := by
    have h1 := congrArg (fun t : ℝ => t ^ 2) hw_norm
    rw [Complex.sq_norm, Complex.normSq_apply] at h1
    dsimp [y]
    nlinarith
  have hw2_re : (w ^ 2).re = 1 - 2 * y ^ 2 := by
    simp only [sq, Complex.mul_re]
    dsimp [y]
    linarith
  have hw3_im : (w ^ 3).im = 3 * y - 4 * y ^ 3 := by
    have hpow : w ^ 3 = w * (w * w) := by ring
    have hre2 : w.re ^ 2 = 1 - y ^ 2 := by linarith
    rw [hpow]
    simp only [Complex.mul_im, Complex.mul_re]
    dsimp [y]
    calc
      w.re * (w.re * w.im + w.im * w.re) + w.im * (w.re * w.re - w.im * w.im)
        = 3 * w.re ^ 2 * w.im - w.im ^ 3 := by ring
      _ = 3 * (1 - w.im ^ 2) * w.im - w.im ^ 3 := by rw [hre2]
      _ = 3 * w.im - 4 * w.im ^ 3 := by ring
  have hmain_re : (c2 * z ^ 2 + c3 * z ^ 3).re =
      a * (1 - 2 * y ^ 2) * r ^ 2 + (p * (w ^ 3).re - v * (3 * y - 4 * y ^ 3)) * r ^ 3 := by
    rw [hzw, mul_pow, mul_pow, hc2]
    have h1 : ((a : ℂ) * ((r : ℂ) ^ 2 * w ^ 2)).re = a * r ^ 2 * (w ^ 2).re := by
      rw [← Complex.ofReal_pow, ← mul_assoc, ← Complex.ofReal_mul]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have h2 : (c3 * ((r : ℂ) ^ 3 * w ^ 3)).re = r ^ 3 * (p * (w ^ 3).re - v * (w ^ 3).im) := by
      rw [← Complex.ofReal_pow, show c3 * ((r ^ 3 : ℝ) * w ^ 3) =
        ((r ^ 3 : ℝ) : ℂ) * (c3 * w ^ 3) by ring]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rfl
    rw [Complex.add_re, h1, h2, hw2_re, hw3_im]
    ring
  have ht := LandauLog.tail_bound_192 hh hh0 hh1 hre hz4
  have hd := (neg_le_abs _).trans (Complex.abs_re_le_norm _) |>.trans ht
  rw [Complex.sub_re, hmain_re] at hd
  have hlog := LandauLiuMinda.log_ell_le (norm_nonneg z) (by linarith)
  linarith

private theorem cubic_term_abs_le {c3 w : ℂ} (hw : ‖w‖ = 1) (hc3 : ‖c3‖ ≤ 48) :
    |c3.re * (w ^ 3).re - c3.im * (3 * w.im - 4 * w.im ^ 3)| ≤ 48 := by
  have hxy : w.re ^ 2 + w.im ^ 2 = 1 := by
    have h1 := congrArg (fun t : ℝ => t ^ 2) hw
    rw [Complex.sq_norm, Complex.normSq_apply] at h1
    nlinarith
  have hw3_im : (w ^ 3).im = 3 * w.im - 4 * w.im ^ 3 := by
    have hpow : w ^ 3 = w * (w * w) := by ring
    have hre2 : w.re ^ 2 = 1 - w.im ^ 2 := by linarith
    rw [hpow]
    simp only [Complex.mul_im, Complex.mul_re]
    calc
      w.re * (w.re * w.im + w.im * w.re) + w.im * (w.re * w.re - w.im * w.im)
        = 3 * w.re ^ 2 * w.im - w.im ^ 3 := by ring
      _ = 3 * (1 - w.im ^ 2) * w.im - w.im ^ 3 := by rw [hre2]
      _ = 3 * w.im - 4 * w.im ^ 3 := by ring
  have hre_eq : c3.re * (w ^ 3).re - c3.im * (3 * w.im - 4 * w.im ^ 3) =
      (c3 * w ^ 3).re := by
    rw [← hw3_im]
    simp [Complex.mul_re]
  rw [hre_eq]
  calc
    |(c3 * w ^ 3).re| ≤ ‖c3 * w ^ 3‖ := Complex.abs_re_le_norm _
    _ = ‖c3‖ := by rw [norm_mul, norm_pow, hw, one_pow, mul_one]
    _ ≤ 48 := hc3

private theorem case1_disk_cover {G h : ℂ → ℂ}
    (hgα : DifferentiableOn ℂ G (ball 0 1)) (hgα0 : G 0 = 0) (hgα1 : deriv G 0 = 1)
    (hgαne : ∀ z ∈ ball (0 : ℂ) 1, deriv G z ≠ 0)
    (hWα : ∀ z ∈ ball (0 : ℂ) 1, (1 - ‖z‖ ^ 2) * ‖deriv G z‖ ≤ 1)
    (hh : DifferentiableOn ℂ h (ball 0 1)) (hh0 : h 0 = 0) (hh1 : deriv h 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) 1, Complex.exp (h z) = deriv G z)
    (hre : ∀ z ∈ ball (0 : ℂ) 1, (h z).re ≤ -Real.log (1 - ‖z‖ ^ 2))
    (hc2_im : ((cauchyPowerSeries h 0 (1 / 2)).coeff 2).im = 0)
    (hc2_re : 0 ≤ ((cauchyPowerSeries h 0 (1 / 2)).coeff 2).re)
    (hc3_norm : ‖(cauchyPowerSeries h 0 (1 / 2)).coeff 3‖ ≤ 48)
    (ha_case : ((cauchyPowerSeries h 0 (1 / 2)).coeff 2).re ≤ 1 - 1 / (10 : ℝ) ^ 8) :
    ∃ c, ball c (1 / 2 + 1 / (10 : ℝ) ^ 44) ⊆ G '' ball 0 1 := by
  set a := ((cauchyPowerSeries h 0 (1 / 2)).coeff 2).re
  set p := ((cauchyPowerSeries h 0 (1 / 2)).coeff 3).re
  set v := ((cauchyPowerSeries h 0 (1 / 2)).coeff 3).im
  refine ⟨0, ?_⟩
  intro w hw
  rcases eq_or_ne w 0 with rfl | hwne
  · exact ⟨0, mem_ball_self zero_lt_one, hgα0⟩
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hwne
  let u := w / (‖w‖ : ℂ)
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hwn, div_self hwn.ne']
  have hwu : (‖w‖ : ℂ) * u = w := mul_div_cancel₀ w (Complex.ofReal_ne_zero.mpr hwn.ne')
  rw [← hwu]
  refine excess_ray_bound hgα hgα0 hgα1 hgαne hWα hh hh0 hexp hu
    (A := 5 / (10 : ℝ) ^ 9) (r₁ := 1 / (10 : ℝ) ^ 11) (k := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hwn ?_
  · intro z _ t _ _ hz0 hzr₁
    have hre_lb := re_h_sub_log_ell hh hh0 hh1 hre hc2_im hz0 (by linarith)
    set wz := z / (‖z‖ : ℂ)
    have hwz_norm : ‖wz‖ = 1 := by
      dsimp [wz]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz0, div_self hz0.ne']
    have hy2 : wz.im ^ 2 ≤ 1 := by
      have := Complex.abs_im_le_norm wz
      rw [hwz_norm, abs_le] at this
      nlinarith
    have hquad : 1 / (10 : ℝ) ^ 8 ≤ 1 + a * (1 - 2 * wz.im ^ 2) := by
      nlinarith [hc2_re]
    have hcub_abs := cubic_term_abs_le hwz_norm hc3_norm
    have hcub : -48 ≤ 4 / 3 + p * (wz ^ 3).re - v * (3 * wz.im - 4 * wz.im ^ 3) := by
      linarith [(neg_le_abs _).trans hcub_abs]
    have hq_mul : (1 / (10 : ℝ) ^ 8) * ‖z‖ ^ 2 ≤ (1 + a * (1 - 2 * wz.im ^ 2)) * ‖z‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hquad (sq_nonneg _)
    have hc_mul : (-48 : ℝ) * ‖z‖ ^ 3 ≤
        (4 / 3 + p * (wz ^ 3).re - v * (3 * wz.im - 4 * wz.im ^ 3)) * ‖z‖ ^ 3 :=
      mul_le_mul_of_nonneg_right hcub (pow_nonneg hz0.le 3)
    have h1 : (1 / (10 : ℝ) ^ 8) * ‖z‖ ^ 2 - 48 * ‖z‖ ^ 3 - 192 * ‖z‖ ^ 4 ≤
        (h z).re - Real.log (LandauLiuMinda.ell ‖z‖) := by linarith
    have h3 : 48 * ‖z‖ + 192 * ‖z‖ ^ 2 ≤ 5 / (10 : ℝ) ^ 9 := by
      have hz2 : ‖z‖ ^ 2 ≤ (1 / (10 : ℝ) ^ 11) ^ 2 := by nlinarith [hz0, hzr₁]
      linarith
    have h3m : (48 * ‖z‖ + 192 * ‖z‖ ^ 2) * ‖z‖ ^ 2 ≤ (5 / (10 : ℝ) ^ 9) * ‖z‖ ^ 2 :=
      mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
    have h3eq : (48 * ‖z‖ + 192 * ‖z‖ ^ 2) * ‖z‖ ^ 2 = 48 * ‖z‖ ^ 3 + 192 * ‖z‖ ^ 4 := by ring
    linarith
  · have hwlt : ‖w‖ < 1 / 2 + 1 / (10 : ℝ) ^ 44 := mem_ball_zero_iff.mp hw
    have hnum : (1 : ℝ) / (10 : ℝ) ^ 44 ≤
        (5 / (10 : ℝ) ^ 9) * (1 / (10 : ℝ) ^ 11) ^ (2 + 1) / (4 : ℝ) ^ (2 + 2) := by
      norm_num
    linarith

private theorem case2a_ray {G h : ℂ → ℂ}
    (hgα : DifferentiableOn ℂ G (ball 0 1)) (hgα0 : G 0 = 0) (hgα1 : deriv G 0 = 1)
    (hgαne : ∀ z ∈ ball (0 : ℂ) 1, deriv G z ≠ 0)
    (hWα : ∀ z ∈ ball (0 : ℂ) 1, (1 - ‖z‖ ^ 2) * ‖deriv G z‖ ≤ 1)
    (hh : DifferentiableOn ℂ h (ball 0 1)) (hh0 : h 0 = 0) (hh1 : deriv h 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) 1, Complex.exp (h z) = deriv G z)
    (hre : ∀ z ∈ ball (0 : ℂ) 1, (h z).re ≤ -Real.log (1 - ‖z‖ ^ 2))
    (hc2_im : ((cauchyPowerSeries h 0 (1 / 2)).coeff 2).im = 0)
    (hc2_norm : ‖(cauchyPowerSeries h 0 (1 / 2)).coeff 2‖ ≤ 1)
    (hc3_norm : ‖(cauchyPowerSeries h 0 (1 / 2)).coeff 3‖ ≤ 48)
    (ha_le : ((cauchyPowerSeries h 0 (1 / 2)).coeff 2).re ≤ 1)
    (ha_gt : 1 - 1 / (10 : ℝ) ^ 8 < ((cauchyPowerSeries h 0 (1 / 2)).coeff 2).re)
    {u : ℂ} (hu : ‖u‖ = 1) (huim : |u.im| ≤ 19 / 20)
    {t : ℝ} (ht0 : 0 < t) (htlt : t < 1 / 2 + 1 / (10 : ℝ) ^ 15) :
    (t : ℂ) * u ∈ G '' ball 0 1 := by
  set a := ((cauchyPowerSeries h 0 (1 / 2)).coeff 2).re
  set p := ((cauchyPowerSeries h 0 (1 / 2)).coeff 3).re
  set v := ((cauchyPowerSeries h 0 (1 / 2)).coeff 3).im
  refine excess_ray_bound hgα hgα0 hgα1 hgαne hWα hh hh0 hexp hu
    (A := 1 / 20) (r₁ := 1 / 500) (k := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ ht0 ?_
  · intro z _ s hs0 hgz hz0 hzr₁
    have him_cl := LandauAngle.im_unit_close hgα hgα0 hgα1 hWα hh hh0 hexp hc2_norm
      hz0 hzr₁.le hu hs0 hgz
    set wz := z / (‖z‖ : ℂ)
    have hwz_norm : ‖wz‖ = 1 := by
      dsimp [wz]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz0, div_self hz0.ne']
    have hy_abs : |wz.im| ≤ 24 / 25 := by
      rw [abs_le] at huim ⊢
      rw [abs_lt] at him_cl
      constructor <;> linarith
    have hy2 : wz.im ^ 2 ≤ (24 / 25 : ℝ) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hy_abs 2
    have hquad : (3 / 20 : ℝ) ≤ 1 + a * (1 - 2 * wz.im ^ 2) := by
      have : 1 + a * (1 - 2 * wz.im ^ 2) = (1 - a) + 2 * a * (1 - wz.im ^ 2) := by ring
      rw [this]
      nlinarith
    have hcub_abs := cubic_term_abs_le hwz_norm hc3_norm
    have hre_lb := re_h_sub_log_ell hh hh0 hh1 hre hc2_im hz0 (by linarith)
    have hcub : -48 ≤ 4 / 3 + p * (wz ^ 3).re - v * (3 * wz.im - 4 * wz.im ^ 3) := by
      linarith [(neg_le_abs _).trans hcub_abs]
    have hq_mul : (3 / 20 : ℝ) * ‖z‖ ^ 2 ≤ (1 + a * (1 - 2 * wz.im ^ 2)) * ‖z‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hquad (sq_nonneg _)
    have hc_mul : (-48 : ℝ) * ‖z‖ ^ 3 ≤
        (4 / 3 + p * (wz ^ 3).re - v * (3 * wz.im - 4 * wz.im ^ 3)) * ‖z‖ ^ 3 :=
      mul_le_mul_of_nonneg_right hcub (pow_nonneg hz0.le 3)
    have h1 : (3 / 20 : ℝ) * ‖z‖ ^ 2 - 48 * ‖z‖ ^ 3 - 192 * ‖z‖ ^ 4 ≤
        (h z).re - Real.log (LandauLiuMinda.ell ‖z‖) := by linarith
    have h3 : 48 * ‖z‖ + 192 * ‖z‖ ^ 2 ≤ 1 / 10 := by
      have hz2 : ‖z‖ ^ 2 ≤ (1 / 500 : ℝ) ^ 2 := by nlinarith [hz0, hzr₁]
      linarith
    have h3m : (48 * ‖z‖ + 192 * ‖z‖ ^ 2) * ‖z‖ ^ 2 ≤ (1 / 10 : ℝ) * ‖z‖ ^ 2 :=
      mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
    have h3eq : (48 * ‖z‖ + 192 * ‖z‖ ^ 2) * ‖z‖ ^ 2 = 48 * ‖z‖ ^ 3 + 192 * ‖z‖ ^ 4 := by ring
    linarith
  · have hnum : (1 : ℝ) / (10 : ℝ) ^ 15 ≤
        (1 / 20 : ℝ) * (1 / 500 : ℝ) ^ (2 + 1) / (4 : ℝ) ^ (2 + 2) := by
      norm_num
    linarith

private theorem case2b_ray {G h : ℂ → ℂ}
    (hgα : DifferentiableOn ℂ G (ball 0 1)) (hgα0 : G 0 = 0) (hgα1 : deriv G 0 = 1)
    (hgαne : ∀ z ∈ ball (0 : ℂ) 1, deriv G z ≠ 0)
    (hWα : ∀ z ∈ ball (0 : ℂ) 1, (1 - ‖z‖ ^ 2) * ‖deriv G z‖ ≤ 1)
    (hh : DifferentiableOn ℂ h (ball 0 1)) (hh0 : h 0 = 0) (hh1 : deriv h 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) 1, Complex.exp (h z) = deriv G z)
    (hre : ∀ z ∈ ball (0 : ℂ) 1, (h z).re ≤ -Real.log (1 - ‖z‖ ^ 2))
    (hc2_im : ((cauchyPowerSeries h 0 (1 / 2)).coeff 2).im = 0)
    (hc2_re : 0 ≤ ((cauchyPowerSeries h 0 (1 / 2)).coeff 2).re)
    (hc2_norm : ‖(cauchyPowerSeries h 0 (1 / 2)).coeff 2‖ ≤ 1)
    (hc3_im : 0 ≤ ((cauchyPowerSeries h 0 (1 / 2)).coeff 3).im)
    (ha_le : ((cauchyPowerSeries h 0 (1 / 2)).coeff 2).re ≤ 1)
    (hp_le : |((cauchyPowerSeries h 0 (1 / 2)).coeff 3).re| ≤ 1 / 50)
    {u : ℂ} (hu : ‖u‖ = 1) (huim : 19 / 20 < u.im)
    {t : ℝ} (ht0 : 0 < t) (htlt : t < 1 / 2 + 1 / (10 : ℝ) ^ 15) :
    (t : ℂ) * u ∈ G '' ball 0 1 := by
  set a := ((cauchyPowerSeries h 0 (1 / 2)).coeff 2).re
  set p := ((cauchyPowerSeries h 0 (1 / 2)).coeff 3).re
  set v := ((cauchyPowerSeries h 0 (1 / 2)).coeff 3).im
  refine excess_ray_bound hgα hgα0 hgα1 hgαne hWα hh hh0 hexp hu
    (A := 1 / 2) (r₁ := 1 / 500) (k := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ ht0 ?_
  · intro z _ s hs0 hgz hz0 hzr₁
    have him_cl := LandauAngle.im_unit_close hgα hgα0 hgα1 hWα hh hh0 hexp hc2_norm
      hz0 hzr₁.le hu hs0 hgz
    set wz := z / (‖z‖ : ℂ)
    have hwz_norm : ‖wz‖ = 1 := by
      dsimp [wz]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz0, div_self hz0.ne']
    have hy_gt : 47 / 50 < wz.im := by
      rw [abs_lt] at him_cl
      linarith
    have hsin3_neg : 3 * wz.im - 4 * wz.im ^ 3 ≤ 0 := by
      have : 3 * wz.im - 4 * wz.im ^ 3 = wz.im * (3 - 4 * wz.im ^ 2) := by ring
      rw [this]
      nlinarith
    have hw3_re_abs : |(wz ^ 3).re| ≤ 1 := by
      calc
        |(wz ^ 3).re| ≤ ‖wz ^ 3‖ := Complex.abs_re_le_norm _
        _ = 1 := by rw [norm_pow, hwz_norm, one_pow]
    have hp_term : -(1 / 50 : ℝ) ≤ p * (wz ^ 3).re := by
      have h1 : |p * (wz ^ 3).re| ≤ 1 / 50 := by
        rw [abs_mul]
        nlinarith [abs_nonneg p, abs_nonneg (wz ^ 3).re]
      exact (neg_le_abs _).trans h1 |> fun h => by linarith
    have hcub : 1 ≤ 4 / 3 + p * (wz ^ 3).re - v * (3 * wz.im - 4 * wz.im ^ 3) := by
      have hv_term : 0 ≤ -(v * (3 * wz.im - 4 * wz.im ^ 3)) := by
        nlinarith [hc3_im]
      linarith
    have hy2 : wz.im ^ 2 ≤ 1 := by
      have := Complex.abs_im_le_norm wz
      rw [hwz_norm, abs_le] at this
      nlinarith
    have hquad : 0 ≤ 1 + a * (1 - 2 * wz.im ^ 2) := by
      nlinarith [hc2_re, ha_le]
    have hre_lb := re_h_sub_log_ell hh hh0 hh1 hre hc2_im hz0 (by linarith)
    have hq_mul : 0 ≤ (1 + a * (1 - 2 * wz.im ^ 2)) * ‖z‖ ^ 2 :=
      mul_nonneg hquad (sq_nonneg _)
    have hc_mul : 1 * ‖z‖ ^ 3 ≤
        (4 / 3 + p * (wz ^ 3).re - v * (3 * wz.im - 4 * wz.im ^ 3)) * ‖z‖ ^ 3 :=
      mul_le_mul_of_nonneg_right hcub (pow_nonneg hz0.le 3)
    have h1 : 1 * ‖z‖ ^ 3 - 192 * ‖z‖ ^ 4 ≤
        (h z).re - Real.log (LandauLiuMinda.ell ‖z‖) := by linarith
    have hrem : 192 * ‖z‖ ^ 4 ≤ (1 / 2 : ℝ) * ‖z‖ ^ 3 := by
      have h3 : 192 * ‖z‖ ≤ 1 / 2 := by linarith
      have h3m := mul_le_mul_of_nonneg_right h3 (pow_nonneg hz0.le 3)
      have h3eq : (192 * ‖z‖) * ‖z‖ ^ 3 = 192 * ‖z‖ ^ 4 := by ring
      linarith
    linarith
  · have hnum : (1 : ℝ) / (10 : ℝ) ^ 15 ≤
        (1 / 2 : ℝ) * (1 / 500 : ℝ) ^ (3 + 1) / (4 : ℝ) ^ (3 + 2) := by
      norm_num
    linarith

private theorem normalized_rotated_disk_cover {G h : ℂ → ℂ}
    (hgα : DifferentiableOn ℂ G (ball 0 1)) (hgα0 : G 0 = 0) (hgα1 : deriv G 0 = 1)
    (hgαne : ∀ z ∈ ball (0 : ℂ) 1, deriv G z ≠ 0)
    (hWα : ∀ z ∈ ball (0 : ℂ) 1, (1 - ‖z‖ ^ 2) * ‖deriv G z‖ ≤ 1)
    (hh : DifferentiableOn ℂ h (ball 0 1)) (hh0 : h 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) 1, Complex.exp (h z) = deriv G z)
    (hc2_im : ((cauchyPowerSeries h 0 (1 / 2)).coeff 2).im = 0)
    (hc2_re : 0 ≤ ((cauchyPowerSeries h 0 (1 / 2)).coeff 2).re)
    (hc3_im : 0 ≤ ((cauchyPowerSeries h 0 (1 / 2)).coeff 3).im) :
    ∃ c, ball c (1 / 2 + 1 / (10 : ℝ) ^ 44) ⊆ G '' ball 0 1 := by
  have hh1 := LandauLog.deriv_log_zero hgα hgα1 hWα hh hh0 hexp
  have hre : ∀ z ∈ ball (0 : ℂ) 1, (h z).re ≤ -Real.log (1 - ‖z‖ ^ 2) :=
    fun z hz => LandauLog.re_log_le hWα hexp hz
  have ha_le : ((cauchyPowerSeries h 0 (1 / 2)).coeff 2).re ≤ 1 :=
    LandauLog.a_le_one hh hh0 hh1 hre hc2_im
  have hc2_norm : ‖(cauchyPowerSeries h 0 (1 / 2)).coeff 2‖ ≤ 1 := by
    have hc2_eq : (cauchyPowerSeries h 0 (1 / 2)).coeff 2 =
        (((cauchyPowerSeries h 0 (1 / 2)).coeff 2).re : ℂ) := Complex.ext rfl hc2_im
    rw [hc2_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc2_re]
    exact ha_le
  have hc3_norm : ‖(cauchyPowerSeries h 0 (1 / 2)).coeff 3‖ ≤ 48 := by
    have := LandauLog.coeff_bound_six hh hh0 hre 3
    norm_num at this
    exact this
  by_cases ha_case : ((cauchyPowerSeries h 0 (1 / 2)).coeff 2).re ≤ 1 - 1 / (10 : ℝ) ^ 8
  · exact case1_disk_cover hgα hgα0 hgα1 hgαne hWα hh hh0 hh1 hexp hre
      hc2_im hc2_re hc3_norm ha_case
  · push Not at ha_case
    have hp_le : |((cauchyPowerSeries h 0 (1 / 2)).coeff 3).re| ≤ 1 / 50 :=
      LandauLog.abs_p_le_of_a_close hh hh0 hh1 hre hc2_im ha_case
    let ε : ℝ := 1 / (10 : ℝ) ^ 16
    let c : ℂ := (ε : ℂ) * Complex.I
    refine ⟨c, ?_⟩
    intro w hw
    have hwR : ‖w - c‖ < 1 / 2 + ε / 2 := by
      have h1 : ‖w - c‖ < 1 / 2 + 1 / (10 : ℝ) ^ 44 := mem_ball_iff_norm.mp hw
      have h2 : (1 : ℝ) / (10 : ℝ) ^ 44 ≤ ε / 2 := by norm_num [ε]
      linarith
    rcases eq_or_ne w 0 with rfl | hwne
    · exact ⟨0, mem_ball_self zero_lt_one, hgα0⟩
    have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hwne
    let u := w / (‖w‖ : ℂ)
    have hu : ‖u‖ = 1 := by
      dsimp [u]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hwn, div_self hwn.ne']
    have hwu : (‖w‖ : ℂ) * u = w := mul_div_cancel₀ w (Complex.ofReal_ne_zero.mpr hwn.ne')
    rw [← hwu]
    by_cases him : -(19 / 20 : ℝ) ≤ u.im
    · have ht_lt : ‖w‖ < 1 / 2 + 1 / (10 : ℝ) ^ 15 := by
        have hc_norm : ‖c‖ = ε := by
          dsimp [c]
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by norm_num [ε])]
        have htri : ‖w‖ ≤ ‖w - c‖ + ‖c‖ := by
          simpa using norm_add_le (w - c) c
        have hnum : ε / 2 + ε < 1 / (10 : ℝ) ^ 15 := by norm_num [ε]
        rw [hc_norm] at htri
        calc
          ‖w‖ ≤ ‖w - c‖ + ε := htri
          _ < (1 / 2 + ε / 2) + ε := add_lt_add_of_lt_of_le hwR le_rfl
          _ = 1 / 2 + (ε / 2 + ε) := by ring
          _ < 1 / 2 + 1 / (10 : ℝ) ^ 15 := add_lt_add_of_le_of_lt le_rfl hnum
      by_cases him2 : u.im ≤ 19 / 20
      · exact case2a_ray hgα hgα0 hgα1 hgαne hWα hh hh0 hh1 hexp hre
          hc2_im hc2_norm hc3_norm ha_le ha_case hu (abs_le.mpr ⟨him, him2⟩) hwn ht_lt
      · push Not at him2
        exact case2b_ray hgα hgα0 hgα1 hgαne hWα hh hh0 hh1 hexp hre
          hc2_im hc2_re hc2_norm hc3_im ha_le hp_le hu him2 hwn ht_lt
    · push Not at him
      have ht_half : ‖w‖ < 1 / 2 := by
        have hwim : w.im = ‖w‖ * u.im := by
          have := congrArg Complex.im hwu.symm
          simpa [Complex.mul_im] using this
        have hsq : ‖w - c‖ ^ 2 = ‖w‖ ^ 2 + ε ^ 2 - 2 * ‖w‖ * ε * u.im := by
          have h1 : ‖w - c‖ ^ 2 = w.re ^ 2 + (w.im - ε) ^ 2 := by
            rw [Complex.sq_norm, Complex.normSq_apply]
            simp [c]
            ring
          have h2 : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
            rw [Complex.sq_norm, Complex.normSq_apply]
            ring
          rw [h1, h2, hwim]
          ring
        have hsq_lt : ‖w - c‖ ^ 2 < (1 / 2 + ε / 2) ^ 2 :=
          pow_lt_pow_left₀ hwR (norm_nonneg _) two_ne_zero
        have hε_pos : 0 < ε := by norm_num [ε]
        by_contra! hge
        have hpos : 0 < ‖w‖ * ε := mul_pos hwn hε_pos
        have h1 : (19 / 10 : ℝ) * (‖w‖ * ε) < -(2 * ‖w‖ * ε * u.im) := by
          have : -(2 * ‖w‖ * ε * u.im) = (-2 * u.im) * (‖w‖ * ε) := by ring
          rw [this]
          nlinarith
        have h2 : (1 / 4 : ℝ) ≤ ‖w‖ ^ 2 := by nlinarith
        have h3 : (1 / 2 : ℝ) * ε ≤ ‖w‖ * ε := mul_le_mul_of_nonneg_right hge hε_pos.le
        have hexp_R : (1 / 2 + ε / 2) ^ 2 = 1 / 4 + ε / 2 + ε ^ 2 / 4 := by ring
        rw [hexp_R] at hsq_lt
        have h4 : (19 / 20 : ℝ) * ε < -(2 * ‖w‖ * ε * u.im) := by
          have h4a : (19 / 20 : ℝ) * ε ≤ 19 / 10 * (‖w‖ * ε) := by
            have := mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ 19 / 10)
            have heq : (19 / 10 : ℝ) * ((1 / 2 : ℝ) * ε) = (19 / 20 : ℝ) * ε := by ring
            rwa [heq] at this
          exact h4a.trans_lt h1
        have hsq_eq : ‖w - c‖ ^ 2 = ‖w‖ ^ 2 + ε ^ 2 + -(2 * ‖w‖ * ε * u.im) := by
          rw [hsq]; ring
        have hstep1 : 1 / 4 + ε ^ 2 + (19 / 20 : ℝ) * ε < ‖w - c‖ ^ 2 := by
          rw [hsq_eq]
          exact add_lt_add_of_le_of_lt (add_le_add h2 le_rfl) h4
        have hstep2 : 1 / 4 + ε / 2 + ε ^ 2 / 4 < 1 / 4 + ε ^ 2 + (19 / 20 : ℝ) * ε := by
          have hsub : (1 / 4 + ε ^ 2 + (19 / 20 : ℝ) * ε) - (1 / 4 + ε / 2 + ε ^ 2 / 4) =
              (3 / 4 : ℝ) * ε ^ 2 + (9 / 20 : ℝ) * ε := by ring
          have hpos2 : (0 : ℝ) < (3 / 4 : ℝ) * ε ^ 2 + (9 / 20 : ℝ) * ε :=
            add_pos (mul_pos (by norm_num) (sq_pos_of_pos hε_pos))
              (mul_pos (by norm_num) hε_pos)
          exact sub_pos.mp (hsub.symm ▸ hpos2)
        exact lt_irrefl (‖w - c‖ ^ 2) (hsq_lt.trans (hstep2.trans hstep1))
      exact baseline_ray_bound hgα hgα0 hgα1 hgαne hWα hh hh0 hexp hu hwn ht_half

theorem normalized_disk_cover {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball 0 1)) (hg0 : g 0 = 0) (hg1 : deriv g 0 = 1)
    (hgne : ∀ z ∈ ball (0 : ℂ) 1, deriv g z ≠ 0)
    (hW : ∀ z ∈ ball (0 : ℂ) 1, (1 - ‖z‖ ^ 2) * ‖deriv g z‖ ≤ 1) :
    ∃ c, ball c (1 / 2 + 1 / (10 : ℝ) ^ 44) ⊆ g '' ball 0 1 := by
  obtain ⟨h₀, hh₀, hh₀0, hexp₀⟩ := LandauLog.exists_holo_log hg hg1 hgne
  obtain ⟨α, hα, hgα, hgα0, hgα1, hgαne, hWα, hh, hh0, hexp, hc2_im, hc2_re, hc3_im⟩ :=
    LandauLog.rotation_normalization hg hg0 hg1 hgne hW hh₀ hh₀0 hexp₀
  obtain ⟨c, hc⟩ := normalized_rotated_disk_cover hgα hgα0 hgα1 hgαne hWα hh hh0 hexp
    hc2_im hc2_re hc3_im
  refine ⟨α * c, ?_⟩
  intro w hw
  have hαne : α ≠ 0 := norm_pos_iff.mp (by linarith)
  have hw' : α⁻¹ * w ∈ ball c (1 / 2 + 1 / (10 : ℝ) ^ 44) := by
    rw [mem_ball_iff_norm] at hw ⊢
    have heq : α⁻¹ * w - c = α⁻¹ * (w - α * c) := by
      field_simp [hαne]
    rw [heq, norm_mul, norm_inv, hα, inv_one, one_mul]
    exact hw
  obtain ⟨z, hz, heq⟩ := hc hw'
  refine ⟨α * z, ?_, ?_⟩
  · rw [mem_ball_zero_iff] at hz ⊢
    simpa [norm_mul, hα] using hz
  · exact mul_left_cancel₀ (inv_ne_zero hαne) heq

end LandauMain

theorem OMA.solution : OMA.R_Bloch_landauConstant_lower_bound_R1.H2 := by
  have hB : (0 : ℝ) < 0.5 + 10 ^ (-335 : ℤ) := by positivity
  have hBR : (0.5 : ℝ) + 10 ^ (-335 : ℤ) < 1 / 2 + 1 / (10 : ℝ) ^ 44 := by
    have hpow : (10 : ℝ) ^ (-335 : ℤ) < (10 : ℝ) ^ (-44 : ℤ) :=
      zpow_lt_zpow_right₀ (by norm_num) (by norm_num)
    have h44 : (10 : ℝ) ^ (-44 : ℤ) = 1 / (10 : ℝ) ^ 44 := by norm_num
    have hhalf : (0.5 : ℝ) = 1 / 2 := by norm_num
    rw [hhalf, ← h44]
    exact add_lt_add_of_le_of_lt le_rfl hpow
  exact LandauNorm.normalized_reduction hB hBR
    (fun g hg hg0 hg1 hgne hW => LandauMain.normalized_disk_cover hg hg0 hg1 hgne hW)
