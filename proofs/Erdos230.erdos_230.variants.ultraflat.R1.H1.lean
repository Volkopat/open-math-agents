import OMAReductions.R_Erdos230_erdos_230_variants_ultraflat_R1
import Mathlib

/-! # Disk-valued approximately flat polynomials via smooth chirps

We prove `OMA.R_Erdos230_erdos_230_variants_ultraflat_R1.H1` by constructing,
for every sufficiently large `n`, a `2*pi`-periodic unimodular function
`f(t) = exp(I * phi(t))` whose phase second derivative `phi''(t) = A * g(t)`
is continuous, piecewise linear, equal to `A` on the bulk interval
`[eta, 2*pi - eta - delta]`, boosted to `128 * A` near the endpoints of
`[delta, 2*pi - 2*delta]`, and rapidly returning on `[2*pi - delta, 2*pi]`.

Stationary-phase and van der Corput estimates yield a uniform upper bound
`||fourierCoeff F k|| <= D_n = (1 / sqrt n) * (1 + O(n^(-1/20)))` for all `k`,
while two integrations by parts give a tail bound
`sum_{k notin [-M, n - 1 - M]} ||fourierCoeff F k|| = O(n^(-1/10))`.
Parseval identity on `|f| = 1` then automatically controls the squared-modulus
deficit `sum (1 - ||c n k||^2) = O(n^(19/20)) = o(n / log n)`.
-/

namespace Erdos230UltraflatH1

open Finset Real Complex Filter Topology MeasureTheory
open scoped Real

/- ## Section 1: Elementary Fresnel integral upper bound -/

private lemma norm_exp_I_mul_sub_exp_I_mul_le (a b : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖ ≤ |a - b| := by
  have h1 : Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ)) =
      (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) * Complex.exp (Complex.I * (b : ℂ)) := by
    rw [sub_mul, ← Complex.exp_add, one_mul]
    congr 1
    push_cast
    ring
  rw [h1, norm_mul]
  have h2 : ‖Complex.exp (Complex.I * (b : ℂ))‖ = 1 := by
    rw [mul_comm]
    exact Complex.norm_exp_ofReal_mul_I b
  rw [h2, mul_one]
  simpa [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)

private lemma norm_exp_neg_sub_I_mul_sq (ε t : ℝ) :
    ‖Complex.exp (-(((ε : ℂ) - Complex.I) * (t : ℂ) ^ 2))‖ = Real.exp (-ε * t ^ 2) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, sq]

private lemma one_le_norm_ofReal_sub_I (ε : ℝ) : 1 ≤ ‖(ε : ℂ) - Complex.I‖ := by
  have hsq : 1 ≤ ‖(ε : ℂ) - Complex.I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    nlinarith [sq_nonneg ε]
  nlinarith [norm_nonneg ((ε : ℂ) - Complex.I)]

private lemma integrableOn_Ioi_inv_sq {L : ℝ} (hL : 0 < L) :
    IntegrableOn (fun t : ℝ => (1 : ℝ) / t ^ 2) (Set.Ioi L) volume := by
  have h := integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (c := L) (by norm_num) hL
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht0 : 0 < t := lt_trans hL ht
  dsimp only
  rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht0.le, Real.rpow_natCast, one_div]

private lemma integral_Ioi_inv_sq {L : ℝ} (hL : 0 < L) :
    ∫ t in Set.Ioi L, (1 : ℝ) / t ^ 2 = 1 / L := by
  have hderiv : ∀ x ∈ Set.Ici L, HasDerivAt (fun t : ℝ => -1 / t) (1 / x ^ 2) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hL hx)
    have h1 := ((hasDerivAt_id x).fun_inv hx0).fun_neg
    refine (h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv ?_
    · simp [neg_div, one_div]
    · simp [neg_div, one_div]
  have htend : Tendsto (fun t : ℝ => -1 / t) atTop (𝓝 0) := by
    simpa [neg_div] using (tendsto_const_nhds (x := (-1 : ℝ))).div_atTop tendsto_id
  have hres := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (integrableOn_Ioi_inv_sq hL) htend
  rw [hres]
  ring

private lemma damped_fresnel_tail_le {ε L : ℝ} (hε : 0 < ε) (hL : 0 < L) :
    ‖∫ t in Set.Ioi L, Complex.exp (-(((ε : ℂ) - Complex.I) * (t : ℂ) ^ 2))‖ ≤ 1 / L := by
  set b : ℂ := (ε : ℂ) - Complex.I
  have hb_norm : 1 ≤ ‖b‖ := one_le_norm_ofReal_sub_I ε
  have hb_ne : b ≠ 0 := by
    intro h; rw [h, norm_zero] at hb_norm; linarith
  have h2norm : ‖(2 : ℂ)‖ = 2 := by norm_num
  set f : ℝ → ℂ := fun t => Complex.exp (-b * (t : ℂ) ^ 2)
  set G : ℝ → ℂ := fun t => f t / (-2 * b * (t : ℂ))
  set R : ℝ → ℂ := fun t => f t / (2 * b * (t : ℂ) ^ 2)
  have hf_norm : ∀ t : ℝ, ‖f t‖ = Real.exp (-ε * t ^ 2) := fun t => by
    dsimp [f]; rw [neg_mul]; exact norm_exp_neg_sub_I_mul_sq ε t
  have hf_norm_le : ∀ t : ℝ, ‖f t‖ ≤ 1 := fun t => by
    rw [hf_norm t]
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
  have hf_int : Integrable f volume := by
    have hdom : Integrable (fun t : ℝ => Real.exp (-ε * t ^ 2)) volume :=
      integrable_exp_neg_mul_sq hε
    refine Integrable.mono' hdom ?_ (Filter.Eventually.of_forall fun t => (hf_norm t).le)
    exact (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.pow 2))).aestronglyMeasurable
  have hR_norm : ∀ t ∈ Set.Ioi L, ‖R t‖ ≤ (1 / 2 : ℝ) * (1 / t ^ 2) := by
    intro t ht
    have ht0 : 0 < t := lt_trans hL ht
    dsimp [R]
    rw [norm_div, norm_mul, norm_mul, norm_pow, h2norm,
      Complex.norm_real, Real.norm_of_nonneg ht0.le]
    calc ‖f t‖ / (2 * ‖b‖ * t ^ 2)
        ≤ 1 / (2 * 1 * t ^ 2) := by
          gcongr
          exact hf_norm_le t
      _ = (1 / 2 : ℝ) * (1 / t ^ 2) := by ring
  have hdom_int : IntegrableOn (fun t : ℝ => (1 / 2 : ℝ) * (1 / t ^ 2)) (Set.Ioi L) volume :=
    (integrableOn_Ioi_inv_sq hL).const_mul (1 / 2 : ℝ)
  have hR_int : IntegrableOn R (Set.Ioi L) volume := by
    refine Integrable.mono' hdom_int ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      intro t ht
      have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans hL ht))
      refine ContinuousAt.continuousWithinAt ?_
      exact (Complex.continuous_exp.comp
        (continuous_const.mul (Complex.continuous_ofReal.pow 2))).continuousAt.div
        (continuous_const.mul (Complex.continuous_ofReal.pow 2)).continuousAt
        (mul_ne_zero (mul_ne_zero (by norm_num) hb_ne) (pow_ne_zero 2 ht0))
    · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall hR_norm)
  have hderiv : ∀ x ∈ Set.Ici L, HasDerivAt G (f x + R x) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hL hx)
    have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0
    have hof : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
    have hsq : HasDerivAt (fun t : ℝ => (t : ℂ) ^ 2) (2 * (x : ℂ)) x := by
      have h := hof.fun_pow 2
      simpa [pow_one, mul_one] using h
    have h1 : HasDerivAt (fun t : ℝ => -b * (t : ℂ) ^ 2) (-2 * b * (x : ℂ)) x := by
      exact (hsq.const_mul (-b)).congr_deriv (by ring)
    have hf' : HasDerivAt f (f x * (-2 * b * (x : ℂ))) x := h1.cexp
    have hden : HasDerivAt (fun t : ℝ => -2 * b * (t : ℂ)) (-2 * b) x := by
      simpa using hof.const_mul (-2 * b)
    have hdiv := hf'.fun_div hden (mul_ne_zero (mul_ne_zero (by norm_num) hb_ne) hxc)
    refine hdiv.congr_deriv ?_
    dsimp [R]
    field_simp [hb_ne, hxc]
    ring
  have htend : Tendsto G atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := (1 / 2 : ℝ))).div_atTop tendsto_id)
    filter_upwards [eventually_gt_atTop 0] with t ht
    dsimp [G]
    rw [norm_div, norm_mul, norm_mul, norm_neg, h2norm,
      Complex.norm_real, Real.norm_of_nonneg ht.le]
    calc ‖f t‖ / (2 * ‖b‖ * t)
        ≤ 1 / (2 * 1 * t) := by
          gcongr
          exact hf_norm_le t
      _ = 1 / 2 / t := by ring
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (hf_int.integrableOn.add hR_int) htend
  rw [integral_add hf_int.integrableOn hR_int, zero_sub] at hftc
  have hfeq : ∫ t in Set.Ioi L, f t = -G L - ∫ t in Set.Ioi L, R t := eq_sub_of_add_eq hftc
  have hGL : ‖-G L‖ ≤ 1 / (2 * L) := by
    rw [norm_neg]
    dsimp [G]
    rw [norm_div, norm_mul, norm_mul, norm_neg, h2norm,
      Complex.norm_real, Real.norm_of_nonneg hL.le]
    calc ‖f L‖ / (2 * ‖b‖ * L)
        ≤ 1 / (2 * 1 * L) := by
          gcongr
          exact hf_norm_le L
      _ = 1 / (2 * L) := by ring
  have hR_bound : ‖∫ t in Set.Ioi L, R t‖ ≤ 1 / (2 * L) := by
    calc ‖∫ t in Set.Ioi L, R t‖
        ≤ ∫ t in Set.Ioi L, ‖R t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Set.Ioi L, (1 / 2 : ℝ) * (1 / t ^ 2) :=
          setIntegral_mono_on hR_int.norm hdom_int measurableSet_Ioi hR_norm
      _ = (1 / 2 : ℝ) * ∫ t in Set.Ioi L, (1 : ℝ) / t ^ 2 := integral_const_mul _ _
      _ = (1 / 2 : ℝ) * (1 / L) := by rw [integral_Ioi_inv_sq hL]
      _ = 1 / (2 * L) := by ring
  calc ‖∫ t in Set.Ioi L, Complex.exp (-(((ε : ℂ) - Complex.I) * (t : ℂ) ^ 2))‖
      = ‖∫ t in Set.Ioi L, f t‖ := by
        congr 2; ext t; dsimp [f, b]; rw [neg_mul]
    _ = ‖-G L - ∫ t in Set.Ioi L, R t‖ := by rw [hfeq]
    _ ≤ ‖-G L‖ + ‖∫ t in Set.Ioi L, R t‖ := norm_sub_le _ _
    _ ≤ 1 / (2 * L) + 1 / (2 * L) := add_le_add hGL hR_bound
    _ = 1 / L := by ring

private lemma damped_fresnel_norm_le {ε L : ℝ} (hε : 0 < ε) (hL : 0 < L) :
    ‖∫ t in (-L)..L, Complex.exp (-(((ε : ℂ) - Complex.I) * (t : ℂ) ^ 2))‖ ≤ √Real.pi + 2 / L := by
  set b : ℂ := (ε : ℂ) - Complex.I
  set f : ℝ → ℂ := fun t => Complex.exp (-(b * (t : ℂ) ^ 2))
  have hb_re : 0 < b.re := by simp [b, hε]
  have hb_norm : 1 ≤ ‖b‖ := one_le_norm_ofReal_sub_I ε
  have hb_ne : b ≠ 0 := by intro h; rw [h, norm_zero] at hb_norm; linarith
  have hf_int : Integrable f volume := by
    have hdom : Integrable (fun t : ℝ => Real.exp (-ε * t ^ 2)) volume :=
      integrable_exp_neg_mul_sq hε
    refine Integrable.mono' hdom ?_ (Filter.Eventually.of_forall fun t => (norm_exp_neg_sub_I_mul_sq ε t).le)
    exact (Complex.continuous_exp.comp
      ((continuous_const.mul (Complex.continuous_ofReal.pow 2)).neg)).aestronglyMeasurable
  have hgauss : ∫ x : ℝ, f x = ((Real.pi : ℂ) / b) ^ ((1 : ℂ) / 2) := by
    have h := integral_gaussian_complex hb_re
    convert h using 1
    congr 1; ext x; simp [f, neg_mul]
  have hgauss_norm : ‖∫ x : ℝ, f x‖ ≤ √Real.pi := by
    rw [hgauss]
    have hne : (Real.pi : ℂ) / b ≠ 0 := div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne') hb_ne
    rw [Complex.norm_cpow_of_ne_zero hne]
    simp only [one_div, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat, Complex.inv_im,
      Complex.im_ofNat, neg_zero, zero_div, mul_zero, Real.exp_zero, div_one]
    have harg : (2 : ℝ) / (2 * 2) = 1 / 2 := by norm_num
    rw [harg, norm_div, Complex.norm_of_nonneg Real.pi_pos.le, ← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt (div_le_self Real.pi_pos.le hb_norm)
  have hsplit : ∫ x : ℝ, f x =
      (∫ x in Set.Iic (-L), f x) + (∫ x in Set.Ioc (-L) L, f x) + (∫ x in Set.Ioi L, f x) := by
    have h1 : Set.Iic (-L) ∪ Set.Ioc (-L) L = Set.Iic L := Set.Iic_union_Ioc_eq_Iic (by linarith)
    have h2 : Set.Iic L ∪ Set.Ioi L = Set.univ := Set.Iic_union_Ioi
    have hd1 : Disjoint (Set.Iic (-L)) (Set.Ioc (-L) L) := Set.Iic_disjoint_Ioc le_rfl
    have hd2 : Disjoint (Set.Iic L) (Set.Ioi L) := Set.Iic_disjoint_Ioi le_rfl
    rw [← setIntegral_univ, ← h2, setIntegral_union hd2 measurableSet_Ioi hf_int.integrableOn hf_int.integrableOn,
      ← h1, setIntegral_union hd1 measurableSet_Ioc hf_int.integrableOn hf_int.integrableOn]
  have heven : ∫ x in Set.Iic (-L), f x = ∫ x in Set.Ioi L, f x := by
    have hcomp := integral_comp_neg_Ioi (f := f) L
    simpa [f] using hcomp.symm
  have hmid : ∫ t in (-L)..L, f t =
      (∫ x : ℝ, f x) - (∫ x in Set.Iic (-L), f x) - (∫ x in Set.Ioi L, f x) := by
    rw [intervalIntegral.integral_of_le (by linarith : -L ≤ L)]
    rw [hsplit]
    ring
  have htail := damped_fresnel_tail_le hε hL
  rw [hmid]
  calc ‖(∫ x : ℝ, f x) - (∫ x in Set.Iic (-L), f x) - (∫ x in Set.Ioi L, f x)‖
      ≤ ‖(∫ x : ℝ, f x) - (∫ x in Set.Iic (-L), f x)‖ + ‖∫ x in Set.Ioi L, f x‖ := norm_sub_le _ _
    _ ≤ ‖∫ x : ℝ, f x‖ + ‖∫ x in Set.Iic (-L), f x‖ + ‖∫ x in Set.Ioi L, f x‖ := by
        gcongr; exact norm_sub_le _ _
    _ = ‖∫ x : ℝ, f x‖ + ‖∫ x in Set.Ioi L, f x‖ + ‖∫ x in Set.Ioi L, f x‖ := by rw [heven]
    _ ≤ √Real.pi + 1 / L + 1 / L := by gcongr
    _ = √Real.pi + 2 / L := by ring

private lemma fresnel_norm_le {L : ℝ} (hL : 0 < L) :
    ‖∫ t in (-L)..L, Complex.exp (Complex.I * ((t : ℂ) ^ 2))‖ ≤ √Real.pi + 2 / L := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  set ε : ℝ := δ / (2 * L ^ 3)
  have hε : 0 < ε := div_pos hδ (by positivity)
  set f0 : ℝ → ℂ := fun t => Complex.exp (Complex.I * ((t : ℂ) ^ 2))
  set f1 : ℝ → ℂ := fun t => Complex.exp (-(((ε : ℂ) - Complex.I) * (t : ℂ) ^ 2))
  have hdiff_pt : ∀ t ∈ Set.uIoc (-L) L, ‖f0 t - f1 t‖ ≤ ε * L ^ 2 := by
    intro t ht
    rw [Set.uIoc_of_le (by linarith : -L ≤ L)] at ht
    have htsq : t ^ 2 ≤ L ^ 2 := by nlinarith [ht.1, ht.2]
    have hfac : f0 t - f1 t =
        f0 t * ((1 - Real.exp (-ε * t ^ 2) : ℝ) : ℂ) := by
      dsimp [f0, f1]
      rw [Complex.ofReal_sub, Complex.ofReal_one, mul_sub, mul_one, Complex.ofReal_exp,
        ← Complex.exp_add]
      congr 2
      push_cast
      ring
    rw [hfac, norm_mul]
    have hf0_norm : ‖f0 t‖ = 1 := by
      dsimp [f0]
      have : Complex.I * (t : ℂ) ^ 2 = ((t ^ 2 : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [this]
      exact Complex.norm_exp_ofReal_mul_I (t ^ 2)
    rw [hf0_norm, one_mul, Complex.norm_real, Real.norm_of_nonneg]
    · have hexp : 1 - ε * t ^ 2 ≤ Real.exp (-ε * t ^ 2) := by
        linarith [Real.add_one_le_exp (-ε * t ^ 2)]
      nlinarith
    · have : Real.exp (-ε * t ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
      linarith
  have hcont0 : Continuous f0 :=
    Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.pow 2))
  have hcont1 : Continuous f1 :=
    Complex.continuous_exp.comp ((continuous_const.mul (Complex.continuous_ofReal.pow 2)).neg)
  have hdiff_int : ‖(∫ t in (-L)..L, f0 t) - (∫ t in (-L)..L, f1 t)‖ ≤ δ := by
    rw [← intervalIntegral.integral_sub (hcont0.intervalIntegrable _ _) (hcont1.intervalIntegrable _ _)]
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const hdiff_pt
    have habs : |L - -L| = 2 * L := by rw [show L - -L = 2 * L by ring, abs_of_pos (by positivity)]
    rw [habs] at hbound
    calc ‖∫ t in (-L)..L, f0 t - f1 t‖
        ≤ ε * L ^ 2 * (2 * L) := hbound
      _ = δ := by dsimp [ε]; field_simp [hL.ne']
  calc ‖∫ t in (-L)..L, f0 t‖
      ≤ ‖(∫ t in (-L)..L, f0 t) - (∫ t in (-L)..L, f1 t)‖ + ‖∫ t in (-L)..L, f1 t‖ := by
        simpa [sub_add_cancel] using norm_add_le ((∫ t in (-L)..L, f0 t) - (∫ t in (-L)..L, f1 t))
          (∫ t in (-L)..L, f1 t)
    _ ≤ δ + (√Real.pi + 2 / L) := add_le_add hdiff_int (damped_fresnel_norm_le hε hL)
    _ = √Real.pi + 2 / L + δ := by ring

/- ## Section 2: Van der Corput and stationary-phase oscillatory integral bounds -/

private lemma abs_sub_le_of_deriv_le {a b C x y : ℝ} {f f' : ℝ → ℝ}
    (hf : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hf' : ContinuousOn f' (Set.Icc a b))
    (hC : ∀ t ∈ Set.Icc a b, |f' t| ≤ C)
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    |f y - f x| ≤ C * |y - x| := by
  have hsub : Set.uIcc x y ⊆ Set.Icc a b := Set.uIcc_subset_Icc hx hy
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hf t (hsub ht))
    ((hf'.mono hsub).intervalIntegrable)
  rw [← hftc, ← Real.norm_eq_abs]
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht => by
    rw [Real.norm_eq_abs]
    exact hC t (hsub (Set.uIoc_subset_uIcc ht)))

private lemma osc_ibp_bound {a b m : ℝ} {u u' u'' : ℝ → ℝ}
    (hab : a ≤ b) (hm : 0 < m)
    (hu : ∀ x ∈ Set.Icc a b, HasDerivAt u (u' x) x)
    (hu' : ∀ x ∈ Set.Icc a b, HasDerivAt u' (u'' x) x)
    (hu'' : ContinuousOn u'' (Set.Icc a b))
    (hnonneg : ∀ x ∈ Set.Icc a b, 0 ≤ u'' x)
    (hlower : ∀ x ∈ Set.Icc a b, m ≤ |u' x|) :
    ‖∫ x in a..b, Complex.exp (Complex.I * (u x : ℂ))‖ ≤ 3 / m := by
  have hne : ∀ x ∈ Set.Icc a b, u' x ≠ 0 := fun x hx h => by
    have := hlower x hx; rw [h, abs_zero] at this; linarith
  have hcont_u : ContinuousOn u (Set.Icc a b) := fun x hx => (hu x hx).continuousAt.continuousWithinAt
  have hcont_u' : ContinuousOn u' (Set.Icc a b) := fun x hx => (hu' x hx).continuousAt.continuousWithinAt
  set F : ℝ → ℂ := fun x => Complex.exp (Complex.I * (u x : ℂ)) / (Complex.I * (u' x : ℂ))
  set E : ℝ → ℂ := fun x => Complex.exp (Complex.I * (u x : ℂ))
  set R : ℝ → ℂ := fun x => Complex.I * ((u'' x / (u' x) ^ 2 : ℝ) : ℂ) * E x
  have hF_deriv : ∀ x ∈ Set.uIcc a b, HasDerivAt F (E x + R x) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hux : HasDerivAt (fun t : ℝ => Complex.I * (u t : ℂ)) (Complex.I * (u' x : ℂ)) x :=
      ((hu x hx).ofReal_comp).const_mul Complex.I
    have hE' : HasDerivAt E (E x * (Complex.I * (u' x : ℂ))) x := hux.cexp
    have hden' : HasDerivAt (fun t : ℝ => Complex.I * (u' t : ℂ)) (Complex.I * (u'' x : ℂ)) x :=
      ((hu' x hx).ofReal_comp).const_mul Complex.I
    have hden_ne : Complex.I * (u' x : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (hne x hx))
    have hdiv := hE'.fun_div hden' hden_ne
    refine hdiv.congr_deriv ?_
    dsimp [R, E]
    have huxc : (u' x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hne x hx)
    push_cast
    field_simp [Complex.I_ne_zero, huxc]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hE_int : IntervalIntegrable E volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hcont_u))
  have hR_int : IntervalIntegrable R volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    refine (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn ?_)).mul ?_
    · exact hu''.div (hcont_u'.pow 2) (fun x hx => pow_ne_zero 2 (hne x hx))
    · exact Complex.continuous_exp.comp_continuousOn
        (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hcont_u))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hF_deriv (hE_int.add hR_int)
  rw [intervalIntegral.integral_add hE_int hR_int] at hftc
  have hEeq : ∫ x in a..b, E x = F b - F a - ∫ x in a..b, R x := eq_sub_of_add_eq hftc
  have hF_norm : ∀ x ∈ Set.Icc a b, ‖F x‖ ≤ 1 / m := by
    intro x hx
    dsimp [F]
    rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have he1 : ‖Complex.exp (Complex.I * (u x : ℂ))‖ = 1 := by
      rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I (u x)
    rw [he1]
    exact one_div_le_one_div_of_le hm (hlower x hx)
  have hR_bound : ‖∫ x in a..b, R x‖ ≤ 1 / m := by
    have hR_norm : ∀ x ∈ Set.Icc a b, ‖R x‖ = u'' x / (u' x) ^ 2 := by
      intro x hx
      dsimp [R, E]
      have he1 : ‖Complex.exp (Complex.I * (u x : ℂ))‖ = 1 := by
        rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I (u x)
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, he1, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (div_nonneg (hnonneg x hx) (sq_nonneg _))]
    have hinv_deriv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun t : ℝ => -1 / u' t) (u'' x / (u' x) ^ 2) x := by
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      have h1 := ((hu' x hx).fun_inv (hne x hx)).fun_neg
      refine (h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv ?_
      · simp [neg_div, one_div]
      · ring
    have hquot_int : IntervalIntegrable (fun x : ℝ => u'' x / (u' x) ^ 2) volume a b := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hab]
      exact hu''.div (hcont_u'.pow 2) (fun x hx => pow_ne_zero 2 (hne x hx))
    have hquot_eval := intervalIntegral.integral_eq_sub_of_hasDerivAt hinv_deriv hquot_int
    calc ‖∫ x in a..b, R x‖
        ≤ ∫ x in a..b, ‖R x‖ := intervalIntegral.norm_integral_le_integral_norm hab
      _ = ∫ x in a..b, u'' x / (u' x) ^ 2 := by
          refine intervalIntegral.integral_congr fun x hx => ?_
          rw [Set.uIcc_of_le hab] at hx
          exact hR_norm x hx
      _ = -1 / u' b - -1 / u' a := hquot_eval
      _ ≤ 1 / m := by
          have hmono : u' a ≤ u' b := by
            have hftc' := intervalIntegral.integral_eq_sub_of_hasDerivAt
              (fun x hx => hu' x (by rwa [Set.uIcc_of_le hab] at hx))
              (hu''.intervalIntegrable_of_Icc hab)
            have hnn : 0 ≤ ∫ x in a..b, u'' x :=
              intervalIntegral.integral_nonneg hab (fun x hx => hnonneg x hx)
            linarith
          have ha_abs := hlower a ⟨le_rfl, hab⟩
          have hb_abs := hlower b ⟨hab, le_rfl⟩
          by_cases ha_pos : 0 < u' a
          · have hb_pos : 0 < u' b := lt_of_lt_of_le ha_pos hmono
            have ha_ge : m ≤ u' a := by rwa [abs_of_pos ha_pos] at ha_abs
            have h1 : 1 / u' a ≤ 1 / m := one_div_le_one_div_of_le hm ha_ge
            have h2 : 0 < 1 / u' b := one_div_pos.mpr hb_pos
            rw [neg_div, neg_div]
            linarith
          · have ha_neg : u' a < 0 := lt_of_le_of_ne (not_lt.mp ha_pos) (hne a ⟨le_rfl, hab⟩)
            have hb_neg : u' b < 0 := by
              by_contra hb_nn
              push Not at hb_nn
              have h0 : (0 : ℝ) ∈ Set.Icc (u' a) (u' b) := ⟨ha_neg.le, hb_nn⟩
              obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hab hcont_u' h0
              exact hne c hc hc0
            have hb_le : u' b ≤ -m := by
              rw [abs_of_neg hb_neg] at hb_abs; linarith
            have h1 : -1 / u' b ≤ 1 / m := by
              rw [show -1 / u' b = 1 / (-u' b) by ring]
              exact one_div_le_one_div_of_le hm (by linarith)
            have h2 : 0 < -1 / u' a := by
              rw [show -1 / u' a = 1 / (-u' a) by ring]
              exact one_div_pos.mpr (by linarith)
            linarith
  rw [hEeq]
  calc ‖F b - F a - ∫ x in a..b, R x‖
      ≤ ‖F b - F a‖ + ‖∫ x in a..b, R x‖ := norm_sub_le _ _
    _ ≤ ‖F b‖ + ‖F a‖ + ‖∫ x in a..b, R x‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ 1 / m + 1 / m + 1 / m := by
        gcongr
        · exact hF_norm b ⟨hab, le_rfl⟩
        · exact hF_norm a ⟨le_rfl, hab⟩
    _ = 3 / m := by ring

private lemma deriv_sub_ge_of_deriv2_ge {a b B : ℝ} {u' u'' : ℝ → ℝ}
    (hab : a ≤ b)
    (hu' : ∀ x ∈ Set.Icc a b, HasDerivAt u' (u'' x) x)
    (hu'' : ContinuousOn u'' (Set.Icc a b))
    (hB : ∀ x ∈ Set.Icc a b, B ≤ u'' x) :
    B * (b - a) ≤ u' b - u' a := by
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hu' x (by rwa [Set.uIcc_of_le hab] at hx))
    (hu''.intervalIntegrable_of_Icc hab)
  rw [← hftc]
  have h1 : ∫ _ in a..b, B = B * (b - a) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  rw [← h1]
  exact intervalIntegral.integral_mono_on hab intervalIntegrable_const
    (hu''.intervalIntegrable_of_Icc hab) hB

private lemma norm_integral_exp_I_le_length {a b : ℝ} {u : ℝ → ℝ} (hab : a ≤ b) :
    ‖∫ x in a..b, Complex.exp (Complex.I * (u x : ℂ))‖ ≤ b - a := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := 1)
    (f := fun x => Complex.exp (Complex.I * (u x : ℂ))) (fun x _ => by
      rw [mul_comm, Complex.norm_exp_ofReal_mul_I])
  simpa [abs_of_nonneg (sub_nonneg.mpr hab)] using h

private lemma osc_vdc2_bound {a b B : ℝ} {u u' u'' : ℝ → ℝ}
    (hab : a ≤ b) (hB : 0 < B)
    (hu : ∀ x ∈ Set.Icc a b, HasDerivAt u (u' x) x)
    (hu' : ∀ x ∈ Set.Icc a b, HasDerivAt u' (u'' x) x)
    (hu'' : ContinuousOn u'' (Set.Icc a b))
    (hlower : ∀ x ∈ Set.Icc a b, B ≤ u'' x) :
    ‖∫ x in a..b, Complex.exp (Complex.I * (u x : ℂ))‖ ≤ 8 / √B := by
  set E : ℝ → ℂ := fun x => Complex.exp (Complex.I * (u x : ℂ))
  have hcont_u : ContinuousOn u (Set.Icc a b) := fun x hx => (hu x hx).continuousAt.continuousWithinAt
  have hcont_u' : ContinuousOn u' (Set.Icc a b) := fun x hx => (hu' x hx).continuousAt.continuousWithinAt
  have hE_int : ∀ x y, x ∈ Set.Icc a b → y ∈ Set.Icc a b → IntervalIntegrable E volume x y := by
    intro x y hx hy
    apply ContinuousOn.intervalIntegrable
    refine Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn ?_))
    exact hcont_u.mono (Set.uIcc_subset_Icc hx hy)
  set r : ℝ := 2 / √B
  have hr : 0 < r := div_pos (by norm_num) (Real.sqrt_pos.mpr hB)
  have hBr : B * r = 2 * √B := by
    dsimp [r]
    have hs : √B ≠ 0 := (Real.sqrt_pos.mpr hB).ne'
    field_simp [hs]
    nlinarith [Real.sq_sqrt hB.le]
  have hBr_pos : 0 < B * r := mul_pos hB hr
  have hnonneg : ∀ x ∈ Set.Icc a b, 0 ≤ u'' x := fun x hx => le_trans hB.le (hlower x hx)
  by_cases ha0 : 0 ≤ u' a
  · set c := min (a + r) b
    have hac : a ≤ c := le_min (by linarith) hab
    have hcb : c ≤ b := min_le_right _ _
    have hsplit : ∫ x in a..b, E x = (∫ x in a..c, E x) + (∫ x in c..b, E x) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hE_int a c ⟨le_rfl, hab⟩ ⟨hac, hcb⟩) (hE_int c b ⟨hac, hcb⟩ ⟨hab, le_rfl⟩)).symm
    rw [hsplit]
    have h1 : ‖∫ x in a..c, E x‖ ≤ r :=
      (norm_integral_exp_I_le_length hac).trans (by linarith [min_le_left (a + r) b])
    have h2 : ‖∫ x in c..b, E x‖ ≤ 3 / (B * r) := by
      by_cases hlt : a + r < b
      · have hc_eq : c = a + r := min_eq_left hlt.le
        refine osc_ibp_bound hcb hBr_pos
          (fun x hx => hu x ⟨hac.trans hx.1, hx.2⟩)
          (fun x hx => hu' x ⟨hac.trans hx.1, hx.2⟩)
          (hu''.mono fun x hx => ⟨hac.trans hx.1, hx.2⟩)
          (fun x hx => hnonneg x ⟨hac.trans hx.1, hx.2⟩) ?_
        intro x hx
        have hstep := deriv_sub_ge_of_deriv2_ge (hac.trans hx.1)
          (fun t ht => hu' t ⟨ht.1, ht.2.trans hx.2⟩)
          (hu''.mono fun t ht => ⟨ht.1, ht.2.trans hx.2⟩)
          (fun t ht => hlower t ⟨ht.1, ht.2.trans hx.2⟩)
        have hge : B * r ≤ u' x := by
          have : r ≤ x - a := by linarith [hx.1, hc_eq]
          nlinarith
        rw [abs_of_nonneg (hBr_pos.le.trans hge)]
        exact hge
      · have hc_eq : c = b := min_eq_right (not_lt.mp hlt)
        rw [hc_eq, intervalIntegral.integral_same, norm_zero]
        positivity
    calc ‖(∫ x in a..c, E x) + (∫ x in c..b, E x)‖
        ≤ ‖∫ x in a..c, E x‖ + ‖∫ x in c..b, E x‖ := norm_add_le _ _
      _ ≤ r + 3 / (B * r) := add_le_add h1 h2
      _ = 7 / (2 * √B) := by rw [hBr]; dsimp [r]; ring
      _ ≤ 8 / √B := by
          have hs : 0 < √B := Real.sqrt_pos.mpr hB
          rw [div_le_div_iff₀ (by positivity) hs]; linarith
  · push Not at ha0
    by_cases hb0 : u' b ≤ 0
    · set c := max a (b - r)
      have hac : a ≤ c := le_max_left _ _
      have hcb : c ≤ b := max_le hab (by linarith)
      have hsplit : ∫ x in a..b, E x = (∫ x in a..c, E x) + (∫ x in c..b, E x) :=
        (intervalIntegral.integral_add_adjacent_intervals
          (hE_int a c ⟨le_rfl, hab⟩ ⟨hac, hcb⟩) (hE_int c b ⟨hac, hcb⟩ ⟨hab, le_rfl⟩)).symm
      rw [hsplit]
      have h2 : ‖∫ x in c..b, E x‖ ≤ r :=
        (norm_integral_exp_I_le_length hcb).trans (by linarith [le_max_right a (b - r)])
      have h1 : ‖∫ x in a..c, E x‖ ≤ 3 / (B * r) := by
        by_cases hlt : a < b - r
        · have hc_eq : c = b - r := max_eq_right hlt.le
          refine osc_ibp_bound hac hBr_pos
            (fun x hx => hu x ⟨hx.1, hx.2.trans hcb⟩)
            (fun x hx => hu' x ⟨hx.1, hx.2.trans hcb⟩)
            (hu''.mono fun x hx => ⟨hx.1, hx.2.trans hcb⟩)
            (fun x hx => hnonneg x ⟨hx.1, hx.2.trans hcb⟩) ?_
          intro x hx
          have hstep := deriv_sub_ge_of_deriv2_ge (hx.2.trans hcb)
            (fun t ht => hu' t ⟨hx.1.trans ht.1, ht.2⟩)
            (hu''.mono fun t ht => ⟨hx.1.trans ht.1, ht.2⟩)
            (fun t ht => hlower t ⟨hx.1.trans ht.1, ht.2⟩)
          have hle : u' x ≤ -(B * r) := by
            have : r ≤ b - x := by linarith [hx.2, hc_eq]
            nlinarith
          rw [abs_of_neg (by linarith)]
          linarith
        · have hc_eq : c = a := max_eq_left (not_lt.mp hlt)
          rw [hc_eq, intervalIntegral.integral_same, norm_zero]
          positivity
      calc ‖(∫ x in a..c, E x) + (∫ x in c..b, E x)‖
          ≤ ‖∫ x in a..c, E x‖ + ‖∫ x in c..b, E x‖ := norm_add_le _ _
        _ ≤ 3 / (B * r) + r := add_le_add h1 h2
        _ = 7 / (2 * √B) := by rw [hBr]; dsimp [r]; ring
        _ ≤ 8 / √B := by
            have hs : 0 < √B := Real.sqrt_pos.mpr hB
            rw [div_le_div_iff₀ (by positivity) hs]; linarith
    · push Not at hb0
      obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hab hcont_u' ⟨ha0.le, hb0.le⟩
      set c1 := max a (c - r)
      set c2 := min b (c + r)
      have hac1 : a ≤ c1 := le_max_left _ _
      have hc1c : c1 ≤ c := max_le hc.1 (by linarith)
      have hcc2 : c ≤ c2 := le_min hc.2 (by linarith)
      have hc2b : c2 ≤ b := min_le_left _ _
      have hc1c2 : c1 ≤ c2 := hc1c.trans hcc2
      have hsplit1 : ∫ x in a..b, E x =
          (∫ x in a..c1, E x) + (∫ x in c1..c2, E x) + (∫ x in c2..b, E x) := by
        rw [intervalIntegral.integral_add_adjacent_intervals
          (hE_int a c1 ⟨le_rfl, hab⟩ ⟨hac1, hc1c.trans hc.2⟩)
          (hE_int c1 c2 ⟨hac1, hc1c.trans hc.2⟩ ⟨hc.1.trans hcc2, hc2b⟩),
          intervalIntegral.integral_add_adjacent_intervals
          (hE_int a c2 ⟨le_rfl, hab⟩ ⟨hc.1.trans hcc2, hc2b⟩)
          (hE_int c2 b ⟨hc.1.trans hcc2, hc2b⟩ ⟨hab, le_rfl⟩)]
      rw [hsplit1]
      have hmid : ‖∫ x in c1..c2, E x‖ ≤ 2 * r :=
        (norm_integral_exp_I_le_length hc1c2).trans
          (by linarith [le_max_right a (c - r), min_le_right b (c + r)])
      have hleft : ‖∫ x in a..c1, E x‖ ≤ 3 / (B * r) := by
        by_cases hlt : a < c - r
        · have hc1_eq : c1 = c - r := max_eq_right hlt.le
          refine osc_ibp_bound hac1 hBr_pos
            (fun x hx => hu x ⟨hx.1, hx.2.trans (hc1c.trans hc.2)⟩)
            (fun x hx => hu' x ⟨hx.1, hx.2.trans (hc1c.trans hc.2)⟩)
            (hu''.mono fun x hx => ⟨hx.1, hx.2.trans (hc1c.trans hc.2)⟩)
            (fun x hx => hnonneg x ⟨hx.1, hx.2.trans (hc1c.trans hc.2)⟩) ?_
          intro x hx
          have hstep := deriv_sub_ge_of_deriv2_ge (hx.2.trans hc1c)
            (fun t ht => hu' t ⟨hx.1.trans ht.1, ht.2.trans hc.2⟩)
            (hu''.mono fun t ht => ⟨hx.1.trans ht.1, ht.2.trans hc.2⟩)
            (fun t ht => hlower t ⟨hx.1.trans ht.1, ht.2.trans hc.2⟩)
          have hle : u' x ≤ -(B * r) := by
            have : r ≤ c - x := by linarith [hx.2, hc1_eq]
            nlinarith
          rw [abs_of_neg (by linarith)]
          linarith
        · have hc1_eq : c1 = a := max_eq_left (not_lt.mp hlt)
          rw [hc1_eq, intervalIntegral.integral_same, norm_zero]
          positivity
      have hright : ‖∫ x in c2..b, E x‖ ≤ 3 / (B * r) := by
        by_cases hlt : c + r < b
        · have hc2_eq : c2 = c + r := min_eq_right hlt.le
          refine osc_ibp_bound hc2b hBr_pos
            (fun x hx => hu x ⟨(hc.1.trans hcc2).trans hx.1, hx.2⟩)
            (fun x hx => hu' x ⟨(hc.1.trans hcc2).trans hx.1, hx.2⟩)
            (hu''.mono fun x hx => ⟨(hc.1.trans hcc2).trans hx.1, hx.2⟩)
            (fun x hx => hnonneg x ⟨(hc.1.trans hcc2).trans hx.1, hx.2⟩) ?_
          intro x hx
          have hstep := deriv_sub_ge_of_deriv2_ge (hcc2.trans hx.1)
            (fun t ht => hu' t ⟨hc.1.trans ht.1, ht.2.trans hx.2⟩)
            (hu''.mono fun t ht => ⟨hc.1.trans ht.1, ht.2.trans hx.2⟩)
            (fun t ht => hlower t ⟨hc.1.trans ht.1, ht.2.trans hx.2⟩)
          have hge : B * r ≤ u' x := by
            have : r ≤ x - c := by linarith [hx.1, hc2_eq]
            nlinarith
          rw [abs_of_nonneg (hBr_pos.le.trans hge)]
          exact hge
        · have hc2_eq : c2 = b := min_eq_left (not_lt.mp hlt)
          rw [hc2_eq, intervalIntegral.integral_same, norm_zero]
          positivity
      calc ‖(∫ x in a..c1, E x) + (∫ x in c1..c2, E x) + (∫ x in c2..b, E x)‖
          ≤ ‖(∫ x in a..c1, E x) + (∫ x in c1..c2, E x)‖ + ‖∫ x in c2..b, E x‖ := norm_add_le _ _
        _ ≤ ‖∫ x in a..c1, E x‖ + ‖∫ x in c1..c2, E x‖ + ‖∫ x in c2..b, E x‖ := by
            gcongr; exact norm_add_le _ _
        _ ≤ 3 / (B * r) + 2 * r + 3 / (B * r) := by gcongr
        _ = 7 / √B := by rw [hBr]; dsimp [r]; ring
        _ ≤ 8 / √B := by gcongr; norm_num

private lemma osc_stationary_bound {a b A M3 h θ0 : ℝ} {u u' u'' : ℝ → ℝ}
    (hA : 0 < A) (hM3 : 0 ≤ M3) (hh : 0 < h)
    (hθa : a + h ≤ θ0) (hθb : θ0 ≤ b - h)
    (hu : ∀ x ∈ Set.Icc a b, HasDerivAt u (u' x) x)
    (hu' : ∀ x ∈ Set.Icc a b, HasDerivAt u' (u'' x) x)
    (hu'' : ContinuousOn u'' (Set.Icc a b))
    (hlower : ∀ x ∈ Set.Icc a b, A ≤ u'' x)
    (hroot : u' θ0 = 0)
    (hlip : ∀ x ∈ Set.Icc (θ0 - h) (θ0 + h), |u'' x - u'' θ0| ≤ M3 * |x - θ0|) :
    ‖∫ x in a..b, Complex.exp (Complex.I * (u x : ℂ))‖ ≤
      √(2 * Real.pi / A) + 10 / (A * h) + 2 * M3 * h ^ 4 := by
  have hab : a ≤ b := by linarith
  have hc1 : a ≤ θ0 - h := by linarith
  have hc2 : θ0 + h ≤ b := by linarith
  have hθ_mem : θ0 ∈ Set.Icc a b := ⟨by linarith, by linarith⟩
  have hsub : Set.Icc (θ0 - h) (θ0 + h) ⊆ Set.Icc a b := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  set E : ℝ → ℂ := fun x => Complex.exp (Complex.I * (u x : ℂ))
  have hcont_u : ContinuousOn u (Set.Icc a b) := fun x hx => (hu x hx).continuousAt.continuousWithinAt
  have hE_int : ∀ x y, x ∈ Set.Icc a b → y ∈ Set.Icc a b → IntervalIntegrable E volume x y := by
    intro x y hx hy
    apply ContinuousOn.intervalIntegrable
    refine Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn ?_))
    exact hcont_u.mono (Set.uIcc_subset_Icc hx hy)
  have hsplit : ∫ x in a..b, E x =
      (∫ x in a..(θ0 - h), E x) + (∫ x in (θ0 - h)..(θ0 + h), E x) + (∫ x in (θ0 + h)..b, E x) := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hE_int a (θ0 - h) ⟨le_rfl, hab⟩ ⟨hc1, by linarith⟩)
      (hE_int (θ0 - h) (θ0 + h) ⟨hc1, by linarith⟩ ⟨by linarith, hc2⟩),
      intervalIntegral.integral_add_adjacent_intervals
      (hE_int a (θ0 + h) ⟨le_rfl, hab⟩ ⟨by linarith, hc2⟩)
      (hE_int (θ0 + h) b ⟨by linarith, hc2⟩ ⟨hab, le_rfl⟩)]
  have hAh : 0 < A * h := mul_pos hA hh
  have hnonneg : ∀ x ∈ Set.Icc a b, 0 ≤ u'' x := fun x hx => le_trans hA.le (hlower x hx)
  have hleft : ‖∫ x in a..(θ0 - h), E x‖ ≤ 3 / (A * h) := by
    refine osc_ibp_bound hc1 hAh
      (fun x hx => hu x ⟨hx.1, by linarith [hx.2]⟩)
      (fun x hx => hu' x ⟨hx.1, by linarith [hx.2]⟩)
      (hu''.mono fun x hx => ⟨hx.1, by linarith [hx.2]⟩)
      (fun x hx => hnonneg x ⟨hx.1, by linarith [hx.2]⟩) ?_
    intro x hx
    have hstep := deriv_sub_ge_of_deriv2_ge (by linarith [hx.2] : x ≤ θ0)
      (fun t ht => hu' t ⟨hx.1.trans ht.1, ht.2.trans hθ_mem.2⟩)
      (hu''.mono fun t ht => ⟨hx.1.trans ht.1, ht.2.trans hθ_mem.2⟩)
      (fun t ht => hlower t ⟨hx.1.trans ht.1, ht.2.trans hθ_mem.2⟩)
    have hle : u' x ≤ -(A * h) := by
      have : h ≤ θ0 - x := by linarith [hx.2]
      nlinarith
    rw [abs_of_neg (by linarith)]
    linarith
  have hright : ‖∫ x in (θ0 + h)..b, E x‖ ≤ 3 / (A * h) := by
    refine osc_ibp_bound hc2 hAh
      (fun x hx => hu x ⟨by linarith [hx.1], hx.2⟩)
      (fun x hx => hu' x ⟨by linarith [hx.1], hx.2⟩)
      (hu''.mono fun x hx => ⟨by linarith [hx.1], hx.2⟩)
      (fun x hx => hnonneg x ⟨by linarith [hx.1], hx.2⟩) ?_
    intro x hx
    have hstep := deriv_sub_ge_of_deriv2_ge (by linarith [hx.1] : θ0 ≤ x)
      (fun t ht => hu' t ⟨hθ_mem.1.trans ht.1, ht.2.trans hx.2⟩)
      (hu''.mono fun t ht => ⟨hθ_mem.1.trans ht.1, ht.2.trans hx.2⟩)
      (fun t ht => hlower t ⟨hθ_mem.1.trans ht.1, ht.2.trans hx.2⟩)
    have hge : A * h ≤ u' x := by
      have : h ≤ x - θ0 := by linarith [hx.1]
      nlinarith
    rw [abs_of_nonneg (hAh.le.trans hge)]
    exact hge
  set B : ℝ := u'' θ0
  have hBA : A ≤ B := hlower θ0 hθ_mem
  have hB : 0 < B := lt_of_lt_of_le hA hBA
  set q : ℝ → ℝ := fun x => u θ0 + (B / 2) * (x - θ0) ^ 2
  set Q : ℝ → ℂ := fun x => Complex.exp (Complex.I * (q x : ℂ))
  have hrem : ∀ x ∈ Set.Icc (θ0 - h) (θ0 + h), |u x - q x| ≤ M3 * h ^ 3 := by
    intro x hx
    set err : ℝ → ℝ := fun t => u t - q t
    set err' : ℝ → ℝ := fun t => u' t - B * (t - θ0)
    have herr_d : ∀ t ∈ Set.Icc (θ0 - h) (θ0 + h), HasDerivAt err (err' t) t := by
      intro t ht
      have hqd : HasDerivAt q (B * (t - θ0)) t := by
        have hsq : HasDerivAt (fun s : ℝ => (s - θ0) ^ 2) (2 * (t - θ0)) t := by
          have h1 := ((hasDerivAt_id t).sub_const θ0).fun_pow 2
          simpa [pow_one, mul_one] using h1
        exact ((hsq.const_mul (B / 2)).const_add (u θ0)).congr_deriv (by ring)
      exact (hu t (hsub ht)).sub hqd
    have herr'_d : ∀ t ∈ Set.Icc (θ0 - h) (θ0 + h), HasDerivAt err' (u'' t - B) t := by
      intro t ht
      have h1 : HasDerivAt (fun s : ℝ => B * (s - θ0)) B t := by
        simpa using ((hasDerivAt_id t).sub_const θ0).const_mul B
      exact (hu' t (hsub ht)).sub h1
    have herr'_cont : ContinuousOn err' (Set.Icc (θ0 - h) (θ0 + h)) := fun t ht =>
      (herr'_d t ht).continuousAt.continuousWithinAt
    have herr'_bound : ∀ t ∈ Set.Icc (θ0 - h) (θ0 + h), |err' t| ≤ M3 * h ^ 2 := by
      intro t ht
      have hdist : |t - θ0| ≤ h := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hbd := abs_sub_le_of_deriv_le (x := θ0) (y := t) herr'_d ((hu''.mono hsub).sub continuousOn_const)
        (fun s hs => by
          have hs_dist : |s - θ0| ≤ h := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
          exact (hlip s hs).trans (mul_le_mul_of_nonneg_left hs_dist hM3))
        ⟨by linarith [hh], by linarith [hh]⟩ ht
      simp only [err', hroot, sub_self, mul_zero, sub_zero] at hbd
      calc |u' t - B * (t - θ0)|
          ≤ M3 * h * |t - θ0| := hbd
        _ ≤ M3 * h * h := mul_le_mul_of_nonneg_left hdist (by positivity)
        _ = M3 * h ^ 2 := by ring
    have hbd2 := abs_sub_le_of_deriv_le (x := θ0) (y := x) herr_d herr'_cont herr'_bound
      ⟨by linarith [hh], by linarith [hh]⟩ hx
    have hdist : |x - θ0| ≤ h := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have herr0 : err θ0 = 0 := by simp [err, q]
    rw [herr0, sub_zero] at hbd2
    calc |u x - q x|
        ≤ M3 * h ^ 2 * |x - θ0| := hbd2
      _ ≤ M3 * h ^ 2 * h := mul_le_mul_of_nonneg_left hdist (by positivity)
      _ = M3 * h ^ 3 := by ring
  have hQ_int : IntervalIntegrable Q volume (θ0 - h) (θ0 + h) := by
    apply Continuous.intervalIntegrable
    exact Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_const.add (continuous_const.mul ((continuous_id.sub continuous_const).pow 2)))))
  have hdiff_mid : ‖(∫ x in (θ0 - h)..(θ0 + h), E x) - (∫ x in (θ0 - h)..(θ0 + h), Q x)‖ ≤
      2 * M3 * h ^ 4 := by
    rw [← intervalIntegral.integral_sub
      (hE_int (θ0 - h) (θ0 + h) ⟨hc1, by linarith⟩ ⟨by linarith, hc2⟩) hQ_int]
    have hbd := intervalIntegral.norm_integral_le_of_norm_le_const (C := M3 * h ^ 3)
      (a := θ0 - h) (b := θ0 + h) (f := fun x => E x - Q x) (fun x hx => by
        rw [Set.uIoc_of_le (by linarith : θ0 - h ≤ θ0 + h)] at hx
        exact (norm_exp_I_mul_sub_exp_I_mul_le (u x) (q x)).trans (hrem x ⟨hx.1.le, hx.2⟩))
    have habs : |(θ0 + h) - (θ0 - h)| = 2 * h := by
      rw [show (θ0 + h) - (θ0 - h) = 2 * h by ring, abs_of_pos (by positivity)]
    rw [habs] at hbd
    linarith
  have hQ_norm : ‖∫ x in (θ0 - h)..(θ0 + h), Q x‖ ≤ √(2 * Real.pi / A) + 4 / (A * h) := by
    set s : ℝ := √(B / 2)
    have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
    set L : ℝ := s * h
    have hL : 0 < L := mul_pos hs hh
    have hQ_eq : ∫ x in (θ0 - h)..(θ0 + h), Q x =
        Complex.exp (Complex.I * (u θ0 : ℂ)) *
          ((s⁻¹ : ℝ) • ∫ t in (-L)..L, Complex.exp (Complex.I * ((t : ℂ) ^ 2))) := by
      have hfac : ∀ x : ℝ, Q x =
          Complex.exp (Complex.I * (u θ0 : ℂ)) *
            Complex.exp (Complex.I * (((s * (x - θ0)) : ℝ) : ℂ) ^ 2) := by
        intro x
        dsimp [Q, q]
        rw [← Complex.exp_add]
        congr 1
        have hsq : s ^ 2 = B / 2 := Real.sq_sqrt (by positivity)
        have hsqc : (s : ℂ) ^ 2 = (B : ℂ) / 2 := by exact_mod_cast hsq
        push_cast
        have hmul : ((s : ℂ) * ((x : ℂ) - (θ0 : ℂ))) ^ 2 = (s : ℂ) ^ 2 * ((x : ℂ) - (θ0 : ℂ)) ^ 2 := by ring
        rw [hmul, hsqc]
        ring
      simp_rw [hfac]
      rw [intervalIntegral.integral_const_mul]
      congr 1
      have hcomp := intervalIntegral.integral_comp_mul_add
        (f := fun t : ℝ => Complex.exp (Complex.I * ((t : ℂ) ^ 2)))
        (a := θ0 - h) (b := θ0 + h) (c := s) hs.ne' (-s * θ0)
      have ha_eq : s * (θ0 - h) + -s * θ0 = -L := by dsimp [L]; ring
      have hb_eq : s * (θ0 + h) + -s * θ0 = L := by dsimp [L]; ring
      rw [ha_eq, hb_eq] at hcomp
      rw [← hcomp]
      congr 1; ext x; congr 2; push_cast; ring
    rw [hQ_eq, norm_mul]
    have hphase : ‖Complex.exp (Complex.I * (u θ0 : ℂ))‖ = 1 := by
      rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I (u θ0)
    rw [hphase, one_mul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs.le)]
    calc s⁻¹ * ‖∫ t in (-L)..L, Complex.exp (Complex.I * ((t : ℂ) ^ 2))‖
        ≤ s⁻¹ * (√Real.pi + 2 / L) := mul_le_mul_of_nonneg_left (fresnel_norm_le hL) (inv_nonneg.mpr hs.le)
      _ = √(2 * Real.pi / B) + 4 / (B * h) := by
          have h1 : s⁻¹ * √Real.pi = √(2 * Real.pi / B) := by
            dsimp [s]
            rw [← Real.sqrt_inv, ← Real.sqrt_mul (by positivity)]
            congr 1; field_simp [hB.ne']
          have h2 : s⁻¹ * (2 / L) = 4 / (B * h) := by
            dsimp [L]
            have hsq : s ^ 2 = B / 2 := Real.sq_sqrt (by positivity)
            field_simp [hs.ne', hh.ne', hB.ne']
            nlinarith
          rw [mul_add, h1, h2]
      _ ≤ √(2 * Real.pi / A) + 4 / (A * h) := by
          gcongr
  have hmid : ‖∫ x in (θ0 - h)..(θ0 + h), E x‖ ≤ √(2 * Real.pi / A) + 4 / (A * h) + 2 * M3 * h ^ 4 := by
    calc ‖∫ x in (θ0 - h)..(θ0 + h), E x‖
        ≤ ‖(∫ x in (θ0 - h)..(θ0 + h), E x) - (∫ x in (θ0 - h)..(θ0 + h), Q x)‖ +
          ‖∫ x in (θ0 - h)..(θ0 + h), Q x‖ := by
          simpa [sub_add_cancel] using norm_add_le
            ((∫ x in (θ0 - h)..(θ0 + h), E x) - (∫ x in (θ0 - h)..(θ0 + h), Q x))
            (∫ x in (θ0 - h)..(θ0 + h), Q x)
      _ ≤ 2 * M3 * h ^ 4 + (√(2 * Real.pi / A) + 4 / (A * h)) := add_le_add hdiff_mid hQ_norm
      _ = √(2 * Real.pi / A) + 4 / (A * h) + 2 * M3 * h ^ 4 := by ring
  rw [hsplit]
  calc ‖(∫ x in a..(θ0 - h), E x) + (∫ x in (θ0 - h)..(θ0 + h), E x) + (∫ x in (θ0 + h)..b, E x)‖
      ≤ ‖(∫ x in a..(θ0 - h), E x) + (∫ x in (θ0 - h)..(θ0 + h), E x)‖ + ‖∫ x in (θ0 + h)..b, E x‖ :=
        norm_add_le _ _
    _ ≤ ‖∫ x in a..(θ0 - h), E x‖ + ‖∫ x in (θ0 - h)..(θ0 + h), E x‖ + ‖∫ x in (θ0 + h)..b, E x‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ 3 / (A * h) + (√(2 * Real.pi / A) + 4 / (A * h) + 2 * M3 * h ^ 4) + 3 / (A * h) := by
        gcongr
    _ = √(2 * Real.pi / A) + 10 / (A * h) + 2 * M3 * h ^ 4 := by ring

/- ## Section 3: Explicit 7-piece piecewise-linear curvature profile -/

private noncomputable def lin (a b va vb t : ℝ) : ℝ :=
  va + (vb - va) * ((t - a) / (b - a))

private lemma lin_left (a b va vb : ℝ) : lin a b va vb a = va := by
  simp [lin]

private lemma lin_right {a b : ℝ} (hab : a ≠ b) (va vb : ℝ) : lin a b va vb b = vb := by
  unfold lin
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  field_simp [hba]
  ring

private lemma hasDerivAt_lin {a b : ℝ} (va vb t : ℝ) :
    HasDerivAt (lin a b va vb) ((vb - va) / (b - a)) t := by
  unfold lin
  have h1 : HasDerivAt (fun s : ℝ => (s - a) / (b - a)) (1 / (b - a)) t := by
    simpa using ((hasDerivAt_id t).sub_const a).div_const (b - a)
  exact ((h1.const_mul (vb - va)).const_add va).congr_deriv (by ring)

private lemma continuous_lin (a b va vb : ℝ) : Continuous (lin a b va vb) :=
  continuous_const.add (continuous_const.mul ((continuous_id.sub continuous_const).div_const _))

private lemma integral_lin {a b : ℝ} (hab : a ≠ b) (va vb : ℝ) :
    ∫ t in a..b, lin a b va vb t = (b - a) * (va + vb) / 2 := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  set F : ℝ → ℝ := fun t => va * (t - a) + (vb - va) / (2 * (b - a)) * (t - a) ^ 2
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt F (lin a b va vb x) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => va * (t - a)) va x := by
      simpa using ((hasDerivAt_id x).sub_const a).const_mul va
    have hsq : HasDerivAt (fun t : ℝ => (t - a) ^ 2) (2 * (x - a)) x := by
      have h := ((hasDerivAt_id x).sub_const a).fun_pow 2
      simpa [pow_one, mul_one] using h
    have h2 := hsq.const_mul ((vb - va) / (2 * (b - a)))
    refine (h1.add h2).congr_deriv ?_
    unfold lin
    field_simp [hba]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ((continuous_lin a b va vb).intervalIntegrable _ _)]
  dsimp [F]
  field_simp [hba]
  ring

private lemma lin_mem_bounds {a b va vb t : ℝ} (hab : a < b) (ht : t ∈ Set.Icc a b) :
    min va vb ≤ lin a b va vb t ∧ lin a b va vb t ≤ max va vb := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hs0 : 0 ≤ (t - a) / (b - a) := div_nonneg (sub_nonneg.mpr ht.1) hba.le
  have hs1 : (t - a) / (b - a) ≤ 1 := (div_le_one hba).mpr (sub_le_sub_right ht.2 a)
  unfold lin
  constructor
  · by_cases h : va ≤ vb
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right (le_of_not_ge h)]; nlinarith
  · by_cases h : va ≤ vb
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left (le_of_not_ge h)]; nlinarith

private lemma lin_abs_sub {a b va vb x y : ℝ} :
    |lin a b va vb x - lin a b va vb y| = |(vb - va) / (b - a)| * |x - y| := by
  have h : lin a b va vb x - lin a b va vb y = ((vb - va) / (b - a)) * (x - y) := by
    unfold lin; ring
  rw [h, abs_mul]

private def B0 : ℝ := 128

private structure Params where
  δ : ℝ
  η : ℝ
  A : ℝ
  h : ℝ
  hδ_pos : 0 < δ
  hη_pos : 0 < η
  hδη : 4 * δ < η
  hη1 : η < 1
  h2π : 2 * η + 2 * δ < 2 * Real.pi
  hA_pos : 0 < A
  hh_pos : 0 < h
  hh_small : 2 * h < (η - δ) / 2

private noncomputable def posArea (P : Params) : ℝ :=
  2 * Real.pi + (B0 - 1) * P.η - 2 * P.δ

private lemma posArea_gt_two_pi (P : Params) : 2 * Real.pi < posArea P := by
  unfold posArea B0
  linarith [P.hδη, P.hδ_pos]

private lemma posArea_pos (P : Params) : 0 < posArea P :=
  lt_trans (by positivity) (posArea_gt_two_pi P)

private noncomputable def Hval (P : Params) : ℝ :=
  2 * posArea P / P.δ

private lemma Hval_pos (P : Params) : 0 < Hval P :=
  div_pos (mul_pos (by norm_num) (posArea_pos P)) P.hδ_pos

private noncomputable def g (P : Params) (t : ℝ) : ℝ :=
  if t ≤ P.δ then lin 0 P.δ 0 B0 t
  else if t ≤ P.η then lin P.δ P.η B0 1 t
  else if t ≤ 2 * Real.pi - P.η - P.δ then 1
  else if t ≤ 2 * Real.pi - 2 * P.δ then
    lin (2 * Real.pi - P.η - P.δ) (2 * Real.pi - 2 * P.δ) 1 B0 t
  else if t ≤ 2 * Real.pi - P.δ then
    lin (2 * Real.pi - 2 * P.δ) (2 * Real.pi - P.δ) B0 0 t
  else if t ≤ 2 * Real.pi - P.δ / 2 then
    lin (2 * Real.pi - P.δ) (2 * Real.pi - P.δ / 2) 0 (-Hval P) t
  else
    lin (2 * Real.pi - P.δ / 2) (2 * Real.pi) (-Hval P) 0 t

private lemma g_eq_piece1 (P : Params) {t : ℝ} (ht : t ∈ Set.Icc 0 P.δ) :
    g P t = lin 0 P.δ 0 B0 t := by
  unfold g; simp [ht.2]

private lemma g_eq_piece2 (P : Params) {t : ℝ} (ht : t ∈ Set.Icc P.δ P.η) :
    g P t = lin P.δ P.η B0 1 t := by
  unfold g
  by_cases h1 : t ≤ P.δ
  · have hteq : t = P.δ := le_antisymm h1 ht.1
    rw [if_pos h1, hteq, lin_right P.hδ_pos.ne, lin_left]
  · rw [if_neg h1, if_pos ht.2]

private lemma g_eq_piece3 (P : Params) {t : ℝ} (ht : t ∈ Set.Icc P.η (2 * Real.pi - P.η - P.δ)) :
    g P t = 1 := by
  have h1 : ¬ t ≤ P.δ := by linarith [ht.1, P.hδη, P.hδ_pos]
  unfold g
  rw [if_neg h1]
  by_cases h2 : t ≤ P.η
  · have hteq : t = P.η := le_antisymm h2 ht.1
    rw [if_pos h2, hteq, lin_right (by linarith [P.hδη, P.hδ_pos])]
  · rw [if_neg h2, if_pos ht.2]

private lemma g_eq_piece4 (P : Params) {t : ℝ}
    (ht : t ∈ Set.Icc (2 * Real.pi - P.η - P.δ) (2 * Real.pi - 2 * P.δ)) :
    g P t = lin (2 * Real.pi - P.η - P.δ) (2 * Real.pi - 2 * P.δ) 1 B0 t := by
  have h1 : ¬ t ≤ P.δ := by linarith [ht.1, P.h2π, P.hδη, P.hδ_pos]
  have h2 : ¬ t ≤ P.η := by linarith [ht.1, P.h2π, P.hδη, P.hδ_pos]
  unfold g
  rw [if_neg h1, if_neg h2]
  by_cases h3 : t ≤ 2 * Real.pi - P.η - P.δ
  · have hteq : t = 2 * Real.pi - P.η - P.δ := le_antisymm h3 ht.1
    rw [if_pos h3, hteq, lin_left]
  · rw [if_neg h3, if_pos ht.2]

private lemma g_eq_piece5 (P : Params) {t : ℝ}
    (ht : t ∈ Set.Icc (2 * Real.pi - 2 * P.δ) (2 * Real.pi - P.δ)) :
    g P t = lin (2 * Real.pi - 2 * P.δ) (2 * Real.pi - P.δ) B0 0 t := by
  have h1 : ¬ t ≤ P.δ := by linarith [ht.1, P.h2π, P.hδη, P.hδ_pos]
  have h2 : ¬ t ≤ P.η := by linarith [ht.1, P.h2π, P.hδη, P.hδ_pos]
  have h3 : ¬ t ≤ 2 * Real.pi - P.η - P.δ := by linarith [ht.1, P.hδη, P.hδ_pos]
  unfold g
  rw [if_neg h1, if_neg h2, if_neg h3]
  by_cases h4 : t ≤ 2 * Real.pi - 2 * P.δ
  · have hteq : t = 2 * Real.pi - 2 * P.δ := le_antisymm h4 ht.1
    rw [if_pos h4, hteq, lin_right (by linarith [P.hδη, P.hδ_pos]), lin_left]
  · rw [if_neg h4, if_pos ht.2]

private lemma g_eq_piece6 (P : Params) {t : ℝ}
    (ht : t ∈ Set.Icc (2 * Real.pi - P.δ) (2 * Real.pi - P.δ / 2)) :
    g P t = lin (2 * Real.pi - P.δ) (2 * Real.pi - P.δ / 2) 0 (-Hval P) t := by
  have h1 : ¬ t ≤ P.δ := by linarith [ht.1, P.h2π, P.hδη, P.hδ_pos]
  have h2 : ¬ t ≤ P.η := by linarith [ht.1, P.h2π, P.hδη, P.hδ_pos]
  have h3 : ¬ t ≤ 2 * Real.pi - P.η - P.δ := by linarith [ht.1, P.hδη, P.hδ_pos]
  have h4 : ¬ t ≤ 2 * Real.pi - 2 * P.δ := by linarith [ht.1, P.hδ_pos]
  unfold g
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
  by_cases h5 : t ≤ 2 * Real.pi - P.δ
  · have hteq : t = 2 * Real.pi - P.δ := le_antisymm h5 ht.1
    rw [if_pos h5, hteq, lin_right (by linarith [P.hδ_pos]), lin_left]
  · rw [if_neg h5, if_pos ht.2]

private lemma g_eq_piece7 (P : Params) {t : ℝ}
    (ht : t ∈ Set.Icc (2 * Real.pi - P.δ / 2) (2 * Real.pi)) :
    g P t = lin (2 * Real.pi - P.δ / 2) (2 * Real.pi) (-Hval P) 0 t := by
  have h1 : ¬ t ≤ P.δ := by linarith [ht.1, P.h2π, P.hδη, P.hδ_pos]
  have h2 : ¬ t ≤ P.η := by linarith [ht.1, P.h2π, P.hδη, P.hδ_pos]
  have h3 : ¬ t ≤ 2 * Real.pi - P.η - P.δ := by linarith [ht.1, P.hδη, P.hδ_pos]
  have h4 : ¬ t ≤ 2 * Real.pi - 2 * P.δ := by linarith [ht.1, P.hδ_pos]
  have h5 : ¬ t ≤ 2 * Real.pi - P.δ := by linarith [ht.1, P.hδ_pos]
  unfold g
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]
  by_cases h6 : t ≤ 2 * Real.pi - P.δ / 2
  · have hteq : t = 2 * Real.pi - P.δ / 2 := le_antisymm h6 ht.1
    rw [if_pos h6, hteq, lin_right (by linarith [P.hδ_pos]), lin_left]
  · rw [if_neg h6]

private lemma g_zero (P : Params) : g P 0 = 0 := by
  rw [g_eq_piece1 P ⟨le_rfl, P.hδ_pos.le⟩, lin_left]

private lemma g_two_pi (P : Params) : g P (2 * Real.pi) = 0 := by
  rw [g_eq_piece7 P ⟨by linarith [P.hδ_pos], le_rfl⟩, lin_right (by linarith [P.hδ_pos])]

private lemma continuousOn_Icc_union {a b c : ℝ} {f : ℝ → ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : ContinuousOn f (Set.Icc a b)) (h2 : ContinuousOn f (Set.Icc b c)) :
    ContinuousOn f (Set.Icc a c) := by
  have hun : Set.Icc a c = Set.Icc a b ∪ Set.Icc b c := (Set.Icc_union_Icc_eq_Icc hab hbc).symm
  rw [hun]
  exact h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc

private lemma continuousOn_g (P : Params) : ContinuousOn (g P) (Set.Icc 0 (2 * Real.pi)) := by
  have c1 : ContinuousOn (g P) (Set.Icc 0 P.δ) :=
    (continuous_lin _ _ _ _).continuousOn.congr (fun t ht => g_eq_piece1 P ht)
  have c2 : ContinuousOn (g P) (Set.Icc P.δ P.η) :=
    (continuous_lin _ _ _ _).continuousOn.congr (fun t ht => g_eq_piece2 P ht)
  have c3 : ContinuousOn (g P) (Set.Icc P.η (2 * Real.pi - P.η - P.δ)) :=
    continuousOn_const.congr (fun t ht => g_eq_piece3 P ht)
  have c4 : ContinuousOn (g P) (Set.Icc (2 * Real.pi - P.η - P.δ) (2 * Real.pi - 2 * P.δ)) :=
    (continuous_lin _ _ _ _).continuousOn.congr (fun t ht => g_eq_piece4 P ht)
  have c5 : ContinuousOn (g P) (Set.Icc (2 * Real.pi - 2 * P.δ) (2 * Real.pi - P.δ)) :=
    (continuous_lin _ _ _ _).continuousOn.congr (fun t ht => g_eq_piece5 P ht)
  have c6 : ContinuousOn (g P) (Set.Icc (2 * Real.pi - P.δ) (2 * Real.pi - P.δ / 2)) :=
    (continuous_lin _ _ _ _).continuousOn.congr (fun t ht => g_eq_piece6 P ht)
  have c7 : ContinuousOn (g P) (Set.Icc (2 * Real.pi - P.δ / 2) (2 * Real.pi)) :=
    (continuous_lin _ _ _ _).continuousOn.congr (fun t ht => g_eq_piece7 P ht)
  have h12 := continuousOn_Icc_union P.hδ_pos.le (by linarith [P.hδη, P.hδ_pos]) c1 c2
  have h13 := continuousOn_Icc_union (by linarith [P.hδη, P.hδ_pos]) (by linarith [P.h2π, P.hδ_pos]) h12 c3
  have h14 := continuousOn_Icc_union (by linarith [P.h2π, P.hη_pos, P.hδ_pos]) (by linarith [P.hδη, P.hδ_pos]) h13 c4
  have h15 := continuousOn_Icc_union (by linarith [P.h2π, P.hη_pos, P.hδ_pos]) (by linarith [P.hδ_pos]) h14 c5
  have h16 := continuousOn_Icc_union (by linarith [P.h2π, P.hη_pos, P.hδ_pos]) (by linarith [P.hδ_pos]) h15 c6
  exact continuousOn_Icc_union (by linarith [P.h2π, P.hη_pos, P.hδ_pos]) (by linarith [P.hδ_pos]) h16 c7

private lemma g_nonneg_pos (P : Params) {t : ℝ} (ht : t ∈ Set.Icc 0 (2 * Real.pi - P.δ)) :
    0 ≤ g P t := by
  by_cases h1 : t ≤ P.δ
  · rw [g_eq_piece1 P ⟨ht.1, h1⟩]
    have hb := (lin_mem_bounds (va := 0) (vb := B0) P.hδ_pos ⟨ht.1, h1⟩).1
    unfold B0 at *; linarith [min_eq_left (by norm_num : (0 : ℝ) ≤ 128)]
  · push Not at h1
    by_cases h2 : t ≤ P.η
    · rw [g_eq_piece2 P ⟨h1.le, h2⟩]
      have hb := (lin_mem_bounds (va := B0) (vb := 1) (by linarith [P.hδη, P.hδ_pos]) ⟨h1.le, h2⟩).1
      unfold B0 at *; linarith [min_eq_right (by norm_num : (1 : ℝ) ≤ 128)]
    · push Not at h2
      by_cases h3 : t ≤ 2 * Real.pi - P.η - P.δ
      · rw [g_eq_piece3 P ⟨h2.le, h3⟩]; norm_num
      · push Not at h3
        by_cases h4 : t ≤ 2 * Real.pi - 2 * P.δ
        · rw [g_eq_piece4 P ⟨h3.le, h4⟩]
          have hb := (lin_mem_bounds (va := 1) (vb := B0) (by linarith [P.hδη, P.hδ_pos]) ⟨h3.le, h4⟩).1
          unfold B0 at *; linarith [min_eq_left (by norm_num : (1 : ℝ) ≤ 128)]
        · push Not at h4
          rw [g_eq_piece5 P ⟨h4.le, ht.2⟩]
          have hb := (lin_mem_bounds (va := B0) (vb := 0) (by linarith [P.hδ_pos]) ⟨h4.le, ht.2⟩).1
          unfold B0 at *; linarith [min_eq_right (by norm_num : (0 : ℝ) ≤ 128)]

private lemma g_le_B0_pos (P : Params) {t : ℝ} (ht : t ∈ Set.Icc 0 (2 * Real.pi - P.δ)) :
    g P t ≤ B0 := by
  by_cases h1 : t ≤ P.δ
  · rw [g_eq_piece1 P ⟨ht.1, h1⟩]
    have hb := (lin_mem_bounds (va := 0) (vb := B0) P.hδ_pos ⟨ht.1, h1⟩).2
    unfold B0 at *; linarith [max_eq_right (by norm_num : (0 : ℝ) ≤ 128)]
  · push Not at h1
    by_cases h2 : t ≤ P.η
    · rw [g_eq_piece2 P ⟨h1.le, h2⟩]
      have hb := (lin_mem_bounds (va := B0) (vb := 1) (by linarith [P.hδη, P.hδ_pos]) ⟨h1.le, h2⟩).2
      unfold B0 at *; linarith [max_eq_left (by norm_num : (1 : ℝ) ≤ 128)]
    · push Not at h2
      by_cases h3 : t ≤ 2 * Real.pi - P.η - P.δ
      · rw [g_eq_piece3 P ⟨h2.le, h3⟩]; unfold B0; norm_num
      · push Not at h3
        by_cases h4 : t ≤ 2 * Real.pi - 2 * P.δ
        · rw [g_eq_piece4 P ⟨h3.le, h4⟩]
          have hb := (lin_mem_bounds (va := 1) (vb := B0) (by linarith [P.hδη, P.hδ_pos]) ⟨h3.le, h4⟩).2
          unfold B0 at *; linarith [max_eq_right (by norm_num : (1 : ℝ) ≤ 128)]
        · push Not at h4
          rw [g_eq_piece5 P ⟨h4.le, ht.2⟩]
          have hb := (lin_mem_bounds (va := B0) (vb := 0) (by linarith [P.hδ_pos]) ⟨h4.le, ht.2⟩).2
          unfold B0 at *; linarith [max_eq_left (by norm_num : (0 : ℝ) ≤ 128)]

private lemma g_nonpos_neg (P : Params) {t : ℝ} (ht : t ∈ Set.Icc (2 * Real.pi - P.δ) (2 * Real.pi)) :
    g P t ≤ 0 := by
  have hH : 0 < Hval P := Hval_pos P
  by_cases h6 : t ≤ 2 * Real.pi - P.δ / 2
  · rw [g_eq_piece6 P ⟨ht.1, h6⟩]
    have hb := (lin_mem_bounds (va := 0) (vb := -Hval P) (by linarith [P.hδ_pos]) ⟨ht.1, h6⟩).2
    rw [max_eq_left (by linarith)] at hb; exact hb
  · push Not at h6
    rw [g_eq_piece7 P ⟨h6.le, ht.2⟩]
    have hb := (lin_mem_bounds (va := -Hval P) (vb := 0) (by linarith [P.hδ_pos]) ⟨h6.le, ht.2⟩).2
    rw [max_eq_right (by linarith)] at hb; exact hb

private lemma g_ge_neg_H (P : Params) {t : ℝ} (ht : t ∈ Set.Icc (2 * Real.pi - P.δ) (2 * Real.pi)) :
    -Hval P ≤ g P t := by
  have hH : 0 < Hval P := Hval_pos P
  by_cases h6 : t ≤ 2 * Real.pi - P.δ / 2
  · rw [g_eq_piece6 P ⟨ht.1, h6⟩]
    have hb := (lin_mem_bounds (va := 0) (vb := -Hval P) (by linarith [P.hδ_pos]) ⟨ht.1, h6⟩).1
    rw [min_eq_right (by linarith)] at hb; exact hb
  · push Not at h6
    rw [g_eq_piece7 P ⟨h6.le, ht.2⟩]
    have hb := (lin_mem_bounds (va := -Hval P) (vb := 0) (by linarith [P.hδ_pos]) ⟨h6.le, ht.2⟩).1
    rw [min_eq_left (by linarith)] at hb; exact hb

private lemma g_ge_one_good (P : Params) {t : ℝ} (ht : t ∈ Set.Icc P.δ (2 * Real.pi - 2 * P.δ)) :
    1 ≤ g P t := by
  by_cases h2 : t ≤ P.η
  · rw [g_eq_piece2 P ⟨ht.1, h2⟩]
    have hb := (lin_mem_bounds (va := B0) (vb := 1) (by linarith [P.hδη, P.hδ_pos]) ⟨ht.1, h2⟩).1
    unfold B0 at *; linarith [min_eq_right (by norm_num : (1 : ℝ) ≤ 128)]
  · push Not at h2
    by_cases h3 : t ≤ 2 * Real.pi - P.η - P.δ
    · rw [g_eq_piece3 P ⟨h2.le, h3⟩]
    · push Not at h3
      rw [g_eq_piece4 P ⟨h3.le, ht.2⟩]
      have hb := (lin_mem_bounds (va := 1) (vb := B0) (by linarith [P.hδη, P.hδ_pos]) ⟨h3.le, ht.2⟩).1
      unfold B0 at *; linarith [min_eq_left (by norm_num : (1 : ℝ) ≤ 128)]

private lemma g_ge_64_left (P : Params) {t : ℝ} (ht : t ∈ Set.Icc P.δ (P.δ + 2 * P.h)) :
    64 ≤ g P t := by
  have ht2 : t ≤ P.η := by linarith [ht.2, P.hh_small, P.hδη, P.hδ_pos]
  rw [g_eq_piece2 P ⟨ht.1, ht2⟩]
  unfold lin B0
  have hden : 0 < P.η - P.δ := by linarith [P.hδη, P.hδ_pos]
  have hfrac : (t - P.δ) / (P.η - P.δ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hden (by norm_num)]
    linarith [ht.2, P.hh_small]
  nlinarith

private lemma g_ge_64_right (P : Params) {t : ℝ}
    (ht : t ∈ Set.Icc (2 * Real.pi - 2 * P.δ - 2 * P.h) (2 * Real.pi - 2 * P.δ)) :
    64 ≤ g P t := by
  have ht3 : 2 * Real.pi - P.η - P.δ ≤ t := by linarith [ht.1, P.hh_small, P.hδη, P.hδ_pos]
  rw [g_eq_piece4 P ⟨ht3, ht.2⟩]
  unfold lin B0
  have hden : 0 < (2 * Real.pi - 2 * P.δ) - (2 * Real.pi - P.η - P.δ) := by
    linarith [P.hδη, P.hδ_pos]
  have hfrac : 1 / 2 ≤ (t - (2 * Real.pi - P.η - P.δ)) /
      ((2 * Real.pi - 2 * P.δ) - (2 * Real.pi - P.η - P.δ)) := by
    rw [div_le_div_iff₀ (by norm_num) hden]
    linarith [ht.1, P.hh_small]
  nlinarith

private lemma g_lip_good (P : Params) {x y : ℝ}
    (hx : x ∈ Set.Icc P.δ (2 * Real.pi - 2 * P.δ))
    (hy : y ∈ Set.Icc P.δ (2 * Real.pi - 2 * P.δ)) :
    |g P x - g P y| ≤ (2 * B0 / P.η) * |x - y| := by
  set L : ℝ := 2 * B0 / P.η
  have hL_nn : 0 ≤ L := div_nonneg (by unfold B0; norm_num) P.hη_pos.le
  have hslope : (B0 - 1) / (P.η - P.δ) ≤ L := by
    dsimp [L]
    unfold B0
    have h1 : 0 < P.η - P.δ := by linarith [P.hδη, P.hδ_pos]
    rw [div_le_div_iff₀ h1 P.hη_pos]
    linarith [P.hδη, P.hδ_pos]
  have hpiece : ∀ u v, u ≤ v → u ∈ Set.Icc P.δ (2 * Real.pi - 2 * P.δ) →
      v ∈ Set.Icc P.δ (2 * Real.pi - 2 * P.δ) → |g P u - g P v| ≤ L * (v - u) := by
    set t2 := P.η
    set t3 := 2 * Real.pi - P.η - P.δ
    have ht12 : P.δ < t2 := by dsimp [t2]; linarith [P.hδη, P.hδ_pos]
    have ht23 : t2 < t3 := by dsimp [t2, t3]; linarith [P.h2π, P.hδ_pos]
    have ht34 : t3 < 2 * Real.pi - 2 * P.δ := by dsimp [t3]; linarith [P.hδη, P.hδ_pos]
    have hP2 : ∀ a b, a ∈ Set.Icc P.δ t2 → b ∈ Set.Icc P.δ t2 → a ≤ b →
        |g P a - g P b| ≤ L * (b - a) := by
      intro a b ha hb hab
      rw [g_eq_piece2 P ha, g_eq_piece2 P hb, lin_abs_sub,
        show |a - b| = b - a by rw [abs_of_nonpos (by linarith)]; ring]
      gcongr
      rw [show (1 - B0) / (P.η - P.δ) = -((B0 - 1) / (P.η - P.δ)) by ring, abs_neg,
        abs_of_nonneg (div_nonneg (by unfold B0; norm_num) (by linarith [P.hδη, P.hδ_pos]))]
      exact hslope
    have hP3 : ∀ a b, a ∈ Set.Icc t2 t3 → b ∈ Set.Icc t2 t3 → a ≤ b →
        |g P a - g P b| ≤ L * (b - a) := by
      intro a b ha hb hab
      rw [g_eq_piece3 P ha, g_eq_piece3 P hb, sub_self, abs_zero]
      exact mul_nonneg hL_nn (sub_nonneg.mpr hab)
    have hP4 : ∀ a b, a ∈ Set.Icc t3 (2 * Real.pi - 2 * P.δ) →
        b ∈ Set.Icc t3 (2 * Real.pi - 2 * P.δ) → a ≤ b →
        |g P a - g P b| ≤ L * (b - a) := by
      intro a b ha hb hab
      rw [g_eq_piece4 P ha, g_eq_piece4 P hb, lin_abs_sub,
        show |a - b| = b - a by rw [abs_of_nonpos (by linarith)]; ring]
      gcongr
      rw [show (2 * Real.pi - 2 * P.δ) - (2 * Real.pi - P.η - P.δ) = P.η - P.δ by ring,
        abs_of_nonneg (div_nonneg (by unfold B0; norm_num) (by linarith [P.hδη, P.hδ_pos]))]
      exact hslope
    intro u v huv hu hv
    by_cases hv2 : v ≤ t2
    · exact hP2 u v ⟨hu.1, huv.trans hv2⟩ ⟨hu.1.trans huv, hv2⟩ huv
    · push Not at hv2
      by_cases hu2 : u ≤ t2
      · by_cases hv3 : v ≤ t3
        · calc |g P u - g P v|
              ≤ |g P u - g P t2| + |g P t2 - g P v| := abs_sub_le _ _ _
            _ ≤ L * (t2 - u) + L * (v - t2) :=
                add_le_add (hP2 u t2 ⟨hu.1, hu2⟩ ⟨ht12.le, le_rfl⟩ hu2)
                  (hP3 t2 v ⟨le_rfl, ht23.le⟩ ⟨hv2.le, hv3⟩ hv2.le)
            _ = L * (v - u) := by ring
        · push Not at hv3
          calc |g P u - g P v|
              ≤ |g P u - g P t2| + |g P t2 - g P t3| + |g P t3 - g P v| := by
                linarith [abs_sub_le (g P u) (g P t2) (g P v), abs_sub_le (g P t2) (g P t3) (g P v)]
            _ ≤ L * (t2 - u) + L * (t3 - t2) + L * (v - t3) := by
                gcongr
                · exact hP2 u t2 ⟨hu.1, hu2⟩ ⟨ht12.le, le_rfl⟩ hu2
                · exact hP3 t2 t3 ⟨le_rfl, ht23.le⟩ ⟨ht23.le, le_rfl⟩ ht23.le
                · exact hP4 t3 v ⟨le_rfl, ht34.le⟩ ⟨hv3.le, hv.2⟩ hv3.le
            _ = L * (v - u) := by ring
      · push Not at hu2
        by_cases hv3 : v ≤ t3
        · exact hP3 u v ⟨hu2.le, huv.trans hv3⟩ ⟨hu2.le.trans huv, hv3⟩ huv
        · push Not at hv3
          by_cases hu3 : u ≤ t3
          · calc |g P u - g P v|
                ≤ |g P u - g P t3| + |g P t3 - g P v| := abs_sub_le _ _ _
              _ ≤ L * (t3 - u) + L * (v - t3) :=
                  add_le_add (hP3 u t3 ⟨hu2.le, hu3⟩ ⟨ht23.le, le_rfl⟩ hu3)
                    (hP4 t3 v ⟨le_rfl, ht34.le⟩ ⟨hv3.le, hv.2⟩ hv3.le)
              _ = L * (v - u) := by ring
          · push Not at hu3
            exact hP4 u v ⟨hu3.le, hu.2⟩ ⟨hu3.le.trans huv, hv.2⟩ huv
  by_cases hxy : x ≤ y
  · rw [show |x - y| = y - x by rw [abs_of_nonpos (by linarith)]; ring]
    exact hpiece x y hxy hx hy
  · push Not at hxy
    rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hxy)]
    exact hpiece y x hxy.le hy hx

private lemma integral_g_pos_part (P : Params) :
    ∫ t in (0 : ℝ)..(2 * Real.pi - P.δ), g P t = posArea P := by
  have hint : ∀ a b, a ∈ Set.Icc 0 (2 * Real.pi) → b ∈ Set.Icc 0 (2 * Real.pi) →
      IntervalIntegrable (g P) volume a b := fun a b ha hb =>
    ((continuousOn_g P).mono (Set.uIcc_subset_Icc ha hb)).intervalIntegrable
  let t1 := P.δ
  let t2 := P.η
  let t3 := 2 * Real.pi - P.η - P.δ
  let t4 := 2 * Real.pi - 2 * P.δ
  let t5 := 2 * Real.pi - P.δ
  have m0 : (0 : ℝ) ∈ Set.Icc 0 (2 * Real.pi) := ⟨le_rfl, by positivity⟩
  have m1 : t1 ∈ Set.Icc 0 (2 * Real.pi) := ⟨P.hδ_pos.le, by dsimp [t1]; linarith [P.h2π, P.hη_pos, P.hδ_pos]⟩
  have m2 : t2 ∈ Set.Icc 0 (2 * Real.pi) := ⟨P.hη_pos.le, by dsimp [t2]; linarith [P.h2π, P.hη_pos, P.hδ_pos]⟩
  have m3 : t3 ∈ Set.Icc 0 (2 * Real.pi) := ⟨by dsimp [t3]; linarith [P.h2π, P.hη_pos, P.hδ_pos], by dsimp [t3]; linarith [P.hη_pos, P.hδ_pos]⟩
  have m4 : t4 ∈ Set.Icc 0 (2 * Real.pi) := ⟨by dsimp [t4]; linarith [P.h2π, P.hη_pos, P.hδ_pos], by dsimp [t4]; linarith [P.hδ_pos]⟩
  have m5 : t5 ∈ Set.Icc 0 (2 * Real.pi) := ⟨by dsimp [t5]; linarith [P.h2π, P.hη_pos, P.hδ_pos], by dsimp [t5]; linarith [P.hδ_pos]⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 t4 m0 m4) (hint t4 t5 m4 m5),
      ← intervalIntegral.integral_add_adjacent_intervals (hint 0 t3 m0 m3) (hint t3 t4 m3 m4),
      ← intervalIntegral.integral_add_adjacent_intervals (hint 0 t2 m0 m2) (hint t2 t3 m2 m3),
      ← intervalIntegral.integral_add_adjacent_intervals (hint 0 t1 m0 m1) (hint t1 t2 m1 m2)]
  have i1 : ∫ t in (0 : ℝ)..t1, g P t = P.δ * B0 / 2 := by
    have hc : ∫ t in (0 : ℝ)..t1, g P t = ∫ t in (0 : ℝ)..P.δ, lin 0 P.δ 0 B0 t :=
      intervalIntegral.integral_congr fun t ht => by
        rw [Set.uIcc_of_le P.hδ_pos.le] at ht; exact g_eq_piece1 P ht
    rw [hc, integral_lin P.hδ_pos.ne]
    ring
  have i2 : ∫ t in t1..t2, g P t = (P.η - P.δ) * (B0 + 1) / 2 := by
    have hc : ∫ t in t1..t2, g P t = ∫ t in P.δ..P.η, lin P.δ P.η B0 1 t :=
      intervalIntegral.integral_congr fun t ht => by
        rw [Set.uIcc_of_le (by linarith [P.hδη, P.hδ_pos])] at ht; exact g_eq_piece2 P ht
    rw [hc, integral_lin (by linarith [P.hδη, P.hδ_pos])]
  have i3 : ∫ t in t2..t3, g P t = (2 * Real.pi - 2 * P.η - P.δ) := by
    have hc : ∫ t in t2..t3, g P t = ∫ _ in P.η..(2 * Real.pi - P.η - P.δ), (1 : ℝ) :=
      intervalIntegral.integral_congr fun t ht => by
        rw [Set.uIcc_of_le (by linarith [P.h2π, P.hδ_pos])] at ht; exact g_eq_piece3 P ht
    rw [hc, intervalIntegral.integral_const, smul_eq_mul, mul_one]
    ring
  have i4 : ∫ t in t3..t4, g P t = (P.η - P.δ) * (1 + B0) / 2 := by
    have hc : ∫ t in t3..t4, g P t =
        ∫ t in (2 * Real.pi - P.η - P.δ)..(2 * Real.pi - 2 * P.δ),
          lin (2 * Real.pi - P.η - P.δ) (2 * Real.pi - 2 * P.δ) 1 B0 t :=
      intervalIntegral.integral_congr fun t ht => by
        rw [Set.uIcc_of_le (by linarith [P.hδη, P.hδ_pos])] at ht; exact g_eq_piece4 P ht
    rw [hc, integral_lin (by linarith [P.hδη, P.hδ_pos])]
    ring
  have i5 : ∫ t in t4..t5, g P t = P.δ * B0 / 2 := by
    have hc : ∫ t in t4..t5, g P t =
        ∫ t in (2 * Real.pi - 2 * P.δ)..(2 * Real.pi - P.δ),
          lin (2 * Real.pi - 2 * P.δ) (2 * Real.pi - P.δ) B0 0 t :=
      intervalIntegral.integral_congr fun t ht => by
        rw [Set.uIcc_of_le (by linarith [P.hδ_pos])] at ht; exact g_eq_piece5 P ht
    rw [hc, integral_lin (by linarith [P.hδ_pos])]
    ring
  rw [i1, i2, i3, i4, i5]
  unfold posArea
  ring

private lemma integral_g_neg_part (P : Params) :
    ∫ t in (2 * Real.pi - P.δ)..(2 * Real.pi), g P t = -posArea P := by
  have hint : ∀ a b, a ∈ Set.Icc 0 (2 * Real.pi) → b ∈ Set.Icc 0 (2 * Real.pi) →
      IntervalIntegrable (g P) volume a b := fun a b ha hb =>
    ((continuousOn_g P).mono (Set.uIcc_subset_Icc ha hb)).intervalIntegrable
  let t5 := 2 * Real.pi - P.δ
  let tm := 2 * Real.pi - P.δ / 2
  let t6 := 2 * Real.pi
  have m5 : t5 ∈ Set.Icc 0 (2 * Real.pi) := ⟨by dsimp [t5]; linarith [P.h2π, P.hη_pos, P.hδ_pos], by dsimp [t5]; linarith [P.hδ_pos]⟩
  have mm : tm ∈ Set.Icc 0 (2 * Real.pi) := ⟨by dsimp [tm]; linarith [P.h2π, P.hη_pos, P.hδ_pos], by dsimp [tm]; linarith [P.hδ_pos]⟩
  have m6 : t6 ∈ Set.Icc 0 (2 * Real.pi) := ⟨by positivity, le_rfl⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint t5 tm m5 mm) (hint tm t6 mm m6)]
  have i6 : ∫ t in t5..tm, g P t = -(P.δ / 2) * Hval P / 2 := by
    have hc : ∫ t in t5..tm, g P t =
        ∫ t in (2 * Real.pi - P.δ)..(2 * Real.pi - P.δ / 2),
          lin (2 * Real.pi - P.δ) (2 * Real.pi - P.δ / 2) 0 (-Hval P) t :=
      intervalIntegral.integral_congr fun t ht => by
        rw [Set.uIcc_of_le (by dsimp [t5, tm]; linarith [P.hδ_pos])] at ht; exact g_eq_piece6 P ht
    rw [hc, integral_lin (by linarith [P.hδ_pos])]
    ring
  have i7 : ∫ t in tm..t6, g P t = -(P.δ / 2) * Hval P / 2 := by
    have hc : ∫ t in tm..t6, g P t =
        ∫ t in (2 * Real.pi - P.δ / 2)..(2 * Real.pi),
          lin (2 * Real.pi - P.δ / 2) (2 * Real.pi) (-Hval P) 0 t :=
      intervalIntegral.integral_congr fun t ht => by
        rw [Set.uIcc_of_le (by dsimp [tm, t6]; linarith [P.hδ_pos])] at ht; exact g_eq_piece7 P ht
    rw [hc, integral_lin (by linarith [P.hδ_pos])]
    ring
  rw [i6, i7]
  unfold Hval
  field_simp [P.hδ_pos.ne']
  ring

private lemma integral_g_full (P : Params) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), g P t = 0 := by
  have hint : ∀ a b, a ∈ Set.Icc 0 (2 * Real.pi) → b ∈ Set.Icc 0 (2 * Real.pi) →
      IntervalIntegrable (g P) volume a b := fun a b ha hb =>
    ((continuousOn_g P).mono (Set.uIcc_subset_Icc ha hb)).intervalIntegrable
  have m0 : (0 : ℝ) ∈ Set.Icc 0 (2 * Real.pi) := ⟨le_rfl, by positivity⟩
  have m5 : 2 * Real.pi - P.δ ∈ Set.Icc 0 (2 * Real.pi) :=
    ⟨by linarith [P.h2π, P.hη_pos, P.hδ_pos], by linarith [P.hδ_pos]⟩
  have m6 : 2 * Real.pi ∈ Set.Icc 0 (2 * Real.pi) := ⟨by positivity, le_rfl⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 _ m0 m5) (hint _ _ m5 m6),
      integral_g_pos_part P, integral_g_neg_part P, add_neg_cancel]

private lemma continuous_g (P : Params) : Continuous (g P) := by
  have hle : ContinuousOn (g P) (Set.Iic P.δ) :=
    (continuous_lin 0 P.δ 0 B0).continuousOn.congr (fun x hx => by
      have hx' : x ≤ P.δ := hx
      unfold g; rw [if_pos hx'])
  have hge : ContinuousOn (g P) (Set.Ici (2 * Real.pi - P.δ / 2)) :=
    (continuous_lin (2 * Real.pi - P.δ / 2) (2 * Real.pi) (-Hval P) 0).continuousOn.congr
      (fun x hx => by
        have hx' : 2 * Real.pi - P.δ / 2 ≤ x := hx
        have h1 : ¬ x ≤ P.δ := by linarith [hx', P.h2π, P.hδη, P.hδ_pos]
        have h2 : ¬ x ≤ P.η := by linarith [hx', P.h2π, P.hδη, P.hδ_pos]
        have h3 : ¬ x ≤ 2 * Real.pi - P.η - P.δ := by linarith [hx', P.hδη, P.hδ_pos]
        have h4 : ¬ x ≤ 2 * Real.pi - 2 * P.δ := by linarith [hx', P.hδ_pos]
        have h5 : ¬ x ≤ 2 * Real.pi - P.δ := by linarith [hx', P.hδ_pos]
        unfold g
        rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]
        by_cases h6 : x ≤ 2 * Real.pi - P.δ / 2
        · have hxeq : x = 2 * Real.pi - P.δ / 2 := le_antisymm h6 hx'
          rw [if_pos h6, hxeq, lin_right (by linarith [P.hδ_pos]), lin_left]
        · rw [if_neg h6])
  have hu1 := hle.union_of_isClosed (continuousOn_g P) isClosed_Iic isClosed_Icc
  have hu2 := hu1.union_of_isClosed hge (isClosed_Iic.union isClosed_Icc) isClosed_Ici
  have huniv : (Set.Iic P.δ ∪ Set.Icc 0 (2 * Real.pi)) ∪ Set.Ici (2 * Real.pi - P.δ / 2) = Set.univ := by
    ext x; simp only [Set.mem_union, Set.mem_Iic, Set.mem_Icc, Set.mem_Ici, Set.mem_univ, iff_true]
    by_cases hx1 : x ≤ P.δ
    · exact Or.inl (Or.inl hx1)
    · by_cases hx2 : x ≤ 2 * Real.pi
      · exact Or.inl (Or.inr ⟨by linarith [P.hδ_pos], hx2⟩)
      · exact Or.inr (by linarith [P.hδ_pos])
  rw [huniv] at hu2
  exact continuousOn_univ.mp hu2

private noncomputable def ψ0 (P : Params) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, g P s

private lemma hasDerivAt_ψ0 (P : Params) (t : ℝ) :
    HasDerivAt (ψ0 P) (g P t) t :=
  intervalIntegral.integral_hasDerivAt_right ((continuous_g P).intervalIntegrable 0 t)
    ((continuous_g P).stronglyMeasurableAtFilter volume (𝓝 t)) (continuous_g P).continuousAt

private lemma ψ0_zero (P : Params) : ψ0 P 0 = 0 := by
  simp [ψ0]

private lemma ψ0_two_pi (P : Params) : ψ0 P (2 * Real.pi) = 0 :=
  integral_g_full P

private lemma ψ0_bounds (P : Params) {t : ℝ} (ht : t ∈ Set.Icc 0 (2 * Real.pi)) :
    0 ≤ ψ0 P t ∧ ψ0 P t ≤ posArea P := by
  have hint : ∀ a b, a ∈ Set.Icc 0 (2 * Real.pi) → b ∈ Set.Icc 0 (2 * Real.pi) →
      IntervalIntegrable (g P) volume a b := fun a b ha hb =>
    ((continuousOn_g P).mono (Set.uIcc_subset_Icc ha hb)).intervalIntegrable
  let t5 := 2 * Real.pi - P.δ
  have m0 : (0 : ℝ) ∈ Set.Icc 0 (2 * Real.pi) := ⟨le_rfl, by positivity⟩
  have m5 : t5 ∈ Set.Icc 0 (2 * Real.pi) :=
    ⟨by dsimp [t5]; linarith [P.h2π, P.hη_pos, P.hδ_pos], by dsimp [t5]; linarith [P.hδ_pos]⟩
  have m6 : 2 * Real.pi ∈ Set.Icc 0 (2 * Real.pi) := ⟨by positivity, le_rfl⟩
  by_cases ht5 : t ≤ t5
  · constructor
    · exact intervalIntegral.integral_nonneg ht.1 (fun x hx => g_nonneg_pos P ⟨hx.1, hx.2.trans ht5⟩)
    · have hadd := intervalIntegral.integral_add_adjacent_intervals (hint 0 t m0 ht) (hint t t5 ht m5)
      have hnn : 0 ≤ ∫ s in t..t5, g P s :=
        intervalIntegral.integral_nonneg ht5 (fun x hx => g_nonneg_pos P ⟨ht.1.trans hx.1, hx.2⟩)
      have hpos := integral_g_pos_part P
      unfold ψ0; linarith
  · push Not at ht5
    constructor
    · have hadd := intervalIntegral.integral_add_adjacent_intervals (hint 0 t m0 ht) (hint t (2 * Real.pi) ht m6)
      have hnp : ∫ s in t..(2 * Real.pi), g P s ≤ 0 := by
        have hneg : 0 ≤ ∫ s in t..(2 * Real.pi), -g P s :=
          intervalIntegral.integral_nonneg ht.2 (fun x hx => neg_nonneg.mpr (g_nonpos_neg P ⟨ht5.le.trans hx.1, hx.2⟩))
        rw [intervalIntegral.integral_neg] at hneg
        linarith
      have hfull := integral_g_full P
      unfold ψ0; linarith
    · have hadd := intervalIntegral.integral_add_adjacent_intervals (hint 0 t5 m0 m5) (hint t5 t m5 ht)
      have hnp : ∫ s in t5..t, g P s ≤ 0 := by
        have hneg : 0 ≤ ∫ s in t5..t, -g P s :=
          intervalIntegral.integral_nonneg ht5.le (fun x hx => neg_nonneg.mpr (g_nonpos_neg P ⟨hx.1, hx.2.trans ht.2⟩))
        rw [intervalIntegral.integral_neg] at hneg
        linarith
      have hpos := integral_g_pos_part P
      unfold ψ0; linarith

private noncomputable def meanPsi (P : Params) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ s in (0 : ℝ)..(2 * Real.pi), P.A * ψ0 P s

private noncomputable def KInt (P : Params) : ℤ :=
  ⌈meanPsi P⌉

private noncomputable def shiftVal (P : Params) : ℝ :=
  (KInt P : ℝ) - meanPsi P

private lemma shiftVal_bounds (P : Params) : 0 ≤ shiftVal P ∧ shiftVal P < 1 := by
  unfold shiftVal KInt
  constructor
  · linarith [Int.le_ceil (meanPsi P)]
  · linarith [Int.ceil_lt_add_one (meanPsi P)]

private noncomputable def ψ (P : Params) (t : ℝ) : ℝ :=
  P.A * ψ0 P t + shiftVal P

private lemma hasDerivAt_ψ (P : Params) (t : ℝ) :
    HasDerivAt (ψ P) (P.A * g P t) t := by
  unfold ψ
  simpa using ((hasDerivAt_ψ0 P t).const_mul P.A).add_const (shiftVal P)

private lemma ψ_zero_eq_two_pi (P : Params) : ψ P 0 = ψ P (2 * Real.pi) := by
  simp [ψ, ψ0_zero, ψ0_two_pi]

private lemma ψ_bounds (P : Params) {t : ℝ} (ht : t ∈ Set.Icc 0 (2 * Real.pi)) :
    0 ≤ ψ P t ∧ ψ P t ≤ P.A * posArea P + 1 := by
  have h1 := ψ0_bounds P ht
  have h2 := shiftVal_bounds P
  unfold ψ
  constructor
  · nlinarith [P.hA_pos]
  · nlinarith [P.hA_pos]

private lemma continuous_ψ (P : Params) : Continuous (ψ P) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_ψ P t).continuousAt

private lemma integral_ψ_full (P : Params) :
    ∫ s in (0 : ℝ)..(2 * Real.pi), ψ P s = 2 * Real.pi * (KInt P : ℝ) := by
  have hint0 : IntervalIntegrable (fun s => P.A * ψ0 P s) volume 0 (2 * Real.pi) := by
    have hcont : Continuous (fun s => P.A * ψ0 P s) :=
      continuous_const.mul (continuous_iff_continuousAt.mpr fun t => (hasDerivAt_ψ0 P t).continuousAt)
    exact hcont.intervalIntegrable 0 (2 * Real.pi)
  unfold ψ
  rw [intervalIntegral.integral_add hint0 intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  unfold shiftVal meanPsi
  have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  field_simp [h2pi]
  ring

private noncomputable def φ (P : Params) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, ψ P s

private lemma hasDerivAt_φ (P : Params) (t : ℝ) :
    HasDerivAt (φ P) (ψ P t) t :=
  intervalIntegral.integral_hasDerivAt_right ((continuous_ψ P).intervalIntegrable 0 t)
    ((continuous_ψ P).stronglyMeasurableAtFilter volume (𝓝 t)) (continuous_ψ P).continuousAt

private lemma φ_zero (P : Params) : φ P 0 = 0 := by simp [φ]

private lemma φ_two_pi (P : Params) : φ P (2 * Real.pi) = 2 * Real.pi * (KInt P : ℝ) :=
  integral_ψ_full P

private lemma exp_I_φ_periodic (P : Params) :
    Complex.exp (Complex.I * (φ P (2 * Real.pi) : ℂ)) = Complex.exp (Complex.I * (φ P 0 : ℂ)) := by
  rw [φ_zero, φ_two_pi]
  push_cast
  rw [mul_zero, Complex.exp_zero]
  have h : Complex.I * (2 * (Real.pi : ℂ) * (KInt P : ℂ)) = (KInt P : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

/- ## Section 4: Fourier representation, uniform coefficient bound, tail bound, and Parseval -/

private lemma two_pi_pos_fact : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

private lemma continuous_φ (P : Params) : Continuous (φ P) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_φ P t).continuousAt

private noncomputable def fCircle (P : Params) : C(AddCircle (2 * Real.pi), ℂ) :=
  letI : Fact (0 < 2 * Real.pi) := two_pi_pos_fact
  ⟨AddCircle.liftIco (2 * Real.pi) 0 (fun t => Complex.exp (Complex.I * (φ P t : ℂ))),
   AddCircle.liftIco_continuous (by simpa [zero_add] using (exp_I_φ_periodic P).symm)
     (Complex.continuous_exp.comp
       (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_φ P)))).continuousOn⟩

private lemma exists_mem_Ico_addCircle (x : AddCircle (2 * Real.pi)) :
    ∃ t ∈ Set.Ico (0 : ℝ) (2 * Real.pi), (t : AddCircle (2 * Real.pi)) = x := by
  induction x using QuotientAddGroup.induction_on with
  | H y =>
    have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
    set m : ℤ := ⌊y / (2 * Real.pi)⌋
    set t : ℝ := y - (m : ℝ) * (2 * Real.pi)
    refine ⟨t, ⟨?_, ?_⟩, ?_⟩
    · have hm : (m : ℝ) ≤ y / (2 * Real.pi) := Int.floor_le _
      have := (le_div_iff₀ h2pi).mp hm
      dsimp [t]; linarith
    · have hm : y / (2 * Real.pi) < (m : ℝ) + 1 := Int.lt_floor_add_one _
      have := (div_lt_iff₀ h2pi).mp hm
      dsimp [t]; linarith
    · dsimp [t]
      rw [← QuotientAddGroup.mk_sub, QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff]
      refine ⟨m, ?_⟩
      simp only [zsmul_eq_mul]
      ring

private lemma fCircle_coe_apply (P : Params) {t : ℝ} (ht : t ∈ Set.Icc 0 (2 * Real.pi)) :
    fCircle P (t : AddCircle (2 * Real.pi)) = Complex.exp (Complex.I * (φ P t : ℂ)) := by
  have : Fact (0 < 2 * Real.pi) := two_pi_pos_fact
  by_cases hlt : t < 2 * Real.pi
  · change AddCircle.liftIco (2 * Real.pi) 0 (fun s => Complex.exp (Complex.I * (φ P s : ℂ)))
      (t : AddCircle (2 * Real.pi)) = _
    exact AddCircle.liftIco_coe_apply (p := 2 * Real.pi) (a := 0) (by rw [zero_add]; exact ⟨ht.1, hlt⟩)
  · have hteq : t = 2 * Real.pi := le_antisymm ht.2 (not_lt.mp hlt)
    rw [hteq]
    have hcoe : ((2 * Real.pi : ℝ) : AddCircle (2 * Real.pi)) = (0 : AddCircle (2 * Real.pi)) := by
      simp [AddCircle.coe_period]
    rw [hcoe]
    have h0 : fCircle P (0 : AddCircle (2 * Real.pi)) = Complex.exp (Complex.I * (φ P 0 : ℂ)) := by
      change AddCircle.liftIco (2 * Real.pi) 0 (fun s => Complex.exp (Complex.I * (φ P s : ℂ)))
        ((0 : ℝ) : AddCircle (2 * Real.pi)) = _
      exact AddCircle.liftIco_coe_apply (p := 2 * Real.pi) (a := 0)
        (by rw [zero_add]; exact ⟨le_rfl, by positivity⟩)
    rw [h0, exp_I_φ_periodic P]

private lemma fCircle_norm (P : Params) (x : AddCircle (2 * Real.pi)) : ‖fCircle P x‖ = 1 := by
  obtain ⟨t, ht, rfl⟩ := exists_mem_Ico_addCircle x
  rw [fCircle_coe_apply P ⟨ht.1, ht.2.le⟩, mul_comm]
  exact Complex.norm_exp_ofReal_mul_I (φ P t)

private lemma fourier_two_pi_apply (k : ℤ) (t : ℝ) :
    (fourier (T := 2 * Real.pi) k (t : AddCircle (2 * Real.pi)) : ℂ) =
      Complex.exp (Complex.I * (((k : ℝ) * t : ℝ) : ℂ)) := by
  rw [fourier_coe_apply]
  congr 1
  have h2pi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  push_cast
  field_simp [h2pi]

private lemma fourierCoeff_fCircle_eq (P : Params) (k : ℤ) :
    letI : Fact (0 < 2 * Real.pi) := two_pi_pos_fact
    fourierCoeff (fCircle P) k =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (0 : ℝ)..(2 * Real.pi),
        Complex.exp (Complex.I * ((φ P t - (k : ℝ) * t : ℝ) : ℂ)) := by
  have : Fact (0 < 2 * Real.pi) := two_pi_pos_fact
  rw [fourierCoeff_eq_intervalIntegral (fCircle P) k 0, zero_add, Complex.real_smul]
  congr 1
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le (by positivity)] at ht
  rw [smul_eq_mul, fCircle_coe_apply P ht, fourier_two_pi_apply (-k) t, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma fourierCoeff_fCircle_norm_le_one (P : Params) (k : ℤ) :
    letI : Fact (0 < 2 * Real.pi) := two_pi_pos_fact
    ‖fourierCoeff (fCircle P) k‖ ≤ 1 := by
  have : Fact (0 < 2 * Real.pi) := two_pi_pos_fact
  rw [fourierCoeff_fCircle_eq P k, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  have hbd := norm_integral_exp_I_le_length (a := 0) (b := 2 * Real.pi)
    (u := fun t => φ P t - (k : ℝ) * t) (by positivity)
  calc (1 / (2 * Real.pi)) * ‖∫ t in (0 : ℝ)..(2 * Real.pi),
        Complex.exp (Complex.I * ((φ P t - (k : ℝ) * t : ℝ) : ℂ))‖
      ≤ (1 / (2 * Real.pi)) * (2 * Real.pi - 0) :=
        mul_le_mul_of_nonneg_left hbd (by positivity)
    _ = 1 := by rw [sub_zero]; field_simp [Real.pi_pos.ne']

private lemma fourierCoeff_fCircle_norm_le (P : Params)
    (hstep : 3 / (P.A * P.h) ≤ 1 / √P.A) (k : ℤ) :
    letI : Fact (0 < 2 * Real.pi) := two_pi_pos_fact
    ‖fourierCoeff (fCircle P) k‖ ≤
      (1 / (2 * Real.pi)) * (√(2 * Real.pi / P.A) + 3 * P.δ + 10 / (P.A * P.h) +
        2 * (2 * B0 * P.A / P.η) * P.h ^ 4) := by
  have : Fact (0 < 2 * Real.pi) := two_pi_pos_fact
  rw [fourierCoeff_fCircle_eq P k, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  set u : ℝ → ℝ := fun t => φ P t - (k : ℝ) * t
  set u' : ℝ → ℝ := fun t => ψ P t - (k : ℝ)
  set u'' : ℝ → ℝ := fun t => P.A * g P t
  set E : ℝ → ℂ := fun t => Complex.exp (Complex.I * (u t : ℂ))
  have hu : ∀ t : ℝ, HasDerivAt u (u' t) t := fun t => by
    have hk : HasDerivAt (fun s : ℝ => (k : ℝ) * s) (k : ℝ) t := by
      simpa using (hasDerivAt_id t).const_mul (k : ℝ)
    exact (hasDerivAt_φ P t).sub hk
  have hu' : ∀ t : ℝ, HasDerivAt u' (u'' t) t := fun t => by
    exact (hasDerivAt_ψ P t).sub_const (k : ℝ)
  have hu''_cont : Continuous u'' := continuous_const.mul (continuous_g P)
  have hE_cont : Continuous E :=
    Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_iff_continuousAt.mpr fun t => (hu t).continuousAt)))
  have hsplit : ∫ t in (0 : ℝ)..(2 * Real.pi), E t =
      (∫ t in (0 : ℝ)..P.δ, E t) +
      (∫ t in P.δ..(2 * Real.pi - 2 * P.δ), E t) +
      (∫ t in (2 * Real.pi - 2 * P.δ)..(2 * Real.pi), E t) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hE_cont.intervalIntegrable _ _)
      (hE_cont.intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals (hE_cont.intervalIntegrable _ _)
      (hE_cont.intervalIntegrable _ _)]
  have hbad1 : ‖∫ t in (0 : ℝ)..P.δ, E t‖ ≤ P.δ := by
    simpa using norm_integral_exp_I_le_length (u := u) P.hδ_pos.le
  have hbad2 : ‖∫ t in (2 * Real.pi - 2 * P.δ)..(2 * Real.pi), E t‖ ≤ 2 * P.δ := by
    have h := norm_integral_exp_I_le_length (u := u) (a := 2 * Real.pi - 2 * P.δ)
      (b := 2 * Real.pi) (by linarith [P.hδ_pos])
    linarith
  set M3 : ℝ := 2 * B0 * P.A / P.η
  have hM3_nn : 0 ≤ M3 := by dsimp [M3]; unfold B0; have := P.hA_pos; have := P.hη_pos; positivity
  have hgood_bound : ‖∫ t in P.δ..(2 * Real.pi - 2 * P.δ), E t‖ ≤
      √(2 * Real.pi / P.A) + 10 / (P.A * P.h) + 2 * M3 * P.h ^ 4 := by
    set a := P.δ
    set b := 2 * Real.pi - 2 * P.δ
    have hab : a + 2 * P.h ≤ b - 2 * P.h := by
      dsimp [a, b]; linarith [P.h2π, P.hh_small, P.hδη, P.hδ_pos]
    have hlower : ∀ x ∈ Set.Icc a b, P.A ≤ u'' x := fun x hx => by
      have h1 : 1 ≤ g P x := g_ge_one_good P hx
      dsimp [u'']; nlinarith [P.hA_pos]
    have hnonneg : ∀ x ∈ Set.Icc a b, 0 ≤ u'' x := fun x hx => le_trans P.hA_pos.le (hlower x hx)
    have h2_le_sqrt : 2 / √P.A ≤ √(2 * Real.pi / P.A) := by
      have hsqA : 0 < √P.A := Real.sqrt_pos.mpr P.hA_pos
      have h4le : (4 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
      rw [Real.sqrt_div (by positivity)]
      gcongr
      calc (2 : ℝ) = √4 := by norm_num
        _ ≤ √(2 * Real.pi) := Real.sqrt_le_sqrt h4le
    have hAh_pos : 0 < P.A * P.h := mul_pos P.hA_pos P.hh_pos
    by_cases hL0 : 0 ≤ u' (a + P.h)
    · have hsp : ∫ t in a..b, E t = (∫ t in a..(a + 2 * P.h), E t) + (∫ t in (a + 2 * P.h)..b, E t) :=
        (intervalIntegral.integral_add_adjacent_intervals
          (hE_cont.intervalIntegrable _ _) (hE_cont.intervalIntegrable _ _)).symm
      rw [hsp]
      have h1 : ‖∫ t in a..(a + 2 * P.h), E t‖ ≤ 1 / √P.A := by
        have hvdc := osc_vdc2_bound (a := a) (b := a + 2 * P.h) (B := 64 * P.A)
          (by linarith [P.hh_pos]) (by have := P.hA_pos; positivity)
          (fun x _ => hu x) (fun x _ => hu' x) hu''_cont.continuousOn
          (fun x hx => by
            have hg := g_ge_64_left P hx
            dsimp [u'']; nlinarith [P.hA_pos])
        have hsqrt64 : √(64 * P.A) = 8 * √P.A := by
          rw [Real.sqrt_mul (by norm_num)]
          norm_num
        rw [hsqrt64] at hvdc
        calc ‖∫ t in a..(a + 2 * P.h), E t‖
            ≤ 8 / (8 * √P.A) := hvdc
          _ = 1 / √P.A := by
              have hs : √P.A ≠ 0 := (Real.sqrt_pos.mpr P.hA_pos).ne'
              field_simp [hs]
      have h2 : ‖∫ t in (a + 2 * P.h)..b, E t‖ ≤ 3 / (P.A * P.h) := by
        refine osc_ibp_bound (by linarith [P.hh_pos]) hAh_pos
          (fun x _ => hu x) (fun x _ => hu' x) hu''_cont.continuousOn
          (fun x hx => hnonneg x ⟨by linarith [hx.1, P.hh_pos], hx.2⟩) ?_
        intro x hx
        have hinc := deriv_sub_ge_of_deriv2_ge (a := a + P.h) (b := x) (B := P.A)
          (by linarith [hx.1, P.hh_pos])
          (fun t _ => hu' t) hu''_cont.continuousOn
          (fun t ht => hlower t ⟨by linarith [ht.1, P.hh_pos], ht.2.trans hx.2⟩)
        have hge : P.A * P.h ≤ u' x := by
          have : P.h ≤ x - (a + P.h) := by linarith [hx.1]
          nlinarith [P.hA_pos]
        rw [abs_of_nonneg (hAh_pos.le.trans hge)]
        exact hge
      have haux : 0 ≤ 10 / (P.A * P.h) + 2 * M3 * P.h ^ 4 := by positivity
      calc ‖(∫ t in a..(a + 2 * P.h), E t) + (∫ t in (a + 2 * P.h)..b, E t)‖
          ≤ ‖∫ t in a..(a + 2 * P.h), E t‖ + ‖∫ t in (a + 2 * P.h)..b, E t‖ := norm_add_le _ _
        _ ≤ 1 / √P.A + 3 / (P.A * P.h) := add_le_add h1 h2
        _ ≤ 1 / √P.A + 1 / √P.A := by linarith
        _ = 2 / √P.A := by ring
        _ ≤ √(2 * Real.pi / P.A) := h2_le_sqrt
        _ ≤ √(2 * Real.pi / P.A) + 10 / (P.A * P.h) + 2 * M3 * P.h ^ 4 := by linarith
    · push Not at hL0
      by_cases hR0 : u' (b - P.h) ≤ 0
      · have hsp : ∫ t in a..b, E t =
            (∫ t in a..(b - 2 * P.h), E t) + (∫ t in (b - 2 * P.h)..b, E t) :=
          (intervalIntegral.integral_add_adjacent_intervals
            (hE_cont.intervalIntegrable _ _) (hE_cont.intervalIntegrable _ _)).symm
        rw [hsp]
        have h2 : ‖∫ t in (b - 2 * P.h)..b, E t‖ ≤ 1 / √P.A := by
          have hvdc := osc_vdc2_bound (a := b - 2 * P.h) (b := b) (B := 64 * P.A)
            (by linarith [P.hh_pos]) (by have := P.hA_pos; positivity)
            (fun x _ => hu x) (fun x _ => hu' x) hu''_cont.continuousOn
            (fun x hx => by
              have hg := g_ge_64_right P hx
              dsimp [u'']; nlinarith [P.hA_pos])
          have hsqrt64 : √(64 * P.A) = 8 * √P.A := by
            rw [Real.sqrt_mul (by norm_num)]
            norm_num
          rw [hsqrt64] at hvdc
          calc ‖∫ t in (b - 2 * P.h)..b, E t‖
              ≤ 8 / (8 * √P.A) := hvdc
            _ = 1 / √P.A := by
                have hs : √P.A ≠ 0 := (Real.sqrt_pos.mpr P.hA_pos).ne'
                field_simp [hs]
        have h1 : ‖∫ t in a..(b - 2 * P.h), E t‖ ≤ 3 / (P.A * P.h) := by
          refine osc_ibp_bound (by linarith [P.hh_pos]) hAh_pos
            (fun x _ => hu x) (fun x _ => hu' x) hu''_cont.continuousOn
            (fun x hx => hnonneg x ⟨hx.1, by linarith [hx.2, P.hh_pos]⟩) ?_
          intro x hx
          have hinc := deriv_sub_ge_of_deriv2_ge (a := x) (b := b - P.h) (B := P.A)
            (by linarith [hx.2, P.hh_pos])
            (fun t _ => hu' t) hu''_cont.continuousOn
            (fun t ht => hlower t ⟨hx.1.trans ht.1, by linarith [ht.2, P.hh_pos]⟩)
          have hle : u' x ≤ -(P.A * P.h) := by
            have : P.h ≤ (b - P.h) - x := by linarith [hx.2]
            nlinarith [P.hA_pos]
          rw [abs_of_neg (by linarith)]
          linarith
        have haux : 0 ≤ 10 / (P.A * P.h) + 2 * M3 * P.h ^ 4 := by positivity
        calc ‖(∫ t in a..(b - 2 * P.h), E t) + (∫ t in (b - 2 * P.h)..b, E t)‖
            ≤ ‖∫ t in a..(b - 2 * P.h), E t‖ + ‖∫ t in (b - 2 * P.h)..b, E t‖ := norm_add_le _ _
          _ ≤ 3 / (P.A * P.h) + 1 / √P.A := add_le_add h1 h2
          _ ≤ 1 / √P.A + 1 / √P.A := by linarith
          _ = 2 / √P.A := by ring
          _ ≤ √(2 * Real.pi / P.A) := h2_le_sqrt
          _ ≤ √(2 * Real.pi / P.A) + 10 / (P.A * P.h) + 2 * M3 * P.h ^ 4 := by linarith
      · push Not at hR0
        have hcont_u' : ContinuousOn u' (Set.Icc (a + P.h) (b - P.h)) :=
          ((continuous_ψ P).sub continuous_const).continuousOn
        obtain ⟨θ0, hθ0, hroot⟩ :=
          intermediate_value_Icc (by linarith [P.hh_pos]) hcont_u' ⟨hL0.le, hR0.le⟩
        refine osc_stationary_bound P.hA_pos hM3_nn P.hh_pos hθ0.1 hθ0.2
          (fun x _ => hu x) (fun x _ => hu' x) hu''_cont.continuousOn hlower hroot ?_
        intro x hx
        have hlip := g_lip_good P
          (x := x) (y := θ0) ⟨by linarith [hx.1, hθ0.1], by linarith [hx.2, hθ0.2]⟩
          ⟨by linarith [hθ0.1, P.hh_pos], by linarith [hθ0.2, P.hh_pos]⟩
        dsimp [u'', M3]
        rw [← mul_sub, abs_mul, abs_of_pos P.hA_pos]
        calc P.A * |g P x - g P θ0|
            ≤ P.A * (2 * B0 / P.η * |x - θ0|) := mul_le_mul_of_nonneg_left hlip P.hA_pos.le
          _ = 2 * B0 * P.A / P.η * |x - θ0| := by ring
  rw [hsplit]
  calc ‖(∫ t in (0 : ℝ)..P.δ, E t) + (∫ t in P.δ..(2 * Real.pi - 2 * P.δ), E t) +
        (∫ t in (2 * Real.pi - 2 * P.δ)..(2 * Real.pi), E t)‖
      ≤ ‖(∫ t in (0 : ℝ)..P.δ, E t) + (∫ t in P.δ..(2 * Real.pi - 2 * P.δ), E t)‖ +
        ‖∫ t in (2 * Real.pi - 2 * P.δ)..(2 * Real.pi), E t‖ := norm_add_le _ _
    _ ≤ ‖∫ t in (0 : ℝ)..P.δ, E t‖ + ‖∫ t in P.δ..(2 * Real.pi - 2 * P.δ), E t‖ +
        ‖∫ t in (2 * Real.pi - 2 * P.δ)..(2 * Real.pi), E t‖ := by
          gcongr; exact norm_add_le _ _
    _ ≤ P.δ + (√(2 * Real.pi / P.A) + 10 / (P.A * P.h) + 2 * M3 * P.h ^ 4) + 2 * P.δ := by
          gcongr
    _ = √(2 * Real.pi / P.A) + 3 * P.δ + 10 / (P.A * P.h) + 2 * (2 * B0 * P.A / P.η) * P.h ^ 4 := by
          dsimp [M3]; ring

private lemma second_ibp_piece {a b s : ℝ} {u u' u'' : ℝ → ℝ}
    (hab : a ≤ b)
    (hu : ∀ t ∈ Set.Icc a b, HasDerivAt u (u' t) t)
    (hu' : ∀ t ∈ Set.Icc a b, HasDerivAt u' (u'' t) t)
    (hu'' : ∀ t ∈ Set.Icc a b, HasDerivAt u'' s t)
    (hne : ∀ t ∈ Set.Icc a b, u' t ≠ 0) :
    let E : ℝ → ℂ := fun t => Complex.exp (Complex.I * (u t : ℂ))
    let F2 : ℝ → ℂ := fun t => ((u'' t / (u' t) ^ 3 : ℝ) : ℂ) * (E t / Complex.I)
    ∫ t in a..b, ((u'' t / (u' t) ^ 2 : ℝ) : ℂ) * E t =
      F2 b - F2 a -
      (1 / Complex.I) * ∫ t in a..b,
        (((s / (u' t) ^ 3 - 3 * (u'' t) ^ 2 / (u' t) ^ 4 : ℝ) : ℂ) * E t) := by
  intro E F2
  have hcont_u : ContinuousOn u (Set.Icc a b) := fun t ht => (hu t ht).continuousAt.continuousWithinAt
  have hcont_u' : ContinuousOn u' (Set.Icc a b) := fun t ht => (hu' t ht).continuousAt.continuousWithinAt
  have hcont_u'' : ContinuousOn u'' (Set.Icc a b) := fun t ht => (hu'' t ht).continuousAt.continuousWithinAt
  have hcont_E : ContinuousOn E (Set.Icc a b) :=
    Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hcont_u))
  set A1 : ℝ → ℂ := fun t => ((u'' t / (u' t) ^ 2 : ℝ) : ℂ) * E t
  set A2 : ℝ → ℂ := fun t =>
    (1 / Complex.I) * (((s / (u' t) ^ 3 - 3 * (u'' t) ^ 2 / (u' t) ^ 4 : ℝ) : ℂ) * E t)
  have hF2_deriv : ∀ t ∈ Set.uIcc a b, HasDerivAt F2 (A1 t + A2 t) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have hne_t : u' t ≠ 0 := hne t ht
    have hpow3 : HasDerivAt (fun x : ℝ => (u' x) ^ 3) (3 * (u' t) ^ 2 * u'' t) t := by
      have h := (hu' t ht).fun_pow 3
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    have hq : HasDerivAt (fun x : ℝ => u'' x / (u' x) ^ 3)
        ((s * (u' t) ^ 3 - u'' t * (3 * (u' t) ^ 2 * u'' t)) / ((u' t) ^ 3) ^ 2) t :=
      (hu'' t ht).fun_div hpow3 (pow_ne_zero 3 hne_t)
    have hqc : HasDerivAt (fun x : ℝ => ((u'' x / (u' x) ^ 3 : ℝ) : ℂ))
        ((((s * (u' t) ^ 3 - u'' t * (3 * (u' t) ^ 2 * u'' t)) / ((u' t) ^ 3) ^ 2 : ℝ) : ℂ)) t :=
      hq.ofReal_comp
    have hE' : HasDerivAt E (E t * (Complex.I * (u' t : ℂ))) t :=
      (((hu t ht).ofReal_comp).const_mul Complex.I).cexp
    have hEI : HasDerivAt (fun x : ℝ => E x / Complex.I) (E t * (u' t : ℂ)) t := by
      refine (hE'.div_const Complex.I).congr_deriv ?_
      field_simp [Complex.I_ne_zero]
    have hmul := hqc.fun_mul hEI
    refine hmul.congr_deriv ?_
    dsimp [A1, A2]
    have htc : (u' t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hne_t
    push_cast
    field_simp [Complex.I_ne_zero, htc]
    ring
  have hA1_int : IntervalIntegrable A1 volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact (Complex.continuous_ofReal.comp_continuousOn
      (hcont_u''.div (hcont_u'.pow 2) (fun t ht => pow_ne_zero 2 (hne t ht)))).mul hcont_E
  have hA2_int : IntervalIntegrable A2 volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    refine continuousOn_const.mul ((Complex.continuous_ofReal.comp_continuousOn ?_).mul hcont_E)
    exact (continuousOn_const.div (hcont_u'.pow 3) (fun t ht => pow_ne_zero 3 (hne t ht))).sub
      ((continuousOn_const.mul (hcont_u''.pow 2)).div (hcont_u'.pow 4)
        (fun t ht => pow_ne_zero 4 (hne t ht)))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hF2_deriv (hA1_int.add hA2_int)
  rw [intervalIntegral.integral_add hA1_int hA2_int] at hftc
  have heq := eq_sub_of_add_eq hftc
  rw [heq]
  congr 1
  dsimp [A2]
  rw [intervalIntegral.integral_const_mul]

private lemma fourierCoeff_fCircle_tail_le (P : Params) (harea : posArea P ≤ 10)
    (k : ℤ) {d : ℝ} (hd : 0 < d) (hdist : ∀ t ∈ Set.Icc 0 (2 * Real.pi), d ≤ |ψ P t - (k : ℝ)|) :
    letI : Fact (0 < 2 * Real.pi) := two_pi_pos_fact
    ‖fourierCoeff (fCircle P) k‖ ≤
      (1 / (2 * Real.pi)) * (P.A * (4 * B0 + 40 / P.δ) / d ^ 3 +
        3 * P.A ^ 2 * (2 * Real.pi * B0 ^ 2 + 400 / P.δ) / d ^ 4) := by
  have : Fact (0 < 2 * Real.pi) := two_pi_pos_fact
  rw [fourierCoeff_fCircle_eq P k, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  set u : ℝ → ℝ := fun t => φ P t - (k : ℝ) * t
  set u' : ℝ → ℝ := fun t => ψ P t - (k : ℝ)
  set u'' : ℝ → ℝ := fun t => P.A * g P t
  set E : ℝ → ℂ := fun t => Complex.exp (Complex.I * (u t : ℂ))
  have hne : ∀ t ∈ Set.Icc 0 (2 * Real.pi), u' t ≠ 0 := fun t ht h => by
    have := hdist t ht; dsimp [u'] at h; rw [h, abs_zero] at this; linarith
  have hu : ∀ t : ℝ, HasDerivAt u (u' t) t := fun t => by
    have hk : HasDerivAt (fun s : ℝ => (k : ℝ) * s) (k : ℝ) t := by
      simpa using (hasDerivAt_id t).const_mul (k : ℝ)
    exact (hasDerivAt_φ P t).sub hk
  have hu' : ∀ t : ℝ, HasDerivAt u' (u'' t) t := fun t => (hasDerivAt_ψ P t).sub_const (k : ℝ)
  have hu''_cont : Continuous u'' := continuous_const.mul (continuous_g P)
  have hE_cont : Continuous E :=
    Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_iff_continuousAt.mpr fun t => (hu t).continuousAt)))
  -- Step 1: First integration by parts on [0, 2*pi] with zero boundary term
  set F1 : ℝ → ℂ := fun t => E t / (Complex.I * (u' t : ℂ))
  set Q1 : ℝ → ℂ := fun t => ((u'' t / (u' t) ^ 2 : ℝ) : ℂ) * E t
  have hF1_deriv : ∀ t ∈ Set.uIcc 0 (2 * Real.pi), HasDerivAt F1 (E t + Complex.I * Q1 t) t := by
    intro t ht
    rw [Set.uIcc_of_le (by positivity)] at ht
    have hE' : HasDerivAt E (E t * (Complex.I * (u' t : ℂ))) t :=
      (((hu t).ofReal_comp).const_mul Complex.I).cexp
    have hden' : HasDerivAt (fun s : ℝ => Complex.I * (u' s : ℂ)) (Complex.I * (u'' t : ℂ)) t :=
      ((hu' t).ofReal_comp).const_mul Complex.I
    have hden_ne : Complex.I * (u' t : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (hne t ht))
    refine (hE'.fun_div hden' hden_ne).congr_deriv ?_
    dsimp [Q1]
    have htc : (u' t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hne t ht)
    push_cast
    field_simp [Complex.I_ne_zero, htc]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hQ1_int : ∀ a b, a ∈ Set.Icc 0 (2 * Real.pi) → b ∈ Set.Icc 0 (2 * Real.pi) →
      IntervalIntegrable Q1 volume a b := by
    intro a b ha hb
    apply ContinuousOn.intervalIntegrable
    have hsub : Set.uIcc a b ⊆ Set.Icc 0 (2 * Real.pi) := Set.uIcc_subset_Icc ha hb
    refine (Complex.continuous_ofReal.comp_continuousOn ?_).mul hE_cont.continuousOn
    exact hu''_cont.continuousOn.div (((continuous_ψ P).sub continuous_const).continuousOn.pow 2)
      (fun t ht => pow_ne_zero 2 (hne t (hsub ht)))
  have hF1_eq : F1 (2 * Real.pi) = F1 0 := by
    dsimp [F1, E, u, u']
    rw [ψ_zero_eq_two_pi P]
    congr 1
    rw [φ_zero, φ_two_pi]
    push_cast
    rw [mul_zero, sub_zero, mul_zero, Complex.exp_zero]
    have h : Complex.I * (2 * (Real.pi : ℂ) * (KInt P : ℂ) - (k : ℂ) * (2 * (Real.pi : ℂ))) =
        (((KInt P - k : ℤ) : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast; ring
    rw [h, Complex.exp_int_mul_two_pi_mul_I]
  have hibp1 : ∫ t in (0 : ℝ)..(2 * Real.pi), E t =
      -Complex.I * ∫ t in (0 : ℝ)..(2 * Real.pi), Q1 t := by
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hF1_deriv
      ((hE_cont.intervalIntegrable _ _).add
        ((hQ1_int 0 (2 * Real.pi) ⟨le_rfl, by positivity⟩ ⟨by positivity, le_rfl⟩).const_mul Complex.I))
    rw [hF1_eq, sub_self, intervalIntegral.integral_add (hE_cont.intervalIntegrable _ _)
      ((hQ1_int 0 (2 * Real.pi) ⟨le_rfl, by positivity⟩ ⟨by positivity, le_rfl⟩).const_mul Complex.I),
      intervalIntegral.integral_const_mul] at hftc
    linear_combination hftc
  rw [hibp1, norm_mul, norm_neg, Complex.norm_I, one_mul]
  -- Step 2: Second integration by parts on each of the 7 linear pieces of g P
  set F2 : ℝ → ℂ := fun t => ((u'' t / (u' t) ^ 3 : ℝ) : ℂ) * (E t / Complex.I)
  have hF2_zero : F2 0 = 0 := by simp [F2, u'', g_zero]
  have hF2_two_pi : F2 (2 * Real.pi) = 0 := by simp [F2, u'', g_two_pi]
  -- Helper to bound each linear piece [a, b] where g P t = lin a b va vb t
  have hpiece_bound : ∀ {a b va vb : ℝ}, a < b → a ∈ Set.Icc 0 (2 * Real.pi) →
      b ∈ Set.Icc 0 (2 * Real.pi) →
      (∀ t ∈ Set.Icc a b, g P t = lin a b va vb t) →
      ‖(∫ t in a..b, Q1 t) - (F2 b - F2 a)‖ ≤
        P.A * |vb - va| / d ^ 3 + 3 * (∫ t in a..b, (u'' t) ^ 2) / d ^ 4 := by
    intro a b va vb hab ha hb hlin_eq
    set s : ℝ := P.A * ((vb - va) / (b - a))
    set u''_loc : ℝ → ℝ := fun t => P.A * lin a b va vb t
    have hsub : Set.Icc a b ⊆ Set.Icc 0 (2 * Real.pi) := fun t ht => ⟨ha.1.trans ht.1, ht.2.trans hb.2⟩
    have hu'_loc : ∀ t ∈ Set.Icc a b, HasDerivAt u' (u''_loc t) t := fun t ht => by
      have h := hu' t
      dsimp [u''] at h
      rwa [hlin_eq t ht] at h
    have hu''_loc_d : ∀ t ∈ Set.Icc a b, HasDerivAt u''_loc s t := fun t _ =>
      (hasDerivAt_lin va vb t).const_mul P.A
    have hibp2 := second_ibp_piece hab.le (fun t _ => hu t) hu'_loc hu''_loc_d
      (fun t ht => hne t (hsub ht))
    dsimp only at hibp2
    have hcongr1 : ∫ t in a..b, Q1 t = ∫ t in a..b, ((u''_loc t / (u' t) ^ 2 : ℝ) : ℂ) * E t :=
      intervalIntegral.integral_congr fun t ht => by
        rw [Set.uIcc_of_le hab.le] at ht
        dsimp [Q1, u'', u''_loc]; rw [hlin_eq t ht]
    have hFb : ((u''_loc b / (u' b) ^ 3 : ℝ) : ℂ) * (E b / Complex.I) = F2 b := by
      dsimp [F2, u'', u''_loc]; rw [hlin_eq b ⟨hab.le, le_rfl⟩]
    have hFa : ((u''_loc a / (u' a) ^ 3 : ℝ) : ℂ) * (E a / Complex.I) = F2 a := by
      dsimp [F2, u'', u''_loc]; rw [hlin_eq a ⟨le_rfl, hab.le⟩]
    rw [hcongr1]
    change ‖(∫ t in a..b, ((u''_loc t / (u' t) ^ 2 : ℝ) : ℂ) * E t) - (F2 b - F2 a)‖ ≤ _
    rw [hibp2]
    change ‖(((u''_loc b / (u' b) ^ 3 : ℝ) : ℂ) * (E b / Complex.I) -
        ((u''_loc a / (u' a) ^ 3 : ℝ) : ℂ) * (E a / Complex.I) -
        (1 / Complex.I) * ∫ t in a..b,
          (((s / (u' t) ^ 3 - 3 * (u''_loc t) ^ 2 / (u' t) ^ 4 : ℝ) : ℂ) * E t)) - (F2 b - F2 a)‖ ≤ _
    rw [hFb, hFa]
    have hsub_eq : (F2 b - F2 a - (1 / Complex.I) * ∫ t in a..b,
        (((s / (u' t) ^ 3 - 3 * (u''_loc t) ^ 2 / (u' t) ^ 4 : ℝ) : ℂ) * E t)) - (F2 b - F2 a) =
        -(1 / Complex.I) * ∫ t in a..b,
          (((s / (u' t) ^ 3 - 3 * (u''_loc t) ^ 2 / (u' t) ^ 4 : ℝ) : ℂ) * E t) := by ring
    rw [hsub_eq, norm_mul, norm_neg, norm_div, norm_one, Complex.norm_I, div_one, one_mul]
    have hdom_cont : ContinuousOn (fun t : ℝ => |s| / d ^ 3 + 3 * (u'' t) ^ 2 / d ^ 4) (Set.Icc a b) :=
      continuousOn_const.add ((continuousOn_const.mul (hu''_cont.continuousOn.pow 2)).div_const _)
    have hpt : ∀ t ∈ Set.Icc a b,
        ‖((s / (u' t) ^ 3 - 3 * (u''_loc t) ^ 2 / (u' t) ^ 4 : ℝ) : ℂ) * E t‖ ≤
          |s| / d ^ 3 + 3 * (u'' t) ^ 2 / d ^ 4 := by
      intro t ht
      have hE1 : ‖E t‖ = 1 := by dsimp [E]; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I (u t)
      rw [norm_mul, hE1, mul_one, Complex.norm_real, Real.norm_eq_abs]
      have hd_t : d ≤ |u' t| := hdist t (hsub ht)
      have hu''_eq : u''_loc t = u'' t := by dsimp [u'', u''_loc]; rw [hlin_eq t ht]
      rw [hu''_eq]
      calc |s / (u' t) ^ 3 - 3 * (u'' t) ^ 2 / (u' t) ^ 4|
          ≤ |s / (u' t) ^ 3| + |3 * (u'' t) ^ 2 / (u' t) ^ 4| := abs_sub _ _
        _ = |s| / |u' t| ^ 3 + 3 * (u'' t) ^ 2 / |u' t| ^ 4 := by
            rw [abs_div, abs_pow, abs_div, abs_pow,
              abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (sq_nonneg (u'' t)))]
        _ ≤ |s| / d ^ 3 + 3 * (u'' t) ^ 2 / d ^ 4 := by
            gcongr
    have hnorm_int : IntervalIntegrable
        (fun t => ‖((s / (u' t) ^ 3 - 3 * (u''_loc t) ^ 2 / (u' t) ^ 4 : ℝ) : ℂ) * E t‖) volume a b := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hab.le]
      refine ContinuousOn.norm ?_
      refine (Complex.continuous_ofReal.comp_continuousOn ?_).mul hE_cont.continuousOn
      have hcu' : ContinuousOn u' (Set.Icc a b) := ((continuous_ψ P).sub continuous_const).continuousOn
      have hcu'' : ContinuousOn u''_loc (Set.Icc a b) := (continuous_const.mul (continuous_lin _ _ _ _)).continuousOn
      exact (continuousOn_const.div (hcu'.pow 3) (fun t ht => pow_ne_zero 3 (hne t (hsub ht)))).sub
        ((continuousOn_const.mul (hcu''.pow 2)).div (hcu'.pow 4)
          (fun t ht => pow_ne_zero 4 (hne t (hsub ht))))
    calc ‖∫ t in a..b, (((s / (u' t) ^ 3 - 3 * (u''_loc t) ^ 2 / (u' t) ^ 4 : ℝ) : ℂ) * E t)‖
        ≤ ∫ t in a..b, ‖(((s / (u' t) ^ 3 - 3 * (u''_loc t) ^ 2 / (u' t) ^ 4 : ℝ) : ℂ) * E t)‖ :=
          intervalIntegral.norm_integral_le_integral_norm hab.le
      _ ≤ ∫ t in a..b, (|s| / d ^ 3 + 3 * (u'' t) ^ 2 / d ^ 4) :=
          intervalIntegral.integral_mono_on hab.le hnorm_int
            (hdom_cont.intervalIntegrable_of_Icc hab.le) hpt
      _ = (∫ _ in a..b, |s| / d ^ 3) + (∫ t in a..b, 3 * (u'' t) ^ 2 / d ^ 4) :=
          intervalIntegral.integral_add intervalIntegrable_const
            (((continuousOn_const.mul (hu''_cont.continuousOn.pow 2)).div_const _).intervalIntegrable_of_Icc hab.le)
      _ = P.A * |vb - va| / d ^ 3 + 3 * (∫ t in a..b, (u'' t) ^ 2) / d ^ 4 := by
          have h1 : ∫ _ in a..b, |s| / d ^ 3 = P.A * |vb - va| / d ^ 3 := by
            rw [intervalIntegral.integral_const, smul_eq_mul]
            dsimp [s]
            rw [abs_mul, abs_of_pos P.hA_pos, abs_div, abs_of_pos (sub_pos.mpr hab)]
            have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
            field_simp [hba, hd.ne']
          have h2 : ∫ t in a..b, 3 * (u'' t) ^ 2 / d ^ 4 = 3 * (∫ t in a..b, (u'' t) ^ 2) / d ^ 4 := by
            have hfn : (fun t : ℝ => 3 * (u'' t) ^ 2 / d ^ 4) =
                fun t : ℝ => (3 / d ^ 4) * (u'' t) ^ 2 := by ext t; ring
            rw [hfn, intervalIntegral.integral_const_mul]
            ring
          rw [h1, h2]
  -- Apply hpiece_bound to each of the 7 pieces and telescope F2
  let t0 : ℝ := 0
  let t1 : ℝ := P.δ
  let t2 : ℝ := P.η
  let t3 : ℝ := 2 * Real.pi - P.η - P.δ
  let t4 : ℝ := 2 * Real.pi - 2 * P.δ
  let t5 : ℝ := 2 * Real.pi - P.δ
  let tm : ℝ := 2 * Real.pi - P.δ / 2
  let t6 : ℝ := 2 * Real.pi
  have m0 : t0 ∈ Set.Icc 0 (2 * Real.pi) := ⟨le_rfl, by positivity⟩
  have m1 : t1 ∈ Set.Icc 0 (2 * Real.pi) := ⟨P.hδ_pos.le, by dsimp [t1]; linarith [P.h2π, P.hη_pos, P.hδ_pos]⟩
  have m2 : t2 ∈ Set.Icc 0 (2 * Real.pi) := ⟨P.hη_pos.le, by dsimp [t2]; linarith [P.h2π, P.hη_pos, P.hδ_pos]⟩
  have m3 : t3 ∈ Set.Icc 0 (2 * Real.pi) := ⟨by dsimp [t3]; linarith [P.h2π, P.hη_pos, P.hδ_pos], by dsimp [t3]; linarith [P.hη_pos, P.hδ_pos]⟩
  have m4 : t4 ∈ Set.Icc 0 (2 * Real.pi) := ⟨by dsimp [t4]; linarith [P.h2π, P.hη_pos, P.hδ_pos], by dsimp [t4]; linarith [P.hδ_pos]⟩
  have m5 : t5 ∈ Set.Icc 0 (2 * Real.pi) := ⟨by dsimp [t5]; linarith [P.h2π, P.hη_pos, P.hδ_pos], by dsimp [t5]; linarith [P.hδ_pos]⟩
  have mm : tm ∈ Set.Icc 0 (2 * Real.pi) := ⟨by dsimp [tm]; linarith [P.h2π, P.hη_pos, P.hδ_pos], by dsimp [tm]; linarith [P.hδ_pos]⟩
  have m6 : t6 ∈ Set.Icc 0 (2 * Real.pi) := ⟨by positivity, le_rfl⟩
  have hQ_split : ∫ t in (0 : ℝ)..(2 * Real.pi), Q1 t =
      ((∫ t in t0..t1, Q1 t) - (F2 t1 - F2 t0)) +
      ((∫ t in t1..t2, Q1 t) - (F2 t2 - F2 t1)) +
      ((∫ t in t2..t3, Q1 t) - (F2 t3 - F2 t2)) +
      ((∫ t in t3..t4, Q1 t) - (F2 t4 - F2 t3)) +
      ((∫ t in t4..t5, Q1 t) - (F2 t5 - F2 t4)) +
      ((∫ t in t5..tm, Q1 t) - (F2 tm - F2 t5)) +
      ((∫ t in tm..t6, Q1 t) - (F2 t6 - F2 tm)) := by
    have hadd : ∫ t in t0..t6, Q1 t =
        (∫ t in t0..t1, Q1 t) + (∫ t in t1..t2, Q1 t) + (∫ t in t2..t3, Q1 t) +
        (∫ t in t3..t4, Q1 t) + (∫ t in t4..t5, Q1 t) + (∫ t in t5..tm, Q1 t) +
        (∫ t in tm..t6, Q1 t) := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (hQ1_int t0 tm m0 mm) (hQ1_int tm t6 mm m6),
          ← intervalIntegral.integral_add_adjacent_intervals (hQ1_int t0 t5 m0 m5) (hQ1_int t5 tm m5 mm),
          ← intervalIntegral.integral_add_adjacent_intervals (hQ1_int t0 t4 m0 m4) (hQ1_int t4 t5 m4 m5),
          ← intervalIntegral.integral_add_adjacent_intervals (hQ1_int t0 t3 m0 m3) (hQ1_int t3 t4 m3 m4),
          ← intervalIntegral.integral_add_adjacent_intervals (hQ1_int t0 t2 m0 m2) (hQ1_int t2 t3 m2 m3),
          ← intervalIntegral.integral_add_adjacent_intervals (hQ1_int t0 t1 m0 m1) (hQ1_int t1 t2 m1 m2)]
    change ∫ t in t0..t6, Q1 t = _
    rw [hadd]
    have h0' : F2 t0 = 0 := hF2_zero
    have h6' : F2 t6 = 0 := hF2_two_pi
    linear_combination h6' - h0'
  have p1 := hpiece_bound (a := t0) (b := t1) (va := 0) (vb := B0) P.hδ_pos m0 m1 (fun t ht => g_eq_piece1 P ht)
  have p2 := hpiece_bound (a := t1) (b := t2) (va := B0) (vb := 1) (by dsimp [t1, t2]; linarith [P.hδη, P.hδ_pos]) m1 m2 (fun t ht => g_eq_piece2 P ht)
  have p3 := hpiece_bound (a := t2) (b := t3) (va := 1) (vb := 1) (by dsimp [t2, t3]; linarith [P.h2π, P.hδ_pos]) m2 m3
    (fun t ht => by rw [g_eq_piece3 P ht]; unfold lin; ring)
  have p4 := hpiece_bound (a := t3) (b := t4) (va := 1) (vb := B0) (by dsimp [t3, t4]; linarith [P.hδη, P.hδ_pos]) m3 m4 (fun t ht => g_eq_piece4 P ht)
  have p5 := hpiece_bound (a := t4) (b := t5) (va := B0) (vb := 0) (by dsimp [t4, t5]; linarith [P.hδ_pos]) m4 m5 (fun t ht => g_eq_piece5 P ht)
  have p6 := hpiece_bound (a := t5) (b := tm) (va := 0) (vb := -Hval P) (by dsimp [t5, tm]; linarith [P.hδ_pos]) m5 mm (fun t ht => g_eq_piece6 P ht)
  have p7 := hpiece_bound (a := tm) (b := t6) (va := -Hval P) (vb := 0) (by dsimp [tm, t6]; linarith [P.hδ_pos]) mm m6 (fun t ht => g_eq_piece7 P ht)
  have hsq_split : (∫ t in t0..t1, (u'' t) ^ 2) + (∫ t in t1..t2, (u'' t) ^ 2) +
      (∫ t in t2..t3, (u'' t) ^ 2) + (∫ t in t3..t4, (u'' t) ^ 2) +
      (∫ t in t4..t5, (u'' t) ^ 2) + (∫ t in t5..tm, (u'' t) ^ 2) +
      (∫ t in tm..t6, (u'' t) ^ 2) = ∫ t in (0 : ℝ)..(2 * Real.pi), (u'' t) ^ 2 := by
    have hi : ∀ a b, IntervalIntegrable (fun t => (u'' t) ^ 2) volume a b :=
      fun a b => (hu''_cont.pow 2).intervalIntegrable a b
    rw [intervalIntegral.integral_add_adjacent_intervals (hi t0 t1) (hi t1 t2),
        intervalIntegral.integral_add_adjacent_intervals (hi t0 t2) (hi t2 t3),
        intervalIntegral.integral_add_adjacent_intervals (hi t0 t3) (hi t3 t4),
        intervalIntegral.integral_add_adjacent_intervals (hi t0 t4) (hi t4 t5),
        intervalIntegral.integral_add_adjacent_intervals (hi t0 t5) (hi t5 tm),
        intervalIntegral.integral_add_adjacent_intervals (hi t0 tm) (hi tm t6)]
  have hH_le : Hval P ≤ 20 / P.δ := by
    unfold Hval
    have hδ := P.hδ_pos
    exact div_le_div_of_nonneg_right (by linarith) hδ.le
  have hsq_bound : ∫ t in (0 : ℝ)..(2 * Real.pi), (u'' t) ^ 2 ≤
      P.A ^ 2 * (2 * Real.pi * B0 ^ 2 + 400 / P.δ) := by
    have hi : ∀ a b, IntervalIntegrable (fun t => (u'' t) ^ 2) volume a b :=
      fun a b => (hu''_cont.pow 2).intervalIntegrable a b
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 (2 * Real.pi - P.δ))
      (hi (2 * Real.pi - P.δ) (2 * Real.pi))]
    have hpos_sq : ∫ t in (0 : ℝ)..(2 * Real.pi - P.δ), (u'' t) ^ 2 ≤
        P.A ^ 2 * (2 * Real.pi * B0 ^ 2) := by
      calc ∫ t in (0 : ℝ)..(2 * Real.pi - P.δ), (u'' t) ^ 2
          ≤ ∫ _ in (0 : ℝ)..(2 * Real.pi - P.δ), (P.A * B0) ^ 2 := by
            refine intervalIntegral.integral_mono_on (by linarith [P.h2π, P.hη_pos, P.hδ_pos])
              (hi _ _) intervalIntegrable_const (fun t ht => ?_)
            dsimp [u'']
            have h0 := g_nonneg_pos P ht
            have h1 := g_le_B0_pos P ht
            have hA0 := P.hA_pos
            have hAg : 0 ≤ P.A * g P t := mul_nonneg hA0.le h0
            have hAB : P.A * g P t ≤ P.A * B0 := mul_le_mul_of_nonneg_left h1 hA0.le
            nlinarith
        _ = (2 * Real.pi - P.δ) * (P.A * B0) ^ 2 := by
            rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
        _ ≤ P.A ^ 2 * (2 * Real.pi * B0 ^ 2) := by
            have := P.hδ_pos; unfold B0; nlinarith [sq_nonneg P.A]
    have hneg_sq : ∫ t in (2 * Real.pi - P.δ)..(2 * Real.pi), (u'' t) ^ 2 ≤
        P.A ^ 2 * (400 / P.δ) := by
      calc ∫ t in (2 * Real.pi - P.δ)..(2 * Real.pi), (u'' t) ^ 2
          ≤ ∫ _ in (2 * Real.pi - P.δ)..(2 * Real.pi), (P.A * (20 / P.δ)) ^ 2 := by
            refine intervalIntegral.integral_mono_on (by linarith [P.hδ_pos])
              (hi _ _) intervalIntegrable_const (fun t ht => ?_)
            dsimp [u'']
            have h0 := g_nonpos_neg P ht
            have h1 := g_ge_neg_H P ht
            have h2 : -(20 / P.δ) ≤ g P t := by linarith
            have hA0 := P.hA_pos
            have hAg0 : P.A * g P t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hA0.le h0
            have hAg2 : -(P.A * (20 / P.δ)) ≤ P.A * g P t := by
              have := mul_le_mul_of_nonneg_left h2 hA0.le
              linarith
            nlinarith
        _ = P.δ * (P.A * (20 / P.δ)) ^ 2 := by
            rw [intervalIntegral.integral_const, smul_eq_mul]; ring
        _ = P.A ^ 2 * (400 / P.δ) := by
            field_simp [P.hδ_pos.ne']; ring
    linarith
  have habs_sum : |B0 - 0| + |1 - B0| + |1 - 1| + |B0 - 1| + |0 - B0| + |-Hval P - 0| + |0 - -Hval P| ≤
      4 * B0 + 40 / P.δ := by
    have hHp := Hval_pos P
    rw [show |B0 - 0| = B0 by unfold B0; norm_num,
        show |1 - B0| = B0 - 1 by unfold B0; norm_num,
        show |(1 : ℝ) - 1| = 0 by norm_num,
        show |B0 - 1| = B0 - 1 by unfold B0; norm_num,
        show |0 - B0| = B0 by unfold B0; norm_num,
        show |-Hval P - 0| = Hval P by rw [sub_zero, abs_neg, abs_of_pos hHp],
        show |0 - -Hval P| = Hval P by rw [zero_sub, neg_neg, abs_of_pos hHp]]
    have h2H : Hval P + Hval P ≤ 40 / P.δ := by
      have h1 : Hval P + Hval P ≤ 20 / P.δ + 20 / P.δ := add_le_add hH_le hH_le
      have h2 : (20 : ℝ) / P.δ + 20 / P.δ = 40 / P.δ := by ring
      linarith
    linarith
  rw [hQ_split]
  have htri : ‖((∫ t in t0..t1, Q1 t) - (F2 t1 - F2 t0)) +
      ((∫ t in t1..t2, Q1 t) - (F2 t2 - F2 t1)) +
      ((∫ t in t2..t3, Q1 t) - (F2 t3 - F2 t2)) +
      ((∫ t in t3..t4, Q1 t) - (F2 t4 - F2 t3)) +
      ((∫ t in t4..t5, Q1 t) - (F2 t5 - F2 t4)) +
      ((∫ t in t5..tm, Q1 t) - (F2 tm - F2 t5)) +
      ((∫ t in tm..t6, Q1 t) - (F2 t6 - F2 tm))‖ ≤
      ‖(∫ t in t0..t1, Q1 t) - (F2 t1 - F2 t0)‖ +
      ‖(∫ t in t1..t2, Q1 t) - (F2 t2 - F2 t1)‖ +
      ‖(∫ t in t2..t3, Q1 t) - (F2 t3 - F2 t2)‖ +
      ‖(∫ t in t3..t4, Q1 t) - (F2 t4 - F2 t3)‖ +
      ‖(∫ t in t4..t5, Q1 t) - (F2 t5 - F2 t4)‖ +
      ‖(∫ t in t5..tm, Q1 t) - (F2 tm - F2 t5)‖ +
      ‖(∫ t in tm..t6, Q1 t) - (F2 t6 - F2 tm)‖ := by
    calc _ ≤ ‖((∫ t in t0..t1, Q1 t) - (F2 t1 - F2 t0)) +
              ((∫ t in t1..t2, Q1 t) - (F2 t2 - F2 t1)) +
              ((∫ t in t2..t3, Q1 t) - (F2 t3 - F2 t2)) +
              ((∫ t in t3..t4, Q1 t) - (F2 t4 - F2 t3)) +
              ((∫ t in t4..t5, Q1 t) - (F2 t5 - F2 t4)) +
              ((∫ t in t5..tm, Q1 t) - (F2 tm - F2 t5))‖ +
            ‖(∫ t in tm..t6, Q1 t) - (F2 t6 - F2 tm)‖ := norm_add_le _ _
      _ ≤ ‖((∫ t in t0..t1, Q1 t) - (F2 t1 - F2 t0)) +
              ((∫ t in t1..t2, Q1 t) - (F2 t2 - F2 t1)) +
              ((∫ t in t2..t3, Q1 t) - (F2 t3 - F2 t2)) +
              ((∫ t in t3..t4, Q1 t) - (F2 t4 - F2 t3)) +
              ((∫ t in t4..t5, Q1 t) - (F2 t5 - F2 t4))‖ +
            ‖(∫ t in t5..tm, Q1 t) - (F2 tm - F2 t5)‖ +
            ‖(∫ t in tm..t6, Q1 t) - (F2 t6 - F2 tm)‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ‖((∫ t in t0..t1, Q1 t) - (F2 t1 - F2 t0)) +
              ((∫ t in t1..t2, Q1 t) - (F2 t2 - F2 t1)) +
              ((∫ t in t2..t3, Q1 t) - (F2 t3 - F2 t2)) +
              ((∫ t in t3..t4, Q1 t) - (F2 t4 - F2 t3))‖ +
            ‖(∫ t in t4..t5, Q1 t) - (F2 t5 - F2 t4)‖ +
            ‖(∫ t in t5..tm, Q1 t) - (F2 tm - F2 t5)‖ +
            ‖(∫ t in tm..t6, Q1 t) - (F2 t6 - F2 tm)‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ‖((∫ t in t0..t1, Q1 t) - (F2 t1 - F2 t0)) +
              ((∫ t in t1..t2, Q1 t) - (F2 t2 - F2 t1)) +
              ((∫ t in t2..t3, Q1 t) - (F2 t3 - F2 t2))‖ +
            ‖(∫ t in t3..t4, Q1 t) - (F2 t4 - F2 t3)‖ +
            ‖(∫ t in t4..t5, Q1 t) - (F2 t5 - F2 t4)‖ +
            ‖(∫ t in t5..tm, Q1 t) - (F2 tm - F2 t5)‖ +
            ‖(∫ t in tm..t6, Q1 t) - (F2 t6 - F2 tm)‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ‖((∫ t in t0..t1, Q1 t) - (F2 t1 - F2 t0)) +
              ((∫ t in t1..t2, Q1 t) - (F2 t2 - F2 t1))‖ +
            ‖(∫ t in t2..t3, Q1 t) - (F2 t3 - F2 t2)‖ +
            ‖(∫ t in t3..t4, Q1 t) - (F2 t4 - F2 t3)‖ +
            ‖(∫ t in t4..t5, Q1 t) - (F2 t5 - F2 t4)‖ +
            ‖(∫ t in t5..tm, Q1 t) - (F2 tm - F2 t5)‖ +
            ‖(∫ t in tm..t6, Q1 t) - (F2 t6 - F2 tm)‖ := by gcongr; exact norm_add_le _ _
      _ ≤ _ := by gcongr; exact norm_add_le _ _
  have hcomb : P.A * (|B0 - 0| + |1 - B0| + |1 - 1| + |B0 - 1| + |0 - B0| + |-Hval P - 0| + |0 - -Hval P|) / d ^ 3 +
      3 * (∫ t in (0 : ℝ)..(2 * Real.pi), (u'' t) ^ 2) / d ^ 4 ≤
      P.A * (4 * B0 + 40 / P.δ) / d ^ 3 +
      3 * P.A ^ 2 * (2 * Real.pi * B0 ^ 2 + 400 / P.δ) / d ^ 4 := by
    have h1 : P.A * (|B0 - 0| + |1 - B0| + |1 - 1| + |B0 - 1| + |0 - B0| + |-Hval P - 0| + |0 - -Hval P|) / d ^ 3 ≤
        P.A * (4 * B0 + 40 / P.δ) / d ^ 3 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left habs_sum P.hA_pos.le) (by positivity)
    have h2 : 3 * (∫ t in (0 : ℝ)..(2 * Real.pi), (u'' t) ^ 2) / d ^ 4 ≤
        3 * P.A ^ 2 * (2 * Real.pi * B0 ^ 2 + 400 / P.δ) / d ^ 4 := by
      have h3 : 3 * (∫ t in (0 : ℝ)..(2 * Real.pi), (u'' t) ^ 2) ≤
          3 * P.A ^ 2 * (2 * Real.pi * B0 ^ 2 + 400 / P.δ) := by linarith [hsq_bound]
      exact div_le_div_of_nonneg_right h3 (by positivity)
    linarith
  calc _ ≤ _ := htri
    _ ≤ (P.A * |B0 - 0| / d ^ 3 + 3 * (∫ t in t0..t1, (u'' t) ^ 2) / d ^ 4) +
        (P.A * |1 - B0| / d ^ 3 + 3 * (∫ t in t1..t2, (u'' t) ^ 2) / d ^ 4) +
        (P.A * |1 - 1| / d ^ 3 + 3 * (∫ t in t2..t3, (u'' t) ^ 2) / d ^ 4) +
        (P.A * |B0 - 1| / d ^ 3 + 3 * (∫ t in t3..t4, (u'' t) ^ 2) / d ^ 4) +
        (P.A * |0 - B0| / d ^ 3 + 3 * (∫ t in t4..t5, (u'' t) ^ 2) / d ^ 4) +
        (P.A * |-Hval P - 0| / d ^ 3 + 3 * (∫ t in t5..tm, (u'' t) ^ 2) / d ^ 4) +
        (P.A * |0 - -Hval P| / d ^ 3 + 3 * (∫ t in tm..t6, (u'' t) ^ 2) / d ^ 4) := by
          gcongr
    _ = P.A * (|B0 - 0| + |1 - B0| + |1 - 1| + |B0 - 1| + |0 - B0| + |-Hval P - 0| + |0 - -Hval P|) / d ^ 3 +
        3 * ((∫ t in t0..t1, (u'' t) ^ 2) + (∫ t in t1..t2, (u'' t) ^ 2) +
          (∫ t in t2..t3, (u'' t) ^ 2) + (∫ t in t3..t4, (u'' t) ^ 2) +
          (∫ t in t4..t5, (u'' t) ^ 2) + (∫ t in t5..tm, (u'' t) ^ 2) +
          (∫ t in tm..t6, (u'' t) ^ 2)) / d ^ 4 := by ring
    _ = P.A * (|B0 - 0| + |1 - B0| + |1 - 1| + |B0 - 1| + |0 - B0| + |-Hval P - 0| + |0 - -Hval P|) / d ^ 3 +
        3 * (∫ t in (0 : ℝ)..(2 * Real.pi), (u'' t) ^ 2) / d ^ 4 := by rw [hsq_split]
    _ ≤ _ := hcomb

private lemma hasSum_telescoping_inv (M : ℕ) (hM : 1 ≤ M) :
    HasSum (fun m : ℕ => (1 : ℝ) / ((M + m : ℕ) : ℝ) - 1 / ((M + 1 + m : ℕ) : ℝ))
      (1 / (M : ℝ)) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · have hsum : ∀ N : ℕ, ∑ m ∈ Finset.range N,
        ((1 : ℝ) / ((M + m : ℕ) : ℝ) - 1 / ((M + 1 + m : ℕ) : ℝ)) =
        1 / (M : ℝ) - 1 / ((M + N : ℕ) : ℝ) := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        have : M + 1 + N = M + (N + 1) := by omega
        rw [this]
        ring
    simp_rw [hsum]
    have htend : Tendsto (fun N : ℕ => (1 : ℝ) / ((M + N : ℕ) : ℝ)) atTop (𝓝 0) := by
      refine tendsto_const_nhds.div_atTop ?_
      have h1 : Tendsto (fun N : ℕ => (M : ℝ) + (N : ℝ)) atTop atTop :=
        tendsto_atTop_add_const_left atTop (M : ℝ) tendsto_natCast_atTop_atTop
      simpa [Nat.cast_add] using h1
    simpa using tendsto_const_nhds.sub htend
  · intro m
    have h1 : (0 : ℝ) < ((M + m : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < M + m)
    have h2 : ((M + m : ℕ) : ℝ) ≤ ((M + 1 + m : ℕ) : ℝ) := by exact_mod_cast (by omega : M + m ≤ M + 1 + m)
    linarith [one_div_le_one_div_of_le h1 h2]

private lemma summable_and_tsum_inv_cube (M : ℕ) (hM : 1 ≤ M) :
    Summable (fun m : ℕ => (1 : ℝ) / ((M + 1 + m : ℕ) : ℝ) ^ 3) ∧
    (∑' m : ℕ, (1 : ℝ) / ((M + 1 + m : ℕ) : ℝ) ^ 3) ≤ 1 / (M : ℝ) ^ 2 := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have htel := (hasSum_telescoping_inv M hM).mul_left (1 / (M : ℝ))
  have hdom : ∀ m : ℕ, (1 : ℝ) / ((M + 1 + m : ℕ) : ℝ) ^ 3 ≤
      (1 / (M : ℝ)) * ((1 : ℝ) / ((M + m : ℕ) : ℝ) - 1 / ((M + 1 + m : ℕ) : ℝ)) := by
    intro m
    have ha : (0 : ℝ) < ((M + m : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < M + m)
    have hb : (0 : ℝ) < ((M + 1 + m : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < M + 1 + m)
    have hdiff : (1 : ℝ) / ((M + m : ℕ) : ℝ) - 1 / ((M + 1 + m : ℕ) : ℝ) =
        1 / (((M + m : ℕ) : ℝ) * ((M + 1 + m : ℕ) : ℝ)) := by
      field_simp [ha.ne', hb.ne']
      push_cast; ring
    rw [hdiff, one_div_mul_one_div]
    apply one_div_le_one_div_of_le (by positivity)
    have h1 : (M : ℝ) ≤ ((M + 1 + m : ℕ) : ℝ) := by exact_mod_cast (by omega : M ≤ M + 1 + m)
    have h2 : ((M + m : ℕ) : ℝ) ≤ ((M + 1 + m : ℕ) : ℝ) := by exact_mod_cast (by omega : M + m ≤ M + 1 + m)
    have h3 : (M : ℝ) * ((M + m : ℕ) : ℝ) ≤ ((M + 1 + m : ℕ) : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hsum : Summable (fun m : ℕ => (1 : ℝ) / ((M + 1 + m : ℕ) : ℝ) ^ 3) :=
    Summable.of_nonneg_of_le (fun m => by positivity) hdom htel.summable
  refine ⟨hsum, ?_⟩
  calc ∑' m : ℕ, (1 : ℝ) / ((M + 1 + m : ℕ) : ℝ) ^ 3
      ≤ ∑' m : ℕ, (1 / (M : ℝ)) * ((1 : ℝ) / ((M + m : ℕ) : ℝ) - 1 / ((M + 1 + m : ℕ) : ℝ)) :=
        hsum.tsum_le_tsum hdom htel.summable
    _ = (1 / (M : ℝ)) * (1 / (M : ℝ)) := htel.tsum_eq
    _ = 1 / (M : ℝ) ^ 2 := by ring

private lemma summable_and_tsum_inv_fourth (M : ℕ) (hM : 1 ≤ M) :
    Summable (fun m : ℕ => (1 : ℝ) / ((M + 1 + m : ℕ) : ℝ) ^ 4) ∧
    (∑' m : ℕ, (1 : ℝ) / ((M + 1 + m : ℕ) : ℝ) ^ 4) ≤ 1 / (M : ℝ) ^ 3 := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have htel := (hasSum_telescoping_inv M hM).mul_left (1 / (M : ℝ) ^ 2)
  have hdom : ∀ m : ℕ, (1 : ℝ) / ((M + 1 + m : ℕ) : ℝ) ^ 4 ≤
      (1 / (M : ℝ) ^ 2) * ((1 : ℝ) / ((M + m : ℕ) : ℝ) - 1 / ((M + 1 + m : ℕ) : ℝ)) := by
    intro m
    have ha : (0 : ℝ) < ((M + m : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < M + m)
    have hb : (0 : ℝ) < ((M + 1 + m : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < M + 1 + m)
    have hdiff : (1 : ℝ) / ((M + m : ℕ) : ℝ) - 1 / ((M + 1 + m : ℕ) : ℝ) =
        1 / (((M + m : ℕ) : ℝ) * ((M + 1 + m : ℕ) : ℝ)) := by
      field_simp [ha.ne', hb.ne']
      push_cast; ring
    rw [hdiff, one_div_mul_one_div]
    apply one_div_le_one_div_of_le (by positivity)
    have h1 : (M : ℝ) ≤ ((M + 1 + m : ℕ) : ℝ) := by exact_mod_cast (by omega : M ≤ M + 1 + m)
    have h2 : ((M + m : ℕ) : ℝ) ≤ ((M + 1 + m : ℕ) : ℝ) := by exact_mod_cast (by omega : M + m ≤ M + 1 + m)
    have h3 : (M : ℝ) ^ 2 ≤ ((M + 1 + m : ℕ) : ℝ) ^ 2 := by nlinarith
    have h4 : ((M + m : ℕ) : ℝ) * ((M + 1 + m : ℕ) : ℝ) ≤ ((M + 1 + m : ℕ) : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hsum : Summable (fun m : ℕ => (1 : ℝ) / ((M + 1 + m : ℕ) : ℝ) ^ 4) :=
    Summable.of_nonneg_of_le (fun m => by positivity) hdom htel.summable
  refine ⟨hsum, ?_⟩
  calc ∑' m : ℕ, (1 : ℝ) / ((M + 1 + m : ℕ) : ℝ) ^ 4
      ≤ ∑' m : ℕ, (1 / (M : ℝ) ^ 2) * ((1 : ℝ) / ((M + m : ℕ) : ℝ) - 1 / ((M + 1 + m : ℕ) : ℝ)) :=
        hsum.tsum_le_tsum hdom htel.summable
    _ = (1 / (M : ℝ) ^ 2) * (1 / (M : ℝ)) := htel.tsum_eq
    _ = 1 / (M : ℝ) ^ 3 := by ring

private noncomputable def tailBound (P : Params) (M : ℕ) : ℝ :=
  (1 / Real.pi) * (P.A * (4 * B0 + 40 / P.δ) / (M : ℝ) ^ 2 +
    3 * P.A ^ 2 * (2 * Real.pi * B0 ^ 2 + 400 / P.δ) / (M : ℝ) ^ 3)

private lemma tailBound_nonneg (P : Params) (M : ℕ) : 0 ≤ tailBound P M := by
  unfold tailBound B0
  have := P.hA_pos; have := P.hδ_pos; positivity

private lemma fourier_tail_and_parseval (P : Params) (n M : ℕ)
    (hM : 1 ≤ M) (harea : posArea P ≤ 10)
    (hspan : P.A * posArea P + 1 ≤ (n : ℝ) - 2 * (M : ℝ) - 2) :
    letI : Fact (0 < 2 * Real.pi) := two_pi_pos_fact
    let S : Finset ℤ := Finset.Ico (-(M : ℤ)) ((n : ℤ) - (M : ℤ))
    (∀ θ : ℝ, |‖∑ k ∈ S, fourierCoeff (fCircle P) k *
        fourier (T := 2 * Real.pi) k (θ : AddCircle (2 * Real.pi))‖ - 1| ≤ tailBound P M) ∧
    (1 - tailBound P M ≤ ∑ k ∈ S, ‖fourierCoeff (fCircle P) k‖ ^ 2) := by
  have : Fact (0 < 2 * Real.pi) := two_pi_pos_fact
  intro S
  set C1 : ℝ := (1 / (2 * Real.pi)) * (P.A * (4 * B0 + 40 / P.δ))
  set C2 : ℝ := (1 / (2 * Real.pi)) * (3 * P.A ^ 2 * (2 * Real.pi * B0 ^ 2 + 400 / P.δ))
  have hC1 : 0 ≤ C1 := by dsimp [C1]; unfold B0; have := P.hA_pos; have := P.hδ_pos; positivity
  have hC2 : 0 ≤ C2 := by dsimp [C2]; unfold B0; have := P.hA_pos; have := P.hδ_pos; positivity
  have htail_neg : ∀ m : ℕ, ‖fourierCoeff (fCircle P) (-((M + 1 + m : ℕ) : ℤ))‖ ≤
      C1 * (1 / ((M + 1 + m : ℕ) : ℝ) ^ 3) + C2 * (1 / ((M + 1 + m : ℕ) : ℝ) ^ 4) := by
    intro m
    have hd : (0 : ℝ) < ((M + 1 + m : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < M + 1 + m)
    have hbd := fourierCoeff_fCircle_tail_le P harea (-((M + 1 + m : ℕ) : ℤ)) hd (fun t ht => by
      have hψ := (ψ_bounds P ht).1
      push_cast
      rw [sub_neg_eq_add, abs_of_nonneg (by positivity)]
      linarith)
    calc ‖fourierCoeff (fCircle P) (-((M + 1 + m : ℕ) : ℤ))‖
        ≤ _ := hbd
      _ = C1 * (1 / ((M + 1 + m : ℕ) : ℝ) ^ 3) + C2 * (1 / ((M + 1 + m : ℕ) : ℝ) ^ 4) := by
          dsimp [C1, C2]; ring
  have htail_pos : ∀ m : ℕ, ‖fourierCoeff (fCircle P) ((n : ℤ) - (M : ℤ) + (m : ℤ))‖ ≤
      C1 * (1 / ((M + 1 + m : ℕ) : ℝ) ^ 3) + C2 * (1 / ((M + 1 + m : ℕ) : ℝ) ^ 4) := by
    intro m
    have hd : (0 : ℝ) < ((M + 1 + m : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < M + 1 + m)
    have hbd := fourierCoeff_fCircle_tail_le P harea ((n : ℤ) - (M : ℤ) + (m : ℤ)) hd (fun t ht => by
      have hψ := (ψ_bounds P ht).2
      push_cast
      have hle : ψ P t - ((n : ℝ) - (M : ℝ) + (m : ℝ)) ≤ -((M : ℝ) + 1 + (m : ℝ)) := by linarith
      rw [abs_of_neg (by linarith)]
      linarith)
    calc ‖fourierCoeff (fCircle P) ((n : ℤ) - (M : ℤ) + (m : ℤ))‖
        ≤ _ := hbd
      _ = C1 * (1 / ((M + 1 + m : ℕ) : ℝ) ^ 3) + C2 * (1 / ((M + 1 + m : ℕ) : ℝ) ^ 4) := by
          dsimp [C1, C2]; ring
  obtain ⟨hs3, ht3⟩ := summable_and_tsum_inv_cube M hM
  obtain ⟨hs4, ht4⟩ := summable_and_tsum_inv_fourth M hM
  have hdom_sum : Summable (fun m : ℕ =>
      C1 * (1 / ((M + 1 + m : ℕ) : ℝ) ^ 3) + C2 * (1 / ((M + 1 + m : ℕ) : ℝ) ^ 4)) :=
    (hs3.mul_left C1).add (hs4.mul_left C2)
  have hdom_tsum : (∑' m : ℕ, (C1 * (1 / ((M + 1 + m : ℕ) : ℝ) ^ 3) +
      C2 * (1 / ((M + 1 + m : ℕ) : ℝ) ^ 4))) ≤ tailBound P M / 2 := by
    rw [Summable.tsum_add (hs3.mul_left C1) (hs4.mul_left C2), tsum_mul_left, tsum_mul_left]
    calc C1 * (∑' m : ℕ, 1 / ((M + 1 + m : ℕ) : ℝ) ^ 3) +
         C2 * (∑' m : ℕ, 1 / ((M + 1 + m : ℕ) : ℝ) ^ 4)
        ≤ C1 * (1 / (M : ℝ) ^ 2) + C2 * (1 / (M : ℝ) ^ 3) := by gcongr
      _ = tailBound P M / 2 := by dsimp [C1, C2, tailBound]; ring
  have hsum_neg : Summable (fun m : ℕ => ‖fourierCoeff (fCircle P) (-((M + 1 + m : ℕ) : ℤ))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) htail_neg hdom_sum
  have hsum_pos : Summable (fun m : ℕ => ‖fourierCoeff (fCircle P) ((n : ℤ) - (M : ℤ) + (m : ℤ))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) htail_pos hdom_sum
  -- Define tail indicator on ℤ
  set g_norm : ℤ → ℝ := fun k => if k ∈ S then 0 else ‖fourierCoeff (fCircle P) k‖
  -- Split g_norm into negative part (k < -M) and positive part (n - M ≤ k)
  set g_neg : ℤ → ℝ := fun k => if k < -(M : ℤ) then ‖fourierCoeff (fCircle P) k‖ else 0
  set g_pos : ℤ → ℝ := fun k => if (n : ℤ) - (M : ℤ) ≤ k then ‖fourierCoeff (fCircle P) k‖ else 0
  have hgn_eq : ∀ k : ℤ, g_norm k = g_neg k + g_pos k := by
    intro k
    have hMn : -(M : ℤ) ≤ (n : ℤ) - (M : ℤ) := by omega
    dsimp [g_norm, g_neg, g_pos, S]
    simp only [Finset.mem_Ico]
    by_cases h1 : k < -(M : ℤ)
    · have h2 : ¬ ((n : ℤ) - (M : ℤ) ≤ k) := by omega
      have h3 : ¬ (-(M : ℤ) ≤ k ∧ k < (n : ℤ) - (M : ℤ)) := by omega
      simp [h1, h2, h3]
    · by_cases h2 : (n : ℤ) - (M : ℤ) ≤ k
      · have h3 : ¬ (-(M : ℤ) ≤ k ∧ k < (n : ℤ) - (M : ℤ)) := by omega
        simp [h1, h2, h3]
      · have h3 : -(M : ℤ) ≤ k ∧ k < (n : ℤ) - (M : ℤ) := by omega
        simp [h1, h2, h3]
  have hneg_equiv : Summable g_neg ∧ (∑' k : ℤ, g_neg k) =
      ∑' m : ℕ, ‖fourierCoeff (fCircle P) (-((M + 1 + m : ℕ) : ℤ))‖ := by
    let emb : ℕ → ℤ := fun m => -((M + 1 + m : ℕ) : ℤ)
    have hemb_inj : Function.Injective emb := fun a b h => by
      dsimp [emb] at h; omega
    have hsupp : ∀ k : ℤ, k ∉ Set.range emb → g_neg k = 0 := by
      intro k hk
      dsimp [g_neg]
      rw [if_neg]
      intro hlt
      apply hk
      refine ⟨((-k - (M : ℤ) - 1)).toNat, ?_⟩
      dsimp [emb]; omega
    have hcomp : g_neg ∘ emb = fun m : ℕ => ‖fourierCoeff (fCircle P) (-((M + 1 + m : ℕ) : ℤ))‖ := by
      ext m; dsimp [g_neg, emb]; rw [if_pos (by omega)]
    have hs : Summable g_neg := by
      rw [← Function.Injective.summable_iff hemb_inj hsupp, hcomp]
      exact hsum_neg
    refine ⟨hs, ?_⟩
    have hts := Function.Injective.tsum_eq hemb_inj (f := g_neg) (fun k hk => by
      by_contra hnot
      exact hk (hsupp k hnot))
    rw [← hts]
    exact congrArg tsum hcomp
  have hpos_equiv : Summable g_pos ∧ (∑' k : ℤ, g_pos k) =
      ∑' m : ℕ, ‖fourierCoeff (fCircle P) ((n : ℤ) - (M : ℤ) + (m : ℤ))‖ := by
    let emb : ℕ → ℤ := fun m => (n : ℤ) - (M : ℤ) + (m : ℤ)
    have hemb_inj : Function.Injective emb := fun a b h => by
      dsimp [emb] at h; omega
    have hsupp : ∀ k : ℤ, k ∉ Set.range emb → g_pos k = 0 := by
      intro k hk
      dsimp [g_pos]
      rw [if_neg]
      intro hge
      apply hk
      refine ⟨(k - ((n : ℤ) - (M : ℤ))).toNat, ?_⟩
      dsimp [emb]; omega
    have hcomp : g_pos ∘ emb = fun m : ℕ => ‖fourierCoeff (fCircle P) ((n : ℤ) - (M : ℤ) + (m : ℤ))‖ := by
      ext m; dsimp [g_pos, emb]; rw [if_pos (by omega)]
    have hs : Summable g_pos := by
      rw [← Function.Injective.summable_iff hemb_inj hsupp, hcomp]
      exact hsum_pos
    refine ⟨hs, ?_⟩
    have hts := Function.Injective.tsum_eq hemb_inj (f := g_pos) (fun k hk => by
      by_contra hnot
      exact hk (hsupp k hnot))
    rw [← hts]
    exact congrArg tsum hcomp
  have hgn_sum : Summable g_norm := by
    have h := hneg_equiv.1.add hpos_equiv.1
    exact h.congr (fun k => (hgn_eq k).symm)
  have hgn_tsum_le : ∑' k : ℤ, g_norm k ≤ tailBound P M := by
    have h1 : ∑' k : ℤ, g_norm k = (∑' k : ℤ, g_neg k) + (∑' k : ℤ, g_pos k) := by
      rw [← Summable.tsum_add hneg_equiv.1 hpos_equiv.1]
      congr 1; ext k; exact hgn_eq k
    rw [h1, hneg_equiv.2, hpos_equiv.2]
    have hb1 : (∑' m : ℕ, ‖fourierCoeff (fCircle P) (-((M + 1 + m : ℕ) : ℤ))‖) ≤ tailBound P M / 2 :=
      (hsum_neg.tsum_le_tsum htail_neg hdom_sum).trans hdom_tsum
    have hb2 : (∑' m : ℕ, ‖fourierCoeff (fCircle P) ((n : ℤ) - (M : ℤ) + (m : ℤ))‖) ≤ tailBound P M / 2 :=
      (hsum_pos.tsum_le_tsum htail_pos hdom_sum).trans hdom_tsum
    linarith
  have hfc_norm_sum : Summable (fun k : ℤ => ‖fourierCoeff (fCircle P) k‖) := by
    have hfin : Summable (fun k : ℤ => if k ∈ S then ‖fourierCoeff (fCircle P) k‖ else 0) :=
      summable_of_ne_finset_zero (s := S) (fun k hk => by simp [hk])
    exact (hfin.add hgn_sum).congr fun k => by
      dsimp [g_norm]; by_cases hk : k ∈ S <;> simp [hk]
  have hfc_sum : Summable (fourierCoeff (fCircle P)) := hfc_norm_sum.of_norm
  -- Part 1: Uniform flatness on all θ ∈ ℝ
  have hflat : ∀ θ : ℝ, |‖∑ k ∈ S, fourierCoeff (fCircle P) k *
      fourier (T := 2 * Real.pi) k (θ : AddCircle (2 * Real.pi))‖ - 1| ≤ tailBound P M := by
    intro θ
    set x : AddCircle (2 * Real.pi) := (θ : AddCircle (2 * Real.pi))
    have hhas := hasSum_fourier_series_of_summable (f := fCircle P) hfc_sum
    have hhas_pt : HasSum (fun k : ℤ => fourierCoeff (fCircle P) k * fourier (T := 2 * Real.pi) k x)
        (fCircle P x) := by
      have hm := hhas.map (ContinuousMap.evalCLM ℂ x) (ContinuousMap.evalCLM ℂ x).continuous
      simpa [Function.comp_def, smul_eq_mul] using hm
    set term : ℤ → ℂ := fun k => fourierCoeff (fCircle P) k * fourier (T := 2 * Real.pi) k x
    have hterm_norm : ∀ k : ℤ, ‖term k‖ = ‖fourierCoeff (fCircle P) k‖ := fun k => by
      change ‖fourierCoeff (fCircle P) k *
        (fourier (T := 2 * Real.pi) k (θ : AddCircle (2 * Real.pi)) : ℂ)‖ = _
      have he1 : ‖Complex.exp (Complex.I * (((k : ℝ) * θ : ℝ) : ℂ))‖ = 1 := by
        rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
      rw [norm_mul, fourier_two_pi_apply k θ, he1, mul_one]
    have hfin_has : HasSum (fun k : ℤ => if k ∈ S then term k else 0) (∑ k ∈ S, term k) := by
      have h : HasSum (fun k : ℤ => if k ∈ S then term k else 0)
          (∑ k ∈ S, if k ∈ S then term k else 0) :=
        hasSum_sum_of_ne_finset_zero (s := S) (fun k hk => by simp [hk])
      have hsum_eq : (∑ k ∈ S, if k ∈ S then term k else 0) = ∑ k ∈ S, term k :=
        Finset.sum_congr rfl fun k hk => by simp [hk]
      rwa [hsum_eq] at h
    have htail_has : HasSum (fun k : ℤ => if k ∈ S then 0 else term k)
        (fCircle P x - ∑ k ∈ S, term k) := by
      have hsub := hhas_pt.sub hfin_has
      have hfun : (fun k : ℤ => if k ∈ S then (0 : ℂ) else term k) =
          fun b : ℤ => term b - if b ∈ S then term b else 0 := by
        ext k; by_cases hk : k ∈ S <;> simp [hk]
      rw [hfun]
      exact hsub
    have htail_norm_sum : Summable (fun k : ℤ => ‖if k ∈ S then (0 : ℂ) else term k‖) :=
      hgn_sum.congr fun k => by
        dsimp [g_norm]; by_cases hk : k ∈ S <;> simp [hk, hterm_norm]
    have hdiff : ‖fCircle P x - ∑ k ∈ S, term k‖ ≤ tailBound P M := by
      rw [← htail_has.tsum_eq]
      calc ‖∑' k : ℤ, (if k ∈ S then (0 : ℂ) else term k)‖
          ≤ ∑' k : ℤ, ‖if k ∈ S then (0 : ℂ) else term k‖ := norm_tsum_le_tsum_norm htail_norm_sum
        _ = ∑' k : ℤ, g_norm k := by
            congr 1; ext k; dsimp [g_norm]; by_cases hk : k ∈ S <;> simp [hk, hterm_norm]
        _ ≤ tailBound P M := hgn_tsum_le
    calc |‖∑ k ∈ S, term k‖ - 1|
        = |‖∑ k ∈ S, term k‖ - ‖fCircle P x‖| := by rw [fCircle_norm P x]
      _ ≤ ‖(∑ k ∈ S, term k) - fCircle P x‖ := abs_norm_sub_norm_le _ _
      _ = ‖fCircle P x - ∑ k ∈ S, term k‖ := norm_sub_rev _ _
      _ ≤ tailBound P M := hdiff
  -- Part 2: Parseval lower bound on ∑_{k ∈ S} ‖c_k‖^2
  have hparseval : 1 - tailBound P M ≤ ∑ k ∈ S, ‖fourierCoeff (fCircle P) k‖ ^ 2 := by
    set fLp := ContinuousMap.toLp 2 (AddCircle.haarAddCircle (T := 2 * Real.pi)) ℂ (fCircle P)
    have hae : (fLp : AddCircle (2 * Real.pi) → ℂ) =ᵐ[AddCircle.haarAddCircle] fCircle P :=
      ContinuousMap.coeFn_toLp (AddCircle.haarAddCircle (T := 2 * Real.pi)) (fCircle P)
    have hfc_eq : fourierCoeff (fLp : AddCircle (2 * Real.pi) → ℂ) = fourierCoeff (fCircle P) :=
      fourierCoeff_congr_ae hae
    have hpar := tsum_sq_fourierCoeff fLp
    rw [hfc_eq] at hpar
    have hint1 : ∫ t : AddCircle (2 * Real.pi), ‖(fLp : AddCircle (2 * Real.pi) → ℂ) t‖ ^ 2
        ∂AddCircle.haarAddCircle = 1 := by
      have hae_sq : (fun t => ‖(fLp : AddCircle (2 * Real.pi) → ℂ) t‖ ^ 2) =ᵐ[AddCircle.haarAddCircle]
          fun _ => (1 : ℝ) := by
        filter_upwards [hae] with t ht
        rw [ht, fCircle_norm P t, one_pow]
      rw [integral_congr_ae hae_sq, integral_const]
      simp
    rw [hint1] at hpar
    have hsq_sum : Summable (fun k : ℤ => ‖fourierCoeff (fCircle P) k‖ ^ 2) :=
      Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
        (fun k => by
          have h1 := fourierCoeff_fCircle_norm_le_one P k
          nlinarith [norm_nonneg (fourierCoeff (fCircle P) k)])
        hfc_norm_sum
    have htail_sq_sum : Summable (fun k : ℤ => if k ∈ S then (0 : ℝ) else ‖fourierCoeff (fCircle P) k‖ ^ 2) :=
      Summable.of_nonneg_of_le (fun k => by by_cases hk : k ∈ S <;> simp [hk])
        (fun k => by
          dsimp [g_norm]
          by_cases hk : k ∈ S
          · simp [hk]
          · simp only [hk, ↓reduceIte]
            have h1 := fourierCoeff_fCircle_norm_le_one P k
            nlinarith [norm_nonneg (fourierCoeff (fCircle P) k)])
        hgn_sum
    have hfin_sq : HasSum (fun k : ℤ => if k ∈ S then ‖fourierCoeff (fCircle P) k‖ ^ 2 else 0)
        (∑ k ∈ S, ‖fourierCoeff (fCircle P) k‖ ^ 2) := by
      have h : HasSum (fun k : ℤ => if k ∈ S then ‖fourierCoeff (fCircle P) k‖ ^ 2 else 0)
          (∑ k ∈ S, if k ∈ S then ‖fourierCoeff (fCircle P) k‖ ^ 2 else 0) :=
        hasSum_sum_of_ne_finset_zero (s := S) (fun k hk => by simp [hk])
      have hsum_eq : (∑ k ∈ S, if k ∈ S then ‖fourierCoeff (fCircle P) k‖ ^ 2 else 0) =
          ∑ k ∈ S, ‖fourierCoeff (fCircle P) k‖ ^ 2 :=
        Finset.sum_congr rfl fun k hk => by simp [hk]
      rwa [hsum_eq] at h
    have hsplit_sq : (∑' k : ℤ, ‖fourierCoeff (fCircle P) k‖ ^ 2) =
        (∑ k ∈ S, ‖fourierCoeff (fCircle P) k‖ ^ 2) +
        (∑' k : ℤ, if k ∈ S then (0 : ℝ) else ‖fourierCoeff (fCircle P) k‖ ^ 2) := by
      rw [← hfin_sq.tsum_eq, ← Summable.tsum_add hfin_sq.summable htail_sq_sum]
      congr 1; ext k; by_cases hk : k ∈ S <;> simp [hk]
    have htail_sq_le : (∑' k : ℤ, if k ∈ S then (0 : ℝ) else ‖fourierCoeff (fCircle P) k‖ ^ 2) ≤
        tailBound P M := by
      calc (∑' k : ℤ, if k ∈ S then (0 : ℝ) else ‖fourierCoeff (fCircle P) k‖ ^ 2)
          ≤ ∑' k : ℤ, g_norm k :=
            htail_sq_sum.tsum_le_tsum (fun k => by
              dsimp [g_norm]
              by_cases hk : k ∈ S
              · simp [hk]
              · simp only [hk, ↓reduceIte]
                have h1 := fourierCoeff_fCircle_norm_le_one P k
                nlinarith [norm_nonneg (fourierCoeff (fCircle P) k)]) hgn_sum
        _ ≤ tailBound P M := hgn_tsum_le
    linarith
  exact ⟨hflat, hparseval⟩

/- ## Section 5: Asymptotic parameter sequence and main theorem -/

private noncomputable def δSeq (n : ℕ) : ℝ := (n : ℝ) ^ (-(3 : ℝ) / 5)
private noncomputable def ηSeq (n : ℕ) : ℝ := (n : ℝ) ^ (-(1 : ℝ) / 10)
private noncomputable def MSeq (n : ℕ) : ℕ := ⌊(n : ℝ) ^ ((9 : ℝ) / 10)⌋₊
private noncomputable def NspanSeq (n : ℕ) : ℝ := (n : ℝ) - 2 * (MSeq n : ℝ) - 4
private noncomputable def posAreaSeq (n : ℕ) : ℝ := 2 * Real.pi + (B0 - 1) * ηSeq n - 2 * δSeq n
private noncomputable def ASeq (n : ℕ) : ℝ := NspanSeq n / posAreaSeq n
private noncomputable def hSeq (n : ℕ) : ℝ := (ASeq n) ^ (-(9 : ℝ) / 20)

private noncomputable def DSeq (P : Params) : ℝ :=
  (1 / (2 * Real.pi)) * (√(2 * Real.pi / P.A) + 3 * P.δ + 10 / (P.A * P.h) +
    2 * (2 * B0 * P.A / P.η) * P.h ^ 4)

private lemma tendsto_nat_rpow_neg {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (-r)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop hr).comp tendsto_natCast_atTop_atTop

private lemma eventually_params_good :
    ∀ᶠ n : ℕ in atTop,
      1 ≤ n ∧
      0 < δSeq n ∧ 0 < ηSeq n ∧ 4 * δSeq n < ηSeq n ∧ ηSeq n < 1 ∧
      2 * ηSeq n + 2 * δSeq n < 2 * Real.pi ∧
      0 < ASeq n ∧ 0 < hSeq n ∧ 2 * hSeq n < (ηSeq n - δSeq n) / 2 ∧
      3 / (ASeq n * hSeq n) ≤ 1 / √(ASeq n) ∧
      posAreaSeq n ≤ 10 ∧
      1 ≤ MSeq n ∧
      (1 / 2 : ℝ) * (n : ℝ) ^ ((9 : ℝ) / 10) ≤ (MSeq n : ℝ) ∧
      (1 / 20 : ℝ) * (n : ℝ) ≤ ASeq n ∧ ASeq n ≤ (n : ℝ) ∧
      (1 / 2 : ℝ) * (n : ℝ) ≤ NspanSeq n ∧
      (n : ℝ) ^ (-(1 : ℝ) / 10) ≤ 1 / 20 ∧
      (1 : ℝ) ≤ (n : ℝ) ^ ((9 : ℝ) / 10) := by
  have hδ0 : Tendsto δSeq atTop (𝓝 0) := by
    have h := tendsto_nat_rpow_neg (r := 3 / 5) (by norm_num)
    exact h.congr fun n => by unfold δSeq; congr 1; ring
  have hη0 : Tendsto ηSeq atTop (𝓝 0) := by
    have h := tendsto_nat_rpow_neg (r := 1 / 10) (by norm_num)
    exact h.congr fun n => by unfold ηSeq; congr 1; ring
  have h5 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 2)) atTop (𝓝 0) := by
    have h := tendsto_nat_rpow_neg (r := 1 / 2) (by norm_num)
    exact h.congr fun n => by congr 1; ring
  have h20 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 20)) atTop (𝓝 0) := by
    have h := tendsto_nat_rpow_neg (r := 1 / 20) (by norm_num)
    exact h.congr fun n => by congr 1; ring
  have h910 : Tendsto (fun n : ℕ => (n : ℝ) ^ ((9 : ℝ) / 10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hposArea : Tendsto posAreaSeq atTop (𝓝 (2 * Real.pi)) := by
    unfold posAreaSeq
    have h1 := (tendsto_const_nhds (x := 2 * Real.pi)).add (hη0.const_mul (B0 - 1))
    have h2 := h1.sub (hδ0.const_mul 2)
    simpa using h2
  have hev_n1 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  have hev_n100 : ∀ᶠ n : ℕ in atTop, (100 : ℝ) ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop 100)
  have hev_δ : ∀ᶠ n : ℕ in atTop, δSeq n < 1 / 4 :=
    hδ0.eventually (Iio_mem_nhds (by norm_num))
  have hev_η : ∀ᶠ n : ℕ in atTop, ηSeq n < 1 / 20 :=
    hη0.eventually (Iio_mem_nhds (by norm_num))
  have hev_half : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-(1 : ℝ) / 2) < 1 / 4 :=
    h5.eventually (Iio_mem_nhds (by norm_num))
  have hev_20 : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-(1 : ℝ) / 20) < 1 / 200 :=
    h20.eventually (Iio_mem_nhds (by norm_num))
  have hev_910 : ∀ᶠ n : ℕ in atTop, (4 : ℝ) ≤ (n : ℝ) ^ ((9 : ℝ) / 10) :=
    h910.eventually (eventually_ge_atTop 4)
  have hev_pa : ∀ᶠ n : ℕ in atTop, posAreaSeq n ≤ 10 :=
    hposArea.eventually (Iic_mem_nhds (by linarith [Real.pi_lt_four]))
  filter_upwards [hev_n1, hev_n100, hev_δ, hev_η, hev_half, hev_20, hev_910, hev_pa] with
    n hn1 hn100 hδlt hηlt hhalflt h20lt h910ge hpa10
  have hxpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hδpos : 0 < δSeq n := Real.rpow_pos_of_pos hxpos _
  have hηpos : 0 < ηSeq n := Real.rpow_pos_of_pos hxpos _
  have hδη : 4 * δSeq n < ηSeq n := by
    have hmul : δSeq n = ηSeq n * (n : ℝ) ^ (-(1 : ℝ) / 2) := by
      unfold δSeq ηSeq
      rw [← Real.rpow_add hxpos]
      congr 1; norm_num
    rw [hmul]
    nlinarith
  have hη1 : ηSeq n < 1 := by linarith
  have h2π : 2 * ηSeq n + 2 * δSeq n < 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hM_le : (MSeq n : ℝ) ≤ (n : ℝ) ^ ((9 : ℝ) / 10) := Nat.floor_le (by positivity)
  have hM_gt : (n : ℝ) ^ ((9 : ℝ) / 10) - 1 < (MSeq n : ℝ) := by
    unfold MSeq
    linarith [Nat.lt_floor_add_one ((n : ℝ) ^ ((9 : ℝ) / 10))]
  have hM_lo : (1 / 2 : ℝ) * (n : ℝ) ^ ((9 : ℝ) / 10) ≤ (MSeq n : ℝ) := by linarith
  have hM1 : 1 ≤ MSeq n := by
    have : (1 : ℝ) ≤ (MSeq n : ℝ) := by linarith
    exact_mod_cast this
  have h910_le_n : (n : ℝ) ^ ((9 : ℝ) / 10) = (n : ℝ) * ηSeq n := by
    unfold ηSeq
    conv_lhs => rw [show (9 : ℝ) / 10 = 1 + (-(1 : ℝ) / 10) by norm_num]
    rw [Real.rpow_add hxpos, Real.rpow_one]
  have hNspan_lo : (1 / 2 : ℝ) * (n : ℝ) ≤ NspanSeq n := by
    unfold NspanSeq
    have h1 : (MSeq n : ℝ) ≤ (n : ℝ) * (1 / 20) := by nlinarith
    linarith
  have hpa_gt : 2 * Real.pi < posAreaSeq n := by
    unfold posAreaSeq B0; linarith
  have hpa_pos : 0 < posAreaSeq n := lt_trans (by positivity) hpa_gt
  have hA_lo : (1 / 20 : ℝ) * (n : ℝ) ≤ ASeq n := by
    unfold ASeq
    rw [le_div_iff₀ hpa_pos]
    nlinarith
  have hA_pos : 0 < ASeq n := lt_of_lt_of_le (by positivity) hA_lo
  have hA_hi : ASeq n ≤ (n : ℝ) := by
    unfold ASeq
    rw [div_le_iff₀ hpa_pos]
    have hNle : NspanSeq n ≤ (n : ℝ) := by unfold NspanSeq; linarith [Nat.cast_nonneg (α := ℝ) (MSeq n)]
    have hpa1 : 1 ≤ posAreaSeq n := by linarith [Real.pi_gt_three]
    nlinarith
  have hh_pos : 0 < hSeq n := Real.rpow_pos_of_pos hA_pos _
  have h20_pow : (20 : ℝ) ^ ((9 : ℝ) / 20) ≤ 20 := by
    calc (20 : ℝ) ^ ((9 : ℝ) / 20) ≤ (20 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 20 := Real.rpow_one 20
  have hh_ub : hSeq n ≤ 20 * (n : ℝ) ^ (-(9 : ℝ) / 20) := by
    unfold hSeq
    have h1 : (ASeq n) ^ (-(9 : ℝ) / 20) ≤ ((1 / 20 : ℝ) * (n : ℝ)) ^ (-(9 : ℝ) / 20) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hA_lo (by norm_num)
    have h2 : ((1 / 20 : ℝ) * (n : ℝ)) ^ (-(9 : ℝ) / 20) =
        (20 : ℝ) ^ ((9 : ℝ) / 20) * (n : ℝ) ^ (-(9 : ℝ) / 20) := by
      rw [Real.mul_rpow (by positivity) hxpos.le]
      congr 1
      rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
      congr 1; norm_num
    rw [h2] at h1
    calc (ASeq n) ^ (-(9 : ℝ) / 20) ≤ (20 : ℝ) ^ ((9 : ℝ) / 20) * (n : ℝ) ^ (-(9 : ℝ) / 20) := h1
      _ ≤ 20 * (n : ℝ) ^ (-(9 : ℝ) / 20) :=
          mul_le_mul_of_nonneg_right h20_pow (Real.rpow_nonneg hxpos.le _)
  have hh_small : 2 * hSeq n < (ηSeq n - δSeq n) / 2 := by
    have h720 : (n : ℝ) ^ (-(7 : ℝ) / 20) ≤ (n : ℝ) ^ (-(1 : ℝ) / 20) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ (n : ℝ)) (by norm_num)
    have hfac : (n : ℝ) ^ (-(9 : ℝ) / 20) = ηSeq n * (n : ℝ) ^ (-(7 : ℝ) / 20) := by
      unfold ηSeq; rw [← Real.rpow_add hxpos]; congr 1; norm_num
    have h40 : 2 * hSeq n ≤ 40 * ηSeq n * (n : ℝ) ^ (-(1 : ℝ) / 20) := by
      calc 2 * hSeq n ≤ 2 * (20 * (n : ℝ) ^ (-(9 : ℝ) / 20)) := by linarith
        _ = 40 * ηSeq n * (n : ℝ) ^ (-(7 : ℝ) / 20) := by rw [hfac]; ring
        _ ≤ 40 * ηSeq n * (n : ℝ) ^ (-(1 : ℝ) / 20) := by gcongr
    have h1 : 40 * ηSeq n * (n : ℝ) ^ (-(1 : ℝ) / 20) < (1 / 5 : ℝ) * ηSeq n := by
      nlinarith only [hηpos, h20lt]
    have h2 : (3 / 8 : ℝ) * ηSeq n < (ηSeq n - δSeq n) / 2 := by linarith only [hδη]
    linarith only [h40, h1, h2, hηpos]
  have hstep : 3 / (ASeq n * hSeq n) ≤ 1 / √(ASeq n) := by
    have hAh_pos : 0 < ASeq n * hSeq n := mul_pos hA_pos hh_pos
    have hsqA_pos : 0 < √(ASeq n) := Real.sqrt_pos.mpr hA_pos
    rw [div_le_div_iff₀ hAh_pos hsqA_pos, one_mul]
    have hprod : ASeq n * hSeq n = √(ASeq n) * (ASeq n) ^ ((1 : ℝ) / 20) := by
      unfold hSeq
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hA_pos]
      have h1 : ASeq n * (ASeq n) ^ (-(9 : ℝ) / 20) = (ASeq n) ^ (1 : ℝ) * (ASeq n) ^ (-(9 : ℝ) / 20) := by
        rw [Real.rpow_one]
      rw [h1, ← Real.rpow_add hA_pos]
      congr 1; norm_num
    rw [hprod]
    have hA120 : (3 : ℝ) ≤ (ASeq n) ^ ((1 : ℝ) / 20) := by
      have hge1 : (20 : ℝ) ^ (-(1 : ℝ) / 20) * (n : ℝ) ^ ((1 : ℝ) / 20) ≤ (ASeq n) ^ ((1 : ℝ) / 20) := by
        calc (20 : ℝ) ^ (-(1 : ℝ) / 20) * (n : ℝ) ^ ((1 : ℝ) / 20)
            = ((1 / 20 : ℝ) * (n : ℝ)) ^ ((1 : ℝ) / 20) := by
              rw [Real.mul_rpow (by positivity) hxpos.le]
              congr 1
              rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
              congr 1; ring
          _ ≤ (ASeq n) ^ ((1 : ℝ) / 20) :=
              Real.rpow_le_rpow (by positivity) hA_lo (by norm_num)
      have h20neg : (1 / 20 : ℝ) ≤ (20 : ℝ) ^ (-(1 : ℝ) / 20) := by
        calc (1 / 20 : ℝ) = (20 : ℝ) ^ (-1 : ℝ) := by rw [Real.rpow_neg_one, one_div]
          _ ≤ (20 : ℝ) ^ (-(1 : ℝ) / 20) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      have hn120 : (200 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 20) := by
        have hinv : (n : ℝ) ^ ((1 : ℝ) / 20) = ((n : ℝ) ^ (-(1 : ℝ) / 20))⁻¹ := by
          rw [show (-(1 : ℝ) / 20) = -((1 : ℝ) / 20) by ring, Real.rpow_neg hxpos.le, inv_inv]
        rw [hinv]
        have hp : 0 < (n : ℝ) ^ (-(1 : ℝ) / 20) := Real.rpow_pos_of_pos hxpos _
        rw [le_inv_comm₀ (by norm_num) hp]
        linarith
      nlinarith only [hge1, h20neg, hn120]
    nlinarith only [hsqA_pos, hA120]
  exact ⟨hn1, hδpos, hηpos, hδη, hη1, h2π, hA_pos, hh_pos, hh_small, hstep, hpa10,
    hM1, hM_lo, hA_lo, hA_hi, hNspan_lo, hηlt.le, by linarith⟩

private lemma poly_shift_norm (n M : ℕ) (a : ℤ → ℂ) (θ : ℝ) :
    ‖∑ k : Fin n, a ((k.val : ℤ) - (M : ℤ)) *
      (Complex.exp ((θ : ℂ) * Complex.I)) ^ (k.val + 1)‖ =
    ‖∑ j ∈ Finset.Ico (-(M : ℤ)) ((n : ℤ) - (M : ℤ)),
      a j * fourier (T := 2 * Real.pi) j (θ : AddCircle (2 * Real.pi))‖ := by
  set z : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
  set phase : ℂ := Complex.exp (((M : ℂ) + 1) * (θ : ℂ) * Complex.I)
  have hphase_norm : ‖phase‖ = 1 := by
    dsimp [phase]
    have : ((M : ℂ) + 1) * (θ : ℂ) * Complex.I = ((((M : ℝ) + 1) * θ : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this]
    exact Complex.norm_exp_ofReal_mul_I _
  have hterm : ∀ k : Fin n,
      a ((k.val : ℤ) - (M : ℤ)) * z ^ (k.val + 1) =
      phase * (a ((k.val : ℤ) - (M : ℤ)) *
        (fourier (T := 2 * Real.pi) ((k.val : ℤ) - (M : ℤ)) (θ : AddCircle (2 * Real.pi)) : ℂ)) := by
    intro k
    rw [fourier_two_pi_apply]
    dsimp only [z, phase]
    rw [← Complex.exp_nat_mul]
    conv_rhs => rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [hterm, ← Finset.mul_sum, norm_mul, hphase_norm, one_mul]
  congr 1
  refine Finset.sum_bij (fun (k : Fin n) _ => (k.val : ℤ) - (M : ℤ)) ?_ ?_ ?_ ?_
  · intro k _
    rw [Finset.mem_Ico]
    have := k.isLt
    omega
  · intro k1 _ k2 _ h
    exact Fin.ext (by omega)
  · intro j hj
    rw [Finset.mem_Ico] at hj
    refine ⟨⟨(j + (M : ℤ)).toNat, by omega⟩, Finset.mem_univ _, ?_⟩
    dsimp
    omega
  · intro k _; rfl

private lemma sum_sq_shift (n M : ℕ) (a : ℤ → ℝ) :
    ∑ k : Fin n, a ((k.val : ℤ) - (M : ℤ)) =
    ∑ j ∈ Finset.Ico (-(M : ℤ)) ((n : ℤ) - (M : ℤ)), a j := by
  refine Finset.sum_bij (fun (k : Fin n) _ => (k.val : ℤ) - (M : ℤ)) ?_ ?_ ?_ ?_
  · intro k _
    rw [Finset.mem_Ico]
    have := k.isLt
    omega
  · intro k1 _ k2 _ h
    exact Fin.ext (by omega)
  · intro j hj
    rw [Finset.mem_Ico] at hj
    refine ⟨⟨(j + (M : ℤ)).toNat, by omega⟩, Finset.mem_univ _, ?_⟩
    dsimp
    omega
  · intro k _; rfl

private lemma DSeq_mul_sqrt_sub_le (n : ℕ) (P : Params)
    (hδeq : P.δ = δSeq n) (hηeq : P.η = ηSeq n) (hAeq : P.A = ASeq n) (hheq : P.h = hSeq n)
    (hn1 : 1 ≤ n) (hAlo : (1 / 20 : ℝ) * (n : ℝ) ≤ P.A)
    (hNspan_lo : (1 / 2 : ℝ) * (n : ℝ) ≤ NspanSeq n)
    (h10le : (n : ℝ) ^ (-(1 : ℝ) / 10) ≤ 1 / 20)
    (h910ge1 : (1 : ℝ) ≤ (n : ℝ) ^ ((9 : ℝ) / 10)) :
    DSeq P * √(n : ℝ) - 1 ≤ 12000 * (n : ℝ) ^ (-(1 : ℝ) / 20) := by
  have hxpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hxge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hApos : 0 < P.A := P.hA_pos
  have h10_le_20 : (n : ℝ) ^ (-(1 : ℝ) / 10) ≤ (n : ℝ) ^ (-(1 : ℝ) / 20) :=
    Real.rpow_le_rpow_of_exponent_le hxge1 (by norm_num)
  have h5_le_20 : (n : ℝ) ^ (-(1 : ℝ) / 5) ≤ (n : ℝ) ^ (-(1 : ℝ) / 20) :=
    Real.rpow_le_rpow_of_exponent_le hxge1 (by norm_num)
  have hM_le : (MSeq n : ℝ) ≤ (n : ℝ) ^ ((9 : ℝ) / 10) := Nat.floor_le (by positivity)
  have ht1 : (1 / (2 * Real.pi)) * √(2 * Real.pi / P.A) * √(n : ℝ) - 1 ≤
      200 * (n : ℝ) ^ (-(1 : ℝ) / 20) := by
    have hrew : (1 / (2 * Real.pi)) * √(2 * Real.pi / P.A) * √(n : ℝ) =
        √((n : ℝ) / (2 * Real.pi * P.A)) := by
      have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
      rw [Real.sqrt_div h2pi_pos.le, Real.sqrt_div hxpos.le, Real.sqrt_mul h2pi_pos.le]
      have hs1 : √(2 * Real.pi) ≠ 0 := (Real.sqrt_pos.mpr h2pi_pos).ne'
      have hs2 : √P.A ≠ 0 := (Real.sqrt_pos.mpr hApos).ne'
      field_simp [hs1, hs2]
      nlinarith only [Real.sq_sqrt h2pi_pos.le]
    rw [hrew]
    have hpa_eq : posArea P = posAreaSeq n := by unfold posArea posAreaSeq; rw [hηeq, hδeq]
    have hratio : (n : ℝ) / (2 * Real.pi * P.A) =
        ((n : ℝ) / NspanSeq n) * (posArea P / (2 * Real.pi)) := by
      have hpa_pos : 0 < posArea P := posArea_pos P
      have hNs_pos : 0 < NspanSeq n := by linarith only [hxpos, hNspan_lo]
      rw [hAeq]
      unfold ASeq
      rw [← hpa_eq]
      field_simp [hpa_pos.ne', hNs_pos.ne', Real.pi_pos.ne']
    have hf1 : (n : ℝ) / NspanSeq n ≤ 1 + 12 * (n : ℝ) ^ (-(1 : ℝ) / 10) := by
      have hNs_pos : 0 < NspanSeq n := by linarith only [hxpos, hNspan_lo]
      rw [div_le_iff₀ hNs_pos]
      have h910_eq : (n : ℝ) ^ ((9 : ℝ) / 10) = (n : ℝ) * (n : ℝ) ^ (-(1 : ℝ) / 10) := by
        conv_lhs => rw [show (9 : ℝ) / 10 = 1 + (-(1 : ℝ) / 10) by norm_num]
        rw [Real.rpow_add hxpos, Real.rpow_one]
      have hprod : (n : ℝ) - NspanSeq n = 2 * (MSeq n : ℝ) + 4 := by unfold NspanSeq; ring
      have h2M4 : (n : ℝ) - NspanSeq n ≤ 6 * (n : ℝ) * (n : ℝ) ^ (-(1 : ℝ) / 10) := by
        linarith only [hprod, hM_le, h910ge1, h910_eq]
      have hnn : 0 ≤ (n : ℝ) ^ (-(1 : ℝ) / 10) := Real.rpow_nonneg hxpos.le _
      have hmul : 6 * (n : ℝ) * (n : ℝ) ^ (-(1 : ℝ) / 10) ≤
          12 * (n : ℝ) ^ (-(1 : ℝ) / 10) * NspanSeq n := by
        nlinarith only [hNspan_lo, hnn]
      linarith only [h2M4, hmul]
    have hf2 : posArea P / (2 * Real.pi) ≤ 1 + 25 * (n : ℝ) ^ (-(1 : ℝ) / 10) := by
      rw [div_le_iff₀ (by positivity)]
      unfold posArea B0
      rw [hηeq]
      unfold ηSeq
      have hnn : 0 ≤ (n : ℝ) ^ (-(1 : ℝ) / 10) := Real.rpow_nonneg hxpos.le _
      have hpi := Real.pi_gt_three
      have hδp := P.hδ_pos
      nlinarith only [hnn, hpi, hδp]
    have hprod_le : (n : ℝ) / (2 * Real.pi * P.A) ≤ 1 + 200 * (n : ℝ) ^ (-(1 : ℝ) / 10) := by
      rw [hratio]
      have hnn2 : 0 ≤ posArea P / (2 * Real.pi) := div_nonneg (posArea_pos P).le (by positivity)
      have h1 : (n : ℝ) / NspanSeq n * (posArea P / (2 * Real.pi)) ≤
          (1 + 12 * (n : ℝ) ^ (-(1 : ℝ) / 10)) * (1 + 25 * (n : ℝ) ^ (-(1 : ℝ) / 10)) :=
        mul_le_mul hf1 hf2 hnn2 (by positivity)
      have hnn : 0 ≤ (n : ℝ) ^ (-(1 : ℝ) / 10) := Real.rpow_nonneg hxpos.le _
      nlinarith only [h1, hnn, h10le]
    have hsq_le : √((n : ℝ) / (2 * Real.pi * P.A)) ≤ 1 + 200 * (n : ℝ) ^ (-(1 : ℝ) / 10) := by
      have hnn : 0 ≤ (n : ℝ) ^ (-(1 : ℝ) / 10) := Real.rpow_nonneg hxpos.le _
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      nlinarith only [hprod_le, hnn]
    linarith only [hsq_le, h10_le_20]
  have ht2 : (1 / (2 * Real.pi)) * (3 * P.δ) * √(n : ℝ) ≤ (n : ℝ) ^ (-(1 : ℝ) / 20) := by
    have hprod : P.δ * √(n : ℝ) = (n : ℝ) ^ (-(1 : ℝ) / 10) := by
      rw [hδeq]; unfold δSeq
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hxpos]
      congr 1; norm_num
    have hcoeff : 3 / (2 * Real.pi) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [Real.pi_gt_three]
    have hnn : 0 ≤ (n : ℝ) ^ (-(1 : ℝ) / 10) := Real.rpow_nonneg hxpos.le _
    calc (1 / (2 * Real.pi)) * (3 * P.δ) * √(n : ℝ)
        = (3 / (2 * Real.pi)) * (P.δ * √(n : ℝ)) := by ring
      _ = (3 / (2 * Real.pi)) * (n : ℝ) ^ (-(1 : ℝ) / 10) := by rw [hprod]
      _ ≤ 1 * (n : ℝ) ^ (-(1 : ℝ) / 10) := mul_le_mul_of_nonneg_right hcoeff hnn
      _ ≤ (n : ℝ) ^ (-(1 : ℝ) / 20) := by linarith only [h10_le_20]
  have ht3 : (1 / (2 * Real.pi)) * (10 / (P.A * P.h)) * √(n : ℝ) ≤
      200 * (n : ℝ) ^ (-(1 : ℝ) / 20) := by
    have hAh : P.A * P.h = P.A ^ ((11 : ℝ) / 20) := by
      rw [hheq]; unfold hSeq; rw [← hAeq]
      have h1 : P.A * P.A ^ (-(9 : ℝ) / 20) = P.A ^ (1 : ℝ) * P.A ^ (-(9 : ℝ) / 20) := by
        rw [Real.rpow_one]
      rw [h1, ← Real.rpow_add hApos]
      congr 1; norm_num
    have hAh_lo : (1 / 20 : ℝ) * (n : ℝ) ^ ((11 : ℝ) / 20) ≤ P.A * P.h := by
      rw [hAh]
      have h1 : ((1 / 20 : ℝ) * (n : ℝ)) ^ ((11 : ℝ) / 20) ≤ P.A ^ ((11 : ℝ) / 20) :=
        Real.rpow_le_rpow (by positivity) hAlo (by norm_num)
      rw [Real.mul_rpow (by positivity) hxpos.le] at h1
      have h2 : (1 / 20 : ℝ) ≤ (1 / 20 : ℝ) ^ ((11 : ℝ) / 20) := by
        calc (1 / 20 : ℝ) = (1 / 20 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (1 / 20 : ℝ) ^ ((11 : ℝ) / 20) :=
            Real.rpow_le_rpow_of_exponent_ge (by positivity) (by norm_num) (by norm_num)
      calc (1 / 20 : ℝ) * (n : ℝ) ^ ((11 : ℝ) / 20)
          ≤ (1 / 20 : ℝ) ^ ((11 : ℝ) / 20) * (n : ℝ) ^ ((11 : ℝ) / 20) :=
            mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hxpos.le _)
        _ ≤ P.A ^ ((11 : ℝ) / 20) := h1
    have hinv : 1 / (P.A * P.h) ≤ 20 * (n : ℝ) ^ (-(11 : ℝ) / 20) := by
      have h1 := one_div_le_one_div_of_le (by positivity) hAh_lo
      calc 1 / (P.A * P.h) ≤ 1 / ((1 / 20 : ℝ) * (n : ℝ) ^ ((11 : ℝ) / 20)) := h1
        _ = 20 * ((n : ℝ) ^ ((11 : ℝ) / 20))⁻¹ := by ring
        _ = 20 * (n : ℝ) ^ (-(11 : ℝ) / 20) := by
            rw [show (-(11 : ℝ) / 20) = -((11 : ℝ) / 20) by ring, Real.rpow_neg hxpos.le]
    have hprod : (n : ℝ) ^ (-(11 : ℝ) / 20) * √(n : ℝ) = (n : ℝ) ^ (-(1 : ℝ) / 20) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hxpos]; congr 1; norm_num
    have h2pi1 : (1 : ℝ) / (2 * Real.pi) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [Real.pi_gt_three]
    calc (1 / (2 * Real.pi)) * (10 / (P.A * P.h)) * √(n : ℝ)
        = (1 / (2 * Real.pi)) * 10 * ((1 / (P.A * P.h)) * √(n : ℝ)) := by ring
      _ ≤ 1 * 10 * ((20 * (n : ℝ) ^ (-(11 : ℝ) / 20)) * √(n : ℝ)) := by
          have := P.hh_pos; gcongr
      _ = 200 * ((n : ℝ) ^ (-(11 : ℝ) / 20) * √(n : ℝ)) := by ring
      _ = 200 * (n : ℝ) ^ (-(1 : ℝ) / 20) := by rw [hprod]
  have ht4 : (1 / (2 * Real.pi)) * (2 * (2 * B0 * P.A / P.η) * P.h ^ 4) * √(n : ℝ) ≤
      11000 * (n : ℝ) ^ (-(1 : ℝ) / 20) := by
    have hAh4 : P.A * P.h ^ 4 = P.A ^ (-(4 : ℝ) / 5) := by
      rw [hheq]; unfold hSeq; rw [← hAeq]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hApos.le]
      have h1 : P.A * P.A ^ (-(9 : ℝ) / 20 * (4 : ℕ)) =
          P.A ^ (1 : ℝ) * P.A ^ (-(9 : ℝ) / 20 * (4 : ℕ)) := by rw [Real.rpow_one]
      rw [h1, ← Real.rpow_add hApos]
      congr 1; norm_num
    have hAh4_ub : P.A * P.h ^ 4 ≤ 20 * (n : ℝ) ^ (-(4 : ℝ) / 5) := by
      rw [hAh4]
      have h1 : P.A ^ (-(4 : ℝ) / 5) ≤ ((1 / 20 : ℝ) * (n : ℝ)) ^ (-(4 : ℝ) / 5) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hAlo (by norm_num)
      rw [Real.mul_rpow (by positivity) hxpos.le] at h1
      have h2 : (1 / 20 : ℝ) ^ (-(4 : ℝ) / 5) ≤ 20 := by
        rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num),
          show -(-(4 : ℝ) / 5) = 4 / 5 by ring]
        calc (20 : ℝ) ^ ((4 : ℝ) / 5) ≤ (20 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 20 := Real.rpow_one 20
      calc P.A ^ (-(4 : ℝ) / 5)
          ≤ (1 / 20 : ℝ) ^ (-(4 : ℝ) / 5) * (n : ℝ) ^ (-(4 : ℝ) / 5) := h1
        _ ≤ 20 * (n : ℝ) ^ (-(4 : ℝ) / 5) :=
            mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hxpos.le _)
    have hprod : (n : ℝ) ^ (-(4 : ℝ) / 5) / P.η * √(n : ℝ) = (n : ℝ) ^ (-(1 : ℝ) / 5) := by
      rw [hηeq]; unfold ηSeq
      rw [← Real.rpow_sub hxpos, Real.sqrt_eq_rpow, ← Real.rpow_add hxpos]
      congr 1; norm_num
    have h2pi1 : (1 : ℝ) / (2 * Real.pi) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [Real.pi_gt_three]
    have hηp := P.hη_pos
    have h80 : (80 * B0) * (n : ℝ) ^ (-(1 : ℝ) / 5) ≤ 11000 * (n : ℝ) ^ (-(1 : ℝ) / 20) := by
      unfold B0; linarith only [h5_le_20, Real.rpow_nonneg hxpos.le (-(1 : ℝ) / 20)]
    calc (1 / (2 * Real.pi)) * (2 * (2 * B0 * P.A / P.η) * P.h ^ 4) * √(n : ℝ)
        = (1 / (2 * Real.pi)) * (4 * B0) * ((P.A * P.h ^ 4) / P.η * √(n : ℝ)) := by ring
      _ ≤ 1 * (4 * B0) * ((20 * (n : ℝ) ^ (-(4 : ℝ) / 5)) / P.η * √(n : ℝ)) := by
          unfold B0; gcongr
      _ = (80 * B0) * ((n : ℝ) ^ (-(4 : ℝ) / 5) / P.η * √(n : ℝ)) := by ring
      _ = (80 * B0) * (n : ℝ) ^ (-(1 : ℝ) / 5) := by rw [hprod]
      _ ≤ 11000 * (n : ℝ) ^ (-(1 : ℝ) / 20) := h80
  have hD_expand : DSeq P * √(n : ℝ) - 1 =
      ((1 / (2 * Real.pi)) * √(2 * Real.pi / P.A) * √(n : ℝ) - 1) +
      (1 / (2 * Real.pi)) * (3 * P.δ) * √(n : ℝ) +
      (1 / (2 * Real.pi)) * (10 / (P.A * P.h)) * √(n : ℝ) +
      (1 / (2 * Real.pi)) * (2 * (2 * B0 * P.A / P.η) * P.h ^ 4) * √(n : ℝ) := by
    unfold DSeq; ring
  linarith only [hD_expand, ht1, ht2, ht3, ht4, Real.rpow_nonneg hxpos.le (-(1 : ℝ) / 20)]

private lemma tailBound_seq_le (n : ℕ) (P : Params)
    (hδeq : P.δ = δSeq n) (hn1 : 1 ≤ n)
    (hMlo : (1 / 2 : ℝ) * (n : ℝ) ^ ((9 : ℝ) / 10) ≤ (MSeq n : ℝ))
    (hAhi : P.A ≤ (n : ℝ)) :
    tailBound P (MSeq n) ≤ 5000000 * (n : ℝ) ^ (-(1 : ℝ) / 20) := by
  have hxpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hxge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hδpos : 0 < P.δ := P.hδ_pos
  have hApos : 0 < P.A := P.hA_pos
  have h10_le_20 : (n : ℝ) ^ (-(1 : ℝ) / 10) ≤ (n : ℝ) ^ (-(1 : ℝ) / 20) :=
    Real.rpow_le_rpow_of_exponent_le hxge1 (by norm_num)
  have h5_le_20 : (n : ℝ) ^ (-(1 : ℝ) / 5) ≤ (n : ℝ) ^ (-(1 : ℝ) / 20) :=
    Real.rpow_le_rpow_of_exponent_le hxge1 (by norm_num)
  have hδ_le1 : P.δ ≤ 1 := by
    rw [hδeq]; unfold δSeq
    exact Real.rpow_le_one_of_one_le_of_nonpos hxge1 (by norm_num)
  have hinv_δ : 1 / P.δ = (n : ℝ) ^ ((3 : ℝ) / 5) := by
    rw [hδeq]; unfold δSeq
    rw [one_div, show (-(3 : ℝ) / 5) = -((3 : ℝ) / 5) by ring, Real.rpow_neg hxpos.le, inv_inv]
  have hM2_lo : (1 / 4 : ℝ) * (n : ℝ) ^ ((9 : ℝ) / 5) ≤ (MSeq n : ℝ) ^ 2 := by
    have hsq : ((1 / 2 : ℝ) * (n : ℝ) ^ ((9 : ℝ) / 10)) ^ 2 ≤ (MSeq n : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hMlo 2
    have hpow : ((n : ℝ) ^ ((9 : ℝ) / 10)) ^ 2 = (n : ℝ) ^ ((9 : ℝ) / 5) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]; congr 1; norm_num
    have hmul : ((1 / 2 : ℝ) * (n : ℝ) ^ ((9 : ℝ) / 10)) ^ 2 =
        (1 / 4 : ℝ) * ((n : ℝ) ^ ((9 : ℝ) / 10)) ^ 2 := by ring
    linarith only [hsq, hpow, hmul]
  have hM3_lo : (1 / 8 : ℝ) * (n : ℝ) ^ ((27 : ℝ) / 10) ≤ (MSeq n : ℝ) ^ 3 := by
    have hcu : ((1 / 2 : ℝ) * (n : ℝ) ^ ((9 : ℝ) / 10)) ^ 3 ≤ (MSeq n : ℝ) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hMlo 3
    have hpow : ((n : ℝ) ^ ((9 : ℝ) / 10)) ^ 3 = (n : ℝ) ^ ((27 : ℝ) / 10) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]; congr 1; norm_num
    have hcube : ((1 / 2 : ℝ) * (n : ℝ) ^ ((9 : ℝ) / 10)) ^ 3 =
        (1 / 8 : ℝ) * ((n : ℝ) ^ ((9 : ℝ) / 10)) ^ 3 := by ring
    linarith only [hcu, hpow, hcube]
  have hb1 : P.A * (4 * B0 + 40 / P.δ) / (MSeq n : ℝ) ^ 2 ≤ 3000 * (n : ℝ) ^ (-(1 : ℝ) / 20) := by
    have hnum : 4 * B0 + 40 / P.δ ≤ 600 / P.δ := by
      have h1 : 4 * B0 ≤ 560 / P.δ := by
        rw [le_div_iff₀ hδpos]; unfold B0; linarith only [hδ_le1]
      have h2 : (560 : ℝ) / P.δ + 40 / P.δ = 600 / P.δ := by ring
      linarith only [h1, h2]
    have h1 : P.A * (4 * B0 + 40 / P.δ) / (MSeq n : ℝ) ^ 2 ≤
        (n : ℝ) * (600 / P.δ) / ((1 / 4 : ℝ) * (n : ℝ) ^ ((9 : ℝ) / 5)) := by
      apply div_le_div₀ (by positivity)
      · exact mul_le_mul hAhi hnum (by unfold B0; positivity) hxpos.le
      · positivity
      · exact hM2_lo
    have h2 : (n : ℝ) * (600 / P.δ) / ((1 / 4 : ℝ) * (n : ℝ) ^ ((9 : ℝ) / 5)) =
        2400 * (n : ℝ) ^ (-(1 : ℝ) / 5) := by
      rw [show 600 / P.δ = 600 * (1 / P.δ) by ring, hinv_δ]
      have heq : (n : ℝ) * (n : ℝ) ^ ((3 : ℝ) / 5) / (n : ℝ) ^ ((9 : ℝ) / 5) =
          (n : ℝ) ^ (-(1 : ℝ) / 5) := by
        have h1' : (n : ℝ) * (n : ℝ) ^ ((3 : ℝ) / 5) = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ ((3 : ℝ) / 5) := by
          rw [Real.rpow_one]
        rw [h1', ← Real.rpow_add hxpos, ← Real.rpow_sub hxpos]
        congr 1; norm_num
      calc (n : ℝ) * (600 * (n : ℝ) ^ ((3 : ℝ) / 5)) / ((1 / 4 : ℝ) * (n : ℝ) ^ ((9 : ℝ) / 5))
          = 2400 * ((n : ℝ) * (n : ℝ) ^ ((3 : ℝ) / 5) / (n : ℝ) ^ ((9 : ℝ) / 5)) := by ring
        _ = 2400 * (n : ℝ) ^ (-(1 : ℝ) / 5) := by rw [heq]
    linarith only [h1, h2, h5_le_20, Real.rpow_nonneg hxpos.le (-(1 : ℝ) / 20)]
  have hb2 : 3 * P.A ^ 2 * (2 * Real.pi * B0 ^ 2 + 400 / P.δ) / (MSeq n : ℝ) ^ 3 ≤
      4900000 * (n : ℝ) ^ (-(1 : ℝ) / 20) := by
    have hnum : 2 * Real.pi * B0 ^ 2 + 400 / P.δ ≤ 200000 / P.δ := by
      have h1 : 2 * Real.pi * B0 ^ 2 ≤ 199600 / P.δ := by
        rw [le_div_iff₀ hδpos]; unfold B0; nlinarith only [Real.pi_lt_four, Real.pi_pos, hδ_le1, hδpos]
      have h2 : (199600 : ℝ) / P.δ + 400 / P.δ = 200000 / P.δ := by ring
      linarith only [h1, h2]
    have h1 : 3 * P.A ^ 2 * (2 * Real.pi * B0 ^ 2 + 400 / P.δ) / (MSeq n : ℝ) ^ 3 ≤
        3 * (n : ℝ) ^ 2 * (200000 / P.δ) / ((1 / 8 : ℝ) * (n : ℝ) ^ ((27 : ℝ) / 10)) := by
      apply div_le_div₀ (by positivity)
      · have hA2 : P.A ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ hApos.le hAhi 2
        exact mul_le_mul (by linarith only [hA2]) hnum (by unfold B0; positivity) (by positivity)
      · positivity
      · exact hM3_lo
    have h2 : 3 * (n : ℝ) ^ 2 * (200000 / P.δ) / ((1 / 8 : ℝ) * (n : ℝ) ^ ((27 : ℝ) / 10)) =
        4800000 * (n : ℝ) ^ (-(1 : ℝ) / 10) := by
      rw [show 200000 / P.δ = 200000 * (1 / P.δ) by ring, hinv_δ]
      have heq : (n : ℝ) ^ 2 * (n : ℝ) ^ ((3 : ℝ) / 5) / (n : ℝ) ^ ((27 : ℝ) / 10) =
          (n : ℝ) ^ (-(1 : ℝ) / 10) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hxpos, ← Real.rpow_sub hxpos]
        congr 1; norm_num
      calc 3 * (n : ℝ) ^ 2 * (200000 * (n : ℝ) ^ ((3 : ℝ) / 5)) / ((1 / 8 : ℝ) * (n : ℝ) ^ ((27 : ℝ) / 10))
          = 4800000 * ((n : ℝ) ^ 2 * (n : ℝ) ^ ((3 : ℝ) / 5) / (n : ℝ) ^ ((27 : ℝ) / 10)) := by ring
        _ = 4800000 * (n : ℝ) ^ (-(1 : ℝ) / 10) := by rw [heq]
    linarith only [h1, h2, h10_le_20, Real.rpow_nonneg hxpos.le (-(1 : ℝ) / 20)]
  unfold tailBound
  have hpi1 : (1 : ℝ) / Real.pi ≤ 1 := by
    rw [div_le_one Real.pi_pos]; linarith [Real.pi_gt_three]
  have hsum_nn : 0 ≤ P.A * (4 * B0 + 40 / P.δ) / (MSeq n : ℝ) ^ 2 +
      3 * P.A ^ 2 * (2 * Real.pi * B0 ^ 2 + 400 / P.δ) / (MSeq n : ℝ) ^ 3 := by
    unfold B0; positivity
  calc (1 / Real.pi) * (P.A * (4 * B0 + 40 / P.δ) / (MSeq n : ℝ) ^ 2 +
        3 * P.A ^ 2 * (2 * Real.pi * B0 ^ 2 + 400 / P.δ) / (MSeq n : ℝ) ^ 3)
      ≤ 1 * (P.A * (4 * B0 + 40 / P.δ) / (MSeq n : ℝ) ^ 2 +
        3 * P.A ^ 2 * (2 * Real.pi * B0 ^ 2 + 400 / P.δ) / (MSeq n : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_right hpi1 hsum_nn
    _ ≤ 5000000 * (n : ℝ) ^ (-(1 : ℝ) / 20) := by
        linarith only [hb1, hb2, Real.rpow_nonneg hxpos.le (-(1 : ℝ) / 20)]

private lemma construct_at_large_n (n : ℕ)
    (hgood :
      1 ≤ n ∧
      0 < δSeq n ∧ 0 < ηSeq n ∧ 4 * δSeq n < ηSeq n ∧ ηSeq n < 1 ∧
      2 * ηSeq n + 2 * δSeq n < 2 * Real.pi ∧
      0 < ASeq n ∧ 0 < hSeq n ∧ 2 * hSeq n < (ηSeq n - δSeq n) / 2 ∧
      3 / (ASeq n * hSeq n) ≤ 1 / √(ASeq n) ∧
      posAreaSeq n ≤ 10 ∧
      1 ≤ MSeq n ∧
      (1 / 2 : ℝ) * (n : ℝ) ^ ((9 : ℝ) / 10) ≤ (MSeq n : ℝ) ∧
      (1 / 20 : ℝ) * (n : ℝ) ≤ ASeq n ∧ ASeq n ≤ (n : ℝ) ∧
      (1 / 2 : ℝ) * (n : ℝ) ≤ NspanSeq n ∧
      (n : ℝ) ^ (-(1 : ℝ) / 10) ≤ 1 / 20 ∧
      (1 : ℝ) ≤ (n : ℝ) ^ ((9 : ℝ) / 10)) :
    ∃ c : Fin n → ℂ,
      (∀ k, ‖c k‖ ≤ 1) ∧
      (∀ θ : ℝ, |‖∑ k : Fin n, c k * (Complex.exp ((θ : ℂ) * Complex.I)) ^ (k.val + 1)‖ / √(n : ℝ) - 1| ≤
        5020000 * (n : ℝ) ^ (-(1 : ℝ) / 20)) ∧
      (∑ k : Fin n, (1 - ‖c k‖ ^ 2)) ≤ 6000000 * (n : ℝ) * (n : ℝ) ^ (-(1 : ℝ) / 20) := by
  rcases hgood with ⟨hn1, hδpos, hηpos, hδη, hη1, h2π, hApos, hhpos, hhsmall, hstep,
    hpa10, hM1, hMlo, hAlo, hAhi, hNspan_lo, h10le, h910ge1⟩
  have : Fact (0 < 2 * Real.pi) := two_pi_pos_fact
  let P : Params := ⟨δSeq n, ηSeq n, ASeq n, hSeq n, hδpos, hηpos, hδη, hη1, h2π, hApos, hhpos, hhsmall⟩
  have hxpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hsqx_pos : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hxpos
  set D : ℝ := DSeq P
  have hD_ge_inv_sqrt : 1 / √(2 * Real.pi * P.A) ≤ D := by
    dsimp [D, DSeq]
    have h1 : (1 / (2 * Real.pi)) * √(2 * Real.pi / P.A) = 1 / √(2 * Real.pi * P.A) := by
      have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
      rw [Real.sqrt_div h2pi_pos.le, Real.sqrt_mul h2pi_pos.le]
      have hs1 : √(2 * Real.pi) ≠ 0 := (Real.sqrt_pos.mpr h2pi_pos).ne'
      have hs2 : √P.A ≠ 0 := (Real.sqrt_pos.mpr hApos).ne'
      field_simp [hs1, hs2]
      nlinarith only [Real.sq_sqrt h2pi_pos.le]
    have hrest : 0 ≤ 3 * P.δ + 10 / (P.A * P.h) + 2 * (2 * B0 * P.A / P.η) * P.h ^ 4 := by
      unfold B0; positivity
    have h2 : (1 / (2 * Real.pi)) * √(2 * Real.pi / P.A) ≤
        (1 / (2 * Real.pi)) * (√(2 * Real.pi / P.A) + 3 * P.δ + 10 / (P.A * P.h) +
          2 * (2 * B0 * P.A / P.η) * P.h ^ 4) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith only [hrest]
    linarith only [h1, h2]
  have h2piA_le_n : 2 * Real.pi * P.A ≤ (n : ℝ) := by
    have hpa_gt : 2 * Real.pi < posArea P := posArea_gt_two_pi P
    have hpa_pos : 0 < posArea P := posArea_pos P
    have hN_le : NspanSeq n ≤ (n : ℝ) := by
      unfold NspanSeq; linarith only [Nat.cast_nonneg (α := ℝ) (MSeq n)]
    change 2 * Real.pi * (NspanSeq n / posArea P) ≤ (n : ℝ)
    rw [mul_div_assoc', div_le_iff₀ hpa_pos]
    have hNs_nn : 0 ≤ NspanSeq n := by linarith only [hxpos, hNspan_lo]
    nlinarith only [hpa_gt, hN_le, hNs_nn, Real.pi_pos]
  have hDsqx_ge1 : 1 ≤ D * √(n : ℝ) := by
    have h1 : 1 / √(n : ℝ) ≤ 1 / √(2 * Real.pi * P.A) :=
      one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_le_sqrt h2piA_le_n)
    have h2 : 1 / √(n : ℝ) ≤ D := h1.trans hD_ge_inv_sqrt
    have h3 := mul_le_mul_of_nonneg_right h2 hsqx_pos.le
    rwa [one_div_mul_cancel hsqx_pos.ne'] at h3
  have hDpos : 0 < D := by nlinarith only [hDsqx_ge1, hsqx_pos]
  have hDsqx_sub_le : D * √(n : ℝ) - 1 ≤ 12000 * (n : ℝ) ^ (-(1 : ℝ) / 20) :=
    DSeq_mul_sqrt_sub_le n P rfl rfl rfl rfl hn1 hAlo hNspan_lo h10le h910ge1
  have hT_le : tailBound P (MSeq n) ≤ 5000000 * (n : ℝ) ^ (-(1 : ℝ) / 20) :=
    tailBound_seq_le n P rfl hn1 hMlo hAhi
  have hspan : P.A * posArea P + 1 ≤ (n : ℝ) - 2 * (MSeq n : ℝ) - 2 := by
    have hpa_pos : 0 < posArea P := posArea_pos P
    have hmul : P.A * posArea P = NspanSeq n := by
      change (NspanSeq n / posArea P) * posArea P = NspanSeq n
      exact div_mul_cancel₀ _ hpa_pos.ne'
    rw [hmul]; unfold NspanSeq; linarith
  obtain ⟨hflat, hparseval⟩ := fourier_tail_and_parseval P n (MSeq n) hM1 hpa10 hspan
  let c : Fin n → ℂ := fun k =>
    fourierCoeff (fCircle P) ((k.val : ℤ) - (MSeq n : ℤ)) / (D : ℂ)
  refine ⟨c, ?_, ?_, ?_⟩
  · intro k
    dsimp [c]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hDpos.le, div_le_one hDpos]
    exact fourierCoeff_fCircle_norm_le P hstep _
  · intro θ
    set S : Finset ℤ := Finset.Ico (-(MSeq n : ℤ)) ((n : ℤ) - (MSeq n : ℤ))
    have hpoly : ‖∑ k : Fin n, c k * (Complex.exp ((θ : ℂ) * Complex.I)) ^ (k.val + 1)‖ =
        (1 / D) * ‖∑ j ∈ S, fourierCoeff (fCircle P) j *
          fourier (T := 2 * Real.pi) j (θ : AddCircle (2 * Real.pi))‖ := by
      have hrew : (∑ k : Fin n, c k * (Complex.exp ((θ : ℂ) * Complex.I)) ^ (k.val + 1)) =
          ((1 / D : ℝ) : ℂ) * ∑ k : Fin n,
            fourierCoeff (fCircle P) ((k.val : ℤ) - (MSeq n : ℤ)) *
              (Complex.exp ((θ : ℂ) * Complex.I)) ^ (k.val + 1) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        dsimp [c]; push_cast; ring
      rw [hrew, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      congr 1
      exact poly_shift_norm n (MSeq n) (fourierCoeff (fCircle P)) θ
    rw [hpoly]
    set X : ℝ := ‖∑ j ∈ S, fourierCoeff (fCircle P) j *
      fourier (T := 2 * Real.pi) j (θ : AddCircle (2 * Real.pi))‖
    have hX : |X - 1| ≤ tailBound P (MSeq n) := hflat θ
    have hdiv_eq : 1 / D * X / √(n : ℝ) - 1 = (X - 1 - (D * √(n : ℝ) - 1)) / (D * √(n : ℝ)) := by
      field_simp [hDpos.ne', hsqx_pos.ne']
      ring
    have habs_D : |D * √(n : ℝ) - 1| = D * √(n : ℝ) - 1 :=
      abs_of_nonneg (by linarith only [hDsqx_ge1])
    rw [hdiv_eq, abs_div, abs_of_pos (mul_pos hDpos hsqx_pos)]
    calc |X - 1 - (D * √(n : ℝ) - 1)| / (D * √(n : ℝ))
        ≤ |X - 1 - (D * √(n : ℝ) - 1)| / 1 :=
          div_le_div_of_nonneg_left (abs_nonneg _) zero_lt_one hDsqx_ge1
      _ = |X - 1 - (D * √(n : ℝ) - 1)| := div_one _
      _ ≤ |X - 1| + |D * √(n : ℝ) - 1| := abs_sub _ _
      _ = |X - 1| + (D * √(n : ℝ) - 1) := by rw [habs_D]
      _ ≤ tailBound P (MSeq n) + 12000 * (n : ℝ) ^ (-(1 : ℝ) / 20) := add_le_add hX hDsqx_sub_le
      _ ≤ 5020000 * (n : ℝ) ^ (-(1 : ℝ) / 20) := by
          linarith only [hT_le, Real.rpow_nonneg hxpos.le (-(1 : ℝ) / 20)]
  · set S : Finset ℤ := Finset.Ico (-(MSeq n : ℤ)) ((n : ℤ) - (MSeq n : ℤ))
    have hsum_c : ∑ k : Fin n, ‖c k‖ ^ 2 =
        (1 / D ^ 2) * ∑ j ∈ S, ‖fourierCoeff (fCircle P) j‖ ^ 2 := by
      have hterm : ∀ k : Fin n, ‖c k‖ ^ 2 =
          (1 / D ^ 2) * ‖fourierCoeff (fCircle P) ((k.val : ℤ) - (MSeq n : ℤ))‖ ^ 2 := by
        intro k
        dsimp [c]
        rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hDpos.le, div_pow]
        ring
      simp_rw [hterm, ← Finset.mul_sum]
      congr 1
      exact sum_sq_shift n (MSeq n) (fun j => ‖fourierCoeff (fCircle P) j‖ ^ 2)
    have hdef_eq : ∑ k : Fin n, (1 - ‖c k‖ ^ 2) = (n : ℝ) - ∑ k : Fin n, ‖c k‖ ^ 2 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [hdef_eq, hsum_c]
    have hlb : (1 / D ^ 2) * (1 - tailBound P (MSeq n)) ≤
        (1 / D ^ 2) * ∑ j ∈ S, ‖fourierCoeff (fCircle P) j‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hparseval (by positivity)
    have hD2_ge : 1 ≤ (n : ℝ) * D ^ 2 := by
      have h1 : (1 : ℝ) ^ 2 ≤ (D * √(n : ℝ)) ^ 2 := pow_le_pow_left₀ zero_le_one hDsqx_ge1 2
      rw [mul_pow, Real.sq_sqrt hxpos.le] at h1
      linarith only [h1]
    have hquot : (n : ℝ) - (1 / D ^ 2) * (1 - tailBound P (MSeq n)) ≤
        (n : ℝ) * (2 * (D * √(n : ℝ) - 1) + tailBound P (MSeq n)) := by
      have hne_D2 : D ^ 2 ≠ 0 := pow_ne_zero 2 hDpos.ne'
      have hident : (n : ℝ) - (1 / D ^ 2) * (1 - tailBound P (MSeq n)) =
          (n : ℝ) * (((n : ℝ) * D ^ 2 - 1 + tailBound P (MSeq n)) / ((n : ℝ) * D ^ 2)) := by
        field_simp [hne_D2, hxpos.ne']
        ring
      rw [hident]
      apply mul_le_mul_of_nonneg_left _ hxpos.le
      have h1 : ((n : ℝ) * D ^ 2 - 1) / ((n : ℝ) * D ^ 2) ≤ 2 * (D * √(n : ℝ) - 1) := by
        have hsq : (n : ℝ) * D ^ 2 = (D * √(n : ℝ)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hxpos.le]; ring
        rw [div_le_iff₀ (by positivity), hsq]
        have hdiff_nn : 0 ≤ D * √(n : ℝ) - 1 := by linarith only [hDsqx_ge1]
        nlinarith only [hDsqx_ge1, hdiff_nn, sq_nonneg (D * √(n : ℝ) - 1)]
      have h2 : tailBound P (MSeq n) / ((n : ℝ) * D ^ 2) ≤ tailBound P (MSeq n) :=
        div_le_self (tailBound_nonneg P (MSeq n)) hD2_ge
      rw [add_div]
      linarith only [h1, h2]
    calc (n : ℝ) - (1 / D ^ 2) * ∑ j ∈ S, ‖fourierCoeff (fCircle P) j‖ ^ 2
        ≤ (n : ℝ) - (1 / D ^ 2) * (1 - tailBound P (MSeq n)) := by linarith only [hlb]
      _ ≤ (n : ℝ) * (2 * (D * √(n : ℝ) - 1) + tailBound P (MSeq n)) := hquot
      _ ≤ (n : ℝ) * (2 * (12000 * (n : ℝ) ^ (-(1 : ℝ) / 20)) +
            5000000 * (n : ℝ) ^ (-(1 : ℝ) / 20)) := by
          apply mul_le_mul_of_nonneg_left _ hxpos.le
          linarith only [hDsqx_sub_le, hT_le]
      _ ≤ 6000000 * (n : ℝ) * (n : ℝ) ^ (-(1 : ℝ) / 20) := by
          have hnn : 0 ≤ (n : ℝ) ^ (-(1 : ℝ) / 20) := Real.rpow_nonneg hxpos.le _
          nlinarith only [hxpos, hnn]

private lemma tendsto_rpow_mul_log_grid :
    Tendsto (fun n : ℕ => ((1 : ℝ) / (n : ℝ) + 6000000 * (n : ℝ) ^ (-(1 : ℝ) / 20)) *
      Real.log (4 * ((8 * (n + 1) ^ 2 + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
  have hlo : Tendsto (fun x : ℝ => Real.log x / x ^ ((1 : ℝ) / 20)) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).tendsto_div_nhds_zero
    exact h
  have hlo_nat : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ ((1 : ℝ) / 20)) atTop (𝓝 0) :=
    hlo.comp tendsto_natCast_atTop_atTop
  have h20 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 20)) atTop (𝓝 0) := by
    simpa [neg_div] using tendsto_nat_rpow_neg (r := 1 / 20) (by norm_num)
  have hupper : Tendsto (fun n : ℕ =>
      6000001 * (Real.log 256 * (n : ℝ) ^ (-(1 : ℝ) / 20) +
        2 * (Real.log (n : ℝ) / (n : ℝ) ^ ((1 : ℝ) / 20)))) atTop (𝓝 0) := by
    have h1 := h20.const_mul (Real.log 256)
    have h2 := hlo_nat.const_mul 2
    simpa using (h1.add h2).const_mul 6000001
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hx : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have harg : (1 : ℝ) ≤ 4 * ((8 * (n + 1) ^ 2 + 1 : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ 8 * (n + 1) ^ 2 + 1 := by omega
      have h1 : (1 : ℝ) ≤ ((8 * (n + 1) ^ 2 + 1 : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    exact mul_nonneg (by positivity) (Real.log_nonneg harg)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hx : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hxpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hcoeff : (1 : ℝ) / (n : ℝ) + 6000000 * (n : ℝ) ^ (-(1 : ℝ) / 20) ≤
        6000001 * (n : ℝ) ^ (-(1 : ℝ) / 20) := by
      have h1 : (1 : ℝ) / (n : ℝ) ≤ (n : ℝ) ^ (-(1 : ℝ) / 20) := by
        rw [one_div, ← Real.rpow_neg_one]
        exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
      linarith
    have hlog_le : Real.log (4 * ((8 * (n + 1) ^ 2 + 1 : ℕ) : ℝ)) ≤
        Real.log 256 + 2 * Real.log (n : ℝ) := by
      have harg_pos : (0 : ℝ) < 4 * ((8 * (n + 1) ^ 2 + 1 : ℕ) : ℝ) := by positivity
      have harg_le : 4 * ((8 * (n + 1) ^ 2 + 1 : ℕ) : ℝ) ≤ 256 * (n : ℝ) ^ 2 := by
        push_cast
        nlinarith
      calc Real.log (4 * ((8 * (n + 1) ^ 2 + 1 : ℕ) : ℝ))
          ≤ Real.log (256 * (n : ℝ) ^ 2) := Real.log_le_log harg_pos harg_le
        _ = Real.log 256 + Real.log ((n : ℝ) ^ 2) :=
            Real.log_mul (by norm_num) (pow_ne_zero 2 hxpos.ne')
        _ = Real.log 256 + 2 * Real.log (n : ℝ) := by rw [Real.log_pow]; ring
    have hlog_nn : 0 ≤ Real.log (4 * ((8 * (n + 1) ^ 2 + 1 : ℕ) : ℝ)) := by
      apply Real.log_nonneg
      have : (1 : ℕ) ≤ 8 * (n + 1) ^ 2 + 1 := by omega
      have h1 : (1 : ℝ) ≤ ((8 * (n + 1) ^ 2 + 1 : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    have hrpow_eq : (n : ℝ) ^ (-(1 : ℝ) / 20) * Real.log (n : ℝ) =
        Real.log (n : ℝ) / (n : ℝ) ^ ((1 : ℝ) / 20) := by
      rw [show (-(1 : ℝ) / 20) = -((1 : ℝ) / 20) by ring, Real.rpow_neg hxpos.le,
        inv_mul_eq_div]
    calc ((1 : ℝ) / (n : ℝ) + 6000000 * (n : ℝ) ^ (-(1 : ℝ) / 20)) *
          Real.log (4 * ((8 * (n + 1) ^ 2 + 1 : ℕ) : ℝ))
        ≤ (6000001 * (n : ℝ) ^ (-(1 : ℝ) / 20)) * (Real.log 256 + 2 * Real.log (n : ℝ)) :=
          mul_le_mul hcoeff hlog_le hlog_nn (by positivity)
      _ = 6000001 * (Real.log 256 * (n : ℝ) ^ (-(1 : ℝ) / 20) +
            2 * ((n : ℝ) ^ (-(1 : ℝ) / 20) * Real.log (n : ℝ))) := by ring
      _ = 6000001 * (Real.log 256 * (n : ℝ) ^ (-(1 : ℝ) / 20) +
            2 * (Real.log (n : ℝ) / (n : ℝ) ^ ((1 : ℝ) / 20))) := by rw [hrpow_eq]

end Erdos230UltraflatH1

theorem OMA.solution : OMA.R_Erdos230_erdos_230_variants_ultraflat_R1.H1 := by
  classical
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp Erdos230UltraflatH1.eventually_params_good
  let c : (n : ℕ) → Fin n → ℂ := fun n =>
    if h : N0 ≤ n then (Erdos230UltraflatH1.construct_at_large_n n (hN0 n h)).choose
    else fun _ => 0
  let e : ℕ → ℝ := fun n =>
    if N0 ≤ n then 5020000 * (n : ℝ) ^ (-(1 : ℝ) / 20) else 1
  refine ⟨c, e, ?_, ?_, ?_, ?_⟩
  · intro n k
    dsimp [c]
    split_ifs with h
    · exact (Erdos230UltraflatH1.construct_at_large_n n (hN0 n h)).choose_spec.1 k
    · simp
  · have h20 : Filter.Tendsto (fun n : ℕ => 5020000 * (n : ℝ) ^ (-(1 : ℝ) / 20))
        Filter.atTop (nhds 0) := by
      have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 20)).comp
        tendsto_natCast_atTop_atTop
      simpa [neg_div] using h.const_mul 5020000
    refine h20.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop N0] with n hn
    dsimp [e]; rw [if_pos hn]
  · intro n j
    dsimp only [c, e]
    split_ifs with h
    · exact (Erdos230UltraflatH1.construct_at_large_n n (hN0 n h)).choose_spec.2.1
        ((j.val : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 - 4)
    · simp
  · refine squeeze_zero' ?_ ?_ Erdos230UltraflatH1.tendsto_rpow_mul_log_grid
    · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have hdisk : ∀ k : Fin n, ‖c n k‖ ≤ 1 := by
        intro k; dsimp [c]; split_ifs with h
        · exact (Erdos230UltraflatH1.construct_at_large_n n (hN0 n h)).choose_spec.1 k
        · simp
      have hsum_nn : 0 ≤ ∑ k : Fin n, (1 - ‖c n k‖ ^ 2) :=
        Finset.sum_nonneg fun k _ => by have := hdisk k; nlinarith [norm_nonneg (c n k)]
      have hlog_nn : 0 ≤ Real.log (4 * ((8 * (n + 1) ^ 2 + 1 : ℕ) : ℝ)) := by
        apply Real.log_nonneg
        have : (1 : ℕ) ≤ 8 * (n + 1) ^ 2 + 1 := by omega
        have h1 : (1 : ℝ) ≤ ((8 * (n + 1) ^ 2 + 1 : ℕ) : ℝ) := by exact_mod_cast this
        linarith
      exact div_nonneg (mul_nonneg (by linarith) hlog_nn) (Nat.cast_nonneg n)
    · filter_upwards [Filter.eventually_ge_atTop (max N0 1)] with n hn
      have hN : N0 ≤ n := le_trans (le_max_left _ _) hn
      have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
      have hxpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      have hdef : ∑ k : Fin n, (1 - ‖c n k‖ ^ 2) ≤
          6000000 * (n : ℝ) * (n : ℝ) ^ (-(1 : ℝ) / 20) := by
        dsimp only [c]; rw [dif_pos hN]
        exact (Erdos230UltraflatH1.construct_at_large_n n (hN0 n hN)).choose_spec.2.2
      have hlog_nn : 0 ≤ Real.log (4 * ((8 * (n + 1) ^ 2 + 1 : ℕ) : ℝ)) := by
        apply Real.log_nonneg
        have : (1 : ℕ) ≤ 8 * (n + 1) ^ 2 + 1 := by omega
        have h1 : (1 : ℝ) ≤ ((8 * (n + 1) ^ 2 + 1 : ℕ) : ℝ) := by exact_mod_cast this
        linarith
      have hdiv : (1 + ∑ k : Fin n, (1 - ‖c n k‖ ^ 2)) / (n : ℝ) ≤
          (1 : ℝ) / (n : ℝ) + 6000000 * (n : ℝ) ^ (-(1 : ℝ) / 20) := by
        rw [add_div]
        have h2 : (∑ k : Fin n, (1 - ‖c n k‖ ^ 2)) / (n : ℝ) ≤
            6000000 * (n : ℝ) ^ (-(1 : ℝ) / 20) := by
          rw [div_le_iff₀ hxpos]
          linarith
        linarith
      calc (1 + ∑ k : Fin n, (1 - ‖c n k‖ ^ 2)) *
            Real.log (4 * ((8 * (n + 1) ^ 2 + 1 : ℕ) : ℝ)) / (n : ℝ)
          = ((1 + ∑ k : Fin n, (1 - ‖c n k‖ ^ 2)) / (n : ℝ)) *
              Real.log (4 * ((8 * (n + 1) ^ 2 + 1 : ℕ) : ℝ)) := by ring
        _ ≤ ((1 : ℝ) / (n : ℝ) + 6000000 * (n : ℝ) ^ (-(1 : ℝ) / 20)) *
              Real.log (4 * ((8 * (n + 1) ^ 2 + 1 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_right hdiv hlog_nn
