import FormalConjectures.ErdosProblems.«1189»
import Mathlib

/-!
# Erdős Problem 1189 — BBMST Upper Bound

Upstream: `FormalConjectures/ErdosProblems/1189.lean:192` (`Erdos1189.erdos_1189.variants.bbmst`).
Credit: `@gdyan2022`.

Prime Number Theorem section (`chebyshev_asymptotic`) adapted from `PrimeNumberTheoremAnd`
(Apache-2.0) and `@ldy985`'s Wiener-Ikehara extraction for Mathlib v4.33.1.
Remaining proof: self-contained elementary proof of the BBMST upper bound via Simpson's
product bound, single-path codimension-1 extraction, iterated round decomposition,
explicit finite coding, discrete prime-sum lemma, and Lagrange multiplier divisor bounds.
-/

section PNTX_Base

namespace Function

variable {α : Type*} [Zero α]

theorem support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

theorem support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end Function


open Filter Topology

namespace Asymptotics

variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {R : Type*}
  {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variable [Norm E] [Norm F] [Norm G]

variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedRing R']


theorem _root_.Filter.Eventually.natCast {f : ℝ → Prop} (hf : ∀ᶠ x in atTop, f x) :
    ∀ᶠ n : ℕ in atTop, f n :=
  tendsto_natCast_atTop_atTop.eventually hf

theorem IsBigO.natCast {f g : ℝ → E} (h : f =O[atTop] g) :
    (fun n : ℕ => f n) =O[atTop] fun n : ℕ => g n :=
  h.comp_tendsto tendsto_natCast_atTop_atTop

end Asymptotics


open Filter Real

/-- log^b x / x^a goes to zero at infinity if a is positive. -/
theorem Real.tendsto_pow_log_div_pow_atTop (a : ℝ) (b : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun x ↦ log x ^ b / x^a) Filter.atTop (nhds 0) := by
  apply Asymptotics.isLittleO_iff_tendsto' _|>.mp <| isLittleO_log_rpow_rpow_atTop _ ha
  filter_upwards [eventually_gt_atTop 0] with x hx
  intro h
  rw [rpow_eq_zero hx.le ha.ne.symm] at h
  exfalso
  linarith

end PNTX_Base

-- Ported from PrimeNumberTheoremAnd: Sobolev.lean
section PNTX_Sobolev

open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun

theorem CS.ext {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : CS n E}
    (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; cases h; rfl

structure trunc extends (CS 2 ℝ) where
  h3 : (Set.Icc (-1) (1)).indicator 1 ≤ toFun
  h4 : toFun ≤ Set.indicator (Set.Ioo (-2) (2)) 1

structure W1 (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  smooth : ContDiff ℝ n toFun
  integrable : ∀ ⦃k⦄, k ≤ n → Integrable (iteratedDeriv k toFun)

abbrev W21 := W1 2 ℂ

section lemmas

noncomputable def funscale {E : Type*} (g : ℝ → E) (R x : ℝ) : E := g (R⁻¹ • x)

lemma contDiff_ofReal : ContDiff ℝ ∞ ofReal := by
  have key x : HasDerivAt ofReal 1 x := hasDerivAt_id x |>.ofReal_comp
  have key' : deriv ofReal = fun _ => 1 := by ext x ; exact (key x).deriv
  refine contDiff_infty_iff_deriv.mpr ⟨fun x => (key x).differentiableAt, ?_⟩
  simpa [key'] using contDiff_const

omit [NormedSpace ℝ E] in
lemma tendsto_funscale {f : ℝ → E} (hf : ContinuousAt f 0) (x : ℝ) :
    Tendsto (fun R => funscale f R x) atTop (𝓝 (f 0)) :=
  hf.tendsto.comp (by simpa using tendsto_inv_atTop_zero.mul_const x)

end lemmas

namespace CS

variable {f : CS n E} {R x v : ℝ}

instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun

instance : Coe (CS n ℝ) (CS n ℂ) where coe f := ⟨fun x => f x,
  contDiff_ofReal.of_le (mod_cast le_top) |>.comp f.h1, f.h2.comp_left (g := ofReal) rfl⟩

def neg (f : CS n E) : CS n E where
  toFun := -f
  h1 := f.h1.neg
  h2 := by simpa [HasCompactSupport, tsupport] using f.h2

instance : Neg (CS n E) where neg := neg

@[simp] lemma neg_apply {x : ℝ} : (-f) x = - (f x) := rfl

def smul (R : ℝ) (f : CS n E) : CS n E := ⟨R • f, f.h1.const_smul R, f.h2.smul_left⟩

instance : HSMul ℝ (CS n E) (CS n E) where hSMul := smul

@[simp] lemma smul_apply : (R • f) x = R • f x := rfl

lemma continuous (f : CS n E) : Continuous f := f.h1.continuous

noncomputable def deriv (f : CS (n + 1) E) : CS n E where
  toFun := _root_.deriv f
  h1 := (contDiff_succ_iff_deriv.mp f.h1).2.2
  h2 := f.h2.deriv

lemma hasDerivAt (f : CS (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  (f.h1.differentiable (by simp)).differentiableAt.hasDerivAt

lemma deriv_smul {f : CS (n + 1) E} : (R • f).deriv = R • f.deriv := by
  refine CS.ext (funext fun x => ?_) ; exact (f.hasDerivAt x |>.const_smul R).deriv

noncomputable def scale (g : CS n E) (R : ℝ) : CS n E := by
  by_cases h : R = 0
  · exact ⟨0, contDiff_const, by simp [HasCompactSupport, tsupport]⟩
  · refine ⟨fun x => funscale g R x, ?_, ?_⟩
    · exact g.h1.comp (contDiff_const_smul R⁻¹)
    · exact g.h2.comp_smul (inv_ne_zero h)

lemma deriv_scale {f : CS (n + 1) E} : (f.scale R).deriv = R⁻¹ • f.deriv.scale R := by
  refine CS.ext (funext fun v => ?_) ; by_cases hR : R = 0
  · simp [hR, scale, deriv]
  · simp only [scale, hR, ↓reduceDIte, smul_apply]
    exact ((f.hasDerivAt (R⁻¹ • v)).scomp v
      (by simpa using! (hasDerivAt_id v).const_smul R⁻¹)).deriv

lemma deriv_scale' {f : CS (n + 1) E} :
    (f.scale R).deriv v = R⁻¹ • f.deriv (R⁻¹ • v) := by
  rw [deriv_scale, smul_apply]
  by_cases hR : R = 0 <;> simp [hR, scale, funscale]

lemma hasDerivAt_scale (f : CS (n + 1) E) (R x : ℝ) :
    HasDerivAt (f.scale R) (R⁻¹ • _root_.deriv f (R⁻¹ • x)) x := by
  convert hasDerivAt (f.scale R) x ; rw [deriv_scale'] ; rfl

lemma tendsto_scale (f : CS n E) (x : ℝ) : Tendsto (fun R => f.scale R x) atTop (𝓝 (f 0)) := by
  apply (tendsto_funscale f.continuous.continuousAt x).congr'
  filter_upwards [eventually_ne_atTop 0] with R hR ; simp [scale, hR]

lemma bounded : ∃ C, ∀ v, ‖f v‖ ≤ C := by
  obtain ⟨x, hx⟩ :=
    (continuous_norm.comp f.continuous).exists_forall_ge_of_hasCompactSupport f.h2.norm
  exact ⟨_, hx⟩

end CS

namespace trunc

instance : CoeFun trunc (fun _ => ℝ → ℝ) where coe f := f.toFun

instance : Coe trunc (CS 2 ℝ) where coe := trunc.toCS

lemma nonneg (g : trunc) (x : ℝ) : 0 ≤ g x := (Set.indicator_nonneg (by simp) x).trans (g.h3 x)

lemma le_one (g : trunc) (x : ℝ) : g x ≤ 1 :=
  (g.h4 x).trans <| Set.indicator_le_self' (by simp) x

lemma zero (g : trunc) : g =ᶠ[𝓝 0] 1 := by
  have : Set.Icc (-1) 1 ∈ 𝓝 (0 : ℝ) := by apply Icc_mem_nhds <;> linarith
  exact eventually_of_mem this (fun x hx => le_antisymm (g.le_one x) (by simpa [hx] using g.h3 x))

@[simp] lemma zero_at {g : trunc} : g 0 = 1 := g.zero.eq_of_nhds

end trunc

namespace W1

instance : CoeFun (W1 n E) (fun _ => ℝ → E) where coe := W1.toFun

lemma continuous (f : W1 n E) : Continuous f := f.smooth.continuous

lemma differentiable (f : W1 (n + 1) E) : Differentiable ℝ f :=
  f.smooth.differentiable (by simp)

lemma iteratedDeriv_sub {f g : ℝ → E} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    iteratedDeriv n (f - g) = iteratedDeriv n f - iteratedDeriv n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    have hf' : ContDiff ℝ n (deriv f) := hf.iterate_deriv' n 1
    have hg' : ContDiff ℝ n (deriv g) := hg.iterate_deriv' n 1
    have hfg : deriv (f - g) = deriv f - deriv g := by
      ext x ; apply deriv_sub
      · exact (hf.differentiable (by simp)).differentiableAt
      · exact (hg.differentiable (by simp)).differentiableAt
    simp_rw [iteratedDeriv_succ', ← ih hf' hg', hfg]

noncomputable def deriv (f : W1 (n + 1) E) : W1 n E where
  toFun := _root_.deriv f
  smooth := contDiff_succ_iff_deriv.mp f.smooth |>.2.2
  integrable k hk := by
    simpa [iteratedDeriv_succ'] using f.integrable (Nat.succ_le_succ hk)

lemma hasDerivAt (f : W1 (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  f.differentiable.differentiableAt.hasDerivAt

def sub (f g : W1 n E) : W1 n E where
  toFun := f - g
  smooth := f.smooth.sub g.smooth
  integrable k hk := by
    have hf : ContDiff ℝ k f := f.smooth.of_le (by simp [hk])
    have hg : ContDiff ℝ k g := g.smooth.of_le (by simp [hk])
    simpa [iteratedDeriv_sub hf hg] using (f.integrable hk).sub (g.integrable hk)

instance : Sub (W1 n E) where sub := sub

lemma integrable_iteratedDeriv_Schwarz {f : 𝓢(ℝ, ℂ)} : Integrable (iteratedDeriv n f) := by
  induction n generalizing f with
  | zero => exact f.integrable
  | succ n ih => simpa [iteratedDeriv_succ'] using! ih (f := SchwartzMap.derivCLM ℝ ℂ f)

noncomputable def of_Schwartz (f : 𝓢(ℝ, ℂ)) : W1 n ℂ where
  toFun := f
  smooth := f.smooth n
  integrable _ _ := integrable_iteratedDeriv_Schwarz

end W1

namespace W21

variable {f : W21}

noncomputable def norm (f : ℝ → ℂ) : ℝ :=
    (∫ v, ‖f v‖) + (4 * π ^ 2)⁻¹ * (∫ v, ‖deriv (deriv f) v‖)

lemma norm_nonneg {f : ℝ → ℂ} : 0 ≤ norm f :=
  add_nonneg (integral_nonneg (fun t => by simp))
    (mul_nonneg (by positivity) (integral_nonneg (fun t => by simp)))

noncomputable instance : Norm W21 where norm := norm ∘ W1.toFun

noncomputable instance : Coe 𝓢(ℝ, ℂ) W21 where coe := W1.of_Schwartz

def ofCS2 (f : CS 2 ℂ) : W21 := by
  refine ⟨f, f.h1, fun k hk => ?_⟩ ; match k with
  | 0 => exact f.h1.continuous.integrable_of_hasCompactSupport f.h2
  | 1 => simpa using (f.h1.continuous_deriv one_le_two).integrable_of_hasCompactSupport f.h2.deriv
  | 2 => simpa [iteratedDeriv_succ] using
    (f.h1.iterate_deriv' 0 2).continuous.integrable_of_hasCompactSupport f.h2.deriv.deriv

instance : Coe (CS 2 ℂ) W21 where coe := ofCS2

instance : HMul (CS 2 ℂ) W21 (CS 2 ℂ) where
  hMul g f := ⟨g * f, g.h1.mul f.smooth, g.h2.mul_right⟩

instance : HMul (CS 2 ℝ) W21 (CS 2 ℂ) where hMul g f := (g : CS 2 ℂ) * f

lemma hf (f : W21) : Integrable f := f.integrable zero_le_two

lemma hf' (f : W21) : Integrable (deriv f) := by
  simpa [iteratedDeriv_succ] using f.integrable one_le_two

lemma hf'' (f : W21) : Integrable (deriv (deriv f))  := by
  simpa [iteratedDeriv_succ] using f.integrable le_rfl

end W21

theorem W21_approximation (f : W21) (g : trunc) :
    Tendsto (fun R => ‖f - (g.scale R * f : W21)‖) atTop (𝓝 0) := by

  -- Definitions
  let f' := f.deriv
  let f'' := f'.deriv
  let g' := (g : CS 2 ℝ).deriv
  let g'' := g'.deriv
  let h R v := 1 - g.scale R v
  let h' R := - (g.scale R).deriv
  let h'' R := - (g.scale R).deriv.deriv

  -- Properties of h
  have ch {R} : Continuous (fun v => (h R v : ℂ)) :=
    continuous_ofReal.comp <| continuous_const.sub (CS.continuous _)
  have ch' {R} : Continuous (fun v => (h' R v : ℂ)) := continuous_ofReal.comp (CS.continuous _)
  have ch'' {R} : Continuous (fun v => (h'' R v : ℂ)) := continuous_ofReal.comp (CS.continuous _)
  have dh R v : HasDerivAt (h R) (h' R v) v := by
    convert! CS.hasDerivAt_scale (g : CS 2 ℝ) R v |>.const_sub 1 using 1
    simp [h', CS.deriv_scale', show g.deriv.toFun = deriv g.toFun from rfl]
  have dh' R v : HasDerivAt (h' R) (h'' R v) v := ((g.scale R).deriv.hasDerivAt v).neg
  have hh1 R v : |h R v| ≤ 1 := by
    by_cases hR : R = 0 <;>
      simp only [CS.scale, funscale, smul_eq_mul, hR, ↓reduceDIte, Pi.zero_apply, sub_zero,
        abs_one, le_refl, h]
    rw [abs_le] ; constructor <;>
    linarith [g.le_one (R⁻¹ * v), g.nonneg (R⁻¹ * v)]
  have vR v : Tendsto (fun R : ℝ => v * R⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul v

  -- Proof
  convert_to Tendsto (fun R => W21.norm (fun v => h R v * f v)) atTop (𝓝 0)
  · ext R ; change W21.norm _ = _ ; congr ; ext v ; simp [h, sub_mul] ; rfl
  rw [show (0 : ℝ) = 0 + ((4 * π ^ 2)⁻¹ : ℝ) * 0 by simp]
  refine Tendsto.add ?_ (Tendsto.const_mul _ ?_)

  · let F R v := ‖h R v * f v‖
    have eh v : ∀ᶠ R in atTop, h R v = 0 := by
      filter_upwards [(vR v).eventually g.zero, eventually_ne_atTop 0] with R hR hR'
      simp [h, hR, CS.scale, hR', funscale, mul_comm R⁻¹]
    have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume := by
      apply Eventually.of_forall ; intro R
      exact (ch.mul f.continuous).norm.aestronglyMeasurable
    have e2 : ∀ᶠ (n : ℝ) in atTop, ∀ᵐ (a : ℝ), ‖F n a‖ ≤ ‖f a‖ := by
      apply Eventually.of_forall ; intro R
      apply Eventually.of_forall ; intro v
      simpa [F] using mul_le_mul (hh1 R v) le_rfl (by simp) zero_le_one
    have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
      apply Eventually.of_forall ; intro v
      apply tendsto_nhds_of_eventually_eq ; filter_upwards [eh v] with R hR ; simp [F, hR]
    simpa [F] using tendsto_integral_filter_of_dominated_convergence _ e1 e2 f.hf.norm e4

  · let F R v := ‖h'' R v * f v + 2 * h' R v * f' v + h R v * f'' v‖
    convert_to Tendsto (fun R ↦ ∫ (v : ℝ), F R v) atTop (𝓝 0)
    · have this R v :
        deriv (deriv (fun v => h R v * f v)) v =
          h'' R v * f v + 2 * h' R v * f' v + h R v * f'' v := by
        have df v : HasDerivAt f (f' v) v := f.hasDerivAt v
        have df' v : HasDerivAt f' (f'' v) v := f'.hasDerivAt v
        have l3 v : HasDerivAt (fun v => h R v * f v) (h' R v * f v + h R v * f' v) v :=
          (dh R v).ofReal_comp.mul (df v)
        have l5 : HasDerivAt (fun v => h' R v * f v) (h'' R v * f v + h' R v * f' v) v :=
          (dh' R v).ofReal_comp.mul (df v)
        have l7 : HasDerivAt (fun v => h R v * f' v) (h' R v * f' v + h R v * f'' v) v :=
          (dh R v).ofReal_comp.mul (df' v)
        have d1 : deriv (fun v => h R v * f v) = fun v => h' R v * f v + h R v * f' v :=
          funext (fun v => (l3 v).deriv)
        rw [d1] ; convert! (l5.add l7).deriv using 1 ; ring
      simp_rw [this, F]

    obtain ⟨c1, mg'⟩ := g'.bounded
    obtain ⟨c2, mg''⟩ := g''.bounded
    let bound v := c2 * ‖f v‖ + 2 * c1 * ‖f' v‖ + ‖f'' v‖
    have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume := by
      apply Eventually.of_forall ; intro R ; apply (Continuous.norm ?_).aestronglyMeasurable
      exact ((ch''.mul f.continuous).add ((continuous_const.mul ch').mul f.deriv.continuous)).add
        (ch.mul f.deriv.deriv.continuous)
    have e2 : ∀ᶠ R in atTop, ∀ᵐ (a : ℝ), ‖F R a‖ ≤ bound a := by
      have hc1 : ∀ᶠ R in atTop, ∀ v, |h' R v| ≤ c1 := by
        filter_upwards [eventually_ge_atTop 1] with R hR v
        have hR' : R ≠ 0 := by linarith
        have : 0 ≤ R := by linarith
        simp only [CS.deriv_scale, CS.neg_apply, CS.smul_apply, smul_eq_mul, abs_neg, abs_mul,
          abs_inv, abs_eq_self.mpr this, ge_iff_le, h']
        simp only [CS.scale, hR', ↓reduceDIte, funscale, smul_eq_mul]
        convert_to _ ≤ c1 * 1
        · simp
        · rw [mul_comm]
          apply mul_le_mul (mg' _)
            (inv_le_of_inv_le₀ (by linarith) (by simpa using hR)) (by positivity)
          exact (abs_nonneg _).trans (mg' 0)
      have hc2 : ∀ᶠ R in atTop, ∀ v, |h'' R v| ≤ c2 := by
        filter_upwards [eventually_ge_atTop 1] with R hR v
        have e1 : 0 ≤ R := by linarith
        have e2 : R⁻¹ ≤ 1 := inv_le_of_inv_le₀ (by linarith) (by simpa using hR)
        have e3 : R ≠ 0 := by linarith
        simp only [CS.deriv_scale, CS.deriv_smul, CS.neg_apply, CS.smul_apply, smul_eq_mul, abs_neg,
          abs_mul, abs_inv, abs_eq_self.mpr e1, ge_iff_le, h'']
        convert_to _ ≤ 1 * (1 * c2)
        · simp
        apply mul_le_mul e2 ?_ (by positivity) zero_le_one
        apply mul_le_mul e2 ?_ (by positivity) zero_le_one
        simp only [CS.scale, e3, ↓reduceDIte, funscale, smul_eq_mul] ; apply mg''
      filter_upwards [hc1, hc2] with R hc1 hc2
      apply Eventually.of_forall ; intro v ; specialize hc1 v ; specialize hc2 v
      simp only [F, bound, norm_norm]
      refine (norm_add_le _ _).trans ?_ ; apply add_le_add
      · refine (norm_add_le _ _).trans ?_ ; apply add_le_add <;> simp only [Complex.norm_mul,
        Complex.norm_ofNat, norm_real, norm_eq_abs] <;> gcongr
      · simpa using mul_le_mul (hh1 R v) le_rfl (by simp) zero_le_one
    have e3 : Integrable bound volume :=
      (((f.hf.norm).const_mul _).add ((f.hf'.norm).const_mul _)).add f.hf''.norm
    have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
      apply Eventually.of_forall ; intro v
      have evg' : g' =ᶠ[𝓝 0] 0 := by convert! ← g.zero.deriv ; exact deriv_const' _
      have evg'' : g'' =ᶠ[𝓝 0] 0 := by convert! ← evg'.deriv ; exact deriv_const' _
      refine tendsto_norm_zero.comp <| (ZeroAtFilter.add ?_ ?_).add ?_
      · have eh'' v : ∀ᶠ R in atTop, h'' R v = 0 := by
          filter_upwards [(vR v).eventually evg'', eventually_ne_atTop 0] with R hR hR'
          simp only [CS.deriv_scale, CS.deriv_smul, CS.neg_apply, CS.smul_apply, smul_eq_mul,
            neg_eq_zero, mul_eq_zero, inv_eq_zero, hR', false_or, h'']
          simp only [CS.scale, hR', ↓reduceDIte, funscale, smul_eq_mul, mul_comm R⁻¹]
          exact hR
        apply tendsto_nhds_of_eventually_eq
        filter_upwards [eh'' v] with R hR ; simp [hR]
      · have eh' v : ∀ᶠ R in atTop, h' R v = 0 := by
          filter_upwards [(vR v).eventually evg'] with R hR
          simp [g'] at hR
          simp [h', CS.deriv_scale', mul_comm R⁻¹, hR]
        apply tendsto_nhds_of_eventually_eq
        filter_upwards [eh' v] with R hR ; simp [hR]
      · simpa [h] using! ((g.tendsto_scale v).const_sub 1).ofReal.mul tendsto_const_nhds
    simpa [F] using tendsto_integral_filter_of_dominated_convergence bound e1 e2 e3 e4

end PNTX_Sobolev

-- Ported from PrimeNumberTheoremAnd: Fourier.lean
section PNTX_Fourier

open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

section lemmas

@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 :=
  NNReal.coe_eq_one.mp (by simp [Circle.norm_coe])

@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]

noncomputable def e (u : ℝ) : ℝ →ᵇ ℂ where
  toFun v := 𝐞 (-v * u)
  map_bounded' :=
    ⟨2, fun x y => (dist_le_norm_add_norm _ _).trans (by simp [Circle.norm_coe, one_add_one_eq_two])⟩

@[simp] lemma e_apply (u : ℝ) (v : ℝ) : e u v = 𝐞 (-v * u) := rfl

@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourier_eq, integral_neg]

@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  have : Continuous fun p : ℝ × ℝ ↦ ((innerₗ ℝ) p.1) p.2 := continuous_inner
  have := fourierIntegral_add continuous_fourierChar this hf hg
  exact congr_fun this x

@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x

@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u

end lemmas

theorem fourierIntegral_self_add_deriv_deriv (f : W21) (u : ℝ) :
    (1 + u ^ 2) * 𝓕 (f : ℝ → ℂ) u =
      𝓕 (fun u : ℝ => (f u - (1 / (4 * π ^ 2)) * deriv^[2] f u : ℂ)) u := by
  have l1 : Integrable (fun x => (((π : ℂ) ^ 2)⁻¹ * 4⁻¹) * deriv (deriv f) x) := by
    apply Integrable.const_mul ; simpa [iteratedDeriv_succ] using f.integrable le_rfl
  have l4 : Differentiable ℝ f := f.differentiable
  have l5 : Differentiable ℝ (deriv f) := f.deriv.differentiable
  simp [f.hf, l1, add_mul, Real.fourier_deriv f.hf' l5 f.hf'', Real.fourier_deriv f.hf l4 f.hf']
  field_simp [pi_ne_zero] ; ring_nf ; simp

@[simp] lemma deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv

end PNTX_Fourier

-- Ported from PrimeNumberTheoremAnd: SmoothExistence.lean
section PNTX_Smooth

open MeasureTheory Set Real
open scoped ContDiff

lemma smooth_urysohn_support_Ioo {a b c d : ℝ} (h1 : a < b) (h3 : c < d) :
    ∃ Ψ : ℝ → ℝ, (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
    Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 ∧
    (Function.support Ψ = Set.Ioo a d) := by
  have := exists_contMDiff_zero_iff_one_iff_of_isClosed (n := ⊤)
    (modelWithCornersSelf ℝ ℝ) (s := Set.Iic a ∪ Set.Ici d) (t := Set.Icc b c)
    (IsClosed.union isClosed_Iic isClosed_Ici) isClosed_Icc
    (by
      simp_rw [Set.disjoint_union_left, Set.disjoint_iff, Set.subset_def,
        Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_empty_iff_false,
        and_imp, imp_false, not_le, Set.mem_Ici]
      constructor <;> intros <;> linarith)
  obtain ⟨Ψ, hΨSmooth, hΨrange, hΨ0, hΨ1⟩ := this
  simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_Icc] at *
  use Ψ
  simp only [range_subset_iff, mem_Icc] at hΨrange
  refine ⟨ContMDiff.contDiff hΨSmooth, ?_, ?_, ?_, ?_⟩
  · apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc a d) isCompact_Icc
    simp only [Function.support_subset_iff, ne_eq, mem_Icc, ← hΨ0, not_or]
    bound
  · apply Set.indicator_le'
    · intro x hx
      rw [hΨ1 x |>.mp, Pi.one_apply]
      simpa using hx
    · exact fun x _ ↦ (hΨrange x).1
  · intro x
    apply Set.le_indicator_apply
    · exact fun _ ↦ (hΨrange x).2
    · intro hx
      rw [← hΨ0 x |>.mp]
      simpa [-not_and, mem_Ioo, not_and_or, not_lt] using hx
  · ext x
    simp only [Function.mem_support, ne_eq, mem_Ioo, ← hΨ0, not_or, not_le]



lemma SmoothExistence :
    ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
    ν.support ⊆ Icc (1 / 2) 2 ∧ ∫ x in Ici 0, ν x / x = 1 := by
  suffices h : ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
      ν.support ⊆ Set.Icc (1 / 2) 2 ∧ 0 < ∫ x in Set.Ici 0, ν x / x by
    obtain ⟨ν, hν, hνnonneg, hνsupp, hνpos⟩ := h
    let c := (∫ x in Ici 0, ν x / x)
    use fun y ↦ ν y / c
    refine ⟨hν.div_const c, fun y ↦ div_nonneg (hνnonneg y) (le_of_lt hνpos), ?_, ?_⟩
    · rw [Function.support_div, Function.support_const (ne_of_lt hνpos).symm, inter_univ]
      convert hνsupp
    · simp only [div_right_comm _ c _, integral_div c, div_self <| ne_of_gt hνpos, c]
  have := smooth_urysohn_support_Ioo (a := 1 / 2) (b := 1) (c := 3 / 2) (d := 2)
    (by linarith) (by linarith)
  obtain ⟨ν, hνContDiff, _, hν0, hν1, hνSupport⟩ := this
  use ν, hνContDiff
  unfold indicator at hν0 hν1
  simp only [mem_Icc, Pi.one_apply, Pi.le_def, mem_Ioo] at hν0 hν1
  simp only [hνSupport, subset_def, mem_Ioo, mem_Icc, and_imp]
  split_ands
  · exact fun x ↦ le_trans (by simp [apply_ite]) (hν0 x)
  · exact fun y hy hy' ↦ ⟨by linarith, by linarith⟩
  · rw [integral_pos_iff_support_of_nonneg]
    · simp only [Function.support_div, measurableSet_Ici, Measure.restrict_apply',
        hνSupport, Function.support_id']
      have : (Ioo (1 / 2 : ℝ) 2 ∩ {0}ᶜ ∩ Ici 0) = Ioo (1 / 2) 2 := by
        ext x
        simp only [one_div, mem_inter_iff, mem_Ioo, mem_compl_iff, mem_singleton_iff, mem_Ici]
        bound
      simp only [this, volume_Ioo, ENNReal.ofReal_pos, sub_pos, gt_iff_lt]
      linarith
    · simp_rw [Pi.le_def, Pi.zero_apply]
      intro y
      by_cases h : y ∈ Function.support ν
      · apply div_nonneg <| le_trans (by simp [apply_ite]) (hν0 y)
        rw [hνSupport, mem_Ioo] at h
        linarith [h.left]
      · simp only [Function.mem_support, ne_eq, not_not] at h
        simp [h]
    · have : (fun x ↦ ν x / x).support ⊆ Icc (1 / 2) 2 := by
        rw [Function.support_div, hνSupport]
        exact (inter_subset_left).trans Ioo_subset_Icc_self
      apply (integrableOn_iff_integrable_of_support_subset this).mp
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply hνContDiff.continuous.continuousOn.div continuousOn_id ?_
      simp only [mem_Icc, ne_eq, and_imp, id_eq]
      intros; linarith

end PNTX_Smooth

-- Ported from PrimeNumberTheoremAnd: Wiener.lean (up to and including theorem WeakPNT)
section PNTX_Wiener

-- note: the opening of ArithmeticFunction introduces a notation σ that seems
-- impossible to hide, and hence parameters that are traditionally called σ will
-- have to be called σ' instead in this file.

open Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate

variable {n : ℕ} {A a b c d u x y t σ' : ℝ} {ψ Ψ : ℝ → ℂ} {F G : ℂ → ℂ} {f : ℕ → ℂ} {𝕜 : Type}
  [RCLike 𝕜]



noncomputable
def nterm (f : ℕ → ℂ) (σ' : ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else ‖f n‖ / n ^ σ'

lemma nterm_eq_norm_term {f : ℕ → ℂ} : nterm f σ' n = ‖term f σ' n‖ := by
  by_cases h : n = 0 <;> simp [nterm, term, h]

theorem norm_term_eq_nterm_re (s : ℂ) :
    ‖term f s n‖ = nterm f (s.re) n := by
  simp only [nterm, term, apply_ite (‖·‖), norm_zero, norm_div]
  apply ite_congr rfl (fun _ ↦ rfl)
  intro h
  congr
  refine norm_natCast_cpow_of_pos (by omega) s

lemma hf_coe1 (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hσ : 1 < σ') :
    ∑' i, (‖term f σ' i‖₊ : ENNReal) ≠ ⊤ := by
  simp_rw [ENNReal.tsum_coe_ne_top_iff_summable_coe, ← norm_toNNReal]
  norm_cast
  apply Summable.toNNReal
  convert hf σ' hσ with i
  simp [nterm_eq_norm_term]

instance instMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype _
instance instBorelSpace : BorelSpace Circle :=
  inferInstanceAs <| BorelSpace <| Subtype (· ∈ Metric.sphere (0 : ℂ) 1)


lemma first_fourier_aux1 (hψ : AEMeasurable ψ) {x : ℝ} (n : ℕ) : AEMeasurable fun (u : ℝ) ↦
    (‖fourierChar (-(u * ((1 : ℝ) / ((2 : ℝ) * π) * (n / x).log))) • ψ u‖ₑ : ENNReal) := by
  fun_prop

lemma first_fourier_aux2a :
    (2 : ℂ) * π * -(y * (1 / (2 * π) * Real.log ((n) / x))) = -(y * ((n) / x).log) := by
  calc
    _ = -(y * (((2 : ℂ) * π) / (2 * π) * Real.log ((n) / x))) := by ring
    _ = _ := by rw [div_self (by norm_num), one_mul]

lemma first_fourier_aux2 (hx : 0 < x) (n : ℕ) :
    term f σ' n * 𝐞 (-(y * (1 / (2 * π) * Real.log (n / x)))) • ψ y =
    term f (σ' + y * I) n • (ψ y * x ^ (y * I)) := by
  by_cases hn : n = 0
  · simp [term, hn]
  simp only [term, hn, ↓reduceIte]
  calc
    _ = (f n * (cexp ((2 * π * -(y * (1 / (2 * π) * Real.log (n / x)))) * I) /
        ↑((n : ℝ) ^ σ'))) • ψ y := by
      rw [Circle.smul_def, fourierChar_apply, ofReal_cpow (by norm_num)]
      simp only [one_div, mul_inv_rev, mul_neg, ofReal_neg, ofReal_mul, ofReal_ofNat, ofReal_inv,
        neg_mul, smul_eq_mul, ofReal_natCast]
      ring
    _ = (f n * (x ^ (y * I) / n ^ (σ' + y * I))) • ψ y := by
      congr 2
      have l1 : 0 < (n : ℝ) := by simpa using Nat.pos_iff_ne_zero.mpr hn
      have l2 : (x : ℂ) ≠ 0 := by simp [hx.ne.symm]
      have l3 : (n : ℂ) ≠ 0 := by simp [hn]
      rw [Real.rpow_def_of_pos l1, Complex.cpow_def_of_ne_zero l2, Complex.cpow_def_of_ne_zero l3]
      push_cast
      simp_rw [← Complex.exp_sub]
      congr 1
      rw [first_fourier_aux2a, Real.log_div l1.ne.symm hx.ne.symm]
      push_cast
      rw [Complex.ofReal_log hx.le]
      ring
    _ = _ := by simp ; group

lemma first_fourier (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hsupp : Integrable ψ) (hx : 0 < x) (hσ : 1 < σ') :
    ∑' n : ℕ, term f σ' n * (𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))) =
    ∫ t : ℝ, LSeries f (σ' + t * I) * ψ t * x ^ (t * I) := by

  calc
    _ = ∑' n, term f σ' n * ∫ (v : ℝ), 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      simp only [Real.fourier_eq]
      simp only [one_div, mul_inv_rev, RCLike.inner_apply', conj_trivial]
    _ = ∑' n, ∫ (v : ℝ), term f σ' n * 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      simp [integral_const_mul]
    _ = ∫ (v : ℝ), ∑' n, term f σ' n * 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      refine (integral_tsum ?_ ?_).symm
      · refine fun _ ↦ AEMeasurable.aestronglyMeasurable ?_
        have := hsupp.aemeasurable
        fun_prop
      · simp only [enorm_mul]
        simp_rw [lintegral_const_mul'' _ (first_fourier_aux1 hsupp.aemeasurable _)]
        calc
          _ = (∑' (i : ℕ), ‖term f σ' i‖ₑ) * ∫⁻ (a : ℝ), ‖ψ a‖ₑ ∂volume := by
            simp [ENNReal.tsum_mul_right, enorm_eq_nnnorm]
          _ ≠ ⊤ := ENNReal.mul_ne_top (hf_coe1 hf hσ)
            (ne_top_of_lt hsupp.2)
    _ = _ := by
      congr 1; ext y
      simp_rw [mul_assoc (LSeries _ _), ← smul_eq_mul (a := (LSeries _ _)), LSeries]
      rw [← Summable.tsum_smul_const]
      · simp_rw [first_fourier_aux2 hx]
      · apply Summable.of_norm
        convert hf σ' hσ with n
        rw [norm_term_eq_nterm_re]
        simp



lemma second_fourier_integrable_aux1a (hσ : 1 < σ') :
    IntegrableOn (fun (x : ℝ) ↦ cexp (-((x : ℂ) * ((σ' : ℂ) - 1)))) (Ici (-Real.log x)) := by
  norm_cast
  suffices IntegrableOn (fun (x : ℝ) ↦ (rexp (-(x * (σ' - 1))))) (Ici (-x.log)) _ from this.ofReal
  simp_rw [fun (a x : ℝ) ↦ (by ring : -(x * a) = -a * x)]
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  apply exp_neg_integrableOn_Ioi
  linarith

lemma second_fourier_integrable_aux1 (hcont : Measurable ψ) (hsupp : Integrable ψ) (hσ : 1 < σ') :
    let ν : Measure (ℝ × ℝ) := (volume.restrict (Ici (-Real.log x))).prod volume
    Integrable (Function.uncurry fun (u : ℝ) (a : ℝ) ↦ ((rexp (-u * (σ' - 1))) : ℂ) •
    (𝐞 (Multiplicative.ofAdd (-(a * (u / (2 * π))))) : ℂ) • ψ a) ν := by
  intro ν
  constructor
  · apply Measurable.aestronglyMeasurable
    -- `Multiplicative.ofAdd x` is definitionally `x`; unfold it by `change` since `fun_prop`
    -- does not see through it.
    change Measurable (Function.uncurry fun (u : ℝ) (a : ℝ) ↦ ((rexp (-u * (σ' - 1))) : ℂ) •
      (𝐞 (-(a * (u / (2 * π)))) : ℂ) • ψ a)
    simp only [neg_mul, ofReal_exp, ofReal_neg, ofReal_mul, ofReal_sub, ofReal_one, smul_eq_mul]
    fun_prop
  · let f1 : ℝ → ENNReal := fun a1 ↦ ‖cexp (-(↑a1 * (↑σ' - 1)))‖ₑ
    let f2 : ℝ → ENNReal := fun a2 ↦ ‖ψ a2‖ₑ
    suffices ∫⁻ (a : ℝ × ℝ), f1 a.1 * f2 a.2 ∂ν < ⊤ by
      simpa [hasFiniteIntegral_iff_enorm, enorm_eq_nnnorm, Function.uncurry]
    refine (lintegral_prod_mul ?_ ?_).trans_lt ?_ <;> try fun_prop
    exact ENNReal.mul_lt_top (second_fourier_integrable_aux1a hσ).2 hsupp.2

lemma second_fourier_integrable_aux2 (hσ : 1 < σ') :
    IntegrableOn (fun (u : ℝ) ↦ cexp ((1 - ↑σ' - ↑t * I) * ↑u)) (Ioi (-Real.log x)) := by
  refine (integrable_norm_iff (Measurable.aestronglyMeasurable <| by fun_prop)).mp ?_
  suffices IntegrableOn (fun a ↦ rexp (-(σ' - 1) * a)) (Ioi (-x.log)) _ by simpa [Complex.norm_exp]
  apply exp_neg_integrableOn_Ioi
  linarith

lemma second_fourier_aux (hx : 0 < x) :
    -(cexp (-((1 - ↑σ' - ↑t * I) * ↑(Real.log x))) / (1 - ↑σ' - ↑t * I)) =
    ↑(x ^ (σ' - 1)) * (↑σ' + ↑t * I - 1)⁻¹ * ↑x ^ (↑t * I) := by
  calc
    _ = cexp (↑(Real.log x) * ((↑σ' - 1) + ↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [← div_neg]; ring_nf
    _ = (x ^ ((↑σ' - 1) + ↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt hx)), Complex.ofReal_log hx.le]
    _ = (x ^ ((σ' : ℂ) - 1)) * (x ^ (↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [Complex.cpow_add _ _ (ofReal_ne_zero.mpr (ne_of_gt hx))]
    _ = _ := by rw [ofReal_cpow hx.le]; push_cast; ring

lemma second_fourier (hcont : Measurable ψ) (hsupp : Integrable ψ)
    {x σ' : ℝ} (hx : 0 < x) (hσ : 1 < σ') :
    ∫ u in Ici (-log x), Real.exp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)) =
    (x^(σ' - 1) : ℝ) * ∫ t, (1 / (σ' + t * I - 1)) * ψ t * x^(t * I) ∂ volume := by

  conv in ↑(rexp _) * _ => { rw [Real.fourier_real_eq, ← smul_eq_mul, ← integral_smul] }
  rw [MeasureTheory.integral_integral_swap]
  swap
  · exact second_fourier_integrable_aux1 hcont hsupp hσ
  rw [← integral_const_mul]
  congr 1; ext t
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  rw [fun (a b d : ℂ) ↦ show a * (b * (ψ t) * d) = (a * b * d) * ψ t by ring]
  simp_rw [← mul_assoc]
  rw [integral_mul_const]
  congr 1
  push_cast
  simp_rw [← Complex.exp_add]
  have (u : ℝ) :
      -↑u * (↑σ' - 1) + 2 * ↑π * -(↑t * (↑u / (2 * ↑π))) * I = (1 - σ' - t * I) * u := calc
    _ = -↑u * (↑σ' - 1) + (2 * ↑π) / (2 * ↑π) * -(↑t * ↑u) * I := by ring
    _ = -↑u * (↑σ' - 1) + 1 * -(↑t * ↑u) * I := by rw [div_self (by norm_num)]
    _ = _ := by ring
  simp_rw [this]
  let c : ℂ := (1 - ↑σ' - ↑t * I)
  have : c ≠ 0 := by simp [Complex.ext_iff, c, sub_ne_zero.mpr hσ.ne]
  let f' (u : ℝ) := cexp (c * u)
  let f := fun (u : ℝ) ↦ (f' u) / c
  have hderiv : ∀ u ∈ Ici (-Real.log x), HasDerivAt f (f' u) u := by
    intro u _
    rw [show f' u = cexp (c * u) * (c * 1) / c by simp only [f']; field_simp]
    exact (hasDerivAt_id' u).ofReal_comp.const_mul c |>.cexp.div_const c
  have hf : Tendsto f atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    suffices Tendsto (fun (x : ℝ) ↦ ‖cexp (c * ↑x)‖ / ‖c‖) atTop (𝓝 (0 / ‖c‖)) by
      simpa [f, f'] using this
    apply Filter.Tendsto.div_const
    suffices Tendsto (· * (1 - σ')) atTop atBot by simpa [Complex.norm_exp, mul_comm (1 - σ'), c]
    exact Tendsto.atTop_mul_const_of_neg (by linarith) fun ⦃s⦄ h ↦ h
  rw [integral_Ici_eq_integral_Ioi,
    integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (second_fourier_integrable_aux2 hσ) hf]
  simpa [f, f'] using second_fourier_aux hx



lemma one_add_sq_pos (u : ℝ) : 0 < 1 + u ^ 2 := zero_lt_one.trans_le (by simpa using sq_nonneg u)

lemma decay_bounds_key (f : W21) (u : ℝ) : ‖𝓕 (f : ℝ → ℂ) u‖ ≤ ‖f‖ * (1 + u ^ 2)⁻¹ := by
  have l1 : 0 < 1 + u ^ 2 := one_add_sq_pos _
  have l2 : 1 + u ^ 2 = ‖(1 : ℂ) + u ^ 2‖ := by
    norm_cast ; simp only [Real.norm_eq_abs, abs_eq_self.2 l1.le]
  have l3 : ‖1 / ((4 : ℂ) * ↑π ^ 2)‖ ≤ (4 * π ^ 2)⁻¹ := by simp
  have key := fourierIntegral_self_add_deriv_deriv f u
  simp only [Function.iterate_succ _ 1, Function.iterate_one, Function.comp_apply] at key
  rw [F_sub f.hf (f.hf''.const_mul (1 / (4 * ↑π ^ 2)))] at key
  rw [← div_eq_mul_inv, le_div_iff₀ l1, mul_comm, l2, ← norm_mul, key, sub_eq_add_neg]
  apply norm_add_le _ _ |>.trans
  change _ ≤ W21.norm _
  rw [norm_neg, F_mul, norm_mul, W21.norm]
  gcongr <;> apply VectorFourier.norm_fourierIntegral_le_integral_norm

lemma decay_bounds_cor (ψ : W21) :
    ∃ C : ℝ, ∀ u, ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ C / (1 + u ^ 2) := by
  simpa only [div_eq_mul_inv] using ⟨_, decay_bounds_key ψ⟩

lemma continuous_FourierIntegral (ψ : W21) : Continuous (𝓕 (ψ : ℝ → ℂ)) :=
  VectorFourier.fourierIntegral_continuous continuous_fourierChar
    (by simp only [innerₗ_apply_apply, RCLike.inner_apply', conj_trivial, continuous_mul])
    ψ.hf

lemma W21.integrable_fourier (ψ : W21) (hc : c ≠ 0) :
    Integrable fun u ↦ 𝓕 (ψ : ℝ → ℂ) (u / c) := by
  have l1 (C) : Integrable (fun u ↦ C / (1 + (u / c) ^ 2)) volume := by
    simpa using! (integrable_inv_one_add_sq.comp_div hc).const_mul C
  have l2 : AEStronglyMeasurable (fun u ↦ 𝓕 (ψ : ℝ → ℂ) (u / c)) volume := by
    apply Continuous.aestronglyMeasurable ; have := continuous_FourierIntegral ψ ; fun_prop
  obtain ⟨C, h⟩ := decay_bounds_cor ψ
  apply @Integrable.mono' ℝ ℂ _ volume _ _ (fun u => C / (1 + (u / c) ^ 2)) (l1 C) l2 ?_
  apply Eventually.of_forall (fun x => h _)





lemma continuous_LSeries_aux (hf : Summable (nterm f σ')) :
    Continuous fun x : ℝ => LSeries f (σ' + x * I) := by

  have l1 i : Continuous fun x : ℝ ↦ term f (σ' + x * I) i := by
    by_cases h : i = 0
    · simpa [h] using continuous_const
    · simpa [h] using! continuous_const.div (continuous_const.cpow (by fun_prop) (by simp [h]))
        (fun x => by simp [h])
  have l2 n (x : ℝ) : ‖term f (σ' + x * I) n‖ = nterm f σ' n := by
    by_cases h : n = 0
    · simp [h, nterm]
    · simp [h, nterm, cpow_add _ _ (Nat.cast_ne_zero.mpr h),
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero h)]
  exact continuous_tsum l1 hf (fun n x => le_of_eq (l2 n x))

-- Here compact support is used but perhaps it is not necessary
lemma limiting_fourier_aux (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (ψ : CS 2 ℂ) (hx : 1 ≤ x) (σ' : ℝ)
    (hσ' : 1 < σ') :
    ∑' n, term f σ' n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
    A * (x ^ (1 - σ') : ℝ) * ∫ u in Ici (- log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ)
      (u / (2 * π)) = ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I) := by
  have hint : Integrable ψ := ψ.h1.continuous.integrable_of_hasCompactSupport ψ.h2
  have l3 : 0 < x := zero_lt_one.trans_le hx
  have l1 (σ') (hσ' : 1 < σ') := first_fourier hf hint l3 hσ'
  have l2 (σ') (hσ' : 1 < σ') := second_fourier ψ.h1.continuous.measurable hint l3 hσ'
  have l8 : Continuous fun t : ℝ ↦ (x : ℂ) ^ (t * I) :=
    continuous_const.cpow (continuous_ofReal.mul continuous_const) (by simp [l3])
  have l6 : Continuous fun t : ℝ ↦ LSeries f (↑σ' + ↑t * I) * ψ t * ↑x ^ (↑t * I) := by
    apply ((continuous_LSeries_aux (hf _ hσ')).mul ψ.h1.continuous).mul l8
  have l4 : Integrable fun t : ℝ ↦ LSeries f (↑σ' + ↑t * I) * ψ t * ↑x ^ (↑t * I) := by
    exact l6.integrable_of_hasCompactSupport ψ.h2.mul_left.mul_right
  have e2 (u : ℝ) : σ' + u * I - 1 ≠ 0 := by
    intro h ; have := congr_arg Complex.re h ; simp at this ; linarith
  have l7 : Continuous fun a ↦ A * ↑(x ^ (1 - σ')) * (↑(x ^ (σ' - 1)) *
      (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
    simp only [one_div, ← mul_assoc]
    refine ((continuous_const.mul <| Continuous.inv₀ ?_ e2).mul ψ.h1.continuous).mul l8
    fun_prop
  have l5 : Integrable fun a ↦ A * ↑(x ^ (1 - σ')) * (↑(x ^ (σ' - 1)) *
      (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
    apply l7.integrable_of_hasCompactSupport
    exact ψ.h2.mul_left.mul_right.mul_left.mul_left

  simp_rw [l1 σ' hσ', l2 σ' hσ', ← integral_const_mul, ← integral_sub l4 l5]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro u
  have e1 : 1 < ((σ' : ℂ) + (u : ℂ) * I).re := by simp [hσ']
  simp_rw [hG' e1, sub_mul, ← mul_assoc]
  simp only [one_div, sub_right_inj, mul_eq_mul_right_iff, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq,
    mul_eq_zero, I_ne_zero, or_false]
  left ; left
  field_simp [e2]
  norm_cast
  simp [mul_assoc, ← rpow_add l3]

section nabla

variable {α E : Type*} [OfNat α 1] [Add α] [Sub α] {u : α → ℂ}

def cumsum [AddCommMonoid E] (u : ℕ → E) (n : ℕ) : E := ∑ i ∈ Finset.range n, u i

def nabla [Sub E] (u : α → E) (n : α) : E := u (n + 1) - u n

/- `nnabla` is the backward difference `u n - u (n+1)`; kept alongside `nabla`
   for summation-by-parts identities that prefer that orientation. -/
def nnabla [Sub E] (u : α → E) (n : α) : E := u n - u (n + 1)

def shift (u : α → E) (n : α) : E := u (n + 1)

@[simp] lemma cumsum_zero [AddCommMonoid E] {u : ℕ → E} : cumsum u 0 = 0 := by simp [cumsum]

lemma cumsum_succ [AddCommMonoid E] {u : ℕ → E} (n : ℕ) :
    cumsum u (n + 1) = cumsum u n + u n := by
  simp [cumsum, Finset.sum_range_succ]

@[simp] lemma nabla_cumsum [AddCommGroup E] {u : ℕ → E} : nabla (cumsum u) = u := by
  ext n ; simp [nabla, cumsum, Finset.range_add_one]

lemma neg_cumsum [AddCommGroup E] {u : ℕ → E} : -(cumsum u) = cumsum (-u) :=
  funext (fun n => by simp [cumsum])

lemma cumsum_nonneg {u : ℕ → ℝ} (hu : 0 ≤ u) : 0 ≤ cumsum u :=
  fun _ => Finset.sum_nonneg (fun i _ => hu i)

omit [Sub α] in
lemma neg_nabla [Ring E] {u : α → E} : -(nabla u) = nnabla u := by ext n ; simp [nabla, nnabla]

omit [Sub α] in
@[simp] lemma nabla_mul [Ring E] {u : α → E} {c : E} : nabla (fun n => c * u n) = c • nabla u := by
  ext n ; simp [nabla, mul_sub]

omit [Sub α] in
@[simp] lemma nnabla_mul [Ring E] {u : α → E} {c : E} :
    nnabla (fun n => c * u n) = c • nnabla u := by
  ext n ; simp [nnabla, mul_sub]

end nabla

lemma Finset.sum_shift_front {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = u 0 + cumsum (shift u) n := by
  simp_rw [add_comm n, cumsum, sum_range_add, sum_range_one, add_comm 1] ; rfl

lemma Finset.sum_shift_back {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = cumsum u n + u n := by
  simp [cumsum, Finset.range_add_one, add_comm]

lemma summation_by_parts {E : Type*} [Ring E] {a A b : ℕ → E} (ha : a = nabla A) {n : ℕ} :
    cumsum (a * b) (n + 1) = A (n + 1) * b n - A 0 * b 0 -
    cumsum (shift A * fun i => (b (i + 1) - b i)) n := by
  have l1 : ∑ x ∈ Finset.range (n + 1), A (x + 1) * b x = ∑ x ∈ Finset.range n,
      A (x + 1) * b x + A (n + 1) * b n :=
    Finset.sum_shift_back
  have l2 : ∑ x ∈ Finset.range (n + 1), A x * b x = A 0 * b 0 + ∑ x ∈ Finset.range n,
      A (x + 1) * b (x + 1) :=
    Finset.sum_shift_front
  simp only [cumsum, ha, Pi.mul_apply, nabla, sub_mul, Finset.sum_sub_distrib, l1, l2, shift,
    mul_sub]
  abel

lemma summation_by_parts' {E : Type*} [Ring E] {a b : ℕ → E} {n : ℕ} :
    cumsum (a * b) (n + 1) = cumsum a (n + 1) * b n - cumsum (shift (cumsum a) * nabla b) n := by
  simpa using! summation_by_parts (a := a) (b := b) (A := cumsum a) (by simp)

lemma summation_by_parts'' {E : Type*} [Ring E] {a b : ℕ → E} :
    shift (cumsum (a * b)) = shift (cumsum a) * b - cumsum (shift (cumsum a) * nabla b) := by
  ext n ; apply summation_by_parts'

lemma summable_iff_bounded {u : ℕ → ℝ} (hu : 0 ≤ u) :
    Summable u ↔ BoundedAtFilter atTop (cumsum u) := by
  have l1 : (cumsum u =O[atTop] 1) ↔ _ := isBigO_one_nat_atTop_iff
  have l2 n : ‖cumsum u n‖ = cumsum u n := by simpa using cumsum_nonneg hu n
  simp only [BoundedAtFilter, l1, l2]
  constructor <;> intro ⟨C, h1⟩
  · exact ⟨C, fun n => sum_le_hasSum _ (fun i _ => hu i) h1⟩
  · exact summable_of_sum_range_le hu h1

lemma Filter.EventuallyEq.summable {u v : ℕ → ℝ} (h : u =ᶠ[atTop] v) (hu : Summable v) :
    Summable u :=
  summable_of_isBigO_nat hu h.isBigO

lemma summable_congr_ae {u v : ℕ → ℝ} (huv : u =ᶠ[atTop] v) : Summable u ↔ Summable v := by
  constructor <;> intro h <;> simp [huv.summable, huv.symm.summable, h]

lemma BoundedAtFilter.add_const {u : ℕ → ℝ} {c : ℝ} :
    BoundedAtFilter atTop (fun n => u n + c) ↔ BoundedAtFilter atTop u := by
  have : u = fun n => (u n + c) + (-c) := by ext n ; ring
  simp only [BoundedAtFilter]
  constructor <;> intro h
  on_goal 1 => rw [this]
  all_goals { exact h.add (const_boundedAtFilter _ _) }

lemma BoundedAtFilter.comp_add {u : ℕ → ℝ} {N : ℕ} :
    BoundedAtFilter atTop (fun n => u (n + N)) ↔ BoundedAtFilter atTop u := by
  simp only [BoundedAtFilter, isBigO_iff, norm_eq_abs, Pi.one_apply,
    eventually_atTop]
  constructor <;> intro ⟨C, n₀, h⟩ <;> use C
  · refine ⟨n₀ + N, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (m := N) (n := n) (by grind)
    exact h _ <| Nat.add_le_add_iff_right.mp hn
  · exact ⟨n₀, fun n hn => h _ (by grind)⟩

lemma summable_iff_bounded' {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, 0 ≤ u n) :
    Summable u ↔ BoundedAtFilter atTop (cumsum u) := by
  obtain ⟨N, hu⟩ := eventually_atTop.mp hu
  have e2 : cumsum (fun i ↦ u (i + N)) = fun n => cumsum u (n + N) - cumsum u N := by
    ext n ; simp_rw [cumsum, add_comm _ N, Finset.sum_range_add] ; ring
  rw [← summable_nat_add_iff N, summable_iff_bounded (fun n => hu _ <| Nat.le_add_left N n), e2]
  simp_rw [sub_eq_add_neg, BoundedAtFilter.add_const, BoundedAtFilter.comp_add]

lemma bounded_of_shift {u : ℕ → ℝ} (h : BoundedAtFilter atTop (shift u)) :
    BoundedAtFilter atTop u := by
  simp only [BoundedAtFilter, isBigO_iff, eventually_atTop] at h ⊢
  obtain ⟨C, N, hC⟩ := h
  refine ⟨C, N + 1, fun n hn => ?_⟩
  simp only [shift] at hC
  have r1 : n - 1 ≥ N := Nat.le_sub_one_of_lt hn
  have r2 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  simpa [r2] using hC (n - 1) r1

lemma dirichlet_test' {a b : ℕ → ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hAb : BoundedAtFilter atTop (shift (cumsum a) * b)) (hbb : ∀ᶠ n in atTop, b (n + 1) ≤ b n)
    (h : Summable (shift (cumsum a) * nnabla b)) : Summable (a * b) := by
  have l1 : ∀ᶠ n in atTop, 0 ≤ (shift (cumsum a) * nnabla b) n := by
    filter_upwards [hbb] with n hb
    exact mul_nonneg (by simpa [shift] using! Finset.sum_nonneg' ha) (sub_nonneg.mpr hb)
  rw [summable_iff_bounded (mul_nonneg ha hb)]
  rw [summable_iff_bounded' l1] at h
  apply bounded_of_shift
  simpa only [summation_by_parts'', sub_eq_add_neg, neg_cumsum, ← mul_neg, neg_nabla]
    using hAb.add h

lemma exists_antitone_of_eventually {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, u (n + 1) ≤ u n) :
    ∃ v : ℕ → ℝ, range v ⊆ range u ∧ Antitone v ∧ v =ᶠ[atTop] u := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hu
  let v (n : ℕ) := u (if n < N then N else n)
  refine ⟨v, ?_, ?_, ?_⟩
  · exact fun x ⟨n, hn⟩ => ⟨if n < N then N else n, hn⟩
  · refine antitone_nat_of_succ_le (fun n => ?_)
    by_cases h : n < N
    · by_cases h' : n + 1 < N <;> simp [v, h, h']
      have : n + 1 = N := by linarith
      simp [this]
    · have : ¬(n + 1 < N) := by linarith
      simp only [this, ↓reduceIte, h, ge_iff_le, v] ; apply hN ; linarith
  · have : ∀ᶠ n in atTop, ¬(n < N) := by simpa using ⟨N, fun b hb => by linarith⟩
    filter_upwards [this] with n hn ; simp [v, hn]

lemma summable_inv_mul_log_sq : Summable (fun n : ℕ => (n * (Real.log n) ^ 2)⁻¹) := by
  let u (n : ℕ) := (n * (Real.log n) ^ 2)⁻¹
  have l7 : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n :=
    tendsto_atTop.mp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop) 1
  have l8 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  have l9 : ∀ᶠ n in atTop, u (n + 1) ≤ u n := by
    filter_upwards [l7, l8] with n l2 l8; dsimp [u]; gcongr <;> simp
  obtain ⟨v, l1, l2, l3⟩ := exists_antitone_of_eventually l9
  rw [summable_congr_ae l3.symm]
  have l4 (n : ℕ) : 0 ≤ v n := by obtain ⟨k, hk⟩ := l1 ⟨n, rfl⟩ ; rw [← hk] ; positivity
  apply (summable_condensed_iff_of_nonneg l4 (fun _ _ _ a ↦ l2 a)).mp
  suffices this : ∀ᶠ k : ℕ in atTop, 2 ^ k * v (2 ^ k) = ((k : ℝ) ^ 2)⁻¹ * ((Real.log 2) ^ 2)⁻¹ by
    exact (summable_congr_ae this).mpr <| (Real.summable_nat_pow_inv.mpr one_lt_two).mul_right _
  have l5 : ∀ᶠ k in atTop, v (2 ^ k) = u (2 ^ k) :=
    l3.comp_tendsto <| tendsto_pow_atTop_atTop_of_one_lt Nat.le.refl
  filter_upwards [l5, l8] with k l5 l8
  simp only [l5, mul_inv_rev, Nat.cast_pow, Nat.cast_ofNat, log_pow, u]
  field_simp

lemma tendsto_mul_add_atTop {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x => a * x + b) atTop atTop :=
  tendsto_atTop_add_const_right _ b (tendsto_id.const_mul_atTop ha)

lemma isLittleO_const_of_tendsto_atTop {α : Type*} [Preorder α] (a : ℝ) {f : α → ℝ}
    (hf : Tendsto f atTop atTop) : (fun _ => a) =o[atTop] f := by
  simp [tendsto_norm_atTop_atTop.comp hf]

lemma isLittleO_mul_add_sq (a b : ℝ) : (fun x => a * x + b) =o[atTop] (fun x => x ^ 2) := by
  apply IsLittleO.add
  · apply IsLittleO.const_mul_left ; simpa using isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) one_lt_two
  · apply isLittleO_const_of_tendsto_atTop _ <| tendsto_pow_atTop (by linarith)

lemma log_mul_add_isBigO_log {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (fun x => Real.log (a * x + b)) =O[atTop] Real.log := by
  apply IsBigO.of_bound (2 : ℕ)
  have l2 : ∀ᶠ x : ℝ in atTop, 0 ≤ log x := tendsto_atTop.mp tendsto_log_atTop 0
  have l3 : ∀ᶠ x : ℝ in atTop, 0 ≤ log (a * x + b) :=
    tendsto_atTop.mp (tendsto_log_atTop.comp (tendsto_mul_add_atTop ha b)) 0
  have l5 : ∀ᶠ x : ℝ in atTop, 1 ≤ a * x + b := tendsto_atTop.mp (tendsto_mul_add_atTop ha b) 1
  have l1 : ∀ᶠ x : ℝ in atTop, a * x + b ≤ x ^ 2 := by
    filter_upwards [(isLittleO_mul_add_sq a b).eventuallyLE, l5] with x r2 l5
    simpa [abs_eq_self.mpr (zero_le_one.trans l5)] using r2
  filter_upwards [l1, l2, l3, l5] with x l1 l2 l3 l5
  simpa [abs_eq_self.mpr l2, abs_eq_self.mpr l3, Real.log_pow] using
    Real.log_le_log (by linarith) l1

lemma isBigO_log_mul_add {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Real.log =O[atTop] (fun x => Real.log (a * x + b)) := by
  convert! (log_mul_add_isBigO_log (b := -b / a) (inv_pos.mpr ha)).comp_tendsto
    (tendsto_mul_add_atTop (b := b) ha) using 1
  ext x
  simp only [Function.comp_apply]
  congr
  field_simp
  simp

lemma log_isbigo_log_div {d : ℝ} (hb : 0 < d) :
    (fun n ↦ Real.log n) =O[atTop] (fun n ↦ Real.log (n / d)) := by
  convert isBigO_log_mul_add (inv_pos.mpr hb) 0 using 1; simp only [add_zero]; field_simp

lemma Asymptotics.IsBigO.add_isLittleO_right {f g : ℝ → ℝ} (h : g =o[atTop] f) :
    f =O[atTop] (f + g) := by
  rw [isLittleO_iff] at h ; specialize h (c := 2⁻¹) (by norm_num)
  rw [isBigO_iff'']
  refine ⟨2⁻¹, by norm_num, ?_⟩
  filter_upwards [h] with x h
  simp only [norm_eq_abs, Pi.add_apply] at h ⊢
  calc _ = |f x| - 2⁻¹ * |f x| := by ring
       _ ≤ |f x| - |g x| := by linarith
       _ ≤ |(|f x| - |g x|)| := le_abs_self _
       _ ≤ _ := by rw [← sub_neg_eq_add, ← abs_neg (g x)] ; exact abs_abs_sub_abs_le (f x) (-g x)

lemma Asymptotics.IsBigO.sq {α : Type*} [Preorder α] {f g : α → ℝ} (h : f =O[atTop] g) :
    (fun n ↦ f n ^ 2) =O[atTop] (fun n => g n ^ 2) := by
  simpa [pow_two] using h.mul h

lemma log_sq_isbigo_mul {a b : ℝ} (hb : 0 < b) :
    (fun x ↦ Real.log x ^ 2) =O[atTop] (fun x ↦ a + Real.log (x / b) ^ 2) := by
  apply (log_isbigo_log_div hb).sq.trans ; simp_rw [add_comm a]
  refine IsBigO.add_isLittleO_right <| isLittleO_const_of_tendsto_atTop _ ?_
  exact (tendsto_pow_atTop two_ne_zero).comp <|
    tendsto_log_atTop.comp <| tendsto_id.atTop_div_const hb

theorem log_add_div_isBigO_log (a : ℝ) {b : ℝ} (hb : 0 < b) :
    (fun x ↦ Real.log ((x + a) / b)) =O[atTop] fun x ↦ Real.log x := by
  convert log_mul_add_isBigO_log (inv_pos.mpr hb) (a / b) using 3 ; ring

lemma log_add_one_sub_log_le {x : ℝ} (hx : 0 < x) : nabla Real.log x ≤ x⁻¹ := by
  have l1 : ContinuousOn Real.log (Icc x (x + 1)) := by
    apply continuousOn_log.mono ; intro t ⟨h1, _⟩ ; simp ; linarith
  have l2 t (ht : t ∈ Ioo x (x + 1)) : HasDerivAt Real.log t⁻¹ t :=
    Real.hasDerivAt_log (by linarith [ht.1])
  obtain ⟨t, ⟨ht1, _⟩, htx⟩ := exists_hasDerivAt_eq_slope Real.log (·⁻¹) (by linarith) l1 l2
  simp only [add_sub_cancel_left, div_one] at htx
  rw [nabla, ← htx, inv_le_inv₀ (by linarith) hx]
  exact ht1.le

lemma nabla_log_main : nabla Real.log =O[atTop] fun x ↦ 1 / x := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_gt_atTop 0] with x l1
  have l2 : log x ≤ log (x + 1) := log_le_log l1 (by linarith)
  simpa [nabla, abs_eq_self.mpr l1.le, abs_eq_self.mpr (sub_nonneg.mpr l2)] using
    log_add_one_sub_log_le l1

lemma nabla_log {b : ℝ} (hb : 0 < b) :
    nabla (fun x => Real.log (x / b)) =O[atTop] (fun x => 1 / x) := by
  refine EventuallyEq.trans_isBigO ?_ nabla_log_main
  filter_upwards [eventually_gt_atTop 0] with x l2
  rw [nabla, log_div (by linarith) (by linarith), log_div l2.ne.symm (by linarith), nabla] ; ring

lemma nnabla_mul_log_sq (a : ℝ) {b : ℝ} (hb : 0 < b) :
    nabla (fun x => x * (a + Real.log (x / b) ^ 2)) =O[atTop] (fun x => Real.log x ^ 2) := by

  have l1 : nabla (fun n => n * (a + Real.log (n / b) ^ 2)) = fun n =>
      a + Real.log ((n + 1) / b) ^ 2 +
        (n * (Real.log ((n + 1) / b) ^ 2 - Real.log (n / b) ^ 2)) := by
    ext n ; simp [nabla] ; ring
  have l2 := (isLittleO_const_of_tendsto_atTop a
    ((tendsto_pow_atTop two_ne_zero).comp tendsto_log_atTop)).isBigO
  have l3 := (log_add_div_isBigO_log 1 hb).sq
  have l4 : (fun x => Real.log ((x + 1) / b) + Real.log (x / b)) =O[atTop] Real.log := by
    simpa using (log_add_div_isBigO_log _ hb).add (log_add_div_isBigO_log 0 hb)
  have e2 : (fun x : ℝ => x * (Real.log x * (1 / x))) =ᶠ[atTop] Real.log := by
    filter_upwards [eventually_ge_atTop 1] with x hx using by field_simp
  have l5 : (fun n ↦ n * (Real.log n * (1 / n))) =O[atTop] (fun n ↦ (Real.log n) ^ 2) :=
    e2.trans_isBigO
      (by simpa using! (isLittleO_mul_add_sq 1 0).isBigO.comp_tendsto Real.tendsto_log_atTop)

  simp_rw [l1, _root_.sq_sub_sq]
  exact ((l2.add l3).add (isBigO_refl (·) atTop |>.mul (l4.mul (nabla_log hb)) |>.trans l5))

lemma nnabla_bound_aux1 (a : ℝ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun x => x * (a + Real.log (x / b) ^ 2)) atTop atTop :=
  tendsto_id.atTop_mul_atTop₀ <| tendsto_atTop_add_const_left _ _ <|
    (tendsto_pow_atTop two_ne_zero).comp <| tendsto_log_atTop.comp <| tendsto_id.atTop_div_const hb

lemma nnabla_bound_aux2 (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ x in atTop, 0 < x * (a + Real.log (x / b) ^ 2) :=
  (nnabla_bound_aux1 a hb).eventually (eventually_gt_atTop 0)

lemma Real.log_eventually_gt_atTop (a : ℝ) :
    ∀ᶠ x in atTop, a < Real.log x :=
  Real.tendsto_log_atTop.eventually (eventually_gt_atTop a)

/-- Should this be a gcongr lemma? -/
theorem norm_lt_norm_of_nonneg (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    ‖x‖ ≤ ‖y‖ := by
  simp_rw [Real.norm_eq_abs]
  apply abs_le_abs hxy
  linarith

lemma nnabla_bound_aux {x : ℝ} (hx : 0 < x) :
    nnabla (fun n ↦ 1 / (n * ((2 * π) ^ 2 + Real.log (n / x) ^ 2))) =O[atTop]
    (fun n ↦ 1 / (Real.log n ^ 2 * n ^ 2)) := by

  let d n : ℝ := n * ((2 * π) ^ 2 + Real.log (n / x) ^ 2)
  change (fun x_1 ↦ nnabla (fun n ↦ 1 / d n) x_1) =O[atTop] _

  have l2 : ∀ᶠ n in atTop, 0 < d n := (nnabla_bound_aux2 ((2 * π) ^ 2) hx)
  have l3 : ∀ᶠ n in atTop, 0 < d (n + 1) :=
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id).eventually l2
  have l1 : ∀ᶠ n : ℝ in atTop,
      nnabla (fun n ↦ 1 / d n) n = (d (n + 1) - d n) * (d n)⁻¹ * (d (n + 1))⁻¹ := by
    filter_upwards [l2, l3] with n l2 l3
    rw [nnabla, one_div, one_div, inv_sub_inv l2.ne.symm l3.ne.symm, div_eq_mul_inv, mul_inv,
      mul_assoc]

  have l4 : (fun n => (d n)⁻¹) =O[atTop] (fun n => (n * (Real.log n) ^ 2)⁻¹) := by
    apply IsBigO.inv_rev
    · refine (isBigO_refl _ _).mul <| (log_sq_isbigo_mul hx)
    · filter_upwards [Real.log_eventually_gt_atTop 0, eventually_gt_atTop 0] with x hx hx'
      rw [← not_imp_not]
      intro _
      positivity
  have l5 : (fun n => (d (n + 1))⁻¹) =O[atTop] (fun n => (n * (Real.log n) ^ 2)⁻¹) := by
    refine IsBigO.trans ?_ l4
    rw [isBigO_iff]; use 1
    have e3 : ∀ᶠ n in atTop, d n ≤ d (n + 1) := by
      filter_upwards [eventually_ge_atTop x] with n hn
      have e2 : 1 ≤ n / x := (one_le_div hx).mpr hn
      have : 0 ≤ n := hx.le.trans hn
      simp only [d]
      gcongr <;> simp [Real.log_nonneg, *]
    filter_upwards [l2, l3, e3] with n e1 e2 e3
    simp_rw [one_mul]
    exact norm_lt_norm_of_nonneg _ _ (inv_nonneg.mpr e2.le) (inv_anti₀ e1 e3)

  have l6 : (fun n => d (n + 1) - d n) =O[atTop] (fun n => (Real.log n) ^ 2) := by
    simpa [d, nabla] using! (nnabla_mul_log_sq ((2 * π) ^ 2) hx)

  apply EventuallyEq.trans_isBigO l1

  apply ((l6.mul l4).mul l5).trans_eventuallyEq
  filter_upwards [eventually_ge_atTop 2, Real.log_eventually_gt_atTop 0] with n hn hn'
  field_simp

lemma nnabla_bound (C : ℝ) {x : ℝ} (hx : 0 < x) :
    nnabla (fun n => C / (1 + (Real.log (n / x) / (2 * π)) ^ 2) / n) =O[atTop]
    (fun n => (n ^ 2 * (Real.log n) ^ 2)⁻¹) := by
  field_simp
  simp only [div_eq_mul_inv, mul_inv, nnabla_mul, one_mul]
  apply IsBigO.const_mul_left
  simpa [div_eq_mul_inv, mul_pow, mul_comm] using nnabla_bound_aux hx

def chebyWith (C : ℝ) (f : ℕ → ℂ) : Prop := ∀ n, cumsum (‖f ·‖) n ≤ C * n

def cheby (f : ℕ → ℂ) : Prop := ∃ C, chebyWith C f

lemma cheby.bigO (h : cheby f) : cumsum (‖f ·‖) =O[atTop] ((↑) : ℕ → ℝ) := by
  have l1 : 0 ≤ cumsum (‖f ·‖) := cumsum_nonneg (fun _ => norm_nonneg _)
  obtain ⟨C, hC⟩ := h
  apply isBigO_of_le' (c := C) atTop
  intro n
  rw [Real.norm_eq_abs, abs_eq_self.mpr (l1 n)]
  simpa using hC n

lemma limiting_fourier_lim1_aux (hcheby : cheby f) (hx : 0 < x) (C : ℝ) (hC : 0 ≤ C) :
    Summable fun n ↦ ‖f n‖ / ↑n * (C / (1 + (1 / (2 * π) * Real.log (↑n / x)) ^ 2)) := by

  let a (n : ℕ) := (C / (1 + (Real.log (↑n / x) / (2 * π)) ^ 2) / ↑n)
  replace hcheby := hcheby.bigO

  have l1 : shift (cumsum (‖f ·‖)) =O[atTop] (fun n : ℕ => (↑(n + 1) : ℝ)) :=
    hcheby.comp_tendsto <| tendsto_add_atTop_nat 1
  have l2 : shift (cumsum (‖f ·‖)) =O[atTop] (fun n => (n : ℝ)) :=
    l1.trans
      (by simpa using (isBigO_refl _ _).add <| isBigO_iff.mpr ⟨1, by simpa using ⟨1, by tauto⟩⟩)
  have l5 : BoundedAtFilter atTop (fun n : ℕ => C / (1 + (Real.log (↑n / x) / (2 * π)) ^ 2)) := by
    simp only [BoundedAtFilter]
    field_simp
    apply isBigO_of_le' (c := C) ; intro n
    have : 0 ≤ 2 ^ 2 * π ^ 2 + Real.log (n / x) ^ 2 := by positivity
    simp only [norm_div, norm_mul, norm_eq_abs, abs_eq_self.mpr hC, norm_pow,
      abs_eq_self.mpr pi_nonneg, abs_eq_self.mpr this, Pi.one_apply, one_mem,
      CStarRing.norm_of_mem_unitary, mul_one, ge_iff_le, Nat.abs_ofNat]
    apply div_le_of_le_mul₀ this hC
    rw [mul_add, ← mul_assoc]
    apply le_add_of_le_of_nonneg le_rfl
    positivity
  have l3 : a =O[atTop] (fun n => 1 / (n : ℝ)) := by
    simpa [a] using! IsBigO.mul l5 (isBigO_refl (fun n : ℕ => 1 / (n : ℝ)) _)
  have l4 : nnabla a =O[atTop] (fun n : ℕ => (n ^ 2 * (Real.log n) ^ 2)⁻¹) := by
    convert (nnabla_bound C hx).natCast ; simp [nnabla, a]

  simp_rw [div_mul_eq_mul_div, mul_div_assoc, one_mul]
  apply dirichlet_test'
  · intro n ; exact norm_nonneg _
  · intro n ; positivity
  · apply (l2.mul l3).trans_eventuallyEq
    apply eventually_of_mem (Ici_mem_atTop 1)
    intro x (hx : 1 ≤ x)
    have : x ≠ 0 := Nat.one_le_iff_ne_zero.mp hx
    simp [this]
  · have : ∀ᶠ n : ℕ in atTop, x ≤ n := by simpa using eventually_ge_atTop ⌈x⌉₊
    filter_upwards [this] with n hn
    have e1 : 0 < (n : ℝ) := by linarith
    have e2 : 1 ≤ n / x := (one_le_div hx).mpr hn
    have e3 := Nat.le_succ n
    gcongr
    refine div_nonneg (Real.log_nonneg e2) (by norm_num [pi_nonneg])
  · apply summable_of_isBigO_nat summable_inv_mul_log_sq
    apply (l2.mul l4).trans_eventuallyEq
    apply eventually_of_mem (Ici_mem_atTop 2)
    intro x (hx : 2 ≤ x)
    have : (x : ℝ) ≠ 0 := by simp ; linarith
    have : Real.log x ≠ 0 := by
      have ll : 2 ≤ (x : ℝ) := by simp [hx]
      simp
      grind
    field_simp

theorem limiting_fourier_lim1 (hcheby : cheby f) (ψ : W21) (hx : 0 < x) :
    Tendsto (fun σ' : ℝ ↦
        ∑' n, term f σ' n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (n / x))) (𝓝[>] 1)
      (𝓝 (∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (n / x)))) := by

  obtain ⟨C, hC⟩ := decay_bounds_cor ψ
  have : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 0)
  refine tendsto_tsum_of_dominated_convergence
    (limiting_fourier_lim1_aux hcheby hx C this) (fun n => ?_) ?_
  · apply Tendsto.mul_const
    by_cases h : n = 0 <;> simp only [term, h, ↓reduceIte, CharP.cast_eq_zero, div_zero,
      tendsto_const_nhds_iff]
    refine tendsto_const_nhds.div ?_ (by simp [h])
    simpa using ((continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds).const_cpow
  · rw [eventually_nhdsWithin_iff]
    apply Eventually.of_forall
    intro σ' (hσ' : 1 < σ') n
    rw [norm_mul, ← nterm_eq_norm_term]
    refine mul_le_mul ?_ (hC _) (norm_nonneg _) (div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
    by_cases h : n = 0 <;> simp only [nterm, h, ↓reduceIte, CharP.cast_eq_zero, div_zero, le_refl]
    have : 1 ≤ (n : ℝ) := by simpa using! Nat.pos_iff_ne_zero.mpr h
    refine div_le_div₀ (norm_nonneg _) le_rfl (by simpa [Nat.pos_iff_ne_zero]) ?_
    simpa using Real.rpow_le_rpow_of_exponent_le this hσ'.le

theorem limiting_fourier_lim2_aux (x : ℝ) (C : ℝ) :
    Integrable (fun t ↦ max |x| 1 * (C / (1 + (t / (2 * π)) ^ 2)))
      (Measure.restrict volume (Ici (-Real.log x))) := by
  simp_rw [div_eq_mul_inv C]
  exact (((integrable_inv_one_add_sq.comp_div
    (by simp [pi_ne_zero])).const_mul _).const_mul _).restrict

theorem limiting_fourier_lim2 (A : ℝ) (ψ : W21) (hx : 1 ≤ x) :
    Tendsto (fun σ' ↦ A * ↑(x ^ (1 - σ')) *
        ∫ u in Ici (-Real.log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))
      (𝓝[>] 1) (𝓝 (A * ∫ u in Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))) := by

  obtain ⟨C, hC⟩ := decay_bounds_cor ψ
  apply Tendsto.mul
  · suffices h : Tendsto (fun σ' : ℝ ↦ ofReal (x ^ (1 - σ'))) (𝓝[>] 1) (𝓝 1) by
      simpa using h.const_mul ↑A
    suffices h : Tendsto (fun σ' : ℝ ↦ x ^ (1 - σ')) (𝓝[>] 1) (𝓝 1) from
      (continuous_ofReal.tendsto 1).comp h
    have : Tendsto (fun σ' : ℝ ↦ σ') (𝓝 1) (𝓝 1) := fun _ a ↦ a
    have : Tendsto (fun σ' : ℝ ↦ 1 - σ') (𝓝[>] 1) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds (by simpa using this.const_sub 1)
    simpa using tendsto_const_nhds.rpow this (Or.inl (zero_lt_one.trans_le hx).ne.symm)
  · refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_
      (limiting_fourier_lim2_aux x C) ?_
    · apply Eventually.of_forall ; intro σ'
      apply Continuous.aestronglyMeasurable
      have := continuous_FourierIntegral ψ
      continuity
    · apply eventually_of_mem (U := Ioo 1 2)
      · apply Ioo_mem_nhdsGT_of_mem ; simp
      · intro σ' ⟨h1, h2⟩
        rw [ae_restrict_iff' measurableSet_Ici]
        apply Eventually.of_forall
        intro t (ht : - Real.log x ≤ t)
        rw [norm_mul]
        have hdom_nonneg : 0 ≤ max |x| 1 := by
          exact (abs_nonneg x).trans (le_max_left _ _)
        refine mul_le_mul ?_ (hC _) (norm_nonneg _) hdom_nonneg
        simp only [neg_mul, ofReal_exp, ofReal_neg, ofReal_mul, ofReal_sub, ofReal_one, norm_exp,
          neg_re, mul_re, ofReal_re, sub_re, one_re, ofReal_im, sub_im, one_im, sub_self, mul_zero,
          sub_zero]
        have : -Real.log x * (σ' - 1) ≤ t * (σ' - 1) := mul_le_mul_of_nonneg_right ht (by linarith)
        have : -(t * (σ' - 1)) ≤ Real.log x * (σ' - 1) := by simpa using neg_le_neg this
        have := Real.exp_monotone this
        apply this.trans
        have l1 : σ' - 1 ≤ 1 := by linarith
        have : 0 ≤ Real.log x := Real.log_nonneg hx
        have := mul_le_mul_of_nonneg_left l1 this
        refine (Real.exp_monotone this).trans ?_
        have hxabs : |x| = x := abs_of_nonneg (zero_le_one.trans hx)
        calc
          Real.exp (Real.log x * 1) = |x| := by
            simpa [mul_one, hxabs] using (Real.exp_log (zero_lt_one.trans_le hx))
          _ ≤ max |x| 1 := le_max_left _ _
    · apply Eventually.of_forall
      intro x
      suffices h : Tendsto (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) (𝓝[>] 1) (𝓝 1) by
        simpa using h.mul_const _
      apply Tendsto.mono_left ?_ nhdsWithin_le_nhds
      suffices h : Continuous (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) by simpa using h.tendsto 1
      continuity

theorem limiting_fourier_lim3 (hG : ContinuousOn G {s | 1 ≤ s.re}) (ψ : CS 2 ℂ) (hx : 1 ≤ x) :
    Tendsto (fun σ' : ℝ ↦ ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I)) (𝓝[>] 1)
      (𝓝 (∫ t : ℝ, G (1 + t * I) * ψ t * x ^ (t * I))) := by

  by_cases hh : tsupport ψ = ∅
  · simp [tsupport_eq_empty_iff.mp hh]
  obtain ⟨a₀, ha₀⟩ := Set.nonempty_iff_ne_empty.mpr hh

  let S : Set ℂ := reProdIm (Icc 1 2) (tsupport ψ)
  have l1 : IsCompact S := by
    refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
    · exact isClosed_Icc.reProdIm (isClosed_tsupport ψ)
    · exact (Metric.isBounded_Icc 1 2).reProdIm ψ.h2.isBounded
  have l2 : S ⊆ {s : ℂ | 1 ≤ s.re} := fun z hz => (mem_reProdIm.mp hz).1.1
  have l3 : ContinuousOn (‖G ·‖) S := (hG.mono l2).norm
  have l4 : S.Nonempty := ⟨1 + a₀ * I, by simp [S, mem_reProdIm, ha₀]⟩
  obtain ⟨z, -, hmax⟩ := l1.exists_isMaxOn l4 l3
  let MG := ‖G z‖
  let bound (a : ℝ) : ℝ := MG * ‖ψ a‖

  apply tendsto_integral_filter_of_dominated_convergence (bound := bound)
  · apply eventually_of_mem (U := Icc 1 2) (Icc_mem_nhdsGT_of_mem (by simp)) ; intro u hu
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · exact (hG.comp_continuous (by fun_prop) (by simp [hu.1])).mul ψ.h1.continuous
    · apply Continuous.const_cpow (by fun_prop) ; simp ; linarith
  · apply eventually_of_mem (U := Icc 1 2) (Icc_mem_nhdsGT_of_mem (by simp))
    intro u hu
    apply Eventually.of_forall ; intro v
    by_cases h : v ∈ tsupport ψ
    · have r1 : u + v * I ∈ S := by simp [S, mem_reProdIm, hu.1, hu.2, h]
      have r2 := isMaxOn_iff.mp hmax _ r1
      have r4 : (x : ℂ) ≠ 0 := by simp ; linarith
      have r5 : arg x = 0 := by simp [arg_eq_zero_iff] ; linarith
      have r3 : ‖(x : ℂ) ^ (v * I)‖ = 1 := by simp [norm_cpow_of_ne_zero r4, r5]
      simp_rw [norm_mul, r3, mul_one]
      exact mul_le_mul_of_nonneg_right r2 (norm_nonneg _)
    · have : v ∉ Function.support ψ := fun a ↦ h (subset_tsupport ψ a)
      simp at this ; simp [this, bound]

  · suffices h : Continuous bound by exact h.integrable_of_hasCompactSupport ψ.h2.norm.mul_left
    have := ψ.h1.continuous ; fun_prop
  · apply Eventually.of_forall ; intro t
    apply Tendsto.mul_const
    apply Tendsto.mul_const
    refine (hG (1 + t * I) (by simp)).tendsto.comp <| tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact ((continuous_ofReal.tendsto _).add tendsto_const_nhds).mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall (fun x (hx : 1 < x) => by simp [hx.le])

lemma limiting_fourier (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (ψ : CS 2 ℂ) (hx : 1 ≤ x) :
    ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)) =
      ∫ (t : ℝ), (G (1 + t * I)) * (ψ t) * x ^ (t * I) := by

  have l1 := limiting_fourier_lim1 hcheby ψ (by linarith)
  have l2 := limiting_fourier_lim2 A ψ hx
  have l3 := limiting_fourier_lim3 hG ψ hx
  apply tendsto_nhds_unique_of_eventuallyEq (l1.sub l2) l3
  simpa [eventuallyEq_nhdsWithin_iff] using! Eventually.of_forall (limiting_fourier_aux hG' hf ψ hx)




lemma limiting_cor_aux {f : ℝ → ℂ} : Tendsto (fun x : ℝ ↦ ∫ t, f t * x ^ (t * I)) atTop (𝓝 0) := by

  have l1 : ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, x ^ (t * I) = exp (log x * t * I) := by
    filter_upwards [eventually_ne_atTop 0, eventually_ge_atTop 0] with x hx hx' t
    rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx), ofReal_log hx'] ; ring_nf

  have l2 : ∀ᶠ x : ℝ in atTop, ∫ t, f t * x ^ (t * I) = ∫ t, f t * exp (log x * t * I) := by
    filter_upwards [l1] with x hx
    refine integral_congr_ae (Eventually.of_forall (fun x => by simp [hx]))

  simp_rw [tendsto_congr' l2]
  convert_to Tendsto (fun x => 𝓕 f (-Real.log x / (2 * π))) atTop (𝓝 0)
  · ext x
    rw [Real.fourier_real_eq_integral_exp_smul]
    congr 1; ext t
    rw [smul_eq_mul, mul_comm (f t)]
    congr 2
    push_cast
    field_simp
  refine (Real.zero_at_infty_fourier f).comp <| Tendsto.mono_right ?_ _root_.atBot_le_cocompact
  exact (tendsto_neg_atBot_iff.mpr tendsto_log_atTop).atBot_mul_const (inv_pos.mpr two_pi_pos)

lemma limiting_cor (ψ : CS 2 ℂ) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) := by

  apply limiting_cor_aux.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx using
    limiting_fourier hcheby hG hG' hf ψ hx |>.symm





lemma smooth_urysohn (a b c d : ℝ) (h1 : a < b) (h3 : c < d) : ∃ Ψ : ℝ → ℝ,
    (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
      Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 := by

  obtain ⟨ψ, l1, l2, l3, l4, -⟩ := smooth_urysohn_support_Ioo h1 h3
  refine ⟨ψ, l1, l2, l3, l4⟩



noncomputable def exists_trunc : trunc := by
  choose ψ h1 h2 h3 h4 using smooth_urysohn (-2) (-1) (1) (2) (by linarith) (by linarith)
  exact ⟨⟨ψ, h1.of_le (by norm_cast), h2⟩, h3, h4⟩

noncomputable def pp (a x : ℝ) : ℝ := a ^ 2 * (x + 1) ^ 2 + (1 - a) * (1 + a)

lemma pp_pos {a : ℝ} (ha : a ∈ Ioo (-1) 1) (x : ℝ) : 0 < pp a x := by
  simp only [pp]
  have : 0 < 1 - a := by linarith [ha.2]
  have : 0 < 1 + a := by linarith [ha.1]
  positivity

noncomputable def hh (a t : ℝ) : ℝ := (t * (1 + (a * log t) ^ 2))⁻¹

noncomputable def hh' (a t : ℝ) : ℝ := - pp a (log t) * hh a t ^ 2

lemma hh_nonneg (a : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ hh a t := by dsimp only [hh] ; positivity

lemma hh_deriv (a : ℝ) {t : ℝ} (ht : t ≠ 0) : HasDerivAt (hh a) (hh' a t) t := by
  have e1 : t * (1 + (a * log t) ^ 2) ≠ 0 := mul_ne_zero ht (_root_.ne_of_lt (by positivity)).symm
  have l5 : HasDerivAt (fun t : ℝ => log t) t⁻¹ t := Real.hasDerivAt_log ht
  have l4 : HasDerivAt (fun t : ℝ => a * log t) (a * t⁻¹) t := l5.const_mul _
  have l3 : HasDerivAt (fun t : ℝ => (a * log t) ^ 2) (2 * a ^ 2 * t⁻¹ * log t) t := by
    convert! l4.pow 2 using 1 ; ring
  have l2 : HasDerivAt (fun t : ℝ => 1 + (a * log t) ^ 2) (2 * a ^ 2 * t⁻¹ * log t) t :=
    l3.const_add _
  have l1 : HasDerivAt (fun t : ℝ => t * (1 + (a * log t) ^ 2))
      (1 + 2 * a ^ 2 * log t + a ^ 2 * log t ^ 2) t := by
    convert! (hasDerivAt_id' t).mul l2 using 1; field_simp; ring
  convert! l1.inv e1 using 1; simp only [hh', pp, hh]; field_simp; ring

lemma hh_continuous (a : ℝ) : ContinuousOn (hh a) (Ioi 0) :=
  fun t (ht : 0 < t) => (hh_deriv a ht.ne.symm).continuousAt.continuousWithinAt

lemma hh'_nonpos {a x : ℝ} (ha : a ∈ Ioo (-1) 1) : hh' a x ≤ 0 := by
  have := pp_pos ha (log x)
  simp only [hh', neg_mul, Left.neg_nonpos_iff, ge_iff_le]
  positivity

lemma hh_antitone {a : ℝ} (ha : a ∈ Ioo (-1) 1) : AntitoneOn (hh a) (Ioi 0) := by
  have l1 x (hx : x ∈ interior (Ioi 0)) :
      HasDerivWithinAt (hh a) (hh' a x) (interior (Ioi 0)) x := by
    have : x ≠ 0 := by contrapose! hx ; simp [hx]
    exact (hh_deriv a this).hasDerivWithinAt
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi _) (hh_continuous _) l1
    (fun x _ => hh'_nonpos ha)

noncomputable def gg (x i : ℝ) : ℝ := 1 / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹

lemma gg_of_hh {x : ℝ} (hx : x ≠ 0) (i : ℝ) : gg x i = x⁻¹ * hh (1 / (2 * π)) (i / x) := by
  simp only [gg, hh]
  field_simp

lemma gg_le_one (i : ℕ) : gg x i ≤ 1 := by
  by_cases hi : i = 0 <;> simp only [gg, hi, CharP.cast_eq_zero, div_zero, one_div, mul_inv_rev,
    zero_div, Real.log_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero, inv_one, mul_one, zero_le_one]
  have l1 : 1 ≤ (i : ℝ) := by simp ; omega
  have l2 : 1 ≤ 1 + (π⁻¹ * 2⁻¹ * Real.log (↑i / x)) ^ 2 := by
    simp only [le_add_iff_nonneg_right] ; positivity
  rw [← mul_inv] ; apply inv_le_one_of_one_le₀ ; simpa using mul_le_mul l1 l2 zero_le_one (by simp)

lemma one_div_two_pi_mem_Ioo : 1 / (2 * π) ∈ Ioo (-1) 1 := by
  constructor
  · trans 0
    · linarith
    · positivity
  · rw [div_lt_iff₀ (by positivity)]
    convert_to! 1 * 1 < 2 * π
    · simp
    · simp
    apply mul_lt_mul one_lt_two ?_ zero_lt_one zero_le_two
    trans 2
    · exact one_le_two
    · exact two_le_pi

lemma cancel_aux {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i * g i ≤ g (n - 1) * (C * n) + (C * (↑(n - 1 - 1) + 1) * g 0
      - C * (↑(n - 1 - 1) + 1) * g (n - 1) -
    ((n - 1 - 1) • (C * g 0) - ∑ x ∈ Finset.range (n - 1 - 1), C * g (x + 1))) := by

  have l1 (n : ℕ) :
      (g n - g (n + 1)) * ∑ i ∈ Finset.range (n + 1), f i ≤ (g n - g (n + 1)) * (C * (n + 1)) := by
    apply mul_le_mul le_rfl (by simpa using! hf' (n + 1)) (Finset.sum_nonneg' hf) ?_
    simp only [sub_nonneg] ; apply hg' ; simp
  have l2 (x : ℕ) : C * (↑(x + 1) + 1) - C * (↑x + 1) = C := by simp ; ring
  have l3 (n : ℕ) : 0 ≤ cumsum f n := Finset.sum_nonneg' hf

  convert_to ∑ i ∈ Finset.range n, (g i) • (f i) ≤ _
  · simp [mul_comm]
  rw [Finset.sum_range_by_parts, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  simp_rw [← neg_smul, neg_sub, smul_eq_mul]
  apply _root_.add_le_add
  · exact mul_le_mul le_rfl (hf' n) (l3 n) (hg _)
  · apply Finset.sum_le_sum (fun n _ => l1 n) |>.trans
    convert_to! ∑ i ∈ Finset.range (n - 1), (C * (↑i + 1)) • (g i - g (i + 1)) ≤ _
    · congr ; ext i ; simp ; ring
    rw [Finset.sum_range_by_parts]
    simp_rw [Finset.sum_range_sub', l2, smul_sub, smul_eq_mul, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range]
    apply le_of_eq ; ring_nf

lemma sum_range_succ (a : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, a (i + 1) = (∑ i ∈ Finset.range (n + 1), a i) - a 0 := by
  have := Finset.sum_range_sub a n
  rw [Finset.sum_sub_distrib, sub_eq_iff_eq_add] at this
  rw [Finset.sum_range_succ, this] ; ring

lemma cancel_aux' {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i * g i ≤
        C * n * g (n - 1)
      + C * cumsum g (n - 1 - 1 + 1)
      - C * (↑(n - 1 - 1) + 1) * g (n - 1)
      := by
  have := cancel_aux hf hg hf' hg' n
  simp only [nsmul_eq_mul, ← Finset.mul_sum, sum_range_succ] at this
  convert this using 1 ; unfold cumsum ; ring

lemma cancel_main' {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hf0 : f 0 = 0) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    cumsum (f * g) n ≤ C * cumsum g n := by
  match n with
  | 0 => simp [cumsum]
  | 1 => specialize hg 0 ; specialize hf' 1 ; simp only [cumsum, Finset.range_one,
    Finset.sum_singleton, hf0, Nat.cast_one, mul_one, Pi.zero_apply, Pi.mul_apply, zero_mul,
    ge_iff_le] at hf' hg ⊢ ; positivity
  | n + 2 => convert! cancel_aux' hf hg hf' hg' (n + 2) using 1 ; simp [cumsum_succ] ; ring

theorem sum_le_integral {x₀ : ℝ} {f : ℝ → ℝ} {n : ℕ} (hf : AntitoneOn f (Ioc x₀ (x₀ + n)))
    (hfi : IntegrableOn f (Icc x₀ (x₀ + n))) :
    (∑ i ∈ Finset.range n, f (x₀ + ↑(i + 1))) ≤ ∫ x in x₀..x₀ + n, f x := by

  cases n with simp only [Nat.cast_add, Nat.cast_one, CharP.cast_eq_zero, add_zero,
      lt_self_iff_false, not_false_eq_true,
    Ioc_eq_empty, Finset.range_zero, Nat.cast_add, Nat.cast_one, Finset.sum_empty,
    intervalIntegral.integral_same, le_refl] at hf ⊢
  | succ n =>
  have : Finset.range (n + 1) = {0} ∪ Finset.Ico 1 (n + 1) := by
    ext i ; by_cases hi : i = 0 <;> simp [hi] ; omega
  simp only [this, Finset.singleton_union, Finset.mem_Ico, nonpos_iff_eq_zero, one_ne_zero,
    lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, and_true, not_false_eq_true,
    Finset.sum_insert, CharP.cast_eq_zero, zero_add, ge_iff_le]

  have l4 : IntervalIntegrable f volume x₀ (x₀ + 1) := by
    apply IntegrableOn.intervalIntegrable
    simp only [le_add_iff_nonneg_right, zero_le_one, uIcc_of_le]
    apply hfi.mono_set
    apply Icc_subset_Icc le_rfl
    simp
  have l5 x (hx : x ∈ Ioc x₀ (x₀ + 1)) : (fun x ↦ f (x₀ + 1)) x ≤ f x := by
    rcases hx with ⟨hx1, hx2⟩
    refine hf ⟨hx1, by linarith⟩ ⟨by linarith, by linarith⟩ hx2
  have l6 : ∫ x in x₀..x₀ + 1, f (x₀ + 1) = f (x₀ + 1) := by simp

  have l1 : f (x₀ + 1) ≤ ∫ x in x₀..x₀ + 1, f x := by
    rw [← l6] ; apply intervalIntegral.integral_mono_ae_restrict (by linarith) (by simp) l4
    apply eventually_of_mem _ l5
    have : (Ioc x₀ (x₀ + 1))ᶜ ∩ Icc x₀ (x₀ + 1) = {x₀} := by simp [← sdiff_eq_compl_inter]
    rw [mem_ae_iff, Measure.restrict_apply measurableSet_Ioc.compl, this]
    simp

  have l2 : AntitoneOn (fun x ↦ f (x₀ + x)) (Icc 1 ↑(n + 1)) := by
    intro u ⟨hu1, _⟩ v ⟨_, hv2⟩ huv ; push_cast at hv2
    refine hf ⟨?_, ?_⟩ ⟨?_, ?_⟩ ?_ <;> linarith

  have l3 := @AntitoneOn.sum_le_integral_Ico 1 (n + 1) (fun x => f (x₀ + x)) (by simp)
    (by simpa using l2)

  simp only [Nat.cast_add, Nat.cast_one, intervalIntegral.integral_comp_add_left] at l3
  convert! _root_.add_le_add l1 l3

  have := @intervalIntegral.integral_comp_mul_add ℝ _ _ 1 (n + 1) 1 f one_ne_zero x₀
  rw [intervalIntegral.integral_add_adjacent_intervals]
  · exact l4
  · apply IntegrableOn.intervalIntegrable
    simp only [add_le_add_iff_left, le_add_iff_nonneg_left, Nat.cast_nonneg, uIcc_of_le]
    apply hfi.mono_set
    apply Icc_subset_Icc
    · linarith
    · simp

lemma hh_integrable_aux (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (IntegrableOn (fun t ↦ a * hh b (t / c)) (Ici 0)) ∧
    (∫ (t : ℝ) in Ioi 0, a * hh b (t / c) = a * c / b * π) := by

  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  simp only [hh]

  let g (x : ℝ) := (a * c / b) * Real.arctan (b * log (x / c))
  let g₀ (x : ℝ) := if x = 0 then ((a * c / b) * (- (π / 2))) else g x
  let g' (x : ℝ) := a * (x / c * (1 + (b * Real.log (x / c)) ^ 2))⁻¹

  have l3 (x) (hx : 0 < x) : HasDerivAt Real.log x⁻¹ x := by apply Real.hasDerivAt_log (by linarith)
  have l4 (x) : HasDerivAt (fun t => t / c) (1 / c) x := (hasDerivAt_id x).div_const c
  have l2 (x) (hx : 0 < x) : HasDerivAt (fun t => log (t / c)) x⁻¹ x := by
    have := @HasDerivAt.comp _ _ _ _ _ _ (fun t => t / c) _ _ _  (l3 (x / c) (by positivity)) (l4 x)
    convert! this using 1 ; field_simp
  have l5 (x) (hx : 0 < x) := (l2 x hx).const_mul b
  have l1 (x) (hx : 0 < x) := (l5 x hx).arctan
  have l6 (x) (hx : 0 < x) : HasDerivAt g (g' x) x := by
    convert! (l1 x hx).const_mul (a * c / b) using 1
    simp only [g']
    field_simp
  have key (x) (hx : 0 < x) : HasDerivAt g₀ (g' x) x := by
    apply (l6 x hx).congr_of_eventuallyEq
    apply eventually_of_mem <| Ioi_mem_nhds hx
    intro y (hy : 0 < y)
    simp [g₀, hy.ne.symm]

  have k1 : Tendsto g₀ atTop (𝓝 ((a * c / b) * (π / 2))) := by
    have : g =ᶠ[atTop] g₀ := by
      apply eventually_of_mem (Ioi_mem_atTop 0)
      intro y (hy : 0 < y)
      simp [g₀, hy.ne.symm]
    apply Tendsto.congr' this
    apply Tendsto.const_mul
    apply (tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
    apply Tendsto.const_mul_atTop hb
    apply tendsto_log_atTop.comp
    apply Tendsto.atTop_div_const hc
    apply tendsto_id

  have k2 : Tendsto g₀ (𝓝[>] 0) (𝓝 (g₀ 0)) := by
    have : g =ᶠ[𝓝[>] 0] g₀ := by
      apply eventually_of_mem self_mem_nhdsWithin
      intro x (hx : 0 < x) ; simp [g₀, hx.ne.symm]
    simp only [g₀]
    apply Tendsto.congr' this
    apply Tendsto.const_mul
    apply (tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp
    apply Tendsto.const_mul_atBot hb
    apply tendsto_log_nhdsGT_zero.comp
    rw [Metric.tendsto_nhdsWithin_nhdsWithin]
    intro ε hε
    refine ⟨c * ε, by positivity, fun x hx1 hx2 => ⟨?_, ?_⟩⟩
    · simp only [mem_Ioi] at hx1 ⊢ ; positivity
    · simp only [dist_zero_right, norm_eq_abs, norm_div, abs_eq_self.mpr hc.le] at hx2 ⊢
      rwa [div_lt_iff₀ hc, mul_comm]

  have k3 : ContinuousWithinAt g₀ (Ici 0) 0 := by
    rw [Metric.continuousWithinAt_iff]
    rw [Metric.tendsto_nhdsWithin_nhds] at k2
    peel k2 with ε hε δ hδ x h
    intro (hx : 0 ≤ x)
    have := le_iff_lt_or_eq.mp hx
    cases this with
    | inl hx => exact h hx
    | inr hx => simp [g₀, hx.symm, hε]

  have k4 : ∀ x ∈ Ioi 0, 0 ≤ g' x := by
    intro x (hx : 0 < x) ; simp only [mul_inv_rev, inv_div, g'] ; positivity

  constructor
  · convert_to IntegrableOn g' _
    exact integrableOn_Ioi_deriv_of_nonneg k3 key k4 k1
  · have := integral_Ioi_of_hasDerivAt_of_nonneg k3 key k4 k1
    simp only [mul_inv_rev, inv_div, mul_neg, ↓reduceIte, sub_neg_eq_add, g', g₀] at this ⊢
    convert this using 1 ; field_simp ; ring

lemma hh_integrable (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    IntegrableOn (fun t ↦ a * hh b (t / c)) (Ici 0) :=
  hh_integrable_aux ha hb hc |>.1

lemma hh_integral (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∫ (t : ℝ) in Ioi 0, a * hh b (t / c) = a * c / b * π :=
  hh_integrable_aux ha hb hc |>.2

lemma hh_integral' : ∫ t in Ioi 0, hh (1 / (2 * π)) t = 2 * π ^ 2 := by
  have := hh_integral (a := 1) (b := 1 / (2 * π)) (c := 1)
    (by positivity) (by positivity) (by positivity)
  convert this using 1 <;> simp ; ring

lemma bound_sum_log {C : ℝ} (hf0 : f 0 = 0) (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤
      C * (1 + ∫ t in Ioi 0, hh (1 / (2 * π)) t) := by

  let ggg (i : ℕ) : ℝ := if i = 0 then 1 else gg x i

  have l0 : x ≠ 0 := by linarith
  have l1 i : 0 ≤ ggg i := by by_cases hi : i = 0 <;> simp only [gg, one_div, mul_inv_rev, hi,
    ↓reduceIte, zero_le_one, ggg] ; positivity
  have l2 : Antitone ggg := by
    intro i j hij ; by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp only [hj, ↓reduceIte, hi,
      le_refl, ggg]
    · exact gg_le_one _
    · omega
    · simp only [gg_of_hh l0]
      gcongr
      apply hh_antitone one_div_two_pi_mem_Ioo
      · simp only [mem_Ioi] ; positivity
      · simp only [mem_Ioi] ; positivity
      · gcongr
  have l3 : 0 ≤ C := by simpa [cumsum, hf0] using hf 1

  have l4 : 0 ≤ ∫ (t : ℝ) in Ioi 0, hh (π⁻¹ * 2⁻¹) t :=
    setIntegral_nonneg measurableSet_Ioi (fun x hx => hh_nonneg _ (LT.lt.le hx))

  have l5 {n : ℕ} : AntitoneOn (fun t ↦ x⁻¹ * hh (1 / (2 * π)) (t / x)) (Ioc 0 n) := by
    intro u ⟨hu1, _⟩ v ⟨hv1, _⟩ huv
    simp only
    apply mul_le_mul le_rfl ?_ (hh_nonneg _ (by positivity)) (by positivity)
    apply hh_antitone one_div_two_pi_mem_Ioo (by simp only [mem_Ioi] ; positivity)
      (by simp only [mem_Ioi] ; positivity)
    apply (div_le_div_iff_of_pos_right (by positivity)).mpr huv

  have l6 {n : ℕ} : IntegrableOn (fun t ↦ x⁻¹ * hh (π⁻¹ * 2⁻¹) (t / x)) (Icc 0 n) volume := by
    apply IntegrableOn.mono_set
      (hh_integrable (by positivity) (by positivity) (by positivity)) Icc_subset_Ici_self

  apply Real.tsum_le_of_sum_range_le (fun n => by positivity) ; intro n
  convert_to! ∑ i ∈ Finset.range n, ‖f i‖ * ggg i ≤ _
  · congr ; ext i
    by_cases hi : i = 0
    · simp [hi, hf0]
    · simp only [gg, hi, ↓reduceIte, ggg]
      field_simp

  apply cancel_main' (fun _ => norm_nonneg _) (by simp [hf0]) l1 hf l2 n |>.trans
  gcongr ; simp only [cumsum, gg_of_hh l0, one_div, mul_inv_rev, ggg]

  by_cases hn : n = 0
  · simp only [hn, Finset.range_zero, Finset.sum_empty] ; positivity
  replace hn : 0 < n := by omega
  have : Finset.range n = {0} ∪ Finset.Ico 1 n := by
    ext i ; simp ; by_cases hi : i = 0 <;> simp [hi, hn] ; omega
  simp only [this, Finset.singleton_union, Finset.mem_Ico, nonpos_iff_eq_zero, one_ne_zero,
    false_and, not_false_eq_true, Finset.sum_insert, ↓reduceIte, add_le_add_iff_left, ge_iff_le]
  convert_to! ∑ x_1 ∈ Finset.Ico 1 n, x⁻¹ * hh (π⁻¹ * 2⁻¹) (↑x_1 / x) ≤ _
  · apply Finset.sum_congr rfl (fun i hi => ?_)
    simp at hi
    have : i ≠ 0 := by omega
    simp [this]
  simp_rw [Finset.sum_Ico_eq_sum_range, add_comm 1]
  have := @sum_le_integral 0 (fun t => x⁻¹ * hh (π⁻¹ * 2⁻¹) (t / x)) (n - 1)
    (by simpa using l5) (by simpa using l6)
  simp only [zero_add] at this
  apply this.trans
  rw [@intervalIntegral.integral_comp_div ℝ _ _ 0 ↑(n - 1) x (fun t => x⁻¹ * hh (π⁻¹ * 2⁻¹) (t)) l0]
  simp only [zero_div, intervalIntegral.integral_const_mul, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ l0, one_mul]
  have : (0 : ℝ) ≤ ↑(n - 1) / x := by positivity
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  simp only [this, ↓reduceIte, uIoc_of_le, smul_eq_mul, one_mul, ge_iff_le]
  apply integral_mono_measure
  · apply Measure.restrict_mono Ioc_subset_Ioi_self le_rfl
  · apply eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi)
    intro x (hx : 0 < x)
    apply hh_nonneg _ hx.le
  · have := (@hh_integrable 1 (1 / (2 * π)) 1 (by positivity) (by positivity) (by positivity))
    simpa using! this.mono_set Ioi_subset_Ici_self

lemma bound_sum_log0 {C : ℝ} (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤
      C * (1 + ∫ t in Ioi 0, hh (1 / (2 * π)) t) := by

  let f0 i := if i = 0 then 0 else f i
  have l1 : chebyWith C f0 := by
    intro n ; refine Finset.sum_le_sum (fun i _ => ?_) |>.trans (hf n)
    by_cases hi : i = 0 <;> simp [hi, f0]
  have l2 i : ‖f i‖ / i = ‖f0 i‖ / i := by by_cases hi : i = 0 <;> simp [hi, f0]
  simp_rw [l2] ; apply bound_sum_log rfl l1 hx

lemma bound_sum_log' {C : ℝ} (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤ C * (1 + 2 * π ^ 2) := by
  simpa only [hh_integral'] using bound_sum_log0 hf hx

variable (f x) in
lemma summable_fourier_aux (ψ : W21) (i : ℕ) :
    ‖f i / i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (i / x))‖ ≤
      W21.norm ψ * (‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹) := by
  convert! mul_le_mul_of_nonneg_left (decay_bounds_key ψ (1 / (2 * π) * log (i / x)))
    (norm_nonneg (f i / i)) using 1
  · simp
  · change _ = _ * (W21.norm ψ * _)
    simp only [W21.norm, mul_inv_rev, one_div, Complex.norm_div, RCLike.norm_natCast]
    ring

lemma summable_fourier (x : ℝ) (hx : 0 < x) (ψ : W21) (hcheby : cheby f) :
    Summable fun i ↦ ‖f i / ↑i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑i / x))‖ := by
  have l5 : Summable fun i ↦ ‖f i‖ / ↑i * ((1 + (1 / (2 * ↑π) * ↑(Real.log (↑i / x))) ^ 2)⁻¹) := by
    simpa using limiting_fourier_lim1_aux hcheby hx 1 (zero_le_one' ℝ)
  have l6 := summable_fourier_aux x f ψ
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) l6
    (by simpa using l5.const_smul (W21.norm ψ))

lemma bound_I1 (x : ℝ) (hx : 0 < x) (ψ : W21) (hcheby : cheby f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))‖ ≤
    W21.norm ψ • ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ := by

  have l5 : Summable fun i ↦ ‖f i‖ / ↑i * ((1 + (1 / (2 * ↑π) * ↑(Real.log (↑i / x))) ^ 2)⁻¹) := by
    simpa using limiting_fourier_lim1_aux hcheby hx 1 (zero_le_one' ℝ)
  have l6 := summable_fourier_aux x f ψ
  have l1 : Summable fun i ↦ ‖f i / ↑i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑i / x))‖ := by
    exact summable_fourier x hx ψ hcheby
  apply (norm_tsum_le_tsum_norm l1).trans
  simpa only [← Summable.tsum_const_smul _ l5] using!
    Summable.tsum_mono l1 (by simpa using l5.const_smul (W21.norm ψ)) l6

lemma bound_I1' {C : ℝ} (x : ℝ) (hx : 1 ≤ x) (ψ : W21) (hcheby : chebyWith C f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))‖ ≤
      W21.norm ψ * C * (1 + 2 * π ^ 2) := by

  apply bound_I1 x (by linarith) ψ ⟨_, hcheby⟩ |>.trans
  rw [smul_eq_mul, mul_assoc]
  apply mul_le_mul le_rfl (bound_sum_log' hcheby hx) ?_ W21.norm_nonneg
  apply tsum_nonneg (fun i => by positivity)

lemma bound_I2 (x : ℝ) (ψ : W21) :
    ‖∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))‖ ≤ W21.norm ψ * (2 * π ^ 2) := by

  have key a : ‖𝓕 (ψ : ℝ → ℂ) (a / (2 * π))‖ ≤ W21.norm ψ * (1 + (a / (2 * π)) ^ 2)⁻¹ :=
    decay_bounds_key ψ _
  have twopi : 0 ≤ 2 * π := by simp [pi_nonneg]
  have l3 : Integrable (fun a ↦ (1 + (a / (2 * π)) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_div (by norm_num [pi_ne_zero])
  have l2 : IntegrableOn (fun i ↦ W21.norm ψ * (1 + (i / (2 * π)) ^ 2)⁻¹) (Ici (-Real.log x)) := by
    exact (l3.const_mul _).integrableOn
  have l1 : IntegrableOn (fun i ↦ ‖𝓕 (ψ : ℝ → ℂ) (i / (2 * π))‖) (Ici (-Real.log x)) := by
    refine ((l3.const_mul (W21.norm ψ)).mono' ?_ ?_).integrableOn
    · apply Continuous.aestronglyMeasurable ; have := continuous_FourierIntegral ψ ; fun_prop
    · simp only [norm_norm, key] ; simp
  have l5 : 0 ≤ᵐ[volume] fun a ↦ (1 + (a / (2 * π)) ^ 2)⁻¹ := by
    apply Eventually.of_forall ; intro x ; positivity
  refine (norm_integral_le_integral_norm _).trans <| (setIntegral_mono l1 l2 key).trans ?_
  rw [integral_const_mul] ; gcongr
  · apply W21.norm_nonneg
  refine (setIntegral_le_integral l3 l5).trans ?_
  rw [Measure.integral_comp_div (fun x => (1 + x ^ 2)⁻¹) (2 * π)]
  simp [abs_eq_self.mpr twopi] ; ring_nf ; rfl

lemma bound_main {C : ℝ} (A : ℂ) (x : ℝ) (hx : 1 ≤ x) (ψ : W21)
    (hcheby : chebyWith C f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))‖ ≤
      W21.norm ψ * (C * (1 + 2 * π ^ 2) + ‖A‖ * (2 * π ^ 2)) := by

  have l1 := bound_I1' x hx ψ hcheby
  have l2 := mul_le_mul (le_refl ‖A‖) (bound_I2 x ψ) (by positivity) (by positivity)
  apply norm_sub_le _ _ |>.trans ; rw [norm_mul]
  convert _root_.add_le_add l1 l2 using 1 ; ring


lemma limiting_cor_W21 (ψ : W21) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) := by

  -- Shorter notation for clarity
  let S1 x (ψ : ℝ → ℂ) := ∑' (n : ℕ), f n / ↑n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑n / x))
  let S2 x (ψ : ℝ → ℂ) := ↑A * ∫ (u : ℝ) in Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))
  let S x ψ := S1 x ψ - S2 x ψ ; change Tendsto (fun x ↦ S x ψ) atTop (𝓝 0)

  -- Build the truncation
  obtain g := exists_trunc
  let Ψ R := g.scale R * ψ
  have key R : Tendsto (fun x ↦ S x (Ψ R)) atTop (𝓝 0) := limiting_cor (Ψ R) hf hcheby hG hG'

  -- Choose the truncation radius
  obtain ⟨C, hcheby⟩ := hcheby
  have hC : 0 ≤ C := by
    have : ‖f 0‖ ≤ C := by simpa [cumsum] using hcheby 1
    have : 0 ≤ ‖f 0‖ := by positivity
    linarith
  have key2 : Tendsto (fun R ↦ W21.norm (ψ - Ψ R)) atTop (𝓝 0) := W21_approximation ψ g
  simp_rw [Metric.tendsto_nhds] at key key2 ⊢ ; intro ε hε
  let M := C * (1 + 2 * π ^ 2) + ‖(A : ℂ)‖ * (2 * π ^ 2)
  obtain ⟨R, hRψ⟩ := (key2 ((ε / 2) / (1 + M)) (by positivity)).exists
  simp only [dist_zero_right, Real.norm_eq_abs, abs_eq_self.mpr W21.norm_nonneg] at hRψ key

  -- Apply the compact support case
  filter_upwards [eventually_ge_atTop 1, key R (ε / 2) (by positivity)] with x hx key

  -- Control the tail term
  have key3 : ‖S x (ψ - Ψ R)‖ < ε / 2 := by
    have : ‖S x _‖ ≤ _ * M := @bound_main f C A x hx (ψ - Ψ R) hcheby
    apply this.trans_lt
    apply (mul_le_mul (d := 1 + M) le_rfl (by simp) (by positivity) W21.norm_nonneg).trans_lt
    have : 0 < 1 + M := by positivity
    convert! (mul_lt_mul_iff_left₀ this).mpr hRψ using 1 ; field_simp

  -- Conclude the proof
  have S1_sub_1 x : 𝓕 (⇑ψ - ⇑(Ψ R)) x = 𝓕 (ψ : ℝ → ℂ) x - 𝓕 ⇑(Ψ R) x := by
    have l1 : AEStronglyMeasurable (fun x_1 : ℝ ↦ cexp (-(2 * ↑π * (↑x_1 * ↑x) * I))) volume := by
      refine (Continuous.mul ?_ continuous_const).neg.cexp.aestronglyMeasurable
      apply continuous_const.mul <| contDiff_ofReal.continuous.mul continuous_const
    simp only [Real.fourier_eq', neg_mul, RCLike.inner_apply', conj_trivial, ofReal_neg,
      ofReal_mul, ofReal_ofNat, Pi.sub_apply, smul_eq_mul, mul_sub]
    apply integral_sub
    · apply ψ.hf.bdd_mul (c := 1) l1 ; simp [Complex.norm_exp]
    · apply (Ψ R : W21) |>.hf |>.bdd_mul (c := 1) l1
      simp [Complex.norm_exp]

  have S1_sub : S1 x (ψ - Ψ R) = S1 x ψ - S1 x (Ψ R) := by
    simp only [one_div, mul_inv_rev, S1_sub_1, mul_sub, S1] ; apply Summable.tsum_sub
    · have := summable_fourier x (by positivity) ψ ⟨_, hcheby⟩
      rw [summable_norm_iff] at this
      simpa using this
    · have := summable_fourier x (by positivity) (Ψ R) ⟨_, hcheby⟩
      rw [summable_norm_iff] at this
      simpa using! this

  have S2_sub : S2 x (ψ - Ψ R) = S2 x ψ - S2 x (Ψ R) := by
    simp only [S1_sub_1, S2] ; rw [integral_sub]
    · ring
    · exact ψ.integrable_fourier (by positivity) |>.restrict
    · exact (Ψ R : W21).integrable_fourier (by positivity) |>.restrict

  have S_sub : S x (ψ - Ψ R) = S x ψ - S x (Ψ R) := by simp [S, S1_sub, S2_sub] ; ring
  simpa [S_sub, Ψ] using norm_add_le _ _ |>.trans_lt (_root_.add_lt_add key3 key)

lemma limiting_cor_schwartz (ψ : 𝓢(ℝ, ℂ)) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) :=
  limiting_cor_W21 ψ hf hcheby hG hG'





-- just the surjectivity is stated here, as this is all that is needed for the current
-- application, but perhaps one should state and prove bijectivity instead

lemma fourier_surjection_on_schwartz (f : 𝓢(ℝ, ℂ)) : ∃ g : 𝓢(ℝ, ℂ), 𝓕 g = f := by
  refine ⟨𝓕⁻ f, ?_⟩
  exact FourierTransform.fourier_fourierInv_eq f




noncomputable def toSchwartz (f : ℝ → ℂ) (h1 : ContDiff ℝ ∞ f)
    (h2 : HasCompactSupport f) : 𝓢(ℝ, ℂ) where
  toFun := f
  smooth' := h1
  decay' k n := by
    have l1 : Continuous (fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) := by
      have : ContDiff ℝ ∞ (iteratedFDeriv ℝ n f) := h1.iteratedFDeriv_right (mod_cast le_top)
      exact Continuous.mul (by continuity) this.continuous.norm
    have l2 : HasCompactSupport (fun x ↦ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) :=
      (h2.iteratedFDeriv _).norm.mul_left
    simpa using l1.bounded_above_of_compact_support l2

@[simp] lemma toSchwartz_apply (f : ℝ → ℂ) {h1 h2 x} : SchwartzMap.mk f h1 h2 x = f x := rfl

lemma comp_exp_support0 {Ψ : ℝ → ℂ} (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    ∀ᶠ x in 𝓝 0, Ψ x = 0 :=
  notMem_tsupport_iff_eventuallyEq.mp (fun h => lt_irrefl 0 <| mem_Ioi.mp (hplus h))

lemma comp_exp_support1 {Ψ : ℝ → ℂ} (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    ∀ᶠ x in atBot, Ψ (exp x) = 0 :=
  Real.tendsto_exp_atBot <| comp_exp_support0 hplus

lemma comp_exp_support2 {Ψ : ℝ → ℂ} (hsupp : HasCompactSupport Ψ) :
    ∀ᶠ (x : ℝ) in atTop, (Ψ ∘ rexp) x = 0 := by
  simp only [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop] at hsupp
  exact Real.tendsto_exp_atTop hsupp.2

theorem comp_exp_support {Ψ : ℝ → ℂ} (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) : HasCompactSupport (Ψ ∘ rexp) := by
  simp only [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop]
  exact ⟨comp_exp_support1 hplus, comp_exp_support2 hsupp⟩

lemma wiener_ikehara_smooth_aux (l0 : Continuous Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) (x : ℝ) (hx : 0 < x) :
    ∫ (u : ℝ) in Ioi (-Real.log x), ↑(rexp u) * Ψ (rexp u) = ∫ (y : ℝ) in Ioi (1 / x), Ψ y := by

  have l1 : ContinuousOn rexp (Ici (-Real.log x)) := by fun_prop
  have l2 : Tendsto rexp atTop atTop := Real.tendsto_exp_atTop
  have l3 t (_ : t ∈ Ioi (-log x)) : HasDerivWithinAt rexp (rexp t) (Ioi t) t :=
    (Real.hasDerivAt_exp t).hasDerivWithinAt
  have l4 : ContinuousOn Ψ (rexp '' Ioi (-Real.log x)) := by fun_prop
  have l5 : IntegrableOn Ψ (rexp '' Ici (-Real.log x)) volume :=
    (l0.integrable_of_hasCompactSupport hsupp).integrableOn
  have l6 : IntegrableOn (fun x ↦ rexp x • (Ψ ∘ rexp) x) (Ici (-Real.log x)) volume := by
    refine (Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_).integrableOn
    change HasCompactSupport (rexp • (Ψ ∘ rexp))
    exact (comp_exp_support hsupp hplus).smul_left
  have := MeasureTheory.integral_deriv_smul_comp_Ioi l1 l2 l3 l4 l5 l6
  simpa [Real.exp_neg, Real.exp_log hx] using this

theorem wiener_ikehara_smooth_sub (h1 : Integrable Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    Tendsto (fun x ↦ (↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y) - ↑A * ∫ (y : ℝ) in Ioi 0, Ψ y)
      atTop (𝓝 0) := by

  obtain ⟨ε, hε, hh⟩ := Metric.eventually_nhds_iff.mp <| comp_exp_support0 hplus
  apply tendsto_nhds_of_eventually_eq ; filter_upwards [eventually_gt_atTop ε⁻¹] with x hxε

  have l1 : Integrable (indicator (Ioi x⁻¹) (fun x : ℝ => Ψ x)) := h1.indicator measurableSet_Ioi
  have l2 : Integrable (indicator (Ioi 0) (fun x : ℝ => Ψ x)) := h1.indicator measurableSet_Ioi

  simp_rw [← MeasureTheory.integral_indicator measurableSet_Ioi, ← mul_sub, ← integral_sub l1 l2]
  simp only [mul_eq_zero, ofReal_eq_zero]
  right
  apply MeasureTheory.integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro t
  simp only [Pi.zero_apply]

  have hε' : 0 < ε⁻¹ := by positivity
  have hx : 0 < x := by linarith
  have hx' : 0 < x⁻¹ := by positivity
  have hεx : x⁻¹ < ε := (inv_lt_comm₀ hε hx).mp hxε

  have l3 : Ioi 0 = Ioc 0 x⁻¹ ∪ Ioi x⁻¹ := by
    ext t ; simp only [mem_Ioi, mem_union, mem_Ioc] ; constructor <;> intro h
    · simp [h, le_or_gt]
    · cases h with
      | inl h => exact h.1
      | inr h => exact hx'.trans h
  have l4 : Disjoint (Ioc 0 x⁻¹) (Ioi x⁻¹) := by simp
  have l5 := Set.indicator_union_of_disjoint l4 Ψ
  rw [l3, l5]
  simp only
  rw [add_comm, sub_add_cancel_left]
  by_cases ht : t ∈ Ioc 0 x⁻¹
  · simp only [ht, indicator_of_mem, neg_eq_zero]
    apply hh ; simp only [mem_Ioc, dist_zero_right, norm_eq_abs] at ht ⊢
    apply hεx.trans_le'
    rw [abs_le] ; constructor <;> linarith
  simp [ht]



lemma wiener_ikehara_smooth (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x - A * ∫ y in Set.Ioi 0, Ψ y)
      atTop (𝓝 0) := by

  let h (x : ℝ) : ℂ := rexp (2 * π * x) * Ψ (exp (2 * π * x))
  have h1 : ContDiff ℝ ∞ h := by
    have : ContDiff ℝ ∞ (fun x : ℝ => (rexp (2 * π * x))) := (contDiff_const.mul contDiff_id).exp
    exact (contDiff_ofReal.comp this).mul (hsmooth.comp this)
  have h2 : HasCompactSupport h := by
    have : 2 * π ≠ 0 := by simp [pi_ne_zero]
    simpa using! (comp_exp_support hsupp hplus).comp_smul this |>.mul_left
  obtain ⟨g, hg⟩ := fourier_surjection_on_schwartz (toSchwartz h h1 h2)

  have l1 {y} (hy : 0 < y) : y * Ψ y = 𝓕 g (1 / (2 * π) * Real.log y) := by
    simp only [one_div, mul_inv_rev, hg, toSchwartz, ofReal_exp, ofReal_mul, ofReal_ofNat,
      toSchwartz_apply, ofReal_inv, h]
    field_simp
    norm_cast
    rw [Real.exp_log hy]

  have key := limiting_cor_schwartz g hf hcheby hG hG'

  have l2 : ∀ᶠ x in atTop, ∑' (n : ℕ), f n / ↑n * 𝓕 g (1 / (2 * π) * Real.log (↑n / x)) =
      ∑' (n : ℕ), f n * Ψ (↑n / x) / x := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    congr ; ext n
    by_cases hn : n = 0
    · simp [hn, (comp_exp_support0 hplus).self_of_nhds]
    rw [← l1 (by positivity)]
    have : (n : ℂ) ≠ 0 := by simpa using hn
    have : (x : ℂ) ≠ 0 := by simpa using hx.ne.symm
    simp only [ofReal_div, ofReal_natCast]
    field_simp

  have l3 : ∀ᶠ x in atTop, ↑A * ∫ (u : ℝ) in Ici (-Real.log x), 𝓕 g (u / (2 * π)) =
      ↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    congr 1
    simp only [hg, toSchwartz, ofReal_exp, ofReal_mul, ofReal_ofNat, toSchwartz_apply,
      ofReal_div, h]
    norm_cast ; field_simp; norm_cast
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    exact wiener_ikehara_smooth_aux hsmooth.continuous hsupp hplus x hx

  have l4 : Tendsto (fun x => (↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y) - ↑A * ∫ (y : ℝ) in Ioi 0, Ψ y)
      atTop (𝓝 0) := by
    exact wiener_ikehara_smooth_sub (hsmooth.continuous.integrable_of_hasCompactSupport hsupp) hplus

  simpa [tsum_div_const] using (key.congr' <| EventuallyEq.sub l2 l3) |>.add l4



lemma wiener_ikehara_smooth' (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x) atTop (nhds (A * ∫ y in Set.Ioi 0, Ψ y)) :=
  tendsto_sub_nhds_zero_iff.mp <| wiener_ikehara_smooth hf hcheby hG hG' hsmooth hsupp hplus

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

lemma wiener_ikehara_smooth_real {f : ℕ → ℝ} {Ψ : ℝ → ℝ}
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x) atTop (nhds (A * ∫ y in Set.Ioi 0, Ψ y)) := by

  let Ψ' := ofReal ∘ Ψ
  have l1 : ContDiff ℝ ∞ Ψ' := contDiff_ofReal.comp hsmooth
  have l2 : HasCompactSupport Ψ' := hsupp.comp_left rfl
  have l3 : closure (Function.support Ψ') ⊆ Ioi 0 := by rwa [Function.support_comp_eq] ; simp
  have key := (continuous_re.tendsto _).comp
    (@wiener_ikehara_smooth' A Ψ G f hf hcheby hG hG' l1 l2 l3)
  simp at key ; norm_cast at key

lemma interval_approx_inf (ha : 0 < a) (hab : a < b) :
    ∀ᶠ ε in 𝓝[>] 0, ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      closure (Function.support ψ) ⊆ Set.Ioi 0 ∧
        ψ ≤ indicator (Ico a b) 1 ∧ b - a - ε ≤ ∫ y in Ioi 0, ψ y := by

  have l1 : Iio ((b - a) / 3) ∈ 𝓝[>] 0 := nhdsWithin_le_nhds <| Iio_mem_nhds <| by
    rw [← sub_pos] at hab
    positivity
  filter_upwards [self_mem_nhdsWithin, l1] with ε (hε : 0 < ε) (hε' : ε < (b - a) / 3)
  have l2 : a < a + ε / 2 := by simp [hε]
  have l3 : b - ε / 2 < b := by simp [hε]
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := smooth_urysohn_support_Ioo l2 l3
  refine ⟨ψ, h1, h2, ?_, ?_, ?_⟩
  · simp [h5, hab.ne, Icc_subset_Ioi_iff hab.le, ha]
  · exact h4.trans <| indicator_le_indicator_of_subset Ioo_subset_Ico_self (by simp)
  · have l4 : 0 ≤ b - a - ε := by linarith
    have l5 : Icc (a + ε / 2) (b - ε / 2) ⊆ Ioi 0 := by
      intro t ht
      simp only [mem_Icc, mem_Ioi] at ht ⊢
      exact ha.trans <| l2.trans_le <| ht.1
    have l6 : Icc (a + ε / 2) (b - ε / 2) ∩ Ioi 0 = Icc (a + ε / 2) (b - ε / 2) :=
      inter_eq_left.mpr l5
    have l7 : ∫ y in Ioi 0, indicator (Icc (a + ε / 2) (b - ε / 2)) 1 y = b - a - ε := by
      simp only [measurableSet_Icc, integral_indicator_one, measureReal_restrict_apply, l6,
        volume_real_Icc]
      convert max_eq_left l4 using 1 ; ring_nf
    have l8 : IntegrableOn ψ (Ioi 0) volume :=
      (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    rw [← l7] ; apply setIntegral_mono ?_ l8 h3
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Icc]
    apply IntegrableOn.mono ?_ subset_rfl Measure.restrict_le_self
    apply integrableOn_const <;>
    simp

lemma interval_approx_sup (ha : 0 < a) (hab : a < b) :
    ∀ᶠ ε in 𝓝[>] 0, ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      closure (Function.support ψ) ⊆ Set.Ioi 0 ∧
        indicator (Ico a b) 1 ≤ ψ ∧ ∫ y in Ioi 0, ψ y ≤ b - a + ε := by

  have l1 : Iio (a / 2) ∈ 𝓝[>] 0 := nhdsWithin_le_nhds <| Iio_mem_nhds (by linarith)
  filter_upwards [self_mem_nhdsWithin, l1] with ε (hε : 0 < ε) (hε' : ε < a / 2)
  have l2 : a - ε / 2 < a := by linarith
  have l3 : b < b + ε / 2 := by linarith
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := smooth_urysohn_support_Ioo l2 l3
  refine ⟨ψ, h1, h2, ?_, ?_, ?_⟩
  · have l4 : a - ε / 2 < b + ε / 2 := by linarith
    have l5 : ε / 2 < a := by linarith
    simp [h5, l4.ne, Icc_subset_Ioi_iff l4.le, l5]
  · apply le_trans ?_ h3
    apply indicator_le_indicator_of_subset Ico_subset_Icc_self (by simp)
  · have l4 : 0 ≤ b - a + ε := by linarith
    have l5 : Ioo (a - ε / 2) (b + ε / 2) ⊆ Ioi 0 := by intro t ht ; simp at ht ⊢ ; linarith
    have l6 : Ioo (a - ε / 2) (b + ε / 2) ∩ Ioi 0 = Ioo (a - ε / 2) (b + ε / 2) := inter_eq_left.mpr l5
    have l7 : ∫ y in Ioi 0, indicator (Ioo (a - ε / 2) (b + ε / 2)) 1 y = b - a + ε := by
      simp only [measurableSet_Ioo, integral_indicator_one, measureReal_restrict_apply, l6,
        volume_real_Ioo]
      convert max_eq_left l4 using 1 ; ring_nf
    have l8 : IntegrableOn ψ (Ioi 0) volume := (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    rw [← l7]
    refine setIntegral_mono l8 ?_ h4
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioo]
    apply IntegrableOn.mono ?_ subset_rfl Measure.restrict_le_self
    apply integrableOn_const <;>
    simp

lemma WI_summable {f : ℕ → ℝ} {g : ℝ → ℝ} (hg : HasCompactSupport g) (hx : 0 < x) :
    Summable (fun n => f n * g (n / x)) := by
  obtain ⟨M, hM⟩ := hg.bddAbove.mono subset_closure
  apply summable_of_hasFiniteSupport
  unfold Function.HasFiniteSupport
  simp only [Function.support_mul] ; apply Finite.inter_of_right ; rw [finite_iff_bddAbove]
  exact ⟨Nat.ceil (M * x), fun i hi => by simpa using Nat.ceil_mono ((div_le_iff₀ hx).mp (hM hi))⟩

lemma WI_sum_le {f : ℕ → ℝ} {g₁ g₂ : ℝ → ℝ} (hf : 0 ≤ f) (hg : g₁ ≤ g₂) (hx : 0 < x)
    (hg₁ : HasCompactSupport g₁) (hg₂ : HasCompactSupport g₂) :
    (∑' n, f n * g₁ (n / x)) / x ≤ (∑' n, f n * g₂ (n / x)) / x := by
  apply div_le_div_of_nonneg_right ?_ hx.le
  exact Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hg _) (hf _))
    (WI_summable hg₁ hx) (WI_summable hg₂ hx)

lemma WI_sum_Iab_le {f : ℕ → ℝ} (hpos : 0 ≤ f) {C : ℝ} (hcheby : chebyWith C f) (hb : 0 < b) (hxb : 2 / b < x) :
    (∑' n, f n * indicator (Ico a b) 1 (n / x)) / x ≤ C * 2 * b := by
  have hb' : 0 < 2 / b := by positivity
  have hx : 0 < x := by linarith
  have hxb' : 2 < x * b := (div_lt_iff₀ hb).mp hxb
  have l1 (i : ℕ) (hi : i ∉ Finset.range ⌈b * x⌉₊) : f i * indicator (Ico a b) 1 (i / x) = 0 := by
    simp_all [le_div_iff₀ hx]
  have l2 (i : ℕ) (_ : i ∈ Finset.range ⌈b * x⌉₊) : f i * indicator (Ico a b) 1 (i / x) ≤ |f i| := by
    rw [abs_eq_self.mpr (hpos _)]
    convert_to _ ≤ f i * 1
    · ring
    apply mul_le_mul_of_nonneg_left ?_ (hpos _)
    by_cases hi : (i / x) ∈ (Ico a b) <;> simp [hi]
  rw [tsum_eq_sum l1, div_le_iff₀ hx, mul_assoc, mul_assoc]
  apply Finset.sum_le_sum l2 |>.trans
  have := hcheby ⌈b * x⌉₊ ; simp only [norm_real, norm_eq_abs] at this ; apply this.trans
  have : 0 ≤ C := by have := hcheby 1 ; simp only [cumsum, Finset.range_one, norm_real,
    Finset.sum_singleton, Nat.cast_one, mul_one] at this ; exact (abs_nonneg _).trans this
  refine mul_le_mul_of_nonneg_left ?_ this
  apply (Nat.ceil_lt_add_one (by positivity)).le.trans
  linarith

lemma WI_sum_Iab_le' {f : ℕ → ℝ} (hpos : 0 ≤ f) {C : ℝ} (hcheby : chebyWith C f) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, (∑' n, f n * indicator (Ico a b) 1 (n / x)) / x ≤ C * 2 * b := by
  filter_upwards [eventually_gt_atTop (2 / b)] with x hx using WI_sum_Iab_le hpos hcheby hb hx

lemma le_of_eventually_nhdsWithin {a b : ℝ} (h : ∀ᶠ c in 𝓝[>] b, a ≤ c) : a ≤ b := by
  apply le_of_forall_gt ; intro d hd
  have key : ∀ᶠ c in 𝓝[>] b, c < d := by
    apply eventually_of_mem (U := Iio d) ?_ (fun x hx => hx)
    rw [mem_nhdsWithin]
    refine ⟨Iio d, isOpen_Iio, hd, inter_subset_left⟩
  obtain ⟨x, h1, h2⟩ := (h.and key).exists
  linarith

lemma ge_of_eventually_nhdsWithin {a b : ℝ} (h : ∀ᶠ c in 𝓝[<] b, c ≤ a) : b ≤ a := by
  apply le_of_forall_lt ; intro d hd
  have key : ∀ᶠ c in 𝓝[<] b, c > d := by
    apply eventually_of_mem (U := Ioi d) ?_ (fun x hx => hx)
    rw [mem_nhdsWithin]
    refine ⟨Ioi d, isOpen_Ioi, hd, inter_subset_left⟩
  obtain ⟨x, h1, h2⟩ := (h.and key).exists
  linarith

lemma WI_tendsto_aux (a b : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun c => c / A - (b - a)) (𝓝[>] (A * (b - a))) (𝓝[>] 0) := by
  rw [Metric.tendsto_nhdsWithin_nhdsWithin]
  intro ε hε
  refine ⟨A * ε, by positivity, ?_⟩
  intro x hx1 hx2
  constructor
  · simpa [lt_div_iff₀' hA]
  · simp only [Real.dist_eq, dist_zero_right, Real.norm_eq_abs] at hx2 ⊢
    have : |x / A - (b - a)| = |x - A * (b - a)| / A := by
      rw [← abs_eq_self.mpr hA.le, ← abs_div, abs_eq_self.mpr hA.le] ; congr ; field_simp
    rwa [this, div_lt_iff₀' hA]

lemma WI_tendsto_aux' (a b : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun c => (b - a) - c / A) (𝓝[<] (A * (b - a))) (𝓝[>] 0) := by
  rw [Metric.tendsto_nhdsWithin_nhdsWithin]
  intro ε hε
  refine ⟨A * ε, by positivity, ?_⟩
  intro x hx1 hx2
  constructor
  · simpa [div_lt_iff₀' hA]
  · simp only [Real.dist_eq, dist_zero_right, norm_eq_abs] at hx2 ⊢
    have : |(b - a) - x / A| = |A * (b - a) - x| / A := by
      rw [← abs_eq_self.mpr hA.le, ← abs_div, abs_eq_self.mpr hA.le] ; congr ; field_simp
    rwa [this, div_lt_iff₀' hA, ← neg_sub, abs_neg]

theorem residue_nonneg {f : ℕ → ℝ} (hpos : 0 ≤ f)
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm (fun n ↦ ↑(f n)) σ')) (hcheby : cheby fun n ↦ ↑(f n))
    (hG : ContinuousOn G {s | 1 ≤ s.re}) (hG' : EqOn G (fun s ↦ LSeries (fun n ↦ ↑(f n)) s - ↑A / (s - 1)) {s | 1 < s.re}) : 0 ≤ A := by
  let S (g : ℝ → ℝ) (x : ℝ) := (∑' n, f n * g (n / x)) / x
  have hSnonneg {g : ℝ → ℝ} (hg : 0 ≤ g) : ∀ᶠ x : ℝ in atTop, 0 ≤ S g x := by
    filter_upwards [eventually_ge_atTop 0] with x hx
    exact div_nonneg (tsum_nonneg (fun i => mul_nonneg (hpos _) (hg _))) hx
  obtain ⟨ε, ψ, h1, h2, h3, h4, -⟩ := (interval_approx_sup zero_lt_one one_lt_two).exists
  have key := @wiener_ikehara_smooth_real A G f ψ hf hcheby hG hG' h1 h2 h3
  have l2 : 0 ≤ ψ := by apply le_trans _ h4 ; apply indicator_nonneg ; simp
  have l1 : ∀ᶠ x in atTop, 0 ≤ S ψ x := hSnonneg l2
  have l3 : 0 ≤ A * ∫ (y : ℝ) in Ioi 0, ψ y := ge_of_tendsto key l1
  have l4 : 0 < ∫ (y : ℝ) in Ioi 0, ψ y := by
    have r1 : 0 ≤ᵐ[Measure.restrict volume (Ioi 0)] ψ := Eventually.of_forall l2
    have r2 : IntegrableOn (fun y ↦ ψ y) (Ioi 0) volume :=
      (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    have r3 : Ico 1 2 ⊆ Function.support ψ := by intro x hx ; have := h4 x ; simp [hx] at this ⊢ ; linarith
    have r4 : Ico 1 2 ⊆ Function.support ψ ∩ Ioi 0 := by
      simp only [subset_inter_iff, r3, true_and] ; apply Ico_subset_Icc_self.trans ; rw [Icc_subset_Ioi_iff] <;> linarith
    have r5 : 1 ≤ volume ((Function.support fun y ↦ ψ y) ∩ Ioi 0) := by convert! volume.mono r4 ; norm_num
    simpa [setIntegral_pos_iff_support_of_nonneg_ae r1 r2] using! zero_lt_one.trans_le r5
  have := div_nonneg l3 l4.le ; field_simp at this ; exact this



lemma WienerIkeharaInterval {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * (indicator (Ico a b) 1 (n / x))) / x) atTop (nhds (A * (b - a))) := by

  -- Take care of the trivial case `a = b`
  by_cases hab : a = b
  · simp [hab]
  replace hb : a < b := lt_of_le_of_ne hb hab ; clear hab

  -- Notation to make the proof more readable
  let S (g : ℝ → ℝ) (x : ℝ) :=  (∑' n, f n * g (n / x)) / x
  have hSnonneg {g : ℝ → ℝ} (hg : 0 ≤ g) : ∀ᶠ x : ℝ in atTop, 0 ≤ S g x := by
    filter_upwards [eventually_ge_atTop 0] with x hx
    refine div_nonneg ?_ hx
    refine tsum_nonneg (fun i => mul_nonneg (hpos _) (hg _))
  have hA : 0 ≤ A := residue_nonneg hpos hf hcheby hG hG'

  -- A few facts about the indicator function of `Icc a b`
  let Iab : ℝ → ℝ := indicator (Ico a b) 1
  change Tendsto (S Iab) atTop (𝓝 (A * (b - a)))
  have hIab : HasCompactSupport Iab := by simpa [Iab, HasCompactSupport, tsupport, hb.ne] using isCompact_Icc
  have Iab_nonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ S Iab x := hSnonneg (indicator_nonneg (by simp))
  have Iab2 : IsBoundedUnder (· ≤ ·) atTop (S Iab) := by
    obtain ⟨C, hC⟩ := hcheby ; exact ⟨C * 2 * b, WI_sum_Iab_le' hpos hC (by linarith)⟩
  have Iab3 : IsBoundedUnder (· ≥ ·) atTop (S Iab) := ⟨0, Iab_nonneg⟩
  have Iab0 : IsCoboundedUnder (· ≥ ·) atTop (S Iab) := Iab2.isCoboundedUnder_ge
  have Iab1 : IsCoboundedUnder (· ≤ ·) atTop (S Iab) := Iab3.isCoboundedUnder_le

  -- Bound from above by a smooth function
  have sup_le : limsup (S Iab) atTop ≤ A * (b - a) := by
    have l_sup : ∀ᶠ ε in 𝓝[>] 0, limsup (S Iab) atTop ≤ A * (b - a + ε) := by
      filter_upwards [interval_approx_sup ha hb] with ε ⟨ψ, h1, h2, h3, h4, h6⟩
      have l1 : Tendsto (S ψ) atTop _ := wiener_ikehara_smooth_real hf hcheby hG hG' h1 h2 h3
      have l6 : S Iab ≤ᶠ[atTop] S ψ := by
        filter_upwards [eventually_gt_atTop 0] with x hx using WI_sum_le hpos h4 hx hIab h2
      have l5 : IsBoundedUnder (· ≤ ·) atTop (S ψ) := l1.isBoundedUnder_le
      have l3 : limsup (S Iab) atTop ≤ limsup (S ψ) atTop := limsup_le_limsup l6 Iab1 l5
      apply l3.trans ; rw [l1.limsup_eq] ; gcongr
    obtain rfl | h := eq_or_ne A 0
    · simpa using l_sup
    apply le_of_eventually_nhdsWithin
    have key : 0 < A := lt_of_le_of_ne hA h.symm
    filter_upwards [WI_tendsto_aux a b key l_sup] with x hx
    simpa [mul_div_cancel₀ _ h] using hx

  -- Bound from below by a smooth function
  have le_inf : A * (b - a) ≤ liminf (S Iab) atTop := by
    have l_inf : ∀ᶠ ε in 𝓝[>] 0, A * (b - a - ε) ≤ liminf (S Iab) atTop := by
      filter_upwards [interval_approx_inf ha hb] with ε ⟨ψ, h1, h2, h3, h5, h6⟩
      have l1 : Tendsto (S ψ) atTop _ := wiener_ikehara_smooth_real hf hcheby hG hG' h1 h2 h3
      have l2 : S ψ ≤ᶠ[atTop] S Iab := by
        filter_upwards [eventually_gt_atTop 0] with x hx using WI_sum_le hpos h5 hx h2 hIab
      have l4 : IsBoundedUnder (· ≥ ·) atTop (S ψ) := l1.isBoundedUnder_ge
      have l3 : liminf (S ψ) atTop ≤ liminf (S Iab) atTop := liminf_le_liminf l2 l4 Iab0
      apply le_trans ?_ l3 ; rw [l1.liminf_eq] ; gcongr
    obtain rfl | h := eq_or_ne A 0
    · simpa using l_inf
    apply ge_of_eventually_nhdsWithin
    have key : 0 < A := lt_of_le_of_ne hA h.symm
    filter_upwards [WI_tendsto_aux' a b key l_inf] with x hx
    simpa [mul_div_cancel₀ _ h] using hx

  -- Combine the two bounds
  have : liminf (S Iab) atTop ≤ limsup (S Iab) atTop := liminf_le_limsup Iab2 Iab3
  refine tendsto_of_liminf_eq_limsup ?_ ?_ Iab2 Iab3 <;> linarith



lemma lt_ceil_mul_iff (hx : 0 < x) : n < ⌈b * x⌉₊ ↔ n / x < b := by
  rw [div_lt_iff₀ hx, Nat.lt_ceil]

lemma ceil_mul_le_iff (hx : 0 < x) : ⌈a * x⌉₊ ≤ n ↔ a ≤ n / x := by
  rw [le_div_iff₀ hx, Nat.ceil_le]

lemma mem_Ico_iff_div (hx : 0 < x) : n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊ ↔ n / x ∈ Ico a b := by
  rw [Finset.mem_Ico, mem_Ico, ceil_mul_le_iff hx, lt_ceil_mul_iff hx]

lemma tsum_indicator {f : ℕ → ℝ} (hx : 0 < x) :
    ∑' n, f n * (indicator (Ico a b) 1 (n / x)) = ∑ n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n := by
  have l1 : ∀ n ∉ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n * indicator (Ico a b) 1 (↑n / x) = 0 := by
    simp [mem_Ico_iff_div hx] ; tauto
  rw [tsum_eq_sum l1] ; apply Finset.sum_congr rfl ; simp only [mem_Ico_iff_div hx] ; intro n hn ; simp [hn]

lemma WienerIkeharaInterval_discrete {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun x : ℝ ↦ (∑ n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n) / x) atTop (nhds (A * (b - a))) := by
  apply (WienerIkeharaInterval hpos hf hcheby hG hG' ha hb).congr'
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [tsum_indicator hx]

lemma WienerIkeharaInterval_discrete' {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.Ico ⌈a * N⌉₊ ⌈b * N⌉₊, f n) / N) atTop (nhds (A * (b - a))) :=
  WienerIkeharaInterval_discrete hpos hf hcheby hG hG' ha hb |>.comp tendsto_natCast_atTop_atTop

-- TODO with `Ico`



/-- A version of the *Wiener-Ikehara Tauberian Theorem*: If `f` is a nonnegative arithmetic
function whose L-series has a simple pole at `s = 1` with residue `A` and otherwise extends
continuously to the closed half-plane `re s ≥ 1`, then `∑ n < N, f n` is asymptotic to `A*N`. -/

lemma tendsto_mul_ceil_div :
    Tendsto (fun (p : ℝ × ℕ) => ⌈p.1 * p.2⌉₊ / (p.2 : ℝ)) (𝓝[>] 0 ×ˢ atTop) (𝓝 0) := by
  rw [Metric.tendsto_nhds] ; intro δ hδ
  have l1 : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo 0 (δ / 2) := inter_mem_nhdsWithin _ (Iio_mem_nhds (by positivity))
  have l2 : ∀ᶠ N : ℕ in atTop, 1 ≤ δ / 2 * N := by
    apply Tendsto.eventually_ge_atTop
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  filter_upwards [l1.prod_mk l2] with (ε, N) ⟨⟨hε, h1⟩, h2⟩ ; dsimp only at *
  have l3 : 0 < (N : ℝ) := by
    simp only [Nat.cast_pos, Nat.pos_iff_ne_zero] ; rintro rfl ; simp [zero_lt_one.not_ge] at h2
  have l5 : 0 ≤ ε * ↑N := by positivity
  have l6 : ε * N ≤ δ / 2 * N := mul_le_mul h1.le le_rfl (by positivity) (by positivity)
  simp only [dist_zero_right, norm_div, RCLike.norm_natCast, div_lt_iff₀ l3, gt_iff_lt]
  convert (Nat.ceil_lt_add_one l5).trans_le (add_le_add l6 h2) using 1 ; ring

noncomputable def S (f : ℕ → 𝕜) (ε : ℝ) (N : ℕ) : 𝕜 := (∑ n ∈ Finset.Ico ⌈ε * N⌉₊ N, f n) / N

lemma S_sub_S {f : ℕ → 𝕜} {ε : ℝ} {N : ℕ} (hε : ε ≤ 1) : S f 0 N - S f ε N = cumsum f ⌈ε * N⌉₊ / N := by
  have hceilN : ⌈ε * N⌉₊ ≤ N := by
    simp only [Nat.ceil_le]
    exact mul_le_of_le_one_left N.cast_nonneg hε
  have r1 : Finset.range N = Finset.range ⌈ε * N⌉₊ ∪ Finset.Ico ⌈ε * N⌉₊ N := by
    ext n
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have r2 : Disjoint (Finset.range ⌈ε * N⌉₊) (Finset.Ico ⌈ε * N⌉₊ N) := by
    rw [Finset.range_eq_Ico] ; apply Finset.Ico_disjoint_Ico_consecutive
  simp [S, r1, Finset.sum_union r2, cumsum, add_div]

lemma tendsto_S_S_zero {f : ℕ → ℝ} (hpos : 0 ≤ f) (hcheby : cheby f) :
    TendstoUniformlyOnFilter (S f) (S f 0) (𝓝[>] 0) atTop := by
  rw [Metric.tendstoUniformlyOnFilter_iff] ; intro δ hδ
  obtain ⟨C, hC⟩ := hcheby
  have l1 : ∀ᶠ (p : ℝ × ℕ) in 𝓝[>] 0 ×ˢ atTop, C * ⌈p.1 * p.2⌉₊ / p.2 < δ := by
    have r1 := tendsto_mul_ceil_div.const_mul C
    simp only [mul_div_assoc', mul_zero] at r1 ; exact r1 (Iio_mem_nhds hδ)
  have : Ioc 0 1 ∈ 𝓝[>] (0 : ℝ) := inter_mem_nhdsWithin _ (Iic_mem_nhds zero_lt_one)
  filter_upwards [l1, Eventually.prod_inl this _] with (ε, N) h1 h2
  have l2 : ‖cumsum f ⌈ε * ↑N⌉₊ / ↑N‖ ≤ C * ⌈ε * N⌉₊ / N := by
    have r1 := hC ⌈ε * N⌉₊
    have r2 : 0 ≤ cumsum f ⌈ε * N⌉₊ := by apply cumsum_nonneg hpos
    simp only [norm_real, norm_of_nonneg (hpos _), norm_div,
      norm_of_nonneg r2, Real.norm_natCast] at r1 ⊢
    apply div_le_div_of_nonneg_right r1 (by positivity)
  simpa [← S_sub_S h2.2] using! l2.trans_lt h1

theorem WienerIkeharaTheorem' {f : ℕ → ℝ} (hpos : 0 ≤ f)
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun N => cumsum f N / N) atTop (𝓝 A) := by

  convert_to Tendsto (S f 0) atTop (𝓝 A) ; · ext N ; simp [S, cumsum]
  apply (tendsto_S_S_zero hpos hcheby).tendsto_of_eventually_tendsto
  · have L0 : Ioc 0 1 ∈ 𝓝[>] (0 : ℝ) := inter_mem_nhdsWithin _ (Iic_mem_nhds zero_lt_one)
    apply eventually_of_mem L0
    · intro ε hε
      simpa using! WienerIkeharaInterval_discrete' hpos hf hcheby hG hG' hε.1 hε.2
  · have : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    simpa using (this.const_sub 1).const_mul A

theorem vonMangoldt_cheby : cheby Λ := by
  use Real.log 4 + 4
  intro N
  by_cases! h : N = 0
  · simp [h, cumsum]
  simp only [cumsum, norm_real, norm_eq_abs]
  rw [Nat.range_eq_Icc_zero_sub_one _ h, (by simp : N - 1 = ⌊(N : ℝ) - 1⌋₊)]
  simp_rw [abs_of_nonneg vonMangoldt_nonneg]
  rw [← Chebyshev.psi_eq_sum_Icc]
  grw [Chebyshev.psi_le_const_mul_self <| sub_nonneg_of_le <| Nat.one_le_cast_iff_ne_zero.mpr h]
  gcongr
  linarith



-- Proof extracted from the `EulerProducts` project so we can adapt it to the
-- version of the Wiener-Ikehara theorem proved above (with the `cheby`
-- hypothesis)

theorem WeakPNT : Tendsto (fun N ↦ cumsum Λ N / N) atTop (𝓝 1) := by
  let F := vonMangoldt.LFunctionResidueClassAux (q := 1) 1
  have hnv := riemannZeta_ne_zero_of_one_le_re
  have l1 (n : ℕ) : 0 ≤ Λ n := vonMangoldt_nonneg
  have l2 s (hs : 1 < s.re) : F s = LSeries Λ s - 1 / (s - 1) := by
    have := vonMangoldt.eqOn_LFunctionResidueClassAux (q := 1) isUnit_one hs
    simp only [F, this, vonMangoldt.residueClass, Nat.totient_one, Nat.cast_one, inv_one, one_div, sub_left_inj]
    apply LSeries_congr
    intro n _
    simp only [ofReal_inj, indicator_apply_eq_self, mem_ofPred_eq]
    exact fun hn ↦ absurd (Subsingleton.eq_one _) hn
  have l3 : ContinuousOn F {s | 1 ≤ s.re} := vonMangoldt.continuousOn_LFunctionResidueClassAux 1
  have l4 : cheby Λ := vonMangoldt_cheby
  have l5 (σ' : ℝ) (hσ' : 1 < σ') : Summable (nterm Λ σ') := by
    simpa only [← nterm_eq_norm_term] using (@ArithmeticFunction.LSeriesSummable_vonMangoldt σ' hσ').norm
  apply WienerIkeharaTheorem' l1 l5 l4 l3 l2

end PNTX_Wiener

-- Ported from PrimeNumberTheoremAnd: Consequences.lean (selected lemmas up to chebyshev_asymptotic), followed by the new proof of H1
section PNTX_Conseq

section PNTConseq
open ArithmeticFunction hiding log
open Nat hiding log
open Finset
open BigOperators Filter Real Classical Asymptotics MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega Chebyshev

/-- If u ~ v and u-w = o(v) then w ~ v. -/
theorem Asymptotics.IsEquivalent.add_isLittleO'' {α : Type*} {β : Type*} [NormedAddCommGroup β]
    {u : α → β} {v : α → β} {w : α → β} {l : Filter α}
    (huv : Asymptotics.IsEquivalent l u v) (hwu : (u - w) =o[l] v) :
    Asymptotics.IsEquivalent l w v := by
  rw [← sub_sub_self u w]
  exact sub_isLittleO huv hwu

theorem WeakPNT' : Tendsto (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) atTop (nhds 1) := by
  have : (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) =
      (fun N ↦ (∑ n ∈ range N, Λ n)/N + Λ N / N) := by
    ext N
    have : N ∈ Iic N := mem_Iic.mpr (le_refl _)
    rw [← Finset.sum_erase_add _ _ this, ← Nat.Iio_eq_range, Iic_erase]
    exact add_div _ _ _

  rw [this, ← add_zero 1]
  apply Tendsto.add WeakPNT
  convert squeeze_zero (f := fun N ↦ Λ N / N) (g := fun N ↦ log N / N) (t₀ := atTop) ?_ ?_ ?_
  · intro N
    exact div_nonneg vonMangoldt_nonneg (cast_nonneg N)
  · intro N
    exact div_le_div_of_nonneg_right vonMangoldt_le_log (cast_nonneg N)
  have := Real.tendsto_pow_log_div_pow_atTop 1 1 Real.zero_lt_one
  simp only [rpow_one] at this
  exact Tendsto.comp this tendsto_natCast_atTop_atTop

/-- An alternate form of the Weak PNT. -/
theorem WeakPNT'' : ψ ~[atTop] (fun x ↦ x) := by
    rw [(by rfl : ψ = (fun x ↦ ψ x))]
    simp_rw [Chebyshev.psi_eq_sum_Icc]
    apply IsEquivalent.trans (v := fun x ↦ (⌊x⌋₊:ℝ))
    · rw [isEquivalent_iff_tendsto_one]
      · convert! Tendsto.comp WeakPNT' tendsto_nat_floor_atTop
        infer_instance
      rw [eventually_iff]
      simp only [ne_eq, cast_eq_zero, floor_eq_zero, not_lt, mem_atTop_sets,
        Set.mem_ofPred_eq]
      use 1
      simp only [imp_self, implies_true]
    apply IsLittleO.isEquivalent
    rw [← isLittleO_neg_left]
    apply IsLittleO.of_bound
    intro ε hε
    simp only [Pi.sub_apply, neg_sub, norm_eq_abs, eventually_atTop]
    use ε⁻¹
    intro b hb
    have hb' : 0 ≤ b := le_of_lt (lt_of_lt_of_le (inv_pos_of_pos hε) hb)
    rw [abs_of_nonneg, abs_of_nonneg hb']
    · apply LE.le.trans _ ((inv_le_iff_one_le_mul₀' hε).mp hb)
      linarith [Nat.lt_floor_add_one b]
    rw [sub_nonneg]
    exact floor_le hb'

/-- `√x · log x = o(x)` as `x → ∞`. -/
lemma isLittleO_sqrt_mul_log : (fun x : ℝ ↦ x.sqrt * x.log) =o[atTop] _root_.id := by
  have : (fun x : ℝ ↦ x.sqrt * x.log) =o[atTop] fun x ↦ x := by
    refine (isLittleO_mul_iff_isLittleO_div ?_).mpr ?_
    · filter_upwards [eventually_gt_atTop 0] with x hx; exact (sqrt_ne_zero hx.le).mpr hx.ne'
    · convert! isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2) using 2 with x
      rw [div_sqrt, sqrt_eq_rpow]
  exact this

theorem chebyshev_asymptotic : θ ~[atTop] id := by
  refine WeakPNT''.add_isLittleO'' (IsBigO.trans_isLittleO (g := fun x ↦ 2 * x.sqrt * x.log) ?_ ?_)
  · rw [isBigO_iff']; refine ⟨1, one_pos, ?_⟩
    simp only [one_mul, eventually_atTop]
    exact ⟨2, fun x hx ↦ by
      rw [Pi.sub_apply, norm_eq_abs, norm_eq_abs, abs_of_nonneg (by bound : 0 ≤ 2 * √x * log x)]
      exact (abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x))).symm ▸
        Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith : 1 ≤ x)⟩
  · simpa only [mul_assoc] using! isLittleO_sqrt_mul_log.const_mul_left 2

end PNTConseq

end PNTX_Conseq

/- Section 2: Normalized Minimal Covering Systems, Simpson's Product Bound, and CRT/Base-p Box Translation. -/

namespace Erdos1189BBMST

open Finset Real Filter
open scoped Classical

section NormalizedAndSimpson

/-- Normalized minimal covering system: finite set of `(m, a)` with `1 < m`, `0 ≤ a < m`,
covering `ℤ` irredundantly. -/
def MinimalSys (A : Finset (ℕ × ℤ)) : Prop :=
  (∀ p ∈ A, 1 < p.1 ∧ 0 ≤ p.2 ∧ p.2 < (p.1 : ℤ)) ∧
  (∀ z : ℤ, ∃ p ∈ A, z ≡ p.2 [ZMOD p.1]) ∧
  (∀ p ∈ A, ∃ z : ℤ, z ≡ p.2 [ZMOD p.1] ∧
    ∀ q ∈ A, q ≠ p → ¬ (z ≡ q.2 [ZMOD q.1]))

/-- Every irreducible covering set `M` is the modulus projection of a normalized minimal covering system
of the same cardinality. -/
lemma normalized_family {M : Finset ℕ} (irr : Erdos1189.IsIrreducibleCoveringSet M) :
    ∃ A : Finset (ℕ × ℤ), MinimalSys A ∧ A.card = M.card ∧ A.image Prod.fst = M := by
  obtain ⟨⟨mods, a, cover⟩, minimal⟩ := irr
  let f : ℕ → ℕ × ℤ := fun m => (m, a m % (m : ℤ))
  have fi : Function.Injective f := fun _ _ h => congrArg Prod.fst h
  refine ⟨M.image f, ⟨?_, ?_, ?_⟩, Finset.card_image_of_injective _ fi, ?_⟩
  · intro p hp
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hp
    have hpos : (0 : ℤ) < (m : ℤ) := by exact_mod_cast Nat.zero_lt_of_lt (mods m hm)
    exact ⟨mods m hm, Int.emod_nonneg _ hpos.ne', Int.emod_lt_of_pos _ hpos⟩
  · intro z
    obtain ⟨m, hm, hcong⟩ := cover z
    exact ⟨f m, Finset.mem_image_of_mem _ hm, hcong.trans (Int.mod_modEq _ _).symm⟩
  · intro p hp
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hp
    have hmiss : ¬ ∀ z : ℤ, ∃ j ∈ M.erase m, z ≡ a j [ZMOD j] := fun h =>
      minimal _ (Finset.erase_ssubset hm) ⟨fun j hj => mods j (Finset.mem_of_mem_erase hj), a, h⟩
    obtain ⟨z, hz⟩ := Classical.not_forall.mp hmiss
    obtain ⟨j, hj, hcong⟩ := cover z
    have hjm : j = m := by
      by_contra hne
      exact hz ⟨j, Finset.mem_erase.mpr ⟨hne, hj⟩, hcong⟩
    subst hjm
    refine ⟨z, hcong.trans (Int.mod_modEq _ _).symm, ?_⟩
    intro q hq hne hmatch
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
    exact hz ⟨j, Finset.mem_erase.mpr ⟨fun h => hne (congrArg f h), hj⟩,
      hmatch.trans (Int.mod_modEq _ _)⟩
  · ext m
    simp [Finset.image_image, f, Function.comp_def]

/-- An axis-aligned hyperplane (subcube) in `Π i : ι, S i`: `H i = some a` fixes coordinate `i`
to `a`, while `H i = none` leaves coordinate `i` free. -/
abbrev HPlane (ι : Type*) (S : ι → Type*) := (i : ι) → Option (S i)

/-- Point membership in a hyperplane. -/
def HPlane.mem {ι : Type*} {S : ι → Type*} (H : HPlane ι S) (x : (i : ι) → S i) : Prop :=
  ∀ i a, H i = some a → x i = a

/-- The set of coordinates fixed by a hyperplane `H`. -/
def HPlane.fixed {ι : Type*} [Fintype ι] {S : ι → Type*} (H : HPlane ι S) : Finset ι :=
  Finset.univ.filter fun i => (H i).isSome

lemma mem_fixed_iff {ι : Type*} [Fintype ι] {S : ι → Type*} {H : HPlane ι S} {i : ι} :
    i ∈ H.fixed ↔ (H i).isSome := by
  simp [HPlane.fixed]

lemma notMem_fixed_iff {ι : Type*} [Fintype ι] {S : ι → Type*} {H : HPlane ι S} {i : ι} :
    i ∉ H.fixed ↔ H i = none := by
  simp [HPlane.fixed, Option.isSome_iff_ne_none]

/-- Coverage of the slice `{ x | ∀ i ∈ D, x i = z i }` by a family of hyperplanes `A`. -/
def CoversOn {ι : Type*} {S : ι → Type*} (D : Finset ι) (z : (i : ι) → S i)
    (A : Finset (HPlane ι S)) : Prop :=
  ∀ x : (i : ι) → S i, (∀ i ∈ D, x i = z i) → ∃ H ∈ A, H.mem x

/-- Full coverage of `Π i : ι, S i`. -/
def Covers {ι : Type*} {S : ι → Type*} (A : Finset (HPlane ι S)) : Prop :=
  ∀ x : (i : ι) → S i, ∃ H ∈ A, H.mem x

/-- Minimal (irredundant) cover of `Π i : ι, S i`. -/
def IsMinCover {ι : Type*} {S : ι → Type*} (A : Finset (HPlane ι S)) : Prop :=
  Covers A ∧ ∀ H ∈ A, ∃ x : (i : ι) → S i, H.mem x ∧ ∀ H' ∈ A, H' ≠ H → ¬ H'.mem x

lemma coversOn_mono {ι : Type*} {S : ι → Type*} {D : Finset ι} {z : (i : ι) → S i}
    {A B : Finset (HPlane ι S)} (hAB : A ⊆ B) (hA : CoversOn D z A) : CoversOn D z B := by
  intro x hx
  obtain ⟨H, hH, hmem⟩ := hA x hx
  exact ⟨H, hAB hH, hmem⟩

/-- Every covering subfamily `P ∪ C` on a slice contains a minimal `Q ⊆ C` such that `P ∪ Q`
still covers the slice. -/
lemma exists_minimal_subcoverOn {ι : Type*} {S : ι → Type*} [DecidableEq (HPlane ι S)]
    (D : Finset ι) (z : (i : ι) → S i)
    (P C : Finset (HPlane ι S)) (hcov : CoversOn D z (P ∪ C)) :
    ∃ Q ⊆ C, CoversOn D z (P ∪ Q) ∧ ∀ Q' ⊂ Q, ¬ CoversOn D z (P ∪ Q') := by
  induction hn : C.card using Nat.strong_induction_on generalizing C with
  | _ n ih =>
    by_cases hmin : ∀ Q' ⊂ C, ¬ CoversOn D z (P ∪ Q')
    · exact ⟨C, Subset.rfl, hcov, hmin⟩
    · push Not at hmin
      obtain ⟨Q', hQ'ss, hQ'cov⟩ := hmin
      have hlt : Q'.card < n := hn ▸ Finset.card_lt_card hQ'ss
      obtain ⟨Q, hQQ', hQcov, hQmin⟩ := ih Q'.card hlt Q' hQ'cov rfl
      exact ⟨Q, hQQ'.trans hQ'ss.subset, hQcov, hQmin⟩

/-- Helper: if `H` is free at `j₀`, then `H.mem (Function.update x j₀ a) ↔ H.mem x`. -/
lemma hplane_mem_update_of_none {ι : Type*} {S : ι → Type*} {H : HPlane ι S}
    {j₀ : ι} (hfree : H j₀ = none) (x : (i : ι) → S i) (a : S j₀) :
    H.mem (Function.update x j₀ a) ↔ H.mem x := by
  constructor <;> intro h i b hib
  · have hne : i ≠ j₀ := by rintro rfl; simp [hfree] at hib
    have := h i b hib
    rwa [Function.update_of_ne hne] at this
  · by_cases hi : i = j₀
    · subst hi; simp [hfree] at hib
    · rw [Function.update_of_ne hi]; exact h i b hib

/-- **Simpson's Relative Bound** (1985 / BBMST Theorem 2.4):
If `F₀ ∪ B` covers the slice `(D, z)`, `F₀` alone does not cover `(D, z)`, every `H ∈ F₀` is free on
`W` (disjoint from `D`), and no coordinate `j ∈ W` can be dropped from `B` while maintaining coverage,
then `1 + ∑ j ∈ W, (|S j| - 1) ≤ B.card`. -/
theorem simpson_relative_bound {ι : Type*} [Fintype ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] (hS : ∀ i, 2 ≤ Fintype.card (S i)) :
    ∀ (m : ℕ) (D W : Finset ι) (z : (i : ι) → S i)
      (F₀ B : Finset (HPlane ι S)),
      W.card ≤ m →
      Disjoint D W →
      CoversOn D z (F₀ ∪ B) →
      ¬ CoversOn D z F₀ →
      (∀ H ∈ F₀, ∀ j ∈ W, H j = none) →
      (∀ j ∈ W, ¬ CoversOn D z (F₀ ∪ B.filter fun H => H j = none)) →
      1 + ∑ j ∈ W, (Fintype.card (S j) - 1) ≤ B.card := by
  intro m
  induction m with
  | zero =>
    intro D W z F₀ B hWm _ hcov hnotF _ _
    have hW : W = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hWm)
    subst hW
    simp only [Finset.sum_empty, add_zero]
    by_contra hB0
    have hBe : B = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hBe
    rw [Finset.union_empty] at hcov
    exact hnotF hcov
  | succ m ih =>
    intro D W z F₀ B hWm hDW hcov hnotF hFfree hess
    by_cases hW0 : W = ∅
    · subst hW0
      simp only [Finset.sum_empty, add_zero]
      by_contra hB0
      have hBe : B = ∅ := Finset.card_eq_zero.mp (by omega)
      subst hBe
      rw [Finset.union_empty] at hcov
      exact hnotF hcov
    · obtain ⟨j₀, hj₀W⟩ := Finset.nonempty_iff_ne_empty.mpr hW0
      set W' := W.erase j₀
      have hW'card : W'.card ≤ m := by
        have h1 : W'.card = W.card - 1 := Finset.card_erase_of_mem hj₀W
        omega
      have hj₀D : j₀ ∉ D := Finset.disjoint_right.mp hDW hj₀W
      have hDW' : Disjoint (insert j₀ D) W' := by
        rw [Finset.disjoint_insert_left]
        exact ⟨Finset.notMem_erase j₀ W, hDW.mono_right (Finset.erase_subset j₀ W)⟩
      set B_free := B.filter fun H => H j₀ = none
      set F₁ := F₀ ∪ B_free
      have hnotF₁ : ¬ CoversOn D z F₁ := hess j₀ hj₀W
      have hF₁free : ∀ H ∈ F₁, H j₀ = none := by
        intro H hH
        rcases Finset.mem_union.mp hH with h0 | hb
        · exact hFfree H h0 j₀ hj₀W
        · exact (Finset.mem_filter.mp hb).2
      have hnotF₁_slice : ∀ a : S j₀, ¬ CoversOn (insert j₀ D) (Function.update z j₀ a) F₁ := by
        intro a hcov_a
        apply hnotF₁
        intro x hx
        have hupd : ∀ i ∈ insert j₀ D, Function.update x j₀ a i = Function.update z j₀ a i := by
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hiD
          · simp
          · have hne : i ≠ j₀ := fun h => hj₀D (h ▸ hiD)
            rw [Function.update_of_ne hne, Function.update_of_ne hne]
            exact hx i hiD
        obtain ⟨H, hH, hmem⟩ := hcov_a (Function.update x j₀ a) hupd
        exact ⟨H, hH, (hplane_mem_update_of_none (hF₁free H hH) x a).mp hmem⟩
      -- Inner induction over a nodup list of values `l : List (S j₀)`
      have hlist : ∀ (l : List (S j₀)), l.Nodup →
          ∀ (P : Finset (HPlane ι S)) (W_done : Finset ι),
            F₀ ⊆ P →
            P ⊆ F₁ →
            W_done ⊆ W' →
            (∀ H ∈ P, ∀ j ∈ W' \ W_done, H j = none) →
            ∃ (Q_all : Finset (HPlane ι S)) (W_new : Finset ι),
              Q_all ⊆ (B_free \ P) ∪ B.filter (fun H => ∃ a ∈ l, H j₀ = some a) ∧
              W_new ⊆ W' \ W_done ∧
              (∀ a ∈ l, CoversOn (insert j₀ D) (Function.update z j₀ a) (P ∪ Q_all)) ∧
              (∀ H ∈ Q_all, ∀ j ∈ (W' \ W_done) \ W_new, H j = none) ∧
              l.length + ∑ j ∈ W_new, (Fintype.card (S j) - 1) ≤ Q_all.card := by
        intro l
        induction l with
        | nil =>
          intro _ P W_done _ _ _ _
          exact ⟨∅, ∅, Finset.empty_subset _, Finset.empty_subset _,
            by simp, by simp, by simp⟩
        | cons a l' ihl =>
          intro hnod P W_done hF₀P hPF₁ hWdW' hPfree
          rw [List.nodup_cons] at hnod
          rcases hnod with ⟨ha_not, hnod'⟩
          set B_a := B.filter fun H => H j₀ = some a
          have hcov_a : CoversOn (insert j₀ D) (Function.update z j₀ a) (P ∪ ((B_free \ P) ∪ B_a)) := by
            intro x hx
            have hxD : ∀ i ∈ D, x i = z i := by
              intro i hiD
              have hne : i ≠ j₀ := fun h => hj₀D (h ▸ hiD)
              have := hx i (Finset.mem_insert_of_mem hiD)
              rwa [Function.update_of_ne hne] at this
            have hxj₀ : x j₀ = a := by simpa using hx j₀ (Finset.mem_insert_self j₀ D)
            obtain ⟨H, hH, hmem⟩ := hcov x hxD
            rcases Finset.mem_union.mp hH with hHF₀ | hHB
            · exact ⟨H, Finset.mem_union_left _ (hF₀P hHF₀), hmem⟩
            · by_cases hHP : H ∈ P
              · exact ⟨H, Finset.mem_union_left _ hHP, hmem⟩
              · refine ⟨H, Finset.mem_union_right _ ?_, hmem⟩
                cases hHj : H j₀ with
                | none =>
                  exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hHB, hHj⟩, hHP⟩)
                | some b =>
                  have hba : b = a := by
                    have := hmem j₀ b hHj; rw [hxj₀] at this; exact this.symm
                  subst hba
                  exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hHB, hHj⟩)
          obtain ⟨Q_a, hQa_sub, hQa_cov, hQa_min⟩ :=
            exists_minimal_subcoverOn (insert j₀ D) (Function.update z j₀ a) P ((B_free \ P) ∪ B_a) hcov_a
          set W_a := (W' \ W_done).filter fun j => ∃ H ∈ Q_a, (H j).isSome
          have hWa_sub : W_a ⊆ W' \ W_done := Finset.filter_subset _ _
          have hWa_W' : W_a ⊆ W' := hWa_sub.trans Finset.sdiff_subset
          have hQa_bound : 1 + ∑ j ∈ W_a, (Fintype.card (S j) - 1) ≤ Q_a.card := by
            refine ih (insert j₀ D) W_a (Function.update z j₀ a) P Q_a
              ((Finset.card_le_card hWa_W').trans hW'card)
              (hDW'.mono_right hWa_W')
              hQa_cov
              (fun hP => hnotF₁_slice a (coversOn_mono hPF₁ hP))
              (fun H hH j hj => hPfree H hH j (hWa_sub hj))
              ?_
            intro j hj
            have hjsome : ∃ H ∈ Q_a, (H j).isSome := (Finset.mem_filter.mp hj).2
            obtain ⟨H, hHQ, hHj⟩ := hjsome
            have hss : Q_a.filter (fun H => H j = none) ⊂ Q_a := by
              rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
              refine ⟨H, hHQ, ?_⟩
              simp only [Finset.mem_filter, not_and]
              intro _ hnone
              simp [hnone] at hHj
            exact hQa_min _ hss
          -- Apply inner IH to `l'` with `P' = P ∪ (Q_a ∩ B_free)` and `W_done' = W_done ∪ W_a`
          set P' := P ∪ (Q_a ∩ B_free)
          set W_done' := W_done ∪ W_a
          have hF₀P' : F₀ ⊆ P' := hF₀P.trans Finset.subset_union_left
          have hP'F₁ : P' ⊆ F₁ := Finset.union_subset hPF₁
            (Finset.inter_subset_right.trans Finset.subset_union_right)
          have hWd'W' : W_done' ⊆ W' := Finset.union_subset hWdW' hWa_W'
          have hP'free : ∀ H ∈ P', ∀ j ∈ W' \ W_done', H j = none := by
            intro H hH j hj
            rcases Finset.mem_sdiff.mp hj with ⟨hjW', hjnot⟩
            have hjnotWd : j ∉ W_done := fun h => hjnot (Finset.mem_union_left _ h)
            have hjnotWa : j ∉ W_a := fun h => hjnot (Finset.mem_union_right _ h)
            rcases Finset.mem_union.mp hH with hHP | hHQB
            · exact hPfree H hHP j (Finset.mem_sdiff.mpr ⟨hjW', hjnotWd⟩)
            · have hHQ : H ∈ Q_a := (Finset.mem_inter.mp hHQB).1
              by_contra hne
              exact hjnotWa (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hjW', hjnotWd⟩,
                ⟨H, hHQ, Option.isSome_iff_ne_none.mpr hne⟩⟩)
          obtain ⟨Q_rest, W_rest, hQr_sub, hWr_sub, hQr_cov, hQr_free, hQr_bound⟩ :=
            ihl hnod' P' W_done' hF₀P' hP'F₁ hWd'W' hP'free
          have hdisj_Q : Disjoint Q_a Q_rest := by
            rw [Finset.disjoint_left]
            intro H hHQa hHQr
            have hQr_mem := hQr_sub hHQr
            rcases Finset.mem_union.mp (hQa_sub hHQa) with hHfree | hHBa
            · have hHBf : H ∈ B_free := (Finset.mem_sdiff.mp hHfree).1
              have hHP' : H ∈ P' := Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hHQa, hHBf⟩)
              rcases Finset.mem_union.mp hQr_mem with h1 | h2
              · exact (Finset.mem_sdiff.mp h1).2 hHP'
              · obtain ⟨b, _, hHb⟩ := (Finset.mem_filter.mp h2).2
                have hnone := (Finset.mem_filter.mp hHBf).2
                simp [hnone] at hHb
            · have hHa : H j₀ = some a := (Finset.mem_filter.mp hHBa).2
              rcases Finset.mem_union.mp hQr_mem with h1 | h2
              · have hnone := (Finset.mem_filter.mp (Finset.mem_sdiff.mp h1).1).2
                simp [hnone] at hHa
              · obtain ⟨b, hbl', hHb⟩ := (Finset.mem_filter.mp h2).2
                rw [hHa] at hHb
                exact ha_not ((Option.some.inj hHb) ▸ hbl')
          have hdisj_W : Disjoint W_a W_rest := by
            rw [Finset.disjoint_left]
            intro j hjWa hjWr
            exact (Finset.mem_sdiff.mp (hWr_sub hjWr)).2 (Finset.mem_union_right _ hjWa)
          refine ⟨Q_a ∪ Q_rest, W_a ∪ W_rest, ?_, ?_, ?_, ?_, ?_⟩
          · refine Finset.union_subset ?_ ?_
            · refine hQa_sub.trans (Finset.union_subset Finset.subset_union_left ?_)
              intro H hH
              rcases Finset.mem_filter.mp hH with ⟨hHB, hHa⟩
              exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hHB, a, List.mem_cons_self, hHa⟩)
            · refine hQr_sub.trans (Finset.union_subset ?_ ?_)
              · intro H hH
                rcases Finset.mem_sdiff.mp hH with ⟨hHBf, hHnotP'⟩
                exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hHBf, fun h => hHnotP' (Finset.mem_union_left _ h)⟩)
              · intro H hH
                rcases Finset.mem_filter.mp hH with ⟨hHB, b, hbl', hHb⟩
                exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hHB, b, List.mem_cons_of_mem a hbl', hHb⟩)
          · exact Finset.union_subset hWa_sub (hWr_sub.trans (Finset.sdiff_subset_sdiff Subset.rfl Finset.subset_union_left))
          · intro b hb
            rcases List.mem_cons.mp hb with rfl | hbl'
            · exact coversOn_mono (Finset.union_subset_union_right Finset.subset_union_left) hQa_cov
            · refine coversOn_mono ?_ (hQr_cov b hbl')
              refine Finset.union_subset ?_ (Finset.subset_union_right.trans (Finset.union_subset_union_right Finset.subset_union_right))
              refine Finset.union_subset Finset.subset_union_left ?_
              exact Finset.inter_subset_left.trans (Finset.subset_union_left.trans Finset.subset_union_right)
          · intro H hH j hj
            rcases Finset.mem_sdiff.mp hj with ⟨hjW, hjnot⟩
            have hjnotWa : j ∉ W_a := fun h => hjnot (Finset.mem_union_left _ h)
            have hjnotWr : j ∉ W_rest := fun h => hjnot (Finset.mem_union_right _ h)
            rcases Finset.mem_union.mp hH with hHQa | hHQr
            · by_contra hne
              exact hjnotWa (Finset.mem_filter.mpr ⟨hjW, ⟨H, hHQa, Option.isSome_iff_ne_none.mpr hne⟩⟩)
            · refine hQr_free H hHQr j (Finset.mem_sdiff.mpr ⟨?_, hjnotWr⟩)
              rcases Finset.mem_sdiff.mp hjW with ⟨hjW', hjnotWd⟩
              exact Finset.mem_sdiff.mpr ⟨hjW', fun h => by
                rcases Finset.mem_union.mp h with h1 | h2
                · exact hjnotWd h1
                · exact hjnotWa h2⟩
          · rw [List.length_cons, Finset.sum_union hdisj_W, Finset.card_union_of_disjoint hdisj_Q]
            omega
      -- Apply `hlist` to `Finset.univ.toList` of `S j₀`
      let l_all : List (S j₀) := (Finset.univ : Finset (S j₀)).toList
      have hnod_all : l_all.Nodup := Finset.nodup_toList _
      have hlen_all : l_all.length = Fintype.card (S j₀) := by
        simp [l_all]
      obtain ⟨Q_all, W_new, hQ_sub, hW_sub, hQ_cov, hQ_free, hQ_bound⟩ :=
        hlist l_all hnod_all F₀ ∅ Subset.rfl Finset.subset_union_left (Finset.empty_subset _)
          (fun H hH j hj => hFfree H hH j (Finset.erase_subset j₀ W (Finset.mem_sdiff.mp hj).1))
      have hW_eq : W_new = W' := by
        apply Finset.Subset.antisymm
        · exact hW_sub.trans Finset.sdiff_subset
        · intro j hjW'
          by_contra hjnot
          have hjW : j ∈ W := Finset.mem_of_mem_erase hjW'
          apply hess j hjW
          intro x hxD
          have ha_mem : x j₀ ∈ l_all := Finset.mem_toList.mpr (Finset.mem_univ _)
          have hxupd : ∀ i ∈ insert j₀ D, x i = Function.update z j₀ (x j₀) i := by
            intro i hi
            rcases Finset.mem_insert.mp hi with rfl | hiD
            · simp
            · have hne : i ≠ j₀ := fun h => hj₀D (h ▸ hiD)
              rw [Function.update_of_ne hne]; exact hxD i hiD
          obtain ⟨H, hH, hmem⟩ := hQ_cov (x j₀) ha_mem x hxupd
          rcases Finset.mem_union.mp hH with hHF₀ | hHQ
          · exact ⟨H, Finset.mem_union_left _ hHF₀, hmem⟩
          · have hHB : H ∈ B := by
              rcases Finset.mem_union.mp (hQ_sub hHQ) with h1 | h2
              · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp h1).1).1
              · exact (Finset.mem_filter.mp h2).1
            have hHj : H j = none := hQ_free H hHQ j (Finset.mem_sdiff.mpr
              ⟨Finset.mem_sdiff.mpr ⟨hjW', Finset.notMem_empty _⟩, hjnot⟩)
            exact ⟨H, Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hHB, hHj⟩), hmem⟩
      have hQ_sub_B : Q_all ⊆ B := by
        intro H hH
        rcases Finset.mem_union.mp (hQ_sub hH) with h1 | h2
        · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp h1).1).1
        · exact (Finset.mem_filter.mp h2).1
      have hcard_Q : Q_all.card ≤ B.card := Finset.card_le_card hQ_sub_B
      rw [hlen_all, hW_eq] at hQ_bound
      have hsum_eq : ∑ j ∈ W, (Fintype.card (S j) - 1) =
          (Fintype.card (S j₀) - 1) + ∑ j ∈ W', (Fintype.card (S j) - 1) :=
        (Finset.add_sum_erase W (fun j => Fintype.card (S j) - 1) hj₀W).symm
      have hSj₀ : 2 ≤ Fintype.card (S j₀) := hS j₀
      omega

/-- **Simpson's Product Bound**: Any minimal hyperplane cover `A` of `Π i : ι, S i` (with `|S i| ≥ 2`)
in which every coordinate `i : ι` is fixed by at least one `H ∈ A` satisfies
`1 + ∑ i, (|S i| - 1) ≤ A.card`. -/
theorem simpson_product_bound {ι : Type*} [Fintype ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] (hS : ∀ i, 2 ≤ Fintype.card (S i))
    {A : Finset (HPlane ι S)} (hA : IsMinCover A)
    (hact : ∀ i : ι, ∃ H ∈ A, (H i).isSome) :
    1 + ∑ i : ι, (Fintype.card (S i) - 1) ≤ A.card := by
  have hnonempty : Nonempty ((i : ι) → S i) := ⟨fun i =>
    (Fintype.card_pos_iff.mp (by have := hS i; omega : 0 < Fintype.card (S i))).some⟩
  obtain ⟨z⟩ := hnonempty
  refine simpson_relative_bound hS (Fintype.card ι) ∅ Finset.univ z ∅ A
    (by simp) (Finset.disjoint_empty_left _) ?_ ?_ (by simp) ?_
  · intro x _; rw [Finset.empty_union]; exact hA.1 x
  · intro h; obtain ⟨H, hH, _⟩ := h z (by simp); exact Finset.notMem_empty H hH
  · intro j _ hcov
    rw [Finset.empty_union] at hcov
    obtain ⟨H, hHA, hHj⟩ := hact j
    obtain ⟨x, _, hpriv⟩ := hA.2 H hHA
    obtain ⟨H', hH'f, hH'mem⟩ := hcov x (by simp)
    rcases Finset.mem_filter.mp hH'f with ⟨hH'A, hH'j⟩
    have hne : H' ≠ H := by rintro rfl; simp [hH'j] at hHj
    exact hpriv H' hH'A hne hH'mem

end NormalizedAndSimpson

section CRTBoxTranslation

/-- Base-`p` digit expansion identity: `n % p ^ (β + 1) = n % p ^ β + p ^ β * ((n / p ^ β) % p)`. -/
lemma nat_mod_pow_succ (p β n : ℕ) (hp : 0 < p) :
    n % p ^ (β + 1) = n % p ^ β + p ^ β * ((n / p ^ β) % p) := by
  have h1 : n = p ^ (β + 1) * (n / p ^ β / p) + (n % p ^ β + p ^ β * ((n / p ^ β) % p)) := by
    have ha := Nat.div_add_mod n (p ^ β)
    have hb := Nat.div_add_mod (n / p ^ β) p
    calc n = p ^ β * (n / p ^ β) + n % p ^ β := ha.symm
      _ = p ^ β * (p * (n / p ^ β / p) + (n / p ^ β) % p) + n % p ^ β := by rw [hb]
      _ = p ^ (β + 1) * (n / p ^ β / p) + (n % p ^ β + p ^ β * ((n / p ^ β) % p)) := by
        rw [pow_succ]; ring
  have hlt : n % p ^ β + p ^ β * ((n / p ^ β) % p) < p ^ (β + 1) := by
    have h1' : n % p ^ β < p ^ β := Nat.mod_lt n (pow_pos hp β)
    have h2' : (n / p ^ β) % p + 1 ≤ p := Nat.mod_lt _ hp
    calc n % p ^ β + p ^ β * ((n / p ^ β) % p)
        < p ^ β + p ^ β * ((n / p ^ β) % p) := Nat.add_lt_add_right h1' _
      _ = p ^ β * ((n / p ^ β) % p + 1) := by ring
      _ ≤ p ^ β * p := Nat.mul_le_mul_left _ h2'
      _ = p ^ (β + 1) := (pow_succ p β).symm
  conv_lhs => rw [h1]
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

/-- Congruence modulo `p ^ β` is equivalent to agreement of the first `β` base-`p` digits. -/
lemma nat_modEq_pow_iff_digits {p : ℕ} (hp : 0 < p) (β a b : ℕ) :
    a ≡ b [MOD p ^ β] ↔ ∀ j < β, (a / p ^ j) % p = (b / p ^ j) % p := by
  induction β with
  | zero => simp [Nat.ModEq, Nat.mod_one]
  | succ β ih =>
    constructor
    · intro h j hj
      have hmod : a % p ^ (β + 1) = b % p ^ (β + 1) := h
      rw [nat_mod_pow_succ p β a hp, nat_mod_pow_succ p β b hp] at hmod
      have hrem : a % p ^ β = b % p ^ β := by
        have := congrArg (· % p ^ β) hmod
        simp only [Nat.add_mul_mod_self_left, Nat.mod_mod] at this
        exact this
      by_cases hlt : j < β
      · exact ih.mp hrem j hlt
      · have hjeq : j = β := by omega
        subst j
        have hmul : p ^ β * ((a / p ^ β) % p) = p ^ β * ((b / p ^ β) % p) := by omega
        exact Nat.eq_of_mul_eq_mul_left (pow_pos hp β) hmul
    · intro h
      have hprev : a % p ^ β = b % p ^ β := ih.mpr fun j hj => h j (by omega)
      have htop : (a / p ^ β) % p = (b / p ^ β) % p := h β (Nat.lt_succ_self β)
      change a % p ^ (β + 1) = b % p ^ (β + 1)
      rw [nat_mod_pow_succ p β a hp, nat_mod_pow_succ p β b hp, hprev, htop]

/-- Reconstructing a number `< p ^ α` from its `α` base-`p` digits. -/
lemma baseP_sum_lt {p : ℕ} (α : ℕ) (d : ℕ → ℕ) (hd : ∀ j < α, d j < p) :
    ∑ j ∈ Finset.range α, d j * p ^ j < p ^ α := by
  induction α with
  | zero => simp
  | succ α ih =>
    rw [Finset.sum_range_succ]
    have hprev := ih (fun j hj => hd j (by omega))
    have htop : d α + 1 ≤ p := hd α (Nat.lt_succ_self α)
    calc (∑ j ∈ Finset.range α, d j * p ^ j) + d α * p ^ α
        < p ^ α + d α * p ^ α := Nat.add_lt_add_right hprev _
      _ = (d α + 1) * p ^ α := by ring
      _ ≤ p * p ^ α := Nat.mul_le_mul_right _ htop
      _ = p ^ (α + 1) := by rw [pow_succ']

/-- Extracting the `j`-th base-`p` digit from `∑ i ∈ range α, d i * p ^ i`. -/
lemma baseP_sum_digit {p : ℕ} (hp : 0 < p) (α : ℕ) (d : ℕ → ℕ) (hd : ∀ j < α, d j < p) :
    ∀ j < α, ((∑ i ∈ Finset.range α, d i * p ^ i) / p ^ j) % p = d j := by
  induction α with
  | zero => intro j hj; omega
  | succ α ih =>
    intro j hj
    rw [Finset.sum_range_succ]
    set S := ∑ i ∈ Finset.range α, d i * p ^ i
    have hSlt : S < p ^ α := baseP_sum_lt α d (fun i hi => hd i (by omega))
    by_cases hlt : j < α
    · have hdvd : p ^ (j + 1) ∣ p ^ α := Nat.pow_dvd_pow p (by omega)
      have hmod : S + d α * p ^ α ≡ S [MOD p ^ (j + 1)] := by
        change (S + d α * p ^ α) % p ^ (j + 1) = S % p ^ (j + 1)
        rcases hdvd with ⟨c, hc⟩
        rw [hc, show d α * (p ^ (j + 1) * c) = p ^ (j + 1) * (d α * c) by ring, Nat.add_mul_mod_self_left]
      rw [(nat_modEq_pow_iff_digits hp (j + 1) _ _).mp hmod j (Nat.lt_succ_self j)]
      exact ih (fun i hi => hd i (by omega)) j hlt
    · have hjeq : j = α := by omega
      subst j
      have hdiv : (S + d α * p ^ α) / p ^ α = d α := by
        rw [Nat.add_mul_div_right _ _ (pow_pos hp α), Nat.div_eq_of_lt hSlt, zero_add]
      rw [hdiv, Nat.mod_eq_of_lt (hd α (Nat.lt_succ_self α))]

/-- Prime-power coordinate set `V(N) = { (p, j) | p ∈ N.primeFactors ∧ j < N.factorization p }`. -/
def primeCoords (N : ℕ) : Finset (ℕ × ℕ) :=
  N.primeFactors.biUnion fun p =>
    (Finset.range (N.factorization p)).image fun j => (p, j)

lemma mem_primeCoords {N : ℕ} {v : ℕ × ℕ} :
    v ∈ primeCoords N ↔ v.1 ∈ N.primeFactors ∧ v.2 < N.factorization v.1 := by
  simp only [primeCoords, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨p, hp, j, hj, rfl⟩
    exact ⟨hp, hj⟩
  · rintro ⟨hp, hj⟩
    exact ⟨v.1, hp, v.2, hj, Prod.eta v⟩

/-- Index type of prime-power coordinates for `N`. -/
abbrev CoordIdx (N : ℕ) := { v : ℕ × ℕ // v ∈ primeCoords N }

/-- Alphabet `Fin p` at coordinate `v = (p, j)`. -/
abbrev CoordVal (N : ℕ) (v : CoordIdx N) := Fin v.1.1

lemma coordVal_card_ge_two {N : ℕ} (v : CoordIdx N) : 2 ≤ Fintype.card (CoordVal N v) := by
  have hp : v.1.1.Prime := Nat.prime_of_mem_primeFactors (mem_primeCoords.mp v.2).1
  simpa using hp.two_le

/-- Map an integer `z : ℤ` to its prime-power base-`p` digits in `Π v : CoordIdx N, Fin v.1.1`. -/
def crtDigitMap (N : ℕ) (z : ℤ) (v : CoordIdx N) : CoordVal N v :=
  let p := v.1.1
  let α := N.factorization p
  have hp : p.Prime := Nat.prime_of_mem_primeFactors (mem_primeCoords.mp v.2).1
  ⟨((z % ((p ^ α : ℕ) : ℤ)).toNat / p ^ v.1.2) % p, Nat.mod_lt _ hp.pos⟩

/-- Surjectivity of `crtDigitMap N : ℤ → Π v : CoordIdx N, Fin v.1.1` via CRT. -/
lemma crtDigitMap_surjective {N : ℕ} :
    Function.Surjective (crtDigitMap N) := by
  intro x
  let d : ℕ → ℕ → ℕ := fun p j =>
    if h : (p, j) ∈ primeCoords N then (x ⟨(p, j), h⟩).val else 0
  let b : ℕ → ℕ := fun p => ∑ j ∈ Finset.range (N.factorization p), d p j * p ^ j
  let s : ℕ → ℕ := fun p => p ^ N.factorization p
  have hs : ∀ p ∈ N.primeFactors, s p ≠ 0 := fun p hp =>
    (pow_pos (Nat.prime_of_mem_primeFactors hp).pos _).ne'
  have hpp : Set.Pairwise (N.primeFactors : Set ℕ) (Function.onFun Nat.Coprime s) := by
    intro p hp q hq hne
    change (p ^ N.factorization p).Coprime (q ^ N.factorization q)
    exact ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr hne).pow _ _
  let k := (Nat.chineseRemainderOfFinset b s N.primeFactors hs hpp).val
  have hk : ∀ p ∈ N.primeFactors, k ≡ b p [MOD s p] :=
    (Nat.chineseRemainderOfFinset b s N.primeFactors hs hpp).property
  refine ⟨(k : ℤ), funext fun v => Fin.ext ?_⟩
  rcases mem_primeCoords.mp v.2 with ⟨hpN, hjlt⟩
  have hp : v.1.1.Prime := Nat.prime_of_mem_primeFactors hpN
  have hd_lt : ∀ j < N.factorization v.1.1, d v.1.1 j < v.1.1 := by
    intro j hj
    have hvj : (v.1.1, j) ∈ primeCoords N := mem_primeCoords.mpr ⟨hpN, hj⟩
    simp only [d, dif_pos hvj]
    exact (x ⟨(v.1.1, j), hvj⟩).isLt
  have hblt : b v.1.1 < s v.1.1 := baseP_sum_lt (N.factorization v.1.1) (d v.1.1) hd_lt
  have hkmod : ((k : ℤ) % ((s v.1.1 : ℕ) : ℤ)).toNat = b v.1.1 := by
    have h1 : (k : ℤ) % ((s v.1.1 : ℕ) : ℤ) = ((k % s v.1.1 : ℕ) : ℤ) := by norm_cast
    rw [h1, Int.toNat_natCast]
    have h2 : k % s v.1.1 = b v.1.1 % s v.1.1 := hk v.1.1 hpN
    rw [h2, Nat.mod_eq_of_lt hblt]
  change (((k : ℤ) % ((s v.1.1 : ℕ) : ℤ)).toNat / v.1.1 ^ v.1.2) % v.1.1 = (x v).val
  rw [hkmod, baseP_sum_digit hp.pos (N.factorization v.1.1) (d v.1.1) hd_lt v.1.2 hjlt]
  have hv_eq : (v.1.1, v.1.2) = v.1 := Prod.eta v.1
  have hmem : (v.1.1, v.1.2) ∈ primeCoords N := by rw [hv_eq]; exact v.2
  simp only [d, dif_pos hmem]

/-- If `p ∉ n.primeFactors`, then `n.factorization p = 0`. -/
lemma factorization_eq_zero_of_notMem_primeFactors {n p : ℕ} (hp : p ∉ n.primeFactors) :
    n.factorization p = 0 := by
  rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
  exact hp

/-- Arithmetic hyperplane in `Π v : CoordIdx N, Fin v.1.1` corresponding to `z ≡ a [ZMOD m]`. -/
def arithHPlane (N m : ℕ) (a : ℤ) : HPlane (CoordIdx N) (CoordVal N) :=
  fun v => if v.1.2 < m.factorization v.1.1 then some (crtDigitMap N a v) else none

/-- Exact equivalence between modular congruence `z ≡ a [ZMOD m]` (for `m ∣ N`, `0 < m, N`)
and membership in `arithHPlane N m a`. -/
lemma modEq_iff_mem_arithHPlane {N m : ℕ} (hN : 0 < N) (hm0 : 0 < m) (hmN : m ∣ N) (a z : ℤ) :
    (z ≡ a [ZMOD m]) ↔ (arithHPlane N m a).mem (crtDigitMap N z) := by
  have hm_prod : m = ∏ p ∈ N.primeFactors, p ^ m.factorization p := by
    have h1 : ∏ p ∈ m.primeFactors, p ^ m.factorization p = m := by
      have := Nat.prod_factorization_pow_eq_self hm0.ne'
      simpa [Finsupp.prod, Nat.support_factorization] using this
    conv_lhs => rw [← h1]
    refine Finset.prod_subset (f := fun p : ℕ => p ^ m.factorization p)
      (Nat.primeFactors_mono hmN hN.ne') ?_
    intro p _ hpnot
    rw [factorization_eq_zero_of_notMem_primeFactors hpnot, pow_zero]
  have hmod_iff_primes : (z ≡ a [ZMOD m]) ↔
      ∀ p ∈ N.primeFactors, z ≡ a [ZMOD ((p ^ m.factorization p : ℕ) : ℤ)] := by
    constructor
    · intro h p _
      have hdvd : p ^ m.factorization p ∣ m := Nat.ordProj_dvd m p
      exact h.of_dvd (Int.natCast_dvd_natCast.mpr hdvd)
    · intro h
      rw [Int.modEq_iff_dvd, hm_prod]
      push_cast
      refine Finset.prod_dvd_of_coprime ?_ ?_
      · intro p hp q hq hne
        change IsCoprime ((p ^ m.factorization p : ℕ) : ℤ) ((q ^ m.factorization q : ℕ) : ℤ)
        have hc : (p ^ m.factorization p).Coprime (q ^ m.factorization q) :=
          ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
            (Nat.prime_of_mem_primeFactors hq)).mpr hne).pow _ _
        exact Nat.isCoprime_iff_coprime.mpr hc
      · intro p hp
        exact Int.modEq_iff_dvd.mp (h p hp)
  rw [hmod_iff_primes]
  -- Now match each prime `p ∈ N.primeFactors` with the base-`p` digits!
  constructor
  · intro h v b hb
    dsimp only [arithHPlane] at hb
    by_cases hjlt : v.1.2 < m.factorization v.1.1
    · rw [if_pos hjlt] at hb
      injection hb with hbeq
      subst hbeq
      rcases mem_primeCoords.mp v.2 with ⟨hpN, _⟩
      have hp : v.1.1.Prime := Nat.prime_of_mem_primeFactors hpN
      have hfac_le : m.factorization v.1.1 ≤ N.factorization v.1.1 :=
        Nat.factorization_le_iff_dvd hm0.ne' hN.ne' |>.mpr hmN v.1.1
      have hcong_p := h v.1.1 hpN
      have hnat_mod : (z % ((v.1.1 ^ N.factorization v.1.1 : ℕ) : ℤ)).toNat ≡
          (a % ((v.1.1 ^ N.factorization v.1.1 : ℕ) : ℤ)).toNat [MOD v.1.1 ^ m.factorization v.1.1] := by
        rw [← Int.natCast_modEq_iff]
        have hposN : (0 : ℤ) < ((v.1.1 ^ N.factorization v.1.1 : ℕ) : ℤ) := by
          exact_mod_cast pow_pos hp.pos _
        rw [Int.toNat_of_nonneg (Int.emod_nonneg z hposN.ne'),
            Int.toNat_of_nonneg (Int.emod_nonneg a hposN.ne')]
        have hdvd : ((v.1.1 ^ m.factorization v.1.1 : ℕ) : ℤ) ∣ ((v.1.1 ^ N.factorization v.1.1 : ℕ) : ℤ) := by
          exact_mod_cast Nat.pow_dvd_pow v.1.1 hfac_le
        exact ((Int.mod_modEq z _).of_dvd hdvd).trans (hcong_p.trans ((Int.mod_modEq a _).of_dvd hdvd).symm)
      apply Fin.ext
      exact (nat_modEq_pow_iff_digits hp.pos (m.factorization v.1.1) _ _).mp hnat_mod v.1.2 hjlt
    · rw [if_neg hjlt] at hb
      simp at hb
  · intro hmem p hpN
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpN
    have hfac_le : m.factorization p ≤ N.factorization p :=
      Nat.factorization_le_iff_dvd hm0.ne' hN.ne' |>.mpr hmN p
    have hnat_mod : (z % ((p ^ N.factorization p : ℕ) : ℤ)).toNat ≡
        (a % ((p ^ N.factorization p : ℕ) : ℤ)).toNat [MOD p ^ m.factorization p] := by
      rw [nat_modEq_pow_iff_digits hp.pos]
      intro j hj
      have hv : (p, j) ∈ primeCoords N := mem_primeCoords.mpr ⟨hpN, lt_of_lt_of_le hj hfac_le⟩
      have h1 := hmem ⟨(p, j), hv⟩ (crtDigitMap N a ⟨(p, j), hv⟩) (by simp [arithHPlane, hj])
      exact congrArg Fin.val h1
    rw [← Int.natCast_modEq_iff] at hnat_mod
    have hposN : (0 : ℤ) < ((p ^ N.factorization p : ℕ) : ℤ) := by exact_mod_cast pow_pos hp.pos _
    rw [Int.toNat_of_nonneg (Int.emod_nonneg z hposN.ne'),
        Int.toNat_of_nonneg (Int.emod_nonneg a hposN.ne')] at hnat_mod
    have hdvd : ((p ^ m.factorization p : ℕ) : ℤ) ∣ ((p ^ N.factorization p : ℕ) : ℤ) := by
      exact_mod_cast Nat.pow_dvd_pow p hfac_le
    exact ((Int.mod_modEq z _).of_dvd hdvd).symm.trans (hnat_mod.trans ((Int.mod_modEq a _).of_dvd hdvd))

/-- Every prime power `p ^ (N.factorization p)` dividing `N = M.lcm id` divides some `m ∈ M`. -/
lemma exists_mem_factorization_eq_lcm {M : Finset ℕ} (hM : ∀ m ∈ M, 0 < m)
    {p : ℕ} (hpN : p ∈ (M.lcm id).primeFactors) :
    ∃ m ∈ M, m.factorization p = (M.lcm id).factorization p := by
  set N := M.lcm id
  have hN0 : N ≠ 0 := by
    intro h0
    simp [h0] at hpN
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpN
  have hfac_pos : 0 < N.factorization p :=
    Nat.Prime.factorization_pos_of_dvd hp hN0 (Nat.dvd_of_mem_primeFactors hpN)
  by_contra hall
  push Not at hall
  have hdvd_Np : ∀ m ∈ M, m ∣ N / p := by
    intro m hm
    have hm0 : m ≠ 0 := (hM m hm).ne'
    have hmN : m ∣ N := Finset.dvd_lcm hm
    have hNp0 : N / p ≠ 0 := by
      have hpN_dvd : p ∣ N := Nat.dvd_of_mem_primeFactors hpN
      exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hpN_dvd) hp.pos).ne'
    rw [← Nat.factorization_le_iff_dvd hm0 hNp0]
    intro q
    have hleN : m.factorization q ≤ N.factorization q :=
      (Nat.factorization_le_iff_dvd hm0 hN0).mpr hmN q
    have hNp_fac : (N / p).factorization q = N.factorization q - (if q = p then 1 else 0) := by
      have hpN_dvd : p ∣ N := Nat.dvd_of_mem_primeFactors hpN
      rw [Nat.factorization_div hpN_dvd]
      simp [Nat.Prime.factorization hp, Finsupp.single_apply, eq_comm]
    rw [hNp_fac]
    by_cases hqp : q = p
    · subst hqp
      have hne := hall m hm
      simp only [↓reduceIte]; omega
    · simp only [hqp, ↓reduceIte, Nat.sub_zero]; exact hleN
  have hN_dvd : N ∣ N / p := Finset.lcm_dvd fun m hm => hdvd_Np m hm
  have hN_le : N ≤ N / p := Nat.le_of_dvd
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) (Nat.dvd_of_mem_primeFactors hpN)) hp.pos) hN_dvd
  have hdiv_lt : N / p < N := Nat.div_lt_self (Nat.pos_of_ne_zero hN0) hp.one_lt
  omega

/-- Translating a normalized minimal covering system `A` to a minimal hyperplane cover of `CoordIdx N`. -/
lemma minimalSys_to_minCover {A : Finset (ℕ × ℤ)} (hA : MinimalSys A) :
    let N := (A.image Prod.fst).lcm id
    0 < N ∧
    (∀ p ∈ A, p.1 ∣ N) ∧
    (A.image fun p => arithHPlane N p.1 p.2).card = A.card ∧
    IsMinCover (A.image fun p => arithHPlane N p.1 p.2) ∧
    (∀ v : CoordIdx N, ∃ H ∈ A.image fun p => arithHPlane N p.1 p.2, (H v).isSome) := by
  intro N
  have hNpos : 0 < N := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    have := Finset.lcm_eq_zero_iff.mp h0
    obtain ⟨m, hm, hm0⟩ := this
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
    have := (hA.1 p hp).1
    simp at hm0; omega
  have hdvdN : ∀ p ∈ A, p.1 ∣ N := fun p hp =>
    Finset.dvd_lcm (Finset.mem_image_of_mem Prod.fst hp)
  have hinj : Set.InjOn (fun p : ℕ × ℤ => arithHPlane N p.1 p.2) A := by
    intro p hp q hq heq
    dsimp only at heq
    by_contra hne
    obtain ⟨z, hz1, hz2⟩ := hA.2.2 p hp
    have hmemp : (arithHPlane N p.1 p.2).mem (crtDigitMap N z) :=
      (modEq_iff_mem_arithHPlane hNpos (by have := (hA.1 p hp).1; omega) (hdvdN p hp) p.2 z).mp hz1
    rw [heq] at hmemp
    exact hz2 q hq (fun h => hne h.symm)
      ((modEq_iff_mem_arithHPlane hNpos (by have := (hA.1 q hq).1; omega) (hdvdN q hq) q.2 z).mpr hmemp)
  refine ⟨hNpos, hdvdN, Finset.card_image_of_injOn hinj, ⟨?_, ?_⟩, ?_⟩
  · intro x
    obtain ⟨z, rfl⟩ := crtDigitMap_surjective x
    obtain ⟨p, hp, hcong⟩ := hA.2.1 z
    exact ⟨arithHPlane N p.1 p.2, Finset.mem_image_of_mem _ hp,
      (modEq_iff_mem_arithHPlane hNpos (by have := (hA.1 p hp).1; omega) (hdvdN p hp) p.2 z).mp hcong⟩
  · intro H hH
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨z, hz1, hz2⟩ := hA.2.2 p hp
    refine ⟨crtDigitMap N z,
      (modEq_iff_mem_arithHPlane hNpos (by have := (hA.1 p hp).1; omega) (hdvdN p hp) p.2 z).mp hz1, ?_⟩
    intro H' hH' hne hmem'
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hH'
    have hqp : q ≠ p := fun h => hne (by rw [h])
    exact hz2 q hq hqp
      ((modEq_iff_mem_arithHPlane hNpos (by have := (hA.1 q hq).1; omega) (hdvdN q hq) q.2 z).mpr hmem')
  · intro v
    rcases mem_primeCoords.mp v.2 with ⟨hpN, hjlt⟩
    have hMpos : ∀ m ∈ A.image Prod.fst, 0 < m := by
      intro m hm
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
      have := (hA.1 p hp).1; omega
    obtain ⟨m, hm, hmfac⟩ := exists_mem_factorization_eq_lcm hMpos hpN
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
    change p.1.factorization v.1.1 = N.factorization v.1.1 at hmfac
    refine ⟨arithHPlane N p.1 p.2, Finset.mem_image_of_mem _ hp, ?_⟩
    simp [arithHPlane, hmfac, hjlt]

/-- Sum of `v.1 - 1` over `primeCoords N` equals `∑ p ∈ N.primeFactors, N.factorization p * (p - 1)`. -/
lemma sum_primeCoords_sub_one (N : ℕ) :
    ∑ v ∈ primeCoords N, (v.1 - 1) = ∑ p ∈ N.primeFactors, N.factorization p * (p - 1) := by
  unfold primeCoords
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_image (fun _ _ _ _ h => (Prod.mk.inj h).2)]
    simp [Finset.sum_const, smul_eq_mul]
  · intro p _ q _ hne
    change Disjoint ((Finset.range (N.factorization p)).image fun j => (p, j))
      ((Finset.range (N.factorization q)).image fun j => (q, j))
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    obtain ⟨j1, _, rfl⟩ := Finset.mem_image.mp hv1
    obtain ⟨j2, _, h⟩ := Finset.mem_image.mp hv2
    exact hne (Prod.mk.inj h).1.symm

/-- **Simpson's LCM Bound**: For any irreducible covering set `M` with `N = M.lcm id`,
`1 + ∑ p ∈ N.primeFactors, N.factorization p * (p - 1) ≤ M.card`. -/
theorem simpson_lcm_bound {M : Finset ℕ} (irr : Erdos1189.IsIrreducibleCoveringSet M) :
    let N := M.lcm id
    0 < N ∧ 1 + ∑ p ∈ N.primeFactors, N.factorization p * (p - 1) ≤ M.card := by
  obtain ⟨A, hA, hcard, himg⟩ := normalized_family irr
  obtain ⟨hNpos, _, hcard_box, hmin_box, hact_box⟩ := minimalSys_to_minCover hA
  rw [himg] at hNpos hcard_box hmin_box hact_box
  have hsb := simpson_product_bound (fun v => coordVal_card_ge_two v) hmin_box hact_box
  rw [hcard_box, hcard] at hsb
  have hsum : ∑ v : CoordIdx (M.lcm id), (Fintype.card (CoordVal (M.lcm id) v) - 1) =
      ∑ v ∈ primeCoords (M.lcm id), (v.1 - 1) := by
    simp only [Fintype.card_fin]
    exact Finset.sum_coe_sort (primeCoords (M.lcm id)) (fun v => v.1 - 1)
  rw [hsum, sum_primeCoords_sub_one] at hsb
  exact ⟨hNpos, hsb⟩

/-- Elementary inequality: `p ≤ 2 ^ (p - 1)` for all `p ≥ 1`. -/
lemma le_two_pow_sub_one {p : ℕ} (hp : 1 ≤ p) : p ≤ 2 ^ (p - 1) := by
  induction p with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => simp
    | succ m =>
      have h1 := ih (by omega)
      simp only [Nat.add_sub_cancel] at h1 ⊢
      rw [pow_succ']
      omega

/-- Corollary: For any irreducible covering set `M`, `M.lcm id ≤ 2 ^ (M.card - 1)`. -/
theorem lcm_le_two_pow {M : Finset ℕ} (irr : Erdos1189.IsIrreducibleCoveringSet M) :
    M.lcm id ≤ 2 ^ (M.card - 1) := by
  obtain ⟨hNpos, hsb⟩ := simpson_lcm_bound irr
  set N := M.lcm id
  have hN_eq : N = ∏ p ∈ N.primeFactors, p ^ N.factorization p := by
    have := Nat.prod_factorization_pow_eq_self hNpos.ne'
    simpa [Finsupp.prod, Nat.support_factorization] using this.symm
  calc N = ∏ p ∈ N.primeFactors, p ^ N.factorization p := hN_eq
    _ ≤ ∏ p ∈ N.primeFactors, (2 ^ (p - 1)) ^ N.factorization p := by
        refine Finset.prod_le_prod' fun p hp => Nat.pow_le_pow_left
          (le_two_pow_sub_one (Nat.prime_of_mem_primeFactors hp).one_le) _
    _ = ∏ p ∈ N.primeFactors, 2 ^ (N.factorization p * (p - 1)) := by
        refine Finset.prod_congr rfl fun p _ => by rw [← pow_mul, mul_comm]
    _ = 2 ^ (∑ p ∈ N.primeFactors, N.factorization p * (p - 1)) := by
        rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ 2 ^ (M.card - 1) := Nat.pow_le_pow_right (by omega) (by omega)

end CRTBoxTranslation

end Erdos1189BBMST

/- Section 3: Single-Path Codimension-1 Extraction (Lemma B) and Iterated Round Decomposition. -/

namespace Erdos1189BBMST

open Finset Real Filter
open scoped Classical

section ExtractionAndRounds

/-- Cardinality of a product box `{ x | (∀ u ∉ I, x u = z u) ∧ (∀ u ∈ I, x u ∈ A u) }`. -/
lemma card_box_eq_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (I : Finset ι) (z : (i : ι) → S i) (A : (i : ι) → Finset (S i)) :
    (Finset.univ.filter fun x : (i : ι) → S i =>
      (∀ u ∉ I, x u = z u) ∧ (∀ u ∈ I, x u ∈ A u)).card =
      ∏ u ∈ I, (A u).card := by
  let F : (i : ι) → Finset (S i) := fun u => if u ∈ I then A u else {z u}
  have heq : (Finset.univ.filter fun x : (i : ι) → S i =>
      (∀ u ∉ I, x u = z u) ∧ (∀ u ∈ I, x u ∈ A u)) = Fintype.piFinset F := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, F]
    constructor
    · rintro ⟨hout, hin⟩ u
      split_ifs with hu
      · exact hin u hu
      · exact Finset.mem_singleton.mpr (hout u hu)
    · intro h
      refine ⟨fun u hu => ?_, fun u hu => ?_⟩
      · have := h u; simp [hu] at this; exact this
      · have := h u; simp [hu] at this; exact this
  rw [heq, Fintype.card_piFinset]
  have hprod : ∏ u : ι, (F u).card =
      (∏ u ∈ I, (F u).card) * (∏ u ∈ Finset.univ \ I, (F u).card) := by
    rw [← Finset.prod_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset (Finset.subset_univ I)]
  rw [hprod]
  have h1 : ∏ u ∈ I, (F u).card = ∏ u ∈ I, (A u).card :=
    Finset.prod_congr rfl fun u hu => by simp [F, hu]
  have h2 : ∏ u ∈ Finset.univ \ I, (F u).card = 1 :=
    Finset.prod_eq_one fun u hu => by
      have hnot : u ∉ I := (Finset.mem_sdiff.mp hu).2
      simp [F, hnot]
  rw [h1, h2, mul_one]

/-- Cardinality of the intersection of a hyperplane `H` with a box `B`, bounded by `B.card / (C - 1)^2`
whenever `H` fixes at least 2 coordinates in `I` and every `u ∈ I` has `|A u| ≥ c`. -/
lemma card_hplane_inter_box_mul_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (I : Finset ι) (z : (i : ι) → S i) (A : (i : ι) → Finset (S i))
    {c : ℕ} (hc : ∀ u ∈ I, c ≤ (A u).card)
    {H : HPlane ι S} (h2 : 2 ≤ (H.fixed ∩ I).card) :
    let B := Finset.univ.filter fun x : (i : ι) → S i =>
      (∀ u ∉ I, x u = z u) ∧ (∀ u ∈ I, x u ∈ A u)
    (B.filter H.mem).card * c ^ 2 ≤ B.card := by
  intro B
  by_cases hne : (B.filter H.mem).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    rcases Finset.mem_filter.mp hx₀ with ⟨hx₀B, hx₀H⟩
    rcases Finset.mem_filter.mp hx₀B with ⟨_, hx₀out, hx₀in⟩
    let F_I := H.fixed ∩ I
    let A' : (i : ι) → Finset (S i) := fun u =>
      match H u with
      | some a => {a}
      | none => A u
    have hsub : B.filter H.mem ⊆ Finset.univ.filter fun x : (i : ι) → S i =>
        (∀ u ∉ I, x u = z u) ∧ (∀ u ∈ I, x u ∈ A' u) := by
      intro x hx
      rcases Finset.mem_filter.mp hx with ⟨hxB, hxH⟩
      rcases Finset.mem_filter.mp hxB with ⟨_, hxout, hxin⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxout, fun u hu => ?_⟩
      dsimp only [A']
      cases hHu : H u with
      | none => exact hxin u hu
      | some a => exact Finset.mem_singleton.mpr (hxH u a hHu)
    have hcard_le : (B.filter H.mem).card ≤ ∏ u ∈ I, (A' u).card :=
      (Finset.card_le_card hsub).trans (card_box_eq_prod I z A').le
    have hprod_A' : ∏ u ∈ I, (A' u).card = ∏ u ∈ I \ F_I, (A u).card := by
      have hsplit : I = (I \ F_I) ∪ F_I := (Finset.sdiff_union_of_subset Finset.inter_subset_right).symm
      conv_lhs => rw [hsplit, Finset.prod_union Finset.sdiff_disjoint]
      have h1 : ∏ u ∈ I \ F_I, (A' u).card = ∏ u ∈ I \ F_I, (A u).card := by
        refine Finset.prod_congr rfl fun u hu => ?_
        have huI : u ∈ I := (Finset.mem_sdiff.mp hu).1
        have hunotF : u ∉ H.fixed := fun h => (Finset.mem_sdiff.mp hu).2 (Finset.mem_inter.mpr ⟨h, huI⟩)
        have hnone : H u = none := notMem_fixed_iff.mp hunotF
        simp [A', hnone]
      have h2' : ∏ u ∈ F_I, (A' u).card = 1 := by
        refine Finset.prod_eq_one fun u hu => ?_
        have hsome : (H u).isSome := mem_fixed_iff.mp (Finset.mem_inter.mp hu).1
        rcases Option.isSome_iff_exists.mp hsome with ⟨a, ha⟩
        simp [A', ha]
      rw [h1, h2', mul_one]
    have hB_eq : B.card = (∏ u ∈ I \ F_I, (A u).card) * (∏ u ∈ F_I, (A u).card) := by
      have hsplit : I = (I \ F_I) ∪ F_I := (Finset.sdiff_union_of_subset Finset.inter_subset_right).symm
      rw [card_box_eq_prod]
      conv_lhs => rw [hsplit, Finset.prod_union Finset.sdiff_disjoint]
    have hFI2 : 2 ≤ F_I.card := h2
    obtain ⟨u₁, hu₁, u₂, hu₂, hne12⟩ := Finset.one_lt_card.mp (by omega : 1 < F_I.card)
    have hpair : {u₁, u₂} ⊆ F_I := by
      intro u hu; rcases Finset.mem_insert.mp hu with rfl | h
      · exact hu₁
      · rw [Finset.mem_singleton.mp h]; exact hu₂
    have hprod_ge : c ^ 2 ≤ ∏ u ∈ F_I, (A u).card := by
      have h1 : ∏ u ∈ ({u₁, u₂} : Finset ι), (A u).card ≤ ∏ u ∈ F_I, (A u).card := by
        rw [← Finset.prod_sdiff hpair]
        have hpos : 1 ≤ ∏ u ∈ F_I \ {u₁, u₂}, (A u).card := by
          refine Finset.one_le_prod' fun u hu => ?_
          have huI : u ∈ I := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hu).1).2
          exact Finset.card_pos.mpr ⟨x₀ u, hx₀in u huI⟩
        calc ∏ u ∈ ({u₁, u₂} : Finset ι), (A u).card
            = 1 * ∏ u ∈ ({u₁, u₂} : Finset ι), (A u).card := (one_mul _).symm
          _ ≤ (∏ u ∈ F_I \ {u₁, u₂}, (A u).card) * ∏ u ∈ ({u₁, u₂} : Finset ι), (A u).card :=
            Nat.mul_le_mul_right _ hpos
      rw [Finset.prod_pair hne12] at h1
      have hc1 : c ≤ (A u₁).card := hc u₁ (Finset.mem_inter.mp hu₁).2
      have hc2 : c ≤ (A u₂).card := hc u₂ (Finset.mem_inter.mp hu₂).2
      calc c ^ 2 = c * c := sq c
        _ ≤ (A u₁).card * (A u₂).card := Nat.mul_le_mul hc1 hc2
        _ ≤ ∏ u ∈ F_I, (A u).card := h1
    rw [hB_eq]
    calc (B.filter H.mem).card * c ^ 2
        ≤ (∏ u ∈ I \ F_I, (A u).card) * c ^ 2 := by rw [← hprod_A']; exact Nat.mul_le_mul_right _ hcard_le
      _ ≤ (∏ u ∈ I \ F_I, (A u).card) * (∏ u ∈ F_I, (A u).card) := Nat.mul_le_mul_left _ hprod_ge
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, zero_mul]
    exact Nat.zero_le _

/-- **Lemma B (Single-Path Codimension-1 Extraction)**:
Given a minimal hyperplane cover `A` of size `k`, a subset of big coordinates `V_big` with
`|S v| ≥ C` and `k < (C - 1)^2` (`2 ≤ C`), and any `H_star ∈ A` with private point `z`,
there exists a nodup sequence `seq` of big coordinates and pairwise disjoint codimension-1 buckets
`buckets v ⊆ A.erase H_star` such that:
1. `H_star.fixed ∩ V_big ⊆ seq.toFinset`,
2. for every `v ∈ seq`, `|S v| ≤ (buckets v).card + C`,
3. for every `i < seq.length` and `H ∈ buckets (seq[i])`:
   - `H.fixed ∩ V_big ⊆ insert (seq[i]) (seq.take i).toFinset`,
   - `(H (seq[i])).isSome` and `H ↦ H (seq[i])` is injective on `buckets (seq[i])`,
   - for all `u ∈ V_big`, `u ≠ seq[i] → H u = none ∨ H u = some (z u)`. -/
theorem single_path_extract {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    {A : Finset (HPlane ι S)} (hA : IsMinCover A)
    (V_big : Finset ι) {C : ℕ} (hC2 : 2 ≤ C) (hCsq : A.card < (C - 1) ^ 2)
    {H_star : HPlane ι S} (_hHsA : H_star ∈ A)
    (z : (i : ι) → S i) (hzH : H_star.mem z)
    (hzpriv : ∀ H ∈ A, H ≠ H_star → ¬ H.mem z) :
    ∃ (seq : List ι) (buckets : ι → Finset (HPlane ι S)),
      seq.Nodup ∧
      (∀ v ∈ seq, v ∈ V_big) ∧
      H_star.fixed ∩ V_big ⊆ seq.toFinset ∧
      (∀ v ∈ seq, buckets v ⊆ A.erase H_star) ∧
      (∀ v ∈ seq, Fintype.card (S v) ≤ (buckets v).card + C) ∧
      (∀ i j : Fin seq.length, i ≠ j → Disjoint (buckets (seq.get i)) (buckets (seq.get j))) ∧
      (∀ i : Fin seq.length, ∀ H ∈ buckets (seq.get i),
        H.fixed ∩ V_big ⊆ insert (seq.get i) (seq.take i.val).toFinset ∧
        (H (seq.get i)).isSome ∧
        (∀ u ∈ V_big, u ≠ seq.get i → H u = none ∨ H u = some (z u))) ∧
      (∀ v ∈ seq, Set.InjOn (fun H : HPlane ι S => H v) (buckets v)) := by
  -- Outer induction on `I.card`, maintaining `(W, I = V_big \ W, rem, buck, buck_done)`
  suffices hmain : ∀ (m : ℕ) (W : Finset ι)
      (rem : (v : ι) → Finset (S v))
      (buck : ι → Finset (HPlane ι S)),
      W ⊆ V_big →
      (V_big \ W).card ≤ m →
      (∀ v ∈ V_big \ W, z v ∈ rem v) →
      (∀ v ∈ V_big \ W, buck v ⊆ A.erase H_star) →
      (∀ v ∈ V_big \ W, (buck v).card + (rem v).card = Fintype.card (S v)) →
      (∀ v ∈ V_big \ W, ∀ H ∈ buck v,
        (∃ a, H v = some a ∧ a ∉ rem v) ∧
        H.fixed ∩ V_big ⊆ insert v W ∧
        (∀ u ∈ V_big, u ≠ v → H u = none ∨ H u = some (z u))) →
      (∀ v ∈ V_big \ W, Set.InjOn (fun H : HPlane ι S => H v) (buck v)) →
      (∀ v ∈ V_big \ W, ∀ w ∈ V_big \ W, v ≠ w → Disjoint (buck v) (buck w)) →
      ∃ (seq : List ι) (buckets : ι → Finset (HPlane ι S)),
        seq.Nodup ∧
        (∀ v ∈ seq, v ∈ V_big \ W) ∧
        H_star.fixed ∩ (V_big \ W) ⊆ seq.toFinset ∧
        (∀ v ∈ seq, buckets v ⊆ A.erase H_star) ∧
        (∀ v ∈ seq, Fintype.card (S v) ≤ (buckets v).card + C) ∧
        (∀ i j : Fin seq.length, i ≠ j → Disjoint (buckets (seq.get i)) (buckets (seq.get j))) ∧
        (∀ i : Fin seq.length, ∀ H ∈ buckets (seq.get i),
          H.fixed ∩ V_big ⊆ insert (seq.get i) (W ∪ (seq.take i.val).toFinset) ∧
          (∃ a, H (seq.get i) = some a ∧ a ≠ z (seq.get i)) ∧
          (∀ u ∈ V_big, u ≠ seq.get i → H u = none ∨ H u = some (z u))) ∧
        (∀ v ∈ seq, Set.InjOn (fun H : HPlane ι S => H v) (buckets v)) by
    obtain ⟨seq, buckets, hnod, hsub, hcov, hbuckA, hcard, hdisj, hprop, hinj⟩ :=
      hmain V_big.card ∅ (fun _ => Finset.univ) (fun _ => ∅)
        (Finset.empty_subset _) (by simp)
        (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.empty_subset _)
        (fun _ _ => by simp) (fun _ _ _ h => absurd h (Finset.notMem_empty _))
        (fun _ _ _ h => absurd h (Finset.notMem_empty _))
        (fun _ _ _ _ _ => Finset.disjoint_empty_left _)
    refine ⟨seq, buckets, hnod,
      fun v hv => (Finset.mem_sdiff.mp (hsub v hv)).1,
      by simpa using hcov, hbuckA, hcard, hdisj, ?_, hinj⟩
    intro i H hH
    rcases hprop i H hH with ⟨hfix, ⟨a, ha, _⟩, hout⟩
    rw [Finset.empty_union] at hfix
    exact ⟨hfix, by rw [ha]; rfl, hout⟩
  intro m
  induction m with
  | zero =>
    intro W rem buck hWV hI0 _ _ _ _ _ _
    have hIe : V_big \ W = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hI0)
    refine ⟨[], fun _ => ∅, List.nodup_nil, by simp, by simp [hIe],
      by simp, by simp, fun i => Fin.elim0 i, fun i => Fin.elim0 i, by simp⟩
  | succ m ihm =>
    intro W rem buck hWV hIm hzrem hbuckA hsumcard hbuckP hinjB hdisjB
    set I := V_big \ W
    -- Inner induction on `∑ v ∈ I, (rem v).card` to exhaust all codimension-1 hyperplanes on `I`
    suffices hinner : ∀ (r : ℕ) (rem' : (v : ι) → Finset (S v)) (buck' : ι → Finset (HPlane ι S)),
        (∑ v ∈ I, (rem' v).card) ≤ r →
        (∀ v ∈ I, z v ∈ rem' v) →
        (∀ v ∈ I, buck' v ⊆ A.erase H_star) →
        (∀ v ∈ I, (buck' v).card + (rem' v).card = Fintype.card (S v)) →
        (∀ v ∈ I, ∀ H ∈ buck' v,
          (∃ a, H v = some a ∧ a ∉ rem' v) ∧
          H.fixed ∩ V_big ⊆ insert v W ∧
          (∀ u ∈ V_big, u ≠ v → H u = none ∨ H u = some (z u))) →
        (∀ v ∈ I, Set.InjOn (fun H : HPlane ι S => H v) (buck' v)) →
        (∀ v ∈ I, ∀ w ∈ I, v ≠ w → Disjoint (buck' v) (buck' w)) →
        ∃ (seq : List ι) (buckets : ι → Finset (HPlane ι S)),
          seq.Nodup ∧
          (∀ v ∈ seq, v ∈ I) ∧
          H_star.fixed ∩ I ⊆ seq.toFinset ∧
          (∀ v ∈ seq, buckets v ⊆ A.erase H_star) ∧
          (∀ v ∈ seq, Fintype.card (S v) ≤ (buckets v).card + C) ∧
          (∀ i j : Fin seq.length, i ≠ j → Disjoint (buckets (seq.get i)) (buckets (seq.get j))) ∧
          (∀ i : Fin seq.length, ∀ H ∈ buckets (seq.get i),
            H.fixed ∩ V_big ⊆ insert (seq.get i) (W ∪ (seq.take i.val).toFinset) ∧
            (∃ a, H (seq.get i) = some a ∧ a ≠ z (seq.get i)) ∧
            (∀ u ∈ V_big, u ≠ seq.get i → H u = none ∨ H u = some (z u))) ∧
          (∀ v ∈ seq, Set.InjOn (fun H : HPlane ι S => H v) (buckets v)) by
      exact hinner (∑ v ∈ I, (rem v).card) rem buck le_rfl hzrem hbuckA hsumcard hbuckP hinjB hdisjB
    intro r
    induction r with
    | zero =>
      intro rem' buck' hr0 hz' hbuckA' hsum' hbuckP' hinj' hdisj'
      have hIe : I = ∅ := by
        by_contra hne
        obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        have hpos : 1 ≤ (rem' v).card := Finset.card_pos.mpr ⟨z v, hz' v hv⟩
        have hle := Finset.single_le_sum (f := fun u => (rem' u).card) (fun _ _ => Nat.zero_le _) hv
        omega
      refine ⟨[], fun _ => ∅, List.nodup_nil, by simp, by simp [hIe],
        by simp, by simp, fun i => Fin.elim0 i, fun i => Fin.elim0 i, by simp⟩
    | succ r ihr =>
      intro rem' buck' hr hz' hbuckA' hsum' hbuckP' hinj' hdisj'
      -- Check if there is a codimension-1 hyperplane `H ∈ A.erase H_star` intersecting the box
      by_cases hex : ∃ v ∈ I, ∃ a ∈ (rem' v).erase (z v), ∃ H ∈ A.erase H_star,
          (∀ u ∉ I, H u = none ∨ H u = some (z u)) ∧
          H.fixed ∩ I = {v} ∧ H v = some a
      · obtain ⟨v₀, hv₀I, a₀, ha₀mem, H₀, hH₀A, hH₀out, hH₀fix, hH₀v⟩ := hex
        rcases Finset.mem_erase.mp ha₀mem with ⟨ha₀ne, ha₀rem⟩
        let rem'' : (v : ι) → Finset (S v) := fun v =>
          if h : v₀ = v then h ▸ (rem' v₀).erase a₀ else rem' v
        let buck'' : ι → Finset (HPlane ι S) := fun v => if v = v₀ then insert H₀ (buck' v) else buck' v
        -- Show `H₀ ∉ buck' w` for all `w ∈ I`
        have hH₀not : ∀ w ∈ I, H₀ ∉ buck' w := by
          intro w hw hmem
          obtain ⟨⟨b, hH₀w, hbnot⟩, _, _⟩ := hbuckP' w hw H₀ hmem
          have hwfix : w ∈ H₀.fixed ∩ I := Finset.mem_inter.mpr ⟨mem_fixed_iff.mpr (by simp [hH₀w]), hw⟩
          rw [hH₀fix, Finset.mem_singleton] at hwfix
          subst hwfix
          rw [hH₀v] at hH₀w
          exact hbnot ((Option.some.inj hH₀w) ▸ ha₀rem)
        have hsum_dec : ∑ v ∈ I, (rem'' v).card ≤ r := by
          have h1 : (rem'' v₀).card + 1 = (rem' v₀).card := by
            simp only [rem'', ↓reduceDIte]
            exact Finset.card_erase_add_one ha₀rem
          have h2 : ∑ v ∈ I, (rem'' v).card + 1 = ∑ v ∈ I, (rem' v).card := by
            rw [← Finset.add_sum_erase I (fun v => (rem'' v).card) hv₀I,
                ← Finset.add_sum_erase I (fun v => (rem' v).card) hv₀I]
            have hrest : ∑ v ∈ I.erase v₀, (rem'' v).card = ∑ v ∈ I.erase v₀, (rem' v).card :=
              Finset.sum_congr rfl fun v hv => by
                have hne : v₀ ≠ v := (Finset.mem_erase.mp hv).1.symm
                simp [rem'', hne]
            rw [hrest]; omega
          omega
        refine ihr rem'' buck'' hsum_dec ?_ ?_ ?_ ?_ ?_ ?_
        · intro v hv
          dsimp only [rem'']
          split_ifs with hvv
          · subst hvv; exact Finset.mem_erase.mpr ⟨ha₀ne.symm, hz' v₀ hv⟩
          · exact hz' v hv
        · intro v hv
          dsimp only [buck'']
          split_ifs with hvv
          · exact Finset.insert_subset hH₀A (hbuckA' v hv)
          · exact hbuckA' v hv
        · intro v hv
          dsimp only [rem'', buck'']
          by_cases hvv : v₀ = v
          · subst hvv
            simp only [↓reduceDIte, ↓reduceIte]
            rw [Finset.card_insert_of_notMem (hH₀not v₀ hv)]
            have her := Finset.card_erase_add_one ha₀rem
            have h0 := hsum' v₀ hv
            omega
          · have hvv' : v ≠ v₀ := fun h => hvv h.symm
            simp only [dif_neg hvv, if_neg hvv']
            exact hsum' v hv
        · intro v hv H hH
          dsimp only [buck''] at hH
          by_cases hvv : v₀ = v
          · subst hvv
            simp only [↓reduceIte] at hH
            rcases Finset.mem_insert.mp hH with rfl | hHold
            · refine ⟨⟨a₀, hH₀v, ?_⟩, ?_, ?_⟩
              · simp [rem'']
              · intro u hu
                rcases Finset.mem_inter.mp hu with ⟨huF, huV⟩
                by_cases huW : u ∈ W
                · exact Finset.mem_insert_of_mem huW
                · have huI : u ∈ I := Finset.mem_sdiff.mpr ⟨huV, huW⟩
                  have hu1 : u ∈ H.fixed ∩ I := Finset.mem_inter.mpr ⟨huF, huI⟩
                  rw [hH₀fix, Finset.mem_singleton] at hu1
                  exact Finset.mem_insert.mpr (Or.inl hu1)
              · intro u huV huv
                by_cases huI : u ∈ I
                · left
                  apply notMem_fixed_iff.mp
                  intro huF
                  have : u ∈ H.fixed ∩ I := Finset.mem_inter.mpr ⟨huF, huI⟩
                  rw [hH₀fix, Finset.mem_singleton] at this
                  exact huv this
                · exact hH₀out u huI
            · rcases hbuckP' v₀ hv H hHold with ⟨⟨b, hHb, hbnot⟩, hfix, hout⟩
              exact ⟨⟨b, hHb, by simp [rem'', Finset.mem_erase, hbnot]⟩, hfix, hout⟩
          · have hvv' : v ≠ v₀ := fun h => hvv h.symm
            simp only [if_neg hvv'] at hH
            rcases hbuckP' v hv H hH with ⟨⟨b, hHb, hbnot⟩, hfix, hout⟩
            exact ⟨⟨b, hHb, by simp [rem'', hvv, hbnot]⟩, hfix, hout⟩
        · intro v hv
          dsimp only [buck'']
          split_ifs with hvv
          · subst hvv
            intro H₁ hH₁ H₂ hH₂ heq
            dsimp only at heq
            rcases Finset.mem_insert.mp hH₁ with rfl | h1 <;>
            rcases Finset.mem_insert.mp hH₂ with rfl | h2
            · rfl
            · rcases hbuckP' v hv H₂ h2 with ⟨⟨b, hH₂v, hbnot⟩, _, _⟩
              rw [hH₀v, hH₂v] at heq
              exact absurd ((Option.some.inj heq) ▸ ha₀rem) hbnot
            · rcases hbuckP' v hv H₁ h1 with ⟨⟨b, hH₁v, hbnot⟩, _, _⟩
              rw [hH₁v, hH₀v] at heq
              exact absurd ((Option.some.inj heq.symm) ▸ ha₀rem) hbnot
            · exact hinj' v hv h1 h2 heq
          · exact hinj' v hv
        · intro v hv w hw hvw
          dsimp only [buck'']
          by_cases h1 : v = v₀ <;> by_cases h2 : w = v₀
          · exact absurd (h1.trans h2.symm) hvw
          · subst h1
            simp only [↓reduceIte, if_neg h2]
            rw [Finset.disjoint_insert_left]
            exact ⟨hH₀not w hw, hdisj' v hv w hw hvw⟩
          · subst h2
            simp only [if_neg h1, ↓reduceIte]
            rw [Finset.disjoint_insert_right]
            exact ⟨hH₀not v hv, hdisj' v hv w hw hvw⟩
          · simp only [if_neg h1, if_neg h2]
            exact hdisj' v hv w hw hvw
      · -- Inner shrinking stopped! Either `H_star.fixed ∩ I = ∅` (done) or some `v* ∈ I` has `(rem' v*).card ≤ C`.
        by_cases hdone : H_star.fixed ∩ I = ∅
        · refine ⟨[], fun _ => ∅, List.nodup_nil, by simp, by simp [hdone],
            by simp, by simp, fun i => Fin.elim0 i, fun i => Fin.elim0 i, by simp⟩
        · -- Show `∃ v* ∈ I, (rem' v*).card ≤ C`
          have hex_small : ∃ v ∈ I, (rem' v).card ≤ C := by
            by_contra hall
            push Not at hall
            -- Every `v ∈ I` has `C < (rem' v).card`, so `C - 1 ≤ ((rem' v).erase (z v)).card`.
            let A_minus : (v : ι) → Finset (S v) := fun v => (rem' v).erase (z v)
            have hAm_ge : ∀ v ∈ I, C - 1 ≤ (A_minus v).card := by
              intro v hv
              have h1 := hall v hv
              have h2 := Finset.card_erase_add_one (hz' v hv)
              dsimp only [A_minus]; omega
            let B_minus := Finset.univ.filter fun x : (i : ι) → S i =>
              (∀ u ∉ I, x u = z u) ∧ (∀ u ∈ I, x u ∈ A_minus u)
            have hBm_pos : 0 < B_minus.card := by
              rw [card_box_eq_prod]
              refine Finset.prod_pos fun v hv => ?_
              have := hAm_ge v hv; omega
            -- `H_star` is disjoint from `B_minus` because `H_star.fixed ∩ I ≠ ∅`
            obtain ⟨u₀, hu₀⟩ := Finset.nonempty_iff_ne_empty.mpr hdone
            rcases Finset.mem_inter.mp hu₀ with ⟨hu₀F, hu₀I⟩
            obtain ⟨b₀, hb₀⟩ := Option.isSome_iff_exists.mp (mem_fixed_iff.mp hu₀F)
            have hb₀z : b₀ = z u₀ := (hzH u₀ b₀ hb₀).symm
            have hHs_disj : ∀ x ∈ B_minus, ¬ H_star.mem x := by
              intro x hx hmem
              have hx_u₀ := hmem u₀ b₀ hb₀
              have hmemA := (Finset.mem_filter.mp hx).2.2 u₀ hu₀I
              exact (Finset.mem_erase.mp hmemA).1 (hx_u₀.trans hb₀z)
            -- Hence `A.erase H_star` covers `B_minus`
            have hcov_Bm : B_minus ⊆ (A.erase H_star).biUnion fun H => B_minus.filter H.mem := by
              intro x hx
              obtain ⟨H, hHA, hHmem⟩ := hA.1 x
              have hne : H ≠ H_star := fun h => hHs_disj x hx (h ▸ hHmem)
              exact Finset.mem_biUnion.mpr ⟨H, Finset.mem_erase.mpr ⟨hne, hHA⟩,
                Finset.mem_filter.mpr ⟨hx, hHmem⟩⟩
            -- Every `H ∈ A.erase H_star` intersecting `B_minus` has `2 ≤ (H.fixed ∩ I).card`
            have hcard_mul : ∀ H ∈ A.erase H_star, (B_minus.filter H.mem).card * (C - 1) ^ 2 ≤ B_minus.card := by
              intro H hHA
              by_cases hne : (B_minus.filter H.mem).Nonempty
              · obtain ⟨x, hx⟩ := hne
                rcases Finset.mem_filter.mp hx with ⟨hxB, hxH⟩
                rcases Finset.mem_filter.mp hxB with ⟨_, hxout, hxin⟩
                have hHout : ∀ u ∉ I, H u = none ∨ H u = some (z u) := by
                  intro u hu
                  cases hHu : H u with
                  | none => exact Or.inl rfl
                  | some b => exact Or.inr (congrArg some ((hxH u b hHu).symm.trans (hxout u hu)))
                have h2 : 2 ≤ (H.fixed ∩ I).card := by
                  by_contra hlt2
                  have hle1 : (H.fixed ∩ I).card ≤ 1 := by omega
                  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle1 with h0 | h1
                  · -- `H.fixed ∩ I = ∅` implies `H.mem z`, contradicting `hzpriv`!
                    have hempty : H.fixed ∩ I = ∅ := Finset.card_eq_zero.mp h0
                    have hHz : H.mem z := by
                      intro u b hHu
                      by_cases huI : u ∈ I
                      · exfalso
                        have : u ∈ H.fixed ∩ I := Finset.mem_inter.mpr ⟨mem_fixed_iff.mpr (by simp [hHu]), huI⟩
                        rw [hempty] at this; exact Finset.notMem_empty _ this
                      · rcases hHout u huI with hnone | hsome
                        · simp [hnone] at hHu
                        · rw [hHu] at hsome; exact (Option.some.inj hsome).symm
                    rcases Finset.mem_erase.mp hHA with ⟨hneH, hHAmem⟩
                    exact hzpriv H hHAmem hneH hHz
                  · -- `(H.fixed ∩ I).card = 1` contradicts `¬ hex`!
                    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h1
                    have hvmem : v ∈ H.fixed ∩ I := by rw [hv]; exact Finset.mem_singleton_self v
                    rcases Finset.mem_inter.mp hvmem with ⟨hvF, hvI⟩
                    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (mem_fixed_iff.mp hvF)
                    have hxa : x v = a := hxH v a ha
                    have hamem : a ∈ (rem' v).erase (z v) := hxa ▸ hxin v hvI
                    exact hex ⟨v, hvI, a, hamem, H, hHA, hHout, hv, ha⟩
                exact card_hplane_inter_box_mul_sq_le I z A_minus hAm_ge h2
              · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, zero_mul]
                exact Nat.zero_le _
            have htot : B_minus.card * (C - 1) ^ 2 ≤ A.card * B_minus.card := by
              calc B_minus.card * (C - 1) ^ 2
                  ≤ ((A.erase H_star).biUnion fun H => B_minus.filter H.mem).card * (C - 1) ^ 2 :=
                    Nat.mul_le_mul_right _ (Finset.card_le_card hcov_Bm)
                _ ≤ (∑ H ∈ A.erase H_star, (B_minus.filter H.mem).card) * (C - 1) ^ 2 :=
                    Nat.mul_le_mul_right _ Finset.card_biUnion_le
                _ = ∑ H ∈ A.erase H_star, ((B_minus.filter H.mem).card * (C - 1) ^ 2) :=
                    Finset.sum_mul _ _ _
                _ ≤ ∑ _H ∈ A.erase H_star, B_minus.card := Finset.sum_le_sum hcard_mul
                _ = (A.erase H_star).card * B_minus.card := by rw [Finset.sum_const, smul_eq_mul]
                _ ≤ A.card * B_minus.card := Nat.mul_le_mul_right _ (Finset.card_erase_le)
            have hle : (C - 1) ^ 2 ≤ A.card :=
              Nat.le_of_mul_le_mul_right (by simpa [mul_comm] using htot) hBm_pos
            omega
          -- Pick `v* ∈ I` with `(rem' v*).card ≤ C` and move `v*` into `W`!
          obtain ⟨v_star, hv_starI, hrem_leC⟩ := hex_small
          have hv_starV : v_star ∈ V_big := (Finset.mem_sdiff.mp hv_starI).1
          have hv_starW : v_star ∉ W := (Finset.mem_sdiff.mp hv_starI).2
          have hW'V : insert v_star W ⊆ V_big := Finset.insert_subset hv_starV hWV
          have hI'_eq : V_big \ insert v_star W = I.erase v_star := by
            ext u; simp [I, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]; tauto
          have hI'card : (V_big \ insert v_star W).card ≤ m := by
            rw [hI'_eq]
            have := Finset.card_erase_of_mem hv_starI; omega
          -- Apply outer IH `ihm` to `insert v_star W`!
          obtain ⟨seq', buckets', hnod', hsub', hcov', hbuckA_rec, hcard_rec, hdisj_rec, hprop_rec, hinj_rec⟩ :=
            ihm (insert v_star W) rem' buck' hW'V hI'card
              (fun v hv => hz' v (by rw [hI'_eq] at hv; exact Finset.mem_of_mem_erase hv))
              (fun v hv => hbuckA' v (by rw [hI'_eq] at hv; exact Finset.mem_of_mem_erase hv))
              (fun v hv => hsum' v (by rw [hI'_eq] at hv; exact Finset.mem_of_mem_erase hv))
              (fun v hv H hH => by
                have hvI : v ∈ I := by rw [hI'_eq] at hv; exact Finset.mem_of_mem_erase hv
                rcases hbuckP' v hvI H hH with ⟨ha, hfix, hout⟩
                exact ⟨ha, hfix.trans (Finset.insert_subset_insert v (Finset.subset_insert v_star W)), hout⟩)
              (fun v hv => hinj' v (by rw [hI'_eq] at hv; exact Finset.mem_of_mem_erase hv))
              (fun v hv w hw hne => hdisj' v (by rw [hI'_eq] at hv; exact Finset.mem_of_mem_erase hv)
                w (by rw [hI'_eq] at hw; exact Finset.mem_of_mem_erase hw) hne)
          -- Prepend `v_star` with bucket `buck' v_star`!
          have hv_not_seq' : v_star ∉ seq' := fun h => by
            have := hsub' v_star h
            rw [hI'_eq] at this
            exact (Finset.mem_erase.mp this).1 rfl
          let buckets_fin : ι → Finset (HPlane ι S) := fun v =>
            if v = v_star then buck' v_star else buckets' v
          refine ⟨v_star :: seq', buckets_fin,
            List.nodup_cons.mpr ⟨hv_not_seq', hnod'⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro v hv
            rcases List.mem_cons.mp hv with rfl | hv'
            · exact hv_starI
            · have := hsub' v hv'; rw [hI'_eq] at this; exact Finset.mem_of_mem_erase this
          · intro v hv
            rcases Finset.mem_inter.mp hv with ⟨hvF, hvI⟩
            by_cases hveq : v = v_star
            · subst hveq; simp
            · have hvI' : v ∈ V_big \ insert v_star W := by
                rw [hI'_eq]; exact Finset.mem_erase.mpr ⟨hveq, hvI⟩
              have := hcov' (Finset.mem_inter.mpr ⟨hvF, hvI'⟩)
              simp only [List.toFinset_cons, Finset.mem_insert]
              exact Or.inr this
          · intro v hv
            dsimp only [buckets_fin]
            split_ifs with hveq
            · subst hveq; exact hbuckA' v hv_starI
            · rcases List.mem_cons.mp hv with rfl | hv'
              · exact absurd rfl hveq
              · exact hbuckA_rec v hv'
          · intro v hv
            dsimp only [buckets_fin]
            split_ifs with hveq
            · subst hveq
              have := hsum' v hv_starI; omega
            · rcases List.mem_cons.mp hv with rfl | hv'
              · exact absurd rfl hveq
              · exact hcard_rec v hv'
          · intro i j hij
            cases i using Fin.cases with
            | zero =>
              cases j using Fin.cases with
              | zero => exact absurd rfl hij
              | succ j' =>
                simp only [List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero,
                  Fin.val_succ, List.getElem_cons_succ, buckets_fin, ↓reduceIte]
                have hne' : seq'[j'.val] ≠ v_star := fun h => hv_not_seq' (h ▸ List.getElem_mem j'.isLt)
                rw [if_neg hne']
                -- Every `H ∈ buck' v_star` has `H v_star = some a` with `a ≠ z v_star`,
                -- whereas every `H ∈ buckets' (seq'[j'])` has `H v_star = none ∨ H v_star = some (z v_star)`!
                rw [Finset.disjoint_left]
                intro H hH1 hH2
                rcases hbuckP' v_star hv_starI H hH1 with ⟨⟨a, hHa, hanot⟩, _, _⟩
                have haz : a ≠ z v_star := fun h => hanot (h ▸ hz' v_star hv_starI)
                rcases hprop_rec ⟨j'.val, j'.isLt⟩ H hH2 with ⟨_, _, hout⟩
                rcases hout v_star hv_starV hne'.symm with hnone | hsome
                · simp [hnone] at hHa
                · rw [hHa] at hsome; exact haz (Option.some.inj hsome)
            | succ i' =>
              cases j using Fin.cases with
              | zero =>
                simp only [List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero,
                  Fin.val_succ, List.getElem_cons_succ, buckets_fin, ↓reduceIte]
                have hne' : seq'[i'.val] ≠ v_star := fun h => hv_not_seq' (h ▸ List.getElem_mem i'.isLt)
                rw [if_neg hne']
                rw [Finset.disjoint_right]
                intro H hH1 hH2
                rcases hbuckP' v_star hv_starI H hH1 with ⟨⟨a, hHa, hanot⟩, _, _⟩
                have haz : a ≠ z v_star := fun h => hanot (h ▸ hz' v_star hv_starI)
                rcases hprop_rec ⟨i'.val, i'.isLt⟩ H hH2 with ⟨_, _, hout⟩
                rcases hout v_star hv_starV hne'.symm with hnone | hsome
                · simp [hnone] at hHa
                · rw [hHa] at hsome; exact haz (Option.some.inj hsome)
              | succ j' =>
                simp only [List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ, buckets_fin]
                have hnei : seq'[i'.val] ≠ v_star := fun h => hv_not_seq' (h ▸ List.getElem_mem i'.isLt)
                have hnej : seq'[j'.val] ≠ v_star := fun h => hv_not_seq' (h ▸ List.getElem_mem j'.isLt)
                rw [if_neg hnei, if_neg hnej]
                exact hdisj_rec ⟨i'.val, i'.isLt⟩ ⟨j'.val, j'.isLt⟩ (fun h => hij (by
                  apply Fin.ext; exact congrArg (· + 1) (congrArg Fin.val h)))
          · intro i H hH
            cases i using Fin.cases with
            | zero =>
              simp only [List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero,
                buckets_fin, ↓reduceIte, List.take_zero, List.toFinset_nil, Finset.union_empty] at hH ⊢
              rcases hbuckP' v_star hv_starI H hH with ⟨⟨a, hHa, hanot⟩, hfix, hout⟩
              exact ⟨hfix, ⟨a, hHa, fun h => hanot (h ▸ hz' v_star hv_starI)⟩, hout⟩
            | succ i' =>
              simp only [List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ, buckets_fin] at hH ⊢
              have hnei : seq'[i'.val] ≠ v_star := fun h => hv_not_seq' (h ▸ List.getElem_mem i'.isLt)
              rw [if_neg hnei] at hH
              rcases hprop_rec ⟨i'.val, i'.isLt⟩ H hH with ⟨hfix, hsome, hout⟩
              refine ⟨?_, hsome, hout⟩
              have htake : W ∪ ((v_star :: seq').take (i'.val + 1)).toFinset =
                  insert v_star W ∪ (seq'.take i'.val).toFinset := by
                ext u; simp [List.take_succ_cons, Finset.mem_union, Finset.mem_insert]
              rw [htake]; exact hfix
          · intro v hv
            dsimp only [buckets_fin]
            split_ifs with hveq
            · subst hveq; exact hinj' v hv_starI
            · rcases List.mem_cons.mp hv with rfl | hv'
              · exact absurd rfl hveq
              · exact hinj_rec v hv'

/-- Deterministic slot-budget expansion of a single round `(seq, cnts)`:
for each `i < seq.length`, outputs `cnts[i]` copies of `((seq.take i).toFinset, some seq[i])`,
followed by one copy of `(seq.toFinset, none)` for the anchor. -/
def roundSlots {ι : Type*} [DecidableEq ι] (seq : List ι) (cnts : List ℕ) :
    List (Finset ι × Option ι) :=
  ((List.range seq.length).flatMap fun i =>
    if h : i < seq.length then
      List.replicate (cnts.getD i 0) ((seq.take i).toFinset, some (seq[i]'h))
    else []) ++ [(seq.toFinset, none)]

/-- Deterministic slot-budget expansion of all rounds plus the stopped tail. -/
def allSlots {ι : Type*} [DecidableEq ι] (roundSpecs : List (List ι × List ℕ))
    (W_all : Finset ι) (tailLen : ℕ) : List (Finset ι × Option ι) :=
  (roundSpecs.flatMap fun p => roundSlots p.1 p.2) ++ List.replicate tailLen (W_all, none)

/-- Allowed big-coordinate set for a slot `(W, extra)`. -/
def slotAllowed {ι : Type*} [DecidableEq ι] (sl : Finset ι × Option ι) : Finset ι :=
  match sl.2 with
  | some v => insert v sl.1
  | none => sl.1

/-- Total number of hyperplanes revealed in one round spec `(seq, cnts)`. -/
def roundSize {ι : Type*} (p : List ι × List ℕ) : ℕ :=
  ((List.range p.1.length).map fun i => p.2.getD i 0).sum + 1

lemma roundSlots_length {ι : Type*} [DecidableEq ι] (seq : List ι) (cnts : List ℕ) :
    (roundSlots seq cnts).length = roundSize (seq, cnts) := by
  unfold roundSlots roundSize
  rw [List.length_append, List.length_singleton, List.length_flatMap]
  congr 1
  refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
  have hi' : i < seq.length := List.mem_range.mp hi
  simp [hi']

lemma allSlots_length {ι : Type*} [DecidableEq ι] (roundSpecs : List (List ι × List ℕ))
    (W_all : Finset ι) (tailLen : ℕ) :
    (allSlots roundSpecs W_all tailLen).length = (roundSpecs.map roundSize).sum + tailLen := by
  unfold allSlots
  rw [List.length_append, List.length_replicate, List.length_flatMap]
  congr 1
  refine congrArg List.sum (List.map_congr_left fun p _ => roundSlots_length p.1 p.2)

/-- Helper: given a single extraction round `(seq, buckets, H_star)` and currently revealed `R ⊆ A`,
build the ordered list of newly revealed hyperplanes `newList` matching `roundSlots seq cnts`! -/
lemma build_round_list {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    {A R : Finset (HPlane ι S)} (hRA : R ⊆ A) (V_big : Finset ι) {C : ℕ}
    {H_star : HPlane ι S} (hHsA : H_star ∈ A) (hHsNotR : H_star ∉ R)
    (seq : List ι) (buckets : ι → Finset (HPlane ι S))
    (hnod : seq.Nodup)
    (hseqV : ∀ v ∈ seq, v ∈ V_big)
    (hHs_fix : H_star.fixed ∩ V_big ⊆ seq.toFinset)
    (hbuckA : ∀ v ∈ seq, buckets v ⊆ A.erase H_star)
    (hbuck_card : ∀ v ∈ seq, Fintype.card (S v) ≤ (buckets v).card + C)
    (hdisj : ∀ i j : Fin seq.length, i ≠ j → Disjoint (buckets (seq.get i)) (buckets (seq.get j)))
    (hprop : ∀ i : Fin seq.length, ∀ H ∈ buckets (seq.get i),
      H.fixed ∩ V_big ⊆ insert (seq.get i) (seq.take i.val).toFinset) :
    let cnts : List ℕ := (List.range seq.length).map fun i =>
      if h : i < seq.length then (buckets (seq[i]'h) \ R).card else 0
    let R_new : Finset (HPlane ι S) := R ∪ seq.toFinset.biUnion buckets ∪ {H_star}
    ∃ newList : List (HPlane ι S),
      newList.Nodup ∧
      newList.length = roundSize (seq, cnts) ∧
      (∀ H ∈ newList, H ∈ R_new \ R) ∧
      (∀ H ∈ R_new \ R, H ∈ newList) ∧
      R_new ⊆ A ∧
      R_new.card = R.card + newList.length ∧
      (∀ t (ht : t < newList.length) (hsl : t < (roundSlots seq cnts).length),
        let sl := (roundSlots seq cnts)[t]'hsl
        (newList[t]'ht).fixed ∩ V_big ⊆ slotAllowed sl ∧
        ∑ v ∈ sl.1, Fintype.card (S v) ≤ R.card + t + V_big.card * C) := by
  intro cnts R_new
  -- Build the bucket lists for each `i < seq.length`
  let buckList : ℕ → List (HPlane ι S) := fun i =>
    if h : i < seq.length then (buckets (seq[i]'h) \ R).toList else []
  let prefList : List (HPlane ι S) := (List.range seq.length).flatMap buckList
  let newList : List (HPlane ι S) := prefList ++ [H_star]
  have hcnts_getD : ∀ i (hi : i < seq.length), cnts.getD i 0 = (buckets (seq[i]'hi) \ R).card := by
    intro i hi
    have hlen : i < cnts.length := by simp [cnts, hi]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
    simp [cnts, hi]
  have hbuckList_len : ∀ i < seq.length, (buckList i).length = cnts.getD i 0 := by
    intro i hi
    rw [hcnts_getD i hi]
    simp [buckList, hi]
  have hnew_len : newList.length = roundSize (seq, cnts) := by
    simp only [newList, prefList, roundSize, List.length_append, List.length_singleton, List.length_flatMap]
    congr 1
    refine congrArg List.sum (List.map_congr_left fun i hi => hbuckList_len i (List.mem_range.mp hi))
  have hdisj_buckList : ∀ i j : ℕ, i < seq.length → j < seq.length → i ≠ j →
      ∀ H, H ∈ buckList i → H ∉ buckList j := by
    intro i j hi hj hij H h1 h2
    simp only [buckList, hi, hj, ↓reduceDIte, Finset.mem_toList, Finset.mem_sdiff] at h1 h2
    exact Finset.disjoint_left.mp (hdisj ⟨i, hi⟩ ⟨j, hj⟩ (fun h => hij (congrArg Fin.val h))) h1.1 h2.1
  have hpref_nodup : prefList.Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun i hi => ?_, ?_⟩
    · have hi' : i < seq.length := List.mem_range.mp hi
      simp [buckList, hi', Finset.nodup_toList]
    · refine List.nodup_range.imp_of_mem ?_
      intro i j hi hj hij
      exact List.disjoint_left.mpr fun H h1 h2 =>
        hdisj_buckList i j (List.mem_range.mp hi) (List.mem_range.mp hj) hij H h1 h2
  have hHs_not_pref : H_star ∉ prefList := by
    intro hmem
    rw [List.mem_flatMap] at hmem
    obtain ⟨i, hi, hHi⟩ := hmem
    have hi' : i < seq.length := List.mem_range.mp hi
    simp only [buckList, hi', ↓reduceDIte, Finset.mem_toList, Finset.mem_sdiff] at hHi
    exact (Finset.mem_erase.mp (hbuckA (seq[i]'hi') (List.getElem_mem hi') hHi.1)).1 rfl
  have hnew_nodup : newList.Nodup := by
    rw [List.nodup_append]
    refine ⟨hpref_nodup, List.nodup_singleton _, ?_⟩
    intro H1 hH1 H2 hH2 heq
    rw [heq, List.mem_singleton.mp hH2] at hH1
    exact hHs_not_pref hH1
  have hmem_iff : ∀ H, H ∈ newList ↔ H ∈ R_new \ R := by
    intro H
    simp only [newList, prefList, R_new, List.mem_append, List.mem_flatMap, List.mem_range,
      List.mem_singleton, Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion,
      List.mem_toFinset, Finset.mem_singleton]
    constructor
    · rintro (⟨i, hi, hHi⟩ | rfl)
      · simp only [buckList, hi, ↓reduceDIte, Finset.mem_toList, Finset.mem_sdiff] at hHi
        exact ⟨Or.inl (Or.inr ⟨seq[i]'hi, List.getElem_mem hi, hHi.1⟩), hHi.2⟩
      · exact ⟨Or.inr rfl, hHsNotR⟩
    · rintro ⟨(hR | ⟨v, hv, hHv⟩) | rfl, hnotR⟩
      · exact absurd hR hnotR
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
        exact Or.inl ⟨i, hi, by simp [buckList, hi, hHv, hnotR]⟩
      · exact Or.inr rfl
  have hRnew_sub : R_new ⊆ A := by
    intro H hH
    simp only [R_new, Finset.mem_union, Finset.mem_biUnion, List.mem_toFinset,
      Finset.mem_singleton] at hH
    rcases hH with (hR | ⟨v, hv, hHv⟩) | rfl
    · exact hRA hR
    · exact Finset.mem_of_mem_erase (hbuckA v hv hHv)
    · exact hHsA
  have hcard_Rnew : R_new.card = R.card + newList.length := by
    have hRsub : R ⊆ R_new := Finset.subset_union_left.trans Finset.subset_union_left
    have h1 := Finset.card_sdiff_add_card_eq_card hRsub
    have h2 : newList.toFinset = R_new \ R := by
      ext H; rw [List.mem_toFinset, hmem_iff]
    have h3 : (R_new \ R).card = newList.length := by
      rw [← h2, List.toFinset_card_of_nodup hnew_nodup]
    omega
  -- Prove the slot-by-slot invariant!
  -- First, for any prefix `i ≤ seq.length`, bound `∑ v ∈ (seq.take i).toFinset, |S v|`!
  have hpref_cost : ∀ i ≤ seq.length,
      ∑ v ∈ (seq.take i).toFinset, Fintype.card (S v) ≤
        R.card + ((List.range i).map fun j => (buckList j).length).sum + V_big.card * C := by
    intro i hi
    have htake_nodup : (seq.take i).Nodup := hnod.sublist (List.take_sublist i seq)
    have htake_sub : (seq.take i).toFinset ⊆ V_big := fun v hv =>
      hseqV v (List.mem_of_mem_take (List.mem_toFinset.mp hv))
    have htake_card : (seq.take i).toFinset.card ≤ V_big.card := Finset.card_le_card htake_sub
    have hsum1 : ∑ v ∈ (seq.take i).toFinset, Fintype.card (S v) ≤
        (∑ v ∈ (seq.take i).toFinset, (buckets v).card) + (seq.take i).toFinset.card * C := by
      calc ∑ v ∈ (seq.take i).toFinset, Fintype.card (S v)
          ≤ ∑ v ∈ (seq.take i).toFinset, ((buckets v).card + C) :=
            Finset.sum_le_sum fun v hv => hbuck_card v (List.mem_of_mem_take (List.mem_toFinset.mp hv))
        _ = (∑ v ∈ (seq.take i).toFinset, (buckets v).card) + (seq.take i).toFinset.card * C := by
            rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
    -- Split each `buckets v` into `(buckets v ∩ R) ∪ (buckets v \ R)`!
    have hdisj_take : ((seq.take i).toFinset : Set ι).PairwiseDisjoint buckets := by
      intro u hu v hv huv
      obtain ⟨iu, hiu, rfl⟩ := List.getElem_of_mem (List.mem_of_mem_take (List.mem_toFinset.mp hu))
      obtain ⟨iv, hiv, rfl⟩ := List.getElem_of_mem (List.mem_of_mem_take (List.mem_toFinset.mp hv))
      exact hdisj ⟨iu, hiu⟩ ⟨iv, hiv⟩ (fun h => huv (by
        have hval : iu = iv := congrArg Fin.val h
        subst hval; rfl))
    have hsum_R : ∑ v ∈ (seq.take i).toFinset, (buckets v ∩ R).card ≤ R.card := by
      rw [← Finset.card_biUnion (fun u hu v hv huv =>
        (hdisj_take hu hv huv).mono Finset.inter_subset_left Finset.inter_subset_left)]
      exact Finset.card_le_card (Finset.biUnion_subset.mpr fun _ _ => Finset.inter_subset_right)
    have hsum_new : ∑ v ∈ (seq.take i).toFinset, (buckets v \ R).card =
        ((List.range i).map fun j => (buckList j).length).sum := by
      rw [List.sum_toFinset _ htake_nodup]
      have hmap : (seq.take i).map (fun v => (buckets v \ R).card) =
          (List.range i).map fun j => (buckList j).length := by
        refine List.ext_getElem ?_ ?_
        · simp [hi]
        · intro j hj1 hj2
          have hj_i : j < i := by simpa using hj2
          have hj_len : j < seq.length := lt_of_lt_of_le hj_i hi
          simp [List.getElem_take, buckList, hj_len]
      rw [hmap]
    have hsplit : ∑ v ∈ (seq.take i).toFinset, (buckets v).card =
        (∑ v ∈ (seq.take i).toFinset, (buckets v ∩ R).card) +
        (∑ v ∈ (seq.take i).toFinset, (buckets v \ R).card) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      exact (Finset.card_inter_add_card_sdiff (buckets v) R).symm
    have hmulC : (seq.take i).toFinset.card * C ≤ V_big.card * C := Nat.mul_le_mul_right C htake_card
    omega
  -- Match each index `t < newList.length` with its corresponding slot in `roundSlots seq cnts`
  have hslot_match : ∀ t (ht : t < newList.length) (hsl : t < (roundSlots seq cnts).length),
      let sl := (roundSlots seq cnts)[t]'hsl
      (newList[t]'ht).fixed ∩ V_big ⊆ slotAllowed sl ∧
      ∑ v ∈ sl.1, Fintype.card (S v) ≤ R.card + t + V_big.card * C := by
    intro t ht hsl
    by_cases ht_pref : t < prefList.length
    · -- `t` falls inside `prefList = (List.range seq.length).flatMap buckList`
      have hflat : ∀ (n : ℕ) (hn : n ≤ seq.length),
          ∀ t (ht1 : t < ((List.range n).flatMap buckList).length),
          let S_n := (List.range n).flatMap fun i =>
            if h : i < seq.length then
              List.replicate (cnts.getD i 0) ((seq.take i).toFinset, some (seq[i]'h))
            else []
          ∃ (i : ℕ) (hi : i < n),
            ((List.range i).map fun j => (buckList j).length).sum ≤ t ∧
            (((List.range n).flatMap buckList)[t]'ht1) ∈ buckList i ∧
            (S_n[t]'(by
              have hlen : S_n.length = ((List.range n).flatMap buckList).length := by
                simp only [S_n, List.length_flatMap]
                refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
                have hj' : j < seq.length := lt_of_lt_of_le (List.mem_range.mp hj) hn
                simp [hj', hbuckList_len j hj']
              rw [hlen]; exact ht1)) = ((seq.take i).toFinset, some (seq[i]'(lt_of_lt_of_le hi hn))) := by
        intro n
        induction n with
        | zero => intro _ t ht1; simp at ht1
        | succ n ihn =>
          intro hn t ht1
          have hn' : n < seq.length := hn
          have hL_eq : (List.range (n + 1)).flatMap buckList =
              ((List.range n).flatMap buckList) ++ buckList n := by
            rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
          have hS_eq : ((List.range (n + 1)).flatMap fun i =>
                if h : i < seq.length then
                  List.replicate (cnts.getD i 0) ((seq.take i).toFinset, some (seq[i]'h))
                else []) =
              ((List.range n).flatMap fun i =>
                if h : i < seq.length then
                  List.replicate (cnts.getD i 0) ((seq.take i).toFinset, some (seq[i]'h))
                else []) ++ List.replicate (cnts.getD n 0) ((seq.take n).toFinset, some (seq[n]'hn')) := by
            rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, dif_pos hn']
          have hlen_n : ((List.range n).flatMap fun i =>
                if h : i < seq.length then
                  List.replicate (cnts.getD i 0) ((seq.take i).toFinset, some (seq[i]'h))
                else []).length = ((List.range n).flatMap buckList).length := by
            simp only [List.length_flatMap]
            refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
            have hj' : j < seq.length := lt_of_lt_of_le (List.mem_range.mp hj) (by omega)
            simp [hj', hbuckList_len j hj']
          by_cases hlt : t < ((List.range n).flatMap buckList).length
          · obtain ⟨i, hi, hsum, hmem, hslot⟩ := ihn (by omega) t hlt
            refine ⟨i, by omega, hsum, ?_, ?_⟩
            · simp only [hL_eq, List.getElem_append_left hlt]; exact hmem
            · have hltS : t < ((List.range n).flatMap fun i =>
                  if h : i < seq.length then
                    List.replicate (cnts.getD i 0) ((seq.take i).toFinset, some (seq[i]'h))
                  else []).length := by omega
              simp only [hS_eq]
              rw [List.getElem_append_left hltS]
              exact hslot
          · refine ⟨n, Nat.lt_succ_self n, ?_, ?_, ?_⟩
            · rw [← List.length_flatMap]; omega
            · have hgeL : ((List.range n).flatMap buckList).length ≤ t := by omega
              have hlt2 : t - ((List.range n).flatMap buckList).length < (buckList n).length := by
                rw [hL_eq, List.length_append] at ht1; omega
              simp only [hL_eq]
              rw [List.getElem_append_right hgeL]
              exact List.getElem_mem hlt2
            · have hgeS : ((List.range n).flatMap fun i =>
                  if h : i < seq.length then
                    List.replicate (cnts.getD i 0) ((seq.take i).toFinset, some (seq[i]'h))
                  else []).length ≤ t := by omega
              simp only [hS_eq]
              rw [List.getElem_append_right hgeS]
              exact List.getElem_replicate _
      obtain ⟨i, hi, hsum_le, hmem_bi, hslot_eq⟩ := hflat seq.length le_rfl t ht_pref
      have hnew_eq : newList[t]'ht = prefList[t]'ht_pref := List.getElem_append_left ht_pref
      have hSlen : ((List.range seq.length).flatMap fun i =>
            if h : i < seq.length then
              List.replicate (cnts.getD i 0) ((seq.take i).toFinset, some (seq[i]'h))
            else []).length = prefList.length := by
        simp only [prefList, List.length_flatMap]
        refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
        have hj' : j < seq.length := List.mem_range.mp hj
        simp [hj', hbuckList_len j hj']
      have hround_eq : (roundSlots seq cnts)[t]'hsl =
          ((seq.take i).toFinset, some (seq[i]'hi)) := by
        unfold roundSlots at hsl ⊢
        have hltS : t < ((List.range seq.length).flatMap fun i =>
            if h : i < seq.length then
              List.replicate (cnts.getD i 0) ((seq.take i).toFinset, some (seq[i]'h))
            else []).length := by omega
        rw [List.getElem_append_left hltS]
        exact hslot_eq
      dsimp only
      rw [hround_eq, hnew_eq]
      simp only [buckList, hi, ↓reduceDIte, Finset.mem_toList, Finset.mem_sdiff] at hmem_bi
      refine ⟨hprop ⟨i, hi⟩ _ hmem_bi.1, ?_⟩
      dsimp only
      have hc := hpref_cost i hi.le
      omega
    · -- `t = prefList.length`, the anchor `H_star`!
      have ht_eq : t = prefList.length := by
        simp only [newList, List.length_append, List.length_singleton] at ht; omega
      have hnew_eq : newList[t]'ht = H_star := by
        simp only [newList, List.getElem_append_right (by omega : prefList.length ≤ t)]
        have hzero : t - prefList.length = 0 := by omega
        simp [hzero]
      have hSlen : ((List.range seq.length).flatMap fun i =>
            if h : i < seq.length then
              List.replicate (cnts.getD i 0) ((seq.take i).toFinset, some (seq[i]'h))
            else []).length = prefList.length := by
        simp only [prefList, List.length_flatMap]
        refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
        have hj' : j < seq.length := List.mem_range.mp hj
        simp [hj', hbuckList_len j hj']
      have hround_eq : (roundSlots seq cnts)[t]'hsl = (seq.toFinset, none) := by
        unfold roundSlots at hsl ⊢
        have hgeS : ((List.range seq.length).flatMap fun i =>
            if h : i < seq.length then
              List.replicate (cnts.getD i 0) ((seq.take i).toFinset, some (seq[i]'h))
            else []).length ≤ t := by omega
        rw [List.getElem_append_right hgeS]
        simp
      dsimp only
      rw [hround_eq, hnew_eq]
      refine ⟨hHs_fix, ?_⟩
      dsimp only
      have hc := hpref_cost seq.length le_rfl
      have htake_all : seq.take seq.length = seq := List.take_length
      have hsum_all : ((List.range seq.length).map fun j => (buckList j).length).sum = prefList.length := by
        simp [prefList, List.length_flatMap]
      rw [htake_all, hsum_all] at hc
      omega
  exact ⟨newList, hnew_nodup, hnew_len, fun H hH => (hmem_iff H).mp hH, fun H hH => (hmem_iff H).mpr hH,
    hRnew_sub, hcard_Rnew, hslot_match⟩

/-- **Iterated Round Decomposition** (Complete Flat-Slot Form):
Given a minimal hyperplane cover `A` of size `k`, big coordinates `V_big`, `2 ≤ C` with `k < (C - 1)^2`,
and round threshold `K ≥ 1`, produces `(roundSpecs, R_card, W_all, ordA)` such that:
1. `roundSpecs.length * K ≤ R_card` and `R_card = (roundSpecs.map roundSize).sum ≤ A.card`,
2. every `(seq, cnts) ∈ roundSpecs` has `seq.Nodup`, `∀ v ∈ seq, v ∈ V_big`, `cnts.length = seq.length`,
   and `∀ c ∈ cnts, c ≤ A.card`,
3. `W_all ⊆ V_big`,
4. `ordA : List (HPlane ι S)` has `ordA.Nodup`, `ordA.length = A.card`, `ordA.toFinset = A`,
5. for every `t < A.card`, letting `sl := (allSlots roundSpecs W_all (A.card - R_card))[t]`:
   - `(ordA[t]).fixed ∩ V_big ⊆ slotAllowed sl`,
   - if `t < R_card`, `∑ v ∈ sl.1, |S v| ≤ t + V_big.card * C`,
   - if `R_card ≤ t`, `∑ v ∈ sl.1, |S v| ≤ R_card + V_big.card * (C + K) + V_big.card ^ 2`! -/
theorem iterated_round_decomp {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    {A : Finset (HPlane ι S)} (hA : IsMinCover A)
    (V_big : Finset ι) {C K : ℕ} (hC2 : 2 ≤ C) (hCsq : A.card < (C - 1) ^ 2) (hK1 : 1 ≤ K) :
    ∃ (roundSpecs : List (List ι × List ℕ)) (R_card : ℕ) (W_all : Finset ι) (ordA : List (HPlane ι S)),
      roundSpecs.length * K ≤ R_card ∧
      R_card = (roundSpecs.map roundSize).sum ∧
      R_card ≤ A.card ∧
      (∀ p ∈ roundSpecs, p.1.Nodup ∧ (∀ v ∈ p.1, v ∈ V_big) ∧ p.2.length = p.1.length ∧ ∀ c ∈ p.2, c ≤ A.card) ∧
      W_all ⊆ V_big ∧
      ordA.Nodup ∧
      ordA.length = A.card ∧
      ordA.toFinset = A ∧
      (∀ t (hsl : t < (allSlots roundSpecs W_all (A.card - R_card)).length) (hord : t < ordA.length),
        let sl := (allSlots roundSpecs W_all (A.card - R_card))[t]'hsl
        (ordA[t]'hord).fixed ∩ V_big ⊆ slotAllowed sl ∧
        (t < R_card → ∑ v ∈ sl.1, Fintype.card (S v) ≤ t + V_big.card * C) ∧
        (R_card ≤ t → ∑ v ∈ sl.1, Fintype.card (S v) ≤ R_card + V_big.card * (C + K) + V_big.card ^ 2)) := by
  -- Strong induction on `(A \ R).card` maintaining accumulated `(roundSpecs, revList)` covering `R ⊆ A`!
  suffices hloop : ∀ (remN : ℕ) (R : Finset (HPlane ι S))
      (roundSpecs : List (List ι × List ℕ)) (revList : List (HPlane ι S)),
      R ⊆ A →
      (A \ R).card ≤ remN →
      roundSpecs.length * K ≤ R.card →
      R.card = (roundSpecs.map roundSize).sum →
      (∀ p ∈ roundSpecs, p.1.Nodup ∧ (∀ v ∈ p.1, v ∈ V_big) ∧ p.2.length = p.1.length ∧ ∀ c ∈ p.2, c ≤ A.card) →
      revList.Nodup ∧ revList.length = R.card ∧ revList.toFinset = R →
      (∀ t (hsl : t < (roundSpecs.flatMap fun p => roundSlots p.1 p.2).length) (hrev : t < revList.length),
        let sl := (roundSpecs.flatMap fun p => roundSlots p.1 p.2)[t]'hsl
        (revList[t]'hrev).fixed ∩ V_big ⊆ slotAllowed sl ∧
        ∑ v ∈ sl.1, Fintype.card (S v) ≤ t + V_big.card * C) →
      ∃ (roundSpecs' : List (List ι × List ℕ)) (R_card : ℕ) (W_all : Finset ι) (ordA : List (HPlane ι S)),
        roundSpecs'.length * K ≤ R_card ∧
        R_card = (roundSpecs'.map roundSize).sum ∧
        R_card ≤ A.card ∧
        (∀ p ∈ roundSpecs', p.1.Nodup ∧ (∀ v ∈ p.1, v ∈ V_big) ∧ p.2.length = p.1.length ∧ ∀ c ∈ p.2, c ≤ A.card) ∧
        W_all ⊆ V_big ∧
        ordA.Nodup ∧
        ordA.length = A.card ∧
        ordA.toFinset = A ∧
        (∀ t (hsl : t < (allSlots roundSpecs' W_all (A.card - R_card)).length) (hord : t < ordA.length),
          let sl := (allSlots roundSpecs' W_all (A.card - R_card))[t]'hsl
          (ordA[t]'hord).fixed ∩ V_big ⊆ slotAllowed sl ∧
          (t < R_card → ∑ v ∈ sl.1, Fintype.card (S v) ≤ t + V_big.card * C) ∧
          (R_card ≤ t → ∑ v ∈ sl.1, Fintype.card (S v) ≤ R_card + V_big.card * (C + K) + V_big.card ^ 2)) by
    exact hloop A.card ∅ [] [] (Finset.empty_subset _) (by simp) (by simp) (by simp)
      (by simp) ⟨List.nodup_nil, by simp, by simp⟩ (fun t hsl _ => by simp at hsl)
  intro remN
  induction remN using Nat.strong_induction_on with
  | _ remN ih =>
    intro R roundSpecs revList hRA hrem hlenK hRsum hspecs ⟨hrev_nod, hrev_len, hrev_fin⟩ hrev_inv
    -- For every `H_star ∈ A \ R`, pick its canonical private point and `single_path_extract`
    have hextract : ∀ H_star ∈ A \ R,
        ∃ (z : (i : ι) → S i) (seq : List ι) (buckets : ι → Finset (HPlane ι S)),
          seq.Nodup ∧
          (∀ v ∈ seq, v ∈ V_big) ∧
          H_star.fixed ∩ V_big ⊆ seq.toFinset ∧
          (∀ v ∈ seq, buckets v ⊆ A.erase H_star) ∧
          (∀ v ∈ seq, Fintype.card (S v) ≤ (buckets v).card + C) ∧
          (∀ i j : Fin seq.length, i ≠ j → Disjoint (buckets (seq.get i)) (buckets (seq.get j))) ∧
          (∀ i : Fin seq.length, ∀ H ∈ buckets (seq.get i),
            H.fixed ∩ V_big ⊆ insert (seq.get i) (seq.take i.val).toFinset ∧
            (H (seq.get i)).isSome ∧
            (∀ u ∈ V_big, u ≠ seq.get i → H u = none ∨ H u = some (z u))) ∧
          (∀ v ∈ seq, Set.InjOn (fun H : HPlane ι S => H v) (buckets v)) := by
      intro H_star hHs
      have hHsA : H_star ∈ A := (Finset.mem_sdiff.mp hHs).1
      obtain ⟨z, hzH, hzpriv⟩ := hA.2 H_star hHsA
      obtain ⟨seq, buckets, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
        single_path_extract hA V_big hC2 hCsq hHsA z hzH hzpriv
      exact ⟨z, seq, buckets, h1, h2, h3, h4, h5, h6, h7, h8⟩
    -- Check if any `H_star ∈ A \ R` yields a round with `≥ K` newly revealed hyperplanes!
    by_cases hbig_round : ∃ H_star ∈ A \ R, ∃ (seq : List ι) (buckets : ι → Finset (HPlane ι S)),
        seq.Nodup ∧ (∀ v ∈ seq, v ∈ V_big) ∧ H_star.fixed ∩ V_big ⊆ seq.toFinset ∧
        (∀ v ∈ seq, buckets v ⊆ A.erase H_star) ∧
        (∀ v ∈ seq, Fintype.card (S v) ≤ (buckets v).card + C) ∧
        (∀ i j : Fin seq.length, i ≠ j → Disjoint (buckets (seq.get i)) (buckets (seq.get j))) ∧
        (∀ i : Fin seq.length, ∀ H ∈ buckets (seq.get i),
          H.fixed ∩ V_big ⊆ insert (seq.get i) (seq.take i.val).toFinset) ∧
        K ≤ ((R ∪ seq.toFinset.biUnion buckets ∪ {H_star}) \ R).card
    · obtain ⟨H_star, hHs, seq, buckets, hnod, hseqV, hHs_fix, hbuckA, hbuck_card, hdisj, hprop, hgeK⟩ := hbig_round
      rcases Finset.mem_sdiff.mp hHs with ⟨hHsA, hHsNotR⟩
      let cnts : List ℕ := (List.range seq.length).map fun i =>
        if h : i < seq.length then (buckets (seq[i]'h) \ R).card else 0
      let R_new : Finset (HPlane ι S) := R ∪ seq.toFinset.biUnion buckets ∪ {H_star}
      obtain ⟨newList, hnew_nod, hnew_len, hnew_in, hnew_cov, hRnew_sub, hRnew_card, hnew_inv⟩ :=
        build_round_list hRA V_big hHsA hHsNotR seq buckets hnod hseqV hHs_fix hbuckA hbuck_card hdisj hprop
      have hnew_geK : K ≤ newList.length := by
        have h1 : newList.toFinset = R_new \ R := by
          ext H; rw [List.mem_toFinset]; exact ⟨hnew_in H, hnew_cov H⟩
        rw [← List.toFinset_card_of_nodup hnew_nod, h1]
        exact hgeK
      have hrem_lt : (A \ R_new).card < remN := by
        have h1 := Finset.card_sdiff_add_card_eq_card hRA
        have h2 : (A \ R_new).card + R_new.card = A.card := Finset.card_sdiff_add_card_eq_card hRnew_sub
        have h3 : R_new.card = R.card + newList.length := hRnew_card
        omega
      let roundSpecs' := roundSpecs ++ [(seq, cnts)]
      let revList' := revList ++ newList
      have hRnew_sum : R_new.card = (roundSpecs'.map roundSize).sum := by
        simp only [roundSpecs', List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
        rw [hRnew_card, hRsum, hnew_len]
      have hlenK' : roundSpecs'.length * K ≤ R_new.card := by
        simp only [roundSpecs', List.length_append, List.length_singleton]
        rw [hRnew_card, Nat.add_mul, one_mul]
        omega
      have hspecs' : ∀ p ∈ roundSpecs', p.1.Nodup ∧ (∀ v ∈ p.1, v ∈ V_big) ∧
          p.2.length = p.1.length ∧ ∀ c ∈ p.2, c ≤ A.card := by
        intro p hp
        rcases List.mem_append.mp hp with hp1 | hp2
        · exact hspecs p hp1
        · rw [List.mem_singleton.mp hp2]
          refine ⟨hnod, hseqV, by simp [cnts], ?_⟩
          intro c hc
          simp only [cnts, List.mem_map, List.mem_range] at hc
          obtain ⟨i, hi, rfl⟩ := hc
          simp only [hi, ↓reduceDIte]
          exact (Finset.card_le_card (Finset.sdiff_subset.trans
            ((hbuckA (seq[i]'hi) (List.getElem_mem hi)).trans (Finset.erase_subset _ _))))
      have hrev'_nod : revList'.Nodup := by
        rw [List.nodup_append]
        refine ⟨hrev_nod, hnew_nod, ?_⟩
        intro H1 h1 H2 h2 heq
        subst heq
        have hR : H1 ∈ R := hrev_fin ▸ List.mem_toFinset.mpr h1
        exact (Finset.mem_sdiff.mp (hnew_in H1 h2)).2 hR
      have hrev'_len : revList'.length = R_new.card := by
        rw [List.length_append, hrev_len, hRnew_card]
      have hrev'_fin : revList'.toFinset = R_new := by
        ext H
        rw [List.mem_toFinset, List.mem_append]
        constructor
        · rintro (h1 | h2)
          · have hHR : H ∈ R := hrev_fin ▸ List.mem_toFinset.mpr h1
            exact (Finset.subset_union_left.trans Finset.subset_union_left) hHR
          · exact (Finset.mem_sdiff.mp (hnew_in H h2)).1
        · intro hH
          by_cases hHR : H ∈ R
          · exact Or.inl (List.mem_toFinset.mp (hrev_fin.symm ▸ hHR))
          · exact Or.inr (hnew_cov H (Finset.mem_sdiff.mpr ⟨hH, hHR⟩))
      have hrev'_inv : ∀ t (hsl : t < (roundSpecs'.flatMap fun p => roundSlots p.1 p.2).length)
          (hrev : t < revList'.length),
          let sl := (roundSpecs'.flatMap fun p => roundSlots p.1 p.2)[t]'hsl
          (revList'[t]'hrev).fixed ∩ V_big ⊆ slotAllowed sl ∧
          ∑ v ∈ sl.1, Fintype.card (S v) ≤ t + V_big.card * C := by
        intro t hsl hrev
        have hflat_eq : (roundSpecs'.flatMap fun p => roundSlots p.1 p.2) =
            (roundSpecs.flatMap fun p => roundSlots p.1 p.2) ++ roundSlots seq cnts := by
          simp [roundSpecs', List.flatMap_append]
        have hflat_len : (roundSpecs.flatMap fun p => roundSlots p.1 p.2).length = R.card := by
          rw [List.length_flatMap]
          have : (roundSpecs.map fun p => (roundSlots p.1 p.2).length) = roundSpecs.map roundSize :=
            List.map_congr_left fun p _ => roundSlots_length p.1 p.2
          rw [this, hRsum]
        by_cases hlt : t < R.card
        · dsimp only
          have hlt_flat : t < (roundSpecs.flatMap fun p => roundSlots p.1 p.2).length := by omega
          have hlt_rev : t < revList.length := by omega
          simp only [hflat_eq, revList']
          rw [List.getElem_append_left hlt_flat, List.getElem_append_left hlt_rev]
          exact hrev_inv t hlt_flat hlt_rev
        · have hge_flat : (roundSpecs.flatMap fun p => roundSlots p.1 p.2).length ≤ t := by omega
          have hge_rev : revList.length ≤ t := by omega
          have ht2 : t - R.card < newList.length := by
            have : revList'.length = R.card + newList.length := by rw [hrev'_len, hRnew_card]
            omega
          have hsl2 : t - R.card < (roundSlots seq cnts).length := by
            rw [roundSlots_length, ← hnew_len]; exact ht2
          dsimp only
          simp only [hflat_eq, revList']
          rw [List.getElem_append_right hge_flat, List.getElem_append_right hge_rev]
          simp only [hflat_len, hrev_len]
          have hni := hnew_inv (t - R.card) ht2 hsl2
          refine ⟨hni.1, ?_⟩
          have hcost : ∑ v ∈ ((roundSlots seq cnts)[t - R.card]'hsl2).1, Fintype.card (S v) ≤
              R.card + (t - R.card) + V_big.card * C := hni.2
          omega
      exact ih (A \ R_new).card hrem_lt R_new roundSpecs' revList'
        hRnew_sub le_rfl hlenK' hRnew_sum hspecs' ⟨hrev'_nod, hrev'_len, hrev'_fin⟩ hrev'_inv
    · -- Stopped state! Every `H_star ∈ A \ R` reveals `< K` new hyperplanes!
      set U := A \ R
      set W_all := U.biUnion fun H => H.fixed ∩ V_big
      have hWall_sub : W_all ⊆ V_big := Finset.biUnion_subset.mpr fun _ _ => Finset.inter_subset_right
      -- For each `v ∈ W_all`, extract `E(v) ⊆ R` with `|S v| ≤ |E(v)| + C + K`, injective on `v`,
      -- and at most 1 value on every other `u ∈ V_big \ {v}`!
      have hex_E : ∀ v ∈ W_all,
          ∃ (E : Finset (HPlane ι S)) (z : (i : ι) → S i),
            E ⊆ R ∧
            Fintype.card (S v) ≤ E.card + C + K ∧
            (∀ H ∈ E, (H v).isSome ∧ ∀ u ∈ V_big, u ≠ v → H u = none ∨ H u = some (z u)) ∧
            Set.InjOn (fun H : HPlane ι S => H v) E := by
        intro v hv
        obtain ⟨H_star, hHsU, hvfix⟩ := Finset.mem_biUnion.mp hv
        obtain ⟨z, seq, buckets, hnod, hseqV, hHs_fix, hbuckA, hbuck_card, hdisj, hprop, hinj⟩ :=
          hextract H_star hHsU
        have hvseq : v ∈ seq := List.mem_toFinset.mp (hHs_fix hvfix)
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hvseq
        -- Since `hbig_round` is false, `((R ∪ seq.toFinset.biUnion buckets ∪ {H_star}) \ R).card < K`!
        have hltK : ((R ∪ seq.toFinset.biUnion buckets ∪ {H_star}) \ R).card < K := by
          by_contra hge
          push Not at hge
          exact hbig_round ⟨H_star, hHsU, seq, buckets, hnod, hseqV, hHs_fix, hbuckA, hbuck_card,
            hdisj, fun j H hH => (hprop j H hH).1, hge⟩
        have hsdiff_sub : buckets (seq[i]'hi) \ R ⊆ (R ∪ seq.toFinset.biUnion buckets ∪ {H_star}) \ R := by
          intro H hH
          rcases Finset.mem_sdiff.mp hH with ⟨hHb, hHnotR⟩
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨seq[i]'hi, List.mem_toFinset.mpr hvseq, hHb⟩)), hHnotR⟩
        have hnew_ltK : (buckets (seq[i]'hi) \ R).card < K :=
          lt_of_le_of_lt (Finset.card_le_card hsdiff_sub) hltK
        have hsplit := Finset.card_inter_add_card_sdiff (buckets (seq[i]'hi)) R
        have hcard_v := hbuck_card (seq[i]'hi) hvseq
        refine ⟨buckets (seq[i]'hi) ∩ R, z, Finset.inter_subset_right, by omega, ?_,
          (hinj (seq[i]'hi) hvseq).mono Finset.inter_subset_left⟩
        intro H hH
        have h1 := hprop ⟨i, hi⟩ H (Finset.mem_inter.mp hH).1
        exact ⟨h1.2.1, h1.2.2⟩
      -- Choose `E : ι → Finset (HPlane ι S)` on `W_all` without needing a dummy `z` outside `W_all`
      let E : ι → Finset (HPlane ι S) := fun v =>
        if h : v ∈ W_all then (hex_E v h).choose else ∅
      have hE_spec : ∀ v (hv : v ∈ W_all),
          ∃ z : (i : ι) → S i,
            E v ⊆ R ∧
            Fintype.card (S v) ≤ (E v).card + C + K ∧
            (∀ H ∈ E v, (H v).isSome ∧ ∀ u ∈ V_big, u ≠ v → H u = none ∨ H u = some (z u)) ∧
            Set.InjOn (fun H : HPlane ι S => H v) (E v) := by
        intro v hv
        simp only [E, dif_pos hv]
        exact (hex_E v hv).choose_spec
      -- Pairwise intersection bound: for distinct `v, u ∈ W_all`, `|(E v) ∩ (E u)| ≤ 1`!
      have hpair : ∀ v ∈ W_all, ∀ u ∈ W_all, v ≠ u → ((E v) ∩ (E u)).card ≤ 1 := by
        intro v hv u hu hvu
        obtain ⟨zv, _, _, hEv_prop, hEv_inj⟩ := hE_spec v hv
        obtain ⟨zu, _, _, hEu_prop, _⟩ := hE_spec u hu
        rw [Finset.card_le_one]
        intro H1 hH1 H2 hH2
        rcases Finset.mem_inter.mp hH1 with ⟨h1v, h1u⟩
        rcases Finset.mem_inter.mp hH2 with ⟨h2v, h2u⟩
        have h1_eq : H1 v = some (zu v) := by
          have hs := (hEv_prop H1 h1v).1
          rcases (hEu_prop H1 h1u).2 v (hWall_sub hv) hvu with hnone | hsome
          · simp [hnone] at hs
          · exact hsome
        have h2_eq : H2 v = some (zu v) := by
          have hs := (hEv_prop H2 h2v).1
          rcases (hEu_prop H2 h2u).2 v (hWall_sub hv) hvu with hnone | hsome
          · simp [hnone] at hs
          · exact hsome
        exact hEv_inj h1v h2v (h1_eq.trans h2_eq.symm)
      -- Disjointify `E` on `W_all` by removing elements shared with any other `u ∈ W_all`
      let E' : ι → Finset (HPlane ι S) := fun v =>
        (E v).filter fun H => ∀ u ∈ W_all, u ≠ v → H ∉ E u
      have hE'_sub : ∀ v ∈ W_all, E' v ⊆ E v := fun v _ => Finset.filter_subset _ _
      have hE'_R : ∀ v ∈ W_all, E' v ⊆ R := fun v hv => by
        obtain ⟨_, hER, _, _, _⟩ := hE_spec v hv
        exact (hE'_sub v hv).trans hER
      have hE'_disj : (W_all : Set ι).PairwiseDisjoint E' := by
        intro v hv u hu hvu
        change Disjoint (E' v) (E' u)
        rw [Finset.disjoint_left]
        intro H hHv hHu
        exact (Finset.mem_filter.mp hHv).2 u hu hvu.symm (hE'_sub u hu hHu)
      have hE_diff : ∀ v ∈ W_all, (E v \ E' v).card ≤ W_all.card := by
        intro v hv
        have hsub : E v \ E' v ⊆ (W_all.erase v).biUnion fun u => E v ∩ E u := by
          intro H hH
          rcases Finset.mem_sdiff.mp hH with ⟨hHv, hnot⟩
          have hnot' : ¬ ∀ u ∈ W_all, u ≠ v → H ∉ E u := fun hall =>
            hnot (Finset.mem_filter.mpr ⟨hHv, hall⟩)
          push Not at hnot'
          obtain ⟨u, huW, huv, hHu⟩ := hnot'
          exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_erase.mpr ⟨huv, huW⟩,
            Finset.mem_inter.mpr ⟨hHv, hHu⟩⟩
        calc (E v \ E' v).card
            ≤ ((W_all.erase v).biUnion fun u => E v ∩ E u).card := Finset.card_le_card hsub
          _ ≤ ∑ u ∈ W_all.erase v, (E v ∩ E u).card := Finset.card_biUnion_le
          _ ≤ ∑ _u ∈ W_all.erase v, 1 := Finset.sum_le_sum fun u hu => by
              rcases Finset.mem_erase.mp hu with ⟨huv, huW⟩
              exact hpair v hv u huW huv.symm
          _ = (W_all.erase v).card := by simp
          _ ≤ W_all.card := Finset.card_le_card (Finset.erase_subset _ _)
      have hsum_E' : ∑ v ∈ W_all, (E' v).card ≤ R.card := by
        rw [← Finset.card_biUnion hE'_disj]
        exact Finset.card_le_card (Finset.biUnion_subset.mpr fun v hv => hE'_R v hv)
      have hWall_cost : ∑ v ∈ W_all, Fintype.card (S v) ≤
          R.card + V_big.card * (C + K) + V_big.card ^ 2 := by
        have h1 : ∑ v ∈ W_all, Fintype.card (S v) ≤
            ∑ v ∈ W_all, ((E' v).card + (W_all.card + C + K)) := by
          refine Finset.sum_le_sum fun v hv => ?_
          obtain ⟨_, _, hcard_v, _, _⟩ := hE_spec v hv
          have hsd := Finset.card_sdiff_add_card_eq_card (hE'_sub v hv)
          have hd := hE_diff v hv
          omega
        have h2 : ∑ v ∈ W_all, ((E' v).card + (W_all.card + C + K)) =
            (∑ v ∈ W_all, (E' v).card) + W_all.card * (W_all.card + C + K) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
        have hWle : W_all.card ≤ V_big.card := Finset.card_le_card hWall_sub
        have hmul1 : W_all.card * (C + K) ≤ V_big.card * (C + K) := Nat.mul_le_mul_right _ hWle
        have hmul2 : W_all.card * W_all.card ≤ V_big.card ^ 2 := by
          rw [sq]; exact Nat.mul_le_mul hWle hWle
        have hdist : W_all.card * (W_all.card + C + K) =
            W_all.card * W_all.card + W_all.card * (C + K) := by ring
        omega
      -- Assemble final ordered list `ordA := revList ++ U.toList`
      let ordA : List (HPlane ι S) := revList ++ U.toList
      have hR_le_A : R.card ≤ A.card := Finset.card_le_card hRA
      have hU_card : U.card = A.card - R.card := by
        have h1 : U.card + R.card = A.card := Finset.card_sdiff_add_card_eq_card hRA
        omega
      have hord_nod : ordA.Nodup := by
        rw [List.nodup_append]
        refine ⟨hrev_nod, U.nodup_toList, ?_⟩
        intro H1 h1 H2 h2 heq
        subst heq
        have hHR : H1 ∈ R := hrev_fin ▸ List.mem_toFinset.mpr h1
        have hHU : H1 ∈ U := Finset.mem_toList.mp h2
        exact (Finset.mem_sdiff.mp hHU).2 hHR
      have hord_len : ordA.length = A.card := by
        rw [List.length_append, hrev_len, Finset.length_toList, hU_card]
        omega
      have hord_fin : ordA.toFinset = A := by
        ext H
        rw [List.mem_toFinset, List.mem_append]
        constructor
        · rintro (h1 | h2)
          · exact hRA (hrev_fin ▸ List.mem_toFinset.mpr h1)
          · exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp h2)).1
        · intro hHA
          by_cases hHR : H ∈ R
          · exact Or.inl (List.mem_toFinset.mp (hrev_fin.symm ▸ hHR))
          · exact Or.inr (Finset.mem_toList.mpr (Finset.mem_sdiff.mpr ⟨hHA, hHR⟩))
      refine ⟨roundSpecs, R.card, W_all, ordA, hlenK, hRsum, hR_le_A, hspecs, hWall_sub,
        hord_nod, hord_len, hord_fin, ?_⟩
      intro t hsl hord
      have hflat_len : (roundSpecs.flatMap fun p => roundSlots p.1 p.2).length = R.card := by
        rw [List.length_flatMap]
        have : (roundSpecs.map fun p => (roundSlots p.1 p.2).length) = roundSpecs.map roundSize :=
          List.map_congr_left fun p _ => roundSlots_length p.1 p.2
        rw [this, hRsum]
      by_cases hlt : t < R.card
      · dsimp only
        have hlt_flat : t < (roundSpecs.flatMap fun p => roundSlots p.1 p.2).length := by omega
        have hlt_rev : t < revList.length := by omega
        have hsl_eq : (allSlots roundSpecs W_all (A.card - R.card))[t]'hsl =
            (roundSpecs.flatMap fun p => roundSlots p.1 p.2)[t]'hlt_flat := by
          unfold allSlots
          exact List.getElem_append_left hlt_flat
        have hord_t : ordA[t]'hord = revList[t]'hlt_rev := by
          dsimp only [ordA]
          exact List.getElem_append_left hlt_rev
        rw [hsl_eq, hord_t]
        have hinv := hrev_inv t hlt_flat hlt_rev
        exact ⟨hinv.1, fun _ => hinv.2, fun hge => by omega⟩
      · dsimp only
        have hge_flat : (roundSpecs.flatMap fun p => roundSlots p.1 p.2).length ≤ t := by omega
        have hge_rev : revList.length ≤ t := by omega
        have hsl_eq : (allSlots roundSpecs W_all (A.card - R.card))[t]'hsl =
            (W_all, none) := by
          unfold allSlots at hsl ⊢
          rw [List.getElem_append_right hge_flat]
          exact List.getElem_replicate _
        have hord_t : ordA[t]'hord = U.toList[t - R.card]'(by rw [Finset.length_toList]; omega) := by
          dsimp only [ordA]
          rw [List.getElem_append_right hge_rev]
          simp only [hrev_len]
        rw [hsl_eq, hord_t]
        have hmemU : U.toList[t - R.card]'(by rw [Finset.length_toList]; omega) ∈ U :=
          Finset.mem_toList.mp (List.getElem_mem _)
        refine ⟨?_, fun hlt' => by omega, fun _ => hWall_cost⟩
        simp only [slotAllowed]
        exact Finset.subset_biUnion_of_mem (fun H => H.fixed ∩ V_big) hmemU

end ExtractionAndRounds

end Erdos1189BBMST

/- Section 4: Explicit Finite Code Injection and Cardinality Bound for `irreducibleCount k`. -/

namespace Erdos1189BBMST

open Finset Real Filter
open scoped Classical

section CountingInjection

/-- The big prime-power coordinates `v = (p, j)` of `N` with `M_cut ≤ p`. -/
def bigCoords (N M_cut : ℕ) : Finset (CoordIdx N) :=
  Finset.univ.filter fun v : CoordIdx N => M_cut ≤ v.1.1

/-- Simpson's bound implies `|bigCoords N M_cut| ≤ k / (M_cut - 1)`. -/
lemma bigCoords_card_le {N M_cut k : ℕ} (hM2 : 2 ≤ M_cut)
    (hsimp : 1 + ∑ p ∈ N.primeFactors, N.factorization p * (p - 1) ≤ k) :
    (bigCoords N M_cut).card ≤ k / (M_cut - 1) := by
  have hMpos : 0 < M_cut - 1 := by omega
  rw [Nat.le_div_iff_mul_le hMpos]
  calc (bigCoords N M_cut).card * (M_cut - 1)
      = ∑ _v ∈ bigCoords N M_cut, (M_cut - 1) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ v ∈ bigCoords N M_cut, (v.1.1 - 1) := by
        refine Finset.sum_le_sum fun v hv => ?_
        have hge : M_cut ≤ v.1.1 := (Finset.mem_filter.mp hv).2
        omega
    _ ≤ ∑ v : CoordIdx N, (v.1.1 - 1) :=
        Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
    _ = ∑ v ∈ primeCoords N, (v.1 - 1) :=
        Finset.sum_coe_sort (primeCoords N) (fun v => v.1 - 1)
    _ = ∑ p ∈ N.primeFactors, N.factorization p * (p - 1) := sum_primeCoords_sub_one N
    _ ≤ k := by omega

/-- Divisors of `N` supported only on primes `< M_cut`. -/
def smallDivs (N M_cut : ℕ) : Finset ℕ :=
  N.divisors.filter fun d => ∀ p ∈ d.primeFactors, p < M_cut

/-- Exact product formula for the number of small-prime divisors of `N`. -/
def dSmall (N M_cut : ℕ) : ℕ :=
  ∏ p ∈ N.primeFactors.filter (· < M_cut), (N.factorization p + 1)

lemma card_smallDivs_le {N M_cut : ℕ} (hN : 0 < N) :
    (smallDivs N M_cut).card ≤ dSmall N M_cut := by
  let P := N.primeFactors.filter (· < M_cut)
  let f : {d : ℕ // d ∈ smallDivs N M_cut} → (p : {p : ℕ // p ∈ P}) → Fin (N.factorization p.1 + 1) :=
    fun d p =>
      have hdvd : d.1 ∣ N := (Nat.mem_divisors.mp (Finset.mem_filter.mp d.2).1).1
      have hd0 : d.1 ≠ 0 := ne_zero_of_dvd_ne_zero hN.ne' hdvd
      ⟨d.1.factorization p.1, Nat.lt_succ_of_le
        ((Nat.factorization_le_iff_dvd hd0 hN.ne').mpr hdvd p.1)⟩
  have hfinj : Function.Injective f := by
    intro d1 d2 heq
    apply Subtype.ext
    have hd1 : d1.1 ∣ N := (Nat.mem_divisors.mp (Finset.mem_filter.mp d1.2).1).1
    have hd2 : d2.1 ∣ N := (Nat.mem_divisors.mp (Finset.mem_filter.mp d2.2).1).1
    have hd10 : d1.1 ≠ 0 := ne_zero_of_dvd_ne_zero hN.ne' hd1
    have hd20 : d2.1 ≠ 0 := ne_zero_of_dvd_ne_zero hN.ne' hd2
    have hsm1 := (Finset.mem_filter.mp d1.2).2
    have hsm2 := (Finset.mem_filter.mp d2.2).2
    refine Nat.eq_of_factorization_eq hd10 hd20 fun p => ?_
    by_cases hp : p ∈ P
    · have := congrArg (fun g => (g ⟨p, hp⟩).val) heq
      exact this
    · have h1 : p ∉ d1.1.primeFactors := by
        intro hmem
        exact hp (Finset.mem_filter.mpr ⟨Nat.primeFactors_mono hd1 hN.ne' hmem, hsm1 p hmem⟩)
      have h2 : p ∉ d2.1.primeFactors := by
        intro hmem
        exact hp (Finset.mem_filter.mpr ⟨Nat.primeFactors_mono hd2 hN.ne' hmem, hsm2 p hmem⟩)
      rw [factorization_eq_zero_of_notMem_primeFactors h1,
          factorization_eq_zero_of_notMem_primeFactors h2]
  calc (smallDivs N M_cut).card
      = Fintype.card {d : ℕ // d ∈ smallDivs N M_cut} := (Fintype.card_coe _).symm
    _ ≤ Fintype.card ((p : {p : ℕ // p ∈ P}) → Fin (N.factorization p.1 + 1)) :=
        Fintype.card_le_of_injective f hfinj
    _ = ∏ p : {p : ℕ // p ∈ P}, (N.factorization p.1 + 1) := by
        simp [Fintype.card_pi]
    _ = dSmall N M_cut := Finset.prod_coe_sort P (fun p => N.factorization p + 1)

/-- Big prime-power coordinates fixed by a modulus `m`. -/
def divBigCoords (N M_cut m : ℕ) : Finset (CoordIdx N) :=
  (bigCoords N M_cut).filter fun v => v.1.2 < m.factorization v.1.1

lemma arithHPlane_fixed_inter_bigCoords (N M_cut m : ℕ) (a : ℤ) :
    (arithHPlane N m a).fixed ∩ bigCoords N M_cut = divBigCoords N M_cut m := by
  ext v
  simp only [Finset.mem_inter, mem_fixed_iff, divBigCoords, Finset.mem_filter, arithHPlane]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, ?_⟩
    by_cases hlt : v.1.2 < m.factorization v.1.1
    · exact hlt
    · simp [hlt] at h1
  · rintro ⟨h1, h2⟩
    exact ⟨by simp [h2], h1⟩

/-- Number of coordinates in `W` belonging to prime `p`. -/
def coordMult (N : ℕ) (W : Finset (CoordIdx N)) (p : ℕ) : ℕ :=
  (W.filter fun v : CoordIdx N => v.1.1 = p).card

/-- Divisors of `N` supported only on primes `≥ M_cut` whose big coordinates lie inside `W`. -/
def bigDivsIn (N M_cut : ℕ) (W : Finset (CoordIdx N)) : Finset ℕ :=
  N.divisors.filter fun d =>
    (∀ p ∈ d.primeFactors, M_cut ≤ p) ∧ divBigCoords N M_cut d ⊆ W

/-- Upper bound `∏_{p | N, p ≥ M_cut} (coordMult N W p + 1)` on `|bigDivsIn N M_cut W|`. -/
def dBig (N M_cut : ℕ) (W : Finset (CoordIdx N)) : ℕ :=
  ∏ p ∈ N.primeFactors.filter (M_cut ≤ ·), (coordMult N W p + 1)

lemma card_bigDivsIn_le {N M_cut : ℕ} (hN : 0 < N) (W : Finset (CoordIdx N)) :
    (bigDivsIn N M_cut W).card ≤ dBig N M_cut W := by
  let P := N.primeFactors.filter (M_cut ≤ ·)
  have hfac_le_mult : ∀ d ∈ bigDivsIn N M_cut W, ∀ p ∈ P, d.factorization p ≤ coordMult N W p := by
    intro d hd p hp
    rcases Finset.mem_filter.mp hd with ⟨hdN, _, hsub⟩
    rcases Finset.mem_filter.mp hp with ⟨hpN, hpM⟩
    have hdvd : d ∣ N := (Nat.mem_divisors.mp hdN).1
    have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hN.ne' hdvd
    have hleN : d.factorization p ≤ N.factorization p :=
      (Nat.factorization_le_iff_dvd hd0 hN.ne').mpr hdvd p
    let g : Fin (d.factorization p) → CoordIdx N := fun j =>
      ⟨(p, j.val), mem_primeCoords.mpr ⟨hpN, lt_of_lt_of_le j.isLt hleN⟩⟩
    have hginj : Function.Injective g := by
      intro j1 j2 h
      apply Fin.ext
      exact (Prod.mk.inj (congrArg Subtype.val h)).2
    have hgsub : Finset.univ.image g ⊆ W.filter fun v : CoordIdx N => v.1.1 = p := by
      intro v hv
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
      refine Finset.mem_filter.mpr ⟨hsub ?_, rfl⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpM⟩, j.isLt⟩
    calc d.factorization p
        = (Finset.univ : Finset (Fin (d.factorization p))).card := by simp
      _ = (Finset.univ.image g).card := (Finset.card_image_of_injective _ hginj).symm
      _ ≤ coordMult N W p := Finset.card_le_card hgsub
  let f : {d : ℕ // d ∈ bigDivsIn N M_cut W} → (p : {p : ℕ // p ∈ P}) → Fin (coordMult N W p.1 + 1) :=
    fun d p => ⟨d.1.factorization p.1, Nat.lt_succ_of_le (hfac_le_mult d.1 d.2 p.1 p.2)⟩
  have hfinj : Function.Injective f := by
    intro d1 d2 heq
    apply Subtype.ext
    have hd1 : d1.1 ∣ N := (Nat.mem_divisors.mp (Finset.mem_filter.mp d1.2).1).1
    have hd2 : d2.1 ∣ N := (Nat.mem_divisors.mp (Finset.mem_filter.mp d2.2).1).1
    have hd10 : d1.1 ≠ 0 := ne_zero_of_dvd_ne_zero hN.ne' hd1
    have hd20 : d2.1 ≠ 0 := ne_zero_of_dvd_ne_zero hN.ne' hd2
    have hbg1 := (Finset.mem_filter.mp d1.2).2.1
    have hbg2 := (Finset.mem_filter.mp d2.2).2.1
    refine Nat.eq_of_factorization_eq hd10 hd20 fun p => ?_
    by_cases hp : p ∈ P
    · exact congrArg (fun g => (g ⟨p, hp⟩).val) heq
    · have h1 : p ∉ d1.1.primeFactors := by
        intro hmem
        exact hp (Finset.mem_filter.mpr ⟨Nat.primeFactors_mono hd1 hN.ne' hmem, hbg1 p hmem⟩)
      have h2 : p ∉ d2.1.primeFactors := by
        intro hmem
        exact hp (Finset.mem_filter.mpr ⟨Nat.primeFactors_mono hd2 hN.ne' hmem, hbg2 p hmem⟩)
      rw [factorization_eq_zero_of_notMem_primeFactors h1,
          factorization_eq_zero_of_notMem_primeFactors h2]
  calc (bigDivsIn N M_cut W).card
      = Fintype.card {d : ℕ // d ∈ bigDivsIn N M_cut W} := (Fintype.card_coe _).symm
    _ ≤ Fintype.card ((p : {p : ℕ // p ∈ P}) → Fin (coordMult N W p.1 + 1)) :=
        Fintype.card_le_of_injective f hfinj
    _ = ∏ p : {p : ℕ // p ∈ P}, (coordMult N W p.1 + 1) := by simp [Fintype.card_pi]
    _ = dBig N M_cut W := Finset.prod_coe_sort P (fun p => coordMult N W p + 1)

/-- Adding one coordinate to `W` at most doubles `dBig N M_cut W`. -/
lemma dBig_insert_le (N M_cut : ℕ) (W : Finset (CoordIdx N)) (v0 : CoordIdx N) :
    dBig N M_cut (insert v0 W) ≤ 2 * dBig N M_cut W := by
  unfold dBig
  let P := N.primeFactors.filter (M_cut ≤ ·)
  have hne_eq : ∀ p, p ≠ v0.1.1 → coordMult N (insert v0 W) p = coordMult N W p := by
    intro p hp
    unfold coordMult
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨rfl | hv, hvp⟩
      · exact absurd hvp.symm hp
      · exact ⟨hv, hvp⟩
    · rintro ⟨hv, hvp⟩
      exact ⟨Or.inr hv, hvp⟩
  have hle_at : coordMult N (insert v0 W) v0.1.1 + 1 ≤ 2 * (coordMult N W v0.1.1 + 1) := by
    have hsub : (insert v0 W).filter (fun v : CoordIdx N => v.1.1 = v0.1.1) ⊆
        insert v0 (W.filter fun v : CoordIdx N => v.1.1 = v0.1.1) := by
      intro v hv
      rcases Finset.mem_filter.mp hv with ⟨hins, hvp⟩
      rcases Finset.mem_insert.mp hins with rfl | hvW
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hvW, hvp⟩)
    have hc : coordMult N (insert v0 W) v0.1.1 ≤ coordMult N W v0.1.1 + 1 :=
      (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    omega
  by_cases hvP : v0.1.1 ∈ P
  · rw [← Finset.mul_prod_erase P _ hvP, ← Finset.mul_prod_erase P _ hvP]
    have hrest : ∏ p ∈ P.erase v0.1.1, (coordMult N (insert v0 W) p + 1) =
        ∏ p ∈ P.erase v0.1.1, (coordMult N W p + 1) := by
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [hne_eq p (Finset.mem_erase.mp hp).1]
    rw [hrest, ← mul_assoc]
    exact Nat.mul_le_mul_right _ hle_at
  · have heq : ∏ p ∈ P, (coordMult N (insert v0 W) p + 1) =
        ∏ p ∈ P, (coordMult N W p + 1) := by
      refine Finset.prod_congr rfl fun p hp => ?_
      have hne : p ≠ v0.1.1 := fun h => hvP (h ▸ hp)
      rw [hne_eq p hne]
    dsimp only [P] at heq
    rw [heq]
    omega

/-- Weight identity relating `coordMult N W p` to `∑ v ∈ W, (v.1.1 - 1)`. -/
lemma sum_coordMult_mul_sub_one {N M_cut : ℕ} {W : Finset (CoordIdx N)}
    (hW : W ⊆ bigCoords N M_cut) :
    ∑ p ∈ N.primeFactors.filter (M_cut ≤ ·), coordMult N W p * (p - 1) =
      ∑ v ∈ W, (v.1.1 - 1) := by
  have hmap : ∀ v ∈ W, v.1.1 ∈ N.primeFactors.filter (M_cut ≤ ·) := fun v hv =>
    Finset.mem_filter.mpr ⟨(mem_primeCoords.mp v.2).1, (Finset.mem_filter.mp (hW hv)).2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun v => v.1.1 - 1)]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hconst : ∑ v ∈ W.filter (fun v : CoordIdx N => v.1.1 = p), (v.1.1 - 1) =
      ∑ _v ∈ W.filter (fun v : CoordIdx N => v.1.1 = p), (p - 1) :=
    Finset.sum_congr rfl fun v hv => by rw [(Finset.mem_filter.mp hv).2]
  rw [hconst, Finset.sum_const, smul_eq_mul]
  rfl

/-- Divisors of `N` allowed at a slot `sl`. -/
def slotDivs (N M_cut : ℕ) (sl : Finset (CoordIdx N) × Option (CoordIdx N)) : Finset ℕ :=
  N.divisors.filter fun m => divBigCoords N M_cut m ⊆ slotAllowed sl

/-- Every allowed divisor factors into `smallDivs N M_cut × bigDivsIn N M_cut (slotAllowed sl)`,
giving `|slotDivs N M_cut sl| ≤ 2 * dSmall N M_cut * dBig N M_cut sl.1`. -/
lemma card_slotDivs_le {N M_cut : ℕ} (hN : 0 < N)
    (sl : Finset (CoordIdx N) × Option (CoordIdx N)) :
    (slotDivs N M_cut sl).card ≤ 2 * dSmall N M_cut * dBig N M_cut sl.1 := by
  have hsub : slotDivs N M_cut sl ⊆
      (smallDivs N M_cut ×ˢ bigDivsIn N M_cut (slotAllowed sl)).image (fun p => p.1 * p.2) := by
    intro m hm
    rcases Finset.mem_filter.mp hm with ⟨hmN, hmW⟩
    have hmdvd : m ∣ N := (Nat.mem_divisors.mp hmN).1
    have hm0 : m ≠ 0 := ne_zero_of_dvd_ne_zero hN.ne' hmdvd
    let ms := ∏ p ∈ m.primeFactors.filter (· < M_cut), p ^ m.factorization p
    let mb := ∏ p ∈ m.primeFactors.filter (M_cut ≤ ·), p ^ m.factorization p
    have hprod : ms * mb = m := by
      have hdisj : Disjoint (m.primeFactors.filter (· < M_cut))
          (m.primeFactors.filter (M_cut ≤ ·)) := by
        rw [Finset.disjoint_left]
        intro p h1 h2
        have := (Finset.mem_filter.mp h1).2
        have := (Finset.mem_filter.mp h2).2
        omega
      have hunion : m.primeFactors.filter (· < M_cut) ∪ m.primeFactors.filter (M_cut ≤ ·) =
          m.primeFactors := by
        ext p
        simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        · intro h
          by_cases hlt : p < M_cut
          · exact Or.inl ⟨h, hlt⟩
          · exact Or.inr ⟨h, by omega⟩
      dsimp only [ms, mb]
      rw [← Finset.prod_union hdisj, hunion]
      have := Nat.prod_factorization_pow_eq_self hm0
      simpa [Finsupp.prod, Nat.support_factorization] using this
    have hms_dvd : ms ∣ N := dvd_trans ⟨mb, hprod.symm⟩ hmdvd
    have hmb_dvd : mb ∣ N := dvd_trans ⟨ms, by rw [mul_comm]; exact hprod.symm⟩ hmdvd
    have hms_pf : ∀ p ∈ ms.primeFactors, p < M_cut := by
      intro p hp
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hp_dvd : p ∣ ms := Nat.dvd_of_mem_primeFactors hp
      obtain ⟨q, hq, hpq⟩ := (hp_prime.prime.dvd_finsetProd_iff _).mp hp_dvd
      have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
      have hp_eq_q : p = q :=
        (Nat.prime_dvd_prime_iff_eq hp_prime hq_prime).mp (hp_prime.dvd_of_dvd_pow hpq)
      exact hp_eq_q ▸ (Finset.mem_filter.mp hq).2
    have hmb_pf : ∀ p ∈ mb.primeFactors, M_cut ≤ p := by
      intro p hp
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hp_dvd : p ∣ mb := Nat.dvd_of_mem_primeFactors hp
      obtain ⟨q, hq, hpq⟩ := (hp_prime.prime.dvd_finsetProd_iff _).mp hp_dvd
      have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
      have hp_eq_q : p = q :=
        (Nat.prime_dvd_prime_iff_eq hp_prime hq_prime).mp (hp_prime.dvd_of_dvd_pow hpq)
      exact hp_eq_q ▸ (Finset.mem_filter.mp hq).2
    have hmb_sub : divBigCoords N M_cut mb ⊆ slotAllowed sl := by
      intro v hv
      apply hmW
      rcases Finset.mem_filter.mp hv with ⟨hvbig, hvlt⟩
      refine Finset.mem_filter.mpr ⟨hvbig, lt_of_lt_of_le hvlt ?_⟩
      have hmb_dvd_m : mb ∣ m := ⟨ms, by rw [mul_comm]; exact hprod.symm⟩
      have hmb0 : mb ≠ 0 := ne_zero_of_dvd_ne_zero hm0 hmb_dvd_m
      exact (Nat.factorization_le_iff_dvd hmb0 hm0).mpr hmb_dvd_m v.1.1
    exact Finset.mem_image.mpr ⟨(ms, mb), Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hms_dvd, hN.ne'⟩, hms_pf⟩,
       Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hmb_dvd, hN.ne'⟩, hmb_pf, hmb_sub⟩⟩, hprod⟩
  have hdBig_sl : dBig N M_cut (slotAllowed sl) ≤ 2 * dBig N M_cut sl.1 := by
    cases h2 : sl.2 with
    | none =>
      simp only [slotAllowed, h2]
      omega
    | some v0 =>
      simp only [slotAllowed, h2]
      exact dBig_insert_le N M_cut sl.1 v0
  calc (slotDivs N M_cut sl).card
      ≤ ((smallDivs N M_cut ×ˢ bigDivsIn N M_cut (slotAllowed sl)).image (fun p => p.1 * p.2)).card :=
        Finset.card_le_card hsub
    _ ≤ (smallDivs N M_cut ×ˢ bigDivsIn N M_cut (slotAllowed sl)).card := Finset.card_image_le
    _ = (smallDivs N M_cut).card * (bigDivsIn N M_cut (slotAllowed sl)).card := Finset.card_product _ _
    _ ≤ dSmall N M_cut * dBig N M_cut (slotAllowed sl) :=
        Nat.mul_le_mul (card_smallDivs_le hN) (card_bigDivsIn_le hN _)
    _ ≤ dSmall N M_cut * (2 * dBig N M_cut sl.1) := Nat.mul_le_mul_left _ hdBig_sl
    _ = 2 * dSmall N M_cut * dBig N M_cut sl.1 := by ring

/-- Decode a fixed-width single-round table `f : Fin B → Option ({v // v ∈ V} × Fin (k + 1))`
back to a round spec `(seq, cnts)`. -/
def decodeRound {α : Type*} {V : Finset α} {B k : ℕ}
    (f : Fin B → Option ({v : α // v ∈ V} × Fin (k + 1))) : List α × List ℕ :=
  let pairs := (List.finRange B).filterMap f
  (pairs.map fun x => x.1.1, pairs.map fun x => x.2.val)

/-- Encode a round spec `(seq, cnts)` with `seq.length ≤ B`, `∀ v ∈ seq, v ∈ V`,
`cnts.length = seq.length`, `∀ c ∈ cnts, c ≤ k` into a fixed-width table. -/
def encodeRound {α : Type*} {V : Finset α} {B k : ℕ}
    (seq : List α) (cnts : List ℕ)
    (hseqV : ∀ v ∈ seq, v ∈ V)
    (hcnt_len : cnts.length = seq.length)
    (hcnt_le : ∀ c ∈ cnts, c ≤ k) :
    Fin B → Option ({v : α // v ∈ V} × Fin (k + 1)) :=
  fun i =>
    if h : i.val < seq.length then
      some (⟨seq[i.val]'h, hseqV _ (List.getElem_mem h)⟩,
        ⟨cnts[i.val]'(by omega), Nat.lt_succ_of_le (hcnt_le _ (List.getElem_mem (by omega)))⟩)
    else none

lemma decodeRound_encodeRound {α : Type*} {V : Finset α} {B k : ℕ}
    (seq : List α) (cnts : List ℕ)
    (hlen : seq.length ≤ B)
    (hseqV : ∀ v ∈ seq, v ∈ V)
    (hcnt_len : cnts.length = seq.length)
    (hcnt_le : ∀ c ∈ cnts, c ≤ k) :
    decodeRound (encodeRound (B := B) (k := k) seq cnts hseqV hcnt_len hcnt_le) = (seq, cnts) := by
  let f := encodeRound (B := B) (k := k) seq cnts hseqV hcnt_len hcnt_le
  have hfilter : (List.finRange B).filterMap f =
      (List.finRange seq.length).map fun i =>
        (⟨seq[i.val]'i.isLt, hseqV _ (List.getElem_mem i.isLt)⟩,
         ⟨cnts[i.val]'(by omega), Nat.lt_succ_of_le (hcnt_le _ (List.getElem_mem (by omega)))⟩) := by
    have hsplit : List.finRange B =
        (List.finRange seq.length).map (Fin.castLE hlen) ++
        ((List.finRange B).drop seq.length) := by
      refine List.ext_getElem ?_ ?_
      · simp [hlen]
      · intro j hj1 hj2
        rw [List.getElem_finRange]
        by_cases hlt : j < seq.length
        · rw [List.getElem_append_left (by simp [hlt])]
          simp
        · rw [List.getElem_append_right (by simp; omega)]
          simp only [List.length_map, List.length_finRange, List.getElem_drop, List.getElem_finRange]
          apply Fin.ext
          dsimp
          omega
    rw [hsplit, List.filterMap_append, List.filterMap_map]
    have h1 : (List.finRange seq.length).filterMap (f ∘ Fin.castLE hlen) =
        (List.finRange seq.length).map fun i =>
          (⟨seq[i.val]'i.isLt, hseqV _ (List.getElem_mem i.isLt)⟩,
           ⟨cnts[i.val]'(by omega), Nat.lt_succ_of_le (hcnt_le _ (List.getElem_mem (by omega)))⟩) := by
      rw [← List.filterMap_eq_map]
      refine List.filterMap_congr fun i _ => ?_
      simp [f, encodeRound, i.isLt]
    have h2 : ((List.finRange B).drop seq.length).filterMap f = [] := by
      rw [List.filterMap_eq_nil_iff]
      intro i hi
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hi
      rw [List.getElem_drop, List.getElem_finRange]
      have hge : ¬ (seq.length + j < seq.length) := by omega
      simp [f, encodeRound, hge]
    rw [h1, h2, List.append_nil]
  unfold decodeRound
  dsimp only
  rw [hfilter, List.map_map, List.map_map]
  ext1
  · refine List.ext_getElem (by simp) fun j hj1 hj2 => by simp
  · refine List.ext_getElem (by simp [hcnt_len]) fun j hj1 hj2 => by simp

/-- Decode a fixed-width sequence of round tables into `List (List α × List ℕ)`. -/
def decodeRounds {α : Type*} {V : Finset α} {B k S_max : ℕ}
    (g : Fin S_max → Option (Fin B → Option ({v : α // v ∈ V} × Fin (k + 1)))) :
    List (List α × List ℕ) :=
  ((List.finRange S_max).filterMap g).map decodeRound

lemma decodeRounds_surjective {α : Type*} {V : Finset α} {B k S_max : ℕ}
    (roundSpecs : List (List α × List ℕ))
    (hs : roundSpecs.length ≤ S_max)
    (hspec : ∀ p ∈ roundSpecs, p.1.length ≤ B ∧ (∀ v ∈ p.1, v ∈ V) ∧
      p.2.length = p.1.length ∧ ∀ c ∈ p.2, c ≤ k) :
    ∃ g : Fin S_max → Option (Fin B → Option ({v : α // v ∈ V} × Fin (k + 1))),
      decodeRounds g = roundSpecs := by
  let g : Fin S_max → Option (Fin B → Option ({v : α // v ∈ V} × Fin (k + 1))) := fun i =>
    if h : i.val < roundSpecs.length then
      let p := roundSpecs[i.val]'h
      let hp := hspec p (List.getElem_mem h)
      some (encodeRound (B := B) (k := k) p.1 p.2 hp.2.1 hp.2.2.1 hp.2.2.2)
    else none
  refine ⟨g, ?_⟩
  unfold decodeRounds
  have hsplit : List.finRange S_max =
      (List.finRange roundSpecs.length).map (Fin.castLE hs) ++
      ((List.finRange S_max).drop roundSpecs.length) := by
    refine List.ext_getElem ?_ ?_
    · simp [hs]
    · intro j hj1 hj2
      rw [List.getElem_finRange]
      by_cases hlt : j < roundSpecs.length
      · rw [List.getElem_append_left (by simp [hlt])]
        simp
      · rw [List.getElem_append_right (by simp; omega)]
        simp only [List.length_map, List.length_finRange, List.getElem_drop, List.getElem_finRange]
        apply Fin.ext; dsimp; omega
  rw [hsplit, List.filterMap_append, List.filterMap_map]
  have h2 : ((List.finRange S_max).drop roundSpecs.length).filterMap g = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hi
    rw [List.getElem_drop, List.getElem_finRange]
    have hge : ¬ (roundSpecs.length + j < roundSpecs.length) := by omega
    simp [g, hge]
  rw [h2, List.append_nil]
  have h1 : (List.finRange roundSpecs.length).filterMap (g ∘ Fin.castLE hs) =
      (List.finRange roundSpecs.length).map fun i =>
        let p := roundSpecs[i.val]'i.isLt
        let hp := hspec p (List.getElem_mem i.isLt)
        encodeRound (B := B) (k := k) p.1 p.2 hp.2.1 hp.2.2.1 hp.2.2.2 := by
    rw [← List.filterMap_eq_map]
    refine List.filterMap_congr fun i _ => ?_
    simp [g, i.isLt]
  rw [h1, List.map_map]
  refine List.ext_getElem (by simp) fun j hj1 hj2 => ?_
  simp only [List.getElem_map, Function.comp_apply, List.getElem_finRange]
  have hp := hspec (roundSpecs[j]'hj2) (List.getElem_mem hj2)
  exact decodeRound_encodeRound _ _ hp.1 hp.2.1 hp.2.2.1 hp.2.2.2

/-- Every slot in `roundSlots seq cnts` has `sl.1 ⊆ V_big` when `∀ v ∈ seq, v ∈ V_big`. -/
lemma roundSlots_fst_subset {ι : Type*} [DecidableEq ι] {V_big : Finset ι}
    {seq : List ι} {cnts : List ℕ} (hseqV : ∀ v ∈ seq, v ∈ V_big) :
    ∀ sl ∈ roundSlots seq cnts, sl.1 ⊆ V_big := by
  intro sl hsl
  unfold roundSlots at hsl
  rcases List.mem_append.mp hsl with h1 | h2
  · rw [List.mem_flatMap] at h1
    obtain ⟨i, hi, hrep⟩ := h1
    have hi' : i < seq.length := List.mem_range.mp hi
    simp only [hi', ↓reduceDIte, List.mem_replicate] at hrep
    rw [hrep.2]
    intro v hv
    exact hseqV v (List.mem_of_mem_take (List.mem_toFinset.mp hv))
  · rw [List.mem_singleton.mp h2]
    intro v hv
    exact hseqV v (List.mem_toFinset.mp hv)

/-- Every slot in `allSlots roundSpecs W_all tailLen` has `sl.1 ⊆ V_big`. -/
lemma allSlots_fst_subset {ι : Type*} [DecidableEq ι] {V_big : Finset ι}
    {roundSpecs : List (List ι × List ℕ)} {W_all : Finset ι} {tailLen : ℕ}
    (hspecs : ∀ p ∈ roundSpecs, ∀ v ∈ p.1, v ∈ V_big)
    (hWall : W_all ⊆ V_big) :
    ∀ sl ∈ allSlots roundSpecs W_all tailLen, sl.1 ⊆ V_big := by
  intro sl hsl
  unfold allSlots at hsl
  rcases List.mem_append.mp hsl with h1 | h2
  · rw [List.mem_flatMap] at h1
    obtain ⟨p, hp, hpsl⟩ := h1
    exact roundSlots_fst_subset (hspecs p hp) sl hpsl
  · rw [(List.mem_replicate.mp h2).2]
    exact hWall

/-- **Explicit Combinatorial Cardinality Bound for `irreducibleCount k`**:
Injects `{M | IsIrreducibleCoveringSet M ∧ M.card = k}` into an explicit finite code space
parameterized by `(N, roundSpecs, W_all, modsFn)`, yielding an explicit upper bound in terms
of any small-prime bound `F_small` and big-prime budget bound `F_big`. -/
theorem irreducibleCount_le_explicit
    {k M_cut C K : ℕ} (hk : 1 ≤ k) (hM2 : 2 ≤ M_cut) (hC2 : 2 ≤ C)
    (hCsq : k < (C - 1) ^ 2) (hK1 : 1 ≤ K)
    {F_small : ℝ} (hFs0 : 0 ≤ F_small)
    {F_big : ℕ → ℝ} (hFb0 : ∀ x, 0 ≤ F_big x)
    (h_small : ∀ N, 0 < N → 1 + ∑ p ∈ N.primeFactors, N.factorization p * (p - 1) ≤ k →
      (dSmall N M_cut : ℝ) ≤ F_small)
    (h_big : ∀ N, 0 < N → 1 + ∑ p ∈ N.primeFactors, N.factorization p * (p - 1) ≤ k →
      ∀ W : Finset (CoordIdx N), W ⊆ bigCoords N M_cut → ∀ x : ℕ,
      (∑ p ∈ N.primeFactors.filter (M_cut ≤ ·), coordMult N W p * (p - 1)) ≤ x →
      (dBig N M_cut W : ℝ) ≤ F_big x) :
    let B := k / (M_cut - 1)
    let S_max := k / K
    (Erdos1189.irreducibleCount k : ℝ) ≤
      (2 : ℝ) ^ k *
      ((((B + 1 : ℝ) * (k + 1 : ℝ)) ^ B + 1) ^ S_max) *
      (2 : ℝ) ^ B *
      (2 * F_small) ^ k *
      (∑ R ∈ Finset.range (k + 1),
        (∏ t ∈ Finset.range R, F_big (t + B * C)) *
        (F_big (R + B * (C + K) + B ^ 2)) ^ (k - R)) := by
  intro B S_max
  let GoodN : Finset ℕ := (Finset.Icc 1 (2 ^ k)).filter fun N =>
    1 + ∑ p ∈ N.primeFactors, N.factorization p * (p - 1) ≤ k
  let RoundEnc (N : ℕ) :=
    Fin S_max → Option (Fin B → Option ({v : CoordIdx N // v ∈ bigCoords N M_cut} × Fin (k + 1)))
  let SubBig (N : ℕ) := {W : Finset (CoordIdx N) // W ⊆ bigCoords N M_cut}
  let MetaType := Σ N : {N : ℕ // N ∈ GoodN}, RoundEnc N.1 × SubBig N.1
  let metaRounds (m : MetaType) : List (List (CoordIdx m.1.1) × List ℕ) :=
    decodeRounds m.2.1
  let metaR (m : MetaType) : ℕ := ((metaRounds m).map roundSize).sum
  let metaSlots (m : MetaType) : List (Finset (CoordIdx m.1.1) × Option (CoordIdx m.1.1)) :=
    allSlots (metaRounds m) m.2.2.1 (k - metaR m)
  let ValidMeta (m : MetaType) : Prop :=
    metaR m ≤ k ∧
    ∀ t (ht : t < k),
      let sl := (metaSlots m)[t]'(by
        dsimp only [metaSlots]; rw [allSlots_length]; change metaR m + (k - metaR m) > t; omega)
      sl.1 ⊆ bigCoords m.1.1 M_cut ∧
      (t < metaR m → ∑ v ∈ sl.1, v.1.1 ≤ t + B * C) ∧
      (metaR m ≤ t → ∑ v ∈ sl.1, v.1.1 ≤ metaR m + B * (C + K) + B ^ 2)
  let ValidMetaType := {m : MetaType // ValidMeta m}
  let metaSlot (m : ValidMetaType) (t : Fin k) :
      Finset (CoordIdx m.1.1.1) × Option (CoordIdx m.1.1.1) :=
    (metaSlots m.1)[t.val]'(by
      have hR := m.2.1
      dsimp only [metaSlots]; rw [allSlots_length]; change metaR m.1 + (k - metaR m.1) > t.val; omega)
  let Code := Σ m : ValidMetaType, (t : Fin k) → {d : ℕ // d ∈ slotDivs m.1.1.1 M_cut (metaSlot m t)}
  let decode : Code → Finset ℕ := fun c => Finset.univ.image fun t : Fin k => (c.2 t).1
  -- Step 1: Show every irreducible covering set `M` of size `k` is in `Finset.univ.image decode`!
  have hcov : {M : Finset ℕ | Erdos1189.IsIrreducibleCoveringSet M ∧ M.card = k} ⊆
      ((Finset.univ.image decode : Finset (Finset ℕ)) : Set (Finset ℕ)) := by
    intro M hM
    rcases hM with ⟨irr, hMcard⟩
    simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and]
    obtain ⟨A, hA, hAcard, hAimg⟩ := normalized_family irr
    obtain ⟨hNpos, hdvdN, hbox_card, hbox_min, _⟩ := minimalSys_to_minCover hA
    set N := (A.image Prod.fst).lcm id
    have hNeq : N = M.lcm id := by dsimp only [N]; rw [hAimg]
    obtain ⟨_, hsimp⟩ := simpson_lcm_bound irr
    rw [← hNeq, hMcard] at hsimp
    have hNlcm : N ≤ 2 ^ k := by
      calc N = M.lcm id := hNeq
        _ ≤ 2 ^ (M.card - 1) := lcm_le_two_pow irr
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
    have hNgood : N ∈ GoodN := Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hNpos, hNlcm⟩, hsimp⟩
    let A_box := A.image fun p => arithHPlane N p.1 p.2
    have hAbox_card : A_box.card = k := by rw [hbox_card, hAcard, hMcard]
    have hVbig_le : (bigCoords N M_cut).card ≤ B := bigCoords_card_le hM2 hsimp
    obtain ⟨roundSpecs, R_card, W_all, ordA, hlenK, hRsum, hRle, hspecs, hWall_sub,
        hord_nod, hord_len, hord_fin, hord_inv⟩ :=
      iterated_round_decomp hbox_min (bigCoords N M_cut) hC2 (by omega : A_box.card < (C - 1) ^ 2) hK1
    rw [hAbox_card] at hRle hord_len hspecs hord_inv
    have hs_le : roundSpecs.length ≤ S_max := by
      rw [Nat.le_div_iff_mul_le (by omega : 0 < K)]
      omega
    have hspec_enc : ∀ p ∈ roundSpecs, p.1.length ≤ B ∧ (∀ v ∈ p.1, v ∈ bigCoords N M_cut) ∧
        p.2.length = p.1.length ∧ ∀ c ∈ p.2, c ≤ k := by
      intro p hp
      rcases hspecs p hp with ⟨hnod, hsub, hlen2, hcle⟩
      have hlen1 : p.1.length ≤ B := by
        calc p.1.length = p.1.toFinset.card := (List.toFinset_card_of_nodup hnod).symm
          _ ≤ (bigCoords N M_cut).card := Finset.card_le_card (fun v hv => hsub v (List.mem_toFinset.mp hv))
          _ ≤ B := hVbig_le
      exact ⟨hlen1, hsub, hlen2, hcle⟩
    obtain ⟨g, hg_dec⟩ := decodeRounds_surjective roundSpecs hs_le hspec_enc
    let m0 : MetaType := ⟨⟨N, hNgood⟩, (g, ⟨W_all, hWall_sub⟩)⟩
    have hm0_rounds : metaRounds m0 = roundSpecs := hg_dec
    have hm0_R : metaR m0 = R_card := by
      dsimp only [metaR]; rw [hm0_rounds, ← hRsum]
    have hm0_slots : metaSlots m0 = allSlots roundSpecs W_all (k - R_card) := by
      dsimp only [metaSlots]; rw [hm0_rounds, hm0_R]
    have hm0_valid : ValidMeta m0 := by
      refine ⟨by omega, ?_⟩
      intro t ht
      have hsl_eq : (metaSlots m0)[t]'(by
          dsimp only [metaSlots]; rw [allSlots_length]; change metaR m0 + (k - metaR m0) > t; omega) =
          (allSlots roundSpecs W_all (k - R_card))[t]'(by rw [allSlots_length]; omega) := by
        simp only [hm0_slots]
      have hinv := hord_inv t (by rw [allSlots_length]; omega) (by omega)
      have hsub_sl : ((allSlots roundSpecs W_all (k - R_card))[t]'(by rw [allSlots_length]; omega)).1 ⊆
          bigCoords N M_cut :=
        allSlots_fst_subset (fun p hp => (hspecs p hp).2.1) hWall_sub _ (List.getElem_mem _)
      dsimp only
      rw [hsl_eq]
      refine ⟨hsub_sl, fun hlt => ?_, fun hge => ?_⟩
      · have h1 : ∑ v ∈ ((allSlots roundSpecs W_all (k - R_card))[t]'(by rw [allSlots_length]; omega)).1,
            v.1.1 ≤ t + (bigCoords N M_cut).card * C := by
          simpa only [Fintype.card_fin] using hinv.2.1 (by omega)
        have hmul : (bigCoords N M_cut).card * C ≤ B * C := Nat.mul_le_mul_right C hVbig_le
        exact h1.trans (Nat.add_le_add_left hmul t)
      · have h2 : ∑ v ∈ ((allSlots roundSpecs W_all (k - R_card))[t]'(by rw [allSlots_length]; omega)).1,
            v.1.1 ≤ R_card + (bigCoords N M_cut).card * (C + K) + (bigCoords N M_cut).card ^ 2 := by
          simpa only [Fintype.card_fin] using hinv.2.2 (by omega)
        have hmul1 : (bigCoords N M_cut).card * (C + K) ≤ B * (C + K) :=
          Nat.mul_le_mul_right _ hVbig_le
        have hmul2 : (bigCoords N M_cut).card ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left hVbig_le 2
        rw [hm0_R]
        exact h2.trans (Nat.add_le_add (Nat.add_le_add_left hmul1 R_card) hmul2)
    -- Recover the unique `(m, a) ∈ A` for each `H ∈ A_box`
    have hinjA : Set.InjOn (fun p : ℕ × ℤ => arithHPlane N p.1 p.2) A := by
      have h := hbox_card
      exact (Finset.card_image_iff).mp h
    let pickA : (t : Fin k) → {p : ℕ × ℤ // p ∈ A ∧ arithHPlane N p.1 p.2 = ordA[t.val]'(by omega)} :=
      fun t =>
        have hmem : ordA[t.val]'(by omega) ∈ A_box := by
          dsimp only [A_box]
          rw [← hord_fin, List.mem_toFinset]; exact List.getElem_mem _
        let hEx := Finset.mem_image.mp hmem
        ⟨Classical.choose hEx, Classical.choose_spec hEx⟩
    let mFn : (t : Fin k) → {d : ℕ // d ∈ slotDivs N M_cut (metaSlot ⟨m0, hm0_valid⟩ t)} :=
      fun t =>
        let p := (pickA t).1
        have hpA : p ∈ A := (pickA t).2.1
        have hpH : arithHPlane N p.1 p.2 = ordA[t.val]'(by omega) := (pickA t).2.2
        have hp_div : p.1 ∈ N.divisors := Nat.mem_divisors.mpr ⟨hdvdN p hpA, hNpos.ne'⟩
        have hp_sub : divBigCoords N M_cut p.1 ⊆ slotAllowed (metaSlot ⟨m0, hm0_valid⟩ t) := by
          rw [← arithHPlane_fixed_inter_bigCoords N M_cut p.1 p.2, hpH]
          have h1 := (hord_inv t.val (by rw [allSlots_length]; omega) (by omega)).1
          have hsl_eq : metaSlot ⟨m0, hm0_valid⟩ t =
              (allSlots roundSpecs W_all (k - R_card))[t.val]'(by rw [allSlots_length]; omega) := by
            dsimp only [metaSlot]; simp only [hm0_slots]
          rw [hsl_eq]
          exact h1
        ⟨p.1, Finset.mem_filter.mpr ⟨hp_div, hp_sub⟩⟩
    refine ⟨⟨⟨m0, hm0_valid⟩, mFn⟩, ?_⟩
    -- Prove `decode ⟨⟨m0, hm0_valid⟩, mFn⟩ = M`!
    ext m
    simp only [decode, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨t, rfl⟩
      rw [← hAimg]
      exact Finset.mem_image_of_mem Prod.fst (pickA t).2.1
    · intro hmM
      rw [← hAimg] at hmM
      obtain ⟨p, hpA, rfl⟩ := Finset.mem_image.mp hmM
      have hH_mem : arithHPlane N p.1 p.2 ∈ ordA := by
        rw [← List.mem_toFinset, hord_fin]
        exact Finset.mem_image_of_mem _ hpA
      obtain ⟨t, ht, hord_eq⟩ := List.getElem_of_mem hH_mem
      refine ⟨⟨t, by omega⟩, ?_⟩
      have hqA := (pickA ⟨t, by omega⟩).2.1
      have hqH := (pickA ⟨t, by omega⟩).2.2
      have hpq : (pickA ⟨t, by omega⟩).1 = p := hinjA hqA hpA (hqH.trans hord_eq)
      exact congrArg Prod.fst hpq
  -- Step 2: Bound `irreducibleCount k ≤ Fintype.card Code`!
  have hncard_le : Erdos1189.irreducibleCount k ≤ Fintype.card Code := by
    calc Erdos1189.irreducibleCount k
        = ({M : Finset ℕ | Erdos1189.IsIrreducibleCoveringSet M ∧ M.card = k}).ncard := rfl
      _ ≤ ((Finset.univ.image decode : Finset (Finset ℕ)) : Set (Finset ℕ)).ncard :=
          Set.ncard_le_ncard hcov (Finset.finite_toSet _)
      _ = (Finset.univ.image decode).card := Set.ncard_coe_finset _
      _ ≤ (Finset.univ : Finset Code).card := Finset.card_image_le
      _ = Fintype.card Code := Finset.card_univ
  -- Step 3: Evaluate `Fintype.card Code` in `ℝ` and bound each fiber + metadata count!
  set TailSum : ℝ := ∑ R ∈ Finset.range (k + 1),
    (∏ t ∈ Finset.range R, F_big (t + B * C)) *
    (F_big (R + B * (C + K) + B ^ 2)) ^ (k - R)
  have hTail_nonneg : ∀ R ∈ Finset.range (k + 1),
      0 ≤ (∏ t ∈ Finset.range R, F_big (t + B * C)) *
        (F_big (R + B * (C + K) + B ^ 2)) ^ (k - R) := fun R _ =>
    mul_nonneg (Finset.prod_nonneg fun t _ => hFb0 _) (pow_nonneg (hFb0 _) _)
  have hTail0 : 0 ≤ TailSum := Finset.sum_nonneg hTail_nonneg
  have hfiber_le : ∀ m : ValidMetaType,
      ((∏ t : Fin k, (slotDivs m.1.1.1 M_cut (metaSlot m t)).card : ℕ) : ℝ) ≤
        (2 * F_small) ^ k * TailSum := by
    intro m
    have hNmem := Finset.mem_filter.mp m.1.1.2
    have hNpos : 0 < m.1.1.1 := (Finset.mem_Icc.mp hNmem.1).1
    have hNsimp := hNmem.2
    have hRle : metaR m.1 ≤ k := m.2.1
    push_cast
    have hper_t : ∀ t : Fin k,
        ((slotDivs m.1.1.1 M_cut (metaSlot m t)).card : ℝ) ≤
          (2 * F_small) *
            if t.val < metaR m.1 then F_big (t.val + B * C)
            else F_big (metaR m.1 + B * (C + K) + B ^ 2) := by
      intro t
      have hcard := card_slotDivs_le (M_cut := M_cut) hNpos (metaSlot m t)
      have hcardR : ((slotDivs m.1.1.1 M_cut (metaSlot m t)).card : ℝ) ≤
          2 * (dSmall m.1.1.1 M_cut : ℝ) * (dBig m.1.1.1 M_cut (metaSlot m t).1 : ℝ) := by
        exact_mod_cast hcard
      have hsmR : (dSmall m.1.1.1 M_cut : ℝ) ≤ F_small := h_small m.1.1.1 hNpos hNsimp
      have hm_t := m.2.2 t.val t.isLt
      have hsub_t : (metaSlot m t).1 ⊆ bigCoords m.1.1.1 M_cut := hm_t.1
      have hwt_le : ∑ p ∈ m.1.1.1.primeFactors.filter (M_cut ≤ ·),
          coordMult m.1.1.1 (metaSlot m t).1 p * (p - 1) ≤
          ∑ v ∈ (metaSlot m t).1, v.1.1 := by
        rw [sum_coordMult_mul_sub_one hsub_t]
        exact Finset.sum_le_sum fun v _ => Nat.sub_le _ _
      have hbgR : (dBig m.1.1.1 M_cut (metaSlot m t).1 : ℝ) ≤
          if t.val < metaR m.1 then F_big (t.val + B * C)
          else F_big (metaR m.1 + B * (C + K) + B ^ 2) := by
        split_ifs with hlt
        · exact h_big m.1.1.1 hNpos hNsimp (metaSlot m t).1 hsub_t _ (hwt_le.trans (hm_t.2.1 hlt))
        · exact h_big m.1.1.1 hNpos hNsimp (metaSlot m t).1 hsub_t _
            (hwt_le.trans (hm_t.2.2 (by omega)))
      calc ((slotDivs m.1.1.1 M_cut (metaSlot m t)).card : ℝ)
          ≤ (2 * (dSmall m.1.1.1 M_cut : ℝ)) * (dBig m.1.1.1 M_cut (metaSlot m t).1 : ℝ) := hcardR
        _ ≤ (2 * F_small) * (if t.val < metaR m.1 then F_big (t.val + B * C)
            else F_big (metaR m.1 + B * (C + K) + B ^ 2)) := by
            refine mul_le_mul (by linarith) hbgR (Nat.cast_nonneg _) (by linarith)
    calc ∏ t : Fin k, ((slotDivs m.1.1.1 M_cut (metaSlot m t)).card : ℝ)
        ≤ ∏ t : Fin k, ((2 * F_small) *
            if t.val < metaR m.1 then F_big (t.val + B * C)
            else F_big (metaR m.1 + B * (C + K) + B ^ 2)) :=
          Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun t _ => hper_t t)
      _ = (2 * F_small) ^ k * ∏ t ∈ Finset.range k,
            (if t < metaR m.1 then F_big (t + B * C)
             else F_big (metaR m.1 + B * (C + K) + B ^ 2)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          congr 1
          exact Fin.prod_univ_eq_prod_range
            (fun t => if t < metaR m.1 then F_big (t + B * C)
              else F_big (metaR m.1 + B * (C + K) + B ^ 2)) k
      _ = (2 * F_small) ^ k *
            ((∏ t ∈ Finset.range (metaR m.1), F_big (t + B * C)) *
             (F_big (metaR m.1 + B * (C + K) + B ^ 2)) ^ (k - metaR m.1)) := by
          congr 1
          have hsplit : Finset.range k =
              Finset.range (metaR m.1) ∪ (Finset.range k \ Finset.range (metaR m.1)) :=
            (Finset.union_sdiff_of_subset (Finset.range_mono hRle)).symm
          rw [hsplit, Finset.prod_union Finset.disjoint_sdiff]
          congr 1
          · refine Finset.prod_congr rfl fun t ht => if_pos (Finset.mem_range.mp ht)
          · have hconst : ∏ t ∈ Finset.range k \ Finset.range (metaR m.1),
                (if t < metaR m.1 then F_big (t + B * C)
                 else F_big (metaR m.1 + B * (C + K) + B ^ 2)) =
                ∏ _t ∈ Finset.range k \ Finset.range (metaR m.1),
                  F_big (metaR m.1 + B * (C + K) + B ^ 2) := by
              refine Finset.prod_congr rfl fun t ht => ?_
              have hnot : ¬ (t < metaR m.1) := by
                have := (Finset.mem_sdiff.mp ht).2
                rw [Finset.mem_range] at this; exact this
              exact if_neg hnot
            rw [hconst, Finset.prod_const,
                Finset.card_sdiff_of_subset (Finset.range_mono hRle), Finset.card_range, Finset.card_range]
      _ ≤ (2 * F_small) ^ k * TailSum := by
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by linarith) _)
          exact Finset.single_le_sum hTail_nonneg (Finset.mem_range.mpr (by omega))
  -- Step 4: Bound `Fintype.card ValidMetaType ≤ 2^k * (((B+1)*(k+1))^B + 1)^S_max * 2^B`!
  have hmeta_card : (Fintype.card ValidMetaType : ℝ) ≤
      (2 : ℝ) ^ k * ((((B + 1 : ℝ) * (k + 1 : ℝ)) ^ B + 1) ^ S_max) * (2 : ℝ) ^ B := by
    have h1 : Fintype.card ValidMetaType ≤ Fintype.card MetaType :=
      Fintype.card_subtype_le _
    have h2 : Fintype.card MetaType ≤
        2 ^ k * (((B + 1) * (k + 1)) ^ B + 1) ^ S_max * 2 ^ B := by
      rw [Fintype.card_sigma]
      have hGood_le : (Finset.univ : Finset {N : ℕ // N ∈ GoodN}).card ≤ 2 ^ k := by
        rw [Finset.card_univ, Fintype.card_coe]
        calc GoodN.card ≤ (Finset.Icc 1 (2 ^ k)).card := Finset.card_le_card (Finset.filter_subset _ _)
          _ = 2 ^ k := by simp
      have hterm : ∀ N : {N : ℕ // N ∈ GoodN},
          Fintype.card (RoundEnc N.1 × SubBig N.1) ≤
            (((B + 1) * (k + 1)) ^ B + 1) ^ S_max * 2 ^ B := by
        intro N
        have hNsimp := (Finset.mem_filter.mp N.2).2
        have hVle : (bigCoords N.1 M_cut).card ≤ B := bigCoords_card_le hM2 hNsimp
        rw [Fintype.card_prod]
        refine Nat.mul_le_mul ?_ ?_
        · dsimp only [RoundEnc]
          rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_option,
              Fintype.card_fun, Fintype.card_fin, Fintype.card_option,
              Fintype.card_prod, Fintype.card_coe, Fintype.card_fin]
          refine Nat.pow_le_pow_left ?_ S_max
          refine Nat.add_le_add_right (Nat.pow_le_pow_left ?_ B) 1
          have h1' : (bigCoords N.1 M_cut).card * (k + 1) ≤ B * (k + 1) :=
            Nat.mul_le_mul_right _ hVle
          have h2' : B * (k + 1) + 1 ≤ (B + 1) * (k + 1) := by
            rw [Nat.add_mul, one_mul]; omega
          omega
        · dsimp only [SubBig]
          have heq : Fintype.card {W : Finset (CoordIdx N.1) // W ⊆ bigCoords N.1 M_cut} =
              (bigCoords N.1 M_cut).powerset.card := by
            rw [← Fintype.card_coe]
            refine Fintype.card_congr ⟨fun x => ⟨x.1, Finset.mem_powerset.mpr x.2⟩,
              fun x => ⟨x.1, Finset.mem_powerset.mp x.2⟩, fun _ => rfl, fun _ => rfl⟩
          rw [heq, Finset.card_powerset]
          exact Nat.pow_le_pow_right (by omega) hVle
      calc ∑ N : {N : ℕ // N ∈ GoodN}, Fintype.card (RoundEnc N.1 × SubBig N.1)
          ≤ ∑ _N : {N : ℕ // N ∈ GoodN}, ((((B + 1) * (k + 1)) ^ B + 1) ^ S_max * 2 ^ B) :=
            Finset.sum_le_sum fun N _ => hterm N
        _ = (Finset.univ : Finset {N : ℕ // N ∈ GoodN}).card *
            ((((B + 1) * (k + 1)) ^ B + 1) ^ S_max * 2 ^ B) := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ 2 ^ k * ((((B + 1) * (k + 1)) ^ B + 1) ^ S_max * 2 ^ B) :=
            Nat.mul_le_mul_right _ hGood_le
        _ = 2 ^ k * (((B + 1) * (k + 1)) ^ B + 1) ^ S_max * 2 ^ B := by ring
    exact_mod_cast h1.trans h2
  -- Step 5: Combine everything!
  calc (Erdos1189.irreducibleCount k : ℝ)
      ≤ (Fintype.card Code : ℝ) := by exact_mod_cast hncard_le
    _ = ∑ m : ValidMetaType, ((∏ t : Fin k, (slotDivs m.1.1.1 M_cut (metaSlot m t)).card : ℕ) : ℝ) := by
        have hc : Fintype.card Code =
            ∑ m : ValidMetaType, ∏ t : Fin k, (slotDivs m.1.1.1 M_cut (metaSlot m t)).card := by
          dsimp only [Code]
          rw [Fintype.card_sigma]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Fintype.card_pi]
          refine Finset.prod_congr rfl fun t _ => Fintype.card_coe _
        rw [hc, Nat.cast_sum]
    _ ≤ ∑ _m : ValidMetaType, ((2 * F_small) ^ k * TailSum) :=
        Finset.sum_le_sum fun m _ => hfiber_le m
    _ = (Fintype.card ValidMetaType : ℝ) * ((2 * F_small) ^ k * TailSum) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ ((2 : ℝ) ^ k * ((((B + 1 : ℝ) * (k + 1 : ℝ)) ^ B + 1) ^ S_max) * (2 : ℝ) ^ B) *
          ((2 * F_small) ^ k * TailSum) :=
        mul_le_mul_of_nonneg_right hmeta_card (mul_nonneg (pow_nonneg (by linarith) _) hTail0)
    _ = (2 : ℝ) ^ k * ((((B + 1 : ℝ) * (k + 1 : ℝ)) ^ B + 1) ^ S_max) * (2 : ℝ) ^ B *
          (2 * F_small) ^ k * TailSum := by ring

end CountingInjection

end Erdos1189BBMST

/- Section 5: PNT Prime-Counting Bound, Discrete Prime-Sum Lemma, Lagrange Divisor Bounds,
   Discrete 2/3 Integral Bound, and Final BBMST Asymptotic Proof. -/

namespace Erdos1189BBMST

open Finset Real Filter
open scoped Classical

section AnalyticBounds

/-- Helper identity: `a / √(a * b) = √(a / b)` for `a, b > 0`. -/
lemma div_sqrt_mul_eq_sqrt_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a / Real.sqrt (a * b) = Real.sqrt (a / b) := by
  rw [Real.sqrt_mul ha.le, Real.sqrt_div ha.le]
  have hsa : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have hsb : Real.sqrt b ≠ 0 := (Real.sqrt_pos.mpr hb).ne'
  field_simp [hsa, hsb]
  exact (Real.sq_sqrt ha.le).symm

/-- Helper identity: `√(a * b) / b = √(a / b)` for `a, b > 0`. -/
lemma sqrt_mul_div_eq_sqrt_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a * b) / b = Real.sqrt (a / b) := by
  rw [Real.sqrt_mul ha.le, Real.sqrt_div ha.le]
  have hsb : Real.sqrt b ≠ 0 := (Real.sqrt_pos.mpr hb).ne'
  field_simp [hsb]
  exact Real.sq_sqrt hb.le

/-- Finite set of primes `≤ n`. -/
def primesLE (n : ℕ) : Finset ℕ := (Finset.Iic n).filter Nat.Prime

/-- PNT upper bound on `π(x)`: for every `δ > 0`, eventually `|primesLE ⌊x⌋₊| ≤ (1 + δ) * x / log x`. -/
lemma primeCounting_upper_pnt {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop,
      ((primesLE ⌊x⌋₊).card : ℝ) ≤ (1 + δ) * (x / Real.log x) := by
  let u : ℝ := min (δ / 4) (1 / 4)
  have hu_pos : 0 < u := lt_min (by linarith) (by norm_num)
  have hu_le : u ≤ 1 / 4 := min_le_right _ _
  have hu_d : u ≤ δ / 4 := min_le_left _ _
  -- From `chebyshev_asymptotic : θ ~[atTop] id`, eventually `θ x ≤ (1 + u) * x`.
  have htheta : ∀ᶠ x : ℝ in atTop, Chebyshev.theta x ≤ (1 + u) * x := by
    have hlim : Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (nhds 1) :=
      (Asymptotics.isEquivalent_iff_tendsto_one
        (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx; exact hx.ne')).mp
        _root_.chebyshev_asymptotic
    have hev := hlim.eventually (Iio_mem_nhds (by linarith : (1 : ℝ) < 1 + u))
    filter_upwards [hev, eventually_gt_atTop (1 : ℝ)] with x hx hx1
    have hdiv : Chebyshev.theta x / x < 1 + u := hx
    exact ((div_lt_iff₀ (by linarith : (0 : ℝ) < x)).mp hdiv).le
  -- `log (log x) / log x → 0`
  have hloglog : Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x) atTop (nhds 0) :=
    ((isLittleO_log_rpow_atTop one_pos).tendsto_div_nhds_zero.comp Real.tendsto_log_atTop).congr'
      (by filter_upwards [eventually_gt_atTop (1 : ℝ)] with x _; simp [Function.comp_apply])
  have hev_loglog : ∀ᶠ x : ℝ in atTop, 2 * Real.log (Real.log x) ≤ u * Real.log x := by
    have hev := hloglog.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < u / 2))
    filter_upwards [hev, eventually_gt_atTop (Real.exp 1)] with x hx hx1
    have hlog_pos : 0 < Real.log x := by
      have : 1 < Real.log x := by
        rw [← Real.log_exp 1]
        exact Real.log_lt_log (Real.exp_pos 1) hx1
      linarith
    have h1 : Real.log (Real.log x) / Real.log x < u / 2 := hx
    have h2 : Real.log (Real.log x) < (u / 2) * Real.log x := (div_lt_iff₀ hlog_pos).mp h1
    linarith
  have hev_invlog : ∀ᶠ x : ℝ in atTop, 1 / Real.log x ≤ u := by
    have h1 : Tendsto (fun x : ℝ => (Real.log x)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
    have hev := h1.eventually (Iio_mem_nhds hu_pos)
    filter_upwards [hev] with x hx
    rw [one_div]; exact le_of_lt hx
  have hev_xlog2 : ∀ᶠ x : ℝ in atTop, Real.exp 1 < x / (Real.log x) ^ 2 := by
    have h0 : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) atTop (nhds 0) :=
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    have hsq : Tendsto (fun x : ℝ => (Real.log x / x ^ (1 / 2 : ℝ)) ^ 2) atTop (nhds 0) := by
      simpa using h0.pow 2
    have h1 : Tendsto (fun x : ℝ => (Real.log x) ^ 2 / x) atTop (nhds 0) := by
      refine hsq.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [div_pow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hx.le]
    have h2 := h1.eventually (Iio_mem_nhds (inv_pos.mpr (Real.exp_pos 1)))
    filter_upwards [h2, eventually_gt_atTop (Real.exp 1)] with x hx hx1
    have hlog_pos : 0 < Real.log x := by
      have : 1 < Real.log x := by
        rw [← Real.log_exp 1]; exact Real.log_lt_log (Real.exp_pos 1) hx1
      linarith
    have hxpos : 0 < x := lt_trans (Real.exp_pos 1) hx1
    have hsq_pos : 0 < (Real.log x) ^ 2 := sq_pos_of_pos hlog_pos
    rw [lt_div_iff₀ hsq_pos]
    have hlt : (Real.log x) ^ 2 / x < (Real.exp 1)⁻¹ := hx
    have hmul : (Real.log x) ^ 2 < (Real.exp 1)⁻¹ * x := (div_lt_iff₀ hxpos).mp hlt
    calc Real.exp 1 * (Real.log x) ^ 2
        < Real.exp 1 * ((Real.exp 1)⁻¹ * x) := mul_lt_mul_of_pos_left hmul (Real.exp_pos 1)
      _ = x := by field_simp [(Real.exp_pos 1).ne']
  filter_upwards [htheta, hev_loglog, hev_invlog, hev_xlog2, eventually_gt_atTop (Real.exp 2)] with
      x hth hll hinv hxlog2 hx2
  have hxpos : 0 < x := lt_trans (Real.exp_pos 2) hx2
  have hlog_gt1 : 1 < Real.log x := by
    have : (2 : ℝ) < Real.log x := by
      rw [← Real.log_exp 2]; exact Real.log_lt_log (Real.exp_pos 2) hx2
    linarith
  have hlog_pos : 0 < Real.log x := by linarith
  let y : ℝ := x / (Real.log x) ^ 2
  have hy_gt : Real.exp 1 < y := hxlog2
  have hy_pos : 0 < y := lt_trans (Real.exp_pos 1) hy_gt
  have hlogy_pos : 0 < Real.log y := by
    have : 1 < Real.log y := by
      rw [← Real.log_exp 1]; exact Real.log_lt_log (Real.exp_pos 1) hy_gt
    linarith
  have hlogy_ge : (1 - u) * Real.log x ≤ Real.log y := by
    have hlog_eq : Real.log y = Real.log x - 2 * Real.log (Real.log x) := by
      dsimp only [y]
      rw [Real.log_div hxpos.ne' (sq_pos_of_pos hlog_pos).ne', Real.log_pow]
      ring
    linarith
  -- Split `primesLE ⌊x⌋₊` at `y` (keeping `p : ℕ`!)
  let P_lo : Finset ℕ := (primesLE ⌊x⌋₊).filter fun p : ℕ => (p : ℝ) ≤ y
  let P_hi : Finset ℕ := (primesLE ⌊x⌋₊).filter fun p : ℕ => ¬ ((p : ℝ) ≤ y)
  have hcard_split : ((primesLE ⌊x⌋₊).card : ℝ) = (P_lo.card : ℝ) + (P_hi.card : ℝ) := by
    have h := Finset.sum_filter_add_sum_filter_not (primesLE ⌊x⌋₊) (fun p : ℕ => (p : ℝ) ≤ y)
      (fun _ => (1 : ℝ))
    simpa [P_lo, P_hi] using h.symm
  have hlo_le : (P_lo.card : ℝ) ≤ y := by
    have hsub : P_lo ⊆ Finset.Icc 1 ⌊y⌋₊ := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpP, hpy⟩
      have hp_prime : p.Prime := (Finset.mem_filter.mp hpP).2
      exact Finset.mem_Icc.mpr ⟨hp_prime.one_le, Nat.le_floor hpy⟩
    have hc : P_lo.card ≤ ⌊y⌋₊ := by
      calc P_lo.card ≤ (Finset.Icc 1 ⌊y⌋₊).card := Finset.card_le_card hsub
        _ = ⌊y⌋₊ := by simp
    exact (Nat.cast_le.mpr hc).trans (Nat.floor_le hy_pos.le)
  have hhi_le : (P_hi.card : ℝ) * Real.log y ≤ Chebyshev.theta x := by
    have htheta_eq : Chebyshev.theta x = ∑ p ∈ primesLE ⌊x⌋₊, Real.log (p : ℝ) := by
      unfold Chebyshev.theta
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext p
      simp only [primesLE, Finset.mem_filter, Finset.mem_Iic, Finset.mem_Ioc]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1.2, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨h2.pos, h1⟩, h2⟩⟩
    rw [htheta_eq]
    calc (P_hi.card : ℝ) * Real.log y
        = ∑ _p ∈ P_hi, Real.log y := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ P_hi, Real.log (p : ℝ) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hgt : y < (p : ℝ) := not_le.mp (Finset.mem_filter.mp hp).2
          exact Real.log_le_log hy_pos hgt.le
      _ ≤ ∑ p ∈ primesLE ⌊x⌋₊, Real.log (p : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
          intro p hp _
          have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
            exact_mod_cast (Finset.mem_filter.mp hp).2.one_le
          exact Real.log_nonneg hp1
  have hhi_div : (P_hi.card : ℝ) ≤ ((1 + u) / (1 - u)) * (x / Real.log x) := by
    have h1 : (P_hi.card : ℝ) * ((1 - u) * Real.log x) ≤ (1 + u) * x := by
      calc (P_hi.card : ℝ) * ((1 - u) * Real.log x)
          ≤ (P_hi.card : ℝ) * Real.log y := mul_le_mul_of_nonneg_left hlogy_ge (Nat.cast_nonneg _)
        _ ≤ Chebyshev.theta x := hhi_le
        _ ≤ (1 + u) * x := hth
    have hden_pos : 0 < (1 - u) * Real.log x := mul_pos (by linarith) hlog_pos
    have h2 : (P_hi.card : ℝ) ≤ ((1 + u) * x) / ((1 - u) * Real.log x) :=
      (le_div_iff₀ hden_pos).mpr h1
    calc (P_hi.card : ℝ) ≤ ((1 + u) * x) / ((1 - u) * Real.log x) := h2
      _ = ((1 + u) / (1 - u)) * (x / Real.log x) := by
          field_simp [(by linarith : (1 : ℝ) - u ≠ 0), hlog_pos.ne']
  have hy_bound : y ≤ u * (x / Real.log x) := by
    have h1 : y = (1 / Real.log x) * (x / Real.log x) := by
      dsimp only [y]; field_simp [hlog_pos.ne']
    rw [h1]
    exact mul_le_mul_of_nonneg_right hinv (div_nonneg hxpos.le hlog_pos.le)
  have hcoeff : u + (1 + u) / (1 - u) ≤ 1 + δ := by
    have h1 : (1 + u) / (1 - u) ≤ 1 + 3 * u := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - u)]
      nlinarith
    linarith
  rw [hcard_split]
  calc (P_lo.card : ℝ) + (P_hi.card : ℝ)
      ≤ u * (x / Real.log x) + ((1 + u) / (1 - u)) * (x / Real.log x) :=
        add_le_add (hlo_le.trans hy_bound) hhi_div
    _ = (u + (1 + u) / (1 - u)) * (x / Real.log x) := by ring
    _ ≤ (1 + δ) * (x / Real.log x) :=
        mul_le_mul_of_nonneg_right hcoeff (div_nonneg hxpos.le hlog_pos.le)

/-- **Discrete Prime-Sum Lemma**: for every `δ > 0`, there exists `X₀ ≥ 4` such that for all `X ≥ X₀`,
`∑ p ∈ primesLE ⌊X⌋₊, (X - p) ≤ (1 + δ) * X^2 / (2 * log X)`. -/
lemma sum_primes_sub_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ X₀ : ℝ, 4 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      ∑ p ∈ primesLE ⌊X⌋₊, (X - (p : ℝ)) ≤ (1 + δ) * X ^ 2 / (2 * Real.log X) := by
  let u : ℝ := min (δ / 8) (1 / 8)
  have hu_pos : 0 < u := lt_min (by linarith) (by norm_num)
  have hu_le : u ≤ 1 / 8 := min_le_right _ _
  have hu_d : u ≤ δ / 8 := min_le_left _ _
  let m : ℕ := max 1 ⌈1 / u⌉₊
  have hm_pos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hm_Rpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
  have h1m_le : 1 / (m : ℝ) ≤ u := by
    have h1 : 1 / u ≤ (m : ℝ) := (Nat.le_ceil (1 / u)).trans (by exact_mod_cast le_max_right 1 _)
    rw [div_le_iff₀ hm_Rpos]
    have h2 : 1 ≤ u * (m : ℝ) := by
      have := (div_le_iff₀ hu_pos).mp h1
      linarith
    linarith
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.mp (primeCounting_upper_pnt hu_pos)
  let X₀ : ℝ := max 4 (max ((m : ℝ) * max X₁ 4) (Real.exp (Real.log (m : ℝ) / u)))
  have hX₀_4 : 4 ≤ X₀ := le_max_left _ _
  refine ⟨X₀, hX₀_4, fun X hX => ?_⟩
  have hX4 : 4 ≤ X := hX₀_4.trans hX
  have hXpos : 0 < X := by linarith
  have hXm : (m : ℝ) * max X₁ 4 ≤ X := (le_max_left _ _).trans ((le_max_right _ _).trans hX)
  have hXexp : Real.exp (Real.log (m : ℝ) / u) ≤ X :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hX)
  have hlogX_pos : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogm_le : Real.log (m : ℝ) ≤ u * Real.log X := by
    have h1 : Real.log (m : ℝ) / u ≤ Real.log X := by
      rw [← Real.log_exp (Real.log (m : ℝ) / u)]
      exact Real.log_le_log (Real.exp_pos _) hXexp
    linarith [(div_le_iff₀ hu_pos).mp h1]
  let step : ℝ := X / (m : ℝ)
  have hstep_pos : 0 < step := div_pos hXpos hm_Rpos
  -- Step 1: Pointwise step-function domination
  have hpt : ∀ p ∈ primesLE ⌊X⌋₊,
      X - (p : ℝ) ≤ ∑ j ∈ Finset.range m,
        (if (p : ℝ) ≤ ((j + 1 : ℕ) : ℝ) * step then step else 0) := by
    intro p hp
    have hp_leX : (p : ℝ) ≤ X := (Nat.cast_le.mpr (Finset.mem_Iic.mp (Finset.mem_filter.mp hp).1)).trans
      (Nat.floor_le hXpos.le)
    let q : ℕ := ⌊(p : ℝ) / step⌋₊
    have hq_le : q * step ≤ (p : ℝ) := by
      have := Nat.floor_le (div_nonneg (Nat.cast_nonneg p) hstep_pos.le)
      exact (le_div_iff₀ hstep_pos).mp this
    have hlt_succ : ∀ j ∈ Finset.range m, q ≤ j → (p : ℝ) ≤ ((j + 1 : ℕ) : ℝ) * step := by
      intro j _ hqj
      have h1 : (p : ℝ) / step < (q : ℝ) + 1 := Nat.lt_floor_add_one _
      have h2 : (q : ℝ) + 1 ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hqj
      have h3 : (p : ℝ) / step ≤ ((j + 1 : ℕ) : ℝ) := le_trans h1.le h2
      exact (div_le_iff₀ hstep_pos).mp h3
    by_cases hqm : q ≤ m
    · have hsub : Finset.Ico q m ⊆ Finset.range m := fun j hj =>
        Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2
      have hsum_ge : ((m - q : ℕ) : ℝ) * step ≤
          ∑ j ∈ Finset.range m, (if (p : ℝ) ≤ ((j + 1 : ℕ) : ℝ) * step then step else 0) := by
        calc ((m - q : ℕ) : ℝ) * step
            = ∑ _j ∈ Finset.Ico q m, step := by
                rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
          _ = ∑ j ∈ Finset.Ico q m, (if (p : ℝ) ≤ ((j + 1 : ℕ) : ℝ) * step then step else 0) := by
                refine Finset.sum_congr rfl fun j hj => ?_
                rw [if_pos (hlt_succ j (hsub hj) (Finset.mem_Ico.mp hj).1)]
          _ ≤ ∑ j ∈ Finset.range m, (if (p : ℝ) ≤ ((j + 1 : ℕ) : ℝ) * step then step else 0) := by
                refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => ?_
                split_ifs <;> linarith
      have hmstep : (m : ℝ) * step = X := by dsimp only [step]; field_simp [hm_Rpos.ne']
      have hsub_cast : ((m - q : ℕ) : ℝ) = (m : ℝ) - (q : ℝ) := Nat.cast_sub hqm
      rw [hsub_cast, sub_mul, hmstep] at hsum_ge
      linarith
    · have hmq : (m : ℝ) < (q : ℝ) := by exact_mod_cast not_le.mp hqm
      have hmstep : (m : ℝ) * step = X := by dsimp only [step]; field_simp [hm_Rpos.ne']
      have : X < (p : ℝ) := by
        calc X = (m : ℝ) * step := hmstep.symm
          _ < (q : ℝ) * step := mul_lt_mul_of_pos_right hmq hstep_pos
          _ ≤ (p : ℝ) := hq_le
      linarith
  -- Step 2: Swap sums and apply `primeCounting_upper_pnt` at each `x_j = (j+1) * step`
  have hswap : ∑ p ∈ primesLE ⌊X⌋₊, (X - (p : ℝ)) ≤
      step * ∑ j ∈ Finset.range m, ((primesLE ⌊((j + 1 : ℕ) : ℝ) * step⌋₊).card : ℝ) := by
    calc ∑ p ∈ primesLE ⌊X⌋₊, (X - (p : ℝ))
        ≤ ∑ p ∈ primesLE ⌊X⌋₊, ∑ j ∈ Finset.range m,
            (if (p : ℝ) ≤ ((j + 1 : ℕ) : ℝ) * step then step else 0) := Finset.sum_le_sum hpt
      _ = ∑ j ∈ Finset.range m, ∑ p ∈ primesLE ⌊X⌋₊,
            (if (p : ℝ) ≤ ((j + 1 : ℕ) : ℝ) * step then step else 0) := Finset.sum_comm
      _ ≤ ∑ j ∈ Finset.range m, step * ((primesLE ⌊((j + 1 : ℕ) : ℝ) * step⌋₊).card : ℝ) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
          refine mul_le_mul_of_nonneg_left ?_ hstep_pos.le
          exact_mod_cast Finset.card_le_card (fun p hp => by
            rcases Finset.mem_filter.mp hp with ⟨hpP, hple⟩
            exact Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr (Nat.le_floor hple),
              (Finset.mem_filter.mp hpP).2⟩)
      _ = step * ∑ j ∈ Finset.range m, ((primesLE ⌊((j + 1 : ℕ) : ℝ) * step⌋₊).card : ℝ) := by
          rw [Finset.mul_sum]
  -- Step 3: Bound each `π((j+1) * step)`
  have hterm : ∀ j ∈ Finset.range m,
      ((primesLE ⌊((j + 1 : ℕ) : ℝ) * step⌋₊).card : ℝ) ≤
        ((1 + u) / (1 - u)) * (((j + 1 : ℕ) : ℝ) * step / Real.log X) := by
    intro j _
    let xj : ℝ := ((j + 1 : ℕ) : ℝ) * step
    have hj1 : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos j
    have hstep_ge : max X₁ 4 ≤ step := (le_div_iff₀ hm_Rpos).mpr (by linarith)
    have hxj_ge_step : step ≤ xj := by
      calc step = 1 * step := (one_mul _).symm
        _ ≤ ((j + 1 : ℕ) : ℝ) * step := mul_le_mul_of_nonneg_right hj1 hstep_pos.le
    have hxj_X₁ : X₁ ≤ xj := (le_max_left _ _).trans (hstep_ge.trans hxj_ge_step)
    have hxj_4 : 4 ≤ xj := (le_max_right _ _).trans (hstep_ge.trans hxj_ge_step)
    have hlogxj_pos : 0 < Real.log xj := Real.log_pos (by linarith)
    have hlogxj_ge : (1 - u) * Real.log X ≤ Real.log xj := by
      have h1 : Real.log step ≤ Real.log xj := Real.log_le_log hstep_pos hxj_ge_step
      have h2 : Real.log step = Real.log X - Real.log (m : ℝ) :=
        Real.log_div hXpos.ne' hm_Rpos.ne'
      linarith
    have hpnt := hX₁ xj hxj_X₁
    have hden_pos : 0 < (1 - u) * Real.log X := mul_pos (by linarith) hlogX_pos
    calc ((primesLE ⌊xj⌋₊).card : ℝ)
        ≤ (1 + u) * (xj / Real.log xj) := hpnt
      _ ≤ (1 + u) * (xj / ((1 - u) * Real.log X)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          exact div_le_div_of_nonneg_left (by linarith) hden_pos hlogxj_ge
      _ = ((1 + u) / (1 - u)) * (xj / Real.log X) := by
          field_simp [(by linarith : (1 : ℝ) - u ≠ 0), hlogX_pos.ne']
  -- Step 4: Sum `j + 1` over `j ∈ range m` = `m * (m + 1) / 2`
  have hsum_j : ∑ j ∈ Finset.range m, ((j + 1 : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) + 1) / 2 := by
    have hnat : 2 * ∑ j ∈ Finset.range m, (j + 1) = m * (m + 1) := by
      induction m with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, mul_add, ih]
        ring
    have hR : (2 : ℝ) * ∑ j ∈ Finset.range m, ((j + 1 : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) + 1) := by
      exact_mod_cast hnat
    linarith
  have hfinal_coeff : ((1 + u) / (1 - u)) * (1 + 1 / (m : ℝ)) ≤ 1 + δ := by
    have h1 : (1 + u) / (1 - u) ≤ 1 + 3 * u := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - u)]
      nlinarith
    have h2 : 1 + 1 / (m : ℝ) ≤ 1 + u := by linarith
    calc ((1 + u) / (1 - u)) * (1 + 1 / (m : ℝ))
        ≤ (1 + 3 * u) * (1 + u) := mul_le_mul h1 h2 (by positivity) (by linarith)
      _ ≤ 1 + 8 * u := by nlinarith
      _ ≤ 1 + δ := by linarith
  calc ∑ p ∈ primesLE ⌊X⌋₊, (X - (p : ℝ))
      ≤ step * ∑ j ∈ Finset.range m, ((primesLE ⌊((j + 1 : ℕ) : ℝ) * step⌋₊).card : ℝ) := hswap
    _ ≤ step * ∑ j ∈ Finset.range m, (((1 + u) / (1 - u)) * (((j + 1 : ℕ) : ℝ) * step / Real.log X)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) hstep_pos.le
    _ = ((1 + u) / (1 - u)) * (step ^ 2 / Real.log X) * ∑ j ∈ Finset.range m, ((j + 1 : ℕ) : ℝ) := by
        have hpull : ∑ j ∈ Finset.range m, ((1 + u) / (1 - u)) * (((j + 1 : ℕ) : ℝ) * step / Real.log X) =
            ((1 + u) / (1 - u)) * (step / Real.log X) * ∑ j ∈ Finset.range m, ((j + 1 : ℕ) : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring
        rw [hpull]; ring
    _ = ((1 + u) / (1 - u)) * (1 + 1 / (m : ℝ)) * (X ^ 2 / (2 * Real.log X)) := by
        rw [hsum_j]
        dsimp only [step]
        field_simp [hm_Rpos.ne', hlogX_pos.ne']
    _ ≤ (1 + δ) * (X ^ 2 / (2 * Real.log X)) :=
        mul_le_mul_of_nonneg_right hfinal_coeff (div_nonneg (sq_nonneg X) (by linarith))
    _ = (1 + δ) * X ^ 2 / (2 * Real.log X) := by ring

/-- Step weight `c_t = log ((t + 2) / (t + 1))`. -/
noncomputable def tauTerm (t : ℕ) : ℝ :=
  Real.log (((t : ℝ) + 2) / ((t : ℝ) + 1))

lemma tauTerm_pos (t : ℕ) : 0 < tauTerm t := by
  unfold tauTerm
  refine Real.log_pos ?_
  rw [one_lt_div (by positivity)]
  linarith

lemma tauTerm_le_inv (t : ℕ) : tauTerm t ≤ 1 / ((t : ℝ) + 1) := by
  unfold tauTerm
  have h1 := Real.log_le_sub_one_of_pos (div_pos (by positivity : (0 : ℝ) < (t : ℝ) + 2)
    (by positivity : (0 : ℝ) < (t : ℝ) + 1))
  have h2 : ((t : ℝ) + 2) / ((t : ℝ) + 1) - 1 = 1 / ((t : ℝ) + 1) := by
    field_simp [(by positivity : (0 : ℝ) < (t : ℝ) + 1).ne']; ring
  linarith

lemma sum_tauTerm_eq_log (e : ℕ) :
    ∑ t ∈ Finset.range e, tauTerm t = Real.log ((e : ℝ) + 1) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Finset.sum_range_succ, ih]
    unfold tauTerm
    have h1 : (0 : ℝ) < (e : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < (e : ℝ) + 2 := by positivity
    rw [← Real.log_mul h1.ne' (div_pos h2 h1).ne']
    congr 1
    push_cast
    field_simp [h1.ne']
    ring

lemma bbmstTau_summable : Summable (fun t : ℕ => tauTerm t ^ 2) := by
  have hinv : Summable (fun t : ℕ => 1 / ((t : ℝ) + 1) ^ 2) := by
    have h := (Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num)
    have hshift := (summable_nat_add_iff 1).mpr h
    simpa [one_div] using hshift
  refine Summable.of_nonneg_of_le (fun t => sq_nonneg _) (fun t => ?_) hinv
  have h1 := tauTerm_le_inv t
  have h2 := (tauTerm_pos t).le
  have hsq := mul_le_mul h1 h1 h2 (by positivity)
  simpa [sq, one_div] using hsq

lemma bbmstTau_pos : 0 < Erdos1189.bbmstTau := by
  have h0 : 0 < tauTerm 0 ^ 2 := sq_pos_of_pos (tauTerm_pos 0)
  have hle : tauTerm 0 ^ 2 ≤ Erdos1189.bbmstTau :=
    bbmstTau_summable.le_tsum 0 (fun t _ => sq_nonneg _)
  linarith

lemma sum_tauTerm_sq_le_bbmstTau (S : Finset ℕ) :
    ∑ t ∈ S, tauTerm t ^ 2 ≤ Erdos1189.bbmstTau :=
  bbmstTau_summable.sum_le_tsum S (fun _ _ => sq_nonneg _)

/-- Tail bound: for `1 ≤ t₀`, `∑ t ∈ Ico t₀ E, (tauTerm t)^2 ≤ 1 / t₀`. -/
lemma sum_tauTerm_sq_Ico_le {t₀ E : ℕ} (ht₀ : 1 ≤ t₀) :
    ∑ t ∈ Finset.Ico t₀ E, tauTerm t ^ 2 ≤ 1 / (t₀ : ℝ) := by
  have htele : ∀ n : ℕ, ∑ t ∈ Finset.Ico t₀ (t₀ + n), (1 / (t : ℝ) - 1 / ((t : ℝ) + 1)) =
      1 / (t₀ : ℝ) - 1 / ((t₀ + n : ℕ) : ℝ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show t₀ + (n + 1) = (t₀ + n) + 1 by omega,
          Finset.sum_Ico_succ_top (by omega : t₀ ≤ t₀ + n), ih]
      push_cast
      ring
  by_cases hle : t₀ ≤ E
  · calc ∑ t ∈ Finset.Ico t₀ E, tauTerm t ^ 2
        ≤ ∑ t ∈ Finset.Ico t₀ E, (1 / (t : ℝ) - 1 / ((t : ℝ) + 1)) := by
          refine Finset.sum_le_sum fun t ht => ?_
          have ht1 : 1 ≤ t := ht₀.trans (Finset.mem_Ico.mp ht).1
          have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht1
          have ht1pos : (0 : ℝ) < (t : ℝ) + 1 := by linarith
          have h1 := tauTerm_le_inv t
          have hsq : tauTerm t ^ 2 ≤ 1 / ((t : ℝ) + 1) ^ 2 := by
            have := mul_le_mul h1 h1 (tauTerm_pos t).le (by positivity)
            simpa [sq, one_div] using this
          have h2 : 1 / ((t : ℝ) + 1) ^ 2 ≤ 1 / (t : ℝ) - 1 / ((t : ℝ) + 1) := by
            have heq : 1 / (t : ℝ) - 1 / ((t : ℝ) + 1) = 1 / ((t : ℝ) * ((t : ℝ) + 1)) := by
              field_simp [htpos.ne', ht1pos.ne']; ring
            rw [heq]
            refine one_div_le_one_div_of_le (mul_pos htpos ht1pos) ?_
            nlinarith
          exact hsq.trans h2
      _ = 1 / (t₀ : ℝ) - 1 / (E : ℝ) := by
          have := htele (E - t₀)
          rw [Nat.add_sub_of_le hle] at this
          exact this
      _ ≤ 1 / (t₀ : ℝ) := by
          have : (0 : ℝ) ≤ 1 / (E : ℝ) := by positivity
          linarith
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    positivity

/-- **Master Lagrange Divisor Identity**: for any finite set `P : Finset ℕ`, exponent function `e`,
`E ≥ sup_{p ∈ P} e p`, and `lam > 0`:
`log (∏ p ∈ P, (e p + 1)) ≤ lam * (∑ p ∈ P, e p * (p - 1)) + ∑ t ∈ range E, lam * ∑ p ∈ P with p ≤ c_t/lam + 1, (c_t/lam + 1 - p)`. -/
lemma master_lagrange_bound (P : Finset ℕ) (e : ℕ → ℕ) (E : ℕ)
    (hE : ∀ p ∈ P, e p ≤ E) {lam : ℝ} (hlam : 0 < lam) :
    Real.log (∏ p ∈ P, ((e p : ℝ) + 1)) ≤
      lam * (∑ p ∈ P, (e p : ℝ) * ((p : ℝ) - 1)) +
      ∑ t ∈ Finset.range E,
        lam * ∑ p ∈ P.filter (fun p : ℕ => (p : ℝ) ≤ tauTerm t / lam + 1),
          (tauTerm t / lam + 1 - (p : ℝ)) := by
  have hlog_prod : Real.log (∏ p ∈ P, ((e p : ℝ) + 1)) =
      ∑ p ∈ P, ∑ t ∈ Finset.range (e p), tauTerm t := by
    rw [Real.log_prod (fun p _ => by positivity)]
    refine Finset.sum_congr rfl fun p _ => (sum_tauTerm_eq_log (e p)).symm
  have hlin : lam * (∑ p ∈ P, (e p : ℝ) * ((p : ℝ) - 1)) =
      ∑ p ∈ P, ∑ _t ∈ Finset.range (e p), lam * ((p : ℝ) - 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hdiff : Real.log (∏ p ∈ P, ((e p : ℝ) + 1)) - lam * (∑ p ∈ P, (e p : ℝ) * ((p : ℝ) - 1)) =
      ∑ p ∈ P, ∑ t ∈ Finset.range (e p), (tauTerm t - lam * ((p : ℝ) - 1)) := by
    rw [hlog_prod, hlin, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => by rw [← Finset.sum_sub_distrib]
  have hstep1 : ∑ p ∈ P, ∑ t ∈ Finset.range (e p), (tauTerm t - lam * ((p : ℝ) - 1)) ≤
      ∑ t ∈ Finset.range E, ∑ p ∈ P, max 0 (tauTerm t - lam * ((p : ℝ) - 1)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun p hp => ?_
    calc ∑ t ∈ Finset.range (e p), (tauTerm t - lam * ((p : ℝ) - 1))
        ≤ ∑ t ∈ Finset.range (e p), max 0 (tauTerm t - lam * ((p : ℝ) - 1)) :=
          Finset.sum_le_sum fun t _ => le_max_right _ _
      _ ≤ ∑ t ∈ Finset.range E, max 0 (tauTerm t - lam * ((p : ℝ) - 1)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (hE p hp))
            (fun _ _ _ => le_max_left _ _)
  have hstep2 : ∀ t ∈ Finset.range E,
      ∑ p ∈ P, max 0 (tauTerm t - lam * ((p : ℝ) - 1)) =
        lam * ∑ p ∈ P.filter (fun p : ℕ => (p : ℝ) ≤ tauTerm t / lam + 1),
          (tauTerm t / lam + 1 - (p : ℝ)) := by
    intro t _
    rw [Finset.mul_sum]
    rw [← Finset.sum_filter_add_sum_filter_not P (fun p : ℕ => (p : ℝ) ≤ tauTerm t / lam + 1)]
    have hzero : ∑ p ∈ P.filter (fun p : ℕ => ¬ ((p : ℝ) ≤ tauTerm t / lam + 1)),
        max 0 (tauTerm t - lam * ((p : ℝ) - 1)) = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      have hgt : tauTerm t / lam + 1 < (p : ℝ) := not_le.mp (Finset.mem_filter.mp hp).2
      have hneg : tauTerm t - lam * ((p : ℝ) - 1) ≤ 0 := by
        have h1 : tauTerm t < lam * ((p : ℝ) - 1) := by
          have := mul_lt_mul_of_pos_left (by linarith : tauTerm t / lam < (p : ℝ) - 1) hlam
          rwa [mul_div_cancel₀ _ hlam.ne'] at this
        linarith
      exact max_eq_left hneg
    rw [hzero, add_zero]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hle : (p : ℝ) ≤ tauTerm t / lam + 1 := (Finset.mem_filter.mp hp).2
    have hnonneg : 0 ≤ tauTerm t - lam * ((p : ℝ) - 1) := by
      have h1 : lam * ((p : ℝ) - 1) ≤ tauTerm t := by
        have := mul_le_mul_of_nonneg_left (by linarith : (p : ℝ) - 1 ≤ tauTerm t / lam) hlam.le
        rwa [mul_div_cancel₀ _ hlam.ne'] at this
      linarith
    rw [max_eq_right hnonneg]
    field_simp [hlam.ne']
    ring
  have hcomb : Real.log (∏ p ∈ P, ((e p : ℝ) + 1)) - lam * (∑ p ∈ P, (e p : ℝ) * ((p : ℝ) - 1)) ≤
      ∑ t ∈ Finset.range E,
        lam * ∑ p ∈ P.filter (fun p : ℕ => (p : ℝ) ≤ tauTerm t / lam + 1),
          (tauTerm t / lam + 1 - (p : ℝ)) := by
    rw [hdiff]
    calc ∑ p ∈ P, ∑ t ∈ Finset.range (e p), (tauTerm t - lam * ((p : ℝ) - 1))
        ≤ ∑ t ∈ Finset.range E, ∑ p ∈ P, max 0 (tauTerm t - lam * ((p : ℝ) - 1)) := hstep1
      _ = ∑ t ∈ Finset.range E, lam * ∑ p ∈ P.filter (fun p : ℕ => (p : ℝ) ≤ tauTerm t / lam + 1),
            (tauTerm t / lam + 1 - (p : ℝ)) := Finset.sum_congr rfl hstep2
  linarith

/-- **Big-Prime Divisor Bound**: If `M_cut ≥ X₀` (where `X₀ ≥ 4` witnesses `sum_primes_sub_le δ`),
then for any `N > 0`, `W ⊆ bigCoords N M_cut` with weight `≤ x`:
`(dBig N M_cut W : ℝ) ≤ exp (√(2 * (1 + δ) * (M_cut / (M_cut - 1))^2 * bbmstTau * (x + 1) / log M_cut))`. -/
lemma dBig_le_exp {δ X₀ : ℝ} (hδ : 0 < δ) (hX₀4 : 4 ≤ X₀)
    (hsum_p : ∀ X : ℝ, X₀ ≤ X →
      ∑ p ∈ primesLE ⌊X⌋₊, (X - (p : ℝ)) ≤ (1 + δ) * X ^ 2 / (2 * Real.log X))
    {N M_cut x : ℕ} (hM_ge : X₀ ≤ (M_cut : ℝ))
    (W : Finset (CoordIdx N))
    (hwt : ∑ p ∈ N.primeFactors.filter (M_cut ≤ ·), coordMult N W p * (p - 1) ≤ x) :
    (dBig N M_cut W : ℝ) ≤
      Real.exp (Real.sqrt (2 * (1 + δ) * ((M_cut : ℝ) / ((M_cut : ℝ) - 1)) ^ 2 *
        Erdos1189.bbmstTau * ((x : ℝ) + 1) / Real.log (M_cut : ℝ))) := by
  let P : Finset ℕ := N.primeFactors.filter (M_cut ≤ ·)
  let e : ℕ → ℕ := coordMult N W
  have hM4 : (4 : ℝ) ≤ (M_cut : ℝ) := hX₀4.trans hM_ge
  have hM1_pos : (0 : ℝ) < (M_cut : ℝ) - 1 := by linarith
  have hlogM_pos : 0 < Real.log (M_cut : ℝ) := Real.log_pos (by linarith)
  let A : ℝ := (1 + δ) * ((M_cut : ℝ) / ((M_cut : ℝ) - 1)) ^ 2 * Erdos1189.bbmstTau
  have hA_pos : 0 < A := by
    refine mul_pos (mul_pos (by linarith) (sq_pos_of_pos (div_pos (by linarith) hM1_pos))) bbmstTau_pos
  let y : ℝ := (x : ℝ) + 1
  have hy_pos : 0 < y := by positivity
  let lam : ℝ := Real.sqrt (A / (2 * y * Real.log (M_cut : ℝ)))
  have hlam_pos : 0 < lam := Real.sqrt_pos.mpr (div_pos hA_pos (by positivity))
  have hdBig_pos : (0 : ℝ) < (dBig N M_cut W : ℝ) := by
    unfold dBig
    push_cast
    exact Finset.prod_pos fun p _ => by positivity
  rw [← Real.log_le_iff_le_exp hdBig_pos]
  have hdBig_eq : (dBig N M_cut W : ℝ) = ∏ p ∈ P, ((e p : ℝ) + 1) := by
    unfold dBig; push_cast; rfl
  rw [hdBig_eq]
  let E : ℕ := P.sup e
  have hE : ∀ p ∈ P, e p ≤ E := fun p hp => Finset.le_sup hp
  have hml := master_lagrange_bound P e E hE hlam_pos
  -- Bound the linear term `lam * ∑ p ∈ P, e p * (p - 1) ≤ lam * y`
  have hwt_R : ∑ p ∈ P, (e p : ℝ) * ((p : ℝ) - 1) ≤ y := by
    have h1 : ∑ p ∈ P, (e p : ℝ) * ((p : ℝ) - 1) =
        ((∑ p ∈ P, e p * (p - 1) : ℕ) : ℝ) := by
      push_cast
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).one_le
      rw [Nat.cast_sub hp1, Nat.cast_one]
    rw [h1]
    have h2 : ((∑ p ∈ P, e p * (p - 1) : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hwt
    linarith
  -- Bound each `t`-slice using `hsum_p`!
  have hslice : ∀ t ∈ Finset.range E,
      lam * ∑ p ∈ P.filter (fun p : ℕ => (p : ℝ) ≤ tauTerm t / lam + 1),
        (tauTerm t / lam + 1 - (p : ℝ)) ≤
        ((1 + δ) * ((M_cut : ℝ) / ((M_cut : ℝ) - 1)) ^ 2 / (2 * lam * Real.log (M_cut : ℝ))) *
          tauTerm t ^ 2 := by
    intro t _
    let Xt : ℝ := tauTerm t / lam + 1
    let Pt : Finset ℕ := P.filter fun p : ℕ => (p : ℝ) ≤ Xt
    change lam * ∑ p ∈ Pt, (Xt - (p : ℝ)) ≤ _
    by_cases hne : Pt.Nonempty
    · obtain ⟨p0, hp0⟩ := hne
      rcases Finset.mem_filter.mp hp0 with ⟨hp0P, hp0le⟩
      have hp0M : (M_cut : ℝ) ≤ (p0 : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp0P).2
      have hXt_geM : (M_cut : ℝ) ≤ Xt := hp0M.trans hp0le
      have hXt_geX₀ : X₀ ≤ Xt := hM_ge.trans hXt_geM
      have hXt_pos : 0 < Xt := by linarith
      have hsub : Pt ⊆ primesLE ⌊Xt⌋₊ := by
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpP, hple⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr (Nat.le_floor hple),
          Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hpP).1⟩
      have hsum_le : ∑ p ∈ Pt, (Xt - (p : ℝ)) ≤ (1 + δ) * Xt ^ 2 / (2 * Real.log Xt) := by
        calc ∑ p ∈ Pt, (Xt - (p : ℝ))
            ≤ ∑ p ∈ primesLE ⌊Xt⌋₊, (Xt - (p : ℝ)) := by
              refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => ?_
              have hpX : (p : ℝ) ≤ Xt :=
                (Nat.cast_le.mpr (Finset.mem_Iic.mp (Finset.mem_filter.mp hp).1)).trans
                  (Nat.floor_le hXt_pos.le)
              linarith
          _ ≤ (1 + δ) * Xt ^ 2 / (2 * Real.log Xt) := hsum_p Xt hXt_geX₀
      have hXt_le_ct : Xt ≤ ((M_cut : ℝ) / ((M_cut : ℝ) - 1)) * (tauTerm t / lam) := by
        have h1 : (M_cut : ℝ) * (Xt - 1) ≥ ((M_cut : ℝ) - 1) * Xt := by nlinarith
        have h2 : Xt - 1 = tauTerm t / lam := by dsimp only [Xt]; ring
        rw [h2] at h1
        rw [div_mul_eq_mul_div, le_div_iff₀ hM1_pos]
        linarith
      have hXt_sq : Xt ^ 2 ≤ ((M_cut : ℝ) / ((M_cut : ℝ) - 1)) ^ 2 * (tauTerm t / lam) ^ 2 := by
        calc Xt ^ 2 ≤ (((M_cut : ℝ) / ((M_cut : ℝ) - 1)) * (tauTerm t / lam)) ^ 2 :=
              pow_le_pow_left₀ hXt_pos.le hXt_le_ct 2
          _ = ((M_cut : ℝ) / ((M_cut : ℝ) - 1)) ^ 2 * (tauTerm t / lam) ^ 2 := mul_pow _ _ 2
      have hlogXt_ge : Real.log (M_cut : ℝ) ≤ Real.log Xt :=
        Real.log_le_log (by linarith) hXt_geM
      calc lam * ∑ p ∈ Pt, (Xt - (p : ℝ))
          ≤ lam * ((1 + δ) * Xt ^ 2 / (2 * Real.log Xt)) :=
            mul_le_mul_of_nonneg_left hsum_le hlam_pos.le
        _ ≤ lam * ((1 + δ) * Xt ^ 2 / (2 * Real.log (M_cut : ℝ))) := by
            refine mul_le_mul_of_nonneg_left ?_ hlam_pos.le
            exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
        _ ≤ lam * ((1 + δ) * (((M_cut : ℝ) / ((M_cut : ℝ) - 1)) ^ 2 * (tauTerm t / lam) ^ 2) /
              (2 * Real.log (M_cut : ℝ))) := by
            refine mul_le_mul_of_nonneg_left ?_ hlam_pos.le
            refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hXt_sq (by linarith)) (by positivity)
        _ = ((1 + δ) * ((M_cut : ℝ) / ((M_cut : ℝ) - 1)) ^ 2 / (2 * lam * Real.log (M_cut : ℝ))) *
              tauTerm t ^ 2 := by
            field_simp [hlam_pos.ne', hlogM_pos.ne']
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty, mul_zero]
      positivity
  have hsum_slices : ∑ t ∈ Finset.range E,
      lam * ∑ p ∈ P.filter (fun p : ℕ => (p : ℝ) ≤ tauTerm t / lam + 1),
        (tauTerm t / lam + 1 - (p : ℝ)) ≤ A / (2 * lam * Real.log (M_cut : ℝ)) := by
    calc ∑ t ∈ Finset.range E,
          lam * ∑ p ∈ P.filter (fun p : ℕ => (p : ℝ) ≤ tauTerm t / lam + 1),
            (tauTerm t / lam + 1 - (p : ℝ))
        ≤ ∑ t ∈ Finset.range E,
            ((1 + δ) * ((M_cut : ℝ) / ((M_cut : ℝ) - 1)) ^ 2 / (2 * lam * Real.log (M_cut : ℝ))) *
              tauTerm t ^ 2 := Finset.sum_le_sum hslice
      _ = ((1 + δ) * ((M_cut : ℝ) / ((M_cut : ℝ) - 1)) ^ 2 / (2 * lam * Real.log (M_cut : ℝ))) *
            ∑ t ∈ Finset.range E, tauTerm t ^ 2 := by rw [← Finset.mul_sum]
      _ ≤ ((1 + δ) * ((M_cut : ℝ) / ((M_cut : ℝ) - 1)) ^ 2 / (2 * lam * Real.log (M_cut : ℝ))) *
            Erdos1189.bbmstTau :=
          mul_le_mul_of_nonneg_left (sum_tauTerm_sq_le_bbmstTau _) (by positivity)
      _ = A / (2 * lam * Real.log (M_cut : ℝ)) := by dsimp only [A]; ring
  have hopt : lam * y + A / (2 * lam * Real.log (M_cut : ℝ)) =
      Real.sqrt (2 * A * y / Real.log (M_cut : ℝ)) := by
    have hlam_sq : lam ^ 2 = A / (2 * y * Real.log (M_cut : ℝ)) :=
      Real.sq_sqrt (div_nonneg hA_pos.le (by positivity))
    have hterm2 : A / (2 * lam * Real.log (M_cut : ℝ)) = lam * y := by
      have hA_eq : A = lam ^ 2 * (2 * y * Real.log (M_cut : ℝ)) := by
        rw [hlam_sq]; field_simp [hy_pos.ne', hlogM_pos.ne']
      rw [hA_eq]; field_simp [hlam_pos.ne', hlogM_pos.ne']
    rw [hterm2, ← two_mul, ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 * (lam * y))]
    congr 1
    calc (2 * (lam * y)) ^ 2 = 4 * lam ^ 2 * y ^ 2 := by ring
      _ = 4 * (A / (2 * y * Real.log (M_cut : ℝ))) * y ^ 2 := by rw [hlam_sq]
      _ = 2 * A * y / Real.log (M_cut : ℝ) := by field_simp [hy_pos.ne', hlogM_pos.ne']; ring
  have hA_expand : 2 * A * y / Real.log (M_cut : ℝ) =
      2 * (1 + δ) * ((M_cut : ℝ) / ((M_cut : ℝ) - 1)) ^ 2 *
        Erdos1189.bbmstTau * ((x : ℝ) + 1) / Real.log (M_cut : ℝ) := by
    dsimp only [A, y]; ring
  calc Real.log (∏ p ∈ P, ((e p : ℝ) + 1))
      ≤ lam * (∑ p ∈ P, (e p : ℝ) * ((p : ℝ) - 1)) +
        ∑ t ∈ Finset.range E,
          lam * ∑ p ∈ P.filter (fun p : ℕ => (p : ℝ) ≤ tauTerm t / lam + 1),
            (tauTerm t / lam + 1 - (p : ℝ)) := hml
    _ ≤ lam * y + A / (2 * lam * Real.log (M_cut : ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hwt_R hlam_pos.le) hsum_slices
    _ = Real.sqrt (2 * A * y / Real.log (M_cut : ℝ)) := hopt
    _ = Real.sqrt (2 * (1 + δ) * ((M_cut : ℝ) / ((M_cut : ℝ) - 1)) ^ 2 *
          Erdos1189.bbmstTau * ((x : ℝ) + 1) / Real.log (M_cut : ℝ)) := by rw [hA_expand]

/-- Helper for `dSmall_le_exp`: large-`k` asymptotic setup. -/
lemma dSmall_hev1 {η X₁ X₀ : ℝ} (hη0 : 0 < η) :
    ∀ᶠ k : ℕ in atTop,
      Real.exp 4 ≤ (k : ℝ) ∧
      max X₁ 4 ≤ (⌊η ^ 3 * Real.sqrt ((k : ℝ) * Real.log (k : ℝ))⌋₊ : ℝ) ∧
      Real.log (k : ℝ) / 4 ≤ Real.log (⌊η ^ 3 * Real.sqrt ((k : ℝ) * Real.log (k : ℝ))⌋₊ : ℝ) ∧
      X₀ ≤ Real.sqrt (Real.sqrt (Real.sqrt (k : ℝ))) ∧
      Real.sqrt (Real.sqrt (k : ℝ)) ≤ η * Real.sqrt ((k : ℝ) / Real.log (k : ℝ)) := by
  have hsqrt_inf : Tendsto (fun k : ℕ => Real.sqrt ((k : ℝ) * Real.log (k : ℝ))) atTop atTop :=
    Tendsto.comp Real.tendsto_sqrt_atTop
      (Tendsto.atTop_mul_atTop₀ tendsto_natCast_atTop_atTop
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  have hM_inf : Tendsto (fun k : ℕ => (⌊η ^ 3 * Real.sqrt ((k : ℝ) * Real.log (k : ℝ))⌋₊ : ℝ))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (tendsto_nat_floor_atTop.comp (Tendsto.const_mul_atTop (pow_pos hη0 3) hsqrt_inf))
  have h1 : ∀ᶠ k : ℕ in atTop, Real.exp 4 ≤ (k : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  have h2 : ∀ᶠ k : ℕ in atTop,
      max X₁ 4 ≤ (⌊η ^ 3 * Real.sqrt ((k : ℝ) * Real.log (k : ℝ))⌋₊ : ℝ) :=
    hM_inf.eventually (eventually_ge_atTop _)
  have h3 : ∀ᶠ k : ℕ in atTop,
      Real.log (k : ℝ) / 4 ≤ Real.log (⌊η ^ 3 * Real.sqrt ((k : ℝ) * Real.log (k : ℝ))⌋₊ : ℝ) := by
    have hlim : Tendsto (fun k : ℕ => Real.sqrt (Real.sqrt (k : ℝ)) / Real.sqrt (k : ℝ)) atTop (nhds 0) := by
      have h := tendsto_inv_atTop_zero.comp
        (Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with k hk
      dsimp only [Function.comp_apply]
      have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
      have hpos2 : 0 < Real.sqrt (Real.sqrt (k : ℝ)) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hkpos)
      have hpos1 : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hkpos
      field_simp [hpos2.ne', hpos1.ne']
      exact (Real.sq_sqrt (Real.sqrt_nonneg _)).symm
    have hcmp : ∀ᶠ k : ℕ in atTop,
        Real.sqrt (Real.sqrt (k : ℝ)) + 1 ≤ η ^ 3 * Real.sqrt ((k : ℝ) * Real.log (k : ℝ)) := by
      have hsqk_inf : Tendsto (fun k : ℕ => Real.sqrt (k : ℝ)) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
      filter_upwards [hlim.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < η ^ 3 / 2)),
          hsqk_inf.eventually (eventually_ge_atTop (2 / η ^ 3)),
          tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (Real.exp 1))] with k hlt hbig hexp
      have hkpos : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le (Real.exp_pos 1) hexp
      have hlog1 : 1 ≤ Real.log (k : ℝ) := by
        rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hexp
      have hsq_pos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hkpos
      have ha : Real.sqrt (Real.sqrt (k : ℝ)) < (η ^ 3 / 2) * Real.sqrt (k : ℝ) :=
        (div_lt_iff₀ hsq_pos).mp hlt
      have hb : 1 ≤ (η ^ 3 / 2) * Real.sqrt (k : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_left hbig (by positivity : (0 : ℝ) ≤ η ^ 3 / 2)
        have hsimp : (η ^ 3 / 2) * (2 / η ^ 3) = 1 := by field_simp [(pow_pos hη0 3).ne']
        linarith
      have hprod : Real.sqrt (k : ℝ) ≤ Real.sqrt ((k : ℝ) * Real.log (k : ℝ)) :=
        Real.sqrt_le_sqrt (by nlinarith)
      nlinarith [pow_pos hη0 3]
    filter_upwards [hcmp, h1] with k hkcmp hk1
    have hkpos : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le (Real.exp_pos 4) hk1
    have hss_pos : 0 < Real.sqrt (Real.sqrt (k : ℝ)) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hkpos)
    have hfloor_ge : Real.sqrt (Real.sqrt (k : ℝ)) ≤
        (⌊η ^ 3 * Real.sqrt ((k : ℝ) * Real.log (k : ℝ))⌋₊ : ℝ) := by
      have hlt := Nat.lt_floor_add_one (η ^ 3 * Real.sqrt ((k : ℝ) * Real.log (k : ℝ)))
      linarith
    have hlog_ss : Real.log (Real.sqrt (Real.sqrt (k : ℝ))) = Real.log (k : ℝ) / 4 := by
      rw [Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt hkpos.le]; ring
    rw [← hlog_ss]
    exact Real.log_le_log hss_pos hfloor_ge
  have h4 : ∀ᶠ k : ℕ in atTop, X₀ ≤ Real.sqrt (Real.sqrt (Real.sqrt (k : ℝ))) :=
    (Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))).eventually (eventually_ge_atTop X₀)
  have h5 : ∀ᶠ k : ℕ in atTop,
      Real.sqrt (Real.sqrt (k : ℝ)) ≤ η * Real.sqrt ((k : ℝ) / Real.log (k : ℝ)) := by
    have hlim : Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (nhds 0) := by
      have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
      refine h.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x _
      rw [Real.sqrt_eq_rpow]
    filter_upwards [(hlim.comp tendsto_natCast_atTop_atTop).eventually
        (Iio_mem_nhds (sq_pos_of_pos hη0)), h1] with k hk hk1
    dsimp only [Function.comp_apply] at hk
    have hkpos : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le (Real.exp_pos 4) hk1
    have hlog_pos : 0 < Real.log (k : ℝ) := Real.log_pos (by
      have : (1 : ℝ) < Real.exp 4 := Real.one_lt_exp_iff.mpr (by norm_num)
      linarith)
    have hsq_pos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hkpos
    have hlog_lt : Real.log (k : ℝ) ≤ η ^ 2 * Real.sqrt (k : ℝ) :=
      ((div_lt_iff₀ hsq_pos).mp hk).le
    have hsq_le : Real.sqrt (k : ℝ) ≤ η ^ 2 * ((k : ℝ) / Real.log (k : ℝ)) := by
      rw [← mul_div_assoc, le_div_iff₀ hlog_pos]
      have hksq : Real.sqrt (k : ℝ) * Real.sqrt (k : ℝ) = (k : ℝ) := Real.mul_self_sqrt hkpos.le
      have := mul_le_mul_of_nonneg_left hlog_lt hsq_pos.le
      nlinarith
    calc Real.sqrt (Real.sqrt (k : ℝ))
        ≤ Real.sqrt (η ^ 2 * ((k : ℝ) / Real.log (k : ℝ))) := Real.sqrt_le_sqrt hsq_le
      _ = η * Real.sqrt ((k : ℝ) / Real.log (k : ℝ)) := by
          rw [Real.sqrt_mul (sq_nonneg η), Real.sqrt_sq hη0.le]
  filter_upwards [h1, h2, h3, h4, h5] with k h1k h2k h3k h4k h5k
  exact ⟨h1k, h2k, h3k, h4k, h5k⟩

/-- **Small-Prime Divisor Bound**: For fixed `η ∈ (0, 1/10]` and sufficiently large `k`
with `M_cut = ⌊η^3 * √(k * log k)⌋₊`, every Simpson-valid `N > 0` satisfies
`(dSmall N M_cut : ℝ) ≤ exp (50 * η * √(k / log k))`. -/
lemma dSmall_le_exp {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 10) :
    ∀ᶠ k : ℕ in atTop,
      let M_cut := ⌊η ^ 3 * Real.sqrt ((k : ℝ) * Real.log (k : ℝ))⌋₊
      ∀ N : ℕ, 0 < N → 1 + ∑ p ∈ N.primeFactors, N.factorization p * (p - 1) ≤ k →
        (dSmall N M_cut : ℝ) ≤ Real.exp (50 * η * Real.sqrt ((k : ℝ) / Real.log (k : ℝ))) := by
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.mp (primeCounting_upper_pnt (δ := 1) one_pos)
  obtain ⟨X₀, hX₀4, hsum_p⟩ := sum_primes_sub_le (δ := 1) one_pos
  let t₀ : ℕ := max 1 ⌈1 / η ^ 2⌉₊
  have ht₀_ge1 : 1 ≤ t₀ := le_max_left _ _
  have ht₀_Rpos : (0 : ℝ) < (t₀ : ℝ) := by exact_mod_cast ht₀_ge1
  have h1t₀_le : 1 / (t₀ : ℝ) ≤ η ^ 2 := by
    have h1 : 1 / η ^ 2 ≤ (t₀ : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 _)
    rw [div_le_iff₀ ht₀_Rpos]
    have := (div_le_iff₀ (sq_pos_of_pos hη0)).mp h1
    linarith
  have ht₀_le : (t₀ : ℝ) ≤ 2 / η ^ 2 := by
    have h1 : (⌈1 / η ^ 2⌉₊ : ℝ) < 1 / η ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : (1 : ℝ) ≤ 1 / η ^ 2 := by
      rw [one_le_div (sq_pos_of_pos hη0)]; nlinarith
    have h3 : (t₀ : ℝ) ≤ max 1 (1 / η ^ 2 + 1) := by
      dsimp only [t₀]
      push_cast
      exact max_le (le_max_left _ _) (le_trans h1.le (le_max_right _ _))
    have h4 : max (1 : ℝ) (1 / η ^ 2 + 1) = 1 / η ^ 2 + 1 := max_eq_right (by linarith)
    have h5 : 1 / η ^ 2 + 1 ≤ 2 / η ^ 2 := by
      rw [show (2 : ℝ) / η ^ 2 = 1 / η ^ 2 + 1 / η ^ 2 by ring]; linarith
    linarith
  filter_upwards [dSmall_hev1 (X₁ := X₁) (X₀ := X₀) hη0] with k ⟨hk_exp, hM_ge, hlogM_ge, hX₀_le, hq_le⟩
  intro M_cut N hN hsimp
  have hkpos : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le (Real.exp_pos 4) hk_exp
  have hlogk_ge4 : 4 ≤ Real.log (k : ℝ) := by
    rw [← Real.log_exp 4]; exact Real.log_le_log (Real.exp_pos 4) hk_exp
  have hlogk_pos : 0 < Real.log (k : ℝ) := by linarith
  have hM_le_R : (M_cut : ℝ) ≤ η ^ 3 * Real.sqrt ((k : ℝ) * Real.log (k : ℝ)) :=
    Nat.floor_le (by positivity)
  have hM_ge4 : (4 : ℝ) ≤ (M_cut : ℝ) := (le_max_right _ _).trans hM_ge
  have hM_geX₁ : X₁ ≤ (M_cut : ℝ) := (le_max_left _ _).trans hM_ge
  let P : Finset ℕ := N.primeFactors.filter (· < M_cut)
  let e : ℕ → ℕ := fun p => N.factorization p
  let lam : ℝ := η / Real.sqrt ((k : ℝ) * Real.log (k : ℝ))
  have hlam_pos : 0 < lam := div_pos hη0 (Real.sqrt_pos.mpr (mul_pos hkpos hlogk_pos))
  have hdSmall_pos : (0 : ℝ) < (dSmall N M_cut : ℝ) := by
    unfold dSmall; push_cast; exact Finset.prod_pos fun _ _ => by positivity
  rw [← Real.log_le_iff_le_exp hdSmall_pos]
  have hdSmall_eq : (dSmall N M_cut : ℝ) = ∏ p ∈ P, ((e p : ℝ) + 1) := by
    unfold dSmall; push_cast; rfl
  rw [hdSmall_eq]
  let E : ℕ := max t₀ (P.sup e)
  have hE : ∀ p ∈ P, e p ≤ E := fun p hp => (Finset.le_sup hp).trans (le_max_right _ _)
  have hml := master_lagrange_bound P e E hE hlam_pos
  -- Linear term: `lam * ∑ p ∈ P, e p * (p - 1) ≤ lam * k = η * √(k / log k)`
  have hwt_k : ∑ p ∈ P, (e p : ℝ) * ((p : ℝ) - 1) ≤ (k : ℝ) := by
    have h1 : ∑ p ∈ P, (e p : ℝ) * ((p : ℝ) - 1) =
        ((∑ p ∈ P, e p * (p - 1) : ℕ) : ℝ) := by
      push_cast
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).one_le
      rw [Nat.cast_sub hp1, Nat.cast_one]
    rw [h1]
    have h2 : ∑ p ∈ P, e p * (p - 1) ≤ k := by
      calc ∑ p ∈ P, e p * (p - 1)
          ≤ ∑ p ∈ N.primeFactors, N.factorization p * (p - 1) :=
            Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        _ ≤ k := by omega
    exact_mod_cast h2
  have hlin_bound : lam * (∑ p ∈ P, (e p : ℝ) * ((p : ℝ) - 1)) ≤
      η * Real.sqrt ((k : ℝ) / Real.log (k : ℝ)) := by
    calc lam * (∑ p ∈ P, (e p : ℝ) * ((p : ℝ) - 1))
        ≤ lam * (k : ℝ) := mul_le_mul_of_nonneg_left hwt_k hlam_pos.le
      _ = η * ((k : ℝ) / Real.sqrt ((k : ℝ) * Real.log (k : ℝ))) := by dsimp only [lam]; ring
      _ = η * Real.sqrt ((k : ℝ) / Real.log (k : ℝ)) := by
          rw [div_sqrt_mul_eq_sqrt_div hkpos hlogk_pos]
  have hsplit_E : Finset.range E = Finset.range t₀ ∪ Finset.Ico t₀ E := by
    ext t; simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    have : t₀ ≤ E := le_max_left _ _; omega
  have hdisj_E : Disjoint (Finset.range t₀) (Finset.Ico t₀ E) := by
    rw [Finset.disjoint_left]
    intro t h1 h2; rw [Finset.mem_range] at h1; rw [Finset.mem_Ico] at h2; omega
  let sliceTerm (t : ℕ) : ℝ :=
    lam * ∑ p ∈ P.filter (fun p : ℕ => (p : ℝ) ≤ tauTerm t / lam + 1),
      (tauTerm t / lam + 1 - (p : ℝ))
  -- Part 1: `t < t₀`!
  have hpart1 : ∑ t ∈ Finset.range t₀, sliceTerm t ≤
      16 * η * Real.sqrt ((k : ℝ) / Real.log (k : ℝ)) := by
    have hcardP : (P.card : ℝ) ≤ 8 * η ^ 3 * Real.sqrt ((k : ℝ) / Real.log (k : ℝ)) := by
      have hsubP : P ⊆ primesLE ⌊(M_cut : ℝ)⌋₊ := by
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpN, hplt⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr ?_, Nat.prime_of_mem_primeFactors hpN⟩
        rw [Nat.floor_natCast]; omega
      have hpi := hX₁ (M_cut : ℝ) hM_geX₁
      have hlogM_ge' : Real.log (k : ℝ) / 4 ≤ Real.log (M_cut : ℝ) := hlogM_ge
      calc (P.card : ℝ)
          ≤ ((primesLE ⌊(M_cut : ℝ)⌋₊).card : ℝ) := by exact_mod_cast Finset.card_le_card hsubP
        _ ≤ (1 + 1) * ((M_cut : ℝ) / Real.log (M_cut : ℝ)) := hpi
        _ ≤ (1 + 1) * ((M_cut : ℝ) / (Real.log (k : ℝ) / 4)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact div_le_div_of_nonneg_left (Nat.cast_nonneg M_cut)
              (by linarith : (0 : ℝ) < Real.log (k : ℝ) / 4) hlogM_ge'
        _ = 8 * ((M_cut : ℝ) / Real.log (k : ℝ)) := by ring
        _ ≤ 8 * ((η ^ 3 * Real.sqrt ((k : ℝ) * Real.log (k : ℝ))) / Real.log (k : ℝ)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact div_le_div_of_nonneg_right hM_le_R hlogk_pos.le
        _ = 8 * η ^ 3 * (Real.sqrt ((k : ℝ) * Real.log (k : ℝ)) / Real.log (k : ℝ)) := by ring
        _ = 8 * η ^ 3 * Real.sqrt ((k : ℝ) / Real.log (k : ℝ)) := by
            rw [sqrt_mul_div_eq_sqrt_div hkpos hlogk_pos]
    have hper : ∀ t ∈ Finset.range t₀, sliceTerm t ≤ (P.card : ℝ) * tauTerm t := by
      intro t _
      dsimp only [sliceTerm]
      calc lam * ∑ p ∈ P.filter (fun p : ℕ => (p : ℝ) ≤ tauTerm t / lam + 1),
            (tauTerm t / lam + 1 - (p : ℝ))
          ≤ lam * ∑ _p ∈ P.filter (fun p : ℕ => (p : ℝ) ≤ tauTerm t / lam + 1), (tauTerm t / lam) := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p hp => ?_) hlam_pos.le
            have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
              exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).one_le
            linarith
        _ = ((P.filter (fun p : ℕ => (p : ℝ) ≤ tauTerm t / lam + 1)).card : ℝ) * tauTerm t := by
            rw [Finset.sum_const, nsmul_eq_mul]
            field_simp [hlam_pos.ne']
        _ ≤ (P.card : ℝ) * tauTerm t :=
            mul_le_mul_of_nonneg_right
              (by exact_mod_cast Finset.card_le_card (Finset.filter_subset _ P)) (tauTerm_pos t).le
    have hlog_t0 : Real.log ((t₀ : ℝ) + 1) ≤ (t₀ : ℝ) := by
      have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (t₀ : ℝ) + 1)
      linarith
    calc ∑ t ∈ Finset.range t₀, sliceTerm t
        ≤ ∑ t ∈ Finset.range t₀, (P.card : ℝ) * tauTerm t := Finset.sum_le_sum hper
      _ = (P.card : ℝ) * ∑ t ∈ Finset.range t₀, tauTerm t := by rw [← Finset.mul_sum]
      _ = (P.card : ℝ) * Real.log ((t₀ : ℝ) + 1) := by rw [sum_tauTerm_eq_log]
      _ ≤ (8 * η ^ 3 * Real.sqrt ((k : ℝ) / Real.log (k : ℝ))) * (2 / η ^ 2) :=
          mul_le_mul hcardP (hlog_t0.trans ht₀_le) (Real.log_nonneg (by linarith)) (by positivity)
      _ = 16 * η * Real.sqrt ((k : ℝ) / Real.log (k : ℝ)) := by
          field_simp [hη0.ne']; ring
  -- Part 2: `t ∈ Ico t₀ E`, split at `K8 = k^(1/8)`!
  let K8 : ℝ := Real.sqrt (Real.sqrt (Real.sqrt (k : ℝ)))
  have hK8_pos : 0 < K8 := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hkpos))
  have hK8_sq : K8 ^ 2 = Real.sqrt (Real.sqrt (k : ℝ)) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hlogK8 : Real.log K8 = Real.log (k : ℝ) / 8 := by
    dsimp only [K8]
    rw [Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt hkpos.le]
    ring
  let S_A : Finset ℕ := (Finset.Ico t₀ E).filter fun t : ℕ => K8 ≤ tauTerm t / lam + 1
  let S_B : Finset ℕ := (Finset.Ico t₀ E).filter fun t : ℕ => ¬ (K8 ≤ tauTerm t / lam + 1)
  have hsplit_AB : ∑ t ∈ Finset.Ico t₀ E, sliceTerm t =
      (∑ t ∈ S_A, sliceTerm t) + (∑ t ∈ S_B, sliceTerm t) :=
    (Finset.sum_filter_add_sum_filter_not (Finset.Ico t₀ E) _ sliceTerm).symm
  -- Subcase A: `K8 ≤ X_t`
  have hpartA : ∑ t ∈ S_A, sliceTerm t ≤ 32 * η * Real.sqrt ((k : ℝ) / Real.log (k : ℝ)) := by
    have hperA : ∀ t ∈ S_A, sliceTerm t ≤ (32 / (lam * Real.log (k : ℝ))) * tauTerm t ^ 2 := by
      intro t ht
      have hXt_ge : K8 ≤ tauTerm t / lam + 1 := (Finset.mem_filter.mp ht).2
      let Xt : ℝ := tauTerm t / lam + 1
      have hXt_X₀ : X₀ ≤ Xt := hX₀_le.trans hXt_ge
      have hXt_4 : 4 ≤ Xt := hX₀4.trans hXt_X₀
      have hXt_le2 : Xt ≤ 2 * (tauTerm t / lam) := by
        have : 1 ≤ tauTerm t / lam := by linarith
        linarith
      have hsub : P.filter (fun p : ℕ => (p : ℝ) ≤ Xt) ⊆ primesLE ⌊Xt⌋₊ := by
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpP, hple⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr (Nat.le_floor hple),
          Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hpP).1⟩
      have hsum_le : ∑ p ∈ P.filter (fun p : ℕ => (p : ℝ) ≤ Xt), (Xt - (p : ℝ)) ≤
          2 * Xt ^ 2 / (2 * Real.log Xt) := by
        calc ∑ p ∈ P.filter (fun p : ℕ => (p : ℝ) ≤ Xt), (Xt - (p : ℝ))
            ≤ ∑ p ∈ primesLE ⌊Xt⌋₊, (Xt - (p : ℝ)) := by
              refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => ?_
              have hpX : (p : ℝ) ≤ Xt :=
                (Nat.cast_le.mpr (Finset.mem_Iic.mp (Finset.mem_filter.mp hp).1)).trans
                  (Nat.floor_le (by linarith))
              linarith
          _ ≤ (1 + 1) * Xt ^ 2 / (2 * Real.log Xt) := hsum_p Xt hXt_X₀
          _ = 2 * Xt ^ 2 / (2 * Real.log Xt) := by ring
      have hlogXt_ge : Real.log (k : ℝ) / 8 ≤ Real.log Xt := by
        rw [← hlogK8]; exact Real.log_le_log hK8_pos hXt_ge
      have hXt_sq : Xt ^ 2 ≤ 4 * (tauTerm t / lam) ^ 2 := by
        calc Xt ^ 2 ≤ (2 * (tauTerm t / lam)) ^ 2 := pow_le_pow_left₀ (by linarith) hXt_le2 2
          _ = 4 * (tauTerm t / lam) ^ 2 := by ring
      dsimp only [sliceTerm]
      calc lam * ∑ p ∈ P.filter (fun p : ℕ => (p : ℝ) ≤ Xt), (Xt - (p : ℝ))
          ≤ lam * (2 * Xt ^ 2 / (2 * Real.log Xt)) := mul_le_mul_of_nonneg_left hsum_le hlam_pos.le
        _ = lam * (Xt ^ 2 / Real.log Xt) := by ring
        _ ≤ lam * (Xt ^ 2 / (Real.log (k : ℝ) / 8)) := by
            refine mul_le_mul_of_nonneg_left ?_ hlam_pos.le
            exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hlogXt_ge
        _ ≤ lam * ((4 * (tauTerm t / lam) ^ 2) / (Real.log (k : ℝ) / 8)) := by
            refine mul_le_mul_of_nonneg_left ?_ hlam_pos.le
            exact div_le_div_of_nonneg_right hXt_sq (by positivity)
        _ = (32 / (lam * Real.log (k : ℝ))) * tauTerm t ^ 2 := by
            field_simp [hlam_pos.ne', hlogk_pos.ne']; ring
    calc ∑ t ∈ S_A, sliceTerm t
        ≤ ∑ t ∈ S_A, (32 / (lam * Real.log (k : ℝ))) * tauTerm t ^ 2 := Finset.sum_le_sum hperA
      _ = (32 / (lam * Real.log (k : ℝ))) * ∑ t ∈ S_A, tauTerm t ^ 2 := by rw [← Finset.mul_sum]
      _ ≤ (32 / (lam * Real.log (k : ℝ))) * ∑ t ∈ Finset.Ico t₀ E, tauTerm t ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => sq_nonneg _)
      _ ≤ (32 / (lam * Real.log (k : ℝ))) * η ^ 2 := by
          refine mul_le_mul_of_nonneg_left ((sum_tauTerm_sq_Ico_le ht₀_ge1).trans h1t₀_le) (by positivity)
      _ = 32 * η * (Real.sqrt ((k : ℝ) * Real.log (k : ℝ)) / Real.log (k : ℝ)) := by
          dsimp only [lam]
          field_simp [hη0.ne', hlogk_pos.ne']
      _ = 32 * η * Real.sqrt ((k : ℝ) / Real.log (k : ℝ)) := by
          rw [sqrt_mul_div_eq_sqrt_div hkpos hlogk_pos]
  -- Subcase B: `X_t < K8`
  have hpartB : ∑ t ∈ S_B, sliceTerm t ≤ η * Real.sqrt ((k : ℝ) / Real.log (k : ℝ)) := by
    let S_B_act : Finset ℕ := S_B.filter fun t : ℕ => 2 ≤ tauTerm t / lam + 1
    have hSB_eq : ∑ t ∈ S_B, sliceTerm t = ∑ t ∈ S_B_act, sliceTerm t := by
      rw [← Finset.sum_filter_add_sum_filter_not S_B (fun t : ℕ => 2 ≤ tauTerm t / lam + 1)]
      have hzero : ∑ t ∈ S_B.filter (fun t : ℕ => ¬ (2 ≤ tauTerm t / lam + 1)), sliceTerm t = 0 := by
        refine Finset.sum_eq_zero fun t ht => ?_
        have hlt2 : tauTerm t / lam + 1 < 2 := not_le.mp (Finset.mem_filter.mp ht).2
        have hemp : P.filter (fun p : ℕ => (p : ℝ) ≤ tauTerm t / lam + 1) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro p hp
          have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
            exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).two_le
          linarith
        simp [sliceTerm, hemp]
      rw [hzero, add_zero]
    have hact_sub : S_B_act ⊆ Finset.range ⌊1 / lam⌋₊ := by
      intro t ht
      have hge2 : 2 ≤ tauTerm t / lam + 1 := (Finset.mem_filter.mp ht).2
      have h1 : lam ≤ tauTerm t := by
        have := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ tauTerm t / lam) hlam_pos.le
        rwa [div_mul_cancel₀ _ hlam_pos.ne', one_mul] at this
      have h2 : lam ≤ 1 / ((t : ℝ) + 1) := h1.trans (tauTerm_le_inv t)
      have h3 : (t : ℝ) + 1 ≤ 1 / lam := by
        rw [le_div_iff₀ hlam_pos]
        have := (le_div_iff₀ (by positivity : (0 : ℝ) < (t : ℝ) + 1)).mp h2
        linarith
      have h4 : t + 1 ≤ ⌊1 / lam⌋₊ := Nat.le_floor (by exact_mod_cast h3)
      exact Finset.mem_range.mpr (by omega)
    have hact_card : (S_B_act.card : ℝ) ≤ 1 / lam := by
      calc (S_B_act.card : ℝ) ≤ ((Finset.range ⌊1 / lam⌋₊).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hact_sub
        _ = (⌊1 / lam⌋₊ : ℝ) := by simp
        _ ≤ 1 / lam := Nat.floor_le (by positivity)
    have hperB : ∀ t ∈ S_B_act, sliceTerm t ≤ lam * K8 ^ 2 := by
      intro t ht
      have hltK : tauTerm t / lam + 1 < K8 :=
        not_le.mp (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).2
      let Xt : ℝ := tauTerm t / lam + 1
      have hsub : P.filter (fun p : ℕ => (p : ℝ) ≤ Xt) ⊆ Finset.Icc 1 ⌊Xt⌋₊ := by
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpP, hple⟩
        exact Finset.mem_Icc.mpr
          ⟨(Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hpP).1).one_le, Nat.le_floor hple⟩
      have hcard_le : ((P.filter (fun p : ℕ => (p : ℝ) ≤ Xt)).card : ℝ) ≤ K8 := by
        have h1 : (P.filter (fun p : ℕ => (p : ℝ) ≤ Xt)).card ≤ ⌊Xt⌋₊ := by
          calc (P.filter (fun p : ℕ => (p : ℝ) ≤ Xt)).card ≤ (Finset.Icc 1 ⌊Xt⌋₊).card :=
                Finset.card_le_card hsub
            _ = ⌊Xt⌋₊ := by simp
        have hXt_nn : 0 ≤ Xt := by
          have := (tauTerm_pos t).le
          dsimp only [Xt]; positivity
        exact ((Nat.cast_le.mpr h1).trans (Nat.floor_le hXt_nn)).trans hltK.le
      dsimp only [sliceTerm]
      refine mul_le_mul_of_nonneg_left ?_ hlam_pos.le
      calc ∑ p ∈ P.filter (fun p : ℕ => (p : ℝ) ≤ Xt), (Xt - (p : ℝ))
          ≤ ∑ _p ∈ P.filter (fun p : ℕ => (p : ℝ) ≤ Xt), K8 :=
            Finset.sum_le_sum fun p _ => by have : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p; linarith
        _ = ((P.filter (fun p : ℕ => (p : ℝ) ≤ Xt)).card : ℝ) * K8 := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ K8 * K8 := mul_le_mul_of_nonneg_right hcard_le hK8_pos.le
        _ = K8 ^ 2 := (sq K8).symm
    rw [hSB_eq]
    calc ∑ t ∈ S_B_act, sliceTerm t
        ≤ ∑ _t ∈ S_B_act, (lam * K8 ^ 2) := Finset.sum_le_sum hperB
      _ = (S_B_act.card : ℝ) * (lam * K8 ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (1 / lam) * (lam * K8 ^ 2) := mul_le_mul_of_nonneg_right hact_card (by positivity)
      _ = K8 ^ 2 := by field_simp [hlam_pos.ne']
      _ = Real.sqrt (Real.sqrt (k : ℝ)) := hK8_sq
      _ ≤ η * Real.sqrt ((k : ℝ) / Real.log (k : ℝ)) := hq_le
  calc Real.log (∏ p ∈ P, ((e p : ℝ) + 1))
      ≤ lam * (∑ p ∈ P, (e p : ℝ) * ((p : ℝ) - 1)) + ∑ t ∈ Finset.range E, sliceTerm t := hml
    _ = lam * (∑ p ∈ P, (e p : ℝ) * ((p : ℝ) - 1)) +
        ((∑ t ∈ Finset.range t₀, sliceTerm t) + ((∑ t ∈ S_A, sliceTerm t) + (∑ t ∈ S_B, sliceTerm t))) := by
        rw [hsplit_E, Finset.sum_union hdisj_E, hsplit_AB]
    _ ≤ η * Real.sqrt ((k : ℝ) / Real.log (k : ℝ)) +
        (16 * η * Real.sqrt ((k : ℝ) / Real.log (k : ℝ)) +
          (32 * η * Real.sqrt ((k : ℝ) / Real.log (k : ℝ)) +
            η * Real.sqrt ((k : ℝ) / Real.log (k : ℝ)))) := by linarith
    _ = 50 * η * Real.sqrt ((k : ℝ) / Real.log (k : ℝ)) := by ring

/-- Exact elementary induction: `∑ t ∈ range R, √t ≤ (2/3) * R * √R`. -/
lemma sum_sqrt_range_le (R : ℕ) :
    ∑ t ∈ Finset.range R, Real.sqrt (t : ℝ) ≤ (2 / 3 : ℝ) * (R : ℝ) * Real.sqrt (R : ℝ) := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Finset.sum_range_succ]
    have hstep : (2 / 3 : ℝ) * (R : ℝ) * Real.sqrt (R : ℝ) + Real.sqrt (R : ℝ) ≤
        (2 / 3 : ℝ) * ((R + 1 : ℕ) : ℝ) * Real.sqrt ((R + 1 : ℕ) : ℝ) := by
      have hL : 0 ≤ (2 * (R : ℝ) + 3) * Real.sqrt (R : ℝ) := by positivity
      have hR : 0 ≤ 2 * ((R : ℝ) + 1) * Real.sqrt ((R : ℝ) + 1) := by positivity
      have hsq : ((2 * (R : ℝ) + 3) * Real.sqrt (R : ℝ)) ^ 2 ≤
          (2 * ((R : ℝ) + 1) * Real.sqrt ((R : ℝ) + 1)) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg R), Real.sq_sqrt (by positivity)]
        nlinarith [Nat.cast_nonneg (α := ℝ) R]
      have hle : (2 * (R : ℝ) + 3) * Real.sqrt (R : ℝ) ≤
          2 * ((R : ℝ) + 1) * Real.sqrt ((R : ℝ) + 1) := by
        nlinarith [sq_nonneg ((2 * (R : ℝ) + 3) * Real.sqrt (R : ℝ) -
          2 * ((R : ℝ) + 1) * Real.sqrt ((R : ℝ) + 1))]
      push_cast
      linarith
    linarith

/-- Exact discrete `2/3` integral inequality: for every `R ≤ k`,
`(∑ t ∈ range R, √t) + (k - R) * √R ≤ (2/3) * k * √k`. -/
lemma sum_sqrt_plus_tail_le {R k : ℕ} (hRk : R ≤ k) :
    (∑ t ∈ Finset.range R, Real.sqrt (t : ℝ)) + ((k - R : ℕ) : ℝ) * Real.sqrt (R : ℝ) ≤
      (2 / 3 : ℝ) * (k : ℝ) * Real.sqrt (k : ℝ) := by
  have h1 := sum_sqrt_range_le R
  have hsub : ((k - R : ℕ) : ℝ) = (k : ℝ) - (R : ℝ) := Nat.cast_sub hRk
  rw [hsub]
  set u := Real.sqrt (R : ℝ)
  set v := Real.sqrt (k : ℝ)
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hv : 0 ≤ v := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = (R : ℝ) := Real.sq_sqrt (Nat.cast_nonneg R)
  have hv2 : v ^ 2 = (k : ℝ) := Real.sq_sqrt (Nat.cast_nonneg k)
  have hfact : 0 ≤ (v - u) ^ 2 * (2 * v + u) := mul_nonneg (sq_nonneg _) (by linarith)
  have hcub : (2 / 3 : ℝ) * u ^ 3 + (v ^ 2 - u ^ 2) * u ≤ (2 / 3 : ℝ) * v ^ 3 := by nlinarith
  have hL : (2 / 3 : ℝ) * (R : ℝ) * u + ((k : ℝ) - (R : ℝ)) * u =
      (2 / 3 : ℝ) * u ^ 3 + (v ^ 2 - u ^ 2) * u := by
    rw [← hu2, ← hv2]; ring
  have hR : (2 / 3 : ℝ) * (k : ℝ) * v = (2 / 3 : ℝ) * v ^ 3 := by
    rw [← hv2]; ring
  linarith

/-- Subadditivity of `Real.sqrt` on nonnegative reals. -/
lemma sqrt_add_le_sqrt_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h1 : Real.sqrt (a + b) ^ 2 ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    rw [Real.sq_sqrt (by linarith), add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
    have : 0 ≤ 2 * Real.sqrt a * Real.sqrt b := by positivity
    linarith
  nlinarith [Real.sqrt_nonneg (a + b), Real.sqrt_nonneg a, Real.sqrt_nonneg b]

/-- Helper 1 for `bbmst_main`: basic large-`k` bounds on `M_cut` and `K_fn`. -/
lemma bbmst_hev_base {η X₀ : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 10) :
    let M_cut : ℕ → ℕ := fun k => ⌊η ^ 3 * Real.sqrt ((k : ℝ) * Real.log (k : ℝ))⌋₊
    let K_fn : ℕ → ℕ := fun k => max 1 ⌈η ^ 5 * Real.sqrt ((k : ℝ) * Real.log (k : ℝ))⌉₊
    ∀ᶠ k : ℕ in atTop,
      Real.exp 4 ≤ (k : ℝ) ∧
      max X₀ (2 / η + 4) ≤ (M_cut k : ℝ) ∧
      (1 - η) * (Real.log (k : ℝ) / 2) ≤ Real.log (M_cut k : ℝ) ∧
      η ^ 3 * Real.sqrt ((k : ℝ) * Real.log (k : ℝ)) / 2 ≤ ((M_cut k - 1 : ℕ) : ℝ) ∧
      η ^ 5 * Real.sqrt ((k : ℝ) * Real.log (k : ℝ)) ≤ (K_fn k : ℝ) ∧
      (K_fn k : ℝ) ≤ 2 * η ^ 5 * Real.sqrt ((k : ℝ) * Real.log (k : ℝ)) := by
  intro M_cut K_fn
  have hsq_inf : Tendsto (fun k : ℕ => Real.sqrt ((k : ℝ) * Real.log (k : ℝ))) atTop atTop :=
    Tendsto.comp Real.tendsto_sqrt_atTop
      (Tendsto.atTop_mul_atTop₀ tendsto_natCast_atTop_atTop
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  have hM_inf : Tendsto (fun k : ℕ => (M_cut k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (tendsto_nat_floor_atTop.comp (Tendsto.const_mul_atTop (pow_pos hη0 3) hsq_inf))
  have h1 : ∀ᶠ k : ℕ in atTop, Real.exp 4 ≤ (k : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  have h2 : ∀ᶠ k : ℕ in atTop, max X₀ (2 / η + 4) ≤ (M_cut k : ℝ) :=
    hM_inf.eventually (eventually_ge_atTop _)
  have h3 : ∀ᶠ k : ℕ in atTop, (1 - η) * (Real.log (k : ℝ) / 2) ≤ Real.log (M_cut k : ℝ) := by
    have hrp : Tendsto (fun x : ℝ => x ^ (η / 2)) atTop atTop := tendsto_rpow_atTop (by linarith)
    filter_upwards [(hrp.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (4 / η ^ 3)), h1] with k hkp hk1
    dsimp only [Function.comp_apply] at hkp
    have hkpos : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le (Real.exp_pos 4) hk1
    have hlog1 : 1 ≤ Real.log (k : ℝ) := by
      have : (4 : ℝ) ≤ Real.log (k : ℝ) := by
        rw [← Real.log_exp 4]; exact Real.log_le_log (Real.exp_pos 4) hk1
      linarith
    have hpow_ge : 4 * (k : ℝ) ^ ((1 - η) / 2) ≤ η ^ 3 * Real.sqrt (k : ℝ) := by
      have hmul : (k : ℝ) ^ ((1 - η) / 2) * (k : ℝ) ^ (η / 2) = Real.sqrt (k : ℝ) := by
        rw [← Real.rpow_add hkpos, show (1 - η) / 2 + η / 2 = (1 / 2 : ℝ) by ring, Real.sqrt_eq_rpow]
      have h1' : (4 / η ^ 3) * (k : ℝ) ^ ((1 - η) / 2) ≤ (k : ℝ) ^ (η / 2) * (k : ℝ) ^ ((1 - η) / 2) :=
        mul_le_mul_of_nonneg_right hkp (Real.rpow_nonneg hkpos.le _)
      rw [mul_comm ((k : ℝ) ^ (η / 2)), hmul] at h1'
      have h2' := mul_le_mul_of_nonneg_left h1' (pow_pos hη0 3).le
      have h3' : η ^ 3 * ((4 / η ^ 3) * (k : ℝ) ^ ((1 - η) / 2)) = 4 * (k : ℝ) ^ ((1 - η) / 2) := by
        field_simp [(pow_pos hη0 3).ne']
      linarith
    have hpow_ge1 : (1 : ℝ) ≤ (k : ℝ) ^ ((1 - η) / 2) :=
      Real.one_le_rpow (le_trans (Real.one_le_exp (by norm_num)) hk1) (by linarith)
    have hsq_le : Real.sqrt (k : ℝ) ≤ Real.sqrt ((k : ℝ) * Real.log (k : ℝ)) :=
      Real.sqrt_le_sqrt (by nlinarith)
    have hM_ge_pow : (k : ℝ) ^ ((1 - η) / 2) ≤ (M_cut k : ℝ) := by
      have hlt := Nat.lt_floor_add_one (η ^ 3 * Real.sqrt ((k : ℝ) * Real.log (k : ℝ)))
      have hge : 4 * (k : ℝ) ^ ((1 - η) / 2) ≤ η ^ 3 * Real.sqrt ((k : ℝ) * Real.log (k : ℝ)) :=
        hpow_ge.trans (mul_le_mul_of_nonneg_left hsq_le (pow_pos hη0 3).le)
      dsimp only [M_cut]; linarith
    have hlog_eq : Real.log ((k : ℝ) ^ ((1 - η) / 2)) = (1 - η) * (Real.log (k : ℝ) / 2) := by
      rw [Real.log_rpow hkpos]; ring
    rw [← hlog_eq]
    exact Real.log_le_log (Real.rpow_pos_of_pos hkpos _) hM_ge_pow
  have h4 : ∀ᶠ k : ℕ in atTop,
      η ^ 3 * Real.sqrt ((k : ℝ) * Real.log (k : ℝ)) / 2 ≤ ((M_cut k - 1 : ℕ) : ℝ) := by
    filter_upwards [h2] with k hk
    have h2eta : (0 : ℝ) < 2 / η := div_pos (by norm_num) hη0
    have hM4 : (4 : ℝ) ≤ (M_cut k : ℝ) := le_trans (by linarith) ((le_max_right _ _).trans hk)
    have hM1 : 1 ≤ M_cut k := by exact_mod_cast (by linarith : (1 : ℝ) ≤ (M_cut k : ℝ))
    have hsub : ((M_cut k - 1 : ℕ) : ℝ) = (M_cut k : ℝ) - 1 := by simpa using Nat.cast_sub hM1
    have hlt := Nat.lt_floor_add_one (η ^ 3 * Real.sqrt ((k : ℝ) * Real.log (k : ℝ)))
    rw [hsub]
    dsimp only [M_cut] at hlt ⊢
    linarith
  have h5 : ∀ᶠ k : ℕ in atTop,
      η ^ 5 * Real.sqrt ((k : ℝ) * Real.log (k : ℝ)) ≤ (K_fn k : ℝ) ∧
      (K_fn k : ℝ) ≤ 2 * η ^ 5 * Real.sqrt ((k : ℝ) * Real.log (k : ℝ)) := by
    filter_upwards [(Tendsto.const_mul_atTop (pow_pos hη0 5) hsq_inf).eventually
        (eventually_ge_atTop (2 : ℝ))] with k hk
    have hge1 : 1 ≤ ⌈η ^ 5 * Real.sqrt ((k : ℝ) * Real.log (k : ℝ))⌉₊ := by
      exact_mod_cast (le_trans (by norm_num : (1 : ℝ) ≤ 2) (hk.trans (Nat.le_ceil _)))
    have hKeq : K_fn k = ⌈η ^ 5 * Real.sqrt ((k : ℝ) * Real.log (k : ℝ))⌉₊ := max_eq_right hge1
    rw [hKeq]
    refine ⟨Nat.le_ceil _, ?_⟩
    have hlt := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ η ^ 5 * Real.sqrt ((k : ℝ) * Real.log (k : ℝ)))
    linarith
  filter_upwards [h1, h2, h3, h4, h5] with k h1k h2k h3k h4k ⟨h5a, h5b⟩
  exact ⟨h1k, h2k, h3k, h4k, h5a, h5b⟩

/-- Helper 2 for `bbmst_main`: large-`k` error bounds for `Δ` and metadata terms. -/
lemma bbmst_hev_err {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 10) :
    ∀ᶠ k : ℕ in atTop,
      ((2 / η ^ 3) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ))) * (Real.sqrt (k : ℝ) + 2) +
        ((2 / η ^ 3) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ))) ^ 2 + 1 ≤ η ^ 2 * (k : ℝ) ∧
      (k : ℝ) * (Real.log 2 + Real.log 2) +
        ((1 / η ^ 5) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ))) *
          (((2 / η ^ 3) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ))) * (2 * Real.log ((k : ℝ) + 1)) + 1) +
        ((2 / η ^ 3) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ))) * Real.log 2 +
        Real.log ((k : ℝ) + 1) ≤
        η * ((k : ℝ) * Real.sqrt (k : ℝ) / Real.sqrt (Real.log (k : ℝ))) := by
  have hlog_inf : Tendsto (fun k : ℕ => Real.log (k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsqlog_inf : Tendsto (fun k : ℕ => Real.sqrt (Real.log (k : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hlog_inf
  have hdiv_inf : Tendsto (fun k : ℕ => Real.sqrt (k : ℝ) / Real.sqrt (Real.log (k : ℝ))) atTop atTop := by
    have hlim : Tendsto (fun k : ℕ => Real.log (k : ℝ) / (k : ℝ)) atTop (nhds 0) := by
      have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
        simpa using (isLittleO_log_rpow_atTop one_pos).tendsto_div_nhds_zero
      exact h0.comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun k : ℕ => Real.sqrt (Real.log (k : ℝ)) / Real.sqrt (k : ℝ)) atTop (nhds 0) := by
      have hsq := (Real.continuous_sqrt.tendsto 0).comp hlim
      simp only [Real.sqrt_zero] at hsq
      refine hsq.congr' ?_
      filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (Real.exp 1))] with k hk
      dsimp only [Function.comp_apply]
      have h1k : (1 : ℝ) ≤ (k : ℝ) := le_trans (Real.one_le_exp (by norm_num)) hk
      rw [Real.sqrt_div (Real.log_nonneg h1k)]
    have hpos : ∀ᶠ k : ℕ in atTop, 0 < Real.sqrt (Real.log (k : ℝ)) / Real.sqrt (k : ℝ) := by
      filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (Real.exp 1))] with k hk
      have h1k : (1 : ℝ) < (k : ℝ) := lt_trans (Real.one_lt_exp_iff.mpr (by norm_num)) hk
      exact div_pos (Real.sqrt_pos.mpr (Real.log_pos h1k))
        (Real.sqrt_pos.mpr (lt_trans (Real.exp_pos 1) hk))
    have hinv := Filter.Tendsto.inv_tendsto_nhdsGT_zero
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h2 hpos)
    refine hinv.congr' ?_
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (Real.exp 1))] with k _
    simp [inv_div]
  have he1 : ∀ᶠ k : ℕ in atTop,
      ((2 / η ^ 3) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ))) * (Real.sqrt (k : ℝ) + 2) +
        ((2 / η ^ 3) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ))) ^ 2 + 1 ≤ η ^ 2 * (k : ℝ) := by
    filter_upwards [hsqlog_inf.eventually (eventually_ge_atTop (12 / η ^ 5)),
        hlog_inf.eventually (eventually_ge_atTop (12 / η ^ 8)),
        tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (max (Real.exp 4) (4 / η ^ 2)))]
        with k hsqL hL hk
    have hk_exp : Real.exp 4 ≤ (k : ℝ) := (le_max_left _ _).trans hk
    have hk_big : 4 / η ^ 2 ≤ (k : ℝ) := (le_max_right _ _).trans hk
    have hkpos : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le (Real.exp_pos 4) hk_exp
    have hlog_pos : 0 < Real.log (k : ℝ) :=
      Real.log_pos (lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) hk_exp)
    have hsqlog_pos : 0 < Real.sqrt (Real.log (k : ℝ)) := Real.sqrt_pos.mpr hlog_pos
    have hsqk_ge2 : 2 ≤ Real.sqrt (k : ℝ) := by
      have hk4 : (4 : ℝ) ≤ (k : ℝ) := le_trans (by linarith [Real.add_one_le_exp (4 : ℝ)]) hk_exp
      calc (2 : ℝ) = Real.sqrt 4 := by norm_num
        _ ≤ Real.sqrt (k : ℝ) := Real.sqrt_le_sqrt hk4
    have hterm1 : ((2 / η ^ 3) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ))) * (Real.sqrt (k : ℝ) + 2) ≤
        (η ^ 2 / 3) * (k : ℝ) := by
      rw [Real.sqrt_div hkpos.le]
      have h1 : Real.sqrt (k : ℝ) + 2 ≤ 2 * Real.sqrt (k : ℝ) := by linarith
      have hksq : Real.sqrt (k : ℝ) * Real.sqrt (k : ℝ) = (k : ℝ) := Real.mul_self_sqrt hkpos.le
      have hbound : 4 / (η ^ 3 * Real.sqrt (Real.log (k : ℝ))) ≤ η ^ 2 / 3 := by
        rw [div_le_iff₀ (by positivity)]
        have hmul := mul_le_mul_of_nonneg_left hsqL (by positivity : (0 : ℝ) ≤ η ^ 5 / 3)
        have hsimp : (η ^ 5 / 3) * (12 / η ^ 5) = 4 := by field_simp [hη0.ne']; ring
        nlinarith
      calc ((2 / η ^ 3) * (Real.sqrt (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))) * (Real.sqrt (k : ℝ) + 2)
          ≤ ((2 / η ^ 3) * (Real.sqrt (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))) * (2 * Real.sqrt (k : ℝ)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (4 / (η ^ 3 * Real.sqrt (Real.log (k : ℝ)))) * (Real.sqrt (k : ℝ) * Real.sqrt (k : ℝ)) := by ring
        _ = (4 / (η ^ 3 * Real.sqrt (Real.log (k : ℝ)))) * (k : ℝ) := by rw [hksq]
        _ ≤ (η ^ 2 / 3) * (k : ℝ) := mul_le_mul_of_nonneg_right hbound hkpos.le
    have hterm2 : ((2 / η ^ 3) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ))) ^ 2 ≤ (η ^ 2 / 3) * (k : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (div_nonneg hkpos.le hlog_pos.le)]
      have hbound : (2 / η ^ 3) ^ 2 / Real.log (k : ℝ) ≤ η ^ 2 / 3 := by
        rw [div_le_iff₀ hlog_pos]
        have hmul := mul_le_mul_of_nonneg_left hL (by positivity : (0 : ℝ) ≤ η ^ 2 / 3)
        have hsimp : (η ^ 2 / 3) * (12 / η ^ 8) = (2 / η ^ 3) ^ 2 := by field_simp [hη0.ne']; ring
        linarith
      calc (2 / η ^ 3) ^ 2 * ((k : ℝ) / Real.log (k : ℝ))
          = ((2 / η ^ 3) ^ 2 / Real.log (k : ℝ)) * (k : ℝ) := by ring
        _ ≤ (η ^ 2 / 3) * (k : ℝ) := mul_le_mul_of_nonneg_right hbound hkpos.le
    have hterm3 : (1 : ℝ) ≤ (η ^ 2 / 3) * (k : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hk_big (by positivity : (0 : ℝ) ≤ η ^ 2 / 3)
      have hsimp : (η ^ 2 / 3) * (4 / η ^ 2) = 4 / 3 := by field_simp [hη0.ne']
      linarith
    linarith
  have he2 : ∀ᶠ k : ℕ in atTop,
      (k : ℝ) * (Real.log 2 + Real.log 2) +
        ((1 / η ^ 5) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ))) *
          (((2 / η ^ 3) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ))) * (2 * Real.log ((k : ℝ) + 1)) + 1) +
        ((2 / η ^ 3) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ))) * Real.log 2 +
        Real.log ((k : ℝ) + 1) ≤
        η * ((k : ℝ) * Real.sqrt (k : ℝ) / Real.sqrt (Real.log (k : ℝ))) := by
    let C_meta : ℝ := 20 / η ^ 8
    filter_upwards [hdiv_inf.eventually (eventually_ge_atTop (C_meta / η)),
        tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (Real.exp 4))] with k hdiv hk_exp
    have hkpos : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le (Real.exp_pos 4) hk_exp
    have hlog_ge4 : 4 ≤ Real.log (k : ℝ) := by
      rw [← Real.log_exp 4]; exact Real.log_le_log (Real.exp_pos 4) hk_exp
    have hlog_pos : 0 < Real.log (k : ℝ) := by linarith
    have hlog2_le : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hlogk1_le : Real.log ((k : ℝ) + 1) ≤ 2 * Real.log (k : ℝ) := by
      have hk4 : (4 : ℝ) ≤ (k : ℝ) := le_trans (by linarith [Real.add_one_le_exp (4 : ℝ)]) hk_exp
      calc Real.log ((k : ℝ) + 1) ≤ Real.log ((k : ℝ) ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
        _ = 2 * Real.log (k : ℝ) := by rw [Real.log_pow]; ring
    have hsq_le_k : Real.sqrt ((k : ℝ) / Real.log (k : ℝ)) ≤ (k : ℝ) := by
      have h1 : (k : ℝ) / Real.log (k : ℝ) ≤ (k : ℝ) := div_le_self hkpos.le (by linarith)
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := le_trans (Real.one_le_exp (by norm_num)) hk_exp
      calc Real.sqrt ((k : ℝ) / Real.log (k : ℝ))
          ≤ Real.sqrt (k : ℝ) := Real.sqrt_le_sqrt h1
        _ ≤ Real.sqrt ((k : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = (k : ℝ) := Real.sqrt_sq hkpos.le
    have hlogk_le_k : Real.log (k : ℝ) ≤ (k : ℝ) := by linarith [Real.log_le_sub_one_of_pos hkpos]
    have hη8_ge1 : (1 : ℝ) ≤ 1 / η ^ 8 := by
      rw [one_le_div (pow_pos hη0 8)]; exact pow_le_one₀ hη0.le (by linarith)
    have hη5_le : 1 / η ^ 5 ≤ 1 / η ^ 8 :=
      one_div_le_one_div_of_le (pow_pos hη0 8) (pow_le_pow_of_le_one hη0.le (by linarith) (by norm_num))
    have hη3_le : 1 / η ^ 3 ≤ 1 / η ^ 8 :=
      one_div_le_one_div_of_le (pow_pos hη0 8) (pow_le_pow_of_le_one hη0.le (by linarith) (by norm_num))
    have hprod_sq : Real.sqrt ((k : ℝ) / Real.log (k : ℝ)) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ)) =
        (k : ℝ) / Real.log (k : ℝ) := Real.mul_self_sqrt (div_nonneg hkpos.le hlog_pos.le)
    have hmid : ((1 / η ^ 5) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ))) *
          (((2 / η ^ 3) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ))) * (2 * Real.log ((k : ℝ) + 1)) + 1) ≤
        9 * (1 / η ^ 8) * (k : ℝ) := by
      rw [mul_add, mul_one]
      have h1 : ((1 / η ^ 5) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ))) *
          (((2 / η ^ 3) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ))) * (2 * Real.log ((k : ℝ) + 1))) ≤
          8 * (1 / η ^ 8) * (k : ℝ) := by
        have ha : ((1 / η ^ 5) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ))) *
            (((2 / η ^ 3) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ))) * (2 * Real.log ((k : ℝ) + 1))) =
            4 * (1 / η ^ 8) * (Real.sqrt ((k : ℝ) / Real.log (k : ℝ)) *
              Real.sqrt ((k : ℝ) / Real.log (k : ℝ))) * Real.log ((k : ℝ) + 1) := by ring
        rw [ha, hprod_sq]
        calc 4 * (1 / η ^ 8) * ((k : ℝ) / Real.log (k : ℝ)) * Real.log ((k : ℝ) + 1)
            ≤ 4 * (1 / η ^ 8) * ((k : ℝ) / Real.log (k : ℝ)) * (2 * Real.log (k : ℝ)) :=
              mul_le_mul_of_nonneg_left hlogk1_le (by positivity)
          _ = 8 * (1 / η ^ 8) * (k : ℝ) := by field_simp [hlog_pos.ne']; ring
      have h2 : (1 / η ^ 5) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ)) ≤ (1 / η ^ 8) * (k : ℝ) :=
        mul_le_mul hη5_le hsq_le_k (Real.sqrt_nonneg _) (by positivity)
      linarith
    have ha : (k : ℝ) * (Real.log 2 + Real.log 2) ≤ 2 * (1 / η ^ 8) * (k : ℝ) := by
      have : Real.log 2 + Real.log 2 ≤ 2 * (1 / η ^ 8) := by linarith
      nlinarith
    have hb : ((2 / η ^ 3) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ))) * Real.log 2 ≤
        2 * (1 / η ^ 8) * (k : ℝ) := by
      have h1 : (1 / η ^ 3) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ)) ≤ (1 / η ^ 8) * (k : ℝ) :=
        mul_le_mul hη3_le hsq_le_k (Real.sqrt_nonneg _) (by positivity)
      have h2 : (2 / η ^ 3) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ)) ≤ 2 * (1 / η ^ 8) * (k : ℝ) := by
        rw [show (2 : ℝ) / η ^ 3 = 2 * (1 / η ^ 3) by ring]; linarith
      have h3 : 0 ≤ (2 / η ^ 3) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ)) := by positivity
      nlinarith
    have hc : Real.log ((k : ℝ) + 1) ≤ 2 * (1 / η ^ 8) * (k : ℝ) := by nlinarith
    have hLHS_le : (k : ℝ) * (Real.log 2 + Real.log 2) +
          ((1 / η ^ 5) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ))) *
            (((2 / η ^ 3) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ))) * (2 * Real.log ((k : ℝ) + 1)) + 1) +
          ((2 / η ^ 3) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ))) * Real.log 2 +
          Real.log ((k : ℝ) + 1) ≤ C_meta * (k : ℝ) := by
      have hC_eq : C_meta * (k : ℝ) = 20 * (1 / η ^ 8) * (k : ℝ) := by dsimp only [C_meta]; ring
      have hpos8 : 0 ≤ (1 / η ^ 8) * (k : ℝ) := by positivity
      linarith
    have hRHS_ge : C_meta * (k : ℝ) ≤ η * ((k : ℝ) * Real.sqrt (k : ℝ) / Real.sqrt (Real.log (k : ℝ))) := by
      have h1 : C_meta ≤ η * (Real.sqrt (k : ℝ) / Real.sqrt (Real.log (k : ℝ))) :=
        ((div_le_iff₀ hη0).mp hdiv).trans (by rw [mul_comm])
      calc C_meta * (k : ℝ)
          ≤ (η * (Real.sqrt (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))) * (k : ℝ) :=
            mul_le_mul_of_nonneg_right h1 hkpos.le
        _ = η * ((k : ℝ) * Real.sqrt (k : ℝ) / Real.sqrt (Real.log (k : ℝ))) := by ring
    exact hLHS_le.trans hRHS_ge
  filter_upwards [he1, he2] with k h1 h2
  exact ⟨h1, h2⟩

/-- Helper 3 for `bbmst_main`: simplify `dBig_le_exp` into `F_big x` for large `k`. -/
lemma bbmst_dBig_to_Fbig {η X₀ : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 10) (hX₀4 : 4 ≤ X₀)
    (hsum_p : ∀ X : ℝ, X₀ ≤ X →
      ∑ p ∈ primesLE ⌊X⌋₊, (X - (p : ℝ)) ≤ (1 + η) * X ^ 2 / (2 * Real.log X))
    {k M_cut : ℕ} (hlogk_pos : 0 < Real.log (k : ℝ))
    (hM_geX₀ : X₀ ≤ (M_cut : ℝ))
    (hM_ratio : (M_cut : ℝ) / ((M_cut : ℝ) - 1) ≤ 1 + η)
    (hlogM_ge : (1 - η) * (Real.log (k : ℝ) / 2) ≤ Real.log (M_cut : ℝ))
    {N x : ℕ} (W : Finset (CoordIdx N))
    (hwt : ∑ p ∈ N.primeFactors.filter (M_cut ≤ ·), coordMult N W p * (p - 1) ≤ x) :
    (dBig N M_cut W : ℝ) ≤
      Real.exp (((1 + 3 * η) * (2 * Real.sqrt Erdos1189.bbmstTau)) *
        Real.sqrt (((x : ℝ) + 1) / Real.log (k : ℝ))) := by
  let sTau : ℝ := Real.sqrt Erdos1189.bbmstTau
  let κ : ℝ := (1 + 3 * η) * (2 * sTau)
  have hsTau_pos : 0 < sTau := Real.sqrt_pos.mpr bbmstTau_pos
  have hκ_pos : 0 < κ := by positivity
  have hM4 : (4 : ℝ) ≤ (M_cut : ℝ) := hX₀4.trans hM_geX₀
  have hM1_pos : (0 : ℝ) < (M_cut : ℝ) - 1 := by linarith
  have hdb := dBig_le_exp hη0 hX₀4 hsum_p hM_geX₀ W hwt
  refine hdb.trans (Real.exp_le_exp.mpr ?_)
  have hcoeff_sq : (1 + η) * ((M_cut : ℝ) / ((M_cut : ℝ) - 1)) ^ 2 / (1 - η) ≤ (1 + 3 * η) ^ 2 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - η)]
    have hsq : ((M_cut : ℝ) / ((M_cut : ℝ) - 1)) ^ 2 ≤ (1 + η) ^ 2 :=
      pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) hM1_pos.le) hM_ratio 2
    have h1 : (1 + η) * ((M_cut : ℝ) / ((M_cut : ℝ) - 1)) ^ 2 ≤ (1 + η) ^ 3 := by
      calc (1 + η) * ((M_cut : ℝ) / ((M_cut : ℝ) - 1)) ^ 2
          ≤ (1 + η) * (1 + η) ^ 2 := mul_le_mul_of_nonneg_left hsq (by linarith)
        _ = (1 + η) ^ 3 := by ring
    have h2 : (1 + η) ^ 3 ≤ (1 + 3 * η) ^ 2 * (1 - η) := by
      have hdiff : (1 + 3 * η) ^ 2 * (1 - η) - (1 + η) ^ 3 = 2 * η * (1 - 5 * η ^ 2) := by ring
      have hpos : 0 ≤ 2 * η * (1 - 5 * η ^ 2) := mul_nonneg (by linarith) (by nlinarith)
      linarith
    exact h1.trans h2
  have hinside : 2 * (1 + η) * ((M_cut : ℝ) / ((M_cut : ℝ) - 1)) ^ 2 *
        Erdos1189.bbmstTau * ((x : ℝ) + 1) / Real.log (M_cut : ℝ) ≤
      κ ^ 2 * (((x : ℝ) + 1) / Real.log (k : ℝ)) := by
    have hnum_nn : 0 ≤ 2 * (1 + η) * ((M_cut : ℝ) / ((M_cut : ℝ) - 1)) ^ 2 *
        Erdos1189.bbmstTau * ((x : ℝ) + 1) := by
      have htau := bbmstTau_pos.le
      positivity
    have hden_pos : 0 < (1 - η) * (Real.log (k : ℝ) / 2) := mul_pos (by linarith) (by linarith)
    have h1 : 2 * (1 + η) * ((M_cut : ℝ) / ((M_cut : ℝ) - 1)) ^ 2 *
          Erdos1189.bbmstTau * ((x : ℝ) + 1) / Real.log (M_cut : ℝ) ≤
        2 * (1 + η) * ((M_cut : ℝ) / ((M_cut : ℝ) - 1)) ^ 2 *
          Erdos1189.bbmstTau * ((x : ℝ) + 1) / ((1 - η) * (Real.log (k : ℝ) / 2)) :=
      div_le_div_of_nonneg_left hnum_nn hden_pos hlogM_ge
    have h2 : 2 * (1 + η) * ((M_cut : ℝ) / ((M_cut : ℝ) - 1)) ^ 2 *
          Erdos1189.bbmstTau * ((x : ℝ) + 1) / ((1 - η) * (Real.log (k : ℝ) / 2)) =
        ((1 + η) * ((M_cut : ℝ) / ((M_cut : ℝ) - 1)) ^ 2 / (1 - η)) *
          (4 * Erdos1189.bbmstTau * (((x : ℝ) + 1) / Real.log (k : ℝ))) := by
      field_simp [(by linarith : (1 : ℝ) - η ≠ 0), hlogk_pos.ne']
      ring
    have hκ_sq : κ ^ 2 = (1 + 3 * η) ^ 2 * (4 * Erdos1189.bbmstTau) := by
      dsimp only [κ, sTau]
      rw [mul_pow, mul_pow, Real.sq_sqrt bbmstTau_pos.le]; ring
    rw [h2] at h1
    calc _ ≤ ((1 + η) * ((M_cut : ℝ) / ((M_cut : ℝ) - 1)) ^ 2 / (1 - η)) *
            (4 * Erdos1189.bbmstTau * (((x : ℝ) + 1) / Real.log (k : ℝ))) := h1
      _ ≤ (1 + 3 * η) ^ 2 * (4 * Erdos1189.bbmstTau * (((x : ℝ) + 1) / Real.log (k : ℝ))) :=
          mul_le_mul_of_nonneg_right hcoeff_sq (mul_nonneg (mul_nonneg (by norm_num) bbmstTau_pos.le) (by positivity))
      _ = κ ^ 2 * (((x : ℝ) + 1) / Real.log (k : ℝ)) := by rw [hκ_sq]; ring
  calc Real.sqrt (2 * (1 + η) * ((M_cut : ℝ) / ((M_cut : ℝ) - 1)) ^ 2 *
          Erdos1189.bbmstTau * ((x : ℝ) + 1) / Real.log (M_cut : ℝ))
      ≤ Real.sqrt (κ ^ 2 * (((x : ℝ) + 1) / Real.log (k : ℝ))) := Real.sqrt_le_sqrt hinside
    _ = κ * Real.sqrt (((x : ℝ) + 1) / Real.log (k : ℝ)) := by
        rw [Real.sqrt_mul (sq_nonneg κ), Real.sqrt_sq hκ_pos.le]

/-- **Main BBMST Upper Bound Theorem** (`Erdos1189.erdos_1189.variants.bbmst`). -/
theorem bbmst_main : type_of% @Erdos1189.erdos_1189.variants.bbmst := by
  intro ε hε
  let sTau : ℝ := Real.sqrt Erdos1189.bbmstTau
  have hsTau_pos : 0 < sTau := Real.sqrt_pos.mpr bbmstTau_pos
  let η : ℝ := min (1 / 10) (ε / (15 * sTau + 60))
  have hη0 : 0 < η := lt_min (by norm_num) (div_pos hε (by linarith))
  have hη1 : η ≤ 1 / 10 := min_le_left _ _
  have hη_eps : η * (15 * sTau + 58) ≤ ε := by
    have h1 : η ≤ ε / (15 * sTau + 60) := min_le_right _ _
    have h2 : η * (15 * sTau + 60) ≤ ε := (le_div_iff₀ (by linarith)).mp h1
    nlinarith
  obtain ⟨X₀, hX₀4, hsum_p⟩ := sum_primes_sub_le (δ := η) hη0
  let M_cut : ℕ → ℕ := fun k => ⌊η ^ 3 * Real.sqrt ((k : ℝ) * Real.log (k : ℝ))⌋₊
  let C_fn : ℕ → ℕ := fun k => Nat.sqrt k + 2
  let K_fn : ℕ → ℕ := fun k => max 1 ⌈η ^ 5 * Real.sqrt ((k : ℝ) * Real.log (k : ℝ))⌉₊
  filter_upwards [dSmall_le_exp hη0 hη1, bbmst_hev_base (X₀ := X₀) hη0 hη1, bbmst_hev_err hη0 hη1] with
      k hdSm ⟨hk_exp, hM_ge, hlogM_ge, hM1_ge, hK_ge, hK_le⟩ ⟨hDelta_le, hMeta_le⟩
  have hkpos : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le (Real.exp_pos 4) hk_exp
  have hk1 : 1 ≤ k := by
    have : (1 : ℝ) ≤ (k : ℝ) := le_trans (Real.one_le_exp (by norm_num)) hk_exp
    exact_mod_cast this
  have hlogk_ge4 : 4 ≤ Real.log (k : ℝ) := by
    rw [← Real.log_exp 4]; exact Real.log_le_log (Real.exp_pos 4) hk_exp
  have hlogk_pos : 0 < Real.log (k : ℝ) := by linarith
  have hM_geX₀ : X₀ ≤ (M_cut k : ℝ) := (le_max_left _ _).trans hM_ge
  have hM_ge_eta : 2 / η + 4 ≤ (M_cut k : ℝ) := (le_max_right _ _).trans hM_ge
  have hM2 : 2 ≤ M_cut k := by
    have : (2 : ℝ) ≤ (M_cut k : ℝ) := by linarith [div_pos (by norm_num : (0 : ℝ) < 2) hη0]
    exact_mod_cast this
  have hC2 : 2 ≤ C_fn k := by dsimp only [C_fn]; omega
  have hCsq : k < (C_fn k - 1) ^ 2 := by
    dsimp only [C_fn]
    have hsub : Nat.sqrt k + 2 - 1 = Nat.sqrt k + 1 := by omega
    rw [hsub]
    exact Nat.lt_succ_sqrt' k
  have hK1 : 1 ≤ K_fn k := le_max_left _ _
  have hM_ratio : (M_cut k : ℝ) / ((M_cut k : ℝ) - 1) ≤ 1 + η := by
    have h1eta : 0 < 1 / η := div_pos one_pos hη0
    have hM1_pos : (0 : ℝ) < (M_cut k : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (M_cut k : ℝ) := by exact_mod_cast hM2
      linarith
    rw [div_le_iff₀ hM1_pos]
    have h1 : 1 / η + 1 ≤ (M_cut k : ℝ) := by
      have h2eq : (2 : ℝ) / η = 1 / η + 1 / η := by ring
      linarith
    have h2 : 1 + η ≤ η * (M_cut k : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left h1 hη0.le
      have hsimp : η * (1 / η + 1) = 1 + η := by field_simp [hη0.ne']
      linarith
    linarith
  let κ : ℝ := (1 + 3 * η) * (2 * sTau)
  have hκ_pos : 0 < κ := by positivity
  let F_small : ℝ := Real.exp (50 * η * Real.sqrt ((k : ℝ) / Real.log (k : ℝ)))
  let F_big : ℕ → ℝ := fun x => Real.exp (κ * Real.sqrt (((x : ℝ) + 1) / Real.log (k : ℝ)))
  have h_big_ok : ∀ N, 0 < N → 1 + ∑ p ∈ N.primeFactors, N.factorization p * (p - 1) ≤ k →
      ∀ W : Finset (CoordIdx N), W ⊆ bigCoords N (M_cut k) → ∀ x : ℕ,
      (∑ p ∈ N.primeFactors.filter (M_cut k ≤ ·), coordMult N W p * (p - 1)) ≤ x →
      (dBig N (M_cut k) W : ℝ) ≤ F_big x := fun N _ _ W _ x hwt =>
    bbmst_dBig_to_Fbig hη0 hη1 hX₀4 hsum_p hlogk_pos hM_geX₀ hM_ratio hlogM_ge W hwt
  have hcount := irreducibleCount_le_explicit hk1 hM2 hC2 hCsq hK1
    (Real.exp_pos _).le (fun _ => (Real.exp_pos _).le) hdSm h_big_ok
  dsimp only at hcount
  set B : ℕ := k / (M_cut k - 1)
  set S_max : ℕ := k / K_fn k
  have hB_le : (B : ℝ) ≤ (2 / η ^ 3) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ)) := by
    have hM1_pos : (0 : ℝ) < ((M_cut k - 1 : ℕ) : ℝ) := by
      have : 1 ≤ M_cut k - 1 := by omega
      exact_mod_cast this
    have h1 : (B : ℝ) ≤ (k : ℝ) / ((M_cut k - 1 : ℕ) : ℝ) := by
      rw [le_div_iff₀ hM1_pos]; exact_mod_cast Nat.div_mul_le_self k (M_cut k - 1)
    calc (B : ℝ) ≤ (k : ℝ) / ((M_cut k - 1 : ℕ) : ℝ) := h1
      _ ≤ (k : ℝ) / (η ^ 3 * Real.sqrt ((k : ℝ) * Real.log (k : ℝ)) / 2) :=
          div_le_div_of_nonneg_left hkpos.le (by positivity) hM1_ge
      _ = (2 / η ^ 3) * ((k : ℝ) / Real.sqrt ((k : ℝ) * Real.log (k : ℝ))) := by
          field_simp [hη0.ne']
      _ = (2 / η ^ 3) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ)) := by
          rw [div_sqrt_mul_eq_sqrt_div hkpos hlogk_pos]
  have hS_le : (S_max : ℝ) ≤ (1 / η ^ 5) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ)) := by
    have hK_pos : (0 : ℝ) < (K_fn k : ℝ) := by exact_mod_cast hK1
    have h1 : (S_max : ℝ) ≤ (k : ℝ) / (K_fn k : ℝ) := by
      rw [le_div_iff₀ hK_pos]; exact_mod_cast Nat.div_mul_le_self k (K_fn k)
    calc (S_max : ℝ) ≤ (k : ℝ) / (K_fn k : ℝ) := h1
      _ ≤ (k : ℝ) / (η ^ 5 * Real.sqrt ((k : ℝ) * Real.log (k : ℝ))) :=
          div_le_div_of_nonneg_left hkpos.le (by positivity) hK_ge
      _ = (1 / η ^ 5) * ((k : ℝ) / Real.sqrt ((k : ℝ) * Real.log (k : ℝ))) := by
          field_simp [hη0.ne']
      _ = (1 / η ^ 5) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ)) := by
          rw [div_sqrt_mul_eq_sqrt_div hkpos hlogk_pos]
  let Δ : ℝ := (B : ℝ) * ((C_fn k : ℝ) + (K_fn k : ℝ)) + (B : ℝ) ^ 2 + 1
  have hΔ_le : Δ ≤ 5 * η ^ 2 * (k : ℝ) := by
    have hC_le : (C_fn k : ℝ) ≤ Real.sqrt (k : ℝ) + 2 := by
      dsimp only [C_fn]; push_cast
      have h1 : (Nat.sqrt k : ℝ) ≤ Real.sqrt (k : ℝ) := by
        rw [Real.le_sqrt (Nat.cast_nonneg _) hkpos.le, sq]
        exact_mod_cast Nat.sqrt_le k
      linarith
    have hBK_le : (B : ℝ) * (K_fn k : ℝ) ≤ 4 * η ^ 2 * (k : ℝ) := by
      calc (B : ℝ) * (K_fn k : ℝ)
          ≤ ((2 / η ^ 3) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ))) *
              (2 * η ^ 5 * Real.sqrt ((k : ℝ) * Real.log (k : ℝ))) :=
            mul_le_mul hB_le hK_le (Nat.cast_nonneg _) (by positivity)
        _ = 4 * η ^ 2 * (Real.sqrt ((k : ℝ) / Real.log (k : ℝ)) *
              Real.sqrt ((k : ℝ) * Real.log (k : ℝ))) := by field_simp [hη0.ne']; ring
        _ = 4 * η ^ 2 * (k : ℝ) := by
            rw [← Real.sqrt_mul (div_nonneg hkpos.le hlogk_pos.le)]
            have : (k : ℝ) / Real.log (k : ℝ) * ((k : ℝ) * Real.log (k : ℝ)) = (k : ℝ) ^ 2 := by
              field_simp [hlogk_pos.ne']
            rw [this, Real.sqrt_sq hkpos.le]
    have hBC_B2 : (B : ℝ) * (C_fn k : ℝ) + (B : ℝ) ^ 2 + 1 ≤ η ^ 2 * (k : ℝ) := by
      have h1 : (B : ℝ) * (C_fn k : ℝ) ≤
          ((2 / η ^ 3) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ))) * (Real.sqrt (k : ℝ) + 2) :=
        mul_le_mul hB_le hC_le (Nat.cast_nonneg _) (by positivity)
      have h2 : (B : ℝ) ^ 2 ≤ ((2 / η ^ 3) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ))) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hB_le 2
      linarith
    dsimp only [Δ]; linarith
  have hsqrtΔ_le : Real.sqrt Δ ≤ 3 * η * Real.sqrt (k : ℝ) := by
    have hΔ9 : Δ ≤ 9 * η ^ 2 * (k : ℝ) := by
      have : 0 ≤ η ^ 2 * (k : ℝ) := by positivity
      linarith
    calc Real.sqrt Δ ≤ Real.sqrt (9 * η ^ 2 * (k : ℝ)) := Real.sqrt_le_sqrt hΔ9
      _ = Real.sqrt ((3 * η) ^ 2 * (k : ℝ)) := by congr 1; ring
      _ = 3 * η * Real.sqrt (k : ℝ) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have hR_term : ∀ R ∈ Finset.range (k + 1),
      (∏ t ∈ Finset.range R, F_big (t + B * C_fn k)) *
        (F_big (R + B * (C_fn k + K_fn k) + B ^ 2)) ^ (k - R) ≤
        Real.exp (κ * (2 / 3 + 3 * η) * ((k : ℝ) * Real.sqrt (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))) := by
    intro R hR
    have hRk : R ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hR)
    have hprod_eq : (∏ t ∈ Finset.range R, F_big (t + B * C_fn k)) *
          (F_big (R + B * (C_fn k + K_fn k) + B ^ 2)) ^ (k - R) =
        Real.exp ((κ / Real.sqrt (Real.log (k : ℝ))) *
          ((∑ t ∈ Finset.range R, Real.sqrt ((t : ℝ) + ((B * C_fn k : ℕ) : ℝ) + 1)) +
            ((k - R : ℕ) : ℝ) * Real.sqrt ((R : ℝ) + Δ))) := by
      dsimp only [F_big]
      rw [← Real.exp_sum, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      have h1 : ∀ t, κ * Real.sqrt ((((t + B * C_fn k : ℕ) : ℝ) + 1) / Real.log (k : ℝ)) =
          (κ / Real.sqrt (Real.log (k : ℝ))) * Real.sqrt ((t : ℝ) + ((B * C_fn k : ℕ) : ℝ) + 1) := by
        intro t
        rw [Real.sqrt_div (by positivity), Nat.cast_add]
        ring
      have h2 : κ * Real.sqrt ((((R + B * (C_fn k + K_fn k) + B ^ 2 : ℕ) : ℝ) + 1) / Real.log (k : ℝ)) =
          (κ / Real.sqrt (Real.log (k : ℝ))) * Real.sqrt ((R : ℝ) + Δ) := by
        rw [Real.sqrt_div (by positivity)]
        have heq : (((R + B * (C_fn k + K_fn k) + B ^ 2 : ℕ) : ℝ) + 1) = (R : ℝ) + Δ := by
          dsimp only [Δ]; push_cast; ring
        rw [heq]; ring
      simp_rw [h1, h2, ← Finset.mul_sum]
      ring
    rw [hprod_eq]
    refine Real.exp_le_exp.mpr ?_
    have hBC_le : ((B * C_fn k : ℕ) : ℝ) + 1 ≤ Δ := by
      dsimp only [Δ]; push_cast
      have : (0 : ℝ) ≤ (B : ℝ) * (K_fn k : ℝ) + (B : ℝ) ^ 2 := by positivity
      linarith
    have hinner : (∑ t ∈ Finset.range R, Real.sqrt ((t : ℝ) + ((B * C_fn k : ℕ) : ℝ) + 1)) +
          ((k - R : ℕ) : ℝ) * Real.sqrt ((R : ℝ) + Δ) ≤
        (2 / 3 + 3 * η) * ((k : ℝ) * Real.sqrt (k : ℝ)) := by
      have hs1 : ∑ t ∈ Finset.range R, Real.sqrt ((t : ℝ) + ((B * C_fn k : ℕ) : ℝ) + 1) ≤
          (∑ t ∈ Finset.range R, Real.sqrt (t : ℝ)) + (R : ℝ) * Real.sqrt Δ := by
        calc ∑ t ∈ Finset.range R, Real.sqrt ((t : ℝ) + ((B * C_fn k : ℕ) : ℝ) + 1)
            ≤ ∑ t ∈ Finset.range R, Real.sqrt ((t : ℝ) + Δ) :=
              Finset.sum_le_sum fun t _ => Real.sqrt_le_sqrt (by linarith)
          _ ≤ ∑ t ∈ Finset.range R, (Real.sqrt (t : ℝ) + Real.sqrt Δ) :=
              Finset.sum_le_sum fun t _ => sqrt_add_le_sqrt_add (Nat.cast_nonneg t) (by positivity)
          _ = (∑ t ∈ Finset.range R, Real.sqrt (t : ℝ)) + (R : ℝ) * Real.sqrt Δ := by
              rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hs2 : ((k - R : ℕ) : ℝ) * Real.sqrt ((R : ℝ) + Δ) ≤
          ((k - R : ℕ) : ℝ) * Real.sqrt (R : ℝ) + ((k - R : ℕ) : ℝ) * Real.sqrt Δ := by
        have hΔnn : 0 ≤ Δ := by dsimp only [Δ]; positivity
        have hadd := sqrt_add_le_sqrt_add (Nat.cast_nonneg R) hΔnn
        have := mul_le_mul_of_nonneg_left hadd (Nat.cast_nonneg (k - R))
        linarith
      have hcomb := sum_sqrt_plus_tail_le hRk
      have hRsub : (R : ℝ) + ((k - R : ℕ) : ℝ) = (k : ℝ) := by rw [Nat.cast_sub hRk]; ring
      have hΔk : (k : ℝ) * Real.sqrt Δ ≤ 3 * η * ((k : ℝ) * Real.sqrt (k : ℝ)) := by
        have := mul_le_mul_of_nonneg_left hsqrtΔ_le hkpos.le
        linarith
      linarith [show (R : ℝ) * Real.sqrt Δ + ((k - R : ℕ) : ℝ) * Real.sqrt Δ = (k : ℝ) * Real.sqrt Δ by
        rw [← add_mul, hRsub]]
    calc (κ / Real.sqrt (Real.log (k : ℝ))) *
          ((∑ t ∈ Finset.range R, Real.sqrt ((t : ℝ) + ((B * C_fn k : ℕ) : ℝ) + 1)) +
            ((k - R : ℕ) : ℝ) * Real.sqrt ((R : ℝ) + Δ))
        ≤ (κ / Real.sqrt (Real.log (k : ℝ))) * ((2 / 3 + 3 * η) * ((k : ℝ) * Real.sqrt (k : ℝ))) :=
          mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = κ * (2 / 3 + 3 * η) * ((k : ℝ) * Real.sqrt (k : ℝ) / Real.sqrt (Real.log (k : ℝ))) := by ring
  have hTail_sum_le :
      (∑ R ∈ Finset.range (k + 1),
        (∏ t ∈ Finset.range R, F_big (t + B * C_fn k)) *
        (F_big (R + B * (C_fn k + K_fn k) + B ^ 2)) ^ (k - R)) ≤
      ((k : ℝ) + 1) *
        Real.exp (κ * (2 / 3 + 3 * η) * ((k : ℝ) * Real.sqrt (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))) := by
    calc _ ≤ ∑ _R ∈ Finset.range (k + 1),
            Real.exp (κ * (2 / 3 + 3 * η) * ((k : ℝ) * Real.sqrt (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))) :=
          Finset.sum_le_sum hR_term
      _ = ((k : ℝ) + 1) *
            Real.exp (κ * (2 / 3 + 3 * η) * ((k : ℝ) * Real.sqrt (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; rfl
  have hB_le_k : (B : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.div_le_self k (M_cut k - 1)
  have hmeta_exp :
      (2 : ℝ) ^ k * ((((B + 1 : ℝ) * (k + 1 : ℝ)) ^ B + 1) ^ S_max) * (2 : ℝ) ^ B *
        (2 : ℝ) ^ k * ((k : ℝ) + 1) ≤
      Real.exp (η * ((k : ℝ) * Real.sqrt (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))) := by
    have hpos : 0 < (2 : ℝ) ^ k * ((((B + 1 : ℝ) * (k + 1 : ℝ)) ^ B + 1) ^ S_max) *
        (2 : ℝ) ^ B * (2 : ℝ) ^ k * ((k : ℝ) + 1) := by positivity
    rw [← Real.log_le_iff_le_exp hpos]
    have hlog_eq : Real.log ((2 : ℝ) ^ k * ((((B + 1 : ℝ) * (k + 1 : ℝ)) ^ B + 1) ^ S_max) *
          (2 : ℝ) ^ B * (2 : ℝ) ^ k * ((k : ℝ) + 1)) =
        (k : ℝ) * (Real.log 2 + Real.log 2) +
        (S_max : ℝ) * Real.log (((B + 1 : ℝ) * ((k : ℝ) + 1)) ^ B + 1) +
        (B : ℝ) * Real.log 2 + Real.log ((k : ℝ) + 1) := by
      rw [Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity),
          Real.log_pow, Real.log_pow, Real.log_pow]
      ring
    rw [hlog_eq]
    have hinner_log : Real.log (((B + 1 : ℝ) * ((k : ℝ) + 1)) ^ B + 1) ≤
        (B : ℝ) * (2 * Real.log ((k : ℝ) + 1)) + 1 := by
      have hbase_ge1 : (1 : ℝ) ≤ ((B + 1 : ℝ) * ((k : ℝ) + 1)) ^ B :=
        one_le_pow₀ (one_le_mul_of_one_le_of_one_le (by linarith [Nat.cast_nonneg (α := ℝ) B]) (by linarith))
      have h1 : ((B + 1 : ℝ) * ((k : ℝ) + 1)) ^ B + 1 ≤ 2 * ((B + 1 : ℝ) * ((k : ℝ) + 1)) ^ B := by linarith
      have h2 : (B + 1 : ℝ) * ((k : ℝ) + 1) ≤ ((k : ℝ) + 1) ^ 2 := by
        rw [sq]; exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
      calc Real.log (((B + 1 : ℝ) * ((k : ℝ) + 1)) ^ B + 1)
          ≤ Real.log (2 * ((B + 1 : ℝ) * ((k : ℝ) + 1)) ^ B) := Real.log_le_log (by positivity) h1
        _ = Real.log 2 + (B : ℝ) * Real.log ((B + 1 : ℝ) * ((k : ℝ) + 1)) := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        _ ≤ 1 + (B : ℝ) * Real.log (((k : ℝ) + 1) ^ 2) := by
            refine add_le_add hlog2 (mul_le_mul_of_nonneg_left
              (Real.log_le_log (by positivity) h2) (Nat.cast_nonneg B))
        _ = (B : ℝ) * (2 * Real.log ((k : ℝ) + 1)) + 1 := by rw [Real.log_pow]; ring
    have hS_term : (S_max : ℝ) * Real.log (((B + 1 : ℝ) * ((k : ℝ) + 1)) ^ B + 1) ≤
        ((1 / η ^ 5) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ))) *
          (((2 / η ^ 3) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ))) * (2 * Real.log ((k : ℝ) + 1)) + 1) := by
      refine mul_le_mul hS_le ?_ (Real.log_nonneg (by
        have : (0 : ℝ) ≤ ((B + 1 : ℝ) * ((k : ℝ) + 1)) ^ B := by positivity
        linarith)) (by positivity)
      calc Real.log (((B + 1 : ℝ) * ((k : ℝ) + 1)) ^ B + 1)
          ≤ (B : ℝ) * (2 * Real.log ((k : ℝ) + 1)) + 1 := hinner_log
        _ ≤ ((2 / η ^ 3) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ))) * (2 * Real.log ((k : ℝ) + 1)) + 1 := by
            refine add_le_add (mul_le_mul_of_nonneg_right hB_le ?_) le_rfl
            have : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith
            linarith [Real.log_nonneg this]
    have hB_term : (B : ℝ) * Real.log 2 ≤
        ((2 / η ^ 3) * Real.sqrt ((k : ℝ) / Real.log (k : ℝ))) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hB_le (Real.log_nonneg (by norm_num))
    linarith
  have hFs_pow : F_small ^ k =
      Real.exp (50 * η * ((k : ℝ) * Real.sqrt (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))) := by
    dsimp only [F_small]
    rw [← Real.exp_nat_mul]
    congr 1
    rw [Real.sqrt_div hkpos.le]
    ring
  have hpow32 : ((k : ℝ) ^ (3 / 2 : ℝ)) / Real.sqrt (Real.log (k : ℝ)) =
      (k : ℝ) * Real.sqrt (k : ℝ) / Real.sqrt (Real.log (k : ℝ)) := by
    congr 1
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hkpos, Real.rpow_one,
        ← Real.sqrt_eq_rpow]
  have hfinal_const : η + 50 * η + κ * (2 / 3 + 3 * η) ≤ 4 * sTau / 3 + ε := by
    have hκ_exp : κ * (2 / 3 + 3 * η) = (4 / 3) * sTau + η * ((10 + 18 * η) * sTau) := by
      dsimp only [κ]; ring
    rw [hκ_exp]
    have h18 : (10 + 18 * η) * sTau ≤ 15 * sTau :=
      mul_le_mul_of_nonneg_right (by linarith) hsTau_pos.le
    have h18' : η * ((10 + 18 * η) * sTau) ≤ η * (15 * sTau) :=
      mul_le_mul_of_nonneg_left h18 hη0.le
    linarith [hη_eps]
  rw [hpow32]
  calc (Erdos1189.irreducibleCount k : ℝ)
      ≤ (2 : ℝ) ^ k * ((((B + 1 : ℝ) * (k + 1 : ℝ)) ^ B + 1) ^ S_max) * (2 : ℝ) ^ B *
          (2 * F_small) ^ k *
          (∑ R ∈ Finset.range (k + 1),
            (∏ t ∈ Finset.range R, F_big (t + B * C_fn k)) *
            (F_big (R + B * (C_fn k + K_fn k) + B ^ 2)) ^ (k - R)) := hcount
    _ ≤ (2 : ℝ) ^ k * ((((B + 1 : ℝ) * (k + 1 : ℝ)) ^ B + 1) ^ S_max) * (2 : ℝ) ^ B *
          ((2 : ℝ) ^ k * F_small ^ k) *
          (((k : ℝ) + 1) *
            Real.exp (κ * (2 / 3 + 3 * η) *
              ((k : ℝ) * Real.sqrt (k : ℝ) / Real.sqrt (Real.log (k : ℝ))))) := by
        rw [mul_pow (2 : ℝ) F_small k]
        refine mul_le_mul_of_nonneg_left hTail_sum_le ?_
        dsimp only [F_small]; positivity
    _ = ((2 : ℝ) ^ k * ((((B + 1 : ℝ) * (k + 1 : ℝ)) ^ B + 1) ^ S_max) * (2 : ℝ) ^ B *
          (2 : ℝ) ^ k * ((k : ℝ) + 1)) * F_small ^ k *
          Real.exp (κ * (2 / 3 + 3 * η) *
            ((k : ℝ) * Real.sqrt (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))) := by ring
    _ ≤ Real.exp (η * ((k : ℝ) * Real.sqrt (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))) *
          Real.exp (50 * η * ((k : ℝ) * Real.sqrt (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))) *
          Real.exp (κ * (2 / 3 + 3 * η) *
            ((k : ℝ) * Real.sqrt (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))) := by
        rw [← hFs_pow]
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_right hmeta_exp (pow_nonneg (Real.exp_pos _).le _)
    _ = Real.exp ((η + 50 * η + κ * (2 / 3 + 3 * η)) *
          ((k : ℝ) * Real.sqrt (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp ((4 * sTau / 3 + ε) *
          ((k : ℝ) * Real.sqrt (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hfinal_const (by positivity))

end AnalyticBounds

end Erdos1189BBMST


theorem OMA.solution : type_of% @Erdos1189.erdos_1189.variants.bbmst :=
  Erdos1189BBMST.bbmst_main
