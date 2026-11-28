import OMAStatements.S_oeis_a002107
import Mathlib

/-!
# The two summatory constants for OEIS A002107

After the substitution `m = 12n+1`, the absolute coefficient is the norm of a
Gaussian character sum. Its Euler factors identify the square of its Dirichlet
series with the product of the four characters modulo 12. The second-moment
series has the same numerator, divided by the principal L-function at `2s`.
We evaluate the three nonprincipal L-values at 1 by integration. Polynomial
approximation gives the harmonic sums from their real-axis singularities.
The logarithmic convolution and the prime number theorem for 1 modulo 12 then
give the ordinary sums. The square-supported correction for the second moment
has mean zero.
-/

-- Gaussian norm representatives and factorization bijections adapted from @TheWaler,
-- GaussCircleProblem.exact_form_floor, merged in 2d437695 (PR 775).
-- The divisor-sum rearrangement is from @Genbox, Erdos323.erdos_323.variants.k_eq_2.R1.H1.
-- Finite character and convolution lemmas adapted from the fleet Wave 9Q EulerSquare file.
-- The PNT block below credits its original authors and the merged port by @marcusbuffett.
-- ===== lts-lib block PNT (fleet/lib/PNT.lean) =====
/-
The proof of θ(x) ~ x (and of the weak prime number theorem it rests on, via the Wiener-Ikehara
tauberian theorem) is ported from the PrimeNumberTheoremAnd project,
  https://github.com/AlexKontorovich/PrimeNumberTheoremAnd , commit 55270df807,
by Alex Kontorovich, Terence Tao and the project's contributors, used under the Apache License 2.0.
Files used, in this order (each in its own section below):
  PrimeNumberTheoremAnd/Mathlib/Algebra/Notation/Support.lean
  PrimeNumberTheoremAnd/Mathlib/Analysis/Asymptotics/Asymptotics.lean
  PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean
  PrimeNumberTheoremAnd/Sobolev.lean
  PrimeNumberTheoremAnd/Fourier.lean
  PrimeNumberTheoremAnd/SmoothExistence.lean
  PrimeNumberTheoremAnd/Wiener.lean (up to and including theorem WeakPNT)
  PrimeNumberTheoremAnd/Consequences.lean (only add_isLittleO'', WeakPNT', WeakPNT'',
    isLittleO_sqrt_mul_log and chebyshev_asymptotic)
Modifications: imports merged into the single import above; blueprint annotations and all
attributes (blueprint, ext, continuity, fun_prop, gcongr, norm_cast) and option settings removed,
with the call sites that relied on them adjusted (an explicit CS.ext lemma, explicit continuity
facts handed to fun_prop, an explicit monotonicity step in place of gcongr); the proofs of
second_fourier and limiting_cor_aux were rewritten so that they compile without the
backward.isDefEq.respectTransparency option; four unproved and unused lemmas of Wiener.lean
(prelim_decay_2, prelim_decay_3, decay_alt and the definition AbsolutelyContinuous) were deleted.
The progression argument also adapts the arithmetic-progression consequence from the same project.
Library block OMALib.PNT (fleet/lib/PNT.lean), assembled from the fleet's merged proofs
Erdos12.erdos_12.variants.example (the Wiener-Ikehara development, Consequences.lean lemmas, and
the arithmetic-progression consequence WeakPNT_AP / chebyshev_asymptotic_pnt, also adapted from
PrimeNumberTheoremAnd) and Erdos170.erdos170.existing_bounds.R1.H1 (exists_prime_of_theta_lt and
exists_prime_Ioc_mul, written for this fleet, credit @marcusbuffett). Changes for the library:
everything put in namespace OMALib.PNT except the lemmas that extend Mathlib namespaces
(section PNTX_Base and eleven lemmas such as Filter.EventuallyEq.summable, which keep their
original root names so that dot notation still finds them); WeakPNT_AP made public; comments removed; unused declarations removed.
-/

section

section PNTX_Base

namespace Function

variable {α : Type*} [Zero α]

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

theorem IsBigO.natCast {f g : ℝ → E} (h : f =O[atTop] g) :
    (fun n : ℕ => f n) =O[atTop] fun n : ℕ => g n :=
  h.comp_tendsto tendsto_natCast_atTop_atTop

end Asymptotics

open Filter Real

theorem Real.tendsto_pow_log_div_pow_atTop (a : ℝ) (b : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun x ↦ log x ^ b / x^a) Filter.atTop (nhds 0) := by
  apply Asymptotics.isLittleO_iff_tendsto' _|>.mp <| isLittleO_log_rpow_rpow_atTop _ ha
  filter_upwards [eventually_gt_atTop 0] with x hx
  intro h
  rw [rpow_eq_zero hx.le ha.ne.symm] at h
  exfalso
  linarith

end PNTX_Base

namespace OMALib.PNT

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

lemma deriv_apply {f : CS (n + 1) E} {x : ℝ} : f.deriv x = _root_.deriv f x := rfl

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

  let f' := f.deriv
  let f'' := f'.deriv
  let g' := (g : CS 2 ℝ).deriv
  let g'' := g'.deriv
  let h R v := 1 - g.scale R v
  let h' R := - (g.scale R).deriv
  let h'' R := - (g.scale R).deriv.deriv

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

theorem hasDerivAt_e {u x : ℝ} : HasDerivAt (e u) (-2 * π * u * I * e u x) x := by
  have l2 : HasDerivAt (fun v => -v * u) (-u) x := by
    simpa only [neg_mul_comm] using hasDerivAt_mul_const (-u)
  convert! (hasDerivAt_fourierChar (-x * u)).scomp x l2 using 1
  change _ = ((-u : ℝ) : ℂ) * _
  simp ; ring

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

end PNTX_Smooth

section PNTX_Wiener

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

lemma _root_.Finset.sum_shift_front {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = u 0 + cumsum (shift u) n := by
  simp_rw [add_comm n, cumsum, Finset.sum_range_add, Finset.sum_range_one, add_comm 1] ; rfl

lemma _root_.Finset.sum_shift_back {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
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

lemma _root_.Filter.EventuallyEq.summable {u v : ℕ → ℝ} (h : u =ᶠ[atTop] v) (hu : Summable v) :
    Summable u :=
  summable_of_isBigO_nat hu h.isBigO

lemma summable_congr_ae {u v : ℕ → ℝ} (huv : u =ᶠ[atTop] v) : Summable u ↔ Summable v := by
  constructor <;> intro h <;> simp [huv.summable, huv.symm.summable, h]

lemma _root_.BoundedAtFilter.add_const {u : ℕ → ℝ} {c : ℝ} :
    BoundedAtFilter atTop (fun n => u n + c) ↔ BoundedAtFilter atTop u := by
  have : u = fun n => (u n + c) + (-c) := by ext n ; ring
  simp only [BoundedAtFilter]
  constructor <;> intro h
  on_goal 1 => rw [this]
  all_goals { exact h.add (const_boundedAtFilter _ _) }

lemma _root_.BoundedAtFilter.comp_add {u : ℕ → ℝ} {N : ℕ} :
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

lemma _root_.Asymptotics.IsBigO.add_isLittleO_right {f g : ℝ → ℝ} (h : g =o[atTop] f) :
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

lemma _root_.Asymptotics.IsBigO.sq {α : Type*} [Preorder α] {f g : α → ℝ} (h : f =O[atTop] g) :
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

lemma _root_.Real.log_eventually_gt_atTop (a : ℝ) :
    ∀ᶠ x in atTop, a < Real.log x :=
  Real.tendsto_log_atTop.eventually (eventually_gt_atTop a)

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

noncomputable def pp' (a x : ℝ) : ℝ := a ^ 2 * (2 * (x + 1))

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

  let S1 x (ψ : ℝ → ℂ) := ∑' (n : ℕ), f n / ↑n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑n / x))
  let S2 x (ψ : ℝ → ℂ) := ↑A * ∫ (u : ℝ) in Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))
  let S x ψ := S1 x ψ - S2 x ψ ; change Tendsto (fun x ↦ S x ψ) atTop (𝓝 0)

  obtain g := exists_trunc
  let Ψ R := g.scale R * ψ
  have key R : Tendsto (fun x ↦ S x (Ψ R)) atTop (𝓝 0) := limiting_cor (Ψ R) hf hcheby hG hG'

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

  filter_upwards [eventually_ge_atTop 1, key R (ε / 2) (by positivity)] with x hx key

  have key3 : ‖S x (ψ - Ψ R)‖ < ε / 2 := by
    have : ‖S x _‖ ≤ _ * M := @bound_main f C A x hx (ψ - Ψ R) hcheby
    apply this.trans_lt
    apply (mul_le_mul (d := 1 + M) le_rfl (by simp) (by positivity) W21.norm_nonneg).trans_lt
    have : 0 < 1 + M := by positivity
    convert! (mul_lt_mul_iff_left₀ this).mpr hRψ using 1 ; field_simp

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

  by_cases hab : a = b
  · simp [hab]
  replace hb : a < b := lt_of_le_of_ne hb hab ; clear hab

  let S (g : ℝ → ℝ) (x : ℝ) :=  (∑' n, f n * g (n / x)) / x
  have hSnonneg {g : ℝ → ℝ} (hg : 0 ≤ g) : ∀ᶠ x : ℝ in atTop, 0 ≤ S g x := by
    filter_upwards [eventually_ge_atTop 0] with x hx
    refine div_nonneg ?_ hx
    refine tsum_nonneg (fun i => mul_nonneg (hpos _) (hg _))
  have hA : 0 ≤ A := residue_nonneg hpos hf hcheby hG hG'

  let Iab : ℝ → ℝ := indicator (Ico a b) 1
  change Tendsto (S Iab) atTop (𝓝 (A * (b - a)))
  have hIab : HasCompactSupport Iab := by simpa [Iab, HasCompactSupport, tsupport, hb.ne] using isCompact_Icc
  have Iab_nonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ S Iab x := hSnonneg (indicator_nonneg (by simp))
  have Iab2 : IsBoundedUnder (· ≤ ·) atTop (S Iab) := by
    obtain ⟨C, hC⟩ := hcheby ; exact ⟨C * 2 * b, WI_sum_Iab_le' hpos hC (by linarith)⟩
  have Iab3 : IsBoundedUnder (· ≥ ·) atTop (S Iab) := ⟨0, Iab_nonneg⟩
  have Iab0 : IsCoboundedUnder (· ≥ ·) atTop (S Iab) := Iab2.isCoboundedUnder_ge
  have Iab1 : IsCoboundedUnder (· ≤ ·) atTop (S Iab) := Iab3.isCoboundedUnder_le

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

theorem WeakPNT : Tendsto (fun N ↦ cumsum Λ N / N) atTop (𝓝 1) := by
  let F := vonMangoldt.LFunctionResidueClassAux (q := 1) 1
  have hnv := riemannZeta_ne_zero_of_one_le_re
  have l1 (n : ℕ) : 0 ≤ Λ n := vonMangoldt_nonneg
  have l2 s (hs : 1 < s.re) : F s = LSeries Λ s - 1 / (s - 1) := by
    have := vonMangoldt.eqOn_LFunctionResidueClassAux (q := 1) isUnit_one hs
    simp only [F, this, vonMangoldt.residueClass, Nat.totient_one, Nat.cast_one, inv_one, one_div, sub_left_inj]
    apply LSeries_congr
    intro n _
    simp only [ofReal_inj, indicator_apply_eq_self, mem_setOf_eq]
    exact fun hn ↦ absurd (Subsingleton.eq_one _) hn
  have l3 : ContinuousOn F {s | 1 ≤ s.re} := vonMangoldt.continuousOn_LFunctionResidueClassAux 1
  have l4 : cheby Λ := vonMangoldt_cheby
  have l5 (σ' : ℝ) (hσ' : 1 < σ') : Summable (nterm Λ σ') := by
    simpa only [← nterm_eq_norm_term] using (@ArithmeticFunction.LSeriesSummable_vonMangoldt σ' hσ').norm
  apply WienerIkeharaTheorem' l1 l5 l4 l3 l2

end PNTX_Wiener

section PNTX_Conseq

section PNTConseq
open ArithmeticFunction hiding log
open Nat hiding log
open Finset
open BigOperators Filter Real Classical Asymptotics MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega Chebyshev

theorem _root_.Asymptotics.IsEquivalent.add_isLittleO'' {α : Type*} {β : Type*} [NormedAddCommGroup β]
    {u : α → β} {v : α → β} {w : α → β} {l : Filter α}
    (huv : Asymptotics.IsEquivalent l u v) (hwu : (u - w) =o[l] v) :
    Asymptotics.IsEquivalent l w v := by
  rw [← sub_sub_self u w]
  exact Asymptotics.IsEquivalent.sub_isLittleO huv hwu

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

theorem WeakPNT'' : ψ ~[atTop] (fun x ↦ x) := by
    rw [(by rfl : ψ = (fun x ↦ ψ x))]
    simp_rw [Chebyshev.psi_eq_sum_Icc]
    apply IsEquivalent.trans (v := fun x ↦ (⌊x⌋₊:ℝ))
    · rw [isEquivalent_iff_tendsto_one]
      · convert! Tendsto.comp WeakPNT' tendsto_nat_floor_atTop
        infer_instance
      rw [eventually_iff]
      simp only [ne_eq, cast_eq_zero, floor_eq_zero, not_lt, mem_atTop_sets,
        Set.mem_setOf_eq]
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

section PNTX_AP
open Filter Real
open ArithmeticFunction hiding log
open scoped Topology
theorem WeakPNT_AP {q a : ℕ} (hq : q ≥ 1) (ha : a.Coprime q) (ha' : a < q) :
    Tendsto (fun N ↦ cumsum (fun n ↦ if n % q = a then vonMangoldt n else 0) N / N)
      atTop (𝓝 (1 / q.totient)) := by
  haveI : NeZero q := ⟨by omega⟩
  let F := vonMangoldt.residueClass (a : ZMod q)
  have hpos : 0 ≤ F := fun n => vonMangoldt.residueClass_nonneg _ _
  have hle (n : ℕ) : F n ≤ vonMangoldt n := vonMangoldt.residueClass_le _ _
  have habs (n : ℕ) : ‖(F n : ℂ)‖ ≤ ‖(vonMangoldt n : ℂ)‖ := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hpos _),
      abs_of_nonneg vonMangoldt_nonneg] using hle n
  have hcheb : cheby (fun n => (F n : ℂ)) := by
    obtain ⟨C,hC⟩ := vonMangoldt_cheby
    exact ⟨C,fun N => (Finset.sum_le_sum fun n _ => habs n).trans (hC N)⟩
  have hsum (σ : ℝ) (hσ : 1 < σ) : Summable (nterm (fun n => (F n:ℂ)) σ) := by
    have hbase : Summable (nterm (fun n => (vonMangoldt n:ℂ)) σ) := by
      simpa only [← nterm_eq_norm_term] using (@ArithmeticFunction.LSeriesSummable_vonMangoldt σ hσ).norm
    apply Summable.of_nonneg_of_le _ _ hbase
    · intro n; simp only [nterm]; split <;> positivity
    · intro n; simp only [nterm]; split <;> first | exact le_rfl | exact div_le_div_of_nonneg_right (habs n) (by positivity)
  have hu := (ZMod.isUnit_iff_coprime a q).mpr ha
  have hres : Set.EqOn (vonMangoldt.LFunctionResidueClassAux (a : ZMod q))
      (fun s : ℂ => LSeries (fun n => (F n:ℂ)) s - ((1 / (q.totient:ℝ):ℝ):ℂ) / (s-1))
      {s | 1 < s.re} := by
    simpa [F,one_div] using vonMangoldt.eqOn_LFunctionResidueClassAux hu
  have ht := WienerIkeharaTheorem' hpos hsum hcheb
    (vonMangoldt.continuousOn_LFunctionResidueClassAux (a : ZMod q)) hres
  have he (n : ℕ) : F n = (if n % q = a then vonMangoldt n else 0) := by
    simp [F,vonMangoldt.residueClass,Set.indicator_apply,ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha']
  simpa only [cumsum,he] using ht
end PNTX_AP
end OMALib.PNT
end
-- End of the PNT block.

namespace Wave9Q.EulerSquare

/-- The exponent mod 4 of 1+i in F9, reduced from its discrete logarithm mod 8.
The zero input is unused. -/
def code (x y : ZMod 3) : ZMod 4 :=
  if x = 0 then 2 else if y = 0 then 0 else if x = y then 1 else 3

theorem code_mul : ∀ a b c d : ZMod 3, (a ≠ 0 ∨ b ≠ 0) → (c ≠ 0 ∨ d ≠ 0) →
    code (a*c-b*d) (a*d+b*c) = code a b + code c d := by
  decide +kernel

theorem code_conj : ∀ a b : ZMod 3, code a (-b) = -code a b := by
  decide +kernel

def parityCode (b : ZMod 2) : ZMod 4 := if b = 0 then 0 else 2

theorem parity_mul : ∀ a b c d : ZMod 2, a+b=1 → c+d=1 →
    parityCode (a*d+b*c) = parityCode b + parityCode d := by
  decide +kernel

/-- The pentagonal pair gives the Gaussian norm, with both polygonal indices integral. -/
theorem pentagonal_norm (u v : ℤ) :
    (3*(u+v)+1)^2 + (3*(u-v))^2 =
    6*(u*(3*u+1) + v*(3*v+1)) + 1 := by ring

/-- The finite target uses exactly these convolution coefficients. -/
theorem finite_square (n : ℕ) :
    (∏ k ∈ Finset.range n, (1 - Polynomial.X ^ (k+1) : Polynomial ℤ)^2).coeff n =
    ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
      (∏ k ∈ Finset.range n, (1 - Polynomial.X ^ (k+1) : Polynomial ℤ)).coeff ij.1 *
      (∏ k ∈ Finset.range n, (1 - Polynomial.X ^ (k+1) : Polynomial ℤ)).coeff ij.2 := by
  rw [Finset.prod_pow, pow_two, Polynomial.coeff_mul]

/-- Logarithmic derivative in the evaluation of L(1,chi_12). -/
theorem primitive_derivative_algebra (x r : ℝ) (hr : r^2 = 3) :
    ((2*x+r)*(x^2-r*x+1) - (2*x-r)*(x^2+r*x+1)) *
       (1-x^2+x^4) = 2*r*(1-x^2)*(x^2+r*x+1)*(x^2-r*x+1) := by
  linear_combination (2*r*x^2*(1-x^2)) * hr

/-- Bounding the error on the terminal part of the log-weighted convolution.
The indices in s can be any finite collection of positive integers d ≤ x. -/
theorem convolution_tail {s : Finset ℕ} (w err : ℕ → ℝ) (C : ℝ)
    (hw : ∀ d ∈ s, 0 ≤ w d) (he : ∀ d ∈ s, |err d| ≤ C) :
    |∑ d ∈ s, w d * err d| ≤ C * ∑ d ∈ s, w d := by
  calc
    _ ≤ ∑ d ∈ s, |w d * err d| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ s, C * w d := by
      refine Finset.sum_le_sum (fun d hd => ?_)
      rw [abs_mul, abs_of_nonneg (hw d hd), mul_comm C]
      exact mul_le_mul_of_nonneg_left (he d hd) (hw d hd)
    _ = _ := (Finset.mul_sum ..).symm

open Filter

theorem coeff_euler_trunc {d n : ℕ} (hd : d ≤ n) :
    (∏ k ∈ Finset.range n, (1 - Polynomial.X ^ (k+1) : Polynomial ℤ)).coeff d =
      (PowerSeries.pentagonalSeries ℤ).coeff d := by
  let P (m : ℕ) := ∏ k ∈ Finset.range m, (1 - PowerSeries.X ^ (k+1) : PowerSeries ℤ)
  have stable (m : ℕ) (hm : n ≤ m) : (P m).coeff d = (P n).coeff d := by
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ih =>
      simpa [P, Finset.prod_range_succ, mul_sub, PowerSeries.coeff_mul_X_pow',
        show ¬ m + 1 ≤ d by omega] using ih
  obtain ⟨m, hm⟩ := eventually_atTop.mp (tendsto_finset_range.eventually
    (PowerSeries.coeff_prod_one_sub_X_pow_eventually_eq ℤ d))
  have he := (stable (max m n) (le_max_right ..)).symm.trans (hm _ (le_max_left ..))
  let φ := Polynomial.coeToPowerSeries.ringHom (R := ℤ)
  rw [← Polynomial.coeff_coe]
  change (PowerSeries.coeff d (φ (∏ k ∈ Finset.range n,
    (1 - Polynomial.X ^ (k+1) : Polynomial ℤ)))) = _
  rw [map_prod]
  simp_rw [map_sub, map_one, map_pow]
  simpa only [P, φ, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X] using he

theorem coefficient_convolution (n : ℕ) :
    OMA.S_oeis_a002107.a n = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        (PowerSeries.pentagonalSeries ℤ).coeff ij.1 *
        (PowerSeries.pentagonalSeries ℤ).coeff ij.2 := by
  rw [OMA.S_oeis_a002107.a, finite_square]
  refine Finset.sum_congr rfl fun ⟨i,j⟩ hij => ?_
  have hij' : i+j=n := by simpa using hij
  rw [coeff_euler_trunc (d := i) (by omega), coeff_euler_trunc (d := j) (by omega)]


noncomputable def primaryPoints (m : ℕ) : Finset GaussianInt :=
  (((Finset.Icc (-(m : ℤ)) (m : ℤ)) ×ˢ
    (Finset.Icc (-(m : ℤ)) (m : ℤ))).image
    (fun p : ℤ × ℤ => (⟨p.1,p.2⟩ : GaussianInt))).filter
    (fun z => z.norm = (m : ℤ) ∧ z.re % 3 = 1 ∧ z.im % 3 = 0)

theorem gaussian_norm (z : GaussianInt) : z.norm = z.re^2 + z.im^2 := by
  simp [Zsqrtd.norm, pow_two]

theorem mem_primary {m : ℕ} {z : GaussianInt} :
    z ∈ primaryPoints m ↔ z.norm = (m : ℤ) ∧ z.re % 3 = 1 ∧ z.im % 3 = 0 := by
  rw [primaryPoints, Finset.mem_filter]
  refine and_iff_right_of_imp fun h => ?_
  obtain ⟨hz, -, -⟩ := h
  rw [gaussian_norm] at hz
  refine Finset.mem_image.mpr ⟨(z.re,z.im), ?_, rfl⟩
  simp only [Finset.mem_product, Finset.mem_Icc]
  have bound (x : ℤ) : -x^2 ≤ x ∧ x ≤ x^2 := by
    rcases le_or_gt x 0 with hx | hx
    · by_cases hz : x = 0
      · simp [hz]
      · constructor <;> nlinarith [mul_nonneg_of_nonpos_of_nonpos hx (show x+1 ≤ 0 by omega), sq_nonneg x]
    · constructor <;> nlinarith [mul_nonneg hx.le (show 0 ≤ x-1 by omega), sq_nonneg x]
  have hx := bound z.re
  have hy := bound z.im
  constructor <;> constructor <;> nlinarith [sq_nonneg z.re,sq_nonneg z.im]

def gaussPoint (u v : ℤ) : GaussianInt := ⟨3*(u+v)+1, 3*(u-v)⟩

theorem norm_gaussPoint (u v : ℤ) :
    (gaussPoint u v).norm = 12 * ((pentagonal (-u) : ℤ) + pentagonal (-v)) + 1 := by
  rw [gaussian_norm]
  change (3*(u+v)+1)^2 + (3*(u-v))^2 = _
  rw [pentagonal_norm]
  linarith [two_mul_natCast_pentagonal_neg u, two_mul_natCast_pentagonal_neg v]

theorem recover_gaussPoint {n : ℕ} {z : GaussianInt} (hz : z ∈ primaryPoints (12*n+1)) :
    gaussPoint ((z.re+z.im-1)/6) ((z.re-z.im-1)/6) = z := by
  obtain ⟨hn,hx,hy⟩ := mem_primary.mp hz
  rw [gaussian_norm] at hn
  push_cast at hn
  have hsq (k : ℤ) : k^2 % 2 = k % 2 := by
    rw [sq, Int.mul_emod]
    rcases (show k % 2 = 0 ∨ k % 2 = 1 by omega) with e | e <;> rw [e] <;> decide
  have hpar := congrArg (fun k : ℤ => k % 2) hn
  change (_ + _) % 2 = _ at hpar
  rw [Int.add_emod, hsq, hsq] at hpar
  apply Zsqrtd.ext <;> dsimp [gaussPoint] <;> omega

theorem sign_gaussPoint (u v : ℤ) :
    (gaussPoint u v).im.negOnePow = (-u).negOnePow * (-v).negOnePow := by
  rw [← Int.negOnePow_add, Int.negOnePow_eq_iff]
  exact ⟨2*u-v, by dsimp [gaussPoint]; ring⟩


theorem coefficient_primary (n : ℕ) : OMA.S_oeis_a002107.a n =
    ∑ z ∈ primaryPoints (12*n+1), (z.im.negOnePow : ℤ) := by
  rw [coefficient_convolution]
  symm
  let u (z : GaussianInt) := (z.re+z.im-1)/6
  let v (z : GaussianInt) := (z.re-z.im-1)/6
  have inv (i j : ℤ) : u (gaussPoint i j) = i ∧ v (gaussPoint i j) = j := by
    dsimp [u,v,gaussPoint]
    constructor <;> omega
  refine Finset.sum_bij_ne_zero (fun z _ _ => (pentagonal (-(u z)), pentagonal (-(v z))))
    ?_ ?_ ?_ ?_
  · intro z hz _
    have e := norm_gaussPoint (u z) (v z)
    rw [recover_gaussPoint hz, (mem_primary.mp hz).1] at e
    simp only [Finset.HasAntidiagonal.mem_antidiagonal]
    omega
  · intro a ha _ b hb _ h
    have hu : u a = u b := by simpa using congrArg Prod.fst h
    have hv : v a = v b := by simpa using congrArg Prod.snd h
    calc
      a = gaussPoint (u a) (v a) := (recover_gaussPoint ha).symm
      _ = gaussPoint (u b) (v b) := by rw [hu,hv]
      _ = b := recover_gaussPoint hb
  · rintro ⟨i,j⟩ hij h
    have hij' : i+j=n := by simpa using hij
    obtain ⟨hi,hj⟩ := mul_ne_zero_iff.mp h
    obtain ⟨a, rfl⟩ : i ∈ Set.range pentagonal := by
      by_contra hn
      exact hi (PowerSeries.coeff_pentagonalSeries_eq_zero ℤ hn)
    obtain ⟨b, rfl⟩ : j ∈ Set.range pentagonal := by
      by_contra hn
      exact hj (PowerSeries.coeff_pentagonalSeries_eq_zero ℤ hn)
    refine ⟨gaussPoint (-a) (-b), mem_primary.mpr ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [norm_gaussPoint, neg_neg, neg_neg, Nat.cast_add, Nat.cast_mul]
      omega
    · dsimp [gaussPoint]; omega
    · dsimp [gaussPoint]; omega
    · exact Units.ne_zero _
    · simp only [(inv (-a) (-b)).1, (inv (-a) (-b)).2, neg_neg]
  · intro z hz _
    simp only [PowerSeries.coeff_pentagonalSeries_pentagonal, Int.cast_id]
    have he := sign_gaussPoint (u z) (v z)
    rw [recover_gaussPoint hz] at he
    exact congrArg (fun c : ℤˣ => (c : ℤ)) he

private def giNorm (z : GaussianInt) : ℕ := z.norm.natAbs

private lemma giNorm_eq (z : GaussianInt) :
    giNorm z = z.re.natAbs ^ 2 + z.im.natAbs ^ 2 := by
  simpa [giNorm, sq] using GaussianInt.natAbs_norm_eq z

private lemma giNorm_mul (z w : GaussianInt) : giNorm (z * w) = giNorm z * giNorm w := by
  simp [giNorm, Zsqrtd.norm_mul, Int.natAbs_mul]

private lemma giNorm_pow (z : GaussianInt) (k : ℕ) : giNorm (z ^ k) = (giNorm z) ^ k := by
  induction k with
  | zero => simp [giNorm]
  | succ k ih => rw [pow_succ, giNorm_mul, ih, pow_succ]

private lemma giNorm_star (z : GaussianInt) : giNorm (star z) = giNorm z := by
  simp [giNorm, Zsqrtd.norm_conj]

private lemma giNorm_natCast (n : ℕ) : giNorm (n : GaussianInt) = n ^ 2 := by
  simp [giNorm, Zsqrtd.norm_natCast, Int.natAbs_mul, sq]

private lemma giNorm_eq_one_iff (z : GaussianInt) : giNorm z = 1 ↔ IsUnit z :=
  Zsqrtd.norm_eq_one_iff

private lemma giNorm_eq_zero_iff (z : GaussianInt) : giNorm z = 0 ↔ z = 0 := by
  simp only [giNorm, Int.natAbs_eq_zero]
  exact Zsqrtd.norm_eq_zero_iff (d := -1) (by norm_num) z

private lemma giNorm_eq_of_associated {z w : GaussianInt} (h : Associated z w) :
    giNorm z = giNorm w := by
  rcases h with ⟨u, rfl⟩
  rw [giNorm_mul, (giNorm_eq_one_iff (u : GaussianInt)).mpr u.isUnit, mul_one]

private lemma giNorm_dvd_of_dvd {z w : GaussianInt} (h : z ∣ w) : giNorm z ∣ giNorm w := by
  rcases h with ⟨c, rfl⟩
  rw [giNorm_mul]
  exact dvd_mul_right _ _

private lemma gi_mul_star (z : GaussianInt) : z * star z = (giNorm z : GaussianInt) := by
  have h1 : (z.norm : GaussianInt) = z * star z := Zsqrtd.norm_eq_mul_conj z
  have h2 : (giNorm z : GaussianInt) = (z.norm : GaussianInt) := by
    simp [giNorm]
  exact h1.symm.trans h2.symm

private def giI : GaussianInt := ⟨0, 1⟩

private def giUnits : Finset GaussianInt := {1, -1, giI, -giI}

private lemma giUnits_card : giUnits.card = 4 := by decide

private lemma mem_giUnits_iff (u : GaussianInt) : u ∈ giUnits ↔ IsUnit u := by
  constructor
  · intro hu
    rw [← giNorm_eq_one_iff]
    simp only [giUnits, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> decide
  · intro hu
    have hnorm : u.re.natAbs ^ 2 + u.im.natAbs ^ 2 = 1 := by
      rw [← giNorm_eq, (giNorm_eq_one_iff u).mpr hu]
    have ha : u.re.natAbs ≤ 1 := by nlinarith
    have hb : u.im.natAbs ≤ 1 := by nlinarith
    have hcases : (u.re = 1 ∧ u.im = 0) ∨ (u.re = -1 ∧ u.im = 0) ∨
        (u.re = 0 ∧ u.im = 1) ∨ (u.re = 0 ∧ u.im = -1) := by
      interval_cases ha' : u.re.natAbs <;> interval_cases hb' : u.im.natAbs <;>
        omega
    simp only [giUnits, Finset.mem_insert, Finset.mem_singleton]
    rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; ext <;> simp [h1, h2]
    · right; left; ext <;> simp [h1, h2]
    · right; right; left; ext <;> simp [giI, h1, h2]
    · right; right; right; ext <;> simp [giI, h1, h2]

private def InQ1 (z : GaussianInt) : Prop := 0 < z.re ∧ 0 ≤ z.im

private instance : DecidablePred InQ1 := fun z => inferInstanceAs (Decidable (0 < z.re ∧ 0 ≤ z.im))

private def canon (z : GaussianInt) : GaussianInt :=
  if 0 < z.re ∧ 0 ≤ z.im then z
  else if z.re ≤ 0 ∧ 0 < z.im then -giI * z
  else if z.re < 0 ∧ z.im ≤ 0 then -z
  else giI * z

private lemma canon_associated (z : GaussianInt) : Associated z (canon z) := by
  have h2 : IsUnit (-1 : GaussianInt) := (mem_giUnits_iff (-1)).mp (by decide)
  have h3 : IsUnit giI := (mem_giUnits_iff giI).mp (by decide)
  have h4 : IsUnit (-giI) := (mem_giUnits_iff (-giI)).mp (by decide)
  unfold canon
  split_ifs
  · exact Associated.refl z
  · rcases h4 with ⟨u, hu⟩
    exact ⟨u, by rw [hu, mul_comm]⟩
  · rcases h2 with ⟨u, hu⟩
    exact ⟨u, by rw [hu]; ring⟩
  · rcases h3 with ⟨u, hu⟩
    exact ⟨u, by rw [hu, mul_comm]⟩

private lemma canon_inQ1 {z : GaussianInt} (hz : z ≠ 0) : InQ1 (canon z) := by
  have hne : z.re ≠ 0 ∨ z.im ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (by ext <;> simp [h.1, h.2])
  unfold canon InQ1
  split_ifs with h1 h2 h3
  · exact h1
  · constructor <;> simp [giI] <;> omega
  · constructor <;> simp <;> omega
  · constructor <;> simp [giI] <;> omega

private lemma eq_of_associated_inQ1 {z w : GaussianInt}
    (hz : InQ1 z) (hw : InQ1 w) (h : Associated z w) : z = w := by
  rcases h with ⟨u, hu⟩
  have hmem : (u : GaussianInt) ∈ giUnits := (mem_giUnits_iff u).mpr u.isUnit
  simp only [giUnits, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h1 | h1 | h1 | h1
  · rw [h1, mul_one] at hu; exact hu
  · rw [h1] at hu
    have hre : w.re = -z.re := by rw [← hu]; simp
    have : 0 < z.re := hz.1
    have : 0 < w.re := hw.1
    omega
  · rw [h1] at hu
    have hre : w.re = -z.im := by rw [← hu]; simp [giI]
    have : 0 ≤ z.im := hz.2
    have : 0 < w.re := hw.1
    omega
  · rw [h1] at hu
    have him : w.im = -z.re := by rw [← hu]; simp [giI]
    have : 0 < z.re := hz.1
    have : 0 ≤ w.im := hw.2
    omega

private lemma canon_eq_iff_associated {z w : GaussianInt} (hz : z ≠ 0) (hw : w ≠ 0) :
    canon z = canon w ↔ Associated z w := by
  constructor
  · intro h
    exact (canon_associated z).trans (h ▸ (canon_associated w).symm)
  · intro h
    have hass : Associated (canon z) (canon w) :=
      (canon_associated z).symm.trans (h.trans (canon_associated w))
    exact eq_of_associated_inQ1 (canon_inQ1 hz) (canon_inQ1 hw) hass

private lemma canon_eq_self {z : GaussianInt} (hz : InQ1 z) : canon z = z := by
  have hz0 : z ≠ 0 := by
    intro h0; subst h0; exact lt_irrefl 0 hz.1
  exact eq_of_associated_inQ1 (canon_inQ1 hz0) hz (canon_associated z).symm

private lemma giNorm_canon (z : GaussianInt) : giNorm (canon z) = giNorm z :=
  giNorm_eq_of_associated (canon_associated z).symm

/- ### Finite sets of Gaussian integers of norm `n` -/

private noncomputable def giOfNorm (n : ℕ) : Finset GaussianInt :=
  ((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).image fun p => (⟨p.1, p.2⟩ : GaussianInt)).filter
    fun z => giNorm z = n

private lemma mem_giOfNorm_iff {n : ℕ} {z : GaussianInt} :
    z ∈ giOfNorm n ↔ giNorm z = n := by
  simp only [giOfNorm, Finset.mem_filter, Finset.mem_image, Finset.mem_product, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro hn
    refine ⟨⟨(z.re, z.im), ⟨?_, ?_⟩, by ext <;> rfl⟩, hn⟩
    · have hle : z.re.natAbs ≤ n := by
        have hsq : z.re.natAbs ≤ z.re.natAbs ^ 2 := Nat.le_self_pow (by norm_num) _
        have := giNorm_eq z
        omega
      omega
    · have hle : z.im.natAbs ≤ n := by
        have hsq : z.im.natAbs ≤ z.im.natAbs ^ 2 := Nat.le_self_pow (by norm_num) _
        have := giNorm_eq z
        omega
      omega

private noncomputable def Q1Set (n : ℕ) : Finset GaussianInt :=
  (giOfNorm n).filter InQ1

private lemma mem_Q1Set_iff {n : ℕ} {z : GaussianInt} :
    z ∈ Q1Set n ↔ giNorm z = n ∧ InQ1 z := by
  simp [Q1Set, mem_giOfNorm_iff]


private def char6 (x y : ZMod 6) : GaussianInt :=
  if (x.val + y.val) % 2 = 0 ∨ (x.val % 3 = 0 ∧ y.val % 3 = 0) then 0
  else giI ^ (code x.val y.val + parityCode y.val).val

private def character (z : GaussianInt) : GaussianInt := char6 z.re z.im

private lemma char6_mul : ∀ a b c d : ZMod 6,
    char6 (a*c-b*d) (a*d+b*c) = char6 a b * char6 c d := by decide +kernel

private lemma character_mul (z w : GaussianInt) :
    character (z*w) = character z * character w := by
  simpa [character, sub_eq_add_neg, mul_comm]
    using char6_mul z.re z.im w.re w.im

private lemma character_one : character 1 = 1 := by decide
private lemma character_pow (z : GaussianInt) (k : ℕ) : character (z^k) = character z ^ k := by
  induction k with
  | zero => simp [character_one]
  | succ k ih => rw [pow_succ, character_mul, ih, ← pow_succ]

private lemma character_associated {a b : GaussianInt} (hab : Associated a b) :
    character a = character b := by
  obtain ⟨u,rfl⟩ := hab
  rw [character_mul]
  have hu := (mem_giUnits_iff _).mpr u.isUnit
  simp only [giUnits, Finset.mem_insert, Finset.mem_singleton] at hu
  have h : character (u : GaussianInt) = 1 := by
    rcases hu with h|h|h|h <;> rw [h] <;> decide
  simp [h]

private noncomputable def b (n : ℕ) : GaussianInt := ∑ z ∈ Q1Set n, character z

private lemma isCoprime_natCast {m n : ℕ} (hmn : Nat.Coprime m n) :
    IsCoprime (m : GaussianInt) (n : GaussianInt) := by
  have hbez := Nat.gcd_eq_gcd_ab m n
  rw [hmn.gcd_eq_one] at hbez
  refine ⟨(Nat.gcdA m n : GaussianInt), (Nat.gcdB m n : GaussianInt), ?_⟩
  have hcast : ((1 : ℤ) : GaussianInt) =
      ((m : ℤ) * Nat.gcdA m n + (n : ℤ) * Nat.gcdB m n : ℤ) := by
    exact_mod_cast hbez
  push_cast at hcast
  linear_combination -hcast

private lemma isCoprime_of_dvd {a b c d : GaussianInt}
    (h : IsCoprime a b) (hc : c ∣ a) (hd : d ∣ b) : IsCoprime c d := by
  rcases h with ⟨x, y, hxy⟩
  rcases hc with ⟨u, rfl⟩
  rcases hd with ⟨v, rfl⟩
  exact ⟨x * u, y * v, by linear_combination hxy⟩

private lemma isCoprime_of_coprime_giNorm {a b : GaussianInt}
    (h : Nat.Coprime (giNorm a) (giNorm b)) : IsCoprime a b := by
  have hmn : IsCoprime (giNorm a : GaussianInt) (giNorm b : GaussianInt) := isCoprime_natCast h
  have ha : a ∣ (giNorm a : GaussianInt) := ⟨star a, (gi_mul_star a).symm⟩
  have hb : b ∣ (giNorm b : GaussianInt) := ⟨star b, (gi_mul_star b).symm⟩
  exact isCoprime_of_dvd hmn ha hb

private lemma b_mul {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : Nat.Coprime m n) :
    b (m * n) = b m * b n := by
  simp only [b, Finset.sum_mul_sum]
  rw [← Finset.sum_product' ]
  symm
  refine Finset.sum_bij (fun (p : GaussianInt × GaussianInt) _ => canon (p.1 * p.2)) ?_ ?_ ?_ ?_
  · intro p hp
    rcases Finset.mem_product.mp hp with ⟨hu, hv⟩
    have hum := (mem_Q1Set_iff.mp hu).1
    have hvn := (mem_Q1Set_iff.mp hv).1
    have huv0 : p.1 * p.2 ≠ 0 := by
      intro h0
      have := giNorm_mul p.1 p.2
      rw [h0, (giNorm_eq_zero_iff 0).mpr rfl, hum, hvn] at this
      nlinarith
    exact mem_Q1Set_iff.mpr ⟨by rw [giNorm_canon, giNorm_mul, hum, hvn], canon_inQ1 huv0⟩
  · intro p₁ hp₁ p₂ hp₂ heq
    rcases Finset.mem_product.mp hp₁ with ⟨hu₁, hv₁⟩
    rcases Finset.mem_product.mp hp₂ with ⟨hu₂, hv₂⟩
    have hum₁ := (mem_Q1Set_iff.mp hu₁).1
    have hvn₁ := (mem_Q1Set_iff.mp hv₁).1
    have hum₂ := (mem_Q1Set_iff.mp hu₂).1
    have hvn₂ := (mem_Q1Set_iff.mp hv₂).1
    have hne₁ : p₁.1 * p₁.2 ≠ 0 := by
      intro h0
      have := giNorm_mul p₁.1 p₁.2
      rw [h0, (giNorm_eq_zero_iff 0).mpr rfl, hum₁, hvn₁] at this
      nlinarith
    have hne₂ : p₂.1 * p₂.2 ≠ 0 := by
      intro h0
      have := giNorm_mul p₂.1 p₂.2
      rw [h0, (giNorm_eq_zero_iff 0).mpr rfl, hum₂, hvn₂] at this
      nlinarith
    have hass : Associated (p₁.1 * p₁.2) (p₂.1 * p₂.2) :=
      (canon_eq_iff_associated hne₁ hne₂).mp heq
    have hdvd1 : p₁.1 ∣ p₂.1 * p₂.2 := (dvd_mul_right p₁.1 p₁.2).trans hass.dvd
    have hdvd2 : p₂.1 ∣ p₁.1 * p₁.2 := (dvd_mul_right p₂.1 p₂.2).trans hass.symm.dvd
    have hcop12 : IsCoprime p₁.1 p₂.2 := isCoprime_of_coprime_giNorm (by rwa [hum₁, hvn₂])
    have hcop21 : IsCoprime p₂.1 p₁.2 := isCoprime_of_coprime_giNorm (by rwa [hum₂, hvn₁])
    have hu_ass : Associated p₁.1 p₂.1 :=
      associated_of_dvd_dvd (hcop12.dvd_of_dvd_mul_right hdvd1) (hcop21.dvd_of_dvd_mul_right hdvd2)
    have hu_eq : p₁.1 = p₂.1 :=
      eq_of_associated_inQ1 (mem_Q1Set_iff.mp hu₁).2 (mem_Q1Set_iff.mp hu₂).2 hu_ass
    have hv_dvd1 : p₁.2 ∣ p₂.2 := by
      have h1 : p₁.2 ∣ p₂.1 * p₂.2 := (dvd_mul_left p₁.2 p₁.1).trans hass.dvd
      exact hcop21.symm.dvd_of_dvd_mul_left h1
    have hv_dvd2 : p₂.2 ∣ p₁.2 := by
      have h2 : p₂.2 ∣ p₁.1 * p₁.2 := (dvd_mul_left p₂.2 p₂.1).trans hass.symm.dvd
      exact hcop12.symm.dvd_of_dvd_mul_left h2
    have hv_eq : p₁.2 = p₂.2 :=
      eq_of_associated_inQ1 (mem_Q1Set_iff.mp hv₁).2 (mem_Q1Set_iff.mp hv₂).2
        (associated_of_dvd_dvd hv_dvd1 hv_dvd2)
    exact Prod.ext hu_eq hv_eq
  · intro w hw
    have hwn := (mem_Q1Set_iff.mp hw).1
    have hwq := (mem_Q1Set_iff.mp hw).2
    have hw0 : w ≠ 0 := by
      intro h0; rw [h0, (giNorm_eq_zero_iff 0).mpr rfl] at hwn; nlinarith
    have hw_dvd_mn : w ∣ (m : GaussianInt) * (n : GaussianInt) := by
      refine ⟨star w, ?_⟩
      rw [gi_mul_star, hwn, Nat.cast_mul]
    let g₁ : GaussianInt := EuclideanDomain.gcd w (m : GaussianInt)
    let g₂ : GaussianInt := EuclideanDomain.gcd w (n : GaussianInt)
    have hg1_w : g₁ ∣ w := EuclideanDomain.gcd_dvd_left w (m : GaussianInt)
    have hg1_m : g₁ ∣ (m : GaussianInt) := EuclideanDomain.gcd_dvd_right w (m : GaussianInt)
    have hg2_w : g₂ ∣ w := EuclideanDomain.gcd_dvd_left w (n : GaussianInt)
    have hg2_n : g₂ ∣ (n : GaussianInt) := EuclideanDomain.gcd_dvd_right w (n : GaussianInt)
    have hcop_g : IsCoprime g₁ g₂ :=
      isCoprime_of_dvd (isCoprime_natCast hmn) hg1_m hg2_n
    have hg12_dvd_w : g₁ * g₂ ∣ w := hcop_g.mul_dvd hg1_w hg2_w
    have hw_dvd_g12 : w ∣ g₁ * g₂ := by
      have h1 := EuclideanDomain.gcd_eq_gcd_ab w (m : GaussianInt)
      have h2 := EuclideanDomain.gcd_eq_gcd_ab w (n : GaussianInt)
      have hexp : g₁ * g₂ =
          w * (w * EuclideanDomain.gcdA w m * EuclideanDomain.gcdA w n +
               (m : GaussianInt) * EuclideanDomain.gcdB w m * EuclideanDomain.gcdA w n +
               (n : GaussianInt) * EuclideanDomain.gcdB w n * EuclideanDomain.gcdA w m) +
          ((m : GaussianInt) * (n : GaussianInt)) *
            (EuclideanDomain.gcdB w m * EuclideanDomain.gcdB w n) := by
        change EuclideanDomain.gcd w m * EuclideanDomain.gcd w n = _
        rw [h1, h2]
        ring
      rw [hexp]
      exact dvd_add (dvd_mul_right w _) (dvd_mul_of_dvd_left hw_dvd_mn _)
    have hass_w : Associated (g₁ * g₂) w := associated_of_dvd_dvd hg12_dvd_w hw_dvd_g12
    have hprod_norm : giNorm g₁ * giNorm g₂ = m * n := by
      rw [← giNorm_mul, giNorm_eq_of_associated hass_w, hwn]
    have hg1_dvd_m2 : giNorm g₁ ∣ m ^ 2 := by
      simpa [giNorm_natCast] using giNorm_dvd_of_dvd hg1_m
    have hg2_dvd_n2 : giNorm g₂ ∣ n ^ 2 := by
      simpa [giNorm_natCast] using giNorm_dvd_of_dvd hg2_n
    have hcop_g1_n : Nat.Coprime (giNorm g₁) n :=
      ((hmn.pow_left 2).coprime_dvd_left hg1_dvd_m2)
    have hcop_g2_m : Nat.Coprime (giNorm g₂) m :=
      ((hmn.symm.pow_left 2).coprime_dvd_left hg2_dvd_n2)
    have hg1_eq : giNorm g₁ = m := by
      have hd1 : giNorm g₁ ∣ m := hcop_g1_n.dvd_of_dvd_mul_right ⟨giNorm g₂, hprod_norm.symm⟩
      have hd2 : m ∣ giNorm g₁ := hcop_g2_m.symm.dvd_of_dvd_mul_right ⟨n, by linarith⟩
      exact Nat.dvd_antisymm hd1 hd2
    have hg2_eq : giNorm g₂ = n := by
      rw [hg1_eq] at hprod_norm
      exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < m) hprod_norm
    have hg1_ne : g₁ ≠ 0 := by
      intro h0; rw [h0, (giNorm_eq_zero_iff 0).mpr rfl] at hg1_eq; omega
    have hg2_ne : g₂ ≠ 0 := by
      intro h0; rw [h0, (giNorm_eq_zero_iff 0).mpr rfl] at hg2_eq; omega
    refine ⟨(canon g₁, canon g₂), Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · exact mem_Q1Set_iff.mpr ⟨by rw [giNorm_canon, hg1_eq], canon_inQ1 hg1_ne⟩
    · exact mem_Q1Set_iff.mpr ⟨by rw [giNorm_canon, hg2_eq], canon_inQ1 hg2_ne⟩
    · have hc_ass : Associated (canon g₁ * canon g₂) w :=
        ((canon_associated g₁).symm.mul_mul (canon_associated g₂).symm).trans hass_w
      have hc_ne : canon g₁ * canon g₂ ≠ 0 := by
        intro h0
        have := giNorm_eq_of_associated hc_ass
        rw [h0, (giNorm_eq_zero_iff 0).mpr rfl, hwn] at this
        nlinarith
      rw [← canon_eq_self hwq]
      exact (canon_eq_iff_associated hc_ne hw0).mpr hc_ass


  · intro p _
    rw [← character_associated (canon_associated _), character_mul]


private lemma int_giNorm (z : GaussianInt) : (giNorm z : ℤ) = z.norm := by
  simp [giNorm, abs_of_nonneg (GaussianInt.norm_nonneg z)]

private lemma norm_mod_six {z : GaussianInt} {n : ℕ} (h : z.norm = (12*n+1 : ℕ)) :
    (z.re : ZMod 6)^2 + (z.im : ZMod 6)^2 = 1 := by
  rw [gaussian_norm] at h
  have hc := congrArg (fun k : ℤ => (k : ZMod 6)) h
  push_cast at hc
  simpa only [show (12 : ZMod 6) = 0 by decide, zero_mul, zero_add] using hc

private lemma character_primary {z : GaussianInt} {n : ℕ} (hz : z ∈ primaryPoints (12*n+1)) :
    character z = ((z.im.negOnePow : ℤ) : GaussianInt) := by
  obtain ⟨hn,hx,hy⟩ := mem_primary.mp hz
  have h6 : ∀ x y : ZMod 6, x^2+y^2=1 → x.val % 3 = 1 → y.val % 3 = 0 →
      char6 x y = if y.val % 2 = 0 then 1 else -1 := by decide +kernel
  have hx6 := ZMod.val_intCast (n := 6) z.re
  have hy6 := ZMod.val_intCast (n := 6) z.im
  change (((z.re : ZMod 6).val : ℕ) : ℤ) = z.re % 6 at hx6
  change (((z.im : ZMod 6).val : ℕ) : ℤ) = z.im % 6 at hy6
  rw [character, h6 _ _ (norm_mod_six hn) (by omega) (by omega)]
  split_ifs with he
  · rw [Int.negOnePow_even z.im (Int.even_iff.mpr (by omega))]
    simp
  · rw [Int.negOnePow_odd z.im (Int.odd_iff.mpr (by omega))]
    simp

private lemma primary_unique {a b : GaussianInt} {m : ℕ} (ha : a ∈ primaryPoints m)
    (hb : b ∈ primaryPoints m) (hab : Associated a b) : a = b := by
  obtain ⟨-,ha1,ha2⟩ := mem_primary.mp ha
  obtain ⟨-,hb1,hb2⟩ := mem_primary.mp hb
  obtain ⟨u,rfl⟩ := hab
  have h := (mem_giUnits_iff _).mpr u.isUnit
  simp only [giUnits, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h|h|h|h <;> rw [h] at hb1 hb2 ⊢ <;> simp [giI] at hb1 hb2 ⊢ <;> omega

private lemma primary_exists {z : GaussianInt} {n : ℕ} (hz : giNorm z = 12*n+1) :
    ∃ w ∈ primaryPoints (12*n+1), Associated z w := by
  have hn : z.norm = (12*n+1 : ℕ) := by rw [← int_giNorm, hz]
  have h6 : ∀ x y : ZMod 6, x^2+y^2=1 →
      (x.val % 3 = 1 ∧ y.val % 3 = 0) ∨ (x.val % 3 = 2 ∧ y.val % 3 = 0) ∨
      (x.val % 3 = 0 ∧ y.val % 3 = 1) ∨ (x.val % 3 = 0 ∧ y.val % 3 = 2) := by decide +kernel
  have ho := h6 _ _ (norm_mod_six hn)
  have hx := ZMod.val_intCast (n := 6) z.re
  have hy := ZMod.val_intCast (n := 6) z.im
  change (((z.re : ZMod 6).val : ℕ) : ℤ) = z.re % 6 at hx
  change (((z.im : ZMod 6).val : ℕ) : ℤ) = z.im % 6 at hy
  have aux (u : GaussianInt) (hu : u ∈ giUnits) (h : (z*u).re % 3 = 1 ∧ (z*u).im % 3 = 0) :
      ∃ w ∈ primaryPoints (12*n+1), Associated z w := by
    obtain ⟨v, rfl⟩ := (mem_giUnits_iff _).mp hu
    have hass : Associated z (z * ↑v) := ⟨v,rfl⟩
    exact ⟨_, mem_primary.mpr ⟨by rw [← int_giNorm, ← giNorm_eq_of_associated hass, hz],h⟩,hass⟩
  rcases ho with h|h|h|h
  · apply aux 1 (by decide); simp; omega
  · apply aux (-1) (by decide); simp; omega
  · apply aux (-giI) (by decide); simp [giI]; omega
  · apply aux giI (by decide); simp [giI]; omega

theorem coefficient_character (n : ℕ) : (OMA.S_oeis_a002107.a n : GaussianInt) = b (12*n+1) := by
  rw [coefficient_primary, Int.cast_sum]
  refine Finset.sum_bij (fun z _ => canon z) ?_ ?_ ?_ ?_
  · intro z hz
    have h := (mem_primary.mp hz).1
    rw [← int_giNorm] at h
    have hn : giNorm z = 12*n+1 := by exact_mod_cast h
    refine mem_Q1Set_iff.mpr ⟨(giNorm_canon z).trans hn,canon_inQ1 ?_⟩
    intro he; rw [he, (giNorm_eq_zero_iff 0).mpr rfl] at hn; omega
  · intro a ha b hb hab
    exact primary_unique ha hb ((canon_associated a).trans (hab ▸ (canon_associated b).symm))
  · intro z hz
    obtain ⟨hn,hq⟩ := mem_Q1Set_iff.mp hz
    obtain ⟨w,hw,hass⟩ := primary_exists hn
    exact ⟨w,hw,eq_of_associated_inQ1
      (canon_inQ1 (fun h => by have := (mem_primary.mp hw).2.1; simp [h] at this))
      hq ((canon_associated w).symm.trans hass.symm)⟩
  · intro z hz
    exact (character_primary hz).symm.trans (character_associated (canon_associated z))

private lemma gi_prime_of_norm_prime {π : GaussianInt} {p : ℕ} (hp : p.Prime)
    (hπ : giNorm π = p) : Prime π := by
  have hπ0 : π ≠ 0 := by
    intro h0; rw [h0, (giNorm_eq_zero_iff 0).mpr rfl] at hπ; exact hp.ne_zero hπ.symm
  have hnu : ¬ IsUnit π := by
    rw [← giNorm_eq_one_iff, hπ]; exact hp.ne_one
  refine ⟨hπ0, hnu, fun x y hxy => ?_⟩
  by_cases hx : π ∣ x
  · exact Or.inl hx
  · right
    let g := EuclideanDomain.gcd π x
    have hgπ : g ∣ π := EuclideanDomain.gcd_dvd_left π x
    have hgx : g ∣ x := EuclideanDomain.gcd_dvd_right π x
    have hgdvd : giNorm g ∣ p := by rw [← hπ]; exact giNorm_dvd_of_dvd hgπ
    rcases hp.eq_one_or_self_of_dvd _ hgdvd with hg1 | hgp
    · rcases (giNorm_eq_one_iff g).mp hg1 with ⟨u, hu⟩
      have hab := EuclideanDomain.gcd_eq_gcd_ab π x
      change g = π * EuclideanDomain.gcdA π x + x * EuclideanDomain.gcdB π x at hab
      have hy : y = π * (EuclideanDomain.gcdA π x * (u⁻¹ : GaussianIntˣ) * y) +
          (x * y) * (EuclideanDomain.gcdB π x * (u⁻¹ : GaussianIntˣ)) := by
        have h1 : (1 : GaussianInt) =
            π * (EuclideanDomain.gcdA π x * (u⁻¹ : GaussianIntˣ)) +
            x * (EuclideanDomain.gcdB π x * (u⁻¹ : GaussianIntˣ)) := by
          calc
            (1 : GaussianInt) = (u : GaussianInt) * (u⁻¹ : GaussianIntˣ) := by simp
            _ = g * (u⁻¹ : GaussianIntˣ) := by rw [hu]
            _ = (π * EuclideanDomain.gcdA π x + x * EuclideanDomain.gcdB π x) *
                  (u⁻¹ : GaussianIntˣ) := by rw [hab]
            _ = _ := by ring
        calc
          y = 1 * y := (one_mul y).symm
          _ = (π * (EuclideanDomain.gcdA π x * (u⁻¹ : GaussianIntˣ)) +
                x * (EuclideanDomain.gcdB π x * (u⁻¹ : GaussianIntˣ))) * y := by rw [← h1]
          _ = _ := by ring
      rw [hy]
      exact dvd_add (dvd_mul_right π _) (dvd_mul_of_dvd_left hxy _)
    · exfalso
      rcases hgπ with ⟨c, hc⟩
      have hc1 : giNorm c = 1 := by
        have hmul := giNorm_mul g c
        rw [← hc, hπ, hgp] at hmul
        exact Nat.eq_of_mul_eq_mul_left hp.pos (by linarith)
      rcases (giNorm_eq_one_iff c).mp hc1 with ⟨u, hu⟩
      have hπg : π ∣ g := ⟨(u⁻¹ : GaussianIntˣ), by rw [hc, ← hu]; simp⟩
      exact hx (hπg.trans hgx)

private lemma card_Q1Set_mod4_three {p : ℕ} (hp : p.Prime) (hp3 : p % 4 = 3) (k : ℕ) :
    ((Q1Set (p ^ k)).card : ℤ) = if Even k then 1 else 0 := by
  have hdvd_both : ∀ z : GaussianInt, p ∣ giNorm z → (p : GaussianInt) ∣ z := by
    intro z hz
    have hmod : ((z.re : ZMod p) ^ 2 + (z.im : ZMod p) ^ 2) = 0 := by
      have h2 : (p : ℤ) ∣ z.re ^ 2 + z.im ^ 2 := by
        have : (z.re.natAbs ^ 2 + z.im.natAbs ^ 2 : ℤ) = z.re ^ 2 + z.im ^ 2 := by
          simp
        rw [← this]
        rw [giNorm_eq] at hz
        exact_mod_cast hz
      rcases h2 with ⟨c, hc⟩
      have hcast : (((z.re ^ 2 + z.im ^ 2 : ℤ) : ZMod p)) = ((p : ℤ) * c : ℤ) := by
        rw [hc]
      push_cast at hcast
      simpa using hcast
    have : Fact p.Prime := ⟨hp⟩
    have hre0 : (z.re : ZMod p) = 0 := by
      by_contra hne
      have hsq : IsSquare (-1 : ZMod p) := by
        refine ⟨(z.im : ZMod p) * (z.re : ZMod p)⁻¹, ?_⟩
        have h1 : (z.im : ZMod p) ^ 2 = -(z.re : ZMod p) ^ 2 := eq_neg_of_add_eq_zero_right hmod
        calc
          (-1 : ZMod p) = -((z.re : ZMod p) ^ 2 * ((z.re : ZMod p)⁻¹) ^ 2) := by
            rw [← mul_pow, mul_inv_cancel₀ hne, one_pow]
          _ = (-(z.re : ZMod p) ^ 2) * ((z.re : ZMod p)⁻¹) ^ 2 := by ring
          _ = (z.im : ZMod p) ^ 2 * ((z.re : ZMod p)⁻¹) ^ 2 := by rw [← h1]
          _ = ((z.im : ZMod p) * (z.re : ZMod p)⁻¹) * ((z.im : ZMod p) * (z.re : ZMod p)⁻¹) := by
            ring
      have hne3 : p % 4 ≠ 3 := ZMod.exists_sq_eq_neg_one_iff.mp hsq
      exact hne3 hp3
    have him0 : (z.im : ZMod p) = 0 := by
      rw [hre0, zero_pow (by norm_num), zero_add] at hmod
      exact eq_zero_of_pow_eq_zero hmod
    have hdre : (p : ℤ) ∣ z.re := (ZMod.intCast_zmod_eq_zero_iff_dvd z.re p).mp hre0
    have hdim : (p : ℤ) ∣ z.im := (ZMod.intCast_zmod_eq_zero_iff_dvd z.im p).mp him0
    rcases hdre with ⟨a, ha⟩
    rcases hdim with ⟨b, hb⟩
    refine ⟨⟨a, b⟩, ?_⟩
    ext <;> simp [ha, hb]
  have hstep : ∀ m : ℕ, (Q1Set (p ^ (m + 2))).card = (Q1Set (p ^ m)).card := by
    intro m
    symm
    refine Finset.card_bij (fun w _ => (p : GaussianInt) * w) ?_ ?_ ?_
    · intro w hw
      rcases mem_Q1Set_iff.mp hw with ⟨hwn, hre, him⟩
      refine mem_Q1Set_iff.mpr ⟨?_, ?_, ?_⟩
      · rw [giNorm_mul, giNorm_natCast, hwn]; ring
      · simp
        have hp_pos : (0 : ℤ) < p := by exact_mod_cast hp.pos
        nlinarith
      · simp
        have hp_pos : (0 : ℤ) < p := by exact_mod_cast hp.pos
        nlinarith
    · intro w₁ _ w₂ _ heq
      have hp0 : (p : GaussianInt) ≠ 0 := by exact_mod_cast hp.ne_zero
      exact mul_left_cancel₀ hp0 heq
    · intro z hz
      rcases mem_Q1Set_iff.mp hz with ⟨hzn, hre, him⟩
      have hpdvd : p ∣ giNorm z := by
        rw [hzn, pow_add]; exact dvd_mul_of_dvd_right (dvd_pow_self p (by norm_num)) _
      rcases hdvd_both z hpdvd with ⟨w, hw⟩
      refine ⟨w, mem_Q1Set_iff.mpr ⟨?_, ?_, ?_⟩, hw.symm⟩
      · have hmul := giNorm_mul (p : GaussianInt) w
        rw [← hw, hzn, giNorm_natCast, pow_add] at hmul
        have hp2_pos : 0 < p ^ 2 := pow_pos hp.pos 2
        exact Nat.eq_of_mul_eq_mul_left hp2_pos (by linarith)
      · have hre' : z.re = (p : ℤ) * w.re := by rw [hw]; simp
        have hp_pos : (0 : ℤ) < p := by exact_mod_cast hp.pos
        nlinarith
      · have him' : z.im = (p : ℤ) * w.im := by rw [hw]; simp
        have hp_pos : (0 : ℤ) < p := by exact_mod_cast hp.pos
        nlinarith
  have hbase0 : (Q1Set 1).card = 1 := by
    have hset : Q1Set 1 = {1} := by
      ext z
      simp only [mem_Q1Set_iff, Finset.mem_singleton]
      constructor
      · rintro ⟨hz1, hzq⟩
        have hass : Associated z 1 := by
          rcases (giNorm_eq_one_iff z).mp hz1 with ⟨u, hu⟩
          exact ⟨u⁻¹, by rw [← hu]; simp⟩
        exact eq_of_associated_inQ1 hzq ⟨by decide, by decide⟩ hass
      · rintro rfl
        exact ⟨by decide, ⟨by decide, by decide⟩⟩
    rw [hset, Finset.card_singleton]
  have hbase1 : (Q1Set p).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro z hz
    have hzn : giNorm z = p := (mem_Q1Set_iff.mp hz).1
    rcases hdvd_both z (by rw [hzn]) with ⟨w, hw⟩
    have hmul := giNorm_mul (p : GaussianInt) w
    rw [← hw, hzn, giNorm_natCast] at hmul
    have hp2 : p ^ 2 ≤ p := by
      have hw1 : 1 ≤ giNorm w := by
        by_contra h0
        have hw0 : giNorm w = 0 := by omega
        rw [hw0, mul_zero] at hmul
        exact hp.ne_zero hmul
      nlinarith [hp.two_le]
    nlinarith [hp.two_le]
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp [hbase0]
    | 1 => simp [hbase1]
    | m + 2 =>
      rw [hstep m, ih m (by omega)]
      have hev : Even (m + 2) ↔ Even m := by
        constructor
        · rintro ⟨r, hr⟩; exact ⟨r - 1, by omega⟩
        · rintro ⟨r, hr⟩; exact ⟨r + 1, by omega⟩
      simp [hev]

private lemma b_split {p : ℕ} (hp : p.Prime) (hp1 : p % 4 = 1) (k : ℕ) :
    ∃ π : GaussianInt, giNorm π = p ∧ b (p ^ k) =
      ∑ j ∈ Finset.range (k+1), character π ^ j * character (star π) ^ (k-j) := by
  have : Fact p.Prime := ⟨hp⟩
  rcases Nat.Prime.sq_add_sq (p := p) (by omega : p % 4 ≠ 3) with ⟨a, b, hab⟩
  let π : GaussianInt := ⟨(a : ℤ), (b : ℤ)⟩
  let π' : GaussianInt := star π
  have hπ_norm : giNorm π = p := by
    simp only [giNorm_eq, π, Int.natAbs_natCast]
    exact hab
  have hπ'_norm : giNorm π' = p := by rw [giNorm_star, hπ_norm]
  have hπ_prime : Prime π := gi_prime_of_norm_prime hp hπ_norm
  have hπ'_prime : Prime π' := gi_prime_of_norm_prime hp hπ'_norm
  have hmul_p : π * π' = (p : GaussianInt) := by
    simpa [π', hπ_norm] using gi_mul_star π
  have hnot_ass : ¬ Associated π π' := by
    intro hass
    have ha_ne0 : a ≠ 0 := by
      intro h0; subst h0
      have hb2 : b ^ 2 = p := by simpa using hab
      have hb_pos : 0 < b := by nlinarith [hp.two_le]
      rcases (by omega : b = 1 ∨ 2 ≤ b) with rfl | hb2'
      · nlinarith [hp.two_le]
      · have hdvd : b ∣ p := ⟨b, by linarith⟩
        rcases hp.eq_one_or_self_of_dvd b hdvd with h1 | hbp
        · omega
        · nlinarith
    have hb_ne0 : b ≠ 0 := by
      intro h0; subst h0
      have ha2 : a ^ 2 = p := by simpa using hab
      have ha_pos : 0 < a := by nlinarith [hp.two_le]
      rcases (by omega : a = 1 ∨ 2 ≤ a) with rfl | ha2'
      · nlinarith [hp.two_le]
      · have hdvd : a ∣ p := ⟨a, by linarith⟩
        rcases hp.eq_one_or_self_of_dvd a hdvd with h1 | hap
        · omega
        · nlinarith
    have hab_ne : a ≠ b := by
      intro heq; subst heq
      have h2 : 2 ∣ p := ⟨a ^ 2, by linarith⟩
      rcases hp.eq_one_or_self_of_dvd 2 h2 with h1 | h2p
      · omega
      · omega
    rcases hass with ⟨u, hu⟩
    have hmem := (mem_giUnits_iff u).mpr u.isUnit
    simp only [giUnits, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h1 | h1 | h1
    · rw [h1, mul_one] at hu
      have := congr_arg Zsqrtd.im hu
      simp [π, π'] at this; omega
    · rw [h1] at hu
      have := congr_arg Zsqrtd.re hu
      simp [π, π'] at this; omega
    · rw [h1] at hu
      have := congr_arg Zsqrtd.re hu
      simp [π, π', giI] at this; omega
    · rw [h1] at hu
      have := congr_arg Zsqrtd.re hu
      simp [π, π', giI] at this; omega
  have hall : ∀ m : ℕ, ∀ z : GaussianInt, giNorm z = p ^ m →
      ∃ j ≤ m, Associated z (π ^ j * π' ^ (m - j)) := by
    intro m
    induction m with
    | zero =>
      intro z hz
      rw [pow_zero, giNorm_eq_one_iff] at hz
      rcases hz with ⟨u, hu⟩
      exact ⟨0, le_refl 0, ⟨u⁻¹, by simp [← hu]⟩⟩
    | succ m ih =>
      intro z hz
      have hprod : z * star z = (p ^ (m + 1) : GaussianInt) := by
        simpa [hz] using gi_mul_star z
      have hπ_dvd_prod : π ∣ z * star z := by
        refine ⟨π' * (p : GaussianInt) ^ m, ?_⟩
        calc
          z * star z = (p : GaussianInt) * (p : GaussianInt) ^ m := by
            rw [hprod, pow_succ']
          _ = (π * π') * (p : GaussianInt) ^ m := by rw [hmul_p]
          _ = π * (π' * (p : GaussianInt) ^ m) := by ring
      rcases hπ_prime.dvd_or_dvd hπ_dvd_prod with hπz | hπsz
      · rcases hπz with ⟨w, hw⟩
        have hwn : giNorm w = p ^ m := by
          have hmul := giNorm_mul π w
          rw [← hw, hz, hπ_norm, pow_succ'] at hmul
          exact Nat.eq_of_mul_eq_mul_left hp.pos hmul.symm
        rcases ih w hwn with ⟨j, hjm, hass⟩
        refine ⟨j + 1, by omega, ?_⟩
        have hsub : m + 1 - (j + 1) = m - j := by omega
        rw [hsub, hw, pow_succ', mul_assoc]
        exact (Associated.refl π).mul_mul hass
      · rcases hπsz with ⟨w, hw⟩
        have hπ'z : z = π' * star w := by
          have := congr_arg star hw
          simpa [π', star_mul, mul_comm] using this
        have hwn : giNorm (star w) = p ^ m := by
          have hmul := giNorm_mul π' (star w)
          rw [← hπ'z, hz, hπ'_norm, pow_succ'] at hmul
          exact Nat.eq_of_mul_eq_mul_left hp.pos hmul.symm
        rcases ih (star w) hwn with ⟨j, hjm, hass⟩
        refine ⟨j, by omega, ?_⟩
        have hsub : m + 1 - j = (m - j) + 1 := by omega
        rw [hsub, hπ'z, pow_succ', mul_left_comm]
        exact (Associated.refl π').mul_mul hass
  refine ⟨π, hπ_norm, ?_⟩
  unfold Wave9Q.EulerSquare.b
  symm
  refine Finset.sum_bij (fun j _ => canon (π ^ j * π' ^ (k - j))) ?_ ?_ ?_ ?_
  · intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hnorm : giNorm (π ^ j * π' ^ (k - j)) = p ^ k := by
      rw [giNorm_mul, giNorm_pow, giNorm_pow, hπ_norm, hπ'_norm, ← pow_add,
        Nat.add_sub_of_le hjk]
    have hne : π ^ j * π' ^ (k - j) ≠ 0 := by
      intro h0
      rw [h0, (giNorm_eq_zero_iff 0).mpr rfl] at hnorm
      exact pow_ne_zero k hp.ne_zero hnorm.symm
    exact mem_Q1Set_iff.mpr ⟨by rw [giNorm_canon, hnorm], canon_inQ1 hne⟩
  · intro j₁ hj₁ j₂ hj₂ heq
    have hjk₁ : j₁ ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj₁)
    have hjk₂ : j₂ ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj₂)
    have hne₁ : π ^ j₁ * π' ^ (k - j₁) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hπ_prime.ne_zero) (pow_ne_zero _ hπ'_prime.ne_zero)
    have hne₂ : π ^ j₂ * π' ^ (k - j₂) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hπ_prime.ne_zero) (pow_ne_zero _ hπ'_prime.ne_zero)
    have hass := (canon_eq_iff_associated hne₁ hne₂).mp heq
    by_contra hne
    have hcontra : ∀ a b : ℕ, a < b → b ≤ k →
        Associated (π ^ a * π' ^ (k - a)) (π ^ b * π' ^ (k - b)) → False := by
      intro a b hab hbk hba
      have hba_dvd : π ^ b * π' ^ (k - b) ∣ π ^ a * π' ^ (k - a) := hba.symm.dvd
      have hre1 : π ^ b * π' ^ (k - b) = (π ^ a * π' ^ (k - b)) * π ^ (b - a) := by
        rw [mul_right_comm, ← pow_add, Nat.add_sub_of_le (le_of_lt hab)]
      have hre2 : π ^ a * π' ^ (k - a) = (π ^ a * π' ^ (k - b)) * π' ^ (b - a) := by
        rw [mul_assoc, ← pow_add, show (k - b) + (b - a) = k - a by omega]
      rw [hre1, hre2] at hba_dvd
      have hc0 : π ^ a * π' ^ (k - b) ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ hπ_prime.ne_zero) (pow_ne_zero _ hπ'_prime.ne_zero)
      have hpow_dvd : π ^ (b - a) ∣ π' ^ (b - a) := (mul_dvd_mul_iff_left hc0).mp hba_dvd
      have hπ_dvd_pow : π ∣ π' ^ (b - a) :=
        (dvd_pow_self π (by omega : b - a ≠ 0)).trans hpow_dvd
      have hπ_dvd_π' : π ∣ π' := hπ_prime.dvd_of_dvd_pow hπ_dvd_pow
      rcases hπ_dvd_π' with ⟨c, hc⟩
      have hc1 : giNorm c = 1 := by
        have hmul := giNorm_mul π c
        rw [← hc, hπ'_norm, hπ_norm] at hmul
        exact Nat.eq_of_mul_eq_mul_left hp.pos (by linarith)
      rcases (giNorm_eq_one_iff c).mp hc1 with ⟨u, hu⟩
      exact hnot_ass ⟨u, by rw [hu, ← hc]⟩
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hcontra j₁ j₂ hlt hjk₂ hass
    · exact hcontra j₂ j₁ hgt hjk₁ hass.symm
  · intro z hz
    rcases mem_Q1Set_iff.mp hz with ⟨hzn, hzq⟩
    have hz0 : z ≠ 0 := by
      intro h0; rw [h0, (giNorm_eq_zero_iff 0).mpr rfl] at hzn
      exact pow_ne_zero k hp.ne_zero hzn.symm
    rcases hall k z hzn with ⟨j, hjk, hass⟩
    refine ⟨j, Finset.mem_range.mpr (by omega), ?_⟩
    have hne : π ^ j * π' ^ (k - j) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hπ_prime.ne_zero) (pow_ne_zero _ hπ'_prime.ne_zero)
    rw [← canon_eq_self hzq]
    exact (canon_eq_iff_associated hne hz0).mpr hass.symm

  · intro j _
    rw [← character_associated (canon_associated _), character_mul, character_pow, character_pow]


noncomputable def f (n : ℕ) : ℝ := Real.sqrt (giNorm (b n))

theorem f_mul {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (h : m.Coprime n) :
    f (m*n) = f m * f n := by simp [f, b_mul hm hn h, giNorm_mul, Real.sqrt_mul]

theorem f_coefficient (n : ℕ) : f (12*n+1) = |(OMA.S_oeis_a002107.a n : ℝ)| := by
  simp [f, ← coefficient_character, giNorm_eq, Real.sqrt_sq_eq_abs]

private lemma norm_residue {p : ℕ} {z : GaussianInt} (hp : giNorm z = p) :
    (z.re : ZMod 6)^2 + (z.im : ZMod 6)^2 = (p : ZMod 6) := by
  have hi : z.re^2 + z.im^2 = (p : ℤ) := by rw [← gaussian_norm, ← int_giNorm,hp]
  exact_mod_cast congrArg (fun k : ℤ => (k : ZMod 6)) hi

private lemma char_star (z : GaussianInt) : character (star z) = char6 z.re (-(z.im : ZMod 6)) := by
  simp [character]

private lemma b_equal_factors (t : GaussianInt) (k : ℕ) :
    (∑ j ∈ Finset.range (k+1), t^j * t^(k-j)) = (k+1 : ℕ) * t^k := by
  calc
    _ = ∑ _j ∈ Finset.range (k+1), t^k := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
    _ = _ := by simp [nsmul_eq_mul]

private lemma b_opposite_factors (t : GaussianInt) (k : ℕ) :
    (∑ j ∈ Finset.range (k+1), (-t)^j * t^(k-j)) = if Even k then t^k else 0 := by
  calc
    _ = ∑ j ∈ Finset.range (k+1), (-1)^j * t^k := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [← neg_one_mul t, mul_pow, mul_assoc, ← pow_add,
        Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
    _ = _ := by rw [← Finset.sum_mul, neg_one_geom_sum]; split_ifs <;> simp_all [Nat.even_add_one]

theorem f_split {p : ℕ} (hp : p.Prime) (h1 : p % 4 = 1) (k : ℕ) :
    f (p^k) = if p % 12 = 1 then (k+1 : ℕ) else if Even k then 1 else 0 := by
  obtain ⟨π,hπ,hb⟩ := b_split hp h1 k
  have hmod := norm_residue hπ
  have h3 : ¬ 3 ∣ p := by
    intro hd
    rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega
  have hcast : (p : ZMod 6) = (p % 6 : ℕ) := by simp
  unfold f
  rw [hb]
  by_cases h : p % 12 = 1
  · rw [if_pos h]
    rw [hcast, show p%6=1 by omega] at hmod
    have aux : ∀ x y : ZMod 6, x^2+y^2=1 →
        char6 x y = char6 x (-y) ∧ giNorm (char6 x (-y)) = 1 := by decide +kernel
    obtain ⟨he,hu⟩ := aux _ _ hmod
    rw [char_star, show character π = _ from he, b_equal_factors, giNorm_mul,
      giNorm_natCast,giNorm_pow,hu]
    simp [Real.sqrt_sq (show (0:ℝ) ≤ k+1 by positivity)]
  · rw [if_neg h]
    have hp12 : p%12=5 := by
      have hrem : p%12%4=1 := by simpa using h1
      have hrem3 : p%12%3 ≠ 0 := by simpa using (show p % 3 ≠ 0 by omega)
      have hlt := Nat.mod_lt p (by decide : 0 < 12)
      interval_cases hm : p%12 <;> omega
    rw [hcast, show p%6=5 by omega] at hmod
    have aux : ∀ x y : ZMod 6, x^2+y^2=5 →
        char6 x y = -char6 x (-y) ∧ giNorm (char6 x (-y)) = 1 := by decide +kernel
    obtain ⟨he,hu⟩ := aux _ _ hmod
    rw [char_star, show character π = _ from he, b_opposite_factors]
    split_ifs
    · simp [giNorm_pow, hu]
    · simp [giNorm]


theorem f_one : f 1 = 1 := by simpa [OMA.S_oeis_a002107.a] using f_coefficient 0

theorem f_bad {m : ℕ} (h : 2 ∣ m ∨ 3 ∣ m) : f m = 0 := by
  have hb : b m = 0 := by
    refine Finset.sum_eq_zero fun z hz => ?_
    have hm := norm_residue (mem_Q1Set_iff.mp hz).1
    have aux : ∀ x y : ZMod 6, (x^2+y^2).val % 2 = 0 ∨ (x^2+y^2).val % 3 = 0 →
        char6 x y = 0 := by decide +kernel
    apply aux
    rw [hm,ZMod.val_natCast]
    omega
  simp [f,hb,giNorm]

theorem f_inert {p : ℕ} (hp : p.Prime) (h4 : p%4=3) (h3 : p ≠ 3) (k : ℕ) :
    f (p^k) = if Even k then 1 else 0 := by
  have hc := card_Q1Set_mod4_three hp h4 k
  split_ifs with he
  · obtain ⟨j,rfl⟩ := he
    have he : Even (j+j) := ⟨_,rfl⟩
    rw [if_pos he] at hc
    have hz : (p^j : GaussianInt) ∈ Q1Set (p^(j+j)) := by
      refine mem_Q1Set_iff.mpr ⟨?_, ?_⟩
      · rw [giNorm_pow,giNorm_natCast,← pow_mul]; congr 1; omega
      · rw [← Nat.cast_pow]
        change 0 < ((p^j : ℕ) : ℤ) ∧ (0 : ℤ) ≤ 0
        exact ⟨by exact_mod_cast pow_pos hp.pos j, le_rfl⟩
    obtain ⟨w,hw⟩ := Finset.card_eq_one.mp (show (Q1Set (p^(j+j))).card = 1 by exact_mod_cast hc)
    rw [hw,Finset.mem_singleton] at hz
    rw [← hz] at hw
    have hp6 : p%6=1 ∨ p%6=5 := by
      have hnd : ¬ 3 ∣ p := fun h => h3 ((hp.eq_one_or_self_of_dvd 3 h).resolve_left (by decide)).symm
      have hlt := Nat.mod_lt p (by decide : 0<6)
      have h2 : p%6%2=1 := by rw [Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 6)]; omega
      have h3 : p%6%3≠0 := by rw [Nat.mod_mod_of_dvd _ (by decide : 3 ∣ 6)]; omega
      interval_cases hm : p%6 <;> omega
    have hch : character (p : GaussianInt) = 1 := by
      change char6 ((p : ℤ) : ZMod 6) 0 = 1
      rw [Int.cast_natCast, ← ZMod.natCast_mod p 6]
      rcases hp6 with h|h <;> rw [h] <;> decide
    simp [f,b,hw,character_pow,hch,giNorm]
  · rw [if_neg he] at hc
    have h0 : (Q1Set (p^k)).card = 0 := by exact_mod_cast hc
    simp [f,b,Finset.card_eq_zero.mp h0,giNorm]


theorem f_prime_pow {p e : ℕ} (hp : p.Prime) (he : 0 < e) :
    f (p^e) = if p=2 ∨ p=3 then 0 else if p%12=1 then (e+1 : ℕ)
      else if Even e then 1 else 0 := by
  split_ifs with hb h12 hEven
  · rcases hb with rfl|rfl
    · simpa using f_bad (.inl (dvd_pow_self 2 he.ne'))
    · simpa using f_bad (.inr (dvd_pow_self 3 he.ne'))
  · simp [f_split hp (show p%4=1 by omega) e, h12]
  all_goals
    have hodd := hp.odd_of_ne_two (show p ≠ 2 by tauto)
    have h4 : p%4=1 ∨ p%4=3 := by obtain ⟨k,hk⟩ := hodd; omega
    rcases h4 with h|h
    · simp [f_split hp h, h12, hEven]
    · simp [f_inert hp h (show p ≠ 3 by tauto), hEven]

theorem f_support (n : ℕ) : f n ≠ 0 → n%12=1 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp [f_bad (m := 0) (by simp)]
  | one => intro _; decide
  | coprime a b ha hb hc ia ib =>
    rw [f_mul ha.le hb.le hc, mul_ne_zero_iff]
    rintro ⟨h,k⟩
    rw [Nat.mul_mod, ia h, ib k]
  | prime_pow p e hp he =>
    rw [f_prime_pow hp he]
    split_ifs with hb h12 hEven
    · simp
    · intro _
      simpa [Nat.ModEq] using (Nat.ModEq.pow e (show p ≡ 1 [MOD 12] from h12))
    · intro _
      obtain ⟨j,rfl⟩ := hEven
      have hcop : p.Coprime 12 := hp.coprime_iff_not_dvd.mpr (by
        intro hd
        have := Nat.le_of_dvd (by decide : 0<12) hd
        interval_cases p <;> norm_num at *)
      have aux : ∀ x : ZMod 12, IsUnit x → x^2=1 := by decide +kernel
      have hu := (ZMod.isUnit_iff_coprime p 12).mpr hcop
      have h2 := aux _ hu
      have hpow : (p : ZMod 12)^(j+j) = 1 := by
        rw [← two_mul, pow_mul, h2, one_pow]
      exact (ZMod.natCast_eq_natCast_iff (p^(j+j)) 1 12).mp (by simpa using hpow)
    · simp


/-- The four real characters of the units modulo twelve, extended by zero. -/
private def sign12 (j : Fin 4) (x : ZMod 12) : ℤ :=
  if x = 1 then 1 else if x = 5 then (if j = 1 ∨ j = 3 then -1 else 1)
  else if x = 7 then (if j = 2 ∨ j = 3 then -1 else 1)
  else if x = 11 then (if j = 1 ∨ j = 2 then -1 else 1) else 0

private lemma sign12_mul : ∀ (j : Fin 4) (x y : ZMod 12),
    sign12 j (x*y) = sign12 j x * sign12 j y := by decide +kernel

private lemma sign12_zero : ∀ j : Fin 4, sign12 j 0 = 0 := by decide

private noncomputable def chi (j : Fin 4) : ArithmeticFunction ℂ :=
  ⟨fun n => ((sign12 j n : ℤ) : ℂ), by simp [sign12_zero]⟩

private lemma chi_mul (j : Fin 4) (m n : ℕ) : chi j (m*n) = chi j m * chi j n := by
  simp [chi, Nat.cast_mul, sign12_mul]

private lemma chi_mult (j : Fin 4) : (chi j).IsMultiplicative :=
  ⟨by simp [chi,sign12], fun {_ _} _ => chi_mul j _ _⟩

private noncomputable def weight : ArithmeticFunction ℂ :=
  ⟨fun n => (f n : ℂ), by simp [f_bad (m := 0) (by simp)]⟩

private lemma weight_mult : weight.IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  exact ⟨by simp [weight,f_one], fun hm hn hc => by simp [weight, f_mul (by omega) (by omega) hc]⟩

private noncomputable def bell (p : ℕ) (w : ArithmeticFunction ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun j => w (p^j)

private lemma bell_mul {p : ℕ} (hp : p.Prime) (w v : ArithmeticFunction ℂ) :
    bell p (w*v) = bell p w * bell p v := by
  apply PowerSeries.ext
  intro k
  simp only [bell, PowerSeries.coeff_mk, PowerSeries.coeff_mul, ArithmeticFunction.mul_apply]
  rw [Nat.sum_divisorsAntidiagonal (fun i j => w i * v j), Nat.sum_divisors_prime_pow hp,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => w (p^i) * v (p^j))]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Nat.pow_div (by simpa using hi : i ≤ k) hp.pos]

private noncomputable def geom (t : ℂ) : PowerSeries ℂ := PowerSeries.mk (t^·)

private lemma bell_chi (p : ℕ) (j : Fin 4) : bell p (chi j) = geom (chi j p) := by
  apply PowerSeries.ext
  intro k
  simp only [bell,geom,PowerSeries.coeff_mk]
  induction k with
  | zero => simp [(chi_mult j).1]
  | succ k ih => rw [pow_succ,chi_mul,ih,pow_succ]

private lemma geom_denom (t : ℂ) : geom t * (1-PowerSeries.X * PowerSeries.C t) = 1 := by
  apply PowerSeries.ext
  intro n
  rw [mul_sub, mul_one, ← mul_assoc]
  simp only [map_sub, PowerSeries.coeff_mul_C, PowerSeries.coeff_one]
  rw [← pow_one (PowerSeries.X : PowerSeries ℂ),PowerSeries.coeff_mul_X_pow']
  cases n <;> simp [geom,pow_succ]


private lemma geom_zero : geom 0 = 1 := by simpa using geom_denom 0

private lemma coeff_geom_pair (x : ℂ) (k : ℕ) :
    (geom x * geom 1).coeff k = ∑ j ∈ Finset.range (k+1), x^j := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => (geom x).coeff i * (geom 1).coeff j)]
  simp [geom]

private lemma bell_bad {p : ℕ} (hp : p = 2 ∨ p = 3) : bell p weight = 1 := by
  apply PowerSeries.ext
  intro j
  cases j with
  | zero => simp [bell,weight,f_one]
  | succ j =>
    have h : 2 ∣ p^(j+1) ∨ 3 ∣ p^(j+1) := by
      rcases hp with rfl|rfl
      · exact .inl (dvd_pow_self _ (by omega))
      · exact .inr (dvd_pow_self _ (by omega))
    simp [bell,weight,f_bad h]

private lemma bell_good {p : ℕ} (hp : p.Prime) (hg : ¬(p=2 ∨ p=3)) :
    bell p weight = geom (if p%12=1 then 1 else -1) * geom 1 := by
  apply PowerSeries.ext
  intro k
  rw [coeff_geom_pair]
  cases k with
  | zero => simp [bell,weight,f_one]
  | succ k =>
    simp only [bell,PowerSeries.coeff_mk,weight,ArithmeticFunction.coe_mk,
      f_prime_pow hp (Nat.succ_pos _),if_neg hg]
    by_cases h : p%12=1
    · simp [h]
    · rw [if_neg h,if_neg h,neg_one_geom_sum]
      simp [Nat.even_add_one]
      split_ifs <;> simp_all [Nat.odd_iff, Nat.even_iff]

private noncomputable def K : ArithmeticFunction ℂ := chi 0 * chi 1 * chi 2 * chi 3

theorem convolution_square : weight * weight = K := by
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ (weight_mult.mul weight_mult)
    _ ((((chi_mult 0).mul (chi_mult 1)).mul (chi_mult 2)).mul (chi_mult 3))).mpr
  intro p j hp
  suffices h : bell p (weight * weight) = bell p K from congrArg (PowerSeries.coeff j) h
    |> fun he => by simpa only [bell, K, PowerSeries.coeff_mk] using he
  simp only [K, bell_mul hp, bell_chi]
  have hval := ZMod.val_natCast 12 p
  have eqv : (p : ZMod 12) = (p%12 : ℕ) := by simp
  by_cases hb : p=2 ∨ p=3
  · rw [bell_bad hb]
    rcases hb with rfl|rfl <;>
      norm_num [chi,sign12,geom_zero, show (2 : ZMod 12) ≠ 1 by decide,
        show (2 : ZMod 12) ≠ 5 by decide, show (2 : ZMod 12) ≠ 7 by decide,
        show (2 : ZMod 12) ≠ 11 by decide, show (3 : ZMod 12) ≠ 1 by decide,
        show (3 : ZMod 12) ≠ 5 by decide, show (3 : ZMod 12) ≠ 7 by decide,
        show (3 : ZMod 12) ≠ 11 by decide]
  · rw [bell_good hp hb]
    have cop : p.Coprime 12 := hp.coprime_iff_not_dvd.mpr (by
      intro hd
      have := Nat.le_of_dvd (by decide : 0<12) hd
      interval_cases p <;> norm_num at *)
    have hu := (ZMod.isUnit_iff_coprime p 12).mpr cop
    have hc : ∀ x : ZMod 12, IsUnit x → x.val = 1 ∨ x.val = 5 ∨ x.val = 7 ∨ x.val = 11 := by
      decide +kernel
    have hr := hc _ hu
    rw [hval] at hr
    simp only [chi, ArithmeticFunction.coe_mk]
    rw [eqv]
    rcases hr with h|h|h|h <;> rw [h] <;>
      norm_num [sign12, Fin.reduceFinMk] <;>
      (repeat' rw [if_neg (by decide)]) <;> ring


private lemma LSeriesSummable_of_domination {u v : ℕ → ℂ} {s : ℂ} (hv : LSeriesSummable v s)
    (h : ∀ n, ‖u n‖ ≤ ‖v n‖) : LSeriesSummable u s :=
  (summable_norm_iff.mpr hv).of_norm_bounded fun n => LSeries.norm_term_le s (h n)

private lemma chi_summable (j : Fin 4) {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (chi j) s := by
  apply LSeriesSummable_of_domination (LSeriesSummable_one_iff.mpr hs)
  intro n
  have h : ∀ (i : Fin 4) (x : ZMod 12), |sign12 i x| ≤ 1 := by decide +kernel
  simpa only [chi,ArithmeticFunction.coe_mk, Complex.norm_intCast, Pi.one_apply,norm_one]
    using (show (|(sign12 j n : ℤ)| : ℝ) ≤ 1 by exact_mod_cast h j n)

private lemma K_summable {s : ℂ} (hs : 1 < s.re) : LSeriesSummable K s :=
  ArithmeticFunction.LSeriesSummable_mul (ArithmeticFunction.LSeriesSummable_mul
    (ArithmeticFunction.LSeriesSummable_mul (chi_summable 0 hs) (chi_summable 1 hs))
    (chi_summable 2 hs)) (chi_summable 3 hs)

private lemma nonneg_f (n : ℕ) : 0 ≤ f n := Real.sqrt_nonneg _

private lemma weight_le_K (n : ℕ) : f n ≤ (K n).re := by
  rw [← convolution_square, ArithmeticFunction.mul_apply]
  simp only [weight,ArithmeticFunction.coe_mk, ← Complex.ofReal_mul, ← Complex.ofReal_sum,
    Complex.ofReal_re]
  by_cases hn : n=0
  · simp [hn,f_bad (m := 0) (by simp)]
  have h := Finset.single_le_sum (f := fun ij : ℕ × ℕ => f ij.1 * f ij.2)
    (fun i _ => mul_nonneg (nonneg_f _) (nonneg_f _))
    (show (1,n) ∈ n.divisorsAntidiagonal by simp [Nat.mem_divisorsAntidiagonal,hn])
  simpa [f_one] using h

private lemma weight_summable {s : ℂ} (hs : 1 < s.re) : LSeriesSummable weight s := by
  apply LSeriesSummable_of_domination (K_summable hs)
  intro n
  simpa only [weight,ArithmeticFunction.coe_mk,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (nonneg_f n)] using (weight_le_K n).trans (K n).re_le_norm

private noncomputable def L12 (j : Fin 4) := ZMod.LFunction (fun x => (sign12 j x : ℂ))

theorem LSeries_weight_square {s : ℂ} (hs : 1 < s.re) :
    LSeries weight s ^ 2 = L12 0 s * L12 1 s * L12 2 s * L12 3 s := by
  have eqL (j : Fin 4) : L12 j s = LSeries (chi j) s :=
    ZMod.LFunction_eq_LSeries _ hs
  simp only [eqL]
  rw [pow_two, ← ArithmeticFunction.LSeries_mul' (weight_summable hs) (weight_summable hs),
    convolution_square]
  have h01 := ArithmeticFunction.LSeriesSummable_mul (chi_summable 0 hs) (chi_summable 1 hs)
  rw [K, ArithmeticFunction.LSeries_mul' (ArithmeticFunction.LSeriesSummable_mul h01
    (chi_summable 2 hs)) (chi_summable 3 hs),ArithmeticFunction.LSeries_mul' h01 (chi_summable 2 hs),
    ArithmeticFunction.LSeries_mul' (chi_summable 0 hs) (chi_summable 1 hs)]

private lemma L12_cont {j : Fin 4} (hj : j ≠ 0) : Continuous (L12 j) := by
  have h : ∀ i : Fin 4, i ≠ 0 → ∑ x : ZMod 12, sign12 i x = 0 := by decide +kernel
  apply (ZMod.differentiable_LFunction_of_sum_zero _).continuous
  exact_mod_cast h j hj

open Topology in
theorem L12_product_residue :
    Tendsto (fun s : ℂ => (s-1) * (L12 0 s * L12 1 s * L12 2 s * L12 3 s))
      (𝓝[≠] 1) (𝓝 ((1/3 : ℂ) * L12 1 1 * L12 2 1 * L12 3 1)) := by
  have h : ∑ x : ZMod 12, sign12 0 x = 4 := by decide +kernel
  have h0 := ZMod.LFunction_residue_one (fun x => (sign12 0 x : ℂ))
  rw [← Finset.sum_div, ← Int.cast_sum, h] at h0
  norm_num at h0
  have hc (j : Fin 4) (hj : j ≠ 0) : Tendsto (L12 j) (𝓝[≠] 1) (𝓝 (L12 j 1)) :=
    ((L12_cont hj).tendsto _).mono_left nhdsWithin_le_nhds
  simpa only [← mul_assoc, L12] using (((h0.mul (hc 1 (by decide))).mul
    (hc 2 (by decide))).mul (hc 3 (by decide)))


private noncomputable def squareIndicator : ArithmeticFunction ℂ :=
  ⟨fun n => if n.Coprime 6 ∧ IsSquare n then 1 else 0, by simp⟩

private lemma squareIndicator_mult : squareIndicator.IsMultiplicative := by
  refine ⟨by simp [squareIndicator], ?_⟩
  intro m n h
  have hs : IsSquare (m*n) ↔ IsSquare m ∧ IsSquare n := by
    refine ⟨?_, fun h => h.1.mul h.2⟩
    rintro ⟨u,hu⟩
    have aux (a b : ℕ) (hc : a.Coprime b) (he : a*b=u*u) : IsSquare a := by
      obtain ⟨r,hr⟩ := exists_eq_pow_of_mul_eq_pow
        (show IsUnit (gcd a b) by rw [show gcd a b = 1 from hc.gcd_eq_one]; exact isUnit_one)
        (show a*b=u^2 by rwa [sq])
      exact ⟨r,by rwa [← sq]⟩
    exact ⟨aux _ _ h hu,aux _ _ h.symm (by simpa [mul_comm] using hu)⟩
  simp only [squareIndicator, ArithmeticFunction.coe_mk, Nat.coprime_mul_iff_left, hs]
  split_ifs <;> simp_all

private lemma squareIndicator_pp {p : ℕ} (hp : p.Prime) (k : ℕ) :
    squareIndicator (p^k) =
      if k = 0 then 1 else if p = 2 ∨ p = 3 then 0 else if Even k then 1 else 0 := by
  rcases k with _ | k
  · simp [squareIndicator]
  have hs : IsSquare (p^(k+1)) ↔ Even (k+1) := by
    refine ⟨?_,fun e => e.isSquare_pow p⟩
    rintro ⟨q,hq⟩
    have hf := congrArg (fun n : ℕ => n.factorization p) hq
    have hq0 : q ≠ 0 := by intro hz; simp [hz,hp.ne_zero] at hq
    rw [Nat.factorization_mul hq0 hq0, hp.factorization_pow] at hf
    simp at hf
    exact ⟨_,hf⟩
  have hc : (p^(k+1)).Coprime 6 ↔ ¬(p=2 ∨ p=3) := by
    rw [Nat.coprime_pow_left_iff (by omega),hp.coprime_iff_not_dvd]
    constructor
    · rintro h (rfl|rfl) <;> exact h (by decide)
    · intro h hd
      have := Nat.le_of_dvd (by decide : 0<6) hd
      interval_cases p <;> norm_num at *
  simp only [squareIndicator,ArithmeticFunction.coe_mk,hs,hc,Nat.succ_ne_zero,if_false]
  split_ifs <;> tauto

private noncomputable def evenGeom : PowerSeries ℂ := PowerSeries.mk fun j => if Even j then 1 else 0

private lemma evenGeom_eq : evenGeom = geom (-1) * geom 1 := by
  apply PowerSeries.ext
  intro k
  rw [coeff_geom_pair, neg_one_geom_sum]
  simp only [evenGeom,PowerSeries.coeff_mk,Nat.even_add_one]
  split_ifs <;> simp_all

private lemma bell_sq_good {p : ℕ} (hp : p.Prime) (h : ¬(p=2 ∨ p=3)) :
    bell p squareIndicator = evenGeom := by
  apply PowerSeries.ext
  intro k
  cases k <;> simp [bell,evenGeom,squareIndicator_pp hp,h]

private lemma bell_sq_bad {p : ℕ} (hp : p.Prime) (h : p=2 ∨ p=3) :
    bell p squareIndicator = 1 := by
  apply PowerSeries.ext
  intro k
  simp only [bell, PowerSeries.coeff_mk, squareIndicator_pp hp, if_pos h, PowerSeries.coeff_one]

private noncomputable def moment2 := weight.pmul weight

private lemma moment2_apply (n : ℕ) : moment2 n = (f n : ℂ) * (f n : ℂ) := rfl

private lemma moment2_mult : moment2.IsMultiplicative := weight_mult.pmul weight_mult


private lemma weight_p1 {p : ℕ} (hp : p.Prime) (h : p%12=1) (k : ℕ) :
    weight (p^k) = (k+1 : ℂ) := by
  have hg : ¬(p=2 ∨ p=3) := by omega
  cases k <;> simp [weight,f_prime_pow hp,f_one,h,hg]

private lemma moment2_local_split {p : ℕ} (hp : p.Prime) (h : p%12=1) :
    bell p moment2 * (1-PowerSeries.X) = bell p weight * (1+PowerSeries.X) := by
  rw [mul_sub,mul_add,mul_one,mul_one]
  apply PowerSeries.ext
  intro k
  simp only [map_add,map_sub]
  rw [← pow_one (PowerSeries.X : PowerSeries ℂ),PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mul_X_pow']
  cases k <;> simp [bell,moment2,ArithmeticFunction.pmul_apply,weight_p1 hp h] <;> ring

private lemma moment2_local_rest {p : ℕ} (hp : p.Prime) (h : p%12≠1) :
    bell p moment2 = bell p weight := by
  apply PowerSeries.ext
  intro k
  cases k with
  | zero => simp [bell,moment2_apply,weight,f_one]
  | succ k =>
    simp only [bell,PowerSeries.coeff_mk,moment2_apply,weight,
      ArithmeticFunction.coe_mk,f_prime_pow hp (Nat.succ_pos k),if_neg h]
    split_ifs <;> simp

theorem convolution_second : moment2 * squareIndicator = K := by
  rw [← convolution_square]
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    (moment2_mult.mul squareIndicator_mult) _ (weight_mult.mul weight_mult)).mpr
  intro p k hp
  suffices h : bell p (moment2 * squareIndicator) = bell p (weight*weight) by
    simpa only [bell,PowerSeries.coeff_mk] using congrArg (PowerSeries.coeff k) h
  rw [bell_mul hp,bell_mul hp]
  by_cases hb : p=2 ∨ p=3
  · rw [moment2_local_rest hp (by omega),bell_bad hb,bell_sq_bad hp hb]
  rw [bell_sq_good hp hb,evenGeom_eq]
  by_cases h : p%12=1
  · have hm := moment2_local_split hp h
    have hw := bell_good hp hb
    rw [if_pos h] at hw
    rw [hw] at hm ⊢
    have ha : geom 1 * (1-PowerSeries.X) = 1 := by simpa using geom_denom 1
    have hb : geom (-1) * (1+PowerSeries.X) = 1 := by simpa using geom_denom (-1)
    linear_combination
      (geom (-1) * geom 1 ^ 2) * hm -
      (bell p moment2 * geom (-1) * geom 1) * ha + geom 1 ^ 4 * hb
  · rw [moment2_local_rest hp h,bell_good hp hb,if_neg h]

private lemma squareIndicator_nonneg (n : ℕ) : 0 ≤ (squareIndicator n).re := by
  simp only [squareIndicator,ArithmeticFunction.coe_mk]; split_ifs <;> norm_num

private lemma moment2_summable {s : ℂ} (hs : 1 < s.re) : LSeriesSummable moment2 s := by
  apply LSeriesSummable_of_domination (K_summable hs)
  intro n
  have ht (m d : ℕ) : (moment2 m * squareIndicator d).re =
      (f m)^2 * (squareIndicator d).re := by
    simp [moment2_apply,Complex.mul_re,pow_two]
  by_cases hn : n=0
  · simp [hn]
  have h := Finset.single_le_sum (f := fun ij : ℕ × ℕ => (f ij.1)^2 * (squareIndicator ij.2).re)
    (fun i _ => mul_nonneg (sq_nonneg _) (squareIndicator_nonneg _))
    (show (n,1) ∈ n.divisorsAntidiagonal by simp [Nat.mem_divisorsAntidiagonal,hn])
  have hk : (K n).re = ∑ ij ∈ n.divisorsAntidiagonal, (f ij.1)^2 * (squareIndicator ij.2).re := by
    simp only [← convolution_second, ArithmeticFunction.mul_apply, Complex.re_sum,ht]
  have he : (f n)^2 ≤ (K n).re := by simpa [← hk, squareIndicator_mult.1] using h
  simpa [moment2_apply,abs_of_nonneg (nonneg_f n),pow_two] using he.trans (K n).re_le_norm

private lemma squareIndicator_summable {s : ℂ} (hs : 1 < s.re) : LSeriesSummable squareIndicator s := by
  apply LSeriesSummable_of_domination (LSeriesSummable_one_iff.mpr hs)
  intro n
  simp only [squareIndicator,ArithmeticFunction.coe_mk, Pi.one_apply, norm_one]
  split_ifs <;> simp

theorem LSeries_second {s : ℂ} (hs : 1 < s.re) :
    LSeries moment2 s * LSeries squareIndicator s = LSeries weight s ^ 2 := by
  rw [← ArithmeticFunction.LSeries_mul' (moment2_summable hs) (squareIndicator_summable hs),
    convolution_second,← convolution_square,ArithmeticFunction.LSeries_mul' (weight_summable hs)
    (weight_summable hs),pow_two]


private lemma sign12_principal : ∀ x : ZMod 12, sign12 0 x = if IsUnit x then 1 else 0 := by
  decide +kernel

private lemma chi0_coprime (n : ℕ) : chi 0 n = if n.Coprime 6 then 1 else 0 := by
  have hc : n.Coprime 12 ↔ n.Coprime 6 := by
    rw [show 12=2*6 by decide,Nat.coprime_mul_iff_right,show 6=2*3 by decide, Nat.coprime_mul_iff_right]
    tauto
  simp [chi,sign12_principal,ZMod.isUnit_iff_coprime,hc, apply_ite]

theorem LSeries_squareIndicator {s : ℂ} (hs : 1 < s.re) :
    LSeries squareIndicator s = L12 0 (2*s) := by
  have hs2 : 1 < (2*s).re := by simp; linarith
  rw [L12,ZMod.LFunction_eq_LSeries _ hs2]
  change (∑' n, LSeries.term squareIndicator s n) = ∑' n, LSeries.term (chi 0) (2*s) n
  rw [← (Nat.pow_left_injective (by decide : 2≠0)).tsum_eq]
  · apply tsum_congr
    intro n
    have hc : squareIndicator (n^2) = chi 0 n := by
      simp [squareIndicator,chi0_coprime,IsSquare,show ∃ r, n^2=r*r from ⟨n,pow_two _⟩,
        Nat.coprime_pow_left_iff]
    have hpow : (n : ℂ)^(2*s) = ((n:ℂ)^2)^s := Complex.natCast_cpow_natCast_mul n 2 s
    simp [LSeries.term_def,hc,hpow]
  · intro n hn
    by_contra h
    have hns : ¬IsSquare n := by
      rintro ⟨r,hr⟩; exact h ⟨r,by simpa [sq] using hr.symm⟩
    exact hn (by simp [LSeries.term_def,squareIndicator,hns])

private lemma L12_principal : L12 0 = DirichletCharacter.LFunctionTrivChar 12 := by
  change ZMod.LFunction _ = ZMod.LFunction _
  congr 1
  funext x
  rw [sign12_principal]
  split_ifs with h
  · simp [MulChar.one_apply h]
  · simp [MulChar.map_nonunit _ h]

theorem L12_principal_two : L12 0 2 = (Real.pi : ℂ)^2 / 9 := by
  rw [L12_principal,DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (by norm_num),
    riemannZeta_two,show Nat.primeFactors 12 = {2,3} by decide +kernel]
  simp [Complex.cpow_neg,Complex.cpow_ofNat] <;> ring


private noncomputable def logWeight (w : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => (Real.log n : ℂ) * w n, by simp⟩

private lemma logWeight_mul (u v : ArithmeticFunction ℂ) :
    logWeight (u*v) = logWeight u * v + u * logWeight v := by
  ext n
  rw [ArithmeticFunction.add_apply, ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
  change (Real.log n : ℂ) * ((u*v) n) = _
  rw [ArithmeticFunction.mul_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  simp only [logWeight, ArithmeticFunction.coe_mk]
  refine Finset.sum_congr rfl fun ⟨a,b⟩ hab => ?_
  obtain ⟨h,hn⟩ := Nat.mem_divisorsAntidiagonal.mp hab
  change a*b=n at h
  subst n
  have ha : (a:ℝ)≠0 := by exact_mod_cast left_ne_zero_of_mul hn
  have hb : (b:ℝ)≠0 := by exact_mod_cast right_ne_zero_of_mul hn
  rw [Nat.cast_mul, Real.log_mul ha hb,Complex.ofReal_add]; ring

private noncomputable def twistLambda (j : Fin 4) : ArithmeticFunction ℂ :=
  ⟨fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * chi j n, by simp⟩

private lemma logWeight_chi (j : Fin 4) : logWeight (chi j) = twistLambda j * chi j := by
  ext n
  simp only [ArithmeticFunction.mul_apply,logWeight,ArithmeticFunction.coe_mk]
  calc
    _ = ∑ i ∈ n.divisors, (ArithmeticFunction.vonMangoldt i : ℂ) * chi j n := by
      rw [← Finset.sum_mul,← Complex.ofReal_sum, ArithmeticFunction.vonMangoldt_sum]
    _ = _ := by
      rw [Nat.sum_divisorsAntidiagonal (fun a b => twistLambda j a * chi j b)]
      apply Finset.sum_congr rfl
      intro i hi
      change _ = ((ArithmeticFunction.vonMangoldt i : ℂ) * chi j i) * chi j (n/i)
      rw [mul_assoc, ← chi_mul, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hi)]

noncomputable def progressionLambda (n : ℕ) : ℝ :=
  if n%12=1 then 2 * ArithmeticFunction.vonMangoldt n else 0

private noncomputable def lambdaAF : ArithmeticFunction ℂ :=
  ⟨fun n => (progressionLambda n : ℂ), by simp [progressionLambda]⟩

private lemma sum_twist : twistLambda 0 + twistLambda 1 + twistLambda 2 + twistLambda 3 =
    lambdaAF + lambdaAF := by
  ext n
  have hs : ∀ x : ZMod 12, sign12 0 x + sign12 1 x + sign12 2 x + sign12 3 x =
      if x=1 then 4 else 0 := by decide +kernel
  have h := congrArg (fun m : ℤ => (m : ℂ)) (hs n)
  push_cast at h
  have hn : (n : ZMod 12) = 1 ↔ n%12=1 := ZMod.natCast_eq_natCast_iff n 1 12
  simp only [ArithmeticFunction.add_apply]
  simp only [twistLambda,chi,lambdaAF,ArithmeticFunction.coe_mk,
    ← mul_add,progressionLambda]
  change _ * ((sign12 0 n : ℂ) + sign12 1 n + sign12 2 n + sign12 3 n) = _
  rw [h]
  by_cases he : n%12=1 <;> simp [he,hn] <;> ring

theorem logWeight_first : logWeight weight = weight * lambdaAF := by
  have hu : IsUnit weight := ArithmeticFunction.isUnit_iff_isUnit_apply_one.mpr (by rw [weight_mult.1]; exact isUnit_one)
  apply hu.mul_right_inj.mp
  have h := congrArg logWeight convolution_square
  simp only [K,logWeight_mul,logWeight_chi] at h
  have hs := sum_twist
  have hK : chi 0*chi 1*chi 2*chi 3 = weight*weight := convolution_square.symm
  have he : weight * logWeight weight + weight * logWeight weight =
      weight * (weight * lambdaAF) + weight * (weight * lambdaAF) := by
    calc
      _ = (chi 0*chi 1*chi 2*chi 3) * (twistLambda 0 + twistLambda 1 + twistLambda 2 + twistLambda 3) := by
        linear_combination h
      _ = _ := by rw [hK,hs]; ring
  ext n
  have h2 := congrArg (fun w : ArithmeticFunction ℂ => w n) he
  simp only [ArithmeticFunction.add_apply] at h2
  linear_combination (1/2 : ℂ) * h2

theorem log_convolution (n : ℕ) : Real.log n * f n =
    ∑ ij ∈ n.divisorsAntidiagonal, f ij.1 * progressionLambda ij.2 := by
  have h := congrArg (fun u : ArithmeticFunction ℂ => u n) logWeight_first
  change logWeight weight n = (weight * lambdaAF) n at h
  rw [ArithmeticFunction.mul_apply] at h
  simpa only [logWeight, ArithmeticFunction.coe_mk,weight,
    lambdaAF,← Complex.ofReal_mul, ← Complex.ofReal_sum,Complex.ofReal_inj] using h

open Topology in
theorem progressionLambda_mean :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, progressionLambda k) / n)
      atTop (𝓝 (1/2 : ℝ)) := by
  have h := OMALib.PNT.WeakPNT_AP (q := 12) (a := 1) (by decide) (by decide) (by decide)
  rw [show Nat.totient 12 = 4 by decide +kernel] at h
  have hm := h.const_mul (2 : ℝ)
  convert hm using 1
  · funext n
    simp only [progressionLambda,OMALib.PNT.cumsum, ← mul_div_assoc, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> ring
  · norm_num


private noncomputable def charNumerator (j : Fin 4) (x : ℝ) :=
  ∑ n ∈ Finset.range 12, (sign12 j n : ℝ) * x^n

private lemma char_geometric (j : Fin 4) (x : ℝ) (hx : 0 ≤ x) (hx' : x < 1) :
    HasSum (fun n : ℕ => (sign12 j n : ℝ) * x^n) (charNumerator j x / (1-x^12)) := by
  let a (n : ℕ) := (sign12 j n : ℝ) * x^n
  have hs : Summable a := by
    refine (hasSum_geometric_of_lt_one hx hx').summable.of_norm_bounded fun n => ?_
    have ha : ∀ (j : Fin 4) (x : ZMod 12), |sign12 j x| ≤ 1 := by decide +kernel
    have h : |(sign12 j n : ℝ)| ≤ 1 := by exact_mod_cast ha j n
    simpa [a,abs_mul,abs_of_nonneg hx] using mul_le_mul_of_nonneg_right h (pow_nonneg hx n)
  have hshift (n : ℕ) : a (n+12) = a n * x^12 := by
    simp [a,Nat.cast_add,pow_add,mul_assoc,show (12 : ZMod 12)=0 by decide]
  have he := hs.sum_add_tsum_nat_add 12
  simp_rw [hshift] at he
  rw [tsum_mul_right] at he
  convert hs.hasSum using 1
  symm
  apply (eq_div_iff (sub_ne_zero.mpr (pow_lt_one₀ hx hx' (by decide : 12≠0)).ne')).mpr
  change (∑' n, a n) * (1-x^12) = ∑ i ∈ Finset.range 12, a i
  linarith

open MeasureTheory Set Asymptotics Topology in
private lemma L12_mellin_one {j : Fin 4} (hj : j ≠ 0) {R : ℝ → ℝ} (hR : Continuous R)
    (hrat : ∀ x : ℝ, 0 < x → x < 1 → charNumerator j x / (1-x^12) = x*R x) :
    L12 j 1 = ∫ t in Ioi (0:ℝ), ((Real.exp (-t)*R (Real.exp (-t)) : ℝ) : ℂ) := by
  let F (t : ℝ) : ℂ := ((Real.exp (-t)*R (Real.exp (-t)) : ℝ) : ℂ)
  have hF : Continuous F := by dsimp [F]; fun_prop
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0:ℝ) 1) hR.continuousOn
  have hb (t : ℝ) (ht : 0 ≤ t) : ‖F t‖ ≤ C * Real.exp (-t) := by
    have h := hC (Real.exp (-t)) ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (by linarith)⟩
    simp only [F,Complex.norm_real,Real.norm_eq_abs,abs_mul,Real.abs_exp]
    simpa only [Real.norm_eq_abs,mul_comm] using
      mul_le_mul_of_nonneg_left h (Real.exp_pos (-t)).le
  have htop : F =O[atTop] fun t => Real.exp (-(1:ℝ)*t) := by
    apply IsBigO.of_bound C
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    simpa using hb t ht
  have hCpos : 0 ≤ C := (norm_nonneg _).trans (hC 0 (by simp))
  have hbot : F =O[𝓝[>] 0] fun t : ℝ => t ^ (-(0:ℝ)) := by
    apply IsBigO.of_bound C
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hle := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (le_of_lt (show 0<t from ht)))
    simpa using (hb t (le_of_lt ht)).trans (mul_le_mul_of_nonneg_left hle hCpos)
  have hcont := (mellin_differentiableAt_of_isBigO_rpow_exp (s := (1:ℂ)) (by norm_num : (0:ℝ)<1)
    (hF.continuousOn.locallyIntegrableOn measurableSet_Ioi) htop hbot (by norm_num)).continuousAt
  have hM (s : ℂ) (hs : 1 < s.re) : mellin F s = Complex.Gamma s * L12 j s := by
    have hsum := hasSum_mellin (a := fun n : ℕ => chi j n) (p := fun n : ℕ => (n:ℝ))
      (F := F) (s := s) (fun n => by rcases n with _|n; simp; right; positivity)
      (by linarith) (fun t ht => ?_) ?_
    · rw [← hsum.tsum_eq, L12, ZMod.LFunction_eq_LSeries _ hs,LSeries, ← tsum_mul_left]
      apply tsum_congr
      intro n
      by_cases hn : n=0
      · simp [hn,chi,sign12_zero,LSeries.term_def]
      · simp [LSeries.term_def,hn,chi,mul_div_assoc]
    · have he := char_geometric j _ (Real.exp_pos (-t)).le (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht))
      rw [hrat _ (Real.exp_pos _) (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht))] at he
      apply (Complex.hasSum_ofReal.mpr he).congr_fun
      intro n
      rw [show -(n : ℝ)*t=(n : ℝ)*(-t) by ring,Real.exp_nat_mul]
      push_cast; rfl
    · have hh := (chi_summable j hs).norm
      refine hh.congr fun n => ?_
      rw [LSeries.norm_term_eq]
      by_cases hn : n=0 <;> simp [hn,Real.zero_rpow (show s.re ≠ 0 by linarith)]
  have ht : Tendsto (fun t : ℝ => (t:ℂ)) (𝓝[>] 1) (𝓝 1) :=
    (Complex.continuous_ofReal.tendsto' _ _ (by simp)).mono_left nhdsWithin_le_nhds
  have hG := Complex.continuousAt_Gamma 1 (fun m h => by
    have e : (1 : ℝ) = -(m : ℝ) := by simpa using congrArg Complex.re h
    linarith [Nat.cast_nonneg (α := ℝ) m])
  have heq := tendsto_nhds_unique_of_eventuallyEq (hcont.tendsto.comp ht)
    ((hG.mul (L12_cont hj).continuousAt).tendsto.comp ht) (by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact hM _ (by exact_mod_cast ht))
  simpa [mellin,F] using heq.symm


open MeasureTheory Set Topology in
private lemma L12_primitive {j : Fin 4} (hj : j≠0) {R U : ℝ → ℝ}
    (hR : Continuous R) (hU : ∀ x, HasDerivAt U (R x) x)
    (hn : ∀ x ∈ Icc 0 1, 0 ≤ R x)
    (hfrac : ∀ x, 0<x → x<1 → charNumerator j x/(1-x^12)=x*R x) :
    L12 j 1 = ((U 1 - U 0 : ℝ) : ℂ) := by
  rw [L12_mellin_one hj hR hfrac,integral_complex_ofReal]
  have hi := integral_Ioi_of_hasDerivAt_of_nonneg' (g := fun t => -U (Real.exp (-t)))
    (g' := fun t => Real.exp (-t)*R (Real.exp (-t))) (a := 0) (l := -U 0)
    (fun t _ => ?_) (fun t ht => ?_) ((hU 0).continuousAt.tendsto.comp
      Real.tendsto_exp_neg_atTop_nhds_zero).neg
  · rw [hi]; simp; ring_nf
  · have he : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-t)*(-1)) t :=
      (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg
    change HasDerivAt (fun x => -U (Real.exp (-x))) (Real.exp (-t) * R (Real.exp (-t))) t
    simpa [Function.comp_def,Pi.neg_def,mul_comm] using ((hU (Real.exp (-t))).comp t he).neg
  · apply mul_nonneg (Real.exp_pos _).le
    exact hn _ ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith [show 0<t from ht])⟩
private lemma numerator_1 (x : ℝ) : charNumerator 1 x = x - x^5 + x^7 - x^11 := by
  simp only [charNumerator, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num1
  have h0 : sign12 1 (0 : ℕ) = 0 := by decide
  have h1 : sign12 1 (1 : ℕ) = 1 := by decide
  have h2 : sign12 1 (2 : ℕ) = 0 := by decide
  have h3 : sign12 1 (3 : ℕ) = 0 := by decide
  have h4 : sign12 1 (4 : ℕ) = 0 := by decide
  have h5 : sign12 1 (5 : ℕ) = -1 := by decide
  have h6 : sign12 1 (6 : ℕ) = 0 := by decide
  have h7 : sign12 1 (7 : ℕ) = 1 := by decide
  have h8 : sign12 1 (8 : ℕ) = 0 := by decide
  have h9 : sign12 1 (9 : ℕ) = 0 := by decide
  have h10 : sign12 1 (10 : ℕ) = 0 := by decide
  have h11 : sign12 1 (11 : ℕ) = -1 := by decide
  simp only [Nat.cast_ofNat,Nat.cast_one,Nat.cast_zero] at *
  simp [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11]; ring

private lemma numerator_2 (x : ℝ) : charNumerator 2 x = x + x^5 - x^7 - x^11 := by
  simp only [charNumerator, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num1
  have h0 : sign12 2 (0 : ℕ) = 0 := by decide
  have h1 : sign12 2 (1 : ℕ) = 1 := by decide
  have h2 : sign12 2 (2 : ℕ) = 0 := by decide
  have h3 : sign12 2 (3 : ℕ) = 0 := by decide
  have h4 : sign12 2 (4 : ℕ) = 0 := by decide
  have h5 : sign12 2 (5 : ℕ) = 1 := by decide
  have h6 : sign12 2 (6 : ℕ) = 0 := by decide
  have h7 : sign12 2 (7 : ℕ) = -1 := by decide
  have h8 : sign12 2 (8 : ℕ) = 0 := by decide
  have h9 : sign12 2 (9 : ℕ) = 0 := by decide
  have h10 : sign12 2 (10 : ℕ) = 0 := by decide
  have h11 : sign12 2 (11 : ℕ) = -1 := by decide
  simp only [Nat.cast_ofNat,Nat.cast_one,Nat.cast_zero] at *
  simp [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11]; ring

private lemma numerator_3 (x : ℝ) : charNumerator 3 x = x - x^5 - x^7 + x^11 := by
  simp only [charNumerator, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num1
  have h0 : sign12 3 (0 : ℕ) = 0 := by decide
  have h1 : sign12 3 (1 : ℕ) = 1 := by decide
  have h2 : sign12 3 (2 : ℕ) = 0 := by decide
  have h3 : sign12 3 (3 : ℕ) = 0 := by decide
  have h4 : sign12 3 (4 : ℕ) = 0 := by decide
  have h5 : sign12 3 (5 : ℕ) = -1 := by decide
  have h6 : sign12 3 (6 : ℕ) = 0 := by decide
  have h7 : sign12 3 (7 : ℕ) = -1 := by decide
  have h8 : sign12 3 (8 : ℕ) = 0 := by decide
  have h9 : sign12 3 (9 : ℕ) = 0 := by decide
  have h10 : sign12 3 (10 : ℕ) = 0 := by decide
  have h11 : sign12 3 (11 : ℕ) = 1 := by decide
  simp only [Nat.cast_ofNat,Nat.cast_one,Nat.cast_zero] at *
  simp [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11]; ring


theorem L12_at_one_second : L12 2 1 = (Real.pi/3 : ℝ) := by
  let U (x : ℝ) := Real.arctan x + Real.arctan (x^3)/3
  let R (x : ℝ) := 1/(1+x^2) + x^2/(1+x^6)
  have hR : Continuous R := by dsimp [R]; fun_prop (disch := (intro x; positivity))
  have hU (x : ℝ) : HasDerivAt U (R x) x := by
    have h := (Real.hasDerivAt_arctan x).add
      (((Real.hasDerivAt_arctan (x^3)).comp x ((hasDerivAt_id x).pow 3)).div_const 3)
    apply h.congr_deriv
    dsimp [R]; ring
  rw [L12_primitive (j := 2) (by decide) hR hU (fun x hx => by dsimp [R]; positivity)
    (fun x hx hx1 => ?_)]
  · norm_num [U,Real.arctan_one]; ring
  · rw [numerator_2]; dsimp [R]
    have hne : 1-x^12≠0 := sub_ne_zero.mpr (pow_lt_one₀ hx.le hx1 (by decide : 12≠0)).ne'
    field_simp <;> ring

private noncomputable def primitive3 (x : ℝ) :=
  2 / Real.sqrt 3 * Real.arctan ((2*x+1)/Real.sqrt 3)

private lemma primitive3_deriv (x : ℝ) :
    HasDerivAt primitive3 (1/(1+x+x^2)) x := by
  have hr : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : 0 < Real.sqrt 3 := by positivity
  have hq : 0 < 1+x+x^2 := by nlinarith [sq_nonneg (x+1/2)]
  have hx := (((hasDerivAt_id x).const_mul 2).add_const 1).div_const (Real.sqrt 3)
  have hd := ((Real.hasDerivAt_arctan _).comp x hx).const_mul (2/Real.sqrt 3)
  apply hd.congr_deriv
  simp only [id_eq,one_mul,mul_one]
  field_simp
  nlinarith [hr]

theorem L12_at_one_first : L12 1 1 = (Real.pi/(2*Real.sqrt 3) : ℝ) := by
  let R (x : ℝ) := 1/(1+x+x^2) + x/(1+x^2+x^4)
  let U (x : ℝ) := primitive3 x + primitive3 (x^2)/2
  have hq (x : ℝ) : 0 < 1+x+x^2 := by nlinarith [sq_nonneg (x+1/2)]
  have hR : Continuous R := by
    dsimp [R]; fun_prop (disch := (intro x; first | exact (hq _).ne' | positivity))
  have hU (x : ℝ) : HasDerivAt U (R x) x := by
    have hh := (primitive3_deriv x).add
      (((primitive3_deriv (x^2)).comp x ((hasDerivAt_id x).pow 2)).div_const 2)
    apply hh.congr_deriv
    dsimp [R]; ring
  rw [L12_primitive (j := 1) (by decide) hR hU (fun x hx => by
    have := hx.1; dsimp [R]; positivity) (fun x hx hx1 => ?_)]
  · have hs : 0 < Real.sqrt 3 := by positivity
    have he : 3/Real.sqrt 3 = Real.sqrt 3 := (div_eq_iff hs.ne').mpr (by
      nlinarith [Real.sq_sqrt (show (0:ℝ)≤3 by norm_num)])
    norm_num [U, primitive3,he, one_div,Real.arctan_sqrt_three,Real.arctan_inv_sqrt_three] <;> ring
  · rw [numerator_1]; dsimp [R]
    have hne : 1-x^12≠0 := sub_ne_zero.mpr (pow_lt_one₀ hx.le hx1 (by decide : 12≠0)).ne'
    field_simp <;> ring


theorem L12_at_one_third : L12 3 1 = (Real.log (2+Real.sqrt 3)/Real.sqrt 3 : ℝ) := by
  let r := Real.sqrt 3
  have hr : r^2=3 := Real.sq_sqrt (by norm_num)
  have hrp : 0 < r := Real.sqrt_pos.mpr (by norm_num)
  let A (x : ℝ) := x^2+r*x+1
  let B (x : ℝ) := x^2-r*x+1
  let Q (x : ℝ) := 1-x^2+x^4
  let R (x : ℝ) := (1-x^2)/Q x
  let U (x : ℝ) := (Real.log (A x) - Real.log (B x))/(2*r)
  have hA (x : ℝ) : 0 < A x := by dsimp [A]; nlinarith [sq_nonneg (2*x+r)]
  have hB (x : ℝ) : 0 < B x := by dsimp [B]; nlinarith [sq_nonneg (2*x-r)]
  have hQ (x : ℝ) : 0 < Q x := by dsimp [Q]; nlinarith [sq_nonneg (2*x^2-1)]
  have hR : Continuous R := by dsimp [R,Q]; fun_prop (disch := (intro x; exact (hQ x).ne'))
  have hU (x : ℝ) : HasDerivAt U (R x) x := by
    have ha : HasDerivAt A (2*x+r) x := by
      apply ((((hasDerivAt_id x).pow 2).add ((hasDerivAt_id x).const_mul r)).add_const 1).congr_deriv
      simp
    have hb : HasDerivAt B (2*x-r) x := by
      apply ((((hasDerivAt_id x).pow 2).sub ((hasDerivAt_id x).const_mul r)).add_const 1).congr_deriv
      simp
    apply (((ha.log (hA x).ne').sub (hb.log (hB x).ne')).div_const (2*r)).congr_deriv
    dsimp only [R]
    field_simp [(hA x).ne',(hB x).ne',(hQ x).ne',hrp.ne']
    dsimp [A,B,Q]
    linear_combination primitive_derivative_algebra x r hr
  rw [L12_primitive (j := 3) (by decide) hR hU (fun x hx => div_nonneg
    (by nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2),hx.2]) (hQ x).le)
    (fun x hx hx1 => ?_)]
  · have hInv : 2-r = (2+r)⁻¹ := by
      field_simp
      nlinarith
    change ((U 1 - U 0 : ℝ) : ℂ) = ((Real.log (2+r)/r : ℝ) : ℂ)
    congr 1
    norm_num [U,A,B,show (1:ℝ)+r+1 = 2+r by ring, show (1:ℝ)-r+1=2-r by ring,hInv,
      Real.log_inv] <;> ring
  · rw [numerator_3]; dsimp only [R]
    have hne : 1-x^12≠0 := sub_ne_zero.mpr (pow_lt_one₀ hx.le hx1 (by decide : 12≠0)).ne'
    field_simp [(hQ x).ne']; dsimp [Q]; ring

noncomputable def residue : ℝ := Real.pi^2 * Real.log (2+Real.sqrt 3)/54

theorem residue_pos : 0 < residue := by
  have h : 0 < Real.log (2+Real.sqrt 3) := Real.log_pos (by linarith [Real.sqrt_nonneg 3])
  dsimp [residue]; positivity

open Topology in
theorem moment_product_residue :
    Tendsto (fun s : ℂ => (s-1)*(L12 0 s * L12 1 s * L12 2 s * L12 3 s))
      (𝓝[≠] 1) (𝓝 (residue : ℂ)) := by
  convert L12_product_residue using 2
  rw [L12_at_one_first,L12_at_one_second,L12_at_one_third]
  dsimp [residue]
  push_cast
  have h : (Real.sqrt 3 : ℂ)^2=3 := by exact_mod_cast Real.sq_sqrt (show (0:ℝ)≤3 by norm_num)
  have hz : (Real.sqrt 3 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<3)).ne'
  field_simp
  linear_combination 18 * (Real.log (2+Real.sqrt 3) : ℝ) * h


noncomputable def dirichletReal (w : ℕ → ℝ) (s : ℝ) := ∑' n : ℕ, w n / (n:ℝ)^s

private lemma ofReal_dirichlet (w : ℕ → ℝ) (hw : w 0 = 0) (s : ℝ) :
    (dirichletReal w s : ℂ) = LSeries (fun n => (w n : ℂ)) s := by
  unfold dirichletReal LSeries
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl|hn
  · simp [hw,LSeries.term_def]
  · simp [LSeries.term_def,hn,Complex.ofReal_cpow (Nat.cast_nonneg n)]

open Topology in
private lemma real_pole_path : Tendsto (fun t : ℝ => (1+(t:ℂ))) (𝓝[>] 0) (𝓝[≠] 1) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : Continuous (fun t : ℝ => (1+(t:ℂ))) := by fun_prop
    simpa using (h.tendsto 0).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simp [ne_of_gt (show 0<t from ht)]

private lemma f_zero : f 0 = 0 := f_bad (by simp)
private lemma real_first (s : ℝ) : (dirichletReal f s : ℂ) = LSeries weight s :=
  ofReal_dirichlet f f_zero s

private lemma real_second (s : ℝ) :
    (dirichletReal (fun n => f n ^ 2) s : ℂ) = LSeries moment2 s := by
  rw [ofReal_dirichlet _ (by simp [f_zero])]
  congr 1
  funext n
  simp [moment2_apply,pow_two]

open Topology in
private theorem squared_real_limit : Tendsto (fun t : ℝ => t*(dirichletReal f (1+t))^2)
    (𝓝[>] 0) (𝓝 residue) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp (moment_product_residue.comp real_pole_path)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hr : 1 < (1 + (t:ℂ)).re := by simpa using (show 0<t from ht)
  rw [Function.comp_apply, Function.comp_apply, ← LSeries_weight_square hr]
  change ((1+(t:ℂ)-1) * LSeries weight (1+(t:ℂ)) ^ 2).re = _
  rw [show (1+(t:ℂ))=((1+t:ℝ):ℂ) by push_cast; rfl,← real_first]
  simp [← Complex.ofReal_pow]

open Topology in
theorem first_real_limit : Tendsto (fun t : ℝ => Real.sqrt t * dirichletReal f (1+t))
    (𝓝[>] 0) (𝓝 (Real.sqrt residue)) := by
  apply squared_real_limit.sqrt.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [Real.sqrt_mul (le_of_lt (show 0<t from ht)), Real.sqrt_sq]
  exact tsum_nonneg fun n => div_nonneg (nonneg_f _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

open Topology in
theorem second_real_limit :
    Tendsto (fun t : ℝ => t * dirichletReal (fun n => f n ^ 2) (1+t))
      (𝓝[>] 0) (𝓝 (residue/(Real.pi^2/9))) := by
  have hd : ContinuousAt (L12 0) 2 := ZMod.differentiableAt_LFunction _ _ (Or.inl (by norm_num))
    |>.continuousAt
  have path : Tendsto (fun t : ℝ => 2*(1+(t:ℂ))) (𝓝[>] 0) (𝓝 2) := by
    simpa using (tendsto_nhdsWithin_iff.mp real_pole_path).1.const_mul (2:ℂ)
  have hl := hd.tendsto.comp path
  rw [L12_principal_two] at hl
  have hn := (moment_product_residue.comp real_pole_path).div hl (by
    exact div_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) (by norm_num))
  have hh := Complex.continuous_re.continuousAt.tendsto.comp hn
  convert hh.congr' ?_ using 1
  · norm_cast
  filter_upwards [self_mem_nhdsWithin, hl.eventually_ne (show (Real.pi:ℂ)^2/9 ≠ 0 by
    exact div_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) (by norm_num))] with t ht hnz
  have hr : 1 < (1+(t:ℂ)).re := by simpa using (show 0<t from ht)
  change L12 0 (2*(1+(t:ℂ))) ≠ 0 at hnz
  change (((1+(t:ℂ)-1)*(L12 0 _ * L12 1 _ * L12 2 _ * L12 3 _)) / L12 0 (2*(1+(t:ℂ)))).re = _
  rw [← LSeries_weight_square hr,← LSeries_second hr,LSeries_squareIndicator hr,
    ← mul_assoc, mul_div_cancel_right₀ _ hnz,show (1+(t:ℂ))=((1+t:ℝ):ℂ) by push_cast; rfl,← real_second]
  simp


section Tauberian

open Set MeasureTheory Filter Topology

private noncomputable def node (t : ℝ) (n : ℕ) := (max (n:ℝ) 1)^(-t)
private noncomputable def mass (w : ℕ → ℝ) (a t : ℝ) (n : ℕ) := t^a * (w n/(n:ℝ)^(1+t))
private noncomputable def testSum (w : ℕ → ℝ) (a t : ℝ) (g : ℝ → ℝ) :=
  ∑' n, g (node t n) * mass w a t n
private noncomputable def gammaTest (a c : ℝ) (g : ℝ → ℝ) :=
  (c / Real.Gamma a) * ∫ x in Ioi (0:ℝ), g (Real.exp (-x)) * (Real.exp (-x)*x^(a-1))

private lemma node_mem {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : node t n ∈ Icc 0 1 :=
  ⟨Real.rpow_nonneg (by positivity : 0 ≤ max (n:ℝ) 1) _,
    Real.rpow_le_one_of_one_le_of_nonpos (le_max_right ..) (by linarith)⟩

private lemma test_summable {w : ℕ → ℝ} {a t : ℝ} {g : ℝ → ℝ} (ht : 0 < t)
    (hs : Summable fun n : ℕ => w n/(n:ℝ)^(1+t)) (hg : Continuous g) :
    Summable (fun n => g (node t n)*mass w a t n) := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0:ℝ) 1) hg.continuousOn
  have hm : Summable (mass w a t) := hs.mul_left _
  apply (hm.norm.mul_left C).of_norm_bounded
  intro n
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC _ (node_mem ht.le n)) (norm_nonneg _)

private lemma gamma_integrable {a : ℝ} (ha : 0<a) {g : ℝ → ℝ} (hg : Continuous g) :
    IntegrableOn (fun x => g (Real.exp (-x)) * (Real.exp (-x)*x^(a-1))) (Ioi 0) := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0:ℝ) 1) hg.continuousOn
  apply (Real.GammaIntegral_convergent ha).bdd_mul (c := C) (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact hC _ ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith [show 0<x from hx])⟩

private lemma gamma_moment {a : ℝ} (ha : 0<a) (c : ℝ) (k : ℕ) :
    gammaTest a c (·^k) = c / ((k:ℝ)+1)^a := by
  have eq (x : ℝ) : Real.exp (-x)^k * (Real.exp (-x)*x^(a-1)) =
      x^(a-1) * Real.exp (-(((k:ℝ)+1)*x)) := by
    rw [← Real.exp_nat_mul,← mul_assoc,← Real.exp_add]
    rw [mul_comm]
    congr 2 <;> ring
  simp only [gammaTest,eq,Real.integral_rpow_mul_exp_neg_mul_Ioi ha (show 0<(k:ℝ)+1 by positivity)]
  rw [Real.div_rpow (by norm_num) (by positivity),Real.one_rpow]
  field_simp [(Real.Gamma_pos_of_pos ha).ne']

private lemma test_moment {w : ℕ → ℝ} {a c : ℝ} (hw : w 0=0)
    (h : Tendsto (fun t : ℝ => t^a * dirichletReal w (1+t)) (𝓝[>] 0) (𝓝 c)) (k : ℕ) :
    Tendsto (fun t => testSum w a t (·^k)) (𝓝[>] 0) (𝓝 (c/((k:ℝ)+1)^a)) := by
  let d := (k:ℝ)+1
  have hd : 0<d := by dsimp [d]; positivity
  have hp : Tendsto (fun t : ℝ => d*t) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_,?_⟩
    · simpa only [mul_zero] using ((show Continuous (fun t : ℝ => d*t) by fun_prop).tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht using mul_pos hd (show 0<t from ht)
  apply ((h.comp hp).div_const (d^a)).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change (d*t)^a * dirichletReal w (1+d*t) / d^a = _
  rw [Real.mul_rpow hd.le (le_of_lt (show 0<t from ht)),mul_assoc,mul_div_cancel_left₀ _
    (Real.rpow_pos_of_pos hd a).ne']
  rw [dirichletReal,← tsum_mul_left,testSum]
  refine tsum_congr fun n => ?_
  by_cases hn : n=0
  · simp [hn,hw,mass]
  have hp : 0<(n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have h1 : 1≤(n:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  rw [node,max_eq_left h1,← Real.rpow_mul_natCast hp.le]
  simp only [mass,div_eq_mul_inv,← Real.rpow_neg hp.le]
  have e : -(1+d*t) = (-t)*(k:ℝ) + -(1+t) := by dsimp [d]; ring
  rw [e,Real.rpow_add hp]
  ring


private lemma test_poly {w : ℕ → ℝ} {a c : ℝ} (hw : w 0=0) (ha : 0<a)
    (hs : ∀ t : ℝ, 0<t → Summable fun n : ℕ => w n/(n:ℝ)^(1+t))
    (h : Tendsto (fun t : ℝ => t^a * dirichletReal w (1+t)) (𝓝[>] 0) (𝓝 c))
    (p : Polynomial ℝ) :
    Tendsto (fun t => testSum w a t (fun x => p.eval x)) (𝓝[>] 0)
      (𝓝 (gammaTest a c (fun x => p.eval x))) := by
  induction p using Polynomial.induction_on' with
  | add p q ip iq =>
    have e : gammaTest a c (fun x => (p+q).eval x) =
        gammaTest a c (fun x => p.eval x) + gammaTest a c (fun x => q.eval x) := by
      simp only [gammaTest,Polynomial.eval_add,add_mul,integral_add
        (gamma_integrable ha p.continuous) (gamma_integrable ha q.continuous),mul_add]
    rw [e]
    apply (ip.add iq).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [testSum,Polynomial.eval_add,add_mul, Summable.tsum_add
      (test_summable ht (hs t ht) p.continuous) (test_summable ht (hs t ht) q.continuous)]
  | monomial k b =>
    simp only [Polynomial.eval_monomial, gammaTest,testSum,mul_assoc,tsum_mul_left,integral_const_mul]
    rw [mul_left_comm (c / Real.Gamma a) b]
    change Tendsto _ _ (𝓝 (b*gammaTest a c (·^k)))
    rw [gamma_moment ha]
    exact (test_moment hw h k).const_mul b

private lemma test_continuous {w : ℕ → ℝ} {a c : ℝ} (hw : w 0=0) (ha : 0<a)
    (hn : ∀ n, 0 ≤ w n) (hc : 0 ≤ c)
    (hs : ∀ t : ℝ, 0<t → Summable fun n : ℕ => w n/(n:ℝ)^(1+t))
    (h : Tendsto (fun t : ℝ => t^a * dirichletReal w (1+t)) (𝓝[>] 0) (𝓝 c))
    {g : ℝ → ℝ} (hg : Continuous g) :
    Tendsto (fun t => testSum w a t g) (𝓝[>] 0) (𝓝 (gammaTest a c g)) := by
  have hmono {p q : ℝ → ℝ} (hp : Continuous p) (hq : Continuous q)
      (hpq : ∀ x ∈ Icc 0 1, p x ≤ q x) :
      gammaTest a c p ≤ gammaTest a c q := by
    apply mul_le_mul_of_nonneg_left _ (div_nonneg hc (Real.Gamma_pos_of_pos ha).le)
    apply integral_mono_ae (gamma_integrable ha hp) (gamma_integrable ha hq)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hx
    apply mul_le_mul_of_nonneg_right (hpq _ ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (by linarith)⟩)
    positivity
  have hmonot {p q : ℝ → ℝ} (hp : Continuous p) (hq : Continuous q)
      (hpq : ∀ x ∈ Icc 0 1, p x ≤ q x) {t : ℝ} (ht : 0<t) :
      testSum w a t p ≤ testSum w a t q := by
    apply Summable.tsum_le_tsum _ (test_summable ht (hs t ht) hp) (test_summable ht (hs t ht) hq)
    intro n
    apply mul_le_mul_of_nonneg_right (hpq _ (node_mem ht.le _))
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (div_nonneg (hn _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hshift (p : ℝ → ℝ) (hp : Continuous p) (d : ℝ) : gammaTest a c (fun x => p x+d) =
      gammaTest a c p + d*c := by
    have hh := gamma_moment ha c 0
    simp only [pow_zero,Nat.cast_zero,zero_add,Real.one_rpow,div_one] at hh
    simp only [gammaTest,add_mul,integral_add (gamma_integrable ha hp)
      (gamma_integrable ha (continuous_const (y := d))), integral_const_mul,mul_add]
    simp only [gammaTest,one_mul] at hh
    rw [mul_left_comm _ d,hh]
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ := ε/(4*(c+1))
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨p,hp⟩ := exists_polynomial_near_of_continuousOn 0 1 g hg.continuousOn δ hδ
  let lo := p - Polynomial.C δ
  let hi := p + Polynomial.C δ
  have hlo (x : ℝ) (hx : x ∈ Icc 0 1) : lo.eval x ≤ g x := by
    simp only [lo,Polynomial.eval_sub,Polynomial.eval_C]
    linarith [(abs_lt.mp (hp x hx)).2]
  have hhi (x : ℝ) (hx : x ∈ Icc 0 1) : g x ≤ hi.eval x := by
    simp only [hi,Polynomial.eval_add,Polynomial.eval_C]
    linarith [(abs_lt.mp (hp x hx)).1]
  have Hlo := hmono lo.continuous hg hlo
  have Hhi := hmono hg hi.continuous hhi
  have Hd : gammaTest a c (fun x => hi.eval x) - gammaTest a c (fun x => lo.eval x) = 2*δ*c := by
    simp only [hi,lo,Polynomial.eval_add, Polynomial.eval_sub,Polynomial.eval_C]
    simp only [sub_eq_add_neg,hshift _ p.continuous]
    ring
  have he : 2*δ*c < ε/2 := by dsimp [δ]; field_simp; nlinarith
  filter_upwards [self_mem_nhdsWithin, Metric.tendsto_nhds.mp (test_poly hw ha hs h lo) (ε/2) (by positivity),
    Metric.tendsto_nhds.mp (test_poly hw ha hs h hi) (ε/2) (by positivity)] with t ht h1 h2
  have L := hmonot lo.continuous hg hlo ht
  have H := hmonot hg hi.continuous hhi ht
  rw [Real.dist_eq,abs_lt] at h1 h2 ⊢
  constructor <;> linarith


private noncomputable def cut (l u x : ℝ) :=
  min 1 (max 0 ((x-Real.exp (-u))/(Real.exp (-l)-Real.exp (-u)))) / max (Real.exp (-u)) x

private lemma cut_cont (l u : ℝ) : Continuous (cut l u) := by
  unfold cut
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro x
  exact (lt_of_lt_of_le (Real.exp_pos _) (le_max_left _ x)).ne'

private lemma cut_bounds {l u x : ℝ} (hx : 0<x) :
    0 ≤ cut l u x * x ∧ cut l u x * x ≤ 1 := by
  unfold cut
  have hpos : 0 < max (Real.exp (-u)) x := lt_of_lt_of_le hx (le_max_right ..)
  constructor
  · positivity
  · rw [div_mul_eq_mul_div,div_le_iff₀ hpos,one_mul]
    exact (mul_le_of_le_one_left hx.le (min_le_left ..)).trans (le_max_right ..)

private lemma cut_one {l u x : ℝ} (h : l<u) (hx : Real.exp (-l) ≤ x) : cut l u x*x=1 := by
  have he : Real.exp (-u)<Real.exp (-l) := Real.exp_lt_exp.mpr (by linarith)
  have hr : 1≤(x-Real.exp (-u))/(Real.exp (-l)-Real.exp (-u)) :=
    (one_le_div (by linarith)).mpr (by linarith)
  simp [cut,min_eq_left (le_trans hr (le_max_right ..)),max_eq_right (he.le.trans hx),
    (lt_of_lt_of_le (Real.exp_pos _) hx).ne']

private lemma cut_zero {l u x : ℝ} (h : l<u) (hx : x ≤ Real.exp (-u)) : cut l u x=0 := by
  have he : Real.exp (-u)<Real.exp (-l) := Real.exp_lt_exp.mpr (by linarith)
  simp [cut,max_eq_left (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (sub_nonneg.mpr he.le))]

private noncomputable def intervalPower (a v : ℝ) :=
  (Ioc (0:ℝ) v).indicator (fun x : ℝ => x^(a-1))

private lemma intervalPower_integrable {a v : ℝ} (ha : 0<a) (hv : 0≤v) :
    IntegrableOn (intervalPower a v) (Ioi 0) := by
  rw [intervalPower,integrableOn_indicator_iff measurableSet_Ioc,
    inter_eq_left.mpr (show Ioc (0:ℝ) v ⊆ Ioi 0 from fun _ hx => hx.1)]
  exact (intervalIntegral.intervalIntegrable_rpow' (a:=0) (b:=v) (by linarith : -1<a-1)).1

private lemma intervalPower_integral {a v : ℝ} (ha : 0<a) (hv : 0≤v) :
    ∫ x in Ioi 0, intervalPower a v x = v^a/a := by
  rw [intervalPower,setIntegral_indicator measurableSet_Ioc,
    inter_eq_right.mpr (show Ioc (0:ℝ) v ⊆ Ioi 0 from fun _ hx => hx.1),
    ← intervalIntegral.integral_of_le hv,integral_rpow (.inl (by linarith)),
    sub_add_cancel, Real.zero_rpow ha.ne',sub_zero]

private lemma gamma_cut {a c l u : ℝ} (ha : 0<a) (hc : 0≤c) (hl : 0<l) (hu : l<u) :
    (c/Real.Gamma a)*(l^a/a) ≤ gammaTest a c (cut l u) ∧
    gammaTest a c (cut l u) ≤ (c/Real.Gamma a)*(u^a/a) := by
  have hpos := div_nonneg hc (Real.Gamma_pos_of_pos ha).le
  rw [← intervalPower_integral ha hl.le, ← intervalPower_integral ha (hl.trans hu).le]
  constructor
  · apply mul_le_mul_of_nonneg_left _ hpos
    apply integral_mono_ae (intervalPower_integrable ha hl.le) (gamma_integrable ha (cut_cont l u))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0<x := hx
    rw [← mul_assoc]
    by_cases hxl : x≤l
    · rw [intervalPower,indicator_of_mem (show x ∈ Ioc 0 l from ⟨hx,hxl⟩),
        cut_one hu (Real.exp_le_exp.mpr (by linarith)),one_mul]
    · rw [intervalPower,indicator_of_notMem (show x ∉ Ioc 0 l from fun h => hxl h.2)]
      exact mul_nonneg (cut_bounds (Real.exp_pos _)).1 (Real.rpow_nonneg hx0.le _)
  · apply mul_le_mul_of_nonneg_left _ hpos
    apply integral_mono_ae (gamma_integrable ha (cut_cont l u)) (intervalPower_integrable ha (hl.trans hu).le)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0<x := hx
    rw [← mul_assoc]
    by_cases hxu : x≤u
    · rw [intervalPower,indicator_of_mem (show x ∈ Ioc 0 u from ⟨hx,hxu⟩)]
      exact mul_le_of_le_one_left (Real.rpow_nonneg hx0.le _) (cut_bounds (Real.exp_pos _)).2
    · rw [intervalPower,indicator_of_notMem (show x ∉ Ioc 0 u from fun h => hxu h.2),
        cut_zero hu (Real.exp_le_exp.mpr (by linarith)),zero_mul,zero_mul]


private noncomputable def harmonicMean (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, w n / n

private lemma test_cut_sandwich {w : ℕ → ℝ} {a l u : ℝ} (hw : w 0=0) (hn : ∀ n, 0≤w n)
    (hs : ∀ t : ℝ, 0<t → Summable fun n : ℕ => w n/(n:ℝ)^(1+t))
    (hl : l<1) (hu : 1<u) {N : ℕ} (hN : 1<N) :
    let t := (Real.log N)⁻¹
    testSum w a t (cut l 1) ≤ t^a * harmonicMean w N ∧
    t^a * harmonicMean w N ≤ testSum w a t (cut 1 u) := by
  intro t
  have hN' : 1 < (N:ℝ) := by exact_mod_cast hN
  have hlog := Real.log_pos hN'
  have ht : 0<t := inv_pos.mpr hlog
  let b (n : ℕ) : ℝ := if n ∈ Finset.Icc 1 N then t^a * (w n/n) else 0
  have hb (n : ℕ) (h : n ∉ Finset.Icc 1 N) : b n=0 := if_neg h
  have H : ∑' n, b n = t^a * harmonicMean w N := by
    rw [tsum_eq_sum hb,harmonicMean,Finset.mul_sum]
    exact Finset.sum_congr rfl fun n hn => if_pos hn
  rw [← H]
  have estimates (n : ℕ) :
      cut l 1 (node t n)*mass w a t n ≤ b n ∧ b n ≤ cut 1 u (node t n)*mass w a t n := by
    by_cases h0 : n=0
    · subst n; simp [mass,hw,b]
    have hn1 : 1≤n := Nat.one_le_iff_ne_zero.mpr h0
    have hn1' : 1≤(n:ℝ) := by exact_mod_cast hn1
    have hn' : 0<(n:ℝ) := by linarith
    have hp : 0 < node t n := by rw [node,max_eq_left hn1']; positivity
    have e : mass w a t n = node t n * (t^a * (w n/n)) := by
      rw [mass,node,max_eq_left hn1',Real.rpow_neg hn'.le,Real.rpow_add hn',Real.rpow_one]
      ring
    have cmp : Real.exp (-1) ≤ node t n ↔ n≤N := by
      rw [node,max_eq_left hn1',Real.rpow_def_of_pos hn',Real.exp_le_exp]
      change -1 ≤ Real.log n * -(Real.log N)⁻¹ ↔ n≤N
      rw [mul_neg, neg_le_neg_iff, ← div_eq_mul_inv, div_le_one hlog,
        Real.log_le_log_iff hn' (by positivity)]
      exact_mod_cast Iff.rfl
    have hpos : 0 ≤ t^a*(w n/n) := mul_nonneg (Real.rpow_nonneg ht.le _) (div_nonneg (hn _) hn'.le)
    rw [e,← mul_assoc (cut l 1 _),← mul_assoc (cut 1 u _)]
    by_cases hnN : n≤N
    · rw [show b n=t^a*(w n/n) from if_pos (Finset.mem_Icc.mpr ⟨hn1,hnN⟩),
        cut_one hu (cmp.mpr hnN), one_mul]
      exact ⟨mul_le_of_le_one_left hpos (cut_bounds hp).2,le_rfl⟩
    · rw [show b n=0 from if_neg (fun hm => hnN (Finset.mem_Icc.mp hm).2),
        cut_zero hl (le_of_not_ge (fun h => hnN (cmp.mp h))),zero_mul,zero_mul]
      exact ⟨le_rfl,mul_nonneg (cut_bounds hp).1 hpos⟩
  exact ⟨(test_summable ht (hs _ ht) (cut_cont l 1)).tsum_le_tsum (fun n => (estimates n).1)
    (summable_of_ne_finset_zero hb),(summable_of_ne_finset_zero hb).tsum_le_tsum (fun n => (estimates n).2)
    (test_summable ht (hs _ ht) (cut_cont 1 u))⟩

private theorem harmonic_asymptotic {w : ℕ → ℝ} {a c : ℝ} (hw : w 0=0) (ha : 0<a)
    (hn : ∀ n, 0≤w n) (hc : 0≤c)
    (hs : ∀ t : ℝ, 0<t → Summable fun n : ℕ => w n/(n:ℝ)^(1+t))
    (h : Tendsto (fun t : ℝ => t^a * dirichletReal w (1+t)) (𝓝[>] 0) (𝓝 c)) :
    Tendsto (fun N : ℕ => harmonicMean w N / (Real.log N)^a) atTop (𝓝 (c/Real.Gamma (a+1))) := by
  have e : c/Real.Gamma (a+1) = c/Real.Gamma a * ((1:ℝ)^a/a) := by
    rw [Real.Gamma_add_one ha.ne',Real.one_rpow]; ring
  let T (N : ℕ) := (Real.log N)⁻¹
  have hT : Tendsto T atTop (𝓝[>] 0) :=
    tendsto_inv_atTop_nhdsGT_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have B (l u : ℝ) (hl : l<1) (hu : 1<u) : ∀ᶠ N : ℕ in atTop,
      testSum w a (T N) (cut l 1) ≤ harmonicMean w N/(Real.log N)^a ∧
      harmonicMean w N/(Real.log N)^a ≤ testSum w a (T N) (cut 1 u) := by
    filter_upwards [eventually_gt_atTop 1] with N hN
    simpa only [T,Real.inv_rpow (Real.log_nonneg (by exact_mod_cast hN.le : 1≤(N:ℝ))), div_eq_mul_inv,
      mul_comm] using test_cut_sandwich (a:=a) hw hn hs hl hu hN
  have V : ContinuousAt (fun v : ℝ => c/Real.Gamma a * (v^a/a)) 1 := by fun_prop (disch := first | positivity | exact Or.inr ha.le)
  rw [e,tendsto_order]
  constructor
  · intro x hx
    obtain ⟨l,⟨hl0,hl1⟩,hlx⟩ := ((eventually_gt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds |>.and
      (self_mem_nhdsWithin (a:=(1:ℝ)) (s:=Iio 1)) |>.and
      ((V.tendsto.eventually_const_lt hx).filter_mono nhdsWithin_le_nhds)).exists
    have hL := (test_continuous hw ha hn hc hs h (cut_cont l 1)).comp hT
    filter_upwards [hL.eventually_const_lt (hlx.trans_le (gamma_cut ha hc hl0 hl1).1),B l 2 hl1 (by norm_num)]
      with N h1 h2 using h1.trans_le h2.1
  · intro x hx
    obtain ⟨u,hu,hux⟩ := ((show ∀ᶠ u : ℝ in 𝓝[>] 1, 1<u from self_mem_nhdsWithin).and
      ((V.tendsto.eventually_lt_const hx).filter_mono nhdsWithin_le_nhds)).exists
    have hU := (test_continuous hw ha hn hc hs h (cut_cont 1 u)).comp hT
    filter_upwards [hU.eventually_lt_const ((gamma_cut ha hc (by norm_num : (0:ℝ)<1) hu).2.trans_lt hux),
      B 0 u (by norm_num) hu] with N h1 h2 using h2.2.trans_lt h1


private lemma harmonic_scaled {w : ℕ → ℝ} {a b : ℝ} (M : ℕ) (hM : 0<M)
    (H : Tendsto (fun N : ℕ => harmonicMean w N/(Real.log N)^a) atTop (𝓝 b)) :
    Tendsto (fun N : ℕ => harmonicMean w (N/M)/(Real.log N)^a) atTop (𝓝 b) := by
  have hM' : 0<(M:ℝ) := by exact_mod_cast hM
  have divpath : Tendsto (fun N : ℕ => (N:ℝ)/M) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const hM'
  have hfloor : Tendsto (fun N : ℕ => N/M) atTop atTop := by
    simpa only [Function.comp_def,Nat.floor_div_natCast,Nat.floor_natCast] using
      (tendsto_nat_floor_atTop.comp divpath)
  have hrat : Tendsto (fun N : ℕ => ((N/M : ℕ):ℝ)/N) atTop (𝓝 (1/(M:ℝ))) := by
    apply ((tendsto_nat_floor_div_atTop.comp divpath).div_const (M:ℝ)).congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    simp only [Function.comp_apply,Nat.floor_div_natCast,Nat.floor_natCast]
    field_simp
  have hL : Tendsto (fun N : ℕ => Real.log (N/M : ℕ) / Real.log N) atTop (𝓝 1) := by
    have h := (hrat.log (by positivity)).div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    apply (show Tendsto _ _ (𝓝 (1:ℝ)) from (by simpa using h.add_const 1)).congr'
    filter_upwards [hfloor.eventually_gt_atTop 1,eventually_gt_atTop 1] with N hm hn
    have h1 : 1<(N:ℝ) := by exact_mod_cast hn
    have h2 : 1<((N/M:ℕ):ℝ) := by exact_mod_cast hm
    simp only [Function.comp_apply, Real.log_div (by positivity : ((N/M : ℕ):ℝ)≠0)
      (by positivity : (N:ℝ)≠0)]
    field_simp [(Real.log_pos h1).ne'] <;> ring
  have hR := hL.rpow_const (p:=a) (.inl (by norm_num))
  rw [Real.one_rpow] at hR
  apply (show Tendsto _ _ (𝓝 b) from (by simpa using (H.comp hfloor).mul hR)).congr'
  filter_upwards [hfloor.eventually_gt_atTop 1,eventually_gt_atTop 1] with N hm hn
  have h1 : 0<Real.log N := Real.log_pos (by exact_mod_cast hn)
  have h2 : 0<Real.log (N/M : ℕ) := Real.log_pos (by exact_mod_cast hm)
  simp only [Function.comp_apply,Real.div_rpow h2.le h1.le]
  field_simp

private noncomputable def weightedSum (w : ℕ → ℝ) (k : ℝ → ℝ) (N : ℕ) :=
  ∑ d ∈ Finset.Icc 1 N, (w d/d)*k ((N:ℝ)/d)

private lemma weighted_error {w : ℕ → ℝ} {k : ℝ → ℝ} {α ε C : ℝ} {M : ℕ}
    (hn : ∀ n, 0≤w n) (hε : 0≤ε) (hM : 0<M)
    (hclose : ∀ x : ℝ, M≤x → |k x-α|≤ε) (hbound : ∀ x : ℝ, 1≤x → |k x-α|≤C) (N : ℕ) :
    |weightedSum w k N - α*harmonicMean w N| ≤
      ε*harmonicMean w N+C*(harmonicMean w N-harmonicMean w (N/M)) := by
  let S := Finset.Icc 1 N
  let T := Finset.Icc 1 (N/M)
  have sub : T ⊆ S := Finset.Icc_subset_Icc le_rfl (Nat.div_le_self ..)
  let q (d : ℕ) := w d / d
  have hq (d : ℕ) : 0≤q d := div_nonneg (hn _) (Nat.cast_nonneg _)
  have e : weightedSum w k N - α*harmonicMean w N =
      ∑ d ∈ S, q d*(k ((N:ℝ)/d)-α) := by
    simp only [weightedSum,harmonicMean,Finset.mul_sum,← Finset.sum_sub_distrib,S,q]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have big (d : ℕ) (hd : d ∈ S) : 1≤(N:ℝ)/d := by
    obtain ⟨hd0,hdN⟩ := Finset.mem_Icc.mp hd
    exact (one_le_div (by exact_mod_cast (show 0<d by omega))).mpr (by exact_mod_cast hdN)
  have small (d : ℕ) (hd : d ∈ T) : M≤(N:ℝ)/d := by
    obtain ⟨hd0,hdM⟩ := Finset.mem_Icc.mp hd
    apply (le_div_iff₀ (by exact_mod_cast (show 0<d by omega))).mpr
    exact_mod_cast (show M*d≤N by simpa [mul_comm] using (Nat.le_div_iff_mul_le hM).mp hdM)
  have tail : ∑ d ∈ S \ T, q d = harmonicMean w N-harmonicMean w (N/M) :=
    eq_sub_of_add_eq (Finset.sum_sdiff (f:=q) sub)
  rw [e]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  simp only [abs_mul,abs_of_nonneg (hq _)]
  rw [← Finset.sum_sdiff (f:=fun d => q d*|k ((N:ℝ)/d)-α|) sub]
  calc
    _ ≤ C*(∑ d ∈ S \ T, q d) + ε*(∑ d ∈ T, q d) := by
      rw [Finset.mul_sum,Finset.mul_sum]
      apply add_le_add <;> apply Finset.sum_le_sum
      · intro d hd; rw [mul_comm C]; exact mul_le_mul_of_nonneg_left (hbound _ (big _ (Finset.mem_sdiff.mp hd).1)) (hq _)
      · intro d hd; rw [mul_comm ε]; exact mul_le_mul_of_nonneg_left (hclose _ (small _ hd)) (hq _)
    _ ≤ _ := by
      rw [tail,add_comm]
      exact add_le_add (mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg sub (fun d _ _ => hq d)) hε) le_rfl


private lemma weighted_limit {w : ℕ → ℝ} {k : ℝ → ℝ} {a b α C : ℝ} (hn : ∀ n, 0≤w n)
    (hb : 0≤b) (H : Tendsto (fun N : ℕ => harmonicMean w N/(Real.log N)^a) atTop (𝓝 b))
    (hk : Tendsto k atTop (𝓝 α)) (hbound : ∀ x : ℝ, 1≤x → |k x-α|≤C) :
    Tendsto (fun N : ℕ => weightedSum w k N/(Real.log N)^a) atTop (𝓝 (α*b)) := by
  suffices h : Tendsto (fun N : ℕ => (weightedSum w k N-α*harmonicMean w N)/(Real.log N)^a)
      atTop (𝓝 0) by
    simpa only [zero_add] using (h.add (H.const_mul α)).congr
      (fun N => by ring)
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ := ε/(2*(b+1))
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨r,hr⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp hk δ hδ)
  obtain ⟨M,hM⟩ := exists_nat_gt (max r 1)
  have hM' : 0<M := by exact_mod_cast (lt_trans (show (0:ℝ) < max r 1 from lt_of_lt_of_le zero_lt_one (le_max_right ..)) hM)
  have hclose (x : ℝ) (hx : M≤x) : |k x-α|≤δ :=
    (hr _ ((le_max_left _ _).trans (hM.le.trans hx))).le
  have H2 := harmonic_scaled M hM' H
  have HB := (H.const_mul δ).add ((H.sub H2).const_mul C)
  have he : δ*b+C*(b-b)<ε := by dsimp [δ]; simp only [sub_self,mul_zero,add_zero]; field_simp; nlinarith
  filter_upwards [HB.eventually_lt_const he,eventually_gt_atTop 1] with N h1 hN
  have hpos : 0<(Real.log N)^a := Real.rpow_pos_of_pos (Real.log_pos (by exact_mod_cast hN)) _
  rw [Real.dist_eq,sub_zero,abs_div,abs_of_pos hpos]
  apply (div_le_div_of_nonneg_right (weighted_error hn hδ.le hM' hclose hbound N) hpos.le).trans_lt
  convert h1 using 1 <;> ring

private noncomputable def prefixSum (w : ℕ → ℝ) (N : ℕ) := ∑ n ∈ Finset.Icc 1 N, w n
private noncomputable def meanKernel (P : ℕ → ℝ) (x : ℝ) := (P ⌊x⌋₊ + Real.log x)/x

private lemma kernel_limit {P : ℕ → ℝ} {α : ℝ} (h : Tendsto (fun n : ℕ => P n/n) atTop (𝓝 α)) :
    Tendsto (meanKernel P) atTop (𝓝 α) ∧ ∃ C : ℝ, ∀ x : ℝ, 1≤x → |meanKernel P x-α|≤C := by
  have hlog : Tendsto (fun x : ℝ => Real.log x/x) atTop (𝓝 0) :=
    (Asymptotics.isLittleO_iff_tendsto' (by filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx using fun h => False.elim (hx.ne' h))).mp Real.isLittleO_log_id_atTop
  have fac (x : ℝ) (hx : 1≤x) : meanKernel P x =
      (P ⌊x⌋₊/⌊x⌋₊)*((⌊x⌋₊:ℝ)/x)+Real.log x/x := by
    have hp : (0:ℝ)<⌊x⌋₊ := by exact_mod_cast (Nat.floor_pos.mpr hx)
    dsimp [meanKernel]; field_simp
  constructor
  · have H := ((h.comp tendsto_nat_floor_atTop).mul (tendsto_nat_floor_div_atTop (R:=ℝ))).add hlog
    simp only [mul_one,add_zero] at H
    exact H.congr' ((eventually_ge_atTop 1).mono fun x hx => (fac x hx).symm)
  · obtain ⟨C,hC⟩ := h.abs.bddAbove_range
    refine ⟨C+1+|α|,?_⟩
    intro x hx
    have hx0 : 0<x := by linarith
    have H : |P ⌊x⌋₊ / ↑⌊x⌋₊| ≤ C := hC (mem_range_self _)
    have hrat : (⌊x⌋₊:ℝ)/x ≤ 1 := (div_le_one hx0).mpr (Nat.floor_le hx0.le)
    have hl : Real.log x/x ≤ 1 := (div_le_one hx0).mpr (by linarith [Real.log_le_sub_one_of_pos hx0])
    rw [fac x hx]
    calc
      _ ≤ |(P ⌊x⌋₊/⌊x⌋₊)*((⌊x⌋₊:ℝ)/x)+Real.log x/x|+|α| := abs_sub _ _
      _ ≤ (|(P ⌊x⌋₊/⌊x⌋₊)*((⌊x⌋₊:ℝ)/x)|+|Real.log x/x|)+|α| := by gcongr; exact abs_add_le .. 
      _ ≤ _ := by
        rw [abs_mul,abs_of_nonneg (show 0≤(⌊x⌋₊:ℝ)/x by positivity),
          abs_of_nonneg (div_nonneg (Real.log_nonneg hx) hx0.le)]
        linarith [mul_le_of_le_one_right (abs_nonneg (P ⌊x⌋₊/↑⌊x⌋₊)) hrat]

open Finset in
private theorem rearr (N : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ n ∈ Finset.Ioc 0 N, ∑ d ∈ n.divisors, F d (n / d) =
      ∑ d ∈ Finset.Ioc 0 N, ∑ m ∈ Finset.Ioc 0 (N / d), F d m := by
  rw [Finset.sum_comm' (t' := Finset.Ioc 0 N) (s' := fun d => (Finset.Ioc 0 N).filter (d ∣ ·))]
  · apply Finset.sum_congr rfl
    intro d hd
    have hd0 : 0 < d := by simp only [Finset.mem_Ioc] at hd; omega
    symm
    apply Finset.sum_nbij' (fun m => d * m) (fun n => n / d)
    · intro m hm
      simp only [Finset.mem_Ioc, mem_filter] at hm ⊢
      refine ⟨⟨Nat.mul_pos hd0 hm.1, ?_⟩, dvd_mul_right _ _⟩
      have := (Nat.le_div_iff_mul_le hd0).1 hm.2
      linarith [Nat.mul_comm m d]
    · intro n hn
      simp only [Finset.mem_Ioc, mem_filter] at hn ⊢
      obtain ⟨⟨h1, h2⟩, k, rfl⟩ := hn
      rw [Nat.mul_div_cancel_left _ hd0]
      refine ⟨Nat.pos_of_mul_pos_left h1 |> fun h => ?_, ?_⟩
      · rcases Nat.eq_zero_or_pos k with hk | hk
        · subst hk; simp at h1
        · exact hk
      · rw [Nat.le_div_iff_mul_le hd0]; linarith [Nat.mul_comm k d]
    · intro m _
      simp only [Nat.mul_div_cancel_left _ hd0]
    · intro n hn
      simp only [mem_filter] at hn
      exact Nat.mul_div_cancel' hn.2
    · intro m _
      simp only [Nat.mul_div_cancel_left _ hd0]
  · intro n d
    simp only [Finset.mem_Ioc, Nat.mem_divisors, mem_filter]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, _⟩
      exact ⟨⟨⟨h1, h2⟩, h3⟩, Nat.pos_of_dvd_of_pos h3 h1, (Nat.le_of_dvd h1 h3).trans h2⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, _, _⟩
      exact ⟨⟨h1, h2⟩, h3, by omega⟩


private lemma log_prefix {w Λ : ℕ → ℝ} (logconv : ∀ n : ℕ, Real.log n*w n =
    ∑ ij ∈ n.divisorsAntidiagonal, w ij.1 * Λ ij.2) {N : ℕ} (hN : 0<N) :
    weightedSum w (meanKernel (prefixSum Λ)) N = Real.log N * prefixSum w N/N := by
  let S := Finset.Icc 1 N
  have H : ∑ d ∈ S, w d*prefixSum Λ (N/d) = ∑ n ∈ S, Real.log n*w n := by
    simp only [S,prefixSum,Finset.mul_sum,logconv,Nat.sum_divisorsAntidiagonal (fun i j => w i*Λ j),
      show ∀ m : ℕ, Finset.Icc 1 m=Finset.Ioc 0 m from fun m => Finset.Icc_succ_left_eq_Ioc 0 m]
    exact (rearr N (fun i j => w i*Λ j)).symm
  rw [weightedSum,prefixSum,Finset.mul_sum]
  change (∑ d ∈ S, w d/d * meanKernel (prefixSum Λ) ((N:ℝ)/d)) = (∑ n ∈ S, Real.log N*w n)/(N:ℝ)
  apply (eq_div_iff (by exact_mod_cast hN.ne' : (N:ℝ)≠0)).mpr
  rw [Finset.sum_mul]
  calc
    _ = ∑ d ∈ S, (w d*prefixSum Λ (N/d) + w d*(Real.log N - Real.log d)) := by
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd' : (d:ℝ)≠0 := by exact_mod_cast (show d≠0 by have := (Finset.mem_Icc.mp hd).1; omega)
      have hN' : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
      rw [meanKernel,Nat.floor_div_natCast,Nat.floor_natCast,Real.log_div hN' hd']
      field_simp
    _ = _ := by
      rw [Finset.sum_add_distrib,H,← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun n _ => by ring

private theorem mean_from_log {w Λ : ℕ → ℝ} {a c α : ℝ} (hw : w 0=0) (ha : 0<a)
    (hn : ∀ n, 0≤w n) (hc : 0≤c)
    (hs : ∀ t : ℝ, 0<t → Summable fun n : ℕ => w n/(n:ℝ)^(1+t))
    (h : Tendsto (fun t : ℝ => t^a * dirichletReal w (1+t)) (𝓝[>] 0) (𝓝 c))
    (logconv : ∀ n : ℕ, Real.log n*w n = ∑ ij ∈ n.divisorsAntidiagonal, w ij.1 * Λ ij.2)
    (pnt : Tendsto (fun N : ℕ => prefixSum Λ N/N) atTop (𝓝 α)) :
    Tendsto (fun N : ℕ => (Real.log N * prefixSum w N / N)/(Real.log N)^a)
      atTop (𝓝 (α*(c/Real.Gamma (a+1)))) := by
  obtain ⟨hk,C,hC⟩ := kernel_limit pnt
  have hp := weighted_limit hn (div_nonneg hc (Real.Gamma_pos_of_pos (by linarith : 0<a+1)).le)
    (harmonic_asymptotic hw ha hn hc hs h) hk hC
  apply hp.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [log_prefix logconv hN]

private lemma prefix_of_range {g : ℕ → ℝ} {α : ℝ} (hg : g 0=0)
    (h : Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, g k)/N) atTop (𝓝 α)) :
    Tendsto (fun N : ℕ => prefixSum g N/N) atTop (𝓝 α) := by
  have he (N : ℕ) : prefixSum g N = ∑ k ∈ Finset.range (N+1), g k := by
    rw [prefixSum,← Finset.Ico_add_one_right_eq_Icc,Finset.sum_Ico_eq_sub _ (by omega),
      Finset.sum_range_one,hg,sub_zero]
  have hrat : Tendsto (fun N : ℕ => ((N+1:ℕ):ℝ)/N) atTop (𝓝 1) := by
    have h0 := (tendsto_const_nhds (x:=(1:ℝ))).div_atTop (tendsto_natCast_atTop_atTop (R:=ℝ))
    apply (show Tendsto _ _ (𝓝 (1:ℝ)) from (by simpa using h0.add_const 1)).congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    push_cast; field_simp; ring
  have H := (h.comp (tendsto_add_atTop_nat 1)).mul hrat
  simp only [mul_one] at H
  apply H.congr
  intro N
  rw [he]
  simp only [Function.comp_def]; field_simp

end Tauberian


section LiftSquares

private noncomputable def liftSquare (F : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n.sqrt^2=n then F n.sqrt else 0, by simp⟩

private lemma liftSquare_sq (F : ArithmeticFunction ℂ) (n : ℕ) :
    liftSquare F (n^2)=F n := by simp [liftSquare,Nat.sqrt_eq']

private lemma liftSquare_mul (F G : ArithmeticFunction ℂ) :
    liftSquare (F*G)=liftSquare F*liftSquare G := by
  ext n
  rw [ArithmeticFunction.mul_apply]
  by_cases hn : n.sqrt^2=n
  · obtain ⟨m,rfl⟩ : ∃ m, n=m^2 := ⟨_,hn.symm⟩
    rw [liftSquare_sq,ArithmeticFunction.mul_apply]
    let e (ij : ℕ × ℕ) := (ij.1^2,ij.2^2)
    apply Finset.sum_of_injOn e
    · intro ⟨x,y⟩ _ ⟨u,v⟩ _ h
      apply Prod.ext <;> apply Nat.pow_left_injective (by decide : 2≠0)
      · exact congrArg Prod.fst h
      · exact congrArg Prod.snd h
    · rintro ⟨x,y⟩ h
      obtain ⟨hm,h0⟩ := Nat.mem_divisorsAntidiagonal.mp h
      exact Nat.mem_divisorsAntidiagonal.mpr ⟨by change x^2*y^2=m^2; rw [← mul_pow,hm],pow_ne_zero _ h0⟩
    · rintro ⟨x,y⟩ h hnot
      obtain ⟨hm,h0⟩ := Nat.mem_divisorsAntidiagonal.mp h
      change x*y=m^2 at hm
      by_cases hx : x.sqrt^2=x <;> by_cases hy : y.sqrt^2=y
      · exfalso
        apply hnot
        refine ⟨(x.sqrt,y.sqrt),Nat.mem_divisorsAntidiagonal.mpr ⟨?_,by aesop⟩,Prod.ext hx hy⟩
        apply Nat.pow_left_injective (by decide : 2≠0)
        simpa only [mul_pow,hx,hy] using hm
      all_goals simp [liftSquare,hx,hy]
    · intro ij _
      simp [e,liftSquare_sq]
  · rw [show liftSquare (F*G) n=0 by simp [liftSquare,hn]]
    symm
    apply Finset.sum_eq_zero
    rintro ⟨x,y⟩ h
    obtain ⟨hm,h0⟩ := Nat.mem_divisorsAntidiagonal.mp h
    change x*y=n at hm
    by_cases hx : x.sqrt^2=x <;> by_cases hy : y.sqrt^2=y
    · have e : (x.sqrt*y.sqrt)^2=n := by rw [mul_pow,hx,hy,hm]
      exact False.elim (hn (by rw [←e,Nat.sqrt_eq']))
    all_goals simp [liftSquare,hx,hy]

private lemma sum_lift (F : ArithmeticFunction ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (liftSquare F n).re = ∑ m ∈ Finset.Icc 1 N.sqrt, (F m).re := by
  symm
  apply Finset.sum_of_injOn (·^2)
  · exact (Nat.pow_left_injective (by decide : 2≠0)).injOn
  · intro m hm
    obtain ⟨h1,h2⟩ := Finset.mem_Icc.mp hm
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_pow _ _ h1,Nat.le_sqrt'.mp h2⟩
  · intro n hn hnot
    have h : n.sqrt^2 ≠ n := by
      intro e
      apply hnot
      refine ⟨n.sqrt,Finset.mem_Icc.mpr ⟨?_,Nat.sqrt_le_sqrt (Finset.mem_Icc.mp hn).2⟩,e⟩
      have := (Finset.mem_Icc.mp hn).1
      apply Nat.le_sqrt'.mpr
      simpa using this
    simp [liftSquare,h]
  · intro m _; simp only [liftSquare_sq]

end LiftSquares


private lemma indicator_eq_lift : squareIndicator=liftSquare (chi 0) := by
  ext n
  by_cases h : n.sqrt^2=n
  · obtain ⟨m,rfl⟩ : ∃m, n=m^2 := ⟨_,h.symm⟩
    rw [liftSquare_sq,chi0_coprime]
    simp [squareIndicator,IsSquare,show ∃ r, m^2=r*r from ⟨m,pow_two _⟩,Nat.coprime_pow_left_iff]
  · have hns : ¬IsSquare n := by
      rintro ⟨m,rfl⟩; exact h (by rw [Nat.sqrt_eq,pow_two])
    simp [squareIndicator,liftSquare,h,hns]

private lemma logWeight_lift (F : ArithmeticFunction ℂ) :
    logWeight (liftSquare F)=liftSquare (logWeight F)+liftSquare (logWeight F) := by
  ext n
  by_cases h : n.sqrt^2=n
  · obtain ⟨m,rfl⟩ : ∃m, n=m^2 := ⟨_,h.symm⟩
    change (Real.log ((m^2:ℕ):ℝ):ℂ)*liftSquare F (m^2)=
      liftSquare (logWeight F) (m^2)+liftSquare (logWeight F) (m^2)
    rw [liftSquare_sq,liftSquare_sq,Nat.cast_pow,Real.log_pow]
    simp [logWeight]; ring
  · rw [ArithmeticFunction.add_apply]; simp [logWeight,liftSquare,h]

private noncomputable def lambda2AF : ArithmeticFunction ℂ :=
  lambdaAF+lambdaAF-(liftSquare (twistLambda 0)+liftSquare (twistLambda 0))

private lemma logWeight_second : logWeight moment2=moment2*lambda2AF := by
  have hu : IsUnit squareIndicator := ArithmeticFunction.isUnit_iff_isUnit_apply_one.mpr
    (by rw [squareIndicator_mult.1]; exact isUnit_one)
  have hs : logWeight squareIndicator = squareIndicator *
      (liftSquare (twistLambda 0)+liftSquare (twistLambda 0)) := by
    rw [indicator_eq_lift,logWeight_lift,logWeight_chi,liftSquare_mul]; ring
  have h0 := convolution_second.trans convolution_square.symm
  have h := congrArg logWeight h0
  simp only [logWeight_mul,hs,logWeight_first] at h
  apply hu.mul_left_inj.mp
  calc
    logWeight moment2 * squareIndicator =
        (weight * weight)*(lambdaAF+lambdaAF) -
        moment2*(squareIndicator*(liftSquare (twistLambda 0)+liftSquare (twistLambda 0))) := by
      linear_combination h
    _ = _ := by rw [← h0]; unfold lambda2AF; ring

private noncomputable def lambda2 (n : ℕ) := (lambda2AF n).re

private lemma log_convolution₂ (n : ℕ) : Real.log n*f n^2 =
    ∑ ij ∈ n.divisorsAntidiagonal, f ij.1^2*lambda2 ij.2 := by
  have h := congrArg (fun F : ArithmeticFunction ℂ => (F n).re) logWeight_second
  simpa only [ArithmeticFunction.mul_apply,logWeight,ArithmeticFunction.coe_mk,moment2_apply,
    ← Complex.ofReal_mul,Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,pow_two,lambda2] using h


open Filter Topology

private lemma lift_twist_mean :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, (liftSquare (twistLambda 0) n).re)/N)
      atTop (𝓝 0) := by
  have bnd (m : ℕ) : 0≤(twistLambda 0 m).re ∧ (twistLambda 0 m).re≤Real.log m := by
    simp only [twistLambda,ArithmeticFunction.coe_mk,chi0_coprime]
    split_ifs
    · simpa using And.intro (ArithmeticFunction.vonMangoldt_nonneg (n:=m)) (ArithmeticFunction.vonMangoldt_le_log (n:=m))
    · simpa using ArithmeticFunction.vonMangoldt_nonneg.trans (ArithmeticFunction.vonMangoldt_le_log (n:=m))
  have H : Tendsto (fun N : ℕ => Real.log N/Real.sqrt N) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_eq_rpow] using
      ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R:=ℝ)))
  apply squeeze_zero' _ _ H
  · filter_upwards with N
    rw [sum_lift]
    exact div_nonneg (Finset.sum_nonneg (fun i _ => (bnd i).1)) (Nat.cast_nonneg _)
  · filter_upwards [eventually_gt_atTop 1] with N hN
    rw [sum_lift]
    have hN' : 1<(N:ℝ) := by exact_mod_cast hN
    have hs : (N.sqrt:ℝ) ≤ Real.sqrt N :=
      (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr (by exact_mod_cast Nat.sqrt_le' N)
    have bound : ∑ m ∈ Finset.Icc 1 N.sqrt, (twistLambda 0 m).re ≤ (N.sqrt:ℝ)*Real.log N := by
      calc
        _ ≤ ∑ _m ∈ Finset.Icc 1 N.sqrt, Real.log N :=
          Finset.sum_le_sum fun m hm => (bnd m).2.trans
            (Real.log_le_log (by exact_mod_cast (Finset.mem_Icc.mp hm).1) (by
              exact_mod_cast ((Finset.mem_Icc.mp hm).2.trans (Nat.sqrt_le_self N))))
        _ = _ := by simp
    apply (div_le_div_of_nonneg_right (bound.trans (mul_le_mul_of_nonneg_right hs (Real.log_nonneg hN'.le)))
      (Nat.cast_nonneg _)).trans_eq
    field_simp [(Real.sqrt_pos.mpr (by linarith : 0<(N:ℝ))).ne']
    linear_combination (Real.log N) * (Real.sq_sqrt (Nat.cast_nonneg N))

private lemma pnt_first : Tendsto (fun N : ℕ => prefixSum progressionLambda N/N) atTop (𝓝 (1/2:ℝ)) :=
  prefix_of_range (by simp [progressionLambda]) progressionLambda_mean

private lemma pnt_second : Tendsto (fun N : ℕ => prefixSum lambda2 N/N) atTop (𝓝 1) := by
  have H := (pnt_first.add pnt_first).sub (lift_twist_mean.add lift_twist_mean)
  norm_num at H
  apply H.congr
  intro N
  have hLambda (n : ℕ) : lambda2 n = progressionLambda n + progressionLambda n -
      ((liftSquare (twistLambda 0) n).re+(liftSquare (twistLambda 0) n).re) := rfl
  simp only [hLambda,
    Complex.sub_re,Complex.add_re,prefixSum,lambdaAF,ArithmeticFunction.coe_mk,
    Complex.ofReal_re,Finset.sum_sub_distrib,Finset.sum_add_distrib,sub_div,add_div]

private lemma summable_real_of_complex {w : ℕ → ℝ} (hw : w 0=0) (s : ℝ)
    (hs : LSeriesSummable (fun n => (w n : ℂ)) s) :
    Summable (fun n : ℕ => w n/(n:ℝ)^s) := by
  apply Complex.summable_ofReal.mp
  apply hs.congr
  intro n
  by_cases hn : n=0
  · simp [hn,hw]
  · simp [LSeries.term_def,hn,Complex.ofReal_cpow (Nat.cast_nonneg n)]

private theorem first_prefix_limit :
    Tendsto (fun N : ℕ => Real.sqrt (Real.log N)*prefixSum f N/N) atTop
      (𝓝 (Real.sqrt residue/Real.sqrt Real.pi)) := by
  have H := mean_from_log (a:=1/2) f_zero (by norm_num) nonneg_f (Real.sqrt_nonneg residue)
    (fun t ht => summable_real_of_complex f_zero _ (weight_summable (s:=((1+t:ℝ):ℂ)) (by simpa)))
    (by simpa only [← Real.sqrt_eq_rpow] using first_real_limit) log_convolution pnt_first
  rw [Real.Gamma_add_one (by norm_num : (1/2:ℝ)≠0),Real.Gamma_one_half_eq] at H
  convert H.congr' ?_ using 1
  · ring
  filter_upwards [eventually_gt_atTop 1] with N hN
  rw [← Real.sqrt_eq_rpow]
  have hp : 0<Real.log N := Real.log_pos (by exact_mod_cast hN)
  field_simp [(Real.sqrt_pos.mpr hp).ne']
  rw [Real.sq_sqrt hp.le]; ring

private theorem second_prefix_limit :
    Tendsto (fun N : ℕ => prefixSum (fun n => f n^2) N/N) atTop (𝓝 (residue/(Real.pi^2/9))) := by
  have H := mean_from_log (a:=1) (w:=fun n => f n^2) (by simp [f_zero]) zero_lt_one
    (fun _ => sq_nonneg _) (div_nonneg residue_pos.le (by positivity : (0:ℝ) ≤ Real.pi^2/9))
    (fun t ht => summable_real_of_complex (by simp [f_zero]) _
      (by simpa only [show (fun n : ℕ => ((f n^2:ℝ):ℂ)) = ⇑moment2 by
            funext n; simp [moment2_apply,pow_two]] using
          moment2_summable (s:=((1+t:ℝ):ℂ)) (by simpa)))
    (by simpa only [Real.rpow_one] using second_real_limit) log_convolution₂ pnt_second
  norm_num [Real.Gamma_two] at H
  apply H.congr'
  filter_upwards [eventually_gt_atTop 1] with N hN
  have hp : 0<Real.log N := Real.log_pos (by exact_mod_cast hN)
  field_simp


section ChangeIndex

open Filter Topology

private def index12 (N : ℕ) := 12*N+1

private lemma profiled_prefix (w : ℕ → ℝ) (hw : ∀ n, w n≠0 → n%12=1) (N : ℕ) :
    prefixSum w (index12 N) = w 1 + ∑ k ∈ Finset.Icc 1 N, w (12*k+1) := by
  have H : (∑ k ∈ Finset.Icc 0 N, w (12*k+1)) = prefixSum w (index12 N) := by
    apply Finset.sum_of_injOn (fun k : ℕ => 12*k+1)
    · intro x _ y _ h; dsimp at h; omega
    · intro k hk
      obtain ⟨_,hb⟩ := Finset.mem_Icc.mp hk
      dsimp [index12]; exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
    · intro n hn hnot
      by_contra he
      have := hw n he
      have hN := (Finset.mem_Icc.mp hn).2
      dsimp [index12] at hN
      exact hnot ⟨n/12,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,by dsimp; omega⟩
    · intro k _; rfl
  rw [← H,Finset.Icc_eq_cons_Ioc (Nat.zero_le N),Finset.sum_cons,
    ← Finset.Icc_succ_left_eq_Ioc 0 N]
  simp

private lemma index_path : Tendsto index12 atTop atTop :=
  tendsto_atTop_atTop.mpr fun n => ⟨n,fun m hm => by dsimp [index12]; omega⟩

private lemma index_ratio : Tendsto (fun N : ℕ => (index12 N:ℝ)/N) atTop (𝓝 12) := by
  have H := (tendsto_const_nhds (x:=(1:ℝ))).div_atTop (tendsto_natCast_atTop_atTop (R:=ℝ))
  apply (show Tendsto _ _ (𝓝 (12:ℝ)) from (by simpa using H.add_const 12)).congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  dsimp [index12]; push_cast; field_simp; ring

private lemma index_log_ratio :
    Tendsto (fun N : ℕ => Real.sqrt (Real.log N)/Real.sqrt (Real.log (index12 N))) atTop (𝓝 1) := by
  have h := (index_ratio.log (by norm_num)).div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have H : Tendsto (fun N : ℕ => Real.log (index12 N)/Real.log N) atTop (𝓝 1) := by
    apply (show Tendsto _ _ (𝓝 (1:ℝ)) from (by simpa using h.add_const 1)).congr'
    filter_upwards [eventually_gt_atTop 1] with N hN
    have hn : 1<(N:ℝ) := by exact_mod_cast hN
    have hm : 0<(index12 N:ℝ) := by exact_mod_cast (show 0 < index12 N by dsimp [index12]; omega)
    simp only [Function.comp_apply,Real.log_div hm.ne' (by positivity : (N:ℝ)≠0)]
    field_simp [(Real.log_pos hn).ne'] <;> ring
  have h1 := (H.inv₀ (by norm_num)).sqrt
  simp only [inv_one,Real.sqrt_one] at h1
  apply h1.congr'
  filter_upwards [eventually_gt_atTop 1] with N hN
  rw [inv_div,Real.sqrt_div (Real.log_nonneg (by exact_mod_cast hN.le))]

private lemma sqrt_log_over_nat :
    Tendsto (fun N : ℕ => Real.sqrt (Real.log N)/N) atTop (𝓝 0) := by
  have H := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  apply squeeze_zero' _ _ H
  · filter_upwards with N using div_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1] with N hN
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    change 1 ≤ Real.log (N:ℝ) at hN
    nlinarith [Real.sq_sqrt (by linarith : 0≤Real.log (N:ℝ)),Real.sqrt_nonneg (Real.log N),
      sq_nonneg (Real.sqrt (Real.log N)-1)]

end ChangeIndex


private lemma first_constant : Real.sqrt residue/Real.sqrt Real.pi *12 =
    Real.sqrt (8*Real.pi*Real.log (2+Real.sqrt 3)/3) := by
  have hlog : 0 < Real.log (2+Real.sqrt 3) := Real.log_pos (by linarith [Real.sqrt_nonneg 3])
  have hs : 0 ≤ Real.sqrt residue/Real.sqrt Real.pi *12 := by positivity
  apply (sq_eq_sq₀ hs (Real.sqrt_nonneg _)).mp
  rw [mul_pow,div_pow,Real.sq_sqrt residue_pos.le,Real.sq_sqrt Real.pi_pos.le,Real.sq_sqrt (by positivity)]
  unfold residue
  field_simp
  ring

private lemma second_constant : residue/(Real.pi^2/9)*12 = Real.log (7+4*Real.sqrt 3) := by
  have h : 7+4*Real.sqrt 3=(2+Real.sqrt 3)^2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  rw [h,Real.log_pow,residue]
  field_simp [Real.pi_ne_zero]
  ring

private lemma original_first (N : ℕ) :
    ((∑ k ∈ Finset.Icc 1 N, |OMA.S_oeis_a002107.a k| : ℤ) : ℝ) = prefixSum f (index12 N)-1 := by
  rw [profiled_prefix f f_support N,f_one]
  push_cast
  simp only [f_coefficient]; ring

private lemma original_second (N : ℕ) :
    ((∑ k ∈ Finset.Icc 1 N, OMA.S_oeis_a002107.a k^2 : ℤ) : ℝ) =
      prefixSum (fun k => f k^2) (index12 N)-1 := by
  have hs n (hn : f n^2≠0) := f_support n (fun he => hn (by simp [he]))
  rw [profiled_prefix _ hs N,f_one]
  push_cast
  simp only [f_coefficient,sq_abs,one_pow]; ring

private theorem first_final :
    Asymptotics.IsEquivalent atTop (fun n : ℕ => ((∑ k ∈ Finset.Icc 1 n, |OMA.S_oeis_a002107.a k| : ℤ) : ℝ))
      (fun n => Real.sqrt (8*Real.pi*Real.log (2+Real.sqrt 3)/3)*n/Real.sqrt (Real.log n)) := by
  let C := Real.sqrt (8*Real.pi*Real.log (2+Real.sqrt 3)/3)
  have hc : 0<C := by
    dsimp only [C]; rw [← first_constant]; exact mul_pos (div_pos (Real.sqrt_pos.mpr residue_pos) (Real.sqrt_pos.mpr Real.pi_pos)) (by norm_num)
  have H := (((first_prefix_limit.comp index_path).mul index_ratio).mul index_log_ratio).sub sqrt_log_over_nat
  rw [mul_one,sub_zero,first_constant] at H
  have hc' : C≠0 := hc.ne'
  apply (Asymptotics.isEquivalent_iff_tendsto_one ?_).mpr
  · have Hc := H.div_const C
    rw [show Real.sqrt (8*Real.pi*Real.log (2+Real.sqrt 3)/3)/C=1 from div_self hc'] at Hc
    apply Hc.congr'
    filter_upwards [eventually_gt_atTop 1] with n hn
    have hn' : 1<(n:ℝ) := by exact_mod_cast hn
    have hi : 1 < index12 n := by dsimp [index12]; omega
    have hi' : 1<(index12 n:ℝ) := by exact_mod_cast hi
    change (_ - _)/C = _/_
    dsimp only [Function.comp_apply]
    rw [original_first]
    change (_-_)/C = (prefixSum f (index12 n)-1)/(C*n/Real.sqrt (Real.log n))
    field_simp [hc', (Real.sqrt_pos.mpr (Real.log_pos hn')).ne',
      (Real.sqrt_pos.mpr (Real.log_pos hi')).ne',show (index12 n:ℝ) ≠ 0 by positivity]
    <;> ring
  · filter_upwards [eventually_gt_atTop 1] with n hn
    have hn' : 1<(n:ℝ) := by exact_mod_cast hn
    exact div_ne_zero (mul_ne_zero hc' (by positivity)) (Real.sqrt_pos.mpr (Real.log_pos hn')).ne'

private theorem second_final :
    Asymptotics.IsEquivalent atTop (fun n : ℕ => ((∑ k ∈ Finset.Icc 1 n, OMA.S_oeis_a002107.a k^2 : ℤ) : ℝ))
      (fun n => Real.log (7+4*Real.sqrt 3)*n) := by
  let D := Real.log (7+4*Real.sqrt 3)
  have hd : 0<D := Real.log_pos (by linarith [Real.sqrt_nonneg 3])
  have h0 := (tendsto_const_nhds (x:=(1:ℝ))).div_atTop (tendsto_natCast_atTop_atTop (R:=ℝ))
  have H := ((second_prefix_limit.comp index_path).mul index_ratio).sub h0
  rw [sub_zero,second_constant] at H
  have hd' : D≠0 := hd.ne'
  apply (Asymptotics.isEquivalent_iff_tendsto_one ?_).mpr
  · have Hd := H.div_const D
    rw [show Real.log (7+4*Real.sqrt 3)/D=1 from div_self hd'] at Hd
    apply Hd.congr'
    filter_upwards [eventually_gt_atTop 1] with n hn
    have hn' : 1<(n:ℝ) := by exact_mod_cast hn
    have hi : 0 < index12 n := by dsimp [index12]; omega
    have hi' : 0<(index12 n:ℝ) := by exact_mod_cast hi
    change (_ - _)/D = _/_
    dsimp only [Function.comp_apply]
    rw [original_second]
    change (_-_)/D = (prefixSum (fun n => f n^2) (index12 n)-1)/(D*n)
    field_simp [hd',hi'.ne'] <;> ring
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact mul_ne_zero hd' (by exact_mod_cast hn.ne')

end Wave9Q.EulerSquare

theorem OMA.solution : type_of% @OMA.S_oeis_a002107.main :=
  ⟨Wave9Q.EulerSquare.first_final, Wave9Q.EulerSquare.second_final⟩
