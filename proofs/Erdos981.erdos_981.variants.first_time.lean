import FormalConjectures.ErdosProblems.«981»

-- MSL AUTO-ASSEMBLY: accepted reduction + every accepted H proof.
-- Source author credit remains in the original component comments.

section

/-!
# Truncation reduction for the first-passage variant of Erdős Problem 981

Credit: @DarkWingMcQuack.
-/

namespace OMA.R_Erdos981_erdos_981_variants_first_time_R1

open Filter Real
open scoped Topology

/-- For each positive cutoff, the normalized sum of truncated first-passage times converges
to a positive limit. This is the finite-dimensional part of Tang and Zhang's argument. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ B : ℕ, 0 < B →
    ∃ c > (0 : ℝ), Tendsto (fun x : ℝ ↦
      (↑(∑ p : Nat.primesBelow ⌈x⌉₊, min B (Erdos981.f' ε p)) : ℝ) * log x / x)
      atTop (𝓝 c)

/-- As the cutoff grows, the discarded contribution is eventually arbitrarily small.
This is the uniform tail estimate in Tang and Zhang's argument. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∃ B : ℕ, 0 < B ∧ ∀ᶠ x : ℝ in atTop,
    dist
      ((↑(∑ p : Nat.primesBelow ⌈x⌉₊, Erdos981.f' ε p) : ℝ) * log x / x)
      ((↑(∑ p : Nat.primesBelow ⌈x⌉₊, min B (Erdos981.f' ε p)) : ℝ) * log x / x) < δ

theorem main : H1 → H2 → type_of% @Erdos981.erdos_981.variants.first_time := by
  intro hTruncated hTail ε hε
  let average (x : ℝ) : ℝ :=
    (↑(∑ p : Nat.primesBelow ⌈x⌉₊, Erdos981.f' ε p) : ℝ) * log x / x
  let truncated (B : ℕ) (x : ℝ) : ℝ :=
    (↑(∑ p : Nat.primesBelow ⌈x⌉₊, min B (Erdos981.f' ε p)) : ℝ) * log x / x
  have hCauchy : CauchySeq average := by
    refine Metric.cauchySeq_iff.mpr ?_
    intro δ hδ
    have hThird : 0 < δ / 3 := by positivity
    obtain ⟨B, hB, hError⟩ := hTail ε hε (δ / 3) hThird
    obtain ⟨cutoff, hError⟩ := eventually_atTop.mp hError
    obtain ⟨c, _, hc⟩ := hTruncated ε hε B hB
    have hTruncatedCauchy : CauchySeq (truncated B) := hc.cauchySeq
    obtain ⟨start, hDistance⟩ := Metric.cauchySeq_iff.mp hTruncatedCauchy (δ / 3) hThird
    refine ⟨max cutoff start, fun x hx y hy ↦ ?_⟩
    have hxError : dist (average x) (truncated B x) < δ / 3 :=
      hError x ((le_max_left _ _).trans hx)
    have hyError : dist (truncated B y) (average y) < δ / 3 := by
      rw [dist_comm]
      exact hError y ((le_max_left _ _).trans hy)
    have hxy := hDistance x ((le_max_right _ _).trans hx) y ((le_max_right _ _).trans hy)
    calc
      dist (average x) (average y) ≤
          dist (average x) (truncated B x) + dist (truncated B x) (average y) :=
        dist_triangle _ _ _
      _ ≤ dist (average x) (truncated B x) + (dist (truncated B x) (truncated B y) +
          dist (truncated B y) (average y)) := add_le_add le_rfl (dist_triangle _ _ _)
      _ < δ := by linarith
  obtain ⟨limit, hLimit⟩ := cauchySeq_tendsto_of_complete hCauchy
  obtain ⟨lower, hLowerPos, hLower⟩ := hTruncated ε hε 1 Nat.zero_lt_one
  have hBelow : ∀ᶠ x in atTop, truncated 1 x ≤ average x := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hSum :
        (↑(∑ p : Nat.primesBelow ⌈x⌉₊, min 1 (Erdos981.f' ε p)) : ℝ) ≤
          (↑(∑ p : Nat.primesBelow ⌈x⌉₊, Erdos981.f' ε p) : ℝ) :=
      Nat.cast_le.mpr (Finset.sum_le_sum fun _ _ ↦ min_le_right _ _)
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hSum (log_nonneg hx)) (zero_le_one.trans hx)
  exact ⟨limit, hLowerPos.trans_le (le_of_tendsto_of_tendsto hLower hLimit hBelow), hLimit⟩

end OMA.R_Erdos981_erdos_981_variants_first_time_R1

end


-- MERGED SUBPROOF Erdos981.erdos_981.variants.first_time.R1.H1
section

/-! Bounded first hitting times are periodic weights on primes by quadratic reciprocity.
We reuse the prime number theorem in progressions from the Erdős 12 example. -/

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
-/

-- Ported from PrimeNumberTheoremAnd: Mathlib/Algebra/Notation/Support.lean, Mathlib/Analysis/Asymptotics/Asymptotics.lean, Mathlib/Analysis/SpecialFunctions/Log/Basic.lean
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
    simp only [ofReal_inj, indicator_apply_eq_self, mem_setOf_eq]
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

namespace Fact727AP
open Filter Real
open ArithmeticFunction hiding log
open scoped Topology
private theorem WeakPNT_AP {q a : ℕ} (hq : q ≥ 1) (ha : a.Coprime q) (ha' : a < q) :
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

open ArithmeticFunction hiding log
open _root_.Nat hiding log
open Finset
open BigOperators Filter Real Classical Asymptotics MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega Chebyshev

lemma tendsto_floor_add_one_div_self : Tendsto (fun x : ℝ ↦ (⌊x⌋₊ + 1 : ℝ) / x) atTop (nhds 1) := by
  have h := Asymptotics.isEquivalent_nat_floor (R := ℝ)
  have h' : IsEquivalent atTop (fun x : ℝ ↦ (⌊x⌋₊ : ℝ) + 1) _root_.id :=
    h.add_isLittleO (isLittleO_const_id_atTop 1)
  rwa [isEquivalent_iff_tendsto_one
    (by filter_upwards [eventually_gt_atTop 0] with x hx a; simp only [_root_.id] at a; linarith)] at h'

/-- `x =Θ x / c` for nonzero constant `c`. -/
lemma isTheta_self_div_const {c : ℝ} (hc : c ≠ 0) : (fun x : ℝ ↦ x) =Θ[atTop] fun x ↦ x / c := by
  have : (fun x : ℝ ↦ x / c) = fun x ↦ c⁻¹ * x := by ext x; ring
  exact this ▸ (isTheta_const_mul_left (inv_ne_zero hc)).mpr (isTheta_refl ..) |>.symm

/-- Filtered sum over `Iic n` equals filtered sum over `Icc 1 n` for primes. -/
lemma filter_prime_Iic_eq_Icc (n : ℕ) : filter Prime (Iic n) = filter Prime (Icc 1 n) := by
  ext p; simp only [mem_filter, mem_Iic, mem_Icc, and_congr_left_iff]
  exact fun hp ↦ ⟨fun h ↦ ⟨hp.one_lt.le, h⟩, fun ⟨_, h⟩ ↦ h⟩

/-- `Icc 0 n = insert 0 (Icc 1 n)` -/
lemma Icc_zero_eq_insert (n : ℕ) : Icc 0 n = insert 0 (Icc 1 n) := by
  ext m; simp [mem_Icc]; omega


set_option maxHeartbeats 750000 in
theorem chebyshev_asymptotic_pnt
    {q : ℕ} {a : ℕ} (hq : q ≥ 1) (ha : a.Coprime q) (ha' : a < q) :
    (fun x ↦ ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), if p % q = a then log p else 0) ~[atTop]
      fun x ↦ x / q.totient := by
  let ψ_aq : ℝ → ℝ := fun x ↦ ∑ n ∈ Icc 1 ⌊x⌋₊, if n % q = a then Λ n else 0
  have htot_pos : (0 : ℝ) < q.totient := cast_pos.mpr (totient_pos.mpr hq)
  have hψ_equiv : ψ_aq ~[atTop] fun x ↦ x / q.totient := by
    have hW := WeakPNT_AP hq ha ha'
    simp only [cumsum, ← Iio_eq_range] at hW
    have hψ_eq x : ψ_aq x = ∑ n ∈ Iio (⌊x⌋₊ + 1), if n % q = a then Λ n else 0 := by
      simp only [ψ_aq, show Icc 1 ⌊x⌋₊ = (Iio (⌊x⌋₊ + 1)).filter (1 ≤ ·) by
        ext n; simp [mem_Icc, mem_filter]; tauto, sum_filter]
      refine sum_congr rfl fun n _ ↦ ?_
      by_cases hn : 1 ≤ n <;> simp only [hn, ↓reduceIte]
      push Not at hn; interval_cases n; simp
    refine (isEquivalent_iff_tendsto_one ?_).mpr ?_
    · filter_upwards [eventually_ge_atTop 1] with x hx; exact div_ne_zero (by linarith) htot_pos.ne'
    have hlim1 : Tendsto (fun x : ℝ ↦ (∑ n ∈ Iio (⌊x⌋₊ + 1), if n % q = a then Λ n else 0) /
        (⌊x⌋₊ + 1 : ℝ)) atTop (nhds (1 / q.totient)) := by
      have heq : (fun x : ℝ ↦ (∑ n ∈ Iio (⌊x⌋₊ + 1), if n % q = a then Λ n else 0) /
          (⌊x⌋₊ + 1 : ℝ)) = (fun N ↦ (∑ n ∈ Iio N, if n % q = a then Λ n else 0) / N) ∘
          (fun x : ℝ ↦ ⌊x⌋₊ + 1) := by ext x; simp [Function.comp_apply]
      exact heq ▸ hW.comp ((tendsto_add_atTop_nat 1).comp tendsto_nat_floor_atTop)
    have hgoal_eq : (ψ_aq / fun x ↦ x / (q.totient : ℝ)) =
        fun x ↦ ψ_aq x / x * q.totient := by ext x; simp only [Pi.div_apply, div_div_eq_mul_div]; ring
    rw [hgoal_eq, show (1 : ℝ) = 1 / q.totient * 1 * q.totient by field_simp]
    refine Tendsto.mul ?_ tendsto_const_nhds
    have heq' : (fun x ↦ ψ_aq x / x) =ᶠ[atTop]
        fun x ↦ (∑ n ∈ Iio (⌊x⌋₊ + 1), if n % q = a then Λ n else 0) / (⌊x⌋₊ + 1 : ℝ) * ((⌊x⌋₊ + 1 : ℝ) / x) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      simp only [hψ_eq]; field_simp
    exact Tendsto.congr' heq'.symm (hlim1.mul tendsto_floor_add_one_div_self)
  refine hψ_equiv.add_isLittleO'' (IsBigO.trans_isLittleO (g := fun x ↦ 2 * x.sqrt * x.log) ?_ ?_)
  · rw [isBigO_iff']; refine ⟨1, one_pos, eventually_atTop.mpr ⟨2, fun x hx ↦ ?_⟩⟩
    simp only [Pi.sub_apply, norm_eq_abs, one_mul]
    have hdiff_nonneg : 0 ≤ ψ_aq x - ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), if p % q = a then log p else 0 := by
      simp only [ψ_aq, sub_nonneg]
      calc (∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), if p % q = a then log p else (0 : ℝ))
          ≤ ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), if p % q = a then Λ p else (0 : ℝ) :=
            sum_le_sum fun p hp ↦ by split_ifs <;> simp [vonMangoldt_apply_prime (mem_filter.mp hp).2]
        _ ≤ ∑ n ∈ Icc 1 ⌊x⌋₊, if n % q = a then Λ n else (0 : ℝ) :=
            sum_le_sum_of_subset_of_nonneg
              (fun p hp ↦ by simp only [mem_filter, mem_Iic, mem_Icc] at hp ⊢; exact ⟨hp.2.one_lt.le, hp.1⟩)
              (fun n _ _ ↦ by split_ifs <;> [exact vonMangoldt_nonneg; rfl])
    have hdiff_le : ψ_aq x - (∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), if p % q = a then log p else (0 : ℝ)) ≤ ψ x - θ x := by
      simp only [ψ_aq, Chebyshev.psi_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc]
      conv_rhs => rw [Icc_zero_eq_insert, sum_insert (by simp : (0 : ℕ) ∉ Icc 1 ⌊x⌋₊),
        show Λ 0 = 0 by simp only [ArithmeticFunction.map_zero], zero_add,
        show filter Nat.Prime (insert 0 (Icc 1 ⌊x⌋₊)) = filter Nat.Prime (Icc 1 ⌊x⌋₊) by
          simp [filter_insert, Nat.not_prime_zero]]
      rw [filter_prime_Iic_eq_Icc, ← sum_filter_add_sum_filter_not (Icc 1 ⌊x⌋₊) Nat.Prime,
        show (∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), if p % q = a then log p else (0 : ℝ)) =
          ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), if p % q = a then Λ p else (0 : ℝ) from
          sum_congr rfl fun p hp ↦ by simp only [mem_filter] at hp; split_ifs <;> simp [vonMangoldt_apply_prime hp.2],
        ← sum_filter_add_sum_filter_not (Icc 1 ⌊x⌋₊) Nat.Prime,
        show (∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), Λ p) = ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), log p from
          sum_congr rfl fun p hp ↦ vonMangoldt_apply_prime (mem_filter.mp hp).2]
      have h1 : (∑ n ∈ (Icc 1 ⌊x⌋₊).filter (¬Nat.Prime ·), if n % q = a then Λ n else (0 : ℝ)) ≤
          ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (¬Nat.Prime ·), Λ n :=
        sum_le_sum fun n _ ↦ by split_ifs <;> [exact le_refl _; exact vonMangoldt_nonneg]
      linarith
    rw [abs_of_nonneg hdiff_nonneg, abs_of_nonneg (by bound)]
    exact hdiff_le.trans ((le_abs_self _).trans (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith)))
  · simpa only [mul_assoc] using
      (isLittleO_sqrt_mul_log.const_mul_left 2).trans_isTheta (isTheta_self_div_const htot_pos.ne')
end Fact727AP

namespace Trunc981
open Finset Erdos981

lemma nonempty {p : ℕ} (hp : p.Prime) (ho : p ≠ 2) {ε : ℝ} (he : 0 < ε) :
    {m | Erdos981Property ε p m}.Nonempty := by
  let : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  refine ⟨p-1, ?_⟩
  have hsum : ∑ n ∈ range p, jacobiSym (n : ℤ) p = 0 := by
    simp_rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym, Int.cast_natCast]
    rw [← Fin.sum_univ_eq_sum_range]
    have h := quadraticChar_sum_zero (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
    have key (i : Fin p) : ZMod.finEquiv p i = (i.val : ZMod p) := by
      cases p with
      | zero => exact i.elim0
      | succ k => apply Fin.ext; change i.val = i.val % (k+1); rw [Nat.mod_eq_of_lt i.isLt]
    calc
      _ = ∑ i : Fin p, quadraticChar (ZMod p) ((ZMod.finEquiv p).toEquiv i) := Finset.sum_congr rfl (fun i _ => congrArg (quadraticChar (ZMod p)) (key i).symm)
      _ = _ := ((ZMod.finEquiv p).toEquiv.sum_comp (quadraticChar (ZMod p))).trans h
  have h0 : 0 < p-1 := by have := hp.two_le; omega
  change (↑(∑ n ∈ Iic (p-1), jacobiSym (n:ℤ) p) : ℝ) < ε * ↑(p-1)
  rw [← Finset.Iio_add_one_eq_Iic, Nat.Iio_eq_range, Nat.sub_add_cancel (by omega : 1 ≤ p), hsum, Int.cast_zero]
  positivity

lemma first_pos {p : ℕ} (hp : p.Prime) (ho : p ≠ 2) {ε : ℝ} (he : 0 < ε) :
    0 < f' ε p := by
  have h := Nat.sInf_mem (nonempty hp ho he)
  change Erdos981Property ε p (f' ε p) at h
  by_contra! hn
  have e : f' ε p = 0 := by omega
  simpa [e,Erdos981Property,show Finset.Iic (0:ℕ) = {0} by ext; simp,jacobiSym.zero_left hp.one_lt] using h

lemma same {B p q : ℕ} (hp : p.Prime) (hq : q.Prime) (ho : p ≠ 2) (ho' : q ≠ 2)
    {ε : ℝ} (he : 0 < ε) (hmod : p ≡ q [MOD 4 * B.factorial]) :
    min B (f' ε p) = min B (f' ε q) := by
  have eqprop {m : ℕ} (hm : m < B) : Erdos981Property ε p m ↔ Erdos981Property ε q m := by
    unfold Erdos981Property
    have hs : ∑ n ∈ Iic m, jacobiSym (n : ℤ) p = ∑ n ∈ Iic m, jacobiSym (n : ℤ) q := by
      apply sum_congr rfl
      intro n hn
      by_cases hn0 : n=0
      · simp [hn0,jacobiSym.zero_left hp.one_lt,jacobiSym.zero_left hq.one_lt]
      have hd : 4*n ∣ 4*B.factorial := Nat.mul_dvd_mul_left 4 (Nat.dvd_factorial (by omega) ((mem_Iic.mp hn).trans hm.le))
      rw [jacobiSym.mod_right (n:ℤ) (hp.odd_of_ne_two ho), jacobiSym.mod_right (n:ℤ) (hq.odd_of_ne_two ho')]
      simpa using congrArg (jacobiSym (n:ℤ)) (hmod.of_dvd hd)
    rw [hs]
  have small {u v : ℕ} (hu : u.Prime) (hu' : u≠2)
      (h : ∀ m < B, Erdos981Property ε u m → Erdos981Property ε v m) (hf : f' ε u < B) :
      f' ε v ≤ f' ε u :=
    Nat.sInf_le (h _ hf (Nat.sInf_mem (nonempty hu hu' he)))
  by_cases h : f' ε p < B
  · have hq' := small hp ho (fun _ hm => (eqprop hm).mp) h
    have hp' := small hq ho' (fun _ hm => (eqprop hm).mpr) (hq'.trans_lt h)
    rw [le_antisymm hp' hq']
  · by_cases h' : f' ε q < B
    · have hh := small hq ho' (fun _ hm => (eqprop hm).mpr) h'; omega
    · omega
end Trunc981

namespace Trunc981
open Finset Erdos981
lemma weights {ε : ℝ} (he : 0 < ε) {B : ℕ} (hB : 0 < B) :
    ∃ Q : ℕ, 2 ≤ Q ∧ ∃ w : ℕ → ℕ, 0 < w 1 ∧
      ∀ p : ℕ, p.Prime → min B (f' ε p) = w (p%Q) := by
  classical
  let Q := 4*B.factorial
  have hQ : 4 ≤ Q := by dsimp [Q]; have := B.factorial_pos; omega
  let w (r : ℕ) := if h : ∃ p : ℕ, p.Prime ∧ p % Q = r then min B (f' ε h.choose) else 1
  refine ⟨Q,by omega,w,?_,?_⟩
  · dsimp [w]; split
    next h =>
      have hne : h.choose ≠ 2 := by
        intro hh
        have hh' := h.choose_spec.2
        rw [hh,Nat.mod_eq_of_lt (by omega)] at hh'
        contradiction
      exact lt_min hB (first_pos h.choose_spec.1 hne he)
    · decide
  · intro p hp
    have h : ∃ q : ℕ, q.Prime ∧ q%Q=p%Q := ⟨p,hp,rfl⟩
    dsimp [w]; rw [dif_pos h]
    let q := h.choose
    have hq : q.Prime := h.choose_spec.1
    have hm : p ≡ q [MOD Q] := h.choose_spec.2.symm
    have hpar := hm.of_dvd (show 2 ∣ Q from ⟨2*B.factorial,by dsimp [Q];ring⟩)
    by_cases samep : p = q
    · exact congrArg (fun t => min B (f' ε t)) samep
    apply same hp hq _ _ he hm
    · intro e
      have : 2 ∣ q := by apply Nat.dvd_of_mod_eq_zero; change p%2=q%2 at hpar; omega
      exact samep (e.trans ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp this))
    · intro e
      have : 2 ∣ p := by apply Nat.dvd_of_mod_eq_zero; change p%2=q%2 at hpar; omega
      exact samep (((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp this).symm.trans e.symm)
end Trunc981
namespace Trunc981
open Filter Real Finset Asymptotics
open scoped Topology Chebyshev

theorem littleLog : Tendsto (fun x : ℝ => log x / x) atTop (𝓝 0) := by
  simpa using tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero

theorem count_of_theta (S : ℕ → Prop) [DecidablePred S] (c : ℝ)
    (ht : Tendsto (fun x : ℝ => (∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter S, log p) / x) atTop (𝓝 c)) :
    Tendsto (fun x : ℝ => (((Nat.primesBelow ⌈x⌉₊).filter S).card:ℝ) * log x / x) atTop (𝓝 c) := by
  obtain ⟨K,hK⟩ := Chebyshev.primeCounting_sub_theta_div_log_isBigO.exists_pos
  have hh := hK.2.bound
  have hk : Tendsto (fun x : ℝ => K / log x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_log_atTop
  have low := ht.sub littleLog
  have high := ht.add hk
  rw [sub_zero] at low
  rw [add_zero] at high
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' low high
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    let U := (Nat.primesLE ⌊x⌋₊).filter S
    let V := (Nat.primesBelow ⌈x⌉₊).filter S
    have hsub : U ⊆ insert ⌊x⌋₊ V := by
      intro p hp
      obtain ⟨h1,h2⟩ := mem_filter.mp hp
      obtain ⟨hle,hp'⟩ := Nat.mem_primesLE.mp h1
      rcases hle.eq_or_lt with rfl|hlt
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨hlt.trans_le (Nat.floor_le_ceil x),hp'⟩,h2⟩)
    have hcard : (U.card:ℝ) ≤ (V.card:ℝ)+1 := by
      exact_mod_cast (card_le_card hsub).trans (card_insert_le ..)
    have hsum : (∑ p ∈ U, log (p:ℝ)) ≤ U.card * log x := by
      calc
        _ ≤ ∑ _p ∈ U, log x := sum_le_sum fun p hp => by
          obtain ⟨hle,hp'⟩ := Nat.mem_primesLE.mp (mem_filter.mp hp).1
          exact log_le_log (Nat.cast_pos.mpr hp'.pos) ((Nat.le_floor_iff (by linarith)).mp hle)
        _ = _ := by simp
    change (∑ p ∈ U, log (p:ℝ))/x - log x/x ≤ (V.card:ℝ)*log x/x
    rw [← sub_div]
    exact div_le_div_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_right hcard (log_nonneg hx.le)]) (by linarith)
  · filter_upwards [eventually_gt_atTop (1:ℝ),hh] with x hx hKx
    let P := Nat.primesLE ⌊x⌋₊
    let U := P.filter S
    let V := (Nat.primesBelow ⌈x⌉₊).filter S
    have hsub : V ⊆ U := by
      intro p hp
      obtain ⟨h,hS⟩ := mem_filter.mp hp
      obtain ⟨hlt,pp⟩ := Nat.mem_primesBelow.mp h
      exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨by have := Nat.ceil_le_floor_add_one x;omega,pp⟩,hS⟩
    have gap : (U.card:ℝ)*log x - ∑ p ∈ U, log (p:ℝ) ≤
        (⌊x⌋₊.primeCounting:ℝ)*log x - Chebyshev.theta x := by
      have hs : (∑ p ∈ U, (log x - log (p:ℝ))) ≤ ∑ p ∈ P, (log x - log (p:ℝ)) := by
        apply sum_le_sum_of_subset_of_nonneg (filter_subset ..)
        intro p hp _
        obtain ⟨hle,hp'⟩ := Nat.mem_primesLE.mp hp
        exact sub_nonneg.mpr (log_le_log (Nat.cast_pos.mpr hp'.pos) ((Nat.le_floor_iff (by linarith)).mp hle))
      simp only [sum_sub_distrib,sum_const,nsmul_eq_mul,P,Nat.primesLE_card_eq_primeCounting] at hs
      simpa [Chebyshev.theta_eq_sum_primesLE] using hs
    have lx := log_pos hx
    have xx : 0 < x := by linarith
    have hbig : (⌊x⌋₊.primeCounting:ℝ) - Chebyshev.theta x / log x ≤ K * (x / log x^2) := by
      exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs, abs_of_pos xx, abs_of_pos (div_pos xx (sq_pos_of_pos lx))] using hKx)
    have hd := mul_le_mul_of_nonneg_right hbig lx.le
    have eq1 : ((⌊x⌋₊.primeCounting:ℝ) - Chebyshev.theta x / log x)*log x =
        (⌊x⌋₊.primeCounting:ℝ)*log x - Chebyshev.theta x := by field_simp
    have eq2 : K * (x/log x^2)*log x = K/log x*x := by field_simp
    rw [eq1,eq2] at hd
    have hcard : (V.card:ℝ) ≤ U.card := by exact_mod_cast card_le_card hsub
    change (V.card:ℝ)*log x/x ≤ (∑ p ∈ U, log (p:ℝ))/x + K/log x
    apply (div_le_iff₀ xx).mpr
    rw [add_mul,div_mul_cancel₀ _ xx.ne']
    linarith [mul_le_mul_of_nonneg_right hcard lx.le]

end Trunc981

namespace Trunc981
open Filter Real Asymptotics Finset Erdos981
open scoped Topology

theorem assemble (H : ∀ {q a : ℕ}, 1 ≤ q → a.Coprime q → a < q →
    (fun x : ℝ => ∑ p ∈ (Iic ⌊x⌋₊).filter Nat.Prime, if p%q=a then log p else 0) ~[atTop]
      (fun x => x / (q.totient:ℝ)))
    (ε : ℝ) (he : 0 < ε) (B : ℕ) (hB : 0 < B) :
    ∃ c > (0:ℝ), Tendsto (fun x : ℝ =>
      (↑(∑ p : Nat.primesBelow ⌈x⌉₊, min B (f' ε p)) : ℝ)*log x/x) atTop (𝓝 c) := by
  classical
  obtain ⟨Q,hQ,w,hw1,hw⟩ := weights he hB
  let c (r : ℕ) : ℝ := if r.Coprime Q then 1 / (Q.totient:ℝ) else 0
  let F (r : ℕ) (x : ℝ) := (Nat.primesBelow ⌈x⌉₊).filter (fun p => p%Q=r)
  have pos : 0 < (Q.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega))
  have lim (r : ℕ) (hr : r < Q) :
      Tendsto (fun x : ℝ => ((F r x).card:ℝ)*log x/x) atTop (𝓝 (c r)) := by
    by_cases cop : r.Coprime Q
    · dsimp [F,c]; rw [if_pos cop]
      apply count_of_theta
      have hh := H (by omega : 1 ≤ Q) cop hr
      have hlim := (isEquivalent_iff_tendsto_one (by
        filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx using div_ne_zero hx.ne' pos.ne')).mp hh
      have hfin := hlim.div_const (Q.totient:ℝ)
      apply hfin.congr'
      filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
      have eq : (Iic ⌊x⌋₊).filter Nat.Prime = Nat.primesLE ⌊x⌋₊ := by
        ext p; simp [Nat.mem_primesLE,and_comm]
      simp only [Pi.div_apply]
      rw [eq, sum_filter]
      field_simp
    · simp only [c,cop,if_false]
      have hbound (x : ℝ) : (F r x).card ≤ Q+1 := by
        apply (card_le_card (t := range (Q+1)) ?_).trans_eq (card_range _)
        intro p hp
        obtain ⟨hpr,hm⟩ := mem_filter.mp hp
        have pp := (Nat.mem_primesBelow.mp hpr).2
        have hn : ¬ p.Coprime Q := by
          intro hc
          apply cop
          rw [← hm]
          change Nat.gcd (p%Q) Q = 1
          rw [← Nat.gcd_rec]; exact hc.symm
        have hd := not_not.mp (pp.coprime_iff_not_dvd.not.mp hn)
        exact mem_range.mpr (by have := Nat.le_of_dvd (by omega : 0<Q) hd; omega)
      have up := littleLog.const_mul ((Q:ℝ)+1)
      rw [mul_zero] at up
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds up
      · filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
        exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (log_nonneg hx.le)) (by linarith)
      · filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
        rw [mul_div_assoc]
        apply mul_le_mul_of_nonneg_right _ (div_nonneg (log_nonneg hx.le) (by linarith))
        exact_mod_cast hbound x
  refine ⟨∑ r ∈ range Q, (w r:ℝ)*c r, ?_, ?_⟩
  · apply sum_pos' (fun r _ => mul_nonneg (Nat.cast_nonneg _) (by dsimp [c];split <;> positivity))
    exact ⟨1,mem_range.mpr (by omega),mul_pos (Nat.cast_pos.mpr hw1) (by simp [c];positivity)⟩
  · apply (tendsto_finsetSum (range Q) (fun r hr => (lim r (mem_range.mp hr)).const_mul (w r:ℝ))).congr
    intro x
    let P := Nat.primesBelow ⌈x⌉₊
    have partition : ∑ r ∈ range Q, w r * (F r x).card = ∑ p ∈ P, min B (f' ε p) := by
      calc
        _ = ∑ r ∈ range Q, ∑ p ∈ P.filter (fun p => p%Q=r), w (p%Q) := by
          apply sum_congr rfl
          intro r hr
          rw [show (∑ p ∈ P.filter (fun p => p%Q=r), w (p%Q)) =
              ∑ _p ∈ P.filter (fun p => p%Q=r), w r from
                sum_congr rfl (fun p hp => congrArg w (mem_filter.mp hp).2)]
          simp [P,F,mul_comm]
        _ = ∑ p ∈ P, w (p%Q) := sum_fiberwise_of_maps_to (fun p _ => mem_range.mpr (Nat.mod_lt p (by omega))) _
        _ = _ := sum_congr rfl (fun p hp => (hw p (Nat.mem_primesBelow.mp hp).2).symm)
    change (∑ r ∈ range Q, (w r:ℝ)*(((F r x).card:ℝ)*log x/x)) = _
    simp_rw [← mul_div_assoc, ← mul_assoc]
    rw [← sum_div,← sum_mul]
    simp_rw [← Nat.cast_mul]
    rw [← Nat.cast_sum,partition]
    simp only [P,Finset.univ_eq_attach,Finset.sum_attach _ (fun p => min B (f' ε p))]
end Trunc981

theorem OMA.assembled_step_1 : OMA.R_Erdos981_erdos_981_variants_first_time_R1.H1 := by
  exact Trunc981.assemble (fun _ _ _ => Fact727AP.chebyshev_asymptotic_pnt ‹_› ‹_› ‹_›)


end


-- MERGED SUBPROOF Erdos981.erdos_981.variants.first_time.R1.H2
section

/-!
Proof of `OMA.R_Erdos981_erdos_981_variants_first_time_R1.H2`, completing
`Erdos981.erdos_981.variants.first_time` (Tang and Zhang 2025, arXiv:2512.24631).

We prove the uniform tail estimate for the first-passage time `f' ε p`:
for every `ε > 0` and `δ > 0`, there exists `B > 0` such that eventually as `x → ∞`,
  `(log x / x) * ∑_{p < x} (f' ε p - min B (f' ε p)) < δ`.

Proof architecture (self-contained, elementary):
1. Quadratic Gauss sum Parseval identity `‖G(p, 1)‖^2 = p` and the Pólya-Vinogradov bound
   `|S_M(p)| ≤ √p (1 + log p)` for odd primes `p`, yielding the cutoff `f' ε p ≤ (2/ε) √p log p`.
2. Gallagher's additive large sieve (via 1D Sobolev + Parseval on `[0, 1]`) combined with
   quadratic Gauss sums gives the prime-modulus multiplicative large sieve
   `∑_{p < x odd} |∑_{n=1}^N a_n (n/p)|^2 ≤ (x^2 + π N) ∑ |a_n|^2`.
3. Elementary divisor bound `d(n) ≤ C_K n^{1/K}` and representation-count bounds `c_k(u) ≤ d(u)^{k-1}`,
   plus the square-pair bound `C_2(m) ≤ C m^{5/2} (1 + 2 log m)`.
4. Periodicity and vanishing full-period sum of `k ↦ (D/k)` over odd `k mod 8D` for non-square `D`,
   giving `|∑_{k ≤ Y, odd} (D/k)| ≤ 8D`.
5. Classical Selberg sieve weights `λ_d` on odd squarefree `d ≤ z` (`|λ_d| ≤ 1`,
   `∑ λ_{d1} λ_{d2} / [d1, d2] = 1 / G(z) ≤ 4 / log z`), giving the Range 1 (`B ≤ m ≤ x^{1/20}`)
   4th-moment bound with the `1 / log x` factor.
6. Applying the prime multiplicative large sieve to the 80th moment (`k = 40`) handles all large `m`
   (`x^{1/20} < m ≤ (3/ε) √x log x`) in one shot without Heath-Brown's quadratic large sieve.
-/

open Filter Real Complex Finset
open scoped Topology BigOperators

namespace Erdos981H2

/- ### Section 1: Additive characters, quadratic Gauss sums, and Pólya-Vinogradov -/

noncomputable def eC (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))

lemma eC_zero : eC 0 = 1 := by simp [eC]

lemma eC_add (s t : ℝ) : eC (s + t) = eC s * eC t := by
  unfold eC; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma eC_sub (s t : ℝ) : eC (s - t) = eC s * eC (-t) := by
  rw [sub_eq_add_neg, eC_add]

lemma eC_neg (t : ℝ) : eC (-t) = starRingEnd ℂ (eC t) := by
  unfold eC
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  ring

lemma eC_mul_neg_eq_one (t : ℝ) : eC t * eC (-t) = 1 := by
  rw [← eC_add, add_neg_cancel, eC_zero]

lemma eC_norm (t : ℝ) : ‖eC t‖ = 1 := by
  unfold eC
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma eC_int (k : ℤ) : eC (k : ℝ) = 1 := by
  unfold eC
  rw [show 2 * (Real.pi : ℂ) * Complex.I * ((k : ℝ) : ℂ) = (k : ℂ) * (2 * Real.pi * Complex.I) by
    push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

lemma eC_nat (k : ℕ) : eC (k : ℝ) = 1 := by
  simpa using eC_int (k : ℤ)

lemma eC_eq_of_modEq {q a b : ℕ} (h : a ≡ b [MOD q]) :
    eC ((a : ℝ) / (q : ℝ)) = eC ((b : ℝ) / (q : ℝ)) := by
  by_cases hq : q = 0
  · subst hq; simp
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hdvd : (q : ℤ) ∣ (a : ℤ) - (b : ℤ) := (Int.natCast_modEq_iff.mpr h).symm.dvd
  obtain ⟨k, hk⟩ := hdvd
  have hdiff : (a : ℝ) / (q : ℝ) = (b : ℝ) / (q : ℝ) + (k : ℝ) := by
    have hk' : (a : ℝ) - (b : ℝ) = (q : ℝ) * (k : ℝ) := by exact_mod_cast hk
    field_simp [hq']; linarith
  rw [hdiff, eC_add, eC_int, mul_one]

lemma eC_pow_nat (t : ℝ) (n : ℕ) : (eC t) ^ n = eC ((n : ℝ) * t) := by
  induction n with
  | zero => simp [eC_zero]
  | succ n ih =>
    rw [pow_succ, ih, ← eC_add]
    congr 1; push_cast; ring

lemma sum_eC_range_eq {q : ℕ} (hq : 0 < q) (a : ℤ) :
    ∑ k ∈ Finset.range q, eC (((k : ℤ) * a : ℝ) / (q : ℝ)) =
      if (q : ℤ) ∣ a then (q : ℂ) else 0 := by
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  split_ifs with hdvd
  · obtain ⟨m, hm⟩ := hdvd
    have h1 : ∀ k ∈ Finset.range q, eC (((k : ℤ) * a : ℝ) / (q : ℝ)) = 1 := fun k _ => by
      have harg : ((k : ℤ) * a : ℝ) / (q : ℝ) = (((k : ℤ) * m : ℤ) : ℝ) := by
        have hm' : (a : ℝ) = (q : ℝ) * (m : ℝ) := by exact_mod_cast hm
        push_cast; rw [hm']; field_simp [hqR]
      rw [harg, eC_int]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  · let ζ : ℂ := eC ((a : ℝ) / (q : ℝ))
    have hζ_ne : ζ ≠ 1 := by
      intro h1
      have harg : Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) / (q : ℝ) : ℝ) : ℂ)) = 1 := h1
      rw [Complex.exp_eq_one_iff] at harg
      obtain ⟨m, hm⟩ := harg
      have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have heq : ((((a : ℝ) / (q : ℝ)) : ℝ) : ℂ) = ((m : ℝ) : ℂ) := by
        apply mul_left_cancel₀ hpi
        rw [hm]; push_cast; ring
      have heqR : (a : ℝ) / (q : ℝ) = (m : ℝ) := Complex.ofReal_injective heq
      have heqZ : a = (q : ℤ) * m := by
        have h2 : (a : ℝ) = (q : ℝ) * (m : ℝ) := by field_simp [hqR] at heqR; linarith
        exact_mod_cast h2
      exact hdvd ⟨m, heqZ⟩
    have hsum : ∑ k ∈ Finset.range q, eC (((k : ℤ) * a : ℝ) / (q : ℝ)) =
        ∑ k ∈ Finset.range q, ζ ^ k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show ζ ^ k = eC ((k : ℝ) * ((a : ℝ) / (q : ℝ))) from eC_pow_nat _ k]
      congr 1; push_cast; ring
    rw [hsum, geom_sum_eq hζ_ne]
    have hpow : ζ ^ q = 1 := by
      rw [show ζ ^ q = eC ((q : ℝ) * ((a : ℝ) / (q : ℝ))) from eC_pow_nat _ q,
        mul_div_cancel₀ _ hqR, eC_int]
    rw [hpow, sub_self, zero_div]

lemma exists_jacobi_neg_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ a : ℕ, a < p ∧ jacobiSym (a : ℤ) p = -1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; exact hp2
  obtain ⟨x, hx⟩ := FiniteField.exists_nonsquare hchar
  refine ⟨x.val, x.val_lt, ?_⟩
  have hleg : legendreSym p (x.val : ℤ) = -1 := by
    rw [legendreSym.eq_neg_one_iff]
    intro hsq
    apply hx
    rcases hsq with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    have hxval : ((x.val : ℤ) : ZMod p) = x := by simp
    rw [← hxval]; exact hy
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  exact hleg

lemma sum_jacobi_range_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∑ a ∈ Finset.range p, (jacobiSym (a : ℤ) p : ℂ) = 0 := by
  obtain ⟨g, hg_lt, hg_val⟩ := exists_jacobi_neg_one hp hp2
  have hg_pos : 0 < g := by
    by_contra h0; push Not at h0
    have : g = 0 := by omega
    subst this
    rw [Nat.cast_zero, jacobiSym.zero_left hp.one_lt] at hg_val
    norm_num at hg_val
  have hg_cop : Nat.Coprime g p := (hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt hg_pos hg_lt)).symm
  let S : ℂ := ∑ a ∈ Finset.range p, (jacobiSym (a : ℤ) p : ℂ)
  have hS : (jacobiSym (g : ℤ) p : ℂ) * S = S := by
    rw [Finset.mul_sum]
    have hbij : ∑ a ∈ Finset.range p, (jacobiSym (g : ℤ) p : ℂ) * (jacobiSym (a : ℤ) p : ℂ) =
        ∑ a ∈ Finset.range p, (jacobiSym (((g * a) % p : ℕ) : ℤ) p : ℂ) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Int.cast_mul, ← jacobiSym.mul_left, jacobiSym.mod_left]
      have heq : ((g : ℤ) * (a : ℤ)) % (p : ℤ) = (((g * a) % p : ℕ) : ℤ) := by push_cast; rfl
      rw [heq]
    rw [hbij]
    refine Finset.sum_bij (fun a _ => (g * a) % p) (fun a _ => Finset.mem_range.mpr (Nat.mod_lt _ hp.pos)) ?_ ?_ (fun _ _ => rfl)
    · intro a ha b hb hab
      have ha' := Finset.mem_range.mp ha
      have hb' := Finset.mem_range.mp hb
      have hmod : g * a ≡ g * b [MOD p] := hab
      have hcancel : a ≡ b [MOD p] := Nat.ModEq.cancel_left_of_coprime hg_cop.symm hmod
      exact Nat.ModEq.eq_of_lt_of_lt hcancel ha' hb'
    · intro b hb
      have hb' := Finset.mem_range.mp hb
      have : Fact p.Prime := ⟨hp⟩
      let x : ZMod p := (g : ZMod p)⁻¹ * (b : ZMod p)
      refine ⟨x.val, Finset.mem_range.mpr x.val_lt, ?_⟩
      have hg_ne : (g : ZMod p) ≠ 0 := by
        intro h0
        have := (ZMod.natCast_eq_zero_iff g p).mp h0
        exact Nat.not_dvd_of_pos_of_lt hg_pos hg_lt this
      have hprod : ((g * x.val : ℕ) : ZMod p) = (b : ZMod p) := by
        simp only [Nat.cast_mul, ZMod.natCast_zmod_val, x]
        exact mul_inv_cancel_left₀ hg_ne _
      have hval : ((g * x.val : ℕ) : ZMod p).val = (b : ZMod p).val := congrArg ZMod.val hprod
      rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hb'] at hval
      exact hval
  rw [hg_val] at hS
  norm_num at hS
  change S = 0
  linear_combination -hS / 2

noncomputable def gaussSum (p b : ℕ) : ℂ :=
  ∑ a ∈ Finset.range p, (jacobiSym (a : ℤ) p : ℂ) * eC (((a * b : ℕ) : ℝ) / (p : ℝ))

lemma gaussSum_mul {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (b : ℕ) :
    gaussSum p b = (jacobiSym (b : ℤ) p : ℂ) * gaussSum p 1 := by
  by_cases hdiv : p ∣ b
  · have hjac0 : jacobiSym (b : ℤ) p = 0 := by
      rw [jacobiSym.mod_left]
      have hmod : (b : ℤ) % (p : ℤ) = 0 := Int.emod_eq_zero_of_dvd (Int.natCast_dvd_natCast.mpr hdiv)
      rw [hmod, jacobiSym.zero_left hp.one_lt]
    rw [hjac0]; simp only [Int.cast_zero, zero_mul]
    unfold gaussSum
    have h1 : ∀ a ∈ Finset.range p, eC (((a * b : ℕ) : ℝ) / (p : ℝ)) = 1 := fun a _ => by
      obtain ⟨k, rfl⟩ := hdiv
      have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
      rw [show ((a * (p * k) : ℕ) : ℝ) / (p : ℝ) = ((a * k : ℕ) : ℝ) by push_cast; field_simp [hpR]]
      exact eC_nat _
    calc ∑ a ∈ Finset.range p, (jacobiSym (a : ℤ) p : ℂ) * eC (((a * b : ℕ) : ℝ) / (p : ℝ))
        = ∑ a ∈ Finset.range p, (jacobiSym (a : ℤ) p : ℂ) :=
          Finset.sum_congr rfl fun a ha => by rw [h1 a ha, mul_one]
      _ = 0 := sum_jacobi_range_prime hp hp2
  · have hcop : Nat.Coprime b p := (hp.coprime_iff_not_dvd.mpr hdiv).symm
    have hjac_sq : (jacobiSym (b : ℤ) p : ℂ) * (jacobiSym (b : ℤ) p : ℂ) = 1 := by
      have h1 : jacobiSym (b : ℤ) p ^ 2 = 1 := jacobiSym.sq_one (by simpa [Int.gcd] using hcop)
      exact_mod_cast (by rw [← sq]; exact h1 : (jacobiSym (b : ℤ) p : ℤ) * jacobiSym (b : ℤ) p = 1)
    have hstep : (jacobiSym (b : ℤ) p : ℂ) * gaussSum p b = gaussSum p 1 := by
      unfold gaussSum
      rw [Finset.mul_sum]
      have hrew : ∑ a ∈ Finset.range p, (jacobiSym (b : ℤ) p : ℂ) *
            ((jacobiSym (a : ℤ) p : ℂ) * eC (((a * b : ℕ) : ℝ) / (p : ℝ))) =
          ∑ a ∈ Finset.range p, (jacobiSym (((a * b) % p : ℕ) : ℤ) p : ℂ) *
            eC (((((a * b) % p) * 1 : ℕ) : ℝ) / (p : ℝ)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← mul_assoc, ← Int.cast_mul, ← jacobiSym.mul_left, mul_comm (b : ℤ), jacobiSym.mod_left]
        have heq : ((a : ℤ) * (b : ℤ)) % (p : ℤ) = (((a * b) % p : ℕ) : ℤ) := by push_cast; rfl
        rw [heq, mul_one, eC_eq_of_modEq (Nat.mod_modEq (a * b) p).symm]
      rw [hrew]
      refine Finset.sum_bij (fun a _ => (a * b) % p) (fun a _ => Finset.mem_range.mpr (Nat.mod_lt _ hp.pos)) ?_ ?_ (fun _ _ => rfl)
      · intro a ha c hc hac
        have hmod : a * b ≡ c * b [MOD p] := hac
        have hcancel : a ≡ c [MOD p] := Nat.ModEq.cancel_right_of_coprime hcop.symm hmod
        exact Nat.ModEq.eq_of_lt_of_lt hcancel (Finset.mem_range.mp ha) (Finset.mem_range.mp hc)
      · intro c hc
        have : Fact p.Prime := ⟨hp⟩
        have hb_ne : (b : ZMod p) ≠ 0 := by
          intro h0; exact hdiv ((ZMod.natCast_eq_zero_iff b p).mp h0)
        let x : ZMod p := (c : ZMod p) * (b : ZMod p)⁻¹
        refine ⟨x.val, Finset.mem_range.mpr x.val_lt, ?_⟩
        have hprod : ((x.val * b : ℕ) : ZMod p) = (c : ZMod p) := by
          simp only [Nat.cast_mul, ZMod.natCast_zmod_val, x]
          exact inv_mul_cancel_right₀ hb_ne _
        have hval : ((x.val * b : ℕ) : ZMod p).val = (c : ZMod p).val := congrArg ZMod.val hprod
        rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hc)] at hval
        exact hval
    calc gaussSum p b = 1 * gaussSum p b := (one_mul _).symm
      _ = ((jacobiSym (b : ℤ) p : ℂ) * (jacobiSym (b : ℤ) p : ℂ)) * gaussSum p b := by rw [hjac_sq]
      _ = (jacobiSym (b : ℤ) p : ℂ) * ((jacobiSym (b : ℤ) p : ℂ) * gaussSum p b) := by ring
      _ = (jacobiSym (b : ℤ) p : ℂ) * gaussSum p 1 := by rw [hstep]

lemma gaussSum_norm_sq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ‖gaussSum p 1‖ ^ 2 = (p : ℝ) := by
  have hparseval : ∑ b ∈ Finset.range p, (‖gaussSum p b‖ ^ 2 : ℂ) = (p : ℂ) * ((p - 1 : ℕ) : ℂ) := by
    have hnorm : ∀ b ∈ Finset.range p, (‖gaussSum p b‖ ^ 2 : ℂ) =
        gaussSum p b * starRingEnd ℂ (gaussSum p b) := fun b _ => by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
    rw [Finset.sum_congr rfl hnorm]
    have hexp : ∀ b ∈ Finset.range p, gaussSum p b * starRingEnd ℂ (gaussSum p b) =
        ∑ a₁ ∈ Finset.range p, ∑ a₂ ∈ Finset.range p,
          (jacobiSym (a₁ : ℤ) p : ℂ) * (jacobiSym (a₂ : ℤ) p : ℂ) *
            eC ((((b : ℤ) : ℝ) * ((((a₁ : ℤ) - (a₂ : ℤ) : ℤ) : ℝ))) / (p : ℝ)) := fun b _ => by
      unfold gaussSum
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a₁ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a₂ _ => ?_
      rw [map_mul, map_intCast, ← eC_neg]
      have he : eC (((a₁ * b : ℕ) : ℝ) / (p : ℝ)) * eC (-(((a₂ * b : ℕ) : ℝ) / (p : ℝ))) =
          eC ((((b : ℤ) : ℝ) * ((((a₁ : ℤ) - (a₂ : ℤ) : ℤ) : ℝ))) / (p : ℝ)) := by
        rw [← eC_add]; congr 1; push_cast; ring
      linear_combination (jacobiSym (a₁ : ℤ) p : ℂ) * (jacobiSym (a₂ : ℤ) p : ℂ) * he
    rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
    have hswap : ∑ a₁ ∈ Finset.range p, ∑ b ∈ Finset.range p, ∑ a₂ ∈ Finset.range p,
          (jacobiSym (a₁ : ℤ) p : ℂ) * (jacobiSym (a₂ : ℤ) p : ℂ) *
            eC ((((b : ℤ) : ℝ) * ((((a₁ : ℤ) - (a₂ : ℤ) : ℤ) : ℝ))) / (p : ℝ)) =
        ∑ a₁ ∈ Finset.range p, ∑ a₂ ∈ Finset.range p,
          (jacobiSym (a₁ : ℤ) p : ℂ) * (jacobiSym (a₂ : ℤ) p : ℂ) *
            ∑ b ∈ Finset.range p, eC ((((b : ℤ) : ℝ) * ((((a₁ : ℤ) - (a₂ : ℤ) : ℤ) : ℝ))) / (p : ℝ)) := by
      refine Finset.sum_congr rfl fun a₁ _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a₂ _ => (Finset.mul_sum _ _ _).symm
    rw [hswap]
    have hdiag : ∀ a₁ ∈ Finset.range p, ∑ a₂ ∈ Finset.range p,
          (jacobiSym (a₁ : ℤ) p : ℂ) * (jacobiSym (a₂ : ℤ) p : ℂ) *
            ∑ b ∈ Finset.range p, eC ((((b : ℤ) : ℝ) * ((((a₁ : ℤ) - (a₂ : ℤ) : ℤ) : ℝ))) / (p : ℝ)) =
        (p : ℂ) * (if a₁ = 0 then 0 else 1) := fun a₁ ha₁ => by
      have ha₁_lt := Finset.mem_range.mp ha₁
      have hterm : ∀ a₂ ∈ Finset.range p,
          (jacobiSym (a₁ : ℤ) p : ℂ) * (jacobiSym (a₂ : ℤ) p : ℂ) *
            ∑ b ∈ Finset.range p, eC ((((b : ℤ) : ℝ) * ((((a₁ : ℤ) - (a₂ : ℤ) : ℤ) : ℝ))) / (p : ℝ)) =
          if a₂ = a₁ then (p : ℂ) * ((jacobiSym (a₁ : ℤ) p : ℂ) * (jacobiSym (a₁ : ℤ) p : ℂ)) else 0 := fun a₂ ha₂ => by
        rw [sum_eC_range_eq hp.pos ((a₁ : ℤ) - (a₂ : ℤ))]
        have ha₂_lt := Finset.mem_range.mp ha₂
        have hiff : ((p : ℤ) ∣ (a₁ : ℤ) - (a₂ : ℤ)) ↔ a₂ = a₁ := by
          constructor
          · intro hd
            have hmod : a₁ ≡ a₂ [MOD p] := Int.natCast_modEq_iff.mp (Int.modEq_iff_dvd.mpr (dvd_sub_comm.mp hd))
            exact (Nat.ModEq.eq_of_lt_of_lt hmod ha₁_lt ha₂_lt).symm
          · rintro rfl; simp
        by_cases h2 : a₂ = a₁
        · rw [if_pos (hiff.mpr h2), if_pos h2]; subst h2; ring
        · rw [if_neg (mt hiff.mp h2), if_neg h2]; ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' _ _ _, if_pos ha₁]
      by_cases h0 : a₁ = 0
      · subst h0; simp [jacobiSym.zero_left hp.one_lt]
      · rw [if_neg h0]
        have hcop : Nat.Coprime a₁ p := (hp.coprime_iff_not_dvd.mpr
          (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero h0) ha₁_lt)).symm
        have hsq : jacobiSym (a₁ : ℤ) p ^ 2 = 1 := jacobiSym.sq_one (by simpa [Int.gcd] using hcop)
        have hsqC : (jacobiSym (a₁ : ℤ) p : ℂ) * (jacobiSym (a₁ : ℤ) p : ℂ) = 1 := by
          exact_mod_cast (by rw [← sq]; exact hsq : (jacobiSym (a₁ : ℤ) p : ℤ) * jacobiSym (a₁ : ℤ) p = 1)
        rw [hsqC]
    rw [Finset.sum_congr rfl hdiag, ← Finset.mul_sum]
    congr 1
    have hsplit : ∑ a₁ ∈ Finset.range p, (if a₁ = 0 then (0 : ℂ) else 1) =
        ∑ a₁ ∈ (Finset.range p).erase 0, (1 : ℂ) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hp.pos)]
      simp only [if_true, zero_add]
      refine Finset.sum_congr rfl fun a ha => if_neg (Finset.mem_erase.mp ha).1
    rw [hsplit, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_range.mpr hp.pos),
      Finset.card_range, nsmul_eq_mul, mul_one]
  have hlhs : ∑ b ∈ Finset.range p, ‖gaussSum p b‖ ^ 2 = ((p - 1 : ℕ) : ℝ) * ‖gaussSum p 1‖ ^ 2 := by
    have hterm : ∀ b ∈ Finset.range p, ‖gaussSum p b‖ ^ 2 =
        if b = 0 then 0 else ‖gaussSum p 1‖ ^ 2 := fun b hb => by
      rw [gaussSum_mul hp hp2 b, norm_mul, mul_pow]
      by_cases h0 : b = 0
      · subst h0; simp [jacobiSym.zero_left hp.one_lt]
      · rw [if_neg h0]
        have hcop : Nat.Coprime b p := (hp.coprime_iff_not_dvd.mpr
          (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero h0) (Finset.mem_range.mp hb))).symm
        have hsq : jacobiSym (b : ℤ) p ^ 2 = 1 := jacobiSym.sq_one (by simpa [Int.gcd] using hcop)
        have hnorm1 : ‖(jacobiSym (b : ℤ) p : ℂ)‖ ^ 2 = 1 := by
          rw [Complex.norm_intCast, sq_abs]; exact_mod_cast hsq
        rw [hnorm1, one_mul]
    rw [Finset.sum_congr rfl hterm, ← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hp.pos)]
    simp only [if_true, zero_add]
    rw [Finset.sum_congr rfl (fun b hb => if_neg (Finset.mem_erase.mp hb).1),
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_range.mpr hp.pos), Finset.card_range, nsmul_eq_mul]
  have hparsevalR : ∑ b ∈ Finset.range p, ‖gaussSum p b‖ ^ 2 = (p : ℝ) * ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast hparseval
  rw [hlhs] at hparsevalR
  have hp1_ne : ((p - 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hp.two_le; omega)
  exact mul_left_cancel₀ hp1_ne (by linarith)

lemma norm_eC_sub_one (t : ℝ) : ‖eC t - 1‖ = 2 * |Real.sin (Real.pi * t)| := by
  have h1 : eC t - 1 = eC (t / 2) * (eC (t / 2) - eC (-(t / 2))) := by
    rw [mul_sub, ← eC_add, ← eC_add]
    have ha : t / 2 + t / 2 = t := by ring
    have hb : t / 2 + -(t / 2) = 0 := by ring
    rw [ha, hb, eC_zero]
  have h2 : eC (t / 2) - eC (-(t / 2)) = 2 * Complex.I * (Real.sin (Real.pi * t) : ℂ) := by
    unfold eC
    have ha : 2 * (Real.pi : ℂ) * Complex.I * ((t / 2 : ℝ) : ℂ) = ((Real.pi * t : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    have hb : 2 * (Real.pi : ℂ) * Complex.I * ((-(t / 2) : ℝ) : ℂ) = ((-(Real.pi * t) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [ha, hb, Complex.exp_mul_I, Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  rw [h1, h2, norm_mul, eC_norm, one_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_I,
    mul_one, Complex.norm_real, Real.norm_eq_abs]

lemma geom_eC_bound {q k : ℕ} (hq : 2 ≤ q) (hk1 : 1 ≤ k) (hk2 : k < q) (M : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 M, eC (((k * n : ℕ) : ℝ) / (q : ℝ))‖ ≤
      (q : ℝ) / (2 * ((min k (q - k) : ℕ) : ℝ)) := by
  let t : ℝ := (k : ℝ) / (q : ℝ)
  have hq_pos : (0 : ℝ) < (q : ℝ) := by positivity
  have ht_pos : 0 < t := div_pos (by exact_mod_cast hk1) hq_pos
  have ht_lt1 : t < 1 := (div_lt_one hq_pos).mpr (by exact_mod_cast hk2)
  have hsin_pos : 0 < Real.sin (Real.pi * t) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ht_pos) (by nlinarith [Real.pi_pos])
  have hden_ne : eC t - 1 ≠ 0 := by
    intro h0
    have hnorm := norm_eC_sub_one t
    rw [h0, norm_zero, abs_of_pos hsin_pos] at hnorm
    linarith
  have hsum : ∑ n ∈ Finset.Icc 1 M, eC (((k * n : ℕ) : ℝ) / (q : ℝ)) =
      eC t * ∑ j ∈ Finset.range M, (eC t) ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_bij (fun n _ => n - 1)
      (fun n hn => Finset.mem_range.mpr (by have := Finset.mem_Icc.mp hn; omega))
      (fun a ha b hb hab => by have := Finset.mem_Icc.mp ha; have := Finset.mem_Icc.mp hb; omega)
      (fun j hj => ⟨j + 1, Finset.mem_Icc.mpr ⟨by omega, by have := Finset.mem_range.mp hj; omega⟩, by omega⟩)
      (fun n hn => ?_)
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    rw [eC_pow_nat, ← eC_add]
    congr 1; dsimp [t]
    have hsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by simpa using Nat.cast_sub hn1
    rw [hsub]; push_cast; ring
  have hnorm_sum : ‖∑ n ∈ Finset.Icc 1 M, eC (((k * n : ℕ) : ℝ) / (q : ℝ))‖ ≤
      1 / Real.sin (Real.pi * t) := by
    rw [hsum, norm_mul, eC_norm, one_mul, geom_sum_eq (sub_ne_zero.mp hden_ne), norm_div,
      norm_eC_sub_one, abs_of_pos hsin_pos]
    have hnum : ‖(eC t) ^ M - 1‖ ≤ 2 := by
      calc ‖(eC t) ^ M - 1‖ ≤ ‖(eC t) ^ M‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, eC_norm, one_pow, norm_one]; norm_num
    rw [div_le_div_iff₀ (by positivity) hsin_pos]
    nlinarith
  have hsin_ge : 2 * ((min k (q - k) : ℕ) : ℝ) / (q : ℝ) ≤ Real.sin (Real.pi * t) := by
    by_cases hhalf : k ≤ q - k
    · have hmin : ((min k (q - k) : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast min_eq_left hhalf
      rw [hmin]
      have hle : Real.pi * t ≤ Real.pi / 2 := by
        dsimp [t]
        rw [← mul_div_assoc, div_le_div_iff₀ hq_pos (by norm_num : (0 : ℝ) < 2)]
        have h2 : (2 : ℝ) * (k : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 2 * k ≤ q)
        nlinarith [Real.pi_pos]
      have h1 := Real.mul_le_sin (mul_nonneg Real.pi_pos.le ht_pos.le) hle
      have heq : 2 / Real.pi * (Real.pi * t) = 2 * (k : ℝ) / (q : ℝ) := by
        dsimp [t]; field_simp [Real.pi_ne_zero, hq_pos.ne']
      linarith
    · have hlt : q - k ≤ k := by omega
      have hmin : ((min k (q - k) : ℕ) : ℝ) = ((q - k : ℕ) : ℝ) := by exact_mod_cast min_eq_right hlt
      rw [hmin, ← Real.sin_pi_sub]
      have harg : Real.pi - Real.pi * t = Real.pi * (((q - k : ℕ) : ℝ) / (q : ℝ)) := by
        dsimp [t]; rw [Nat.cast_sub hk2.le]; field_simp [hq_pos.ne']
      rw [harg]
      have hle : Real.pi * (((q - k : ℕ) : ℝ) / (q : ℝ)) ≤ Real.pi / 2 := by
        rw [← mul_div_assoc, div_le_div_iff₀ hq_pos (by norm_num : (0 : ℝ) < 2)]
        have h2 : (2 : ℝ) * ((q - k : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 2 * (q - k) ≤ q)
        nlinarith [Real.pi_pos]
      have h1 := Real.mul_le_sin (by positivity [Real.pi_pos]) hle
      have heq : 2 / Real.pi * (Real.pi * (((q - k : ℕ) : ℝ) / (q : ℝ))) =
          2 * ((q - k : ℕ) : ℝ) / (q : ℝ) := by field_simp [Real.pi_ne_zero, hq_pos.ne']
      linarith
  have hmin_pos : (0 : ℝ) < ((min k (q - k) : ℕ) : ℝ) := by
    have : 1 ≤ min k (q - k) := le_min hk1 (by omega)
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  refine hnorm_sum.trans ?_
  rw [div_le_div_iff₀ hsin_pos (by positivity), one_mul]
  have := (div_le_iff₀ hq_pos).mp hsin_ge
  linarith

lemma harmonic_le_one_add_log (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / (k : ℝ) ≤ 1 + Real.log (n : ℝ) := by
  induction n with
  | zero => omega
  | succ m ih =>
    by_cases hm : m = 0
    · subst hm; simp
    · have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm
      have hsplit : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hsplit, Finset.sum_insert (by simp)]
      have hstep : (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
        have hmR : (0 : ℝ) < (m : ℝ) := by positivity
        have hm1R : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
        rw [← Real.log_div hm1R.ne' hmR.ne']
        have h1 : Real.log ((m : ℝ) / ((m + 1 : ℕ) : ℝ)) ≤ (m : ℝ) / ((m + 1 : ℕ) : ℝ) - 1 :=
          Real.log_le_sub_one_of_pos (div_pos hmR hm1R)
        have hneg : Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) = -Real.log ((m : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
          rw [← Real.log_inv, inv_div]
        have hsub : (m : ℝ) / ((m + 1 : ℕ) : ℝ) - 1 = -(1 / ((m + 1 : ℕ) : ℝ)) := by
          push_cast; field_simp [hm1R.ne']; ring
        linarith
      linarith [ih hm1]

lemma polya_vinogradov_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (M : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 M, (jacobiSym (n : ℤ) p : ℂ)‖ ≤ Real.sqrt (p : ℝ) * (1 + Real.log (p : ℝ)) := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hp_pos : (0 : ℝ) < (p : ℝ) := by positivity
  have hG_norm : ‖gaussSum p 1‖ = Real.sqrt (p : ℝ) := by
    have hsq := gaussSum_norm_sq hp hp2
    rw [← Real.sqrt_sq (norm_nonneg (gaussSum p 1)), hsq]
  have hid : gaussSum p 1 * ∑ n ∈ Finset.Icc 1 M, (jacobiSym (n : ℤ) p : ℂ) =
      ∑ b ∈ Finset.Ico 1 p, (jacobiSym (b : ℤ) p : ℂ) *
        ∑ n ∈ Finset.Icc 1 M, eC (((b * n : ℕ) : ℝ) / (p : ℝ)) := by
    rw [Finset.mul_sum]
    have h1 : ∑ n ∈ Finset.Icc 1 M, gaussSum p 1 * (jacobiSym (n : ℤ) p : ℂ) =
        ∑ n ∈ Finset.Icc 1 M, gaussSum p n := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [mul_comm, ← gaussSum_mul hp hp2 n]
    rw [h1]
    have h2 : ∀ n ∈ Finset.Icc 1 M, gaussSum p n =
        ∑ b ∈ Finset.Ico 1 p, (jacobiSym (b : ℤ) p : ℂ) * eC (((b * n : ℕ) : ℝ) / (p : ℝ)) := fun n _ => by
      unfold gaussSum
      rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hp.pos)]
      simp only [Nat.cast_zero, jacobiSym.zero_left hp.one_lt, Int.cast_zero, zero_mul, zero_add]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext b; simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Ico]; omega
    rw [Finset.sum_congr rfl h2, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => (Finset.mul_sum _ _ _).symm
  have hbound : Real.sqrt (p : ℝ) * ‖∑ n ∈ Finset.Icc 1 M, (jacobiSym (n : ℤ) p : ℂ)‖ ≤
      (p : ℝ) * (1 + Real.log (p : ℝ)) := by
    rw [← hG_norm, ← norm_mul, hid]
    calc ‖∑ b ∈ Finset.Ico 1 p, (jacobiSym (b : ℤ) p : ℂ) *
            ∑ n ∈ Finset.Icc 1 M, eC (((b * n : ℕ) : ℝ) / (p : ℝ))‖
        ≤ ∑ b ∈ Finset.Ico 1 p, ‖(jacobiSym (b : ℤ) p : ℂ) *
            ∑ n ∈ Finset.Icc 1 M, eC (((b * n : ℕ) : ℝ) / (p : ℝ))‖ := norm_sum_le _ _
      _ ≤ ∑ b ∈ Finset.Ico 1 p, (p : ℝ) / (2 * ((min b (p - b) : ℕ) : ℝ)) := by
          refine Finset.sum_le_sum fun b hb => ?_
          rw [norm_mul]
          have hb1 : 1 ≤ b := (Finset.mem_Ico.mp hb).1
          have hb2 : b < p := (Finset.mem_Ico.mp hb).2
          have hj1 : ‖(jacobiSym (b : ℤ) p : ℂ)‖ ≤ 1 := by
            rw [Complex.norm_intCast]
            have hcop : Nat.Coprime b p := (hp.coprime_iff_not_dvd.mpr
              (Nat.not_dvd_of_pos_of_lt hb1 hb2)).symm
            have hsq : jacobiSym (b : ℤ) p ^ 2 = 1 := jacobiSym.sq_one (by simpa [Int.gcd] using hcop)
            have : |(jacobiSym (b : ℤ) p : ℝ)| ^ 2 = 1 := by rw [sq_abs]; exact_mod_cast hsq
            nlinarith [abs_nonneg (jacobiSym (b : ℤ) p : ℝ)]
          calc ‖(jacobiSym (b : ℤ) p : ℂ)‖ * ‖∑ n ∈ Finset.Icc 1 M, eC (((b * n : ℕ) : ℝ) / (p : ℝ))‖
              ≤ 1 * ((p : ℝ) / (2 * ((min b (p - b) : ℕ) : ℝ))) :=
                mul_le_mul hj1 (geom_eC_bound hp.two_le hb1 hb2 M) (norm_nonneg _) zero_le_one
            _ = (p : ℝ) / (2 * ((min b (p - b) : ℕ) : ℝ)) := one_mul _
      _ ≤ (p : ℝ) * (1 + Real.log (p : ℝ)) := by
          let h : ℕ := p / 2
          have hp_odd : Odd p := hp.odd_of_ne_two hp2
          have h2h : 2 * h + 1 = p := by rcases hp_odd with ⟨k, rfl⟩; dsimp [h]; omega
          have hsplit : Finset.Ico 1 p = Finset.Icc 1 h ∪ Finset.Icc (h + 1) (2 * h) := by
            ext b; simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_Icc]; omega
          have hdisj : Disjoint (Finset.Icc 1 h) (Finset.Icc (h + 1) (2 * h)) := by
            rw [Finset.disjoint_left]; intro b hb1 hb2
            simp only [Finset.mem_Icc] at hb1 hb2; omega
          rw [hsplit, Finset.sum_union hdisj]
          have hs1 : ∑ b ∈ Finset.Icc 1 h, (p : ℝ) / (2 * ((min b (p - b) : ℕ) : ℝ)) =
              (p : ℝ) / 2 * ∑ b ∈ Finset.Icc 1 h, (1 : ℝ) / (b : ℝ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun b hb => ?_
            have hb' := Finset.mem_Icc.mp hb
            rw [min_eq_left (by omega : b ≤ p - b)]; ring
          have hs2 : ∑ b ∈ Finset.Icc (h + 1) (2 * h), (p : ℝ) / (2 * ((min b (p - b) : ℕ) : ℝ)) =
              (p : ℝ) / 2 * ∑ b ∈ Finset.Icc 1 h, (1 : ℝ) / (b : ℝ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_bij (fun b _ => p - b)
              (fun b hb => Finset.mem_Icc.mpr (by have := Finset.mem_Icc.mp hb; omega))
              (fun a ha b hb hab => by have := Finset.mem_Icc.mp ha; have := Finset.mem_Icc.mp hb; omega)
              (fun c hc => ⟨p - c, Finset.mem_Icc.mpr (by have := Finset.mem_Icc.mp hc; omega),
                by have := Finset.mem_Icc.mp hc; omega⟩)
              (fun b hb => ?_)
            have hb' := Finset.mem_Icc.mp hb
            rw [min_eq_right (by omega : p - b ≤ b)]; ring
          rw [hs1, hs2]
          have hh1 : 1 ≤ h := by omega
          have hharm := harmonic_le_one_add_log h hh1
          have hlog_le : Real.log (h : ℝ) ≤ Real.log (p : ℝ) :=
            Real.log_le_log (by positivity) (by exact_mod_cast (by omega : h ≤ p))
          nlinarith [hp_pos]
  have hsq : Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) = (p : ℝ) := Real.mul_self_sqrt hp_pos.le
  have hsq_pos : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp_pos
  have hbound' : Real.sqrt (p : ℝ) * ‖∑ n ∈ Finset.Icc 1 M, (jacobiSym (n : ℤ) p : ℂ)‖ ≤
      Real.sqrt (p : ℝ) * (Real.sqrt (p : ℝ) * (1 + Real.log (p : ℝ))) := by
    calc Real.sqrt (p : ℝ) * ‖∑ n ∈ Finset.Icc 1 M, (jacobiSym (n : ℤ) p : ℂ)‖
        ≤ (p : ℝ) * (1 + Real.log (p : ℝ)) := hbound
      _ = Real.sqrt (p : ℝ) * (Real.sqrt (p : ℝ) * (1 + Real.log (p : ℝ))) := by
          rw [← mul_assoc, hsq]
  exact le_of_mul_le_mul_left hbound' hsq_pos

/- ### Section 2: Gallagher's Additive Large Sieve & Prime-Modulus Multiplicative Large Sieve -/

lemma intervalIntegral_eC_int (k : ℤ) :
    ∫ t in (0 : ℝ)..1, eC ((k : ℝ) * t) = if k = 0 then (1 : ℂ) else 0 := by
  split_ifs with hk
  · subst hk; simp [eC_zero]
  · let c : ℂ := 2 * Real.pi * Complex.I * (k : ℂ)
    have hc : c ≠ 0 := by
      dsimp [c]; simp [Real.pi_ne_zero, Complex.I_ne_zero, hk]
    let F : ℝ → ℂ := fun t => c⁻¹ * eC ((k : ℝ) * t)
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt F (eC ((k : ℝ) * t)) t := fun t _ => by
      have hlin : HasDerivAt (fun s : ℝ => c * (s : ℂ)) c t := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c
      have hexp : HasDerivAt (fun s : ℝ => Complex.exp (c * (s : ℂ))) (Complex.exp (c * (t : ℂ)) * c) t :=
        hlin.cexp
      have hmul := hexp.const_mul c⁻¹
      have hF : (fun s : ℝ => c⁻¹ * Complex.exp (c * (s : ℂ))) = F := by
        ext s; dsimp [F, eC, c]; congr 2; push_cast; ring
      have hval : c⁻¹ * (Complex.exp (c * (t : ℂ)) * c) = eC ((k : ℝ) * t) := by
        have harg : c * (t : ℂ) = 2 * Real.pi * Complex.I * (((k : ℝ) * t : ℝ) : ℂ) := by
          dsimp [c]; push_cast; ring
        rw [harg, mul_comm (Complex.exp _), ← mul_assoc, inv_mul_cancel₀ hc, one_mul]; rfl
      rw [hF, hval] at hmul
      exact hmul
    have hint : IntervalIntegrable (fun t : ℝ => eC ((k : ℝ) * t)) MeasureTheory.volume 0 1 := by
      refine Continuous.intervalIntegrable ?_ 0 1
      unfold eC
      exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)))
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    dsimp [F]
    rw [mul_one, mul_zero, eC_int k, eC_zero, sub_self]

lemma gallagher_sobolev {f f' : ℝ → ℂ} (hderiv : ∀ t, HasDerivAt f (f' t) t)
    (hf'_cont : Continuous f') (α δ : ℝ) (hδ : 0 < δ) :
    ‖f α‖ ^ 2 ≤ (1 / δ) * (∫ t in (α - δ / 2)..(α + δ / 2), ‖f t‖ ^ 2) +
      ∫ t in (α - δ / 2)..(α + δ / 2), ‖f t‖ * ‖f' t‖ := by
  have hf_cont : Continuous f := continuous_iff_continuousAt.mpr fun t => (hderiv t).continuousAt
  let g : ℝ → ℝ := fun t => ‖f t‖ ^ 2
  let g' : ℝ → ℝ := fun t => 2 * ((f t).re * (f' t).re + (f t).im * (f' t).im)
  have hg_deriv : ∀ t, HasDerivAt g (g' t) t := fun t => by
    have hre : HasDerivAt (fun s => (f s).re) (f' t).re t :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hderiv t)
    have him : HasDerivAt (fun s => (f s).im) (f' t).im t :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hderiv t)
    have hsq : HasDerivAt (fun s => (f s).re ^ 2 + (f s).im ^ 2)
        (2 * (f t).re ^ (2 - 1) * (f' t).re + 2 * (f t).im ^ (2 - 1) * (f' t).im) t :=
      (hre.pow 2).add (him.pow 2)
    have hgeq : (fun s => (f s).re ^ 2 + (f s).im ^ 2) = g := by
      ext s; dsimp [g]; rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have hval : 2 * (f t).re ^ (2 - 1) * (f' t).re + 2 * (f t).im ^ (2 - 1) * (f' t).im = g' t := by
      dsimp [g']; ring
    rw [hgeq, hval] at hsq
    exact hsq
  have hg'_cont : Continuous g' := by
    dsimp [g']
    exact continuous_const.mul
      (((Complex.continuous_re.comp hf_cont).mul (Complex.continuous_re.comp hf'_cont)).add
       ((Complex.continuous_im.comp hf_cont).mul (Complex.continuous_im.comp hf'_cont)))
  have hg'_abs : ∀ t, |g' t| ≤ 2 * (‖f t‖ * ‖f' t‖) := fun t => by
    dsimp [g']
    have hcs : ((f t).re * (f' t).re + (f t).im * (f' t).im) ^ 2 ≤ (‖f t‖ * ‖f' t‖) ^ 2 := by
      rw [mul_pow, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      nlinarith [sq_nonneg ((f t).re * (f' t).im - (f t).im * (f' t).re)]
    have habs : |(f t).re * (f' t).re + (f t).im * (f' t).im| ≤ ‖f t‖ * ‖f' t‖ := by
      rw [← sq_abs] at hcs
      nlinarith [abs_nonneg ((f t).re * (f' t).re + (f t).im * (f' t).im),
        mul_nonneg (norm_nonneg (f t)) (norm_nonneg (f' t))]
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hg_cont : Continuous g := (continuous_norm.comp hf_cont).pow 2
  have hpt_right : ∀ t ∈ Set.Icc α (α + δ / 2),
      g α ≤ g t + ∫ s in α..(α + δ / 2), |g' s| := fun t ht => by
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hg_deriv s)
      (hg'_cont.intervalIntegrable α t)
    have h1 : g α - g t = -(∫ s in α..t, g' s) := by linarith
    have h2 : -(∫ s in α..t, g' s) ≤ ∫ s in α..t, |g' s| := by
      calc -(∫ s in α..t, g' s) ≤ |∫ s in α..t, g' s| := neg_le_abs _
        _ ≤ ∫ s in α..t, |g' s| := intervalIntegral.abs_integral_le_integral_abs ht.1
    have h3 : ∫ s in α..t, |g' s| ≤ ∫ s in α..(α + δ / 2), |g' s| := by
      have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
        (hg'_cont.abs.intervalIntegrable α t) (hg'_cont.abs.intervalIntegrable t (α + δ / 2))
      have hnn : 0 ≤ ∫ s in t..(α + δ / 2), |g' s| :=
        intervalIntegral.integral_nonneg ht.2 fun s _ => abs_nonneg _
      linarith
    linarith
  have hpt_left : ∀ t ∈ Set.Icc (α - δ / 2) α,
      g α ≤ g t + ∫ s in (α - δ / 2)..α, |g' s| := fun t ht => by
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hg_deriv s)
      (hg'_cont.intervalIntegrable t α)
    have h1 : g α - g t = ∫ s in t..α, g' s := by linarith
    have h2 : ∫ s in t..α, g' s ≤ ∫ s in t..α, |g' s| :=
      (le_abs_self _).trans (intervalIntegral.abs_integral_le_integral_abs ht.2)
    have h3 : ∫ s in t..α, |g' s| ≤ ∫ s in (α - δ / 2)..α, |g' s| := by
      have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
        (hg'_cont.abs.intervalIntegrable (α - δ / 2) t) (hg'_cont.abs.intervalIntegrable t α)
      have hnn : 0 ≤ ∫ s in (α - δ / 2)..t, |g' s| :=
        intervalIntegral.integral_nonneg ht.1 fun s _ => abs_nonneg _
      linarith
    linarith
  have hint_L : (δ / 2) * g α ≤ (∫ t in (α - δ / 2)..α, g t) + (δ / 2) * (∫ s in (α - δ / 2)..α, |g' s|) := by
    have h1 := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (by linarith : α - δ / 2 ≤ α)
      intervalIntegrable_const ((hg_cont.add continuous_const).intervalIntegrable _ _) hpt_left
    simp only [Pi.add_apply] at h1
    rw [intervalIntegral.integral_const, smul_eq_mul,
      intervalIntegral.integral_add (hg_cont.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul] at h1
    have hlen : α - (α - δ / 2) = δ / 2 := by ring
    rw [hlen] at h1; exact h1
  have hint_R : (δ / 2) * g α ≤ (∫ t in α..(α + δ / 2), g t) + (δ / 2) * (∫ s in α..(α + δ / 2), |g' s|) := by
    have h1 := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (by linarith : α ≤ α + δ / 2)
      intervalIntegrable_const ((hg_cont.add continuous_const).intervalIntegrable _ _) hpt_right
    simp only [Pi.add_apply] at h1
    rw [intervalIntegral.integral_const, smul_eq_mul,
      intervalIntegral.integral_add (hg_cont.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul] at h1
    have hlen : α + δ / 2 - α = δ / 2 := by ring
    rw [hlen] at h1; exact h1
  have hadd_g := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hg_cont.intervalIntegrable (α - δ / 2) α) (hg_cont.intervalIntegrable α (α + δ / 2))
  have hadd_g' := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hg'_cont.abs.intervalIntegrable (α - δ / 2) α) (hg'_cont.abs.intervalIntegrable α (α + δ / 2))
  have hcomb : δ * g α ≤ (∫ t in (α - δ / 2)..(α + δ / 2), g t) +
      (δ / 2) * (∫ s in (α - δ / 2)..(α + δ / 2), |g' s|) := by
    rw [← hadd_g, ← hadd_g']; linarith
  have hbound_g' : ∫ s in (α - δ / 2)..(α + δ / 2), |g' s| ≤
      2 * ∫ s in (α - δ / 2)..(α + δ / 2), ‖f s‖ * ‖f' s‖ := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on (by linarith) (hg'_cont.abs.intervalIntegrable _ _)
      ((continuous_const.mul ((continuous_norm.comp hf_cont).mul (continuous_norm.comp hf'_cont))).intervalIntegrable _ _)
      (fun s _ => hg'_abs s)
  have hcomb2 : g α * δ ≤ (∫ t in (α - δ / 2)..(α + δ / 2), g t) +
      δ * ∫ s in (α - δ / 2)..(α + δ / 2), ‖f s‖ * ‖f' s‖ := by nlinarith
  have hdiv : g α ≤ ((∫ t in (α - δ / 2)..(α + δ / 2), g t) +
      δ * ∫ s in (α - δ / 2)..(α + δ / 2), ‖f s‖ * ‖f' s‖) / δ :=
    (le_div_iff₀ hδ).mpr hcomb2
  calc ‖f α‖ ^ 2 = g α := rfl
    _ ≤ ((∫ t in (α - δ / 2)..(α + δ / 2), g t) +
        δ * ∫ s in (α - δ / 2)..(α + δ / 2), ‖f s‖ * ‖f' s‖) / δ := hdiv
    _ = (1 / δ) * (∫ t in (α - δ / 2)..(α + δ / 2), ‖f t‖ ^ 2) +
        ∫ s in (α - δ / 2)..(α + δ / 2), ‖f s‖ * ‖f' s‖ := by dsimp [g]; field_simp [hδ.ne']

lemma sum_disjoint_intervals_le {h : ℝ → ℝ} (hh_cont : Continuous h) (hh_nn : ∀ t, 0 ≤ h t)
    {n : ℕ} (a b : Fin n → ℝ) (hab : ∀ i, a i ≤ b i)
    (hord : ∀ i : Fin n, ∀ hi : i.1 + 1 < n, b i ≤ a ⟨i.1 + 1, hi⟩)
    (hlo : ∀ i, 0 ≤ a i) (hhi : ∀ i, b i ≤ 1) :
    ∑ i : Fin n, ∫ t in (a i)..(b i), h t ≤ ∫ t in (0 : ℝ)..1, h t := by
  induction n with
  | zero => simp; exact intervalIntegral.integral_nonneg (by norm_num) fun t _ => hh_nn t
  | succ m ih =>
    have hsplit : ∀ k : ℕ, (hk : k ≤ m + 1) →
        ∑ i : Fin k, ∫ t in (a ⟨i.1, lt_of_lt_of_le i.2 hk⟩)..(b ⟨i.1, lt_of_lt_of_le i.2 hk⟩), h t ≤
        ∫ t in (0 : ℝ)..(if h0 : k = 0 then 0 else b ⟨k - 1, by omega⟩), h t := by
      intro k hk
      induction k with
      | zero => simp
      | succ r ihr =>
        rw [Fin.sum_univ_castSucc]
        have hr_le : r ≤ m + 1 := by omega
        have hprev := ihr hr_le
        split_ifs at hprev with hr0
        · subst hr0
          simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add, one_ne_zero, ↓reduceDIte,
            Fin.val_last, Nat.sub_self]
          have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
            (hh_cont.intervalIntegrable 0 (a ⟨0, by omega⟩))
            (hh_cont.intervalIntegrable (a ⟨0, by omega⟩) (b ⟨0, by omega⟩))
          have hnn : 0 ≤ ∫ t in (0 : ℝ)..(a ⟨0, by omega⟩), h t :=
            intervalIntegral.integral_nonneg (hlo ⟨0, by omega⟩) fun t _ => hh_nn t
          linarith
        · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte, Nat.add_sub_cancel,
            Fin.val_castSucc, Fin.val_last]
          have hgap : b ⟨r - 1, by omega⟩ ≤ a ⟨r, by omega⟩ := by
            have hstep := hord ⟨r - 1, by omega⟩ (show (r - 1) + 1 < m + 1 by omega)
            have heq : (⟨(r - 1) + 1, show (r - 1) + 1 < m + 1 by omega⟩ : Fin (m + 1)) = ⟨r, by omega⟩ :=
              Fin.ext (show (r - 1) + 1 = r by omega)
            rw [heq] at hstep; exact hstep
          have hadd1 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
            (hh_cont.intervalIntegrable 0 (b ⟨r - 1, by omega⟩))
            (hh_cont.intervalIntegrable (b ⟨r - 1, by omega⟩) (a ⟨r, by omega⟩))
          have hadd2 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
            (hh_cont.intervalIntegrable 0 (a ⟨r, by omega⟩))
            (hh_cont.intervalIntegrable (a ⟨r, by omega⟩) (b ⟨r, by omega⟩))
          have hnn : 0 ≤ ∫ t in (b ⟨r - 1, by omega⟩)..(a ⟨r, by omega⟩), h t :=
            intervalIntegral.integral_nonneg hgap fun t _ => hh_nn t
          linarith
    have hmain := hsplit (m + 1) le_rfl
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte, Nat.add_sub_cancel] at hmain
    have htail := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hh_cont.intervalIntegrable 0 (b ⟨m, by omega⟩))
      (hh_cont.intervalIntegrable (b ⟨m, by omega⟩) 1)
    have hnn : 0 ≤ ∫ t in (b ⟨m, by omega⟩)..(1 : ℝ), h t :=
      intervalIntegral.integral_nonneg (hhi ⟨m, by omega⟩) fun t _ => hh_nn t
    linarith

lemma integral_cauchy_schwarz {u v : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hu_nn : ∀ t, 0 ≤ u t) (hv_nn : ∀ t, 0 ≤ v t) :
    ∫ t in (0 : ℝ)..1, u t * v t ≤
      Real.sqrt (∫ t in (0 : ℝ)..1, u t ^ 2) * Real.sqrt (∫ t in (0 : ℝ)..1, v t ^ 2) := by
  let A : ℝ := ∫ t in (0 : ℝ)..1, u t ^ 2
  let B : ℝ := ∫ t in (0 : ℝ)..1, v t ^ 2
  let C : ℝ := ∫ t in (0 : ℝ)..1, u t * v t
  have hA0 : 0 ≤ A := intervalIntegral.integral_nonneg (by norm_num) fun t _ => sq_nonneg _
  have hB0 : 0 ≤ B := intervalIntegral.integral_nonneg (by norm_num) fun t _ => sq_nonneg _
  have hC0 : 0 ≤ C := intervalIntegral.integral_nonneg (by norm_num) fun t _ => mul_nonneg (hu_nn t) (hv_nn t)
  have hsq : C ^ 2 ≤ A * B := by
    by_cases hA : A = 0
    · have hquad : ∀ s : ℝ, 0 ≤ s ^ 2 * A + 2 * s * C + B := fun s => by
        have hnn : 0 ≤ ∫ t in (0 : ℝ)..1, (s * u t + v t) ^ 2 :=
          intervalIntegral.integral_nonneg (by norm_num) fun t _ => sq_nonneg _
        have hexp : ∫ t in (0 : ℝ)..1, (s * u t + v t) ^ 2 = s ^ 2 * A + 2 * s * C + B := by
          have h1 : ∀ t, (s * u t + v t) ^ 2 = s ^ 2 * u t ^ 2 + (2 * s * (u t * v t) + v t ^ 2) := fun t => by ring
          simp_rw [h1]
          rw [intervalIntegral.integral_add
                (f := fun t => s ^ 2 * u t ^ 2) (g := fun t => 2 * s * (u t * v t) + v t ^ 2)
                ((continuous_const.mul (hu.pow 2)).intervalIntegrable _ _)
                (((continuous_const.mul (hu.mul hv)).add (hv.pow 2)).intervalIntegrable _ _),
              intervalIntegral.integral_add
                (f := fun t => 2 * s * (u t * v t)) (g := fun t => v t ^ 2)
                ((continuous_const.mul (hu.mul hv)).intervalIntegrable _ _)
                ((hv.pow 2).intervalIntegrable _ _),
              intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
          dsimp [A, B, C]; ring
        linarith
      rw [hA] at hquad ⊢
      by_contra hCpos
      have hC_gt : 0 < C := by nlinarith
      have := hquad (-(B + 1) / (2 * C))
      have : (-(B + 1) / (2 * C)) ^ 2 * 0 + 2 * (-(B + 1) / (2 * C)) * C + B = -1 := by
        field_simp [hC_gt.ne']; ring
      linarith
    · have hA_pos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hA)
      have hnn : 0 ≤ ∫ t in (0 : ℝ)..1, (C * u t - A * v t) ^ 2 :=
        intervalIntegral.integral_nonneg (by norm_num) fun t _ => sq_nonneg _
      have hexp : ∫ t in (0 : ℝ)..1, (C * u t - A * v t) ^ 2 = C ^ 2 * A - 2 * C * A * C + A ^ 2 * B := by
        have h1 : ∀ t, (C * u t - A * v t) ^ 2 = C ^ 2 * u t ^ 2 + (-(2 * C * A) * (u t * v t) + A ^ 2 * v t ^ 2) := fun t => by ring
        simp_rw [h1]
        rw [intervalIntegral.integral_add
              (f := fun t => C ^ 2 * u t ^ 2) (g := fun t => -(2 * C * A) * (u t * v t) + A ^ 2 * v t ^ 2)
              ((continuous_const.mul (hu.pow 2)).intervalIntegrable _ _)
              (((continuous_const.mul (hu.mul hv)).add (continuous_const.mul (hv.pow 2))).intervalIntegrable _ _),
            intervalIntegral.integral_add
              (f := fun t => -(2 * C * A) * (u t * v t)) (g := fun t => A ^ 2 * v t ^ 2)
              ((continuous_const.mul (hu.mul hv)).intervalIntegrable _ _)
              ((continuous_const.mul (hv.pow 2)).intervalIntegrable _ _),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
        dsimp [A, B, C]; ring
      nlinarith
  have hrhs : (Real.sqrt A * Real.sqrt B) ^ 2 = A * B := by
    rw [mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
  change C ≤ Real.sqrt A * Real.sqrt B
  nlinarith [Real.sqrt_nonneg A, Real.sqrt_nonneg B, mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B)]

lemma additive_large_sieve_unit_interval (N : ℕ) (a : ℕ → ℂ)
    {R : ℕ} (α : Fin R → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ i j : Fin R, i ≠ j → δ ≤ |α i - α j|)
    (hlo : ∀ i : Fin R, δ / 2 ≤ α i) (hhi : ∀ i : Fin R, α i + δ / 2 ≤ 1) :
    ∑ i : Fin R, ‖∑ n ∈ Finset.Icc 1 N, a n * eC ((n : ℝ) * α i)‖ ^ 2 ≤
      (1 / δ + Real.pi * (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  let shift : ℝ := (N : ℝ) / 2
  let f : ℝ → ℂ := fun t => ∑ n ∈ Finset.Icc 1 N, a n * eC (((n : ℝ) - shift) * t)
  let f' : ℝ → ℂ := fun t =>
    ∑ n ∈ Finset.Icc 1 N, a n * (2 * Real.pi * Complex.I * (((n : ℝ) - shift : ℝ) : ℂ)) *
      eC (((n : ℝ) - shift) * t)
  have hf_norm : ∀ t : ℝ, ‖f t‖ = ‖∑ n ∈ Finset.Icc 1 N, a n * eC ((n : ℝ) * t)‖ := fun t => by
    have h1 : f t = eC (-shift * t) * ∑ n ∈ Finset.Icc 1 N, a n * eC ((n : ℝ) * t) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => ?_
      rw [show ((n : ℝ) - shift) * t = -shift * t + (n : ℝ) * t by ring, eC_add]; ring
    rw [h1, norm_mul, eC_norm, one_mul]
  have hderiv : ∀ t, HasDerivAt f (f' t) t := fun t => by
    have hterm : ∀ n ∈ Finset.Icc 1 N,
        HasDerivAt (fun s : ℝ => a n * eC (((n : ℝ) - shift) * s))
          (a n * (2 * Real.pi * Complex.I * (((n : ℝ) - shift : ℝ) : ℂ)) * eC (((n : ℝ) - shift) * t)) t := by
      intro n _
      let c : ℂ := 2 * Real.pi * Complex.I * (((n : ℝ) - shift : ℝ) : ℂ)
      have hlin : HasDerivAt (fun s : ℝ => c * (s : ℂ)) c t := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c
      have hmul := (hlin.cexp).const_mul (a n)
      have hfn : (fun s : ℝ => a n * Complex.exp (c * (s : ℂ))) =
          (fun s : ℝ => a n * eC (((n : ℝ) - shift) * s)) := by
        ext s; dsimp [eC, c]; congr 2; push_cast; ring
      have hval : a n * (Complex.exp (c * (t : ℂ)) * c) =
          a n * (2 * Real.pi * Complex.I * (((n : ℝ) - shift : ℝ) : ℂ)) * eC (((n : ℝ) - shift) * t) := by
        have harg : c * (t : ℂ) = 2 * Real.pi * Complex.I * ((((n : ℝ) - shift) * t : ℝ) : ℂ) := by
          dsimp [c]; push_cast; ring
        rw [harg]; dsimp [eC, c]; ring
      rw [hfn, hval] at hmul
      exact hmul
    simpa [f, f'] using HasDerivAt.fun_sum hterm
  have hf_cont : Continuous f := continuous_iff_continuousAt.mpr fun t => (hderiv t).continuousAt
  have hf'_cont : Continuous f' := by
    dsimp [f']
    refine continuous_finsetSum _ fun n _ => continuous_const.mul ?_
    unfold eC
    exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)))
  -- Sort α into strictly increasing order
  have hinj : Function.Injective α := fun i j hij => by
    by_contra hne
    have := hsep i j hne
    rw [hij, sub_self, abs_zero] at this; linarith
  let S_img : Finset ℝ := Finset.univ.image α
  have hcard : S_img.card = R := by rw [Finset.card_image_of_injective _ hinj, Finset.card_fin]
  let emb : Fin R ↪o ℝ := S_img.orderEmbOfFin hcard
  have hemb_mem : ∀ k : Fin R, emb k ∈ S_img := fun k => Finset.orderEmbOfFin_mem S_img hcard k
  have hbij : ∑ i : Fin R, ‖f (α i)‖ ^ 2 = ∑ k : Fin R, ‖f (emb k)‖ ^ 2 := by
    rw [← Finset.sum_image (f := fun y => ‖f y‖ ^ 2) (fun i _ j _ h => hinj h)]
    refine (Finset.sum_bij (fun k _ => emb k) (fun k _ => hemb_mem k)
      (fun k₁ _ k₂ _ h => emb.injective h)
      (fun y hy => by
        have hrange := Finset.range_orderEmbOfFin S_img hcard
        have : y ∈ Set.range emb := by rw [hrange]; exact hy
        rcases this with ⟨k, rfl⟩
        exact ⟨k, Finset.mem_univ k, rfl⟩)
      (fun _ _ => rfl)).symm
  have hsep_emb : ∀ k : Fin R, ∀ hk : k.1 + 1 < R, emb k + δ / 2 ≤ emb ⟨k.1 + 1, hk⟩ - δ / 2 := by
    intro k hk
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (hemb_mem k)
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (hemb_mem ⟨k.1 + 1, hk⟩)
    have hlt : emb k < emb ⟨k.1 + 1, hk⟩ := emb.strictMono (by show k.1 < k.1 + 1; omega)
    have hne : i ≠ j := fun h => by subst h; linarith
    have hd := hsep i j hne
    rw [hi, hj, abs_sub_comm, abs_of_pos (by linarith)] at hd
    linarith
  have hlo_emb : ∀ k : Fin R, 0 ≤ emb k - δ / 2 := fun k => by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (hemb_mem k)
    linarith [hlo i]
  have hhi_emb : ∀ k : Fin R, emb k + δ / 2 ≤ 1 := fun k => by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (hemb_mem k)
    linarith [hhi i]
  have hsum_le : ∑ k : Fin R, ‖f (emb k)‖ ^ 2 ≤
      (1 / δ) * (∫ t in (0 : ℝ)..1, ‖f t‖ ^ 2) + ∫ t in (0 : ℝ)..1, ‖f t‖ * ‖f' t‖ := by
    calc ∑ k : Fin R, ‖f (emb k)‖ ^ 2
        ≤ ∑ k : Fin R, ((1 / δ) * (∫ t in (emb k - δ / 2)..(emb k + δ / 2), ‖f t‖ ^ 2) +
            ∫ t in (emb k - δ / 2)..(emb k + δ / 2), ‖f t‖ * ‖f' t‖) :=
          Finset.sum_le_sum fun k _ => gallagher_sobolev hderiv hf'_cont (emb k) δ hδ
      _ = (1 / δ) * (∑ k : Fin R, ∫ t in (emb k - δ / 2)..(emb k + δ / 2), ‖f t‖ ^ 2) +
            ∑ k : Fin R, ∫ t in (emb k - δ / 2)..(emb k + δ / 2), ‖f t‖ * ‖f' t‖ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ (1 / δ) * (∫ t in (0 : ℝ)..1, ‖f t‖ ^ 2) + ∫ t in (0 : ℝ)..1, ‖f t‖ * ‖f' t‖ := by
          refine add_le_add (mul_le_mul_of_nonneg_left ?_ (by positivity)) ?_
          · exact sum_disjoint_intervals_le ((continuous_norm.comp hf_cont).pow 2) (fun _ => sq_nonneg _)
              (fun k => emb k - δ / 2) (fun k => emb k + δ / 2) (fun _ => by linarith) hsep_emb hlo_emb hhi_emb
          · exact sum_disjoint_intervals_le ((continuous_norm.comp hf_cont).mul (continuous_norm.comp hf'_cont))
              (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
              (fun k => emb k - δ / 2) (fun k => emb k + δ / 2) (fun _ => by linarith) hsep_emb hlo_emb hhi_emb
  -- Parseval on [0, 1] for any finite sum ∑_{n=1}^N c_n e((n - shift) t)
  have hparseval : ∀ c : ℕ → ℂ,
      ∫ t in (0 : ℝ)..1, ‖∑ n ∈ Finset.Icc 1 N, c n * eC (((n : ℝ) - shift) * t)‖ ^ 2 =
        ∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2 := fun c => by
    have hC : ∫ t in (0 : ℝ)..1, ((‖∑ n ∈ Finset.Icc 1 N, c n * eC (((n : ℝ) - shift) * t)‖ ^ 2 : ℝ) : ℂ) =
        ∑ n ∈ Finset.Icc 1 N, ((‖c n‖ ^ 2 : ℝ) : ℂ) := by
      have hexp : ∀ t : ℝ, ((‖∑ n ∈ Finset.Icc 1 N, c n * eC (((n : ℝ) - shift) * t)‖ ^ 2 : ℝ) : ℂ) =
          ∑ n₁ ∈ Finset.Icc 1 N, ∑ n₂ ∈ Finset.Icc 1 N,
            (c n₁ * starRingEnd ℂ (c n₂)) * eC ((((n₁ : ℤ) - (n₂ : ℤ) : ℤ) : ℝ) * t) := fun t => by
        rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun n₁ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n₂ _ => ?_
        rw [map_mul, ← eC_neg]
        have he : eC (((n₁ : ℝ) - shift) * t) * eC (-(((n₂ : ℝ) - shift) * t)) =
            eC ((((n₁ : ℤ) - (n₂ : ℤ) : ℤ) : ℝ) * t) := by
          rw [← eC_add]; congr 1; push_cast; ring
        linear_combination (c n₁ * starRingEnd ℂ (c n₂)) * he
      simp_rw [hexp]
      have hint1 : ∀ n₁ ∈ Finset.Icc 1 N, ∀ n₂ ∈ Finset.Icc 1 N,
          IntervalIntegrable (fun t : ℝ => (c n₁ * starRingEnd ℂ (c n₂)) *
            eC ((((n₁ : ℤ) - (n₂ : ℤ) : ℤ) : ℝ) * t)) MeasureTheory.volume 0 1 := fun n₁ _ n₂ _ => by
        refine (Continuous.intervalIntegrable ?_ 0 1)
        exact continuous_const.mul (Complex.continuous_exp.comp
          (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id))))
      have houter : ∀ n₁ ∈ Finset.Icc 1 N,
          IntervalIntegrable (fun t : ℝ => ∑ n₂ ∈ Finset.Icc 1 N, (c n₁ * starRingEnd ℂ (c n₂)) *
            eC ((((n₁ : ℤ) - (n₂ : ℤ) : ℤ) : ℝ) * t)) MeasureTheory.volume 0 1 := fun n₁ _ => by
        refine (Continuous.intervalIntegrable ?_ 0 1)
        exact continuous_finsetSum _ fun n₂ _ => continuous_const.mul (Complex.continuous_exp.comp
          (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id))))
      rw [intervalIntegral.integral_finsetSum houter]
      refine Finset.sum_congr rfl fun n₁ hn₁ => ?_
      rw [intervalIntegral.integral_finsetSum (fun n₂ hn₂ => hint1 n₁ hn₁ n₂ hn₂)]
      have hterm : ∀ n₂ ∈ Finset.Icc 1 N,
          ∫ t in (0 : ℝ)..1, (c n₁ * starRingEnd ℂ (c n₂)) * eC ((((n₁ : ℤ) - (n₂ : ℤ) : ℤ) : ℝ) * t) =
          if n₂ = n₁ then ((‖c n₁‖ ^ 2 : ℝ) : ℂ) else 0 := fun n₂ _ => by
        rw [intervalIntegral.integral_const_mul, intervalIntegral_eC_int]
        have hiff : (n₁ : ℤ) - (n₂ : ℤ) = 0 ↔ n₂ = n₁ := by omega
        by_cases h2 : n₂ = n₁
        · rw [if_pos (hiff.mpr h2), if_pos h2]; subst h2
          rw [mul_one, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        · rw [if_neg (mt hiff.mp h2), if_neg h2, mul_zero]
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' _ _ _, if_pos hn₁]
    have hre := congrArg Complex.re hC
    rw [intervalIntegral.integral_ofReal] at hC
    exact_mod_cast hC
  have hI0 : ∫ t in (0 : ℝ)..1, ‖f t‖ ^ 2 = ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := hparseval a
  have hI1 : ∫ t in (0 : ℝ)..1, ‖f' t‖ ^ 2 ≤ (Real.pi * (N : ℝ)) ^ 2 * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
    have h1 := hparseval (fun n => a n * (2 * Real.pi * Complex.I * (((n : ℝ) - shift : ℝ) : ℂ)))
    change ∫ t in (0 : ℝ)..1, ‖f' t‖ ^ 2 = _ at h1
    rw [h1, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn1 := (Finset.mem_Icc.mp hn).1
    have hn2 := (Finset.mem_Icc.mp hn).2
    rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I,
      Complex.norm_real, mul_one, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_pow]
    have habs : |(n : ℝ) - shift| ≤ (N : ℝ) / 2 := by
      dsimp [shift]; rw [abs_le]
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have h2 : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn2
      exact ⟨by linarith, by linarith⟩
    have hcoef : (2 * Real.pi * |(n : ℝ) - shift|) ^ 2 ≤ (Real.pi * (N : ℝ)) ^ 2 := by
      have hle : 2 * Real.pi * |(n : ℝ) - shift| ≤ Real.pi * (N : ℝ) := by nlinarith [Real.pi_pos]
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi) (abs_nonneg ((n : ℝ) - shift)),
        mul_nonneg Real.pi_pos.le (Nat.cast_nonneg N)]
    rw [mul_comm (‖a n‖ ^ 2)]
    exact mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
  have hcross : ∫ t in (0 : ℝ)..1, ‖f t‖ * ‖f' t‖ ≤ Real.pi * (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
    have hcs := integral_cauchy_schwarz (continuous_norm.comp hf_cont) (continuous_norm.comp hf'_cont)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    have hS : 0 ≤ ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hsq1 : Real.sqrt (∫ t in (0 : ℝ)..1, ‖f' t‖ ^ 2) ≤ Real.pi * (N : ℝ) * Real.sqrt (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) := by
      calc Real.sqrt (∫ t in (0 : ℝ)..1, ‖f' t‖ ^ 2)
          ≤ Real.sqrt ((Real.pi * (N : ℝ)) ^ 2 * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) := Real.sqrt_le_sqrt hI1
        _ = Real.sqrt ((Real.pi * (N : ℝ)) ^ 2) * Real.sqrt (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) :=
            Real.sqrt_mul (sq_nonneg _) _
        _ = Real.pi * (N : ℝ) * Real.sqrt (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) := by
            rw [Real.sqrt_sq (by positivity [Real.pi_pos])]
    calc ∫ t in (0 : ℝ)..1, ‖f t‖ * ‖f' t‖
        ≤ Real.sqrt (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) * (Real.pi * (N : ℝ) * Real.sqrt (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2)) := by
          dsimp only [Function.comp] at hcs
          rw [hI0] at hcs
          exact hcs.trans (mul_le_mul_of_nonneg_left hsq1 (Real.sqrt_nonneg _))
      _ = Real.pi * (N : ℝ) * (Real.sqrt (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) * Real.sqrt (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2)) := by ring
      _ = Real.pi * (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by rw [Real.mul_self_sqrt hS]
  have heq_lhs : ∑ i : Fin R, ‖∑ n ∈ Finset.Icc 1 N, a n * eC ((n : ℝ) * α i)‖ ^ 2 =
      ∑ k : Fin R, ‖f (emb k)‖ ^ 2 := by
    rw [← hbij]
    exact Finset.sum_congr rfl fun i _ => by rw [hf_norm]
  rw [heq_lhs]
  calc ∑ k : Fin R, ‖f (emb k)‖ ^ 2
      ≤ (1 / δ) * (∫ t in (0 : ℝ)..1, ‖f t‖ ^ 2) + ∫ t in (0 : ℝ)..1, ‖f t‖ * ‖f' t‖ := hsum_le
    _ ≤ (1 / δ) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) + Real.pi * (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
        rw [hI0]; linarith
    _ = (1 / δ + Real.pi * (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by ring

lemma prime_quad_large_sieve {X : ℕ} (hX : 3 ≤ X) (N : ℕ) (a : ℕ → ℂ) :
    ∑ p ∈ (Nat.primesBelow X).filter (· ≠ 2),
        ‖∑ n ∈ Finset.Icc 1 N, a n * (jacobiSym (n : ℤ) p : ℂ)‖ ^ 2 ≤
      ((X : ℝ) ^ 2 + Real.pi * (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  let P := (Nat.primesBelow X).filter (· ≠ 2)
  -- Step 1: Bound each prime via Gauss sum + Cauchy-Schwarz
  have hstep1 : ∀ p ∈ P,
      ‖∑ n ∈ Finset.Icc 1 N, a n * (jacobiSym (n : ℤ) p : ℂ)‖ ^ 2 ≤
      ∑ b ∈ Finset.Ico 1 p, ‖∑ n ∈ Finset.Icc 1 N, a n * eC ((n : ℝ) * ((b : ℝ) / (p : ℝ)))‖ ^ 2 := by
    intro p hpP
    have hp_below := (Finset.mem_filter.mp hpP).1
    have hp2 := (Finset.mem_filter.mp hpP).2
    have hp := (Nat.mem_primesBelow.mp hp_below).2
    have hG_sq := gaussSum_norm_sq hp hp2
    have hid : gaussSum p 1 * ∑ n ∈ Finset.Icc 1 N, a n * (jacobiSym (n : ℤ) p : ℂ) =
        ∑ b ∈ Finset.Ico 1 p, (jacobiSym (b : ℤ) p : ℂ) *
          ∑ n ∈ Finset.Icc 1 N, a n * eC ((n : ℝ) * ((b : ℝ) / (p : ℝ))) := by
      rw [Finset.mul_sum]
      have h1 : ∀ n ∈ Finset.Icc 1 N, gaussSum p 1 * (a n * (jacobiSym (n : ℤ) p : ℂ)) =
          a n * gaussSum p n := fun n _ => by rw [gaussSum_mul hp hp2 n]; ring
      rw [Finset.sum_congr rfl h1]
      have h2' : ∀ n ∈ Finset.Icc 1 N, a n * gaussSum p n =
          ∑ b ∈ Finset.Ico 1 p, (jacobiSym (b : ℤ) p : ℂ) *
            (a n * eC ((n : ℝ) * ((b : ℝ) / (p : ℝ)))) := fun n _ => by
        unfold gaussSum
        rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hp.pos)]
        simp only [Nat.cast_zero, jacobiSym.zero_left hp.one_lt, Int.cast_zero, zero_mul, zero_add,
          Finset.mul_sum]
        refine Finset.sum_congr (by ext b; simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Ico]; omega) fun b _ => ?_
        have he : eC (((b * n : ℕ) : ℝ) / (p : ℝ)) = eC ((n : ℝ) * ((b : ℝ) / (p : ℝ))) := by
          congr 1; push_cast; ring
        rw [he]; ring
      rw [Finset.sum_congr rfl h2', Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => (Finset.mul_sum _ _ _).symm
    have hcs : (p : ℝ) * ‖∑ n ∈ Finset.Icc 1 N, a n * (jacobiSym (n : ℤ) p : ℂ)‖ ^ 2 ≤
        ((p - 1 : ℕ) : ℝ) * ∑ b ∈ Finset.Ico 1 p,
          ‖∑ n ∈ Finset.Icc 1 N, a n * eC ((n : ℝ) * ((b : ℝ) / (p : ℝ)))‖ ^ 2 := by
      conv_lhs => rw [← hG_sq, ← mul_pow, ← norm_mul, hid]
      have htri : ‖∑ b ∈ Finset.Ico 1 p, (jacobiSym (b : ℤ) p : ℂ) *
            ∑ n ∈ Finset.Icc 1 N, a n * eC ((n : ℝ) * ((b : ℝ) / (p : ℝ)))‖ ≤
          ∑ b ∈ Finset.Ico 1 p, ‖∑ n ∈ Finset.Icc 1 N, a n * eC ((n : ℝ) * ((b : ℝ) / (p : ℝ)))‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b hb => ?_)
        rw [norm_mul]
        have hb1 := (Finset.mem_Ico.mp hb).1
        have hb2 := (Finset.mem_Ico.mp hb).2
        have hcop : Nat.Coprime b p := (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hb1 hb2)).symm
        have hsq : jacobiSym (b : ℤ) p ^ 2 = 1 := jacobiSym.sq_one (by simpa [Int.gcd] using hcop)
        have hnorm1 : ‖(jacobiSym (b : ℤ) p : ℂ)‖ = 1 := by
          rw [Complex.norm_intCast]
          have : |(jacobiSym (b : ℤ) p : ℝ)| ^ 2 = 1 := by rw [sq_abs]; exact_mod_cast hsq
          nlinarith [abs_nonneg (jacobiSym (b : ℤ) p : ℝ)]
        rw [hnorm1, one_mul]
      have hsq_le : ‖∑ b ∈ Finset.Ico 1 p, (jacobiSym (b : ℤ) p : ℂ) *
            ∑ n ∈ Finset.Icc 1 N, a n * eC ((n : ℝ) * ((b : ℝ) / (p : ℝ)))‖ ^ 2 ≤
          (∑ b ∈ Finset.Ico 1 p, ‖∑ n ∈ Finset.Icc 1 N, a n * eC ((n : ℝ) * ((b : ℝ) / (p : ℝ)))‖) ^ 2 :=
        sq_le_sq.mpr (by
          rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
          exact htri)
      have hcs_fin := sq_sum_le_card_mul_sum_sq (s := Finset.Ico 1 p)
        (f := fun b => ‖∑ n ∈ Finset.Icc 1 N, a n * eC ((n : ℝ) * ((b : ℝ) / (p : ℝ)))‖)
      rw [Nat.card_Ico] at hcs_fin
      exact hsq_le.trans hcs_fin
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    have hp1_le : ((p - 1 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast Nat.sub_le p 1
    have hsum_nn : 0 ≤ ∑ b ∈ Finset.Ico 1 p, ‖∑ n ∈ Finset.Icc 1 N, a n * eC ((n : ℝ) * ((b : ℝ) / (p : ℝ)))‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    nlinarith
  -- Step 2: Apply additive large sieve to the Farey fractions {b / p : p ∈ P, 1 ≤ b < p}
  let pairs : Finset (ℕ × ℕ) := P.sigma (fun p => Finset.Ico 1 p) |>.map
    ⟨fun s => (s.1, s.2), fun s₁ s₂ h => by cases s₁; cases s₂; cases h; rfl⟩
  let ePairs : Fin pairs.card ≃ pairs := (Fintype.equivFinOfCardEq (Fintype.card_coe pairs)).symm
  let α : Fin pairs.card → ℝ := fun i => ((ePairs i).1.2 : ℝ) / ((ePairs i).1.1 : ℝ)
  let δ : ℝ := 1 / (X : ℝ) ^ 2
  have hX_pos : (0 : ℝ) < (X : ℝ) := by positivity
  have hδ : 0 < δ := by positivity
  have hmem_pair : ∀ x ∈ pairs, x.1 ∈ P ∧ 1 ≤ x.2 ∧ x.2 < x.1 := fun x hx => by
    simp only [pairs, Finset.mem_map, Finset.mem_sigma, Finset.mem_Ico] at hx
    rcases hx with ⟨⟨p, b⟩, ⟨hp, hb1, hb2⟩, rfl⟩
    exact ⟨hp, hb1, hb2⟩
  have hsep : ∀ i j : Fin pairs.card, i ≠ j → δ ≤ |α i - α j| := by
    intro i j hij
    have hne : (ePairs i).1 ≠ (ePairs j).1 := fun h => hij (ePairs.injective (Subtype.ext h))
    obtain ⟨hp1P, hb1_lo, hb1_hi⟩ := hmem_pair _ (ePairs i).2
    obtain ⟨hp2P, hb2_lo, hb2_hi⟩ := hmem_pair _ (ePairs j).2
    have hp1_lt : (ePairs i).1.1 < X := (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hp1P).1).1
    have hp1_pr : (ePairs i).1.1.Prime := (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hp1P).1).2
    have hp2_lt : (ePairs j).1.1 < X := (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hp2P).1).1
    have hp2_pr : (ePairs j).1.1.Prime := (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hp2P).1).2
    let p₁ := (ePairs i).1.1; let b₁ := (ePairs i).1.2
    let p₂ := (ePairs j).1.1; let b₂ := (ePairs j).1.2
    have hnum_ne : (b₁ : ℤ) * (p₂ : ℤ) - (b₂ : ℤ) * (p₁ : ℤ) ≠ 0 := by
      intro h0
      have heqN : b₁ * p₂ = b₂ * p₁ := by
        have : (b₁ : ℤ) * (p₂ : ℤ) = (b₂ : ℤ) * (p₁ : ℤ) := sub_eq_zero.mp h0
        exact_mod_cast this
      by_cases hp_eq : p₁ = p₂
      · have hb_eq : b₁ = b₂ := Nat.eq_of_mul_eq_mul_right hp2_pr.pos (by rwa [hp_eq] at heqN)
        exact hne (Prod.ext hp_eq hb_eq)
      · have hdvd : p₁ ∣ b₁ * p₂ := ⟨b₂, by linarith⟩
        have hcop12 : Nat.Coprime p₁ p₂ := (Nat.coprime_primes hp1_pr hp2_pr).mpr hp_eq
        have hdvd_b1 : p₁ ∣ b₁ := hcop12.dvd_of_dvd_mul_right hdvd
        exact Nat.not_dvd_of_pos_of_lt hb1_lo hb1_hi hdvd_b1
    have hnum_ge : (1 : ℝ) ≤ |(b₁ : ℝ) * (p₂ : ℝ) - (b₂ : ℝ) * (p₁ : ℝ)| := by
      have h1 : (1 : ℤ) ≤ |(b₁ : ℤ) * (p₂ : ℤ) - (b₂ : ℤ) * (p₁ : ℤ)| := Int.one_le_abs hnum_ne
      exact_mod_cast h1
    have hp1_pos : (0 : ℝ) < (p₁ : ℝ) := by exact_mod_cast hp1_pr.pos
    have hp2_pos : (0 : ℝ) < (p₂ : ℝ) := by exact_mod_cast hp2_pr.pos
    have hdiff : |α i - α j| = |(b₁ : ℝ) * (p₂ : ℝ) - (b₂ : ℝ) * (p₁ : ℝ)| / ((p₁ : ℝ) * (p₂ : ℝ)) := by
      dsimp [α, p₁, p₂, b₁, b₂]
      rw [div_sub_div _ _ hp1_pos.ne' hp2_pos.ne', abs_div, abs_of_pos (mul_pos hp1_pos hp2_pos)]
      congr 2; ring
    rw [hdiff]
    have hden_le : (p₁ : ℝ) * (p₂ : ℝ) ≤ (X : ℝ) ^ 2 := by
      have h1 : (p₁ : ℝ) ≤ (X : ℝ) := by exact_mod_cast hp1_lt.le
      have h2 : (p₂ : ℝ) ≤ (X : ℝ) := by exact_mod_cast hp2_lt.le
      nlinarith
    dsimp [δ]
    rw [div_le_div_iff₀ (sq_pos_of_pos hX_pos) (mul_pos hp1_pos hp2_pos)]
    nlinarith
  have hlo : ∀ i : Fin pairs.card, δ / 2 ≤ α i := fun i => by
    obtain ⟨hp1P, hb1_lo, _⟩ := hmem_pair _ (ePairs i).2
    have hp1_lt : (ePairs i).1.1 < X := (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hp1P).1).1
    have hp1_pr : (ePairs i).1.1.Prime := (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hp1P).1).2
    dsimp [α, δ]
    have hp1_pos : (0 : ℝ) < ((ePairs i).1.1 : ℝ) := by exact_mod_cast hp1_pr.pos
    have hb1_ge : (1 : ℝ) ≤ ((ePairs i).1.2 : ℝ) := by exact_mod_cast hb1_lo
    have hp1_le : ((ePairs i).1.1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hp1_lt.le
    have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (by omega : 1 ≤ X)
    rw [div_div, div_le_div_iff₀ (by positivity) hp1_pos]
    nlinarith
  have hhi : ∀ i : Fin pairs.card, α i + δ / 2 ≤ 1 := fun i => by
    obtain ⟨hp1P, _, hb1_hi⟩ := hmem_pair _ (ePairs i).2
    have hp1_lt : (ePairs i).1.1 < X := (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hp1P).1).1
    have hp1_pr : (ePairs i).1.1.Prime := (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hp1P).1).2
    dsimp [α, δ]
    have hp1_pos : (0 : ℝ) < ((ePairs i).1.1 : ℝ) := by exact_mod_cast hp1_pr.pos
    have hb1_le : ((ePairs i).1.2 : ℝ) ≤ ((ePairs i).1.1 : ℝ) - 1 := by
      have : (ePairs i).1.2 + 1 ≤ (ePairs i).1.1 := hb1_hi
      have : ((ePairs i).1.2 : ℝ) + 1 ≤ ((ePairs i).1.1 : ℝ) := by exact_mod_cast this
      linarith
    have hp1_le : ((ePairs i).1.1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hp1_lt.le
    have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (by omega : 1 ≤ X)
    have hsub : 1 / (X : ℝ) ^ 2 / 2 ≤ 1 / ((ePairs i).1.1 : ℝ) := by
      rw [div_div, div_le_div_iff₀ (by positivity) hp1_pos]; nlinarith
    have h1 : ((ePairs i).1.2 : ℝ) / ((ePairs i).1.1 : ℝ) ≤ 1 - 1 / ((ePairs i).1.1 : ℝ) := by
      rw [le_sub_iff_add_le, ← add_div, div_le_one hp1_pos]; linarith
    linarith
  have hls := additive_large_sieve_unit_interval N a α δ hδ hsep hlo hhi
  have hinv_δ : 1 / δ = (X : ℝ) ^ 2 := by dsimp [δ]; field_simp [hX_pos.ne']
  rw [hinv_δ] at hls
  have hsum_eq : ∑ p ∈ P, ∑ b ∈ Finset.Ico 1 p,
        ‖∑ n ∈ Finset.Icc 1 N, a n * eC ((n : ℝ) * ((b : ℝ) / (p : ℝ)))‖ ^ 2 =
      ∑ i : Fin pairs.card, ‖∑ n ∈ Finset.Icc 1 N, a n * eC ((n : ℝ) * α i)‖ ^ 2 := by
    have hsig : ∑ x ∈ P.sigma (fun p => Finset.Ico 1 p),
          ‖∑ n ∈ Finset.Icc 1 N, a n * eC ((n : ℝ) * ((x.2 : ℝ) / (x.1 : ℝ)))‖ ^ 2 =
        ∑ p ∈ P, ∑ b ∈ Finset.Ico 1 p,
          ‖∑ n ∈ Finset.Icc 1 N, a n * eC ((n : ℝ) * ((b : ℝ) / (p : ℝ)))‖ ^ 2 :=
      Finset.sum_sigma P (fun p => Finset.Ico 1 p)
        (fun x => ‖∑ n ∈ Finset.Icc 1 N, a n * eC ((n : ℝ) * ((x.2 : ℝ) / (x.1 : ℝ)))‖ ^ 2)
    rw [← hsig]
    have h1 : ∑ x ∈ P.sigma (fun p => Finset.Ico 1 p),
          ‖∑ n ∈ Finset.Icc 1 N, a n * eC ((n : ℝ) * ((x.2 : ℝ) / (x.1 : ℝ)))‖ ^ 2 =
        ∑ y ∈ pairs, ‖∑ n ∈ Finset.Icc 1 N, a n * eC ((n : ℝ) * ((y.2 : ℝ) / (y.1 : ℝ)))‖ ^ 2 := by
      dsimp [pairs]; rw [Finset.sum_map]; rfl
    rw [h1, ← Finset.sum_coe_sort pairs]
    exact (Equiv.sum_comp ePairs (fun y : pairs =>
      ‖∑ n ∈ Finset.Icc 1 N, a n * eC ((n : ℝ) * ((y.1.2 : ℝ) / (y.1.1 : ℝ)))‖ ^ 2)).symm
  exact (Finset.sum_le_sum hstep1).trans (hsum_eq.le.trans hls)

/- ### Section 3: Elementary Divisor Bound, Representation Counts, and Square-Pair Bound -/

lemma nat_succ_le_two_pow (t : ℕ) : t + 1 ≤ 2 ^ t := by
  induction t with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; omega

lemma divisors_card_le_pow (K : ℕ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ((1 : ℝ) / (K : ℝ)) := by
  have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hK_ge1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hprime_pow : ∀ (p e : ℕ), p.Prime → 1 ≤ e →
      ((p ^ e).divisors.card : ℝ) / ((p ^ e : ℕ) : ℝ) ^ ((1 : ℝ) / (K : ℝ)) ≤
        if p < 2 ^ K then (K : ℝ) else 1 := by
    intro p e hp he
    have hcard : (p ^ e).divisors.card = e + 1 := by
      rw [Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]
    have hpe_pos : (0 : ℝ) < ((p ^ e : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.pos e
    have hden_pos : (0 : ℝ) < ((p ^ e : ℕ) : ℝ) ^ ((1 : ℝ) / (K : ℝ)) := Real.rpow_pos_of_pos hpe_pos _
    rw [hcard, div_le_iff₀ hden_pos]
    split_ifs with hlt
    · let t : ℕ := e / K
      have ht_le : t * K ≤ e := Nat.div_mul_le_self e K
      have he_le : e + 1 ≤ K * (t + 1) := by
        have hlt' : e < (t + 1) * K := by
          dsimp [t]
          have := Nat.lt_div_mul_add (a := e) (b := K) (by omega)
          linarith
        nlinarith
      have h1 : ((e + 1 : ℕ) : ℝ) ≤ (K : ℝ) * ((2 : ℝ) ^ t) := by
        have hnat : e + 1 ≤ K * 2 ^ t := he_le.trans (Nat.mul_le_mul_left K (nat_succ_le_two_pow t))
        exact_mod_cast hnat
      have h2 : (2 : ℝ) ^ t ≤ ((p ^ e : ℕ) : ℝ) ^ ((1 : ℝ) / (K : ℝ)) := by
        have hpow : (((2 : ℝ) ^ t) ^ (K : ℝ)) ^ ((1 : ℝ) / (K : ℝ)) = (2 : ℝ) ^ t := by
          rw [one_div, Real.rpow_rpow_inv (by positivity) hK_pos.ne']
        rw [← hpow]
        refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
        rw [Real.rpow_natCast, ← pow_mul]
        have h2e : (2 : ℝ) ^ (t * K) ≤ (2 : ℝ) ^ e :=
          pow_le_pow_right₀ (by norm_num) ht_le
        have h2p : (2 : ℝ) ^ e ≤ ((p ^ e : ℕ) : ℝ) := by
          rw [Nat.cast_pow]
          exact pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hp.two_le) e
        exact h2e.trans h2p
      nlinarith
    · push Not at hlt
      rw [one_mul]
      have h1 : ((e + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ e := by exact_mod_cast nat_succ_le_two_pow e
      have h2 : (2 : ℝ) ^ e ≤ ((p ^ e : ℕ) : ℝ) ^ ((1 : ℝ) / (K : ℝ)) := by
        have hpow : (((2 : ℝ) ^ e) ^ (K : ℝ)) ^ ((1 : ℝ) / (K : ℝ)) = (2 : ℝ) ^ e := by
          rw [one_div, Real.rpow_rpow_inv (by positivity) hK_pos.ne']
        rw [← hpow]
        refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
        rw [Real.rpow_natCast, ← pow_mul, mul_comm e K, pow_mul]
        have h2Kp : ((2 ^ K : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hlt
        rw [Nat.cast_pow]
        have : ((2 : ℝ) ^ K) ^ e ≤ (p : ℝ) ^ e :=
          pow_le_pow_left₀ (by positivity) (by exact_mod_cast hlt) e
        exact this
      exact h1.trans h2
  have hmult : ∀ n : ℕ, 1 ≤ n →
      (n.divisors.card : ℝ) / (n : ℝ) ^ ((1 : ℝ) / (K : ℝ)) ≤
        ∏ p ∈ n.primeFactors, if p < 2 ^ K then (K : ℝ) else 1 := by
    intro n
    induction n using Nat.recOnPosPrimePosCoprime with
    | zero => intro h0; omega
    | one => intro _; simp
    | prime_pow p e hp he =>
      intro _
      rw [Nat.primeFactors_prime_pow he.ne' hp, Finset.prod_singleton]
      exact hprime_pow p e hp he
    | coprime a b ha hb hcop iha ihb =>
      intro _
      have ha1 : 1 ≤ a := by omega
      have hb1 : 1 ≤ b := by omega
      have hcard : ((a * b).divisors.card : ℝ) = (a.divisors.card : ℝ) * (b.divisors.card : ℝ) := by
        exact_mod_cast hcop.card_divisors_mul
      have hrpow : ((a * b : ℕ) : ℝ) ^ ((1 : ℝ) / (K : ℝ)) =
          (a : ℝ) ^ ((1 : ℝ) / (K : ℝ)) * (b : ℝ) ^ ((1 : ℝ) / (K : ℝ)) := by
        rw [Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
      have hdisj : Disjoint a.primeFactors b.primeFactors := hcop.disjoint_primeFactors
      have hpf : (a * b).primeFactors = a.primeFactors ∪ b.primeFactors :=
        Nat.primeFactors_mul (by omega) (by omega)
      rw [hcard, hrpow, mul_div_mul_comm, hpf, Finset.prod_union hdisj]
      exact mul_le_mul (iha ha1) (ihb hb1) (by positivity)
        (Finset.prod_nonneg fun p _ => by split_ifs <;> positivity)
  refine ⟨(K : ℝ) ^ (2 ^ K), by positivity, fun n hn => ?_⟩
  have hbound := hmult n hn
  have hprod_le : (∏ p ∈ n.primeFactors, if p < 2 ^ K then (K : ℝ) else 1) ≤ (K : ℝ) ^ (2 ^ K) := by
    let S1 := n.primeFactors.filter (· < 2 ^ K)
    let S2 := n.primeFactors.filter (fun p => ¬ p < 2 ^ K)
    have hsplit : ∏ p ∈ n.primeFactors, (if p < 2 ^ K then (K : ℝ) else 1) =
        (∏ p ∈ S1, (if p < 2 ^ K then (K : ℝ) else 1)) *
        (∏ p ∈ S2, (if p < 2 ^ K then (K : ℝ) else 1)) := by
      exact (Finset.prod_filter_mul_prod_filter_not n.primeFactors (· < 2 ^ K) _).symm
    have hS1 : ∏ p ∈ S1, (if p < 2 ^ K then (K : ℝ) else 1) = (K : ℝ) ^ S1.card := by
      rw [Finset.prod_congr rfl (fun p hp => if_pos (Finset.mem_filter.mp hp).2), Finset.prod_const]
    have hS2 : ∏ p ∈ S2, (if p < 2 ^ K then (K : ℝ) else 1) = 1 := by
      rw [Finset.prod_congr rfl (fun p hp => if_neg (Finset.mem_filter.mp hp).2), Finset.prod_const_one]
    have hcard_le : S1.card ≤ 2 ^ K := by
      have hsub : S1 ⊆ Finset.range (2 ^ K) := fun p hp =>
        Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
      exact (Finset.card_le_card hsub).trans (by rw [Finset.card_range])
    rw [hsplit, hS1, hS2, mul_one]
    exact pow_le_pow_right₀ hK_ge1 hcard_le
  have hden_pos : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / (K : ℝ)) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  exact (div_le_iff₀ hden_pos).mp (hbound.trans hprod_le)

lemma isSquare_iff_even_factorization {n : ℕ} (hn : n ≠ 0) :
    IsSquare n ↔ ∀ p : ℕ, Even (n.factorization p) := by
  constructor
  · rintro ⟨r, rfl⟩ p
    have hr : r ≠ 0 := by intro h; subst h; simp at hn
    rw [Nat.factorization_mul hr hr, Finsupp.add_apply]
    exact ⟨r.factorization p, rfl⟩
  · intro heven
    let r : ℕ := ∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)
    refine ⟨r, ?_⟩
    have hr2 : r * r = ∏ p ∈ n.primeFactors, p ^ (n.factorization p) := by
      dsimp [r]
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [← pow_add]
      obtain ⟨t, ht⟩ := heven p
      congr 1; omega
    exact (Nat.prod_primeFactors_pow_factorization hn).trans hr2.symm

lemma coprime_isSquare_of_mul {a b : ℕ} (hcop : Nat.Coprime a b) (hsq : IsSquare (a * b)) :
    IsSquare a ∧ IsSquare b := by
  by_cases ha : a = 0
  · subst ha
    have hb : b = 1 := by simpa using hcop
    subst hb; exact ⟨⟨0, by ring⟩, ⟨1, by ring⟩⟩
  by_cases hb : b = 0
  · subst hb
    have ha1 : a = 1 := by simpa using hcop
    subst ha1; exact ⟨⟨1, by ring⟩, ⟨0, by ring⟩⟩
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have hev := (isSquare_iff_even_factorization hab).mp hsq
  have hadd : ∀ p, (a * b).factorization p = a.factorization p + b.factorization p := fun p => by
    rw [Nat.factorization_mul ha hb, Finsupp.add_apply]
  have hzero : ∀ p, a.factorization p = 0 ∨ b.factorization p = 0 := fun p => by
    by_contra h
    push Not at h
    have hp_a : p ∈ a.primeFactors := Nat.mem_primeFactors.mpr
      ⟨Nat.prime_of_mem_primeFactors (Nat.support_factorization a ▸ Finsupp.mem_support_iff.mpr h.1),
       (Nat.prime_of_mem_primeFactors (Nat.support_factorization a ▸ Finsupp.mem_support_iff.mpr h.1)).dvd_iff_one_le_factorization ha |>.mpr (Nat.pos_of_ne_zero h.1), ha⟩
    have hp_b : p ∈ b.primeFactors := Nat.mem_primeFactors.mpr
      ⟨Nat.prime_of_mem_primeFactors (Nat.support_factorization b ▸ Finsupp.mem_support_iff.mpr h.2),
       (Nat.prime_of_mem_primeFactors (Nat.support_factorization b ▸ Finsupp.mem_support_iff.mpr h.2)).dvd_iff_one_le_factorization hb |>.mpr (Nat.pos_of_ne_zero h.2), hb⟩
    exact Finset.disjoint_left.mp hcop.disjoint_primeFactors hp_a hp_b
  constructor
  · rw [isSquare_iff_even_factorization ha]
    intro p
    rcases hzero p with h0 | h0
    · rw [h0]; exact ⟨0, rfl⟩
    · have := hev p; rw [hadd p, h0, add_zero] at this; exact this
  · rw [isSquare_iff_even_factorization hb]
    intro p
    rcases hzero p with h0 | h0
    · have := hev p; rw [hadd p, h0, zero_add] at this; exact this
    · rw [h0]; exact ⟨0, rfl⟩

def repCount (k m u : ℕ) : ℕ :=
  ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 m)).filter (fun f => ∏ i : Fin k, f i = u)).card

lemma sum_repCount (k m : ℕ) (_hm : 1 ≤ m) :
    ∑ u ∈ Finset.Icc 1 (m ^ k), repCount k m u = m ^ k := by
  let S := Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 m)
  have hmaps : ∀ f ∈ S, (∏ i : Fin k, f i) ∈ Finset.Icc 1 (m ^ k) := fun f hf => by
    have hmem : ∀ i : Fin k, 1 ≤ f i ∧ f i ≤ m := fun i => Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hf i)
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · calc 1 = ∏ _i : Fin k, 1 := by simp
        _ ≤ ∏ i : Fin k, f i := Finset.prod_le_prod' fun i _ => (hmem i).1
    · calc ∏ i : Fin k, f i ≤ ∏ _i : Fin k, m := Finset.prod_le_prod' fun i _ => (hmem i).2
        _ = m ^ k := by simp
  have hcard : S.card = m ^ k := by
    dsimp [S]
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.card_Icc]
    simp
  exact (Finset.card_eq_sum_card_fiberwise hmaps).symm.trans hcard

lemma jacobiSym_prod_left {ι : Type*} (s : Finset ι) (f : ι → ℕ) (q : ℕ) :
    jacobiSym ((∏ i ∈ s, f i : ℕ) : ℤ) q = ∏ i ∈ s, jacobiSym (f i : ℤ) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Nat.cast_mul, jacobiSym.mul_left, ih]

lemma S_pow_eq_sum_repCount_complex (k m q : ℕ) (_hm : 1 ≤ m) :
    (∑ n ∈ Finset.Icc 1 m, (jacobiSym (n : ℤ) q : ℂ)) ^ k =
      ∑ u ∈ Finset.Icc 1 (m ^ k), (repCount k m u : ℂ) * (jacobiSym (u : ℤ) q : ℂ) := by
  let S := Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 m)
  have hmaps : ∀ f ∈ S, (∏ i : Fin k, f i) ∈ Finset.Icc 1 (m ^ k) := fun f hf => by
    have hmem : ∀ i : Fin k, 1 ≤ f i ∧ f i ≤ m := fun i => Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hf i)
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · calc 1 = ∏ _i : Fin k, 1 := by simp
        _ ≤ ∏ i : Fin k, f i := Finset.prod_le_prod' fun i _ => (hmem i).1
    · calc ∏ i : Fin k, f i ≤ ∏ _i : Fin k, m := Finset.prod_le_prod' fun i _ => (hmem i).2
        _ = m ^ k := by simp
  rw [Finset.sum_pow']
  have hprod : ∑ f ∈ S, ∏ i : Fin k, (jacobiSym (f i : ℤ) q : ℂ) =
      ∑ f ∈ S, (jacobiSym ((∏ i : Fin k, f i : ℕ) : ℤ) q : ℂ) := by
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [jacobiSym_prod_left, Int.cast_prod]
  rw [hprod, ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hconst : ∑ f ∈ S.filter (fun f => ∏ i : Fin k, f i = u),
      (jacobiSym ((∏ i : Fin k, f i : ℕ) : ℤ) q : ℂ) =
      ∑ _f ∈ S.filter (fun f => ∏ i : Fin k, f i = u), (jacobiSym (u : ℤ) q : ℂ) :=
    Finset.sum_congr rfl fun f hf => by rw [(Finset.mem_filter.mp hf).2]
  rw [hconst, Finset.sum_const, nsmul_eq_mul]; rfl

lemma S_pow_eq_sum_repCount_real (k m q : ℕ) (hm : 1 ≤ m) :
    (∑ n ∈ Finset.Icc 1 m, (jacobiSym (n : ℤ) q : ℝ)) ^ k =
      ∑ u ∈ Finset.Icc 1 (m ^ k), (repCount k m u : ℝ) * (jacobiSym (u : ℤ) q : ℝ) := by
  apply Complex.ofReal_injective
  push_cast
  exact S_pow_eq_sum_repCount_complex k m q hm

lemma repCount_le_divisors_pow (k m u : ℕ) (hk : 1 ≤ k) (hu : 1 ≤ u) :
    repCount k m u ≤ u.divisors.card ^ (k - 1) := by
  induction k generalizing u with
  | zero => omega
  | succ r ih =>
    by_cases hr : r = 0
    · subst hr
      simp only [zero_add, Nat.sub_self, pow_zero]
      unfold repCount
      refine Finset.card_le_one.mpr fun f₁ hf₁ f₂ hf₂ => ?_
      have h1 := (Finset.mem_filter.mp hf₁).2
      have h2 := (Finset.mem_filter.mp hf₂).2
      ext i
      have hi : i = 0 := Fin.eq_zero i
      subst hi
      simp only [Fin.prod_univ_one] at h1 h2
      omega
    · have hr1 : 1 ≤ r := Nat.pos_of_ne_zero hr
      have hsub : r + 1 - 1 = r := by omega
      rw [hsub]
      let S := Fintype.piFinset (fun _ : Fin (r + 1) => Finset.Icc 1 m)
      let F := S.filter (fun f => ∏ i : Fin (r + 1), f i = u)
      have hmaps : ∀ f ∈ F, f (Fin.last r) ∈ u.divisors := fun f hf => by
        have hprod := (Finset.mem_filter.mp hf).2
        rw [Fin.prod_univ_castSucc] at hprod
        exact Nat.mem_divisors.mpr ⟨⟨∏ i : Fin r, f i.castSucc, by linarith⟩, by omega⟩
      have hfib := Finset.card_eq_sum_card_fiberwise hmaps
      change F.card ≤ u.divisors.card ^ r
      rw [hfib]
      have hterm : ∀ d ∈ u.divisors, (F.filter (fun f => f (Fin.last r) = d)).card ≤ u.divisors.card ^ (r - 1) := by
        intro d hd
        have hdvd : d ∣ u := (Nat.mem_divisors.mp hd).1
        have hd_pos : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd (by omega)
        have hud_pos : 1 ≤ u / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hd_pos
        let F' := (Fintype.piFinset (fun _ : Fin r => Finset.Icc 1 m)).filter (fun g => ∏ i : Fin r, g i = u / d)
        have hinj : (F.filter (fun f => f (Fin.last r) = d)).card ≤ F'.card := by
          refine Finset.card_le_card_of_injOn (fun f => Fin.init f) ?_ ?_
          · intro f hf
            have hfF := (Finset.mem_filter.mp hf).1
            have hflast := (Finset.mem_filter.mp hf).2
            have hfS := (Finset.mem_filter.mp hfF).1
            have hprod := (Finset.mem_filter.mp hfF).2
            rw [Fin.prod_univ_castSucc, hflast] at hprod
            refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i =>
              Fintype.mem_piFinset.mp hfS i.castSucc, ?_⟩
            exact Nat.eq_div_of_mul_eq_left (by omega) hprod
          · intro f₁ hf₁ f₂ hf₂ heq
            have h1 := (Finset.mem_filter.mp hf₁).2
            have h2 := (Finset.mem_filter.mp hf₂).2
            ext i
            refine Fin.lastCases ?_ (fun j => ?_) i
            · rw [h1, h2]
            · exact congrFun heq j
        have hrec := ih (u / d) hr1 hud_pos
        have hdiv_le : (u / d).divisors.card ≤ u.divisors.card := by
          refine Finset.card_le_card fun x hx => ?_
          have hx1 := (Nat.mem_divisors.mp hx).1
          exact Nat.mem_divisors.mpr ⟨hx1.trans (Nat.div_dvd_of_dvd hdvd), by omega⟩
        calc (F.filter (fun f => f (Fin.last r) = d)).card
            ≤ repCount r m (u / d) := hinj
          _ ≤ (u / d).divisors.card ^ (r - 1) := hrec
          _ ≤ u.divisors.card ^ (r - 1) := Nat.pow_le_pow_left hdiv_le _
      calc ∑ d ∈ u.divisors, (F.filter (fun f => f (Fin.last r) = d)).card
          ≤ ∑ _d ∈ u.divisors, u.divisors.card ^ (r - 1) := Finset.sum_le_sum hterm
        _ = u.divisors.card * u.divisors.card ^ (r - 1) := by rw [Finset.sum_const, smul_eq_mul]
        _ = u.divisors.card ^ r := by
            rw [mul_comm, ← pow_succ]
            congr 1; omega

lemma square_pair_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      ∑ u ∈ Finset.Icc 1 (m ^ 2), ∑ v ∈ Finset.Icc 1 (m ^ 2),
        (if IsSquare (u * v) then (repCount 2 m u : ℝ) * (repCount 2 m v : ℝ) else 0) ≤
      C * (m : ℝ) ^ ((11 : ℝ) / 4) := by
  obtain ⟨C8, hC8_pos, hC8⟩ := divisors_card_le_pow 8 (by norm_num)
  refine ⟨9 * C8 ^ 2, by positivity, fun m hm => ?_⟩
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm_ge1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hrep_le : ∀ u ∈ Finset.Icc 1 (m ^ 2), (repCount 2 m u : ℝ) ≤ C8 * (m : ℝ) ^ ((1 : ℝ) / 4) := by
    intro u hu
    have hu1 := (Finset.mem_Icc.mp hu).1
    have hu2 := (Finset.mem_Icc.mp hu).2
    have h1 : (repCount 2 m u : ℝ) ≤ (u.divisors.card : ℝ) := by
      have := repCount_le_divisors_pow 2 m u (by norm_num) hu1
      simpa using (Nat.cast_le (α := ℝ)).mpr this
    have h2 := hC8 u hu1
    have h3 : (u : ℝ) ^ ((1 : ℝ) / 8) ≤ (m : ℝ) ^ ((1 : ℝ) / 4) := by
      calc (u : ℝ) ^ ((1 : ℝ) / 8)
          ≤ ((m ^ 2 : ℕ) : ℝ) ^ ((1 : ℝ) / 8) := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hu2) (by positivity)
        _ = ((m : ℝ) ^ (2 : ℝ)) ^ ((1 : ℝ) / 8) := by rw [Nat.cast_pow, Real.rpow_two]
        _ = (m : ℝ) ^ ((1 : ℝ) / 4) := by rw [← Real.rpow_mul hm_pos.le]; norm_num
    exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 hC8_pos.le))
  -- Count pairs (u, v) ∈ Icc 1 (m^2) × Icc 1 (m^2) with IsSquare (u * v)
  let sqPairs := (Finset.Icc 1 (m ^ 2) ×ˢ Finset.Icc 1 (m ^ 2)).filter (fun p => IsSquare (p.1 * p.2))
  have hsum_le : ∑ u ∈ Finset.Icc 1 (m ^ 2), ∑ v ∈ Finset.Icc 1 (m ^ 2),
        (if IsSquare (u * v) then (repCount 2 m u : ℝ) * (repCount 2 m v : ℝ) else 0) ≤
      (sqPairs.card : ℝ) * (C8 ^ 2 * (m : ℝ) ^ ((1 : ℝ) / 2)) := by
    rw [← Finset.sum_product']
    have hrew : ∑ p ∈ Finset.Icc 1 (m ^ 2) ×ˢ Finset.Icc 1 (m ^ 2),
          (if IsSquare (p.1 * p.2) then (repCount 2 m p.1 : ℝ) * (repCount 2 m p.2 : ℝ) else 0) =
        ∑ p ∈ sqPairs, (repCount 2 m p.1 : ℝ) * (repCount 2 m p.2 : ℝ) := by
      rw [Finset.sum_filter]
    rw [hrew]
    have hterm : ∀ p ∈ sqPairs, (repCount 2 m p.1 : ℝ) * (repCount 2 m p.2 : ℝ) ≤
        C8 ^ 2 * (m : ℝ) ^ ((1 : ℝ) / 2) := fun p hp => by
      have hp_mem := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      have h1 := hrep_le p.1 hp_mem.1
      have h2 := hrep_le p.2 hp_mem.2
      have hmul := mul_le_mul h1 h2 (by positivity) (by positivity)
      have hr : (C8 * (m : ℝ) ^ ((1 : ℝ) / 4)) * (C8 * (m : ℝ) ^ ((1 : ℝ) / 4)) =
          C8 ^ 2 * (m : ℝ) ^ ((1 : ℝ) / 2) := by
        have hp2 : (m : ℝ) ^ ((1 : ℝ) / 4) * (m : ℝ) ^ ((1 : ℝ) / 4) = (m : ℝ) ^ ((1 : ℝ) / 2) := by
          rw [← Real.rpow_add hm_pos]; norm_num
        calc (C8 * (m : ℝ) ^ ((1 : ℝ) / 4)) * (C8 * (m : ℝ) ^ ((1 : ℝ) / 4))
            = C8 ^ 2 * ((m : ℝ) ^ ((1 : ℝ) / 4) * (m : ℝ) ^ ((1 : ℝ) / 4)) := by ring
          _ = C8 ^ 2 * (m : ℝ) ^ ((1 : ℝ) / 2) := by rw [hp2]
      linarith
    exact (Finset.sum_le_sum hterm).trans (by rw [Finset.sum_const, nsmul_eq_mul])
  -- Bound sqPairs.card by ∑ g ∈ Icc 1 (m^2), (m^2 / g)
  have hcard_sq : (sqPairs.card : ℝ) ≤ (m : ℝ) ^ 2 * (1 + 2 * Real.log (m : ℝ)) := by
    have hmaps : ∀ p ∈ sqPairs, Nat.gcd p.1 p.2 ∈ Finset.Icc 1 (m ^ 2) := fun p hp => by
      have hp_mem := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      have h1 := (Finset.mem_Icc.mp hp_mem.1).1
      have h2 := (Finset.mem_Icc.mp hp_mem.1).2
      exact Finset.mem_Icc.mpr ⟨Nat.gcd_pos_of_pos_left p.2 (by omega),
        (Nat.gcd_le_left p.2 (by omega)).trans h2⟩
    have hfib : sqPairs.card = ∑ g ∈ Finset.Icc 1 (m ^ 2), (sqPairs.filter (fun p => Nat.gcd p.1 p.2 = g)).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    rw [hfib, Nat.cast_sum]
    have hfib_le : ∀ g ∈ Finset.Icc 1 (m ^ 2),
        ((sqPairs.filter (fun p => Nat.gcd p.1 p.2 = g)).card : ℝ) ≤ (m : ℝ) ^ 2 / (g : ℝ) := by
      intro g hg
      have hg1 := (Finset.mem_Icc.mp hg).1
      have hg_pos : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg1
      let B := Nat.sqrt (m ^ 2 / g)
      have hinj : (sqPairs.filter (fun p => Nat.gcd p.1 p.2 = g)).card ≤ (Finset.Icc 1 B ×ˢ Finset.Icc 1 B).card := by
        refine Finset.card_le_card_of_injOn (fun p => (Nat.sqrt (p.1 / g), Nat.sqrt (p.2 / g))) ?_ ?_
        · intro p hp
          have hp_sq := (Finset.mem_filter.mp hp).1
          have hgcd := (Finset.mem_filter.mp hp).2
          have hp_mem := Finset.mem_product.mp (Finset.mem_filter.mp hp_sq).1
          have hp1 := Finset.mem_Icc.mp hp_mem.1
          have hp2 := Finset.mem_Icc.mp hp_mem.2
          have hd1 : g ∣ p.1 := hgcd ▸ Nat.gcd_dvd_left p.1 p.2
          have hd2 : g ∣ p.2 := hgcd ▸ Nat.gcd_dvd_right p.1 p.2
          have hq1_pos : 1 ≤ p.1 / g := Nat.div_pos (Nat.le_of_dvd (by omega) hd1) hg1
          have hq2_pos : 1 ≤ p.2 / g := Nat.div_pos (Nat.le_of_dvd (by omega) hd2) hg1
          have hq1_le : p.1 / g ≤ m ^ 2 / g := Nat.div_le_div_right hp1.2
          have hq2_le : p.2 / g ≤ m ^ 2 / g := Nat.div_le_div_right hp2.2
          exact Finset.mem_product.mpr
            ⟨Finset.mem_Icc.mpr ⟨Nat.le_sqrt.mpr (by omega), Nat.sqrt_le_sqrt hq1_le⟩,
             Finset.mem_Icc.mpr ⟨Nat.le_sqrt.mpr (by omega), Nat.sqrt_le_sqrt hq2_le⟩⟩
        · intro p₁ hp₁ p₂ hp₂ heq
          have hpair_eq : ∀ p ∈ sqPairs.filter (fun p => Nat.gcd p.1 p.2 = g),
              p.1 = g * (Nat.sqrt (p.1 / g)) ^ 2 ∧ p.2 = g * (Nat.sqrt (p.2 / g)) ^ 2 := by
            intro p hp
            have hp_sq := (Finset.mem_filter.mp hp).1
            have hgcd := (Finset.mem_filter.mp hp).2
            have hisq := (Finset.mem_filter.mp hp_sq).2
            have hd1 : g ∣ p.1 := hgcd ▸ Nat.gcd_dvd_left p.1 p.2
            have hd2 : g ∣ p.2 := hgcd ▸ Nat.gcd_dvd_right p.1 p.2
            have hcop : Nat.Coprime (p.1 / g) (p.2 / g) := by
              rw [← hgcd]; exact Nat.coprime_div_gcd_div_gcd (by omega)
            have hprod_eq : p.1 * p.2 = g ^ 2 * ((p.1 / g) * (p.2 / g)) := by
              have h1 := Nat.mul_div_cancel' hd1
              have h2 := Nat.mul_div_cancel' hd2
              calc p.1 * p.2 = (g * (p.1 / g)) * (g * (p.2 / g)) := by rw [h1, h2]
                _ = g ^ 2 * ((p.1 / g) * (p.2 / g)) := by ring
            have hq_sq : IsSquare ((p.1 / g) * (p.2 / g)) := by
              rcases hisq with ⟨r, hr⟩
              have hgr : g ^ 2 ∣ r ^ 2 := ⟨(p.1 / g) * (p.2 / g), by linarith [sq r]⟩
              have hgd : g ∣ r := (Nat.pow_dvd_pow_iff (by norm_num : 2 ≠ 0)).mp hgr
              obtain ⟨s, rfl⟩ := hgd
              refine ⟨s, ?_⟩
              have hmul : g ^ 2 * ((p.1 / g) * (p.2 / g)) = g ^ 2 * (s * s) := by linarith
              exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < g ^ 2) hmul
            obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := coprime_isSquare_of_mul hcop hq_sq
            have ha_sq : Nat.sqrt (p.1 / g) = a := by rw [ha, Nat.sqrt_eq]
            have hb_sq : Nat.sqrt (p.2 / g) = b := by rw [hb, Nat.sqrt_eq]
            constructor
            · rw [ha_sq, sq, ← ha, Nat.mul_div_cancel' hd1]
            · rw [hb_sq, sq, ← hb, Nat.mul_div_cancel' hd2]
          have h1 := hpair_eq p₁ hp₁
          have h2 := hpair_eq p₂ hp₂
          have hfst : Nat.sqrt (p₁.1 / g) = Nat.sqrt (p₂.1 / g) := congrArg Prod.fst heq
          have hsnd : Nat.sqrt (p₁.2 / g) = Nat.sqrt (p₂.2 / g) := congrArg Prod.snd heq
          exact Prod.ext (by rw [h1.1, h2.1, hfst]) (by rw [h1.2, h2.2, hsnd])
      have hcardB : ((Finset.Icc 1 B ×ˢ Finset.Icc 1 B).card : ℝ) ≤ (m : ℝ) ^ 2 / (g : ℝ) := by
        rw [Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel]
        have hB2 : B * B ≤ m ^ 2 / g := Nat.sqrt_le (m ^ 2 / g)
        have hB2g : B * B * g ≤ m ^ 2 := (Nat.mul_le_mul_right g hB2).trans (Nat.div_mul_le_self (m ^ 2) g)
        have hB2R : ((B * B : ℕ) : ℝ) * (g : ℝ) ≤ (m : ℝ) ^ 2 := by exact_mod_cast hB2g
        exact (le_div_iff₀ hg_pos).mpr hB2R
      exact ((Nat.cast_le (α := ℝ)).mpr hinj).trans hcardB
    calc ∑ g ∈ Finset.Icc 1 (m ^ 2), ((sqPairs.filter (fun p => Nat.gcd p.1 p.2 = g)).card : ℝ)
        ≤ ∑ g ∈ Finset.Icc 1 (m ^ 2), (m : ℝ) ^ 2 / (g : ℝ) := Finset.sum_le_sum hfib_le
      _ = (m : ℝ) ^ 2 * ∑ g ∈ Finset.Icc 1 (m ^ 2), (1 : ℝ) / (g : ℝ) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun g _ => by ring
      _ ≤ (m : ℝ) ^ 2 * (1 + Real.log ((m ^ 2 : ℕ) : ℝ)) := by
          refine mul_le_mul_of_nonneg_left (harmonic_le_one_add_log (m ^ 2) (by nlinarith)) (sq_nonneg _)
      _ = (m : ℝ) ^ 2 * (1 + 2 * Real.log (m : ℝ)) := by
          rw [Nat.cast_pow, Real.log_pow]; ring
  -- Bound 1 + 2 log m ≤ 9 * m^(1/4)
  have hlog_le : 1 + 2 * Real.log (m : ℝ) ≤ 9 * (m : ℝ) ^ ((1 : ℝ) / 4) := by
    have hq_pos : 0 < (m : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hm_pos _
    have hq_ge1 : 1 ≤ (m : ℝ) ^ ((1 : ℝ) / 4) := Real.one_le_rpow hm_ge1 (by positivity)
    have hl : Real.log ((m : ℝ) ^ ((1 : ℝ) / 4)) ≤ (m : ℝ) ^ ((1 : ℝ) / 4) - 1 :=
      Real.log_le_sub_one_of_pos hq_pos
    rw [Real.log_rpow hm_pos] at hl
    linarith
  calc ∑ u ∈ Finset.Icc 1 (m ^ 2), ∑ v ∈ Finset.Icc 1 (m ^ 2),
        (if IsSquare (u * v) then (repCount 2 m u : ℝ) * (repCount 2 m v : ℝ) else 0)
      ≤ (sqPairs.card : ℝ) * (C8 ^ 2 * (m : ℝ) ^ ((1 : ℝ) / 2)) := hsum_le
    _ ≤ ((m : ℝ) ^ 2 * (1 + 2 * Real.log (m : ℝ))) * (C8 ^ 2 * (m : ℝ) ^ ((1 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_right hcard_sq (by positivity)
    _ ≤ ((m : ℝ) ^ 2 * (9 * (m : ℝ) ^ ((1 : ℝ) / 4))) * (C8 ^ 2 * (m : ℝ) ^ ((1 : ℝ) / 2)) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog_le (sq_nonneg _)) (by positivity)
    _ = 9 * C8 ^ 2 * (m : ℝ) ^ ((11 : ℝ) / 4) := by
        have hrpow : (m : ℝ) ^ 2 * (m : ℝ) ^ ((1 : ℝ) / 4) * (m : ℝ) ^ ((1 : ℝ) / 2) =
            (m : ℝ) ^ ((11 : ℝ) / 4) := by
          rw [← Real.rpow_two (m : ℝ), ← Real.rpow_add hm_pos, ← Real.rpow_add hm_pos]
          congr 1; norm_num
        calc (m : ℝ) ^ 2 * (9 * (m : ℝ) ^ ((1 : ℝ) / 4)) * (C8 ^ 2 * (m : ℝ) ^ ((1 : ℝ) / 2))
            = 9 * C8 ^ 2 * ((m : ℝ) ^ 2 * (m : ℝ) ^ ((1 : ℝ) / 4) * (m : ℝ) ^ ((1 : ℝ) / 2)) := by ring
          _ = 9 * C8 ^ 2 * (m : ℝ) ^ ((11 : ℝ) / 4) := by rw [hrpow]

/- ### Section 4: Periodicity and Vanishing Period Sum of Non-Square Jacobi Symbols -/

lemma jacobi_odd_periodic {D k₁ k₂ : ℕ} (hk₁ : Odd k₁) (hk₂ : Odd k₂) (hmod : k₁ ≡ k₂ [MOD 8 * D]) :
    jacobiSym (D : ℤ) k₁ = jacobiSym (D : ℤ) k₂ := by
  rw [jacobiSym.mod_right' D hk₁, jacobiSym.mod_right' D hk₂]
  have h4 : k₁ ≡ k₂ [MOD 4 * D] := hmod.of_dvd ⟨2, by ring⟩
  rw [h4]

lemma exists_odd_jacobi_neg_one {D : ℕ} (hD : 1 ≤ D) (hnsq : ¬ IsSquare D) :
    ∃ a : ℕ, Odd a ∧ Nat.Coprime a (8 * D) ∧ jacobiSym (D : ℤ) a = -1 := by
  have hD0 : D ≠ 0 := by omega
  have hex : ∃ q : ℕ, q.Prime ∧ Odd (D.factorization q) := by
    by_contra hall
    push Not at hall
    apply hnsq
    rw [isSquare_iff_even_factorization hD0]
    intro q
    by_cases hq : q.Prime
    · exact Nat.not_odd_iff_even.mp (hall q hq)
    · rw [Nat.factorization_eq_zero_of_not_prime D hq]; exact ⟨0, rfl⟩
  obtain ⟨q, hq_prime, hq_odd_exp⟩ := hex
  let e : ℕ := D.factorization q
  have he_pos : 1 ≤ e := by rcases hq_odd_exp with ⟨t, ht⟩; dsimp [e]; omega
  have hqe_dvd : q ^ e ∣ D := Nat.ordProj_dvd D q
  let R : ℕ := D / q ^ e
  have hDR : D = q ^ e * R := (Nat.mul_div_cancel' hqe_dvd).symm
  have hR_pos : 1 ≤ R := Nat.div_pos (Nat.le_of_dvd (by omega) hqe_dvd) (pow_pos hq_prime.pos e)
  have hq_ndvd_R : ¬ q ∣ R := by
    intro hdvd
    have h1 : q ^ (e + 1) ∣ D := by
      rcases hdvd with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      rw [hDR, ht, pow_succ]; ring
    have h2 : e + 1 ≤ D.factorization q :=
      (hq_prime.pow_dvd_iff_le_factorization hD0).mp h1
    dsimp [e] at h2; omega
  have hcop_qR : Nat.Coprime q R := hq_prime.coprime_iff_not_dvd.mpr hq_ndvd_R
  by_cases hq2 : q = 2
  · -- Case 1: q = 2, so R is odd
    subst hq2
    have hR_odd : Odd R := Nat.odd_iff.mpr (by omega : R % 2 = 1)
    have hcop_8R : Nat.Coprime 8 R := by
      have : Nat.Coprime (2 ^ 3) R := hcop_qR.pow_left 3
      simpa using this
    obtain ⟨a, ha8, haR⟩ := Nat.chineseRemainder hcop_8R 5 1
    have ha_mod8 : a % 8 = 5 := by simpa [Nat.ModEq] using ha8
    have ha_odd : Odd a := Nat.odd_iff.mpr (by omega)
    have ha_mod4 : a % 4 = 1 := by omega
    have hcop_a8 : Nat.Coprime a 8 := by
      rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_rec, ha_mod8]; decide
    have hcop_a2 : Nat.Coprime a 2 := hcop_a8.coprime_dvd_right (by decide : 2 ∣ 8)
    have hcop_aR : Nat.Coprime a R := by
      rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_rec]
      have : a % R = 1 % R := haR
      rw [this]
      by_cases hR1 : R = 1
      · rw [hR1]; simp
      · rw [Nat.mod_eq_of_lt (by omega : 1 < R), Nat.gcd_one_left]
    have hcop_a8D : Nat.Coprime a (8 * D) := by
      rw [hDR]; exact hcop_a8.mul_right ((hcop_a2.pow_right e).mul_right hcop_aR)
    have hjac2 : jacobiSym (2 : ℤ) a = -1 := by
      rw [jacobiSym.at_two ha_odd]
      have h8 : (a : ZMod 8) = 5 := by
        rw [← ZMod.natCast_mod, ha_mod8]; decide
      rw [h8]; decide
    have hjacR : jacobiSym (R : ℤ) a = 1 := by
      rw [jacobiSym.quadratic_reciprocity_one_mod_four' hR_odd ha_mod4, jacobiSym.mod_left]
      have hmodZ : (a : ℤ) % (R : ℤ) = (1 : ℤ) % (R : ℤ) := by
        have : (a % R : ℕ) = (1 % R : ℕ) := haR
        exact_mod_cast this
      rw [hmodZ, ← jacobiSym.mod_left, jacobiSym.one_left]
    refine ⟨a, ha_odd, hcop_a8D, ?_⟩
    rw [hDR, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, jacobiSym.mul_left, jacobiSym.pow_left,
      hjac2, hjacR, mul_one]
    exact hq_odd_exp.neg_one_pow
  · -- Case 2: q is an odd prime
    have hq_odd : Odd q := hq_prime.odd_of_ne_two hq2
    obtain ⟨g, hg_lt, hg_jac⟩ := exists_jacobi_neg_one hq_prime hq2
    have hg_pos : 0 < g := by
      by_contra h0; push Not at h0
      have : g = 0 := by omega
      subst this; rw [Nat.cast_zero, jacobiSym.zero_left hq_prime.one_lt] at hg_jac; norm_num at hg_jac
    have hcop_gq : Nat.Coprime g q := (hq_prime.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt hg_pos hg_lt)).symm
    have hcop_q8 : Nat.Coprime q 8 := by
      have : Nat.Coprime q (2 ^ 3) := (hq_prime.coprime_iff_not_dvd.mpr
        (by intro hd; exact hq2 ((Nat.prime_dvd_prime_iff_eq hq_prime Nat.prime_two).mp hd))).pow_right 3
      simpa using this
    have hcop_q8R : Nat.Coprime q (8 * R) := hcop_q8.mul_right hcop_qR
    obtain ⟨a, haq, ha8R⟩ := Nat.chineseRemainder hcop_q8R g 1
    have ha8 : a ≡ 1 [MOD 8] := ha8R.of_dvd ⟨R, by ring⟩
    have haR : a ≡ 1 [MOD R] := ha8R.of_dvd ⟨8, by ring⟩
    have ha_mod8 : a % 8 = 1 := by simpa [Nat.ModEq] using ha8
    have ha_odd : Odd a := Nat.odd_iff.mpr (by omega)
    have ha_mod4 : a % 4 = 1 := by omega
    have hcop_a8 : Nat.Coprime a 8 := by
      rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_rec, ha_mod8]; decide
    have hcop_aq : Nat.Coprime a q := by
      rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_rec]
      have : a % q = g % q := haq
      rw [this, Nat.mod_eq_of_lt hg_lt]
      exact hcop_gq.gcd_eq_one
    have hcop_aR : Nat.Coprime a R := by
      rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_rec]
      have : a % R = 1 % R := haR
      rw [this]
      by_cases hR1 : R = 1
      · rw [hR1]; simp
      · rw [Nat.mod_eq_of_lt (by omega : 1 < R), Nat.gcd_one_left]
    have hcop_a8D : Nat.Coprime a (8 * D) := by
      rw [hDR]; exact hcop_a8.mul_right ((hcop_aq.pow_right e).mul_right hcop_aR)
    -- Factor R = 2^v * R_odd
    let v : ℕ := R.factorization 2
    have h2v_dvd : 2 ^ v ∣ R := Nat.ordProj_dvd R 2
    let R_odd : ℕ := R / 2 ^ v
    have hR_eq : R = 2 ^ v * R_odd := (Nat.mul_div_cancel' h2v_dvd).symm
    have hR_odd_odd : Odd R_odd := by
      have h2_ndvd : ¬ 2 ∣ R_odd := by
        intro hd
        have h1 : 2 ^ (v + 1) ∣ R := by
          rcases hd with ⟨t, ht⟩; refine ⟨t, ?_⟩; rw [hR_eq, ht, pow_succ]; ring
        have h2 : v + 1 ≤ R.factorization 2 :=
          (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).mp h1
        dsimp [v] at h2; omega
      exact Nat.odd_iff.mpr (by omega)
    have hjac2 : jacobiSym (2 : ℤ) a = 1 := by
      rw [jacobiSym.at_two ha_odd]
      have h8 : (a : ZMod 8) = 1 := by
        rw [← ZMod.natCast_mod, ha_mod8]; decide
      rw [h8]; decide
    have hjac_Rodd : jacobiSym (R_odd : ℤ) a = 1 := by
      rw [jacobiSym.quadratic_reciprocity_one_mod_four' hR_odd_odd ha_mod4, jacobiSym.mod_left]
      have ha_Rodd : a ≡ 1 [MOD R_odd] := haR.of_dvd ⟨2 ^ v, by linarith⟩
      have hmodZ : (a : ℤ) % (R_odd : ℤ) = (1 : ℤ) % (R_odd : ℤ) := by
        have : (a % R_odd : ℕ) = (1 % R_odd : ℕ) := ha_Rodd
        exact_mod_cast this
      rw [hmodZ, ← jacobiSym.mod_left, jacobiSym.one_left]
    have hjac_q : jacobiSym (q : ℤ) a = -1 := by
      rw [jacobiSym.quadratic_reciprocity_one_mod_four' hq_odd ha_mod4, jacobiSym.mod_left]
      have hmodZ : (a : ℤ) % (q : ℤ) = (g : ℤ) % (q : ℤ) := by
        have : (a % q : ℕ) = (g % q : ℕ) := haq
        exact_mod_cast this
      rw [hmodZ, ← jacobiSym.mod_left, hg_jac]
    refine ⟨a, ha_odd, hcop_a8D, ?_⟩
    rw [hDR, hR_eq, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat,
      jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.pow_left, jacobiSym.pow_left,
      hjac_q, hjac2, hjac_Rodd, one_pow, mul_one, mul_one]
    exact hq_odd_exp.neg_one_pow

lemma jacobi_odd_period_zero {D : ℕ} (hD : 1 ≤ D) (hnsq : ¬ IsSquare D) :
    ∑ k ∈ (Finset.range (8 * D)).filter Odd, (jacobiSym (D : ℤ) k : ℝ) = 0 := by
  obtain ⟨a, ha_odd, ha_cop, ha_jac⟩ := exists_odd_jacobi_neg_one hD hnsq
  have ha_ne : a ≠ 0 := by rcases ha_odd with ⟨t, rfl⟩; omega
  let P : ℕ := 8 * D
  have hP_pos : 0 < P := by dsimp [P]; omega
  let S : ℝ := ∑ k ∈ (Finset.range P).filter Odd, (jacobiSym (D : ℤ) k : ℝ)
  have hS : (jacobiSym (D : ℤ) a : ℝ) * S = S := by
    rw [Finset.mul_sum]
    have hrew : ∑ k ∈ (Finset.range P).filter Odd, (jacobiSym (D : ℤ) a : ℝ) * (jacobiSym (D : ℤ) k : ℝ) =
        ∑ k ∈ (Finset.range P).filter Odd, (jacobiSym (D : ℤ) ((a * k) % P) : ℝ) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk_odd : Odd k := (Finset.mem_filter.mp hk).2
      have hk_ne : k ≠ 0 := by rcases hk_odd with ⟨t, rfl⟩; omega
      rw [← Int.cast_mul, ← jacobiSym.mul_right' (D : ℤ) ha_ne hk_ne]
      have hak_odd : Odd (a * k) := ha_odd.mul hk_odd
      have hmod_odd : Odd ((a * k) % P) := by
        rw [Nat.odd_iff] at hak_odd ⊢
        have h2P : 2 ∣ P := ⟨4 * D, by dsimp [P]; ring⟩
        rw [Nat.mod_mod_of_dvd (a * k) h2P]; exact hak_odd
      congr 1
      exact jacobi_odd_periodic hak_odd hmod_odd (Nat.mod_modEq (a * k) P).symm
    rw [hrew]
    refine Finset.sum_bij (fun k _ => (a * k) % P) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro k hk
      have hk_odd := (Finset.mem_filter.mp hk).2
      have hak_odd := ha_odd.mul hk_odd
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hP_pos), ?_⟩
      rw [Nat.odd_iff] at hak_odd ⊢
      rw [Nat.mod_mod_of_dvd (a * k) ⟨4 * D, by dsimp [P]; ring⟩]; exact hak_odd
    · intro k₁ hk₁ k₂ hk₂ heq
      have hmod : a * k₁ ≡ a * k₂ [MOD P] := heq
      have hcancel : k₁ ≡ k₂ [MOD P] := Nat.ModEq.cancel_left_of_coprime ha_cop.symm hmod
      exact Nat.ModEq.eq_of_lt_of_lt hcancel
        (Finset.mem_range.mp (Finset.mem_filter.mp hk₁).1)
        (Finset.mem_range.mp (Finset.mem_filter.mp hk₂).1)
    · intro b hb
      have hb_lt := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
      have hb_odd := (Finset.mem_filter.mp hb).2
      have : NeZero P := ⟨hP_pos.ne'⟩
      let inv_a : ℕ := (ZMod.unitOfCoprime a ha_cop)⁻¹.val.val
      let k : ℕ := (inv_a * b) % P
      have hprod : a * k ≡ b [MOD P] := by
        have h1 : ((a * k : ℕ) : ZMod P) = (b : ZMod P) := by
          dsimp [k, inv_a]
          rw [Nat.cast_mul, ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_zmod_val]
          have hunit : (a : ZMod P) * ((ZMod.unitOfCoprime a ha_cop)⁻¹ : (ZMod P)ˣ) = 1 := by
            simp [ZMod.coe_unitOfCoprime]
          rw [← mul_assoc, hunit, one_mul]
        exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h1
      have hk_odd : Odd k := by
        by_contra hev
        have h2k : 2 ∣ k := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hev)
        have h2ak : 2 ∣ a * k := dvd_mul_of_dvd_right h2k a
        have h2mod : a * k ≡ b [MOD 2] := hprod.of_dvd ⟨4 * D, by dsimp [P]; ring⟩
        have hb2 : b % 2 = 0 := by rw [← h2mod]; exact Nat.mod_eq_zero_of_dvd h2ak
        have := Nat.odd_iff.mp hb_odd; omega
      refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hP_pos), hk_odd⟩, ?_⟩
      rw [hprod, Nat.mod_eq_of_lt hb_lt]
  rw [ha_jac] at hS
  norm_num at hS
  change S = 0
  linarith

lemma jacobi_odd_partial_sum_le {D : ℕ} (hD : 1 ≤ D) (hnsq : ¬ IsSquare D) (Y : ℕ) :
    |∑ k ∈ (Finset.Icc 1 Y).filter Odd, (jacobiSym (D : ℤ) k : ℝ)| ≤ 8 * (D : ℝ) := by
  let P : ℕ := 8 * D
  have hP_pos : 0 < P := by dsimp [P]; omega
  have hq_zero : ∀ q : ℕ, ∑ k ∈ (Finset.range (q * P)).filter Odd, (jacobiSym (D : ℤ) k : ℝ) = 0 := by
    intro q
    induction q with
    | zero => simp
    | succ r ih =>
      have hsplit : (Finset.range ((r + 1) * P)).filter Odd =
          (Finset.range (r * P)).filter Odd ∪ (Finset.Ico (r * P) ((r + 1) * P)).filter Odd := by
        ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
        constructor
        · rintro ⟨hk, hodd⟩
          by_cases hlt : k < r * P
          · exact Or.inl ⟨hlt, hodd⟩
          · exact Or.inr ⟨⟨by omega, hk⟩, hodd⟩
        · rintro (⟨hlt, hodd⟩ | ⟨⟨_, hk⟩, hodd⟩)
          · exact ⟨by nlinarith, hodd⟩
          · exact ⟨hk, hodd⟩
      have hdisj : Disjoint ((Finset.range (r * P)).filter Odd)
          ((Finset.Ico (r * P) ((r + 1) * P)).filter Odd) := by
        rw [Finset.disjoint_left]; intro k h1 h2
        have := (Finset.mem_range.mp (Finset.mem_filter.mp h1).1)
        have := (Finset.mem_Ico.mp (Finset.mem_filter.mp h2).1).1; omega
      rw [hsplit, Finset.sum_union hdisj, ih, zero_add]
      have hshift : ∑ k ∈ (Finset.Ico (r * P) ((r + 1) * P)).filter Odd, (jacobiSym (D : ℤ) k : ℝ) =
          ∑ k ∈ (Finset.range P).filter Odd, (jacobiSym (D : ℤ) k : ℝ) := by
        refine Finset.sum_bij (fun k _ => k - r * P) ?_ ?_ ?_ ?_
        · intro k hk
          have hIco := Finset.mem_Ico.mp (Finset.mem_filter.mp hk).1
          have hodd := (Finset.mem_filter.mp hk).2
          have hlt' : k < r * P + P := by linarith [hIco.2]
          refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
          have hev : Even (r * P) := ⟨r * (4 * D), by dsimp [P]; ring⟩
          rcases hodd with ⟨t, ht⟩; rcases hev with ⟨s, hs⟩
          exact ⟨t - s, by omega⟩
        · intro k₁ hk₁ k₂ hk₂ heq
          have h1 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hk₁).1).1
          have h2 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hk₂).1).1
          omega
        · intro j hj
          have hj_lt := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
          have hj_odd := (Finset.mem_filter.mp hj).2
          have hev : Even (r * P) := ⟨r * (4 * D), by dsimp [P]; ring⟩
          refine ⟨j + r * P, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by nlinarith⟩,
            by rcases hj_odd with ⟨t, rfl⟩; rcases hev with ⟨s, hs⟩; exact ⟨t + s, by omega⟩⟩, by omega⟩
        · intro k hk
          have hIco := Finset.mem_Ico.mp (Finset.mem_filter.mp hk).1
          have hodd := (Finset.mem_filter.mp hk).2
          have hev : Even (r * P) := ⟨r * (4 * D), by dsimp [P]; ring⟩
          have hodd' : Odd (k - r * P) := by
            rcases hodd with ⟨t, ht⟩; rcases hev with ⟨s, hs⟩; exact ⟨t - s, by omega⟩
          have hmod : k ≡ k - r * P [MOD P] := by
            have : k = (k - r * P) + r * P := by omega
            conv_lhs => rw [this]
            exact Nat.ModEq.add_left (k - r * P) (Nat.modEq_zero_iff_dvd.mpr ⟨r, by ring⟩)
          exact congrArg (Int.cast (R := ℝ)) (jacobi_odd_periodic hodd hodd' hmod)
      rw [hshift, jacobi_odd_period_zero hD hnsq]
  have hIcc_eq : (Finset.Icc 1 Y).filter Odd = (Finset.range (Y + 1)).filter Odd := by
    ext k; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, hle⟩, hodd⟩; exact ⟨by omega, hodd⟩
    · rintro ⟨hlt, hodd⟩; exact ⟨⟨by rcases hodd with ⟨t, rfl⟩; omega, by omega⟩, hodd⟩
  rw [hIcc_eq]
  let q : ℕ := (Y + 1) / P
  have hqP_le : q * P ≤ Y + 1 := Nat.div_mul_le_self (Y + 1) P
  have hrem_le : Y + 1 - q * P ≤ P := by
    have hlt : (Y + 1) % P < P := Nat.mod_lt _ hP_pos
    have hdiv : q * P + (Y + 1) % P = Y + 1 := by
      dsimp [q]; rw [mul_comm]; exact Nat.div_add_mod (Y + 1) P
    omega
  have hsplit : (Finset.range (Y + 1)).filter Odd =
      (Finset.range (q * P)).filter Odd ∪ (Finset.Ico (q * P) (Y + 1)).filter Odd := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    constructor
    · rintro ⟨hk, hodd⟩
      by_cases hlt : k < q * P
      · exact Or.inl ⟨hlt, hodd⟩
      · exact Or.inr ⟨⟨by omega, hk⟩, hodd⟩
    · rintro (⟨hlt, hodd⟩ | ⟨⟨_, hk⟩, hodd⟩)
      · exact ⟨lt_of_lt_of_le hlt hqP_le, hodd⟩
      · exact ⟨hk, hodd⟩
  have hdisj : Disjoint ((Finset.range (q * P)).filter Odd)
      ((Finset.Ico (q * P) (Y + 1)).filter Odd) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    have := Finset.mem_range.mp (Finset.mem_filter.mp h1).1
    have := (Finset.mem_Ico.mp (Finset.mem_filter.mp h2).1).1; omega
  rw [hsplit, Finset.sum_union hdisj, hq_zero q, zero_add]
  have htri : |∑ k ∈ (Finset.Ico (q * P) (Y + 1)).filter Odd, (jacobiSym (D : ℤ) k : ℝ)| ≤
      ∑ k ∈ (Finset.Ico (q * P) (Y + 1)).filter Odd, |(jacobiSym (D : ℤ) k : ℝ)| :=
    Finset.abs_sum_le_sum_abs _ _
  have h1 : ∀ k ∈ (Finset.Ico (q * P) (Y + 1)).filter Odd, |(jacobiSym (D : ℤ) k : ℝ)| ≤ 1 := fun k _ => by
    rcases jacobiSym.trichotomy (D : ℤ) k with h | h | h <;> rw [h] <;> norm_num
  have hcard : (((Finset.Ico (q * P) (Y + 1)).filter Odd).card : ℝ) ≤ 8 * (D : ℝ) := by
    have hsub : ((Finset.Ico (q * P) (Y + 1)).filter Odd).card ≤ (Finset.Ico (q * P) (Y + 1)).card :=
      Finset.card_filter_le _ _
    rw [Nat.card_Ico] at hsub
    have : ((Finset.Ico (q * P) (Y + 1)).filter Odd).card ≤ 8 * D := hsub.trans hrem_le
    exact_mod_cast this
  calc |∑ k ∈ (Finset.Ico (q * P) (Y + 1)).filter Odd, (jacobiSym (D : ℤ) k : ℝ)|
      ≤ ∑ k ∈ (Finset.Ico (q * P) (Y + 1)).filter Odd, |(jacobiSym (D : ℤ) k : ℝ)| := htri
    _ ≤ ∑ _k ∈ (Finset.Ico (q * P) (Y + 1)).filter Odd, (1 : ℝ) := Finset.sum_le_sum h1
    _ = (((Finset.Ico (q * P) (Y + 1)).filter Odd).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ 8 * (D : ℝ) := hcard

/- ### Section 5: Classical Selberg Sieve and Weighted Fourth Moment Bound -/

lemma sum_le_sum_of_injOn {α β : Type*} [DecidableEq β] {s : Finset α} {t : Finset β}
    {f : α → ℝ} {g : β → ℝ} (φ : α → β)
    (hmaps : ∀ a ∈ s, φ a ∈ t) (hinj : Set.InjOn φ s)
    (hle : ∀ a ∈ s, f a ≤ g (φ a)) (hnn : ∀ b ∈ t, 0 ≤ g b) :
    ∑ a ∈ s, f a ≤ ∑ b ∈ t, g b := by
  calc ∑ a ∈ s, f a ≤ ∑ a ∈ s, g (φ a) := Finset.sum_le_sum hle
    _ = ∑ b ∈ s.image φ, g b := (Finset.sum_image hinj).symm
    _ ≤ ∑ b ∈ t, g b := Finset.sum_le_sum_of_subset_of_nonneg
        (fun b hb => by rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩; exact hmaps a ha)
        (fun b hb _ => hnn b hb)

lemma coprime_of_mul_squarefree {a b : ℕ} (h : Squarefree (a * b)) : Nat.Coprime a b := by
  rw [Nat.coprime_iff_gcd_eq_one]
  have hdvd : Nat.gcd a b * Nat.gcd a b ∣ a * b :=
    mul_dvd_mul (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b)
  exact isUnit_iff_eq_one.mp (h (Nat.gcd a b) hdvd)

def Dset (z : ℕ) : Finset ℕ :=
  (Finset.Icc 1 z).filter (fun d => Odd d ∧ Squarefree d)

noncomputable def G_sel (z : ℕ) : ℝ :=
  ∑ d ∈ Dset z, (1 : ℝ) / (Nat.totient d : ℝ)

lemma mem_Dset_iff {z d : ℕ} : d ∈ Dset z ↔ 1 ≤ d ∧ d ≤ z ∧ Odd d ∧ Squarefree d := by
  simp only [Dset, Finset.mem_filter, Finset.mem_Icc, and_assoc]

lemma dvd_mem_Dset {z d c : ℕ} (hd : d ∈ Dset z) (hcd : c ∣ d) : c ∈ Dset z := by
  obtain ⟨hd1, hdz, hd_odd, hd_sqf⟩ := mem_Dset_iff.mp hd
  have hc1 : 1 ≤ c := Nat.pos_of_dvd_of_pos hcd (by omega)
  have hcz : c ≤ z := (Nat.le_of_dvd (by omega) hcd).trans hdz
  have hc_odd : Odd c := by
    by_contra hev
    have h2c : 2 ∣ c := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hev)
    have h2d : 2 ∣ d := h2c.trans hcd
    have := Nat.odd_iff.mp hd_odd; omega
  exact mem_Dset_iff.mpr ⟨hc1, hcz, hc_odd, hd_sqf.squarefree_of_dvd hcd⟩

lemma log_succ_le_harmonic (n : ℕ) (hn : 1 ≤ n) :
    Real.log ((n + 1 : ℕ) : ℝ) ≤ ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / (k : ℝ) := by
  induction n with
  | zero => omega
  | succ m ih =>
    by_cases hm : m = 0
    · subst hm
      simp only [zero_add, Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, div_one]
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      push_cast; linarith
    · have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm
      have hsplit : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hsplit, Finset.sum_insert (by simp)]
      have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
      have hm2_pos : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
      have hstep : Real.log ((m + 2 : ℕ) : ℝ) - Real.log ((m + 1 : ℕ) : ℝ) ≤ 1 / ((m + 1 : ℕ) : ℝ) := by
        rw [← Real.log_div hm2_pos.ne' hm1_pos.ne']
        have h1 := Real.log_le_sub_one_of_pos (div_pos hm2_pos hm1_pos)
        have h2 : ((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) - 1 = 1 / ((m + 1 : ℕ) : ℝ) := by
          push_cast; field_simp [hm1_pos.ne']; ring
        linarith
      linarith [ih hm1]

lemma sum_inv_sq_le_two (n : ℕ) :
    ∑ s ∈ Finset.Icc 1 n, (1 : ℝ) / ((s : ℝ) ^ 2) ≤ 2 := by
  by_cases hn : n = 0
  · subst hn; simp
  have hstrong : ∀ m : ℕ, 1 ≤ m → ∑ s ∈ Finset.Icc 1 m, (1 : ℝ) / ((s : ℝ) ^ 2) ≤ 2 - 1 / (m : ℝ) := by
    intro m hm
    induction m with
    | zero => omega
    | succ r ih =>
      by_cases hr : r = 0
      · subst hr; norm_num
      · have hr1 : 1 ≤ r := Nat.pos_of_ne_zero hr
        have hsplit : Finset.Icc 1 (r + 1) = insert (r + 1) (Finset.Icc 1 r) := by
          ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hsplit, Finset.sum_insert (by simp)]
        have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
        have hr1_pos : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by positivity
        have hstep : 1 / ((r + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (r : ℝ) - 1 / ((r + 1 : ℕ) : ℝ) := by
          have hdiff : 1 / (r : ℝ) - 1 / ((r + 1 : ℕ) : ℝ) = 1 / ((r : ℝ) * ((r + 1 : ℕ) : ℝ)) := by
            push_cast; field_simp [hr_pos.ne', hr1_pos.ne']; ring
          rw [hdiff, div_le_div_iff₀ (sq_pos_of_pos hr1_pos) (mul_pos hr_pos hr1_pos)]
          push_cast; nlinarith
        linarith [ih hr1]
  have h1 := hstrong n (Nat.pos_of_ne_zero hn)
  have hnn : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  linarith

lemma odd_squarefree_decomp (n : ℕ) (hn : 1 ≤ n) (hodd : Odd n) :
    ∃ d s : ℕ, 1 ≤ d ∧ d ≤ n ∧ Odd d ∧ Squarefree d ∧ 1 ≤ s ∧ s ≤ n ∧ Odd s ∧ n = d * s ^ 2 := by
  have hn0 : n ≠ 0 := by omega
  let s : ℕ := ∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)
  have hs_pos : 1 ≤ s := by
    dsimp [s]
    calc 1 = ∏ _p ∈ n.primeFactors, 1 := by simp
      _ ≤ ∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2) :=
          Finset.prod_le_prod' fun p hp => Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors hp).pos
  have hs2_dvd : s ^ 2 ∣ n := by
    have hs2 : s ^ 2 = ∏ p ∈ n.primeFactors, p ^ (2 * (n.factorization p / 2)) := by
      dsimp [s]; rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [← pow_mul, mul_comm]
    rw [hs2]
    conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hn0]
    exact Finset.prod_dvd_prod_of_dvd _ _ fun p _ => Nat.pow_dvd_pow p (by omega)
  let d : ℕ := n / s ^ 2
  have hnd : n = d * s ^ 2 := (Nat.div_mul_cancel hs2_dvd).symm
  have hd_pos : 1 ≤ d := Nat.div_pos (Nat.le_of_dvd (by omega) hs2_dvd) (by positivity)
  have hd_le : d ≤ n := Nat.div_le_self n (s ^ 2)
  have hs_le : s ≤ n := by
    have hs2_le : s ^ 2 ≤ n := Nat.le_of_dvd (by omega) hs2_dvd
    nlinarith
  have hd_odd : Odd d := by
    by_contra hev
    have h2 : 2 ∣ d := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hev)
    have h2n : 2 ∣ n := by rw [hnd]; exact dvd_mul_of_dvd_left h2 _
    have := Nat.odd_iff.mp hodd; omega
  have hs_odd : Odd s := by
    by_contra hev
    have h2 : 2 ∣ s := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hev)
    have h2n : 2 ∣ n := by rw [hnd, sq]; exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left h2 s) d
    have := Nat.odd_iff.mp hodd; omega
  have hs_fact : ∀ p : ℕ, s.factorization p = n.factorization p / 2 := fun p => by
    dsimp [s]
    rw [Nat.factorization_prod (fun q hq => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hq).ne_zero),
      Finset.sum_apply']
    have hterm : ∀ q ∈ n.primeFactors, (q ^ (n.factorization q / 2)).factorization p =
        if q = p then n.factorization p / 2 else 0 := fun q hq => by
      have hq_pr := Nat.prime_of_mem_primeFactors hq
      rw [hq_pr.factorization_pow, Finsupp.single_apply]
      by_cases hqp : q = p
      · subst hqp; simp
      · simp [hqp]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
    split_ifs with hp_mem
    · rfl
    · have h0 : n.factorization p = 0 := by
        rw [← Finsupp.notMem_support_iff, Nat.support_factorization]; exact hp_mem
      rw [h0]; simp
  have hd_sqf : Squarefree d := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hdvd
    have hd0 : d ≠ 0 := by omega
    have h2le : 2 ≤ d.factorization p := by
      have : p ^ 2 ∣ d := by simpa [sq] using hdvd
      exact (hp.pow_dvd_iff_le_factorization hd0).mp this
    have hfact_eq : n.factorization p = d.factorization p + 2 * (n.factorization p / 2) := by
      have h1 : n.factorization p = (d * s ^ 2).factorization p := by rw [← hnd]
      rw [Nat.factorization_mul hd0 (pow_ne_zero 2 (by omega)), Finsupp.add_apply,
        Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hs_fact p] at h1
      exact h1
    omega
  exact ⟨d, s, hd_pos, hd_le, hd_odd, hd_sqf, hs_pos, hs_le, hs_odd, hnd⟩

lemma G_sel_ge_one {z : ℕ} (hz : 1 ≤ z) : 1 ≤ G_sel z := by
  have h1 : 1 ∈ Dset z := mem_Dset_iff.mpr ⟨le_rfl, hz, odd_one, squarefree_one⟩
  have hterm : (1 : ℝ) / (Nat.totient 1 : ℝ) ≤ ∑ d ∈ Dset z, (1 : ℝ) / (Nat.totient d : ℝ) :=
    Finset.single_le_sum (f := fun d => (1 : ℝ) / (Nat.totient d : ℝ)) (fun d _ => by positivity) h1
  simpa [G_sel] using hterm

lemma G_sel_ge_quarter_log {z : ℕ} (hz : 2 ≤ z) :
    (1 / 4 : ℝ) * Real.log (z : ℝ) ≤ G_sel z := by
  -- Step 1: ∑_{n ≤ z, odd} 1/n ≥ (1/2) * log z
  have hodd_ge : (1 / 2 : ℝ) * Real.log (z : ℝ) ≤
      ∑ n ∈ (Finset.Icc 1 z).filter Odd, (1 : ℝ) / (n : ℝ) := by
    have hsplit : ∑ n ∈ Finset.Icc 1 z, (1 : ℝ) / (n : ℝ) =
        (∑ n ∈ (Finset.Icc 1 z).filter Odd, (1 : ℝ) / (n : ℝ)) +
        (∑ n ∈ (Finset.Icc 1 z).filter (fun n => ¬ Odd n), (1 : ℝ) / (n : ℝ)) := by
      exact (Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 z) Odd _).symm
    have heven_le : ∑ n ∈ (Finset.Icc 1 z).filter (fun n => ¬ Odd n), (1 : ℝ) / (n : ℝ) ≤
        ∑ n ∈ (Finset.Icc 1 z).filter Odd, (1 : ℝ) / (n : ℝ) := by
      refine sum_le_sum_of_injOn (fun n => n - 1) ?_ ?_ ?_ (fun _ _ => by positivity)
      · intro n hn
        have hIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
        have hev := Nat.not_odd_iff_even.mp (Finset.mem_filter.mp hn).2
        rcases hev with ⟨t, ht⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ⟨t - 1, by omega⟩⟩
      · intro a ha b hb hab
        dsimp only at hab
        have ha1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).1).1
        have hb1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).1).1
        omega
      · intro n hn
        have hIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
        have hev := Nat.not_odd_iff_even.mp (Finset.mem_filter.mp hn).2
        rcases hev with ⟨t, ht⟩
        have h1 : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - 1)
        exact one_div_le_one_div_of_le h1 (by exact_mod_cast (by omega : n - 1 ≤ n))
    have hlog_le : Real.log (z : ℝ) ≤ ∑ n ∈ Finset.Icc 1 z, (1 : ℝ) / (n : ℝ) := by
      have h1 := log_succ_le_harmonic z (by omega)
      have h2 : Real.log (z : ℝ) ≤ Real.log ((z + 1 : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast (by omega : z ≤ z + 1))
      linarith
    linarith
  -- Step 2: ∑_{n ≤ z, odd} 1/n ≤ 2 * G_sel z
  have hodd_le : ∑ n ∈ (Finset.Icc 1 z).filter Odd, (1 : ℝ) / (n : ℝ) ≤ 2 * G_sel z := by
    let S_prod := Dset z ×ˢ Finset.Icc 1 z
    have hsub : ∑ n ∈ (Finset.Icc 1 z).filter Odd, (1 : ℝ) / (n : ℝ) ≤
        ∑ p ∈ S_prod, (1 : ℝ) / ((p.1 * p.2 ^ 2 : ℕ) : ℝ) := by
      have hex : ∀ n ∈ (Finset.Icc 1 z).filter Odd,
          ∃ p ∈ S_prod, p.1 * p.2 ^ 2 = n := fun n hn => by
        have hIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
        have hodd := (Finset.mem_filter.mp hn).2
        obtain ⟨d, s, hd1, hdn, hd_odd, hd_sqf, hs1, hsn, _, hnd⟩ :=
          odd_squarefree_decomp n hIcc.1 hodd
        exact ⟨(d, s), Finset.mem_product.mpr
          ⟨mem_Dset_iff.mpr ⟨hd1, hdn.trans hIcc.2, hd_odd, hd_sqf⟩,
           Finset.mem_Icc.mpr ⟨hs1, hsn.trans hIcc.2⟩⟩, hnd.symm⟩
      choose f hf_mem hf_eq using hex
      refine sum_le_sum_of_injOn (fun n => if h : n ∈ (Finset.Icc 1 z).filter Odd then f n h else (1, 1))
        ?_ ?_ ?_ (fun _ _ => by positivity)
      · intro n hn; simp only [dif_pos hn]; exact hf_mem n hn
      · intro a ha b hb hab
        have ha' := Finset.mem_coe.mp ha
        have hb' := Finset.mem_coe.mp hb
        dsimp only at hab
        rw [dif_pos ha', dif_pos hb'] at hab
        have h1 := hf_eq a ha'; have h2 := hf_eq b hb'
        rw [hab] at h1; linarith
      · intro n hn; simp only [dif_pos hn, hf_eq n hn]; exact le_rfl
    have hfact : ∑ p ∈ S_prod, (1 : ℝ) / ((p.1 * p.2 ^ 2 : ℕ) : ℝ) =
        (∑ d ∈ Dset z, (1 : ℝ) / (d : ℝ)) * (∑ s ∈ Finset.Icc 1 z, (1 : ℝ) / ((s : ℝ) ^ 2)) := by
      dsimp [S_prod]
      rw [Finset.sum_product, Finset.sum_mul]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      push_cast; ring
    have hd_le_G : ∑ d ∈ Dset z, (1 : ℝ) / (d : ℝ) ≤ G_sel z := by
      refine Finset.sum_le_sum fun d hd => ?_
      have hd1 := (mem_Dset_iff.mp hd).1
      have hphi_pos : (0 : ℝ) < (Nat.totient d : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr (by omega)
      exact one_div_le_one_div_of_le hphi_pos (by exact_mod_cast Nat.totient_le d)
    have hs_le : ∑ s ∈ Finset.Icc 1 z, (1 : ℝ) / ((s : ℝ) ^ 2) ≤ 2 := sum_inv_sq_le_two z
    have hnn1 : 0 ≤ ∑ d ∈ Dset z, (1 : ℝ) / (d : ℝ) := Finset.sum_nonneg fun _ _ => by positivity
    have hnn2 : 0 ≤ ∑ s ∈ Finset.Icc 1 z, (1 : ℝ) / ((s : ℝ) ^ 2) := Finset.sum_nonneg fun _ _ => by positivity
    calc ∑ n ∈ (Finset.Icc 1 z).filter Odd, (1 : ℝ) / (n : ℝ)
        ≤ (∑ d ∈ Dset z, (1 : ℝ) / (d : ℝ)) * (∑ s ∈ Finset.Icc 1 z, (1 : ℝ) / ((s : ℝ) ^ 2)) :=
          hsub.trans hfact.le
      _ ≤ G_sel z * 2 := mul_le_mul hd_le_G hs_le hnn2 (by linarith [G_sel_ge_one (by omega : 1 ≤ z)])
      _ = 2 * G_sel z := by ring
  linarith

noncomputable def lam (z d : ℕ) : ℝ :=
  if d ∈ Dset z then
    ((ArithmeticFunction.moebius d : ℝ) / G_sel z) * (d : ℝ) *
      ∑ m ∈ (Dset z).filter (d ∣ ·), (1 : ℝ) / (Nat.totient m : ℝ)
  else 0

lemma lam_one {z : ℕ} (hz : 1 ≤ z) : lam z 1 = 1 := by
  have h1 : 1 ∈ Dset z := mem_Dset_iff.mpr ⟨le_rfl, hz, odd_one, squarefree_one⟩
  have hG : G_sel z ≠ 0 := by linarith [G_sel_ge_one hz]
  have hfilt : (Dset z).filter (1 ∣ ·) = Dset z := by
    ext m; simp
  unfold lam
  rw [if_pos h1, ArithmeticFunction.moebius_apply_one, hfilt]
  push_cast
  change 1 / G_sel z * 1 * G_sel z = 1
  field_simp [hG]

lemma squarefree_div_totient_eq_sum {d : ℕ} (hd1 : 1 ≤ d) (hd_sqf : Squarefree d) :
    (d : ℝ) / (Nat.totient d : ℝ) = ∑ c ∈ d.divisors, (1 : ℝ) / (Nat.totient c : ℝ) := by
  have hphi_pos : (0 : ℝ) < (Nat.totient d : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  rw [div_eq_iff hphi_pos.ne', Finset.sum_mul]
  have hterm : ∀ c ∈ d.divisors, (1 : ℝ) / (Nat.totient c : ℝ) * (Nat.totient d : ℝ) =
      (Nat.totient (d / c) : ℝ) := fun c hc => by
    have hcd : c ∣ d := (Nat.mem_divisors.mp hc).1
    have hc1 : 1 ≤ c := Nat.pos_of_dvd_of_pos hcd (by omega)
    have hphic_pos : (0 : ℝ) < (Nat.totient c : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    have hcop : Nat.Coprime c (d / c) := by
      have hmul : c * (d / c) = d := Nat.mul_div_cancel' hcd
      exact coprime_of_mul_squarefree (by rwa [hmul])
    have hphimul : Nat.totient d = Nat.totient c * Nat.totient (d / c) := by
      conv_lhs => rw [← Nat.mul_div_cancel' hcd]
      exact Nat.totient_mul hcop
    rw [hphimul, Nat.cast_mul]
    field_simp [hphic_pos.ne']
  rw [Finset.sum_congr rfl hterm]
  have hbij : ∑ c ∈ d.divisors, (Nat.totient (d / c) : ℝ) = ∑ c ∈ d.divisors, (Nat.totient c : ℝ) := by
    refine Finset.sum_bij (fun c _ => d / c) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro c hc
      exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hc).1, by omega⟩
    · intro a ha b hb hab
      have ha_d := (Nat.mem_divisors.mp ha).1
      have hb_d := (Nat.mem_divisors.mp hb).1
      have h1 : a * (d / a) = d := Nat.mul_div_cancel' ha_d
      have h2 : b * (d / b) = d := Nat.mul_div_cancel' hb_d
      have hpos : 0 < d / b := Nat.div_pos (Nat.le_of_dvd (by omega) hb_d) (Nat.pos_of_dvd_of_pos hb_d (by omega))
      rw [hab] at h1
      exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
    · intro k hk
      have hkd := (Nat.mem_divisors.mp hk).1
      refine ⟨d / k, Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hkd, by omega⟩, ?_⟩
      exact Nat.div_div_self hkd (by omega)
  rw [hbij]
  exact_mod_cast (Nat.sum_totient d).symm

lemma abs_lam_le_one {z : ℕ} (hz : 1 ≤ z) (d : ℕ) : |lam z d| ≤ 1 := by
  by_cases hd : d ∈ Dset z
  · obtain ⟨hd1, hdz, hd_odd, hd_sqf⟩ := mem_Dset_iff.mp hd
    have hG_pos : 0 < G_sel z := by linarith [G_sel_ge_one hz]
    have hmu : |(ArithmeticFunction.moebius d : ℝ)| = 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree hd_sqf
    have hsum_nn : 0 ≤ ∑ m ∈ (Dset z).filter (d ∣ ·), (1 : ℝ) / (Nat.totient m : ℝ) :=
      Finset.sum_nonneg fun _ _ => by positivity
    unfold lam
    rw [if_pos hd, abs_mul, abs_mul, abs_div, hmu, abs_of_pos hG_pos,
      abs_of_pos (by exact_mod_cast hd1 : (0 : ℝ) < (d : ℝ)), abs_of_nonneg hsum_nn]
    let K := (Dset z).filter (fun k => Nat.Coprime d k ∧ d * k ≤ z)
    have hphi_d_pos : (0 : ℝ) < (Nat.totient d : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    have hsum_eq : ∑ m ∈ (Dset z).filter (d ∣ ·), (1 : ℝ) / (Nat.totient m : ℝ) =
        (1 / (Nat.totient d : ℝ)) * ∑ k ∈ K, (1 : ℝ) / (Nat.totient k : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun m _ => m / d) ?_ ?_ ?_ ?_
      · intro m hm
        have hmD := (Finset.mem_filter.mp hm).1
        have hdm := (Finset.mem_filter.mp hm).2
        have hkmD : m / d ∈ Dset z := dvd_mem_Dset hmD (Nat.div_dvd_of_dvd hdm)
        have hm_sqf := (mem_Dset_iff.mp hmD).2.2.2
        have hmul : d * (m / d) = m := Nat.mul_div_cancel' hdm
        have hcop : Nat.Coprime d (m / d) := coprime_of_mul_squarefree (by rwa [hmul])
        exact Finset.mem_filter.mpr ⟨hkmD, hcop, hmul.le.trans (mem_Dset_iff.mp hmD).2.1⟩
      · intro m₁ hm₁ m₂ hm₂ heq
        have h1 := Nat.mul_div_cancel' (Finset.mem_filter.mp hm₁).2
        have h2 := Nat.mul_div_cancel' (Finset.mem_filter.mp hm₂).2
        rw [← h1, ← h2, heq]
      · intro k hk
        have hkD := (Finset.mem_filter.mp hk).1
        have hcop := (Finset.mem_filter.mp hk).2.1
        have hdkz := (Finset.mem_filter.mp hk).2.2
        obtain ⟨hk1, _, hk_odd, hk_sqf⟩ := mem_Dset_iff.mp hkD
        have hdkD : d * k ∈ Dset z := mem_Dset_iff.mpr
          ⟨by nlinarith, hdkz, hd_odd.mul hk_odd, (Nat.squarefree_mul hcop).mpr ⟨hd_sqf, hk_sqf⟩⟩
        exact ⟨d * k, Finset.mem_filter.mpr ⟨hdkD, dvd_mul_right d k⟩, Nat.mul_div_cancel_left k (by omega)⟩
      · intro m hm
        have hmD := (Finset.mem_filter.mp hm).1
        have hdm := (Finset.mem_filter.mp hm).2
        have hmul : d * (m / d) = m := Nat.mul_div_cancel' hdm
        have hm_sqf := (mem_Dset_iff.mp hmD).2.2.2
        have hcop : Nat.Coprime d (m / d) := coprime_of_mul_squarefree (by rwa [hmul])
        have hphi : Nat.totient m = Nat.totient d * Nat.totient (m / d) := by
          conv_lhs => rw [← hmul]
          exact Nat.totient_mul hcop
        rw [hphi, Nat.cast_mul]; ring
    have hprod_le_G : ((d : ℝ) / (Nat.totient d : ℝ)) * ∑ k ∈ K, (1 : ℝ) / (Nat.totient k : ℝ) ≤ G_sel z := by
      rw [squarefree_div_totient_eq_sum hd1 hd_sqf, Finset.sum_mul]
      have hrew : ∑ c ∈ d.divisors, (1 : ℝ) / (Nat.totient c : ℝ) * ∑ k ∈ K, (1 : ℝ) / (Nat.totient k : ℝ) =
          ∑ p ∈ d.divisors ×ˢ K, (1 : ℝ) / (Nat.totient (p.1 * p.2) : ℝ) := by
        rw [Finset.sum_product]
        refine Finset.sum_congr rfl fun c hc => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hcd := (Nat.mem_divisors.mp hc).1
        have hcop_dk := (Finset.mem_filter.mp hk).2.1
        have hcop_ck : Nat.Coprime c k := hcop_dk.coprime_dvd_left hcd
        rw [Nat.totient_mul hcop_ck, Nat.cast_mul]; ring
      rw [hrew]
      refine sum_le_sum_of_injOn (fun p => p.1 * p.2) ?_ ?_ (fun _ _ => le_rfl) (fun _ _ => by positivity)
      · intro p hp
        have hcD := dvd_mem_Dset hd (Nat.mem_divisors.mp (Finset.mem_product.mp hp).1).1
        have hcd := (Nat.mem_divisors.mp (Finset.mem_product.mp hp).1).1
        have hkD := (Finset.mem_filter.mp (Finset.mem_product.mp hp).2).1
        have hcop_dk := (Finset.mem_filter.mp (Finset.mem_product.mp hp).2).2.1
        have hdkz := (Finset.mem_filter.mp (Finset.mem_product.mp hp).2).2.2
        have hcop_ck : Nat.Coprime p.1 p.2 := hcop_dk.coprime_dvd_left hcd
        obtain ⟨hc1, _, hc_odd, hc_sqf⟩ := mem_Dset_iff.mp hcD
        obtain ⟨hk1, _, hk_odd, hk_sqf⟩ := mem_Dset_iff.mp hkD
        have hc_le_d : p.1 ≤ d := Nat.le_of_dvd (by omega) hcd
        exact mem_Dset_iff.mpr ⟨by nlinarith, (Nat.mul_le_mul_right p.2 hc_le_d).trans hdkz,
          hc_odd.mul hk_odd, (Nat.squarefree_mul hcop_ck).mpr ⟨hc_sqf, hk_sqf⟩⟩
      · intro p₁ hp₁ p₂ hp₂ heq
        dsimp only at heq
        have hc1_d := (Nat.mem_divisors.mp (Finset.mem_product.mp (Finset.mem_coe.mp hp₁)).1).1
        have hc2_d := (Nat.mem_divisors.mp (Finset.mem_product.mp (Finset.mem_coe.mp hp₂)).1).1
        have hk1_cop := (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_coe.mp hp₁)).2).2.1
        have hk2_cop := (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_coe.mp hp₂)).2).2.1
        have hgcd1 : Nat.gcd (p₁.1 * p₁.2) d = p₁.1 := by
          rw [hk1_cop.symm.gcd_mul_right_cancel p₁.1, Nat.gcd_eq_left hc1_d]
        have hgcd2 : Nat.gcd (p₂.1 * p₂.2) d = p₂.1 := by
          rw [hk2_cop.symm.gcd_mul_right_cancel p₂.1, Nat.gcd_eq_left hc2_d]
        have hf : p₁.1 = p₂.1 := by rw [← hgcd1, heq, hgcd2]
        have hc1_pos : 0 < p₁.1 := Nat.pos_of_dvd_of_pos hc1_d (by omega)
        have hs : p₁.2 = p₂.2 := Nat.eq_of_mul_eq_mul_left hc1_pos (by rwa [← hf] at heq)
        exact Prod.ext hf hs
    rw [hsum_eq]
    have hrew2 : 1 / G_sel z * (d : ℝ) * (1 / (Nat.totient d : ℝ) * ∑ k ∈ K, (1 : ℝ) / (Nat.totient k : ℝ)) =
        (((d : ℝ) / (Nat.totient d : ℝ)) * ∑ k ∈ K, (1 : ℝ) / (Nat.totient k : ℝ)) / G_sel z := by ring
    rw [hrew2, div_le_one hG_pos]
    exact hprod_le_G
  · unfold lam; rw [if_neg hd, abs_zero]; norm_num

lemma sum_moebius_divisors_eq (n : ℕ) (hn : 1 ≤ n) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) = if n = 1 then 1 else 0 := by
  have h1 : (ArithmeticFunction.moebius * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) n =
      (1 : ArithmeticFunction ℤ) n := by
    rw [ArithmeticFunction.moebius_mul_coe_zeta]
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (f := fun x y => ArithmeticFunction.moebius x * ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) y))] at h1
  have hsum : ∑ d ∈ n.divisors, ArithmeticFunction.moebius d * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) (n / d) =
      ∑ d ∈ n.divisors, ArithmeticFunction.moebius d := by
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdn := (Nat.mem_divisors.mp hd).1
    have hpos : n / d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (by omega) hdn) (Nat.pos_of_dvd_of_pos hdn (by omega))).ne'
    simp [ArithmeticFunction.zeta_apply_ne hpos]
  rw [hsum] at h1
  have hrhs : ((1 : ArithmeticFunction ℤ) n : ℝ) = if n = 1 then 1 else 0 := by
    rw [ArithmeticFunction.one_apply]; split_ifs <;> simp
  rw [← hrhs]
  exact_mod_cast h1

lemma selberg_quad_form {z : ℕ} (hz : 1 ≤ z) :
    ∑ d₁ ∈ Dset z, ∑ d₂ ∈ Dset z, lam z d₁ * lam z d₂ / (Nat.lcm d₁ d₂ : ℝ) = 1 / G_sel z := by
  have hG_pos : 0 < G_sel z := by linarith [G_sel_ge_one hz]
  -- Step 1: Rewrite 1 / lcm(d₁, d₂) = (∑_{r ∈ Dset z, r ∣ d₁ ∧ r ∣ d₂} φ(r)) / (d₁ * d₂)
  have hlcm_id : ∀ d₁ ∈ Dset z, ∀ d₂ ∈ Dset z,
      lam z d₁ * lam z d₂ / (Nat.lcm d₁ d₂ : ℝ) =
        ∑ r ∈ Dset z, if r ∣ d₁ ∧ r ∣ d₂ then
          (Nat.totient r : ℝ) * (lam z d₁ / (d₁ : ℝ)) * (lam z d₂ / (d₂ : ℝ))
        else 0 := fun d₁ hd₁ d₂ hd₂ => by
    have hd1_pos : 1 ≤ d₁ := (mem_Dset_iff.mp hd₁).1
    have hd2_pos : 1 ≤ d₂ := (mem_Dset_iff.mp hd₂).1
    have hmul : Nat.gcd d₁ d₂ * Nat.lcm d₁ d₂ = d₁ * d₂ := Nat.gcd_mul_lcm d₁ d₂
    have hlcm_pos : (0 : ℝ) < (Nat.lcm d₁ d₂ : ℝ) := by exact_mod_cast Nat.lcm_pos (by omega) (by omega)
    have hd1_ne : (d₁ : ℝ) ≠ 0 := by positivity
    have hd2_ne : (d₂ : ℝ) ≠ 0 := by positivity
    have hfilt : (Dset z).filter (fun r => r ∣ d₁ ∧ r ∣ d₂) = (Nat.gcd d₁ d₂).divisors := by
      ext r; simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨_, h1, h2⟩
        exact ⟨Nat.dvd_gcd h1 h2, (Nat.gcd_pos_of_pos_left d₂ (by omega)).ne'⟩
      · rintro ⟨hgd, _⟩
        have h1 : r ∣ d₁ := hgd.trans (Nat.gcd_dvd_left d₁ d₂)
        have h2 : r ∣ d₂ := hgd.trans (Nat.gcd_dvd_right d₁ d₂)
        exact ⟨dvd_mem_Dset hd₁ h1, h1, h2⟩
    rw [← Finset.sum_filter, hfilt, ← Finset.sum_mul, ← Finset.sum_mul]
    have htot : ∑ r ∈ (Nat.gcd d₁ d₂).divisors, (Nat.totient r : ℝ) = (Nat.gcd d₁ d₂ : ℝ) := by
      exact_mod_cast Nat.sum_totient (Nat.gcd d₁ d₂)
    rw [htot]
    have hmulR : (Nat.gcd d₁ d₂ : ℝ) * (Nat.lcm d₁ d₂ : ℝ) = (d₁ : ℝ) * (d₂ : ℝ) := by exact_mod_cast hmul
    field_simp [hlcm_pos.ne', hd1_ne, hd2_ne]
    linarith [show lam z d₁ * lam z d₂ * ((d₁ : ℝ) * (d₂ : ℝ)) =
      lam z d₁ * lam z d₂ * ((Nat.gcd d₁ d₂ : ℝ) * (Nat.lcm d₁ d₂ : ℝ)) by rw [hmulR]]
  have hdiag : ∑ d₁ ∈ Dset z, ∑ d₂ ∈ Dset z, lam z d₁ * lam z d₂ / (Nat.lcm d₁ d₂ : ℝ) =
      ∑ r ∈ Dset z, (Nat.totient r : ℝ) * (∑ d ∈ (Dset z).filter (r ∣ ·), lam z d / (d : ℝ)) ^ 2 := by
    calc ∑ d₁ ∈ Dset z, ∑ d₂ ∈ Dset z, lam z d₁ * lam z d₂ / (Nat.lcm d₁ d₂ : ℝ)
        = ∑ d₁ ∈ Dset z, ∑ d₂ ∈ Dset z, ∑ r ∈ Dset z,
            if r ∣ d₁ ∧ r ∣ d₂ then (Nat.totient r : ℝ) * (lam z d₁ / (d₁ : ℝ)) * (lam z d₂ / (d₂ : ℝ)) else 0 := by
          refine Finset.sum_congr rfl fun d₁ hd₁ => Finset.sum_congr rfl fun d₂ hd₂ => hlcm_id d₁ hd₁ d₂ hd₂
      _ = ∑ d₁ ∈ Dset z, ∑ r ∈ Dset z, ∑ d₂ ∈ Dset z,
            if r ∣ d₁ ∧ r ∣ d₂ then (Nat.totient r : ℝ) * (lam z d₁ / (d₁ : ℝ)) * (lam z d₂ / (d₂ : ℝ)) else 0 :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ r ∈ Dset z, ∑ d₁ ∈ Dset z, ∑ d₂ ∈ Dset z,
            if r ∣ d₁ ∧ r ∣ d₂ then (Nat.totient r : ℝ) * (lam z d₁ / (d₁ : ℝ)) * (lam z d₂ / (d₂ : ℝ)) else 0 :=
          Finset.sum_comm
      _ = ∑ r ∈ Dset z, (Nat.totient r : ℝ) * (∑ d ∈ (Dset z).filter (r ∣ ·), lam z d / (d : ℝ)) ^ 2 := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [sq, Finset.sum_mul, Finset.mul_sum]
          have h1 : ∀ d₁ ∈ Dset z, ∑ d₂ ∈ Dset z,
                (if r ∣ d₁ ∧ r ∣ d₂ then (Nat.totient r : ℝ) * (lam z d₁ / (d₁ : ℝ)) * (lam z d₂ / (d₂ : ℝ)) else 0) =
              if r ∣ d₁ then (Nat.totient r : ℝ) * ((lam z d₁ / (d₁ : ℝ)) * ∑ d₂ ∈ (Dset z).filter (r ∣ ·), lam z d₂ / (d₂ : ℝ)) else 0 := by
            intro d₁ _
            by_cases hr1 : r ∣ d₁
            · rw [if_pos hr1, Finset.mul_sum, Finset.mul_sum, Finset.sum_filter]
              refine Finset.sum_congr rfl fun d₂ _ => ?_
              by_cases hr2 : r ∣ d₂
              · rw [if_pos ⟨hr1, hr2⟩, if_pos hr2]; ring
              · rw [if_neg (fun h => hr2 h.2), if_neg hr2]
            · rw [if_neg hr1]
              refine Finset.sum_eq_zero fun d₂ _ => if_neg (fun h => hr1 h.1)
          rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
  -- Step 2: Evaluate Y(r) = ∑_{d ∈ Dset z, r ∣ d} lam z d / d = μ(r) / (G_sel z * φ(r))
  have hY : ∀ r ∈ Dset z, ∑ d ∈ (Dset z).filter (r ∣ ·), lam z d / (d : ℝ) =
      (ArithmeticFunction.moebius r : ℝ) / (G_sel z * (Nat.totient r : ℝ)) := by
    intro r hr
    have hrew1 : ∑ d ∈ (Dset z).filter (r ∣ ·), lam z d / (d : ℝ) =
        (1 / G_sel z) * ∑ d ∈ (Dset z).filter (r ∣ ·), ∑ m ∈ (Dset z).filter (r ∣ ·),
          if d ∣ m then (ArithmeticFunction.moebius d : ℝ) * ((1 : ℝ) / (Nat.totient m : ℝ)) else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hdD := (Finset.mem_filter.mp hd).1
      have hrd := (Finset.mem_filter.mp hd).2
      have hd_ne : (d : ℝ) ≠ 0 := by exact_mod_cast (by have := (mem_Dset_iff.mp hdD).1; omega : d ≠ 0)
      unfold lam
      rw [if_pos hdD]
      have hsub_filt : ((Dset z).filter (r ∣ ·)).filter (d ∣ ·) = (Dset z).filter (d ∣ ·) := by
        ext m; simp only [Finset.mem_filter]
        exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hrd.trans h.2⟩, h.2⟩⟩
      rw [← Finset.sum_filter, hsub_filt, ← Finset.mul_sum]
      field_simp [hd_ne]
    rw [hrew1, Finset.sum_comm]
    have hinner : ∀ m ∈ (Dset z).filter (r ∣ ·),
        ∑ d ∈ (Dset z).filter (r ∣ ·),
          (if d ∣ m then (ArithmeticFunction.moebius d : ℝ) * ((1 : ℝ) / (Nat.totient m : ℝ)) else 0) =
        if m = r then (ArithmeticFunction.moebius r : ℝ) * ((1 : ℝ) / (Nat.totient r : ℝ)) else 0 := by
      intro m hm
      have hmD := (Finset.mem_filter.mp hm).1
      have hrm := (Finset.mem_filter.mp hm).2
      obtain ⟨hm1, _, _, hm_sqf⟩ := mem_Dset_iff.mp hmD
      have hr1 := (mem_Dset_iff.mp hr).1
      rw [← Finset.sum_filter, ← Finset.sum_mul]
      have hmoeb_sum : ∑ d ∈ ((Dset z).filter (r ∣ ·)).filter (· ∣ m), (ArithmeticFunction.moebius d : ℝ) =
          (ArithmeticFunction.moebius r : ℝ) * ∑ t ∈ (m / r).divisors, (ArithmeticFunction.moebius t : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_bij (fun d _ => d / r) ?_ ?_ ?_ ?_
        · intro d hd
          have hdm := (Finset.mem_filter.mp hd).2
          have hrd := (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).2
          refine Nat.mem_divisors.mpr ⟨?_, (Nat.div_pos (Nat.le_of_dvd (by omega) hrm) hr1).ne'⟩
          rcases hdm with ⟨q, hq⟩
          refine ⟨q, ?_⟩
          have hmul : r * (d / r) = d := Nat.mul_div_cancel' hrd
          have hm_eq : r * (m / r) = r * ((d / r) * q) := by
            rw [Nat.mul_div_cancel' hrm, ← mul_assoc, hmul, hq]
          exact Nat.eq_of_mul_eq_mul_left (by omega) hm_eq
        · intro d₁ hd₁ d₂ hd₂ heq
          have h1 := Nat.mul_div_cancel' (Finset.mem_filter.mp (Finset.mem_filter.mp hd₁).1).2
          have h2 := Nat.mul_div_cancel' (Finset.mem_filter.mp (Finset.mem_filter.mp hd₂).1).2
          rw [← h1, ← h2, heq]
        · intro t ht
          have htd := (Nat.mem_divisors.mp ht).1
          have hrt_dvd_m : r * t ∣ m := by
            rcases htd with ⟨q, hq⟩
            refine ⟨q, ?_⟩
            calc m = r * (m / r) := (Nat.mul_div_cancel' hrm).symm
              _ = r * (t * q) := by rw [hq]
              _ = (r * t) * q := by ring
          refine ⟨r * t, Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨dvd_mem_Dset hmD hrt_dvd_m, dvd_mul_right r t⟩, hrt_dvd_m⟩,
            Nat.mul_div_cancel_left t (by omega)⟩
        · intro d hd
          have hdD := (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).1
          have hrd := (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).2
          have hd_sqf := (mem_Dset_iff.mp hdD).2.2.2
          have hmul : r * (d / r) = d := Nat.mul_div_cancel' hrd
          have hcop : Nat.Coprime r (d / r) := coprime_of_mul_squarefree (by rwa [hmul])
          have hmu_mul : ArithmeticFunction.moebius d =
              ArithmeticFunction.moebius r * ArithmeticFunction.moebius (d / r) := by
            conv_lhs => rw [← hmul]
            exact ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
          rw [hmu_mul, Int.cast_mul]
      rw [hmoeb_sum, sum_moebius_divisors_eq (m / r) (Nat.div_pos (Nat.le_of_dvd (by omega) hrm) hr1)]
      have hiff : m / r = 1 ↔ m = r := by
        constructor
        · intro h1; rw [← Nat.mul_div_cancel' hrm, h1, mul_one]
        · rintro rfl; exact Nat.div_self (by omega)
      by_cases hmr : m = r
      · rw [if_pos (hiff.mpr hmr), if_pos hmr, mul_one, hmr]
      · rw [if_neg (mt hiff.mp hmr), if_neg hmr, mul_zero, zero_mul]
    rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq' _ r _,
      if_pos (Finset.mem_filter.mpr ⟨hr, dvd_refl r⟩)]
    ring
  -- Step 3: Plug hY into hdiag
  rw [hdiag]
  have hterm : ∀ r ∈ Dset z,
      (Nat.totient r : ℝ) * (∑ d ∈ (Dset z).filter (r ∣ ·), lam z d / (d : ℝ)) ^ 2 =
        (1 / G_sel z ^ 2) * ((1 : ℝ) / (Nat.totient r : ℝ)) := fun r hr => by
    rw [hY r hr]
    obtain ⟨hr1, _, _, hr_sqf⟩ := mem_Dset_iff.mp hr
    have hphi_ne : (Nat.totient r : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (by omega)).ne'
    have hmu2 : (ArithmeticFunction.moebius r : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hr_sqf
    rw [div_pow, hmu2, mul_pow]
    field_simp [hG_pos.ne', hphi_ne]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  change 1 / G_sel z ^ 2 * G_sel z = 1 / G_sel z
  field_simp [hG_pos.ne']

lemma odd_multiples_card_approx (X L : ℕ) (hX : 1 ≤ X) (hL : 1 ≤ L) (hL_odd : Odd L) :
    |(((Finset.Ico 1 X).filter (fun n => Odd n ∧ L ∣ n)).card : ℝ) - (X : ℝ) / (2 * (L : ℝ))| ≤ 1 := by
  let q : ℕ := (X - 1) / L
  have hbij : ((Finset.Ico 1 X).filter (fun n => Odd n ∧ L ∣ n)).card =
      ((Finset.Icc 1 q).filter Odd).card := by
    refine Finset.card_bij (fun n _ => n / L) ?_ ?_ ?_
    · intro n hn
      have hIco := Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1
      have hodd := (Finset.mem_filter.mp hn).2.1
      have hdvd := (Finset.mem_filter.mp hn).2.2
      have hmul : L * (n / L) = n := Nat.mul_div_cancel' hdvd
      have hq1 : 1 ≤ n / L := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hL
      have hq2 : n / L ≤ q := Nat.div_le_div_right (by omega)
      have hk_odd : Odd (n / L) := by
        by_contra hev
        have h2 : 2 ∣ n / L := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hev)
        have h2n : 2 ∣ n := by rw [← hmul]; exact dvd_mul_of_dvd_right h2 L
        have := Nat.odd_iff.mp hodd; omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq1, hq2⟩, hk_odd⟩
    · intro a ha b hb heq
      have h1 := Nat.mul_div_cancel' (Finset.mem_filter.mp ha).2.2
      have h2 := Nat.mul_div_cancel' (Finset.mem_filter.mp hb).2.2
      rw [← h1, ← h2, heq]
    · intro k hk
      have hIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1
      have hk_odd := (Finset.mem_filter.mp hk).2
      have hLk_le : L * k ≤ X - 1 := by
        calc L * k ≤ L * q := Nat.mul_le_mul_left L hIcc.2
          _ ≤ X - 1 := by dsimp [q]; rw [mul_comm]; exact Nat.div_mul_le_self (X - 1) L
      refine ⟨L * k, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by nlinarith, by omega⟩,
        hL_odd.mul hk_odd, dvd_mul_right L k⟩, Nat.mul_div_cancel_left k (by omega)⟩
  have hodd_card : ((Finset.Icc 1 q).filter Odd).card = (q + 1) / 2 := by
    have heq : (Finset.Icc 1 q).filter Odd = (Finset.range ((q + 1) / 2)).image (fun j => 2 * j + 1) := by
      ext k; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨⟨hk1, hkq⟩, ⟨j, rfl⟩⟩
        exact ⟨j, by omega, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨⟨by omega, by omega⟩, ⟨j, rfl⟩⟩
    rw [heq, Finset.card_image_of_injective _ (fun a b h => by omega), Finset.card_range]
  rw [hbij, hodd_card]
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hqL_le : q * L ≤ X - 1 := Nat.div_mul_le_self (X - 1) L
  have hqL_gt : X - 1 < (q + 1) * L := by
    dsimp [q]
    have := Nat.lt_div_mul_add (a := X - 1) (b := L) (by omega)
    linarith
  have hc_lo : (q : ℝ) / 2 ≤ (((q + 1) / 2 : ℕ) : ℝ) := by
    have : q ≤ 2 * ((q + 1) / 2) := by omega
    have : (q : ℝ) ≤ 2 * (((q + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have hc_hi : (((q + 1) / 2 : ℕ) : ℝ) ≤ ((q : ℝ) + 1) / 2 := by
    have : 2 * ((q + 1) / 2) ≤ q + 1 := by omega
    have : 2 * (((q + 1) / 2 : ℕ) : ℝ) ≤ (q : ℝ) + 1 := by exact_mod_cast this
    linarith
  have hq_hi : (q : ℝ) ≤ (X : ℝ) / (L : ℝ) := by
    rw [le_div_iff₀ hL_pos]
    have : q * L ≤ X := by omega
    exact_mod_cast this
  have hq_lo : (X : ℝ) / (L : ℝ) - 1 - 1 / (L : ℝ) ≤ (q : ℝ) := by
    have h1 : (X : ℝ) - 1 ≤ ((q : ℝ) + 1) * (L : ℝ) := by
      have : X ≤ (q + 1) * L + 1 := by omega
      have : (X : ℝ) ≤ ((q : ℝ) + 1) * (L : ℝ) + 1 := by exact_mod_cast this
      linarith
    have h2 : ((X : ℝ) - 1) / (L : ℝ) ≤ (q : ℝ) + 1 := (div_le_iff₀ hL_pos).mpr h1
    have h3 : ((X : ℝ) - 1) / (L : ℝ) = (X : ℝ) / (L : ℝ) - 1 / (L : ℝ) := sub_div _ _ _
    linarith
  have h1L : 1 / (L : ℝ) ≤ 1 := by rw [div_le_one hL_pos]; exact_mod_cast hL
  rw [abs_le]
  have hdiv2 : (X : ℝ) / (2 * (L : ℝ)) = ((X : ℝ) / (L : ℝ)) / 2 := by ring
  rw [hdiv2]
  constructor <;> linarith

lemma selberg_fourth_moment_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (X z m : ℕ), 2 ≤ z → z < X → 1 ≤ m →
      ∑ p ∈ (Nat.primesBelow X).filter (· ≠ 2),
        (∑ n ∈ Finset.Icc 1 m, (jacobiSym (n : ℤ) p : ℝ)) ^ 4 ≤
      (z : ℝ) * (m : ℝ) ^ 4 +
        (2 * (X : ℝ) / Real.log (z : ℝ) + (z : ℝ) ^ 2) * C * (m : ℝ) ^ ((11 : ℝ) / 4) +
        8 * (z : ℝ) ^ 2 * (m : ℝ) ^ 8 := by
  obtain ⟨Csq, hCsq_pos, hCsq⟩ := square_pair_bound
  refine ⟨Csq, hCsq_pos, fun X z m hz hzX hm => ?_⟩
  let S : ℕ → ℝ := fun q => ∑ n ∈ Finset.Icc 1 m, (jacobiSym (n : ℤ) q : ℝ)
  let P_odd := (Nat.primesBelow X).filter (· ≠ 2)
  let P_small := P_odd.filter (· ≤ z)
  let P_large := P_odd.filter (fun p => ¬ p ≤ z)
  have hsplit_P : ∑ p ∈ P_odd, (S p) ^ 4 =
      (∑ p ∈ P_small, (S p) ^ 4) + (∑ p ∈ P_large, (S p) ^ 4) :=
    (Finset.sum_filter_add_sum_filter_not P_odd (· ≤ z) (fun p => (S p) ^ 4)).symm
  -- Bound small primes p ≤ z
  have hsmall_le : ∑ p ∈ P_small, (S p) ^ 4 ≤ (z : ℝ) * (m : ℝ) ^ 4 := by
    have hterm : ∀ p ∈ P_small, (S p) ^ 4 ≤ (m : ℝ) ^ 4 := fun p _ => by
      have habs : |S p| ≤ (m : ℝ) := by
        calc |S p| ≤ ∑ n ∈ Finset.Icc 1 m, |(jacobiSym (n : ℤ) p : ℝ)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _n ∈ Finset.Icc 1 m, (1 : ℝ) := Finset.sum_le_sum fun n _ => by
              rcases jacobiSym.trichotomy (n : ℤ) p with h | h | h <;> rw [h] <;> norm_num
          _ = (m : ℝ) := by rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
      have h1 : |S p| ^ 4 ≤ (m : ℝ) ^ 4 := pow_le_pow_left₀ (abs_nonneg _) habs 4
      have h2 : (S p) ^ 4 = |S p| ^ 4 := by
        have : (S p) ^ 4 = ((S p) ^ 2) ^ 2 := by ring
        rw [this, ← sq_abs (S p)]; ring
      linarith
    have hcard : P_small.card ≤ z := by
      have hsub : P_small ⊆ Finset.Icc 1 z := fun p hp => by
        have hp_pr := (Nat.mem_primesBelow.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).2
        exact Finset.mem_Icc.mpr ⟨hp_pr.one_le, (Finset.mem_filter.mp hp).2⟩
      exact (Finset.card_le_card hsub).trans (by rw [Nat.card_Icc, Nat.add_sub_cancel])
    calc ∑ p ∈ P_small, (S p) ^ 4
        ≤ ∑ _p ∈ P_small, (m : ℝ) ^ 4 := Finset.sum_le_sum hterm
      _ = (P_small.card : ℝ) * (m : ℝ) ^ 4 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (z : ℝ) * (m : ℝ) ^ 4 := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
  -- Bound large primes z < p < X via Selberg weight
  let w : ℕ → ℝ := fun n => ∑ d ∈ (Dset z).filter (· ∣ n), lam z d
  let W : ℝ := ∑ n ∈ (Finset.Ico 1 X).filter Odd, (w n) ^ 2 * (S n) ^ 4
  have hlarge_le_W : ∑ p ∈ P_large, (S p) ^ 4 ≤ W := by
    have hsub : P_large ⊆ (Finset.Ico 1 X).filter Odd := fun p hp => by
      have hp_odd_mem := (Finset.mem_filter.mp hp).1
      have hp_below := (Finset.mem_filter.mp hp_odd_mem).1
      have hp2 := (Finset.mem_filter.mp hp_odd_mem).2
      have hp_lt := (Nat.mem_primesBelow.mp hp_below).1
      have hp_pr := (Nat.mem_primesBelow.mp hp_below).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hp_pr.one_le, hp_lt⟩, hp_pr.odd_of_ne_two hp2⟩
    have hw_one : ∀ p ∈ P_large, w p = 1 := fun p hp => by
      have hp_gt : z < p := Nat.lt_of_not_ge (Finset.mem_filter.mp hp).2
      have hp_pr := (Nat.mem_primesBelow.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).2
      have hfilt : (Dset z).filter (· ∣ p) = {1} := by
        ext d; simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hdD, hdp⟩
          have hdz := (mem_Dset_iff.mp hdD).2.1
          rcases hp_pr.eq_one_or_self_of_dvd d hdp with rfl | rfl
          · rfl
          · omega
        · rintro rfl
          exact ⟨mem_Dset_iff.mpr ⟨le_rfl, by omega, odd_one, squarefree_one⟩, one_dvd p⟩
      dsimp [w]; rw [hfilt, Finset.sum_singleton, lam_one (by omega)]
    calc ∑ p ∈ P_large, (S p) ^ 4
        = ∑ p ∈ P_large, (w p) ^ 2 * (S p) ^ 4 :=
          Finset.sum_congr rfl fun p hp => by rw [hw_one p hp, one_pow, one_mul]
      _ ≤ W := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
  -- Expand W using S(n)^4 = ∑_{u, v ≤ m^2} c_2(u) c_2(v) J(u*v | n)
  have hS4 : ∀ n : ℕ, (S n) ^ 4 =
      ∑ u ∈ Finset.Icc 1 (m ^ 2), ∑ v ∈ Finset.Icc 1 (m ^ 2),
        (repCount 2 m u : ℝ) * (repCount 2 m v : ℝ) * (jacobiSym ((u * v : ℕ) : ℤ) n : ℝ) := fun n => by
    have h2 := S_pow_eq_sum_repCount_real 2 m n hm
    have h4 : (S n) ^ 4 = ((S n) ^ 2) * ((S n) ^ 2) := by ring
    rw [h4, h2, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Nat.cast_mul, jacobiSym.mul_left, Int.cast_mul]; ring
  let inner : ℕ → ℝ := fun D => ∑ n ∈ (Finset.Ico 1 X).filter Odd, (w n) ^ 2 * (jacobiSym (D : ℤ) n : ℝ)
  have hW_exp : W = ∑ u ∈ Finset.Icc 1 (m ^ 2), ∑ v ∈ Finset.Icc 1 (m ^ 2),
      (repCount 2 m u : ℝ) * (repCount 2 m v : ℝ) * inner (u * v) := by
    dsimp [W]
    have h1 : ∀ n ∈ (Finset.Ico 1 X).filter Odd, (w n) ^ 2 * (S n) ^ 4 =
        ∑ u ∈ Finset.Icc 1 (m ^ 2), ∑ v ∈ Finset.Icc 1 (m ^ 2),
          (repCount 2 m u : ℝ) * (repCount 2 m v : ℝ) * ((w n) ^ 2 * (jacobiSym ((u * v : ℕ) : ℤ) n : ℝ)) := by
      intro n _
      rw [hS4 n, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => by ring
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => (Finset.mul_sum _ _ _).symm
  -- Helper: expand ∑_{n < X odd} (w n)^2 * f(n) over d₁, d₂ ∈ Dset z
  have hw2_sum : ∀ f : ℕ → ℝ, ∑ n ∈ (Finset.Ico 1 X).filter Odd, (w n) ^ 2 * f n =
      ∑ d₁ ∈ Dset z, ∑ d₂ ∈ Dset z, lam z d₁ * lam z d₂ *
        ∑ n ∈ (Finset.Ico 1 X).filter (fun n => Odd n ∧ Nat.lcm d₁ d₂ ∣ n), f n := fun f => by
    have h1 : ∀ n ∈ (Finset.Ico 1 X).filter Odd, (w n) ^ 2 * f n =
        ∑ d₁ ∈ Dset z, ∑ d₂ ∈ Dset z,
          if Nat.lcm d₁ d₂ ∣ n then lam z d₁ * lam z d₂ * f n else 0 := fun n _ => by
      dsimp [w]
      rw [sq, Finset.sum_mul, Finset.sum_mul]
      have hleft : ∑ d₁ ∈ (Dset z).filter (· ∣ n),
            (lam z d₁ * ∑ d₂ ∈ (Dset z).filter (· ∣ n), lam z d₂) * f n =
          ∑ d₁ ∈ Dset z, if d₁ ∣ n then
            (lam z d₁ * ∑ d₂ ∈ (Dset z).filter (· ∣ n), lam z d₂) * f n else 0 := by
        rw [Finset.sum_filter]
      rw [hleft]
      refine Finset.sum_congr rfl fun d₁ _ => ?_
      by_cases h1d : d₁ ∣ n
      · rw [if_pos h1d, Finset.mul_sum, Finset.sum_mul, Finset.sum_filter]
        refine Finset.sum_congr rfl fun d₂ _ => ?_
        by_cases h2d : d₂ ∣ n
        · rw [if_pos h2d, if_pos (Nat.lcm_dvd h1d h2d)]
        · rw [if_neg h2d, if_neg (fun hl => h2d ((Nat.dvd_lcm_right d₁ d₂).trans hl))]
      · rw [if_neg h1d]
        exact (Finset.sum_eq_zero fun d₂ _ =>
          if_neg (fun hl => h1d ((Nat.dvd_lcm_left d₁ d₂).trans hl))).symm
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d₁ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d₂ _ => ?_
    rw [← Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext n; simp only [Finset.mem_filter, and_assoc]
  have hDset_card : ((Dset z).card : ℝ) ≤ (z : ℝ) := by
    have hsub : Dset z ⊆ Finset.Icc 1 z := Finset.filter_subset _ _
    have hle : (Dset z).card ≤ z := (Finset.card_le_card hsub).trans (by rw [Nat.card_Icc, Nat.add_sub_cancel])
    exact_mod_cast hle
  -- Case A bound: ∑_{n < X odd} (w n)^2 ≤ 2 * X / log z + z^2
  have hdiag_bound : ∑ n ∈ (Finset.Ico 1 X).filter Odd, (w n) ^ 2 ≤
      2 * (X : ℝ) / Real.log (z : ℝ) + (z : ℝ) ^ 2 := by
    have h1 := hw2_sum (fun _ => (1 : ℝ))
    simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at h1
    rw [h1]
    have herr : ∀ d₁ ∈ Dset z, ∀ d₂ ∈ Dset z,
        lam z d₁ * lam z d₂ * (((Finset.Ico 1 X).filter (fun n => Odd n ∧ Nat.lcm d₁ d₂ ∣ n)).card : ℝ) ≤
        (X : ℝ) / 2 * (lam z d₁ * lam z d₂ / (Nat.lcm d₁ d₂ : ℝ)) + 1 := by
      intro d₁ hd₁ d₂ hd₂
      obtain ⟨hd1_1, _, hd1_odd, _⟩ := mem_Dset_iff.mp hd₁
      obtain ⟨hd2_1, _, hd2_odd, _⟩ := mem_Dset_iff.mp hd₂
      let L := Nat.lcm d₁ d₂
      have hL1 : 1 ≤ L := Nat.lcm_pos (by omega) (by omega)
      have hL_odd : Odd L := by
        have hdiv : L ∣ d₁ * d₂ := Nat.lcm_dvd (dvd_mul_right d₁ d₂) (dvd_mul_left d₂ d₁)
        by_contra hev
        have h2L : 2 ∣ L := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hev)
        have h2d : 2 ∣ d₁ * d₂ := h2L.trans hdiv
        have := Nat.odd_iff.mp (hd1_odd.mul hd2_odd); omega
      have happrox := odd_multiples_card_approx X L (by omega) hL1 hL_odd
      have hlam12 : |lam z d₁ * lam z d₂| ≤ 1 := by
        rw [abs_mul]
        exact mul_le_one₀ (abs_lam_le_one (by omega) d₁) (abs_nonneg _) (abs_lam_le_one (by omega) d₂)
      have hdiff : |lam z d₁ * lam z d₂ *
            ((((Finset.Ico 1 X).filter (fun n => Odd n ∧ L ∣ n)).card : ℝ) - (X : ℝ) / (2 * (L : ℝ)))| ≤ 1 := by
        rw [abs_mul]
        exact mul_le_one₀ hlam12 (abs_nonneg _) happrox
      have hle := (abs_le.mp hdiff).2
      have hrew : (X : ℝ) / 2 * (lam z d₁ * lam z d₂ / (L : ℝ)) =
          lam z d₁ * lam z d₂ * ((X : ℝ) / (2 * (L : ℝ))) := by ring
      linarith
    have hsum_le : ∑ d₁ ∈ Dset z, ∑ d₂ ∈ Dset z,
          lam z d₁ * lam z d₂ * (((Finset.Ico 1 X).filter (fun n => Odd n ∧ Nat.lcm d₁ d₂ ∣ n)).card : ℝ) ≤
        (X : ℝ) / 2 * (∑ d₁ ∈ Dset z, ∑ d₂ ∈ Dset z, lam z d₁ * lam z d₂ / (Nat.lcm d₁ d₂ : ℝ)) +
          ((Dset z).card : ℝ) ^ 2 := by
      calc ∑ d₁ ∈ Dset z, ∑ d₂ ∈ Dset z,
            lam z d₁ * lam z d₂ * (((Finset.Ico 1 X).filter (fun n => Odd n ∧ Nat.lcm d₁ d₂ ∣ n)).card : ℝ)
          ≤ ∑ d₁ ∈ Dset z, ∑ d₂ ∈ Dset z, ((X : ℝ) / 2 * (lam z d₁ * lam z d₂ / (Nat.lcm d₁ d₂ : ℝ)) + 1) :=
            Finset.sum_le_sum fun d₁ hd₁ => Finset.sum_le_sum fun d₂ hd₂ => herr d₁ hd₁ d₂ hd₂
        _ = (X : ℝ) / 2 * (∑ d₁ ∈ Dset z, ∑ d₂ ∈ Dset z, lam z d₁ * lam z d₂ / (Nat.lcm d₁ d₂ : ℝ)) +
            ((Dset z).card : ℝ) ^ 2 := by
            simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
            ring
    rw [selberg_quad_form (by omega)] at hsum_le
    have hlogz_pos : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast hz)
    have hG_ge := G_sel_ge_quarter_log hz
    have hG_pos : 0 < G_sel z := by linarith [G_sel_ge_one (by omega : 1 ≤ z)]
    have hinv_le : 1 / G_sel z ≤ 4 / Real.log (z : ℝ) := by
      rw [div_le_div_iff₀ hG_pos hlogz_pos]; linarith
    have hmain_le : (X : ℝ) / 2 * (1 / G_sel z) ≤ 2 * (X : ℝ) / Real.log (z : ℝ) := by
      calc (X : ℝ) / 2 * (1 / G_sel z)
          ≤ (X : ℝ) / 2 * (4 / Real.log (z : ℝ)) := mul_le_mul_of_nonneg_left hinv_le (by positivity)
        _ = 2 * (X : ℝ) / Real.log (z : ℝ) := by ring
    have hcard_sq : ((Dset z).card : ℝ) ^ 2 ≤ (z : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hDset_card 2
    linarith
  -- Case A: IsSquare (u * v) -> inner (u * v) ≤ 2 * X / log z + z^2
  have hinner_sq : ∀ D : ℕ, inner D ≤ 2 * (X : ℝ) / Real.log (z : ℝ) + (z : ℝ) ^ 2 := fun D => by
    calc inner D ≤ ∑ n ∈ (Finset.Ico 1 X).filter Odd, (w n) ^ 2 := by
          refine Finset.sum_le_sum fun n _ => ?_
          have hj : (jacobiSym (D : ℤ) n : ℝ) ≤ 1 := by
            rcases jacobiSym.trichotomy (D : ℤ) n with h | h | h <;> rw [h] <;> norm_num
          nlinarith [sq_nonneg (w n)]
      _ ≤ 2 * (X : ℝ) / Real.log (z : ℝ) + (z : ℝ) ^ 2 := hdiag_bound
  -- Case B: ¬ IsSquare D (1 ≤ D ≤ m^4) -> inner D ≤ 8 * z^2 * m^4
  have hinner_nsq : ∀ D : ℕ, 1 ≤ D → D ≤ m ^ 4 → ¬ IsSquare D →
      inner D ≤ 8 * (z : ℝ) ^ 2 * (m : ℝ) ^ 4 := fun D hD1 hDm4 hnsq => by
    dsimp [inner]
    rw [hw2_sum (fun n => (jacobiSym (D : ℤ) n : ℝ))]
    have hterm : ∀ d₁ ∈ Dset z, ∀ d₂ ∈ Dset z,
        lam z d₁ * lam z d₂ *
          ∑ n ∈ (Finset.Ico 1 X).filter (fun n => Odd n ∧ Nat.lcm d₁ d₂ ∣ n), (jacobiSym (D : ℤ) n : ℝ) ≤
        8 * (m : ℝ) ^ 4 := by
      intro d₁ hd₁ d₂ hd₂
      obtain ⟨hd1_1, _, hd1_odd, _⟩ := mem_Dset_iff.mp hd₁
      obtain ⟨hd2_1, _, hd2_odd, _⟩ := mem_Dset_iff.mp hd₂
      let L := Nat.lcm d₁ d₂
      have hL1 : 1 ≤ L := Nat.lcm_pos (by omega) (by omega)
      have hL_odd : Odd L := by
        have hdiv : L ∣ d₁ * d₂ := Nat.lcm_dvd (dvd_mul_right d₁ d₂) (dvd_mul_left d₂ d₁)
        by_contra hev
        have h2L : 2 ∣ L := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hev)
        have h2d : 2 ∣ d₁ * d₂ := h2L.trans hdiv
        have := Nat.odd_iff.mp (hd1_odd.mul hd2_odd); omega
      have hreindex : ∑ n ∈ (Finset.Ico 1 X).filter (fun n => Odd n ∧ L ∣ n), (jacobiSym (D : ℤ) n : ℝ) =
          (jacobiSym (D : ℤ) L : ℝ) * ∑ k ∈ (Finset.Icc 1 ((X - 1) / L)).filter Odd, (jacobiSym (D : ℤ) k : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_bij (fun n _ => n / L) ?_ ?_ ?_ ?_
        · intro n hn
          have hIco := Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1
          have hodd := (Finset.mem_filter.mp hn).2.1
          have hdvd := (Finset.mem_filter.mp hn).2.2
          have hmul : L * (n / L) = n := Nat.mul_div_cancel' hdvd
          have hk_odd : Odd (n / L) := by
            by_contra hev
            have h2 : 2 ∣ n / L := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hev)
            have h2n : 2 ∣ n := by rw [← hmul]; exact dvd_mul_of_dvd_right h2 L
            have := Nat.odd_iff.mp hodd; omega
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hL1,
              Nat.div_le_div_right (by omega)⟩, hk_odd⟩
        · intro a ha b hb heq
          rw [← Nat.mul_div_cancel' (Finset.mem_filter.mp ha).2.2,
              ← Nat.mul_div_cancel' (Finset.mem_filter.mp hb).2.2, heq]
        · intro k hk
          have hIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1
          have hk_odd := (Finset.mem_filter.mp hk).2
          have hLk_le : L * k ≤ X - 1 :=
            (Nat.mul_le_mul_left L hIcc.2).trans (by rw [mul_comm]; exact Nat.div_mul_le_self (X - 1) L)
          exact ⟨L * k, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by nlinarith, by omega⟩,
            hL_odd.mul hk_odd, dvd_mul_right L k⟩, Nat.mul_div_cancel_left k (by omega)⟩
        · intro n hn
          have hIco := Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1
          have hdvd := (Finset.mem_filter.mp hn).2.2
          have hk_ne : n / L ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hL1).ne'
          conv_lhs => rw [← Nat.mul_div_cancel' hdvd]
          rw [jacobiSym.mul_right' (D : ℤ) (by omega) hk_ne, Int.cast_mul]
      rw [hreindex]
      have hlam12 : |lam z d₁ * lam z d₂| ≤ 1 := by
        rw [abs_mul]
        exact mul_le_one₀ (abs_lam_le_one (by omega) d₁) (abs_nonneg _) (abs_lam_le_one (by omega) d₂)
      have hjL : |(jacobiSym (D : ℤ) L : ℝ)| ≤ 1 := by
        rcases jacobiSym.trichotomy (D : ℤ) L with h | h | h <;> rw [h] <;> norm_num
      have hpart := jacobi_odd_partial_sum_le hD1 hnsq ((X - 1) / L)
      have hD_le : 8 * (D : ℝ) ≤ 8 * (m : ℝ) ^ 4 := by
        have : (D : ℝ) ≤ (m : ℝ) ^ 4 := by exact_mod_cast hDm4
        linarith
      calc lam z d₁ * lam z d₂ * ((jacobiSym (D : ℤ) L : ℝ) *
              ∑ k ∈ (Finset.Icc 1 ((X - 1) / L)).filter Odd, (jacobiSym (D : ℤ) k : ℝ))
          ≤ |lam z d₁ * lam z d₂ * ((jacobiSym (D : ℤ) L : ℝ) *
              ∑ k ∈ (Finset.Icc 1 ((X - 1) / L)).filter Odd, (jacobiSym (D : ℤ) k : ℝ))| := le_abs_self _
        _ = |lam z d₁ * lam z d₂| * (|(jacobiSym (D : ℤ) L : ℝ)| *
              |∑ k ∈ (Finset.Icc 1 ((X - 1) / L)).filter Odd, (jacobiSym (D : ℤ) k : ℝ)|) := by
              rw [abs_mul (lam z d₁ * lam z d₂), abs_mul (jacobiSym (D : ℤ) L : ℝ)]
        _ ≤ 1 * (1 * (8 * (D : ℝ))) := by
              refine mul_le_mul hlam12 (mul_le_mul hjL hpart (abs_nonneg _) zero_le_one)
                (by positivity) zero_le_one
        _ ≤ 8 * (m : ℝ) ^ 4 := by linarith
    calc ∑ d₁ ∈ Dset z, ∑ d₂ ∈ Dset z, lam z d₁ * lam z d₂ *
          ∑ n ∈ (Finset.Ico 1 X).filter (fun n => Odd n ∧ Nat.lcm d₁ d₂ ∣ n), (jacobiSym (D : ℤ) n : ℝ)
        ≤ ∑ _d₁ ∈ Dset z, ∑ _d₂ ∈ Dset z, (8 * (m : ℝ) ^ 4) :=
          Finset.sum_le_sum fun d₁ hd₁ => Finset.sum_le_sum fun d₂ hd₂ => hterm d₁ hd₁ d₂ hd₂
      _ = ((Dset z).card : ℝ) ^ 2 * (8 * (m : ℝ) ^ 4) := by
          simp only [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ (z : ℝ) ^ 2 * (8 * (m : ℝ) ^ 4) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hDset_card 2) (by positivity)
      _ = 8 * (z : ℝ) ^ 2 * (m : ℝ) ^ 4 := by ring
  -- Combine Case A and Case B in W
  have hW_le : W ≤ (2 * (X : ℝ) / Real.log (z : ℝ) + (z : ℝ) ^ 2) * Csq * (m : ℝ) ^ ((11 : ℝ) / 4) +
      8 * (z : ℝ) ^ 2 * (m : ℝ) ^ 8 := by
    rw [hW_exp]
    have hsplit_uv : ∑ u ∈ Finset.Icc 1 (m ^ 2), ∑ v ∈ Finset.Icc 1 (m ^ 2),
          (repCount 2 m u : ℝ) * (repCount 2 m v : ℝ) * inner (u * v) ≤
        (∑ u ∈ Finset.Icc 1 (m ^ 2), ∑ v ∈ Finset.Icc 1 (m ^ 2),
          (if IsSquare (u * v) then (repCount 2 m u : ℝ) * (repCount 2 m v : ℝ) else 0) *
            (2 * (X : ℝ) / Real.log (z : ℝ) + (z : ℝ) ^ 2)) +
        (∑ u ∈ Finset.Icc 1 (m ^ 2), ∑ v ∈ Finset.Icc 1 (m ^ 2),
          (repCount 2 m u : ℝ) * (repCount 2 m v : ℝ) * (8 * (z : ℝ) ^ 2 * (m : ℝ) ^ 4)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun u hu => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun v hv => ?_
      have huI := Finset.mem_Icc.mp hu
      have hvI := Finset.mem_Icc.mp hv
      have hcc_nn : 0 ≤ (repCount 2 m u : ℝ) * (repCount 2 m v : ℝ) := by positivity
      by_cases hsq : IsSquare (u * v)
      · rw [if_pos hsq]
        have h1 := mul_le_mul_of_nonneg_left (hinner_sq (u * v)) hcc_nn
        have h2 : 0 ≤ (repCount 2 m u : ℝ) * (repCount 2 m v : ℝ) * (8 * (z : ℝ) ^ 2 * (m : ℝ) ^ 4) := by positivity
        linarith
      · rw [if_neg hsq, zero_mul, zero_add]
        have huv1 : 1 ≤ u * v := by nlinarith [huI.1, hvI.1]
        have huv4 : u * v ≤ m ^ 4 := by
          calc u * v ≤ m ^ 2 * m ^ 2 := Nat.mul_le_mul huI.2 hvI.2
            _ = m ^ 4 := by ring
        exact mul_le_mul_of_nonneg_left (hinner_nsq (u * v) huv1 huv4 hsq) hcc_nn
    have hA_le : ∑ u ∈ Finset.Icc 1 (m ^ 2), ∑ v ∈ Finset.Icc 1 (m ^ 2),
          (if IsSquare (u * v) then (repCount 2 m u : ℝ) * (repCount 2 m v : ℝ) else 0) *
            (2 * (X : ℝ) / Real.log (z : ℝ) + (z : ℝ) ^ 2) ≤
        (2 * (X : ℝ) / Real.log (z : ℝ) + (z : ℝ) ^ 2) * Csq * (m : ℝ) ^ ((11 : ℝ) / 4) := by
      simp_rw [← Finset.sum_mul]
      have hfac_nn : 0 ≤ 2 * (X : ℝ) / Real.log (z : ℝ) + (z : ℝ) ^ 2 := by
        have : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast hz)
        positivity
      have h1 := mul_le_mul_of_nonneg_right (hCsq m hm) hfac_nn
      linarith [show Csq * (m : ℝ) ^ ((11 : ℝ) / 4) * (2 * (X : ℝ) / Real.log (z : ℝ) + (z : ℝ) ^ 2) =
        (2 * (X : ℝ) / Real.log (z : ℝ) + (z : ℝ) ^ 2) * Csq * (m : ℝ) ^ ((11 : ℝ) / 4) by ring]
    have hB_eq : ∑ u ∈ Finset.Icc 1 (m ^ 2), ∑ v ∈ Finset.Icc 1 (m ^ 2),
          (repCount 2 m u : ℝ) * (repCount 2 m v : ℝ) * (8 * (z : ℝ) ^ 2 * (m : ℝ) ^ 4) =
        8 * (z : ℝ) ^ 2 * (m : ℝ) ^ 8 := by
      have hsum2 : ∑ u ∈ Finset.Icc 1 (m ^ 2), (repCount 2 m u : ℝ) = (m : ℝ) ^ 2 := by
        exact_mod_cast sum_repCount 2 m hm
      simp_rw [← Finset.sum_mul]
      have hprod : ∑ u ∈ Finset.Icc 1 (m ^ 2), ∑ v ∈ Finset.Icc 1 (m ^ 2),
            (repCount 2 m u : ℝ) * (repCount 2 m v : ℝ) = (m : ℝ) ^ 4 := by
        simp_rw [← Finset.mul_sum, hsum2, ← Finset.sum_mul, hsum2]; ring
      rw [hprod]; ring
    linarith
  linarith [hsplit_P, hsmall_le, hlarge_le_W, hW_le]

/- ### Section 6: Range 1 + Range 2 Assembly and Main Theorem -/

lemma log_le_inv_eta_rpow {x η : ℝ} (hx : 1 ≤ x) (hη : 0 < η) :
    Real.log x ≤ (1 / η) * x ^ η := by
  have hx_pos : 0 < x := by linarith
  have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx_pos η)
  rw [Real.log_rpow hx_pos] at h1
  have h2 : η * Real.log x ≤ x ^ η := by linarith
  calc Real.log x = (1 / η) * (η * Real.log x) := by field_simp [hη.ne']
    _ ≤ (1 / η) * x ^ η := mul_le_mul_of_nonneg_left h2 (by positivity)

lemma odd_prime_sum_Iic_eq_Icc {p : ℕ} (hp : p.Prime) (m : ℕ) :
    ((∑ n ∈ Finset.Iic m, jacobiSym (n : ℤ) p : ℤ) : ℝ) =
      ∑ n ∈ Finset.Icc 1 m, (jacobiSym (n : ℤ) p : ℝ) := by
  rw [Int.cast_sum]
  have h0 : 0 ∈ Finset.Iic m := Finset.mem_Iic.mpr (Nat.zero_le m)
  rw [← Finset.add_sum_erase _ _ h0, Nat.cast_zero, jacobiSym.zero_left hp.one_lt,
    Int.cast_zero, zero_add]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext n; simp only [Finset.mem_erase, Finset.mem_Iic, Finset.mem_Icc]; omega

lemma erdos981_property_at_prime {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Erdos981.Erdos981Property ε p p := by
  unfold Erdos981.Erdos981Property
  have hsum0 : (∑ n ∈ Finset.Iic p, jacobiSym (n : ℤ) p) = 0 := by
    have hsplit : Finset.Iic p = insert p (Finset.range p) := by
      ext n; simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_range]; omega
    rw [hsplit, Finset.sum_insert (by simp)]
    have hpp : jacobiSym (p : ℤ) p = 0 := by
      rw [jacobiSym.mod_left, Int.emod_self, jacobiSym.zero_left hp.one_lt]
    have hrange : (∑ n ∈ Finset.range p, (jacobiSym (n : ℤ) p : ℂ)) = 0 :=
      sum_jacobi_range_prime hp hp2
    have hrangeZ : ∑ n ∈ Finset.range p, jacobiSym (n : ℤ) p = 0 := by
      have hcast : ((∑ n ∈ Finset.range p, jacobiSym (n : ℤ) p : ℤ) : ℂ) = 0 := by
        rw [Int.cast_sum]; exact hrange
      exact_mod_cast hcast
    rw [hpp, hrangeZ, zero_add]
  rw [hsum0, Int.cast_zero]
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  positivity

lemma lt_f'_imp_ge_sum {ε : ℝ} (_hε : 0 < ε) {p m : ℕ} (hp : p.Prime) (_hp2 : p ≠ 2)
    (hm : m < Erdos981.f' ε p) :
    ε * (m : ℝ) ≤ ∑ n ∈ Finset.Icc 1 m, (jacobiSym (n : ℤ) p : ℝ) := by
  have hnot : ¬ Erdos981.Erdos981Property ε p m := fun hmem =>
    absurd (Nat.sInf_le hmem) (not_le_of_gt hm)
  unfold Erdos981.Erdos981Property at hnot
  push Not at hnot
  rw [odd_prime_sum_Iic_eq_Icc hp m] at hnot
  exact hnot

lemma f'_le_cutoff {ε : ℝ} (hε : 0 < ε) {X p : ℕ} (hX : 16 ≤ X) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpX : p < X) :
    Erdos981.f' ε p ≤ Nat.floor ((32 / ε) * (X : ℝ) ^ ((9 : ℝ) / 16)) + 1 := by
  let M : ℕ := Nat.floor ((32 / ε) * (X : ℝ) ^ ((9 : ℝ) / 16)) + 1
  by_contra hgt
  push Not at hgt
  have hge := lt_f'_imp_ge_sum hε hp hp2 hgt
  have hpv := polya_vinogradov_prime hp hp2 M
  have hnorm_eq : ‖∑ n ∈ Finset.Icc 1 M, (jacobiSym (n : ℤ) p : ℂ)‖ =
      |∑ n ∈ Finset.Icc 1 M, (jacobiSym (n : ℤ) p : ℝ)| := by
    have hc : ∑ n ∈ Finset.Icc 1 M, (jacobiSym (n : ℤ) p : ℂ) =
        ((∑ n ∈ Finset.Icc 1 M, (jacobiSym (n : ℤ) p : ℝ) : ℝ) : ℂ) := by
      push_cast; rfl
    rw [hc, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm_eq] at hpv
  have hsum_le : ∑ n ∈ Finset.Icc 1 M, (jacobiSym (n : ℤ) p : ℝ) ≤
      Real.sqrt (p : ℝ) * (1 + Real.log (p : ℝ)) := (le_abs_self _).trans hpv
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hX_pos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hX16 : (16 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlogX_ge1 : 1 ≤ Real.log (X : ℝ) := by
    have he : Real.exp 1 ≤ (X : ℝ) := by
      have := Real.exp_one_lt_d9
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (X : ℝ) := Real.log_le_log (Real.exp_pos 1) he
  have hsqrt_le : Real.sqrt (p : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hpX.le)
  have hlogp_le : 1 + Real.log (p : ℝ) ≤ 2 * Real.log (X : ℝ) := by
    have := Real.log_le_log hp_pos (by exact_mod_cast hpX.le : (p : ℝ) ≤ (X : ℝ))
    linarith
  have hlogX_rpow : Real.log (X : ℝ) ≤ 16 * (X : ℝ) ^ ((1 : ℝ) / 16) := by
    have h1 := log_le_inv_eta_rpow (x := (X : ℝ)) (η := (1 : ℝ) / 16) (by linarith) (by positivity)
    norm_num at h1; exact h1
  have hrhs_le : Real.sqrt (p : ℝ) * (1 + Real.log (p : ℝ)) ≤ 32 * (X : ℝ) ^ ((9 : ℝ) / 16) := by
    calc Real.sqrt (p : ℝ) * (1 + Real.log (p : ℝ))
        ≤ (X : ℝ) ^ ((1 : ℝ) / 2) * (2 * Real.log (X : ℝ)) :=
          mul_le_mul hsqrt_le hlogp_le (by have := Real.log_nonneg (by exact_mod_cast hp.one_le : (1 : ℝ) ≤ (p : ℝ)); linarith)
            (Real.rpow_nonneg hX_pos.le _)
      _ ≤ (X : ℝ) ^ ((1 : ℝ) / 2) * (2 * (16 * (X : ℝ) ^ ((1 : ℝ) / 16))) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hX_pos.le _)
      _ = 32 * ((X : ℝ) ^ ((1 : ℝ) / 2) * (X : ℝ) ^ ((1 : ℝ) / 16)) := by ring
      _ = 32 * (X : ℝ) ^ ((9 : ℝ) / 16) := by
          rw [← Real.rpow_add hX_pos]; congr 2; norm_num
  have hM_gt : (32 / ε) * (X : ℝ) ^ ((9 : ℝ) / 16) < (M : ℝ) := by
    dsimp [M]; push_cast
    exact Nat.lt_floor_add_one _
  have hεM : 32 * (X : ℝ) ^ ((9 : ℝ) / 16) < ε * (M : ℝ) := by
    have hmul := mul_lt_mul_of_pos_left hM_gt hε
    have heq : ε * ((32 / ε) * (X : ℝ) ^ ((9 : ℝ) / 16)) = 32 * (X : ℝ) ^ ((9 : ℝ) / 16) := by
      field_simp [hε.ne']
    linarith
  linarith

lemma large_sieve_80th_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ (X m : ℕ), 3 ≤ X → 1 ≤ m →
      ∑ p ∈ (Nat.primesBelow X).filter (· ≠ 2),
        (∑ n ∈ Finset.Icc 1 m, (jacobiSym (n : ℤ) p : ℝ)) ^ 80 ≤
      C * ((X : ℝ) ^ 2 + Real.pi * (m : ℝ) ^ 40) * (m : ℝ) ^ 40 * (m : ℝ) ^ ((1 : ℝ) / 4) := by
  obtain ⟨Cd, hCd_pos, hCd⟩ := divisors_card_le_pow 6400 (by norm_num)
  refine ⟨Cd ^ 39, by positivity, fun X m hX hm => ?_⟩
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm_ge1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  let a : ℕ → ℂ := fun u => (repCount 40 m u : ℂ)
  have hls := prime_quad_large_sieve hX (m ^ 40) a
  have hlhs : ∑ p ∈ (Nat.primesBelow X).filter (· ≠ 2),
        ‖∑ u ∈ Finset.Icc 1 (m ^ 40), a u * (jacobiSym (u : ℤ) p : ℂ)‖ ^ 2 =
      ∑ p ∈ (Nat.primesBelow X).filter (· ≠ 2),
        (∑ n ∈ Finset.Icc 1 m, (jacobiSym (n : ℤ) p : ℝ)) ^ 80 := by
    refine Finset.sum_congr rfl fun p _ => ?_
    have hpow := (S_pow_eq_sum_repCount_complex 40 m p hm).symm
    have hreal : ∑ n ∈ Finset.Icc 1 m, (jacobiSym (n : ℤ) p : ℂ) =
        ((∑ n ∈ Finset.Icc 1 m, (jacobiSym (n : ℤ) p : ℝ) : ℝ) : ℂ) := by
      push_cast; rfl
    rw [hpow, hreal, norm_pow, Complex.norm_real, Real.norm_eq_abs, ← pow_mul]
    have h80 : |(∑ n ∈ Finset.Icc 1 m, (jacobiSym (n : ℤ) p : ℝ))| ^ (40 * 2) =
        ((|(∑ n ∈ Finset.Icc 1 m, (jacobiSym (n : ℤ) p : ℝ))| ^ 2) ^ 40) := by ring
    rw [h80, sq_abs]; ring
  rw [hlhs] at hls
  have hcoeff : ∑ u ∈ Finset.Icc 1 (m ^ 40), ‖a u‖ ^ 2 ≤
      Cd ^ 39 * (m : ℝ) ^ 40 * (m : ℝ) ^ ((1 : ℝ) / 4) := by
    have hrep_le : ∀ u ∈ Finset.Icc 1 (m ^ 40),
        (repCount 40 m u : ℝ) ≤ Cd ^ 39 * (m : ℝ) ^ ((1 : ℝ) / 4) := by
      intro u hu
      have hu1 := (Finset.mem_Icc.mp hu).1
      have hu2 := (Finset.mem_Icc.mp hu).2
      have h1 : (repCount 40 m u : ℝ) ≤ (u.divisors.card : ℝ) ^ 39 := by
        exact_mod_cast repCount_le_divisors_pow 40 m u (by norm_num) hu1
      have h2 := pow_le_pow_left₀ (by positivity) (hCd u hu1) 39
      rw [mul_pow] at h2
      have h3 : ((u : ℝ) ^ ((1 : ℝ) / (6400 : ℕ))) ^ 39 ≤ (m : ℝ) ^ ((1 : ℝ) / 4) := by
        have hpow_eq : ((u : ℝ) ^ ((1 : ℝ) / (6400 : ℕ))) ^ 39 = (u : ℝ) ^ ((39 : ℝ) / 6400) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; congr 1; norm_num
        rw [hpow_eq]
        calc (u : ℝ) ^ ((39 : ℝ) / 6400)
            ≤ ((m ^ 40 : ℕ) : ℝ) ^ ((39 : ℝ) / 6400) :=
              Real.rpow_le_rpow (by positivity) (by exact_mod_cast hu2) (by positivity)
          _ = ((m : ℝ) ^ (40 : ℝ)) ^ ((39 : ℝ) / 6400) := by rw [Nat.cast_pow, ← Real.rpow_natCast (m : ℝ) 40]; norm_num
          _ = (m : ℝ) ^ ((39 : ℝ) / 160) := by rw [← Real.rpow_mul hm_pos.le]; congr 1; norm_num
          _ ≤ (m : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow_of_exponent_le hm_ge1 (by norm_num)
      exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity)))
    have hsum40 : ∑ u ∈ Finset.Icc 1 (m ^ 40), (repCount 40 m u : ℝ) = (m : ℝ) ^ 40 := by
      exact_mod_cast sum_repCount 40 m hm
    calc ∑ u ∈ Finset.Icc 1 (m ^ 40), ‖a u‖ ^ 2
        = ∑ u ∈ Finset.Icc 1 (m ^ 40), (repCount 40 m u : ℝ) * (repCount 40 m u : ℝ) := by
          refine Finset.sum_congr rfl fun u _ => ?_
          dsimp [a]; rw [Complex.norm_natCast, sq]
      _ ≤ ∑ u ∈ Finset.Icc 1 (m ^ 40), (Cd ^ 39 * (m : ℝ) ^ ((1 : ℝ) / 4)) * (repCount 40 m u : ℝ) :=
          Finset.sum_le_sum fun u hu => mul_le_mul_of_nonneg_right (hrep_le u hu) (by positivity)
      _ = Cd ^ 39 * (m : ℝ) ^ ((1 : ℝ) / 4) * ∑ u ∈ Finset.Icc 1 (m ^ 40), (repCount 40 m u : ℝ) :=
          (Finset.mul_sum _ _ _).symm
      _ = Cd ^ 39 * (m : ℝ) ^ 40 * (m : ℝ) ^ ((1 : ℝ) / 4) := by rw [hsum40]; ring
  calc ∑ p ∈ (Nat.primesBelow X).filter (· ≠ 2),
        (∑ n ∈ Finset.Icc 1 m, (jacobiSym (n : ℤ) p : ℝ)) ^ 80
      ≤ ((X : ℝ) ^ 2 + Real.pi * ((m ^ 40 : ℕ) : ℝ)) * ∑ u ∈ Finset.Icc 1 (m ^ 40), ‖a u‖ ^ 2 := hls
    _ ≤ ((X : ℝ) ^ 2 + Real.pi * (m : ℝ) ^ 40) * (Cd ^ 39 * (m : ℝ) ^ 40 * (m : ℝ) ^ ((1 : ℝ) / 4)) := by
        rw [Nat.cast_pow]
        exact mul_le_mul_of_nonneg_left hcoeff (by positivity [Real.pi_pos])
    _ = Cd ^ 39 * ((X : ℝ) ^ 2 + Real.pi * (m : ℝ) ^ 40) * (m : ℝ) ^ 40 * (m : ℝ) ^ ((1 : ℝ) / 4) := by ring

lemma tail_pseries_small {η : ℝ} (hη : 0 < η) :
    ∃ B₀ : ℕ, 1 ≤ B₀ ∧ ∀ B M : ℕ, B₀ ≤ B →
      ∑ m ∈ Finset.Icc B M, (m : ℝ) ^ (-(5 : ℝ) / 4) ≤ η := by
  have hsum : Summable (fun m : ℕ => (m : ℝ) ^ (-(5 : ℝ) / 4)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hnn : ∀ m : ℕ, 0 ≤ (m : ℝ) ^ (-(5 : ℝ) / 4) := fun m => Real.rpow_nonneg (Nat.cast_nonneg m) _
  have htend := hsum.hasSum.tendsto_sum_nat
  have hev := (Metric.tendsto_atTop.mp htend) η hη
  obtain ⟨N₀, hN₀⟩ := hev
  refine ⟨max 1 N₀, le_max_left _ _, fun B M hB => ?_⟩
  by_cases hBM : M < B
  · have : Finset.Icc B M = ∅ := Finset.Icc_eq_empty (by omega)
    rw [this, Finset.sum_empty]; exact hη.le
  · push Not at hBM
    have hsplit : Finset.range (M + 1) = Finset.range B ∪ Finset.Icc B M := by
      ext m; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Icc]; omega
    have hdisj : Disjoint (Finset.range B) (Finset.Icc B M) := by
      rw [Finset.disjoint_left]; intro m h1 h2
      have := Finset.mem_range.mp h1; have := (Finset.mem_Icc.mp h2).1; omega
    have htot := Finset.sum_union hdisj (f := fun m : ℕ => (m : ℝ) ^ (-(5 : ℝ) / 4))
    rw [← hsplit] at htot
    have hle_tsum : ∑ m ∈ Finset.range (M + 1), (m : ℝ) ^ (-(5 : ℝ) / 4) ≤
        ∑' m : ℕ, (m : ℝ) ^ (-(5 : ℝ) / 4) := hsum.sum_le_tsum _ (fun m _ => hnn m)
    have hB_ge : N₀ ≤ B := (le_max_right 1 N₀).trans hB
    have hdist := hN₀ B hB_ge
    rw [Real.dist_eq, abs_lt] at hdist
    linarith

lemma layer_cake_nat (P : Finset ℕ) (g : ℕ → ℕ) (B M : ℕ) (hle : ∀ p ∈ P, g p ≤ M) :
    ∑ p ∈ P, (g p - min B (g p)) = ∑ m ∈ Finset.Icc B M, (P.filter (fun p => m < g p)).card := by
  have hpoint : ∀ p ∈ P, g p - min B (g p) = ∑ m ∈ Finset.Icc B M, if m < g p then 1 else 0 := by
    intro p hp
    have hgp := hle p hp
    rw [← Finset.card_filter]
    by_cases hlt : B < g p
    · have hmin : min B (g p) = B := min_eq_left hlt.le
      rw [hmin]
      have hfilt : (Finset.Icc B M).filter (fun m => m < g p) = Finset.Ico B (g p) := by
        ext m; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]; omega
      rw [hfilt, Nat.card_Ico]
    · have hmin : min B (g p) = g p := min_eq_right (by omega)
      rw [hmin, Nat.sub_self]
      have hfilt : (Finset.Icc B M).filter (fun m => m < g p) = ∅ := by
        ext m; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false]; omega
      rw [hfilt, Finset.card_empty]
  rw [Finset.sum_congr rfl hpoint, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.card_filter]

lemma range1_bound {ε δ Csq L_p x : ℝ} {B M_max : ℕ}
    (hε : 0 < ε) (hCsq_pos : 0 < Csq)
    (hselberg : ∀ (X z m : ℕ), 2 ≤ z → z < X → 1 ≤ m →
      ∑ p ∈ (Nat.primesBelow X).filter (· ≠ 2),
        (∑ n ∈ Finset.Icc 1 m, (jacobiSym (n : ℤ) p : ℝ)) ^ 4 ≤
      (z : ℝ) * (m : ℝ) ^ 4 +
        (2 * (X : ℝ) / Real.log (z : ℝ) + (z : ℝ) ^ 2) * Csq * (m : ℝ) ^ ((11 : ℝ) / 4) +
        8 * (z : ℝ) ^ 2 * (m : ℝ) ^ 8)
    (htail : ∀ M : ℕ, ∑ m ∈ Finset.Icc B M, (m : ℝ) ^ (-(5 : ℝ) / 4) ≤ (δ / 2) / (32 * Csq / ε ^ 4))
    (hsum_all : Summable (fun m : ℕ => (m : ℝ) ^ (-(5 : ℝ) / 4)))
    (hLp_eq : L_p = ∑' m : ℕ, (m : ℝ) ^ (-(5 : ℝ) / 4))
    (hB1 : 1 ≤ B) (hx65 : (65536 : ℝ) ≤ x) :
    let X : ℕ := ⌈x⌉₊
    let P_odd := (Nat.primesBelow X).filter (· ≠ 2)
    let M1 : ℕ := Nat.floor ((X : ℝ) ^ ((1 : ℝ) / 20))
    let R1 := (Finset.Icc B M_max).filter (· ≤ M1)
    (∑ m ∈ R1, ((P_odd.filter (fun p => m < Erdos981.f' ε p)).card : ℝ)) * Real.log x / x ≤
      δ / 2 + (32 / ε ^ 4 + 32 * Csq * L_p / ε ^ 4 + 256 / ε ^ 4) * (X : ℝ) ^ (-(1 : ℝ) / 8) := by
  intro X P_odd M1 R1
  have hx_pos : 0 < x := by linarith
  have hX_ge_x : x ≤ (X : ℝ) := Nat.le_ceil x
  have hX_lt : (X : ℝ) < x + 1 := Nat.ceil_lt_add_one hx_pos.le
  have hX_le_2x : (X : ℝ) ≤ 2 * x := by linarith
  have hX_ge65536 : 65536 ≤ X := by
    have : (65536 : ℝ) ≤ (X : ℝ) := hx65.trans hX_ge_x
    exact_mod_cast this
  have hX_pos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hX_ge1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (by omega : 1 ≤ X)
  have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogX_pos : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
  have hlogx_div_x : Real.log x / x ≤ 32 * (X : ℝ) ^ (-(15 : ℝ) / 16) := by
    have hlog_le : Real.log x ≤ 16 * (X : ℝ) ^ ((1 : ℝ) / 16) := by
      have h1 := log_le_inv_eta_rpow (x := (X : ℝ)) (η := (1 : ℝ) / 16) hX_ge1 (by positivity)
      norm_num at h1
      exact (Real.log_le_log hx_pos hX_ge_x).trans h1
    have hinv_le : 1 / x ≤ 2 / (X : ℝ) := by
      rw [div_le_div_iff₀ hx_pos hX_pos]; linarith
    calc Real.log x / x = Real.log x * (1 / x) := by ring
      _ ≤ (16 * (X : ℝ) ^ ((1 : ℝ) / 16)) * (2 / (X : ℝ)) :=
          mul_le_mul hlog_le hinv_le (by positivity) (by positivity)
      _ = 32 * ((X : ℝ) ^ ((1 : ℝ) / 16) * (X : ℝ) ^ (-(1 : ℝ))) := by
          rw [Real.rpow_neg_one]; ring
      _ = 32 * (X : ℝ) ^ (-(15 : ℝ) / 16) := by
          rw [← Real.rpow_add hX_pos]; congr 2; norm_num
  let z : ℕ := Nat.floor ((X : ℝ) ^ ((1 : ℝ) / 4))
  have hX14_ge16 : (16 : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 4) := by
    have h1 : (16 : ℝ) = ((65536 : ℝ) ^ ((1 : ℝ) / 4)) := by
      have h2 : (65536 : ℝ) = (16 : ℝ) ^ (4 : ℝ) := by norm_num
      rw [h2, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [h1]
    exact Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hX_ge65536) (by positivity)
  have hz_ge16 : 16 ≤ z := Nat.le_floor hX14_ge16
  have hz_le_X14 : (z : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 4) := Nat.floor_le (by positivity)
  have hz_lt_X : z < X := by
    have hX14_lt : (X : ℝ) ^ ((1 : ℝ) / 4) < (X : ℝ) := by
      have h1 : (X : ℝ) ^ ((1 : ℝ) / 4) < (X : ℝ) ^ (1 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by linarith : (1 : ℝ) < (X : ℝ)) (by norm_num)
      simpa using h1
    have : (z : ℝ) < (X : ℝ) := hz_le_X14.trans_lt hX14_lt
    exact_mod_cast this
  have hlogz_ge : (1 / 8 : ℝ) * Real.log (X : ℝ) ≤ Real.log (z : ℝ) := by
    have hX18_ge4 : (4 : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 8) := by
      have h1 : (4 : ℝ) = ((65536 : ℝ) ^ ((1 : ℝ) / 8)) := by
        have h2 : (65536 : ℝ) = (4 : ℝ) ^ (8 : ℝ) := by norm_num
        rw [h2, ← Real.rpow_mul (by norm_num)]; norm_num
      rw [h1]
      exact Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hX_ge65536) (by positivity)
    have hz_ge_X18 : (X : ℝ) ^ ((1 : ℝ) / 8) ≤ (z : ℝ) := by
      have hgt : (X : ℝ) ^ ((1 : ℝ) / 4) - 1 < (z : ℝ) := by
        have := Nat.lt_floor_add_one ((X : ℝ) ^ ((1 : ℝ) / 4))
        dsimp [z]; linarith
      have hsq : (X : ℝ) ^ ((1 : ℝ) / 4) = (X : ℝ) ^ ((1 : ℝ) / 8) * (X : ℝ) ^ ((1 : ℝ) / 8) := by
        rw [← Real.rpow_add hX_pos]; congr 1; norm_num
      have h4 : 4 * (X : ℝ) ^ ((1 : ℝ) / 8) ≤ (X : ℝ) ^ ((1 : ℝ) / 4) := by
        rw [hsq]
        exact mul_le_mul_of_nonneg_right hX18_ge4 (Real.rpow_nonneg hX_pos.le _)
      linarith
    calc (1 / 8 : ℝ) * Real.log (X : ℝ) = Real.log ((X : ℝ) ^ ((1 : ℝ) / 8)) := (Real.log_rpow hX_pos _).symm
      _ ≤ Real.log (z : ℝ) := Real.log_le_log (Real.rpow_pos_of_pos hX_pos _) hz_ge_X18
  have hlogz_pos : 0 < Real.log (z : ℝ) := by linarith
  have hNm_le : ∀ m ∈ R1, ((P_odd.filter (fun p => m < Erdos981.f' ε p)).card : ℝ) ≤
      ((z : ℝ) / ε ^ 4) +
      ((2 * (X : ℝ) / Real.log (z : ℝ) + (z : ℝ) ^ 2) * Csq / ε ^ 4) * (m : ℝ) ^ (-(5 : ℝ) / 4) +
      (8 * (z : ℝ) ^ 2 / ε ^ 4) * (m : ℝ) ^ 4 := by
    intro m hmR1
    have hmB := (Finset.mem_Icc.mp (Finset.mem_filter.mp hmR1).1).1
    have hm1 : 1 ≤ m := by omega
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hmarkov : (ε * (m : ℝ)) ^ 4 * ((P_odd.filter (fun p => m < Erdos981.f' ε p)).card : ℝ) ≤
        ∑ p ∈ P_odd, (∑ n ∈ Finset.Icc 1 m, (jacobiSym (n : ℤ) p : ℝ)) ^ 4 := by
      calc (ε * (m : ℝ)) ^ 4 * ((P_odd.filter (fun p => m < Erdos981.f' ε p)).card : ℝ)
          = ∑ _p ∈ P_odd.filter (fun p => m < Erdos981.f' ε p), (ε * (m : ℝ)) ^ 4 := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        _ ≤ ∑ p ∈ P_odd.filter (fun p => m < Erdos981.f' ε p),
              (∑ n ∈ Finset.Icc 1 m, (jacobiSym (n : ℤ) p : ℝ)) ^ 4 := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hp_odd := (Finset.mem_filter.mp hp).1
            have hmlt := (Finset.mem_filter.mp hp).2
            have hp_pr := (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hp_odd).1).2
            have hp2 := (Finset.mem_filter.mp hp_odd).2
            exact pow_le_pow_left₀ (by positivity) (lt_f'_imp_ge_sum hε hp_pr hp2 hmlt) 4
        _ ≤ ∑ p ∈ P_odd, (∑ n ∈ Finset.Icc 1 m, (jacobiSym (n : ℤ) p : ℝ)) ^ 4 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun _ _ _ => Even.pow_nonneg (by decide) _)
    have hsel := hselberg X z m (by omega) hz_lt_X hm1
    have hden_pos : 0 < (ε * (m : ℝ)) ^ 4 := by positivity
    have hdiv := (le_div_iff₀' hden_pos).mpr (hmarkov.trans hsel)
    have hrpow_div : (m : ℝ) ^ ((11 : ℝ) / 4) / (m : ℝ) ^ 4 = (m : ℝ) ^ (-(5 : ℝ) / 4) := by
      rw [← Real.rpow_natCast (m : ℝ) 4, ← Real.rpow_sub hm_pos]; congr 1; norm_num
    have hrew : ((z : ℝ) * (m : ℝ) ^ 4 +
          (2 * (X : ℝ) / Real.log (z : ℝ) + (z : ℝ) ^ 2) * Csq * (m : ℝ) ^ ((11 : ℝ) / 4) +
          8 * (z : ℝ) ^ 2 * (m : ℝ) ^ 8) / (ε * (m : ℝ)) ^ 4 =
        ((z : ℝ) / ε ^ 4) +
          ((2 * (X : ℝ) / Real.log (z : ℝ) + (z : ℝ) ^ 2) * Csq / ε ^ 4) * (m : ℝ) ^ (-(5 : ℝ) / 4) +
          (8 * (z : ℝ) ^ 2 / ε ^ 4) * (m : ℝ) ^ 4 := by
      rw [mul_pow, ← hrpow_div]
      field_simp [hε.ne', hm_pos.ne']
    linarith
  have hR1_sub : R1 ⊆ Finset.Icc B M1 := fun m hm =>
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1, (Finset.mem_filter.mp hm).2⟩
  have hR1_card : (R1.card : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 20) := by
    have hsub : R1 ⊆ Finset.Icc 1 M1 := fun m hm =>
      Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1; omega,
        (Finset.mem_filter.mp hm).2⟩
    have h1 : R1.card ≤ M1 := (Finset.card_le_card hsub).trans (by rw [Nat.card_Icc, Nat.add_sub_cancel])
    exact ((Nat.cast_le (α := ℝ)).mpr h1).trans (Nat.floor_le (by positivity))
  have hsum_p54_tail : ∑ m ∈ R1, (m : ℝ) ^ (-(5 : ℝ) / 4) ≤ (δ / 2) / (32 * Csq / ε ^ 4) := by
    calc ∑ m ∈ R1, (m : ℝ) ^ (-(5 : ℝ) / 4)
        ≤ ∑ m ∈ Finset.Icc B M1, (m : ℝ) ^ (-(5 : ℝ) / 4) :=
          Finset.sum_le_sum_of_subset_of_nonneg hR1_sub (fun m _ _ => Real.rpow_nonneg (Nat.cast_nonneg m) _)
      _ ≤ (δ / 2) / (32 * Csq / ε ^ 4) := htail M1
  have hsum_p54_all : ∑ m ∈ R1, (m : ℝ) ^ (-(5 : ℝ) / 4) ≤ L_p := by
    rw [hLp_eq]
    exact hsum_all.sum_le_tsum R1 (fun m _ => Real.rpow_nonneg (Nat.cast_nonneg m) _)
  have hsum_m4 : ∑ m ∈ R1, (m : ℝ) ^ 4 ≤ (X : ℝ) ^ ((1 : ℝ) / 4) := by
    have hterm : ∀ m ∈ R1, (m : ℝ) ^ 4 ≤ ((X : ℝ) ^ ((1 : ℝ) / 20)) ^ 4 := fun m hm => by
      have hm_le : (m : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 20) :=
        ((Nat.cast_le (α := ℝ)).mpr (Finset.mem_filter.mp hm).2).trans (Nat.floor_le (by positivity))
      exact pow_le_pow_left₀ (Nat.cast_nonneg m) hm_le 4
    calc ∑ m ∈ R1, (m : ℝ) ^ 4
        ≤ ∑ _m ∈ R1, ((X : ℝ) ^ ((1 : ℝ) / 20)) ^ 4 := Finset.sum_le_sum hterm
      _ = (R1.card : ℝ) * ((X : ℝ) ^ ((1 : ℝ) / 20)) ^ 4 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (X : ℝ) ^ ((1 : ℝ) / 20) * ((X : ℝ) ^ ((1 : ℝ) / 20)) ^ 4 :=
          mul_le_mul_of_nonneg_right hR1_card (by positivity)
      _ = ((X : ℝ) ^ ((1 : ℝ) / 20)) ^ 5 := by ring
      _ = (X : ℝ) ^ ((1 : ℝ) / 4) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hX_pos.le]; congr 1; norm_num
  have hz2_le : (z : ℝ) ^ 2 ≤ (X : ℝ) ^ ((1 : ℝ) / 2) := by
    calc (z : ℝ) ^ 2 ≤ ((X : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg z) hz_le_X14 2
      _ = (X : ℝ) ^ ((1 : ℝ) / 2) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hX_pos.le]; congr 1; norm_num
  have hR1_sum : ∑ m ∈ R1, ((P_odd.filter (fun p => m < Erdos981.f' ε p)).card : ℝ) ≤
      ((R1.card : ℝ) * ((z : ℝ) / ε ^ 4)) +
      ((2 * (X : ℝ) / Real.log (z : ℝ)) * Csq / ε ^ 4) * (∑ m ∈ R1, (m : ℝ) ^ (-(5 : ℝ) / 4)) +
      (((z : ℝ) ^ 2) * Csq / ε ^ 4) * (∑ m ∈ R1, (m : ℝ) ^ (-(5 : ℝ) / 4)) +
      (8 * (z : ℝ) ^ 2 / ε ^ 4) * (∑ m ∈ R1, (m : ℝ) ^ 4) := by
    calc ∑ m ∈ R1, ((P_odd.filter (fun p => m < Erdos981.f' ε p)).card : ℝ)
        ≤ ∑ m ∈ R1, (((z : ℝ) / ε ^ 4) +
            ((2 * (X : ℝ) / Real.log (z : ℝ) + (z : ℝ) ^ 2) * Csq / ε ^ 4) * (m : ℝ) ^ (-(5 : ℝ) / 4) +
            (8 * (z : ℝ) ^ 2 / ε ^ 4) * (m : ℝ) ^ 4) := Finset.sum_le_sum hNm_le
      _ = ((R1.card : ℝ) * ((z : ℝ) / ε ^ 4)) +
            ((2 * (X : ℝ) / Real.log (z : ℝ)) * Csq / ε ^ 4) * (∑ m ∈ R1, (m : ℝ) ^ (-(5 : ℝ) / 4)) +
            (((z : ℝ) ^ 2) * Csq / ε ^ 4) * (∑ m ∈ R1, (m : ℝ) ^ (-(5 : ℝ) / 4)) +
            (8 * (z : ℝ) ^ 2 / ε ^ 4) * (∑ m ∈ R1, (m : ℝ) ^ 4) := by
          simp_rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
          ring
  have hT0 : ((2 * (X : ℝ) / Real.log (z : ℝ)) * Csq / ε ^ 4) *
      (∑ m ∈ R1, (m : ℝ) ^ (-(5 : ℝ) / 4)) * Real.log x / x ≤ δ / 2 := by
    have hfac : (2 * (X : ℝ) / Real.log (z : ℝ)) * Real.log x / x ≤ 32 := by
      have h1 : Real.log x ≤ Real.log (X : ℝ) := Real.log_le_log hx_pos hX_ge_x
      have h2 : (X : ℝ) / Real.log (z : ℝ) ≤ (2 * x) / ((1 / 8 : ℝ) * Real.log x) := by
        rw [div_le_div_iff₀ hlogz_pos (by positivity)]
        have hlogx_z : (1 / 8 : ℝ) * Real.log x ≤ Real.log (z : ℝ) := by linarith
        exact mul_le_mul hX_le_2x hlogx_z (by positivity) (by positivity)
      have h3 : (2 * x) / ((1 / 8 : ℝ) * Real.log x) * Real.log x / x = 16 := by
        field_simp [hlogx_pos.ne', hx_pos.ne']; ring
      have h4 : (2 * (X : ℝ) / Real.log (z : ℝ)) * Real.log x / x =
          2 * (((X : ℝ) / Real.log (z : ℝ)) * (Real.log x / x)) := by ring
      have h5 : ((X : ℝ) / Real.log (z : ℝ)) * (Real.log x / x) ≤
          ((2 * x) / ((1 / 8 : ℝ) * Real.log x)) * (Real.log x / x) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
      have h6 : ((2 * x) / ((1 / 8 : ℝ) * Real.log x)) * (Real.log x / x) = 16 := by
        have : ((2 * x) / ((1 / 8 : ℝ) * Real.log x)) * (Real.log x / x) =
            (2 * x) / ((1 / 8 : ℝ) * Real.log x) * Real.log x / x := by ring
        rw [this, h3]
      linarith
    have hrew : ((2 * (X : ℝ) / Real.log (z : ℝ)) * Csq / ε ^ 4) *
          (∑ m ∈ R1, (m : ℝ) ^ (-(5 : ℝ) / 4)) * Real.log x / x =
        ((2 * (X : ℝ) / Real.log (z : ℝ)) * Real.log x / x) * (Csq / ε ^ 4) *
          (∑ m ∈ R1, (m : ℝ) ^ (-(5 : ℝ) / 4)) := by ring
    rw [hrew]
    have hsum_nn : 0 ≤ ∑ m ∈ R1, (m : ℝ) ^ (-(5 : ℝ) / 4) :=
      Finset.sum_nonneg fun m _ => Real.rpow_nonneg (Nat.cast_nonneg m) _
    calc ((2 * (X : ℝ) / Real.log (z : ℝ)) * Real.log x / x) * (Csq / ε ^ 4) *
            (∑ m ∈ R1, (m : ℝ) ^ (-(5 : ℝ) / 4))
        ≤ 32 * (Csq / ε ^ 4) * ((δ / 2) / (32 * Csq / ε ^ 4)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right hfac (by positivity)) hsum_p54_tail hsum_nn (by positivity)
      _ = δ / 2 := by field_simp [hCsq_pos.ne', hε.ne']
  have hT1 : ((R1.card : ℝ) * ((z : ℝ) / ε ^ 4)) * Real.log x / x ≤ (32 / ε ^ 4) * (X : ℝ) ^ (-(1 : ℝ) / 8) := by
    have hprod : (R1.card : ℝ) * (z : ℝ) ≤ (X : ℝ) ^ ((3 : ℝ) / 10) := by
      calc (R1.card : ℝ) * (z : ℝ)
          ≤ (X : ℝ) ^ ((1 : ℝ) / 20) * (X : ℝ) ^ ((1 : ℝ) / 4) :=
            mul_le_mul hR1_card hz_le_X14 (Nat.cast_nonneg z) (by positivity)
        _ = (X : ℝ) ^ ((3 : ℝ) / 10) := by rw [← Real.rpow_add hX_pos]; congr 1; norm_num
    have hexp : (X : ℝ) ^ ((3 : ℝ) / 10) * (X : ℝ) ^ (-(15 : ℝ) / 16) ≤ (X : ℝ) ^ (-(1 : ℝ) / 8) := by
      rw [← Real.rpow_add hX_pos]
      exact Real.rpow_le_rpow_of_exponent_le hX_ge1 (by norm_num)
    calc ((R1.card : ℝ) * ((z : ℝ) / ε ^ 4)) * Real.log x / x
        = ((R1.card : ℝ) * (z : ℝ)) / ε ^ 4 * (Real.log x / x) := by ring
      _ ≤ ((X : ℝ) ^ ((3 : ℝ) / 10) / ε ^ 4) * (32 * (X : ℝ) ^ (-(15 : ℝ) / 16)) :=
          mul_le_mul (div_le_div_of_nonneg_right hprod (by positivity)) hlogx_div_x (by positivity) (by positivity)
      _ = (32 / ε ^ 4) * ((X : ℝ) ^ ((3 : ℝ) / 10) * (X : ℝ) ^ (-(15 : ℝ) / 16)) := by ring
      _ ≤ (32 / ε ^ 4) * (X : ℝ) ^ (-(1 : ℝ) / 8) := mul_le_mul_of_nonneg_left hexp (by positivity)
  have hT2 : (((z : ℝ) ^ 2) * Csq / ε ^ 4) * (∑ m ∈ R1, (m : ℝ) ^ (-(5 : ℝ) / 4)) * Real.log x / x ≤
      (32 * Csq * L_p / ε ^ 4) * (X : ℝ) ^ (-(1 : ℝ) / 8) := by
    have hexp : (X : ℝ) ^ ((1 : ℝ) / 2) * (X : ℝ) ^ (-(15 : ℝ) / 16) ≤ (X : ℝ) ^ (-(1 : ℝ) / 8) := by
      rw [← Real.rpow_add hX_pos]
      exact Real.rpow_le_rpow_of_exponent_le hX_ge1 (by norm_num)
    have hsum_nn : 0 ≤ ∑ m ∈ R1, (m : ℝ) ^ (-(5 : ℝ) / 4) :=
      Finset.sum_nonneg fun m _ => Real.rpow_nonneg (Nat.cast_nonneg m) _
    have hLp_nn : 0 ≤ L_p := by rw [hLp_eq]; exact tsum_nonneg fun m => Real.rpow_nonneg (Nat.cast_nonneg m) _
    calc (((z : ℝ) ^ 2) * Csq / ε ^ 4) * (∑ m ∈ R1, (m : ℝ) ^ (-(5 : ℝ) / 4)) * Real.log x / x
        = ((z : ℝ) ^ 2 * (∑ m ∈ R1, (m : ℝ) ^ (-(5 : ℝ) / 4))) * (Csq / ε ^ 4) * (Real.log x / x) := by ring
      _ ≤ ((X : ℝ) ^ ((1 : ℝ) / 2) * L_p) * (Csq / ε ^ 4) * (32 * (X : ℝ) ^ (-(15 : ℝ) / 16)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right
            (mul_le_mul hz2_le hsum_p54_all hsum_nn (by positivity)) (by positivity))
            hlogx_div_x (by positivity) (by positivity)
      _ = (32 * Csq * L_p / ε ^ 4) * ((X : ℝ) ^ ((1 : ℝ) / 2) * (X : ℝ) ^ (-(15 : ℝ) / 16)) := by ring
      _ ≤ (32 * Csq * L_p / ε ^ 4) * (X : ℝ) ^ (-(1 : ℝ) / 8) := mul_le_mul_of_nonneg_left hexp (by positivity)
  have hT3 : (8 * (z : ℝ) ^ 2 / ε ^ 4) * (∑ m ∈ R1, (m : ℝ) ^ 4) * Real.log x / x ≤
      (256 / ε ^ 4) * (X : ℝ) ^ (-(1 : ℝ) / 8) := by
    have hprod : (z : ℝ) ^ 2 * (∑ m ∈ R1, (m : ℝ) ^ 4) ≤ (X : ℝ) ^ ((3 : ℝ) / 4) := by
      calc (z : ℝ) ^ 2 * (∑ m ∈ R1, (m : ℝ) ^ 4)
          ≤ (X : ℝ) ^ ((1 : ℝ) / 2) * (X : ℝ) ^ ((1 : ℝ) / 4) :=
            mul_le_mul hz2_le hsum_m4 (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
        _ = (X : ℝ) ^ ((3 : ℝ) / 4) := by rw [← Real.rpow_add hX_pos]; congr 1; norm_num
    have hexp : (X : ℝ) ^ ((3 : ℝ) / 4) * (X : ℝ) ^ (-(15 : ℝ) / 16) ≤ (X : ℝ) ^ (-(1 : ℝ) / 8) := by
      rw [← Real.rpow_add hX_pos]
      exact Real.rpow_le_rpow_of_exponent_le hX_ge1 (by norm_num)
    calc (8 * (z : ℝ) ^ 2 / ε ^ 4) * (∑ m ∈ R1, (m : ℝ) ^ 4) * Real.log x / x
        = (8 / ε ^ 4) * ((z : ℝ) ^ 2 * (∑ m ∈ R1, (m : ℝ) ^ 4)) * (Real.log x / x) := by ring
      _ ≤ (8 / ε ^ 4) * (X : ℝ) ^ ((3 : ℝ) / 4) * (32 * (X : ℝ) ^ (-(15 : ℝ) / 16)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hprod (by positivity)) hlogx_div_x (by positivity) (by positivity)
      _ = (256 / ε ^ 4) * ((X : ℝ) ^ ((3 : ℝ) / 4) * (X : ℝ) ^ (-(15 : ℝ) / 16)) := by ring
      _ ≤ (256 / ε ^ 4) * (X : ℝ) ^ (-(1 : ℝ) / 8) := mul_le_mul_of_nonneg_left hexp (by positivity)
  calc (∑ m ∈ R1, ((P_odd.filter (fun p => m < Erdos981.f' ε p)).card : ℝ)) * Real.log x / x
      = (∑ m ∈ R1, ((P_odd.filter (fun p => m < Erdos981.f' ε p)).card : ℝ)) * (Real.log x / x) := by ring
    _ ≤ (((R1.card : ℝ) * ((z : ℝ) / ε ^ 4)) +
          ((2 * (X : ℝ) / Real.log (z : ℝ)) * Csq / ε ^ 4) * (∑ m ∈ R1, (m : ℝ) ^ (-(5 : ℝ) / 4)) +
          (((z : ℝ) ^ 2) * Csq / ε ^ 4) * (∑ m ∈ R1, (m : ℝ) ^ (-(5 : ℝ) / 4)) +
          (8 * (z : ℝ) ^ 2 / ε ^ 4) * (∑ m ∈ R1, (m : ℝ) ^ 4)) * (Real.log x / x) :=
        mul_le_mul_of_nonneg_right hR1_sum (by positivity)
    _ = ((R1.card : ℝ) * ((z : ℝ) / ε ^ 4)) * Real.log x / x +
          ((2 * (X : ℝ) / Real.log (z : ℝ)) * Csq / ε ^ 4) * (∑ m ∈ R1, (m : ℝ) ^ (-(5 : ℝ) / 4)) * Real.log x / x +
          (((z : ℝ) ^ 2) * Csq / ε ^ 4) * (∑ m ∈ R1, (m : ℝ) ^ (-(5 : ℝ) / 4)) * Real.log x / x +
          (8 * (z : ℝ) ^ 2 / ε ^ 4) * (∑ m ∈ R1, (m : ℝ) ^ 4) * Real.log x / x := by ring
    _ ≤ (32 / ε ^ 4) * (X : ℝ) ^ (-(1 : ℝ) / 8) + δ / 2 +
          (32 * Csq * L_p / ε ^ 4) * (X : ℝ) ^ (-(1 : ℝ) / 8) +
          (256 / ε ^ 4) * (X : ℝ) ^ (-(1 : ℝ) / 8) := by linarith [hT0, hT1, hT2, hT3]
    _ = δ / 2 + (32 / ε ^ 4 + 32 * Csq * L_p / ε ^ 4 + 256 / ε ^ 4) * (X : ℝ) ^ (-(1 : ℝ) / 8) := by ring

lemma range2_bound {ε Cls x : ℝ} {B : ℕ}
    (hε : 0 < ε) (hCls_pos : 0 < Cls)
    (hls80 : ∀ (X m : ℕ), 3 ≤ X → 1 ≤ m →
      ∑ p ∈ (Nat.primesBelow X).filter (· ≠ 2),
        (∑ n ∈ Finset.Icc 1 m, (jacobiSym (n : ℤ) p : ℝ)) ^ 80 ≤
      Cls * ((X : ℝ) ^ 2 + Real.pi * (m : ℝ) ^ 40) * (m : ℝ) ^ 40 * (m : ℝ) ^ ((1 : ℝ) / 4))
    (hB1 : 1 ≤ B) (hx65 : (65536 : ℝ) ≤ x) :
    let X : ℕ := ⌈x⌉₊
    let P_odd := (Nat.primesBelow X).filter (· ≠ 2)
    let M_max : ℕ := Nat.floor ((32 / ε) * (X : ℝ) ^ ((9 : ℝ) / 16)) + 1
    let M1 : ℕ := Nat.floor ((X : ℝ) ^ ((1 : ℝ) / 20))
    let R2 := (Finset.Icc B M_max).filter (fun m => ¬ m ≤ M1)
    let A_cut : ℝ := 32 / ε + 1
    (∑ m ∈ R2, ((P_odd.filter (fun p => m < Erdos981.f' ε p)).card : ℝ)) * Real.log x / x ≤
      (32 * Cls * A_cut / ε ^ 80 + 32 * Cls * Real.pi * A_cut ^ ((5 : ℝ) / 4) / ε ^ 80) *
        (X : ℝ) ^ (-(1 : ℝ) / 8) := by
  intro X P_odd M_max M1 R2 A_cut
  have hx_pos : 0 < x := by linarith
  have hX_ge_x : x ≤ (X : ℝ) := Nat.le_ceil x
  have hX_lt : (X : ℝ) < x + 1 := Nat.ceil_lt_add_one hx_pos.le
  have hX_le_2x : (X : ℝ) ≤ 2 * x := by linarith
  have hX_ge65536 : 65536 ≤ X := by
    have : (65536 : ℝ) ≤ (X : ℝ) := hx65.trans hX_ge_x
    exact_mod_cast this
  have hX_pos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hX_ge1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (by omega : 1 ≤ X)
  have hA_pos : 0 < A_cut := by dsimp [A_cut]; positivity
  have hlogx_div_x : Real.log x / x ≤ 32 * (X : ℝ) ^ (-(15 : ℝ) / 16) := by
    have hlog_le : Real.log x ≤ 16 * (X : ℝ) ^ ((1 : ℝ) / 16) := by
      have h1 := log_le_inv_eta_rpow (x := (X : ℝ)) (η := (1 : ℝ) / 16) hX_ge1 (by positivity)
      norm_num at h1
      exact (Real.log_le_log hx_pos hX_ge_x).trans h1
    have hinv_le : 1 / x ≤ 2 / (X : ℝ) := by
      rw [div_le_div_iff₀ hx_pos hX_pos]; linarith
    calc Real.log x / x = Real.log x * (1 / x) := by ring
      _ ≤ (16 * (X : ℝ) ^ ((1 : ℝ) / 16)) * (2 / (X : ℝ)) :=
          mul_le_mul hlog_le hinv_le (by positivity) (by positivity)
      _ = 32 * ((X : ℝ) ^ ((1 : ℝ) / 16) * (X : ℝ) ^ (-(1 : ℝ))) := by
          rw [Real.rpow_neg_one]; ring
      _ = 32 * (X : ℝ) ^ (-(15 : ℝ) / 16) := by
          rw [← Real.rpow_add hX_pos]; congr 2; norm_num
  have hMmax_le : (M_max : ℝ) ≤ A_cut * (X : ℝ) ^ ((9 : ℝ) / 16) := by
    have h1 : (M_max : ℝ) ≤ (32 / ε) * (X : ℝ) ^ ((9 : ℝ) / 16) + 1 := by
      dsimp [M_max]; push_cast
      linarith [Nat.floor_le (by positivity : 0 ≤ (32 / ε) * (X : ℝ) ^ ((9 : ℝ) / 16))]
    have hge1 : (1 : ℝ) ≤ (X : ℝ) ^ ((9 : ℝ) / 16) := Real.one_le_rpow hX_ge1 (by positivity)
    have hexpA : A_cut * (X : ℝ) ^ ((9 : ℝ) / 16) =
        (32 / ε) * (X : ℝ) ^ ((9 : ℝ) / 16) + (X : ℝ) ^ ((9 : ℝ) / 16) := by
      dsimp [A_cut]; ring
    linarith
  have hR2_card : (R2.card : ℝ) ≤ A_cut * (X : ℝ) ^ ((9 : ℝ) / 16) := by
    have hsub : R2 ⊆ Finset.Icc 1 M_max := fun m hm =>
      Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1; omega,
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).2⟩
    have h1 : R2.card ≤ M_max := (Finset.card_le_card hsub).trans (by rw [Nat.card_Icc, Nat.add_sub_cancel])
    exact ((Nat.cast_le (α := ℝ)).mpr h1).trans hMmax_le
  have hNm_le2 : ∀ m ∈ R2, ((P_odd.filter (fun p => m < Erdos981.f' ε p)).card : ℝ) ≤
      (Cls / ε ^ 80) * ((X : ℝ) ^ ((1 : ℝ) / 80) +
        Real.pi * A_cut ^ ((1 : ℝ) / 4) * (X : ℝ) ^ ((9 : ℝ) / 64)) := by
    intro m hmR2
    have hmIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hmR2).1
    have hm_gt_M1 : M1 < m := Nat.lt_of_not_ge (Finset.mem_filter.mp hmR2).2
    have hm1 : 1 ≤ m := by omega
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hm_gt_X20 : (X : ℝ) ^ ((1 : ℝ) / 20) ≤ (m : ℝ) := by
      have h1 : (X : ℝ) ^ ((1 : ℝ) / 20) < (M1 : ℝ) + 1 := Nat.lt_floor_add_one _
      have h2 : (M1 : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hm_gt_M1
      linarith
    have hm_le_Mmax : (m : ℝ) ≤ A_cut * (X : ℝ) ^ ((9 : ℝ) / 16) :=
      ((Nat.cast_le (α := ℝ)).mpr hmIcc.2).trans hMmax_le
    have hmarkov : (ε * (m : ℝ)) ^ 80 * ((P_odd.filter (fun p => m < Erdos981.f' ε p)).card : ℝ) ≤
        ∑ p ∈ P_odd, (∑ n ∈ Finset.Icc 1 m, (jacobiSym (n : ℤ) p : ℝ)) ^ 80 := by
      calc (ε * (m : ℝ)) ^ 80 * ((P_odd.filter (fun p => m < Erdos981.f' ε p)).card : ℝ)
          = ∑ _p ∈ P_odd.filter (fun p => m < Erdos981.f' ε p), (ε * (m : ℝ)) ^ 80 := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        _ ≤ ∑ p ∈ P_odd.filter (fun p => m < Erdos981.f' ε p),
              (∑ n ∈ Finset.Icc 1 m, (jacobiSym (n : ℤ) p : ℝ)) ^ 80 := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hp_odd := (Finset.mem_filter.mp hp).1
            have hmlt := (Finset.mem_filter.mp hp).2
            have hp_pr := (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hp_odd).1).2
            have hp2 := (Finset.mem_filter.mp hp_odd).2
            exact pow_le_pow_left₀ (by positivity) (lt_f'_imp_ge_sum hε hp_pr hp2 hmlt) 80
        _ ≤ ∑ p ∈ P_odd, (∑ n ∈ Finset.Icc 1 m, (jacobiSym (n : ℤ) p : ℝ)) ^ 80 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun _ _ _ => Even.pow_nonneg (by decide) _)
    have hmom := hls80 X m (by omega) hm1
    have hden_pos : 0 < (ε * (m : ℝ)) ^ 80 := by positivity
    have hdiv := (le_div_iff₀' hden_pos).mpr (hmarkov.trans hmom)
    have hrew : Cls * ((X : ℝ) ^ 2 + Real.pi * (m : ℝ) ^ 40) * (m : ℝ) ^ 40 * (m : ℝ) ^ ((1 : ℝ) / 4) /
          (ε * (m : ℝ)) ^ 80 =
        (Cls / ε ^ 80) * ((X : ℝ) ^ 2 / (m : ℝ) ^ ((159 : ℝ) / 4) + Real.pi * (m : ℝ) ^ ((1 : ℝ) / 4)) := by
      have hm159 : (m : ℝ) ^ ((159 : ℝ) / 4) * (m : ℝ) ^ ((1 : ℝ) / 4) = (m : ℝ) ^ 40 := by
        rw [← Real.rpow_add hm_pos, show (159 : ℝ) / 4 + 1 / 4 = (40 : ℕ) by norm_num, Real.rpow_natCast]
      have hm159_pos : 0 < (m : ℝ) ^ ((159 : ℝ) / 4) := Real.rpow_pos_of_pos hm_pos _
      rw [mul_pow]
      field_simp [hε.ne', hm_pos.ne', hm159_pos.ne']
      calc ((X : ℝ) ^ 2 + Real.pi * (m : ℝ) ^ 40) * (m : ℝ) ^ ((1 : ℝ) / 4) * (m : ℝ) ^ ((159 : ℝ) / 4)
          = ((X : ℝ) ^ 2 + Real.pi * (m : ℝ) ^ 40) * ((m : ℝ) ^ ((159 : ℝ) / 4) * (m : ℝ) ^ ((1 : ℝ) / 4)) := by ring
        _ = ((X : ℝ) ^ 2 + Real.pi * (m : ℝ) ^ 40) * (m : ℝ) ^ 40 := by rw [hm159]
        _ = (m : ℝ) ^ 40 * ((X : ℝ) ^ 2 + Real.pi * (m : ℝ) ^ ((1 : ℝ) / 4) * (m : ℝ) ^ ((159 : ℝ) / 4)) := by
            rw [mul_assoc Real.pi, mul_comm ((m : ℝ) ^ ((1 : ℝ) / 4)), hm159]; ring
    have ht1 : (X : ℝ) ^ 2 / (m : ℝ) ^ ((159 : ℝ) / 4) ≤ (X : ℝ) ^ ((1 : ℝ) / 80) := by
      have hden_ge : (X : ℝ) ^ ((159 : ℝ) / 80) ≤ (m : ℝ) ^ ((159 : ℝ) / 4) := by
        calc (X : ℝ) ^ ((159 : ℝ) / 80)
            = ((X : ℝ) ^ ((1 : ℝ) / 20)) ^ ((159 : ℝ) / 4) := by
              rw [← Real.rpow_mul hX_pos.le]; congr 1; norm_num
          _ ≤ (m : ℝ) ^ ((159 : ℝ) / 4) :=
              Real.rpow_le_rpow (by positivity) hm_gt_X20 (by positivity)
      have hden_pos1 : 0 < (X : ℝ) ^ ((159 : ℝ) / 80) := Real.rpow_pos_of_pos hX_pos _
      calc (X : ℝ) ^ 2 / (m : ℝ) ^ ((159 : ℝ) / 4)
          ≤ (X : ℝ) ^ 2 / (X : ℝ) ^ ((159 : ℝ) / 80) :=
            div_le_div_of_nonneg_left (sq_nonneg _) hden_pos1 hden_ge
        _ = (X : ℝ) ^ ((1 : ℝ) / 80) := by
            rw [← Real.rpow_two (X : ℝ), ← Real.rpow_sub hX_pos]; congr 1; norm_num
    have ht2 : (m : ℝ) ^ ((1 : ℝ) / 4) ≤ A_cut ^ ((1 : ℝ) / 4) * (X : ℝ) ^ ((9 : ℝ) / 64) := by
      calc (m : ℝ) ^ ((1 : ℝ) / 4)
          ≤ (A_cut * (X : ℝ) ^ ((9 : ℝ) / 16)) ^ ((1 : ℝ) / 4) :=
            Real.rpow_le_rpow hm_pos.le hm_le_Mmax (by positivity)
        _ = A_cut ^ ((1 : ℝ) / 4) * ((X : ℝ) ^ ((9 : ℝ) / 16)) ^ ((1 : ℝ) / 4) :=
            Real.mul_rpow hA_pos.le (by positivity)
        _ = A_cut ^ ((1 : ℝ) / 4) * (X : ℝ) ^ ((9 : ℝ) / 64) := by
            rw [← Real.rpow_mul hX_pos.le]; congr 2; norm_num
    rw [hrew] at hdiv
    refine hdiv.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact add_le_add ht1 (by
      calc Real.pi * (m : ℝ) ^ ((1 : ℝ) / 4)
          ≤ Real.pi * (A_cut ^ ((1 : ℝ) / 4) * (X : ℝ) ^ ((9 : ℝ) / 64)) :=
            mul_le_mul_of_nonneg_left ht2 Real.pi_pos.le
        _ = Real.pi * A_cut ^ ((1 : ℝ) / 4) * (X : ℝ) ^ ((9 : ℝ) / 64) := by ring)
  have hR2_sum : ∑ m ∈ R2, ((P_odd.filter (fun p => m < Erdos981.f' ε p)).card : ℝ) ≤
      (A_cut * (X : ℝ) ^ ((9 : ℝ) / 16)) * ((Cls / ε ^ 80) * ((X : ℝ) ^ ((1 : ℝ) / 80) +
        Real.pi * A_cut ^ ((1 : ℝ) / 4) * (X : ℝ) ^ ((9 : ℝ) / 64))) := by
    calc ∑ m ∈ R2, ((P_odd.filter (fun p => m < Erdos981.f' ε p)).card : ℝ)
        ≤ ∑ _m ∈ R2, (Cls / ε ^ 80) * ((X : ℝ) ^ ((1 : ℝ) / 80) +
            Real.pi * A_cut ^ ((1 : ℝ) / 4) * (X : ℝ) ^ ((9 : ℝ) / 64)) := Finset.sum_le_sum hNm_le2
      _ = (R2.card : ℝ) * ((Cls / ε ^ 80) * ((X : ℝ) ^ ((1 : ℝ) / 80) +
            Real.pi * A_cut ^ ((1 : ℝ) / 4) * (X : ℝ) ^ ((9 : ℝ) / 64))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (A_cut * (X : ℝ) ^ ((9 : ℝ) / 16)) * ((Cls / ε ^ 80) * ((X : ℝ) ^ ((1 : ℝ) / 80) +
            Real.pi * A_cut ^ ((1 : ℝ) / 4) * (X : ℝ) ^ ((9 : ℝ) / 64))) :=
          mul_le_mul_of_nonneg_right hR2_card (by positivity [Real.pi_pos])
  have hexp4 : (X : ℝ) ^ ((9 : ℝ) / 16) * (X : ℝ) ^ ((1 : ℝ) / 80) * (X : ℝ) ^ (-(15 : ℝ) / 16) ≤
      (X : ℝ) ^ (-(1 : ℝ) / 8) := by
    rw [← Real.rpow_add hX_pos, ← Real.rpow_add hX_pos]
    exact Real.rpow_le_rpow_of_exponent_le hX_ge1 (by norm_num)
  have hexp5 : (X : ℝ) ^ ((9 : ℝ) / 16) * (X : ℝ) ^ ((9 : ℝ) / 64) * (X : ℝ) ^ (-(15 : ℝ) / 16) ≤
      (X : ℝ) ^ (-(1 : ℝ) / 8) := by
    rw [← Real.rpow_add hX_pos, ← Real.rpow_add hX_pos]
    exact Real.rpow_le_rpow_of_exponent_le hX_ge1 (by norm_num)
  have hA54 : A_cut * A_cut ^ ((1 : ℝ) / 4) = A_cut ^ ((5 : ℝ) / 4) := by
    calc A_cut * A_cut ^ ((1 : ℝ) / 4) = A_cut ^ (1 : ℝ) * A_cut ^ ((1 : ℝ) / 4) := by rw [Real.rpow_one]
      _ = A_cut ^ ((5 : ℝ) / 4) := by rw [← Real.rpow_add hA_pos]; congr 1; norm_num
  have hlogx_nn : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  calc (∑ m ∈ R2, ((P_odd.filter (fun p => m < Erdos981.f' ε p)).card : ℝ)) * Real.log x / x
      = (∑ m ∈ R2, ((P_odd.filter (fun p => m < Erdos981.f' ε p)).card : ℝ)) * (Real.log x / x) := by ring
    _ ≤ (A_cut * (X : ℝ) ^ ((9 : ℝ) / 16)) * ((Cls / ε ^ 80) * ((X : ℝ) ^ ((1 : ℝ) / 80) +
          Real.pi * A_cut ^ ((1 : ℝ) / 4) * (X : ℝ) ^ ((9 : ℝ) / 64))) *
          (32 * (X : ℝ) ^ (-(15 : ℝ) / 16)) :=
        mul_le_mul hR2_sum hlogx_div_x (by positivity) (by positivity [Real.pi_pos])
    _ = (32 * Cls * A_cut / ε ^ 80) * ((X : ℝ) ^ ((9 : ℝ) / 16) * (X : ℝ) ^ ((1 : ℝ) / 80) * (X : ℝ) ^ (-(15 : ℝ) / 16)) +
        (32 * Cls * Real.pi * A_cut ^ ((5 : ℝ) / 4) / ε ^ 80) *
          ((X : ℝ) ^ ((9 : ℝ) / 16) * (X : ℝ) ^ ((9 : ℝ) / 64) * (X : ℝ) ^ (-(15 : ℝ) / 16)) := by
        rw [← hA54]; ring
    _ ≤ (32 * Cls * A_cut / ε ^ 80) * (X : ℝ) ^ (-(1 : ℝ) / 8) +
        (32 * Cls * Real.pi * A_cut ^ ((5 : ℝ) / 4) / ε ^ 80) * (X : ℝ) ^ (-(1 : ℝ) / 8) :=
        add_le_add (mul_le_mul_of_nonneg_left hexp4 (by positivity))
          (mul_le_mul_of_nonneg_left hexp5 (by positivity [Real.pi_pos]))
    _ = (32 * Cls * A_cut / ε ^ 80 + 32 * Cls * Real.pi * A_cut ^ ((5 : ℝ) / 4) / ε ^ 80) *
          (X : ℝ) ^ (-(1 : ℝ) / 8) := by ring

lemma H2_proof : OMA.R_Erdos981_erdos_981_variants_first_time_R1.H2 := by
  intro ε hε δ hδ
  obtain ⟨Csq, hCsq_pos, hselberg⟩ := selberg_fourth_moment_bound
  obtain ⟨Cls, hCls_pos, hls80⟩ := large_sieve_80th_moment
  have hmain_coef_pos : 0 < 32 * Csq / ε ^ 4 := by positivity
  obtain ⟨B₀, hB₀_ge1, htail⟩ := tail_pseries_small (η := (δ / 2) / (32 * Csq / ε ^ 4)) (by positivity)
  have hsum_all : Summable (fun m : ℕ => (m : ℝ) ^ (-(5 : ℝ) / 4)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  let L_p : ℝ := ∑' m : ℕ, (m : ℝ) ^ (-(5 : ℝ) / 4)
  have hLp_nn : 0 ≤ L_p := tsum_nonneg fun m => Real.rpow_nonneg (Nat.cast_nonneg m) _
  let B : ℕ := max (max B₀ 2) (Erdos981.f' ε 2)
  have hB_pos : 0 < B := by dsimp [B]; omega
  have hB_ge_B0 : B₀ ≤ B := (le_max_left B₀ 2).trans (le_max_left _ _)
  have hB_ge_f2 : Erdos981.f' ε 2 ≤ B := le_max_right _ _
  refine ⟨B, hB_pos, ?_⟩
  let A_cut : ℝ := 32 / ε + 1
  have hA_pos : 0 < A_cut := by positivity
  let C_err1 : ℝ := 32 / ε ^ 4
  let C_err2 : ℝ := 32 * Csq * L_p / ε ^ 4
  let C_err3 : ℝ := 256 / ε ^ 4
  let C_err4 : ℝ := 32 * Cls * A_cut / ε ^ 80
  let C_err5 : ℝ := 32 * Cls * Real.pi * A_cut ^ ((5 : ℝ) / 4) / ε ^ 80
  let C_err : ℝ := C_err1 + C_err2 + C_err3 + C_err4 + C_err5
  have hCerr_pos : 0 < C_err := by
    have h1 : 0 < C_err1 := by positivity
    have h2 : 0 ≤ C_err2 := by positivity
    have h3 : 0 < C_err3 := by positivity
    have h4 : 0 < C_err4 := by positivity
    have h5 : 0 < C_err5 := by positivity [Real.pi_pos]
    linarith
  let X₀ : ℝ := max 65536 (((2 * C_err / δ + 1) : ℝ) ^ 8)
  filter_upwards [eventually_ge_atTop X₀] with x hx
  have hx_ge65536 : (65536 : ℝ) ≤ x := (le_max_left _ _).trans hx
  have hx_ge_err : ((2 * C_err / δ + 1) : ℝ) ^ 8 ≤ x := (le_max_right _ _).trans hx
  have hx_pos : 0 < x := by linarith
  let X : ℕ := ⌈x⌉₊
  have hX_ge_x : x ≤ (X : ℝ) := Nat.le_ceil x
  have hX_ge65536 : 65536 ≤ X := by
    have : (65536 : ℝ) ≤ (X : ℝ) := hx_ge65536.trans hX_ge_x
    exact_mod_cast this
  have hX_pos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  let P_odd := (Nat.primesBelow X).filter (· ≠ 2)
  have hdist_eq :
      dist
        ((↑(∑ p : Nat.primesBelow X, Erdos981.f' ε p) : ℝ) * Real.log x / x)
        ((↑(∑ p : Nat.primesBelow X, min B (Erdos981.f' ε p)) : ℝ) * Real.log x / x) =
      ((∑ p ∈ P_odd, (Erdos981.f' ε p - min B (Erdos981.f' ε p)) : ℕ) : ℝ) * Real.log x / x := by
    have hs1 : ∑ p : Nat.primesBelow X, Erdos981.f' ε p =
        ∑ p ∈ Nat.primesBelow X, Erdos981.f' ε p :=
      Finset.sum_coe_sort (Nat.primesBelow X) (fun p => Erdos981.f' ε p)
    have hs2 : ∑ p : Nat.primesBelow X, min B (Erdos981.f' ε p) =
        ∑ p ∈ Nat.primesBelow X, min B (Erdos981.f' ε p) :=
      Finset.sum_coe_sort (Nat.primesBelow X) (fun p => min B (Erdos981.f' ε p))
    rw [hs1, hs2, Real.dist_eq]
    have hle_sum : ∑ p ∈ Nat.primesBelow X, min B (Erdos981.f' ε p) ≤
        ∑ p ∈ Nat.primesBelow X, Erdos981.f' ε p :=
      Finset.sum_le_sum fun p _ => min_le_right _ _
    have hdiff_nat : ∑ p ∈ Nat.primesBelow X, Erdos981.f' ε p -
          ∑ p ∈ Nat.primesBelow X, min B (Erdos981.f' ε p) =
        ∑ p ∈ Nat.primesBelow X, (Erdos981.f' ε p - min B (Erdos981.f' ε p)) := by
      have hadd : ∑ p ∈ Nat.primesBelow X, min B (Erdos981.f' ε p) +
            ∑ p ∈ Nat.primesBelow X, (Erdos981.f' ε p - min B (Erdos981.f' ε p)) =
          ∑ p ∈ Nat.primesBelow X, Erdos981.f' ε p := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun p _ => Nat.add_sub_of_le (min_le_right _ _)
      omega
    have hdrop2 : ∑ p ∈ Nat.primesBelow X, (Erdos981.f' ε p - min B (Erdos981.f' ε p)) =
        ∑ p ∈ P_odd, (Erdos981.f' ε p - min B (Erdos981.f' ε p)) := by
      have hsplit := (Finset.sum_filter_add_sum_filter_not (Nat.primesBelow X) (· ≠ 2)
        (fun p => Erdos981.f' ε p - min B (Erdos981.f' ε p))).symm
      rw [hsplit]
      have h2zero : ∑ p ∈ (Nat.primesBelow X).filter (fun p => ¬ p ≠ 2),
          (Erdos981.f' ε p - min B (Erdos981.f' ε p)) = 0 := by
        refine Finset.sum_eq_zero fun p hp => ?_
        have hp2 : p = 2 := by have := (Finset.mem_filter.mp hp).2; omega
        subst hp2
        rw [min_eq_right hB_ge_f2, Nat.sub_self]
      rw [h2zero, add_zero]
    have hdiffR : ((∑ p ∈ Nat.primesBelow X, Erdos981.f' ε p : ℕ) : ℝ) * Real.log x / x -
          ((∑ p ∈ Nat.primesBelow X, min B (Erdos981.f' ε p) : ℕ) : ℝ) * Real.log x / x =
        ((∑ p ∈ P_odd, (Erdos981.f' ε p - min B (Erdos981.f' ε p)) : ℕ) : ℝ) * Real.log x / x := by
      have hsubR : ((∑ p ∈ Nat.primesBelow X, Erdos981.f' ε p : ℕ) : ℝ) -
            ((∑ p ∈ Nat.primesBelow X, min B (Erdos981.f' ε p) : ℕ) : ℝ) =
          ((∑ p ∈ P_odd, (Erdos981.f' ε p - min B (Erdos981.f' ε p)) : ℕ) : ℝ) := by
        rw [← hdrop2, ← hdiff_nat, Nat.cast_sub hle_sum]
      calc ((∑ p ∈ Nat.primesBelow X, Erdos981.f' ε p : ℕ) : ℝ) * Real.log x / x -
              ((∑ p ∈ Nat.primesBelow X, min B (Erdos981.f' ε p) : ℕ) : ℝ) * Real.log x / x
          = (((∑ p ∈ Nat.primesBelow X, Erdos981.f' ε p : ℕ) : ℝ) -
              ((∑ p ∈ Nat.primesBelow X, min B (Erdos981.f' ε p) : ℕ) : ℝ)) * Real.log x / x := by ring
        _ = ((∑ p ∈ P_odd, (Erdos981.f' ε p - min B (Erdos981.f' ε p)) : ℕ) : ℝ) * Real.log x / x := by
            rw [hsubR]
    rw [hdiffR, abs_of_nonneg (by positivity)]
  rw [hdist_eq]
  let M_max : ℕ := Nat.floor ((32 / ε) * (X : ℝ) ^ ((9 : ℝ) / 16)) + 1
  have hf'_le : ∀ p ∈ P_odd, Erdos981.f' ε p ≤ M_max := fun p hp => by
    have hp_below := (Finset.mem_filter.mp hp).1
    have hp2 := (Finset.mem_filter.mp hp).2
    exact f'_le_cutoff hε (by omega) (Nat.mem_primesBelow.mp hp_below).2 hp2 (Nat.mem_primesBelow.mp hp_below).1
  have hlc : ((∑ p ∈ P_odd, (Erdos981.f' ε p - min B (Erdos981.f' ε p)) : ℕ) : ℝ) =
      ∑ m ∈ Finset.Icc B M_max, ((P_odd.filter (fun p => m < Erdos981.f' ε p)).card : ℝ) := by
    rw [layer_cake_nat P_odd (Erdos981.f' ε) B M_max hf'_le, Nat.cast_sum]
  rw [hlc]
  let M1 : ℕ := Nat.floor ((X : ℝ) ^ ((1 : ℝ) / 20))
  let R1 := (Finset.Icc B M_max).filter (· ≤ M1)
  let R2 := (Finset.Icc B M_max).filter (fun m => ¬ m ≤ M1)
  have hsplit_R : ∑ m ∈ Finset.Icc B M_max, ((P_odd.filter (fun p => m < Erdos981.f' ε p)).card : ℝ) =
      (∑ m ∈ R1, ((P_odd.filter (fun p => m < Erdos981.f' ε p)).card : ℝ)) +
      (∑ m ∈ R2, ((P_odd.filter (fun p => m < Erdos981.f' ε p)).card : ℝ)) :=
    (Finset.sum_filter_add_sum_filter_not (Finset.Icc B M_max) (· ≤ M1) _).symm
  have hR1 := range1_bound (M_max := M_max) hε hCsq_pos hselberg (fun M => htail B M hB_ge_B0)
    hsum_all rfl (by omega) hx_ge65536
  have hR2 := range2_bound hε hCls_pos hls80 (by omega : 1 ≤ B) hx_ge65536
  have herr_small : C_err * (X : ℝ) ^ (-(1 : ℝ) / 8) < δ / 2 := by
    have hX18_gt : 2 * C_err / δ < (X : ℝ) ^ ((1 : ℝ) / 8) := by
      have h1 : 2 * C_err / δ + 1 ≤ (X : ℝ) ^ ((1 : ℝ) / 8) := by
        have hpow : (((2 * C_err / δ + 1) : ℝ) ^ 8) ^ ((1 : ℝ) / 8) = 2 * C_err / δ + 1 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
        rw [← hpow]
        exact Real.rpow_le_rpow (by positivity) (hx_ge_err.trans hX_ge_x) (by positivity)
      linarith
    have hpos8 : 0 < (X : ℝ) ^ ((1 : ℝ) / 8) := Real.rpow_pos_of_pos hX_pos _
    have hinv : (X : ℝ) ^ (-(1 : ℝ) / 8) = 1 / (X : ℝ) ^ ((1 : ℝ) / 8) := by
      rw [show -(1 : ℝ) / 8 = -((1 : ℝ) / 8) by ring, Real.rpow_neg hX_pos.le,
        one_div ((X : ℝ) ^ ((1 : ℝ) / 8))]
    rw [hinv, mul_one_div, div_lt_iff₀ hpos8]
    have hmul := (div_lt_iff₀ hδ).mp hX18_gt
    linarith
  have hcomb : (∑ m ∈ Finset.Icc B M_max, ((P_odd.filter (fun p => m < Erdos981.f' ε p)).card : ℝ)) *
        Real.log x / x =
      (∑ m ∈ R1, ((P_odd.filter (fun p => m < Erdos981.f' ε p)).card : ℝ)) * Real.log x / x +
      (∑ m ∈ R2, ((P_odd.filter (fun p => m < Erdos981.f' ε p)).card : ℝ)) * Real.log x / x := by
    rw [hsplit_R]; ring
  rw [hcomb]
  have hR1' : (∑ m ∈ R1, ((P_odd.filter (fun p => m < Erdos981.f' ε p)).card : ℝ)) * Real.log x / x ≤
      δ / 2 + (C_err1 + C_err2 + C_err3) * (X : ℝ) ^ (-(1 : ℝ) / 8) := hR1
  have hR2' : (∑ m ∈ R2, ((P_odd.filter (fun p => m < Erdos981.f' ε p)).card : ℝ)) * Real.log x / x ≤
      (C_err4 + C_err5) * (X : ℝ) ^ (-(1 : ℝ) / 8) := hR2
  have hsum_err : (C_err1 + C_err2 + C_err3) * (X : ℝ) ^ (-(1 : ℝ) / 8) +
      (C_err4 + C_err5) * (X : ℝ) ^ (-(1 : ℝ) / 8) = C_err * (X : ℝ) ^ (-(1 : ℝ) / 8) := by
    dsimp [C_err]; ring
  linarith [hR1', hR2', herr_small, hsum_err]

end Erdos981H2

theorem OMA.assembled_step_2 : OMA.R_Erdos981_erdos_981_variants_first_time_R1.H2 :=
  Erdos981H2.H2_proof

end


-- Exact parent; no new mathematical assumption is introduced.
theorem OMA.solution : type_of% @Erdos981.erdos_981.variants.first_time := by
  exact OMA.R_Erdos981_erdos_981_variants_first_time_R1.main OMA.assembled_step_1 OMA.assembled_step_2
