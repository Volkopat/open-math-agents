import FormalConjectures.ErdosProblems.«977»
import Mathlib

/-!
Lai's lower bound for the largest prime divisor of n! + 1, arXiv:2103.14894.
Based on the reduction and prime interval estimate by @marcusbuffett
(PRs #5887 and #6347) and the local valuation estimate by @koolkao (PR #11435).
-/

section

/-! Li Lai, On the largest prime divisor of n! + 1, arXiv:2103.14894.
Use a multiplicative interval [N,(1+d)N]. Its factorials contribute
at least (1-o(1)) N log N per integer. If every largest prime factor
were small, all of that weight would be carried by primes between N and
λ(1+d)N. Applying Lai's local valuation bound on this same interval
and letting d tend to zero recovers 1+9 log 2. -/
namespace OMA.R_Erdos977_erdos_977_variants_lai_R1

open Finset Filter Real
open scoped Classical Topology

/-- The upper half of the prime number theorem on fixed proportional intervals. -/
def H1 : Prop := ∀ b : ℝ, 1<b → ∀ δ : ℝ, 0<δ → ∀ᶠ N : ℕ in atTop,
  (((Ioc N ⌊b*N⌋₊).filter Nat.Prime).card:ℝ)*log N ≤ (b-1+δ)*N

/-- Lai's bound on the sum of the p-adic orders, on a fixed proportional interval.
This is the local estimate obtained by summing Lemma 2.7 over geometric layers. -/
def H2 : Prop := ∀ d : ℝ, 0<d → d<1 → ∀ η : ℝ, 0<η → ∀ᶠ N : ℕ in atTop,
  let T := Icc N ⌊(1+d)*N⌋₊
  ∀ p : ℕ, p.Prime → N<p →
    (∑ n ∈ T, ((n.factorial+1).factorization p : ℝ)*log p) ≤
      (1/(9*log 2)+η)*T.card*(log N)^2

lemma primeDecomposition {m : ℕ} (hn : m ≠ 0) (P : Finset ℕ) (sub : m.primeFactors ⊆ P) :
    log m = ∑ p ∈ P,(m.factorization p:ℝ)*log p := by
  have eq := congrArg (fun n : ℕ => (n:ℝ)) (Nat.prod_primeFactors_pow_factorization hn)
  push_cast at eq
  calc
    log m = log (∏ p ∈ m.primeFactors,(p:ℝ)^m.factorization p) := congrArg log eq
    _ = ∑ p ∈ m.primeFactors,(m.factorization p:ℝ)*log p := by
      rw [Real.log_prod]
      · simp only [log_pow]
      · intro p hp
        exact pow_ne_zero _ (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)
    _ = _ := sum_subset sub fun p _ hp => by
      have h : p ∉ m.factorization.support := by simpa using hp
      simp [Finsupp.notMem_support_iff.mp h]

lemma factorialMass (δ : ℝ) (hd : 0<δ) :
    ∀ᶠ N : ℕ in atTop, ∀ n ≥ N,
      (1-δ)*N*log N ≤ log (n.factorial+1:ℕ) := by
  have grow := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop (1/δ)
  filter_upwards [grow,eventually_ge_atTop 2] with N hlog hN
  intro n hn
  have h1 : N ≠ 0 := by omega
  have st := Stirling.le_log_factorial_stirling h1
  have l0 : 0 ≤ log (2*π) := log_nonneg (by linarith [Real.pi_gt_three])
  have hδ : 1 ≤ δ*log N := by
    have := (div_le_iff₀ hd).mp (show 1/δ ≤ log N from hlog)
    linarith
  have inc : (N.factorial:ℝ) ≤ (n.factorial+1:ℕ) := by
    exact_mod_cast (Nat.factorial_le hn).trans (Nat.le_succ _)
  have incr := log_le_log (by exact_mod_cast Nat.factorial_pos N) inc
  nlinarith only [incr,st,l0,Real.log_natCast_nonneg N,
    mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg (α:=ℝ) N)]

lemma slack (C L : ℝ) (hL : 0<L) (hC : C<1+L) :
    ∃ a : ℝ, 1<a ∧ C<a ∧ ∃ d : ℝ, 0<d ∧ d<1 ∧
      (1/L+d)*(a*(1+d)-1+d)<1-d := by
  let a := (max C 1 + (1+L))/2
  have hm : max C 1 < 1+L := max_lt hC (by linarith)
  have av : max C 1<a := by dsimp [a];linarith
  have al : a<1+L := by dsimp [a];linarith
  refine ⟨a,(le_max_right ..).trans_lt av,(le_max_left ..).trans_lt av,?_⟩
  have init : (1/L+0)*(a*(1+0)-1+0)<1-0 := by
    simp only [add_zero,sub_zero,one_mul,mul_one,one_div]
    rw [←div_eq_inv_mul,div_lt_iff₀ hL]
    linarith
  have u : Continuous (fun z : ℝ => (1/L+z)*(a*(1+z)-1+z)) := by fun_prop
  have v : Continuous (fun z : ℝ => 1-z) := by fun_prop
  have ev : ∀ᶠ z : ℝ in 𝓝 0,(1/L+z)*(a*(1+z)-1+z)<1-z := u.continuousAt.eventually_lt v.continuousAt init
  obtain ⟨e,he,ball⟩ := Metric.eventually_nhds_iff.mp ev
  let z := min (e/2) (1/2)
  have z0 : 0<z := lt_min (by positivity) (by norm_num)
  refine ⟨z,z0,lt_of_le_of_lt (min_le_right ..) (by norm_num),ball ?_⟩
  rw [Real.dist_eq,sub_zero,abs_of_pos z0]
  exact (min_le_left ..).trans_lt (by linarith)

theorem main : H1 → H2 → type_of% @Erdos977.erdos_977.variants.lai := by
  classical
  intro count valu C hC
  let L := 9*log 2
  have hL : 0<L := by dsimp [L];positivity
  obtain ⟨a,ha,hCa,d,hd,hd1,hslack⟩ := slack C L hL hC
  let b := a*(1+d)
  have hb : 1<b := by dsimp [b];nlinarith only [ha,hd,mul_pos (lt_trans zero_lt_one ha) hd]
  by_contra h
  have bad := not_frequently.mp h
  obtain ⟨M,hM⟩ := eventually_atTop.mp bad
  have ev := (count b hb d hd).and ((valu d hd hd1 d hd).and (factorialMass d hd))
  obtain ⟨N,⟨hcount,hval,hfac⟩,hN⟩ := (ev.and (eventually_ge_atTop (M+2))).exists
  let T := Icc N ⌊(1+d)*N⌋₊
  let P := (Ioc N ⌊b*N⌋₊).filter Nat.Prime
  have hnp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have logp : 0<log (N:ℝ) := log_pos (by exact_mod_cast (show 1<N by omega))
  have Tpos : (0:ℝ)<T.card := by
    exact_mod_cast (card_pos.mpr ⟨N,mem_Icc.mpr ⟨le_rfl,Nat.le_floor (by nlinarith [mul_pos hd hnp])⟩⟩ : 0<T.card)
  have hsup (n : ℕ) (hn : n ∈ T) : (n.factorial+1).primeFactors ⊆ P := by
    obtain ⟨hnN,hn'⟩ := mem_Icc.mp hn
    intro p hp
    obtain ⟨pr,dvd,nz⟩ := Nat.mem_primeFactors.mp hp
    have nlt : n<p := by
      by_contra! h
      have one := (Nat.dvd_add_right (Nat.dvd_factorial pr.pos h)).mp dvd
      exact pr.not_dvd_one one
    have maxb := not_lt.mp (hM n (by omega))
    have lp := Nat.le_maxPrimeFac nz pr dvd
    have nu : (n:ℝ) ≤ (1+d)*N := (Nat.le_floor_iff (by positivity)).mp hn'
    have up : (p:ℝ) ≤ b*N := calc
      _ ≤ (Nat.maxPrimeFac (n.factorial+1):ℝ) := by exact_mod_cast lp
      _ ≤ C*n := maxb
      _ ≤ a*n := mul_le_mul_of_nonneg_right hCa.le (Nat.cast_nonneg _)
      _ ≤ b*N := by dsimp [b];rw [mul_assoc];exact mul_le_mul_of_nonneg_left nu (by linarith)
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hnN.trans_lt nlt,Nat.le_floor up⟩,pr⟩
  let F (n p : ℕ) : ℝ := ((n.factorial+1).factorization p:ℝ)*log p
  have lower : (T.card:ℝ)*((1-d)*N*log N) ≤ ∑ p ∈ P,∑ n ∈ T,F n p := by
    rw [sum_comm]
    calc
      _ = ∑ n ∈ T,(1-d)*N*log N := by simp
      _ ≤ _ := sum_le_sum fun n hn => (hfac n (mem_Icc.mp hn).1).trans
        (primeDecomposition (by omega) P (hsup n hn)).le
  have upper : (∑ p ∈ P,∑ n ∈ T,F n p) ≤
      P.card*((1/L+d)*T.card*(log N)^2) := by
    calc
      _ ≤ ∑ p ∈ P, (1/L+d)*T.card*(log N)^2 := sum_le_sum fun p hp =>
        hval p (mem_filter.mp hp).2 (mem_Ioc.mp (mem_filter.mp hp).1).1
      _ = _ := by simp
  have coef : 0 ≤ (1/L+d)*(T.card:ℝ)*log N := by positivity
  have cap := mul_le_mul_of_nonneg_right (show (P.card:ℝ)*log N ≤ (b-1+d)*N from hcount) coef
  have scale : 0<(T.card:ℝ)*N*log N := by positivity
  have strict := mul_lt_mul_of_pos_right hslack scale
  change (1/L+d)*(b-1+d)*_ < _ at strict
  linarith only [lower,upper,cap,strict]

end OMA.R_Erdos977_erdos_977_variants_lai_R1

end


section

/- The PNT portion is adapted from @marcusbuffett in the merged Erdős 950 proof. The prime interval bound uses weighted subtraction. -/

-- Credit: @marcusbuffett
-- The Chebyshev asymptotic is taken from the checked Erdős 30 prime-interval proof.
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


-- to replace existing `isLittleO_const_id_atTop`


-- to replace existing `isLittleO_const_id_atBot`


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
open Finset Filter Real Asymptotics
open scoped Topology Classical

private theorem primeIntervalUpper
    (hθ : (fun x : ℝ => Chebyshev.theta x) ~[atTop] (fun x : ℝ => x)) :
    ∀ b : ℝ, 1<b → ∀ δ : ℝ, 0<δ → ∀ᶠ N : ℕ in atTop,
      (((Ioc N ⌊b*N⌋₊).filter Nat.Prime).card:ℝ)*log N ≤ (b-1+δ)*N := by
  intro b hb δ hd
  have bp : 0<b := zero_lt_one.trans hb
  have lim := (isEquivalent_iff_tendsto_one ((eventually_gt_atTop (0:ℝ)).mono fun _ h => h.ne')).mp hθ
  have natlim := lim.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have binc := (tendsto_natCast_atTop_atTop (R:=ℝ)).const_mul_atTop bp
  have big := (lim.comp binc).mul_const b
  have diff := big.sub natlim
  rw [one_mul] at diff
  filter_upwards [diff.eventually (gt_mem_nhds (by linarith : b-1 < b-1+δ)),eventually_gt_atTop 0] with N h hN
  have np : (0:ℝ)<N := by exact_mod_cast hN
  have bn : 0 ≤ b*N := by positivity
  let U := Nat.primesLE ⌊b*N⌋₊
  let V := Nat.primesLE N
  have sub : V ⊆ U := fun p hp => Nat.mem_primesLE.mpr
    ⟨(Nat.mem_primesLE.mp hp).1.trans (Nat.le_floor (by nlinarith only [mul_lt_mul_of_pos_right hb np])),(Nat.mem_primesLE.mp hp).2⟩
  let P := (Ioc N ⌊b*N⌋₊).filter Nat.Prime
  have sdiff : P=U\V := by
    apply Finset.ext
    intro p
    rw [Finset.mem_sdiff]
    change (p ∈ (Ioc N ⌊b*N⌋₊).filter Nat.Prime) ↔
      p ∈ Nat.primesLE ⌊b*N⌋₊ ∧ p ∉ Nat.primesLE N
    rw [Finset.mem_filter,Finset.mem_Ioc,Nat.mem_primesLE,Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hl,hu⟩,pr⟩
      exact ⟨⟨hu,pr⟩,fun h => (not_le.mpr hl) h.1⟩
    · rintro ⟨⟨hu,pr⟩,hn⟩
      exact ⟨⟨lt_of_not_ge (fun h => hn ⟨h,pr⟩),hu⟩,pr⟩
  have mass : ∑ p ∈ P,log p = Chebyshev.theta (b*N)-Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE,Chebyshev.theta_eq_sum_primesLE_log,sdiff]
    exact eq_sub_of_add_eq (sum_sdiff sub)
  have bound : (P.card:ℝ)*log N ≤ ∑ p ∈ P,log p := by
    calc
      _ = ∑ p ∈ P, log N := by simp
      _ ≤ _ := sum_le_sum fun p hp => log_le_log np
        (by exact_mod_cast (mem_Ioc.mp (mem_filter.mp hp).1).1.le)
  change Chebyshev.theta (b*N)/(b*N)*b-Chebyshev.theta N/N < b-1+δ at h
  have eq : Chebyshev.theta (b*N)/(b*N)*b-Chebyshev.theta N/N =
      (Chebyshev.theta (b*N)-Chebyshev.theta N)/N := by field_simp
  rw [eq,div_lt_iff₀ np] at h
  exact bound.trans (mass.le.trans h.le)


theorem OMA.laiPrimeSum : OMA.R_Erdos977_erdos_977_variants_lai_R1.H1 := primeIntervalUpper chebyshev_asymptotic

end


section

-- Step Erdos977.erdos_977.variants.lai.R1.H2: hypothesis H2 of reduction Erdos977.erdos_977.variants.lai.R1
-- Credit: @koolkao

/-!
# Lai's local valuation bound for n! + 1 on a proportional interval

Original formalization (Lane C, claude-code for koolkao) of the argument of L. Lai,
On the largest prime divisor of n!+1, arXiv:2103.14894 (Lemmas 2.2, 2.4, 2.7 and Section 3),
specialised to f = 1, with all bounds on (log p) * ord_p(n!+1), so uniform in p > N.

* Luca-Shparlinski count: at most H^2 + (b-a)/H + 1 integers n in [a,b], b < p, have p | n!+1
  (a gap of length h between two of them is a root mod p of (X+1)...(X+h) - 1).
* Two blocks (u, u+h], (v, v+h'] with h <= h' whose four endpoints satisfy p^m | n!+1 and with
  distinct products give p^m | (B - A)/h!, so m log p <= h log(e x/h) + (h'-h) log x.
* Lai uses Heath-Brown's prime-gap moments only to make B - A nonzero. Here instead: equal products
  of blocks of lengths h < h' force h' - h <= 2 log2 x + 1 (2-adic valuations), so any
  2 log2 x + 2 gaps in one length bucket contain two with distinct products.
* Lemma 2.7: ranks t' in the top half of the top-t set; pairing and Jensen for y log(e x/y).
* Summing over blocks t -> (1/2 + 1/q) t by strong induction gives (|J|/(9 log(2q/(q+2)))) log^2 x.
-/


/-! Lane C, Erdős 977 (Lai) H2 — arithmetic of blocks of consecutive integers. -/

namespace LaneCLai
open Finset Real
open scoped Nat

/-- `A u h = (u+1)(u+2)…(u+h)`. -/
def A (u h : ℕ) : ℕ := ∏ i ∈ range h, (u + 1 + i)

lemma fact_mul_A (u h : ℕ) : u ! * A u h = (u + h)! := by
  induction h with
  | zero => simp [A]
  | succ h ih =>
    rw [A, prod_range_succ, ← A, ← mul_assoc, ih, show u + (h + 1) = (u + h) + 1 by ring,
      Nat.factorial_succ]
    ring

lemma A_eq (u h : ℕ) : A u h = h ! * (u + h).choose h := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (show h ≤ u + h by omega)
  rw [show u + h - h = u by omega] at h1
  have h2 := fact_mul_A u h
  have hu : 0 < u ! := Nat.factorial_pos u
  have : u ! * A u h = u ! * (h ! * (u + h).choose h) := by rw [h2, ← h1]; ring
  exact Nat.eq_of_mul_eq_mul_left hu this

lemma A_pos (u h : ℕ) : 0 < A u h := by
  unfold A; exact prod_pos (fun i _ => by omega)

lemma A_le {u h x : ℕ} (hx : u + h ≤ x) : A u h ≤ x ^ h := by
  unfold A
  calc ∏ i ∈ range h, (u + 1 + i) ≤ ∏ _i ∈ range h, x :=
        prod_le_prod' (fun i hi => by have := mem_range.mp hi; omega)
    _ = x ^ h := by simp

lemma two_le_A {u h : ℕ} (hu : 1 ≤ u) (hh : 1 ≤ h) : 2 ≤ A u h := by
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  unfold A
  rw [prod_range_succ']
  have : 1 ≤ ∏ i ∈ range k, (u + 1 + (i + 1)) := Nat.one_le_iff_ne_zero.mpr
    (prod_ne_zero_iff.mpr (fun i _ => by omega))
  nlinarith

lemma A_lt_A {u u' h : ℕ} (hh : 1 ≤ h) (hu : u < u') : A u h < A u' h := by
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  unfold A
  rw [prod_range_succ, prod_range_succ]
  have h1 : ∏ i ∈ range k, (u + 1 + i) ≤ ∏ i ∈ range k, (u' + 1 + i) :=
    prod_le_prod' (fun i _ => by omega)
  have h2 : 0 < ∏ i ∈ range k, (u + 1 + i) := prod_pos (fun i _ => by omega)
  calc (∏ i ∈ range k, (u + 1 + i)) * (u + 1 + k) < (∏ i ∈ range k, (u + 1 + i)) * (u' + 1 + k) :=
        Nat.mul_lt_mul_of_pos_left (by omega) h2
    _ ≤ _ := Nat.mul_le_mul_right _ h1

lemma A_inj {u u' h : ℕ} (hh : 1 ≤ h) (he : A u h = A u' h) : u = u' := by
  rcases lt_trichotomy u u' with h1 | h1 | h1
  · exact absurd he (A_lt_A hh h1).ne
  · exact h1
  · exact absurd he (A_lt_A hh h1).ne'

lemma coprime_of_dvd_fact_add_one {p m u : ℕ} (hp : p.Prime) (hm : 0 < m) (hu : p ^ m ∣ u ! + 1) :
    Nat.Coprime (p ^ m) (u !) := by
  apply Nat.Coprime.pow_left
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro h
  have h1 : p ∣ u ! + 1 := (dvd_pow_self p hm.ne').trans hu
  have : p ∣ 1 := (Nat.dvd_add_right h).mp h1
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

/-- Two factorials `≡ -1 (mod p^m)` give `(u+1)…v ≡ 1 (mod p^m)`. -/
lemma dvd_A_sub_one {p m u v : ℕ} (hp : p.Prime) (huv : u ≤ v) (hu : p ^ m ∣ u ! + 1)
    (hv : p ^ m ∣ v ! + 1) : p ^ m ∣ A u (v - u) - 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hcop := coprime_of_dvd_fact_add_one hp hm hu
  have hA := fact_mul_A u (v - u)
  rw [show u + (v - u) = v by omega] at hA
  have hApos := A_pos u (v - u)
  have hd := Nat.dvd_sub hv hu
  have : v ! + 1 - (u ! + 1) = u ! * (A u (v - u) - 1) := by
    rw [← hA, Nat.mul_sub, mul_one]; omega
  rw [this] at hd
  exact hcop.dvd_of_dvd_mul_left hd

/-- The two-block bound (Lai, Lemma 2.4, specialised to `f = 1`). -/
lemma two_block {p m u h u' h' x : ℕ} (hp : p.Prime) (hhp : h < p) (hh : h ≤ h')
    (h1 : p ^ m ∣ A u h - 1) (h2 : p ^ m ∣ A u' h' - 1) (hne : A u h ≠ A u' h')
    (hx1 : u + h ≤ x) (hx2 : u' + h' ≤ x) (hx : 1 ≤ x) : p ^ m * h ! ≤ x ^ h' := by
  have hc1 := A_eq u h
  have hc2 := A_eq u' h'
  obtain ⟨r, hr⟩ := Nat.factorial_dvd_factorial hh
  set c := (u + h).choose h
  set c' := r * (u' + h').choose h'
  have hA2 : A u' h' = h ! * c' := by rw [hc2, hr]; ring
  have hcop : Nat.Coprime (p ^ m) (h !) := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    exact fun hd => absurd ((Nat.Prime.dvd_factorial hp).mp hd) (by omega)
  have hpos1 := A_pos u h
  have hpos2 := A_pos u' h'
  have hcc : c ≠ c' := by
    intro hcc; apply hne; rw [hc1, hA2, hcc]
  rcases lt_or_gt_of_ne hcc with hlt | hlt
  · have hd := Nat.dvd_sub h2 h1
    have : A u' h' - 1 - (A u h - 1) = h ! * (c' - c) := by
      rw [hA2, hc1, Nat.mul_sub]; have := Nat.mul_le_mul_left (h !) hlt.le; omega
    rw [this] at hd
    have hd' := hcop.dvd_of_dvd_mul_left hd
    have hle : p ^ m ≤ c' - c := Nat.le_of_dvd (by omega) hd'
    calc p ^ m * h ! ≤ c' * h ! := Nat.mul_le_mul_right _ (by omega)
      _ = A u' h' := by rw [hA2]; ring
      _ ≤ x ^ h' := A_le hx2
  · have hd := Nat.dvd_sub h1 h2
    have : A u h - 1 - (A u' h' - 1) = h ! * (c - c') := by
      rw [hA2, hc1, Nat.mul_sub]; have := Nat.mul_le_mul_left (h !) hlt.le; omega
    rw [this] at hd
    have hd' := hcop.dvd_of_dvd_mul_left hd
    have hle : p ^ m ≤ c - c' := Nat.le_of_dvd (by omega) hd'
    calc p ^ m * h ! ≤ c * h ! := Nat.mul_le_mul_right _ (by omega)
      _ = A u h := by rw [hc1]; ring
      _ ≤ x ^ h := A_le hx1
      _ ≤ x ^ h' := Nat.pow_le_pow_right hx hh

/-- `phiL x y = y (1 + log x - log y)`. -/
noncomputable def phiL (x y : ℝ) : ℝ := y * (1 + Real.log x - Real.log y)

lemma log_factorial_ge (h : ℕ) : (h : ℝ) * Real.log h - h ≤ Real.log (h ! : ℝ) := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · simp
  have h1 := Real.pow_div_factorial_le_exp (h : ℝ) (show (0 : ℝ) ≤ h by positivity) h
  have hf : (0 : ℝ) < (h ! : ℝ) := by exact_mod_cast Nat.factorial_pos h
  have hp : (0 : ℝ) < (h : ℝ) ^ h := pow_pos (by exact_mod_cast hh) _
  have := Real.log_le_log (div_pos hp hf) h1
  rw [Real.log_div hp.ne' hf.ne', Real.log_exp, Real.log_pow] at this
  linarith

lemma two_block_log {p m u h u' h' x : ℕ} (hp : p.Prime) (hhp : h < p) (hh : h ≤ h')
    (h1 : p ^ m ∣ A u h - 1) (h2 : p ^ m ∣ A u' h' - 1) (hne : A u h ≠ A u' h')
    (hx1 : u + h ≤ x) (hx2 : u' + h' ≤ x) (hx : 1 ≤ x) :
    (m : ℝ) * Real.log p ≤ phiL x h + ((h' : ℝ) - h) * Real.log x := by
  have key := two_block hp hhp hh h1 h2 hne hx1 hx2 hx
  have hpp : (0 : ℝ) < (p : ℝ) ^ m := pow_pos (by exact_mod_cast hp.pos) _
  have hf : (0 : ℝ) < (h ! : ℝ) := by exact_mod_cast Nat.factorial_pos h
  have hx' : (0 : ℝ) < x := by exact_mod_cast hx
  have key' : ((p : ℝ) ^ m) * (h ! : ℝ) ≤ (x : ℝ) ^ h' := by exact_mod_cast key
  have hl := Real.log_le_log (mul_pos hpp hf) key'
  rw [Real.log_mul hpp.ne' hf.ne', Real.log_pow, Real.log_pow] at hl
  have := log_factorial_ge h
  unfold phiL
  nlinarith

lemma one_block_log {p m u h x : ℕ} (hu : 1 ≤ u) (hh : 1 ≤ h) (h1 : p ^ m ∣ A u h - 1)
    (hx1 : u + h ≤ x) (hp : 1 < p) :
    (m : ℝ) * Real.log p ≤ h * Real.log x := by
  have h2 := two_le_A hu hh
  have hle : p ^ m ≤ A u h - 1 := Nat.le_of_dvd (by omega) h1
  have hle2 : p ^ m ≤ x ^ h := le_trans hle (le_trans (Nat.sub_le _ _) (A_le hx1))
  have hx : 1 ≤ x := by omega
  have hpp : (0 : ℝ) < (p : ℝ) ^ m := pow_pos (by exact_mod_cast (show 0 < p by omega)) _
  have key' : ((p : ℝ) ^ m) ≤ (x : ℝ) ^ h := by exact_mod_cast hle2
  have hl := Real.log_le_log hpp key'
  rw [Real.log_pow, Real.log_pow] at hl
  linarith

lemma digits_sum_le (n : ℕ) : (Nat.digits 2 n).sum ≤ Nat.log 2 n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hlen := Nat.length_digits 2 n (by norm_num) hn.ne'
  have : ∀ d ∈ Nat.digits 2 n, d ≤ 1 := fun d hd => by
    have := Nat.digits_lt_base (by norm_num) hd; omega
  calc (Nat.digits 2 n).sum ≤ (Nat.digits 2 n).length * 1 := List.sum_le_card_nsmul _ _ this
    _ = _ := by rw [hlen]; ring

lemma padic_two_fact_ge (n : ℕ) : n ≤ padicValNat 2 (n !) + Nat.log 2 n + 1 := by
  have := @sub_one_mul_padicValNat_factorial 2 ⟨Nat.prime_two⟩ n
  have h2 := digits_sum_le n
  norm_num at this
  omega

lemma padic_two_fact_le (n : ℕ) : padicValNat 2 (n !) ≤ n := by
  have := @sub_one_mul_padicValNat_factorial 2 ⟨Nat.prime_two⟩ n
  norm_num at this
  omega

/-- Equal products of blocks of different lengths force the lengths to be close. -/
lemma eq_prod_close {u h u' h' x : ℕ} (he : A u h = A u' h') (hh : h < h')
    (hx1 : u + h ≤ x) (hx2 : u' + h' ≤ x) : h' - h ≤ 2 * Nat.log 2 x + 1 := by
  have hdvd : h' ! ∣ h ! * (u + h).choose h := by
    rw [← A_eq, he, A_eq]; exact dvd_mul_right _ _
  have hne1 : h ! ≠ 0 := Nat.factorial_ne_zero h
  have hne2 : (u + h).choose h ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hv := (Nat.factorization_le_iff_dvd (Nat.factorial_ne_zero h')
    (mul_ne_zero hne1 hne2)).mpr hdvd 2
  rw [Nat.factorization_mul hne1 hne2] at hv
  simp only [Finsupp.add_apply] at hv
  rw [Nat.factorization_def _ Nat.prime_two, Nat.factorization_def _ Nat.prime_two] at hv
  have hc := @Nat.factorization_choose_le_log 2 (u + h) h
  have h3 := padic_two_fact_ge h'
  have h4 := padic_two_fact_le h
  have h5 : Nat.log 2 (u + h) ≤ Nat.log 2 x := Nat.log_mono_right hx1
  have h6 : Nat.log 2 h' ≤ Nat.log 2 x := Nat.log_mono_right (by omega)
  omega

end LaneCLai


/-! Lane C, Erdős 977 (Lai) H2 — sorted positions and gaps of a finite set of naturals. -/

namespace LaneCLai
open Finset

/-- The `i`-th smallest element of `P` (junk `0` past the end). -/
noncomputable def pos (P : Finset ℕ) (i : ℕ) : ℕ :=
  if h : i < P.card then P.orderEmbOfFin rfl ⟨i, h⟩ else 0

lemma pos_mem {P : Finset ℕ} {i : ℕ} (hi : i < P.card) : pos P i ∈ P := by
  unfold pos; rw [dif_pos hi]; exact orderEmbOfFin_mem P rfl _

lemma pos_lt {P : Finset ℕ} {i j : ℕ} (hij : i < j) (hj : j < P.card) : pos P i < pos P j := by
  unfold pos; rw [dif_pos (hij.trans hj), dif_pos hj]
  exact (P.orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr hij)

lemma pos_le {P : Finset ℕ} {i j : ℕ} (hij : i ≤ j) (hj : j < P.card) : pos P i ≤ pos P j := by
  rcases hij.lt_or_eq with h | rfl
  · exact (pos_lt h hj).le
  · exact le_rfl

lemma pos_inj {P : Finset ℕ} {i j : ℕ} (hi : i < P.card) (hj : j < P.card)
    (h : pos P i = pos P j) : i = j := by
  rcases lt_trichotomy i j with h1 | h1 | h1
  · exact absurd h (pos_lt h1 hj).ne
  · exact h1
  · exact absurd h (pos_lt h1 hi).ne'


lemma pos_mem_Icc {P : Finset ℕ} {a b i : ℕ} (hP : P ⊆ Icc a b) (hi : i < P.card) :
    a ≤ pos P i ∧ pos P i ≤ b := mem_Icc.mp (hP (pos_mem hi))

/-- Length of the `i`-th gap. -/
noncomputable def len (P : Finset ℕ) (i : ℕ) : ℕ := pos P (i + 1) - pos P i

lemma len_pos {P : Finset ℕ} {i : ℕ} (hi : i + 1 < P.card) : 1 ≤ len P i := by
  unfold len; have := pos_lt (P := P) (show i < i + 1 by omega) hi; omega

lemma pos_add_len {P : Finset ℕ} {i : ℕ} (hi : i + 1 < P.card) :
    pos P i + len P i = pos P (i + 1) := by
  unfold len; have := pos_lt (P := P) (show i < i + 1 by omega) hi; omega

lemma sum_len {P : Finset ℕ} (n : ℕ) (hn : n < P.card) :
    ∑ i ∈ range n, len P i = pos P n - pos P 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    have h1 := pos_le (Nat.zero_le n) (show n < P.card by omega)
    have h2 := pos_add_len (P := P) (i := n) hn
    omega

lemma sum_len_le {P : Finset ℕ} {a b : ℕ} (hP : P ⊆ Icc a b) (hc : 1 ≤ P.card) :
    ∑ i ∈ range (P.card - 1), len P i ≤ b - a := by
  rw [sum_len _ (by omega)]
  have h1 := pos_mem_Icc hP (show P.card - 1 < P.card by omega)
  have h2 := pos_mem_Icc hP (show 0 < P.card by omega)
  omega

/-- Gaps with an endpoint outside `P'` number at most `2 |P \ P'|`. -/
lemma card_dead_le {P P' : Finset ℕ} :
    ((range (P.card - 1)).filter (fun i => pos P i ∉ P' ∨ pos P (i + 1) ∉ P')).card
      ≤ 2 * (P \ P').card := by
  have hsub : (range (P.card - 1)).filter (fun i => pos P i ∉ P' ∨ pos P (i + 1) ∉ P') ⊆
      ((range (P.card - 1)).filter (fun i => pos P i ∉ P')) ∪
      ((range (P.card - 1)).filter (fun i => pos P (i + 1) ∉ P')) := by
    intro i hi; simp only [mem_filter, mem_union] at hi ⊢; tauto
  have c1 : ((range (P.card - 1)).filter (fun i => pos P i ∉ P')).card ≤ (P \ P').card := by
    apply card_le_card_of_injOn (pos P)
    · intro i hi
      simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hi
      simp only [coe_sdiff, Set.mem_diff, mem_coe]
      exact ⟨pos_mem (by omega), hi.2⟩
    · intro i hi j hj h
      simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hi hj
      exact pos_inj (by omega) (by omega) h
  have c2 : ((range (P.card - 1)).filter (fun i => pos P (i + 1) ∉ P')).card ≤ (P \ P').card := by
    apply card_le_card_of_injOn (fun i => pos P (i + 1))
    · intro i hi
      simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hi
      simp only [coe_sdiff, Set.mem_diff, mem_coe]
      exact ⟨pos_mem (by omega), hi.2⟩
    · intro i hi j hj h
      simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hi hj
      have := pos_inj (by omega) (by omega) h
      omega
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ ≤ _ := by omega

end LaneCLai


/-! Lane C, Erdős 977 (Lai) H2 — few `n` in an interval below `p` with `p ∣ n! + 1`
(Luca–Shparlinski, Lemma 2.2 of Lai, `f = 1`), via root counting modulo `p`. -/

namespace LaneCLai
open Finset Polynomial
open scoped Nat

/-- `(X+1)(X+2)…(X+h) - 1` over `ZMod p`. -/
noncomputable def Ppoly (p h : ℕ) : (ZMod p)[X] :=
  (∏ j ∈ range h, (X + C ((j : ZMod p) + 1))) - 1

lemma Ppoly_natDegree (p h : ℕ) [Fact p.Prime] (hh : 1 ≤ h) : (Ppoly p h).natDegree = h := by
  unfold Ppoly
  rw [show (1 : (ZMod p)[X]) = C 1 by simp, natDegree_sub_C, natDegree_prod_of_monic]
  · rw [Finset.sum_congr rfl (fun j _ => natDegree_X_add_C _)]
    simp
  · intro j _; exact monic_X_add_C _

lemma Ppoly_ne_zero (p h : ℕ) [Fact p.Prime] (hh : 1 ≤ h) : Ppoly p h ≠ 0 := by
  intro h0
  have := Ppoly_natDegree p h hh
  rw [h0, natDegree_zero] at this
  omega

lemma Ppoly_eval (p u h : ℕ) : (Ppoly p h).eval (u : ZMod p) = ((A u h : ℕ) : ZMod p) - 1 := by
  unfold Ppoly A
  simp only [eval_sub, eval_prod, eval_add, eval_X, eval_C, eval_one, Nat.cast_prod]
  congr 1
  apply prod_congr rfl
  intro j _
  push_cast; ring

/-- At most `h` gaps of length exactly `h`. -/
lemma card_len_eq_le {p : ℕ} (hp : p.Prime) {Q : Finset ℕ} {b : ℕ} (hQ : ∀ n ∈ Q, n ≤ b)
    (hb : b < p) (hdiv : ∀ n ∈ Q, p ∣ n ! + 1) (h : ℕ) (hh : 1 ≤ h) :
    ((range (Q.card - 1)).filter (fun i => len Q i = h)).card ≤ h := by
  haveI : Fact p.Prime := ⟨hp⟩
  set S := (range (Q.card - 1)).filter (fun i => len Q i = h)
  have hinj : Set.InjOn (fun i => ((pos Q i : ℕ) : ZMod p)) (S : Set ℕ) := by
    intro i hi j hj hij
    simp only [S, coe_filter, mem_range, Set.mem_setOf_eq] at hi hj
    have hi' := hQ _ (pos_mem (show i < Q.card by omega))
    have hj' := hQ _ (pos_mem (show j < Q.card by omega))
    have : pos Q i = pos Q j := by
      have := (ZMod.natCast_eq_natCast_iff' _ _ p).mp hij
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact pos_inj (by omega) (by omega) this
  have hcard : S.card = (S.image (fun i => ((pos Q i : ℕ) : ZMod p))).card :=
    (card_image_of_injOn hinj).symm
  rw [hcard, ← Ppoly_natDegree p h hh]
  apply card_le_degree_of_subset_roots
  intro z hz
  rw [Finset.mem_val, mem_image] at hz
  obtain ⟨i, hi, rfl⟩ := hz
  simp only [S, mem_filter, mem_range] at hi
  rw [mem_roots (Ppoly_ne_zero p h hh), IsRoot.def, Ppoly_eval]
  have hu := pos_mem (show i < Q.card by omega)
  have hv := pos_mem (show i + 1 < Q.card by omega)
  have hlen : len Q i = h := hi.2
  have hd := dvd_A_sub_one (m := 1) hp
    (pos_lt (P := Q) (show i < i + 1 by omega) (show i + 1 < Q.card by omega)).le
    (by simpa using hdiv _ hu) (by simpa using hdiv _ hv)
  rw [pow_one] at hd
  change p ∣ A (pos Q i) (len Q i) - 1 at hd
  rw [hlen] at hd
  have hA := A_pos (pos Q i) h
  have h1 : ((A (pos Q i) h - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  rw [Nat.cast_sub hA, Nat.cast_one, sub_eq_zero] at h1
  rw [h1, sub_self]

/-- Lai's Lemma 2.2 for `f = 1`: `|Q| ≤ H² + (b-a)/H + 1`. -/
lemma card_LS {p : ℕ} (hp : p.Prime) {Q : Finset ℕ} {a b : ℕ} (hQ : Q ⊆ Icc a b)
    (hb : b < p) (hdiv : ∀ n ∈ Q, p ∣ n ! + 1) (H : ℕ) (hH : 1 ≤ H) :
    Q.card * H ≤ H * H * H + (b - a) + H := by
  rcases Nat.eq_zero_or_pos Q.card with h0 | hc
  · rw [h0]; simp
  have hQb : ∀ n ∈ Q, n ≤ b := fun n hn => (mem_Icc.mp (hQ hn)).2
  set G := range (Q.card - 1)
  have hsplit : G.card = (G.filter (fun i => len Q i ≤ H)).card +
      (G.filter (fun i => ¬ len Q i ≤ H)).card := (card_filter_add_card_filter_not _).symm
  have hsmall : (G.filter (fun i => len Q i ≤ H)).card ≤ H * H := by
    have hsub : G.filter (fun i => len Q i ≤ H) ⊆
        (Icc 1 H).biUnion (fun h => G.filter (fun i => len Q i = h)) := by
      intro i hi
      simp only [G, mem_filter, mem_range] at hi
      simp only [mem_biUnion, mem_Icc, mem_filter, G, mem_range]
      exact ⟨len Q i, ⟨len_pos (by omega), hi.2⟩, hi.1, rfl⟩
    calc _ ≤ _ := card_le_card hsub
      _ ≤ ∑ h ∈ Icc 1 H, (G.filter (fun i => len Q i = h)).card := card_biUnion_le
      _ ≤ ∑ h ∈ Icc 1 H, H := sum_le_sum (fun h hh => by
          have := mem_Icc.mp hh
          exact (card_len_eq_le hp hQb hb hdiv h this.1).trans this.2)
      _ = H * H := by simp
  have hbig : (G.filter (fun i => ¬ len Q i ≤ H)).card * H ≤ b - a := by
    calc (G.filter (fun i => ¬ len Q i ≤ H)).card * H
        = ∑ i ∈ G.filter (fun i => ¬ len Q i ≤ H), H := by rw [sum_const, smul_eq_mul]
      _ ≤ ∑ i ∈ G.filter (fun i => ¬ len Q i ≤ H), len Q i :=
          sum_le_sum (fun i hi => by simp only [mem_filter] at hi; omega)
      _ ≤ ∑ i ∈ G, len Q i := sum_le_sum_of_subset (filter_subset _ _)
      _ ≤ b - a := sum_len_le hQ hc
  have hG : G.card = Q.card - 1 := card_range _
  have : Q.card ≤ H * H + (G.filter (fun i => ¬ len Q i ≤ H)).card + 1 := by omega
  calc Q.card * H ≤ (H * H + (G.filter (fun i => ¬ len Q i ≤ H)).card + 1) * H :=
        Nat.mul_le_mul_right _ this
    _ = H * H * H + (G.filter (fun i => ¬ len Q i ≤ H)).card * H + H := by ring
    _ ≤ _ := by omega

end LaneCLai


/-! Lane C, Erdős 977 (Lai) H2 — the function `phiL x y = y (1 + log x - log y)`:
monotonicity on `[0, x]`, Jensen's inequality, and a pairing (layer cake) inequality. -/

namespace LaneCLai
open Finset Real

lemma phiL_nonneg {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) : 0 ≤ phiL x y := by
  unfold phiL
  rcases hy.eq_or_lt with rfl | hy'
  · simp
  have := Real.log_le_log hy' hyx
  nlinarith

lemma phiL_mono {x y₁ y₂ : ℝ} (h1 : 0 ≤ y₁) (h12 : y₁ ≤ y₂) (h2x : y₂ ≤ x) : phiL x y₁ ≤ phiL x y₂ := by
  rcases h1.eq_or_lt with rfl | h1'
  · rw [show phiL x 0 = 0 by simp [phiL]]; exact phiL_nonneg (by linarith) h2x
  have hy2 : 0 < y₂ := lt_of_lt_of_le h1' h12
  -- tangent line for y log y at y₂
  have ht : y₂ * Real.log y₂ - y₁ * Real.log y₁ ≤ (Real.log y₂ + 1) * (y₂ - y₁) := by
    have := Real.log_le_sub_one_of_pos (show 0 < y₂ / y₁ from div_pos hy2 h1')
    rw [Real.log_div hy2.ne' h1'.ne'] at this
    have h3 : y₁ * (Real.log y₂ - Real.log y₁) ≤ y₁ * (y₂ / y₁ - 1) :=
      mul_le_mul_of_nonneg_left this h1
    have h4 : y₁ * (y₂ / y₁ - 1) = y₂ - y₁ := by first | (field_simp; ring) | field_simp
    rw [h4] at h3
    linarith
  have hl := Real.log_le_log hy2 h2x
  unfold phiL
  nlinarith

lemma phiL_concave {x : ℝ} (hx : 1 ≤ x) : ConcaveOn ℝ (Set.Ici 0) (phiL x) := by
  have hc : 0 ≤ 1 + Real.log x := by have := Real.log_nonneg hx; linarith
  have h1 : ConcaveOn ℝ (Set.Ici (0:ℝ)) (fun y => (1 + Real.log x) * y) := by
    refine ⟨convex_Ici 0, fun a _ b _ s t _ _ _ => ?_⟩
    simp only [smul_eq_mul]; exact le_of_eq (by ring)
  have h2 := h1.add Real.concaveOn_negMulLog
  have heq : phiL x = (fun y => (1 + Real.log x) * y) + Real.negMulLog := by
    funext y
    simp only [phiL, Pi.add_apply, Real.negMulLog]
    ring
  rw [heq]
  exact h2

/-- Jensen: `∑ phiL(ℓ g) ≤ Λ log n + x` when `∑ ℓ ≤ Λ ≤ x`. -/
lemma jensen_phiL {ι : Type*} (G : Finset ι) (ℓ : ι → ℝ) {x Λ : ℝ} (hx : 1 ≤ x)
    (hℓ : ∀ g ∈ G, 0 ≤ ℓ g) (hS : ∑ g ∈ G, ℓ g ≤ Λ) (hΛ : Λ ≤ x) (hG : 1 ≤ G.card) :
    ∑ g ∈ G, phiL x (ℓ g) ≤ Λ * Real.log G.card + x := by
  set n : ℝ := (G.card : ℝ) with hndef
  have hn : (1 : ℝ) ≤ n := by rw [hndef]; exact_mod_cast hG
  have hn0 : (0 : ℝ) < n := by linarith
  have hn0' : n ≠ 0 := hn0.ne'
  set S := ∑ g ∈ G, ℓ g with hSdef
  have hS0 : 0 ≤ S := sum_nonneg hℓ
  have hΛ0 : 0 ≤ Λ := hS0.trans hS
  have hw1 : ∑ _g ∈ G, (1 / n) = 1 := by
    rw [sum_const, nsmul_eq_mul, ← hndef]; field_simp
  have hJ := (phiL_concave hx).le_map_sum (t := G) (w := fun _ => 1 / n) (p := ℓ)
    (fun _ _ => div_nonneg zero_le_one hn0.le) hw1 (fun g hg => Set.mem_Ici.mpr (hℓ g hg))
  simp only [smul_eq_mul] at hJ
  rw [← mul_sum, ← mul_sum] at hJ
  have hJ' : ∑ g ∈ G, phiL x (ℓ g) ≤ n * phiL x (S / n) := by
    have h1 := mul_le_mul_of_nonneg_left hJ hn0.le
    calc ∑ g ∈ G, phiL x (ℓ g) = n * (1 / n * ∑ g ∈ G, phiL x (ℓ g)) := by field_simp
      _ ≤ n * phiL x (1 / n * S) := h1
      _ = n * phiL x (S / n) := by rw [one_div_mul_eq_div]
  refine hJ'.trans ?_
  have hln := Real.log_nonneg hn
  rcases hS0.eq_or_lt with h0 | hpos
  · rw [← h0]
    simp only [zero_div, phiL, zero_mul, mul_zero]
    nlinarith [mul_nonneg hΛ0 hln]
  have hrw : n * phiL x (S / n) = S * Real.log n + S * (1 + Real.log x - Real.log S) := by
    unfold phiL
    rw [Real.log_div hpos.ne' hn0']
    first | (first | (field_simp; ring) | field_simp) | field_simp
  rw [hrw]
  have hSx : S ≤ x := hS.trans hΛ
  have hxS : S * (1 + Real.log x - Real.log S) ≤ x := by
    have hx0 : 0 < x := by linarith
    have := Real.log_le_sub_one_of_pos (show 0 < x / S from div_pos hx0 hpos)
    rw [Real.log_div hx0.ne' hpos.ne'] at this
    have h3 := mul_le_mul_of_nonneg_left this hpos.le
    have h4 : S * (x / S - 1) = x - S := by first | (field_simp; ring) | field_simp
    rw [h4] at h3
    linarith
  have := mul_le_mul_of_nonneg_right hS hln
  linarith

/-- Pairing inequality: if for each `j < n` at least `2 (n - j)` of the `ℓ g` are `≥ y j`,
then `2 ∑_{j<n} phiL (y j) ≤ ∑_g phiL (ℓ g)`. -/
lemma layer_phiL {ι : Type*} [DecidableEq ι] {x : ℝ} (ℓ : ι → ℝ) (y : ℕ → ℝ)
    (hy : ∀ j, 0 ≤ y j) : ∀ (n : ℕ) (G : Finset ι), (∀ g ∈ G, 0 ≤ ℓ g ∧ ℓ g ≤ x) →
    (∀ j < n, 2 * (n - j) ≤ (G.filter (fun g => y j ≤ ℓ g)).card) →
    2 * ∑ j ∈ range n, phiL x (y j) ≤ ∑ g ∈ G, phiL x (ℓ g) := by
  intro n
  induction n with
  | zero =>
    intro G hG _
    simp only [range_zero, sum_empty, mul_zero]
    exact sum_nonneg (fun g hg => phiL_nonneg (hG g hg).1 (hG g hg).2)
  | succ n ih =>
    intro G hG hcnt
    have h2 := hcnt n (Nat.lt_succ_self n)
    rw [show n + 1 - n = 1 by omega] at h2
    obtain ⟨g₁, hg₁, g₂, hg₂, hne⟩ :=
      (Finset.one_lt_card (s := G.filter (fun g => y n ≤ ℓ g))).mp (by omega)
    simp only [mem_filter] at hg₁ hg₂
    obtain ⟨G', hG'def⟩ : ∃ G' : Finset ι, G' = (G.erase g₁).erase g₂ := ⟨_, rfl⟩
    have hG'm : ∀ g, g ∈ G' ↔ g ≠ g₂ ∧ g ≠ g₁ ∧ g ∈ G := by
      intro g; rw [hG'def, mem_erase, mem_erase]
    have hG' : ∀ g ∈ G', 0 ≤ ℓ g ∧ ℓ g ≤ x := fun g hg => hG g ((hG'm g).mp hg).2.2
    have hcnt' : ∀ j < n, 2 * (n - j) ≤ (G'.filter (fun g => y j ≤ ℓ g)).card := by
      intro j hj
      have := hcnt j (by omega)
      have hsub : G.filter (fun g => y j ≤ ℓ g) ⊆
          insert g₁ (insert g₂ (G'.filter (fun g => y j ≤ ℓ g))) := by
        intro g hg
        simp only [mem_filter] at hg
        simp only [mem_insert, mem_filter, hG'm]
        by_cases h1 : g = g₁
        · left; exact h1
        by_cases h2' : g = g₂
        · right; left; exact h2'
        right; right; exact ⟨⟨h2', h1, hg.1⟩, hg.2⟩
      have := (card_le_card hsub).trans (card_insert_le _ _)
      have := this.trans (Nat.succ_le_succ (card_insert_le _ _))
      omega
    have hrec := ih G' hG' hcnt'
    have hsplit : ∑ g ∈ G, phiL x (ℓ g) =
        phiL x (ℓ g₁) + phiL x (ℓ g₂) + ∑ g ∈ G', phiL x (ℓ g) := by
      rw [hG'def, ← add_sum_erase _ _ hg₁.1,
        ← add_sum_erase _ _ (mem_erase.mpr ⟨hne.symm, hg₂.1⟩)]
      ring
    have m1 := phiL_mono (hy n) hg₁.2 (hG g₁ hg₁.1).2
    have m2 := phiL_mono (hy n) hg₂.2 (hG g₂ hg₂.1).2
    rw [Finset.sum_range_succ, hsplit]
    linarith

end LaneCLai


/-! Lane C, Erdős 977 (Lai) H2 — the one-level estimate behind Lai's Lemma 2.7.

`P` is a set of points, `P' ⊆ P` the points where `p^m ∣ n! + 1`.  If at least `2|P \ P'| + R + 1`
gaps of `P` have length `≤ y`, then at least `R + 1` of them have both endpoints in `P'`; a bucket of
width `y / B + 1` contains `2 log₂ x + 2` of them, two of which have distinct products (lengths of
blocks with equal products differ by at most `2 log₂ x + 1`), and the two-block bound applies. -/

namespace LaneCLai
open Finset Real
open scoped Nat

lemma gap_dvd {p m : ℕ} (hp : p.Prime) {P P' : Finset ℕ} (hm : ∀ n ∈ P', p ^ m ∣ n ! + 1)
    {i : ℕ} (hi : i + 1 < P.card) (h1 : pos P i ∈ P') (h2 : pos P (i + 1) ∈ P') :
    p ^ m ∣ A (pos P i) (len P i) - 1 :=
  dvd_A_sub_one hp (pos_lt (P := P) (show i < i + 1 by omega) hi).le (hm _ h1) (hm _ h2)

lemma sub_lt_of_div_eq {u v w : ℕ} (hw : 0 < w) (huv : u ≤ v) (he : u / w = v / w) : v - u < w := by
  have h1 := Nat.lt_div_mul_add (a := v) hw
  have h2 := Nat.div_mul_le_self u w
  rw [he] at h2
  omega

lemma per_k {p m a b x : ℕ} (hp : p.Prime) (hx : 1 ≤ x) (hbx : b ≤ x) (hbp : b < p)
    {P P' : Finset ℕ} (hP : P ⊆ Icc a b) (hm : ∀ n ∈ P', p ^ m ∣ n ! + 1)
    {y R B : ℕ} (hyx : y ≤ x) (hB : 1 ≤ B) (hBR : B * (2 * Nat.log 2 x + 2) ≤ R)
    (hwin : 2 * (P \ P').card + R + 1 ≤
      ((range (P.card - 1)).filter (fun i => len P i ≤ y)).card) :
    (m : ℝ) * Real.log p ≤ phiL x y + ((y / B : ℕ) : ℝ) * Real.log x := by
  classical
  set E := 2 * Nat.log 2 x + 1 with hE
  set G := range (P.card - 1)
  set W := G.filter (fun i => len P i ≤ y ∧ pos P i ∈ P' ∧ pos P (i + 1) ∈ P')
  have hW : R + 1 ≤ W.card := by
    have hsub : G.filter (fun i => len P i ≤ y) ⊆
        W ∪ G.filter (fun i => pos P i ∉ P' ∨ pos P (i + 1) ∉ P') := by
      intro i hi
      simp only [mem_filter] at hi
      simp only [W, mem_union, mem_filter]
      by_cases h : pos P i ∈ P' ∧ pos P (i + 1) ∈ P'
      · left; exact ⟨hi.1, hi.2, h⟩
      · right; exact ⟨hi.1, by tauto⟩
    have := (card_le_card hsub).trans (card_union_le _ _)
    have hd : (G.filter (fun i => pos P i ∉ P' ∨ pos P (i + 1) ∉ P')).card ≤
        2 * (P \ P').card := card_dead_le (P := P) (P' := P')
    omega
  set w := y / B + 1 with hw
  have hw0 : 0 < w := Nat.succ_pos _
  set f : ℕ → ℕ := fun i => (len P i - 1) / w
  have hmaps : ∀ i ∈ W, f i ∈ range B := by
    intro i hi
    simp only [W, mem_filter] at hi
    rw [mem_range]
    show (len P i - 1) / w < B
    apply Nat.div_lt_of_lt_mul
    have h1 := Nat.lt_div_mul_add (a := y) (show 0 < B by omega)
    have h2 : len P i - 1 ≤ y := by omega
    calc len P i - 1 ≤ y := h2
      _ < y / B * B + B := h1
      _ = w * B := by rw [hw]; ring
  have hcard : (range B).card * (E + 1) < W.card := by
    rw [card_range]
    calc B * (E + 1) = B * (2 * Nat.log 2 x + 2) := by rw [hE]; try ring
      _ ≤ R := hBR
      _ < W.card := by omega
  obtain ⟨c, -, hc⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hcard
  set F := W.filter (fun i => f i = c)
  have hFW : F ⊆ W := filter_subset _ _
  have hlen1 : ∀ i ∈ W, 1 ≤ len P i := by
    intro i hi; simp only [W, G, mem_filter, mem_range] at hi; exact len_pos (by omega)
  have hiW : ∀ i ∈ W, i + 1 < P.card := by
    intro i hi; simp only [W, G, mem_filter, mem_range] at hi; omega
  have hposx : ∀ i ∈ W, pos P i + len P i ≤ x := by
    intro i hi
    rw [pos_add_len (hiW i hi)]
    exact (pos_mem_Icc hP (show i + 1 < P.card from hiW i hi)).2.trans hbx
  -- two gaps in the same bucket with distinct products
  have hex : ∃ i ∈ F, ∃ j ∈ F, len P i ≤ len P j ∧
      A (pos P i) (len P i) ≠ A (pos P j) (len P j) := by
    by_contra hall
    push_neg at hall
    have hFne : F.Nonempty := card_pos.mp (by omega)
    obtain ⟨i₀, hi₀, hmin⟩ := exists_min_image F (len P) hFne
    have hrange : ∀ j ∈ F, len P j ∈ Icc (len P i₀) (len P i₀ + E) := by
      intro j hj
      have h1 := hmin j hj
      rw [mem_Icc]
      refine ⟨h1, ?_⟩
      rcases h1.lt_or_eq with h2 | h2
      · have := eq_prod_close (hall i₀ hi₀ j hj h1) h2 (hposx i₀ (hFW hi₀)) (hposx j (hFW hj))
        omega
      · omega
    have hinj : Set.InjOn (len P) (F : Set ℕ) := by
      intro i hi j hj hij
      have hi' : i ∈ F := hi
      have hj' : j ∈ F := hj
      have hA := hall i hi' j hj' hij.le
      rw [hij] at hA
      have := A_inj (hlen1 j (hFW hj')) hA
      exact pos_inj (by have := hiW i (hFW hi'); omega) (by have := hiW j (hFW hj'); omega) this
    have := card_le_card_of_injOn (len P) (fun j hj => mem_coe.mpr (hrange j (mem_coe.mp hj))) hinj
    rw [Nat.card_Icc] at this
    omega
  obtain ⟨i, hiF, j, hjF, hij, hne⟩ := hex
  have hiW' := hFW hiF
  have hjW' := hFW hjF
  have hi2 := hiW'
  have hj2 := hjW'
  simp only [W, mem_filter] at hi2 hj2
  have hfij : f i = f j := by
    simp only [F, mem_filter] at hiF hjF; rw [hiF.2, hjF.2]
  have hdiff0 : len P j - len P i ≤ w - 1 := by
    have := sub_lt_of_div_eq hw0 (Nat.sub_le_sub_right hij 1) hfij
    have h1 := hlen1 i hiW'
    omega
  have hw1 : w - 1 = y / B := by rw [hw, Nat.add_sub_cancel]
  have hdiff : len P j - len P i ≤ y / B := hw1 ▸ hdiff0
  have hlp : len P i < p := by
    have := pos_mem_Icc hP (show i + 1 < P.card from hiW i hiW')
    have := pos_mem_Icc hP (show i < P.card by have := hiW i hiW'; omega)
    unfold len; omega
  have key := two_block_log hp hlp hij (gap_dvd hp hm (hiW i hiW') hi2.2.2.1 hi2.2.2.2)
    (gap_dvd hp hm (hiW j hjW') hj2.2.2.1 hj2.2.2.2) hne (hposx i hiW') (hposx j hjW') hx
  have hmono := phiL_mono (x := (x : ℝ)) (Nat.cast_nonneg (len P i))
    (show (len P i : ℝ) ≤ y by exact_mod_cast hi2.2.1) (by exact_mod_cast hyx)
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by exact_mod_cast hx)
  have hd' : ((len P j : ℝ) - len P i) ≤ ((y / B : ℕ) : ℝ) := by
    rw [← Nat.cast_sub hij]; exact_mod_cast hdiff
  nlinarith

end LaneCLai


/-! Lane C, Erdős 977 (Lai) H2 — ranks (a greedy chain of top sets) and Lai's Lemma 2.7. -/

namespace LaneCLai
open Finset Real
open scoped Nat

noncomputable def nextPt (Q S : Finset ℕ) (o : ℕ → ℕ) : ℕ :=
  if h : (Q \ S).Nonempty then Classical.choose (exists_max_image (Q \ S) o h) else 0

lemma nextPt_spec {Q S : Finset ℕ} {o : ℕ → ℕ} (h : (Q \ S).Nonempty) :
    nextPt Q S o ∈ Q \ S ∧ ∀ n ∈ Q \ S, o n ≤ o (nextPt Q S o) := by
  unfold nextPt; rw [dif_pos h]; exact Classical.choose_spec (exists_max_image (Q \ S) o h)

/-- `chain Q o r` = the `r` points of `Q` with the largest values of `o` (greedy). -/
noncomputable def chain (Q : Finset ℕ) (o : ℕ → ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | r + 1 => if (Q \ chain Q o r).Nonempty then insert (nextPt Q (chain Q o r) o) (chain Q o r)
      else chain Q o r

/-- `val Q o r` = the `(r+1)`-th largest value. -/
noncomputable def val (Q : Finset ℕ) (o : ℕ → ℕ) (r : ℕ) : ℕ := o (nextPt Q (chain Q o r) o)

variable {Q : Finset ℕ} {o : ℕ → ℕ}

lemma chain_basic : ∀ r ≤ Q.card, chain Q o r ⊆ Q ∧ (chain Q o r).card = r := by
  intro r
  induction r with
  | zero => intro _; simp [chain]
  | succ r ih =>
    intro hr
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hne : (Q \ chain Q o r).Nonempty := by
      rw [← card_pos, card_sdiff_of_subset h1]; omega
    have hs := nextPt_spec (o := o) hne
    rw [mem_sdiff] at hs
    simp only [chain, if_pos hne]
    exact ⟨insert_subset hs.1.1 h1, by rw [card_insert_of_notMem hs.1.2, h2]⟩

lemma chain_succ {r : ℕ} (hr : r < Q.card) :
    chain Q o (r + 1) = insert (nextPt Q (chain Q o r) o) (chain Q o r) ∧
      (Q \ chain Q o r).Nonempty := by
  obtain ⟨h1, h2⟩ := chain_basic (o := o) r hr.le
  have hne : (Q \ chain Q o r).Nonempty := by
    rw [← card_pos, card_sdiff_of_subset h1]; omega
  exact ⟨by simp only [chain, if_pos hne], hne⟩

lemma chain_mono {r s : ℕ} (hrs : r ≤ s) (hs : s ≤ Q.card) : chain Q o r ⊆ chain Q o s := by
  induction s, hrs using Nat.le_induction with
  | base => exact subset_rfl
  | succ s _ ih =>
    rw [(chain_succ (o := o) (show s < Q.card by omega)).1]
    exact ih (by omega) |>.trans (subset_insert _ _)

lemma val_le_val {r s : ℕ} (hrs : r ≤ s) (hs : s < Q.card) : val Q o s ≤ val Q o r := by
  obtain ⟨_, hne⟩ := chain_succ (o := o) hs
  have h1 := (nextPt_spec (o := o) hne).1
  have hsub := chain_mono (o := o) hrs hs.le
  obtain ⟨_, hne'⟩ := chain_succ (o := o) (show r < Q.card by omega)
  have h2 := (nextPt_spec (o := o) hne').2
  unfold val
  apply h2
  rw [mem_sdiff] at h1 ⊢
  exact ⟨h1.1, fun h => h1.2 (hsub h)⟩

/-- Every point among the top `r+1` has value at least the `(r+1)`-th largest. -/
lemma val_le_of_mem {r : ℕ} (hr : r < Q.card) {n : ℕ} (hn : n ∈ chain Q o (r + 1)) :
    val Q o r ≤ o n := by
  induction r with
  | zero =>
    rw [(chain_succ (o := o) hr).1] at hn
    simp only [chain, insert_empty, mem_singleton] at hn
    rw [hn]; rfl
  | succ r ih =>
    rw [(chain_succ (o := o) hr).1, mem_insert] at hn
    rcases hn with rfl | hn
    · rfl
    · exact (val_le_val (Nat.le_succ r) hr).trans (ih (by omega) hn)

lemma sum_chain : ∀ r ≤ Q.card, ∑ n ∈ chain Q o r, o n = ∑ j ∈ range r, val Q o j := by
  intro r
  induction r with
  | zero => intro _; simp [chain]
  | succ r ih =>
    intro hr
    obtain ⟨h1, hne⟩ := chain_succ (o := o) (show r < Q.card by omega)
    have hs := (nextPt_spec (o := o) hne).1
    rw [mem_sdiff] at hs
    rw [h1, sum_insert hs.2, Finset.sum_range_succ, ih (by omega), add_comm] <;> rfl

lemma chain_full : chain Q o Q.card = Q := by
  obtain ⟨h1, h2⟩ := chain_basic (o := o) Q.card le_rfl
  exact eq_of_subset_of_card_le h1 (le_of_eq h2.symm)

/-! ### Lai's Lemma 2.7 (block estimate) -/

section block
variable {p a b x : ℕ}

set_option maxHeartbeats 4000000 in
/-- Parameters: `s = t / (2q)`, `K = t/2 - 2s`, `R = s`, `B = s/(E+1)`, `Y = (b-a)/s`. -/
lemma block (hp : p.Prime) (hx : 1 ≤ x) (hbx : b ≤ x) (hbp : b < p) (hab : a ≤ b)
    (hQ : Q ⊆ Icc a b) (hdiv : ∀ n ∈ Q, p ^ (o n) ∣ n ! + 1) {q t W : ℕ} (hq : 3 ≤ q)
    (hW : 1 ≤ W) (ht : t ≤ Q.card)
    (ht0 : 2 * q * (2 * Nat.log 2 x + 2) * ((2 * q + 1) * W + 1) ≤ t) :
    Real.log p * ∑ k ∈ range (t / 2 - 2 * (t / (2 * q)) + 1), (val Q o (t - k - 1) : ℝ) ≤
      ((b - a : ℕ) * Real.log t + x) / 2 + ((b - a : ℕ) : ℝ) / W * Real.log x := by
  classical
  set E1 := 2 * Nat.log 2 x + 2 with hE1
  set s := t / (2 * q) with hs
  set K := t / 2 - 2 * s with hK
  set B := s / E1 with hB
  set Y := (b - a) / s with hY
  set P := chain Q o t with hPdef
  have hPQ : P ⊆ Q := (chain_basic (Q := Q) (o := o) t ht).1
  have hPc : P.card = t := (chain_basic (Q := Q) (o := o) t ht).2
  have hP : P ⊆ Icc a b := hPQ.trans hQ
  have hE1pos : 2 ≤ E1 := by omega
  -- arithmetic of the parameters
  have hsq : 2 * q * s ≤ t := by
    have := Nat.div_mul_le_self t (2 * q)
    rw [← hs] at this
    linarith [mul_comm s (2 * q)]
  have hs1 : E1 * ((2 * q + 1) * W + 1) ≤ s := by
    rw [hs, Nat.le_div_iff_mul_le (by omega)]
    calc E1 * ((2 * q + 1) * W + 1) * (2 * q) = 2 * q * E1 * ((2 * q + 1) * W + 1) := by ring
      _ ≤ t := ht0
  have hs1' : 1 ≤ s := by
    have : 1 ≤ E1 * ((2 * q + 1) * W + 1) :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (Nat.succ_ne_zero _))
    omega
  have hBE : B * E1 ≤ s := Nat.div_mul_le_self s E1
  have hB1 : (2 * q + 1) * W + 1 ≤ B := by
    rw [hB, Nat.le_div_iff_mul_le (by omega)]
    calc ((2 * q + 1) * W + 1) * E1 = E1 * ((2 * q + 1) * W + 1) := by ring
      _ ≤ s := hs1
  have hBpos : 1 ≤ B := le_trans (Nat.le_add_left 1 _) hB1
  have h6s : 6 * s ≤ t := by nlinarith
  have hs2 : 2 ≤ s := by nlinarith
  have hKt : 2 * K + s + 3 ≤ t := by omega
  have hGc : (range (P.card - 1)).card = t - 1 := by rw [card_range, hPc]
  -- the threshold `y_k`
  have hlenle : ∀ i ∈ range (P.card - 1), len P i ≤ b - a := by
    intro i hi
    rw [mem_range] at hi
    have h1 := pos_mem_Icc hP (show i + 1 < P.card by omega)
    have h2 := pos_mem_Icc hP (show i < P.card by omega)
    unfold len; omega
  have hbig : ((range (P.card - 1)).filter (fun i => ¬ len P i ≤ Y)).card < s := by
    have hsum : ((range (P.card - 1)).filter (fun i => ¬ len P i ≤ Y)).card * (Y + 1) ≤ b - a := by
      calc _ = ∑ i ∈ (range (P.card - 1)).filter (fun i => ¬ len P i ≤ Y), (Y + 1) := by
            rw [sum_const, smul_eq_mul]
        _ ≤ ∑ i ∈ (range (P.card - 1)).filter (fun i => ¬ len P i ≤ Y), len P i :=
            sum_le_sum (fun i hi => by simp only [mem_filter] at hi; omega)
        _ ≤ ∑ i ∈ range (P.card - 1), len P i := sum_le_sum_of_subset (filter_subset _ _)
        _ ≤ b - a := sum_len_le hP (by omega)
    have h2 : b - a < (Y + 1) * s := by
      have := Nat.lt_div_mul_add (a := b - a) (show 0 < s by omega)
      rw [hY]; linarith
    by_contra hc
    have hc' := not_lt.mp hc
    have := Nat.mul_le_mul_left (Y + 1) hc'
    nlinarith
  have hexY : ∀ k ≤ K, 2 * k + s + 1 ≤
      ((range (P.card - 1)).filter (fun i => len P i ≤ Y)).card := by
    intro k hk
    have := card_filter_add_card_filter_not (s := range (P.card - 1))
      (fun i => len P i ≤ Y)
    rw [hGc] at this
    omega
  have hex : ∀ k ≤ K, ∃ y, 2 * k + s + 1 ≤
      ((range (P.card - 1)).filter (fun i => len P i ≤ y)).card := fun k hk => ⟨Y, hexY k hk⟩
  set yk : ℕ → ℕ := fun k =>
    if hk : k ≤ K then Nat.find (hex k hk) else 0 with hyk
  have hyk_spec : ∀ k ≤ K, 2 * k + s + 1 ≤
      ((range (P.card - 1)).filter (fun i => len P i ≤ yk k)).card := by
    intro k hk; simp only [hyk, dif_pos hk]; exact Nat.find_spec (hex k hk)
  have hyk_Y : ∀ k ≤ K, yk k ≤ Y := by
    intro k hk; simp only [hyk, dif_pos hk]; exact Nat.find_min' _ (hexY k hk)
  have hyk_ba : ∀ k ≤ K, yk k ≤ b - a := by
    intro k hk; simp only [hyk, dif_pos hk]
    apply Nat.find_min'
    have : (range (P.card - 1)).filter (fun i => len P i ≤ b - a) = range (P.card - 1) :=
      filter_true_of_mem hlenle
    rw [this, hGc]; omega
  have hyk_min : ∀ k ≤ K, 0 < yk k → ((range (P.card - 1)).filter
      (fun i => len P i ≤ yk k - 1)).card < 2 * k + s + 1 := by
    intro k hk hpos
    have := Nat.find_min (hex k hk) (show Nat.find (hex k hk) - 1 < Nat.find (hex k hk) by
      simp only [hyk, dif_pos hk] at hpos; omega)
    simp only [hyk, dif_pos hk]
    omega
  -- per-k estimate
  have hper : ∀ k ∈ range (K + 1), (val Q o (t - k - 1) : ℝ) * Real.log p ≤
      phiL x (yk k) + ((Y / B : ℕ) : ℝ) * Real.log x := by
    intro k hk
    rw [mem_range] at hk
    have hkt : k < t := by omega
    set P' := chain Q o (t - k)
    have hP'P : P' ⊆ P := chain_mono (o := o) (by omega) ht
    have hcard : (P \ P').card = k := by
      rw [card_sdiff_of_subset hP'P, hPc, (chain_basic (Q := Q) (o := o) (t - k) (by omega)).2]
      omega
    have hm : ∀ n ∈ P', p ^ (val Q o (t - k - 1)) ∣ n ! + 1 := by
      intro n hn
      have hn' : n ∈ chain Q o (t - k - 1 + 1) := by rwa [show t - k - 1 + 1 = t - k by omega]
      have h1 := val_le_of_mem (o := o) (show t - k - 1 < Q.card by omega) hn'
      exact (pow_dvd_pow p h1).trans (hdiv n (hPQ (hP'P hn)))
    have h := per_k hp hx hbx hbp hP hm (y := yk k) (R := s) (B := B)
      ((hyk_ba k (by omega)).trans (by omega)) hBpos hBE
      (by rw [hcard]; exact hyk_spec k (by omega))
    have hmono : ((yk k / B : ℕ) : ℝ) ≤ ((Y / B : ℕ) : ℝ) := by
      exact_mod_cast Nat.div_le_div_right (hyk_Y k (by omega))
    have hlx : 0 ≤ Real.log x := Real.log_nonneg (by exact_mod_cast hx)
    nlinarith
  -- pairing and Jensen
  have hlayer : 2 * ∑ k ∈ range (K + 1), phiL x (yk k) ≤
      ∑ i ∈ range (P.card - 1), phiL x (len P i) := by
    apply layer_phiL (fun i => (len P i : ℝ)) (fun k => (yk k : ℝ)) (fun _ => Nat.cast_nonneg _)
    · intro i hi
      exact ⟨Nat.cast_nonneg _, by exact_mod_cast (hlenle i hi).trans (by omega)⟩
    · intro j hj
      show 2 * (K + 1 - j) ≤ ((range (P.card - 1)).filter (fun i => (yk j : ℝ) ≤ (len P i : ℝ))).card
      have hjK : j ≤ K := by omega
      have := card_filter_add_card_filter_not (s := range (P.card - 1))
        (fun i => len P i ≤ yk j - 1)
      rw [hGc] at this
      have hfeq : (range (P.card - 1)).filter (fun i => ¬ len P i ≤ yk j - 1) ⊆
          (range (P.card - 1)).filter (fun i => (yk j : ℝ) ≤ (len P i : ℝ)) := by
        intro i hi
        simp only [mem_filter] at hi ⊢
        refine ⟨hi.1, ?_⟩
        exact_mod_cast (show yk j ≤ len P i by omega)
      rcases Nat.eq_zero_or_pos (yk j) with h0 | hpos
      · have : (range (P.card - 1)).filter (fun i => (yk j : ℝ) ≤ (len P i : ℝ)) =
            range (P.card - 1) := filter_true_of_mem (fun i _ => by rw [h0]; simp)
        rw [this, hGc]; omega
      · have := hyk_min j hjK hpos
        have := card_le_card hfeq
        omega
  have hjensen : ∑ i ∈ range (P.card - 1), phiL x (len P i) ≤
      ((b - a : ℕ) : ℝ) * Real.log t + x := by
    have hG1 : 1 ≤ (range (P.card - 1)).card := by rw [hGc]; omega
    have hj := jensen_phiL (range (P.card - 1)) (fun i => (len P i : ℝ)) (x := x)
      (Λ := ((b - a : ℕ) : ℝ)) (by exact_mod_cast hx) (fun _ _ => Nat.cast_nonneg _)
      (by exact_mod_cast sum_len_le hP (by omega)) (by exact_mod_cast (show b - a ≤ x by omega)) hG1
    refine hj.trans ?_
    rw [hGc]
    have : Real.log ((t - 1 : ℕ) : ℝ) ≤ Real.log t := by
      rcases Nat.eq_zero_or_pos (t - 1) with h0 | hpos
      · rw [h0]; simp; exact Real.log_natCast_nonneg t
      · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast Nat.sub_le t 1)
    have hΛ0 : (0 : ℝ) ≤ ((b - a : ℕ) : ℝ) := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left this hΛ0
    linarith
  -- the cost term
  have hcost : ((K + 1 : ℕ) : ℝ) * ((Y / B : ℕ) : ℝ) ≤ ((b - a : ℕ) : ℝ) / W := by
    have hKW : (K + 1) * W ≤ s * B := by
      have h1 : t < 2 * q * (s + 1) := by
        have := Nat.lt_div_mul_add (a := t) (show 0 < 2 * q by omega)
        rw [← hs] at this
        nlinarith
      have h2 : K + 1 ≤ q * (s + 1) + 1 := by
        have h3 : K ≤ t / 2 := Nat.sub_le _ _
        have h4 : t / 2 * 2 ≤ t := Nat.div_mul_le_self t 2
        nlinarith
      have h3 : (q * (s + 1) + 1) * W ≤ s * B := by
        have : (q * (s + 1) + 1) ≤ (2 * q + 1) * s := by nlinarith
        calc (q * (s + 1) + 1) * W ≤ (2 * q + 1) * s * W := Nat.mul_le_mul_right _ this
          _ = s * ((2 * q + 1) * W) := by ring
          _ ≤ s * B := Nat.mul_le_mul_left _ (Nat.le_of_succ_le hB1)
      calc (K + 1) * W ≤ (q * (s + 1) + 1) * W := Nat.mul_le_mul_right _ h2
        _ ≤ s * B := h3
    have hYB : Y / B ≤ (b - a) / (s * B) := by
      rw [hY, Nat.div_div_eq_div_mul]
    have hnat : (K + 1) * (Y / B) * W ≤ b - a := by
      calc (K + 1) * (Y / B) * W = (K + 1) * W * (Y / B) := by ring
        _ ≤ s * B * ((b - a) / (s * B)) := Nat.mul_le_mul hKW hYB
        _ ≤ b - a := by rw [mul_comm]; exact Nat.div_mul_le_self _ _
    have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
    rw [le_div_iff₀ hWpos]
    exact_mod_cast hnat
  -- assemble
  have hsum := sum_le_sum hper
  rw [← sum_mul, sum_add_distrib, sum_const, card_range, nsmul_eq_mul] at hsum
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by exact_mod_cast hx)
  have hc2 := mul_le_mul_of_nonneg_right hcost hlx
  have e : Real.log p * ∑ k ∈ range (K + 1), (val Q o (t - k - 1) : ℝ) =
      (∑ k ∈ range (K + 1), (val Q o (t - k - 1) : ℝ)) * Real.log p := mul_comm _ _
  rw [e]
  have e2 : ((K + 1 : ℕ) : ℝ) * (((Y / B : ℕ) : ℝ) * Real.log x) =
      ((K + 1 : ℕ) : ℝ) * ((Y / B : ℕ) : ℝ) * Real.log x := by ring
  rw [e2] at hsum
  linarith

end block

end LaneCLai


/-! Lane C, Erdős 977 (Lai) H2 — summing Lemma 2.7 over geometric blocks (Lai, Section 3),
as a strong induction on the number of ranks. -/

namespace LaneCLai
open Finset Real
open scoped Nat

/-- The bound `Φ(t) = Λ/(4L) (log t)² + β log t + Z`. -/
noncomputable def Φ (Λ x L W t₀ t : ℝ) : ℝ :=
  Λ / (4 * L) * Real.log t ^ 2 + ((x / 2 + Λ * Real.log x / W) / L + Λ / 4) * Real.log t +
    (Real.log 2 + x * Real.log x + Λ * Real.log x * (1 + Real.log t₀))

lemma Φ_mono {Λ x L W t₀ u v : ℝ} (hΛ : 0 ≤ Λ) (hx : 1 ≤ x) (hL : 0 < L) (hW : 0 < W)
    (hu : 1 ≤ u) (huv : u ≤ v) : Φ Λ x L W t₀ u ≤ Φ Λ x L W t₀ v := by
  unfold Φ
  have h1 := Real.log_le_log (by linarith) huv
  have h0 := Real.log_nonneg hu
  have hlx := Real.log_nonneg hx
  have hα : 0 ≤ Λ / (4 * L) := div_nonneg hΛ (by linarith)
  have hβ : 0 ≤ (x / 2 + Λ * Real.log x / W) / L + Λ / 4 :=
    add_nonneg (div_nonneg (add_nonneg (by linarith) (div_nonneg (mul_nonneg hΛ hlx) hW.le)) hL.le)
      (by linarith)
  have : Real.log u ^ 2 ≤ Real.log v ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left this hα, mul_le_mul_of_nonneg_left h1 hβ]

lemma Φ_step {Λ x L W t₀ t ρ : ℝ} (hL : 0 < L) (hW : 0 < W) (hρ : Real.log ρ = -L)
    (ht : 0 < t) (hρ0 : 0 < ρ) :
    Φ Λ x L W t₀ (ρ * t) + (Λ * Real.log t + x) / 2 + Λ / W * Real.log x = Φ Λ x L W t₀ t := by
  unfold Φ
  rw [Real.log_mul hρ0.ne' ht.ne', hρ]
  have hL' : L ≠ 0 := hL.ne'
  have hW' : W ≠ 0 := hW.ne'
  first | (first | (field_simp; ring) | field_simp) | field_simp

section main
variable {p a b x : ℕ} {Q : Finset ℕ} {o : ℕ → ℕ}

set_option maxHeartbeats 2000000 in
lemma base_bound (hp : p.Prime) (ha : 1 ≤ a) (hx : 2 ≤ x) (hbx : b ≤ x) (hbp : b < p)
    (hQ : Q ⊆ Icc a b) (hdiv : ∀ n ∈ Q, p ^ (o n) ∣ n ! + 1) {t : ℕ} (ht : t ≤ Q.card) :
    Real.log p * ∑ j ∈ range t, (val Q o j : ℝ) ≤
      Real.log 2 + x * Real.log x + ((b - a : ℕ) : ℝ) * Real.log x * (1 + Real.log t) := by
  classical
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hΛ : (0 : ℝ) ≤ ((b - a : ℕ) : ℝ) := Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos t with rfl | htpos
  · simp only [range_zero, sum_empty, mul_zero]
    have := Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)
    have := mul_nonneg (show (0:ℝ) ≤ x by positivity) hlx
    have := mul_nonneg (mul_nonneg hΛ hlx) (show (0:ℝ) ≤ 1 + Real.log ((0 : ℕ) : ℝ) by simp)
    linarith
  -- the top value
  have hkey : ∀ n ∈ Q, (o n : ℝ) * Real.log p ≤ Real.log 2 + x * Real.log x := by
    intro n hnQ
    have hnb : n ≤ x := (mem_Icc.mp (hQ hnQ)).2.trans hbx
    have hd := Nat.le_of_dvd (by positivity) (hdiv n hnQ)
    have h2 : n ! + 1 ≤ 2 * x ^ x := by
      have := (Nat.factorial_le_pow n).trans (Nat.pow_le_pow_left hnb n)
      have := Nat.pow_le_pow_right (show 1 ≤ x by omega) (show n ≤ x from hnb)
      have : 1 ≤ x ^ x := Nat.one_le_pow _ _ (by omega)
      omega
    have h3 : ((p : ℝ) ^ (o n)) ≤ 2 * (x : ℝ) ^ x := by exact_mod_cast hd.trans h2
    have h4 := Real.log_le_log (pow_pos (by exact_mod_cast hp.pos) _) h3
    rw [Real.log_pow, Real.log_mul (by norm_num) (pow_pos (by linarith) _).ne', Real.log_pow] at h4
    linarith
  have h0 : (val Q o 0 : ℝ) * Real.log p ≤ Real.log 2 + x * Real.log x := by
    obtain ⟨_, hne⟩ := chain_succ (o := o) (show 0 < Q.card by omega)
    have hn := (nextPt_spec (o := o) hne).1
    rw [mem_sdiff] at hn
    exact hkey _ hn.1
  -- the other values: a gap of length at most `(b-a)/j`
  have hj : ∀ j ∈ range (t - 1), (val Q o (j + 1) : ℝ) * Real.log p ≤
      ((b - a : ℕ) : ℝ) * Real.log x * (1 / ((j : ℝ) + 1)) := by
    intro j hj
    rw [mem_range] at hj
    set P := chain Q o (j + 2)
    have hPQ : P ⊆ Q := (chain_basic (Q := Q) (o := o) (j + 2) (by omega)).1
    have hPc : P.card = j + 2 := (chain_basic (Q := Q) (o := o) (j + 2) (by omega)).2
    have hP : P ⊆ Icc a b := hPQ.trans hQ
    have hsum := sum_len_le hP (by omega)
    rw [hPc] at hsum
    obtain ⟨i, hi, hile⟩ : ∃ i ∈ range (j + 1), len P i * (j + 1) ≤ b - a := by
      by_contra hc
      push_neg at hc
      have : ∑ i ∈ range (j + 1), (b - a) < ∑ i ∈ range (j + 1), len P i * (j + 1) :=
        sum_lt_sum_of_nonempty (by simp) hc
      rw [sum_const, card_range, smul_eq_mul, ← sum_mul] at this
      have h2 := Nat.mul_le_mul_right (j + 1) hsum
      simp only [show j + 2 - 1 = j + 1 by omega] at h2
      nlinarith
    rw [mem_range] at hi
    have hm : ∀ n ∈ P, p ^ (val Q o (j + 1)) ∣ n ! + 1 := by
      intro n hn
      have h1 := val_le_of_mem (o := o) (show j + 1 < Q.card by omega) hn
      exact (pow_dvd_pow p h1).trans (hdiv n (hPQ hn))
    have hdv := gap_dvd hp hm (show i + 1 < P.card by omega) (pos_mem (by omega)) (pos_mem (by omega))
    have hu : 1 ≤ pos P i := (pos_mem_Icc hP (show i < P.card by omega)).1.trans' ha
    have hpx : pos P i + len P i ≤ x := by
      rw [pos_add_len (show i + 1 < P.card by omega)]
      exact (pos_mem_Icc hP (show i + 1 < P.card by omega)).2.trans hbx
    have key := one_block_log hu (len_pos (show i + 1 < P.card by omega)) hdv hpx hp.one_lt
    have hl : (len P i : ℝ) ≤ ((b - a : ℕ) : ℝ) * (1 / ((j : ℝ) + 1)) := by
      rw [mul_one_div, le_div_iff₀ (by positivity)]
      exact_mod_cast hile
    have := mul_le_mul_of_nonneg_right hl hlx
    linarith
  -- sum up
  have hsplit : ∑ j ∈ range t, (val Q o j : ℝ) =
      (val Q o 0 : ℝ) + ∑ j ∈ range (t - 1), (val Q o (j + 1) : ℝ) := by
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    rw [sum_range_succ', add_comm]; simp
  have hharm : ∑ j ∈ range (t - 1), (1 / ((j : ℝ) + 1)) ≤ 1 + Real.log t := by
    have h := harmonic_le_one_add_log (t - 1)
    have : ((harmonic (t - 1) : ℚ) : ℝ) = ∑ j ∈ range (t - 1), (1 / ((j : ℝ) + 1)) := by
      simp [harmonic]
    rw [this] at h
    refine h.trans ?_
    have : Real.log ((t - 1 : ℕ) : ℝ) ≤ Real.log t := by
      rcases Nat.eq_zero_or_pos (t - 1) with h0 | hpos
      · rw [h0]; simp; exact Real.log_natCast_nonneg t
      · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast Nat.sub_le t 1)
    linarith
  rw [hsplit, mul_add, mul_sum]
  have h2 := sum_le_sum hj
  rw [← mul_sum] at h2
  have h3 := mul_le_mul_of_nonneg_left hharm (mul_nonneg hΛ hlx)
  have h4 : ∑ j ∈ range (t - 1), Real.log p * (val Q o (j + 1) : ℝ) =
      ∑ j ∈ range (t - 1), (val Q o (j + 1) : ℝ) * Real.log p := by
    apply sum_congr rfl; intro j _; ring
  rw [h4]
  linarith

set_option maxHeartbeats 4000000 in
/-- The per-prime estimate: `log p · ∑_{n ∈ Q} o n ≤ Φ(|Q|)`. -/
theorem lai_local (hp : p.Prime) (ha : 1 ≤ a) (hx : 2 ≤ x) (hbx : b ≤ x) (hbp : b < p)
    (hab : a ≤ b) (hQ : Q ⊆ Icc a b) (hdiv : ∀ n ∈ Q, p ^ (o n) ∣ n ! + 1) {q W : ℕ}
    (hq : 3 ≤ q) (hW : 1 ≤ W) :
    Real.log p * ∑ n ∈ Q, (o n : ℝ) ≤
      Φ ((b - a : ℕ) : ℝ) x (Real.log (2 * q / (q + 2))) W
        (2 * q * (2 * Nat.log 2 x + 2) * ((2 * q + 1) * W + 1) : ℕ) Q.card := by
  classical
  set t₀ := 2 * q * (2 * Nat.log 2 x + 2) * ((2 * q + 1) * W + 1) with ht₀
  set L := Real.log (2 * q / (q + 2)) with hLdef
  set Λ : ℝ := ((b - a : ℕ) : ℝ)
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hL : 0 < L := Real.log_pos (by rw [lt_div_iff₀ (by linarith)]; linarith)
  set ρ : ℝ := (q + 2) / (2 * q) with hρdef
  have hρ0 : 0 < ρ := by rw [hρdef]; exact div_pos (by linarith) (by linarith)
  have hρL : Real.log ρ = -L := by
    rw [hρdef, hLdef, ← Real.log_inv, inv_div]
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  have hWR : (0 : ℝ) < W := by exact_mod_cast hW
  have hΛ : 0 ≤ Λ := Nat.cast_nonneg _
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have ht0big : 4 ≤ t₀ := by
    rw [ht₀]
    have : 1 ≤ (2 * q + 1) * W + 1 := by omega
    have : 2 ≤ 2 * Nat.log 2 x + 2 := by omega
    have : 6 ≤ 2 * q := by omega
    calc 4 ≤ 6 * 2 * 1 := by norm_num
      _ ≤ 2 * q * (2 * Nat.log 2 x + 2) * ((2 * q + 1) * W + 1) := by gcongr
  -- strong induction on the number of ranks
  have main : ∀ t ≤ Q.card, Real.log p * ∑ j ∈ range t, (val Q o j : ℝ) ≤
      Φ Λ x L W t₀ t := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht
      by_cases hsmall : t ≤ t₀
      · refine (base_bound hp ha hx hbx hbp hQ hdiv ht).trans ?_
        have h1 : Real.log 2 + x * Real.log x + Λ * Real.log x * (1 + Real.log t) ≤
            Real.log 2 + x * Real.log x + Λ * Real.log x * (1 + Real.log t₀) := by
          rcases Nat.eq_zero_or_pos t with h0 | hpos
          · rw [h0]; simp
            have := Real.log_natCast_nonneg t₀
            nlinarith [mul_nonneg hΛ hlx]
          · have := Real.log_le_log (by exact_mod_cast hpos) (show (t : ℝ) ≤ t₀ by exact_mod_cast hsmall)
            nlinarith [mul_nonneg hΛ hlx]
        refine h1.trans ?_
        unfold Φ
        rcases Nat.eq_zero_or_pos t with h0 | hpos
        · rw [h0]; simp
        · have := Real.log_natCast_nonneg t
          have : 0 ≤ (x / 2 + Λ * Real.log x / W) / L + Λ / 4 :=
            add_nonneg (div_nonneg (add_nonneg (by linarith)
              (div_nonneg (mul_nonneg hΛ hlx) hWR.le)) hL.le) (by linarith)
          have : 0 ≤ Λ / (4 * L) * Real.log t ^ 2 :=
            mul_nonneg (div_nonneg hΛ (by linarith)) (sq_nonneg _)
          nlinarith
      push_neg at hsmall
      set s := t / (2 * q)
      set K := t / 2 - 2 * s
      have hsq : s * (2 * q) ≤ t := Nat.div_mul_le_self t (2 * q)
      have h4s : 4 * s ≤ t := by nlinarith
      have hK : K + 1 ≤ t := by omega
      set t' := t - (K + 1)
      have hsplit : ∑ j ∈ range t, (val Q o j : ℝ) = ∑ j ∈ range t', (val Q o j : ℝ) +
          ∑ k ∈ range (K + 1), (val Q o (t - k - 1) : ℝ) := by
        rw [← sum_range_add_sum_Ico _ (show t' ≤ t by omega), sum_Ico_eq_sum_range,
          show t - t' = K + 1 by omega]
        congr 1
        rw [← sum_range_reflect (fun k => (val Q o (t' + k) : ℝ)) (K + 1)]
        apply sum_congr rfl
        intro k hk
        rw [mem_range] at hk
        rw [show t' + (K + 1 - 1 - k) = t - k - 1 by omega]
      have hblock : Real.log p * ∑ k ∈ range (K + 1), (val Q o (t - k - 1) : ℝ) ≤
          ((b - a : ℕ) * Real.log t + x) / 2 + ((b - a : ℕ) : ℝ) / W * Real.log x :=
        block (o := o) hp (by omega) hbx hbp hab hQ hdiv (q := q) (t := t) (W := W)
          hq hW ht hsmall.le
      have hIH := ih t' (by omega) (by omega)
      have ht'1 : 1 ≤ t' := by omega
      have ht'ρ : (t' : ℝ) ≤ ρ * t := by
        have h1 : t' + t / 2 ≤ t / 2 + 2 * s + t / 2 := by omega
        have h2 : (t / 2 : ℕ) * 2 ≤ t := Nat.div_mul_le_self t 2
        have h3 : t' ≤ t / 2 + 2 * s := by omega
        have h4 : (t' : ℝ) ≤ (t / 2 : ℕ) + 2 * (s : ℝ) := by exact_mod_cast h3
        have h5 : ((t / 2 : ℕ) : ℝ) * 2 ≤ t := by exact_mod_cast h2
        have h6 : (s : ℝ) * (2 * q) ≤ t := by exact_mod_cast hsq
        have hq0 : (0 : ℝ) < q := by linarith
        have : ρ * t = t / 2 + t / q := by rw [hρdef]; first | (field_simp; ring) | field_simp
        rw [this]
        have : 2 * (s : ℝ) ≤ t / q := by rw [le_div_iff₀ hq0]; linarith
        linarith
      have hmono := Φ_mono (Λ := Λ) (x := x) (L := L) (W := W) (t₀ := t₀) hΛ hx1 hL hWR
        (show (1 : ℝ) ≤ t' by exact_mod_cast ht'1) ht'ρ
      have hstep := Φ_step (Λ := Λ) (x := x) (W := W) (t₀ := t₀) (t := t) hL hWR hρL
        (by exact_mod_cast (show 0 < t by omega)) hρ0
      rw [hsplit, mul_add]
      linarith
  have hs : (∑ n ∈ Q, (o n : ℝ)) = ∑ j ∈ range Q.card, (val Q o j : ℝ) := by
    have := sum_chain (o := o) Q.card le_rfl
    rw [chain_full] at this
    exact_mod_cast this
  rw [hs]
  exact main Q.card le_rfl

end main

end LaneCLai


/-! Lane C, Erdős 977 (Lai) H2 — final assembly: the per-prime estimate on `[N, (1+d)N]`. -/

namespace LaneCLai
open Finset Real Filter
open scoped Nat Topology

/-- `log (2q/(q+2)) → log 2`. -/
lemma tendsto_Lq : Tendsto (fun q : ℕ => Real.log (2 * q / (q + 2))) atTop (𝓝 (Real.log 2)) := by
  have h : Tendsto (fun q : ℕ => (2 : ℝ) * q / (q + 2)) atTop (𝓝 2) := by
    have h1 : Tendsto (fun q : ℕ => (2 : ℝ) - 4 / ((q : ℝ) + 2)) atTop (𝓝 (2 - 0)) := by
      refine tendsto_const_nhds.sub ?_
      exact tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    rw [sub_zero] at h1
    refine h1.congr' (Eventually.of_forall fun q => ?_)
    have : (q : ℝ) + 2 ≠ 0 := by positivity
    first | (field_simp; ring) | field_simp
  exact (Real.continuousAt_log (by norm_num)).tendsto.comp h

lemma exists_q (η : ℝ) (hη : 0 < η) :
    ∃ q : ℕ, 3 ≤ q ∧ 0 < Real.log (2 * q / (q + 2)) ∧
      1 / (9 * Real.log (2 * q / (q + 2))) ≤ 1 / (9 * Real.log 2) + η / 4 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h0 : Tendsto (fun q : ℕ => 9 * Real.log (2 * q / (q + 2))) atTop (𝓝 (9 * Real.log 2)) :=
    tendsto_const_nhds.mul tendsto_Lq
  have h1' := h0.inv₀ (by positivity)
  have h1 : Tendsto (fun q : ℕ => 1 / (9 * Real.log (2 * q / (q + 2)))) atTop
      (𝓝 (1 / (9 * Real.log 2))) := by
    simp only [one_div]; exact h1'
  have h2 := h1.eventually (ge_mem_nhds (show 1 / (9 * Real.log 2) < 1 / (9 * Real.log 2) + η / 4
    by linarith))
  have h3 := (tendsto_Lq.eventually (lt_mem_nhds hl2))
  obtain ⟨q, hq⟩ := (h2.and (h3.and (eventually_ge_atTop 3))).exists
  exact ⟨q, hq.2.2, hq.2.1, hq.1⟩

lemma card_Q_le {p : ℕ} (hp : p.Prime) {Q : Finset ℕ} {a b x : ℕ} (hQ : Q ⊆ Icc a b)
    (hb : b < p) (hdiv : ∀ n ∈ Q, p ∣ n ! + 1) (hbx : b ≤ x) (hab : a ≤ b) (hx : 1 ≤ x) :
    (Q.card : ℝ) ≤ 6 * (x : ℝ) ^ ((2 : ℝ) / 3) := by
  set H := ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ + 1 with hH
  have hH1 : 1 ≤ H := by omega
  have h := card_LS hp hQ hb hdiv H hH1
  have hx0 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  set c := (x : ℝ) ^ ((1 : ℝ) / 3) with hcdef
  have hc1 : 1 ≤ c := by rw [hcdef]; exact Real.one_le_rpow hx0 (by norm_num)
  have hc3 : c ^ 3 = x := by
    rw [hcdef, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have hc2 : (x : ℝ) ^ ((2 : ℝ) / 3) = c ^ 2 := by
    rw [hcdef, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have hHc : c ≤ H := by
    have := Nat.lt_floor_add_one c; push_cast [hH]; linarith
  have hHc' : (H : ℝ) ≤ c + 1 := by
    have := Nat.floor_le (show 0 ≤ c by linarith); push_cast [hH]; linarith
  have hR : (Q.card : ℝ) * H ≤ (H : ℝ) * H * H + ((b - a : ℕ) : ℝ) + H := by exact_mod_cast h
  have hba : ((b - a : ℕ) : ℝ) ≤ x := by exact_mod_cast (show b - a ≤ x by omega)
  rw [hc2]
  have hHpos : (0 : ℝ) < H := by linarith
  have : (Q.card : ℝ) ≤ (H : ℝ) * H + x / H + 1 := by
    rw [← sub_nonneg]
    have : (H : ℝ) * H + x / H + 1 - Q.card = ((H : ℝ) * H * H + x + H - Q.card * H) / H := by
      first | (field_simp; ring) | field_simp
    rw [this]; apply div_nonneg _ hHpos.le; linarith
  have hxH : (x : ℝ) / H ≤ c ^ 2 := by
    rw [div_le_iff₀ hHpos, ← hc3]; nlinarith
  have hHH : (H : ℝ) * H ≤ (c + 1) * (c + 1) := mul_le_mul hHc' hHc' hHpos.le (by linarith)
  nlinarith [mul_nonneg (sub_nonneg.mpr hc1) (show (0:ℝ) ≤ c by linarith)]

lemma Φ_le {Λ M x L W t₀ t : ℝ} (hΛ : 0 ≤ Λ) (hΛM : Λ ≤ M) (hx : 1 ≤ x) (hL : 0 < L)
    (hW : 0 < W) (ht : 1 ≤ t) (ht₀ : 1 ≤ t₀) : Φ Λ x L W t₀ t ≤ Φ M x L W t₀ t := by
  unfold Φ
  have h1 := Real.log_nonneg ht
  have h2 := Real.log_nonneg hx
  have h3 := Real.log_nonneg ht₀
  have e1 : Λ / (4 * L) * Real.log t ^ 2 ≤ M / (4 * L) * Real.log t ^ 2 :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hΛM (by linarith)) (by positivity)
  have e2a : Λ * Real.log x / W ≤ M * Real.log x / W :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hΛM h2) hW.le
  have e2b : (x / 2 + Λ * Real.log x / W) / L ≤ (x / 2 + M * Real.log x / W) / L :=
    div_le_div_of_nonneg_right (by linarith) hL.le
  have e2 : ((x / 2 + Λ * Real.log x / W) / L + Λ / 4) * Real.log t ≤
      ((x / 2 + M * Real.log x / W) / L + M / 4) * Real.log t :=
    mul_le_mul_of_nonneg_right (by linarith) h1
  have e3 : Λ * Real.log x * (1 + Real.log t₀) ≤ M * Real.log x * (1 + Real.log t₀) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hΛM h2) (by linarith)
  linarith

set_option maxHeartbeats 4000000 in
theorem H2_main (d : ℝ) (hd : 0 < d) (hd1 : d < 1) (η : ℝ) (hη : 0 < η) : ∀ᶠ N : ℕ in atTop,
    ∀ p : ℕ, p.Prime → N < p →
      (∑ n ∈ Icc N ⌊(1 + d) * N⌋₊, ((n.factorial + 1).factorization p : ℝ) * Real.log p) ≤
        (1 / (9 * Real.log 2) + η) * (Icc N ⌊(1 + d) * N⌋₊).card * (Real.log N) ^ 2 := by
  classical
  obtain ⟨q, hq3, hL, hqL⟩ := exists_q η hη
  set L := Real.log (2 * q / (q + 2)) with hLdef
  set κ := 1 / (9 * Real.log 2) with hκdef
  set W : ℕ := ⌈16 / (L * η)⌉₊ + 1 with hWdef
  have hW1 : 1 ≤ W := by omega
  have hWR : (0 : ℝ) < W := by exact_mod_cast hW1
  have hWL : 1 / (W * L) ≤ η / 16 := by
    have h1 : 16 / (L * η) ≤ W := by
      have := Nat.le_ceil (16 / (L * η)); push_cast [hWdef]; linarith
    rw [div_le_iff₀ (by positivity)] at h1
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set C₁ : ℝ := 4 * q * ((2 * q + 1) * W + 1) with hC₁
  have hC₁pos : 1 ≤ C₁ := by
    have : (3 : ℝ) ≤ q := by exact_mod_cast hq3
    have : (1 : ℝ) ≤ W := by exact_mod_cast hW1
    rw [hC₁]
    nlinarith [mul_nonneg (show (0:ℝ) ≤ q by linarith)
      (mul_nonneg (show (0:ℝ) ≤ 2 * q + 1 by linarith) (show (0:ℝ) ≤ W by linarith))]
  -- eventualities in `ℓ = log N`
  have hℓ : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog : ∀ᶠ ℓ : ℝ in atTop, Real.log (2 * ℓ + 3) ≤ η / 64 * (2 * ℓ + 3) := by
    have := Real.isLittleO_log_id_atTop.def (show 0 < η / 64 by positivity)
    have ht : Tendsto (fun ℓ : ℝ => 2 * ℓ + 3) atTop atTop :=
      tendsto_atTop_add_const_right _ 3 (tendsto_id.const_mul_atTop (by norm_num))
    filter_upwards [ht.eventually this, ht.eventually (eventually_ge_atTop 1)] with ℓ h1 h2
    simp only [id, Real.norm_eq_abs] at h1
    rw [abs_of_nonneg (Real.log_nonneg h2), abs_of_nonneg (by linarith)] at h1
    exact h1
  -- the big polynomial inequality, divided by `M = |T|`
  have hpoly : ∀ᶠ ℓ : ℝ in atTop,
      (κ + η / 4) * (ℓ + 4) ^ 2 + η / 16 * (ℓ + 4) ^ 2 + (2 / (d * L) + 1) * (ℓ + 4) +
        (1 + 4 / d * (ℓ + 1)) + (ℓ + 1) * (1 + Real.log C₁ + Real.log (2 * ℓ + 3)) ≤
        (κ + η) * ℓ ^ 2 := by
    have hlC : 0 ≤ Real.log C₁ := Real.log_nonneg hC₁pos
    have hκ : 0 < κ := by
      rw [hκdef]; have := Real.log_pos (show (1:ℝ) < 2 by norm_num); positivity
    set D := 1 + 2 / (d * L) + 4 / d + Real.log C₁ with hDdef
    have hA : 0 ≤ 2 / (d * L) := by positivity
    have hB : 0 ≤ 4 / d := by positivity
    have hD1 : 1 ≤ D := by linarith
    filter_upwards [hlog, eventually_ge_atTop (1 : ℝ),
      eventually_ge_atTop ((10000 * (κ + η + 1) * D) / η)] with ℓ h1 h2 h3
    have h3' : 10000 * (κ + η + 1) * D ≤ η * ℓ := by
      rwa [div_le_iff₀ hη, mul_comm ℓ] at h3
    have hℓ0 : 0 ≤ ℓ := by linarith
    have hbig : 10000 * (κ + η + 1) * D * ℓ ≤ η * ℓ * ℓ := mul_le_mul_of_nonneg_right h3' hℓ0
    have hDℓ : (κ + η + 1) * ℓ ≤ (κ + η + 1) * D * ℓ := by
      have : (κ + η + 1) * 1 ≤ (κ + η + 1) * D := mul_le_mul_of_nonneg_left hD1 (by positivity)
      nlinarith
    have hκℓ : κ ≤ κ * ℓ := by nlinarith
    have hηℓ : η ≤ η * ℓ := by nlinarith
    have hDl : D ≤ D * ℓ := by nlinarith
    have l1 : (2 / (d * L) + 1) * (ℓ + 4) ≤ D * (ℓ + 4) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have l2 : 4 / d * (ℓ + 1) ≤ D * (ℓ + 1) := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have l3 : (ℓ + 1) * (1 + Real.log C₁) ≤ (ℓ + 1) * D :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have l4 : (ℓ + 1) * Real.log (2 * ℓ + 3) ≤ η / 64 * ((ℓ + 1) * (2 * ℓ + 3)) := by
      have := mul_le_mul_of_nonneg_left h1 (show 0 ≤ ℓ + 1 by linarith)
      linarith
    have hsplit : (ℓ + 1) * (1 + Real.log C₁ + Real.log (2 * ℓ + 3)) =
        (ℓ + 1) * (1 + Real.log C₁) + (ℓ + 1) * Real.log (2 * ℓ + 3) := by ring
    rw [hsplit]
    have hD0 : 0 ≤ D := by linarith
    have p1 := mul_nonneg hη.le hℓ0
    have p2 := mul_nonneg hκ.le hℓ0
    have p3 := mul_nonneg (mul_nonneg hκ.le hD0) hℓ0
    have p4 := mul_nonneg (mul_nonneg hη.le hD0) hℓ0
    have p5 := mul_nonneg hD0 hℓ0
    have p6 : 1 * ℓ ≤ D * ℓ := mul_le_mul_of_nonneg_right hD1 hℓ0
    linarith
  filter_upwards [hℓ.eventually hpoly, eventually_ge_atTop 3] with N hN hN3
  intro p hp hNp
  set x := ⌊(1 + d) * N⌋₊ with hxdef
  set T := Icc N x
  have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hx1 : ((1 + d) * N) - 1 < x := Nat.sub_one_lt_floor _
  have hx2 : (x : ℝ) ≤ (1 + d) * N := Nat.floor_le (by positivity)
  have hNx : N ≤ x := by
    apply Nat.le_floor; push_cast; nlinarith
  have hx2' : 2 ≤ x := by omega
  set b := min x (p - 1)
  have hbx : b ≤ x := min_le_left _ _
  have hbp : b < p := by have := hp.pos; omega
  have hab : N ≤ b := by have := hp.pos; omega
  set o : ℕ → ℕ := fun n => (n ! + 1).factorization p
  set Q := (Icc N b).filter (fun n => p ∣ n ! + 1)
  have hQ : Q ⊆ Icc N b := filter_subset _ _
  have hdivQ : ∀ n ∈ Q, p ^ (o n) ∣ n ! + 1 := fun n _ => Nat.ordProj_dvd _ _
  -- the sum over `T` is the sum over `Q`
  have hsumeq : ∑ n ∈ T, ((n ! + 1).factorization p : ℝ) * Real.log p =
      Real.log p * ∑ n ∈ Q, (o n : ℝ) := by
    rw [mul_sum]
    symm
    apply sum_subset_zero_on_sdiff
    · intro n hn
      have := mem_Icc.mp (hQ hn)
      exact mem_Icc.mpr ⟨this.1, this.2.trans hbx⟩
    · intro n hn
      rw [Finset.mem_sdiff] at hn
      have h0 : (n ! + 1).factorization p = 0 := by
        apply Nat.factorization_eq_zero_of_not_dvd
        intro hdv
        apply hn.2
        rw [mem_filter, mem_Icc]
        refine ⟨⟨(mem_Icc.mp hn.1).1, ?_⟩, hdv⟩
        by_contra hnb
        have hnx := (mem_Icc.mp hn.1).2
        have hpn : p ≤ n := by omega
        have := (Nat.dvd_add_right (Nat.dvd_factorial hp.pos hpn)).mp hdv
        exact hp.one_lt.ne' (Nat.dvd_one.mp this)
      simp [h0]
    · intro n _; exact mul_comm _ _
  rw [hsumeq]
  have hloc := lai_local (o := o) hp (by omega) hx2' hbx hbp hab hQ hdivQ hq3 hW1
  refine hloc.trans ?_
  -- bound the number of points
  have hQc := card_Q_le hp hQ hbp (fun n hn => (mem_filter.mp hn).2) hbx hab (by omega)
  set t₀ : ℕ := 2 * q * (2 * Nat.log 2 x + 2) * ((2 * q + 1) * W + 1)
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  set Mt : ℝ := 6 * (x : ℝ) ^ ((2 : ℝ) / 3)
  have hMt1 : 1 ≤ Mt := by
    have := Real.one_le_rpow hxR (show (0:ℝ) ≤ 2 / 3 by norm_num); simp only [Mt]; linarith
  have ht₀1 : (1 : ℝ) ≤ t₀ := by
    have : 1 ≤ t₀ := Nat.one_le_iff_ne_zero.mpr (show 2 * q * (2 * Nat.log 2 x + 2) *
      ((2 * q + 1) * W + 1) ≠ 0 from Nat.mul_ne_zero (Nat.mul_ne_zero (by omega) (by omega))
        (Nat.succ_ne_zero _))
    exact_mod_cast this
  set Λ : ℝ := ((b - N : ℕ) : ℝ)
  set M : ℝ := (T.card : ℝ)
  have hTc : T.card = x + 1 - N := Nat.card_Icc N x
  have hΛM : Λ ≤ M := by
    simp only [Λ, M]; exact_mod_cast (show b - N ≤ T.card by omega)
  have hMd : d * N ≤ M := by
    simp only [M]; rw [hTc]; push_cast [Nat.cast_sub (show N ≤ x + 1 by omega)]; linarith
  have hMpos : 0 < M := by nlinarith
  have hstep1 : Φ Λ x L W t₀ Q.card ≤ Φ M x L W t₀ Mt := by
    refine (?_ : Φ Λ x L W t₀ Q.card ≤ Φ Λ x L W t₀ Mt).trans
      (Φ_le (Nat.cast_nonneg _) hΛM hxR hL hWR hMt1 ht₀1)
    rcases Nat.eq_zero_or_pos Q.card with h0 | hpos
    · rw [h0]
      unfold Φ
      have hΛ0 : 0 ≤ Λ := Nat.cast_nonneg _
      have hb : 0 ≤ (x / 2 + Λ * Real.log x / W) / L + Λ / 4 :=
        add_nonneg (div_nonneg (add_nonneg (by positivity)
          (div_nonneg (mul_nonneg hΛ0 (Real.log_nonneg hxR)) hWR.le)) hL.le) (by linarith)
      have ha : 0 ≤ Λ / (4 * L) * Real.log Mt ^ 2 :=
        mul_nonneg (div_nonneg hΛ0 (by linarith)) (sq_nonneg _)
      have hc := mul_nonneg hb (Real.log_nonneg hMt1)
      simp only [Nat.cast_zero, Real.log_zero]
      nlinarith
    · exact Φ_mono (Nat.cast_nonneg _) hxR hL hWR (by exact_mod_cast hpos) hQc
  refine hstep1.trans ?_
  -- now a real inequality
  set ℓ := Real.log N with hℓdef
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓdef, Real.le_log_iff_exp_le (by linarith)]
    have : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    linarith
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hlx : Real.log x ≤ ℓ + 1 := by
    have h1 : (x : ℝ) ≤ 2 * N := by
      have := mul_le_mul_of_nonneg_right hd1.le (show (0:ℝ) ≤ N by positivity)
      linarith
    have h2 := Real.log_le_log (by linarith) h1
    rw [Real.log_mul (by norm_num) (by linarith), ← hℓdef] at h2
    have := Real.log_two_lt_d9; linarith
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg hxR
  have hlMt : Real.log Mt ≤ (2 / 3) * (ℓ + 1) + 2 := by
    simp only [Mt]
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos (by linarith) _).ne',
      Real.log_rpow (by linarith)]
    have : Real.log 6 < 2 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have := Real.exp_one_gt_d9
      nlinarith [Real.exp_pos 1, show Real.exp 2 = Real.exp 1 * Real.exp 1 by
        rw [← Real.exp_add]; norm_num]
    nlinarith
  have hlMt0 : 0 ≤ Real.log Mt := Real.log_nonneg hMt1
  have hlt₀ : Real.log t₀ ≤ Real.log C₁ + Real.log (2 * ℓ + 3) := by
    have hlog2 : (Nat.log 2 x : ℝ) ≤ Real.log x / Real.log 2 := by
      rw [le_div_iff₀ (Real.log_pos (by norm_num))]
      have := Nat.pow_log_le_self 2 (show x ≠ 0 by omega)
      have h3 : ((2 : ℝ) ^ (Nat.log 2 x)) ≤ x := by exact_mod_cast this
      have := Real.log_le_log (by positivity) h3
      rwa [Real.log_pow] at this
    have hl2 : (1 : ℝ) / 2 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have hlog2' : (Nat.log 2 x : ℝ) ≤ 2 * (ℓ + 1) := by
      refine hlog2.trans ?_
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have : (t₀ : ℝ) ≤ C₁ * (2 * ℓ + 3) := by
      simp only [t₀, C₁]; push_cast
      have : (0 : ℝ) ≤ (2 * q + 1) * W + 1 := by positivity
      have : (0 : ℝ) ≤ q := by positivity
      nlinarith
    calc Real.log t₀ ≤ Real.log (C₁ * (2 * ℓ + 3)) := Real.log_le_log (by linarith) this
      _ = _ := Real.log_mul (by linarith) (by linarith)
  -- expand Φ and compare
  unfold Φ
  have hxN : (x : ℝ) ≤ 2 / d * M := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hd]
    have h1 := mul_le_mul_of_nonneg_right hx2 hd.le
    have h2 : (1 + d) * N * d ≤ 2 * (d * N) := by
      have := mul_nonneg (mul_nonneg hd.le (show (0:ℝ) ≤ N by positivity)) (sub_nonneg.mpr hd1.le)
      nlinarith
    linarith
  have e1 : M / (4 * L) * Real.log Mt ^ 2 ≤ M * ((κ + η / 4) * (ℓ + 4) ^ 2) := by
    have hsq : Real.log Mt ^ 2 ≤ ((2 / 3) * (ℓ + 4)) ^ 2 := by
      have : Real.log Mt ≤ (2 / 3) * (ℓ + 4) := by linarith
      exact pow_le_pow_left₀ hlMt0 this 2
    have : 1 / (4 * L) * ((2 / 3) * (ℓ + 4)) ^ 2 = (1 / (9 * L)) * (ℓ + 4) ^ 2 := by
      first | (field_simp; ring) | field_simp
    have h2 : (1 / (9 * L)) * (ℓ + 4) ^ 2 ≤ (κ + η / 4) * (ℓ + 4) ^ 2 :=
      mul_le_mul_of_nonneg_right hqL (by positivity)
    have hL4 : 0 ≤ 1 / (4 * L) := by positivity
    calc M / (4 * L) * Real.log Mt ^ 2 = M * (1 / (4 * L) * Real.log Mt ^ 2) := by ring
      _ ≤ M * (1 / (4 * L) * ((2 / 3) * (ℓ + 4)) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hL4) hMpos.le
      _ ≤ _ := by rw [this]; exact mul_le_mul_of_nonneg_left h2 hMpos.le
  have e2 : ((x / 2 + M * Real.log x / W) / L + M / 4) * Real.log Mt ≤
      M * (η / 16 * (ℓ + 4) ^ 2 + (2 / (d * L) + 1) * (ℓ + 4)) := by
    have hlt : Real.log Mt ≤ ℓ + 4 := by linarith
    have a1 : (x / 2 / L) * Real.log Mt ≤ M * (1 / (d * L) * (ℓ + 4)) := by
      have hx2M : (x : ℝ) / 2 ≤ M / d := by
        rw [le_div_iff₀ hd]
        have := mul_le_mul_of_nonneg_right hxN hd.le
        have e : 2 / d * M * d = 2 * M := by first | (field_simp; ring) | field_simp
        linarith
      have : x / 2 / L ≤ M * (1 / (d * L)) := by
        have h1 := div_le_div_of_nonneg_right hx2M hL.le
        have e : M / d / L = M * (1 / (d * L)) := by ring
        linarith
      calc (x / 2 / L) * Real.log Mt ≤ M * (1 / (d * L)) * (ℓ + 4) :=
            mul_le_mul this hlt hlMt0 (by positivity)
        _ = _ := by ring
    have a2 : (M * Real.log x / W / L) * Real.log Mt ≤ M * (η / 16 * (ℓ + 4) ^ 2) := by
      have : M * Real.log x / W / L * Real.log Mt = M * (1 / (W * L)) * (Real.log x * Real.log Mt) := by
        ring
      rw [this]
      have h3 : Real.log x * Real.log Mt ≤ (ℓ + 4) ^ 2 := by
        have : Real.log x ≤ ℓ + 4 := by linarith
        calc Real.log x * Real.log Mt ≤ (ℓ + 4) * (ℓ + 4) := mul_le_mul this hlt hlMt0 (by linarith)
          _ = (ℓ + 4) ^ 2 := by ring
      have hWL0 : 0 ≤ 1 / (W * L) := by positivity
      calc M * (1 / (W * L)) * (Real.log x * Real.log Mt) ≤ M * (η / 16) * (ℓ + 4) ^ 2 := by
            rw [mul_assoc, mul_assoc]
            apply mul_le_mul_of_nonneg_left _ hMpos.le
            exact mul_le_mul hWL h3 (mul_nonneg hlx0 hlMt0) (by positivity)
        _ = _ := by ring
    have a3 : M / 4 * Real.log Mt ≤ M * (ℓ + 4) := by
      have := mul_le_mul_of_nonneg_left hlt (show 0 ≤ M / 4 by linarith)
      have : 0 ≤ M * (ℓ + 4) := by positivity
      linarith
    have : ((x / 2 + M * Real.log x / W) / L + M / 4) * Real.log Mt =
        (x / 2 / L) * Real.log Mt + (M * Real.log x / W / L) * Real.log Mt + M / 4 * Real.log Mt := by
      ring
    rw [this]
    have : M * (η / 16 * (ℓ + 4) ^ 2 + (2 / (d * L) + 1) * (ℓ + 4)) =
        M * (1 / (d * L) * (ℓ + 4)) + M * (η / 16 * (ℓ + 4) ^ 2) + M * (ℓ + 4) +
          M * (1 / (d * L) * (ℓ + 4)) := by ring
    rw [this]
    have : 0 ≤ M * (1 / (d * L) * (ℓ + 4)) := by positivity
    linarith
  have e3 : Real.log 2 + x * Real.log x + M * Real.log x * (1 + Real.log t₀) ≤
      M * ((1 + 4 / d * (ℓ + 1)) + (ℓ + 1) * (1 + Real.log C₁ + Real.log (2 * ℓ + 3))) := by
    have a1 : Real.log 2 ≤ M := by
      have := Real.log_two_lt_d9
      have hM1 : (1 : ℝ) ≤ M := by
        simp only [M]; exact_mod_cast (show 1 ≤ T.card by omega)
      linarith
    have a2 : x * Real.log x ≤ M * (4 / d * (ℓ + 1)) := by
      calc x * Real.log x ≤ (2 / d * M) * (ℓ + 1) :=
            mul_le_mul hxN hlx hlx0 (by positivity)
        _ ≤ M * (4 / d * (ℓ + 1)) := by
            have : 0 ≤ M * (2 / d * (ℓ + 1)) := by positivity
            have e : M * (4 / d * (ℓ + 1)) = (2 / d * M) * (ℓ + 1) + M * (2 / d * (ℓ + 1)) := by ring
            linarith
    have a3 : M * Real.log x * (1 + Real.log t₀) ≤
        M * ((ℓ + 1) * (1 + Real.log C₁ + Real.log (2 * ℓ + 3))) := by
      have : 0 ≤ 1 + Real.log t₀ := by have := Real.log_nonneg ht₀1; linarith
      have : Real.log x * (1 + Real.log t₀) ≤ (ℓ + 1) * (1 + Real.log C₁ + Real.log (2 * ℓ + 3)) := by
        apply mul_le_mul hlx (by linarith) (by linarith) (by linarith)
      calc M * Real.log x * (1 + Real.log t₀) = M * (Real.log x * (1 + Real.log t₀)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left this hMpos.le
    have e : M * ((1 + 4 / d * (ℓ + 1)) + (ℓ + 1) * (1 + Real.log C₁ + Real.log (2 * ℓ + 3))) =
        M * 1 + M * (4 / d * (ℓ + 1)) + M * ((ℓ + 1) * (1 + Real.log C₁ + Real.log (2 * ℓ + 3))) := by
      ring
    linarith
  have hfin := mul_le_mul_of_nonneg_left hN hMpos.le
  linarith

end LaneCLai


theorem OMA.laiValuation : OMA.R_Erdos977_erdos_977_variants_lai_R1.H2 := by
  intro d hd hd1 η hη
  filter_upwards [LaneCLai.H2_main d hd hd1 η hη] with N hN
  exact hN

end

theorem OMA.solution : type_of% @Erdos977.erdos_977.variants.lai :=
  OMA.R_Erdos977_erdos_977_variants_lai_R1.main OMA.laiPrimeSum OMA.laiValuation
