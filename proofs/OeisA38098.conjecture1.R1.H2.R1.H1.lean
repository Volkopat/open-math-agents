import OMAReductions.R_OeisA38098_conjecture1_R1_H2_R1
import Mathlib

-- Step OeisA38098.conjecture1.R1.H2.R1.H1: Rosser 1941, Theorem 19, for T >= 100.
-- Credit: @senamakel
-- Backlund's argument as formalised in Garald1/RSBounds (Apache-2.0) and calr3/ternary-goldbach
-- (Apache-2.0), pruned to the declarations the proof uses and ported to this Mathlib.

section
lemma Complex.digamma_apply_add_nat {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) (n : ℕ) :
  Complex.digamma (s + n) = Complex.digamma s + ∑ k ∈ Finset.range n, (s + k)⁻¹ := by
 induction n with
 | zero => simp
 | succ n ih =>
  have hsn (m : ℕ) : s + (n : ℂ) ≠ -(m : ℂ) := fun h =>
   hs (m + n) (by push_cast at h ⊢; linear_combination h)
  rw [show s + ((n + 1 : ℕ) : ℂ) = (s + (n : ℂ)) + 1 by push_cast; ring,
   Complex.digamma_apply_add_one _ hsn, ih, Finset.sum_range_succ]
  ring
lemma Complex.digamma_nat_add_one (n : ℕ) :
  Complex.digamma (n + 1) = harmonic n - Real.eulerMascheroniConstant := by
 have hs : ∀ m : ℕ, (1 : ℂ) ≠ -(m : ℂ) := by
  intro m h
  have := congrArg Complex.re h
  simp at this
  linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
 rw [add_comm _ 1, Complex.digamma_apply_add_nat hs n, Complex.digamma_one, harmonic]
 push_cast [add_comm (1 : ℂ)]
 ring
lemma Complex.norm_exp_mul_I (x : ℂ) : ‖Complex.exp (x * Complex.I)‖ = Real.exp (-x.im) := by
 rw [Complex.norm_exp, Complex.mul_I_re]
lemma Real.arctan_le_self {x : ℝ} (h : 0 ≤ x) : Real.arctan x ≤ x := by
 have h0 : 0 ≤ Real.arctan x := Real.arctan_nonneg.mpr h
 have h1 := Real.le_tan h0 (Real.arctan_lt_pi_div_two x)
 rwa [Real.tan_arctan] at h1
lemma HasDerivAt.logDeriv_Gamma {g : ℂ → ℂ} {a s : ℂ} (hg : HasDerivAt g a s)
  (h : ∀ m : ℕ, g s ≠ -(m : ℂ)) :
  logDeriv (fun z ↦ Complex.Gamma (g z)) s = a * Complex.digamma (g s) := by
 rw [show (fun z ↦ Complex.Gamma (g z)) = Complex.Gamma ∘ g from rfl,
  logDeriv_comp (Complex.differentiableAt_Gamma _ h) hg.differentiableAt, hg.deriv,
  Complex.digamma_def]
 exact mul_comm _ _
section ZetaConj
open Complex ComplexConjugate
lemma Complex.Gammaℝ_conj (s : ℂ) : Gammaℝ (conj s) = conj (Gammaℝ s) := by
 have hpi : (Real.pi : ℂ).arg ≠ Real.pi := by
  rw [arg_ofReal_of_nonneg Real.pi_pos.le]
  exact Real.pi_pos.ne
 have h := cpow_conj (Real.pi : ℂ) (-s / 2) hpi
 rw [conj_ofReal] at h
 rw [Gammaℝ_def, Gammaℝ_def, map_mul, ← Gamma_conj, ← h]
 congr 2 <;> simp [map_div₀, map_neg, map_ofNat]
lemma completedRiemannZeta_conj_of_re_pos' {s : ℂ} (hs : 0 < s.re) :
  completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
 have hcs : 0 < (conj s).re := by rwa [conj_re]
 have key {z : ℂ} (hz : 0 < z.re) : completedRiemannZeta z = riemannZeta z * Gammaℝ z := by
  have hz0 : z ≠ 0 := fun h ↦ by simp [h] at hz
  rw [riemannZeta_def_of_ne_zero hz0]
  exact (div_mul_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos hz)).symm
 rw [key hcs, key hs, map_mul, riemannZeta_conj, Complex.Gammaℝ_conj]
lemma completedRiemannZeta_conj (s : ℂ) :
  completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
 rcases lt_or_ge 0 s.re with hs | hs
 ·exact completedRiemannZeta_conj_of_re_pos' hs
 ·have h1 : 0 < (1 - s).re := by simp only [sub_re, one_re]; linarith
  have hcs : conj (1 - s) = 1 - conj s := by simp
  have := completedRiemannZeta_conj_of_re_pos' h1
  rwa [hcs, completedRiemannZeta_one_sub, completedRiemannZeta_one_sub] at this
end ZetaConj
end
section
namespace vaa.vab.vao
noncomputable def radius : ℝ := 33 / 25
noncomputable def scalar (H L V σ : ℝ) : ℝ :=
 if 5 / 4 ≤ σ then Real.log ‖riemannZeta (σ : ℂ)‖
 else H + L / 2 * (max (1 - σ) 0 + max (-σ) 0) +
  if 0 ≤ σ ∧ σ < 1 then V else 0
noncomputable def vbk (T : ℝ) : ℝ := Real.log (Real.log (T + radius))
noncomputable def vbC (T : ℝ) : ℝ := Real.log ((T + radius) / (2 * Real.pi))
noncomputable def vbt (T : ℝ) : ℝ :=
 Real.log ((T - radius) ^ 2 / ((T - radius) ^ 2 - 4))
noncomputable def vcH (T : ℝ) (z : ℂ) : ℝ :=
 scalar (vbk T) (vbC T) (vbt T) z.re
end vaa.vab.vao
end
section
section EulerMaclaurin
open Finset Interval MeasureTheory
variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}
noncomputable def B1 (x : ℝ) : ℝ := x - ⌊x⌋₊ - 1 / 2
lemma vnF : AEStronglyMeasurable B1 := by
 unfold B1
 fun_prop
lemma vmt {x : ℝ} (hx : 0 ≤ x) : |B1 x| ≤ 1 / 2 := by
 unfold B1
 refine abs_le.mpr ⟨?_, ?_⟩
 ·grind [Nat.floor_le hx]
 ·grind [Nat.lt_succ_floor x]
lemma vfc (c : 𝕜) (hab : a ≤ b) (h_int : IntervalIntegrable (deriv f) volume a b)
  (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) :
  ∫ t in a..b, (t + c) * deriv f t = (b + c) * f b - (a + c) * f a - ∫ t in a..b, f t := by
 rw [← Set.uIcc_of_le hab] at hf_diff
 have : ∀ t ∈ [[a, b]], HasDerivAt (fun (t : ℝ) ↦ t + c) 1 t := by
  intro t ht
  simp only [hasDerivAt_add_const_iff]
  convert! ContinuousLinearMap.hasDerivAt (RCLike.ofRealCLM (K := 𝕜)) using 1
  simp
 replace hf_diff := fun t ht ↦ (hf_diff t ht).hasDerivAt
 rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul this hf_diff (by simp) h_int]
 simp
lemma veu (ha : 0 ≤ a) (hab : a ≤ b) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
  IntervalIntegrable (fun t ↦ deriv f t * B1 t) volume a b := by
 refine IntervalIntegrable.continuousOn_mul ?_ h_cont
 rw [intervalIntegrable_iff']
 apply MeasureTheory.Measure.integrableOn_of_bounded (by simp) (by unfold B1; fun_prop) (M := 1 / 2)
 filter_upwards [self_mem_ae_restrict (by measurability)] with x hx
 rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx
 norm_cast
 exact vmt (by linarith)
lemma ved (ha : 0 ≤ a) (hab : a ≤ b)
  (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
  ∫ t in a..b, deriv f t * (⌊t⌋₊ + 1) = (b + 1 / 2) * f b - (a + 1 / 2) * f a - (∫ t in a..b, f t) - ∫ t in a..b, deriv f t * B1 t := by
 calc
 _ = ∫ t in a..b, (deriv f t * (t + 1 / 2) -deriv f t * B1 t) := by
  congr
  ext
  simp only [B1]
  push_cast
  ring
 _ = (∫ t in a..b, deriv f t * (t + 1 / 2)) - ∫ t in a..b, deriv f t * B1 t := by
  exact intervalIntegral.integral_sub (ContinuousOn.intervalIntegrable (by fun_prop)) (veu ha hab h_cont)
 _ = _ := by
  conv => lhs; arg 1; arg 1; ext; rw [mul_comm]
  rw [vfc _ hab h_cont.intervalIntegrable hf_diff]
lemma vdE (ha : 0 ≤ a) (hab : a ≤ b)
  (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
  (h_cont : ContinuousOn (deriv f) [[a, b]]) :
  ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k =
   f a * B1 a - f b * B1 b + (∫ t in a..b, f t) + ∫ t in a..b, deriv f t * B1 t  := by
 have := sum_mul_eq_sub_sub_integral_mul (fun _ ↦ 1) ha hab hf_diff (Set.uIcc_of_le hab ▸ h_cont).integrableOn_Icc
 simp only [mul_one, sum_const, Nat.card_Icc, tsub_zero, nsmul_eq_mul, Nat.cast_add,
  Nat.cast_one] at this
 rw [this, ← intervalIntegral.integral_of_le hab]
 rw [ved ha hab hf_diff h_cont]
 unfold B1
 push_cast
 ring
end EulerMaclaurin
namespace Real
open Filter Asymptotics
end Real
section Issue1584
open MeasureTheory Set Filter Topology
end Issue1584
namespace vaa.vlv
open Real Finset Filter Asymptotics Topology
open ArithmeticFunction hiding log
lemma vlw (s : ℝ) (hs : 1 < s) :
  log (riemannZeta (s:ℂ)).re = ∑' n, Λ n / (n^s * log n) := by
 have hsc : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs
 have hep := riemannZeta_eulerProduct_exp_log (s := (s : ℂ)) hsc
 set S : ℂ := ∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) with hS
 have hcpow : ∀ p : Nat.Primes, (p : ℂ) ^ (-(s : ℂ)) = (((p : ℝ) ^ (-s) : ℝ) : ℂ) := by
  intro p
  rw [Complex.ofReal_cpow (by positivity)]
  push_cast; ring_nf
 set z : Nat.Primes → ℝ := fun p => (p : ℝ) ^ (-s) with hz
 have hz_pos : ∀ p : Nat.Primes, 0 < z p := fun p => by
  have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  positivity
 have hz_lt_one : ∀ p : Nat.Primes, z p < 1 := by
  intro p
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  change (p : ℝ) ^ (-s) < 1
  rw [Real.rpow_neg (by positivity), inv_lt_one_iff₀]
  right
  exact (Real.one_lt_rpow_iff_of_pos (by positivity)).mpr (Or.inl ⟨hp1, by linarith⟩)
 have hterm : ∀ p : Nat.Primes,
   -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) = ((-Real.log (1 - z p) : ℝ) : ℂ) := by
  intro p
  rw [hcpow p]
  have h1z : (0 : ℝ) < 1 - z p := by have := hz_lt_one p; linarith
  rw [show (1 : ℂ) - ((z p : ℝ) : ℂ) = (((1 - z p : ℝ)) : ℂ) by push_cast; ring]
  rw [← Complex.ofReal_log h1z.le]
  push_cast; ring
 set Sr : ℝ := ∑' p : Nat.Primes, -Real.log (1 - z p) with hSr
 have hSeq : S = (Sr : ℂ) := by
  rw [hS, hSr, Complex.ofReal_tsum]
  exact tsum_congr hterm
 have hSim : S.im = 0 := by rw [hSeq]; exact Complex.ofReal_im _
 have hSre : S.re = Sr := by rw [hSeq]; exact Complex.ofReal_re _
 have hlog_zeta : Complex.log (riemannZeta (s : ℂ)) = S := by
  rw [← hep, Complex.log_exp (by rw [hSim]; exact neg_lt_zero.mpr Real.pi_pos)
   (by rw [hSim]; exact Real.pi_pos.le)]
 have hkey : Real.log (riemannZeta (s : ℂ)).re = Sr := by
  have hζim : (riemannZeta (s : ℂ)).im = 0 := riemannZeta_im_eq_zero_of_one_lt hs
  have hζeq : riemannZeta (s : ℂ) = ((riemannZeta (s : ℂ)).re : ℂ) := by
   apply Complex.ext <;> simp [hζim]
  have : Real.log (riemannZeta (s : ℂ)).re
    = (Complex.log (riemannZeta (s : ℂ))).re := by
   conv_rhs => rw [hζeq]
   rw [Complex.log_ofReal_re]
  rw [this, hlog_zeta, hSre]
 rw [hkey]
 have habs : ∀ p : Nat.Primes, |z p| < 1 := by
  intro p
  rw [abs_of_pos (hz_pos p)]; exact hz_lt_one p
 have htaylor : ∀ p : Nat.Primes,
   HasSum (fun n : ℕ => (z p) ^ (n + 1) / (n + 1)) (-Real.log (1 - z p)) :=
  fun p => hasSum_pow_div_log_of_abs_lt_one (habs p)
 have hSr_double : Sr = ∑' (p : Nat.Primes) (n : ℕ), (z p) ^ (n + 1) / (n + 1) := by
  rw [hSr]
  exact tsum_congr fun p => ((htaylor p).tsum_eq).symm
 have hsummable_z : Summable z := Nat.Primes.summable_rpow.mpr (by linarith)
 have hsummable_prime : Summable (fun p : Nat.Primes => -Real.log (1 - z p)) := by
  have := Real.summable_log_one_add_of_summable hsummable_z.neg
  convert! this.neg using 1
 have hg_nonneg : ∀ pk : Nat.Primes × ℕ, 0 ≤ (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1) := by
  intro pk; positivity [hz_pos pk.1]
 have hsummable_g : Summable (fun pk : Nat.Primes × ℕ => (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1)) := by
  rw [summable_prod_of_nonneg hg_nonneg]
  refine ⟨fun p => (htaylor p).summable, ?_⟩
  refine hsummable_prime.congr (fun p => ?_)
  exact ((htaylor p).tsum_eq).symm
 have hpoint : ∀ (p : Nat.Primes) (n : ℕ),
   Λ ((p : ℕ) ^ (n + 1)) /
    ((((p : ℕ) ^ (n + 1) : ℕ) : ℝ) ^ s * Real.log (((p : ℕ) ^ (n + 1) : ℕ) : ℝ))
   = (z p) ^ (n + 1) / (n + 1) := by
  intro p n
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  rw [vonMangoldt_apply_pow (Nat.succ_ne_zero n), vonMangoldt_apply_prime p.prop]
  have hcast : (((p : ℕ) ^ (n + 1) : ℕ) : ℝ) = (p : ℝ) ^ (n + 1) := by push_cast; ring
  rw [hcast, Real.log_pow]
  rw [show (z p) ^ (n + 1) = ((p : ℝ) ^ (n + 1)) ^ (-s) by
   rw [hz]; rw [← Real.rpow_natCast ((p : ℝ) ^ (-s)) (n + 1),
    ← Real.rpow_natCast ((p : ℝ)) (n + 1), ← Real.rpow_mul (by positivity),
    ← Real.rpow_mul (by positivity)]; ring_nf]
  rw [Real.rpow_neg (by positivity)]
  field_simp
  push_cast
  ring
 set F : ℕ → ℝ := fun n => Λ n / ((n : ℝ) ^ s * Real.log n) with hF
 have hsupp : Function.support F ⊆ {n : ℕ | IsPrimePow n} := by
  intro n hn
  rw [Function.mem_support] at hn
  simp only [Set.mem_ofPred_eq]
  by_contra hpp
  apply hn
  simp only [hF, vonMangoldt_eq_zero_iff.mpr hpp, zero_div]
 have hprod_eq : (∑' pk : Nat.Primes × ℕ, (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1))
   = ∑' m : {n : ℕ // IsPrimePow n}, F m.val := by
  rw [← Equiv.tsum_eq Nat.Primes.prodNatEquiv (fun m : {n : ℕ // IsPrimePow n} => F m.val)]
  apply tsum_congr
  intro pk
  rw [Nat.Primes.coe_prodNatEquiv_apply, hF]
  exact (hpoint pk.1 pk.2).symm
 rw [hSr_double, ← hsummable_g.tsum_prod' (fun p => (htaylor p).summable), hprod_eq]
 exact tsum_subtype_eq_of_support_subset hsupp
section
open MeasureTheory Set
namespace vnt
end vnt
end
section
open MeasureTheory Set
end
end vaa.vlv
end
section
open Complex Filter
open scoped Topology
namespace vaa.vab
private lemma vkT {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
  {z : ℂ} (hz : ‖z‖ = a) :
  ‖(1 - (a : ℂ) ^ 2)⁻¹‖ ≤
   ‖(1 - (a : ℂ))⁻¹‖ * ‖(1 - z)⁻¹‖ := by
 have h1 : 0 < 1 - a := sub_pos.mpr ha1
 have h2 : 0 < 1 - a ^ 2 := by nlinarith
 have hz1 : 0 < ‖(1 : ℂ) - z‖ := by
  apply norm_pos_iff.mpr
  intro h
  have he : z = 1 := (sub_eq_zero.mp h).symm
  have : a = 1 := by simpa [he] using hz.symm
  linarith
 have htri : ‖(1 : ℂ) - z‖ ≤ 1 + a := by
  simpa only [norm_one, hz] using norm_sub_le (1 : ℂ) z
 have hreal1 : ‖(1 : ℂ) - (a : ℂ)‖ = 1 - a := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_of_nonneg h1.le]
 have hreal2 : ‖(1 : ℂ) - (a : ℂ) ^ 2‖ = 1 - a ^ 2 := by
  rw [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
   Complex.norm_of_nonneg h2.le]
 rw [norm_inv, norm_inv, norm_inv, hreal1, hreal2, ← mul_inv]
 apply (inv_le_inv₀ h2 (mul_pos h1 hz1)).mpr
 nlinarith [mul_le_mul_of_nonneg_left htri h1.le]
lemma vfr {s : ℂ} (hs : 1 < s.re) :
  ‖riemannZeta ((2 * s.re : ℝ) : ℂ)‖ / ‖riemannZeta (s.re : ℂ)‖ ≤
   ‖riemannZeta s‖ := by
 have hσ : 1 < ((s.re : ℂ)).re := by simpa using hs
 have h2σ : 1 < (((2 * s.re : ℝ) : ℂ)).re := by simpa using (show 1 < 2 * s.re by linarith)
 have hprod := (riemannZeta_eulerProduct_hasProd hσ).norm.mul
  (riemannZeta_eulerProduct_hasProd hs).norm
 have hprod2 := (riemannZeta_eulerProduct_hasProd h2σ).norm
 have hfactor (p : Nat.Primes) :
   ‖(1 - (p : ℂ) ^ (-((2 * s.re : ℝ) : ℂ)))⁻¹‖ ≤
    ‖(1 - (p : ℂ) ^ (-(s.re : ℂ)))⁻¹‖ *
     ‖(1 - (p : ℂ) ^ (-s))⁻¹‖ := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hp0 : 0 < (p : ℝ) := by linarith
  let a : ℝ := (p : ℝ) ^ (-s.re)
  have ha : 0 ≤ a := Real.rpow_nonneg hp0.le _
  have ha1 : a < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  have hpow : (p : ℂ) ^ (-(s.re : ℂ)) = (a : ℂ) := by
   simpa only [a, Complex.ofReal_neg, Complex.ofReal_natCast] using
    (Complex.ofReal_cpow hp0.le (-s.re)).symm
  have hpow2 : (p : ℂ) ^ (-((2 * s.re : ℝ) : ℂ)) = (a : ℂ) ^ 2 := by
   rw [show -((2 * s.re : ℝ) : ℂ) = -(s.re : ℂ) * (2 : ℕ) by push_cast; ring,
    Complex.cpow_mul_nat, hpow]
  have hz : ‖(p : ℂ) ^ (-s)‖ = a := by
   simpa only [a, Complex.neg_re, Complex.ofReal_natCast] using
    Complex.norm_cpow_eq_rpow_re_of_pos hp0 (-s)
  rw [hpow, hpow2]
  exact vkT ha ha1 hz
 have hlim : ‖riemannZeta ((2 * s.re : ℝ) : ℂ)‖ ≤
   ‖riemannZeta (s.re : ℂ)‖ * ‖riemannZeta s‖ := by
  apply le_of_tendsto_of_tendsto' hprod2 hprod
  intro S
  exact Finset.prod_le_prod (fun p _ => norm_nonneg _) (fun p _ => hfactor p)
 have hζ : 0 < ‖riemannZeta (s.re : ℂ)‖ :=
  norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re hσ)
 exact (div_le_iff₀ hζ).mpr (by simpa only [mul_comm] using hlim)
lemma vdI (T : ℝ) :
  ‖riemannZeta ((5 / 2 : ℝ) : ℂ)‖ / ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ ≤
   ‖riemannZeta (((5 / 4 : ℝ) : ℂ) + T * Complex.I)‖ := by
 have h := vfr
  (s := ((5 / 4 : ℝ) : ℂ) + T * Complex.I) (by simp; norm_num)
 norm_num at h ⊢
 exact h
end vaa.vab
end
section
open scoped BigOperators
open Finset MeasureTheory
namespace vaa.vab.vbg
lemma vbJ {σ : ℝ} (hσ : 1 < σ) :
  ‖riemannZeta (σ : ℂ)‖ = ∑' n : ℕ, (n : ℝ) ^ (-σ) := by
 have hc : riemannZeta (σ : ℂ) =
   Complex.ofReal (∑' n : ℕ, (n : ℝ) ^ (-σ)) := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by simpa using hσ), Complex.ofReal_tsum]
  congr 1
  funext n
  rw [Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_neg,
   Complex.ofReal_natCast, Complex.cpow_neg, one_div]
 rw [hc, Complex.norm_of_nonneg (tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _))]
noncomputable def vbD (σ : ℝ) (n : ℕ) : ℕ → ℝ
 | 0 => 0
 | m + 1 => (n : ℝ) ^ (-σ) + vbD σ (n + 1) m
lemma viS (σ : ℝ) (n m : ℕ) :
  vbD σ n m = ∑ j ∈ Finset.range m, ((j + n : ℕ) : ℝ) ^ (-σ) := by
 induction m generalizing n with
 | zero => simp [vbD]
 | succ m ih =>
  simp [vbD, Finset.sum_range_succ', ih, Nat.add_assoc, add_comm, add_left_comm]
lemma vcW {σ : ℝ} (hσ : 1 < σ) {N : ℕ} (hN : 0 < N) :
  ‖riemannZeta (σ : ℂ)‖ ≤
   vbD σ 1 N + (N : ℝ) ^ (1 - σ) / (σ - 1) := by
 have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
  Real.summable_nat_rpow.mpr (by linarith)
 have hN' : (0 : ℝ) < N := by exact_mod_cast hN
 have anti : AntitoneOn (fun t : ℝ => t ^ (-σ)) (Set.Ici (N : ℝ)) := by
  intro x hx y hy hxy
  exact Real.rpow_le_rpow_of_nonpos (hN'.trans_le hx) hxy (by linarith)
 have ht := anti.tsum_comp_add_le_integral N
  (integrableOn_Ioi_rpow_of_lt (by linarith : -σ < -1) hN')
  (fun t ht => Real.rpow_nonneg (le_of_lt (hN'.trans ht)) _)
 rw [integral_Ioi_rpow_of_lt (by linarith : -σ < -1) hN'] at ht
 have htail : (∑' n : ℕ, ((n + N + 1 : ℕ) : ℝ) ^ (-σ)) ≤
   (N : ℝ) ^ (1 - σ) / (σ - 1) := by
  convert ht using 1
  rw [show -σ + 1 = 1 - σ by ring, show σ - 1 = -(1 - σ) by ring,
   div_neg, neg_div]
 rw [vbJ hσ, hsum.tsum_eq_zero_add]
 rw [Nat.cast_zero, Real.zero_rpow (by linarith : -σ ≠ 0), zero_add]
 have hs1 : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-σ)) := hsum.comp_injective (fun a b h => Nat.add_right_cancel h : Function.Injective (fun n : ℕ => n + 1))
 rw [← hs1.sum_add_tsum_nat_add N, viS]
 exact add_le_add le_rfl htail
lemma vjZ {σ : ℝ} (hσ : 1 < σ) (N : ℕ) :
  vbD σ 1 N ≤ ‖riemannZeta (σ : ℂ)‖ := by
 rw [vbJ hσ]
 have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
  Real.summable_nat_rpow.mpr (by linarith)
 have hs1 : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-σ)) := hsum.comp_injective (fun a b h => Nat.add_right_cancel h : Function.Injective (fun n : ℕ => n + 1))
 rw [hsum.tsum_eq_zero_add, Nat.cast_zero, Real.zero_rpow (by linarith : -σ ≠ 0), zero_add, viS]
 exact hs1.sum_le_tsum _ (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
lemma vlF {σ : ℝ} (hσ : 1 < σ) (N : ℕ) :
  vbD σ 1 N + ((N + 1 : ℕ) : ℝ) ^ (1 - σ) / (σ - 1) ≤
   ‖riemannZeta (σ : ℂ)‖ := by
 have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
  Real.summable_nat_rpow.mpr (by linarith)
 have hN' : (0 : ℝ) < (N + 1 : ℕ) := by positivity
 have anti : AntitoneOn (fun t : ℝ => t ^ (-σ)) (Set.Ici ((N + 1 : ℕ) : ℝ)) := by
  intro x hx y hy hxy
  exact Real.rpow_le_rpow_of_nonpos (hN'.trans_le hx) hxy (by linarith)
 have ht := anti.integral_le_tsum_comp_add (N + 1) hsum
  (fun t ht => Real.rpow_nonneg (le_of_lt (hN'.trans ht)) _)
 rw [integral_Ioi_rpow_of_lt (by linarith : -σ < -1) hN'] at ht
 have htail : ((N + 1 : ℕ) : ℝ) ^ (1 - σ) / (σ - 1) ≤
   ∑' n : ℕ, ((n + (N + 1) : ℕ) : ℝ) ^ (-σ) := by
  convert ht using 1
  rw [show -σ + 1 = 1 - σ by ring, show σ - 1 = -(1 - σ) by ring,
   div_neg, neg_div]
 rw [vbJ hσ, hsum.tsum_eq_zero_add]
 rw [Nat.cast_zero, Real.zero_rpow (by linarith : -σ ≠ 0), zero_add]
 have hs1 : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-σ)) := hsum.comp_injective (fun a b h => Nat.add_right_cancel h : Function.Injective (fun n : ℕ => n + 1))
 rw [← hs1.sum_add_tsum_nat_add N, viS]
 apply add_le_add le_rfl
 simpa only [Nat.add_assoc] using htail
lemma vfB {n p k : ℕ} (hn : 0 < n) (hk : 0 < k) :
  ((n : ℝ) ^ (-(p : ℝ) / k)) ^ k = ((n : ℝ) ^ p)⁻¹ := by
 rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
 have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
 rw [div_mul_cancel₀ _ hk', Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_natCast]
lemma vlO {n p k D b : ℕ} (hn : 0 < n) (hk : 0 < k) (hD : 0 < D)
  (hb : b ^ k * n ^ p ≤ D ^ k) :
  (b : ℝ) / D ≤ (n : ℝ) ^ (-(p : ℝ) / k) := by
 apply (pow_le_pow_iff_left₀ (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _) hk.ne').mp
 rw [div_pow, vfB hn hk]
 have hn' : 0 < (n : ℝ) ^ p := pow_pos (by exact_mod_cast hn) _
 have hD' : 0 < (D : ℝ) ^ k := pow_pos (by exact_mod_cast hD) _
 rw [div_le_iff₀ hD', le_inv_mul_iff₀ hn']
 exact_mod_cast (by simpa [mul_comm] using hb : n ^ p * b ^ k ≤ D ^ k)
lemma vex {n p k D b : ℕ} (hn : 0 < n) (hk : 0 < k) (hD : 0 < D)
  (hb : D ^ k ≤ b ^ k * n ^ p) :
  (n : ℝ) ^ (-(p : ℝ) / k) ≤ (b : ℝ) / D := by
 apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity) hk.ne').mp
 rw [div_pow, vfB hn hk]
 have hn' : 0 < (n : ℝ) ^ p := pow_pos (by exact_mod_cast hn) _
 have hD' : 0 < (D : ℝ) ^ k := pow_pos (by exact_mod_cast hD) _
 rw [le_div_iff₀ hD', inv_mul_le_iff₀ hn']
 exact_mod_cast (by simpa [mul_comm] using hb : D ^ k ≤ n ^ p * b ^ k)
def vej (p k D n : ℕ) : List ℕ → Bool
 | [] => true
 | b :: bs => decide (b ^ k * n ^ p ≤ D ^ k ∧ D ^ k ≤ (b + 1) ^ k * n ^ p) &&
   vej p k D (n + 1) bs
lemma veI {p k D n : ℕ} (hn : 0 < n) (hk : 0 < k) (hD : 0 < D)
  {bs : List ℕ} (hc : vej p k D n bs = true) :
  (bs.sum : ℝ) / D ≤ vbD ((p : ℝ) / k) n bs.length ∧
  vbD ((p : ℝ) / k) n bs.length ≤ ((bs.sum + bs.length : ℕ) : ℝ) / D := by
 induction bs generalizing n with
 | nil => simp [vbD]
 | cons b bs ih =>
  simp only [vej, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hl, hu⟩ := ih (by omega) hc.2
  have hbl := vlO hn hk hD hc.1.1
  have hbu := vex hn hk hD hc.1.2
  simp only [List.sum_cons, List.length_cons, vbD, Nat.cast_add, Nat.cast_one]
  rw [neg_div] at hbl hbu
  simp only [Nat.cast_add, Nat.cast_one, add_div] at hbu hu ⊢
  constructor <;> linarith
end vaa.vab.vbg
end
section
open Real Complex Set Filter MeasureTheory Finset ArithmeticFunction
open scoped Topology BigOperators
namespace vaa.vab.vbe
noncomputable def vaE (σ : ℝ) : ℝ := Real.log ‖riemannZeta (σ : ℂ)‖
noncomputable def vdm (n : ℕ) : ℝ := Λ n / Real.log n
lemma vda (n : ℕ) : 0 ≤ vdm n :=
 div_nonneg vonMangoldt_nonneg (Real.log_natCast_nonneg n)
lemma vlo (n : ℕ) : vdm n ≤ 1 := by
 by_cases hn : n ≤ 1
 ·interval_cases n <;> norm_num [vdm]
 have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
 exact (div_le_one hl).mpr vonMangoldt_le_log
lemma vbi {σ : ℝ} (hσ : 1 < σ) :
  Summable (fun n : ℕ => vdm n * (n : ℝ) ^ (-σ)) := by
 apply Summable.of_nonneg_of_le (fun n => mul_nonneg (vda n) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  (fun n => ?_) (Real.summable_nat_rpow.mpr (show -σ < -1 by linarith))
 exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg n) _) (vlo n)
lemma vbP {σ : ℝ} (hσ : 1 < σ) :
  vaE σ = ∑' n : ℕ, vdm n * (n : ℝ) ^ (-σ) := by
 have he : riemannZeta (σ : ℂ) = ((riemannZeta (σ : ℂ)).re : ℂ) := by
  apply Complex.ext <;> simp [riemannZeta_im_eq_zero_of_one_lt hσ]
 unfold vaE
 rw [he, Complex.norm_of_nonneg (riemannZeta_re_pos_of_one_lt hσ).le,
  vaa.vlv.vlw σ hσ]
 apply tsum_congr
 intro n
 rw [vdm, Real.rpow_neg (Nat.cast_nonneg n)]
 simp only [div_eq_mul_inv, mul_inv_rev]
 ring
lemma vmq {σ : ℝ} (hσ : 1 < σ) : 0 ≤ vaE σ := by
 rw [vbP hσ]
 exact tsum_nonneg (fun n => mul_nonneg (vda n) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
lemma vkV : ConvexOn ℝ (Ioi 1) vaE := by
 refine ⟨convex_Ioi 1, ?_⟩
 intro x hx y hy a b ha hb hab
 have hz : 1 < a • x + b • y := (convex_Ioi 1) hx hy ha hb hab
 rw [vbP hx, vbP hy, vbP hz]
 simp only [smul_eq_mul]
 rw [← tsum_mul_left, ← tsum_mul_left,
  ← Summable.tsum_add ((vbi hx).mul_left a) ((vbi hy).mul_left b)]
 apply (vbi hz).tsum_le_tsum _
  (((vbi hx).mul_left a).add ((vbi hy).mul_left b))
 intro n
 by_cases hn : n = 0
 ·simp [hn, vdm]
 have hn0 : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
 have hh := convexOn_exp.2 (mem_univ (-x * Real.log n))
  (mem_univ (-y * Real.log n)) ha hb hab
 simp only [smul_eq_mul] at hh ⊢
 rw [Real.rpow_def_of_pos hn0, Real.rpow_def_of_pos hn0, Real.rpow_def_of_pos hn0]
 have he : Real.log (n : ℝ) * -(a * x + b * y) =
   a * (-x * Real.log n) + b * (-y * Real.log n) := by ring
 rw [he, show Real.log (n : ℝ) * -x = -x * Real.log n by ring,
  show Real.log (n : ℝ) * -y = -y * Real.log n by ring]
 have hm := mul_le_mul_of_nonneg_left hh (vda n)
 nlinarith [hm]
lemma vfs : AntitoneOn vaE (Ioi 1) := by
 intro x hx y hy hxy
 rw [vbP hx, vbP hy]
 apply (vbi hy).tsum_le_tsum _ (vbi hx)
 intro n
 by_cases hn : n = 0
 ·simp [hn, vdm]
 apply mul_le_mul_of_nonneg_left _ (vda n)
 exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)) (by linarith)
lemma viX : ContinuousOn vaE (Ioi 1) := by
 intro σ hσ
 change 1 < σ at hσ
 unfold vaE
 apply ContinuousWithinAt.log
 ·apply ContinuousWithinAt.norm
  exact ((differentiableAt_riemannZeta (by
   intro he
   have hh := congrArg Complex.re he
   simp only [Complex.ofReal_re, Complex.one_re] at hh
   linarith [hσ])).continuousAt.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
 ·exact norm_ne_zero_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by simpa using hσ))
noncomputable def vaO (θ : ℝ) : ℝ := vaE (5 / 4 + (33 / 25) * Real.cos θ)
lemma vcc {θ : ℝ} (hθ : θ ∈ Icc 0 (Real.pi / 2)) :
  1 < 5 / 4 + (33 / 25) * Real.cos θ := by
 have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
 linarith
lemma vja : ConvexOn ℝ (Icc 0 (Real.pi / 2)) vaO := by
 refine ⟨convex_Icc _ _, ?_⟩
 intro x hx y hy a b ha hb hab
 have hz : a • x + b • y ∈ Icc 0 (Real.pi / 2) := (convex_Icc _ _) hx hy ha hb hab
 have hc := strictConcaveOn_cos_Icc.concaveOn.2
  (show x ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) by constructor <;> linarith [hx.1, hx.2, Real.pi_pos])
  (show y ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) by constructor <;> linarith [hy.1, hy.2, Real.pi_pos])
  ha hb hab
 have hsx := vcc hx
 have hsy := vcc hy
 have hsz := vcc hz
 have hsmix : 1 < a * (5 / 4 + (33 / 25) * Real.cos x) +
   b * (5 / 4 + (33 / 25) * Real.cos y) := by
  exact (convex_Ioi (1 : ℝ)) hsx hsy ha hb hab
 have hsm : a * (5 / 4 + (33 / 25) * Real.cos x) +
   b * (5 / 4 + (33 / 25) * Real.cos y) ≤
   5 / 4 + (33 / 25) * Real.cos (a • x + b • y) := by
  simp only [smul_eq_mul] at hc ⊢
  nlinarith
 have ha1 := vfs hsmix hsz hsm
 have ha2 := vkV.2 hsx hsy ha hb hab
 exact ha1.trans ha2
lemma vdl : ContinuousOn vaO (Icc 0 (Real.pi / 2)) :=
 viX.comp (by fun_prop) (fun _ hx => vcc hx)
lemma vfL {f : ℝ → ℝ} {a : ℝ}
  (hf : ConvexOn ℝ (Icc a (a + 1)) f) (hc : ContinuousOn f (Icc a (a + 1))) :
  (∫ x in a..a + 1, f x) ≤ (f a + f (a + 1)) / 2 := by
 let L : ℝ → ℝ := fun x => (a + 1 - x) * f a + (x - a) * f (a + 1)
 have hL : Continuous L := by dsimp [L]; fun_prop
 have hpoint : ∀ x ∈ Icc a (a + 1), f x ≤ L x := by
  intro x hx
  have hh := hf.2 (show a ∈ Icc a (a + 1) by constructor <;> linarith)
   (show a + 1 ∈ Icc a (a + 1) by constructor <;> linarith)
   (show 0 ≤ a + 1 - x by linarith [hx.2]) (show 0 ≤ x - a by linarith [hx.1])
   (show (a + 1 - x) + (x - a) = 1 by ring)
  simpa only [smul_eq_mul, show (a + 1 - x) * a + (x - a) * (a + 1) = x by ring] using hh
 have hi := intervalIntegral.integral_mono_on (μ := volume) (by linarith : a ≤ a + 1)
  (hc.intervalIntegrable_of_Icc (by linarith)) (hL.intervalIntegrable a (a + 1)) hpoint
 have he : (∫ x in a..a + 1, L x) = (f a + f (a + 1)) / 2 := by
  dsimp [L]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
   intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
   intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
   intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
   intervalIntegral.integral_const, intervalIntegral.integral_const,
   integral_id]
  simp only [smul_eq_mul]
  ring
 exact hi.trans_eq he
lemma vfO {f : ℝ → ℝ} {N : ℕ}
  (hf : ConvexOn ℝ (Icc 0 (N : ℝ)) f) (hc : ContinuousOn f (Icc 0 (N : ℝ))) :
  (∫ x in (0 : ℝ)..N, f x) ≤
   ∑ i ∈ Finset.range N, (f i + f ((i : ℝ) + 1)) / 2 := by
 have hi (i : ℕ) (hi : i < N) : Icc (i : ℝ) (i + 1) ⊆ Icc 0 (N : ℝ) := by
  apply Set.Icc_subset_Icc (Nat.cast_nonneg i)
  exact_mod_cast (show i + 1 ≤ N by omega)
 have hsum := intervalIntegral.sum_integral_adjacent_intervals (f := f) (μ := volume)
  (a := fun i : ℕ => (i : ℝ)) (n := N) (fun i hi' =>
   (hc.mono (by simpa only [Nat.cast_add, Nat.cast_one] using hi i hi')).intervalIntegrable_of_Icc
    (by exact_mod_cast Nat.le_succ i))
 simp only [Nat.cast_zero] at hsum
 rw [← hsum]
 apply Finset.sum_le_sum
 intro i hi'
 simpa only [Nat.cast_add, Nat.cast_one] using vfL
  (hf.subset (hi i (Finset.mem_range.mp hi')) (convex_Icc _ _))
  (hc.mono (hi i (Finset.mem_range.mp hi')))
lemma viN :
  (∫ θ in (0 : ℝ)..Real.pi / 2, vaO θ) / (2 * Real.pi) ≤
   (∑ i ∈ Finset.range 16,
    (vaO (Real.pi / 32 * i) + vaO (Real.pi / 32 * ((i : ℝ) + 1))) / 2) / 64 := by
 let F : ℝ → ℝ := fun x => vaO (Real.pi / 32 * x)
 have hmem {x : ℝ} (hx : x ∈ Icc 0 (16 : ℝ)) : Real.pi / 32 * x ∈ Icc 0 (Real.pi / 2) := by
  rcases hx with ⟨hx0, hx16⟩
  constructor
  ·exact mul_nonneg (by positivity) hx0
  ·nlinarith [mul_le_mul_of_nonneg_left hx16 Real.pi_pos.le]
 have hF : ConvexOn ℝ (Icc 0 (16 : ℝ)) F := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hh := vja.2 (hmem hx) (hmem hy) ha hb hab
  simpa only [F, smul_eq_mul, mul_add, mul_assoc, mul_left_comm] using hh
 have hc : ContinuousOn F (Icc 0 (16 : ℝ)) :=
  vdl.comp (by fun_prop) (fun _ hx => hmem hx)
 have hi := vfO (N := 16) hF hc
 have he := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 16) vaO (Real.pi / 32)
 norm_num only [smul_eq_mul, mul_zero, show Real.pi / 32 * 16 = Real.pi / 2 by ring] at he
 rw [← he]
 have hh := div_le_div_of_nonneg_right hi (show (0 : ℝ) ≤ 64 by norm_num)
 convert hh using 1 <;> (try dsimp only [F]) <;> (try simp only [Nat.cast_ofNat]) <;> (try field_simp [Real.pi_ne_zero]) <;> (try ring)
 all_goals try rfl
end vaa.vab.vbe
end
section
open Complex Real
open scoped ComplexConjugate
namespace vaa.vab.ven
lemma vhg (t : ℝ) :
  ‖Complex.Gamma (1 - (t : ℂ) * I)‖ = ‖Complex.Gamma (1 + (t : ℂ) * I)‖ := by
 have he : 1 - (t : ℂ) * I = conj (1 + (t : ℂ) * I) := by simp [sub_eq_add_neg]
 rw [he, Complex.Gamma_conj, norm_conj]
lemma vfC {t : ℝ} (ht : 0 < t) :
  ‖Complex.Gamma (1 + (t : ℂ) * I)‖ ^ 2 =
   Real.pi * t / Real.sinh (Real.pi * t) := by
 have htC : (t : ℂ) * I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne') I_ne_zero
 have hs : 0 < Real.sinh (Real.pi * t) := Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht)
 have hsin : ‖Complex.sin ((Real.pi : ℂ) * ((t : ℂ) * I))‖ = Real.sinh (Real.pi * t) := by
  have he : (Real.pi : ℂ) * ((t : ℂ) * I) = ((Real.pi * t : ℝ) : ℂ) * I := by
   push_cast
   ring
  rw [he, Complex.sin_mul_I, ← Complex.ofReal_sinh (Real.pi * t), norm_mul,
   norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
 have hr := congrArg norm (Complex.Gamma_mul_Gamma_one_sub ((t : ℂ) * I))
 rw [norm_mul, norm_div, vhg, hsin] at hr
 have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by simp [Real.pi_pos.le]
 rw [hpi] at hr
 have hc := congrArg norm (Complex.Gamma_add_one ((t : ℂ) * I) htC)
 rw [norm_mul, norm_mul] at hc
 have harg : (t : ℂ) * I + 1 = 1 + (t : ℂ) * I := add_comm _ _
 rw [harg] at hc
 simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, norm_I, mul_one] at hc
 calc
  _ = t * (‖Complex.Gamma ((t : ℂ) * I)‖ * ‖Complex.Gamma (1 + (t : ℂ) * I)‖) := by
   rw [pow_two, hc]
   ring
  _ = t * (Real.pi / Real.sinh (Real.pi * t)) := by rw [hr]
  _ = _ := by ring
end vaa.vab.ven
end
section
open Complex Real
open scoped ComplexConjugate
namespace vaa.vab.vaP
noncomputable def vgv (s : ℂ) : ℂ :=
 2 * (2 * (Real.pi : ℂ)) ^ (-(1 - s)) * Complex.Gamma (1 - s) *
  Complex.cos ((Real.pi : ℂ) * (1 - s) / 2)
lemma functional_equation {s : ℂ} (hs : s.im ≠ 0) :
  riemannZeta s = vgv s * riemannZeta (1 - s) := by
 have hn : ∀ n : ℕ, 1 - s ≠ -(n : ℂ) := by
  intro n he
  have hh := congrArg Complex.im he
  simp only [Complex.sub_im, Complex.one_im, Complex.neg_im, Complex.natCast_im,
   neg_zero, zero_sub] at hh
  exact hs (neg_eq_zero.mp hh)
 have hone : 1 - s ≠ 1 := by
  intro he
  have hh := congrArg Complex.im he
  simp only [Complex.sub_im, Complex.one_im, zero_sub] at hh
  exact hs (neg_eq_zero.mp hh)
 have hh := riemannZeta_one_sub hn hone
 simpa [vgv, sub_sub_cancel] using hh
end vaa.vab.vaP
end
section
open Real
namespace vaa.vab.vdj
lemma vkB {t : ℝ} (ht : 50 ≤ t) :
  Real.exp (-Real.pi * t) ≤ 1 / (8 * t ^ 2) := by
 have ht0 : 0 < t := by linarith
 have hp := Real.pow_div_factorial_le_exp (Real.pi * t) (by positivity : 0 ≤ Real.pi * t) 3
 norm_num at hp
 have hcub : (3 * t) ^ 3 ≤ (Real.pi * t) ^ 3 := by
  apply pow_le_pow_left₀ (by positivity)
  exact mul_le_mul_of_nonneg_right (Real.pi_gt_three).le ht0.le
 have hbig : 8 * t ^ 2 ≤ (Real.pi * t) ^ 3 / 6 := by
  have hh := mul_nonneg (by linarith : 0 ≤ t - 2) (sq_nonneg t)
  nlinarith
 have hexp : 8 * t ^ 2 ≤ Real.exp (Real.pi * t) := hbig.trans hp
 have he : -Real.pi * t = -(Real.pi * t) := by ring
 rw [he, Real.exp_neg, ← one_div]
 exact one_div_le_one_div_of_le (by positivity) hexp
lemma vks {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
  Real.sqrt ((1 + q) / (1 - q)) ≤ Real.exp (2 * q) := by
 have hd : 0 < 1 - q := by linarith
 have hr : (1 + q) / (1 - q) ≤ 1 + 4 * q := by
  rw [div_le_iff₀ hd]
  nlinarith [mul_nonneg hq0 (by linarith : 0 ≤ 1 / 2 - q)]
 have he : 1 + 4 * q ≤ Real.exp (4 * q) := by
  linarith [Real.add_one_le_exp (4 * q)]
 have heq : Real.exp (4 * q) = Real.exp (2 * q) ^ 2 := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring
 have hs : Real.sqrt ((1 + q) / (1 - q)) ^ 2 = (1 + q) / (1 - q) :=
  Real.sq_sqrt (by positivity)
 rw [heq] at he
 nlinarith [Real.sqrt_nonneg ((1 + q) / (1 - q)), Real.exp_pos (2 * q)]
lemma vkp {t : ℝ} (ht : 50 ≤ t) :
  Real.sqrt ((1 + Real.exp (-Real.pi * t)) / (1 - Real.exp (-Real.pi * t))) ≤
   Real.exp (1 / (4 * t ^ 2)) := by
 have ht0 : 0 < t := by linarith
 have hq := vkB ht
 have hu : 1 / (8 * t ^ 2) ≤ (1 / 2 : ℝ) := by
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith
 have hb := vks (Real.exp_pos _).le (hq.trans hu)
 refine hb.trans (Real.exp_le_exp.mpr ?_)
 calc
  2 * Real.exp (-Real.pi * t) ≤ 2 * (1 / (8 * t ^ 2)) := by gcongr
  _ = 1 / (4 * t ^ 2) := by ring
end vaa.vab.vdj
end
section
namespace vac
open Complex
noncomputable def vaf (s : ℂ) (k : ℕ) : ℂ := ((k : ℂ) + 1)⁻¹ - ((k : ℂ) + s)⁻¹
lemma vkf {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (k : ℕ) :
  vaf s k = (s - 1) / (((k : ℂ) + 1) * ((k : ℂ) + s)) := by
 have h1 : ((k : ℂ) + 1) ≠ 0 := by
  intro h
  have : ((k : ℝ) + 1) = 0 := by exact_mod_cast congrArg Complex.re h
  have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  linarith
 have h2 : ((k : ℂ) + s) ≠ 0 := fun h ↦ hs k (by linear_combination h)
 simp only [vaf]
 field_simp
 ring
lemma vau {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) : Summable (vaf s) := by
 obtain ⟨N, hN⟩ := exists_nat_gt (2 * ‖s‖)
 have hcomp : Summable (fun k : ℕ ↦ 2 * ‖s - 1‖ / (k : ℝ) ^ 2) := by
  simpa [div_eq_mul_inv] using
   (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left (2 * ‖s - 1‖)
 refine Summable.of_norm_bounded_eventually_nat hcomp ?_
 filter_upwards [Filter.eventually_ge_atTop (max N 1)] with k hk
 have hkN : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_trans (le_max_left N 1) hk
 have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_trans (le_max_right N 1) hk
 have hks : 2 * ‖s‖ < (k : ℝ) := lt_of_lt_of_le hN hkN
 have hlow : (k : ℝ) / 2 ≤ ‖(k : ℂ) + s‖ := by
  have h := norm_sub_norm_le ((k : ℂ)) (-s)
  simp only [norm_neg, sub_neg_eq_add] at h
  have hkabs : ‖((k : ℕ) : ℂ)‖ = (k : ℝ) := by
   simp
  rw [hkabs] at h
  linarith
 have hpos : (0 : ℝ) < (k : ℝ) := by linarith
 rw [vkf hs k, norm_div, norm_mul]
 have hk1n : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by
  have hcast : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
 rw [hk1n]
 have hs1 : (0 : ℝ) ≤ ‖s - 1‖ := norm_nonneg _
 have hnormpos : (0 : ℝ) < ‖(k : ℂ) + s‖ := by linarith
 have hden1 : (0 : ℝ) < ((k : ℝ) + 1) * ‖(k : ℂ) + s‖ :=
  mul_pos (by linarith) hnormpos
 have hden2 : (0 : ℝ) < (k : ℝ) ^ 2 := by nlinarith
 rw [div_le_div_iff₀ hden1 hden2]
 have hmul : ((k : ℝ) + 1) * ((k : ℝ) / 2) ≤ ((k : ℝ) + 1) * ‖(k : ℂ) + s‖ :=
  mul_le_mul_of_nonneg_left hlow (by linarith)
 nlinarith [hmul, hs1, hk1, hpos]
end vac
end
section
namespace vac
open Complex
noncomputable def gaussSum (s : ℂ) : ℂ :=
 -(Real.eulerMascheroniConstant : ℂ) + ∑' k, vaf s k
lemma vhV {F : Type*} [NormedAddCommGroup F] [CompleteSpace F] {f : ℕ → F}
  (hsum : Summable fun k ↦ f k - f (k + 1))
  (hlim : Filter.Tendsto f Filter.atTop (nhds 0)) :
  HasSum (fun k ↦ f k - f (k + 1)) (f 0) := by
 have hpart : ∀ n : ℕ, ∑ i ∈ Finset.range n, (f i - f (i + 1)) = f 0 - f n :=
  fun n ↦ Finset.sum_range_sub' f n
 have h1 := hsum.hasSum.tendsto_sum_nat
 simp only [hpart] at h1
 have h2 : Filter.Tendsto (fun n : ℕ ↦ f 0 - f n) Filter.atTop (nhds (f 0)) := by
  simpa using tendsto_const_nhds.sub hlim
 rw [← tendsto_nhds_unique h1 h2]
 exact hsum.hasSum
lemma vhK (s : ℂ) :
  Filter.Tendsto (fun k : ℕ ↦ ((k : ℂ) + s)⁻¹) Filter.atTop (nhds 0) := by
 rw [tendsto_zero_iff_norm_tendsto_zero]
 simp only [norm_inv]
 refine Filter.Tendsto.inv_tendsto_atTop ?_
 refine Filter.tendsto_atTop_mono (fun k ↦ ?_)
  (Filter.tendsto_atTop_add_const_right _ (-‖s‖) tendsto_natCast_atTop_atTop)
 have h := norm_sub_norm_le ((k : ℂ)) (-s)
 simp only [norm_neg, sub_neg_eq_add] at h
 rw [Complex.norm_natCast] at h
 exact (by linarith : (k : ℝ) + -‖s‖ ≤ ‖(k : ℂ) + s‖)
lemma vhp {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) :
  gaussSum (s + 1) = gaussSum s + s⁻¹ := by
 have hs' : ∀ n : ℕ, s + 1 ≠ -n := fun n h ↦
  hs (n + 1) (by push_cast at h ⊢; linear_combination h)
 set f : ℕ → ℂ := fun k ↦ ((k : ℂ) + s)⁻¹ with hf
 have hdiff : ∀ k : ℕ, vaf (s + 1) k - vaf s k = f k - f (k + 1) := by
  intro k
  simp only [vaf, hf]
  push_cast
  ring
 have hsub : Summable (fun k ↦ f k - f (k + 1)) := by
  have h := (vau hs').sub (vau hs)
  simpa only [hdiff] using h
 have htel := vhV hsub (vhK s)
 have hHS : HasSum (fun k ↦ vaf (s + 1) k - vaf s k)
   ((∑' k, vaf (s + 1) k) - ∑' k, vaf s k) :=
  (vau hs').hasSum.sub (vau hs).hasSum
 have hHS' : HasSum (fun k ↦ vaf (s + 1) k - vaf s k) (f 0) := by
  simpa only [hdiff] using htel
 have hkey := hHS.unique hHS'
 have hf0 : f 0 = s⁻¹ := by simp [hf]
 rw [hf0] at hkey
 simp only [gaussSum]
 linear_combination hkey
@[simp]
lemma voK (k : ℕ) : vaf 1 k = 0 := by simp [vaf]
lemma vnx : gaussSum 1 = -(Real.eulerMascheroniConstant : ℂ) := by
 simp [gaussSum]
lemma viW (n : ℕ) :
  gaussSum ((n : ℂ) + 1)
   = -(Real.eulerMascheroniConstant : ℂ) + ((harmonic n : ℚ) : ℂ) := by
 induction n with
 | zero => simpa using vnx
 | succ n ih =>
  have hne : ∀ m : ℕ, ((n : ℂ) + 1) ≠ -(m : ℂ) := by
   intro m h
   have hre : (n : ℝ) + 1 = -(m : ℝ) := by exact_mod_cast congrArg Complex.re h
   have h1 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
   have h2 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
   linarith
  have hstep : gaussSum (((n : ℂ) + 1) + 1) = gaussSum ((n : ℂ) + 1) + ((n : ℂ) + 1)⁻¹ :=
   vhp hne
  have hcast : (((n : ℕ) + 1 : ℕ) : ℂ) + 1 = ((n : ℂ) + 1) + 1 := by push_cast; ring
  rw [hcast, hstep, ih, harmonic_succ]
  push_cast
  ring
lemma ver (n : ℕ) :
  Complex.digamma ((n : ℂ) + 1) = gaussSum ((n : ℂ) + 1) := by
 rw [Complex.digamma_nat_add_one n, viW n]
 ring
end vac
end
section
namespace vac
open Real Set
lemma vaV {x : ℝ} (hx : 0 < x) :
  DifferentiableAt ℝ (fun t ↦ Real.log (Real.Gamma t)) x := by
 have hΓ : DifferentiableAt ℝ Real.Gamma x :=
  Real.differentiableAt_Gamma (fun m ↦ by
   intro hcon
   have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
   rw [hcon] at hx
   linarith)
 exact (Real.differentiableAt_log (Real.Gamma_pos_of_pos hx).ne').comp x hΓ
lemma vip {x : ℝ} (hx : 0 < x) :
  Real.log (Real.Gamma (x + 1)) - Real.log (Real.Gamma x) = Real.log x := by
 rw [Real.Gamma_add_one hx.ne', Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne']
 ring
lemma vhz {x : ℝ} (hx : 0 < x) :
  deriv (fun t ↦ Real.log (Real.Gamma t)) (x + 1)
   = deriv (fun t ↦ Real.log (Real.Gamma t)) x + 1 / x := by
 have hpos : {t : ℝ | 0 < t} ∈ nhds x :=
  (isOpen_lt continuous_const continuous_id).mem_nhds hx
 have hEq : (fun t : ℝ ↦ Real.log t + Real.log (Real.Gamma t))
   =ᶠ[nhds x] (fun t : ℝ ↦ Real.log (Real.Gamma (t + 1))) := by
  filter_upwards [hpos] with t ht
  rw [Real.Gamma_add_one (ne_of_gt ht), Real.log_mul (ne_of_gt ht)
   (Real.Gamma_pos_of_pos ht).ne']
 have hL : HasDerivAt (fun t : ℝ ↦ Real.log (Real.Gamma (t + 1)))
   (deriv (fun t ↦ Real.log (Real.Gamma t)) (x + 1)) x := by
  have hshift : HasDerivAt (fun t : ℝ ↦ t + 1) 1 x := (hasDerivAt_id x).add_const 1
  have hout := (vaV (by linarith : (0:ℝ) < x + 1)).hasDerivAt
  simpa [Function.comp_def] using hout.comp x hshift
 have hR : HasDerivAt (fun t : ℝ ↦ Real.log t + Real.log (Real.Gamma t))
   (x⁻¹ + deriv (fun t ↦ Real.log (Real.Gamma t)) x) x :=
  (Real.hasDerivAt_log hx.ne').add (vaV hx).hasDerivAt
 have hLR : HasDerivAt (fun t : ℝ ↦ Real.log t + Real.log (Real.Gamma t))
   (deriv (fun t ↦ Real.log (Real.Gamma t)) (x + 1)) x := hL.congr_of_eventuallyEq hEq
 have := hLR.unique hR
 rw [this, one_div]
 ring
lemma vcM :
  MonotoneOn (deriv (fun t ↦ Real.log (Real.Gamma t))) (Ioi 0) :=
 Real.convexOn_log_Gamma.monotoneOn_deriv (fun _ hx ↦ vaV hx)
lemma vgz {x : ℝ} (hx : 0 < x) :
  deriv (fun t ↦ Real.log (Real.Gamma t)) x ≤ Real.log x ∧
   Real.log x ≤ deriv (fun t ↦ Real.log (Real.Gamma t)) (x + 1) := by
 have hsub : Icc x (x + 1) ⊆ Ioi 0 := fun t ht ↦ lt_of_lt_of_le hx ht.1
 have hcont : ContinuousOn (fun t ↦ Real.log (Real.Gamma t)) (Icc x (x + 1)) := fun t ht ↦
  (vaV (hsub ht)).continuousAt.continuousWithinAt
 obtain ⟨c, hc, hcs⟩ :=
  exists_deriv_eq_slope (fun t ↦ Real.log (Real.Gamma t)) (by linarith) hcont
   (fun t ht ↦ (vaV (lt_trans hx ht.1)).differentiableWithinAt)
 have hslope : (Real.log (Real.Gamma (x + 1)) - Real.log (Real.Gamma x)) / (x + 1 - x)
   = Real.log x := by
  rw [add_sub_cancel_left, div_one, vip hx]
 rw [hslope] at hcs
 have hcpos : (0 : ℝ) < c := lt_trans hx hc.1
 have h1 : deriv (fun t ↦ Real.log (Real.Gamma t)) x ≤ Real.log x := by
  rw [← hcs]
  exact vcM (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr hcpos) hc.1.le
 have h2 : Real.log x ≤ deriv (fun t ↦ Real.log (Real.Gamma t)) (x + 1) := by
  rw [← hcs]
  exact vcM (Set.mem_Ioi.mpr hcpos)
   (Set.mem_Ioi.mpr (by linarith)) hc.2.le
 exact ⟨h1, h2⟩
lemma vbB {x : ℝ} (hx : 0 < x) :
  |deriv (fun t ↦ Real.log (Real.Gamma t)) x - Real.log x| ≤ 1 / x := by
 obtain ⟨hle, hge⟩ := vgz hx
 rw [vhz hx] at hge
 rw [abs_le]
 constructor <;> linarith
end vac
end
section
namespace vac
open Complex
lemma vfV {f : ℂ → ℂ} {g : ℝ → ℝ} {g' s : ℝ}
  (hf : DifferentiableAt ℂ f s) (hg : HasDerivAt g g' s) (hfg : ∀ s : ℝ, f ↑s = ↑(g s)) :
  HasDerivAt f ↑g' s := by
 refine HasDerivAt.congr_deriv hf.hasDerivAt ?_
 rw [← (funext hfg ▸ hf.hasDerivAt.comp_ofReal.deriv :)]
 exact hg.ofReal_comp.deriv
lemma vep {x : ℝ} (hx : 0 < x) (m : ℕ) : (x : ℂ) ≠ -(m : ℂ) := by
 intro h
 have hx' : x = -(m : ℝ) := by exact_mod_cast h
 have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
 linarith
lemma vcB {x : ℝ} (hx : 0 < x) : DifferentiableAt ℝ Real.Gamma x :=
 Real.differentiableAt_Gamma (fun m ↦ by
  intro hcon
  have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  rw [hcon] at hx
  linarith)
lemma vhH {x : ℝ} (hx : 0 < x) :
  HasDerivAt Complex.Gamma ((deriv Real.Gamma x : ℝ) : ℂ) (x : ℂ) :=
 vfV
  (Complex.differentiableAt_Gamma _ (vep hx))
  (vcB hx).hasDerivAt
  Complex.Gamma_ofReal
lemma vjU {x : ℝ} (hx : 0 < x) :
  deriv (fun t ↦ Real.log (Real.Gamma t)) x = deriv Real.Gamma x / Real.Gamma x := by
 have hpos := Real.Gamma_pos_of_pos hx
 have h := (Real.hasDerivAt_log hpos.ne').comp x (vcB hx).hasDerivAt
 simp only [Function.comp_def] at h
 rw [h.deriv]
 ring
lemma vdo {x : ℝ} (hx : 0 < x) :
  Complex.digamma (x : ℂ) = ((deriv (fun t ↦ Real.log (Real.Gamma t)) x : ℝ) : ℂ) := by
 have hpos := Real.Gamma_pos_of_pos hx
 rw [Complex.digamma_def, logDeriv_apply, (vhH hx).deriv,
  Complex.Gamma_ofReal, vjU hx]
 push_cast
 ring
end vac
end
section
namespace vac
open Complex
lemma vfG {t : ℝ} (ht : 1 ≤ t) :
  Summable (fun k : ℕ ↦ (((k : ℝ) + t) * ((k : ℝ) + t + 1))⁻¹) := by
 have hcomp : Summable (fun k : ℕ ↦ 1 / (k : ℝ) ^ 2) :=
  Real.summable_one_div_nat_pow.mpr one_lt_two
 refine Summable.of_norm_bounded_eventually_nat hcomp ?_
 filter_upwards [Filter.eventually_ge_atTop 1] with k hk
 have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
 have hsq : (0 : ℝ) < (k : ℝ) ^ 2 := by nlinarith
 have hpos : (0 : ℝ) < ((k : ℝ) + t) * ((k : ℝ) + t + 1) := by nlinarith
 rw [Real.norm_of_nonneg (by positivity), inv_eq_one_div, div_le_div_iff₀ hpos hsq]
 nlinarith
lemma vmv {t : ℝ} (ht : 1 ≤ t) :
  ∑' k : ℕ, (((k : ℝ) + t) * ((k : ℝ) + t + 1))⁻¹ = t⁻¹ := by
 set f : ℕ → ℝ := fun k ↦ ((k : ℝ) + t)⁻¹ with hf
 have hne : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + t := fun k ↦ by
  have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  linarith
 have hdiff : ∀ k : ℕ, f k - f (k + 1) = (((k : ℝ) + t) * ((k : ℝ) + t + 1))⁻¹ := by
  intro k
  have h1 : ((k : ℝ) + t) ≠ 0 := (hne k).ne'
  have h2 : (((k : ℕ) + 1 : ℕ) : ℝ) + t ≠ 0 := (hne (k + 1)).ne'
  simp only [hf]
  push_cast at h2 ⊢
  field_simp
  ring
 have hsum : Summable (fun k : ℕ ↦ f k - f (k + 1)) := by
  simpa only [hdiff] using vfG ht
 have hlim : Filter.Tendsto f Filter.atTop (nhds 0) := by
  simp only [hf]
  exact Filter.Tendsto.inv_tendsto_atTop
   (Filter.tendsto_atTop_add_const_right _ t tendsto_natCast_atTop_atTop)
 have h := vhV hsum hlim
 have hf0 : f 0 = t⁻¹ := by simp [hf]
 rw [hf0] at h
 simpa only [hdiff] using h.tsum_eq
lemma vdC {t : ℝ} (ht : 1 ≤ t) (c : ℝ) :
  HasSum (fun k : ℕ ↦ c * (2 * (((k : ℝ) + t) * ((k : ℝ) + t + 1))⁻¹)) (c * (2 * t⁻¹)) := by
 have h : HasSum (fun k : ℕ ↦ (((k : ℝ) + t) * ((k : ℝ) + t + 1))⁻¹) t⁻¹ := by
  rw [← vmv ht]
  exact (vfG ht).hasSum
 exact (h.mul_left 2).mul_left c
lemma vmO {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (k : ℕ) :
  vaf (a : ℂ) k - vaf (b : ℂ) k
   = ((a : ℂ) - b) / (((k : ℂ) + a) * ((k : ℂ) + b)) := by
 have hkn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
 have h1 : ((k : ℂ) + a) ≠ 0 := by
  intro h
  have : (k : ℝ) + a = 0 := by exact_mod_cast congrArg Complex.re h
  linarith
 have h2 : ((k : ℂ) + b) ≠ 0 := by
  intro h
  have : (k : ℝ) + b = 0 := by exact_mod_cast congrArg Complex.re h
  linarith
 simp only [vaf]
 field_simp
 ring
lemma viQ {n : ℕ} (hn : 1 ≤ n) {a b : ℝ}
    (ha : (n : ℝ) ≤ a) (hb : (n : ℝ) ≤ b) :
    ‖gaussSum (a : ℂ) - gaussSum (b : ℂ)‖ ≤ |a - b| * (2 / n) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hapos : (0 : ℝ) < a := by linarith
  have hbpos : (0 : ℝ) < b := by linarith
  have habs : (0 : ℝ) ≤ |a - b| := abs_nonneg _
  have hsa : ∀ m : ℕ, (a : ℂ) ≠ -m := fun m h ↦ by
    have h' : a = -(m : ℝ) := by exact_mod_cast h
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hsb : ∀ m : ℕ, (b : ℂ) ≠ -m := fun m h ↦ by
    have h' : b = -(m : ℝ) := by exact_mod_cast h
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hHS : HasSum (fun k ↦ vaf (a : ℂ) k - vaf (b : ℂ) k)
      (gaussSum (a : ℂ) - gaussSum (b : ℂ)) := by
    have h := (vau hsa).hasSum.sub (vau hsb).hasSum
    simpa only [gaussSum, add_sub_add_left_eq_sub] using h
  have hbound : ∀ k : ℕ, ‖vaf (a : ℂ) k - vaf (b : ℂ) k‖
      ≤ |a - b| * (2 * (((k : ℝ) + n) * ((k : ℝ) + n + 1))⁻¹) := by
    intro k
    have hkn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hka : (0 : ℝ) < (k : ℝ) + a := by linarith
    have hkb : (0 : ℝ) < (k : ℝ) + b := by linarith
    have hknpos : (0 : ℝ) < (k : ℝ) + n := by linarith
    have hprod : (0 : ℝ) < ((k : ℝ) + a) * ((k : ℝ) + b) := mul_pos hka hkb
    have hnprod : (0 : ℝ) < ((k : ℝ) + n) * ((k : ℝ) + n + 1) := by positivity
    rw [vmO hapos hbpos k, norm_div, norm_mul]
    have hna : ‖((k : ℂ) + a)‖ = (k : ℝ) + a := by
      have hc : ((k : ℂ) + a) = (((k : ℝ) + a : ℝ) : ℂ) := by push_cast; ring
      rw [hc, Complex.norm_real, Real.norm_of_nonneg hka.le]
    have hnb : ‖((k : ℂ) + b)‖ = (k : ℝ) + b := by
      have hc : ((k : ℂ) + b) = (((k : ℝ) + b : ℝ) : ℂ) := by push_cast; ring
      rw [hc, Complex.norm_real, Real.norm_of_nonneg hkb.le]
    have hnum : ‖((a : ℂ) - b)‖ = |a - b| := by
      have hc : ((a : ℂ) - b) = ((a - b : ℝ) : ℂ) := by push_cast; ring
      rw [hc, Complex.norm_real, Real.norm_eq_abs]
    rw [hna, hnb, hnum]
    have hcmp : 1 / (((k : ℝ) + a) * ((k : ℝ) + b))
        ≤ 2 / (((k : ℝ) + n) * ((k : ℝ) + n + 1)) := by
      rw [div_le_div_iff₀ hprod hnprod]
      nlinarith
    calc |a - b| / (((k : ℝ) + a) * ((k : ℝ) + b))
        = |a - b| * (1 / (((k : ℝ) + a) * ((k : ℝ) + b))) := by ring
      _ ≤ |a - b| * (2 / (((k : ℝ) + n) * ((k : ℝ) + n + 1))) :=
          mul_le_mul_of_nonneg_left hcmp habs
      _ = |a - b| * (2 * (((k : ℝ) + n) * ((k : ℝ) + n + 1))⁻¹) := by ring
  have hle := hHS.norm_le_of_bounded (vdC hn1 |a - b|) hbound
  refine hle.trans_eq ?_
  field_simp
lemma vkj {n : ℝ} (hn : 0 < n) {a b : ℝ} (ha : n ≤ a) (hb : n ≤ b) :
  |Real.log a - Real.log b| ≤ |a - b| / n := by
 have key : ∀ u v : ℝ, n ≤ u → n ≤ v → v ≤ u → Real.log u - Real.log v ≤ (u - v) / n := by
  intro u v hu hv hvu
  have hvpos : (0 : ℝ) < v := lt_of_lt_of_le hn hv
  have hupos : (0 : ℝ) < u := lt_of_lt_of_le hn hu
  rw [← Real.log_div hupos.ne' hvpos.ne']
  have h1 : Real.log (u / v) ≤ u / v - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h2 : u / v - 1 = (u - v) / v := by field_simp
  have h3 : (u - v) / v ≤ (u - v) / n := by gcongr
  linarith
 rcases le_total b a with h | h
 ·have hlog : Real.log b ≤ Real.log a := Real.log_le_log (lt_of_lt_of_le hn hb) h
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
  exact key a b ha hb h
 ·have hlog : Real.log a ≤ Real.log b := Real.log_le_log (lt_of_lt_of_le hn ha) h
  rw [abs_sub_comm, abs_sub_comm a b, abs_of_nonneg (by linarith),
   abs_of_nonneg (by linarith)]
  exact key b a hb ha h
lemma vfU {n : ℕ} (hn : 1 ≤ n) {a b : ℝ}
  (ha : (n : ℝ) ≤ a) (hb : (n : ℝ) ≤ b) (hab : |a - b| ≤ 1) :
  |deriv (fun t ↦ Real.log (Real.Gamma t)) a - deriv (fun t ↦ Real.log (Real.Gamma t)) b|
   ≤ 3 / n := by
 have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
 have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
 have hapos : (0 : ℝ) < a := by linarith
 have hbpos : (0 : ℝ) < b := by linarith
 have h1 := vbB hapos
 have h2 := vbB hbpos
 have h3 := vkj hnpos ha hb
 have h1n : (1 : ℝ) / a ≤ 1 / n := by gcongr
 have h2n : (1 : ℝ) / b ≤ 1 / n := by gcongr
 have h3n : |a - b| / n ≤ 1 / n := by gcongr
 have t1 := abs_sub_le (deriv (fun t ↦ Real.log (Real.Gamma t)) a) (Real.log a)
  (deriv (fun t ↦ Real.log (Real.Gamma t)) b)
 have t2 := abs_sub_le (Real.log a) (Real.log b)
  (deriv (fun t ↦ Real.log (Real.Gamma t)) b)
 have t3 : |Real.log b - deriv (fun t ↦ Real.log (Real.Gamma t)) b|
   = |deriv (fun t ↦ Real.log (Real.Gamma t)) b - Real.log b| := abs_sub_comm _ _
 have hthree : (3 : ℝ) / n = 1 / n + 1 / n + 1 / n := by ring
 linarith
lemma vkA {n : ℕ} (hn : 1 ≤ n) {a b : ℝ}
  (ha : (n : ℝ) ≤ a) (hb : (n : ℝ) ≤ b) (hab : |a - b| ≤ 1) :
  ‖(Complex.digamma (a : ℂ) - gaussSum (a : ℂ))
    - (Complex.digamma (b : ℂ) - gaussSum (b : ℂ))‖ ≤ 5 / n := by
 have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
 have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
 have hapos : (0 : ℝ) < a := by linarith
 have hbpos : (0 : ℝ) < b := by linarith
 have hsplit : (Complex.digamma (a : ℂ) - gaussSum (a : ℂ))
   - (Complex.digamma (b : ℂ) - gaussSum (b : ℂ))
   = (Complex.digamma (a : ℂ) - Complex.digamma (b : ℂ))
    - (gaussSum (a : ℂ) - gaussSum (b : ℂ)) := by ring
 have hpsi : ‖Complex.digamma (a : ℂ) - Complex.digamma (b : ℂ)‖ ≤ 3 / n := by
  rw [vdo hapos, vdo hbpos, ← Complex.ofReal_sub, Complex.norm_real,
   Real.norm_eq_abs]
  exact vfU hn ha hb hab
 have hG : ‖gaussSum (a : ℂ) - gaussSum (b : ℂ)‖ ≤ 2 / n := by
  refine (viQ hn ha hb).trans ?_
  have hle : |a - b| * (2 / n) ≤ 1 * (2 / n) := by gcongr
  simpa using hle
 have hfive : (5 : ℝ) / n = 3 / n + 2 / n := by ring
 rw [hsplit]
 refine (norm_sub_le _ _).trans ?_
 linarith
end vac
end
section
namespace vac
lemma vcA {F : Type*} [NormedAddCommGroup F]
  {E : ℝ → F} {C : ℝ}
  (hper : ∀ x : ℝ, 0 < x → E (x + 1) = E x)
  (hnat : ∀ n : ℕ, E ((n : ℝ) + 1) = 0)
  (hosc : ∀ n : ℕ, 1 ≤ n → ∀ a b : ℝ, (n : ℝ) ≤ a → (n : ℝ) ≤ b → |a - b| ≤ 1 →
   ‖E a - E b‖ ≤ C / n)
  {x : ℝ} (hx : 0 < x) : E x = 0 := by
 have hshift : ∀ n : ℕ, ∀ y : ℝ, 0 < y → E (y + n) = E y := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
   intro y hy
   have hyn : (0 : ℝ) < y + n := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
   have hre : y + ((n + 1 : ℕ) : ℝ) = (y + (n : ℝ)) + 1 := by push_cast; ring
   rw [hre, hper (y + n) hyn, ih y hy]
 have key : ∀ n : ℕ, 1 ≤ n → ‖E x‖ ≤ C / n := by
  intro n hn
  set m : ℕ := ⌊x⌋₊ with hm
  have hmx : (m : ℝ) ≤ x := Nat.floor_le hx.le
  have hxm : x < (m : ℝ) + 1 := Nat.lt_floor_add_one x
  have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hnnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hEx : E x = E (x + n) := (hshift n x hx).symm
  have hzero : E (((m + n : ℕ) : ℝ) + 1) = 0 := hnat (m + n)
  have hle_a : (n : ℝ) ≤ x + n := by linarith
  have hle_b : (n : ℝ) ≤ ((m + n : ℕ) : ℝ) + 1 := by push_cast; linarith
  have hclose : |(x + n) - (((m + n : ℕ) : ℝ) + 1)| ≤ 1 := by
   push_cast
   rw [abs_le]
   constructor <;> linarith
  have hb := hosc n hn (x + n) (((m + n : ℕ) : ℝ) + 1) hle_a hle_b hclose
  rwa [hzero, sub_zero, ← hEx] at hb
 have hlim : Filter.Tendsto (fun n : ℕ ↦ C / (n : ℝ)) Filter.atTop (nhds 0) :=
  tendsto_const_div_atTop_nhds_zero_nat C
 have hle : ‖E x‖ ≤ 0 :=
  ge_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨1, fun n hn ↦ key n hn⟩)
 exact norm_le_zero_iff.mp hle
end vac
end
section
namespace vac
open Complex
noncomputable def vbU (x : ℝ) : ℂ :=
 Complex.digamma (x : ℂ) - gaussSum (x : ℂ)
lemma vkv {x : ℝ} (hx : 0 < x) (m : ℕ) : (x : ℂ) ≠ -(m : ℂ) :=
 vep hx m
lemma vjF {x : ℝ} (hx : 0 < x) : vbU (x + 1) = vbU x := by
 have hne := vkv hx
 have hcast : ((x + 1 : ℝ) : ℂ) = (x : ℂ) + 1 := by push_cast; ring
 have hx0 : (x : ℂ) ≠ 0 := by simpa using hne 0
 simp only [vbU, hcast]
 rw [Complex.digamma_apply_add_one _ hne, vhp hne]
 ring
lemma vic (n : ℕ) : vbU ((n : ℝ) + 1) = 0 := by
 have hcast : (((n : ℝ) + 1 : ℝ) : ℂ) = (n : ℂ) + 1 := by push_cast; ring
 simp only [vbU, hcast]
 rw [ver n, sub_self]
lemma via {n : ℕ} (hn : 1 ≤ n) {a b : ℝ}
  (ha : (n : ℝ) ≤ a) (hb : (n : ℝ) ≤ b) (hab : |a - b| ≤ 1) :
  ‖vbU a - vbU b‖ ≤ 5 / n :=
 vkA hn ha hb hab
lemma vfS {x : ℝ} (hx : 0 < x) :
  Complex.digamma (x : ℂ) = gaussSum (x : ℂ) := by
 have h : vbU x = 0 :=
  vcA
   (fun y hy ↦ vjF hy)
   vic
   (fun n hn a b ha hb hab ↦ via hn ha hb hab)
   hx
 rwa [vbU, sub_eq_zero] at h
end vac
end
section
namespace vac
open Complex
def vaB : Set ℂ := {s : ℂ | 0 < s.re}
lemma vcy : IsOpen vaB :=
 isOpen_lt continuous_const Complex.continuous_re
lemma veN : IsPreconnected vaB :=
 (convex_halfSpace_re_gt 0).isPreconnected
lemma van {s : ℂ} : s ∈ vaB ↔ 0 < s.re := Iff.rfl
lemma vat {s : ℂ} (hs : s ∈ vaB) (m : ℕ) : s ≠ -(m : ℂ) := by
 intro h
 have hre : s.re = -(m : ℝ) := by rw [h]; simp
 have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
 have := van.mp hs
 linarith
lemma vhP {δ M : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {s : ℂ}
    (hre : δ ≤ s.re) (hM : ‖s‖ ≤ M) (k : ℕ) :
    ‖vaf s k‖ ≤ (M + 1) / (δ * ((k : ℝ) + 1) ^ 2) := by
  have hkn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hspos : (0 : ℝ) < s.re := lt_of_lt_of_le hδ0 hre
  have hne : ∀ m : ℕ, s ≠ -(m : ℂ) := vat (van.mpr hspos)
  have hMnn : (0 : ℝ) ≤ M := le_trans (norm_nonneg s) hM
  have hk1 : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by
    have hc : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [hc, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hks : (k : ℝ) + δ ≤ ‖(k : ℂ) + s‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    simp only [Complex.add_re, Complex.natCast_re]
    linarith
  have hkspos : (0 : ℝ) < ‖(k : ℂ) + s‖ := lt_of_lt_of_le (by linarith) hks
  have hnum : ‖s - 1‖ ≤ M + 1 := by
    refine le_trans (norm_sub_le s 1) ?_
    simpa using hM
  rw [vkf hne k, norm_div, norm_mul, hk1]
  have hden : (0 : ℝ) < ((k : ℝ) + 1) * ‖(k : ℂ) + s‖ := by positivity
  have hden2 : (0 : ℝ) < δ * ((k : ℝ) + 1) ^ 2 := by positivity
  rw [div_le_div_iff₀ hden hden2]
  have hstep : δ * ((k : ℝ) + 1) ≤ ‖(k : ℂ) + s‖ := by nlinarith
  have hM1 : (0 : ℝ) ≤ (M + 1) * ((k : ℝ) + 1) := by positivity
  calc ‖s - 1‖ * (δ * ((k : ℝ) + 1) ^ 2)
      = (‖s - 1‖ * ((k : ℝ) + 1)) * (δ * ((k : ℝ) + 1)) := by ring
    _ ≤ ((M + 1) * ((k : ℝ) + 1)) * ‖(k : ℂ) + s‖ :=
        mul_le_mul (mul_le_mul_of_nonneg_right hnum (by linarith)) hstep (by positivity) hM1
    _ = (M + 1) * (((k : ℝ) + 1) * ‖(k : ℂ) + s‖) := by ring
lemma vhj {δ M : ℝ} (hδ0 : 0 < δ) :
  Summable (fun k : ℕ ↦ (M + 1) / (δ * ((k : ℝ) + 1) ^ 2)) := by
 have hbase : Summable (fun k : ℕ ↦ 1 / ((k : ℝ) + 1) ^ 2) := by
  have h := (_root_.summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  simpa using h
 have hEq : ∀ k : ℕ, (M + 1) / (δ * ((k : ℝ) + 1) ^ 2)
   = ((M + 1) / δ) * (1 / ((k : ℝ) + 1) ^ 2) := by
  intro k
  field_simp
 simpa only [hEq] using hbase.mul_left ((M + 1) / δ)
lemma vfY (k : ℕ) {V : Set ℂ} (hV : V ⊆ vaB) :
  DifferentiableOn ℂ (fun s ↦ vaf s k) V := by
 intro s hs
 have hne : ((k : ℂ) + s) ≠ 0 := by
  intro h
  have hre : (k : ℝ) + s.re = 0 := by
   have := congrArg Complex.re h
   simpa using this
  have h1 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have h2 := van.mp (hV hs)
  linarith
 refine DifferentiableAt.differentiableWithinAt ?_
 simp only [vaf]
 exact (differentiableAt_const _).sub (((differentiableAt_const _).add differentiableAt_id).inv hne)
lemma vgy {s₀ : ℂ} (hs₀ : s₀ ∈ vaB) :
  DifferentiableAt ℂ gaussSum s₀ := by
 have hre₀ : 0 < s₀.re := van.mp hs₀
 set δ : ℝ := min (s₀.re / 2) 1 with hδ
 set M : ℝ := ‖s₀‖ + 1 with hM
 have hδ0 : 0 < δ := lt_min (by linarith) one_pos
 have hδ1 : δ ≤ 1 := min_le_right _ _
 have hδre : δ < s₀.re := lt_of_le_of_lt (min_le_left _ _) (by linarith)
 set V : Set ℂ := {s : ℂ | δ < s.re} ∩ Metric.ball 0 M with hV
 have hVopen : IsOpen V :=
  (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
 have hs₀V : s₀ ∈ V := by
  refine ⟨hδre, ?_⟩
  simp [Metric.mem_ball, dist_zero_right, hM]
 have hVsub : V ⊆ vaB := fun s hs ↦
  van.mpr (lt_trans hδ0 hs.1)
 have hbound : ∀ (k : ℕ) (w : ℂ), w ∈ V → ‖vaf w k‖ ≤ (M + 1) / (δ * ((k : ℝ) + 1) ^ 2) := by
  intro k w hw
  refine vhP hδ0 hδ1 (le_of_lt hw.1) ?_ k
  have := hw.2
  simp only [Metric.mem_ball, dist_zero_right] at this
  exact this.le
 have hsum : DifferentiableOn ℂ (fun w : ℂ ↦ ∑' k : ℕ, vaf w k) V :=
  Complex.differentiableOn_tsum_of_summable_norm (vhj (M := M) hδ0)
   (fun k ↦ vfY k hVsub) hVopen hbound
 have hat : DifferentiableAt ℂ (fun w : ℂ ↦ ∑' k : ℕ, vaf w k) s₀ :=
  hsum.differentiableAt (hVopen.mem_nhds hs₀V)
 have hres : DifferentiableAt ℂ
   (fun w : ℂ ↦ -(Real.eulerMascheroniConstant : ℂ) + ∑' k : ℕ, vaf w k) s₀ :=
  (differentiableAt_const _).add hat
 exact hres
lemma vgH : DifferentiableOn ℂ gaussSum vaB :=
 fun _ hs ↦ (vgy hs).differentiableWithinAt
lemma vhW : AnalyticOnNhd ℂ gaussSum vaB :=
 vgH.analyticOnNhd vcy
lemma vdd :
  DifferentiableOn ℂ Complex.Gamma vaB := fun s hs ↦
 (Complex.differentiableAt_Gamma s (vat hs)).differentiableWithinAt
lemma vhr : DifferentiableOn ℂ Complex.digamma vaB := by
 have hΓ := vdd
 have hd : DifferentiableOn ℂ (deriv Complex.Gamma) vaB :=
  hΓ.deriv vcy
 have hne : ∀ s ∈ vaB, Complex.Gamma s ≠ 0 := fun s hs ↦
  Complex.Gamma_ne_zero (vat hs)
 have := hd.div hΓ hne
 simpa only [Complex.digamma_def, logDeriv] using this
lemma veo : AnalyticOnNhd ℂ Complex.digamma vaB :=
 vhr.analyticOnNhd vcy
lemma vev :
  ∃ᶠ z in nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ, Complex.digamma z = gaussSum z := by
 set u : ℕ → ℂ := fun n ↦ (((1 : ℝ) + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) with hu
 have hpos : ∀ n : ℕ, (0 : ℝ) < 1 + 1 / ((n : ℝ) + 1) := by
  intro n
  have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  positivity
 have htend : Filter.Tendsto u Filter.atTop (nhds (1 : ℂ)) := by
  have h0 : Filter.Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) Filter.atTop (nhds (0 : ℝ)) :=
   tendsto_one_div_add_atTop_nhds_zero_nat
  have hc : Filter.Tendsto (fun _ : ℕ ↦ (1 : ℝ)) Filter.atTop (nhds (1 : ℝ)) :=
   tendsto_const_nhds
  have hr : Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ) + 1 / ((n : ℝ) + 1)) Filter.atTop
    (nhds (1 : ℝ)) := by simpa using hc.add h0
  simpa [hu, Function.comp_def] using (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp hr
 have hne : ∀ n : ℕ, u n ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by
  intro n
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  simp only [hu, Set.mem_compl_iff, Set.mem_singleton_iff]
  intro h
  have : (1 : ℝ) + 1 / ((n : ℝ) + 1) = 1 := by exact_mod_cast h
  linarith
 have hwithin : Filter.Tendsto u Filter.atTop (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u htend
   (Filter.Eventually.of_forall hne)
 refine hwithin.frequently (Filter.Frequently.of_forall fun n ↦ ?_)
 simpa [hu] using vfS (hpos n)
lemma vbc {s : ℂ} (hs : 0 < s.re) : Complex.digamma s = gaussSum s := by
 have h1 : (1 : ℂ) ∈ vaB := by simp [van]
 exact AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq veo
  vhW veN h1 vev
  (van.mpr hs)
end vac
end
section
open Complex
namespace vaa.vab.vbX.vfR
lemma vlf (N : ℕ) :
  ((harmonic N : ℚ) : ℝ) = ∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1) := by
 rw [harmonic]
 push_cast
 refine Finset.sum_congr rfl fun m _ => ?_
 rw [one_div]
lemma viu {z : ℂ} (hz : 0 < z.re) :
  HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / (z + n + 1))
   (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z) := by
 have hz' : 0 < (z + 1).re := by simp; linarith
 have hne := vac.vat hz
 have hne' := vac.vat (s := z + 1) hz'
 have hs := (vac.vau hne').hasSum
 have he : (∑' k, vac.vaf (z + 1) k) =
   Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z := by
  have h := vac.vbc hz'
  rw [Complex.digamma_apply_add_one z hne, vac.gaussSum] at h
  simp only [one_div]
  linear_combination -h
 rw [he] at hs
 change HasSum (fun n : ℕ => ((n : ℂ) + 1)⁻¹ - ((n : ℂ) + (z + 1))⁻¹)
  (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z) at hs
 simpa only [vac.vaf, one_div, add_assoc, add_comm,
  add_left_comm] using hs
end vaa.vab.vbX.vfR
end
section
noncomputable section
namespace vaa.vab.vbX
namespace vjL
open Complex Filter Topology MeasureTheory intervalIntegral Set
lemma vfi (c : ℂ) (f : ℝ → ℂ) (a b : ℝ) :
  ∫ x in a..b, f x * c = (∫ x in a..b, f x) * c :=
 intervalIntegral.integral_mul_const c f
lemma vkk {w : ℂ} (x : ℝ) : |w.im| ≤ ‖(x : ℂ) + w‖ := by
 have := Complex.abs_im_le_norm ((x : ℂ) + w)
 simpa using this
lemma vlx {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) : 0 < ((x : ℂ) + w).re := by
 simp; linarith
lemma vkE {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) :
  (x : ℂ) + w ∈ Complex.slitPlane :=
 Complex.mem_slitPlane_iff.mpr (Or.inl (vlx hw hx))
lemma add_ne_zero {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) : (x : ℂ) + w ≠ 0 :=
 fun h => by have := vlx hw hx; rw [h] at this; simp at this
lemma vjY {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) :
  HasDerivAt (fun y : ℝ => Complex.log ((y : ℂ) + w)) (((x : ℂ) + w)⁻¹) x := by
 have h1 : HasDerivAt (fun z : ℂ => Complex.log (z + w)) (((x : ℂ) + w)⁻¹) (x : ℂ) := by
  have := (Complex.hasDerivAt_log (vkE hw hx)).comp (x : ℂ)
   ((hasDerivAt_id (x : ℂ)).add_const w)
  simpa [Function.comp_def] using this
 exact h1.comp_ofReal
lemma vcD {w : ℂ} (hw : 0 < w.re) {m : ℝ} (hm : 0 ≤ m) :
  ∫ x in m..(m + 1), ((x : ℂ) + w)⁻¹
   = Complex.log (((m + 1 : ℝ) : ℂ) + w) - Complex.log ((m : ℂ) + w) := by
 have hcont : ContinuousOn (fun x : ℝ => ((x : ℂ) + w)⁻¹) (uIcc m (m + 1)) := by
  apply ContinuousOn.inv₀ (by fun_prop)
  intro x hx
  rw [uIcc_of_le (by linarith)] at hx
  exact add_ne_zero hw (by linarith [hx.1])
 rw [integral_eq_sub_of_hasDerivAt (f := fun y : ℝ => Complex.log ((y : ℂ) + w))
  (fun x hx => by
   rw [uIcc_of_le (by linarith)] at hx
   exact vjY hw (by linarith [hx.1]))
  (hcont.intervalIntegrable)]
lemma vmr {w : ℂ} {x m : ℝ} (hxw : (x : ℂ) + w ≠ 0) (hmw : (m : ℂ) + w ≠ 0) :
  ((x : ℂ) + w)⁻¹
   = ((m : ℂ) + w)⁻¹ - ((x - m : ℝ) : ℂ) / ((m : ℂ) + w) ^ 2
    + ((x - m : ℝ) : ℂ) ^ 2 / (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w)) := by
 field_simp
 push_cast
 ring
def eps (w : ℂ) (m : ℝ) : ℂ :=
 ∫ x in m..(m + 1), ((x - m : ℝ) : ℂ) ^ 2 / (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w))
lemma veX {w : ℂ} (hw : 0 < w.re) {m : ℝ} (hm : 0 ≤ m) :
  ∫ x in m..(m + 1), ((x : ℂ) + w)⁻¹
   = ((m : ℂ) + w)⁻¹ - (1 / 2 : ℂ) / ((m : ℂ) + w) ^ 2 + eps w m := by
 have hmw := add_ne_zero hw hm
 have hcongr : ∫ x in m..(m + 1), ((x : ℂ) + w)⁻¹ = ∫ x in m..(m + 1),
   (((m : ℂ) + w)⁻¹ - ((x - m : ℝ) : ℂ) / ((m : ℂ) + w) ^ 2
    + ((x - m : ℝ) : ℂ) ^ 2 / (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w))) := by
  apply integral_congr
  intro x hx
  rw [uIcc_of_le (by linarith)] at hx
  exact vmr (add_ne_zero hw (by linarith [hx.1])) hmw
 rw [hcongr]
 have hI : ∀ {f : ℝ → ℂ}, Continuous f → IntervalIntegrable f volume m (m + 1) :=
  fun hf => hf.intervalIntegrable _ _
 have hR : IntervalIntegrable (fun x : ℝ =>
   ((x - m : ℝ) : ℂ) ^ 2 / (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w))) volume m (m + 1) := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div (f := fun x : ℝ => ((x - m : ℝ) : ℂ) ^ 2)
   (g := fun x : ℝ => ((m : ℂ) + w) ^ 2 * ((x : ℂ) + w)) (by fun_prop) (by fun_prop)
  intro x hx
  rw [uIcc_of_le (by linarith)] at hx
  exact mul_ne_zero (pow_ne_zero _ hmw) (add_ne_zero hw (by linarith [hx.1]))
 have hmid : ∫ x in m..(m + 1), ((x - m : ℝ) : ℂ) / ((m : ℂ) + w) ^ 2
   = ((1 / 2 : ℝ) : ℂ) * ((((m : ℂ) + w) ^ 2)⁻¹) := by
  have e : (fun x : ℝ => ((x - m : ℝ) : ℂ) / ((m : ℂ) + w) ^ 2)
    = fun x : ℝ => ((x - m : ℝ) : ℂ) * ((((m : ℂ) + w) ^ 2)⁻¹) := by
   funext x; rw [div_eq_mul_inv]
  rw [e, vfi, intervalIntegral.integral_ofReal,
   intervalIntegral.integral_comp_sub_right (fun u : ℝ => u) m]
  simp only [sub_self, add_sub_cancel_left, integral_id]
  norm_num
 rw [integral_add ((hI (by fun_prop)).sub (hI (by fun_prop))) hR,
  integral_sub (hI (by fun_prop)) (hI (by fun_prop)), intervalIntegral.integral_const, hmid,
  show m + 1 - m = (1 : ℝ) by ring, one_smul]
 unfold eps
 push_cast
 ring
lemma vkI {w : ℂ} (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) {m : ℝ} (hm : 0 ≤ m) :
    ‖eps w m‖ ≤ 1 / (3 * ‖(m : ℂ) + w‖ ^ 2 * |w.im|) := by
  have hmw := add_ne_zero hw hm
  have hM : 0 < ‖(m : ℂ) + w‖ := norm_pos_iff.mpr hmw
  have ht0 : 0 < |w.im| := by linarith
  unfold eps
  calc ‖∫ x in m..(m + 1), ((x - m : ℝ) : ℂ) ^ 2 / (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w))‖
      ≤ ∫ x in m..(m + 1), ‖((x - m : ℝ) : ℂ) ^ 2 / (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w))‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by linarith)
    _ ≤ ∫ x in m..(m + 1), (x - m) ^ 2 / (‖(m : ℂ) + w‖ ^ 2 * |w.im|) := by
        apply intervalIntegral.integral_mono_on (by linarith)
        · refine (ContinuousOn.intervalIntegrable ?_).norm
          apply ContinuousOn.div (f := fun x : ℝ => ((x - m : ℝ) : ℂ) ^ 2)
            (g := fun x : ℝ => ((m : ℂ) + w) ^ 2 * ((x : ℂ) + w)) (by fun_prop) (by fun_prop)
          intro x hx
          rw [uIcc_of_le (by linarith)] at hx
          exact mul_ne_zero (pow_ne_zero _ hmw) (add_ne_zero hw (by linarith [hx.1]))
        · exact (by fun_prop : Continuous fun x : ℝ => (x - m) ^ 2 / (‖(m : ℂ) + w‖ ^ 2 * |w.im|))
            |>.intervalIntegrable _ _
        · intro x hx
          have hx0 : 0 ≤ x := by linarith [hx.1]
          have hxw : |w.im| ≤ ‖(x : ℂ) + w‖ := vkk x
          rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
            sq_abs]
          apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hxw (by positivity)
    _ = 1 / (3 * ‖(m : ℂ) + w‖ ^ 2 * |w.im|) := by
        rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_right (fun u : ℝ => u ^ 2) m]
        simp only [sub_self, add_sub_cancel_left, integral_pow]
        norm_num
        field_simp
section Seq
variable {w : ℂ}
lemma vnD (hw : 0 < w.re) (n : ℕ) : 0 < ((n : ℂ) + 1 + w).re := by
 simp; positivity
lemma vdT (hw : 0 < w.re) (n : ℕ) : (n : ℂ) + 1 + w ≠ 0 := fun h => by
 have := vnD hw n; rw [h] at this; simp at this
lemma vjn (hw : 0 < w.re) (n : ℕ) : (n : ℝ) + 1 ≤ ‖(n : ℂ) + 1 + w‖ := by
 have h := Complex.re_le_norm ((n : ℂ) + 1 + w)
 simp at h; linarith
lemma vna (hw : 0 < w.re) (n : ℕ) :
  ((n : ℂ) + 1 + w)⁻¹
   = (Complex.log (((n + 1 : ℕ) : ℂ) + 1 + w) - Complex.log ((n : ℂ) + 1 + w))
    + (1 / 2 : ℂ) / ((n : ℂ) + 1 + w) ^ 2 - eps w ((n : ℝ) + 1) := by
 have hm : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
 have h1 := veX hw hm
 have h2 := vcD hw hm
 rw [h2] at h1
 have e1 : ((((n : ℝ) + 1 : ℝ)) : ℂ) + w = (n : ℂ) + 1 + w := by push_cast; ring
 have e2 : ((((n : ℝ) + 1 + 1 : ℝ)) : ℂ) + w = ((n + 1 : ℕ) : ℂ) + 1 + w := by push_cast; ring
 rw [e1, e2] at h1
 linear_combination (-1 : ℂ) * h1
def rho (w : ℂ) (n : ℕ) : ℂ := 1 / (((n : ℂ) + 1 + w) ^ 2 * ((n : ℂ) + 2 + w))
lemma vlz (hw : 0 < w.re) (n : ℕ) :
  1 / ((n : ℂ) + 1 + w) ^ 2
   = (((n : ℂ) + 1 + w)⁻¹ - (((n + 1 : ℕ) : ℂ) + 1 + w)⁻¹) + rho w n := by
 have h1 := vdT hw n
 have h2 := vdT hw (n + 1)
 have e : ((n + 1 : ℕ) : ℂ) + 1 + w = (n : ℂ) + 2 + w := by push_cast; ring
 rw [e] at h2 ⊢
 unfold rho
 field_simp
 ring
lemma vik (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) (n : ℕ) :
  ‖rho w n‖ ≤ 1 / (‖(n : ℂ) + 1 + w‖ ^ 2 * |w.im|) := by
 have h1 := vdT hw n
 have hn2 : |w.im| ≤ ‖(n : ℂ) + 2 + w‖ := by
  have := Complex.abs_im_le_norm ((n : ℂ) + 2 + w); simpa using this
 have ht0 : 0 < |w.im| := by linarith
 unfold rho
 rw [norm_div, norm_one, norm_mul, norm_pow]
 apply div_le_div_of_nonneg_left zero_le_one (by positivity)
 exact mul_le_mul_of_nonneg_left hn2 (by positivity)
lemma vdG (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) (n : ℕ) :
  ‖eps w ((n : ℝ) + 1)‖ ≤ 1 / (3 * ‖(n : ℂ) + 1 + w‖ ^ 2 * |w.im|) := by
 have := vkI hw ht (m := (n : ℝ) + 1) (by positivity)
 rw [show ((((n : ℝ) + 1 : ℝ)) : ℂ) + w = (n : ℂ) + 1 + w by push_cast; ring] at this
 exact this
lemma vlU (hw : 0 < w.re) (N : ℕ) :
  ∑ n ∈ Finset.range N, (1 / ((n : ℂ) + 1) - 1 / (w + n + 1))
   = (∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1))
    - (Complex.log ((N : ℂ) + 1 + w) - Complex.log ((0 : ℕ) + 1 + w : ℂ))
    - (1 / 2 : ℂ) * (((0 : ℕ) + 1 + w : ℂ)⁻¹ - ((N : ℂ) + 1 + w)⁻¹
      + ∑ n ∈ Finset.range N, rho w n)
    + ∑ n ∈ Finset.range N, eps w ((n : ℝ) + 1) := by
 rw [Finset.sum_sub_distrib]
 have hterm : ∀ n ∈ Finset.range N, (1 : ℂ) / (w + n + 1)
   = (Complex.log (((n + 1 : ℕ) : ℂ) + 1 + w) - Complex.log ((n : ℂ) + 1 + w))
    + (1 / 2 : ℂ) * ((((n : ℂ) + 1 + w)⁻¹ - (((n + 1 : ℕ) : ℂ) + 1 + w)⁻¹) + rho w n)
    - eps w ((n : ℝ) + 1) := by
  intro n _
  have A := vna hw n
  have B := vlz hw n
  rw [show (1 : ℂ) / (w + n + 1) = ((n : ℂ) + 1 + w)⁻¹ by rw [one_div]; ring_nf]
  linear_combination A + (1 / 2 : ℂ) * B
 rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib,
  Finset.sum_range_sub (fun n => Complex.log ((n : ℂ) + 1 + w)) N, ← Finset.mul_sum,
  Finset.sum_add_distrib, Finset.sum_range_sub' (fun n => ((n : ℂ) + 1 + w)⁻¹) N]
 push_cast
 ring
lemma vln (hw : 0 < w.re) (n : ℕ) :
  ((n : ℝ) + 1) ^ 2 + w.im ^ 2 ≤ ‖(n : ℂ) + 1 + w‖ ^ 2 := by
 rw [Complex.sq_norm, Complex.normSq_apply]
 have hre : ((n : ℂ) + 1 + w).re = (n : ℝ) + 1 + w.re := by simp
 have him : ((n : ℂ) + 1 + w).im = w.im := by simp
 rw [hre, him]
 nlinarith
lemma vhs (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) (n : ℕ) :
    1 / ‖(n : ℂ) + 1 + w‖ ^ 2 ≤ 2 * (1 / ((n : ℝ) + |w.im|) - 1 / ((n : ℝ) + 1 + |w.im|)) := by
  have h1 := vln hw n
  have ht0 : 0 < |w.im| := by linarith
  have hpos : 0 < ((n : ℝ) + 1) ^ 2 + w.im ^ 2 := by positivity
  have htele : 1 / ((n : ℝ) + |w.im|) - 1 / ((n : ℝ) + 1 + |w.im|)
      = 1 / (((n : ℝ) + |w.im|) * ((n : ℝ) + 1 + |w.im|)) := by
    field_simp; ring
  rw [htele]
  have hsq : w.im ^ 2 = |w.im| ^ 2 := (sq_abs _).symm
  calc 1 / ‖(n : ℂ) + 1 + w‖ ^ 2 ≤ 1 / (((n : ℝ) + 1) ^ 2 + w.im ^ 2) :=
        div_le_div_of_nonneg_left zero_le_one hpos h1
    _ ≤ 2 * (1 / (((n : ℝ) + |w.im|) * ((n : ℝ) + 1 + |w.im|))) := by
        rw [hsq, ← div_eq_mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg ((n : ℝ) + 1 - |w.im|)]
lemma vjI (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) (N : ℕ) :
    ∑ n ∈ Finset.range N, 1 / ‖(n : ℂ) + 1 + w‖ ^ 2 ≤ 2 / |w.im| := by
  have ht0 : 0 < |w.im| := by linarith
  calc ∑ n ∈ Finset.range N, 1 / ‖(n : ℂ) + 1 + w‖ ^ 2
      ≤ ∑ n ∈ Finset.range N, 2 * (1 / ((n : ℝ) + |w.im|) - 1 / ((n : ℝ) + 1 + |w.im|)) :=
        Finset.sum_le_sum fun n _ => vhs hw ht n
    _ = 2 * (1 / |w.im| - 1 / ((N : ℝ) + |w.im|)) := by
        rw [← Finset.mul_sum, Finset.sum_congr rfl (fun (i : ℕ) _ => by
          rw [show ((i : ℝ) + 1 + |w.im|) = (((i + 1 : ℕ) : ℝ) + |w.im|) by push_cast; ring]),
          Finset.sum_range_sub' (fun n : ℕ => 1 / ((n : ℝ) + |w.im|)) N]
        push_cast
        ring
    _ ≤ 2 / |w.im| := by
        have : 0 ≤ 1 / ((N : ℝ) + |w.im|) := by positivity
        rw [div_eq_mul_one_div 2]
        linarith
lemma vbh (hw : 0 < w.re) :
  Summable (fun n : ℕ => 1 / ‖(n : ℂ) + 1 + w‖ ^ 2) := by
 have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
  have := (Real.summable_one_div_nat_pow.mpr one_lt_two)
  exact_mod_cast (summable_nat_add_iff 1).mpr this
 refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
 exact div_le_div_of_nonneg_left zero_le_one (by positivity)
  (pow_le_pow_left₀ (by positivity) (vjn hw n) 2)
lemma vmR (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) : Summable (rho w) := by
 refine Summable.of_norm_bounded ((vbh hw).mul_left (1 / |w.im|)) fun n => ?_
 refine le_trans (vik hw ht n) (le_of_eq ?_)
 field_simp
lemma vmT (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
  Summable (fun n : ℕ => eps w ((n : ℝ) + 1)) := by
 refine Summable.of_norm_bounded ((vbh hw).mul_left (1 / (3 * |w.im|)))
  fun n => ?_
 refine le_trans (vdG hw ht n) (le_of_eq ?_)
 field_simp
lemma vgj (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) : Summable (fun n => ‖rho w n‖) := by
 refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
  ((vbh hw).mul_left (1 / |w.im|))
 refine le_trans (vik hw ht n) (le_of_eq ?_)
 field_simp
lemma vgm (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
  Summable (fun n : ℕ => ‖eps w ((n : ℝ) + 1)‖) := by
 refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
  ((vbh hw).mul_left (1 / (3 * |w.im|)))
 refine le_trans (vdG hw ht n) (le_of_eq ?_)
 field_simp
lemma veT (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
  ∑' n : ℕ, 1 / ‖(n : ℂ) + 1 + w‖ ^ 2 ≤ 2 / |w.im| :=
 Real.tsum_le_of_sum_range_le (fun n => by positivity) (vjI hw ht)
lemma vlc (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    ‖∑' n, rho w n‖ ≤ 2 / w.im ^ 2 := by
  have ht0 : 0 < |w.im| := by linarith
  have hS := veT hw ht
  calc ‖∑' n, rho w n‖ ≤ ∑' n, ‖rho w n‖ := norm_tsum_le_tsum_norm (vgj hw ht)
    _ ≤ ∑' n : ℕ, (1 / |w.im|) * (1 / ‖(n : ℂ) + 1 + w‖ ^ 2) := by
        refine Summable.tsum_le_tsum (fun n => ?_) (vgj hw ht)
          ((vbh hw).mul_left _)
        refine le_trans (vik hw ht n) (le_of_eq ?_)
        field_simp
    _ = (1 / |w.im|) * ∑' n : ℕ, 1 / ‖(n : ℂ) + 1 + w‖ ^ 2 := tsum_mul_left
    _ ≤ (1 / |w.im|) * (2 / |w.im|) := by gcongr
    _ = 2 / w.im ^ 2 := by rw [← sq_abs]; field_simp
lemma vkP (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    ‖∑' n : ℕ, eps w ((n : ℝ) + 1)‖ ≤ (2 / 3) / w.im ^ 2 := by
  have ht0 : 0 < |w.im| := by linarith
  have hS := veT hw ht
  calc ‖∑' n : ℕ, eps w ((n : ℝ) + 1)‖ ≤ ∑' n : ℕ, ‖eps w ((n : ℝ) + 1)‖ :=
        norm_tsum_le_tsum_norm (vgm hw ht)
    _ ≤ ∑' n : ℕ, (1 / (3 * |w.im|)) * (1 / ‖(n : ℂ) + 1 + w‖ ^ 2) := by
        refine Summable.tsum_le_tsum (fun n => ?_) (vgm hw ht)
          ((vbh hw).mul_left _)
        refine le_trans (vdG hw ht n) (le_of_eq ?_)
        field_simp
    _ = (1 / (3 * |w.im|)) * ∑' n : ℕ, 1 / ‖(n : ℂ) + 1 + w‖ ^ 2 := tsum_mul_left
    _ ≤ (1 / (3 * |w.im|)) * (2 / |w.im|) := by gcongr
    _ = (2 / 3) / w.im ^ 2 := by rw [← sq_abs]; field_simp
lemma vgO (hw : 0 < w.re) :
  Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1))
   - Complex.log ((N : ℂ) + 1 + w)) atTop (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
 have hdecomp : ∀ N : ℕ, (∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1))
   - Complex.log ((N : ℂ) + 1 + w)
   = (((harmonic N : ℚ) : ℝ) - Real.log ((N : ℝ) + 1) : ℝ)
    - Complex.log (1 + w / ((N : ℂ) + 1)) := by
  intro N
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hN1 : (N : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero N
  have hq' : 1 + w / ((N : ℂ) + 1) = ((N : ℂ) + 1 + w) / ((N : ℂ) + 1) := by
   field_simp
  have hq : 1 + w / ((N : ℂ) + 1) ≠ 0 := by
   rw [hq']; exact div_ne_zero (vdT hw N) hN1
  have hlog : Complex.log ((N : ℂ) + 1 + w)
    = Real.log ((N : ℝ) + 1) + Complex.log (1 + w / ((N : ℂ) + 1)) := by
   rw [← Complex.log_ofReal_mul hN hq, hq']
   congr 1
   push_cast
   field_simp
  rw [hlog, vaa.vab.vbX.vfR.vlf]
  push_cast
  ring
 simp_rw [hdecomp]
 have h1 : Tendsto (fun N : ℕ => ((((harmonic N : ℚ) : ℝ) - Real.log ((N : ℝ) + 1) : ℝ) : ℂ))
   atTop (𝓝 (Real.eulerMascheroniConstant : ℂ)) :=
  (Complex.continuous_ofReal.tendsto _).comp Real.tendsto_harmonic_sub_log_add_one
 have h2 : Tendsto (fun N : ℕ => Complex.log (1 + w / ((N : ℂ) + 1))) atTop (𝓝 0) := by
  have hq : Tendsto (fun N : ℕ => w / ((N : ℂ) + 1)) atTop (𝓝 0) := by
   rw [tendsto_zero_iff_norm_tendsto_zero]
   have : (fun N : ℕ => ‖w / ((N : ℂ) + 1)‖) = fun N : ℕ => ‖w‖ * (1 / ((N : ℝ) + 1)) := by
    funext N
    rw [norm_div, show ((N : ℂ) + 1) = (((N : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
     Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    ring
   rw [this]
   simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ‖w‖
  have hcont : ContinuousAt Complex.log 1 := continuousAt_clog (by simp)
  have := hcont.tendsto.comp (by simpa using hq.const_add 1)
  simpa [Function.comp_def] using this
 simpa using h1.sub h2
lemma vku (hw : 0 < w.re) :
  Tendsto (fun N : ℕ => ((N : ℂ) + 1 + w)⁻¹) atTop (𝓝 0) := by
 rw [tendsto_zero_iff_norm_tendsto_zero]
 refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
  tendsto_one_div_add_atTop_nhds_zero_nat (fun N => norm_nonneg _) (fun N => ?_)
 rw [norm_inv]
 have h := vjn hw N
 have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
 rw [inv_eq_one_div]
 exact one_div_le_one_div_of_le hpos h
lemma vod (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
  Complex.digamma w = Complex.log (1 + w) - 1 / w - (1 / 2 : ℂ) * (1 + w)⁻¹
   - (1 / 2 : ℂ) * (∑' n, rho w n) + ∑' n : ℕ, eps w ((n : ℝ) + 1) := by
 have hL := (vaa.vab.vbX.vfR.viu hw).tendsto_sum_nat
 have hR : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (1 / ((n : ℂ) + 1) - 1 / (w + n + 1)))
   atTop (𝓝 ((Real.eulerMascheroniConstant : ℂ) + Complex.log (1 + w)
    - (1 / 2 : ℂ) * ((1 + w)⁻¹ - 0 + ∑' n, rho w n) + ∑' n : ℕ, eps w ((n : ℝ) + 1))) := by
  have e : ∀ N : ℕ, ∑ n ∈ Finset.range N, (1 / ((n : ℂ) + 1) - 1 / (w + n + 1))
    = ((∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1)) - Complex.log ((N : ℂ) + 1 + w))
     + Complex.log (1 + w)
     - (1 / 2 : ℂ) * ((1 + w)⁻¹ - ((N : ℂ) + 1 + w)⁻¹ + ∑ n ∈ Finset.range N, rho w n)
     + ∑ n ∈ Finset.range N, eps w ((n : ℝ) + 1) := by
   intro N
   rw [vlU hw N]
   push_cast
   ring
  simp_rw [e]
  refine (((vgO hw).add tendsto_const_nhds).sub
   (((tendsto_const_nhds.sub (vku hw)).add
    (vmR hw ht).hasSum.tendsto_sum_nat).const_mul _)).add
   (vmT hw ht).hasSum.tendsto_sum_nat
 have := tendsto_nhds_unique hL hR
 rw [sub_zero] at this
 linear_combination this
lemma vjE (hw : 0 < w.re) :
  Complex.log (1 + w) - Complex.log w = w⁻¹ - (1 / 2 : ℂ) / w ^ 2 + eps w 0 := by
 have h1 := veX hw (m := 0) le_rfl
 have h2 := vcD hw (m := 0) le_rfl
 rw [h2] at h1
 simpa [add_comm] using h1
lemma vld (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) : ‖eps w 0‖ ≤ (1 / 3) / |w.im| ^ 3 := by
  have h := vkI hw ht (m := 0) le_rfl
  have ht0 : 0 < |w.im| := by linarith
  have hw' : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
  simp only [Complex.ofReal_zero, zero_add] at h
  calc ‖eps w 0‖ ≤ 1 / (3 * ‖w‖ ^ 2 * |w.im|) := h
    _ ≤ 1 / (3 * |w.im| ^ 2 * |w.im|) := by
        apply div_le_div_of_nonneg_left zero_le_one (by positivity)
        gcongr
    _ = (1 / 3) / |w.im| ^ 3 := by field_simp
lemma vlb (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    ‖Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w‖ ≤ 3 / w.im ^ 2 := by
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
  have h1w : 1 + w ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have ht0 : 0 < |w.im| := by linarith
  have hwn : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
  have h1wn : |w.im| ≤ ‖1 + w‖ := by have := Complex.abs_im_le_norm (1 + w); simpa using this
  have hid := vod hw ht
  have hlog := vjE hw
  have key : Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w
      = -(1 / 2 : ℂ) / (w ^ 2 * (1 + w)) + eps w 0
        - (1 / 2 : ℂ) * (∑' n, rho w n) + ∑' n : ℕ, eps w ((n : ℝ) + 1) := by
    rw [hid, show Complex.log (1 + w) = Complex.log w + (w⁻¹ - (1 / 2 : ℂ) / w ^ 2 + eps w 0) by
      rw [← hlog]; ring]
    field_simp
    ring
  rw [key]
  have hsq : |w.im| ^ 2 = w.im ^ 2 := sq_abs _
  have b1 : ‖-(1 / 2 : ℂ) / (w ^ 2 * (1 + w))‖ ≤ (1 / 2) / w.im ^ 2 := by
    rw [norm_div, norm_neg, norm_mul, norm_pow]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [this, ← hsq]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have h1 : 1 ≤ ‖1 + w‖ := le_trans (by simp; linarith) (Complex.re_le_norm (1 + w))
    calc |w.im| ^ 2 = |w.im| ^ 2 * 1 := (mul_one _).symm
      _ ≤ ‖w‖ ^ 2 * ‖1 + w‖ := by gcongr
  have b2 : ‖eps w 0‖ ≤ (2 / 3) / w.im ^ 2 := by
    refine le_trans (vld hw ht) ?_
    rw [← hsq, div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : |w.im| ^ 3 = |w.im| ^ 2 * |w.im| := by ring
    rw [h3]
    have : 0 < |w.im| ^ 2 := by positivity
    nlinarith
  have b3 : ‖(1 / 2 : ℂ) * ∑' n, rho w n‖ ≤ 1 / w.im ^ 2 := by
    rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    have h := mul_le_mul_of_nonneg_left (vlc hw ht) (by norm_num : (0:ℝ) ≤ 1 / 2)
    calc 1 / 2 * ‖∑' n, rho w n‖ ≤ 1 / 2 * (2 / w.im ^ 2) := h
      _ = 1 / w.im ^ 2 := by ring
  have b4 := vkP hw ht
  calc ‖-(1 / 2 : ℂ) / (w ^ 2 * (1 + w)) + eps w 0 - (1 / 2 : ℂ) * ∑' n, rho w n
        + ∑' n : ℕ, eps w ((n : ℝ) + 1)‖
      ≤ ‖-(1 / 2 : ℂ) / (w ^ 2 * (1 + w))‖ + ‖eps w 0‖ + ‖(1 / 2 : ℂ) * ∑' n, rho w n‖
        + ‖∑' n : ℕ, eps w ((n : ℝ) + 1)‖ := by
        have s1 := norm_add_le (-(1 / 2 : ℂ) / (w ^ 2 * (1 + w)) + eps w 0 - (1 / 2 : ℂ) * ∑' n, rho w n)
          (∑' n : ℕ, eps w ((n : ℝ) + 1))
        have s2 := norm_sub_le (-(1 / 2 : ℂ) / (w ^ 2 * (1 + w)) + eps w 0) ((1 / 2 : ℂ) * ∑' n, rho w n)
        have s3 := norm_add_le (-(1 / 2 : ℂ) / (w ^ 2 * (1 + w))) (eps w 0)
        linarith
    _ ≤ (1 / 2) / w.im ^ 2 + (2 / 3) / w.im ^ 2 + 1 / w.im ^ 2 + (2 / 3) / w.im ^ 2 := by
        gcongr
    _ ≤ 3 / w.im ^ 2 := by
        have hpos : 0 < w.im ^ 2 := by rw [← hsq]; positivity
        rw [show (1 / 2) / w.im ^ 2 + (2 / 3) / w.im ^ 2 + 1 / w.im ^ 2 + (2 / 3) / w.im ^ 2
          = (17 / 6) / w.im ^ 2 by ring]
        apply div_le_div_of_nonneg_right _ hpos.le
        norm_num
end Seq
end vjL
end vaa.vab.vbX
end
end
section
open Complex Real
namespace vaa.vab.vaF
lemma vgL {a t : ℝ}
  (ha : 1 / 2 ≤ a) (ha' : a ≤ 3 / 2) (ht : 50 ≤ t) :
  |(Complex.digamma ((a : ℂ) + t * I)).re - Real.log t| ≤ 9 / (2 * t ^ 2) := by
 let w : ℂ := (a : ℂ) + t * I
 have ha0 : 0 < a := by linarith
 have ht0 : 0 < t := by linarith
 have hre : w.re = a := by simp [w]
 have him : w.im = t := by simp [w]
 have hw : 0 < w.re := by simpa [hre] using ha0
 have hD : 0 < a ^ 2 + t ^ 2 := by positivity
 have hmain := vaa.vab.vbX.vjL.vlb hw
  (by rw [him, abs_of_pos ht0]; linarith)
 rw [him] at hmain
 have hlogre : (Complex.log w).re = Real.log (a ^ 2 + t ^ 2) / 2 := by
  rw [Complex.log_re, show ‖w‖ = Real.sqrt (a ^ 2 + t ^ 2) by
   rw [Complex.norm_eq_sqrt_sq_add_sq, hre, him], Real.log_sqrt hD.le]
 have hinvre : ((1 / 2 : ℂ) / w).re = a / (2 * (a ^ 2 + t ^ 2)) := by
  rw [show (1 / 2 : ℂ) / w = ((1 / 2 : ℝ) : ℂ) * w⁻¹ by push_cast; ring,
   Complex.re_ofReal_mul, Complex.inv_re, Complex.normSq_apply, hre, him]
  field_simp
 have hR : |(Complex.digamma w).re - Real.log (a ^ 2 + t ^ 2) / 2 +
   a / (2 * (a ^ 2 + t ^ 2))| ≤ 3 / t ^ 2 := by
  have h := (Complex.abs_re_le_norm _).trans hmain
  simpa only [Complex.add_re, Complex.sub_re, hlogre, hinvre] using h
 have hlog : 0 ≤ Real.log (a ^ 2 + t ^ 2) / 2 - Real.log t ∧
   Real.log (a ^ 2 + t ^ 2) / 2 - Real.log t ≤ 9 / (8 * t ^ 2) := by
  have he : a ^ 2 + t ^ 2 = t ^ 2 * (1 + a ^ 2 / t ^ 2) := by
   field_simp
   ring
  rw [he, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have hl0 : 0 ≤ Real.log (1 + a ^ 2 / t ^ 2) :=
   Real.log_nonneg (le_add_of_nonneg_right (by positivity))
  have hl1 := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + a ^ 2 / t ^ 2)
  have ha2 : a ^ 2 ≤ 9 / 4 := by nlinarith
  have hq : a ^ 2 / t ^ 2 ≤ (9 / 4) / t ^ 2 :=
   div_le_div_of_nonneg_right ha2 (sq_nonneg t)
  ring_nf at hq hl0 hl1 ⊢
  constructor <;> linarith
 have hi : 0 ≤ a / (2 * (a ^ 2 + t ^ 2)) ∧
   a / (2 * (a ^ 2 + t ^ 2)) ≤ 3 / (4 * t ^ 2) := by
  constructor
  ·positivity
  ·rw [div_le_div_iff₀ (by positivity) (by positivity)]
   nlinarith [mul_nonneg (by linarith : 0 ≤ 3 / 2 - a) (sq_nonneg t)]
 rw [abs_le] at hR ⊢
 change -(9 / (2 * t ^ 2)) ≤ (Complex.digamma w).re - Real.log t ∧
  (Complex.digamma w).re - Real.log t ≤ 9 / (2 * t ^ 2)
 have ht2 : 0 < t ^ 2 := by positivity
 ring_nf at hR hlog hi ⊢
 constructor <;> nlinarith [hR.1, hR.2, hlog.1, hlog.2, hi.1, hi.2,
  sq_nonneg t⁻¹]
end vaa.vab.vaF
end
section
open Complex Real Set
open scoped RealInnerProductSpace
namespace vaa.vab.vaF
lemma vjq {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
  (hf : HasDerivAt f f' x) (hne : f x ≠ 0) :
  HasDerivAt (fun u => Real.log ‖f u‖) (f' / f x).re x := by
 have hn : ‖f x‖ ≠ 0 := norm_ne_zero_iff.mpr hne
 have h := (hf.norm_sq.log (pow_ne_zero 2 hn)).div_const 2
 have e1 : (fun u => Real.log ‖f u‖) = fun x => Real.log (‖f x‖ ^ 2) / 2 := by
  funext u
  rw [Real.log_pow]
  push_cast
  ring
 rw [e1]
 refine h.congr_deriv ?_
 symm
 rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply, Complex.div_re,
  Complex.sq_norm]
 change f'.re * (f x).re / Complex.normSq (f x) +
  f'.im * (f x).im / Complex.normSq (f x) =
  2 * (f' * (starRingEnd ℂ) (f x)).re / Complex.normSq (f x) / 2
 simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
 ring
lemma vgK {a t : ℝ} (ha : 0 < a) :
  HasDerivAt (fun x : ℝ => Real.log ‖Complex.Gamma ((x : ℂ) + t * I)‖)
   (Complex.digamma ((a : ℂ) + t * I)).re a := by
 have hz : 0 < ((a : ℂ) + t * I).re := by simpa using ha
 have hne := vac.vat (s := (a : ℂ) + t * I) hz
 have hG := (Complex.differentiableAt_Gamma _ hne).hasDerivAt
 have hC := hG.comp (a : ℂ) ((hasDerivAt_id (a : ℂ)).add_const ((t : ℂ) * I))
 have hreal : HasDerivAt (fun x : ℝ => Complex.Gamma ((x : ℂ) + t * I))
   (deriv Complex.Gamma ((a : ℂ) + t * I)) a := by
  simpa using hC.comp_ofReal
 have h := vjq hreal (Complex.Gamma_ne_zero hne)
 simpa [Complex.digamma_def, logDeriv_apply] using h
lemma vgF {a t : ℝ}
  (ha : 1 / 2 ≤ a) (ha' : a ≤ 3 / 2) (ht : 50 ≤ t) :
  |Real.log ‖Complex.Gamma ((a : ℂ) + t * I)‖ -
   Real.log ‖Complex.Gamma (1 + t * I)‖ - (a - 1) * Real.log t| ≤
   9 / (4 * t ^ 2) := by
 let f : ℝ → ℝ := fun x => Real.log ‖Complex.Gamma ((x : ℂ) + t * I)‖ - x * Real.log t
 let f' : ℝ → ℝ := fun x => (Complex.digamma ((x : ℂ) + t * I)).re - Real.log t
 have hd : ∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2), HasDerivWithinAt f (f' x)
   (Icc (1 / 2 : ℝ) (3 / 2)) x := by
  intro x hx
  exact (((vgK (t := t)
   (by linarith [hx.1] : 0 < x)).sub
    ((hasDerivAt_id x).mul_const (Real.log t))).congr_deriv (by simp [f'])).hasDerivWithinAt
 have hb : ∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2), ‖f' x‖ ≤ 9 / (2 * t ^ 2) := by
  intro x hx
  simpa [f', Real.norm_eq_abs] using vgL hx.1 hx.2 ht
 have h := (convex_Icc (1 / 2 : ℝ) (3 / 2)).norm_image_sub_le_of_norm_hasDerivWithin_le
  hd hb (x := 1) (y := a) (by norm_num) ⟨ha, ha'⟩
 have hdist : |a - 1| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
 have hc : 0 ≤ 9 / (2 * t ^ 2) := by positivity
 have h' := h.trans (mul_le_mul_of_nonneg_left
  (show ‖a - 1‖ ≤ (1 / 2 : ℝ) by simpa [Real.norm_eq_abs] using hdist) hc)
 rw [Real.norm_eq_abs] at h'
 have e3 : f a - f 1 = Real.log ‖Complex.Gamma ((a : ℂ) + t * I)‖ -
   Real.log ‖Complex.Gamma (1 + t * I)‖ - (a - 1) * Real.log t := by
  simp only [f]
  push_cast
  ring
 rw [e3] at h'
 exact h'.trans (le_of_eq (by ring))
lemma vhy {a t : ℝ}
  (ha : 1 / 2 ≤ a) (ha' : a ≤ 3 / 2) (ht : 50 ≤ t) :
  ‖Complex.Gamma ((a : ℂ) + t * I)‖ ≤
   ‖Complex.Gamma (1 + t * I)‖ * t ^ (a - 1) * Real.exp (9 / (4 * t ^ 2)) := by
 have h := (abs_le.mp (vgF ha ha' ht)).2
 have hGa : 0 < ‖Complex.Gamma ((a : ℂ) + t * I)‖ := by
  apply norm_pos_iff.mpr
  apply Complex.Gamma_ne_zero_of_re_pos
  simp
  linarith
 have hG1 : 0 < ‖Complex.Gamma (1 + t * I)‖ := by
  apply norm_pos_iff.mpr
  apply Complex.Gamma_ne_zero_of_re_pos
  norm_num
 have ht0 : 0 < t := by linarith
 have he := Real.exp_le_exp.mpr (show
  Real.log ‖Complex.Gamma ((a : ℂ) + t * I)‖ ≤
   Real.log ‖Complex.Gamma (1 + t * I)‖ + (a - 1) * Real.log t +
    9 / (4 * t ^ 2) by linarith)
 rw [Real.exp_log hGa, Real.exp_add, Real.exp_add, Real.exp_log hG1] at he
 rw [Real.rpow_def_of_pos ht0]
 simpa [mul_comm (a - 1) (Real.log t)] using he
end vaa.vab.vaF
end
section
open Complex Real
open scoped ComplexConjugate
namespace vaa.vab.vaP
lemma vjA (z : ℂ) : ‖Complex.cos z‖ ≤ Real.cosh z.im := by
 rw [Complex.cos, norm_div, Complex.norm_ofNat]
 calc
  _ ≤ (‖Complex.exp (z * I)‖ + ‖Complex.exp (-z * I)‖) / 2 := by
   gcongr
   exact norm_add_le _ _
  _ = Real.cosh z.im := by
   rw [Complex.norm_exp_mul_I, Complex.norm_exp_mul_I, Complex.neg_im, neg_neg,
    Real.cosh_eq]
   ring
lemma vei {t : ℝ} (ht : 0 < t) :
  Real.cosh (Real.pi * t / 2) / Real.sinh (Real.pi * t / 2) =
   (1 + Real.exp (-Real.pi * t)) / (1 - Real.exp (-Real.pi * t)) := by
 have h : 0 < Real.pi * t / 2 := by positivity
 have he : Real.exp (-Real.pi * t) = (Real.exp (Real.pi * t / 2))⁻¹ ^ 2 := by
  rw [← Real.exp_neg, ← Real.exp_nat_mul]
  congr 1
  ring
 have hp : 1 < Real.exp (Real.pi * t / 2) := Real.one_lt_exp_iff.mpr h
 have hn : Real.exp (Real.pi * t / 2) ≠ 0 := (Real.exp_pos _).ne'
 rw [he, Real.cosh_eq, Real.sinh_eq, Real.exp_neg]
 field_simp <;> ring
lemma vjz {t : ℝ} (ht : 0 < t) :
  ‖Complex.Gamma (1 + (t : ℂ) * I)‖ * Real.cosh (Real.pi * t / 2) / Real.pi =
   Real.sqrt (t / (2 * Real.pi)) *
    Real.sqrt ((1 + Real.exp (-Real.pi * t)) / (1 - Real.exp (-Real.pi * t))) := by
 have hs : 0 < Real.sinh (Real.pi * t / 2) := Real.sinh_pos_iff.mpr (by positivity)
 have hc : 0 < Real.cosh (Real.pi * t / 2) := Real.cosh_pos _
 have hd : Real.sinh (Real.pi * t) =
   2 * Real.sinh (Real.pi * t / 2) * Real.cosh (Real.pi * t / 2) := by
  convert Real.sinh_two_mul (x := Real.pi * t / 2) using 1 <;> ring
 have hq : 0 ≤ (1 + Real.exp (-Real.pi * t)) / (1 - Real.exp (-Real.pi * t)) := by
  rw [← vei ht]
  positivity
 have he : (‖Complex.Gamma (1 + (t : ℂ) * I)‖ * Real.cosh (Real.pi * t / 2) / Real.pi) ^ 2 =
   t / (2 * Real.pi) * ((1 + Real.exp (-Real.pi * t)) / (1 - Real.exp (-Real.pi * t))) := by
  rw [div_pow, mul_pow, ven.vfC ht,
   ← vei ht, hd]
  field_simp <;> ring
 have hs1 := Real.sq_sqrt (by positivity : 0 ≤ t / (2 * Real.pi))
 have hs2 := Real.sq_sqrt hq
 have hprod : (Real.sqrt (t / (2 * Real.pi)) *
   Real.sqrt ((1 + Real.exp (-Real.pi * t)) / (1 - Real.exp (-Real.pi * t)))) ^ 2 =
   t / (2 * Real.pi) * ((1 + Real.exp (-Real.pi * t)) / (1 - Real.exp (-Real.pi * t))) := by
  rw [mul_pow, hs1, hs2]
 have hL : 0 ≤ ‖Complex.Gamma (1 + (t : ℂ) * I)‖ * Real.cosh (Real.pi * t / 2) / Real.pi := by positivity
 have hR : 0 ≤ Real.sqrt (t / (2 * Real.pi)) *
   Real.sqrt ((1 + Real.exp (-Real.pi * t)) / (1 - Real.exp (-Real.pi * t))) := by positivity
 nlinarith
lemma vjy {t : ℝ} (ht : 0 < t) (σ : ℝ) :
  (2 * Real.pi) ^ σ * t ^ (-σ) * Real.sqrt (t / (2 * Real.pi)) =
   (t / (2 * Real.pi)) ^ (1 / 2 - σ) := by
 have hp : 0 < 2 * Real.pi := by positivity
 have hd : 0 < t / (2 * Real.pi) := div_pos ht hp
 rw [Real.sqrt_eq_rpow]
 simp only [Real.rpow_def_of_pos hp, Real.rpow_def_of_pos ht,
  Real.rpow_def_of_pos hd]
 rw [← Real.exp_add, ← Real.exp_add, Real.log_div ht.ne' hp.ne']
 congr 1
 ring
lemma vgY {σ t : ℝ}
  (hσ : -(1 / 2 : ℝ) ≤ σ) (hσ' : σ ≤ 1 / 2) (ht : 50 ≤ t) :
  ‖vgv ((σ : ℂ) + t * I)‖ ≤
   (t / (2 * Real.pi)) ^ (1 / 2 - σ) * Real.exp (5 / (2 * t ^ 2)) := by
 have ht0 : 0 < t := by linarith
 have hp : 0 < 2 * Real.pi := by positivity
 have hG : ‖Complex.Gamma (1 - ((σ : ℂ) + t * I))‖ ≤
   ‖Complex.Gamma (1 + (t : ℂ) * I)‖ * t ^ (-σ) * Real.exp (9 / (4 * t ^ 2)) := by
  have he : 1 - ((σ : ℂ) + t * I) = conj (((1 - σ : ℝ) : ℂ) + t * I) := by
   simp
   push_cast
   ring
  rw [he, Complex.Gamma_conj, norm_conj]
  convert vaF.vhy
   (a := 1 - σ) (t := t) (by linarith) (by linarith) ht using 1 <;> ring
 have hP : ‖(2 * (Real.pi : ℂ)) ^ (-(1 - ((σ : ℂ) + t * I)))‖ =
   (2 * Real.pi) ^ (σ - 1) := by
  have he : 2 * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  rw [he, Complex.norm_cpow_eq_rpow_re_of_pos hp]
  congr 1
  simp <;> ring
 have hC : ‖Complex.cos ((Real.pi : ℂ) * (1 - ((σ : ℂ) + t * I)) / 2)‖ ≤
   Real.cosh (Real.pi * t / 2) := by
  have he : (((Real.pi : ℂ) * (1 - ((σ : ℂ) + t * I)) / 2)).im = -(Real.pi * t / 2) := by
   simp [Complex.div_ofNat_im, Complex.mul_im] <;> ring
  simpa [he, Real.cosh_neg] using vjA
   ((Real.pi : ℂ) * (1 - ((σ : ℂ) + t * I)) / 2)
 have hpow : 2 * (2 * Real.pi) ^ (σ - 1) = (2 * Real.pi) ^ σ / Real.pi := by
  rw [Real.rpow_sub hp, Real.rpow_one]
  field_simp
 unfold vgv
 rw [norm_mul, norm_mul, norm_mul, hP, Complex.norm_ofNat]
 calc
  _ ≤ 2 * (2 * Real.pi) ^ (σ - 1) *
    (‖Complex.Gamma (1 + (t : ℂ) * I)‖ * t ^ (-σ) * Real.exp (9 / (4 * t ^ 2))) *
    Real.cosh (Real.pi * t / 2) := by gcongr
  _ = ((2 * Real.pi) ^ σ * t ^ (-σ) * Real.sqrt (t / (2 * Real.pi))) *
    Real.sqrt ((1 + Real.exp (-Real.pi * t)) / (1 - Real.exp (-Real.pi * t))) *
    Real.exp (9 / (4 * t ^ 2)) := by
   rw [hpow]
   have he := vjz ht0
   calc
    _ = ((2 * Real.pi) ^ σ * t ^ (-σ)) *
      (‖Complex.Gamma (1 + (t : ℂ) * I)‖ * Real.cosh (Real.pi * t / 2) / Real.pi) *
      Real.exp (9 / (4 * t ^ 2)) := by ring
    _ = _ := by rw [he]; ring
  _ ≤ (t / (2 * Real.pi)) ^ (1 / 2 - σ) * Real.exp (1 / (4 * t ^ 2)) *
    Real.exp (9 / (4 * t ^ 2)) := by
   rw [vjy ht0]
   gcongr
   exact vdj.vkp ht
  _ = _ := by
   rw [mul_assoc, ← Real.exp_add]
   congr 2
   ring
lemma vcv {σ t : ℝ}
  (hσ : -(1 / 2 : ℝ) ≤ σ) (hσ' : σ ≤ 1 / 2) (ht : 50 ≤ t) :
  ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤
   (t / (2 * Real.pi)) ^ (1 / 2 - σ) * Real.exp (5 / (2 * t ^ 2)) *
    ‖riemannZeta (((1 - σ : ℝ) : ℂ) + t * I)‖ := by
 have ht0 : 0 < t := by linarith
 rw [functional_equation (by simpa using ht0.ne'), norm_mul]
 have he : 1 - ((σ : ℂ) + t * I) = conj (((1 - σ : ℝ) : ℂ) + t * I) := by
  simp
  push_cast
  ring
 rw [he, riemannZeta_conj, norm_conj]
 exact mul_le_mul_of_nonneg_right (vgY hσ hσ' ht) (norm_nonneg _)
end vaa.vab.vaP
end
section
open Complex MeasureTheory Set Filter
open scoped Interval Topology
namespace vaa.vab.vdO
noncomputable def vbH (a x : ℝ) : ℂ := ((x - a - 1 / 2 : ℝ) : ℂ)
noncomputable def vbK (a x : ℝ) : ℂ :=
 (((x - a) ^ 2 - (x - a) + 1 / 6 : ℝ) / 2 : ℝ)
lemma vin (a x : ℝ) :
  HasDerivAt (vbH a) 1 x := by
 unfold vbH
 convert (((hasDerivAt_id x).sub_const a).sub_const (1 / 2)).ofReal_comp using 1 <;> simp
lemma vhF (a x : ℝ) :
  HasDerivAt (vbK a) (vbH a x) x := by
 unfold vbK vbH
 convert ((((hasDerivAt_id x).sub_const a).pow 2).sub
  ((hasDerivAt_id x).sub_const a) |>.add_const (1 / 6) |>.div_const 2).ofReal_comp using 1 <;>
  simp <;> ring
lemma viK (a : ℝ) {x : ℝ} (hx : x ∈ Icc a (a + 1)) :
  ‖vbK a x‖ ≤ 1 / 12 := by
 rw [vbK, Complex.norm_real, Real.norm_eq_abs, abs_le]
 have hu : 0 ≤ x - a := by linarith [hx.1]
 have hv : x - a ≤ 1 := by linarith [hx.2]
 have hp : (x - a) ^ 2 ≤ x - a := by nlinarith
 constructor <;> nlinarith [sq_nonneg (x - a - 1 / 2)]
lemma vml {f g h : ℝ → ℂ} {a : ℝ}
  (hf : ∀ x ∈ Icc a (a + 1), HasDerivAt f (g x) x)
  (hg : ∀ x ∈ Icc a (a + 1), HasDerivAt g (h x) x)
  (hgi : IntervalIntegrable g volume a (a + 1))
  (hhi : IntervalIntegrable h volume a (a + 1)) :
  (f a + f (a + 1)) / 2 - (∫ x in a..a + 1, f x)
   - (g (a + 1) - g a) / 12 =
   -(∫ x in a..a + 1, vbK a x * h x) := by
 have hab : a ≤ a + 1 := by linarith
 have hfi : IntervalIntegrable f volume a (a + 1) := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  exact fun x hx => (hf x hx).continuousAt.continuousWithinAt
 have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
  (u := vbH a) (u' := fun _ => (1 : ℂ)) (v := f) (v' := g)
  (fun x _ => vin a x)
  (fun x hx => hf x (by simpa [uIcc_of_le hab] using hx))
  intervalIntegrable_const hgi
 have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
  (u := vbK a) (u' := vbH a) (v := g) (v' := h)
  (fun x _ => vhF a x)
  (fun x hx => hg x (by simpa [uIcc_of_le hab] using hx))
  ((show Continuous (vbH a) by unfold vbH; fun_prop).intervalIntegrable _ _) hhi
 simp only [one_mul] at h1
 rw [h1] at h2
 norm_num [vbH, vbK] at h2
 unfold vbK
 push_cast
 linear_combination h2
lemma vmg {f g h : ℝ → ℂ} {a : ℝ}
  (hf : ∀ x ∈ Icc a (a + 1), HasDerivAt f (g x) x)
  (hg : ∀ x ∈ Icc a (a + 1), HasDerivAt g (h x) x)
  (hgi : IntervalIntegrable g volume a (a + 1))
  (hhi : IntervalIntegrable h volume a (a + 1)) :
  ‖(f a + f (a + 1)) / 2 - (∫ x in a..a + 1, f x)
   - (g (a + 1) - g a) / 12‖ ≤
   (1 / 12 : ℝ) * ∫ x in a..a + 1, ‖h x‖ := by
 rw [vml hf hg hgi hhi, norm_neg, ← intervalIntegral.integral_const_mul]
 apply intervalIntegral.norm_integral_le_of_norm_le (by linarith) _ (hhi.norm.const_mul _)
 ·filter_upwards with x hx
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (viK a ⟨hx.1.le, hx.2⟩) (norm_nonneg _)
lemma vlD {f g h : ℝ → ℂ} (N M : ℕ) (hNM : N ≤ M)
  (hf : ∀ x : ℝ, (N : ℝ) ≤ x → HasDerivAt f (g x) x)
  (hg : ∀ x : ℝ, (N : ℝ) ≤ x → HasDerivAt g (h x) x)
  (hc : ContinuousOn h (Ici (N : ℝ))) :
  ‖(∑ k ∈ Finset.Ico N M, f k) + (f M - f N) / 2
    - (∫ x in (N : ℝ)..M, f x) - (g M - g N) / 12‖ ≤
   (1 / 12 : ℝ) * ∫ x in (N : ℝ)..M, ‖h x‖ := by
 have hfc : ContinuousOn f (Ici (N : ℝ)) :=
  fun x hx => (hf x hx).continuousAt.continuousWithinAt
 have hgc : ContinuousOn g (Ici (N : ℝ)) :=
  fun x hx => (hg x hx).continuousAt.continuousWithinAt
 have hint {u v : ℝ} (hu : (N : ℝ) ≤ u) (huv : u ≤ v) :
   IntervalIntegrable f volume u v ∧ IntervalIntegrable g volume u v ∧
    IntervalIntegrable h volume u v := by
  have hsub : uIcc u v ⊆ Ici (N : ℝ) := by
   rw [uIcc_of_le huv]
   exact fun x hx => hu.trans hx.1
  exact ⟨(hfc.mono hsub).intervalIntegrable,
   (hgc.mono hsub).intervalIntegrable, (hc.mono hsub).intervalIntegrable⟩
 induction M, hNM using Nat.le_induction with
 | base => simp
 | succ M hNM ih =>
  have hNM' : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have hM1 : (M : ℝ) ≤ M + 1 := by linarith
  have hI1 := hint (u := N) (v := M) le_rfl hNM'
  have hI2 := hint (u := M) (v := M + 1) hNM' hM1
  have hloc := vmg (a := (M : ℝ))
   (fun x hx => hf x (hNM'.trans hx.1))
   (fun x hx => hg x (hNM'.trans hx.1)) hI2.2.1 hI2.2.2
  have hsumF := intervalIntegral.integral_add_adjacent_intervals hI1.1 hI2.1
  have hsumH := intervalIntegral.integral_add_adjacent_intervals hI1.2.2.norm hI2.2.2.norm
  rw [Finset.sum_Ico_succ_top hNM]
  push_cast
  calc
   _ = ‖((∑ k ∈ Finset.Ico N M, f k) + (f M - f N) / 2
     - (∫ x in (N : ℝ)..M, f x) - (g M - g N) / 12)
     + ((f M + f (M + 1)) / 2 - (∫ x in (M : ℝ)..M + 1, f x)
      - (g (M + 1) - g M) / 12)‖ := by
    congr 1
    rw [← hsumF]
    ring
   _ ≤ ‖(∑ k ∈ Finset.Ico N M, f k) + (f M - f N) / 2
     - (∫ x in (N : ℝ)..M, f x) - (g M - g N) / 12‖
     + ‖(f M + f (M + 1)) / 2 - (∫ x in (M : ℝ)..M + 1, f x)
      - (g (M + 1) - g M) / 12‖ := norm_add_le _ _
   _ ≤ (1 / 12 : ℝ) * (∫ x in (N : ℝ)..M, ‖h x‖)
     + (1 / 12 : ℝ) * (∫ x in (M : ℝ)..M + 1, ‖h x‖) :=
    add_le_add ih hloc
   _ = (1 / 12 : ℝ) * ∫ x in (N : ℝ)..M + 1, ‖h x‖ := by
    rw [← mul_add, hsumH]
lemma veP {f g h : ℝ → ℂ} (N : ℕ) {L : ℂ}
  (hf : ∀ x : ℝ, (N : ℝ) ≤ x → HasDerivAt f (g x) x)
  (hg : ∀ x : ℝ, (N : ℝ) ≤ x → HasDerivAt g (h x) x)
  (hc : ContinuousOn h (Ici (N : ℝ)))
  (hsumint : Tendsto (fun M : ℕ => (∑ k ∈ Finset.Ico N M, f k) -
   (∫ x in (N : ℝ)..M, f x)) atTop (𝓝 L))
  (hf0 : Tendsto (fun M : ℕ => f M) atTop (𝓝 0))
  (hg0 : Tendsto (fun M : ℕ => g M) atTop (𝓝 0))
  (hhi : IntegrableOn h (Ioi (N : ℝ))) :
  ‖L - f N / 2 + g N / 12‖ ≤
   (1 / 12 : ℝ) * ∫ x in Ioi (N : ℝ), ‖h x‖ := by
 have hIH := intervalIntegral_tendsto_integral_Ioi (N : ℝ) hhi.norm
  tendsto_natCast_atTop_atTop
 have hL := ((hsumint.add ((hf0.sub_const (f N)).div_const 2)).sub
  ((hg0.sub_const (g N)).div_const 12)).norm
 have hR := hIH.const_mul (1 / 12 : ℝ)
 have hlim := le_of_tendsto_of_tendsto hL hR
  (show ∀ᶠ M : ℕ in atTop,
   ‖((∑ k ∈ Finset.Ico N M, f k) - (∫ x in (N : ℝ)..M, f x)) +
    (f M - f N) / 2 - (g M - g N) / 12‖ ≤
    (1 / 12 : ℝ) * ∫ x in (N : ℝ)..M, ‖h x‖ from by
   filter_upwards [eventually_ge_atTop N] with M hM
   convert vlD N M hM hf hg hc using 1 <;> congr 1 <;> ring)
 convert hlim using 1 <;> congr 1 <;> ring
end vaa.vab.vdO
end
section
open Complex Metric Set Filter Topology
namespace vaa.vaz
variable {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
noncomputable abbrev divB (f : ℂ → ℂ) (c : ℂ) (R : ℝ) := MeromorphicOn.divisor f (closedBall c R)
lemma vfp (f : ℂ → ℂ) (c : ℂ) (R : ℝ) : (divB f c R).support.Finite :=
 (divB f c R).finiteSupport (isCompact_closedBall c R)
noncomputable def vbM (f : ℂ → ℂ) (c : ℂ) (R r : ℝ) : Finset ℂ :=
 (vfp f c R).toFinset.filter fun u => ‖u - c‖ < r
lemma vis (hR : 0 < R) : Preperfect (closedBall c R) := by
 rw [← closure_ball c hR.ne']
 exact (isOpen_ball.preperfect).perfect_closure.acc
lemma vnJ (hf : Differentiable ℂ f) (hfc : f c ≠ 0) (hR : 0 < R) :
  ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall c R) ∧ (∀ z ∈ ball c (R / 2), g z ≠ 0) ∧
   ∀ z ∈ closedBall c R,
    f z = (∏ u ∈ vbM f c R (R / 2), (z - u) ^ (divB f c R u).toNat) * g z := by
 have hfa : AnalyticOnNhd ℂ f (closedBall c R) := fun z _ => hf.analyticAt z
 have hfa' : AnalyticOnNhd ℂ f univ := fun z _ => hf.analyticAt z
 have hc0 : analyticOrderAt f c ≠ ⊤ := by
  rw [(hf.analyticAt c).analyticOrderAt_eq_zero.2 hfc]; simp
 have h₂f : ∀ u : closedBall c R, meromorphicOrderAt f u ≠ ⊤ := fun u => by
  rw [(hf.analyticAt u).meromorphicOrderAt_eq]
  have := hfa'.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ c)
   (mem_univ (u : ℂ)) hc0
  intro h
  apply this
  cases hk : analyticOrderAt f u <;> simp_all
 obtain ⟨g, hg, hg0, hfg⟩ := hfa.meromorphicOn.extract_zeros_poles h₂f (vfp f c R)
 set D := divB f c R with hD
 set S := (vfp f c R).toFinset with hS
 have hDnn : ∀ u, 0 ≤ D u := fun u => (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfa) u
 have hP : ∀ z, (∏ᶠ u, (· - u) ^ D u) z = ∏ u ∈ S, (z - u) ^ (D u).toNat := by
  intro z
  rw [Function.FactorizedRational.finprod_eq_fun (vfp f c R)]
  simp only
  rw [finprod_eq_prod_of_mulSupport_subset (s := S)]
  ·refine Finset.prod_congr rfl fun u _ => ?_
   rw [← zpow_natCast, Int.toNat_of_nonneg (hDnn u)]
  ·intro u hu
   rw [Function.mem_mulSupport] at hu
   simp only [hS, Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
   intro h0; apply hu; rw [h0, zpow_zero]
 have heq : ∀ z ∈ closedBall c R, f z = (∏ u ∈ S, (z - u) ^ (D u).toNat) * g z := by
  intro z hz
  have hPa : AnalyticAt ℂ (fun z => (∏ u ∈ S, (z - u) ^ (D u).toNat) * g z) z := by
   refine AnalyticAt.mul ?_ (hg z hz)
   exact Finset.analyticAt_fun_prod _ fun u _ => ((analyticAt_id.sub analyticAt_const).pow _)
  have hfg' : f =ᶠ[codiscreteWithin (closedBall c R)]
    (fun z => (∏ u ∈ S, (z - u) ^ (D u).toNat) * g z) := by
   refine hfg.trans (Filter.Eventually.of_forall fun w => ?_)
   simp only [Pi.smul_apply', smul_eq_mul]
   rw [hP w]
  have h := (hf.analyticAt z).meromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
   hPa.meromorphicAt hz (vis hR) hfg'
  exact tendsto_nhds_unique ((hf.continuous.continuousAt).tendsto.mono_left nhdsWithin_le_nhds)
   (hPa.continuousAt.tendsto.mono_left nhdsWithin_le_nhds |>.congr' h.symm)
 set Sout := S.filter fun u => ¬ ‖u - c‖ < R / 2
 refine ⟨fun z => (∏ u ∈ Sout, (z - u) ^ (D u).toNat) * g z, ?_, ?_, ?_⟩
 ·intro z hz
  refine AnalyticAt.mul ?_ (hg z hz)
  exact Finset.analyticAt_fun_prod _ fun u _ => ((analyticAt_id.sub analyticAt_const).pow _)
 ·intro z hz
  refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun u hu => pow_ne_zero _ ?_)
   (hg0 ⟨z, ball_subset_closedBall (ball_subset_ball (by linarith) hz)⟩)
  intro h
  rw [sub_eq_zero] at h
  rw [Finset.mem_filter] at hu
  rw [mem_ball, dist_eq_norm, h] at hz
  exact hu.2 hz
 ·intro z hz
  rw [heq z hz, vbM, ← mul_assoc, Finset.prod_filter_mul_prod_filter_not]
noncomputable def Pin (f : ℂ → ℂ) (c : ℂ) (R : ℝ) (z : ℂ) : ℂ :=
 ∏ u ∈ vbM f c R (R / 2), (z - u) ^ (divB f c R u).toNat
lemma vfo {f : ℂ → ℂ} {c u : ℂ} {R r : ℝ} (hu : u ∈ vbM f c R r) :
  ‖u - c‖ < r ∧ divB f c R u ≠ 0 := by
 rw [vbM, Finset.mem_filter, Set.Finite.mem_toFinset, Function.mem_support] at hu
 exact ⟨hu.2, hu.1⟩
lemma vnu {z : ℂ} (hz : ∀ u ∈ vbM f c R (R / 2), z ≠ u) :
  logDeriv (Pin f c R) z = ∑ u ∈ vbM f c R (R / 2), ((divB f c R u).toNat : ℂ) / (z - u) := by
 have e : Pin f c R = fun w => ∏ u ∈ vbM f c R (R / 2), (w - u) ^ (divB f c R u).toNat := rfl
 rw [e, logDeriv_prod (f := fun (u : ℂ) (w : ℂ) => (w - u) ^ (divB f c R u).toNat) (x := z)
  (fun u hu => pow_ne_zero _ (sub_ne_zero.2 (hz u hu)))
  (fun u _ => (differentiableAt_id.sub_const u).pow _)]
 refine Finset.sum_congr rfl fun u hu => ?_
 have hd : DifferentiableAt ℂ (fun w : ℂ => w - u) z := differentiableAt_id.sub_const u
 rw [logDeriv_fun_pow hd, logDeriv_apply, deriv_sub_const, deriv_id'']
 ring
end vaa.vaz
end
section
open Complex Set MeasureTheory intervalIntegral Metric
open scoped Real Interval
namespace vaa.vaz
noncomputable def vaC (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
 (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
  I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I • (∫ y : ℝ in z.im..w.im, f (z.re + y * I))
lemma vel {a b : ℝ} {κ : ℂ} (h : ∀ x ∈ [[a, b]], (x : ℂ) + κ ∈ slitPlane) :
  ∫ x : ℝ in a..b, ((x : ℂ) + κ)⁻¹ = Complex.log (b + κ) - Complex.log (a + κ) := by
 have hd : ∀ x ∈ [[a, b]], HasDerivAt (fun x : ℝ => Complex.log ((x : ℂ) + κ)) ((x : ℂ) + κ)⁻¹ x := by
  intro x hx
  have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) + κ) 1 x := (hasDerivAt_id x).ofReal_comp.add_const κ
  have := h1.clog_real (h x hx)
  simpa using this
 have hc : ContinuousOn (fun x : ℝ => ((x : ℂ) + κ)⁻¹) [[a, b]] := by
  refine ContinuousOn.inv₀ (by fun_prop) fun x hx => ?_
  exact slitPlane_ne_zero (h x hx)
 exact integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable)
lemma viy {c d σ : ℝ} {κ : ℂ}
  (h : ∀ y ∈ [[c, d]], (σ : ℂ) + y * I + κ ∈ slitPlane) :
  ∫ y : ℝ in c..d, ((σ : ℂ) + y * I + κ)⁻¹ =
   -I * (Complex.log (σ + d * I + κ) - Complex.log (σ + c * I + κ)) := by
 have hd : ∀ y ∈ [[c, d]], HasDerivAt (fun y : ℝ => -I * Complex.log ((σ : ℂ) + y * I + κ))
   ((σ : ℂ) + y * I + κ)⁻¹ y := by
  intro y hy
  have h1 : HasDerivAt (fun y : ℝ => (σ : ℂ) + y * I + κ) I y := by
   have := ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (σ : ℂ) |>.add_const κ
   simpa using this
  have := (h1.clog_real (h y hy)).const_mul (-I)
  refine this.congr_deriv ?_
  have hne := slitPlane_ne_zero (h y hy)
  field_simp
  rw [I_sq]; ring
 have hc : ContinuousOn (fun y : ℝ => ((σ : ℂ) + y * I + κ)⁻¹) [[c, d]] := by
  refine ContinuousOn.inv₀ (by fun_prop) fun y hy => ?_
  exact slitPlane_ne_zero (h y hy)
 rw [integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
 ring
lemma vgB {c d σ : ℝ} {κ : ℂ}
  (h : ∀ y ∈ [[c, d]], -((σ : ℂ) + y * I + κ) ∈ slitPlane) :
  ∫ y : ℝ in c..d, ((σ : ℂ) + y * I + κ)⁻¹ =
   -I * (Complex.log (-((σ : ℂ) + d * I + κ)) - Complex.log (-((σ : ℂ) + c * I + κ))) := by
 have hd : ∀ y ∈ [[c, d]], HasDerivAt (fun y : ℝ => -I * Complex.log (-((σ : ℂ) + y * I + κ)))
   ((σ : ℂ) + y * I + κ)⁻¹ y := by
  intro y hy
  have h1 : HasDerivAt (fun y : ℝ => -((σ : ℂ) + y * I + κ)) (-I) y :=
   ((((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (σ : ℂ)).add_const κ).neg.congr_deriv
    (by simp)
  have := (h1.clog_real (h y hy)).const_mul (-I)
  refine this.congr_deriv ?_
  have hne : (σ : ℂ) + y * I + κ ≠ 0 := by
   intro h0; have := slitPlane_ne_zero (h y hy); rw [h0, neg_zero] at this; exact this rfl
  field_simp
  rw [I_sq]; ring
 have hc : ContinuousOn (fun y : ℝ => ((σ : ℂ) + y * I + κ)⁻¹) [[c, d]] := by
  refine ContinuousOn.inv₀ (by fun_prop) fun y hy => ?_
  intro h0; have := slitPlane_ne_zero (h y hy); rw [h0, neg_zero] at this; exact this rfl
 rw [integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
 ring
lemma vgG {p : ℂ} (hp : 0 < p.im) :
  Complex.log p - Complex.log (-p) = π * I := by
 rw [Complex.log, Complex.log, norm_neg, arg_neg_eq_arg_sub_pi_of_im_pos hp]
 push_cast; ring
lemma vgu {p : ℂ} (hp : p.im < 0) :
  Complex.log p - Complex.log (-p) = -(π * I) := by
 rw [Complex.log, Complex.log, norm_neg, arg_neg_eq_arg_add_pi_of_im_neg hp]
 push_cast; ring
lemma vlr {z w ρ : ℂ} (h1 : z.re < ρ.re) (h2 : ρ.re < w.re) (h3 : z.im < ρ.im)
  (h4 : ρ.im < w.im) : vaC (fun s => (s - ρ)⁻¹) z w = 2 * π * I := by
 unfold vaC
 have hB : ∫ x : ℝ in z.re..w.re, ((x : ℂ) + z.im * I - ρ)⁻¹ =
   Complex.log (w.re + (z.im * I - ρ)) - Complex.log (z.re + (z.im * I - ρ)) := by
  have := vel (a := z.re) (b := w.re) (κ := z.im * I - ρ) (fun x _ => by
   refine Or.inr ?_
   simp; linarith)
  simpa [add_sub_assoc] using this
 have hT : ∫ x : ℝ in z.re..w.re, ((x : ℂ) + w.im * I - ρ)⁻¹ =
   Complex.log (w.re + (w.im * I - ρ)) - Complex.log (z.re + (w.im * I - ρ)) := by
  have := vel (a := z.re) (b := w.re) (κ := w.im * I - ρ) (fun x _ => by
   refine Or.inr ?_
   simp; linarith)
  simpa [add_sub_assoc] using this
 have hR : ∫ y : ℝ in z.im..w.im, ((w.re : ℂ) + y * I - ρ)⁻¹ =
   -I * (Complex.log (w.re + w.im * I + -ρ) - Complex.log (w.re + z.im * I + -ρ)) := by
  have := viy (c := z.im) (d := w.im) (σ := w.re) (κ := -ρ) (fun y _ => by
   refine Or.inl ?_
   simp; linarith)
  simpa [sub_eq_add_neg] using this
 have hL : ∫ y : ℝ in z.im..w.im, ((z.re : ℂ) + y * I - ρ)⁻¹ =
   -I * (Complex.log (-((z.re : ℂ) + w.im * I + -ρ)) - Complex.log (-((z.re : ℂ) + z.im * I + -ρ))) := by
  have := vgB (c := z.im) (d := w.im) (σ := z.re) (κ := -ρ) (fun y _ => by
   refine Or.inl ?_
   simp; linarith)
  simpa [sub_eq_add_neg] using this
 simp only [smul_eq_mul]
 rw [hB, hT, hR, hL]
 have eTL : Complex.log ((z.re : ℂ) + (w.im * I - ρ)) - Complex.log (-((z.re : ℂ) + w.im * I + -ρ)) =
   π * I := by
  have hp : 0 < ((z.re : ℂ) + (w.im * I - ρ)).im := by simp; linarith
  rw [← vgG hp]; congr 2; ring
 have eBL : Complex.log ((z.re : ℂ) + (z.im * I - ρ)) - Complex.log (-((z.re : ℂ) + z.im * I + -ρ)) =
   -(π * I) := by
  have hp : ((z.re : ℂ) + (z.im * I - ρ)).im < 0 := by simp; linarith
  rw [← vgu hp]; congr 2; ring
 have e1 : Complex.log ((w.re : ℂ) + w.im * I + -ρ) = Complex.log ((w.re : ℂ) + (w.im * I - ρ)) := by
  congr 1; ring
 have e2 : Complex.log ((w.re : ℂ) + z.im * I + -ρ) = Complex.log ((w.re : ℂ) + (z.im * I - ρ)) := by
  congr 1; ring
 rw [e1, e2]
 have hII : I * -I = 1 := by rw [mul_neg, I_mul_I, neg_neg]
 linear_combination eTL - eBL + (Complex.log ((w.re : ℂ) + (w.im * I - ρ)) -
  Complex.log ((w.re : ℂ) + (z.im * I - ρ))) * hII -
  (Complex.log (-((z.re : ℂ) + w.im * I + -ρ)) - Complex.log (-((z.re : ℂ) + z.im * I + -ρ))) * hII
lemma veK {z w ρ : ℂ} (h1 : z.re < ρ.re) (h2 : ρ.re < w.re) (h3 : z.im < ρ.im)
  (h4 : ρ.im < w.im) :
  (∀ x : ℝ, (x : ℂ) + z.im * I ≠ ρ) ∧ (∀ x : ℝ, (x : ℂ) + w.im * I ≠ ρ) ∧
   (∀ y : ℝ, (w.re : ℂ) + y * I ≠ ρ) ∧ (∀ y : ℝ, (z.re : ℂ) + y * I ≠ ρ) := by
 refine ⟨fun x h => ?_, fun x h => ?_, fun y h => ?_, fun y h => ?_⟩
 ·have := congrArg Complex.im h; simp at this; linarith
 ·have := congrArg Complex.im h; simp at this; linarith
 ·have := congrArg Complex.re h; simp at this; linarith
 ·have := congrArg Complex.re h; simp at this; linarith
lemma vgr (c : ℂ) (f : ℂ → ℂ) (z w : ℂ) :
  vaC (fun s => c * f s) z w = c * vaC f z w := by
 unfold vaC
 simp only [intervalIntegral.integral_const_mul, smul_eq_mul]
 ring
lemma vcX {f g : ℂ → ℂ} {z w : ℂ}
  (hf1 : IntervalIntegrable (fun x : ℝ => f (x + z.im * I)) volume z.re w.re)
  (hf2 : IntervalIntegrable (fun x : ℝ => f (x + w.im * I)) volume z.re w.re)
  (hf3 : IntervalIntegrable (fun y : ℝ => f (w.re + y * I)) volume z.im w.im)
  (hf4 : IntervalIntegrable (fun y : ℝ => f (z.re + y * I)) volume z.im w.im)
  (hg1 : IntervalIntegrable (fun x : ℝ => g (x + z.im * I)) volume z.re w.re)
  (hg2 : IntervalIntegrable (fun x : ℝ => g (x + w.im * I)) volume z.re w.re)
  (hg3 : IntervalIntegrable (fun y : ℝ => g (w.re + y * I)) volume z.im w.im)
  (hg4 : IntervalIntegrable (fun y : ℝ => g (z.re + y * I)) volume z.im w.im) :
  vaC (fun s => f s + g s) z w = vaC f z w + vaC g z w := by
 unfold vaC
 rw [integral_add hf1 hg1, integral_add hf2 hg2, integral_add hf3 hg3, integral_add hf4 hg4]
 simp only [smul_eq_mul]
 ring
lemma vmE {f g : ℂ → ℂ} {z w : ℂ}
  (h1 : ∀ x : ℝ, f (x + z.im * I) = g (x + z.im * I)) (h2 : ∀ x : ℝ, f (x + w.im * I) = g (x + w.im * I))
  (h3 : ∀ y : ℝ, f (w.re + y * I) = g (w.re + y * I)) (h4 : ∀ y : ℝ, f (z.re + y * I) = g (z.re + y * I)) :
  vaC f z w = vaC g z w := by
 unfold vaC
 simp only [h1, h2, h3, h4]
lemma vcr {f : ℂ → ℂ} {z w : ℂ}
  (hf : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
  IntervalIntegrable (fun x : ℝ => f (x + z.im * I)) volume z.re w.re ∧
  IntervalIntegrable (fun x : ℝ => f (x + w.im * I)) volume z.re w.re ∧
  IntervalIntegrable (fun y : ℝ => f (w.re + y * I)) volume z.im w.im ∧
  IntervalIntegrable (fun y : ℝ => f (z.re + y * I)) volume z.im w.im := by
 refine ⟨?_, ?_, ?_, ?_⟩ <;> refine ContinuousOn.intervalIntegrable ?_ <;>
  refine hf.comp (by fun_prop) fun t ht => ?_ <;>
  simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
   sub_self, add_zero, add_im, mul_im, zero_add]
 ·exact ⟨ht, left_mem_uIcc⟩
 ·exact ⟨ht, right_mem_uIcc⟩
 ·exact ⟨right_mem_uIcc, ht⟩
 ·exact ⟨left_mem_uIcc, ht⟩
lemma vgE {z w ρ : ℂ} (h1 : z.re < ρ.re) (h2 : ρ.re < w.re)
  (h3 : z.im < ρ.im) (h4 : ρ.im < w.im) :
  IntervalIntegrable (fun x : ℝ => ((x + z.im * I : ℂ) - ρ)⁻¹) volume z.re w.re ∧
  IntervalIntegrable (fun x : ℝ => ((x + w.im * I : ℂ) - ρ)⁻¹) volume z.re w.re ∧
  IntervalIntegrable (fun y : ℝ => ((w.re + y * I : ℂ) - ρ)⁻¹) volume z.im w.im ∧
  IntervalIntegrable (fun y : ℝ => ((z.re + y * I : ℂ) - ρ)⁻¹) volume z.im w.im := by
 obtain ⟨b1, b2, b3, b4⟩ := veK h1 h2 h3 h4
 refine ⟨?_, ?_, ?_, ?_⟩ <;> refine ContinuousOn.intervalIntegrable ?_ <;>
  refine ContinuousOn.inv₀ (by fun_prop) fun t _ => sub_ne_zero.2 ?_
 exacts [b1 t, b2 t, b3 t, b4 t]
lemma vjt {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) {z w ρ : ℂ}
  (hsub : [[z.re, w.re]] ×ℂ [[z.im, w.im]] ⊆ U) (hg : DifferentiableOn ℂ g U)
  (h1 : z.re < ρ.re) (h2 : ρ.re < w.re) (h3 : z.im < ρ.im) (h4 : ρ.im < w.im) :
  vaC (fun s => g s * (s - ρ)⁻¹) z w = 2 * π * I * g ρ := by
 set R := [[z.re, w.re]] ×ℂ [[z.im, w.im]] with hR
 have hρU : ρ ∈ U := hsub (mem_reProdIm.2 ⟨Set.mem_uIcc.2 (Or.inl ⟨h1.le, h2.le⟩),
  Set.mem_uIcc.2 (Or.inl ⟨h3.le, h4.le⟩)⟩)
 have hgρ : DifferentiableAt ℂ g ρ := hg.differentiableAt (hU.mem_nhds hρU)
 have hdc : ContinuousOn (dslope g ρ) R := by
  intro s hs
  by_cases hsρ : s = ρ
  ·subst hsρ; exact (continuousAt_dslope_same.2 hgρ).continuousWithinAt
  ·have hgs : DifferentiableAt ℂ g s := hg.differentiableAt (hU.mem_nhds (hsub hs))
   exact ((differentiableAt_dslope_of_ne hsρ).2 hgs).continuousAt.continuousWithinAt
 have hdd : ∀ s ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im) \ {ρ},
   DifferentiableAt ℂ (dslope g ρ) s := by
  intro s hs
  have hsR : s ∈ R := ⟨Ioo_subset_Icc_self hs.1.1, Ioo_subset_Icc_self hs.1.2⟩
  have hgs : DifferentiableAt ℂ g s := hg.differentiableAt (hU.mem_nhds (hsub hsR))
  exact (differentiableAt_dslope_of_ne hs.2).2 hgs
 have h0 : vaC (dslope g ρ) z w = 0 :=
  Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable (dslope g ρ)
   z w {ρ} (countable_singleton ρ) hdc hdd
 obtain ⟨b1, b2, b3, b4⟩ := veK h1 h2 h3 h4
 have hpt : ∀ s, s ≠ ρ → g s * (s - ρ)⁻¹ = dslope g ρ s + g ρ * (s - ρ)⁻¹ := by
  intro s hs
  rw [dslope_of_ne _ hs, slope_def_field]
  have : s - ρ ≠ 0 := sub_ne_zero.2 hs
  field_simp
  ring
 rw [vmE (g := fun s => dslope g ρ s + g ρ * (s - ρ)⁻¹)
  (fun x => hpt _ (b1 x)) (fun x => hpt _ (b2 x)) (fun y => hpt _ (b3 y)) (fun y => hpt _ (b4 y))]
 obtain ⟨d1, d2, d3, d4⟩ := vcr hdc
 obtain ⟨i1, i2, i3, i4⟩ := vgE h1 h2 h3 h4
 rw [vcX d1 d2 d3 d4 (i1.const_mul _) (i2.const_mul _) (i3.const_mul _)
  (i4.const_mul _), h0, zero_add, vgr, vlr h1 h2 h3 h4]
 ring
lemma vmu {f g : ℂ → ℂ} {z w : ℂ}
  (h1 : ∀ x ∈ [[z.re, w.re]], f (x + z.im * I) = g (x + z.im * I))
  (h2 : ∀ x ∈ [[z.re, w.re]], f (x + w.im * I) = g (x + w.im * I))
  (h3 : ∀ y ∈ [[z.im, w.im]], f (w.re + y * I) = g (w.re + y * I))
  (h4 : ∀ y ∈ [[z.im, w.im]], f (z.re + y * I) = g (z.re + y * I)) :
  vaC f z w = vaC g z w := by
 unfold vaC
 rw [integral_congr (fun x hx => h1 x hx), integral_congr (fun x hx => h2 x hx),
  integral_congr (fun y hy => h3 y hy), integral_congr (fun y hy => h4 y hy)]
def vaK (F : ℂ → ℂ) (z w : ℂ) : Prop :=
 IntervalIntegrable (fun x : ℝ => F (x + z.im * I)) volume z.re w.re ∧
 IntervalIntegrable (fun x : ℝ => F (x + w.im * I)) volume z.re w.re ∧
 IntervalIntegrable (fun y : ℝ => F (w.re + y * I)) volume z.im w.im ∧
 IntervalIntegrable (fun y : ℝ => F (z.re + y * I)) volume z.im w.im
lemma vaK.const_mul {F : ℂ → ℂ} {z w : ℂ} (hF : vaK F z w) (c : ℂ) :
  vaK (fun s => c * F s) z w :=
 ⟨hF.1.const_mul c, hF.2.1.const_mul c, hF.2.2.1.const_mul c, hF.2.2.2.const_mul c⟩
lemma veD {F : ℂ → ℂ} {z w : ℂ}
  (hF : ContinuousOn F ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) : vaK F z w :=
 vcr hF
lemma vjH {F G : ℂ → ℂ} {z w : ℂ} (hF : vaK F z w) (hG : vaK G z w) :
  vaC (fun s => F s + G s) z w = vaC F z w + vaC G z w :=
 vcX hF.1 hF.2.1 hF.2.2.1 hF.2.2.2 hG.1 hG.2.1 hG.2.2.1 hG.2.2.2
lemma vkb {ι : Type*} (S : Finset ι) (F : ι → ℂ → ℂ) {z w : ℂ}
  (hF : ∀ i ∈ S, vaK (F i) z w) :
  vaC (fun s => ∑ i ∈ S, F i s) z w = ∑ i ∈ S, vaC (F i) z w := by
 classical
 induction S using Finset.induction_on with
 | empty => simp [vaC]
 | insert a S ha ih =>
  have hS : vaK (fun s => ∑ i ∈ S, F i s) z w := by
   have key : ∀ (φ : ℝ → ℂ) (a b : ℝ),
     (∀ i ∈ S, IntervalIntegrable (fun t => F i (φ t)) volume a b) →
     IntervalIntegrable (fun t => ∑ i ∈ S, F i (φ t)) volume a b := by
    intro φ a b h
    have := IntervalIntegrable.sum S h
    simpa [Finset.sum_fn] using this
   exact ⟨key _ _ _ fun i hi => (hF i (Finset.mem_insert_of_mem hi)).1,
    key _ _ _ fun i hi => (hF i (Finset.mem_insert_of_mem hi)).2.1,
    key _ _ _ fun i hi => (hF i (Finset.mem_insert_of_mem hi)).2.2.1,
    key _ _ _ fun i hi => (hF i (Finset.mem_insert_of_mem hi)).2.2.2⟩
  simp only [Finset.sum_insert ha]
  rw [vjH (hF a (Finset.mem_insert_self a S)) hS,
   ih fun i hi => hF i (Finset.mem_insert_of_mem hi)]
lemma vlY {z w u : ℂ} (hu : u ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]]) (hzw1 : z.re < w.re)
  (hzw2 : z.im < w.im) :
  (z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im) ∨ u.im = z.im ∨ u.im = w.im ∨
   u.re = w.re ∨ u.re = z.re := by
 rw [mem_reProdIm, Set.uIcc_of_le hzw1.le, Set.uIcc_of_le hzw2.le] at hu
 obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := hu
 rcases a1.lt_or_eq with a1 | a1
 ·rcases a2.lt_or_eq with a2 | a2
  ·rcases b1.lt_or_eq with b1 | b1
   ·rcases b2.lt_or_eq with b2 | b2
    ·exact Or.inl ⟨a1, a2, b1, b2⟩
    ·exact Or.inr (Or.inr (Or.inl b2))
   ·exact Or.inr (Or.inl b1.symm)
  ·exact Or.inr (Or.inr (Or.inr (Or.inl a2)))
 ·exact Or.inr (Or.inr (Or.inr (Or.inr a1.symm)))
def vfj (F : ℂ → ℂ) (z w : ℂ) : Prop :=
 (∀ x ∈ [[z.re, w.re]], F (x + z.im * I) ≠ 0) ∧ (∀ x ∈ [[z.re, w.re]], F (x + w.im * I) ≠ 0) ∧
 (∀ y ∈ [[z.im, w.im]], F (w.re + y * I) ≠ 0) ∧ (∀ y ∈ [[z.im, w.im]], F (z.re + y * I) ≠ 0)
lemma vfK {h : ℂ → ℂ} {z w u : ℂ}
  (hh : ContinuousOn h ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
  (hu1 : ∀ x ∈ [[z.re, w.re]], (x : ℂ) + z.im * I ≠ u) (hu2 : ∀ x ∈ [[z.re, w.re]], (x : ℂ) + w.im * I ≠ u)
  (hu3 : ∀ y ∈ [[z.im, w.im]], (w.re : ℂ) + y * I ≠ u) (hu4 : ∀ y ∈ [[z.im, w.im]], (z.re : ℂ) + y * I ≠ u) :
  vaK (fun s => h s * (s - u)⁻¹) z w := by
 have hs := vcr hh
 refine ⟨?_, ?_, ?_, ?_⟩ <;> refine ContinuousOn.intervalIntegrable ?_
 ·refine ContinuousOn.mul ?_ (ContinuousOn.inv₀ (by fun_prop) fun x hx => sub_ne_zero.2 (hu1 x hx))
  exact hh.comp (by fun_prop) fun x hx => by
   simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_self, add_zero, add_im, mul_im, zero_add]; exact ⟨hx, left_mem_uIcc⟩
 ·refine ContinuousOn.mul ?_ (ContinuousOn.inv₀ (by fun_prop) fun x hx => sub_ne_zero.2 (hu2 x hx))
  exact hh.comp (by fun_prop) fun x hx => by
   simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_self, add_zero, add_im, mul_im, zero_add]; exact ⟨hx, right_mem_uIcc⟩
 ·refine ContinuousOn.mul ?_ (ContinuousOn.inv₀ (by fun_prop) fun y hy => sub_ne_zero.2 (hu3 y hy))
  exact hh.comp (by fun_prop) fun y hy => by
   simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_self, add_zero, add_im, mul_im, zero_add]; exact ⟨right_mem_uIcc, hy⟩
 ·refine ContinuousOn.mul ?_ (ContinuousOn.inv₀ (by fun_prop) fun y hy => sub_ne_zero.2 (hu4 y hy))
  exact hh.comp (by fun_prop) fun y hy => by
   simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_self, add_zero, add_im, mul_im, zero_add]; exact ⟨left_mem_uIcc, hy⟩
lemma viV {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ} {R : ℝ} (hR : 0 < R)
  (hfc : f c ≠ 0) {z w : ℂ} (hzw1 : z.re < w.re) (hzw2 : z.im < w.im)
  (hrect : [[z.re, w.re]] ×ℂ [[z.im, w.im]] ⊆ ball c (R / 2)) (hbd : vfj f z w)
  {h : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hsubU : [[z.re, w.re]] ×ℂ [[z.im, w.im]] ⊆ U)
  (hh : DifferentiableOn ℂ h U) :
  vaC (fun s => logDeriv f s * h s) z w = 2 * π * I *
   ∑ u ∈ (vbM f c R (R / 2)).filter
    (fun u => z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im),
    ((divB f c R u).toNat : ℂ) * h u := by
 classical
 obtain ⟨g, hg, hg0, hfg⟩ := vnJ hf hfc hR
 set Z := vbM f c R (R / 2) with hZ
 set Rect := [[z.re, w.re]] ×ℂ [[z.im, w.im]] with hRect
 have hRb : Rect ⊆ ball c R := hrect.trans (ball_subset_ball (by linarith))
 have hfu : ∀ u ∈ Z, f u = 0 := by
  intro u hu
  have hu' := (vfo hu).2
  have hucR : u ∈ closedBall c R := by
   rw [mem_closedBall, dist_eq_norm]; linarith [(vfo hu).1]
  rw [divB, MeromorphicOn.AnalyticOnNhd.divisor_apply
   (fun z _ => hf.analyticAt z : AnalyticOnNhd ℂ f (closedBall c R)) hucR] at hu'
  by_contra hne
  exact hu' (by rw [(hf.analyticAt u).analyticOrderAt_eq_zero.2 hne]; simp)
 have hdec : ∀ s ∈ Rect, f s ≠ 0 →
   logDeriv f s = ∑ u ∈ Z, ((divB f c R u).toNat : ℂ) / (s - u) + logDeriv g s := by
  intro s hs hfs
  have hsZ : ∀ u ∈ Z, s ≠ u := fun u hu h => hfs (h ▸ hfu u hu)
  have hsb : s ∈ ball c R := hRb hs
  have hsb2 : s ∈ ball c (R / 2) := hrect hs
  have hPs : Pin f c R s ≠ 0 :=
   Finset.prod_ne_zero_iff.2 fun u hu => pow_ne_zero _ (sub_ne_zero.2 (hsZ u hu))
  have hgs : g s ≠ 0 := hg0 s hsb2
  have hloc : f =ᶠ[nhds s] fun w => Pin f c R w * g w := by
   filter_upwards [isOpen_ball.mem_nhds hsb] with v hv
   exact hfg v (ball_subset_closedBall hv)
  have hPd : DifferentiableAt ℂ (Pin f c R) s := by
   have : Pin f c R = fun w => ∏ u ∈ Z, (w - u) ^ (divB f c R u).toNat := rfl
   rw [this]
   exact DifferentiableAt.fun_finsetProd fun u _ => (differentiableAt_id.sub_const u).pow _
  have hgd : DifferentiableAt ℂ g s := (hg s (ball_subset_closedBall hsb)).differentiableAt
  rw [(logDeriv_congr_nhds hloc).eq_of_nhds,
   logDeriv_mul (f := Pin f c R) (g := g) s hPs hgs hPd hgd, vnu hsZ]
 have hside1 : ∀ x ∈ [[z.re, w.re]], (x : ℂ) + z.im * I ∈ Rect := fun x hx =>
  mem_reProdIm.2 ⟨by simpa using hx, by simp [left_mem_uIcc]⟩
 have hside2 : ∀ x ∈ [[z.re, w.re]], (x : ℂ) + w.im * I ∈ Rect := fun x hx =>
  mem_reProdIm.2 ⟨by simpa using hx, by simp [right_mem_uIcc]⟩
 have hside3 : ∀ y ∈ [[z.im, w.im]], (w.re : ℂ) + y * I ∈ Rect := fun y hy =>
  mem_reProdIm.2 ⟨by simp [right_mem_uIcc], by simpa using hy⟩
 have hside4 : ∀ y ∈ [[z.im, w.im]], (z.re : ℂ) + y * I ∈ Rect := fun y hy =>
  mem_reProdIm.2 ⟨by simp [left_mem_uIcc], by simpa using hy⟩
 set F : ℂ → ℂ := fun s => (∑ u ∈ Z, ((divB f c R u).toNat : ℂ) * (h s * (s - u)⁻¹)) +
  logDeriv g s * h s with hF
 have hpt : ∀ s ∈ Rect, f s ≠ 0 → logDeriv f s * h s = F s := by
  intro s hs hfs
  rw [hdec s hs hfs, add_mul, Finset.sum_mul, hF]
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [div_eq_mul_inv]; ring
 obtain ⟨b1, b2, b3, b4⟩ := hbd
 rw [vmu (g := F) (fun x hx => hpt _ (hside1 x hx) (b1 x hx))
  (fun x hx => hpt _ (hside2 x hx) (b2 x hx)) (fun y hy => hpt _ (hside3 y hy) (b3 y hy))
  (fun y hy => hpt _ (hside4 y hy) (b4 y hy))]
 have hhc : ContinuousOn h Rect := hh.continuousOn.mono hsubU
 have hnot : ∀ u ∈ Z, (∀ x ∈ [[z.re, w.re]], (x : ℂ) + z.im * I ≠ u) ∧
   (∀ x ∈ [[z.re, w.re]], (x : ℂ) + w.im * I ≠ u) ∧
   (∀ y ∈ [[z.im, w.im]], (w.re : ℂ) + y * I ≠ u) ∧ (∀ y ∈ [[z.im, w.im]], (z.re : ℂ) + y * I ≠ u) := by
  intro u hu
  refine ⟨fun x hx h' => b1 x hx (h' ▸ hfu u hu), fun x hx h' => b2 x hx (h' ▸ hfu u hu),
   fun y hy h' => b3 y hy (h' ▸ hfu u hu), fun y hy h' => b4 y hy (h' ▸ hfu u hu)⟩
 have hint_u : ∀ u ∈ Z, vaK (fun s => h s * (s - u)⁻¹) z w := fun u hu =>
  vfK hhc (hnot u hu).1 (hnot u hu).2.1 (hnot u hu).2.2.1 (hnot u hu).2.2.2
 have hgdiff : DifferentiableOn ℂ (fun s => logDeriv g s * h s) Rect := by
  intro s hs
  have hga : AnalyticAt ℂ g s := hg s (ball_subset_closedBall (hRb hs))
  have hgs : g s ≠ 0 := hg0 s (hrect hs)
  have hhs : DifferentiableAt ℂ h s := hh.differentiableAt (hU.mem_nhds (hsubU hs))
  have : DifferentiableAt ℂ (logDeriv g) s := by
   have e : logDeriv g = fun s => deriv g s / g s := funext fun s => logDeriv_apply g s
   rw [e]; exact hga.deriv.differentiableAt.div hga.differentiableAt hgs
  exact (this.mul hhs).differentiableWithinAt
 have hint_g : vaK (fun s => logDeriv g s * h s) z w :=
  veD hgdiff.continuousOn
 have hint_sum : vaK (fun s => ∑ u ∈ Z, ((divB f c R u).toNat : ℂ) * (h s * (s - u)⁻¹)) z w := by
  have key : ∀ (φ : ℝ → ℂ) (a b : ℝ),
    (∀ u ∈ Z, IntervalIntegrable (fun t => h (φ t) * (φ t - u)⁻¹) volume a b) →
    IntervalIntegrable (fun t => ∑ u ∈ Z, ((divB f c R u).toNat : ℂ) * (h (φ t) * (φ t - u)⁻¹))
     volume a b := by
   intro φ a b hφ
   have := IntervalIntegrable.sum Z fun u hu => (hφ u hu).const_mul ((divB f c R u).toNat : ℂ)
   simpa [Finset.sum_fn] using this
  exact ⟨key _ _ _ fun u hu => (hint_u u hu).1, key _ _ _ fun u hu => (hint_u u hu).2.1,
   key _ _ _ fun u hu => (hint_u u hu).2.2.1, key _ _ _ fun u hu => (hint_u u hu).2.2.2⟩
 have hg0' : vaC (fun s => logDeriv g s * h s) z w = 0 := by
  exact Complex.integral_boundary_rect_eq_zero_of_differentiableOn (fun s => logDeriv g s * h s) z w hgdiff
 rw [hF, vjH hint_sum hint_g, hg0', add_zero,
  vkb Z _ fun u hu => (hint_u u hu).const_mul _]
 simp only [vgr]
 have hterm : ∀ u ∈ Z, ((divB f c R u).toNat : ℂ) * vaC (fun s => h s * (s - u)⁻¹) z w =
   if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im then
    2 * π * I * (((divB f c R u).toNat : ℂ) * h u) else 0 := by
  intro u hu
  split_ifs with hin
  ·rw [vjt hU hsubU hh hin.1 hin.2.1 hin.2.2.1 hin.2.2.2]; ring
  ·by_cases huR : u ∈ Rect
   ·exfalso
    rcases vlY huR hzw1 hzw2 with h' | h' | h' | h' | h'
    ·exact hin h'
    ·exact (hnot u hu).1 u.re (by
      rw [mem_reProdIm] at huR; exact huR.1) (by apply Complex.ext <;> simp [h'])
    ·exact (hnot u hu).2.1 u.re (by
      rw [mem_reProdIm] at huR; exact huR.1) (by apply Complex.ext <;> simp [h'])
    ·exact (hnot u hu).2.2.1 u.im (by
      rw [mem_reProdIm] at huR; exact huR.2) (by apply Complex.ext <;> simp [h'])
    ·exact (hnot u hu).2.2.2 u.im (by
      rw [mem_reProdIm] at huR; exact huR.2) (by apply Complex.ext <;> simp [h'])
   ·have hd : DifferentiableOn ℂ (fun s => h s * (s - u)⁻¹) Rect := by
     intro s hs
     have hsu : s - u ≠ 0 := sub_ne_zero.2 (fun h' => huR (h' ▸ hs))
     exact ((hh.differentiableAt (hU.mem_nhds (hsubU hs))).mul
      ((differentiableAt_id.sub_const u).inv hsu)).differentiableWithinAt
    have h0 : vaC (fun s => h s * (s - u)⁻¹) z w = 0 := by
     exact Complex.integral_boundary_rect_eq_zero_of_differentiableOn (fun s => h s * (s - u)⁻¹) z w hd
    rw [h0, mul_zero]
 rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, ← Finset.mul_sum]
end vaa.vaz
end
section
open Complex MeasureTheory Set Filter
open Finset (range Icc)
namespace vaa.vaz
variable {q : ℕ} [NeZero q]
lemma vfP {t : ℝ} (ht : 0 < t) (s : ℂ) :
  ‖(t : ℂ) ^ (-(s + 1))‖ = t ^ (-(s.re + 1)) := by
 rw [Complex.norm_cpow_eq_rpow_re_of_pos ht]; simp
end vaa.vaz
end
section
open Complex MeasureTheory Set Filter Asymptotics
open scoped Real Topology ArithmeticFunction.vonMangoldt Interval
namespace vaa.vaz
noncomputable def RT (T : ℝ) : ℝ := 2 * (T + 3)
end vaa.vaz
end
section
open Complex MeasureTheory Set Filter Asymptotics Metric
open scoped Real Topology ArithmeticFunction.vonMangoldt Interval
namespace vaa.vaz
noncomputable def vhQ (f : ℂ → ℂ) (T : ℝ) (u : ℂ) : ℕ :=
 (divB f 2 (RT T) u).toNat
end vaa.vaz
end
section
open Complex MeasureTheory Set Filter Asymptotics
open scoped Real Topology
namespace vaa.vaz
noncomputable def vce : ℂ → ℂ := Function.update (fun s ↦ (s - 1) * riemannZeta s) 1 1
lemma vbm {s : ℂ} (hs : s ≠ 1) : vce s = (s - 1) * riemannZeta s :=
 Function.update_of_ne hs _ _
lemma vcu {s : ℂ} (hs : s ≠ 1) : DifferentiableAt ℂ vce s := by
 have : vce =ᶠ[𝓝 s] fun s => (s - 1) * riemannZeta s := by
  filter_upwards [isOpen_ne.mem_nhds hs] with t ht using vbm ht
 exact ((differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hs)).congr_of_eventuallyEq
  this
lemma veE : Differentiable ℂ vce := by
 intro s
 rcases ne_or_eq s 1 with hs | rfl
 ·exact vcu hs
 ·refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
  ·filter_upwards [self_mem_nhdsWithin] with t ht
   exact vcu ht
  ·simpa only [vce, continuousAt_update_same] using riemannZeta_residue_one
noncomputable def saw (t : ℝ) : ℂ := ((⌊t⌋₊ : ℝ) : ℂ) - t
lemma vih {t : ℝ} (ht : 0 ≤ t) : ‖saw t‖ ≤ 1 := by
 rw [saw, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
  abs_of_nonneg (by linarith [Nat.floor_le ht])]
 linarith [Nat.lt_floor_add_one t]
lemma vmf : Measurable saw := by
 unfold saw
 exact (Complex.measurable_ofReal.comp (measurable_from_nat.comp Nat.measurable_floor)).sub
  Complex.measurable_ofReal
noncomputable def vcd (s : ℂ) : ℂ := ∫ t in Ioi (1:ℝ), saw t * (t : ℂ) ^ (-(s + 1))
lemma vdf (s : ℂ) :
  AEStronglyMeasurable (fun t : ℝ => saw t * (t : ℂ) ^ (-(s + 1))) (volume.restrict (Ioi 1)) := by
 refine vmf.aestronglyMeasurable.mul ?_
 refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
 exact (Complex.continuousAt_ofReal_cpow_const t _
  (Or.inr (by have : (1:ℝ) < t := ht; positivity))).continuousWithinAt
lemma vaW {s : ℂ} (hs : 0 < s.re) :
  IntegrableOn (fun t : ℝ => saw t * (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
 refine ((integrableOn_Ioi_rpow_of_lt (a := -(s.re + 1)) (by linarith) one_pos).const_mul
  (1 : ℝ)).mono' (vdf s) ?_
 refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
 have ht' : (0:ℝ) < t := lt_trans one_pos ht
 rw [norm_mul, vfP ht']
 exact mul_le_mul_of_nonneg_right (vih ht'.le) (Real.rpow_nonneg ht'.le _)
lemma vkZ {s₀ : ℂ} (hs : 0 < s₀.re) :
    HasDerivAt vcd (∫ t in Ioi (1:ℝ), saw t * (t : ℂ) ^ (-(s₀ + 1)) * (-(Real.log t : ℂ))) s₀ := by
  set σ₀ := s₀.re
  have hball : ∀ s ∈ Metric.ball s₀ (σ₀ / 2), σ₀ / 2 < s.re := fun s hs' => by
    rw [Metric.mem_ball, dist_eq_norm] at hs'
    have := Complex.abs_re_le_norm (s - s₀)
    rw [Complex.sub_re] at this
    linarith [neg_abs_le (s.re - s₀.re)]
  have hbd : IntegrableOn (fun t : ℝ => (1 : ℝ) * (4 / σ₀) * t ^ (-(σ₀ / 4) - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 1))
    (F := fun s t => saw t * (t : ℂ) ^ (-(s + 1)))
    (F' := fun s t => saw t * (t : ℂ) ^ (-(s + 1)) * (-(Real.log t : ℂ))) (x₀ := s₀)
    (bound := fun t => (1 : ℝ) * (4 / σ₀) * t ^ (-(σ₀ / 4) - 1))
    (Metric.ball_mem_nhds s₀ (half_pos hs))
    (Filter.Eventually.of_forall fun s => vdf s)
    (vaW hs)
    ((vdf s₀).mul
      (Complex.measurable_ofReal.comp Real.measurable_log).neg.aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht s hs' => by
      have ht' : (1:ℝ) < t := ht
      have ht0 : (0:ℝ) < t := by linarith
      have hσ := hball s hs'
      rw [norm_mul, norm_mul, vfP ht0, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg ht'.le)]
      have hlog : Real.log t ≤ t ^ (σ₀ / 4) / (σ₀ / 4) := Real.log_le_rpow_div ht0.le (by positivity)
      have hpow : t ^ (-(s.re + 1)) ≤ t ^ (-(σ₀ / 2) - 1) :=
        Real.rpow_le_rpow_of_exponent_le ht'.le (by linarith)
      have e : t ^ (-(σ₀ / 2) - 1) * (t ^ (σ₀ / 4) / (σ₀ / 4)) = (4 / σ₀) * t ^ (-(σ₀ / 4) - 1) := by
        rw [mul_div_assoc', ← Real.rpow_add ht0, show -(σ₀ / 2) - 1 + σ₀ / 4 = -(σ₀ / 4) - 1 by ring]
        field_simp
      calc ‖saw t‖ * t ^ (-(s.re + 1)) * Real.log t
          ≤ (1 : ℝ) * t ^ (-(σ₀ / 2) - 1) * (t ^ (σ₀ / 4) / (σ₀ / 4)) :=
            mul_le_mul (mul_le_mul (vih ht0.le) hpow (Real.rpow_nonneg ht0.le _)
              (by positivity)) hlog (Real.log_nonneg ht'.le) (by positivity)
          _ = (1 : ℝ) * (4 / σ₀) * t ^ (-(σ₀ / 4) - 1) := by rw [mul_assoc, e]; ring))
    hbd
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht s _ => by
      have ht0 : (0:ℝ) < t := lt_trans one_pos ht
      have ht0' : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
      have h1 : HasDerivAt (fun s : ℂ => -(s + 1)) (-1) s := ((hasDerivAt_id s).add_const 1).neg
      refine ((h1.const_cpow (Or.inl ht0')).const_mul (saw t)).congr_deriv ?_
      rw [← Complex.ofReal_log ht0.le]; ring))
  exact h.2
lemma viT {s : ℂ} (hs : 1 < s.re) :
  riemannZeta s = s / (s - 1) + s * vcd s := by
 have hs0 : 0 < s.re := by linarith
 rw [← LSeries_one_eq_riemannZeta hs]
 have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (1 : ℕ → ℂ) k) =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
  refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun n => ?_)
  simp
 have hsum : LSeriesSummable 1 s := by
  rw [show (1 : ℕ → ℂ) = fun _ => 1 from rfl]
  exact (LSeriesSummable_one_iff).2 hs
 rw [LSeries_eq_mul_integral _ zero_le_one hs hsum hO]
 have e1 : ∀ t : ℝ, (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℕ → ℂ) k) = ((⌊t⌋₊ : ℝ) : ℂ) := by
  intro t; simp
 simp_rw [e1]
 have hI1 : IntegrableOn (fun t : ℝ => saw t * (t : ℂ) ^ (-(s + 1))) (Ioi 1) :=
  vaW hs0
 have hI2 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Ioi 1) :=
  integrableOn_Ioi_cpow_of_lt (by simp; linarith) one_pos
 have e2 : ∀ t ∈ Ioi (1:ℝ), ((⌊t⌋₊ : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) =
   saw t * (t : ℂ) ^ (-(s + 1)) + (t : ℂ) ^ (-s) := by
  intro t ht
  have ht' : (0:ℝ) < t := lt_trans one_pos ht
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht'.ne'
  rw [saw, sub_mul, show (t : ℂ) ^ (-s) = (t : ℂ) * (t : ℂ) ^ (-(s + 1)) by
   rw [show -s = 1 + -(s + 1) by ring, Complex.cpow_add _ _ ht0, Complex.cpow_one]]
  ring
 rw [setIntegral_congr_fun measurableSet_Ioi e2, integral_add hI1 hI2,
  integral_Ioi_cpow_of_lt (by simp; linarith) one_pos, Complex.ofReal_one, Complex.one_cpow]
 have hs1 : s - 1 ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp at this; linarith
 have hs1' : -s + 1 ≠ 0 := by
  intro h; apply hs1; linear_combination -h
 rw [vcd]
 field_simp
 ring
lemma vkM {s : ℂ} (hs : 0 < s.re) : vce s = s + s * (s - 1) * vcd s := by
 set U := {s : ℂ | 0 < s.re}
 have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
 have hUc : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
 have hf : AnalyticOnNhd ℂ vce U := fun z _ => veE.analyticAt z
 have hg : AnalyticOnNhd ℂ (fun s => s + s * (s - 1) * vcd s) U := by
  refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUo
  exact (differentiableAt_id.add ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul
   (vkZ hz).differentiableAt)).differentiableWithinAt
 have h2 : (2 : ℂ) ∈ U := by show (0:ℝ) < (2:ℂ).re; norm_num
 have hev : vce =ᶠ[nhds (2 : ℂ)] fun s => s + s * (s - 1) * vcd s := by
  have hopen : {s : ℂ | 1 < s.re} ∈ nhds (2 : ℂ) :=
   (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by show (1:ℝ) < (2:ℂ).re; norm_num)
  filter_upwards [hopen] with s hs1
  have hne : s ≠ 1 := by intro h; rw [h] at hs1; simp at hs1
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hne
  rw [vbm hne, viT hs1]
  field_simp
 exact hf.eqOn_of_preconnected_of_eventuallyEq hg hUc h2 hev hs
lemma vmG {s : ℂ} (hs : 0 < s.re) : ‖vce s‖ ≤ ‖s‖ + ‖s‖ * ‖s - 1‖ / s.re := by
 rw [vkM hs]
 have hb : ‖vcd s‖ ≤ 1 / s.re := by
  have hi := (integrableOn_Ioi_rpow_of_lt (a := -(s.re + 1)) (by linarith) one_pos).const_mul (1 : ℝ)
  refine (norm_integral_le_of_norm_le hi ((ae_restrict_iff' measurableSet_Ioi).2
   (Filter.Eventually.of_forall fun t ht => ?_))).trans (le_of_eq ?_)
  ·have ht' : (0:ℝ) < t := lt_trans one_pos ht
   rw [norm_mul, vfP ht']
   exact mul_le_mul_of_nonneg_right (vih ht'.le) (Real.rpow_nonneg ht'.le _)
  ·rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow,
    show -(s.re + 1) + 1 = -s.re by ring]
   have : s.re ≠ 0 := hs.ne'
   field_simp
 refine (norm_add_le _ _).trans ?_
 rw [norm_mul, norm_mul]
 have := mul_le_mul_of_nonneg_left hb (by positivity : (0:ℝ) ≤ ‖s‖ * ‖s - 1‖)
 rw [mul_one_div] at this
 linarith
end vaa.vaz
end
section
open Complex MeasureTheory Set Filter Finset
open scoped Topology Interval
namespace vaa.vab.vcO
open vaa.vaz
lemma vjb {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
  riemannZeta s = 1 + 1 / (s - 1) + s * vcd s := by
 have hh := vkM hs
 rw [vbm hs1] at hh
 have hn : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
 apply (mul_left_cancel₀ hn)
 calc
  (s - 1) * riemannZeta s = s + s * (s - 1) * vcd s := hh
  _ = (s - 1) * (1 + 1 / (s - 1) + s * vcd s) := by field_simp [hn]; ring
noncomputable def vbG (s : ℂ) (x : ℝ) : ℂ :=
 (-s * (x : ℂ) ^ (-s - 1)) * (B1 x : ℝ)
lemma vgl (s : ℂ) (x : ℝ) :
  vbG s x = s * (saw x * (x : ℂ) ^ (-(s + 1))) +
   (s / 2) * (x : ℂ) ^ (-s - 1) := by
 unfold vbG B1 saw
 push_cast
 rw [show -(s + 1) = -s - 1 by ring]
 ring
lemma vfE {s : ℂ} (hs : 0 < s.re) :
  IntegrableOn (vbG s) (Ioi (1 : ℝ)) := by
 change IntegrableOn (fun x => vbG s x) (Ioi (1 : ℝ))
 simp_rw [vgl]
 exact ((vaW hs).const_mul s).add
  ((integrableOn_Ioi_cpow_of_lt (a := -s - 1) (by simp; linarith)
   (by norm_num : (0 : ℝ) < 1)).const_mul (s / 2))
lemma vhE {s : ℂ} (hs : 0 < s.re) :
  (∫ x in Ioi (1 : ℝ), vbG s x) = s * vcd s + 1 / 2 := by
 have hs0 : s ≠ 0 := by intro he; simp [he] at hs
 have hfi := vaW hs
 have hgi := integrableOn_Ioi_cpow_of_lt (a := -s - 1) (by simp; linarith)
  (by norm_num : (0 : ℝ) < 1)
 simp_rw [vgl]
 rw [integral_add (hfi.const_mul s) (hgi.const_mul (s / 2)),
  integral_const_mul, integral_const_mul,
  integral_Ioi_cpow_of_lt (by simp; linarith) (by norm_num : (0 : ℝ) < 1)]
 simp only [Complex.ofReal_one, Complex.one_cpow, vcd]
 field_simp [hs0]
 ring
lemma vid {s : ℂ} (hs : 0 < s.re) {M : ℕ} (hM : 1 ≤ M) :
  (∑ k ∈ range M, (k : ℂ) ^ (-s)) - (∫ x in (1 : ℝ)..M, (x : ℂ) ^ (-s)) =
   (1 - (M : ℂ) ^ (-s)) / 2 + ∫ x in (1 : ℝ)..M, vbG s x := by
 let f : ℝ → ℂ := fun x => (x : ℂ) ^ (-s)
 have hs0 : -s ≠ 0 := by
  intro he
  have := congrArg Complex.re he
  simp at this
  linarith
 have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
 have hderiv (x : ℝ) (hx : 1 ≤ x) :
   HasDerivAt f (-s * (x : ℂ) ^ (-s - 1)) x :=
  hasDerivAt_ofReal_cpow_const (by linarith) hs0
 have hc : ContinuousOn (deriv f) (uIcc (1 : ℝ) M) := by
  rw [uIcc_of_le hM']
  apply ContinuousOn.congr (f := fun x : ℝ => -s * (x : ℂ) ^ (-s - 1))
  ·intro x hx
   exact (continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const _ _
    (Or.inr (by linarith [hx.1])))).continuousWithinAt
  ·intro x hx
   exact (hderiv x hx.1).deriv
 have hh := vdE (f := f)
  (a := 1) (b := (M : ℝ)) (by norm_num) hM'
  (fun x hx => (hderiv x hx.1).differentiableAt) hc
 simp only [RCLike.ofReal_eq_complex_ofReal] at hh
 have hsets : Finset.Ioc 1 M = Finset.Ico 2 (M + 1) := by ext k; simp; omega
 have hint : (∫ x in (1 : ℝ)..M, deriv f x * (B1 x : ℝ)) =
   ∫ x in (1 : ℝ)..M, vbG s x := by
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hM'] at hx
  dsimp only
  rw [(hderiv x hx.1).deriv]
  rfl
 rw [hint] at hh
 simp only [Nat.floor_one, Nat.floor_natCast] at hh
 rw [hsets, sum_Ico_eq_sub _ (by omega)] at hh
 simp only [sum_range_succ, sum_range_zero, add_zero] at hh
 norm_num [f, B1, hs0] at hh
 linear_combination hh
lemma vea {s : ℂ} (hs : 0 < s.re) :
  Tendsto (fun M : ℕ => (∑ k ∈ range M, (k : ℂ) ^ (-s)) -
   (∫ x in (1 : ℝ)..M, (x : ℂ) ^ (-s))) atTop (𝓝 (1 + s * vcd s)) := by
 have hf0 : Tendsto (fun M : ℕ => (M : ℂ) ^ (-s)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  change Tendsto (fun M : ℕ => ‖(M : ℂ) ^ (-s)‖) atTop (𝓝 0)
  simp only [Complex.norm_natCast_cpow_of_re_ne_zero _
   (show (-s).re ≠ 0 by simp only [Complex.neg_re]; linarith), Complex.neg_re]
  exact (tendsto_rpow_neg_atTop hs).comp tendsto_natCast_atTop_atTop
 have hI := intervalIntegral_tendsto_integral_Ioi (1 : ℝ)
  (vfE hs) tendsto_natCast_atTop_atTop
 have hlim := ((hf0.const_sub 1).div_const 2).add hI
 rw [vhE hs] at hlim
 have he : (1 - (0 : ℂ)) / 2 + (s * vcd s + 1 / 2) = 1 + s * vcd s := by ring
 rw [he] at hlim
 apply hlim.congr'
 filter_upwards [eventually_ge_atTop 1] with M hM
 exact (vid hs hM).symm
lemma vhI {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
  {N : ℕ} (hN : 1 ≤ N) :
  Tendsto (fun M : ℕ => (∑ k ∈ Ico N M, (k : ℂ) ^ (-s)) -
   (∫ x in (N : ℝ)..M, (x : ℂ) ^ (-s))) atTop
   (𝓝 (riemannZeta s - (∑ k ∈ range N, (k : ℂ) ^ (-s)) -
    (N : ℂ) ^ (1 - s) / (s - 1))) := by
 have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
 have hint {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
   IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  intro x hx
  exact (Complex.continuousAt_ofReal_cpow_const _ _
   (Or.inr (by linarith [hx.1]))).continuousWithinAt
 have hIN : (∫ x in (1 : ℝ)..N, (x : ℂ) ^ (-s)) =
   ((N : ℂ) ^ (1 - s) - 1) / (1 - s) := by
  rw [integral_cpow (Or.inr ⟨by intro he; exact hs1 (neg_inj.mp he),
   by rw [uIcc_of_le hN']; simp⟩), Complex.ofReal_one, Complex.one_cpow]
  push_cast
  congr 2 <;> ring
 have hlim := ((vea hs).sub_const
  (∑ k ∈ range N, (k : ℂ) ^ (-s))).add_const
   (∫ x in (1 : ℝ)..N, (x : ℂ) ^ (-s))
 have htarget : (1 + s * vcd s - (∑ k ∈ range N, (k : ℂ) ^ (-s))) +
   (∫ x in (1 : ℝ)..N, (x : ℂ) ^ (-s)) =
   riemannZeta s - (∑ k ∈ range N, (k : ℂ) ^ (-s)) -
    (N : ℂ) ^ (1 - s) / (s - 1) := by
  rw [hIN, vjb hs hs1]
  field_simp [sub_ne_zero.mpr hs1, sub_ne_zero.mpr hs1.symm]
  ring
 rw [htarget] at hlim
 apply hlim.congr'
 filter_upwards [eventually_ge_atTop N] with M hM
 have hM' : (N : ℝ) ≤ M := by exact_mod_cast hM
 have hcat := intervalIntegral.integral_add_adjacent_intervals
  (hint le_rfl hN') (hint hN' hM')
 rw [sum_Ico_eq_sub _ hM, ← hcat]
 ring
end vaa.vab.vcO
end
section
open Real Finset Filter Topology
namespace vaa.vcP.vjc
lemma vlE {a : ℝ} (ha : 0 < a) :
  HasSum (fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1)) * (1 / (2 * a + 1)) ^ (2 * k + 1))
   (Real.log (1 + a⁻¹)) := Real.hasSum_log_one_add_inv ha
lemma vhU {a : ℝ} (ha : 0 < a) (k : ℕ) :
  0 ≤ (2 : ℝ) * (1 / (2 * k + 1)) * (1 / (2 * a + 1)) ^ (2 * k + 1) := by positivity
lemma vjR {a : ℝ} (ha : 0 < a) : 2 / (2 * a + 1) ≤ Real.log (1 + a⁻¹) := by
 have := le_hasSum (vlE ha) 0 (fun k _ => vhU ha k)
 simp only [Nat.cast_zero, mul_zero, zero_add, div_one, mul_one, pow_one] at this
 rw [div_eq_mul_one_div]; exact this
lemma vbn {a : ℝ} (ha : 0 < a) (K : ℕ) :
    ∑ k ∈ range K, (2 : ℝ) * (1 / (2 * k + 1)) * (1 / (2 * a + 1)) ^ (2 * k + 1) ≤
        Real.log (1 + a⁻¹) ∧
      Real.log (1 + a⁻¹) ≤ ∑ k ∈ range K, (2 : ℝ) * (1 / (2 * k + 1)) * (1 / (2 * a + 1)) ^ (2 * k + 1) +
        2 / (2 * K + 1) * (1 / (2 * a + 1)) ^ (2 * K + 1) / (1 - (1 / (2 * a + 1)) ^ 2) := by
  have h := vlE ha
  refine ⟨sum_le_hasSum _ (fun k _ => vhU ha k) h, ?_⟩
  set y : ℝ := 1 / (2 * a + 1) with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y < 1 := by rw [hy, div_lt_one (by linarith)]; linarith
  have hy2 : y ^ 2 < 1 := by nlinarith
  set f : ℕ → ℝ := fun k => (2 : ℝ) * (1 / (2 * k + 1)) * y ^ (2 * k + 1) with hf
  have htail := (hasSum_nat_add_iff' K).2 h
  have hg : HasSum (fun k : ℕ => 2 / (2 * K + 1) * y ^ (2 * K + 1) * (y ^ 2) ^ k)
      (2 / (2 * K + 1) * y ^ (2 * K + 1) / (1 - y ^ 2)) := by
    have := (hasSum_geometric_of_lt_one (by positivity) hy2).mul_left (2 / (2 * K + 1) * y ^ (2 * K + 1))
    rwa [← div_eq_mul_inv] at this
  have hle : ∀ k, f (k + K) ≤ 2 / (2 * K + 1) * y ^ (2 * K + 1) * (y ^ 2) ^ k := by
    intro k
    simp only [hf]
    have e : y ^ (2 * (↑(k + K) : ℕ) + 1) = y ^ (2 * K + 1) * (y ^ 2) ^ k := by
      rw [← pow_mul, ← pow_add]; congr 1; ring
    rw [show (2 : ℝ) * ((k + K : ℕ) : ℝ) + 1 = 2 * (k + K : ℕ) + 1 from rfl]
    have e2 : y ^ (2 * (k + K) + 1) = y ^ (2 * K + 1) * (y ^ 2) ^ k := by
      rw [← pow_mul, ← pow_add]; congr 1; ring
    rw [e2]
    have hk : (2 : ℝ) * (1 / (2 * ((k + K : ℕ) : ℝ) + 1)) ≤ 2 / (2 * K + 1) := by
      rw [mul_one_div]
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hp : 0 ≤ y ^ (2 * K + 1) * (y ^ 2) ^ k := by positivity
    calc (2 : ℝ) * (1 / (2 * ((k + K : ℕ) : ℝ) + 1)) * (y ^ (2 * K + 1) * (y ^ 2) ^ k)
        ≤ 2 / (2 * K + 1) * (y ^ (2 * K + 1) * (y ^ 2) ^ k) := mul_le_mul_of_nonneg_right hk hp
      _ = _ := by ring
  have hT := hasSum_le hle htail hg
  linarith
lemma vkg {a : ℝ} (ha : 0 < a) :
  Real.log (1 + a⁻¹) ≤ 2 / (2 * a + 1) + 1 / (6 * a * (a + 1) * (2 * a + 1)) := by
 have h := (vbn ha 1).2
 simp only [range_one, sum_singleton, Nat.cast_zero, mul_zero, zero_add, div_one, mul_one,
  pow_one, Nat.cast_one] at h
 refine h.trans (le_of_eq ?_)
 have h1 : (2 * a + 1) ≠ 0 := by positivity
 have h3 : (1 : ℝ) - (1 / (2 * a + 1)) ^ 2 = 4 * a * (a + 1) / (2 * a + 1) ^ 2 := by
  field_simp; ring
 have h4 : (2 : ℝ) / (2 + 1) * (1 / (2 * a + 1)) ^ (2 + 1) / (4 * a * (a + 1) / (2 * a + 1) ^ 2) =
   1 / (6 * a * (a + 1) * (2 * a + 1)) := by
  have : a + 1 ≠ 0 := by positivity
  rw [show (2 : ℕ) + 1 = 3 from rfl, div_pow, one_pow]
  field_simp; ring
 rw [h3, h4, mul_one_div]
lemma vmx {k : ℕ} (hk : 1 ≤ k) :
  1 / (2 * ((k : ℝ) + 1)) - 1 / (2 * ((k : ℝ) + 2)) ≤
    Real.log ((k : ℝ) + 1) - Real.log k - 1 / ((k : ℝ) + 1) ∧
   Real.log ((k : ℝ) + 1) - Real.log k - 1 / ((k : ℝ) + 1) ≤
    1 / (2 * (k : ℝ)) - 1 / (2 * ((k : ℝ) + 1)) := by
 have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
 have hlog : Real.log ((k : ℝ) + 1) - Real.log k = Real.log (1 + (k : ℝ)⁻¹) := by
  rw [← Real.log_div (by positivity) hk0.ne']; congr 1; field_simp
 rw [hlog]
 have hl := vjR hk0
 have hu := vkg hk0
 constructor
 ·have : 1 / (2 * ((k : ℝ) + 1)) - 1 / (2 * ((k : ℝ) + 2)) ≤ 2 / (2 * k + 1) - 1 / ((k : ℝ) + 1) := by
   rw [div_sub_div _ _ (by positivity) (by positivity), div_sub_div _ _ (by positivity) (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
   nlinarith [hk0]
  linarith
 ·have : 2 / (2 * (k : ℝ) + 1) + 1 / (6 * k * (k + 1) * (2 * k + 1)) - 1 / ((k : ℝ) + 1) ≤
    1 / (2 * (k : ℝ)) - 1 / (2 * ((k : ℝ) + 1)) := by
   have e1 : 2 / (2 * (k : ℝ) + 1) + 1 / (6 * k * (k + 1) * (2 * k + 1)) - 1 / ((k : ℝ) + 1) =
     (6 * k + 1) / (6 * k * (k + 1) * (2 * k + 1)) := by field_simp; ring
   have e2 : 1 / (2 * (k : ℝ)) - 1 / (2 * ((k : ℝ) + 1)) = 3 * (2 * k + 1) / (6 * k * (k + 1) * (2 * k + 1)) := by
    field_simp; ring
   rw [e1, e2]
   exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  linarith
lemma vmy (n : ℕ) : ∀ M, n ≤ M →
  ((harmonic n : ℚ) : ℝ) - Real.log n - (((harmonic M : ℚ) : ℝ) - Real.log M) =
   ∑ k ∈ Ico n M, (Real.log ((k : ℝ) + 1) - Real.log k - 1 / ((k : ℝ) + 1)) := by
 intro M hM
 induction M, hM using Nat.le_induction with
 | base => simp
 | succ M hnM ih =>
  rw [sum_Ico_succ_top hnM, ← ih, harmonic_succ]
  push_cast
  ring
lemma vil {n : ℕ} (hn : 1 ≤ n) :
  1 / (2 * ((n : ℝ) + 1)) ≤ ((harmonic n : ℚ) : ℝ) - Real.log n - eulerMascheroniConstant ∧
   ((harmonic n : ℚ) : ℝ) - Real.log n - eulerMascheroniConstant ≤ 1 / (2 * (n : ℝ)) := by
 set u : ℕ → ℝ := fun M => ((harmonic n : ℚ) : ℝ) - Real.log n - eulerMascheroniSeq' M with hu
 have hlim : Tendsto u atTop (𝓝 (((harmonic n : ℚ) : ℝ) - Real.log n - eulerMascheroniConstant)) :=
  tendsto_const_nhds.sub tendsto_eulerMascheroniSeq'
 have hseq : ∀ M, 1 ≤ M → eulerMascheroniSeq' M = ((harmonic M : ℚ) : ℝ) - Real.log M := by
  intro M hM; rw [eulerMascheroniSeq', if_neg (by omega)]
 have hlow : ∀ M, n ≤ M → 1 / (2 * ((n : ℝ) + 1)) - 1 / (2 * ((M : ℝ) + 1)) ≤ u M := by
  intro M hM
  simp only [hu]
  rw [hseq M (le_trans hn hM), vmy n M hM]
  have hsum : ∑ k ∈ Ico n M, (1 / (2 * ((k : ℝ) + 1)) - 1 / (2 * ((k : ℝ) + 2))) =
    1 / (2 * ((n : ℝ) + 1)) - 1 / (2 * ((M : ℝ) + 1)) := by
   induction M, hM using Nat.le_induction with
   | base => simp
   | succ M hnM ih => rw [sum_Ico_succ_top hnM, ih]; push_cast; ring
  rw [← hsum]
  exact sum_le_sum fun k hk => (vmx (le_trans hn (mem_Ico.1 hk).1)).1
 have hup : ∀ M, n ≤ M → u M ≤ 1 / (2 * (n : ℝ)) - 1 / (2 * (M : ℝ)) := by
  intro M hM
  simp only [hu]
  rw [hseq M (le_trans hn hM), vmy n M hM]
  have hsum : ∑ k ∈ Ico n M, (1 / (2 * (k : ℝ)) - 1 / (2 * ((k : ℝ) + 1))) =
    1 / (2 * (n : ℝ)) - 1 / (2 * (M : ℝ)) := by
   induction M, hM using Nat.le_induction with
   | base => simp
   | succ M hnM ih => rw [sum_Ico_succ_top hnM, ih]; push_cast; ring
  rw [← hsum]
  exact sum_le_sum fun k hk => (vmx (le_trans hn (mem_Ico.1 hk).1)).2
 have hz1 : Tendsto (fun M : ℕ => 1 / (2 * ((M : ℝ) + 1))) atTop (𝓝 0) := by
  have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (1 / 2 : ℝ)
  simp only [mul_zero] at this
  refine this.congr fun M => ?_
  field_simp
 have hz2 : Tendsto (fun M : ℕ => 1 / (2 * (M : ℝ))) atTop (𝓝 0) := by
  have := (tendsto_one_div_atTop_nhds_zero_nat).const_mul (1 / 2 : ℝ)
  simp only [mul_zero] at this
  refine this.congr fun M => ?_
  field_simp
 constructor
 ·have h1 : Tendsto (fun M => u M + 1 / (2 * ((M : ℝ) + 1))) atTop
    (𝓝 (((harmonic n : ℚ) : ℝ) - Real.log n - eulerMascheroniConstant + 0)) := hlim.add hz1
  rw [add_zero] at h1
  exact ge_of_tendsto h1 (eventually_atTop.2 ⟨n, fun M hM => by linarith [hlow M hM]⟩)
 ·have h1 : Tendsto (fun M => u M + 1 / (2 * (M : ℝ))) atTop
    (𝓝 (((harmonic n : ℚ) : ℝ) - Real.log n - eulerMascheroniConstant + 0)) := hlim.add hz2
  rw [add_zero] at h1
  exact le_of_tendsto h1 (eventually_atTop.2 ⟨n, fun M hM => by linarith [hup M hM]⟩)
end vaa.vcP.vjc
end
section
open Finset Real
namespace vaa.vcP.vkl
open vaa.vcP.vjc (vbn)
def vdq : ℕ → ℕ → ℕ
 | 0, _ => 0
 | k + 1, n => vdq k n + 2 * 10 ^ 30 / ((2 * k + 1) * (2 * n + 1) ^ (2 * k + 1))
def vjS (n : ℕ) : ℕ := vdq 12 n
def vir (n : ℕ) : ℕ := vdq 12 n + 12 + 3 * 10 ^ 30 / (25 * (2 * n + 1) ^ 25) + 1
lemma vlH (n : ℕ) : ∀ k, (vdq k n : ℝ) ≤
  10 ^ 30 * ∑ j ∈ range k, (2 : ℝ) * (1 / (2 * j + 1)) * (1 / (2 * (n : ℝ) + 1)) ^ (2 * j + 1)
 | 0 => by simp [vdq]
 | k + 1 => by
  rw [vdq, sum_range_succ, mul_add, Nat.cast_add]
  refine add_le_add (vlH n k) ?_
  have := Nat.cast_div_le (α := ℝ) (m := 2 * 10 ^ 30) (n := (2 * k + 1) * (2 * n + 1) ^ (2 * k + 1))
  refine this.trans (le_of_eq ?_)
  rw [one_div_pow]
  push_cast
  field_simp
  norm_num
lemma vlQ (n : ℕ) : ∀ k, 10 ^ 30 * ∑ j ∈ range k,
  (2 : ℝ) * (1 / (2 * j + 1)) * (1 / (2 * (n : ℝ) + 1)) ^ (2 * j + 1) ≤ (vdq k n : ℝ) + k
 | 0 => by simp [vdq]
 | k + 1 => by
  rw [vdq, sum_range_succ, mul_add, Nat.cast_add, Nat.cast_succ]
  have h1 := vlQ n k
  have hpos : 0 < (2 * k + 1) * (2 * n + 1) ^ (2 * k + 1) := by positivity
  have h2 := Nat.lt_div_mul_add (a := 2 * 10 ^ 30) hpos
  have h3 : ((2 * 10 ^ 30 : ℕ) : ℝ) < ((2 * 10 ^ 30 / ((2 * k + 1) * (2 * n + 1) ^ (2 * k + 1)) : ℕ) : ℝ) *
    (((2 * k + 1) * (2 * n + 1) ^ (2 * k + 1) : ℕ) : ℝ) + (((2 * k + 1) * (2 * n + 1) ^ (2 * k + 1) : ℕ) : ℝ) := by
   exact_mod_cast h2
  have hq : (0 : ℝ) < (((2 * k + 1) * (2 * n + 1) ^ (2 * k + 1) : ℕ) : ℝ) := by exact_mod_cast hpos
  have h4 : (10 : ℝ) ^ 30 * (2 * (1 / (2 * (k : ℝ) + 1)) * (1 / (2 * (n : ℝ) + 1)) ^ (2 * k + 1)) ≤
    ((2 * 10 ^ 30 / ((2 * k + 1) * (2 * n + 1) ^ (2 * k + 1)) : ℕ) : ℝ) + 1 := by
   have e : (10 : ℝ) ^ 30 * (2 * (1 / (2 * (k : ℝ) + 1)) * (1 / (2 * (n : ℝ) + 1)) ^ (2 * k + 1)) =
     ((2 * 10 ^ 30 : ℕ) : ℝ) / (((2 * k + 1) * (2 * n + 1) ^ (2 * k + 1) : ℕ) : ℝ) := by
    rw [one_div_pow]; push_cast; field_simp; norm_num
   rw [e, div_le_iff₀ hq]; linarith
  linarith
lemma vkL {n : ℕ} (hn : 1 ≤ n) :
  (vjS n : ℝ) ≤ 10 ^ 30 * Real.log (1 + (n : ℝ)⁻¹) ∧
   10 ^ 30 * Real.log (1 + (n : ℝ)⁻¹) ≤ (vir n : ℝ) := by
 have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
 obtain ⟨h1, h2⟩ := vbn hn0 12
 refine ⟨(vlH n 12).trans (by nlinarith), ?_⟩
 have h3 := vlQ n 12
 set y : ℝ := 1 / (2 * (n : ℝ) + 1) with hy
 have hy0 : 0 < y := by positivity
 have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
 have hy3 : y ≤ 1 / 3 := by
  rw [hy, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
 have htail : 2 / (2 * ((12 : ℕ) : ℝ) + 1) * y ^ (2 * 12 + 1) / (1 - y ^ 2) ≤ 3 / 25 * y ^ 25 := by
  have h1y : 8 / 9 ≤ 1 - y ^ 2 := by nlinarith
  rw [div_le_iff₀ (by linarith)]
  push_cast
  have : 0 ≤ y ^ 25 := by positivity
  nlinarith
 have hfl : (10 : ℝ) ^ 30 * (3 / 25 * y ^ 25) ≤ ((3 * 10 ^ 30 / (25 * (2 * n + 1) ^ 25) : ℕ) : ℝ) + 1 := by
  have hpos : 0 < 25 * (2 * n + 1) ^ 25 := by positivity
  have h2 := Nat.lt_div_mul_add (a := 3 * 10 ^ 30) hpos
  have hq : (0 : ℝ) < ((25 * (2 * n + 1) ^ 25 : ℕ) : ℝ) := by exact_mod_cast hpos
  have h3' : ((3 * 10 ^ 30 : ℕ) : ℝ) < ((3 * 10 ^ 30 / (25 * (2 * n + 1) ^ 25) : ℕ) : ℝ) *
    ((25 * (2 * n + 1) ^ 25 : ℕ) : ℝ) + ((25 * (2 * n + 1) ^ 25 : ℕ) : ℝ) := by exact_mod_cast h2
  have e : (10 : ℝ) ^ 30 * (3 / 25 * y ^ 25) = ((3 * 10 ^ 30 : ℕ) : ℝ) / ((25 * (2 * n + 1) ^ 25 : ℕ) : ℝ) := by
   rw [hy, one_div_pow]; push_cast; field_simp; norm_num
  rw [e, div_le_iff₀ hq]; linarith
 unfold vir
 push_cast
 push_cast at h3
 nlinarith
def isPr (p : ℕ) : Bool :=
 2 ≤ p && (List.range' 2 146).all (fun d => p < d * d || p % d != 0)
lemma voE {p : ℕ} (hp : p < 21609) : isPr p = true ↔ p.Prime := by
 unfold isPr
 simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range'_1,
  Bool.or_eq_true, bne_iff_ne, ne_eq]
 constructor
 ·intro h
  rw [Nat.prime_def_le_sqrt]
  refine ⟨h.1, fun m hm2 hms hdvd => ?_⟩
  have hmm : m * m ≤ p := Nat.le_sqrt.1 hms
  have hm : m ≤ 147 := by nlinarith
  rcases h.2 m ⟨hm2, by omega⟩ with h1 | h1
  ·omega
  ·exact h1 (Nat.mod_eq_zero_of_dvd hdvd)
 ·intro h
  refine ⟨h.two_le, fun d hd => ?_⟩
  by_cases hdd : p < d * d
  ·exact Or.inl hdd
  ·right
   intro hmod
   have hdvd : d ∣ p := Nat.dvd_of_mod_eq_zero hmod
   rcases h.eq_one_or_self_of_dvd d hdvd with h1 | h1
   ·omega
   ·subst h1; nlinarith
lemma vbZ (a b : ℕ) (hb : 0 < b) :
  ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / b ∧ (a : ℝ) / b ≤ ((a / b : ℕ) : ℝ) + 1 := by
 refine ⟨Nat.cast_div_le, ?_⟩
 have h2 := Nat.lt_div_mul_add (a := a) hb
 have hq : (0 : ℝ) < b := by exact_mod_cast hb
 have : (a : ℝ) < ((a / b : ℕ) : ℝ) * b + b := by exact_mod_cast h2
 rw [div_le_iff₀ hq]; linarith
end vaa.vcP.vkl
end
section
open Finset Real
namespace vaa.vcP.vjc
open vaa.vcP.vkl
structure WS where
 Llo : ℕ
 Lhi : ℕ
 Hlo : ℕ
 Hhi : ℕ
 Aplo : ℕ
 Aphi : ℕ
 Anlo : ℕ
 Anhi : ℕ
 Tlo : ℕ
 Thi : ℕ
deriving DecidableEq
def voI (n : ℕ) (s : WS) : WS :=
  let Llo := s.Llo + vjS n
  let Lhi := s.Lhi + vir n
  let w := 10 ^ 30 / ((n + 1) ^ 2)
  { Llo := Llo, Lhi := Lhi,
    Hlo := s.Hlo + 10 ^ 30 / (n + 1), Hhi := s.Hhi + 10 ^ 30 / (n + 1) + 1,
    Aplo := if n + 1 ≤ 2000 ∧ (n + 1) % 2 = 1 then s.Aplo + Llo * w else s.Aplo,
    Aphi := if n + 1 ≤ 2000 ∧ (n + 1) % 2 = 1 then s.Aphi + Lhi * (w + 1) else s.Aphi,
    Anlo := if n + 1 ≤ 2000 ∧ (n + 1) % 2 = 0 then s.Anlo + Llo * w else s.Anlo,
    Anhi := if n + 1 ≤ 2000 ∧ (n + 1) % 2 = 0 then s.Anhi + Lhi * (w + 1) else s.Anhi,
    Tlo := if isPr (n + 1) then s.Tlo + Llo * (10 ^ 30 / (n * (n + 1) * (n + 2))) else s.Tlo,
    Thi := if isPr (n + 1) then s.Thi + Lhi * (10 ^ 30 / (n * (n + 1) * (n + 2)) + 1) else s.Thi }
def vbj : ℕ → ℕ → WS → Option WS
 | _, 0, s => some s
 | n, len + 1, s =>
  if s.Llo + s.Lhi + s.Hlo + s.Hhi + s.Aplo + s.Aphi + s.Anlo + s.Anhi + s.Tlo + s.Thi < 10 ^ 200 then
   vbj (n + 1) len (voI n s) else none
noncomputable def AP (n : ℕ) : ℝ :=
 ∑ k ∈ Icc 1 n, if k ≤ 2000 ∧ k % 2 = 1 then Real.log k / (k : ℝ) ^ 2 else 0
noncomputable def AN (n : ℕ) : ℝ :=
 ∑ k ∈ Icc 1 n, if k ≤ 2000 ∧ k % 2 = 0 then Real.log k / (k : ℝ) ^ 2 else 0
noncomputable def TP (n : ℕ) : ℝ :=
 ∑ k ∈ Icc 1 n, if k.Prime then Real.log k / ((k : ℝ) ^ 3 - k) else 0
noncomputable def Hn (n : ℕ) : ℝ := ∑ k ∈ Icc 1 n, 1 / (k : ℝ)
def Inv (n : ℕ) (s : WS) : Prop :=
 (s.Llo : ℝ) ≤ 10 ^ 30 * Real.log n ∧ 10 ^ 30 * Real.log n ≤ s.Lhi ∧
 (s.Hlo : ℝ) ≤ 10 ^ 30 * Hn n ∧ 10 ^ 30 * Hn n ≤ s.Hhi ∧
 (s.Aplo : ℝ) ≤ 10 ^ 60 * AP n ∧ 10 ^ 60 * AP n ≤ s.Aphi ∧
 (s.Anlo : ℝ) ≤ 10 ^ 60 * AN n ∧ 10 ^ 60 * AN n ≤ s.Anhi ∧
 (s.Tlo : ℝ) ≤ 10 ^ 60 * TP n ∧ 10 ^ 60 * TP n ≤ s.Thi
set_option maxHeartbeats 1000000 in
lemma voz {n : ℕ} (hn : 1 ≤ n) (hn' : n + 1 < 21609) {s : WS} (h : Inv n s) :
  Inv (n + 1) (voI n s) := by
 obtain ⟨l1, l2, h1, h2, p1, p2, q1, q2, t1, t2⟩ := h
 have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
 obtain ⟨i1, i2⟩ := vkL hn
 have hlog : Real.log ((n + 1 : ℕ) : ℝ) = Real.log n + Real.log (1 + (n : ℝ)⁻¹) := by
  rw [← Real.log_mul hn0.ne' (by positivity)]; congr 1; push_cast; field_simp
 have hL1 : ((s.Llo + vjS n : ℕ) : ℝ) ≤ 10 ^ 30 * Real.log ((n + 1 : ℕ) : ℝ) := by
  rw [hlog]; push_cast; linarith
 have hL2 : 10 ^ 30 * Real.log ((n + 1 : ℕ) : ℝ) ≤ ((s.Lhi + vir n : ℕ) : ℝ) := by
  rw [hlog]; push_cast; linarith
 have hlog0 : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
 obtain ⟨f1, f2⟩ := vbZ (10 ^ 30) (n + 1) (by omega)
 obtain ⟨g1, g2⟩ := vbZ (10 ^ 30) ((n + 1) ^ 2) (by positivity)
 have hH : Hn (n + 1) = Hn n + 1 / ((n + 1 : ℕ) : ℝ) := by
  rw [Hn, Hn, sum_Icc_succ_top (by omega)]
 have hAP : AP (n + 1) = AP n + if n + 1 ≤ 2000 ∧ (n + 1) % 2 = 1 then
   Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 else 0 := by
  rw [AP, AP, sum_Icc_succ_top (by omega)]
 have hAN : AN (n + 1) = AN n + if n + 1 ≤ 2000 ∧ (n + 1) % 2 = 0 then
   Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 else 0 := by
  rw [AN, AN, sum_Icc_succ_top (by omega)]
 have hTP : TP (n + 1) = TP n + if (n + 1).Prime then
   Real.log ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 3 - ((n + 1 : ℕ) : ℝ)) else 0 := by
  rw [TP, TP, sum_Icc_succ_top (by omega)]
 have hpr : isPr (n + 1) = true ↔ (n + 1).Prime := voE hn'
 set Lo := s.Llo + vjS n
 set Hi := s.Lhi + vir n
 set w := 10 ^ 30 / ((n + 1) ^ 2)
 have hw : ((10 ^ 30 : ℕ) : ℝ) / (((n + 1) ^ 2 : ℕ) : ℝ) = 10 ^ 30 / ((n + 1 : ℕ) : ℝ) ^ 2 := by push_cast; ring
 rw [hw] at g1 g2
 have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg _
 have hLo0 : (0 : ℝ) ≤ Lo := Nat.cast_nonneg _
 have hT1 : ((Lo * w : ℕ) : ℝ) ≤ 10 ^ 60 * (Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) := by
  rw [Nat.cast_mul]
  have e : (10 : ℝ) ^ 60 * (Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) =
    (10 ^ 30 * Real.log ((n + 1 : ℕ) : ℝ)) * (10 ^ 30 / ((n + 1 : ℕ) : ℝ) ^ 2) := by ring
  rw [e]
  exact mul_le_mul hL1 g1 hw0 (by positivity)
 have hT2 : 10 ^ 60 * (Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) ≤ ((Hi * (w + 1) : ℕ) : ℝ) := by
  rw [Nat.cast_mul, show ((w + 1 : ℕ) : ℝ) = (w : ℝ) + 1 by push_cast; ring]
  have e : (10 : ℝ) ^ 60 * (Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) =
    (10 ^ 30 * Real.log ((n + 1 : ℕ) : ℝ)) * (10 ^ 30 / ((n + 1 : ℕ) : ℝ) ^ 2) := by ring
  rw [e]
  exact mul_le_mul hL2 g2 (by positivity) (by positivity)
 set w3 := 10 ^ 30 / (n * (n + 1) * (n + 2))
 obtain ⟨k1, k2⟩ := vbZ (10 ^ 30) (n * (n + 1) * (n + 2)) (by positivity)
 have hw3 : ((10 ^ 30 : ℕ) : ℝ) / ((n * (n + 1) * (n + 2) : ℕ) : ℝ) =
   10 ^ 30 / (((n + 1 : ℕ) : ℝ) ^ 3 - ((n + 1 : ℕ) : ℝ)) := by push_cast; ring_nf
 rw [hw3] at k1 k2
 have hw30 : (0 : ℝ) ≤ w3 := Nat.cast_nonneg _
 have hden : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ 3 - ((n + 1 : ℕ) : ℝ) := by
  push_cast
  have : (0 : ℝ) < (n : ℝ) * (n + 1) * (n + 2) := by positivity
  nlinarith
 have hU1 : ((Lo * w3 : ℕ) : ℝ) ≤
   10 ^ 60 * (Real.log ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 3 - ((n + 1 : ℕ) : ℝ))) := by
  rw [Nat.cast_mul]
  have e : (10 : ℝ) ^ 60 * (Real.log ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 3 - ((n + 1 : ℕ) : ℝ))) =
    (10 ^ 30 * Real.log ((n + 1 : ℕ) : ℝ)) * (10 ^ 30 / (((n + 1 : ℕ) : ℝ) ^ 3 - ((n + 1 : ℕ) : ℝ))) := by
   ring
  rw [e]
  exact mul_le_mul hL1 k1 hw30 (by positivity)
 have hU2 : 10 ^ 60 * (Real.log ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 3 - ((n + 1 : ℕ) : ℝ))) ≤
   ((Hi * (w3 + 1) : ℕ) : ℝ) := by
  rw [Nat.cast_mul, show ((w3 + 1 : ℕ) : ℝ) = (w3 : ℝ) + 1 by push_cast; ring]
  have e : (10 : ℝ) ^ 60 * (Real.log ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 3 - ((n + 1 : ℕ) : ℝ))) =
    (10 ^ 30 * Real.log ((n + 1 : ℕ) : ℝ)) * (10 ^ 30 / (((n + 1 : ℕ) : ℝ) ^ 3 - ((n + 1 : ℕ) : ℝ))) := by
   ring
  rw [e]
  exact mul_le_mul hL2 k2 (by positivity) (by positivity)
 refine ⟨hL1, hL2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
 ·show ((s.Hlo + 10 ^ 30 / (n + 1) : ℕ) : ℝ) ≤ _
  have e : (10 : ℝ) ^ 30 * (Hn n + 1 / ((n + 1 : ℕ) : ℝ)) =
    10 ^ 30 * Hn n + ((10 ^ 30 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hH, e, Nat.cast_add s.Hlo]; linarith
 ·show _ ≤ ((s.Hhi + 10 ^ 30 / (n + 1) + 1 : ℕ) : ℝ)
  have e : (10 : ℝ) ^ 30 * (Hn n + 1 / ((n + 1 : ℕ) : ℝ)) =
    10 ^ 30 * Hn n + ((10 ^ 30 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hH, e, Nat.cast_add (s.Hhi + 10 ^ 30 / (n + 1)) 1, Nat.cast_add s.Hhi, Nat.cast_one]; linarith
 ·show ((if n + 1 ≤ 2000 ∧ (n + 1) % 2 = 1 then s.Aplo + Lo * w else s.Aplo : ℕ) : ℝ) ≤ _
  rw [hAP]; split_ifs
  ·push_cast at hT1 ⊢; linarith
  ·linarith
 ·show _ ≤ ((if n + 1 ≤ 2000 ∧ (n + 1) % 2 = 1 then s.Aphi + Hi * (w + 1) else s.Aphi : ℕ) : ℝ)
  rw [hAP]; split_ifs
  ·push_cast at hT2 ⊢; linarith
  ·linarith
 ·show ((if n + 1 ≤ 2000 ∧ (n + 1) % 2 = 0 then s.Anlo + Lo * w else s.Anlo : ℕ) : ℝ) ≤ _
  rw [hAN]; split_ifs
  ·push_cast at hT1 ⊢; linarith
  ·linarith
 ·show _ ≤ ((if n + 1 ≤ 2000 ∧ (n + 1) % 2 = 0 then s.Anhi + Hi * (w + 1) else s.Anhi : ℕ) : ℝ)
  rw [hAN]; split_ifs
  ·push_cast at hT2 ⊢; linarith
  ·linarith
 ·show ((if isPr (n + 1) then s.Tlo + Lo * w3 else s.Tlo : ℕ) : ℝ) ≤ _
  rw [hTP]
  by_cases hp : (n + 1).Prime
  ·rw [if_pos (hpr.2 hp), if_pos hp, Nat.cast_add s.Tlo]; linarith
  ·rw [if_neg (fun h' => hp (hpr.1 h')), if_neg hp]; linarith
 ·show _ ≤ ((if isPr (n + 1) then s.Thi + Hi * (w3 + 1) else s.Thi : ℕ) : ℝ)
  rw [hTP]
  by_cases hp : (n + 1).Prime
  ·rw [if_pos (hpr.2 hp), if_pos hp, Nat.cast_add s.Thi]; linarith
  ·rw [if_neg (fun h' => hp (hpr.1 h')), if_neg hp]; linarith
lemma vaA : ∀ (len n : ℕ) (s s' : WS), 1 ≤ n → n + len < 21609 → Inv n s →
  vbj n len s = some s' → Inv (n + len) s' := by
 intro len
 induction len with
 | zero => intro n s s' _ _ h hw; simp only [vbj, Option.some.injEq] at hw; subst hw; simpa using h
 | succ len ih =>
  intro n s s' hn hl h hw
  rw [vbj] at hw
  split_ifs at hw
  rw [show n + (len + 1) = n + 1 + len by ring]
  exact ih (n + 1) _ _ (by omega) (by omega) (voz hn (by omega) h) hw
lemma voJ : Inv 1 ⟨0, 0, 10 ^ 30, 10 ^ 30, 0, 0, 0, 0, 0, 0⟩ := by
 refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Hn, AP, AN, TP] <;> norm_num
lemma wk_1 : vbj 1 999 ⟨0, 0, 1000000000000000000000000000000, 1000000000000000000000000000000, 0, 0, 0, 0, 0, 0⟩ = some ⟨6907755278982031797560645885971, 6907755278982173426209847618105, 7485470860550344912656518203889, 7485470860550344912656518204888, 414161961504611866112429851201522357116253156701092759254066, 414161961504644893991352381387024730346154811309554525795294, 515481990341862445653354812546282635595971934886259701770738, 515481990341920617256590012138992855618994460069094222347433, 185405121375821021928608374452994659023263748269892300871818, 185405121375852387410085774719818692258987424866495758945095⟩ := by decide +kernel
lemma wk_2 : vbj 1000 1000 ⟨6907755278982031797560645885971, 6907755278982173426209847618105, 7485470860550344912656518203889, 7485470860550344912656518204888, 414161961504611866112429851201522357116253156701092759254066, 414161961504644893991352381387024730346154811309554525795294, 515481990341862445653354812546282635595971934886259701770738, 515481990341920617256590012138992855618994460069094222347433, 185405121375821021928608374452994659023263748269892300871818, 185405121375852387410085774719818692258987424866495758945095⟩ = some ⟨7600902459541977106977878005395, 7600902459542118735627079750529, 8178368103610282409577656570719, 8178368103610282409577656572718, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405493882399587505837836209168658420609376961454990886384, 185405493882430952994675611114672547964337666297689662125743⟩ := by decide +kernel
lemma wk_3 : vbj 2000 1 ⟨7600902459541977106977878005395, 7600902459542118735627079750529, 8178368103610282409577656570719, 8178368103610282409577656572718, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405493882399587505837836209168658420609376961454990886384, 185405493882430952994675611114672547964337666297689662125743⟩ = some ⟨7601402334583628154891941620977, 7601402334583769783541143366124, 8178867853735219940812039379314, 8178867853735219940812039381314, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405493882399587505837836209168658420609376961454990886384, 185405493882430952994675611114672547964337666297689662125743⟩ := by decide +kernel
lemma wk_4 : vbj 2001 1 ⟨7601402334583628154891941620977, 7601402334583769783541143366124, 8178867853735219940812039379314, 8178867853735219940812039381314, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405493882399587505837836209168658420609376961454990886384, 185405493882430952994675611114672547964337666297689662125743⟩ = some ⟨7601901959875060640144687404312, 7601901959875202268793889149472, 8179367354234720440312538879813, 8179367354234720440312538881814, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405493882399587505837836209168658420609376961454990886384, 185405493882430952994675611114672547964337666297689662125743⟩ := by decide +kernel
lemma wk_5 : vbj 2002 998 ⟨7601901959875060640144687404312, 7601901959875202268793889149472, 8179367354234720440312538879813, 8179367354234720440312538881814, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405493882399587505837836209168658420609376961454990886384, 185405493882430952994675611114672547964337666297689662125743⟩ = some ⟨8006367567650141488955891118828, 8006367567650283117605092876962, 8583749889959187114343792089862, 8583749889959187114343792092861, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405562840222149984480950547839097581236279845441168941712, 185405562840253515474574868107395388073706668107632243579897⟩ := by decide +kernel
lemma wk_6 : vbj 3000 1000 ⟨8006367567650141488955891118828, 8006367567650283117605092876962, 8583749889959187114343792089862, 8583749889959187114343792092861, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405562840222149984480950547839097581236279845441168941712, 185405562840253515474574868107395388073706668107632243579897⟩ = some ⟨8294049640101922416395110122829, 8294049640102064045044311893963, 8871390299795227230713699726351, 8871390299795227230713699730350, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405586570700973189143874705600131186844277402355603049491, 185405586570732338679650831198156255970473208035157501409983⟩ := by decide +kernel
lemma wk_7 : vbj 4000 1000 ⟨8294049640101922416395110122829, 8294049640102064045044311893963, 8871390299795227230713699726351, 8871390299795227230713699730350, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405586570700973189143874705600131186844277402355603049491, 185405586570732338679650831198156255970473208035157501409983⟩ = some ⟨8517193191416132172161405211175, 8517193191416273800810606995309, 9094508852984436967261245531026, 9094508852984436967261245536025, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405597884874748944150465593974393035140758369103051998724, 185405597884906114434848307486060782829088741145557899728730⟩ := by decide +kernel
lemma wk_8 : vbj 5000 1000 ⟨8517193191416132172161405211175, 8517193191416273800810606995309, 9094508852984436967261245531026, 9094508852984436967261245536025, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405597884874748944150465593974393035140758369103051998724, 185405597884906114434848307486060782829088741145557899728730⟩ = some ⟨8699514748210086798373123234359, 8699514748210228427022325031493, 9276813744130243438421523395398, 9276813744130243438421523401397, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405603885359607389524997272036452755855648576719573672389, 185405603885390972880321629328068820037185415902008790936384⟩ := by decide +kernel
lemma wk_9 : vbj 6000 1000 ⟨8699514748210086798373123234359, 8699514748210228427022325031493, 9276813744130243438421523395398, 9276813744130243438421523401397, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405603885359607389524997272036452755855648576719573672389, 185405603885390972880321629328068820037185415902008790936384⟩ = some ⟨8853665428037345102665998617383, 8853665428037486731315200427517, 9430952519809731520556343117182, 9430952519809731520556343124181, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405607665968443979406887680025710340879430170905492343236, 185405607665999809470264556289612257220669970949979533905607⟩ := by decide +kernel
lemma voO : vbj 7000 1000 ⟨8853665428037345102665998617383, 8853665428037486731315200427517, 9430952519809731520556343117182, 9430952519809731520556343124181, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405607665968443979406887680025710340879430170905492343236, 185405607665999809470264556289612257220669970949979533905607⟩ = some ⟨8987196820661867725812342236424, 8987196820662009354461544059558, 9564474984261422509613354674515, 9564474984261422509613354682514, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405609941934997464197237640246365463757466126735449724966, 185405609941966362955091050280089764792907769828688168573434⟩ := by decide +kernel
lemma voR : vbj 8000 1000 ⟨8987196820661867725812342236424, 8987196820662009354461544059558, 9564474984261422509613354674515, 9564474984261422509613354682514, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405609941934997464197237640246365463757466126735449724966, 185405609941966362955091050280089764792907769828688168573434⟩ = some ⟨9104979856318251180351136343753, 9104979856318392809000338179887, 9682251075746638267914524139659, 9682251075746638267914524148658, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405611571748684985824108809499500714336328280398167916276, 185405611571780050476743444981990857461042353696567948584608⟩ := by decide +kernel
lemma voP : vbj 9000 1000 ⟨9104979856318251180351136343753, 9104979856318392809000338179887, 9682251075746638267914524139659, 9682251075746638267914524148658, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405611571748684985824108809499500714336328280398167916276, 185405611571780050476743444981990857461042353696567948584608⟩ = some ⟨9210340371976077481578637322766, 9210340371976219110227839171900, 9787606036044382264178477900021, 9787606036044382264178477910020, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405612778800474506518477656384828942886747350506934400227, 185405612778831839997456488856567570421760399094258202397594⟩ := by decide +kernel
lemma voV : vbj 10000 1000 ⟨9210340371976077481578637322766, 9210340371976219110227839171900, 9787606036044382264178477900021, 9787606036044382264178477910020, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405612778800474506518477656384828942886747350506934400227, 185405612778831839997456488856567570421760399094258202397594⟩ = some ⟨9305650551780402341622589444417, 9305650551780543970271791306551, 9882911670538789768586373744237, 9882911670538789768586373755236, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405613632061745038105615667633045904919338071692393101857, 185405613632093110529056684205319865549693021838760857481343⟩ := by decide +kernel
lemma voS : vbj 11000 1000 ⟨9305650551780402341622589444417, 9305650551780543970271791306551, 9882911670538789768586373744237, 9882911670538789768586373755236, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405613632061745038105615667633045904919338071692393101857, 185405613632093110529056684205319865549693021838760857481343⟩ = some ⟨9392661928770032107790355344703, 9392661928770173736439557219837, 9969919259759633186255036461821, 9969919259759633186255036473820, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405614265533812178530379595677479754215198851111693146230, 185405614265565177669491045658023386175948951140939192359990⟩ := by decide +kernel
lemma voL : vbj 12000 1000 ⟨9392661928770032107790355344703, 9392661928770173736439557219837, 9969919259759633186255036461821, 9969919259759633186255036473820, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405614265533812178530379595677479754215198851111693146230, 185405614265565177669491045658023386175948951140939192359990⟩ = some ⟨9472704636443568533614133304897, 9472704636443710162263335193031, 10049958762390571540524484725040, 10049958762390571540524484738039, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405614793232699750782288155165736735592139957905911854612, 185405614793264065241750879149519721559821378832381348709617⟩ := by decide +kernel
lemma voY : vbj 13000 1000 ⟨9472704636443568533614133304897, 9472704636443710162263335193031, 10049958762390571540524484725040, 10049958762390571540524484738039, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405614793232699750782288155165736735592139957905911854612, 185405614793264065241750879149519721559821378832381348709617⟩ = some ⟨9546812608597290412083230726710, 9546812608597432040732432627844, 10124063987359472745087069645754, 10124063987359472745087069659753, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405615200271717094108079921431646149778586031555567148362, 185405615200303082585082734603141234909956562831579646345822⟩ := by decide +kernel
lemma voW : vbj 14000 1000 ⟨9546812608597290412083230726710, 9546812608597432040732432627844, 10124063987359472745087069645754, 10124063987359472745087069659753, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405615200271717094108079921431646149778586031555567148362, 185405615200303082585082734603141234909956562831579646345822⟩ = some ⟨9615805480084241863556650430424, 9615805480084383492205852344558, 10193054477948842941784063033116, 10193054477948842941784063048115, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405615520041953905750454815799045209500994395129683450609, 185405615520073319396729836800893669108196386519008033187939⟩ := by decide +kernel
lemma voU : vbj 15000 1000 ⟨9615805480084241863556650430424, 9615805480084383492205852344558, 10193054477948842941784063033116, 10193054477948842941784063048115, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405615520041953905750454815799045209500994395129683450609, 185405615520073319396729836800893669108196386519008033187939⟩ = some ⟨9680344001221813035229574344616, 9680344001221954663878776271750, 10257590915797930317123238174156, 10257590915797930317123238190155, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405615800609902871636529466790095524909668645128437503790, 185405615800641268362620031465517162531161439749248164790480⟩ := by decide +kernel
lemma voX : vbj 16000 1000 ⟨9680344001221813035229574344616, 9680344001221954663878776271750, 10257590915797930317123238174156, 10257590915797930317123238190155, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405615800609902871636529466790095524909668645128437503790, 185405615800641268362620031465517162531161439749248164790480⟩ = some ⟨9740968623038247877810180475156, 9740968623038389506459382415290, 10318213699416241240991341929008, 10318213699416241240991341946007, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405616012809629959673977973227052151010421286828247893257, 185405616012840995450660576018234530801974690896565198596358⟩ := by decide +kernel
lemma voQ : vbj 17000 1000 ⟨9740968623038247877810180475156, 9740968623038389506459382415290, 10318213699416241240991341929008, 10318213699416241240991341946007, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405616012809629959673977973227052151010421286828247893257, 185405616012840995450660576018234530801974690896565198596358⟩ = some ⟨9798127036878196489768368451090, 9798127036878338118417570404224, 10375370479300410736634835063035, 10375370479300410736634835081034, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405616202476518305879147381139012292220653002123318946794, 185405616202507883796868496080778727733379112010328213584568⟩ := by decide +kernel
lemma voT : vbj 18000 1000 ⟨9798127036878196489768368451090, 9798127036878338118417570404224, 10375370479300410736634835063035, 10375370479300410736634835081034, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405616202476518305879147381139012292220653002123318946794, 185405616202507883796868496080778727733379112010328213584568⟩ = some ⟨9852194258148472257569673286171, 9852194258148613886218875252305, 10429436238608743798402895296429, 10429436238608743798402895315428, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405616349488495077860053744194375715964180024136680178820, 185405616349519860568851523105681366648117016025530091458113⟩ := by decide +kernel
lemma voM : vbj 19000 1000 ⟨9852194258148472257569673286171, 9852194258148613886218875252305, 10429436238608743798402895296429, 10429436238608743798402895315428, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405616349488495077860053744194375715964180024136680178820, 185405616349519860568851523105681366648117016025530091458113⟩ = some ⟨9903487552536022790995869428895, 9903487552536164419645071408029, 10480728217229327572814460020486, 10480728217229327572814460040485, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405616488059363053054707220436096183781492452508949937766, 185405616488090728544048164453708440410915279815882807287005⟩ := by decide +kernel
lemma voN : Inv 1 ⟨0, 0, 1000000000000000000000000000000, 1000000000000000000000000000000, 0, 0, 0, 0, 0, 0⟩ := voJ
lemma voC : Inv 1000 ⟨6907755278982031797560645885971, 6907755278982173426209847618105, 7485470860550344912656518203889, 7485470860550344912656518204888, 414161961504611866112429851201522357116253156701092759254066, 414161961504644893991352381387024730346154811309554525795294, 515481990341862445653354812546282635595971934886259701770738, 515481990341920617256590012138992855618994460069094222347433, 185405121375821021928608374452994659023263748269892300871818, 185405121375852387410085774719818692258987424866495758945095⟩ := vaA 999 1 _ _ (by norm_num) (by norm_num) voN wk_1
lemma voG : Inv 2000 ⟨7600902459541977106977878005395, 7600902459542118735627079750529, 8178368103610282409577656570719, 8178368103610282409577656572718, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405493882399587505837836209168658420609376961454990886384, 185405493882430952994675611114672547964337666297689662125743⟩ := vaA 1000 1000 _ _ (by norm_num) (by norm_num) voC wk_2
lemma vox : Inv 2001 ⟨7601402334583628154891941620977, 7601402334583769783541143366124, 8178867853735219940812039379314, 8178867853735219940812039381314, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405493882399587505837836209168658420609376961454990886384, 185405493882430952994675611114672547964337666297689662125743⟩ := vaA 1 2000 _ _ (by norm_num) (by norm_num) voG wk_3
lemma vou : Inv 2002 ⟨7601901959875060640144687404312, 7601901959875202268793889149472, 8179367354234720440312538879813, 8179367354234720440312538881814, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405493882399587505837836209168658420609376961454990886384, 185405493882430952994675611114672547964337666297689662125743⟩ := vaA 1 2001 _ _ (by norm_num) (by norm_num) vox wk_4
lemma voF : Inv 3000 ⟨8006367567650141488955891118828, 8006367567650283117605092876962, 8583749889959187114343792089862, 8583749889959187114343792092861, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405562840222149984480950547839097581236279845441168941712, 185405562840253515474574868107395388073706668107632243579897⟩ := vaA 998 2002 _ _ (by norm_num) (by norm_num) vou wk_5
lemma voy : Inv 4000 ⟨8294049640101922416395110122829, 8294049640102064045044311893963, 8871390299795227230713699726351, 8871390299795227230713699730350, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405586570700973189143874705600131186844277402355603049491, 185405586570732338679650831198156255970473208035157501409983⟩ := vaA 1000 3000 _ _ (by norm_num) (by norm_num) voF wk_6
lemma voH : Inv 5000 ⟨8517193191416132172161405211175, 8517193191416273800810606995309, 9094508852984436967261245531026, 9094508852984436967261245536025, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405597884874748944150465593974393035140758369103051998724, 185405597884906114434848307486060782829088741145557899728730⟩ := vaA 1000 4000 _ _ (by norm_num) (by norm_num) voy wk_7
lemma voB : Inv 6000 ⟨8699514748210086798373123234359, 8699514748210228427022325031493, 9276813744130243438421523395398, 9276813744130243438421523401397, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405603885359607389524997272036452755855648576719573672389, 185405603885390972880321629328068820037185415902008790936384⟩ := vaA 1000 5000 _ _ (by norm_num) (by norm_num) voH wk_8
lemma voD : Inv 7000 ⟨8853665428037345102665998617383, 8853665428037486731315200427517, 9430952519809731520556343117182, 9430952519809731520556343124181, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405607665968443979406887680025710340879430170905492343236, 185405607665999809470264556289612257220669970949979533905607⟩ := vaA 1000 6000 _ _ (by norm_num) (by norm_num) voB wk_9
lemma voA : Inv 8000 ⟨8987196820661867725812342236424, 8987196820662009354461544059558, 9564474984261422509613354674515, 9564474984261422509613354682514, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405609941934997464197237640246365463757466126735449724966, 185405609941966362955091050280089764792907769828688168573434⟩ := vaA 1000 7000 _ _ (by norm_num) (by norm_num) voD voO
lemma vov : Inv 9000 ⟨9104979856318251180351136343753, 9104979856318392809000338179887, 9682251075746638267914524139659, 9682251075746638267914524148658, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405611571748684985824108809499500714336328280398167916276, 185405611571780050476743444981990857461042353696567948584608⟩ := vaA 1000 8000 _ _ (by norm_num) (by norm_num) voA voR
lemma voi : Inv 10000 ⟨9210340371976077481578637322766, 9210340371976219110227839171900, 9787606036044382264178477900021, 9787606036044382264178477910020, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405612778800474506518477656384828942886747350506934400227, 185405612778831839997456488856567570421760399094258202397594⟩ := vaA 1000 9000 _ _ (by norm_num) (by norm_num) vov voP
lemma vok : Inv 11000 ⟨9305650551780402341622589444417, 9305650551780543970271791306551, 9882911670538789768586373744237, 9882911670538789768586373755236, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405613632061745038105615667633045904919338071692393101857, 185405613632093110529056684205319865549693021838760857481343⟩ := vaA 1000 10000 _ _ (by norm_num) (by norm_num) voi voV
lemma voq : Inv 12000 ⟨9392661928770032107790355344703, 9392661928770173736439557219837, 9969919259759633186255036461821, 9969919259759633186255036473820, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405614265533812178530379595677479754215198851111693146230, 185405614265565177669491045658023386175948951140939192359990⟩ := vaA 1000 11000 _ _ (by norm_num) (by norm_num) vok voS
lemma vog : Inv 13000 ⟨9472704636443568533614133304897, 9472704636443710162263335193031, 10049958762390571540524484725040, 10049958762390571540524484738039, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405614793232699750782288155165736735592139957905911854612, 185405614793264065241750879149519721559821378832381348709617⟩ := vaA 1000 12000 _ _ (by norm_num) (by norm_num) voq voL
lemma von : Inv 14000 ⟨9546812608597290412083230726710, 9546812608597432040732432627844, 10124063987359472745087069645754, 10124063987359472745087069659753, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405615200271717094108079921431646149778586031555567148362, 185405615200303082585082734603141234909956562831579646345822⟩ := vaA 1000 13000 _ _ (by norm_num) (by norm_num) vog voY
lemma voj : Inv 15000 ⟨9615805480084241863556650430424, 9615805480084383492205852344558, 10193054477948842941784063033116, 10193054477948842941784063048115, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405615520041953905750454815799045209500994395129683450609, 185405615520073319396729836800893669108196386519008033187939⟩ := vaA 1000 14000 _ _ (by norm_num) (by norm_num) von voW
lemma vor : Inv 16000 ⟨9680344001221813035229574344616, 9680344001221954663878776271750, 10257590915797930317123238174156, 10257590915797930317123238190155, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405615800609902871636529466790095524909668645128437503790, 185405615800641268362620031465517162531161439749248164790480⟩ := vaA 1000 15000 _ _ (by norm_num) (by norm_num) voj voU
lemma vof : Inv 17000 ⟨9740968623038247877810180475156, 9740968623038389506459382415290, 10318213699416241240991341929008, 10318213699416241240991341946007, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405616012809629959673977973227052151010421286828247893257, 185405616012840995450660576018234530801974690896565198596358⟩ := vaA 1000 16000 _ _ (by norm_num) (by norm_num) vor voX
lemma voo : Inv 18000 ⟨9798127036878196489768368451090, 9798127036878338118417570404224, 10375370479300410736634835063035, 10375370479300410736634835081034, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405616202476518305879147381139012292220653002123318946794, 185405616202507883796868496080778727733379112010328213584568⟩ := vaA 1000 17000 _ _ (by norm_num) (by norm_num) vof voQ
lemma vot : Inv 19000 ⟨9852194258148472257569673286171, 9852194258148613886218875252305, 10429436238608743798402895296429, 10429436238608743798402895315428, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405616349488495077860053744194375715964180024136680178820, 185405616349519860568851523105681366648117016025530091458113⟩ := vaA 1000 18000 _ _ (by norm_num) (by norm_num) voo voT
lemma vos : Inv 20000 ⟨9903487552536022790995869428895, 9903487552536164419645071408029, 10480728217229327572814460020486, 10480728217229327572814460040485, 415965612609194953981771179511765782034699251719094814675474, 415965612609228017267835359632587260998168063343960781626071, 517283140441681910657737343026314586432520974860560751180381, 517283140441740117615065411569467023913029209691431588727885, 185405616488059363053054707220436096183781492452508949937766, 185405616488090728544048164453708440410915279815882807287005⟩ := vaA 1000 19000 _ _ (by norm_num) (by norm_num) vot voM
end vaa.vcP.vjc
end
section
open Finset Real
namespace vaa.vab.vcT
open vaa.vcP.vkl
open vaa.vcP.vjc (Hn vil vbn)
lemma viF : ∀ n, ((harmonic n : ℚ) : ℝ) = Hn n
 | 0 => by simp [Hn]
 | n + 1 => by
  rw [harmonic_succ, Rat.cast_add, viF n, Hn, Hn, sum_Icc_succ_top (by omega)]
  push_cast; ring
lemma veC : (0.5772156646 : ℝ) ≤ eulerMascheroniConstant ∧
  eulerMascheroniConstant ≤ 0.577215666 := by
 obtain ⟨b1, b2⟩ := vil (n := 20000) (by norm_num)
 rw [viF] at b1 b2
 obtain ⟨l1, l2, h1, h2, -⟩ := vaa.vcP.vjc.vos
 dsimp only at l1 l2 h1 h2
 push_cast at b1 b2 l1 l2 h1 h2
 constructor <;> linarith
def qAux : ℕ → ℕ → ℕ → ℕ
 | 0, _, _ => 0
 | k + 1, a, b => qAux k a b + 2 * 10 ^ 30 * b ^ (2 * k + 1) / ((2 * k + 1) * (2 * a + b) ^ (2 * k + 1))
def qLo (a b : ℕ) : ℕ := qAux 12 a b
def qHi (a b : ℕ) : ℕ := qAux 12 a b + 12 + 3 * 10 ^ 30 * b ^ 25 / (25 * (2 * a + b) ^ 25) + 1
lemma vnM (a b : ℕ) (hb : 0 < b) : ∀ k, (qAux k a b : ℝ) ≤
  10 ^ 30 * ∑ j ∈ range k, (2 : ℝ) * (1 / (2 * j + 1)) * ((b : ℝ) / (2 * a + b)) ^ (2 * j + 1)
 | 0 => by simp [qAux]
 | k + 1 => by
  rw [qAux, sum_range_succ, mul_add, Nat.cast_add]
  refine add_le_add (vnM a b hb k) ?_
  have := Nat.cast_div_le (α := ℝ) (m := 2 * 10 ^ 30 * b ^ (2 * k + 1))
   (n := (2 * k + 1) * (2 * a + b) ^ (2 * k + 1))
  refine this.trans (le_of_eq ?_)
  have : (0 : ℝ) < 2 * a + b := by positivity
  rw [div_pow]
  push_cast
  field_simp
  norm_num
lemma vnV (a b : ℕ) (hb : 0 < b) : ∀ k, 10 ^ 30 * ∑ j ∈ range k,
  (2 : ℝ) * (1 / (2 * j + 1)) * ((b : ℝ) / (2 * a + b)) ^ (2 * j + 1) ≤ (qAux k a b : ℝ) + k
 | 0 => by simp [qAux]
 | k + 1 => by
  rw [qAux, sum_range_succ, mul_add, Nat.cast_add, Nat.cast_succ]
  have h1 := vnV a b hb k
  have hpos : 0 < (2 * k + 1) * (2 * a + b) ^ (2 * k + 1) := by positivity
  obtain ⟨-, h2⟩ := vbZ (2 * 10 ^ 30 * b ^ (2 * k + 1)) _ hpos
  have e : (10 : ℝ) ^ 30 * (2 * (1 / (2 * (k : ℝ) + 1)) * ((b : ℝ) / (2 * a + b)) ^ (2 * k + 1)) =
    ((2 * 10 ^ 30 * b ^ (2 * k + 1) : ℕ) : ℝ) / (((2 * k + 1) * (2 * a + b) ^ (2 * k + 1) : ℕ) : ℝ) := by
   have : (0 : ℝ) < 2 * a + b := by positivity
   rw [div_pow]; push_cast; field_simp; norm_num
  linarith
lemma vcI {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
  (qLo a b : ℝ) ≤ 10 ^ 30 * Real.log (1 + (b : ℝ) / a) ∧
   10 ^ 30 * Real.log (1 + (b : ℝ) / a) ≤ (qHi a b : ℝ) := by
 have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
 have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
 set r : ℝ := (a : ℝ) / b with hr
 have hr0 : 0 < r := by positivity
 obtain ⟨h1, h2⟩ := vbn hr0 12
 have ey : 1 / (2 * r + 1) = (b : ℝ) / (2 * a + b) := by rw [hr]; field_simp
 have el : 1 + r⁻¹ = 1 + (b : ℝ) / a := by rw [hr, inv_div]
 rw [ey, el] at h1 h2
 refine ⟨(vnM a b hb 12).trans (by nlinarith), ?_⟩
 have h3 := vnV a b hb 12
 set y : ℝ := (b : ℝ) / (2 * a + b) with hy
 have hy0 : 0 < y := by positivity
 have hy3 : y ≤ 1 / 3 := by
  rw [hy, div_le_div_iff₀ (by positivity) (by norm_num)]
  have : (b : ℝ) ≤ a := by exact_mod_cast hba
  linarith
 have htail : 2 / (2 * ((12 : ℕ) : ℝ) + 1) * y ^ (2 * 12 + 1) / (1 - y ^ 2) ≤ 3 / 25 * y ^ 25 := by
  have h1y : 8 / 9 ≤ 1 - y ^ 2 := by nlinarith
  rw [div_le_iff₀ (by linarith)]
  push_cast
  have : 0 ≤ y ^ 25 := by positivity
  nlinarith
 have hfl : (10 : ℝ) ^ 30 * (3 / 25 * y ^ 25) ≤
   ((3 * 10 ^ 30 * b ^ 25 / (25 * (2 * a + b) ^ 25) : ℕ) : ℝ) + 1 := by
  have hpos : 0 < 25 * (2 * a + b) ^ 25 := by positivity
  obtain ⟨-, h4⟩ := vbZ (3 * 10 ^ 30 * b ^ 25) _ hpos
  have e : (10 : ℝ) ^ 30 * (3 / 25 * y ^ 25) =
    ((3 * 10 ^ 30 * b ^ 25 : ℕ) : ℝ) / ((25 * (2 * a + b) ^ 25 : ℕ) : ℝ) := by
   have : (0 : ℝ) < 2 * a + b := by positivity
   rw [hy, div_pow]; push_cast; field_simp; norm_num
  linarith
 unfold qHi
 push_cast
 push_cast at h3
 nlinarith
end vaa.vab.vcT
end
section
open Complex MeasureTheory Set Filter
open scoped Topology
namespace vaa.vab.vaT
lemma vdR {s : ℂ} (hs : 1 < s.re) :
  ‖riemannZeta s‖ ≤ ‖riemannZeta (s.re : ℂ)‖ := by
 rw [zeta_eq_tsum_one_div_nat_cpow hs, vbg.vbJ hs]
 have hsum := Complex.summable_one_div_nat_cpow.mpr hs
 calc
  _ ≤ ∑' n : ℕ, ‖1 / (n : ℂ) ^ s‖ := norm_tsum_le_tsum_norm hsum.norm
  _ = ∑' n : ℕ, (n : ℝ) ^ (-s.re) := by
   congr 1
   funext n
   rw [one_div, ← Complex.cpow_neg,
    Complex.norm_natCast_cpow_of_re_ne_zero _ (by simp; linarith), Complex.neg_re]
lemma vjN {s : ℂ} (hs : 3 / 2 ≤ s.re) : ‖riemannZeta s‖ ≤ 3 := by
 have hs1 : 1 < s.re := by linarith
 have hh := vbg.vcW hs1 (N := 1) (by norm_num)
 norm_num [vbg.vbD] at hh
 have hden : (0 : ℝ) < s.re - 1 := by linarith
 have hdiv : 1 / (s.re - 1) ≤ 2 := by
  apply (div_le_iff₀ hden).mpr
  linarith
 simp only [one_div] at hdiv
 exact (vdR hs1).trans (by linarith)
lemma vek {a : ℂ} (ha : a.re < 0) :
  Tendsto (fun n : ℕ => (n : ℂ) ^ a) atTop (𝓝 0) := by
 rw [tendsto_zero_iff_norm_tendsto_zero]
 simp_rw [Complex.norm_natCast_cpow_of_re_ne_zero _ ha.ne]
 simpa only [neg_neg, Function.comp_def] using
  (tendsto_rpow_neg_atTop (by linarith : 0 < -a.re)).comp
   tendsto_natCast_atTop_atTop
lemma vfA {s : ℂ} (hs : 0 < s.re) (hs_one : s ≠ 1)
  {N : ℕ} (hN : 1 ≤ N) :
  ‖riemannZeta s - (∑ k ∈ Finset.range N, (k : ℂ) ^ (-s))
    - (N : ℂ) ^ (-s) / 2
    - (N : ℂ) ^ (1 - s) / (s - 1)
    - s * (N : ℂ) ^ (-s - 1) / 12‖ ≤
   (1 / 12 : ℝ) * ∫ x in Ioi (N : ℝ),
    ‖s * (s + 1) * (x : ℂ) ^ (-s - 2)‖ := by
 have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
 have hs0 : -s ≠ 0 := by
  intro he
  have := congrArg Complex.re he
  simp only [Complex.neg_re, Complex.zero_re] at this
  linarith
 have hs1 : -s - 1 ≠ 0 := by
  intro he
  have := congrArg Complex.re he
  simp only [Complex.sub_re, Complex.neg_re, Complex.one_re, Complex.zero_re] at this
  linarith
 have hf (x : ℝ) (hx : (N : ℝ) ≤ x) :
   HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s))
    (-s * (x : ℂ) ^ (-s - 1)) x :=
  hasDerivAt_ofReal_cpow_const (hN0.trans_le hx).ne' hs0
 have hg (x : ℝ) (hx : (N : ℝ) ≤ x) :
   HasDerivAt (fun y : ℝ => -s * (y : ℂ) ^ (-s - 1))
    (s * (s + 1) * (x : ℂ) ^ (-s - 2)) x := by
  refine ((hasDerivAt_ofReal_cpow_const (hN0.trans_le hx).ne' hs1).const_mul (-s)).congr_deriv ?_
  rw [show -s - 1 - 1 = -s - 2 by ring]
  ring
 have hc : ContinuousOn (fun x : ℝ => s * (s + 1) * (x : ℂ) ^ (-s - 2))
   (Ici (N : ℝ)) := by
  intro x hx
  exact (continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const _ _
   (Or.inr (hN0.trans_le hx).ne'))).continuousWithinAt
 have hf0 := vek (a := -s) (by simp; linarith)
 have hg0 := (vek (a := -s - 1) (by simp; linarith)).const_mul (-s)
 simp only [mul_zero] at hg0
 have hhi := (integrableOn_Ioi_cpow_of_lt (a := -s - 2) (by simp; linarith)
  hN0).const_mul (s * (s + 1))
 have hh := vdO.veP N hf hg hc
  (vcO.vhI hs hs_one hN) hf0 hg0 hhi
 push_cast at hh
 refine Eq.trans_le ?_ hh
 refine congrArg (fun z : ℂ => ‖z‖) ?_
 ring
lemma vbr {s : ℂ} (hs : 0 < s.re)
  (hs_one : s ≠ 1)
  {N : ℕ} (hN : 1 ≤ N) :
  ‖riemannZeta s - (∑ k ∈ Finset.range N, (k : ℂ) ^ (-s))
    - (N : ℂ) ^ (-s) / 2 - (N : ℂ) ^ (1 - s) / (s - 1)
    - s * (N : ℂ) ^ (-s - 1) / 12‖ ≤
   ‖s * (s + 1)‖ / (12 * (s.re + 1)) * (N : ℝ) ^ (-s.re - 1) := by
 have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
 have hIH : (∫ x in Ioi (N : ℝ), ‖s * (s + 1) * (x : ℂ) ^ (-s - 2)‖) =
   ‖s * (s + 1)‖ * ((N : ℝ) ^ (-s.re - 1) / (s.re + 1)) := by
  calc
   _ = ∫ x in Ioi (N : ℝ), ‖s * (s + 1)‖ * x ^ (-s.re - 2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hN0.trans hx)]
    simp
   _ = ‖s * (s + 1)‖ * ((N : ℝ) ^ (-s.re - 1) / (s.re + 1)) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hN0]
    congr 1
    rw [show -s.re - 2 + 1 = -s.re - 1 by ring,
     show -s.re - 1 = -(s.re + 1) by ring, div_neg, neg_div, neg_neg]
 have hh := vfA hs hs_one hN
 rw [hIH] at hh
 convert hh using 1
 field_simp
lemma vdi {s : ℂ} (hs : 1 < s.re)
  {N : ℕ} (hN : 1 ≤ N) :
  ‖riemannZeta s - (∑ k ∈ Finset.range N, (k : ℂ) ^ (-s))
    - (N : ℂ) ^ (-s) / 2 - (N : ℂ) ^ (1 - s) / (s - 1)
    - s * (N : ℂ) ^ (-s - 1) / 12‖ ≤
   ‖s * (s + 1)‖ / (12 * (s.re + 1)) * (N : ℝ) ^ (-s.re - 1) :=
 vbr (by linarith)
  (by intro he; simp [he] at hs) hN
lemma vfm {s : ℂ} (hs : 1 ≤ s.re) (n : ℕ) :
  ‖∑ k ∈ Finset.range (n + 1), (k : ℂ) ^ (-s)‖ ≤ (harmonic n : ℚ) := by
 have hs0 : -s ≠ 0 := by
  intro he
  have := congrArg Complex.re he
  simp at this
  linarith
 rw [Finset.sum_range_succ']
 simp only [Nat.cast_zero, Complex.zero_cpow hs0, add_zero]
 calc
  _ ≤ ∑ k ∈ Finset.range n, ‖((k + 1 : ℕ) : ℂ) ^ (-s)‖ := norm_sum_le _ _
  _ ≤ ∑ k ∈ Finset.range n, (1 : ℝ) / (k + 1) := by
   apply Finset.sum_le_sum
   intro k hk
   rw [Complex.norm_natCast_cpow_of_pos (Nat.succ_pos k), Complex.neg_re]
   have hk1 : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast (Nat.succ_pos k)
   have hh := Real.rpow_le_rpow_of_exponent_le hk1 (show -s.re ≤ -1 by linarith)
   simpa only [Real.rpow_neg_one, Nat.cast_add, Nat.cast_one, Nat.cast_succ, one_div] using hh
  _ = (harmonic n : ℚ) := by simp [harmonic, Rat.cast_sum, one_div]
lemma vfd {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
  ‖riemannZeta s‖ ≤ (harmonic n : ℚ) + ((n + 1 : ℕ) : ℝ) ^ (-s.re) / 2
   + ((n + 1 : ℕ) : ℝ) ^ (1 - s.re) / ‖s - 1‖
   + ‖s‖ * ((n + 1 : ℕ) : ℝ) ^ (-s.re - 1) / 12
   + ‖s * (s + 1)‖ / (12 * (s.re + 1)) * ((n + 1 : ℕ) : ℝ) ^ (-s.re - 1) := by
 let N : ℕ := n + 1
 let P : ℂ := ∑ k ∈ Finset.range N, (k : ℂ) ^ (-s)
 let a : ℂ := (N : ℂ) ^ (-s) / 2
 let b : ℂ := (N : ℂ) ^ (1 - s) / (s - 1)
 let c : ℂ := s * (N : ℂ) ^ (-s - 1) / 12
 let R : ℂ := riemannZeta s - P - a - b - c
 have hN0 : 0 < N := Nat.succ_pos n
 have hR := vdi hs (N := N) (by omega)
 have hP := vfm hs.le n
 have ha : ‖a‖ = (N : ℝ) ^ (-s.re) / 2 := by
  simp [a, norm_div, Complex.norm_natCast_cpow_of_pos hN0]
 have hb : ‖b‖ = (N : ℝ) ^ (1 - s.re) / ‖s - 1‖ := by
  simp [b, norm_div, Complex.norm_natCast_cpow_of_pos hN0]
 have hc : ‖c‖ = ‖s‖ * (N : ℝ) ^ (-s.re - 1) / 12 := by
  simp [c, norm_div, norm_mul, Complex.norm_natCast_cpow_of_pos hN0]
 have htri : ‖riemannZeta s‖ ≤ ‖P‖ + ‖a‖ + ‖b‖ + ‖c‖ + ‖R‖ := by
  calc
   _ = ‖P + a + b + c + R‖ := by congr 1; dsimp [R]; ring
   _ ≤ ‖P + a + b + c‖ + ‖R‖ := norm_add_le _ _
   _ ≤ (‖P + a + b‖ + ‖c‖) + ‖R‖ := by gcongr; exact norm_add_le _ _
   _ ≤ ((‖P + a‖ + ‖b‖) + ‖c‖) + ‖R‖ := by gcongr; exact norm_add_le _ _
   _ ≤ ((‖P‖ + ‖a‖ + ‖b‖) + ‖c‖) + ‖R‖ := by gcongr; exact norm_add_le _ _
 rw [ha, hb, hc] at htri
 exact htri.trans (by dsimp [R, P, a, b, c, N] at *; linarith)
lemma vgQ (n : ℕ) :
  (harmonic n : ℚ) + 1 / (2 * ((n + 1 : ℕ) : ℝ)) ≤
   Real.log ((n + 1 : ℕ) : ℝ) + Real.eulerMascheroniConstant := by
 have hh := (vaa.vcP.vjc.vil
  (n := n + 1) (by omega)).2
 rw [harmonic_succ] at hh
 push_cast at hh ⊢
 have hden : (n : ℝ) + 1 ≠ 0 := by positivity
 have he : ((n : ℝ) + 1)⁻¹ = 2 * (1 / (2 * ((n : ℝ) + 1))) := by
  field_simp
 rw [he] at hh
 linarith
lemma vhO {s : ℂ} (hs : 1 < s.re) (ht : 0 < s.im) (n : ℕ) :
  ‖riemannZeta s‖ ≤ Real.log ((n + 1 : ℕ) : ℝ) + Real.eulerMascheroniConstant
   + 1 / s.im + ‖s‖ / (12 * (((n + 1 : ℕ) : ℝ) ^ 2))
   + ‖s * (s + 1)‖ / (24 * (((n + 1 : ℕ) : ℝ) ^ 2)) := by
 let N : ℝ := ((n + 1 : ℕ) : ℝ)
 have hN1 : 1 ≤ N := by dsimp [N]; exact_mod_cast Nat.succ_pos n
 have hN0 : 0 < N := by linarith
 have hp1 : N ^ (-s.re) ≤ 1 / N := by
  have hh := Real.rpow_le_rpow_of_exponent_le hN1 (show -s.re ≤ -1 by linarith)
  simpa only [Real.rpow_neg_one, one_div] using hh
 have hp0 : N ^ (1 - s.re) ≤ 1 := by
  have hh := Real.rpow_le_rpow_of_exponent_le hN1 (show 1 - s.re ≤ 0 by linarith)
  simpa only [Real.rpow_zero] using hh
 have hp2 : N ^ (-s.re - 1) ≤ 1 / N ^ 2 := by
  have hh := Real.rpow_le_rpow_of_exponent_le hN1 (show -s.re - 1 ≤ -2 by linarith)
  simpa only [Real.rpow_neg hN0.le, Real.rpow_two, one_div] using hh
 have hden : s.im ≤ ‖s - 1‖ := by
  simpa using (le_abs_self (s - 1).im).trans (Complex.abs_im_le_norm (s - 1))
 have hden0 : 0 < ‖s - 1‖ := ht.trans_le hden
 have hb : N ^ (1 - s.re) / ‖s - 1‖ ≤ 1 / s.im := by
  exact (div_le_div_of_nonneg_right hp0 hden0.le).trans
   (one_div_le_one_div_of_le ht hden)
 have hc : ‖s‖ * N ^ (-s.re - 1) / 12 ≤ ‖s‖ / (12 * N ^ 2) := by
  calc
   _ ≤ ‖s‖ * (1 / N ^ 2) / 12 := by gcongr
   _ = _ := by ring
 have hd0 : ‖s * (s + 1)‖ / (12 * (s.re + 1)) ≤ ‖s * (s + 1)‖ / 24 := by
  exact div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) (by linarith)
 have hd : ‖s * (s + 1)‖ / (12 * (s.re + 1)) * N ^ (-s.re - 1) ≤
   ‖s * (s + 1)‖ / (24 * N ^ 2) := by
  calc
   _ ≤ (‖s * (s + 1)‖ / 24) * (1 / N ^ 2) :=
    mul_le_mul hd0 hp2 (Real.rpow_nonneg hN0.le _) (by positivity)
   _ = _ := by ring
 have ha : (harmonic n : ℚ) + N ^ (-s.re) / 2 ≤
   Real.log N + Real.eulerMascheroniConstant := by
  calc
   _ ≤ (harmonic n : ℚ) + (1 / N) / 2 := by gcongr
   _ = (harmonic n : ℚ) + 1 / (2 * N) := by ring
   _ ≤ _ := vgQ n
 have hz := vfd hs n
 change ‖riemannZeta s‖ ≤ _ at hz
 change ‖riemannZeta s‖ ≤ Real.log N + Real.eulerMascheroniConstant +
  1 / s.im + ‖s‖ / (12 * N ^ 2) + ‖s * (s + 1)‖ / (24 * N ^ 2)
 dsimp only [N] at ha hb hc hd
 linarith
lemma vka {s : ℂ} (hs0 : 1 ≤ s.re) (hs1 : s.re ≤ 3 / 2)
  (ht : 50 ≤ s.im) :
  ‖s‖ ≤ 1.001 * s.im ∧ ‖s * (s + 1)‖ ≤ 1.004 * s.im ^ 2 := by
 have ht0 : 0 ≤ s.im := by linarith
 have ht2 : 2500 ≤ s.im ^ 2 := by nlinarith
 have hs2 : s.re ^ 2 ≤ 9 / 4 := by nlinarith
 have hs3 : (s.re + 1) ^ 2 ≤ 25 / 4 := by nlinarith
 have hn1 := Complex.sq_norm_sub_sq_im s
 have hn2 := Complex.sq_norm_sub_sq_im (s + 1)
 simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, add_zero] at hn2
 have h1 : ‖s‖ ≤ 1.001 * s.im := by nlinarith [norm_nonneg s]
 have h2 : ‖s + 1‖ ≤ 1.002 * s.im := by nlinarith [norm_nonneg (s + 1)]
 refine ⟨h1, ?_⟩
 rw [norm_mul]
 have hp := mul_le_mul h1 h2 (norm_nonneg (s + 1)) (by positivity)
 nlinarith
lemma vbE {s : ℂ}
  (hs : 1 < s.re) (hs1 : s.re ≤ 3 / 2) (ht : 50 ≤ s.im) :
  ‖riemannZeta s‖ ≤ Real.log s.im - 0.048 := by
 let n : ℕ := ⌊s.im / 3⌋₊
 let N : ℝ := ((n + 1 : ℕ) : ℝ)
 have ht0 : 0 < s.im := by linarith
 have hNlo : s.im / 3 ≤ N := by
  dsimp [N, n]
  simpa only [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one (s.im / 3)).le
 have hNhi : N ≤ s.im / 3 + 1 := by
  dsimp [N, n]
  push_cast
  have hh := Nat.floor_le (show (0 : ℝ) ≤ s.im / 3 by positivity)
  linarith
 have hN0 : 0 < N := by linarith
 have hN2 : s.im ^ 2 ≤ 9 * N ^ 2 := by
  have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ s.im / 3) hNlo 2
  nlinarith
 have hlog : Real.log N ≤ Real.log s.im - Real.log 3 + 3 / s.im := by
  have he : s.im / 3 + 1 = (s.im / 3) * (1 + 3 / s.im) := by field_simp
  calc
   _ ≤ Real.log (s.im / 3 + 1) := Real.log_le_log hN0 hNhi
   _ = Real.log s.im - Real.log 3 + Real.log (1 + 3 / s.im) := by
    rw [he, Real.log_mul (by positivity) (by positivity), Real.log_div ht0.ne' (by norm_num)]
   _ ≤ Real.log s.im - Real.log 3 + 3 / s.im := by
    have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 3 / s.im)
    linarith
 obtain ⟨h1, h2⟩ := vka hs.le hs1 ht
 have hc : ‖s‖ / (12 * N ^ 2) ≤ 0.75075 / s.im := by
  apply (div_le_div_iff₀ (by positivity) ht0).mpr
  have hh := mul_le_mul_of_nonneg_right h1 ht0.le
  nlinarith
 have hd : ‖s * (s + 1)‖ / (24 * N ^ 2) ≤ 0.3765 := by
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith
 have hcorr : (4 + 0.75075) / s.im ≤ 0.095015 := by
  apply (div_le_iff₀ ht0).mpr
  nlinarith
 have hγ : Real.eulerMascheroniConstant ≤ 0.578 := by
  linarith [vcT.veC.2]
 have hlog3 : 1.098 ≤ Real.log 3 := by linarith [Real.log_three_gt_d9]
 have hz := vhO hs ht0 n
 change ‖riemannZeta s‖ ≤ Real.log N + Real.eulerMascheroniConstant +
  1 / s.im + ‖s‖ / (12 * N ^ 2) + ‖s * (s + 1)‖ / (24 * N ^ 2) at hz
 have he : 3 / s.im + 1 / s.im + 0.75075 / s.im = (4 + 0.75075) / s.im := by ring
 linarith
lemma vft {s : ℂ} (hs : s.re = 1) (ht : 50 ≤ s.im) :
  ‖riemannZeta s‖ ≤ Real.log s.im - 0.048 := by
 let δ : ℕ → ℝ := fun n => (1 / ((n : ℝ) + 1)) / 2
 have hδ : Tendsto δ atTop (𝓝 0) := by
  simpa only [zero_div, δ] using
   (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 2
 have hδpos (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
 have hδle (n : ℕ) : δ n ≤ 1 / 2 := by
  have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
   (by have := Nat.cast_nonneg (α := ℝ) n; linarith : (1 : ℝ) ≤ (n : ℝ) + 1)
  dsimp [δ]
  norm_num at hh
  simp only [one_div]
  linarith
 have hzseq : Tendsto (fun n : ℕ => s + (δ n : ℂ)) atTop (𝓝 s) := by
  simpa using (Complex.continuous_ofReal.tendsto 0 |>.comp hδ).const_add s
 have hsne : s ≠ 1 := by
  intro he
  have := congrArg Complex.im he
  simp at this
  linarith
 have hζlim := ((differentiableAt_riemannZeta hsne).continuousAt.tendsto.comp hzseq).norm
 apply le_of_tendsto hζlim
 filter_upwards with n
 have hh := vbE (s := s + (δ n : ℂ))
  (by simp [hs]; exact hδpos n) (by simp [hs]; linarith [hδle n]) (by simpa using ht)
 simpa using hh
lemma vbT {s : ℂ} (hs : 1 ≤ s.re) (ht : 50 ≤ s.im) :
  ‖riemannZeta s‖ ≤ Real.log s.im - 0.048 := by
 rcases eq_or_lt_of_le hs with he | hs'
 ·exact vft he.symm ht
 by_cases hs1 : s.re ≤ 3 / 2
 ·exact vbE hs' hs1 ht
 have hz := vjN (le_of_not_ge hs1)
 have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 27)
  (by linarith : (27 : ℝ) ≤ s.im)
 have he : Real.log (27 : ℝ) = 3 * Real.log 3 := by
  rw [show (27 : ℝ) = 3 ^ (3 : ℕ) by norm_num, Real.log_pow]
  norm_num
 rw [he] at hlog
 linarith [Real.log_three_gt_d9]
end vaa.vab.vaT
end
section
namespace vaa.vab.vaF
lemma vnL {t : ℝ} (ht : 0 < t) : Real.log t ≤ t / 2 := by
 have h := Real.log_le_sub_one_of_pos (show 0 < t / 2 by positivity)
 rw [Real.log_div ht.ne' (by norm_num)] at h
 have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
 linarith
lemma vct {t : ℝ} (ht : 50 ≤ t) :
  Real.exp (5 / (2 * t ^ 2)) * (Real.log t - 6 / 125) < Real.log t := by
 have ht0 : 0 < t := by linarith
 have ht2 : 0 < t ^ 2 := by positivity
 have hl0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
 have hq : 5 / (2 * t ^ 2) * Real.log t < 6 / 125 := by
  have h := mul_le_mul_of_nonneg_left (vnL ht0)
   (by positivity : 0 ≤ 5 / (2 * t ^ 2))
  have he : 5 / (2 * t ^ 2) * (t / 2) = 5 / (4 * t) := by
   field_simp
   ring
  rw [he] at h
  have hb : 5 / (4 * t) < 6 / 125 := by
   rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
   linarith
  exact h.trans_lt hb
 have hexp := Real.add_one_le_exp (-(5 / (2 * t ^ 2)))
 have hprod := mul_le_mul_of_nonneg_right hexp hl0
 have hs : Real.log t - 6 / 125 <
   Real.exp (-(5 / (2 * t ^ 2))) * Real.log t := by
  nlinarith
 have hm := mul_lt_mul_of_pos_left hs (Real.exp_pos (5 / (2 * t ^ 2)))
 have he : Real.exp (5 / (2 * t ^ 2)) *
   (Real.exp (-(5 / (2 * t ^ 2))) * Real.log t) = Real.log t := by
  rw [← mul_assoc, ← Real.exp_add]
  simp
 rwa [he] at hm
end vaa.vab.vaF
end
section
open Complex Real
namespace vaa.vab.vde
lemma vhN {σ t : ℝ}
  (hσ : -(1 / 2 : ℝ) ≤ σ) (hσ' : σ ≤ 0) (ht : 50 ≤ t) :
  ‖riemannZeta ((σ : ℂ) + t * I)‖ <
   (t / (2 * Real.pi)) ^ (1 / 2 - σ) * Real.log t := by
 have ht0 : 0 < t := by linarith
 have hζ : ‖riemannZeta (((1 - σ : ℝ) : ℂ) + t * I)‖ ≤ Real.log t - 6 / 125 := by
  have h := vaT.vbT
   (s := (((1 - σ : ℝ) : ℂ) + t * I))
   (by simp; linarith) (by simpa using ht)
  convert h using 1
  norm_num
 have hP : 0 < (t / (2 * Real.pi)) ^ (1 / 2 - σ) :=
  Real.rpow_pos_of_pos (by positivity) _
 calc
  _ ≤ (t / (2 * Real.pi)) ^ (1 / 2 - σ) * Real.exp (5 / (2 * t ^ 2)) *
    ‖riemannZeta (((1 - σ : ℝ) : ℂ) + t * I)‖ :=
   vaP.vcv hσ (by linarith) ht
  _ ≤ (t / (2 * Real.pi)) ^ (1 / 2 - σ) * Real.exp (5 / (2 * t ^ 2)) *
    (Real.log t - 6 / 125) :=
   mul_le_mul_of_nonneg_left hζ (by positivity)
  _ = (t / (2 * Real.pi)) ^ (1 / 2 - σ) *
    (Real.exp (5 / (2 * t ^ 2)) * (Real.log t - 6 / 125)) := by ring
  _ < _ := mul_lt_mul_of_pos_left
   (vaF.vct ht) hP
end vaa.vab.vde
end
section
open Complex Real Set
namespace vaa.vab.vao
lemma vch {T t : ℝ} (hT : 100 ≤ T) (ht : T - radius ≤ t) :
  50 ≤ t := by
 dsimp [radius] at ht
 linarith
lemma viD {T : ℝ} (hT : 100 ≤ T) : 0 < Real.log (T + radius) :=
 Real.log_pos (by dsimp [radius]; linarith)
lemma vhk {T : ℝ} (hT : 100 ≤ T) : 0 ≤ vbk T := by
 have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
  (show (3 : ℝ) ≤ T + radius by dsimp [radius]; linarith)
 exact Real.log_nonneg (by linarith [Real.log_three_gt_d9])
lemma vlB {T : ℝ} (hT : 100 ≤ T) : 0 ≤ vbC T := by
 apply Real.log_nonneg
 rw [le_div_iff₀ (by positivity : 0 < 2 * Real.pi)]
 dsimp [radius]
 nlinarith [Real.pi_lt_four]
lemma vdS {T : ℝ} (hT : 100 ≤ T) : 0 < (T - radius) ^ 2 - 4 := by
 have hl : 50 ≤ T - radius := vch hT le_rfl
 nlinarith
lemma vhR {T : ℝ} (hT : 100 ≤ T) : 0 ≤ vbt T := by
 apply Real.log_nonneg
 rw [le_div_iff₀ (vdS hT)]
 linarith
lemma vmD {H L V σ : ℝ} (hH : 0 ≤ H) (hL : 0 ≤ L) (hV : 0 ≤ V) :
  0 ≤ scalar H L V σ := by
 unfold scalar
 split_ifs with hσ hstrip
 ·exact vbe.vmq (by linarith)
 ·positivity
 ·positivity
lemma vlJ {T : ℝ} (hT : 100 ≤ T) (z : ℂ) : 0 ≤ vcH T z :=
 vmD (vhk hT) (vlB hT) (vhR hT)
lemma vjk {T : ℝ} (hT : 100 ≤ T) :
  Real.exp (vbk T) = Real.log (T + radius) := Real.exp_log (viD hT)
lemma vnd {T : ℝ} (hT : 100 ≤ T) :
  Real.exp (vbt T) = (T - radius) ^ 2 / ((T - radius) ^ 2 - 4) := by
 have hl : 0 < T - radius := by have := vch hT (t := T - radius) le_rfl; linarith
 apply Real.exp_log
 exact div_pos (sq_pos_of_pos hl) (vdS hT)
lemma vhw {T e : ℝ} (hT : 100 ≤ T) :
  Real.exp (vbk T + e * vbC T) =
   Real.log (T + radius) * ((T + radius) / (2 * Real.pi)) ^ e := by
 have hupper : 0 < T + radius := by dsimp [radius]; linarith
 have hbase : 0 < (T + radius) / (2 * Real.pi) := by positivity
 rw [Real.exp_add, vjk hT, Real.rpow_def_of_pos hbase]
 congr 2
 unfold vbC
 ring
lemma vib {T e : ℝ} (hT : 100 ≤ T) :
  Real.exp (vbk T + e * vbC T + vbt T) =
   Real.log (T + radius) * ((T + radius) / (2 * Real.pi)) ^ e *
    ((T - radius) ^ 2 / ((T - radius) ^ 2 - 4)) := by
 rw [Real.exp_add, vhw hT, vnd hT]
lemma vnp {H L V σ : ℝ} (hσ : 5 / 4 ≤ σ) :
  scalar H L V σ = Real.log ‖riemannZeta (σ : ℂ)‖ := by simp [scalar, hσ]
lemma vob {H L V σ : ℝ} (hσ : 1 ≤ σ) (hσ' : σ < 5 / 4) :
  scalar H L V σ = H := by
 simp [scalar, not_le.mpr hσ', max_eq_right (by linarith : 1 - σ ≤ 0),
  max_eq_right (by linarith : -σ ≤ 0), not_lt.mpr hσ]
lemma vmF {H L V σ : ℝ} (hσ : 0 ≤ σ) (hσ' : σ < 1) :
  scalar H L V σ = H + ((1 - σ) / 2) * L + V := by
 simp [scalar, show ¬5 / 4 ≤ σ by linarith, hσ, hσ',
  max_eq_left (by linarith : 0 ≤ 1 - σ)]
 ring
lemma vnK {H L V σ : ℝ} (hσ : σ < 0) :
  scalar H L V σ = H + (1 / 2 - σ) * L := by
 simp [scalar, show ¬5 / 4 ≤ σ by linarith, not_le.mpr hσ,
  max_eq_left (by linarith : 0 ≤ 1 - σ), max_eq_left (by linarith : 0 ≤ -σ)]
 ring
lemma viG {T t e : ℝ} (hT : 100 ≤ T)
  (ht0 : T - radius ≤ t) (ht1 : t ≤ T + radius) (he : 0 ≤ e) :
  (t / (2 * Real.pi)) ^ e * Real.log t ≤
   ((T + radius) / (2 * Real.pi)) ^ e * Real.log (T + radius) := by
 have ht50 := vch hT ht0
 have hT0 : 0 < T := by linarith
 have hupper : 0 < T + radius := by dsimp [radius]; linarith
 have hbase : 0 ≤ t / (2 * Real.pi) := by positivity
 apply mul_le_mul
 ·exact Real.rpow_le_rpow hbase (div_le_div_of_nonneg_right ht1 (by positivity)) he
 ·exact Real.log_le_log (by linarith) ht1
 ·exact Real.log_nonneg (by linarith)
 ·positivity
lemma viU {T t : ℝ} (hT : 100 ≤ T) (ht : T - radius ≤ t) :
  t ^ 2 / (t ^ 2 - 4) ≤ (T - radius) ^ 2 / ((T - radius) ^ 2 - 4) := by
 have hl := vch hT (t := T - radius) le_rfl
 have ht50 := vch hT ht
 have hd : 0 < t ^ 2 - 4 := by nlinarith
 have hs : (T - radius) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (by linarith) ht 2
 rw [div_le_div_iff₀ hd (vdS hT)]
 nlinarith
lemma vdn {z : ℂ}
  (hz : z ∈ Metric.sphere (5 / 4 : ℂ) radius) :
  -(1 / 2 : ℝ) ≤ z.re ∧ |z.im| ≤ radius := by
 have hn : ‖z - (5 / 4 : ℂ)‖ = radius := by
  simpa only [Metric.mem_sphere, dist_eq_norm] using hz
 have hr := Complex.abs_re_le_norm (z - (5 / 4 : ℂ))
 have hi := Complex.abs_im_le_norm (z - (5 / 4 : ℂ))
 rw [hn] at hr hi
 norm_num [Complex.sub_re, Complex.sub_im] at hr hi
 refine ⟨?_, hi⟩
 have hlo := (abs_le.mp hr).1
 dsimp [radius] at hlo
 linarith
lemma viv {T : ℝ} {z : ℂ}
  (hz : z ∈ Metric.sphere (5 / 4 : ℂ) radius) :
  (T - radius ≤ T + z.im ∧ T + z.im ≤ T + radius) ∧
   (T - radius ≤ T - z.im ∧ T - z.im ≤ T + radius) := by
 rcases abs_le.mp (vdn hz).2 with ⟨hlo, hhi⟩
 constructor <;> constructor <;> linarith
end vaa.vab.vao
end
section
open Complex Real Set Filter Metric
open scoped Topology
namespace vaa.vab.vgo
private lemma vjf {ε : ℝ} (hε : 0 < ε) (C : ℝ) :
  Tendsto (fun t : ℝ => Real.exp (ε * (1 - t ^ 2)) * (C * t ^ 2))
   atTop (𝓝 0) := by
 have hp : Tendsto (fun t : ℝ => ε * t ^ 2) atTop atTop :=
  (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).const_mul_atTop hε
 have hh := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hp).const_mul
  (C * Real.exp ε / ε)
 convert hh using 1
 ·funext t
  simp only [Function.comp_apply, pow_one]
  rw [show ε * (1 - t ^ 2) = ε + -(ε * t ^ 2) by ring, Real.exp_add]
  field_simp
 ·ring
lemma norm_le_one {f : ℂ → ℂ} {a : ℝ} (ha : 1 ≤ a)
  (hd : DiffContOnCl ℂ f (Ioo (0 : ℝ) 1 ×ℂ Ioi a))
  (hleft : ∀ z : ℂ, z.re = 0 → a ≤ z.im → ‖f z‖ ≤ 1)
  (hright : ∀ z : ℂ, z.re = 1 → a ≤ z.im → ‖f z‖ ≤ 1)
  (hbottom : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → z.im = a → ‖f z‖ ≤ 1)
  (hgrowth : ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
   0 ≤ z.re → z.re ≤ 1 → a ≤ z.im → ‖f z‖ ≤ C * z.im ^ 2)
  {z : ℂ} (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) (hza : a ≤ z.im) :
  ‖f z‖ ≤ 1 := by
 obtain ⟨C, hC, hgrowth⟩ := hgrowth
 suffices h : ∀ᶠ ε : ℝ in 𝓝[>] 0,
   ‖Complex.exp ((ε : ℂ) * z ^ 2) * f z‖ ≤ 1 by
  apply le_of_tendsto _ h
  have hc : Continuous fun ε : ℝ => ‖Complex.exp ((ε : ℂ) * z ^ 2) * f z‖ := by fun_prop
  simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
 filter_upwards [self_mem_nhdsWithin] with ε hε
 have hε0 : 0 < ε := hε
 let g : ℂ → ℂ := fun w => Complex.exp ((ε : ℂ) * w ^ 2) * f w
 have he (w : ℂ) : ‖g w‖ =
   Real.exp (ε * (w.re ^ 2 - w.im ^ 2)) * ‖f w‖ := by
  simp only [g, norm_mul, Complex.norm_exp]
  congr 2
  simp [pow_two]
 obtain ⟨R, hRz, hRa, hR⟩ : ∃ R : ℝ, z.im < R ∧ a < R ∧
   Real.exp (ε * (1 - R ^ 2)) * (C * R ^ 2) ≤ 1 := by
  have hevent := (vjf hε0 C).eventually
   (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  exact ((eventually_gt_atTop z.im).and
   ((eventually_gt_atTop a).and hevent)).exists
 have hgd : DiffContOnCl ℂ g (Ioo (0 : ℝ) 1 ×ℂ Ioo a R) := by
  have hgexp : Differentiable ℂ (fun w : ℂ => Complex.exp ((ε : ℂ) * w ^ 2)) :=
   ((differentiable_id.pow 2).const_mul _).cexp
  simpa only [smul_eq_mul] using (hgexp.diffContOnCl.smul hd).mono
   (fun w (hw : w ∈ Ioo (0 : ℝ) 1 ×ℂ Ioo a R) => (⟨hw.1, hw.2.1⟩ : w ∈ Ioo (0 : ℝ) 1 ×ℂ Ioi a))
 have hweight (w : ℂ) (hw0 : 0 ≤ w.re) (hw1 : w.re ≤ 1) (hwa : a ≤ w.im) :
   Real.exp (ε * (w.re ^ 2 - w.im ^ 2)) ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  apply mul_nonpos_of_nonneg_of_nonpos hε0.le
  have hr2 : w.re ^ 2 ≤ 1 := pow_le_one₀ hw0 hw1
  nlinarith
 apply Complex.norm_le_of_forall_mem_frontier_norm_le
  ((isBounded_Ioo (0 : ℝ) 1).reProdIm (isBounded_Ioo a R)) hgd
 ·intro w hw
  rw [frontier_reProdIm, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1),
   closure_Ioo hRa.ne, frontier_Ioo (by norm_num : (0 : ℝ) < 1),
   frontier_Ioo hRa] at hw
  simp only [mem_union, mem_reProdIm, mem_insert_iff, mem_singleton_iff] at hw
  rcases hw with ⟨⟨hw0, hw1⟩, hwa | hwR⟩ | ⟨hw0 | hw1, ⟨hwa, _⟩⟩
  ·rw [he]
   exact mul_le_one₀ (hweight w hw0 hw1 hwa.ge) (norm_nonneg _)
    (hbottom w hw0 hw1 hwa)
  ·rw [he, hwR]
   have hr2 : w.re ^ 2 ≤ 1 := pow_le_one₀ hw0 hw1
   calc
    _ ≤ Real.exp (ε * (1 - R ^ 2)) * (C * R ^ 2) := by
     apply mul_le_mul
     ·exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) hε0.le)
     ·simpa [hwR] using hgrowth w hw0 hw1 (by linarith)
     ·exact norm_nonneg _
     ·positivity
    _ ≤ 1 := hR
  ·rw [he]
   exact mul_le_one₀ (hweight w hw0.ge (by linarith) hwa) (norm_nonneg _)
    (hleft w hw0 hwa)
  ·rw [he]
   exact mul_le_one₀ (hweight w (by linarith) hw1.le hwa) (norm_nonneg _)
    (hright w hw1 hwa)
 ·rw [closure_reProdIm, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1), closure_Ioo hRa.ne]
  exact ⟨⟨hz0, hz1⟩, ⟨hza, hRz.le⟩⟩
end vaa.vab.vgo
end
section
open Complex Real MeasureTheory Set
open scoped Topology
namespace vaa.vab.vdx
noncomputable def exponent (s : ℂ) : ℂ :=
 (s - 1) / 2 * Complex.log (-s * I / (2 * Real.pi)) - s / 2
noncomputable def vaG (s : ℂ) : ℂ :=
 riemannZeta s * Complex.exp (exponent s) / Complex.log (-s * I)
lemma vhB {z : ℂ} (hz : 0 < z.re) :
  z.arg = Real.arctan (z.im / z.re) := by
 rw [← Complex.tan_arg]
 exact (Real.arctan_tan
  (Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hz))
  (Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hz))).symm
lemma vjP {x : ℝ} (hx : 0 ≤ x) :
  x - x ^ 3 / 3 ≤ Real.arctan x := by
 have hf : Continuous (fun u : ℝ => 1 - u ^ 2) := by fun_prop
 have hg : Continuous (fun u : ℝ => 1 / (1 + u ^ 2)) := by
  have h1 : ∀ u : ℝ, 1 + u ^ 2 ≠ 0 := fun u => by positivity
  have h2 : Continuous (fun u : ℝ => 1 + u ^ 2) := by fun_prop
  exact Continuous.div (f := fun _ : ℝ => (1 : ℝ)) (g := fun u : ℝ => 1 + u ^ 2)
   continuous_const h2 h1
 have hi := intervalIntegral.integral_mono_on (μ := volume) hx
  (hf.intervalIntegrable 0 x) (hg.intervalIntegrable 0 x)
  (fun u _ => by
   apply (le_div_iff₀ (by positivity : (0 : ℝ) < 1 + u ^ 2)).mpr
   nlinarith [sq_nonneg (u ^ 2)])
 rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
  ((show Continuous (fun u : ℝ => u ^ 2) by fun_prop).intervalIntegrable _ _),
  intervalIntegral.integral_const, integral_pow, integral_one_div_one_add_sq] at hi
 norm_num at hi ⊢
 exact hi
noncomputable def vay (σ t : ℝ) : ℝ :=
 (σ - 1) / 4 * Real.log (1 + (σ / t) ^ 2) +
  t / 2 * Real.arctan (σ / t) - σ / 2
lemma vgx {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
  (ht : 0 < t) : vay σ t ≤ 0 := by
 have hlog : 0 ≤ Real.log (1 + (σ / t) ^ 2) :=
  Real.log_nonneg (by nlinarith [sq_nonneg (σ / t)])
 have ha := Real.arctan_le_self (div_nonneg hσ0 ht.le)
 have hm := mul_le_mul_of_nonneg_left ha (show 0 ≤ t / 2 by positivity)
 have he : t / 2 * (σ / t) = σ / 2 := by field_simp
 rw [he] at hm
 unfold vay
 have hn : (σ - 1) / 4 * Real.log (1 + (σ / t) ^ 2) ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg (by linarith) hlog
 linarith
lemma vhe {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
  (ht : 0 < t) : -(1 / t ^ 2) ≤ vay σ t := by
 have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
 have hu : 0 ≤ σ / t := div_nonneg hσ0 ht.le
 have hl : Real.log (1 + (σ / t) ^ 2) ≤ (σ / t) ^ 2 := by
  simpa [-Complex.ofReal_arctan] using Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + (σ / t) ^ 2)
 have ha := vjP hu
 have hm := mul_le_mul_of_nonneg_left ha (show 0 ≤ t / 2 by positivity)
 have hml := mul_le_mul_of_nonpos_left hl (show (σ - 1) / 4 ≤ 0 by linarith)
 have hs2 : σ ^ 2 ≤ 1 := pow_le_one₀ hσ0 hσ1
 have hs3 : σ ^ 3 ≤ 1 := pow_le_one₀ hσ0 hσ1
 have he : (σ - 1) / 4 * (σ / t) ^ 2 +
   t / 2 * (σ / t - (σ / t) ^ 3 / 3) - σ / 2 =
   (σ ^ 3 / 12 - σ ^ 2 / 4) / t ^ 2 := by
  field_simp
  ring
 have hlo : (σ ^ 3 / 12 - σ ^ 2 / 4) / t ^ 2 ≤ vay σ t := by
  rw [← he]
  unfold vay
  linarith
 refine le_trans ?_ hlo
 rw [← neg_div, div_le_div_iff_of_pos_right ht2]
 nlinarith [pow_nonneg hσ0 3]
noncomputable def vbI (σ t : ℝ) : ℝ :=
 Real.sqrt ((Real.log t + Real.log (1 + (σ / t) ^ 2) / 2) ^ 2 +
  (Real.arctan (σ / t)) ^ 2)
noncomputable def correction (σ t : ℝ) : ℝ :=
 Real.exp (vay σ t) * Real.log t / vbI σ t
lemma vdF {σ t : ℝ} (ht : 1 ≤ t) :
  Real.log t ≤ vbI σ t := by
 have ht0 : 0 < t := by linarith
 have hL : 0 ≤ Real.log t := Real.log_nonneg ht
 have hl : 0 ≤ Real.log (1 + (σ / t) ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg (σ / t)])
 unfold vbI
 apply (Real.le_sqrt (by positivity) (by positivity)).mpr
 nlinarith [sq_nonneg (Real.arctan (σ / t))]
lemma vkq {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
  (ht : 1 < t) : correction σ t ≤ 1 := by
 have hL : 0 < Real.log t := Real.log_pos ht
 have hD := vdF (σ := σ) ht.le
 have he : Real.exp (vay σ t) ≤ 1 :=
  Real.exp_le_one_iff.mpr (vgx hσ0 hσ1 (by linarith))
 unfold correction
 apply (div_le_one (hL.trans_le hD)).mpr
 exact (mul_le_of_le_one_left hL.le he).trans hD
lemma vcl {t : ℝ} (ht : 3 ≤ t) : 1 ≤ Real.log t := by
 have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3) ht
 linarith [Real.log_three_gt_d9]
lemma vkN {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
  (ht : 3 ≤ t) : vbI σ t ≤ Real.log t + 1 / t ^ 2 := by
 have ht0 : 0 < t := by linarith
 have hL := vcl ht
 have hd : 0 ≤ 1 / t ^ 2 := by positivity
 have hu2 : (σ / t) ^ 2 ≤ 1 / t ^ 2 := by
  rw [div_pow]
  exact div_le_div_of_nonneg_right (pow_le_one₀ hσ0 hσ1) (sq_nonneg t)
 have hl0 : 0 ≤ Real.log (1 + (σ / t) ^ 2) :=
  Real.log_nonneg (by nlinarith [sq_nonneg (σ / t)])
 have hl1 : Real.log (1 + (σ / t) ^ 2) ≤ 1 / t ^ 2 := by
  have h := Real.log_le_sub_one_of_pos
   (by positivity : (0 : ℝ) < 1 + (σ / t) ^ 2)
  linarith
 have ha0 : 0 ≤ Real.arctan (σ / t) := Real.arctan_nonneg.mpr (by positivity)
 have ha1 : Real.arctan (σ / t) ≤ 1 / t :=
  (Real.arctan_le_self (by positivity)).trans
   (div_le_div_of_nonneg_right hσ1 ht0.le)
 have ha2 : Real.arctan (σ / t) ^ 2 ≤ 1 / t ^ 2 := by
  have hsq : Real.arctan (σ / t) ^ 2 ≤ (1 / t) ^ 2 := by nlinarith
  simpa [-Complex.ofReal_arctan, div_pow] using hsq
 have hlsq : (Real.log t + Real.log (1 + (σ / t) ^ 2) / 2) ^ 2 ≤
   (Real.log t + (1 / t ^ 2) / 2) ^ 2 := by gcongr
 unfold vbI
 apply Real.sqrt_le_iff.mpr
 constructor
 ·linarith
 ·have hm := mul_nonneg (sub_nonneg.mpr hL) hd
  nlinarith
lemma vkS {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
  (ht : 3 ≤ t) : 1 - 4 / t ^ 2 ≤ correction σ t := by
 have ht0 : 0 < t := by linarith
 have hL := vcl ht
 have hD := vdF (σ := σ) (by linarith : 1 ≤ t)
 have hDpos : 0 < vbI σ t := by linarith
 have hd : 0 ≤ 1 / t ^ 2 := by positivity
 have hdsmall : 1 / t ^ 2 ≤ 1 / 9 := by
  apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 9)
  nlinarith
 have hcoef : 0 ≤ 1 - 4 / t ^ 2 := by
  rw [show 4 / t ^ 2 = 4 * (1 / t ^ 2) by ring]
  linarith
 have hDupper : vbI σ t ≤ Real.log t * (1 + 1 / t ^ 2) := by
  refine (vkN hσ0 hσ1 ht).trans ?_
  have hm := mul_nonneg (sub_nonneg.mpr hL) hd
  nlinarith
 have he : 1 - 1 / t ^ 2 ≤ Real.exp (vay σ t) := by
  have he0 := vhe hσ0 hσ1 ht0
  have he1 := Real.add_one_le_exp (vay σ t)
  linarith
 unfold correction
 apply (le_div_iff₀ hDpos).mpr
 calc
  _ ≤ (1 - 4 / t ^ 2) * (Real.log t * (1 + 1 / t ^ 2)) :=
   mul_le_mul_of_nonneg_left hDupper hcoef
  _ ≤ (1 - 1 / t ^ 2) * Real.log t := by
   have h1 := mul_nonneg (show 0 ≤ Real.log t by linarith) hd
   have h2 := mul_nonneg (show 0 ≤ Real.log t by linarith) (sq_nonneg (1 / t ^ 2))
   linear_combination 2 * h1 + 4 * h2
  _ ≤ Real.exp (vay σ t) * Real.log t :=
   mul_le_mul_of_nonneg_right he (by linarith)
lemma vjr {σ t : ℝ} (ht : 0 < t) :
  Real.log ‖(t : ℂ) - σ * I‖ =
   Real.log t + Real.log (1 + (σ / t) ^ 2) / 2 := by
 have hq : 0 < 1 + (σ / t) ^ 2 := by positivity
 have hn : ‖(t : ℂ) - σ * I‖ = t * Real.sqrt (1 + (σ / t) ^ 2) := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt hq.le, Complex.sq_norm, Complex.normSq_apply]
  simp [-Complex.ofReal_arctan]
  field_simp
 rw [hn, Real.log_mul ht.ne' (Real.sqrt_pos.mpr hq).ne', Real.log_sqrt hq.le]
lemma viq {σ t : ℝ} (ht : 0 < t) :
  Complex.log ((t : ℂ) - σ * I) =
   ((Real.log t + Real.log (1 + (σ / t) ^ 2) / 2 : ℝ) : ℂ) -
    (Real.arctan (σ / t) : ℂ) * I := by
 apply Complex.ext
 ·simpa [-Complex.ofReal_arctan, Complex.log_re] using vjr (σ := σ) ht
 ·rw [Complex.log_im, vhB (by simpa [-Complex.ofReal_arctan] using ht)]
  simp [-Complex.ofReal_arctan, neg_div, Real.arctan_neg]
lemma vjw {σ t : ℝ} (ht : 0 < t) :
  ‖Complex.log ((t : ℂ) - σ * I)‖ = vbI σ t := by
 rw [viq ht, Complex.norm_def]
 simp [-Complex.ofReal_arctan, vbI, Complex.normSq_apply, pow_two]
lemma vgN {s : ℂ} (hs : 1 < s.im) :
  AnalyticAt ℂ vaG s := by
 have ht : 0 < s.im := by linarith
 have hp : s ≠ 1 := by
  intro he
  have hh := congrArg Complex.im he
  simp [-Complex.ofReal_arctan] at hh
  linarith
 have hw : -s * I ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  left
  simpa [-Complex.ofReal_arctan] using ht
 have hw' : -s * I / (2 * Real.pi) ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  left
  rw [show (2 : ℂ) * Real.pi = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
   Complex.div_ofReal_re]
  simpa [-Complex.ofReal_arctan] using div_pos ht (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)
 have hnorm : 1 < ‖-s * I‖ := by
  have h := Complex.re_le_norm (-s * I)
  have hr : (-s * I).re = s.im := by simp [-Complex.ofReal_arctan]
  rw [hr] at h
  linarith
 have hn : Complex.log (-s * I) ≠ 0 := by
  intro he
  have h := congrArg Complex.re he
  rw [Complex.log_re, Complex.zero_re] at h
  have hp := Real.log_pos hnorm
  linarith
 have hd : AnalyticAt ℂ (fun z : ℂ => Complex.log (-z * I)) s :=
  (analyticAt_id.neg.mul analyticAt_const).clog hw
 have hc : AnalyticAt ℂ (fun z : ℂ => Complex.log (-z * I / (2 * Real.pi))) s :=
  ((analyticAt_id.neg.mul analyticAt_const).div_const).clog hw'
 have he : AnalyticAt ℂ exponent s := by
  unfold exponent
  exact (((analyticAt_id.sub analyticAt_const).div_const).mul hc).sub
   analyticAt_id.div_const
 have hz : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s (by simpa [-Complex.ofReal_arctan] using hp)
 exact (hz.mul he.cexp).div hd hn
lemma vif {σ t : ℝ} (ht : 0 < t) :
  (exponent ((σ : ℂ) + t * I)).re =
   (σ - 1) / 2 * Real.log (t / (2 * Real.pi)) + vay σ t := by
 have hp : 0 < 2 * Real.pi := by positivity
 have hw : (t : ℂ) - σ * I ≠ 0 := by
  intro h
  have hh := congrArg Complex.re h
  simp [-Complex.ofReal_arctan] at hh
  exact ht.ne' hh
 have hrot : -((σ : ℂ) + t * I) * I = (t : ℂ) - σ * I := by
  ring_nf
  simp [-Complex.ofReal_arctan]
 have hdiv : ((t : ℂ) - σ * I) / (2 * Real.pi) =
   ((t : ℂ) - σ * I) * (((2 * Real.pi)⁻¹ : ℝ) : ℂ) := by
  push_cast
  rfl
 have hl : Complex.log (((t : ℂ) - σ * I) / (2 * Real.pi)) =
   -(Real.log (2 * Real.pi) : ℂ) +
   ((Real.log t + Real.log (1 + (σ / t) ^ 2) / 2 : ℝ) : ℂ) -
    (Real.arctan (σ / t) : ℂ) * I := by
  rw [hdiv, Complex.log_mul_ofReal _ (inv_pos.mpr hp) _ hw,
   Real.log_inv, viq ht]
  push_cast
  ring
 unfold exponent
 rw [hrot, hl, Real.log_div ht.ne' hp.ne']
 simp [-Complex.ofReal_arctan, vay, Complex.mul_re, Complex.mul_im, div_ofNat_re, div_ofNat_im]
 ring
lemma vcj {σ t : ℝ} (ht : 1 < t) :
  ‖vaG ((σ : ℂ) + t * I)‖ =
   (t / (2 * Real.pi)) ^ ((σ - 1) / 2) *
    ‖riemannZeta ((σ : ℂ) + t * I)‖ / Real.log t * correction σ t := by
 have ht0 : 0 < t := by linarith
 have hp : 0 < t / (2 * Real.pi) := by positivity
 have hlog : Real.log t ≠ 0 := (Real.log_pos ht).ne'
 have hD : vbI σ t ≠ 0 := ne_of_gt
  ((Real.log_pos ht).trans_le (vdF ht.le))
 have hrot : -((σ : ℂ) + t * I) * I = (t : ℂ) - σ * I := by
  ring_nf
  simp [-Complex.ofReal_arctan]
 rw [vaG, norm_div, norm_mul, Complex.norm_exp,
  vif ht0, Real.exp_add, hrot, vjw ht0]
 rw [Real.rpow_def_of_pos hp]
 unfold correction
 field_simp
lemma veO {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
  (ht : 3 ≤ t) (hφ : ‖vaG ((σ : ℂ) + t * I)‖ ≤ 1) :
  ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤
   t ^ 2 / (t ^ 2 - 4) * (t / (2 * Real.pi)) ^ ((1 - σ) / 2) * Real.log t := by
 have ht0 : 0 < t := by linarith
 have ht2 : 0 < t ^ 2 - 4 := by nlinarith
 have hp : 0 < t / (2 * Real.pi) := by positivity
 have hL : 0 < Real.log t := Real.log_pos (by linarith)
 have hA : 0 < (t / (2 * Real.pi)) ^ ((σ - 1) / 2) := Real.rpow_pos_of_pos hp _
 have hq0 : 0 < 1 - 4 / t ^ 2 := by
  apply sub_pos.mpr
  apply (div_lt_one (sq_pos_of_pos ht0)).mpr
  nlinarith
 have hq := vkS hσ0 hσ1 ht
 rw [vcj (by linarith : 1 < t)] at hφ
 have hprod : (t / (2 * Real.pi)) ^ ((σ - 1) / 2) *
   ‖riemannZeta ((σ : ℂ) + t * I)‖ / Real.log t * (1 - 4 / t ^ 2) ≤ 1 :=
  (mul_le_mul_of_nonneg_left hq (by positivity)).trans hφ
 have hab : (t / (2 * Real.pi)) ^ ((σ - 1) / 2) *
   (t / (2 * Real.pi)) ^ ((1 - σ) / 2) = 1 := by
  rw [← Real.rpow_add hp, show (σ - 1) / 2 + (1 - σ) / 2 = 0 by ring,
   Real.rpow_zero]
 have htarget : (t / (2 * Real.pi)) ^ ((σ - 1) / 2) *
   (t ^ 2 / (t ^ 2 - 4) * (t / (2 * Real.pi)) ^ ((1 - σ) / 2) * Real.log t) /
    Real.log t * (1 - 4 / t ^ 2) = 1 := by
  have he : 1 - 4 / t ^ 2 = (t ^ 2 - 4) / t ^ 2 := by field_simp
  rw [he]
  field_simp
  nlinarith [hab]
 have hm : 0 < (t / (2 * Real.pi)) ^ ((σ - 1) / 2) / Real.log t *
   (1 - 4 / t ^ 2) := by positivity
 apply (mul_le_mul_iff_right₀ hm).mp
 convert hprod.trans_eq htarget.symm using 1 <;> (try ring)
 all_goals try rfl
end vaa.vab.vdx
end
section
open Complex Real Finset
namespace vaa.vab.vaD
open vaa.vcP.vkl
def vkn : ℕ → ℕ
 | 0 => 0
 | n + 1 => if n = 0 then 0 else vkn n + vjS n
def vkm : ℕ → ℕ
 | 0 => 0
 | n + 1 => if n = 0 then 0 else vkm n + vir n
lemma viZ (n : ℕ) (hn : 1 ≤ n) :
  (vkn n : ℝ) ≤ 10 ^ 30 * Real.log n ∧
   10 ^ 30 * Real.log n ≤ (vkm n : ℝ) := by
 induction n with
 | zero => omega
 | succ n ih =>
  by_cases hn0 : n = 0
  ·subst n
   simp [vkn, vkm]
  ·have hn1 : 1 ≤ n := by omega
   obtain ⟨hl, hu⟩ := ih hn1
   obtain ⟨hil, hiu⟩ := vkL hn1
   have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
   have hlog : Real.log (n + 1 : ℕ) = Real.log n + Real.log (1 + (n : ℝ)⁻¹) := by
    rw [← Real.log_mul hnR.ne' (by positivity)]
    congr 1
    push_cast
    field_simp
   simp only [Nat.cast_add, Nat.cast_one] at hlog
   simp only [vkn, vkm, if_neg hn0, Nat.cast_add, Nat.cast_one]
   rw [hlog]
   constructor <;> linarith
def piLo : ℚ := 314159265358979323846 / 10 ^ 20
def piHi : ℚ := 314159265358979323847 / 10 ^ 20
def viO (n m : ℕ) (q : ℚ) : Bool := decide
 (-(1 / 100000 : ℚ) ≤ 50 * (vkn n : ℚ) / 10 ^ 30 - q - m * piHi / 2 ∧
  50 * (vkm n : ℚ) / 10 ^ 30 - q - m * piLo / 2 ≤ 1 / 100000)
lemma vll {n m : ℕ} {q : ℚ} (hn : 1 ≤ n)
  (hc : viO n m q = true) :
  |50 * Real.log n - ((q : ℝ) + m * Real.pi / 2)| ≤ 1 / 100000 := by
 have hc' : -(1 / 100000 : ℚ) ≤ 50 * (vkn n : ℚ) / 10 ^ 30 - q - m * piHi / 2 ∧
   50 * (vkm n : ℚ) / 10 ^ 30 - q - m * piLo / 2 ≤ 1 / 100000 :=
  of_decide_eq_true hc
 have hlo := Rat.cast_mono (K := ℝ) hc'.1
 have hhi := Rat.cast_mono (K := ℝ) hc'.2
 push_cast at hlo hhi
 obtain ⟨hl, hu⟩ := viZ n hn
 have hpiL : (piLo : ℝ) ≤ Real.pi := by
  norm_num [piLo]
  linarith [Real.pi_gt_d20]
 have hpiU : Real.pi ≤ (piHi : ℝ) := by
  norm_num [piHi]
  linarith [Real.pi_lt_d20]
 have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
 have hml := mul_le_mul_of_nonneg_left hpiL hm0
 have hmu := mul_le_mul_of_nonneg_left hpiU hm0
 rw [abs_le]
 constructor <;> linarith
noncomputable def taylor (x : ℝ) : ℂ :=
 ∑ k ∈ Finset.range 8, ((x : ℂ) * I) ^ k / k.factorial
def cosPoly (x : ℚ) : ℚ := 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720
def sinPoly (x : ℚ) : ℚ := x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040
lemma vop (q : ℚ) :
  taylor (q : ℝ) = (cosPoly q : ℂ) + (sinPoly q : ℂ) * I := by
 unfold taylor cosPoly sinPoly
 simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
 push_cast
 ring_nf
 simp
 ring
lemma vkX {x : ℝ} (hx : |x| ≤ 1) :
  ‖Complex.exp ((x : ℂ) * I) - taylor x‖ ≤ 1 / 30000 := by
 have hnorm : ‖(x : ℂ) * I‖ ≤ 1 := by simpa using hx
 have h := Complex.exp_bound hnorm (by norm_num : (0 : ℕ) < 8)
 have hp : |x| ^ 8 ≤ 1 := pow_le_one₀ (abs_nonneg _) hx
 norm_num [Nat.factorial] at h
 unfold taylor
 nlinarith
def vdg (q : ℚ) (m : ℕ) : ℚ :=
 if m % 4 = 0 then cosPoly q else if m % 4 = 1 then -sinPoly q
 else if m % 4 = 2 then -cosPoly q else sinPoly q
def vdh (q : ℚ) (m : ℕ) : ℚ :=
 if m % 4 = 0 then sinPoly q else if m % 4 = 1 then cosPoly q
 else if m % 4 = 2 then -sinPoly q else -cosPoly q
lemma vkO (q : ℚ) (m : ℕ) :
  taylor (q : ℝ) * I ^ m = (vdg q m : ℂ) + (vdh q m : ℂ) * I := by
 rw [vop, Complex.I_pow_eq_pow_mod]
 have hm : m % 4 < 4 := Nat.mod_lt m (by decide)
 interval_cases h : m % 4 <;> simp [vdg, vdh, h] <;> ring_nf <;> simp <;> ring
lemma vjd {q : ℚ} (hq : |(q : ℝ)| ≤ 1) (m : ℕ) :
  ‖Complex.exp (((q : ℝ) + m * Real.pi / 2 : ℝ) * I) -
   ((vdg q m : ℂ) + (vdh q m : ℂ) * I)‖ ≤ 1 / 30000 := by
 rw [← vkO]
 have he : Complex.exp (((q : ℝ) + m * Real.pi / 2 : ℝ) * I) =
   Complex.exp ((q : ℂ) * I) * I ^ m := by
  push_cast
  rw [show ((q : ℂ) + m * Real.pi / 2) * I =
   (q : ℂ) * I + (m : ℂ) * (Real.pi / 2 * I) by ring,
   Complex.exp_add, Complex.exp_nat_mul, Complex.exp_pi_div_two_mul_I]
 rw [he, ← sub_mul, norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one]
 exact vkX hq
lemma vnG {n m : ℕ} {q : ℚ} (hn : 1 ≤ n)
  (hc : viO n m q = true) (hq : |(q : ℝ)| ≤ 1) :
  |Real.cos (50 * Real.log n) - (vdg q m : ℝ)| ≤ 1 / 10000 ∧
   |Real.sin (50 * Real.log n) - (vdh q m : ℝ)| ≤ 1 / 10000 := by
 have ha := vll hn hc
 have ht := vjd hq m
 have hr := (Complex.abs_re_le_norm _).trans ht
 have hi := (Complex.abs_im_le_norm _).trans ht
 simp only [Complex.sub_re, Complex.add_re, Complex.mul_I_re, Complex.ratCast_re,
  Complex.ratCast_im, neg_zero, add_zero, Complex.exp_ofReal_mul_I_re] at hr
 simp only [Complex.sub_im, Complex.add_im, Complex.mul_I_im, Complex.ratCast_re,
  Complex.ratCast_im, zero_add, Complex.exp_ofReal_mul_I_im] at hi
 have hcr := (Real.abs_cos_sub_cos_le (50 * Real.log n)
  ((q : ℝ) + m * Real.pi / 2)).trans ha
 have hsi := (Real.abs_sin_sub_sin_le (50 * Real.log n)
  ((q : ℝ) + m * Real.pi / 2)).trans ha
 constructor
 ·have h := abs_add_le (Real.cos (50 * Real.log n) -
   Real.cos ((q : ℝ) + m * Real.pi / 2))
   (Real.cos ((q : ℝ) + m * Real.pi / 2) - (vdg q m : ℝ))
  rw [sub_add_sub_cancel] at h
  linarith
 ·have h := abs_add_le (Real.sin (50 * Real.log n) -
   Real.sin ((q : ℝ) + m * Real.pi / 2))
   (Real.sin ((q : ℝ) + m * Real.pi / 2) - (vdh q m : ℝ))
  rw [sub_add_sub_cancel] at h
  linarith
end vaa.vab.vaD
end
section
namespace vaa.vab.vaD
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
def vaQ : ℕ → ℕ
 | 1 => 0
 | 2 => 22
 | 3 => 35
 | 4 => 44
 | 5 => 51
 | 6 => 57
 | 7 => 62
 | 8 => 66
 | 9 => 70
 | 10 => 73
 | 11 => 76
 | 12 => 79
 | 13 => 82
 | 14 => 84
 | 15 => 86
 | 16 => 88
 | 17 => 90
 | 18 => 92
 | 19 => 94
 | 20 => 95
 | _ => 0
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
def vaI : ℕ → ℚ
 | 1 => 0
 | 2 => (312 / 3125)
 | 3 => (-47257 / 1000000)
 | 4 => (624 / 3125)
 | 5 => (361283 / 1000000)
 | 6 => (52583 / 1000000)
 | 7 => (-18773 / 200000)
 | 8 => (936 / 3125)
 | 9 => (-47257 / 500000)
 | 10 => (461123 / 1000000)
 | 11 => (514243 / 1000000)
 | 12 => (152423 / 1000000)
 | 13 => (-557831 / 1000000)
 | 14 => (239 / 40000)
 | 15 => (157013 / 500000)
 | 16 => (399359 / 1000000)
 | 17 => (144499 / 500000)
 | 18 => (2663 / 500000)
 | 19 => (-216453 / 500000)
 | 20 => (560963 / 1000000)
 | _ => 0
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
def vci : ℕ → ℕ
 | 1 => 1000000
 | 2 => 707107
 | 3 => 577351
 | 4 => 500000
 | 5 => 447214
 | 6 => 408249
 | 7 => 377965
 | 8 => 353554
 | 9 => 333334
 | 10 => 316228
 | 11 => 301512
 | 12 => 288676
 | 13 => 277351
 | 14 => 267262
 | 15 => 258199
 | 16 => 250000
 | 17 => 242536
 | 18 => 235703
 | 19 => 229416
 | 20 => 223607
 | _ => 0
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
def viJ (n : ℕ) : Bool :=
 viO n (vaQ n) (vaI n) &&
  decide (|vaI n| ≤ 1 ∧ 10 ^ 12 ≤ (vci n) ^ 2 * n)
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma vkR : (List.range' 1 20).all viJ = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
def vcS (n : ℕ) : ℚ := 1 / n
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
def vcm (n : ℕ) : ℚ := (vci n : ℚ) / 10 ^ 6
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
def vjO (n : ℕ) : ℚ := min
 (vcS n * (vdg (vaI n) (vaQ n) - 1 / 10000))
 (vcm n * (vdg (vaI n) (vaQ n) - 1 / 10000))
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
def vkd (n : ℕ) : ℚ := max
 (vcS n * (vdg (vaI n) (vaQ n) + 1 / 10000))
 (vcm n * (vdg (vaI n) (vaQ n) + 1 / 10000))
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
def vjJ (n : ℕ) : ℚ := min
 (vcS n * (vdh (vaI n) (vaQ n) - 1 / 10000))
 (vcm n * (vdh (vaI n) (vaQ n) - 1 / 10000))
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
def vjQ (n : ℕ) : ℚ := max
 (vcS n * (vdh (vaI n) (vaQ n) + 1 / 10000))
 (vcm n * (vdh (vaI n) (vaQ n) + 1 / 10000))
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
def weight (n : ℕ) : ℚ := if n = 20 then 1 / 2 else 1
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma vcq :
  -(127 / 100 : ℚ) ≤ ∑ n ∈ Finset.Icc 1 20, weight n * vjO n ∧
  (∑ n ∈ Finset.Icc 1 20, weight n * vkd n) ≤ 159 / 100 ∧
  -(125 / 100 : ℚ) ≤ ∑ n ∈ Finset.Icc 1 20, weight n * vjJ n ∧
  (∑ n ∈ Finset.Icc 1 20, weight n * vjQ n) ≤ 125 / 100 := by decide +kernel
end vaa.vab.vaD
end
section
open Complex Real Finset
namespace vaa.vab.vaD
lemma vkK {n : ℕ} (hn : n ∈ Finset.Icc 1 20) : viJ n = true := by
 obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
 have hm : n ∈ List.range' 1 20 := by
  rw [List.mem_range']
  exact ⟨n - 1, by omega, by omega⟩
 exact List.all_eq_true.mp vkR n hm
lemma vhd {n : ℕ} (hn : n ∈ Finset.Icc 1 20)
  {σ : ℝ} (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
  (vcS n : ℝ) ≤ (n : ℝ) ^ (-σ) ∧
   (n : ℝ) ^ (-σ) ≤ (vcm n : ℝ) := by
 have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
 have hn0 : 0 < n := by omega
 have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
 have hc := vkK hn
 simp only [viJ, Bool.and_eq_true, decide_eq_true_eq] at hc
 have hc' := hc.2
 have hu := vbg.vex (n := n) (p := 1) (k := 2)
  (D := 10 ^ 6) (b := vci n) hn0 (by norm_num) (by norm_num)
  (by norm_num; exact hc'.2)
 constructor
 ·have hh := Real.rpow_le_rpow_of_exponent_le hnR (show (-1 : ℝ) ≤ -σ by linarith)
  simpa [vcS, Real.rpow_neg_one, one_div] using hh
 ·have hh := Real.rpow_le_rpow_of_exponent_le hnR (show -σ ≤ -(1 / 2 : ℝ) by linarith)
  apply hh.trans
  norm_num [vcm] at hu ⊢
  exact hu
lemma vdy {A B C D x y : ℝ}
  (hx0 : 0 ≤ x) (hxl : A ≤ x) (hxu : x ≤ B) (hyl : C ≤ y) (hyu : y ≤ D) :
  min (A * C) (B * C) ≤ x * y ∧ x * y ≤ max (A * D) (B * D) := by
 constructor
 ·apply le_trans _ (mul_le_mul_of_nonneg_left hyl hx0)
  by_cases hC : 0 ≤ C
  ·exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hxl hC)
  ·exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right hxu (le_of_not_ge hC))
 ·apply le_trans (mul_le_mul_of_nonneg_left hyu hx0)
  by_cases hD : 0 ≤ D
  ·exact (mul_le_mul_of_nonneg_right hxu hD).trans (le_max_right _ _)
  ·exact (mul_le_mul_of_nonpos_right hxl (le_of_not_ge hD)).trans (le_max_left _ _)
lemma vkQ {n : ℕ} (hn : 1 ≤ n) (σ : ℝ) :
  ((n : ℂ) ^ (-((σ : ℂ) + 50 * I))).re =
   (n : ℝ) ^ (-σ) * Real.cos (50 * Real.log n) ∧
  ((n : ℂ) ^ (-((σ : ℂ) + 50 * I))).im =
   -((n : ℝ) ^ (-σ) * Real.sin (50 * Real.log n)) := by
 have hn0 : 0 < n := by omega
 have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
 have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
 have hl : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
  simpa using (Complex.ofReal_log hnR.le).symm
 have he : Complex.log (n : ℂ) * (-((σ : ℂ) + 50 * I)) =
   ((-σ * Real.log n : ℝ) : ℂ) + ((-(50 * Real.log n) : ℝ) : ℂ) * I := by
  rw [hl]
  push_cast
  ring
 have hp : (n : ℂ) ^ (-((σ : ℂ) + 50 * I)) =
   Complex.exp (((-σ * Real.log n : ℝ) : ℂ) + ((-(50 * Real.log n) : ℝ) : ℂ) * I) := by
  rw [Complex.cpow_def_of_ne_zero hnC, he]
 have hlr : (Complex.log (n : ℂ)).re = Real.log n := by rw [hl]; rfl
 have hli : (Complex.log (n : ℂ)).im = 0 := by rw [hl]; rfl
 constructor <;> rw [hp] <;>
  simp [Complex.exp_re, Complex.exp_im, Real.rpow_def_of_pos hnR, hlr, hli, mul_comm]
lemma vdu {n : ℕ} (hn : n ∈ Finset.Icc 1 20)
  {σ : ℝ} (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
  (vjO n : ℝ) ≤ ((n : ℂ) ^ (-((σ : ℂ) + 50 * I))).re ∧
   ((n : ℂ) ^ (-((σ : ℂ) + 50 * I))).re ≤ (vkd n : ℝ) ∧
  (vjJ n : ℝ) ≤ -((n : ℂ) ^ (-((σ : ℂ) + 50 * I))).im ∧
   -((n : ℂ) ^ (-((σ : ℂ) + 50 * I))).im ≤ (vjQ n : ℝ) := by
 have hn1 := (Finset.mem_Icc.mp hn).1
 have hc := vkK hn
 simp only [viJ, Bool.and_eq_true, decide_eq_true_eq] at hc
 have hq : |(vaI n : ℝ)| ≤ 1 := by
  exact_mod_cast hc.2.1
 obtain ⟨hcos, hsin⟩ := vnG hn1 hc.1 hq
 rw [abs_le] at hcos hsin
 obtain ⟨ha, hb⟩ := vhd hn hσ0 hσ1
 have hnn := Real.rpow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (-σ)
 have hR := vdy hnn ha hb
  (show (vdg (vaI n) (vaQ n) : ℝ) - 1 / 10000 ≤
   Real.cos (50 * Real.log n) by linarith)
  (show Real.cos (50 * Real.log n) ≤
   (vdg (vaI n) (vaQ n) : ℝ) + 1 / 10000 by linarith)
 have hI := vdy hnn ha hb
  (show (vdh (vaI n) (vaQ n) : ℝ) - 1 / 10000 ≤
   Real.sin (50 * Real.log n) by linarith)
  (show Real.sin (50 * Real.log n) ≤
   (vdh (vaI n) (vaQ n) : ℝ) + 1 / 10000 by linarith)
 obtain ⟨hr, hi⟩ := vkQ hn1 σ
 rw [hr, hi, neg_neg]
 exact ⟨by simpa [vjO] using hR.1, by simpa [vkd] using hR.2,
  by simpa [vjJ] using hI.1, by simpa [vjQ] using hI.2⟩
noncomputable def vap (σ : ℝ) : ℂ :=
 ∑ n ∈ Finset.Icc 1 20, (weight n : ℂ) * (n : ℂ) ^ (-((σ : ℂ) + 50 * I))
lemma viR {σ : ℝ} (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
  -(127 / 100 : ℝ) ≤ (vap σ).re ∧ (vap σ).re ≤ 159 / 100 ∧
   -(125 / 100 : ℝ) ≤ -(vap σ).im ∧ -(vap σ).im ≤ 125 / 100 := by
 have hw (n : ℕ) : 0 ≤ (weight n : ℝ) := by unfold weight; split_ifs <;> norm_num
 have h1 : (∑ n ∈ Finset.Icc 1 20, (weight n : ℝ) * (vjO n : ℝ)) ≤ (vap σ).re := by
  simp only [vap, Complex.re_sum, Complex.mul_re, Complex.ratCast_re,
   Complex.ratCast_im, zero_mul, sub_zero]
  exact Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left
   (vdu hn hσ0 hσ1).1 (hw n)
 have h2 : (vap σ).re ≤ ∑ n ∈ Finset.Icc 1 20, (weight n : ℝ) * (vkd n : ℝ) := by
  simp only [vap, Complex.re_sum, Complex.mul_re, Complex.ratCast_re,
   Complex.ratCast_im, zero_mul, sub_zero]
  exact Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left
   (vdu hn hσ0 hσ1).2.1 (hw n)
 have h3 : (∑ n ∈ Finset.Icc 1 20, (weight n : ℝ) * (vjJ n : ℝ)) ≤ -(vap σ).im := by
  simp only [vap, Complex.im_sum, Complex.mul_im, Complex.ratCast_re,
   Complex.ratCast_im, zero_mul, add_zero, ← Finset.sum_neg_distrib, ← mul_neg]
  exact Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left
   (vdu hn hσ0 hσ1).2.2.1 (hw n)
 have h4 : -(vap σ).im ≤ ∑ n ∈ Finset.Icc 1 20, (weight n : ℝ) * (vjQ n : ℝ) := by
  simp only [vap, Complex.im_sum, Complex.mul_im, Complex.ratCast_re,
   Complex.ratCast_im, zero_mul, add_zero, ← Finset.sum_neg_distrib, ← mul_neg]
  exact Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left
   (vdu hn hσ0 hσ1).2.2.2 (hw n)
 have ha : -(127 / 100 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 20, (weight n : ℝ) * (vjO n : ℝ) := by
  have hh := Rat.cast_mono (K := ℝ) vcq.1
  push_cast at hh
  exact hh
 have hb : (∑ n ∈ Finset.Icc 1 20, (weight n : ℝ) * (vkd n : ℝ)) ≤ 159 / 100 := by
  have hh := Rat.cast_mono (K := ℝ) vcq.2.1
  push_cast at hh
  exact hh
 have hc : -(125 / 100 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 20, (weight n : ℝ) * (vjJ n : ℝ) := by
  have hh := Rat.cast_mono (K := ℝ) vcq.2.2.1
  push_cast at hh
  exact hh
 have hd : (∑ n ∈ Finset.Icc 1 20, (weight n : ℝ) * (vjQ n : ℝ)) ≤ 125 / 100 := by
  have hh := Rat.cast_mono (K := ℝ) vcq.2.2.2
  push_cast at hh
  exact hh
 exact ⟨ha.trans h1, h2.trans hb, hc.trans h3, h4.trans hd⟩
lemma vkh {σ : ℝ} (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
  ‖vap σ‖ ≤ 2.03 := by
 obtain ⟨hlr, hur, hli, hui⟩ := viR hσ0 hσ1
 have hr : (vap σ).re ^ 2 ≤ (1.59 : ℝ) ^ 2 := by nlinarith
 have hi : (vap σ).im ^ 2 ≤ (1.25 : ℝ) ^ 2 := by nlinarith
 have hn := Complex.sq_norm_sub_sq_im (vap σ)
 nlinarith [norm_nonneg (vap σ)]
lemma vmB (σ : ℝ) :
  vap σ = (∑ n ∈ Finset.range 20, (n : ℂ) ^ (-((σ : ℂ) + 50 * I))) +
   (20 : ℂ) ^ (-((σ : ℂ) + 50 * I)) / 2 := by
 have hs0 : -((σ : ℂ) + 50 * I) ≠ 0 := by
  intro he
  have hh := congrArg Complex.im he
  norm_num at hh
 have hsets : Finset.Icc (1 : ℕ) 20 = insert 20 (Finset.Icc 1 19) := by ext n; simp; omega
 have hsets' : Finset.Icc (1 : ℕ) 19 = Finset.Ico 1 20 := by ext n; simp; omega
 have hsum : (∑ n ∈ Finset.Icc 1 19, (weight n : ℂ) *
   (n : ℂ) ^ (-((σ : ℂ) + 50 * I))) =
   ∑ n ∈ Finset.Icc (1 : ℕ) 19, (n : ℂ) ^ (-((σ : ℂ) + 50 * I)) := by
  apply Finset.sum_congr rfl
  intro n hn
  have hn20 : n ≠ 20 := by have := (Finset.mem_Icc.mp hn).2; omega
  simp [weight, hn20]
 rw [vap, hsets, Finset.sum_insert (by decide), hsum, hsets',
  Finset.sum_Ico_eq_sub _ (by decide)]
 simp only [Finset.sum_range_one, Nat.cast_zero, Complex.zero_cpow hs0, sub_zero]
 norm_num [weight, Finset.sum_range_one, hs0]
 ring
lemma vkD {σ : ℝ} (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
  ‖riemannZeta ((σ : ℂ) + 50 * I)‖ ≤ 3.75 := by
 let s : ℂ := (σ : ℂ) + 50 * I
 have hsr : s.re = σ := by simp [s]
 have hsi : s.im = 50 := by simp [s]
 have hs0 : 0 < s.re := by rw [hsr]; linarith
 have hs1 : s ≠ 1 := by intro he; have := congrArg Complex.im he; simp [hsi] at this
 have hn1 : ‖s‖ ≤ 50.01 := by
  have hh := Complex.sq_norm_sub_sq_im s
  rw [hsr, hsi] at hh
  nlinarith [norm_nonneg s]
 have hn2 : ‖s + 1‖ ≤ 50.04 := by
  have hh := Complex.sq_norm_sub_sq_im (s + 1)
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
   hsr, hsi, add_zero] at hh
  nlinarith [norm_nonneg (s + 1)]
 have hp : ‖s * (s + 1)‖ ≤ 50.01 * 50.04 := by
  rw [norm_mul]
  exact mul_le_mul hn1 hn2 (norm_nonneg _) (by norm_num)
 have ha : (20 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 0.223607 := by
  have hh := (vhd (n := 20) (by decide)
   (σ := 1 / 2) (by norm_num) (by norm_num)).2
  norm_num [vcm, vci] at hh ⊢
  exact hh
 have hpow : (20 : ℝ) ^ (-σ - 1) ≤ 0.01118035 := by
  have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 20)
   (show -σ - 1 ≤ -(1 / 2 : ℝ) + -1 by linarith)
  rw [Real.rpow_add (by norm_num), Real.rpow_neg_one] at hh
  nlinarith
 have hmainpow : (20 : ℝ) ^ (1 - σ) ≤ 4.473 := by
  have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 20)
   (show 1 - σ ≤ (1 / 2 : ℝ) by linarith)
  rw [← Real.sqrt_eq_rpow] at hh
  exact hh.trans ((Real.sqrt_le_left (by norm_num)).mpr (by norm_num))
 have hd : (50 : ℝ) ≤ ‖s - 1‖ := by
  simpa [hsi] using Complex.abs_im_le_norm (s - 1)
 let a : ℂ := (20 : ℂ) ^ (1 - s) / (s - 1)
 let b : ℂ := s * (20 : ℂ) ^ (-s - 1) / 12
 have hpowNorm (z : ℂ) : ‖(20 : ℂ) ^ z‖ = (20 : ℝ) ^ z.re := by
  simpa using Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 20) z
 have hna : ‖a‖ ≤ 0.08946 := by
  have he : ‖a‖ = (20 : ℝ) ^ (1 - σ) / ‖s - 1‖ := by
   simp [a, norm_div, hpowNorm, hsr]
  rw [he]
  apply (div_le_iff₀ (by linarith : 0 < ‖s - 1‖)).mpr
  nlinarith
 have hnb : ‖b‖ ≤ 0.047 := by
  have he : ‖b‖ = ‖s‖ * (20 : ℝ) ^ (-σ - 1) / 12 := by
   simp [b, norm_div, norm_mul, hpowNorm, hsr]
  rw [he]
  have hh := mul_le_mul hn1 hpow
   (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 20) _) (by norm_num)
  linarith
 have hcoef : ‖s * (s + 1)‖ / (12 * (σ + 1)) ≤ (50.01 * 50.04 : ℝ) / 18 := by
  apply (div_le_div_iff₀ (by linarith : 0 < 12 * (σ + 1)) (by norm_num)).mpr
  nlinarith
 have htail : ‖s * (s + 1)‖ / (12 * (σ + 1)) * (20 : ℝ) ^ (-σ - 1) ≤ 1.555 := by
  calc
   _ ≤ ((50.01 * 50.04 : ℝ) / 18) * 0.01118035 := mul_le_mul hcoef hpow
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 20) _) (by norm_num)
   _ ≤ _ := by norm_num
 let R : ℂ := riemannZeta s - vap σ - a - b
 have hR : ‖R‖ ≤ 1.555 := by
  have hh := vaT.vbr
   hs0 hs1 (N := 20) (by decide)
  norm_num only [Nat.cast_ofNat] at hh
  rw [hsr] at hh
  have he : riemannZeta s - (∑ k ∈ Finset.range 20, (k : ℂ) ^ (-s)) -
    (20 : ℂ) ^ (-s) / 2 - (20 : ℂ) ^ (1 - s) / (s - 1) -
    s * (20 : ℂ) ^ (-s - 1) / 12 = R := by
   dsimp [R, a, b]
   rw [vmB]
   dsimp [s]
   ring
  rw [he] at hh
  exact hh.trans htail
 have hH := vkh hσ0 hσ1
 have htri : ‖riemannZeta s‖ ≤ ‖vap σ‖ + ‖a‖ + ‖b‖ + ‖R‖ := by
  calc
   _ = ‖vap σ + a + b + R‖ := by congr 1; dsimp [R]; ring
   _ ≤ ‖vap σ + a + b‖ + ‖R‖ := norm_add_le _ _
   _ ≤ ‖vap σ + a‖ + ‖b‖ + ‖R‖ := by gcongr; exact norm_add_le _ _
   _ ≤ ‖vap σ‖ + ‖a‖ + ‖b‖ + ‖R‖ := by gcongr; exact norm_add_le _ _
 change ‖riemannZeta s‖ ≤ 3.75
 linarith
lemma vcZ {σ : ℝ} (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
  ‖riemannZeta ((σ : ℂ) + (50 : ℂ) * I)‖ ≤ 3.75 :=
 vkD hσ0 hσ1
end vaa.vab.vaD
end
section
open Complex Real Set
open scoped Topology
namespace vaa.vab.vjj
open vdx
private lemma vkH {t : ℝ} (ht : 50 ≤ t) : 1 ≤ t / (2 * Real.pi) := by
 rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
 linarith [Real.pi_lt_four]
private lemma vkG {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
  (ht : 50 ≤ t) :
  ‖vaG ((σ : ℂ) + t * I)‖ ≤
   (t / (2 * Real.pi)) ^ ((σ - 1) / 2) *
    ‖riemannZeta ((σ : ℂ) + t * I)‖ / Real.log t := by
 rw [vcj (by linarith : 1 < t)]
 have hL : 0 < Real.log t := Real.log_pos (by linarith)
 exact mul_le_of_le_one_right (by positivity)
  (vkq hσ0 hσ1 (by linarith))
private lemma vcL {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
  (ht : 50 ≤ t) :
  ‖vaG ((σ : ℂ) + t * I)‖ ≤
   ‖riemannZeta ((σ : ℂ) + t * I)‖ / Real.log t := by
 have hL : 0 < Real.log t := Real.log_pos (by linarith)
 have hP : (t / (2 * Real.pi)) ^ ((σ - 1) / 2) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (vkH ht) (by linarith)
 exact (vkG hσ0 hσ1 ht).trans
  (div_le_div_of_nonneg_right (mul_le_of_le_one_left (norm_nonneg _) hP) hL.le)
private lemma vdH {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1 / 2)
  (ht : 50 ≤ t) :
  ‖vaG ((σ : ℂ) + t * I)‖ ≤ Real.exp (5 / (2 * t ^ 2)) *
   ‖riemannZeta (((1 - σ : ℝ) : ℂ) + t * I)‖ / Real.log t := by
 have hL : 0 < Real.log t := Real.log_pos (by linarith)
 have hp : 0 < t / (2 * Real.pi) := by positivity
 have hP : (t / (2 * Real.pi)) ^ (-σ / 2) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (vkH ht) (by linarith)
 have hab : (t / (2 * Real.pi)) ^ ((σ - 1) / 2) *
   (t / (2 * Real.pi)) ^ (1 / 2 - σ) = (t / (2 * Real.pi)) ^ (-σ / 2) := by
  rw [← Real.rpow_add hp]
  congr 1
  ring
 calc
  _ ≤ (t / (2 * Real.pi)) ^ ((σ - 1) / 2) *
   ‖riemannZeta ((σ : ℂ) + t * I)‖ / Real.log t :=
    vkG hσ0 (by linarith) ht
  _ ≤ (t / (2 * Real.pi)) ^ ((σ - 1) / 2) *
   ((t / (2 * Real.pi)) ^ (1 / 2 - σ) * Real.exp (5 / (2 * t ^ 2)) *
    ‖riemannZeta (((1 - σ : ℝ) : ℂ) + t * I)‖) / Real.log t := by
   gcongr
   exact vaP.vcv (by linarith) hσ1 ht
  _ = (t / (2 * Real.pi)) ^ (-σ / 2) *
   (Real.exp (5 / (2 * t ^ 2)) * ‖riemannZeta (((1 - σ : ℝ) : ℂ) + t * I)‖) /
    Real.log t := by rw [← hab]; ring
  _ ≤ _ := div_le_div_of_nonneg_right (mul_le_of_le_one_left (by positivity) hP) hL.le
private lemma vlR {t : ℝ} (ht : 50 ≤ t) :
  ‖vaG (1 + (t : ℂ) * I)‖ ≤ 1 := by
 have hL : 0 < Real.log t := Real.log_pos (by linarith)
 have hz := vaT.vbT
  (s := 1 + (t : ℂ) * I) (by simp) (by simpa using ht)
 have hraw := vcL (σ := 1) (by norm_num) le_rfl ht
 simp only [Complex.ofReal_one] at hraw
 refine hraw.trans ?_
 apply (div_le_one hL).mpr
 simp only [Complex.add_im, Complex.one_im, Complex.mul_I_im, Complex.ofReal_re,
  zero_add] at hz
 linarith
private lemma vmj {t : ℝ} (ht : 50 ≤ t) :
  ‖vaG ((t : ℂ) * I)‖ ≤ 1 := by
 have hL : 0 < Real.log t := Real.log_pos (by linarith)
 have hz := vaT.vbT
  (s := 1 + (t : ℂ) * I) (by simp) (by simpa using ht)
 simp only [Complex.add_im, Complex.one_im, Complex.mul_I_im, Complex.ofReal_re,
  zero_add] at hz
 have hraw := vdH (σ := 0) le_rfl (by norm_num) ht
 norm_num at hraw
 refine hraw.trans ?_
 apply (div_le_one hL).mpr
 have hb : ‖riemannZeta (1 + (t : ℂ) * I)‖ ≤ Real.log t - 6 / 125 := by
  convert hz using 1 <;> norm_num
 exact (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le).trans
  (vaF.vct ht).le
private lemma vjm : (3.75 : ℝ) ≤ Real.log 50 - 6 / 125 := by
 have h48 : Real.log (48 : ℝ) = 4 * Real.log 2 + Real.log 3 := by
  rw [show (48 : ℝ) = 2 ^ 4 * 3 by norm_num,
   Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  norm_num
 have hle := Real.log_le_log (by norm_num : (0 : ℝ) < 48) (by norm_num : (48 : ℝ) ≤ 50)
 rw [h48] at hle
 linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]
private lemma vlh {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
  ‖vaG ((σ : ℂ) + (50 : ℂ) * I)‖ ≤ 1 := by
 have hL : 0 < Real.log (50 : ℝ) := Real.log_pos (by norm_num)
 by_cases hh : 1 / 2 ≤ σ
 ·refine (vcL hσ0 hσ1 (by norm_num : (50 : ℝ) ≤ 50)).trans ?_
  apply (div_le_one hL).mpr
  have h := vaD.vcZ hh hσ1
  norm_num at h ⊢
  linarith [vjm]
 ·have href := vaD.vcZ
   (σ := 1 - σ) (by linarith) (by linarith)
  refine (vdH hσ0 (by linarith) (by norm_num : (50 : ℝ) ≤ 50)).trans ?_
  apply (div_le_one hL).mpr
  have hbound : ‖riemannZeta (((1 - σ : ℝ) : ℂ) + (50 : ℂ) * I)‖ ≤
    Real.log 50 - 6 / 125 := href.trans vjm
  exact (mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le).trans
   (vaF.vct (by norm_num : (50 : ℝ) ≤ 50)).le
private lemma vgn {σ t : ℝ} (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1)
  (ht : 50 ≤ t) : ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤ 5 * t := by
 let s : ℂ := (σ : ℂ) + t * I
 have hs : 0 < s.re := by simp [s]; linarith
 have ht0 : 0 < t := by linarith
 have hp : s ≠ 1 := by
  intro he
  have hh := congrArg Complex.im he
  simp [s] at hh
  linarith
 have hsn : ‖s‖ ≤ 2 * t := by
  have hh := norm_add_le (σ : ℂ) ((t : ℂ) * I)
  simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at hh
  rw [abs_of_nonneg (by linarith : 0 ≤ σ), abs_of_pos ht0] at hh
  change ‖(σ : ℂ) + t * I‖ ≤ 2 * t
  linarith
 have hdn : t ≤ ‖s - 1‖ := by
  have hh := Complex.abs_im_le_norm (s - 1)
  simpa [s, abs_of_pos ht0] using hh
 have hdpos : 0 < ‖s - 1‖ := ht0.trans_le hdn
 have hh := vaa.vaz.vmG hs
 rw [vaa.vaz.vbm hp, norm_mul] at hh
 have hdiv : ‖s‖ * ‖s - 1‖ / s.re ≤ 2 * ‖s‖ * ‖s - 1‖ := by
  apply (div_le_iff₀ hs).mpr
  have hsr : 1 / 2 ≤ s.re := by simpa [s] using hσ0
  have hm := mul_nonneg (mul_nonneg (norm_nonneg s) (norm_nonneg (s - 1)))
   (show 0 ≤ 2 * s.re - 1 by linarith)
  nlinarith
 have hprod : ‖s - 1‖ * ‖riemannZeta s‖ ≤ 2 * t + 4 * t * ‖s - 1‖ := by
  have hm := mul_le_mul_of_nonneg_right hsn (norm_nonneg (s - 1))
  nlinarith
 apply (mul_le_mul_iff_right₀ hdpos).mp
 change ‖s - 1‖ * ‖riemannZeta s‖ ≤ ‖s - 1‖ * (5 * t)
 refine hprod.trans ?_
 have hm := mul_nonneg ht0.le (show 0 ≤ ‖s - 1‖ - 2 by linarith)
 nlinarith
private lemma vnI {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
  (ht : 50 ≤ t) : ‖vaG ((σ : ℂ) + t * I)‖ ≤ t ^ 2 := by
 have ht0 : 0 < t := by linarith
 have hL : 1 ≤ Real.log t := vcl (by linarith)
 have hL0 : 0 < Real.log t := by linarith
 by_cases hh : 1 / 2 ≤ σ
 ·refine (vcL hσ0 hσ1 ht).trans ?_
  have hz := vgn hh hσ1 ht
  apply (div_le_iff₀ hL0).mpr
  have hm := mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hL)
  nlinarith
 ·refine (vdH hσ0 (by linarith) ht).trans ?_
  have hz := vgn (σ := 1 - σ) (by linarith) (by linarith) ht
  have he : Real.exp (5 / (2 * t ^ 2)) ≤ 3 := by
   apply (Real.exp_le_exp.mpr ?_).trans Real.exp_one_lt_three.le
   apply (div_le_one (by positivity : (0 : ℝ) < 2 * t ^ 2)).mpr
   nlinarith
  have hm := mul_le_mul he hz (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)
  apply (div_le_iff₀ hL0).mpr
  have hmul := mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hL)
  nlinarith
lemma vfM {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
  (ht : 50 ≤ t) : ‖vaG ((σ : ℂ) + t * I)‖ ≤ 1 := by
 have hd : DiffContOnCl ℂ vaG (Ioo (0 : ℝ) 1 ×ℂ Ioi (50 : ℝ)) := by
  apply DifferentiableOn.diffContOnCl
  intro z hz
  rw [closure_reProdIm, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1), closure_Ioi] at hz
  have hzim : (50 : ℝ) ≤ z.im := hz.2
  exact (vgN (by linarith)).differentiableAt.differentiableWithinAt
 apply vgo.norm_le_one (a := 50) (by norm_num) hd
 ·intro z hre hzt
  have he : z = (z.im : ℂ) * I := by apply Complex.ext <;> simp [hre]
  rw [he]
  exact vmj hzt
 ·intro z hre hzt
  have he : z = 1 + (z.im : ℂ) * I := by apply Complex.ext <;> simp [hre]
  rw [he]
  exact vlR hzt
 ·intro z hz0 hz1 hzt
  have he : z = (z.re : ℂ) + (50 : ℂ) * I := by apply Complex.ext <;> simp [hzt]
  rw [he]
  exact vlh hz0 hz1
 ·refine ⟨1, by norm_num, ?_⟩
  intro z hz0 hz1 hzt
  simpa only [Complex.re_add_im, one_mul] using vnI hz0 hz1 hzt
 ·simpa using hσ0
 ·simpa using hσ1
 ·simpa using ht
lemma vjW {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
  (ht : 50 ≤ t) :
  ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤
   t ^ 2 / (t ^ 2 - 4) * (t / (2 * Real.pi)) ^ ((1 - σ) / 2) * Real.log t :=
 veO hσ0 hσ1 (by linarith)
  (vfM hσ0 hσ1 ht)
end vaa.vab.vjj
end
section
open Complex Real Set
namespace vaa.vab.vao
lemma vdw {T σ t : ℝ} (hT : 100 ≤ T)
  (hσ : -(1 / 2 : ℝ) ≤ σ) (ht0 : T - radius ≤ t) (ht1 : t ≤ T + radius) :
  ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤
   Real.exp (scalar (vbk T) (vbC T) (vbt T) σ) := by
 have ht50 := vch hT ht0
 have htpos : 0 < t := by linarith
 by_cases hright : 5 / 4 ≤ σ
 ·rw [vnp hright, Real.exp_log]
  ·simpa using vaT.vdR
    (s := (σ : ℂ) + t * I) (by simp; linarith)
  ·apply norm_pos_iff.mpr
   exact riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
 have hright' : σ < 5 / 4 := lt_of_not_ge hright
 by_cases hone : 1 ≤ σ
 ·rw [vob hone hright', vjk hT]
  have hz := vaT.vbT
   (s := (σ : ℂ) + t * I) (by simpa using hone) (by simpa using ht50)
  have hl := Real.log_le_log htpos ht1
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
   Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, zero_mul,
   zero_add, add_zero] at hz
  linarith
 have hone' : σ < 1 := lt_of_not_ge hone
 by_cases hzero : 0 ≤ σ
 ·rw [vmF hzero hone', vib hT]
  have hz := vjj.vjW hzero hone'.le ht50
  have hratio := viU hT ht0
  have hpower := viG hT ht0 ht1 (show 0 ≤ (1 - σ) / 2 by linarith)
  have hp0 : 0 ≤ (t / (2 * Real.pi)) ^ ((1 - σ) / 2) * Real.log t := by
   exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.log_nonneg (by linarith))
  have hc0 : 0 ≤ (T - radius) ^ 2 / ((T - radius) ^ 2 - 4) := by
   exact div_nonneg (sq_nonneg _) (vdS hT).le
  have hm := mul_le_mul hratio hpower hp0 hc0
  have he : t ^ 2 / (t ^ 2 - 4) * (t / (2 * Real.pi)) ^ ((1 - σ) / 2) * Real.log t =
    (t ^ 2 / (t ^ 2 - 4)) * ((t / (2 * Real.pi)) ^ ((1 - σ) / 2) * Real.log t) := by ring
  rw [he] at hz
  exact hz.trans (by convert hm using 1; ring)
 have hzero' : σ < 0 := lt_of_not_ge hzero
 rw [vnK hzero', vhw hT]
 have hz := vde.vhN hσ hzero'.le ht50
 have hm := viG hT ht0 ht1 (show 0 ≤ 1 / 2 - σ by linarith)
 exact hz.le.trans (by simpa only [mul_comm] using hm)
lemma vgR {T : ℝ} (hT : 100 ≤ T) {z : ℂ}
  (hz : z ∈ Metric.sphere (5 / 4 : ℂ) radius) :
  ‖riemannZeta (z + T * I)‖ ≤ Real.exp (vcH T z) := by
 have hheights := (viv (T := T) hz).1
 have hh := vdw hT (vdn hz).1 hheights.1 hheights.2
 have he : z + T * I = (z.re : ℂ) + ((T + z.im : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp [add_comm]
 simpa only [vcH, he] using hh
lemma vfN {T : ℝ} (hT : 100 ≤ T) {z : ℂ}
  (hz : z ∈ Metric.sphere (5 / 4 : ℂ) radius) :
  ‖riemannZeta (z - T * I)‖ ≤ Real.exp (vcH T z) := by
 have hheights := (viv (T := T) hz).2
 have hh := vdw hT (vdn hz).1 hheights.1 hheights.2
 have he : z - T * I = (starRingEnd ℂ)
   ((z.re : ℂ) + ((T - z.im : ℝ) : ℂ) * I) := by
  apply Complex.ext <;> simp
 rw [he, riemannZeta_conj, norm_conj]
 exact hh
end vaa.vab.vao
end
section
open Complex Real MeasureTheory Set
open scoped Interval
namespace vaa.vab.vao
lemma vit (c r θ : ℝ) :
  (circleMap (c : ℂ) r θ).re = c + r * Real.cos θ := by
 simp [circleMap]
lemma vfb {f : ℝ → ℝ} {c r : ℝ}
  (hi : IntervalIntegrable (fun θ => f (c + r * Real.cos θ)) volume 0 Real.pi) :
  CircleIntegrable (fun z : ℂ => f z.re) (c : ℂ) r := by
 let u : ℝ → ℝ := fun θ => f (c + r * Real.cos θ)
 change IntervalIntegrable u volume 0 Real.pi at hi
 have he : ∀ θ, u (-θ) = u θ := by intro θ; simp [u]
 have hp : Function.Periodic u (2 * Real.pi) := by intro θ; simp [u]
 have hn : IntervalIntegrable u volume (-Real.pi) 0 := by
  have h := (IntervalIntegrable.iff_comp_neg).mp hi
  simpa only [neg_zero, he] using h.symm
 have hfull : IntervalIntegrable u volume (-Real.pi) (-Real.pi + 2 * Real.pi) := by
  convert hn.trans hi using 1
  ring
 have hi' := hp.intervalIntegrable (by positivity : 2 * Real.pi ≠ 0) hfull 0 (2 * Real.pi)
 simpa only [CircleIntegrable, vit, u] using hi'
lemma vgI {f : ℝ → ℝ} {c r : ℝ}
  (hi : IntervalIntegrable (fun θ => f (c + r * Real.cos θ)) volume 0 Real.pi) :
  circleAverage (fun z : ℂ => f z.re) (c : ℂ) r =
   (∫ θ in (0 : ℝ)..Real.pi, f (c + r * Real.cos θ)) / Real.pi := by
 let u : ℝ → ℝ := fun θ => f (c + r * Real.cos θ)
 change IntervalIntegrable u volume 0 Real.pi at hi
 have he : ∀ θ, u (-θ) = u θ := by intro θ; simp [u]
 have hn : IntervalIntegrable u volume (-Real.pi) 0 := by
  have h := (IntervalIntegrable.iff_comp_neg).mp hi
  simpa only [neg_zero, he] using h.symm
 have hneg : (∫ θ in -Real.pi..(0 : ℝ), u θ) = ∫ θ in (0 : ℝ)..Real.pi, u θ := by
  have h := intervalIntegral.integral_comp_neg (f := u) (a := 0) (b := Real.pi)
  simpa only [neg_zero, he] using h.symm
 rw [circleAverage_eq_integral_add (η := -Real.pi)]
 simp only [vit]
 change (2 * Real.pi)⁻¹ • (∫ θ in (0 : ℝ)..2 * Real.pi, u (θ + -Real.pi)) = _
 rw [intervalIntegral.integral_comp_add_right]
 norm_num only [zero_add, show 2 * Real.pi + -Real.pi = Real.pi by ring]
 rw [← intervalIntegral.integral_add_adjacent_intervals hn hi, hneg]
 simp only [smul_eq_mul]
 dsimp [u]
 field_simp [Real.pi_ne_zero]
 ring
end vaa.vab.vao
end
section
open Real Complex Finset MeasureTheory
open vaa.vab.vbg
namespace vaa.vab.vbe
def vbv (D : ℕ) (a : ℤ) : List ℤ → Bool
 | [] => true
 | b :: bs => decide (0 ≤ a ∧ b * D ≤ 2 * a ^ 2 - (D : ℤ) ^ 2) && vbv D b bs
def vaU (a : ℤ) : List ℤ → ℤ
 | [] => a
 | b :: bs => vaU b bs
lemma vbA {D : ℕ} (hD : 0 < D) {a : ℤ} {θ : ℝ} {bs : List ℤ}
  (ha : (a : ℝ) / D ≤ Real.cos θ) (hc : vbv D a bs = true) :
  ((vaU a bs : ℤ) : ℝ) / D ≤ Real.cos ((2 : ℝ) ^ bs.length * θ) := by
 have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
 induction bs generalizing a θ with
 | nil => simpa [vaU] using ha
 | cons b bs ih =>
  simp only [vbv, Bool.and_eq_true, decide_eq_true_eq] at hc
  have ha0 : (0 : ℝ) ≤ a := by exact_mod_cast hc.1.1
  have hb : (b : ℝ) * D ≤ 2 * (a : ℝ) ^ 2 - (D : ℝ) ^ 2 := by exact_mod_cast hc.1.2
  have hb' : (b : ℝ) / D ≤ 2 * ((a : ℝ) / D) ^ 2 - 1 := by
   apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hD0)).mp
   convert hb using 1 <;> (try field_simp [hD0.ne']) <;> (try ring)
   all_goals try rfl
  have hnext : (b : ℝ) / D ≤ Real.cos (2 * θ) := by
   rw [Real.cos_two_mul]
   have hsq : ((a : ℝ) / D) ^ 2 ≤ Real.cos θ ^ 2 :=
    pow_le_pow_left₀ (div_nonneg ha0 hD0.le) ha 2
   linarith
  have hh := ih hnext hc.2
  simpa only [vaU, List.length_cons, pow_succ, mul_assoc] using hh
lemma vbQ {θ X c : ℝ} (hθ : 0 ≤ θ) (hθX : θ ≤ X)
  (hc : c ≤ 1 - X ^ 2 / 2) : c ≤ Real.cos θ := by
 have hs : θ ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hθ hθX 2
 linarith [Real.one_sub_sq_div_two_le_cos (x := θ)]
lemma vag {i p : ℕ} {a : ℤ} {bs : List ℤ}
  (hlen : bs.length = 8) (hc : vbv 1000000000000 a bs = true)
  (hinit : (a : ℝ) / 1000000000000 ≤
   1 - ((3.141593 : ℝ) * i / 8192) ^ 2 / 2)
  (hfinal : (p : ℝ) / 64 ≤ 5 / 4 + (33 / 25) *
   ((vaU a bs : ℤ) : ℝ) / 1000000000000) :
  (p : ℝ) / 64 ≤ 5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * i) := by
 have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
 have hθ : Real.pi * i / 8192 ≤ (3.141593 : ℝ) * i / 8192 := by
  gcongr
  exact Real.pi_lt_d6.le
 have hs := vbQ (show 0 ≤ Real.pi * i / 8192 by positivity) hθ hinit
 have he := vbA (by norm_num : 0 < 1000000000000) hs hc
 rw [hlen, show (2 : ℝ) ^ 8 * (Real.pi * i / 8192) = Real.pi / 32 * i by ring] at he
 nlinarith
lemma vai {p : ℕ} (hp : 64 < p) {bs : List ℕ}
  (hlen : bs.length = 16) (hc : vej p 64 100000000 1 bs = true)
  {bTail : ℕ} (hTail : 100000000 ^ 64 ≤ bTail ^ 64 * 16 ^ (p - 64))
  {B : ℝ} (hB : 0 ≤ B)
  (hnum : ((bs.sum + 16 : ℕ) : ℝ) / 100000000 +
   ((bTail : ℝ) / 100000000) / ((p : ℝ) / 64 - 1) ≤
   ∑ i ∈ Finset.range 16, B ^ i / (i.factorial : ℝ)) :
  vaE ((p : ℝ) / 64) ≤ B := by
 have hpR : (64 : ℝ) < p := by exact_mod_cast hp
 have hs : 1 < (p : ℝ) / 64 := by linarith
 have hpart := (veI (by norm_num : 0 < 1) (by norm_num : 0 < 64)
  (by norm_num : 0 < 100000000) hc).2
 rw [hlen] at hpart
 have ht := vcW hs (N := 16) (by norm_num)
 have hroot := vex (n := 16) (p := p - 64) (k := 64)
  (D := 100000000) (b := bTail) (by norm_num) (by norm_num) (by norm_num) hTail
 have he : 1 - (p : ℝ) / 64 = -((p - 64 : ℕ) : ℝ) / 64 := by
  rw [Nat.cast_sub hp.le]
  push_cast
  ring
 rw [he] at ht
 have hz : ‖riemannZeta (((p : ℝ) / 64 : ℝ) : ℂ)‖ ≤ Real.exp B := by
  refine ht.trans ((add_le_add hpart (div_le_div_of_nonneg_right hroot (by linarith))).trans ?_)
  exact hnum.trans (Real.sum_le_exp_of_nonneg hB 16)
 unfold vaE
 have hn : 0 < ‖riemannZeta (((p : ℝ) / 64 : ℝ) : ℂ)‖ :=
  norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by simpa using hs))
 simpa only [Real.log_exp] using Real.log_le_log hn hz
end vaa.vab.vbe
end
section
open Finset
namespace vaa.vab.vbe
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private def vnW : List ℕ := [100000000, 16928194, 5989309, 2865637, 1617667, 1013882, 683024, 485100, 358718, 273841, 214501, 171631, 139804, 115623, 96887, 82118]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma vnE : vaE (164 / 64) ≤ (276700 : ℝ) / 1000000 := by
 apply vai (p := 164) (bs := vnW) (bTail := 1313901)
 ·norm_num
 ·decide +kernel
 ·decide +kernel
 ·decide +kernel
 ·norm_num
 ·norm_num [vnW, Finset.sum_range_succ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma vlS : (164 : ℝ) / 64 ≤
  5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 0) := by
 have h := vag (i := 0) (p := 164)
  (a := 1000000000000) (bs := [1000000000000, 1000000000000, 1000000000000, 1000000000000, 1000000000000, 1000000000000, 1000000000000, 1000000000000])
  (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [vaU])
 simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private def vnU : List ℕ := [100000000, 16928194, 5989309, 2865637, 1617667, 1013882, 683024, 485100, 358718, 273841, 214501, 171631, 139804, 115623, 96887, 82118]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma vmV : vaE (164 / 64) ≤ (276700 : ℝ) / 1000000 := by
 apply vai (p := 164) (bs := vnU) (bTail := 1313901)
 ·norm_num
 ·decide +kernel
 ·decide +kernel
 ·decide +kernel
 ·norm_num
 ·norm_num [vnU, Finset.sum_range_succ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma vlV : (164 : ℝ) / 64 ≤
  5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 1) := by
 have h := vag (i := 1) (p := 164)
  (a := 999999926465) (bs := [999999705860, 999998823440, 999995293762, 999981175092, 999924701076, 999698815643, 998795443996, 995184677894])
  (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [vaU])
 simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private def vnX : List ℕ := [100000000, 17298873, 6198503, 2992510, 1701109, 1072271, 725847, 517670, 384214, 294272, 231193, 185490, 151471, 125563, 105443, 89551]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma vnc : vaE (162 / 64) ≤ (285253 : ℝ) / 1000000 := by
 apply vai (p := 162) (bs := vnX) (bTail := 1432819)
 ·norm_num
 ·decide +kernel
 ·decide +kernel
 ·decide +kernel
 ·norm_num
 ·norm_num [vnX, Finset.sum_range_succ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma vlZ : (162 : ℝ) / 64 ≤
  5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 2) := by
 have h := vag (i := 2) (p := 162)
  (a := 999999705862) (bs := [999998823448, 999995293794, 999981175220, 999924701588, 999698817691, 998795452185, 995184710610, 980785216463])
  (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [vaU])
 simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private def vnT : List ℕ := [100000000, 17677669, 6415002, 3125000, 1788854, 1134023, 771356, 552427, 411522, 316227, 249182, 200468, 164112, 136357, 114755, 97656]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma vnC : vaE (160 / 64) ≤ (294135 : ℝ) / 1000000 := by
 apply vai (p := 160) (bs := vnT) (bTail := 1562500)
 ·norm_num
 ·decide +kernel
 ·decide +kernel
 ·decide +kernel
 ·norm_num
 ·norm_num [vnT, Finset.sum_range_succ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma vmb : (160 : ℝ) / 64 ≤
  5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 3) := by
 have h := vag (i := 3) (p := 160)
  (a := 999999338191) (bs := [999997352764, 999989411070, 999957644504, 999830581603, 999322383817, 997290453595, 989176497663, 956940287057])
  (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [vaU])
 simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private def vnO : List ℕ := [100000000, 18064760, 6639064, 3263355, 1881125, 1199331, 819717, 589517, 440771, 339820, 268572, 216656, 177808, 148080, 124889, 106494]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma vno : vaE (158 / 64) ≤ (303361 : ℝ) / 1000000 := by
 apply vai (p := 158) (bs := vnO) (bTail := 1703919)
 ·norm_num
 ·decide +kernel
 ·decide +kernel
 ·decide +kernel
 ·norm_num
 ·norm_num [vnO, Finset.sum_range_succ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma vmm : (158 : ℝ) / 64 ≤
  5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 4) := by
 have h := vag (i := 4) (p := 158)
  (a := 999998823451) (bs := [999995293806, 999981175268, 999924701780, 999698818459, 998795455256, 995184722880, 980785265307, 923879473286])
  (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [vaU])
 simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private def vnP : List ℕ := [100000000, 18864555, 7110939, 3558714, 2080192, 1341447, 925726, 671335, 505654, 392418, 311995, 253058, 208724, 174634, 147921, 126644]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma vmY : vaE (154 / 64) ≤ (322917 : ℝ) / 1000000 := by
 apply vai (p := 154) (bs := vnP) (bTail := 2026312)
 ·norm_num
 ·decide +kernel
 ·decide +kernel
 ·decide +kernel
 ·norm_num
 ·norm_num [vnP, Finset.sum_range_succ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma vmi : (154 : ℝ) / 64 ≤
  5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 5) := by
 have h := vag (i := 5) (p := 154)
  (a := 999998161642) (bs := [999992646574, 999970586404, 999882347346, 999529417068, 998118111168, 992479527683, 970031225739, 881921157817])
  (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [vaU])
 simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private def vnQ : List ℕ := [100000000, 19699760, 7616352, 3880805, 2300324, 1500403, 1045445, 764509, 580088, 453158, 362439, 295575, 245016, 205950, 175200, 150606]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma vnA : vaE (150 / 64) ≤ (344080 : ℝ) / 1000000 := by
 apply vai (p := 150) (bs := vnQ) (bTail := 2409705)
 ·norm_num
 ·decide +kernel
 ·decide +kernel
 ·decide +kernel
 ·norm_num
 ·norm_num [vnQ, Finset.sum_range_succ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma vmk : (150 : ℝ) / 64 ≤
  5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 6) := by
 have h := vag (i := 6) (p := 150)
  (a := 999997352765) (bs := [999989411074, 999957644520, 999830581667, 999322384073, 997290454618, 989176501744, 956940303204, 831469487792])
  (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [vaU])
 simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private def vnS : List ℕ := [100000000, 20795957, 8298931, 4324718, 2608531, 1725842, 1217095, 899366, 688722, 542469, 437113, 358905, 299379, 253106, 216480, 187031]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma vmZ : vaE (145 / 64) ≤ (373068 : ℝ) / 1000000 := by
 apply vai (p := 145) (bs := vnS) (bTail := 2992511)
 ·norm_num
 ·decide +kernel
 ·decide +kernel
 ·decide +kernel
 ·norm_num
 ·norm_num [vnS, Finset.sum_range_succ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma vmh : (145 : ℝ) / 64 ≤
  5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 7) := by
 have h := vag (i := 7) (p := 145)
  (a := 999996396819) (bs := [999985587301, 999942349619, 999769405123, 999077726839, 996312608531, 985277627835, 941544007824, 773010237338])
  (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [vaU])
 simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private def vnR : List ℕ := [100000000, 22192206, 9199246, 4924940, 3033363, 2041515, 1460671, 1092952, 846261, 673170, 547299, 453057, 380762, 324155, 279046, 242550]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma vnm : vaE (139 / 64) ≤ (412130 : ℝ) / 1000000 := by
 apply vai (p := 139) (bs := vnR) (bTail := 3880806)
 ·norm_num
 ·decide +kernel
 ·decide +kernel
 ·decide +kernel
 ·norm_num
 ·norm_num [vnR, Finset.sum_range_succ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma vma : (139 : ℝ) / 64 ≤
  5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 8) := by
 have h := vag (i := 8) (p := 139)
  (a := 999995293804) (bs := [999981175260, 999924701748, 999698818331, 998795454744, 995184720834, 980785257162, 923879441332, 707106444231])
  (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [vaU])
 simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private def vnZ : List ℕ := [100000000, 23682199, 10197234, 5608465, 3527385, 2414929, 1752994, 1328208, 1039835, 835362, 685260, 571908, 484268, 415147, 359695, 314548]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma vnl : vaE (133 / 64) ≤ (456702 : ℝ) / 1000000 := by
 apply vai (p := 133) (bs := vnZ) (bTail := 5032783)
 ·norm_num
 ·decide +kernel
 ·decide +kernel
 ·decide +kernel
 ·norm_num
 ·norm_num [vnZ, Finset.sum_range_succ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma vlW : (133 : ℝ) / 64 ≤
  5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 9) := by
 have h := vag (i := 9) (p := 133)
  (a := 999994043721) (bs := [999976174954, 999904700951, 999618821967, 998475578461, 993906961566, 975702096498, 903989162221, 634392810826])
  (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [vaU])
 simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private def vng : List ℕ := [100000000, 25547428, 11499197, 6526711, 4206324, 2937749, 2168768, 1667406, 1322315, 1074607, 890754, 750519, 641097, 554064, 483693, 425979]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma vmC : vaE (126 / 64) ≤ (517200 : ℝ) / 1000000 := by
 apply vai (p := 126) (bs := vng) (bTail := 6815674)
 ·norm_num
 ·decide +kernel
 ·decide +kernel
 ·decide +kernel
 ·norm_num
 ·norm_num [vng, Finset.sum_range_succ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma vlp : (126 : ℝ) / 64 ≤
  5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 10) := by
 have h := vag (i := 10) (p := 126)
  (a := 999992646570) (bs := [999970586388, 999882347282, 999529416812, 998118110145, 992479523598, 970031209522, 881921094893, 555569635234])
  (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [vaU])
 simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private def vne : List ℕ := [100000000, 27559564, 12967392, 7595295, 5015943, 3573756, 2683155, 2093230, 1681532, 1382372, 1157871, 984911, 848714, 739465, 650437, 576885]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma vmJ : vaE (119 / 64) ≤ (589182 : ℝ) / 1000000 := by
 apply vai (p := 119) (bs := vne) (bTail := 9230164)
 ·norm_num
 ·decide +kernel
 ·decide +kernel
 ·decide +kernel
 ·norm_num
 ·norm_num [vne, Finset.sum_range_succ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma vlI : (119 : ℝ) / 64 ≤
  5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 11) := by
 have h := vag (i := 11) (p := 119)
  (a := 999991102349) (bs := [999964409554, 999857640749, 999430603528, 997723062536, 990902619032, 963776000808, 857728359466, 471395877264])
  (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [vaU])
 simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private def vnn : List ℕ := [100000000, 29730177, 14623044, 8838834, 5981395, 4347457, 3319544, 2627801, 2138334, 1778279, 1505091, 1292506, 1123567, 986906, 874662, 781250]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma vmH : vaE (112 / 64) ≤ (676082 : ℝ) / 1000000 := by
 apply vai (p := 112) (bs := vnn) (bTail := 12500000)
 ·norm_num
 ·decide +kernel
 ·decide +kernel
 ·decide +kernel
 ·norm_num
 ·norm_num [vnn, Finset.sum_range_succ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma vlK : (112 : ℝ) / 64 ≤
  5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 12) := by
 have h := vag (i := 12) (p := 112)
  (a := 999989411060) (bs := [999957644464, 999830581443, 999322383177, 997290451037, 989176487459, 956940246683, 831469271443, 382682298707])
  (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [vaU])
 simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private def vnh : List ℕ := [100000000, 32420988, 16775596, 10511205, 7314316, 5438814, 4233657, 3407836, 2814206, 2371373, 2031126, 1763317, 1548253, 1372593, 1227020, 1104854]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma vmI : vaE (104 / 64) ≤ (800295 : ℝ) / 1000000 := by
 apply vai (p := 104) (bs := vnh) (bTail := 17677670)
 ·norm_num
 ·decide +kernel
 ·decide +kernel
 ·decide +kernel
 ·norm_num
 ·norm_num [vnh, Finset.sum_range_succ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma vlq : (104 : ℝ) / 64 ≤
  5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 13) := by
 have h := vag (i := 13) (p := 104)
  (a := 999987572703) (bs := [999950291120, 999801169421, 999204756751, 996820291827, 987301388396, 949528063057, 803207085065, 290283242997])
  (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [vaU])
 simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private def vnb : List ℕ := [100000000, 35355339, 19245008, 12500000, 8944271, 6804138, 5399492, 4419417, 3703703, 3162277, 2741012, 2405626, 2133462, 1909008, 1721325, 1562500]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma vmA : vaE (96 / 64) ≤ (963201 : ℝ) / 1000000 := by
 apply vai (p := 96) (bs := vnb) (bTail := 25000000)
 ·norm_num
 ·decide +kernel
 ·decide +kernel
 ·decide +kernel
 ·norm_num
 ·norm_num [vnb, Finset.sum_range_succ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma vlG : (96 : ℝ) / 64 ≤
  5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 14) := by
 have h := vag (i := 14) (p := 96)
  (a := 999985587277) (bs := [999942349523, 999769404739, 999077725304, 996312602397, 985277603390, 941543911483, 773009874501, 195088532152])
  (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [vaU])
 simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private def vnz : List ℕ := [100000000, 38555270, 22077926, 14865088, 10937454, 8512204, 6886367, 5731275, 4874348, 4216965, 3699006, 3281903, 2939868, 2655057, 2414763, 2209708]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma vmM : vaE (88 / 64) ≤ (1188266 : ℝ) / 1000000 := by
 apply vai (p := 88) (bs := vnz) (bTail := 35355340)
 ·norm_num
 ·decide +kernel
 ·decide +kernel
 ·decide +kernel
 ·norm_num
 ·norm_num [vnz, Finset.sum_range_succ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma vlA : (88 : ℝ) / 64 ≤
  5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 15) := by
 have h := vag (i := 15) (p := 88)
  (a := 999983454782) (bs := [999933819675, 999735287459, 998941289981, 995767401657, 983105436405, 932992598178, 740950376509, 98014920897])
  (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [vaU])
 simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private def vmQ : List ℕ := [100000000, 42044820, 25327856, 17677669, 13374806, 10649051, 8782687, 7432544, 6415002, 5623413, 4991822, 4477374, 4051079, 3692665, 3387551, 3125000]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma vmL : vaE (80 / 64) ≤ (1528345 : ℝ) / 1000000 := by
 apply vai (p := 80) (bs := vmQ) (bTail := 50000000)
 ·norm_num
 ·decide +kernel
 ·decide +kernel
 ·decide +kernel
 ·norm_num
 ·norm_num [vmQ, Finset.sum_range_succ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma vlu : (80 : ℝ) / 64 ≤
  5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 16) := by
 rw [show Real.pi / 32 * 16 = Real.pi / 2 by ring, Real.cos_pi_div_two]
 norm_num
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
noncomputable def vbb : ℕ → ℕ
 | 0 => 164
 | 1 => 164
 | 2 => 162
 | 3 => 160
 | 4 => 158
 | 5 => 154
 | 6 => 150
 | 7 => 145
 | 8 => 139
 | 9 => 133
 | 10 => 126
 | 11 => 119
 | 12 => 112
 | 13 => 104
 | 14 => 96
 | 15 => 88
 | 16 => 80
 | _ => 80
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
noncomputable def vfa : ℕ → ℝ
 | 0 => 276700 / 1000000
 | 1 => 276700 / 1000000
 | 2 => 285253 / 1000000
 | 3 => 294135 / 1000000
 | 4 => 303361 / 1000000
 | 5 => 322917 / 1000000
 | 6 => 344080 / 1000000
 | 7 => 373068 / 1000000
 | 8 => 412130 / 1000000
 | 9 => 456702 / 1000000
 | 10 => 517200 / 1000000
 | 11 => 589182 / 1000000
 | 12 => 676082 / 1000000
 | 13 => 800295 / 1000000
 | 14 => 963201 / 1000000
 | 15 => 1188266 / 1000000
 | 16 => 1528345 / 1000000
 | _ => 0
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma vmp (i : ℕ) (hi : i ≤ 16) : 1 < (vbb i : ℝ) / 64 := by
 interval_cases i <;> norm_num [vbb]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma vlm (i : ℕ) (hi : i ≤ 16) : vaE ((vbb i : ℝ) / 64) ≤ vfa i := by
 interval_cases i
 ·exact vnE
 ·exact vmV
 ·exact vnc
 ·exact vnC
 ·exact vno
 ·exact vmY
 ·exact vnA
 ·exact vmZ
 ·exact vnm
 ·exact vnl
 ·exact vmC
 ·exact vmJ
 ·exact vmH
 ·exact vmI
 ·exact vmA
 ·exact vmM
 ·exact vmL
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma vki (i : ℕ) (hi : i ≤ 16) : (vbb i : ℝ) / 64 ≤
  5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * i) := by
 interval_cases i
 ·simpa only [vbb, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using vlS
 ·simpa only [vbb, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using vlV
 ·simpa only [vbb, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using vlZ
 ·simpa only [vbb, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using vmb
 ·simpa only [vbb, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using vmm
 ·simpa only [vbb, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using vmi
 ·simpa only [vbb, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using vmk
 ·simpa only [vbb, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using vmh
 ·simpa only [vbb, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using vma
 ·simpa only [vbb, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using vlW
 ·simpa only [vbb, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using vlp
 ·simpa only [vbb, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using vlI
 ·simpa only [vbb, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using vlK
 ·simpa only [vbb, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using vlq
 ·simpa only [vbb, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using vlG
 ·simpa only [vbb, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using vlA
 ·simpa only [vbb, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using vlu
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma vgS (i : ℕ) (hi : i ≤ 16) :
  vaO (Real.pi / 32 * i) ≤ vfa i := by
 have hiR : (i : ℝ) ≤ 16 := by exact_mod_cast hi
 have hmem : Real.pi / 32 * i ∈ Set.Icc 0 (Real.pi / 2) := by
  constructor
  ·positivity
  ·nlinarith [mul_le_mul_of_nonneg_left hiR Real.pi_pos.le]
 exact (vfs (vmp i hi) (vcc hmem)
  (vki i hi)).trans (vlm i hi)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma viB :
  (∫ θ in (0 : ℝ)..Real.pi / 2, vaO θ) / (2 * Real.pi) < 0.1361 := by
 have hs : (∑ i ∈ Finset.range 16,
   (vaO (Real.pi / 32 * i) + vaO (Real.pi / 32 * ((i : ℝ) + 1))) / 2) ≤
   ∑ i ∈ Finset.range 16, (vfa i + vfa (i + 1)) / 2 := by
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i < 16 := Finset.mem_range.mp hi
  have h0 := vgS i (by omega)
  have h1 := vgS (i + 1) (by omega)
  push_cast at h1
  linarith
 have hn : (∑ i ∈ Finset.range 16, (vfa i + vfa (i + 1)) / 2) / 64 < (0.1361 : ℝ) := by
  norm_num [vfa, Finset.sum_range_succ]
 exact (viN.trans (div_le_div_of_nonneg_right hs (by norm_num))).trans_lt hn
end vaa.vab.vbe
end
section
open Real MeasureTheory
namespace vaa.vab.vad
noncomputable def radius : ℝ := 33 / 25
noncomputable def q : ℝ := Real.log (44 / 25)
noncomputable def alpha : ℝ := Real.arccos (-(25 / 132))
noncomputable def beta : ℝ := Real.arccos (-(125 / 132))
noncomputable def vcQ : ℝ :=
 (radius * Real.sin alpha - (Real.pi - alpha) / 4 +
  radius * Real.sin beta - 5 * (Real.pi - beta) / 4) / (4 * Real.pi * q)
noncomputable def vfy : ℝ := 1 / (4 * q)
noncomputable def vhT (C : ℝ) : ℝ :=
 C / q - vcQ * Real.log (2 * Real.pi) + Real.log (3.426 : ℝ) / (2 * q) + 1 / 2
lemma q_pos : 0 < q := Real.log_pos (by norm_num)
lemma vjM :
  (∫ θ in alpha..Real.pi, (radius * Real.cos θ + 1 / 4)) =
   -radius * Real.sin alpha + (Real.pi - alpha) / 4 := by
 rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
  intervalIntegral.integral_const_mul, integral_cos, Real.sin_pi,
  intervalIntegral.integral_const]
 simp only [smul_eq_mul]
 ring
lemma vjp :
  (∫ θ in beta..Real.pi, (radius * Real.cos θ + 5 / 4)) =
   -radius * Real.sin beta + 5 * (Real.pi - beta) / 4 := by
 rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
  intervalIntegral.integral_const_mul, integral_cos, Real.sin_pi,
  intervalIntegral.integral_const]
 simp only [smul_eq_mul]
 ring
lemma vje (J L H V : ℝ) :
  (2 * Real.pi * J + Real.pi / 2 * H -
   L / 2 * (∫ θ in alpha..Real.pi, (radius * Real.cos θ + 1 / 4)) -
   L / 2 * (∫ θ in beta..Real.pi, (radius * Real.cos θ + 5 / 4)) +
   (beta - alpha) * V) / (2 * Real.pi * q) =
   J / q + vcQ * L + vfy * H + (beta - alpha) * V / (2 * Real.pi * q) := by
 rw [vjM, vjp]
 unfold vcQ vfy
 field_simp [q_pos.ne', Real.pi_ne_zero]
 ring
end vaa.vab.vad
end
section
open Real Set MeasureTheory
open vaa.vab.vbe
open vaa.vab.vad
open vaa.vab.vao (scalar)
namespace vaa.vab.vas
noncomputable def sigma (θ : ℝ) : ℝ := 5 / 4 + radius * Real.cos θ
noncomputable def arc (H L V θ : ℝ) : ℝ := scalar H L V (sigma θ)
lemma vhi : Real.pi / 2 ≤ alpha := by
 have h := Real.arccos_le_arccos (show -(25 / 132 : ℝ) ≤ 0 by norm_num)
 simpa only [Real.arccos_zero, alpha] using h
lemma vgc : alpha ≤ beta :=
 Real.arccos_le_arccos (by norm_num : -(125 / 132 : ℝ) ≤ -(25 / 132))
lemma vey : beta ≤ Real.pi := Real.arccos_le_pi _
lemma vkF : alpha ≤ Real.pi := vgc.trans vey
lemma vjT : 0 ≤ alpha := Real.arccos_nonneg _
lemma vnH : 0 ≤ beta := Real.arccos_nonneg _
lemma vmw : Real.cos alpha = -(25 / 132 : ℝ) :=
 Real.cos_arccos (by norm_num) (by norm_num)
lemma vnf : Real.cos beta = -(125 / 132 : ℝ) :=
 Real.cos_arccos (by norm_num) (by norm_num)
lemma vny {θ : ℝ} (h0 : 0 ≤ θ) (hα : θ < alpha) : 1 < sigma θ := by
 have h := Real.cos_lt_cos_of_nonneg_of_le_pi h0 vkF hα
 rw [vmw] at h
 dsimp [sigma, radius]
 linarith
lemma vmX {θ : ℝ} (hπ : θ ≤ Real.pi) (hα : alpha < θ) : sigma θ < 1 := by
 have h := Real.cos_lt_cos_of_nonneg_of_le_pi vjT hπ hα
 rw [vmw] at h
 dsimp [sigma, radius]
 linarith
lemma sigma_pos {θ : ℝ} (h0 : 0 ≤ θ) (hβ : θ < beta) : 0 < sigma θ := by
 have h := Real.cos_lt_cos_of_nonneg_of_le_pi h0 vey hβ
 rw [vnf] at h
 dsimp [sigma, radius]
 linarith
lemma voe {θ : ℝ} (hπ : θ ≤ Real.pi) (hβ : beta < θ) : sigma θ < 0 := by
 have h := Real.cos_lt_cos_of_nonneg_of_le_pi vnH hπ hβ
 rw [vnf] at h
 dsimp [sigma, radius]
 linarith
lemma viw {θ : ℝ} (hπ : θ ≤ Real.pi) (hθ : Real.pi / 2 < θ) :
  sigma θ < 5 / 4 := by
 have h := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity : 0 ≤ Real.pi / 2) hπ hθ
 rw [Real.cos_pi_div_two] at h
 dsimp [sigma, radius]
 linarith
lemma vlC (H L V : ℝ) {θ : ℝ} (hθ : θ ∈ Ioo 0 (Real.pi / 2)) :
  arc H L V θ = vaO θ := by
 have hcos : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hθ.1], hθ.2.le⟩
 have hs : 5 / 4 ≤ sigma θ := by dsimp [sigma, radius]; linarith
 simp only [arc, scalar, if_pos hs]
 rfl
lemma vls (H L V : ℝ) {θ : ℝ} (hθ : θ ∈ Ioo (Real.pi / 2) alpha) :
  arc H L V θ = H := by
 have h0 : 0 ≤ θ := by linarith [Real.pi_pos, hθ.1]
 have hπ : θ ≤ Real.pi := hθ.2.le.trans vkF
 have hs1 := vny h0 hθ.2
 have hs54 := viw hπ hθ.1
 have hstrip : ¬(0 ≤ sigma θ ∧ sigma θ < 1) := by intro h; linarith [h.2]
 simp only [arc, scalar, if_neg (not_le.mpr hs54),
  max_eq_right (by linarith : 1 - sigma θ ≤ 0),
  max_eq_right (by linarith : -sigma θ ≤ 0), if_neg hstrip,
  add_zero, zero_add, mul_zero]
lemma vjX (H L V : ℝ) {θ : ℝ} (hθ : θ ∈ Ioo alpha beta) :
  arc H L V θ = H - L / 2 * (radius * Real.cos θ + 1 / 4) + V := by
 have h0 : 0 ≤ θ := vjT.trans hθ.1.le
 have hπ : θ ≤ Real.pi := hθ.2.le.trans vey
 have hs0 := sigma_pos h0 hθ.2
 have hs1 := vmX hπ hθ.1
 have hs54 : sigma θ < 5 / 4 := by linarith
 have hstrip : 0 ≤ sigma θ ∧ sigma θ < 1 := ⟨hs0.le, hs1⟩
 simp only [arc, scalar, if_neg (not_le.mpr hs54),
  max_eq_left (by linarith : 0 ≤ 1 - sigma θ),
  max_eq_right (by linarith : -sigma θ ≤ 0), if_pos hstrip, add_zero]
 dsimp [sigma]
 ring
lemma vkJ (H L V : ℝ) {θ : ℝ} (hθ : θ ∈ Ioo beta Real.pi) :
  arc H L V θ = H - L / 2 * (radius * Real.cos θ + 1 / 4) -
   L / 2 * (radius * Real.cos θ + 5 / 4) := by
 have hs0 := voe hθ.2.le hθ.1
 have hs54 : sigma θ < 5 / 4 := by linarith
 have hstrip : ¬(0 ≤ sigma θ ∧ sigma θ < 1) := by intro h; linarith [h.1]
 simp only [arc, scalar, if_neg (not_le.mpr hs54),
  max_eq_left (by linarith : 0 ≤ 1 - sigma θ),
  max_eq_left (by linarith : 0 ≤ -sigma θ), if_neg hstrip, add_zero]
 dsimp [sigma]
 ring
lemma vgi (H L V : ℝ) :
  IntervalIntegrable (arc H L V) volume 0 (Real.pi / 2) ∧
  IntervalIntegrable (arc H L V) volume (Real.pi / 2) alpha ∧
  IntervalIntegrable (arc H L V) volume alpha beta ∧
  IntervalIntegrable (arc H L V) volume beta Real.pi := by
 refine ⟨?_, ?_, ?_, ?_⟩
 ·apply (vdl.intervalIntegrable_of_Icc (by positivity)).congr_uIoo
  rw [uIoo_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
  exact fun θ hθ => (vlC H L V hθ).symm
 ·apply (intervalIntegrable_const (c := H)).congr_uIoo
  rw [uIoo_of_le vhi]
  exact fun θ hθ => (vls H L V hθ).symm
 ·have h : Continuous (fun θ => H - L / 2 * (radius * Real.cos θ + 1 / 4) + V) := by fun_prop
  apply (h.intervalIntegrable alpha beta).congr_uIoo
  rw [uIoo_of_le vgc]
  exact fun θ hθ => (vjX H L V hθ).symm
 ·have h : Continuous (fun θ => H - L / 2 * (radius * Real.cos θ + 1 / 4) -
    L / 2 * (radius * Real.cos θ + 5 / 4)) := by fun_prop
  apply (h.intervalIntegrable beta Real.pi).congr_uIoo
  rw [uIoo_of_le vey]
  exact fun θ hθ => (vkJ H L V hθ).symm
lemma vco (H L V : ℝ) :
  IntervalIntegrable (arc H L V) volume 0 Real.pi := by
 obtain ⟨h1, h2, h3, h4⟩ := vgi H L V
 exact ((h1.trans h2).trans h3).trans h4
lemma vhG (H L V : ℝ) :
  (∫ θ in (0 : ℝ)..Real.pi, arc H L V θ) =
   (∫ θ in (0 : ℝ)..Real.pi / 2, vaO θ) + Real.pi / 2 * H -
   L / 2 * (∫ θ in alpha..Real.pi, (radius * Real.cos θ + 1 / 4)) -
   L / 2 * (∫ θ in beta..Real.pi, (radius * Real.cos θ + 5 / 4)) + (beta - alpha) * V := by
 obtain ⟨h1, h2, h3, h4⟩ := vgi H L V
 have he1 := intervalIntegral.integral_congr_Ioo_of_le (μ := volume) (by positivity : (0 : ℝ) ≤ Real.pi / 2)
  (fun θ hθ => vlC H L V hθ)
 have he2 := intervalIntegral.integral_congr_Ioo_of_le (μ := volume) vhi
  (fun θ hθ => vls H L V hθ)
 have he3 := intervalIntegral.integral_congr_Ioo_of_le (μ := volume) vgc
  (fun θ hθ => vjX H L V hθ)
 have he4 := intervalIntegral.integral_congr_Ioo_of_le (μ := volume) vey
  (fun θ hθ => vkJ H L V hθ)
 have hc1 : Continuous (fun θ => radius * Real.cos θ + 1 / 4) := by fun_prop
 have hc2 : Continuous (fun θ => radius * Real.cos θ + 5 / 4) := by fun_prop
 have hj := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (hc1.intervalIntegrable alpha beta)
  (hc1.intervalIntegrable beta Real.pi)
 rw [← intervalIntegral.integral_add_adjacent_intervals ((h1.trans h2).trans h3) h4,
  ← intervalIntegral.integral_add_adjacent_intervals (h1.trans h2) h3,
  ← intervalIntegral.integral_add_adjacent_intervals h1 h2,
  he1, he2, he3, he4]
 rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop) intervalIntegrable_const,
  intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
   (by apply Continuous.intervalIntegrable; fun_prop),
  intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
   (by apply Continuous.intervalIntegrable; fun_prop),
  intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
   (by apply Continuous.intervalIntegrable; fun_prop)]
 simp only [intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul]
 rw [← hj]
 ring
lemma vim (H L V : ℝ) :
  (∫ θ in (0 : ℝ)..Real.pi, arc H L V θ) / (2 * Real.pi * q) =
   ((∫ θ in (0 : ℝ)..Real.pi / 2, vaO θ) / (2 * Real.pi)) / q +
   vcQ * L + vfy * H + (beta - alpha) * V / (2 * Real.pi * q) := by
 rw [vhG]
 convert vje
  ((∫ θ in (0 : ℝ)..Real.pi / 2, vaO θ) / (2 * Real.pi)) L H V using 1 <;>
  field_simp [Real.pi_ne_zero, q_pos.ne'] <;> ring
lemma vii (H L V : ℝ) :
  (∫ θ in (0 : ℝ)..Real.pi, arc H L V θ) / (2 * Real.pi * q) ≤
   (0.1361 : ℝ) / q + vcQ * L + vfy * H +
    (beta - alpha) * V / (2 * Real.pi * q) := by
 rw [vim]
 have h := div_le_div_of_nonneg_right viB.le q_pos.le
 linarith
end vaa.vab.vas
end
section
open Real Finset
open vaa.vab.vbe
namespace vaa.vab.vad
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private lemma vnq : (25 / 132 : ℝ) ≤ Real.cos (6901 / 5000 : ℝ) := by
 have hs : (9999990916480827 : ℝ) / 10000000000000000 ≤ Real.cos ((6901 / 5000 : ℝ) / 1024) :=
  vbQ (by norm_num) le_rfl (by norm_num)
 have he := vbA (by norm_num : 0 < 10000000000000000) hs
  (by decide +kernel : vbv 10000000000000000 9999990916480827 [9999963665939810, 9999854664023272, 9999418660317597, 9997674708861553, 9990699916841987, 9962816965677297, 9851544378317476, 9410585327591732, 7711823241576957, 1894443541865304] = true)
 norm_num [vaU] at he
 linarith
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private lemma vnj : Real.cos (13803 / 10000 : ℝ) ≤ (25 / 132 : ℝ) := by
 have hs : (9999985207781639 : ℝ) / 10000000000000000 ≤ Real.cos ((Real.pi - (13803 / 10000 : ℝ)) / 1024) := by
  apply vbQ (show 0 ≤ (Real.pi - (13803 / 10000 : ℝ)) / 1024 by linarith [Real.pi_gt_three])
   (show (Real.pi - (13803 / 10000 : ℝ)) / 1024 ≤ (3.141593 - (13803 / 10000 : ℝ)) / 1024 by linarith [Real.pi_lt_d6])
  norm_num
 have he := vbA (by norm_num : 0 < 10000000000000000) hs
  (by decide +kernel : vbv 10000000000000000 9999985207781639 [9999940831170317, 9999763325381458, 9999053312728807, 9996213430158585, 9984856588256572, 9939472217610134, 9758621592928742, 9046139078795019, 6366526446580478, -1893468200998271] = true)
 norm_num only [vaU, List.length_cons, List.length_nil, Nat.reduceAdd] at he
 rw [show (1024 : ℝ) * ((Real.pi - (13803 / 10000 : ℝ)) / 1024) = Real.pi - (13803 / 10000 : ℝ) by ring,
  Real.cos_pi_sub] at he
 norm_num at he
 linarith
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private lemma vmW : (125 / 132 : ℝ) ≤ Real.cos (3271 / 10000 : ℝ) := by
 have hs : (9999999489810895 : ℝ) / 10000000000000000 ≤ Real.cos ((3271 / 10000 : ℝ) / 1024) :=
  vbQ (by norm_num) le_rfl (by norm_num)
 have he := vbA (by norm_num : 0 < 10000000000000000) hs
  (by decide +kernel : vbv 10000000000000000 9999999489810895 [9999997959243632, 9999991836975360, 9999967347914766, 9999869391872295, 9999477570900876, 9997910338189936, 9991642226097040, 9966582874865082, 9866554840310784, 9469780883372032] = true)
 norm_num [vaU] at he
 linarith
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private lemma vnr : Real.cos (409 / 1250 : ℝ) ≤ (125 / 132 : ℝ) := by
 have hs : (9999962230644424 : ℝ) / 10000000000000000 ≤ Real.cos ((Real.pi - (409 / 1250 : ℝ)) / 1024) := by
  apply vbQ (show 0 ≤ (Real.pi - (409 / 1250 : ℝ)) / 1024 by linarith [Real.pi_gt_three])
   (show (Real.pi - (409 / 1250 : ℝ)) / 1024 ≤ (3.141593 - (409 / 1250 : ℝ)) / 1024 by linarith [Real.pi_lt_d6])
  norm_num
 have he := vbA (by norm_num : 0 < 10000000000000000) hs
  (by decide +kernel : vbv 10000000000000000 9999962230644424 [9999848922863000, 9999395696016860, 9997582857104100, 9990332596932355, 9961349079465834, 9845695096594963, 9387542387022819, 7625190413630017, 1628705768823021, -9469463503720523] = true)
 norm_num only [vaU, List.length_cons, List.length_nil, Nat.reduceAdd] at he
 rw [show (1024 : ℝ) * ((Real.pi - (409 / 1250 : ℝ)) / 1024) = Real.pi - (409 / 1250 : ℝ) by ring,
  Real.cos_pi_sub] at he
 norm_num at he
 linarith
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma veC : (1.3802 : ℝ) ≤ Real.arccos (25 / 132) ∧
  Real.arccos (25 / 132) ≤ 1.3803 := by
 constructor
 ·have h := Real.arccos_le_arccos vnq
  rw [Real.arccos_cos (by norm_num) (by linarith [Real.pi_gt_three])] at h
  convert h using 1 <;> (try norm_num)
  all_goals try rfl
 ·have h := Real.arccos_le_arccos vnj
  rw [Real.arccos_cos (by norm_num) (by linarith [Real.pi_gt_three])] at h
  convert h using 1 <;> (try norm_num)
  all_goals try rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma vjV : (0.3271 : ℝ) ≤ Real.arccos (125 / 132) ∧
  Real.arccos (125 / 132) ≤ 0.3272 := by
 constructor
 ·have h := Real.arccos_le_arccos vmW
  rw [Real.arccos_cos (by norm_num) (by linarith [Real.pi_gt_three])] at h
  convert h using 1 <;> (try norm_num)
  all_goals try rfl
 ·have h := Real.arccos_le_arccos vnr
  rw [Real.arccos_cos (by norm_num) (by linarith [Real.pi_gt_three])] at h
  convert h using 1 <;> (try norm_num)
  all_goals try rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma vcI : (0.5653 : ℝ) ≤ q ∧ q ≤ 0.5654 := by
 unfold q
 constructor
 ·apply (Real.le_log_iff_exp_le (by norm_num)).mpr
  have h := Real.exp_bound' (x := (0.5653 : ℝ)) (by norm_num) (by norm_num) (n := 12) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith
 ·apply (Real.log_le_iff_le_exp (by norm_num)).mpr
  have h := Real.sum_le_exp_of_nonneg (x := (0.5654 : ℝ)) (by norm_num) 12
  norm_num [Finset.sum_range_succ] at h
  linarith
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma vla : (1.8378 : ℝ) ≤ Real.log (2 * Real.pi) := by
 apply (Real.le_log_iff_exp_le (by positivity)).mpr
 have h := Real.exp_bound' (x := (0.9189 : ℝ)) (by norm_num) (by norm_num) (n := 14) (by norm_num)
 norm_num [Finset.sum_range_succ] at h
 have h1 : Real.exp (0.9189 : ℝ) ≤ 2.5066 := by linarith
 have h2 := pow_le_pow_left₀ (Real.exp_nonneg (0.9189 : ℝ)) h1 2
 rw [← Real.exp_nat_mul] at h2
 norm_num at h2
 nlinarith [Real.pi_gt_d6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma vlj : Real.log (3.426 : ℝ) ≤ 1.2315 := by
 apply (Real.log_le_iff_le_exp (by norm_num)).mpr
 have h := Real.sum_le_exp_of_nonneg (x := (1.2315 : ℝ)) (by norm_num) 16
 norm_num [Finset.sum_range_succ] at h
 linarith
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma vgq : (5.1844 : ℝ) / 4 ≤ radius * Real.sin alpha ∧
  radius * Real.sin alpha ≤ 5.1845 / 4 := by
 have hcos : Real.cos alpha = -(25 / 132 : ℝ) := Real.cos_arccos (by norm_num) (by norm_num)
 have hs0 : 0 ≤ radius * Real.sin alpha := mul_nonneg (by norm_num [radius])
  (Real.sin_nonneg_of_mem_Icc ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩)
 have hs := Real.sin_sq_add_cos_sq alpha
 rw [hcos] at hs
 constructor
 ·apply (sq_le_sq₀ (by norm_num) hs0).mp
  unfold radius
  nlinarith
 ·apply (sq_le_sq₀ hs0 (by norm_num)).mp
  unfold radius
  nlinarith
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma vfq : (1.6965 : ℝ) / 4 ≤ radius * Real.sin beta ∧
  radius * Real.sin beta ≤ 1.6966 / 4 := by
 have hcos : Real.cos beta = -(125 / 132 : ℝ) := Real.cos_arccos (by norm_num) (by norm_num)
 have hs0 : 0 ≤ radius * Real.sin beta := mul_nonneg (by norm_num [radius])
  (Real.sin_nonneg_of_mem_Icc ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩)
 have hs := Real.sin_sq_add_cos_sq beta
 rw [hcos] at hs
 constructor
 ·apply (sq_le_sq₀ (by norm_num) hs0).mp
  unfold radius
  nlinarith
 ·apply (sq_le_sq₀ hs0 (by norm_num)).mp
  unfold radius
  nlinarith
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma vfJ : (0.1359 : ℝ) ≤ vcQ ∧ vcQ ≤ 0.1361 := by
 have hq0 : 0 < q := q_pos
 have hα : Real.pi - alpha = Real.arccos (25 / 132) := by unfold alpha; rw [Real.arccos_neg]; ring
 have hβ : Real.pi - beta = Real.arccos (125 / 132) := by unfold beta; rw [Real.arccos_neg]; ring
 have hdenpos : 0 < 4 * Real.pi * q := by positivity [q_pos]
 have hdenlo : 4 * (3.141592 : ℝ) * 0.5653 ≤ 4 * Real.pi * q := by
  gcongr
  ·exact Real.pi_gt_d6.le
  ·exact vcI.1
 have hdenhi : 4 * Real.pi * q ≤ 4 * (3.141593 : ℝ) * 0.5654 := by
  gcongr
  ·exact Real.pi_lt_d6.le
  ·exact vcI.2
 unfold vcQ
 rw [hα, hβ]
 constructor
 ·apply (le_div_iff₀ hdenpos).mpr
  nlinarith [vgq.1, vfq.1, veC.2, vjV.2]
 ·apply (div_le_iff₀ hdenpos).mpr
  nlinarith [vgq.2, vfq.2, veC.1, vjV.1]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma vol : vfy ≤ (0.4423 : ℝ) := by
 unfold vfy
 apply (div_le_iff₀ (by positivity [q_pos])).mpr
 nlinarith [vcI.1]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma vju : vhT 0.1361 ≤ (1.5803 : ℝ) := by
 have hq0 : 0 < q := q_pos
 have hA0 : 0 ≤ vcQ := by linarith [vfJ.1]
 have hlog0 : 0 ≤ Real.log (3.426 : ℝ) := Real.log_nonneg (by norm_num)
 have h1 : (0.1361 : ℝ) / q ≤ 0.1361 / 0.5653 := by
  gcongr
  exact vcI.1
 have h2 : Real.log (3.426 : ℝ) / (2 * q) ≤ 1.2315 / (2 * 0.5653) := by
  gcongr
  ·exact vlj
  ·exact vcI.1
 have h3 : (0.1359 : ℝ) * 1.8378 ≤ vcQ * Real.log (2 * Real.pi) := by
  gcongr
  ·exact vfJ.1
  ·exact vla
 unfold vhT
 linarith
end vaa.vab.vad
end
section
open Complex MeasureTheory Set Filter Metric
open scoped Real Topology
namespace vaa.vaz
lemma vko {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
  logDeriv vce s = 1 / (s - 1) + logDeriv riemannZeta s := by
 have hev : vce =ᶠ[𝓝 s] fun s => (s - 1) * riemannZeta s := by
  filter_upwards [isOpen_ne.mem_nhds hs] with t ht using vbm ht
 have hd : deriv vce s = 1 * riemannZeta s + (s - 1) * deriv riemannZeta s := by
  rw [hev.deriv_eq]
  exact ((hasDerivAt_id s).sub_const 1).mul (differentiableAt_riemannZeta hs).hasDerivAt |>.deriv
 have hs1 : s - 1 ≠ 0 := sub_ne_zero.2 hs
 rw [logDeriv_apply, logDeriv_apply, hd, vbm hs]
 field_simp
end vaa.vaz
end
section
open Complex MeasureTheory Set Filter
open scoped Real
namespace vaa.vaz
lemma vdK {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c u : ℂ} {R r : ℝ}
  (hu : u ∈ vbM f c R r) : f u = 0 := by
 by_contra hfu
 apply (vfo hu).2
 by_cases hcR : u ∈ Metric.closedBall c R
 ·rw [divB, MeromorphicOn.AnalyticOnNhd.divisor_apply
   (fun z _ => hf.analyticAt z : AnalyticOnNhd ℂ f (Metric.closedBall c R)) hcR,
   (hf.analyticAt u).analyticOrderAt_eq_zero.2 hfu]
  simp
 ·exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hcR
end vaa.vaz
end
section
open Complex MeasureTheory Set Filter
open scoped Real Topology
namespace vaa.vaz
noncomputable def xiF (s : ℂ) : ℂ := s * (s - 1) * completedRiemannZeta₀ s + 1
lemma vax : Differentiable ℂ xiF := by
 unfold xiF
 exact ((differentiable_id.mul (differentiable_id.sub_const 1)).mul differentiable_completedZeta₀).add_const 1
lemma vie (s : ℂ) : xiF (1 - s) = xiF s := by
 unfold xiF
 rw [completedRiemannZeta₀_one_sub]; ring
lemma vhq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) : xiF s = s * Gammaℝ s * vce s := by
 have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
 have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
 rw [vbm hs1, riemannZeta_def_of_ne_zero hs0, completedRiemannZeta_eq, xiF]
 have h1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.2 (Ne.symm hs1)
 have h2 : s - 1 ≠ 0 := sub_ne_zero.2 hs1
 field_simp
 ring
lemma vnY : xiF 1 = 1 := by simp [xiF]
lemma vow : xiF 0 = 1 := by simp [xiF]
lemma vaJ {s : ℂ} (hs : 1 ≤ s.re) : xiF s ≠ 0 := by
 rcases eq_or_ne s 1 with rfl | hs1
 ·rw [vnY]; exact one_ne_zero
 rw [vhq (by linarith) hs1, vbm hs1]
 have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
 exact mul_ne_zero (mul_ne_zero hs0 (Gammaℝ_ne_zero_of_re_pos (by linarith)))
  (mul_ne_zero (sub_ne_zero.2 hs1) (riemannZeta_ne_zero_of_one_le_re hs))
lemma vbY {s : ℂ} (hs : s.re ≤ 0) : xiF s ≠ 0 := by
 rw [← vie]
 exact vaJ (by simp; linarith)
lemma vhS {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) : xiF s = 0 ↔ riemannZeta s = 0 := by
 have hs1 : s ≠ 1 := by intro h; rw [h] at h1; simp at h1
 have hs0 : s ≠ 0 := by intro h; rw [h] at h0; simp at h0
 rw [vhq h0 hs1, vbm hs1]
 simp [hs0, Gammaℝ_ne_zero_of_re_pos h0, sub_ne_zero.2 hs1]
lemma logDeriv_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
  logDeriv Gammaℝ s = -(1 / 2) * Complex.log π + 1 / 2 * Complex.digamma (s / 2) := by
 have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
 have hm : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
  intro m h
  have := congrArg Complex.re h
  simp at this
  have : (0:ℝ) ≤ m := Nat.cast_nonneg m
  linarith
 have hd1 : HasDerivAt (fun w : ℂ => (π : ℂ) ^ (-w / 2)) ((π : ℂ) ^ (-s / 2) * Complex.log π * (-1 / 2)) s := by
  have : HasDerivAt (fun w : ℂ => -w / 2) (-1 / 2) s := by
   simpa using ((hasDerivAt_id s).neg).div_const 2
  exact this.const_cpow (Or.inl hpi)
 have hd2 : HasDerivAt (fun w : ℂ => w / 2) (1 / 2) s := by
  simpa using (hasDerivAt_id s).div_const 2
 have hp0 : (π : ℂ) ^ (-s / 2) ≠ 0 := by
  rw [Ne, Complex.cpow_eq_zero_iff]; tauto
 have hG0 : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero hm
 have e : Gammaℝ = fun w : ℂ => (π : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2) := by
  ext w; rw [Gammaℝ]
 rw [e, logDeriv_mul (f := fun w : ℂ => (π : ℂ) ^ (-w / 2)) (g := fun w => Complex.Gamma (w / 2)) s
  hp0 hG0 hd1.differentiableAt (differentiableAt_Gamma _ hm |>.comp s hd2.differentiableAt),
  hd2.logDeriv_Gamma hm, logDeriv_apply, hd1.deriv]
 field_simp
lemma vnk {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (hξ : xiF s ≠ 0) :
  logDeriv xiF s = 1 / s + (-(1 / 2) * Complex.log π + 1 / 2 * Complex.digamma (s / 2)) +
   logDeriv vce s := by
 have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
 have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
 have hz : vce s ≠ 0 := by
  intro h; apply hξ; rw [vhq hs hs1, h, mul_zero]
 have hloc : xiF =ᶠ[𝓝 s] fun w => w * Gammaℝ w * vce w := by
  have hU : {w : ℂ | 0 < w.re ∧ w ≠ 1} ∈ 𝓝 s :=
   ((isOpen_lt (continuous_const (y := (0 : ℝ))) Complex.continuous_re).inter
    (isOpen_ne (x := (1 : ℂ)))).mem_nhds (show s ∈ {b : ℂ | 0 < b.re} ∩ {y : ℂ | y ≠ 1} from ⟨hs, hs1⟩)
  filter_upwards [hU] with w hw using vhq hw.1 hw.2
 have hm : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
  intro m h
  have := congrArg Complex.re h
  simp at this
  have : (0:ℝ) ≤ m := Nat.cast_nonneg m
  linarith
 have hGd : DifferentiableAt ℂ Gammaℝ s := by
  have e : Gammaℝ = fun w : ℂ => (π : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2) := by
   ext w; rw [Gammaℝ]
  rw [e]
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  refine (DifferentiableAt.const_cpow (by fun_prop) (Or.inl hpi)).mul ?_
  exact (differentiableAt_Gamma _ hm).comp s (by fun_prop)
 rw [(logDeriv_congr_nhds hloc).eq_of_nhds,
  logDeriv_mul (f := fun w => w * Gammaℝ w) (g := vce) s (mul_ne_zero hs0 hG) hz
   (differentiableAt_id.mul hGd) (veE s),
  logDeriv_mul (f := fun w : ℂ => w) (g := Gammaℝ) s hs0 hG differentiableAt_id hGd,
  logDeriv_id', logDeriv_Gammaℝ hs]
end vaa.vaz
end
section
open Complex Set Metric Filter
open scoped Real Interval Topology ArithmeticFunction.vonMangoldt
namespace vaa.vaz
lemma vkC (w : ℂ) : deriv xiF (1 - w) = -deriv xiF w := by
 have h1 : HasDerivAt (fun s => xiF (1 - s)) (deriv xiF (1 - w) * (-1)) w := by
  have h3 : HasDerivAt (fun s : ℂ => 1 - s) (-1) w := by simpa using (hasDerivAt_id w).const_sub 1
  exact ((vax _).hasDerivAt).comp w h3
 have e : (fun s => xiF (1 - s)) = xiF := funext vie
 rw [e] at h1
 have := h1.unique (vax w).hasDerivAt
 linear_combination -this
lemma viI (w : ℂ) : logDeriv xiF (1 - w) = -logDeriv xiF w := by
 rw [logDeriv_apply, logDeriv_apply, vkC, vie]; ring
lemma vdb {u : ℂ} (hu : xiF u ≠ 0) : ContinuousAt (logDeriv xiF) u := by
 have h1 : ContinuousAt (deriv xiF) u := (vax.analyticAt u).deriv.continuousAt
 have h2 : ContinuousAt xiF u := vax.continuous.continuousAt
 exact h1.div h2 hu
lemma vnv (s : ℂ) : xiF (starRingEnd ℂ s) = starRingEnd ℂ (xiF s) := by
 rcases eq_or_ne s 0 with rfl | h0
 ·simp [vow]
 rcases eq_or_ne s 1 with rfl | h1
 ·simp [vnY]
 have h0' : starRingEnd ℂ s ≠ 0 := by simpa using h0
 have h1' : starRingEnd ℂ s ≠ 1 := by
  intro h; apply h1; simpa using congrArg (starRingEnd ℂ) h
 have e : ∀ w : ℂ, w ≠ 0 → w ≠ 1 → xiF w = w * (w - 1) * (completedRiemannZeta w + 1 / w + 1 / (1 - w)) + 1 := by
  intro w _ _
  rw [completedRiemannZeta_eq]; unfold xiF; ring
 rw [e _ h0' h1', e _ h0 h1, completedRiemannZeta_conj]
 simp [map_add, map_mul, map_sub, map_div₀, map_one]
lemma vgk (s : ℂ) : logDeriv xiF (starRingEnd ℂ s) = starRingEnd ℂ (logDeriv xiF s) := by
 have hf : (starRingEnd ℂ ∘ xiF ∘ starRingEnd ℂ) = xiF := by
  funext w; simp [Function.comp, vnv]
 have hd := deriv_conj_conj (f := xiF)
 rw [hf] at hd
 have h2 : deriv xiF (starRingEnd ℂ s) = starRingEnd ℂ (deriv xiF s) := by
  rw [congrFun hd (starRingEnd ℂ s)]; simp [Function.comp]
 rw [logDeriv_apply, logDeriv_apply, h2, vnv, map_div₀]
end vaa.vaz
end
section
open Complex MeasureTheory Set
open scoped Real Topology Interval
namespace vaa.vab.vae
open vaa.vaz
noncomputable def vck (T : ℝ) : ℝ :=
 (∫ t in (0 : ℝ)..(T / 2), (Complex.digamma (1 / 4 + t * I)).re) -
  T / 2 * Real.log Real.pi
noncomputable def vcx (f : ℂ → ℂ) (a T : ℝ) : ℝ :=
 (∫ t in (0 : ℝ)..T, (logDeriv f ((a : ℂ) + t * I)).re) -
  ∫ σ in (1 / 2 : ℝ)..a, (logDeriv f ((σ : ℂ) + T * I)).im
noncomputable def vbV (T : ℝ) : ℝ := vcx riemannZeta (5 / 4) T
noncomputable def vhh (T : ℝ) : ℝ := vcx xiF (5 / 4) T
def vah (T : ℝ) : Prop :=
 ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.im ≠ T
noncomputable def vaH (T : ℝ) : Finset ℂ :=
 (vbM xiF 2 (RT T) (RT T / 2)).filter (fun ρ => 0 < ρ.im ∧ ρ.im < T)
noncomputable def N (T : ℝ) : ℕ :=
 ∑ ρ ∈ vaH T, vhQ xiF T ρ
end vaa.vab.vae
end
section
open Complex MeasureTheory Set Filter
open scoped Real Topology
namespace vaa.vab.vae
open vaa.vaz
lemma vlg {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
  x ≤ (vce (x : ℂ)).re := by
 have hs : 0 < (x : ℂ).re := hx0
 rw [vkM hs]
 have hI : (vcd (x : ℂ)).re ≤ 0 := by
  unfold vcd
  have hint := vaW hs
  rw [show (∫ t in Ioi (1 : ℝ), saw t * (t : ℂ) ^ (-((x : ℂ) + 1))).re =
    RCLike.re (∫ t in Ioi (1 : ℝ), saw t * (t : ℂ) ^ (-((x : ℂ) + 1))) from rfl,
   ← integral_re hint]
  refine setIntegral_nonpos measurableSet_Ioi fun t (ht : 1 < t) => ?_
  have he : (t : ℂ) ^ (-((x : ℂ) + 1)) = ((t ^ (-(x + 1)) : ℝ) : ℂ) := by
   rw [Complex.ofReal_cpow (by linarith)]
   push_cast
   rfl
  rw [show RCLike.re (saw t * (t : ℂ) ^ (-((x : ℂ) + 1))) =
    (saw t * (t : ℂ) ^ (-((x : ℂ) + 1))).re from rfl,
   he, saw, Complex.re_mul_ofReal]
  simp only [Complex.sub_re, Complex.ofReal_re]
  have hfloor : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith)
  have hp : 0 < t ^ (-(x + 1)) := Real.rpow_pos_of_pos (by linarith) _
  nlinarith
 simp only [add_re, mul_re, mul_im, ofReal_re, ofReal_im, sub_re, sub_im, one_re, one_im,
  sub_zero, sub_self, mul_zero, zero_mul, sub_zero, add_zero]
 have hc : x * (x - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx0.le (by linarith)
 nlinarith [mul_nonneg_of_nonpos_of_nonpos hc hI]
lemma vlk (x : ℝ) : xiF (x : ℂ) ≠ 0 := by
 by_cases hx0 : x ≤ 0
 ·exact vbY hx0
 by_cases hx1 : 1 ≤ x
 ·exact vaJ hx1
 have hx0' : 0 < x := lt_of_not_ge hx0
 have hx1' : x < 1 := lt_of_not_ge hx1
 have hxne1 : (x : ℂ) ≠ 1 := by exact_mod_cast (ne_of_lt hx1')
 rw [vhq hx0' hxne1]
 apply mul_ne_zero (mul_ne_zero (by exact_mod_cast hx0'.ne')
  (Gammaℝ_ne_zero_of_re_pos hx0'))
 intro hz
 have hh := vlg hx0' hx1'
 rw [hz] at hh
 simp only [zero_re] at hh
 linarith
lemma vbR {ρ : ℂ} (hρ : xiF ρ = 0) : 0 < ρ.re ∧ ρ.re < 1 := by
 constructor
 ·by_contra h
  exact vbY (not_lt.mp h) hρ
 ·by_contra h
  exact vaJ (not_lt.mp h) hρ
lemma vdc {T : ℝ} (hg : vah T)
  {s : ℂ} (hs : s.im = T) : xiF s ≠ 0 := by
 intro hz
 have hstrip := vbR hz
 exact hg s ((vhS hstrip.1 hstrip.2).mp hz) hs
end vaa.vab.vae
end
section
open Complex MeasureTheory Set Filter Metric
open scoped Real Topology Interval
namespace vaa.vab.vae
open vaa.vaz
noncomputable def vaX : ℂ := -1 / 4
noncomputable def vaZ (T : ℝ) : ℂ := 5 / 4 + T * I
@[simp] theorem vdt : vaX.re = -1 / 4 := by norm_num [vaX]
@[simp] theorem vdr : vaX.im = 0 := by norm_num [vaX]
@[simp] theorem vds (T : ℝ) : (vaZ T).re = 5 / 4 := by simp [vaZ]
@[simp] theorem vdp (T : ℝ) : (vaZ T).im = T := by simp [vaZ]
lemma vgC (ρ : ℂ) : analyticOrderAt xiF ρ ≠ ⊤ := by
 have h2 : xiF 2 ≠ 0 := vaJ (by norm_num)
 have hc : analyticOrderAt xiF 2 ≠ ⊤ := by
  rw [(vax.analyticAt 2).analyticOrderAt_eq_zero.mpr h2]
  simp
 exact AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected
  (fun z _ => vax.analyticAt z : AnalyticOnNhd ℂ xiF univ)
  isPreconnected_univ (mem_univ 2) (mem_univ ρ) hc
lemma veg {T : ℝ} (hT : 0 < T) {ρ : ℂ} :
  ρ ∈ vaH T ↔ xiF ρ = 0 ∧ 0 < ρ.im ∧ ρ.im < T := by
 classical
 constructor
 ·intro h
  obtain ⟨hz, him0, himT⟩ := Finset.mem_filter.mp h
  exact ⟨vdK vax hz, him0, himT⟩
 ·rintro ⟨hz, him0, himT⟩
  have hre := vbR hz
  have hnorm : ‖ρ - 2‖ < RT T / 2 := by
   refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
   simp only [sub_re, sub_im]
   norm_num only [re_ofNat, im_ofNat, sub_zero]
   rw [abs_of_neg (by linarith : ρ.re - 2 < 0), abs_of_pos him0]
   unfold RT
   linarith
  have hρR : ρ ∈ closedBall (2 : ℂ) (RT T) := by
   rw [mem_closedBall, dist_eq_norm]
   unfold RT at *
   linarith
  have han : AnalyticOnNhd ℂ xiF (closedBall 2 (RT T)) :=
   fun z _ => vax.analyticAt z
  have hdiv : divB xiF 2 (RT T) ρ ≠ 0 := by
   rw [divB, MeromorphicOn.AnalyticOnNhd.divisor_apply han hρR]
   have horder : analyticOrderAt xiF ρ ≠ 0 := by
    rw [Ne, (vax.analyticAt ρ).analyticOrderAt_eq_zero]
    exact not_not.mpr hz
   have hfinite := vgC ρ
   cases ho : analyticOrderAt xiF ρ with
   | top => exact absurd ho hfinite
   | coe n => simpa [ho] using horder
  rw [vaH, Finset.mem_filter, vbM, Finset.mem_filter,
   Set.Finite.mem_toFinset, Function.mem_support]
  exact ⟨⟨hdiv, hnorm⟩, him0, himT⟩
lemma vdv {T : ℝ} (hT : 0 < T) {ρ : ℂ}
  (hρ : ρ ∈ vaH T) :
  vhQ xiF T ρ = (analyticOrderAt xiF ρ).toNat := by
 have hz := (Finset.mem_filter.mp hρ).1
 have hnorm := (vfo hz).1
 have hρR : ρ ∈ closedBall (2 : ℂ) (RT T) := by
  rw [mem_closedBall, dist_eq_norm]
  unfold RT at *
  linarith
 rw [vhQ, divB, MeromorphicOn.AnalyticOnNhd.divisor_apply
  (fun z _ => vax.analyticAt z : AnalyticOnNhd ℂ xiF (closedBall 2 (RT T))) hρR]
 cases ho : analyticOrderAt xiF ρ <;> simp
lemma vij {T : ℝ} (hT : 0 < T) :
  N T = ∑ ρ ∈ vaH T, (analyticOrderAt xiF ρ).toNat := by
 unfold N
 exact Finset.sum_congr rfl (fun ρ hρ => vdv hT hρ)
lemma vdL {T : ℝ} (hT : 0 < T) :
  (vbM xiF 2 (RT T) (RT T / 2)).filter
   (fun ρ => vaX.re < ρ.re ∧ ρ.re < (vaZ T).re ∧
    vaX.im < ρ.im ∧ ρ.im < (vaZ T).im) = vaH T := by
 classical
 apply Finset.ext
 intro ρ
 simp only [Finset.mem_filter, vdt, vdr, vds,
  vdp, vaH]
 constructor
 ·rintro ⟨hz, _, _, h0, hT⟩
  exact ⟨hz, h0, hT⟩
 ·rintro ⟨hz, h0, hT⟩
  have hre := vbR (vdK vax hz)
  exact ⟨hz, by linarith [hre.1], by linarith [hre.2], h0, hT⟩
lemma vkw {T : ℝ} (hg : vah T) :
  vfj xiF vaX (vaZ T) := by
 unfold vfj
 simp only [vdt, vdr, vds, vdp,
  ofReal_zero, zero_mul, add_zero]
 refine ⟨fun x _ => vlk x, ?_, ?_, ?_⟩
 ·intro x _
  exact vdc hg (by simp)
 ·intro y _
  exact vaJ (by norm_num)
 ·intro y _
  exact vbY (by norm_num)
lemma vgZ {T : ℝ} (hT : 0 < T) (hg : vah T) :
  vaC (logDeriv xiF) vaX (vaZ T) =
   2 * Real.pi * I * (N T : ℂ) := by
 have hR : 0 < RT T := by unfold RT; linarith
 have hrect : [[vaX.re, (vaZ T).re]] ×ℂ
   [[vaX.im, (vaZ T).im]] ⊆ ball 2 (RT T / 2) := by
  intro s hs
  rw [mem_reProdIm, vdt, vdr, vds, vdp,
   Set.uIcc_of_le (by norm_num : (-1 / 4 : ℝ) ≤ 5 / 4),
   Set.uIcc_of_le hT.le] at hs
  rw [mem_ball, dist_eq_norm]
  refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
  simp only [sub_re, sub_im]
  norm_num only [re_ofNat, im_ofNat, sub_zero]
  rw [abs_of_neg (by linarith [hs.1.2] : s.re - 2 < 0), abs_of_nonneg hs.2.1]
  unfold RT
  linarith [hs.1.1, hs.2.2]
 have hh := viV vax hR
  (vaJ (by norm_num : 1 ≤ (2 : ℂ).re))
  (by norm_num : vaX.re < (vaZ T).re)
  (by simpa using hT : vaX.im < (vaZ T).im)
  hrect (vkw hg) isOpen_univ (subset_univ _)
  (differentiableOn_const (c := (1 : ℂ)))
 simp only [mul_one] at hh
 rw [vdL hT] at hh
 simpa only [N, Nat.cast_sum, vhQ] using hh
end vaa.vab.vae
end
section
open Complex MeasureTheory Set Filter
open scoped Real Topology Interval ComplexConjugate
namespace vaa.vab.vae
open vaa.vaz
lemma ves :
  Continuous (fun t : ℝ => logDeriv xiF ((5 / 4 : ℂ) + t * I)) := by
 rw [continuous_iff_continuousAt]
 intro t
 apply ContinuousAt.comp (f := fun t : ℝ => (5 / 4 : ℂ) + t * I)
 ·exact vdb (vaJ (by norm_num))
 ·fun_prop
lemma vdP {T : ℝ} (hg : vah T) :
  Continuous (fun σ : ℝ => logDeriv xiF ((σ : ℂ) + T * I)) := by
 rw [continuous_iff_continuousAt]
 intro σ
 apply ContinuousAt.comp (f := fun σ : ℝ => (σ : ℂ) + T * I)
 ·exact vdb (vdc hg (by simp))
 ·fun_prop
private lemma veU (σ T : ℝ) :
  logDeriv xiF (((1 - σ : ℝ) : ℂ) + T * I) =
   -conj (logDeriv xiF ((σ : ℂ) + T * I)) := by
 have he : (((1 - σ : ℝ) : ℂ) + T * I) = 1 - conj ((σ : ℂ) + T * I) := by
  apply Complex.ext <;> simp
 rw [he, viI, vgk]
lemma vfl {T : ℝ} (hg : vah T) :
  (vaC (logDeriv xiF) vaX (vaZ T)).im = 2 * vhh T := by
 set F := logDeriv xiF
 set A : ℂ := ∫ σ in (1 / 2 : ℝ)..(5 / 4), F ((σ : ℂ) + T * I)
 set B : ℂ := ∫ t in (0 : ℝ)..T, F ((5 / 4 : ℂ) + t * I)
 have ht : ∀ a b : ℝ, IntervalIntegrable
   (fun σ : ℝ => F ((σ : ℂ) + T * I)) volume a b :=
  (vdP hg).intervalIntegrable
 have hv := ves.intervalIntegrable (μ := volume) (0 : ℝ) T
 have hbottom : (∫ x in (-1 / 4 : ℝ)..(5 / 4), F (x : ℂ)).im = 0 := by
  have hc : conj (∫ x in (-1 / 4 : ℝ)..(5 / 4), F (x : ℂ)) =
    ∫ x in (-1 / 4 : ℝ)..(5 / 4), F (x : ℂ) := by
   rw [← intervalIntegral.intervalIntegral_conj]
   apply intervalIntegral.integral_congr
   intro x _
   exact (vgk (x : ℂ)).symm.trans (by simp [F])
  have hh := congrArg Complex.im hc
  simp only [conj_im] at hh
  linarith
 have hleft : (∫ t in (0 : ℝ)..T, F ((-1 / 4 : ℂ) + t * I)) = -conj B := by
  rw [← intervalIntegral.intervalIntegral_conj, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro t _
  simpa only [show (1 : ℝ) - 5 / 4 = -1 / 4 by norm_num, ofReal_div,
   ofReal_neg, ofReal_one, ofReal_ofNat] using veU (5 / 4) t
 have htopLeft : (∫ σ in (-1 / 4 : ℝ)..(1 / 2), F ((σ : ℂ) + T * I)) =
   -conj A := by
  have hs := intervalIntegral.integral_comp_sub_left
   (a := (1 / 2 : ℝ)) (b := 5 / 4)
   (fun σ : ℝ => F ((σ : ℂ) + T * I)) 1
  rw [show (1 : ℝ) - 5 / 4 = -1 / 4 by norm_num,
   show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hs
  rw [← hs, ← intervalIntegral.intervalIntegral_conj, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro σ _
  exact veU σ T
 have htop : (∫ σ in (-1 / 4 : ℝ)..(5 / 4), F ((σ : ℂ) + T * I)) =
   A - conj A := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (ht (-1 / 4) (1 / 2))
   (ht (1 / 2) (5 / 4)), htopLeft]
  change -conj A + A = A - conj A
  ring
 have hAim : A.im = ∫ σ in (1 / 2 : ℝ)..(5 / 4),
   (F ((σ : ℂ) + T * I)).im := by
  exact (Complex.imCLM.intervalIntegral_comp_comm (ht (1 / 2) (5 / 4))).symm
 have hBre : B.re = ∫ t in (0 : ℝ)..T, (F ((5 / 4 : ℂ) + t * I)).re := by
  exact (Complex.reCLM.intervalIntegral_comp_comm hv).symm
 unfold vaC
 simp only [vdt, vdr, vds, vdp,
  ofReal_zero, zero_mul, add_zero, smul_eq_mul,
  ofReal_div, ofReal_neg, ofReal_one, ofReal_ofNat]
 change ((∫ x in (-1 / 4 : ℝ)..(5 / 4), F (x : ℂ)) -
   (∫ x in (-1 / 4 : ℝ)..(5 / 4), F ((x : ℂ) + T * I)) +
   I * B - I * (∫ t in (0 : ℝ)..T, F ((-1 / 4 : ℂ) + t * I))).im = _
 rw [htop, hleft]
 simp only [sub_im, add_im, I_mul_im, neg_re, conj_re, conj_im, hbottom]
 unfold vhh vcx
 norm_num only [ofReal_div, ofReal_ofNat]
 rw [← hBre, ← hAim]
 ring
lemma viL {T : ℝ} (hT : 0 < T) (hg : vah T) :
  Real.pi * (N T : ℝ) = vhh T := by
 have hr := congrArg Complex.im (vgZ hT hg)
 rw [vfl hg] at hr
 simp only [mul_im, mul_re, ofReal_re, ofReal_im, natCast_re, natCast_im,
  I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero, zero_add] at hr
 norm_num at hr
 linarith
end vaa.vab.vae
end
section
open Complex MeasureTheory Set Filter
open scoped Real Topology Interval
namespace vaa.vab.vae
open vaa.vaz
lemma vhu {ρ : ℂ} (him : ρ.im ≠ 0)
  (hz : riemannZeta ρ = 0) : xiF ρ = 0 := by
 have hρ0 : ρ ≠ 0 := by intro h; apply him; simp [h]
 have hρ1 : ρ ≠ 1 := by intro h; apply him; simp [h]
 have hG : Gammaℝ ρ ≠ 0 := by
  intro h
  obtain ⟨m, hm⟩ := Gammaℝ_eq_zero_iff.mp h
  apply him
  rw [hm]
  simp
 have hΛ : completedRiemannZeta ρ = 0 := by
  rw [riemannZeta_def_of_ne_zero hρ0] at hz
  exact (div_eq_zero_iff.mp hz).resolve_right hG
 have he : completedRiemannZeta₀ ρ = completedRiemannZeta ρ +
   1 / ρ + 1 / (1 - ρ) := by
  rw [completedRiemannZeta_eq]
  ring
 rw [xiF, he, hΛ]
 have h1 : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr hρ1.symm
 field_simp
 ring
lemma vbo {T : ℝ} (hT : 0 < T) {ρ : ℂ} :
  ρ ∈ vaH T ↔ riemannZeta ρ = 0 ∧ 0 < ρ.im ∧ ρ.im < T := by
 rw [veg hT]
 constructor
 ·rintro ⟨hz, h0, hT⟩
  have hre := vbR hz
  exact ⟨(vhS hre.1 hre.2).mp hz, h0, hT⟩
 ·rintro ⟨hz, h0, hT⟩
  exact ⟨vhu h0.ne' hz, h0, hT⟩
lemma vfZ {ρ : ℂ} (hρ : xiF ρ = 0) :
  analyticOrderAt xiF ρ = analyticOrderAt riemannZeta ρ := by
 have hre := vbR hρ
 have hρ0 : ρ ≠ 0 := by intro h; simp [h] at hre
 have hρ1 : ρ ≠ 1 := by intro h; simp [h] at hre
 have hloc : xiF =ᶠ[𝓝 ρ] fun s => (s * Gammaℝ s * (s - 1)) * riemannZeta s := by
  have hu : {s : ℂ | 0 < s.re ∧ s ≠ 1} ∈ 𝓝 ρ :=
   ((isOpen_lt (continuous_const (y := (0 : ℝ))) Complex.continuous_re).inter
    (isOpen_ne (x := (1 : ℂ)))).mem_nhds
    (show ρ ∈ {b : ℂ | 0 < b.re} ∩ {y : ℂ | y ≠ 1} from ⟨hre.1, hρ1⟩)
  filter_upwards [hu] with s hs
  rw [vhq hs.1 hs.2, vbm hs.2]
  ring
 have hGamma : AnalyticAt ℂ Gammaℝ ρ := by
  apply DifferentiableOn.analyticOnNhd (s := {s : ℂ | 0 < s.re}) _
   (isOpen_lt continuous_const Complex.continuous_re) ρ hre.1
  intro s hs
  change 0 < s.re at hs
  have hm : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
   intro m h
   have hr := congrArg Complex.re h
   simp at hr
   have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
   linarith
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hd : DifferentiableAt ℂ
    (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2)) s :=
   (DifferentiableAt.const_cpow (by fun_prop) (Or.inl hpi)).mul
    ((Complex.differentiableAt_Gamma _ hm).comp s (differentiableAt_id.div_const 2))
  exact hd.differentiableWithinAt
 have he : AnalyticAt ℂ (fun s : ℂ => s * Gammaℝ s * (s - 1)) ρ :=
  (analyticAt_id.mul hGamma).mul (analyticAt_id.sub analyticAt_const)
 have hen : ρ * Gammaℝ ρ * (ρ - 1) ≠ 0 :=
  mul_ne_zero (mul_ne_zero hρ0 (Gammaℝ_ne_zero_of_re_pos hre.1)) (sub_ne_zero.mpr hρ1)
 rw [analyticOrderAt_congr hloc,
  show (fun s : ℂ => (s * Gammaℝ s * (s - 1)) * riemannZeta s) =
   (fun s : ℂ => s * Gammaℝ s * (s - 1)) * riemannZeta from rfl,
  analyticOrderAt_mul he (analyticOn_riemannZeta ρ hρ1),
  he.analyticOrderAt_eq_zero.mpr hen, zero_add]
lemma vgM {T : ℝ} (hT : 0 < T) :
  N T = ∑ ρ ∈ vaH T, (analyticOrderAt riemannZeta ρ).toNat := by
 rw [vij hT]
 apply Finset.sum_congr rfl
 intro ρ hρ
 rw [vfZ ((veg hT).mp hρ).1]
end vaa.vab.vae
end
section
open Complex MeasureTheory Set
open scoped Real Topology Interval
namespace vaa.vab.vae
noncomputable def vaM (s : ℂ) : ℂ := 1 / s + 1 / (s - 1)
lemma vdk {b : ℝ} (hb : 0 < b) (T : ℝ) :
  (∫ t in (0 : ℝ)..T, (1 / ((b : ℂ) + t * I)).re) = Real.arctan (T / b) := by
 have hpt (t : ℝ) : (1 / ((b : ℂ) + t * I)).re = b / (b ^ 2 + t ^ 2) := by
  rw [one_div, Complex.inv_re, Complex.normSq_apply]
  simp [-Complex.ofReal_arctan]
  ring_nf
 simp_rw [hpt]
 have hd : ∀ t ∈ [[(0 : ℝ), T]], HasDerivAt (fun t : ℝ => Real.arctan (t / b))
   (b / (b ^ 2 + t ^ 2)) t := by
  intro t _
  have hh := (Real.hasDerivAt_arctan (t / b)).comp t ((hasDerivAt_id t).div_const b)
  change HasDerivAt (fun u : ℝ => Real.arctan (u / b))
   ((1 / (1 + (t / b) ^ 2)) * (1 / b)) t at hh
  apply hh.congr_deriv
  field_simp <;> ring
 have hc : Continuous (fun t : ℝ => b / (b ^ 2 + t ^ 2)) :=
  continuous_const.div (g := fun t : ℝ => b ^ 2 + t ^ 2) (by fun_prop) (fun _ => by positivity)
 rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)]
 simp [-Complex.ofReal_arctan]
lemma vgD {a : ℝ} (ha : 1 < a) (T : ℝ) :
  (∫ t in (0 : ℝ)..T, (vaM ((a : ℂ) + t * I)).re) =
   Real.arctan (T / a) + Real.arctan (T / (a - 1)) := by
 have he (t : ℝ) : ((a : ℂ) + t * I) - 1 = ((a - 1 : ℝ) : ℂ) + t * I := by
  push_cast
  ring
 have hc (b : ℝ) (hb : 0 < b) : Continuous (fun t : ℝ => (1 / ((b : ℂ) + t * I)).re) := by
  apply Complex.continuous_re.comp
  apply continuous_const.div (g := fun t : ℝ => (b : ℂ) + t * I) (by fun_prop)
  intro t h
  have hr := congrArg Complex.re h
  simp [-Complex.ofReal_arctan] at hr
  linarith
 simp only [vaM, add_im, add_re, he]
 rw [intervalIntegral.integral_add ((hc a (by linarith)).intervalIntegrable _ _)
  ((hc (a - 1) (by linarith)).intervalIntegrable _ _),
  vdk (by linarith), vdk (by linarith)]
lemma vfx {T : ℝ} (hT : 0 < T) (a : ℝ) :
  (∫ σ in (1 / 2 : ℝ)..a, (vaM ((σ : ℂ) + T * I)).im) =
   -(Real.arctan (a / T) + Real.arctan ((a - 1) / T)) := by
 have hpt (σ : ℝ) : (vaM ((σ : ℂ) + T * I)).im =
   -(T / (σ ^ 2 + T ^ 2)) - T / ((σ - 1) ^ 2 + T ^ 2) := by
  rw [vaM, add_im, one_div, one_div, inv_im, inv_im, normSq_apply, normSq_apply]
  simp [-Complex.ofReal_arctan]
  ring_nf
 simp_rw [hpt]
 have hd : ∀ σ ∈ [[(1 / 2 : ℝ), a]],
   HasDerivAt (fun u : ℝ => -Real.arctan (u / T) - Real.arctan ((u - 1) / T))
    (-(T / (σ ^ 2 + T ^ 2)) - T / ((σ - 1) ^ 2 + T ^ 2)) σ := by
  intro σ _
  have h1 := (Real.hasDerivAt_arctan (σ / T)).comp σ ((hasDerivAt_id σ).div_const T)
  have h2 := (Real.hasDerivAt_arctan ((σ - 1) / T)).comp σ
   (((hasDerivAt_id σ).sub_const 1).div_const T)
  have hh : HasDerivAt (fun u : ℝ => -Real.arctan (u / T) - Real.arctan ((u - 1) / T))
    (-(1 / (1 + (σ / T) ^ 2) * (1 / T)) -
     (1 / (1 + ((σ - 1) / T) ^ 2) * (1 / T))) σ := h1.neg.sub h2
  apply hh.congr_deriv
  field_simp
  ring
 have hc : Continuous (fun σ : ℝ => -(T / (σ ^ 2 + T ^ 2)) -
   T / ((σ - 1) ^ 2 + T ^ 2)) := by
  have c1 : Continuous (fun σ : ℝ => T / (σ ^ 2 + T ^ 2)) :=
   continuous_const.div (g := fun σ : ℝ => σ ^ 2 + T ^ 2) (by fun_prop) (fun _ => by positivity)
  have c2 : Continuous (fun σ : ℝ => T / ((σ - 1) ^ 2 + T ^ 2)) :=
   continuous_const.div (g := fun σ : ℝ => (σ - 1) ^ 2 + T ^ 2) (by fun_prop)
    (fun _ => by positivity)
  exact c1.neg.sub c2
 rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)]
 rw [show ((1 : ℝ) / 2 - 1) / T = -((1 / 2) / T) by ring, Real.arctan_neg]
 ring
lemma vmo {a T : ℝ} (ha : 1 < a) (hT : 0 < T) :
  (∫ t in (0 : ℝ)..T, (vaM ((a : ℂ) + t * I)).re) -
   (∫ σ in (1 / 2 : ℝ)..a, (vaM ((σ : ℂ) + T * I)).im) = Real.pi := by
 rw [vgD ha, vfx hT]
 have h1 := Real.arctan_inv_of_pos (show 0 < T / a by positivity)
 have h2 := Real.arctan_inv_of_pos (show 0 < T / (a - 1) by positivity)
 rw [inv_div] at h1 h2
 linarith
end vaa.vab.vae
end
section
open Complex Real MeasureTheory intervalIntegral
open scoped Topology Interval
namespace vaa.vab.vam
noncomputable def vbp (T : ℝ) : ℝ :=
 ∫ t in (0 : ℝ)..(T / 2), (Complex.digamma (1 / 4 + t * Complex.I)).re
lemma vby {z : ℂ} (hz : 0 < z.re) :
  DifferentiableAt ℂ Complex.digamma z :=
 (vac.veo z hz).differentiableAt
lemma vig {x : ℝ} (hx : 0 < x) :
  (Complex.digamma (x : ℂ)).im = 0 := by
 rw [vac.vdo hx]
 rfl
lemma vcg {a : ℝ} (ha : 0 < a) :
  Continuous (fun t : ℝ ↦ Complex.digamma (((a : ℂ) + t * I) / 2)) := by
 rw [continuous_iff_continuousAt]
 intro t
 have hp : 0 < (((a : ℂ) + t * I) / 2).re := by
  simp [Complex.div_ofNat_re]
  positivity
 exact ContinuousAt.comp (g := Complex.digamma)
  (f := fun t : ℝ ↦ ((a : ℂ) + t * I) / 2) (x := t)
  (vby hp).continuousAt (by fun_prop)
lemma vbx (T : ℝ) :
  ContinuousOn (fun a : ℝ ↦ Complex.digamma (((a : ℂ) + T * I) / 2))
   (Set.Ioi 0) := by
 intro a ha
 change 0 < a at ha
 have hp : 0 < (((a : ℂ) + T * I) / 2).re := by
  simpa [Complex.div_ofNat_re] using div_pos ha (by norm_num : (0 : ℝ) < 2)
 exact (ContinuousAt.comp (g := Complex.digamma)
  (f := fun a : ℝ ↦ ((a : ℂ) + T * I) / 2) (x := a)
  (vby hp).continuousAt (by fun_prop)).continuousWithinAt
private lemma integral_im {f : ℝ → ℂ} {a b : ℝ}
  (hf : IntervalIntegrable f volume a b) :
  (∫ t in a..b, f t).im = ∫ t in a..b, (f t).im := by
 exact (Complex.imCLM.intervalIntegral_comp_comm hf).symm
private lemma integral_re {f : ℝ → ℂ} {a b : ℝ}
  (hf : IntervalIntegrable f volume a b) :
  (∫ t in a..b, f t).re = ∫ t in a..b, (f t).re := by
 exact (Complex.reCLM.intervalIntegral_comp_comm hf).symm
lemma vkt {a : ℝ} (ha : 1 / 2 ≤ a) (T : ℝ) :
  (∫ t in (0 : ℝ)..T, (Complex.digamma (((a : ℂ) + t * I) / 2)).re) -
   (∫ σ in (1 / 2 : ℝ)..a, (Complex.digamma (((σ : ℂ) + T * I) / 2)).im) =
   2 * vbp T := by
 let f : ℂ → ℂ := fun s ↦ Complex.digamma (s / 2)
 have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
 have ha0 : 0 < a := hhalf.trans_le ha
 have hc : Set.uIcc (1 / 2 : ℝ) a = Set.Icc (1 / 2 : ℝ) a := Set.uIcc_of_le ha
 have hdiff : DifferentiableOn ℂ f
   (Set.uIcc ((1 / 2 : ℂ).re) (((a : ℂ) + T * I).re) ×ℂ
    Set.uIcc ((1 / 2 : ℂ).im) (((a : ℂ) + T * I).im)) := by
  intro s hs
  rw [Complex.mem_reProdIm] at hs
  have hre : 1 / 2 ≤ s.re := by
   have hsr : s.re ∈ Set.uIcc (1 / 2 : ℝ) a := by simpa using hs.1
   rw [hc] at hsr
   exact hsr.1
  have hp : 0 < (s / 2).re := by
   rw [Complex.div_ofNat_re]
   linarith
  exact ((vby hp).comp s
   (differentiableAt_id.div_const 2)).differentiableWithinAt
 have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
  f (1 / 2 : ℂ) ((a : ℂ) + T * I) hdiff
 have hsub : Set.uIcc (1 / 2 : ℝ) a ⊆ Set.Ioi 0 := by
  intro t ht
  rw [hc] at ht
  exact hhalf.trans_le ht.1
 have htop : IntervalIntegrable (fun σ : ℝ ↦ f ((σ : ℂ) + T * I)) volume (1 / 2) a :=
  ((vbx T).mono hsub).intervalIntegrable
 have hbot : IntervalIntegrable (fun σ : ℝ ↦ f ((σ : ℂ) + (0 : ℂ) * I))
   volume (1 / 2) a :=
  ((vbx 0).mono hsub).intervalIntegrable
 have hright : IntervalIntegrable (fun t : ℝ ↦ f ((a : ℂ) + t * I)) volume 0 T :=
  (vcg ha0).intervalIntegrable 0 T
 have hleft : IntervalIntegrable (fun t : ℝ ↦ f ((1 / 2 : ℂ) + t * I)) volume 0 T :=
  by simpa [f] using (vcg hhalf).intervalIntegrable 0 T
 have him := congrArg Complex.im hrect
 simp only [Complex.div_ofNat_re, Complex.one_re, Complex.div_ofNat_im,
  Complex.one_im, zero_div, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re,
  Complex.ofReal_im, sub_zero, Complex.add_im, Complex.mul_I_im, zero_add,
  neg_zero, add_zero] at him
 norm_num only [Complex.ofReal_zero, Complex.ofReal_div, Complex.ofReal_one,
  Complex.ofReal_ofNat] at him
 rw [Complex.sub_im, Complex.add_im, Complex.sub_im, Complex.zero_im,
  smul_eq_mul, smul_eq_mul, Complex.I_mul_im, Complex.I_mul_im,
  integral_im hbot, integral_im htop, integral_re hright, integral_re hleft] at him
 have hbot0 : (∫ σ in (1 / 2 : ℝ)..a, (f ((σ : ℂ) + (0 : ℂ) * I)).im) = 0 := by
  calc
   _ = ∫ _σ in (1 / 2 : ℝ)..a, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro σ hσ
    have hσ0 : 0 < σ := hsub hσ
    have he : ((σ : ℂ) + (0 : ℂ) * I) / 2 = ((σ / 2 : ℝ) : ℂ) := by
     push_cast
     ring
    dsimp [f]
    rw [he]
    exact vig (by positivity)
   _ = 0 := by simp
 rw [hbot0] at him
 have hl : (∫ t in (0 : ℝ)..T, (f ((1 / 2 : ℂ) + t * I)).re) =
   2 * vbp T := by
  have he : (fun t : ℝ ↦ (f ((1 / 2 : ℂ) + t * I)).re) =
    (fun t : ℝ ↦ (Complex.digamma (1 / 4 + (t / 2 : ℝ) * I)).re) := by
   funext t
   dsimp [f]
   congr 2
   push_cast
   ring
  rw [he, intervalIntegral.integral_comp_div
   (fun u : ℝ ↦ (Complex.digamma (1 / 4 + u * I)).re) (two_ne_zero)]
  simp [vbp, smul_eq_mul]
 rw [hl] at him
 dsimp [f] at him
 linarith
end vaa.vab.vam
end
section
open Complex MeasureTheory Set Filter
open scoped Real Topology Interval
namespace vaa.vab.vae
open vaa.vaz
private lemma vcN {s : ℂ} (hs : s ≠ 1)
  (hz : riemannZeta s ≠ 0) : ContinuousAt (logDeriv riemannZeta) s := by
 have ha : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs
 exact ha.deriv.continuousAt.div ha.continuousAt hz
private lemma vhl :
  Continuous (fun t : ℝ => logDeriv riemannZeta ((5 / 4 : ℂ) + t * I)) := by
 rw [continuous_iff_continuousAt]
 intro t
 apply ContinuousAt.comp (f := fun t : ℝ => (5 / 4 : ℂ) + t * I)
 ·apply vcN
  ·intro h
   have hh := congrArg Complex.re h
   norm_num at hh
  ·exact riemannZeta_ne_zero_of_one_lt_re (by norm_num)
 ·fun_prop
private lemma vgf {T : ℝ} (hT : 0 < T) (hg : vah T) :
  Continuous (fun σ : ℝ => logDeriv riemannZeta ((σ : ℂ) + T * I)) := by
 rw [continuous_iff_continuousAt]
 intro σ
 apply ContinuousAt.comp (f := fun σ : ℝ => (σ : ℂ) + T * I)
 ·apply vcN
  ·intro h
   have hh := congrArg Complex.im h
   simp at hh
   linarith
  ·intro hz
   exact hg _ hz (by simp)
 ·fun_prop
lemma vcY {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
  (hz : riemannZeta s ≠ 0) :
  logDeriv xiF s = vaM s - (Real.log Real.pi : ℂ) / 2 +
   (1 / 2 : ℂ) * Complex.digamma (s / 2) + logDeriv riemannZeta s := by
 have hx : xiF s ≠ 0 := by
  rw [vhq hs hs1, vbm hs1]
  apply mul_ne_zero
  ·apply mul_ne_zero
   ·intro h
    simp [h] at hs
   ·exact Gammaℝ_ne_zero_of_re_pos hs
  ·exact mul_ne_zero (sub_ne_zero.mpr hs1) hz
 rw [vnk hs hs1 hx, vko hs1 hz,
  ← Complex.ofReal_log Real.pi_pos.le]
 unfold vaM
 push_cast
 ring
private lemma vhv :
  Continuous (fun t : ℝ => vaM ((5 / 4 : ℂ) + t * I)) := by
 unfold vaM
 apply Continuous.add
 ·apply continuous_const.div (g := fun t : ℝ => (5 / 4 : ℂ) + t * I) (by fun_prop)
  intro t h
  have hh := congrArg Complex.re h
  norm_num at hh
 ·apply continuous_const.div (g := fun t : ℝ => (5 / 4 : ℂ) + t * I - 1) (by fun_prop)
  intro t h
  have hh := congrArg Complex.re h
  norm_num at hh
private lemma vgb {T : ℝ} (hT : 0 < T) :
  Continuous (fun σ : ℝ => vaM ((σ : ℂ) + T * I)) := by
 unfold vaM
 apply Continuous.add
 ·apply continuous_const.div (g := fun σ : ℝ => (σ : ℂ) + T * I) (by fun_prop)
  intro σ h
  have hh := congrArg Complex.im h
  simp at hh
  linarith
 ·apply continuous_const.div (g := fun σ : ℝ => (σ : ℂ) + T * I - 1) (by fun_prop)
  intro σ h
  have hh := congrArg Complex.im h
  simp at hh
  linarith
lemma vcR {T : ℝ}
  (hT : 0 < T) (hg : vah T) :
  vhh T = Real.pi + vck T + vbV T := by
 have hpv := (Complex.continuous_re.comp vhv).intervalIntegrable (μ := volume) (0 : ℝ) T
 have hgv := (Complex.continuous_re.comp
  (vam.vcg (by norm_num : (0 : ℝ) < 5 / 4))).intervalIntegrable (μ := volume) (0 : ℝ) T
 have hzv := (Complex.continuous_re.comp vhl).intervalIntegrable (μ := volume) (0 : ℝ) T
 have hph := (Complex.continuous_im.comp (vgb hT)).intervalIntegrable (μ := volume) (1 / 2 : ℝ) (5 / 4)
 have hgh : IntervalIntegrable (fun σ : ℝ =>
   (Complex.digamma (((σ : ℂ) + T * I) / 2)).im) volume (1 / 2) (5 / 4) := by
  apply ContinuousOn.intervalIntegrable
  apply Complex.continuous_im.comp_continuousOn
  apply (vam.vbx T).mono
  intro σ hσ
  rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 5 / 4)] at hσ
  exact show (0 : ℝ) < σ from lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hσ.1
 have hzh := (Complex.continuous_im.comp (vgf hT hg)).intervalIntegrable (μ := volume)
  (1 / 2 : ℝ) (5 / 4)
 dsimp only [Function.comp_def] at hpv hgv hzv hph hzh
 norm_num only [ofReal_div, ofReal_ofNat] at hgv
 have hv : (∫ t in (0 : ℝ)..T, (logDeriv xiF ((5 / 4 : ℂ) + t * I)).re) =
   (∫ t in (0 : ℝ)..T, (vaM ((5 / 4 : ℂ) + t * I)).re) - T / 2 * Real.log Real.pi +
   (1 / 2) * (∫ t in (0 : ℝ)..T, (Complex.digamma (((5 / 4 : ℂ) + t * I) / 2)).re) +
   (∫ t in (0 : ℝ)..T, (logDeriv riemannZeta ((5 / 4 : ℂ) + t * I)).re) := by
  have he (t : ℝ) : (logDeriv xiF ((5 / 4 : ℂ) + t * I)).re =
    (vaM ((5 / 4 : ℂ) + t * I)).re - Real.log Real.pi / 2 +
    (1 / 2) * (Complex.digamma (((5 / 4 : ℂ) + t * I) / 2)).re +
    (logDeriv riemannZeta ((5 / 4 : ℂ) + t * I)).re := by
   rw [vcY (by norm_num) (by
    intro h; have hh := congrArg Complex.re h; norm_num at hh)
    (riemannZeta_ne_zero_of_one_lt_re (by norm_num))]
   simp [add_re, sub_re, mul_re, div_ofNat_re]
  simp_rw [he]
  rw [intervalIntegral.integral_add ((hpv.sub intervalIntegrable_const).add (hgv.const_mul _)) hzv,
   intervalIntegral.integral_add (hpv.sub intervalIntegrable_const) (hgv.const_mul _),
   intervalIntegral.integral_sub hpv intervalIntegrable_const,
   intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  ring
 have hh : (∫ σ in (1 / 2 : ℝ)..(5 / 4), (logDeriv xiF ((σ : ℂ) + T * I)).im) =
   (∫ σ in (1 / 2 : ℝ)..(5 / 4), (vaM ((σ : ℂ) + T * I)).im) +
   (1 / 2) * (∫ σ in (1 / 2 : ℝ)..(5 / 4), (Complex.digamma (((σ : ℂ) + T * I) / 2)).im) +
   (∫ σ in (1 / 2 : ℝ)..(5 / 4), (logDeriv riemannZeta ((σ : ℂ) + T * I)).im) := by
  have he : EqOn (fun σ : ℝ => (logDeriv xiF ((σ : ℂ) + T * I)).im)
    (fun σ : ℝ => (vaM ((σ : ℂ) + T * I)).im +
     (1 / 2) * (Complex.digamma (((σ : ℂ) + T * I) / 2)).im +
     (logDeriv riemannZeta ((σ : ℂ) + T * I)).im) [[(1 / 2 : ℝ), 5 / 4]] := by
   intro σ hσ
   rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 5 / 4)] at hσ
   have hs : 0 < (((σ : ℂ) + T * I)).re := by simp; linarith [hσ.1]
   have hs1 : ((σ : ℂ) + T * I) ≠ 1 := by
    intro h; have hi := congrArg Complex.im h; simp at hi; linarith
   have hz : riemannZeta ((σ : ℂ) + T * I) ≠ 0 := by
    intro hz; exact hg _ hz (by simp)
   dsimp only
   rw [vcY hs hs1 hz]
   simp [add_im, sub_im, mul_im, div_ofNat_im]
  rw [intervalIntegral.integral_congr he,
   intervalIntegral.integral_add (hph.add (hgh.const_mul _)) hzh,
   intervalIntegral.integral_add hph (hgh.const_mul _), intervalIntegral.integral_const_mul]
 have hp := vmo (by norm_num : (1 : ℝ) < 5 / 4) hT
 have hgamma := vam.vkt (by norm_num : (1 / 2 : ℝ) ≤ 5 / 4) T
 unfold vhh vcx
 norm_num only [ofReal_div, ofReal_ofNat]
 rw [hv, hh]
 unfold vbV vcx vck vam.vbp at *
 norm_num only [ofReal_div, ofReal_ofNat] at *
 linarith
lemma vlX {T : ℝ} (hT : 0 < T) (hg : vah T) :
  (N T : ℝ) = 1 + vck T / Real.pi + vbV T / Real.pi := by
 have h := viL hT hg
 rw [vcR hT hg] at h
 field_simp
 nlinarith
noncomputable def vcG (T : ℝ) : ℝ :=
 T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8
noncomputable def vaY (T : ℝ) : ℝ :=
 vam.vbp T - T / 2 * Real.log (T / 2) + T / 2 + Real.pi / 8
lemma vhA {T : ℝ} (hT : 0 < T) (hg : vah T) :
  (N T : ℝ) = vcG T + vbV T / Real.pi +
   vaY T / Real.pi := by
 rw [vlX hT hg]
 have hlog : Real.log (T / (2 * Real.pi)) = Real.log (T / 2) - Real.log Real.pi := by
  rw [show T / (2 * Real.pi) = (T / 2) / Real.pi by ring,
   Real.log_div (by positivity : T / 2 ≠ 0) Real.pi_ne_zero]
 rw [show vck T = vam.vbp T -
  T / 2 * Real.log Real.pi from rfl]
 unfold vcG vaY
 rw [hlog]
 field_simp
 ring
end vaa.vab.vae
end
section
namespace vaa.vab.vbg
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
def vns : List ℕ := [
 100000000, 42044820, 25327856, 17677669, 13374806, 10649051, 8782687, 7432544, 6415002, 5623413, 4991822, 4477374,
 4051079, 3692665, 3387551, 3125000, 2896935, 2697176, 2520913, 2364354, 2224466, 2098802, 1985364, 1882504,
 1788854, 1703269, 1624782, 1552574, 1485944, 1424290, 1367092, 1313900, 1264321, 1218011, 1174667, 1134023,
 1095841, 1059913, 1026051, 994088, 963873, 935272, 908164, 882437, 857994, 834742, 812601, 791495,
 771356, 752120, 733731, 716136, 699286, 683136, 667646, 652777, 638493, 624762, 611554, 598840,
 586594, 574791, 563409, 552427, 541824, 531581, 521682, 512110, 502850, 493886, 485207, 476797,
 468647, 460744, 453078, 445638, 438416, 431401, 424586, 417962, 411522, 405259, 399164, 393233,
 387459, 381836, 376357, 371019, 365815, 360742, 355793, 350966, 346255, 341656, 337167, 332782,
 328499, 324315, 320225, 316227, 312318, 308496, 304756, 301098, 297518, 294013, 290583, 287223,
 283933, 280710, 277553, 274458, 271426, 268453, 265538, 262680, 259876, 257126, 254428, 251781,
 249182, 246632, 244128, 241670, 239255, 236884, 234555, 232267, 230018, 227808, 225637, 223502,
 221403, 219340, 217311, 215316, 213353, 211422, 209522, 207653, 205814, 204004, 202222, 200468,
 198742, 197042, 195367, 193719, 192095, 190496, 188920, 187368, 185838, 184331, 182845, 181382,
 179939, 178516, 177114, 175731, 174368, 173023, 171698, 170390, 169100, 167828, 166572, 165334,
 164112, 162906, 161716, 160542, 159383, 158238, 157109, 155994, 154893, 153806, 152733, 151673,
 150626, 149592, 148571, 147563, 146566, 145582, 144609, 143649, 142699, 141761, 140834, 139917,
 139012, 138117, 137232, 136357, 135493, 134638, 133793, 132957, 132131, 131313, 130505, 129706,
 128916, 128134, 127361, 126596, 125839, 125090, 124350, 123617, 122892, 122175, 121465, 120762,
 120067, 119379, 118698, 118024, 117357, 116696, 116042, 115395, 114755, 114120, 113492, 112870,
 112254, 111645, 111041, 110443, 109851, 109264, 108683, 108108, 107538, 106974, 106414, 105860,
 105312, 104768, 104229, 103696, 103167, 102643, 102124, 101609, 101099, 100594, 100093, 99597,
 99105, 98618, 98135, 97656, 97181, 96710, 96244, 95781, 95323, 94868, 94418, 93971,
 93528, 93088, 92653, 92221, 91793, 91368, 90947, 90529, 90114, 89703, 89296, 88892,
 88491, 88093, 87699, 87307, 86919, 86534, 86152, 85773, 85397, 85024, 84654, 84286,
 83922, 83560, 83201, 82845, 82492, 82142, 81794, 81448, 81106, 80766, 80428, 80093,
 79761, 79431, 79103, 78778, 78455, 78135, 77817, 77501, 77188, 76877, 76568, 76261,
 75957, 75655, 75354, 75056, 74761, 74467, 74175, 73886, 73598, 73312, 73029, 72747,
 72467, 72190, 71914, 71640, 71368, 71098, 70829, 70563, 70298, 70035, 69774, 69514,
 69256, 69000, 68746, 68493, 68242, 67993, 67745, 67499, 67255, 67012, 66771, 66531,
 66293, 66056, 65821, 65587, 65355, 65124, 64895, 64667, 64441, 64216, 63992, 63770,
 63550, 63330, 63112, 62896, 62680, 62466, 62254, 62042, 61832, 61623, 61416, 61209,
 61004, 60800, 60598, 60396, 60196, 59997, 59799, 59603, 59407, 59213, 59020, 58828,
 58637, 58447, 58258, 58071, 57884, 57699, 57514, 57331, 57149, 56967, 56787, 56608,
 56430, 56253, 56076, 55901, 55727, 55554, 55382, 55210, 55040, 54870, 54702, 54534,
 54368, 54202, 54037, 53873, 53710, 53548, 53387, 53227, 53067, 52909, 52751, 52594,
 52438, 52282, 52128, 51974, 51821, 51669, 51518, 51368, 51218, 51069, 50921, 50774,
 50627, 50482, 50337, 50192, 50049, 49906, 49764, 49623, 49482, 49342, 49203, 49064,
 48927, 48790, 48653, 48517, 48382, 48248, 48114, 47981, 47849, 47717, 47586, 47456,
 47326, 47197, 47068, 46941, 46813, 46687, 46561, 46435, 46310, 46186, 46063, 45940,
 45817, 45695, 45574, 45454, 45333, 45214, 45095, 44977, 44859, 44741, 44625, 44509,
 44393, 44278, 44163, 44049, 43936, 43823, 43710, 43598, 43487, 43376, 43266, 43156,
 43046, 42937, 42829, 42721, 42614, 42507, 42400, 42294, 42189, 42084, 41979, 41875,
 41772, 41668, 41566, 41463, 41362, 41260, 41159, 41059, 40959, 40859, 40760, 40661,
 40563, 40465, 40368, 40271, 40174, 40078, 39982, 39887, 39792, 39697, 39603, 39510,
 39416, 39323, 39231, 39139, 39047, 38955, 38864, 38774, 38684, 38594, 38504, 38415,
 38326, 38238, 38150, 38062, 37975, 37888, 37802, 37715, 37630, 37544, 37459, 37374,
 37290, 37205, 37122, 37038, 36955, 36872, 36790, 36708, 36626, 36545, 36464, 36383,
 36302, 36222, 36142, 36063, 35984, 35905, 35826, 35748, 35670, 35592, 35515, 35438,
 35361, 35285, 35208, 35132, 35057, 34982, 34907, 34832, 34758, 34683, 34610, 34536,
 34463, 34390, 34317, 34245, 34172, 34100, 34029, 33958, 33886, 33816, 33745, 33675,
 33605, 33535, 33465, 33396, 33327, 33259, 33190, 33122, 33054, 32986, 32919, 32851,
 32784, 32718, 32651, 32585, 32519, 32453, 32388, 32322, 32257, 32193, 32128, 32064,
 32000]
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma vmP : vej 5 4 100000000 1 vns = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma vmN : vns.length = 625 := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma voa : vns.sum = 379526862 := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma vha :
  (379526862 : ℝ) / 100000000 ≤ vbD (5 / 4) 1 625 ∧
  vbD (5 / 4) 1 625 ≤ (379527487 : ℝ) / 100000000 := by
 have h := veI (by norm_num : 0 < 1) (by norm_num : 0 < 4)
  (by norm_num : 0 < 100000000) vmP
 simpa only [vmN, voa, Nat.cast_ofNat, Nat.reduceAdd] using h
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
def vnw : List ℕ := [
 100000000, 17677669, 6415002, 3125000, 1788854, 1134023, 771356, 552427, 411522, 316227, 249182, 200468,
 164112, 136357, 114755, 97656, 83922, 72747, 63550, 55901, 49482, 44049, 39416, 35438,
 32000, 29011, 26399, 24104, 22080, 20286, 18689, 17263, 15985, 14835, 13798, 12860,
 12008, 11234, 10527, 9882, 9290, 8747, 8247, 7786, 7361, 6967, 6603, 6264,
 5949, 5656, 5383, 5128, 4890, 4666, 4457, 4261, 4076, 3903, 3739, 3586,
 3440, 3303, 3174, 3051, 2935, 2825, 2721, 2622, 2528, 2439, 2354, 2273,
 2196, 2122, 2052, 1985, 1922, 1861, 1802, 1746, 1693, 1642, 1593, 1546,
 1501, 1457, 1416, 1376, 1338, 1301, 1265, 1231, 1198, 1167, 1136, 1107,
 1079, 1051, 1025, 1000, 975, 951, 928, 906, 885, 864, 844, 824,
 806, 787, 770, 753, 736, 720, 705, 690, 675, 661, 647, 633,
 620, 608, 595, 584, 572, 561, 550, 539, 529, 518, 509, 499,
 490, 481, 472, 463, 455, 446, 438, 431, 423, 416, 408, 401,
 394, 388, 381, 375, 369, 362, 356, 351, 345, 339, 334, 328,
 323, 318, 313, 308, 304, 299, 294, 290, 285, 281, 277, 273,
 269, 265, 261, 257, 254, 250, 246, 243, 239, 236, 233, 230,
 226, 223, 220, 217, 214, 211, 209, 206, 203, 200, 198, 195,
 193, 190, 188, 185, 183, 181, 179, 176, 174, 172, 170, 168,
 166, 164, 162, 160, 158, 156, 154, 152, 151, 149, 147, 145,
 144, 142, 140, 139, 137, 136, 134, 133, 131, 130, 128, 127,
 126, 124, 123, 121, 120, 119, 118, 116, 115, 114, 113, 112,
 110, 109, 108, 107, 106, 105, 104, 103, 102, 101, 100, 99,
 98, 97, 96, 95, 94, 93, 92, 91, 90, 90, 89, 88,
 87, 86, 85, 85, 84, 83, 82, 81, 81, 80, 79, 79,
 78, 77, 76, 76, 75, 74, 74, 73, 72, 72, 71, 71,
 70, 69, 69, 68, 68, 67, 66, 66, 65, 65, 64, 64,
 63, 63, 62, 62, 61, 61, 60, 60, 59, 59, 58, 58,
 57, 57, 56, 56, 55, 55, 55, 54, 54, 53, 53, 52,
 52, 52, 51, 51, 50, 50, 50, 49, 49, 49, 48, 48,
 47, 47, 47, 46, 46, 46, 45, 45, 45, 44, 44, 44,
 43, 43, 43, 43, 42, 42, 42, 41, 41, 41, 40, 40,
 40, 40, 39, 39, 39, 39, 38, 38, 38, 37, 37, 37,
 37, 36, 36, 36, 36, 35, 35, 35, 35, 35, 34, 34,
 34, 34, 33, 33, 33, 33, 33, 32, 32, 32, 32, 32,
 31, 31, 31, 31, 31, 30, 30, 30, 30, 30, 29, 29,
 29, 29, 29, 29, 28, 28, 28, 28, 28, 27, 27, 27,
 27, 27, 27, 27, 26, 26, 26, 26, 26, 26, 25, 25,
 25, 25, 25, 25, 25, 24, 24, 24, 24, 24, 24, 24,
 23, 23, 23, 23, 23, 23, 23, 23, 22, 22, 22, 22,
 22, 22, 22, 22, 21, 21, 21, 21, 21, 21, 21, 21,
 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 19, 19,
 19, 19, 19, 19, 19, 19, 19, 19, 18, 18, 18, 18,
 18, 18, 18, 18, 18, 18, 17, 17, 17, 17, 17, 17,
 17, 17, 17, 17, 17, 17, 16, 16, 16, 16, 16, 16,
 16, 16, 16, 16, 16, 16, 15, 15, 15, 15, 15, 15,
 15, 15, 15, 15, 15, 15, 15, 15, 14, 14, 14, 14,
 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 13,
 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
 13, 13, 13, 13, 12, 12, 12, 12, 12, 12, 12, 12,
 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 11, 11,
 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11,
 11, 11, 11, 11, 11, 11, 11, 10, 10, 10, 10, 10,
 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10,
 10]
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma vmS : vej 5 2 100000000 1 vnw = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma vmK : vnw.length = 625 := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma voc : vnw.sum = 134144158 := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma vhm :
  (134144158 : ℝ) / 100000000 ≤ vbD (5 / 2) 1 625 ∧
  vbD (5 / 2) 1 625 ≤ (134144783 : ℝ) / 100000000 := by
 have h := veI (by norm_num : 0 < 1) (by norm_num : 0 < 2)
  (by norm_num : 0 < 100000000) vmS
 simpa only [vmK, voc, Nat.cast_ofNat, Nat.reduceAdd] using h
end vaa.vab.vbg
end
section
namespace vaa.vab
open vbg
private lemma vjK :
  ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ ≤ (459527487 : ℝ) / 100000000 := by
 have ht := vcW (σ := 5 / 4) (by norm_num) (N := 625) (by norm_num)
 have hr := vex (n := 625) (p := 1) (k := 4) (D := 5) (b := 1)
  (by norm_num) (by norm_num) (by norm_num) (by norm_num)
 norm_num only [Nat.cast_ofNat] at hr
 rw [show (1 : ℝ) - 5 / 4 = -(1 : ℝ) / 4 by norm_num,
  show (5 / 4 : ℝ) - 1 = 1 / 4 by norm_num] at ht
 linarith [vha.2]
private lemma vke :
  (459486862 : ℝ) / 100000000 ≤ ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ := by
 have ht := vlF (σ := 5 / 4) (by norm_num) 625
 have hr := vlO (n := 626) (p := 1) (k := 4) (D := 10000) (b := 1999)
  (by norm_num) (by norm_num) (by norm_num) (by norm_num)
 norm_num only [Nat.cast_ofNat] at hr
 rw [show (1 : ℝ) - 5 / 4 = -(1 : ℝ) / 4 by norm_num,
  show (5 / 4 : ℝ) - 1 = 1 / 4 by norm_num] at ht
 norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at ht
 linarith [vha.1]
private lemma vgX :
  (134144158 : ℝ) / 100000000 ≤ ‖riemannZeta ((5 / 2 : ℝ) : ℂ)‖ :=
 vhm.1.trans (vjZ (by norm_num) 625)
private lemma vnB :
  ‖riemannZeta ((5 / 2 : ℝ) : ℂ)‖ ≤
   (134144783 : ℝ) / 100000000 + 2 / 46875 := by
 have ht := vcW (σ := 5 / 2) (by norm_num) (N := 625) (by norm_num)
 have hr := vex (n := 625) (p := 3) (k := 2) (D := 15625) (b := 1)
  (by norm_num) (by norm_num) (by norm_num) (by norm_num)
 norm_num only [Nat.cast_ofNat] at hr
 rw [show (1 : ℝ) - 5 / 2 = -(3 : ℝ) / 2 by norm_num,
  show (5 / 2 : ℝ) - 1 = 3 / 2 by norm_num] at ht
 linarith [vhm.2]
lemma vhM :
  ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ < (23 / 5 : ℝ) := by
 linarith [vjK]
lemma veA :
  (3.425 : ℝ) <
   ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ / ‖riemannZeta ((5 / 2 : ℝ) : ℂ)‖ ∧
  ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ / ‖riemannZeta ((5 / 2 : ℝ) : ℂ)‖ < 3.426 := by
 have hpos : 0 < ‖riemannZeta ((5 / 2 : ℝ) : ℂ)‖ := by linarith [vgX]
 constructor
 ·rw [lt_div_iff₀ hpos]
  linarith [vke, vnB]
 ·rw [div_lt_iff₀ hpos]
  linarith [vjK, vgX]
lemma vdJ (T : ℝ) :
  (1 : ℝ) / 3.426 ≤ ‖riemannZeta (((5 / 4 : ℝ) : ℂ) + T * Complex.I)‖ := by
 have h1 : 0 < ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ := by linarith [vke]
 have h2 : 0 < ‖riemannZeta ((5 / 2 : ℝ) : ℂ)‖ := by linarith [vgX]
 have hratio := (div_lt_iff₀ h2).mp veA.2
 have hc : (1 : ℝ) / 3.426 ≤
   ‖riemannZeta ((5 / 2 : ℝ) : ℂ)‖ / ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ := by
  rw [le_div_iff₀ h1]
  linarith
 exact hc.trans (vdI T)
end vaa.vab
end
section
open Complex Filter MeasureTheory
open scoped Topology Interval
namespace vaa.vab.viC
noncomputable def vcJ (s : ℂ) : ℂ :=
 ∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-s))
lemma vhJ {z : ℂ} (hz : ‖z‖ < 1) :
  ‖-Complex.log (1 - z)‖ ≤ -Real.log (1 - ‖z‖) := by
 apply (Complex.hasSum_taylorSeries_neg_log' hz).norm_le_of_bounded
  (Real.hasSum_pow_div_log_of_abs_lt_one (by simpa using hz))
 intro n
 have hd : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
  simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (n + 1)
 simp only [norm_div, norm_pow, hd, le_refl]
lemma vjl {σ : ℝ} (hσ : 1 < σ) :
  vcJ (σ : ℂ) =
   ((∑' p : Nat.Primes, -Real.log (1 - (p : ℝ) ^ (-σ)) : ℝ) : ℂ) := by
 rw [vcJ, Complex.ofReal_tsum]
 apply tsum_congr
 intro p
 have hp : 1 < (p : ℝ) := by exact_mod_cast p.prop.one_lt
 have hp0 : 0 < (p : ℝ) := by linarith
 have hpow : (p : ℂ) ^ (-(σ : ℂ)) = (((p : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  simpa only [Complex.ofReal_neg, Complex.ofReal_natCast] using
   (Complex.ofReal_cpow hp0.le (-σ)).symm
 have hlt : (p : ℝ) ^ (-σ) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
 rw [hpow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
  ← Complex.ofReal_log (by linarith)]
 simp
lemma vkU {s : ℂ} (hs : 1 < s.re) :
  ‖vcJ s‖ ≤ Real.log ‖riemannZeta (s.re : ℂ)‖ := by
 let r : Nat.Primes → ℝ := fun p => (p : ℝ) ^ (-s.re)
 have hrs : Summable r := Nat.Primes.summable_rpow.mpr (by linarith)
 have hlogs : Summable (fun p => -Real.log (1 - r p)) := by
  simpa only [sub_eq_add_neg] using
   (Real.summable_log_one_add_of_summable hrs.neg).neg
 have he : Real.log ‖riemannZeta (s.re : ℂ)‖ =
   ∑' p : Nat.Primes, -Real.log (1 - r p) := by
  rw [← riemannZeta_eulerProduct_exp_log (by simpa using hs),
   show (∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s.re : ℂ)))) =
    vcJ (s.re : ℂ) from rfl,
   vjl hs, Complex.norm_exp, Complex.ofReal_re, Real.log_exp]
 rw [he]
 apply tsum_of_norm_bounded hlogs.hasSum
 intro p
 have hp : 1 < (p : ℝ) := by exact_mod_cast p.prop.one_lt
 have hp0 : 0 < (p : ℝ) := by linarith
 have hn : ‖(p : ℂ) ^ (-s)‖ = r p := by
  simpa only [r, Complex.neg_re, Complex.ofReal_natCast] using
   Complex.norm_cpow_eq_rpow_re_of_pos hp0 (-s)
 have hlt : r p < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
 simpa only [hn] using vhJ (z := (p : ℂ) ^ (-s)) (hn ▸ hlt)
lemma vdZ :
  Real.log ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ < Real.pi / 2 := by
 have he := Real.sum_le_exp_of_nonneg (x := (31 / 20 : ℝ)) (by norm_num) 6
 norm_num [Finset.sum_range_succ] at he
 have hπ : (31 / 20 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_d2]
 have hz : 0 < ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ :=
  norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
 apply (Real.log_lt_iff_lt_exp hz).mpr
 exact vhM.trans
  ((show (23 / 5 : ℝ) < Real.exp (31 / 20) by linarith).trans
   (Real.exp_lt_exp.mpr hπ))
lemma vfv (t : ℝ) :
  0 < (riemannZeta ((5 / 4 : ℂ) + t * I)).re := by
 let s : ℂ := (5 / 4 : ℂ) + t * I
 have hs : 1 < s.re := by simp [s]; norm_num
 have hb : ‖vcJ s‖ < Real.pi / 2 :=
  (vkU hs).trans_lt (by simpa [s] using vdZ)
 have hi : |(vcJ s).im| < Real.pi / 2 :=
  (Complex.abs_im_le_norm _).trans_lt hb
 have hc : 0 < Real.cos (vcJ s).im := Real.cos_pos_of_mem_Ioo (abs_lt.mp hi)
 change 0 < (riemannZeta s).re
 rw [← riemannZeta_eulerProduct_exp_log hs, show
  (∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-s))) = vcJ s from rfl,
  Complex.exp_re]
 exact mul_pos (Real.exp_pos _) hc
private lemma vjo (t : ℝ) : (5 / 4 : ℂ) + t * I ≠ 1 := by
 intro h
 have := congrArg Complex.re h
 norm_num at this
private lemma vlT (t : ℝ) : riemannZeta ((5 / 4 : ℂ) + t * I) ≠ 0 :=
 riemannZeta_ne_zero_of_one_lt_re (by simp; norm_num)
set_option maxHeartbeats 1000000 in
lemma viz (t : ℝ) :
  HasDerivAt (fun u : ℝ => Complex.log (riemannZeta ((5 / 4 : ℂ) + u * I)))
   (logDeriv riemannZeta ((5 / 4 : ℂ) + t * I) * I) t := by
 have hl : HasDerivAt (fun u : ℝ => (5 / 4 : ℂ) + u * I) I t := by
  convert ((Complex.ofRealCLM.hasFDerivAt).hasDerivAt.mul_const I).const_add (5 / 4) using 1 <;> (try simp)
  all_goals try rfl
 have hz := (differentiableAt_riemannZeta (vjo t)).hasDerivAt.scomp t hl
 have h := hz.clog_real (Complex.mem_slitPlane_iff.mpr (Or.inl (vfv t)))
 simp only [Function.comp_def, smul_eq_mul] at h
 convert h using 1 <;> (try simp only [logDeriv_apply]) <;> (try ring)
 all_goals try rfl
lemma veQ :
  Continuous (fun t : ℝ => (logDeriv riemannZeta ((5 / 4 : ℂ) + t * I)).re) := by
 rw [continuous_iff_continuousAt]
 intro t
 have hl : ContinuousAt (fun u : ℝ => (5 / 4 : ℂ) + u * I) t := by fun_prop
 have ha : AnalyticAt ℂ riemannZeta ((5 / 4 : ℂ) + t * I) := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards [eventually_ne_nhds (vjo t)] with z hz
  exact differentiableAt_riemannZeta hz
 have hc : ContinuousAt (fun u : ℝ =>
   deriv riemannZeta ((5 / 4 : ℂ) + u * I) /
    riemannZeta ((5 / 4 : ℂ) + u * I)) t :=
  ContinuousAt.comp (g := fun s : ℂ => deriv riemannZeta s / riemannZeta s)
   (f := fun u : ℝ => (5 / 4 : ℂ) + u * I)
   (ha.deriv.continuousAt.div ha.continuousAt (vlT t)) hl
 simpa only [logDeriv_apply, Function.comp_def] using Complex.continuous_re.continuousAt.comp hc
lemma vgW (T : ℝ) :
  (∫ t in (0 : ℝ)..T, (logDeriv riemannZeta ((5 / 4 : ℂ) + t * I)).re) =
   (riemannZeta ((5 / 4 : ℂ) + T * I)).arg := by
 have hd (t : ℝ) :
   HasDerivAt (fun u : ℝ => (Complex.log (riemannZeta ((5 / 4 : ℂ) + u * I))).im)
    (logDeriv riemannZeta ((5 / 4 : ℂ) + t * I)).re t := by
  convert! Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (viz t) using 1 <;>
   simp [Function.comp_def]
 have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
  (fun t _ => hd t) (veQ.intervalIntegrable 0 T)
 rw [he]
 simp only [Complex.log_im, Complex.ofReal_zero, zero_mul, add_zero]
 have hs := vjl (σ := (5 / 4 : ℝ)) (by norm_num)
 have he' := riemannZeta_eulerProduct_exp_log (s := ((5 / 4 : ℝ) : ℂ)) (by norm_num)
 change Complex.exp (vcJ ((5 / 4 : ℝ) : ℂ)) = _ at he'
 rw [hs] at he'
 norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at he'
 have harg : (riemannZeta (5 / 4 : ℂ)).arg = 0 := by
  rw [← he', ← Complex.ofReal_exp]
  exact Complex.arg_ofReal_of_nonneg (Real.exp_nonneg _)
 rw [harg, sub_zero]
lemma vhx (T : ℝ) :
  |∫ t in (0 : ℝ)..T, (logDeriv riemannZeta ((5 / 4 : ℂ) + t * I)).re| ≤ Real.pi / 2 := by
 rw [vgW]
 exact (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (vfv T))).le
end vaa.vab.viC
end
section
open Complex Filter Topology Set MeasureTheory
namespace vjG
lemma viM {y : ℝ} (hy : 0 < y) :
  HasSum (fun k : ℕ ↦ 1 / ((k : ℝ) + y) - 1 / ((k : ℝ) + 1 + y)) (1 / y) := by
 have hpos : ∀ k : ℕ, 0 ≤ 1 / ((k : ℝ) + y) - 1 / ((k : ℝ) + 1 + y) := by
  intro k
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [sub_nonneg]; apply one_div_le_one_div_of_le (by positivity); linarith
 rw [hasSum_iff_tendsto_nat_of_nonneg hpos]
 have e : ∀ n : ℕ, ∑ k ∈ Finset.range n, (1 / ((k : ℝ) + y) - 1 / ((k : ℝ) + 1 + y))
   = 1 / y - 1 / ((n : ℝ) + y) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
 simp_rw [e]
 have : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + y)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ y tendsto_natCast_atTop_atTop)
 simpa using tendsto_const_nhds.sub this
lemma vjx {z₁ z₂ : ℂ} (h1 : 0 < z₁.re) (h2 : 0 < z₂.re) (him : z₁.im = z₂.im)
    (hy : 2 ≤ z₁.im) :
    ‖Complex.digamma z₁ - Complex.digamma z₂‖ ≤ ‖z₁ - z₂‖ * (4 / z₁.im) := by
  set y := z₁.im with hy_def
  have hy0 : 0 < y := by linarith
  have hn1 : ∀ n : ℕ, z₁ ≠ -n := fun n h ↦ by
    have := congrArg Complex.re h; simp at this; have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hn2 : ∀ n : ℕ, z₂ ≠ -n := fun n h ↦ by
    have := congrArg Complex.re h; simp at this; have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hs1 := vac.vau hn1
  have hs2 := vac.vau hn2
  have hdiff : Complex.digamma z₁ - Complex.digamma z₂
      = ∑' k, (vac.vaf z₁ k - vac.vaf z₂ k) := by
    rw [vac.vbc h1, vac.vbc h2,
      vac.gaussSum, vac.gaussSum, hs1.tsum_sub hs2]
    ring
  have hk : ∀ k : ℕ, ‖vac.vaf z₁ k - vac.vaf z₂ k‖
      ≤ ‖z₁ - z₂‖ * 2 * (1 / ((k : ℝ) + (y - 1)) - 1 / ((k : ℝ) + 1 + (y - 1))) := by
    intro k
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hz1 : ((k : ℂ) + z₁) ≠ 0 := fun h ↦ hn1 k (by linear_combination h)
    have hz2 : ((k : ℂ) + z₂) ≠ 0 := fun h ↦ hn2 k (by linear_combination h)
    have e : vac.vaf z₁ k - vac.vaf z₂ k
        = (z₁ - z₂) / (((k : ℂ) + z₁) * ((k : ℂ) + z₂)) := by
      simp only [vac.vaf]; field_simp; ring
    have hnorm : ∀ z : ℂ, 0 < z.re → z.im = y → (k : ℝ) ^ 2 + y ^ 2 ≤ ‖(k : ℂ) + z‖ ^ 2 := by
      intro z hz hzi
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.natCast_re, Complex.add_im, Complex.natCast_im, zero_add, hzi]
      nlinarith
    have hp1 := hnorm z₁ h1 rfl
    have hp2 := hnorm z₂ h2 him.symm
    have hprod : ((k : ℝ) + y) ^ 2 / 2 ≤ ‖((k : ℂ) + z₁) * ((k : ℂ) + z₂)‖ := by
      rw [norm_mul]
      have ha := norm_nonneg ((k : ℂ) + z₁)
      have hb := norm_nonneg ((k : ℂ) + z₂)
      have : ((k : ℝ) + y) ^ 2 / 2 ≤ (k : ℝ) ^ 2 + y ^ 2 := by nlinarith [sq_nonneg ((k:ℝ) - y)]
      have hc1 : Real.sqrt ((k : ℝ) ^ 2 + y ^ 2) ≤ ‖(k : ℂ) + z₁‖ := by
        have := Real.sqrt_le_sqrt hp1; rwa [Real.sqrt_sq ha] at this
      have hc2 : Real.sqrt ((k : ℝ) ^ 2 + y ^ 2) ≤ ‖(k : ℂ) + z₂‖ := by
        have := Real.sqrt_le_sqrt hp2; rwa [Real.sqrt_sq hb] at this
      have hmm := mul_le_mul hc1 hc2 (Real.sqrt_nonneg _) ha
      rw [Real.mul_self_sqrt (by positivity)] at hmm
      linarith
    have htel : 2 / ((k : ℝ) + y) ^ 2 ≤ 2 * (1 / ((k : ℝ) + (y - 1)) - 1 / ((k : ℝ) + 1 + (y - 1))) := by
      have hky : 0 < (k : ℝ) + (y - 1) := by linarith
      have hky' : 0 < (k : ℝ) + y := by linarith
      have h3 : 1 / ((k : ℝ) + y) ^ 2 ≤ 1 / ((k : ℝ) + (y - 1)) - 1 / ((k : ℝ) + 1 + (y - 1)) := by
        rw [show (k : ℝ) + 1 + (y - 1) = (k : ℝ) + y by ring, div_sub_div _ _ hky.ne' hky'.ne',
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have e2 : 2 / ((k : ℝ) + y) ^ 2 = 2 * (1 / ((k : ℝ) + y) ^ 2) := by ring
      rw [e2]; linarith
    rw [e, norm_div]
    calc ‖z₁ - z₂‖ / ‖((k : ℂ) + z₁) * ((k : ℂ) + z₂)‖
        ≤ ‖z₁ - z₂‖ / (((k : ℝ) + y) ^ 2 / 2) :=
          div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hprod
      _ = ‖z₁ - z₂‖ * (2 / ((k : ℝ) + y) ^ 2) := by field_simp
      _ ≤ ‖z₁ - z₂‖ * (2 * (1 / ((k : ℝ) + (y - 1)) - 1 / ((k : ℝ) + 1 + (y - 1)))) :=
          mul_le_mul_of_nonneg_left htel (norm_nonneg _)
      _ = _ := by ring
  have htele := (viM (y := y - 1) (by linarith)).mul_left (‖z₁ - z₂‖ * 2)
  have hsumn : Summable fun k : ℕ ↦ ‖vac.vaf z₁ k - vac.vaf z₂ k‖ :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hk htele.summable
  rw [hdiff]
  calc _ ≤ ∑' k, ‖vac.vaf z₁ k - vac.vaf z₂ k‖ := norm_tsum_le_tsum_norm hsumn
    _ ≤ ‖z₁ - z₂‖ * 2 * (1 / (y - 1)) := by
        rw [← htele.tsum_eq]; exact Summable.tsum_le_tsum hk hsumn htele.summable
    _ ≤ ‖z₁ - z₂‖ * (4 / y) := by
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        have : 1 / (y - 1) ≤ 2 / y := by rw [div_le_div_iff₀ (by linarith) hy0]; nlinarith
        have e : 4 / y = 2 * (2 / y) := by ring
        rw [e]; linarith
end vjG
end
section
noncomputable section
open Complex Real
open scoped Topology
namespace vaa.vab.vfH
lemma vgw (s : ℂ) :
  logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s = -(Real.log Real.pi : ℂ) / 2 := by
 have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
 have hf : HasDerivAt (fun z : ℂ => -z / 2) (-1 / 2 : ℂ) s := by
  simpa using ((hasDerivAt_id s).neg.div_const 2)
 have hg : HasDerivAt (fun y : ℂ => (Real.pi : ℂ) ^ y)
   ((Real.pi : ℂ) ^ (-s / 2) * Complex.log (Real.pi : ℂ)) (-s / 2) :=
  (hasStrictDerivAt_const_cpow (Or.inl hπ)).hasDerivAt
 have hd : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
   ((Real.pi : ℂ) ^ (-s / 2) * Complex.log (Real.pi : ℂ) * (-1 / 2)) s := by
  have := hg.comp s hf
  exact this
 have hval : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero hπ]; exact Complex.exp_ne_zero _
 rw [logDeriv_apply, hd.deriv, Complex.ofReal_log Real.pi_pos.le]
 field_simp
lemma vff (s : ℂ) :
  (logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s).im = 0 := by
 rw [vgw]
 simp
lemma vew {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
  logDeriv completedRiemannZeta (1 - s) = -logDeriv completedRiemannZeta s := by
 have hfe : completedRiemannZeta ∘ (fun z : ℂ => 1 - z) = completedRiemannZeta := by
  funext z; exact completedRiemannZeta_one_sub z
 have h1s0 : (1 : ℂ) - s ≠ 0 := fun h => hs1 (by linear_combination -h)
 have h1s1 : (1 : ℂ) - s ≠ 1 := fun h => hs0 (by linear_combination -h)
 have hf : DifferentiableAt ℂ completedRiemannZeta (1 - s) :=
  differentiableAt_completedZeta h1s0 h1s1
 have hg : DifferentiableAt ℂ (fun z : ℂ => 1 - z) s := differentiableAt_id.const_sub 1
 have hderiv_g : deriv (fun z : ℂ => 1 - z) s = -1 :=
  ((hasDerivAt_id s).const_sub 1).deriv
 have hcomp := logDeriv_comp hf hg
 rw [hfe, hderiv_g] at hcomp
 rw [hcomp]; ring
lemma vfF (s : ℂ) :
  logDeriv completedRiemannZeta (starRingEnd ℂ s)
   = starRingEnd ℂ (logDeriv completedRiemannZeta s) := by
 have hf : (starRingEnd ℂ ∘ completedRiemannZeta ∘ starRingEnd ℂ) =
   completedRiemannZeta := by
  funext w
  simp [Function.comp, completedRiemannZeta_conj]
 have hd := deriv_conj_conj (f := completedRiemannZeta)
 rw [hf] at hd
 have h2 : deriv completedRiemannZeta (starRingEnd ℂ s) =
   starRingEnd ℂ (deriv completedRiemannZeta s) := by
  rw [congrFun hd (starRingEnd ℂ s)]
  simp [Function.comp]
 rw [logDeriv_apply, logDeriv_apply, h2, completedRiemannZeta_conj, map_div₀]
lemma vdM (σ T : ℝ) (hT : T ≠ 0) :
  (logDeriv completedRiemannZeta ((1 - σ : ℝ) + T * Complex.I)).im
   = (logDeriv completedRiemannZeta ((σ : ℝ) + T * Complex.I)).im := by
 set s : ℂ := (σ : ℝ) + T * Complex.I with hs_def
 have hsim : s.im ≠ 0 := by rw [hs_def]; simp [hT]
 have hs0 : s ≠ 0 := fun h => hsim (by rw [h]; rfl)
 have hs1 : s ≠ 1 := by
  intro h; apply hsim; rw [h]; simp
 have hrewrite : ((1 - σ : ℝ) + T * Complex.I) = 1 - starRingEnd ℂ s := by
  rw [hs_def]; simp only [Complex.conj_ofReal, map_add, map_mul, Complex.conj_I]
  push_cast; ring
 rw [hrewrite]
 have hcs0 : starRingEnd ℂ s ≠ 0 := by rw [ne_eq, map_eq_zero]; exact hs0
 have hcs1 : starRingEnd ℂ s ≠ 1 := by
  intro h; apply hs1
  have := congrArg (starRingEnd ℂ) h
  rwa [Complex.conj_conj, map_one] at this
 rw [vew hcs0 hcs1, vfF s]
 simp [Complex.neg_im, Complex.conj_im]
lemma vdA {σ T : ℝ} (hT : T ≠ 0)
  (hζ : riemannZeta ((σ : ℂ) + T * Complex.I) ≠ 0) :
  (logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im
   = (logDeriv completedRiemannZeta ((σ : ℂ) + T * Complex.I)).im
    - (logDeriv (fun z : ℂ => Complex.Gamma (z / 2))
      ((σ : ℂ) + T * Complex.I)).im := by
 set s : ℂ := (σ : ℂ) + T * Complex.I with hs_def
 have hsim : s.im ≠ 0 := by rw [hs_def]; simp [hT]
 have hs0 : s ≠ 0 := fun h => hsim (by rw [h]; exact Complex.zero_im)
 have hs1 : s ≠ 1 := fun h => hsim (by rw [h]; exact Complex.one_im)
 have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
 have hhalf : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
  intro m h
  apply hsim
  have him := congrArg Complex.im h
  simp only [Complex.div_ofNat_im, Complex.neg_im, Complex.natCast_im,
   neg_zero] at him
  linarith
 have hP_diff : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s := by
  have hf : HasDerivAt (fun z : ℂ => -z / 2) (-1 / 2 : ℂ) s := by
   simpa using ((hasDerivAt_id s).neg.div_const 2)
  have hg : HasDerivAt (fun y : ℂ => (Real.pi : ℂ) ^ y)
    ((Real.pi : ℂ) ^ (-s / 2) * Complex.log (Real.pi : ℂ)) (-s / 2) :=
   (hasStrictDerivAt_const_cpow (Or.inl hπ)).hasDerivAt
  have hd : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
    ((Real.pi : ℂ) ^ (-s / 2) * Complex.log (Real.pi : ℂ) * (-1 / 2)) s := by
   exact hf.const_cpow (Or.inl hπ)
  exact hd.differentiableAt
 have hG_diff : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s := by
  have h1 : DifferentiableAt ℂ Complex.Gamma (s / 2) :=
   Complex.differentiableAt_Gamma _ hhalf
  have h2 : DifferentiableAt ℂ (fun z : ℂ => z / 2) s :=
   differentiableAt_id.div_const 2
  exact DifferentiableAt.comp (g := Complex.Gamma) (f := fun z : ℂ => z / 2) s h1 h2
 have hP_ne : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero hπ]
  exact Complex.exp_ne_zero _
 have hG_ne : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero hhalf
 have hΛ_ne : completedRiemannZeta s ≠ 0 := by
  intro h
  apply hζ
  rw [riemannZeta_def_of_ne_zero hs0, h, zero_div]
 have hΛ_diff : DifferentiableAt ℂ completedRiemannZeta s :=
  differentiableAt_completedZeta hs0 hs1
 have hPG_ne : (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) ≠ 0 :=
  mul_ne_zero hP_ne hG_ne
 have hPG_diff : DifferentiableAt ℂ
   (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)) s :=
  hP_diff.mul hG_diff
 have hopen : IsOpen {z : ℂ | z.im ≠ 0} := isOpen_ne.preimage Complex.continuous_im
 have hEq : riemannZeta =ᶠ[nhds s]
   fun z => completedRiemannZeta z
    / ((Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)) := by
  filter_upwards [hopen.mem_nhds hsim] with z hz
  have hz0 : z ≠ 0 := fun h => hz (by rw [h]; exact Complex.zero_im)
  rw [riemannZeta_def_of_ne_zero hz0, Complex.Gammaℝ_def]
 have hlog_eq : logDeriv riemannZeta s
   = logDeriv (fun z => completedRiemannZeta z
     / ((Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2))) s := by
  rw [logDeriv_apply, logDeriv_apply, hEq.deriv_eq, hEq.self_of_nhds]
 have hdiv := logDeriv_div (f := completedRiemannZeta)
   (g := fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2))
   s hΛ_ne hPG_ne hΛ_diff hPG_diff
 have hmul := logDeriv_mul (f := fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
   (g := fun z : ℂ => Complex.Gamma (z / 2))
   s hP_ne hG_ne hP_diff hG_diff
 try simp only [Pi.div_def, Pi.mul_def] at hdiv hmul
 have hkey : logDeriv riemannZeta s
   = logDeriv completedRiemannZeta s
    - (logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s
      + logDeriv (fun z : ℂ => Complex.Gamma (z / 2)) s) := by
  rw [hlog_eq, hdiv, hmul]
 rw [hkey, Complex.sub_im, Complex.add_im, vff s]
 ring
lemma veR {T : ℝ} (hT : T ≠ 0) (σ : ℝ)
  (hζ : riemannZeta ((σ : ℂ) + T * Complex.I) ≠ 0)
  (hζ' : riemannZeta (((1 - σ : ℝ) : ℂ) + T * Complex.I) ≠ 0) :
  (logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im
    - (logDeriv riemannZeta (((1 - σ : ℝ) : ℂ) + T * Complex.I)).im
   = (logDeriv (fun z : ℂ => Complex.Gamma (z / 2))
      (((1 - σ : ℝ) : ℂ) + T * Complex.I)).im
    - (logDeriv (fun z : ℂ => Complex.Gamma (z / 2))
      ((σ : ℂ) + T * Complex.I)).im := by
 have h1 := vdA hT hζ
 have h2 := vdA hT hζ'
 have hrefl := vdM σ T hT
 linarith
lemma veV {p : ℂ} (hp : p.im ≠ 0) :
  logDeriv (fun s : ℂ => Complex.Gamma (s / 2)) p
   = (1 / 2 : ℂ) * Complex.digamma (p / 2) := by
 have hp2ne : ∀ m : ℕ, (p / 2) ≠ -(m : ℂ) := by
  intro m heq
  apply hp
  have h2 : p = (2 : ℂ) * (p / 2) := by ring
  rw [heq] at h2
  rw [h2]; simp
 have hf : DifferentiableAt ℂ Complex.Gamma (p / 2) :=
  Complex.differentiableAt_Gamma _ hp2ne
 have hg : DifferentiableAt ℂ (fun s : ℂ => s / 2) p := by fun_prop
 have hcomp :
   logDeriv (Complex.Gamma ∘ (fun s : ℂ => s / 2)) p
    = logDeriv Complex.Gamma (p / 2) * deriv (fun s : ℂ => s / 2) p :=
  logDeriv_comp hf hg
 have hderiv2 : deriv (fun s : ℂ => s / 2) p = 1 / 2 := by
  rw [deriv_div_const]; simp
 have hcompeq : (Complex.Gamma ∘ (fun s : ℂ => s / 2)) = (fun s => Complex.Gamma (s / 2)) :=
  rfl
 rw [← hcompeq, hcomp, hderiv2, ← Complex.digamma_def]
 ring
lemma vdX {T : ℝ} (hT : T ≠ 0) (σ : ℝ)
  (hζ : riemannZeta ((σ : ℂ) + T * Complex.I) ≠ 0)
  (hζ' : riemannZeta (((1 - σ : ℝ) : ℂ) + T * Complex.I) ≠ 0) :
  (logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im
    - (logDeriv riemannZeta (((1 - σ : ℝ) : ℂ) + T * Complex.I)).im
   = (1 / 2 : ℝ) *
    (Complex.digamma ((((1 - σ : ℝ) : ℂ) + T * Complex.I) / 2)
     - Complex.digamma (((σ : ℂ) + T * Complex.I) / 2)).im := by
 rw [veR hT σ hζ hζ',
  veV (by simpa using hT),
  veV (by simpa using hT)]
 simp only [Complex.mul_im, Complex.div_ofNat_re, Complex.one_re,
  Complex.div_ofNat_im, Complex.one_im, Complex.sub_im]
 ring
end vaa.vab.vfH
end
end
section
open Complex Filter Set MeasureTheory
open scoped Real Topology Interval
namespace vaa.vab.vcf
lemma vdV {z₁ z₂ : ℂ}
  (h1 : 1 ≤ z₁.re) (h2 : 1 ≤ z₂.re) :
  ‖Complex.digamma z₁ - Complex.digamma z₂‖ ≤ 2 * ‖z₁ - z₂‖ := by
 have hn1 := vac.vat
  (vac.van.mpr (by linarith : 0 < z₁.re))
 have hn2 := vac.vat
  (vac.van.mpr (by linarith : 0 < z₂.re))
 have hs1 := vac.vau hn1
 have hs2 := vac.vau hn2
 have hdiff : Complex.digamma z₁ - Complex.digamma z₂ =
   ∑' k, (vac.vaf z₁ k - vac.vaf z₂ k) := by
  rw [vac.vbc (by linarith),
   vac.vbc (by linarith),
   vac.gaussSum, vac.gaussSum, hs1.tsum_sub hs2]
  ring
 have hk : ∀ k : ℕ, ‖vac.vaf z₁ k - vac.vaf z₂ k‖ ≤
   ‖z₁ - z₂‖ * (2 * (((k : ℝ) + 1) * ((k : ℝ) + 1 + 1))⁻¹) := by
  intro k
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  have hz1 : ((k : ℂ) + z₁) ≠ 0 := fun h => hn1 k (by linear_combination h)
  have hz2 : ((k : ℂ) + z₂) ≠ 0 := fun h => hn2 k (by linear_combination h)
  have he : vac.vaf z₁ k - vac.vaf z₂ k =
    (z₁ - z₂) / (((k : ℂ) + z₁) * ((k : ℂ) + z₂)) := by
   simp only [vac.vaf]
   field_simp
   ring
  have hnz1 : (k : ℝ) + 1 ≤ ‖(k : ℂ) + z₁‖ := by
   have hh := Complex.re_le_norm ((k : ℂ) + z₁)
   simp only [add_re, natCast_re] at hh
   linarith
  have hnz2 : (k : ℝ) + 1 ≤ ‖(k : ℂ) + z₂‖ := by
   have hh := Complex.re_le_norm ((k : ℂ) + z₂)
   simp only [add_re, natCast_re] at hh
   linarith
  have hp : ((k : ℝ) + 1) ^ 2 ≤ ‖((k : ℂ) + z₁) * ((k : ℂ) + z₂)‖ := by
   rw [norm_mul, pow_two]
   exact mul_le_mul hnz1 hnz2 hk1.le (norm_nonneg _)
  have hc : 1 / ((k : ℝ) + 1) ^ 2 ≤
    2 * (((k : ℝ) + 1) * ((k : ℝ) + 1 + 1))⁻¹ := by
   change 1 / ((k : ℝ) + 1) ^ 2 ≤
    2 / (((k : ℝ) + 1) * ((k : ℝ) + 1 + 1))
   rw [div_le_div_iff₀ (sq_pos_of_pos hk1) (by positivity)]
   nlinarith
  rw [he, norm_div]
  calc
   _ ≤ ‖z₁ - z₂‖ / ((k : ℝ) + 1) ^ 2 :=
    div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hk1) hp
   _ = ‖z₁ - z₂‖ * (1 / ((k : ℝ) + 1) ^ 2) := by ring
   _ ≤ _ := mul_le_mul_of_nonneg_left hc (norm_nonneg _)
 have htele := vac.vdC (t := 1) le_rfl ‖z₁ - z₂‖
 have hsumn : Summable (fun k : ℕ =>
   ‖vac.vaf z₁ k - vac.vaf z₂ k‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hk htele.summable
 rw [hdiff]
 calc
  _ ≤ ∑' k, ‖vac.vaf z₁ k - vac.vaf z₂ k‖ :=
   norm_tsum_le_tsum_norm hsumn
  _ ≤ ‖z₁ - z₂‖ * (2 * (1 : ℝ)⁻¹) := by
   rw [← htele.tsum_eq]
   exact Summable.tsum_le_tsum hk hsumn htele.summable
  _ = _ := by ring
lemma vcb {z : ℂ} (hz : z.im ≠ 0) :
  Complex.digamma z = Complex.digamma (z + 2) - z⁻¹ - (z + 1)⁻¹ := by
 have hn : ∀ m : ℕ, z ≠ -(m : ℂ) := by
  intro m he
  have hh := congrArg Complex.im he
  simp only [neg_im, natCast_im, neg_zero] at hh
  exact hz hh
 have hn1 : ∀ m : ℕ, z + 1 ≠ -(m : ℂ) := by
  intro m he
  have hh := congrArg Complex.im he
  simp only [add_im, one_im, add_zero, neg_im, natCast_im, neg_zero] at hh
  exact hz hh
 have h1 := Complex.digamma_apply_add_one z hn
 have h2 := Complex.digamma_apply_add_one (z + 1) hn1
 rw [show z + 2 = z + 1 + 1 by ring, h2, h1]
 ring
noncomputable def vaj (σ T : ℝ) : ℂ := ((1 - σ : ℝ) + T * I) / 2
noncomputable def vav (σ T : ℝ) : ℂ := ((σ : ℝ) + T * I) / 2
lemma vbN (σ T : ℝ) : (vaj σ T).im = T / 2 := by
 simp [vaj, div_ofNat_im]
lemma veF (σ T : ℝ) : (vav σ T).im = T / 2 := by
 simp [vav, div_ofNat_im]
lemma vcV {σ T : ℝ} (hσ : 1 / 2 ≤ σ) :
  ‖vaj σ T - vav σ T‖ = σ - 1 / 2 := by
 have he : vaj σ T - vav σ T = ((1 / 2 - σ : ℝ) : ℂ) := by
  unfold vaj vav
  push_cast
  ring
 rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
 ring
lemma vdz {z₁ z₂ : ℂ} {b : ℝ}
  (hb : 0 < b) (h1 : z₁.im = b) (h2 : z₂.im = b) :
  ‖z₁⁻¹ - z₂⁻¹‖ ≤ ‖z₁ - z₂‖ / b ^ 2 := by
 have hn1 : b ≤ ‖z₁‖ := by
  simpa only [h1, abs_of_pos hb] using Complex.abs_im_le_norm z₁
 have hn2 : b ≤ ‖z₂‖ := by
  simpa only [h2, abs_of_pos hb] using Complex.abs_im_le_norm z₂
 have hz1 : z₁ ≠ 0 := norm_pos_iff.mp (hb.trans_le hn1)
 have hz2 : z₂ ≠ 0 := norm_pos_iff.mp (hb.trans_le hn2)
 have he : z₁⁻¹ - z₂⁻¹ = (z₂ - z₁) / (z₁ * z₂) := by field_simp
 rw [he, norm_div, norm_sub_rev, norm_mul]
 exact div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hb)
  (by rw [pow_two]; exact mul_le_mul hn1 hn2 hb.le (norm_nonneg _))
lemma vfT {σ T : ℝ}
  (hT : 1 ≤ T) (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 5 / 4) :
  ‖Complex.digamma (vaj σ T) - Complex.digamma (vav σ T)‖ ≤
   16 * (σ - 1 / 2) / T := by
 have hT0 : 0 < T := by linarith
 have hb : 0 < T / 2 := by positivity
 have hσ : 0 ≤ σ - 1 / 2 := by linarith
 have h1re : 1 ≤ (vaj σ T + 2).re := by
  simp [vaj, div_ofNat_re]
  linarith
 have h2re : 1 ≤ (vav σ T + 2).re := by
  simp [vav, div_ofNat_re]
  linarith
 have hnorm : ‖(vaj σ T + 2) - (vav σ T + 2)‖ = σ - 1 / 2 := by
  rw [add_sub_add_right_eq_sub, vcV hσ0]
 have hshift : ‖Complex.digamma (vaj σ T + 2) -
   Complex.digamma (vav σ T + 2)‖ ≤ 8 * (σ - 1 / 2) / T := by
  by_cases hT4 : T ≤ 4
  ·have hh := vdV h1re h2re
   rw [hnorm] at hh
   refine hh.trans ?_
   rw [le_div_iff₀ hT0]
   nlinarith
  ·have hh := vjG.vjx
    (show 0 < (vaj σ T + 2).re by linarith)
    (show 0 < (vav σ T + 2).re by linarith)
    (by simp [vbN, veF])
    (by simp [vbN]; linarith : 2 ≤ (vaj σ T + 2).im)
   rw [hnorm] at hh
   norm_num [vbN] at hh
   convert hh using 1; ring
 have hrec0 := vdz hb (vbN σ T) (veF σ T)
 rw [vcV hσ0] at hrec0
 have hrec1 := vdz hb
  (show (vaj σ T + 1).im = T / 2 by simp [vbN])
  (show (vav σ T + 1).im = T / 2 by simp [veF])
 rw [add_sub_add_right_eq_sub, vcV hσ0] at hrec1
 rw [vcb (z := vaj σ T) (by rw [vbN]; exact hb.ne'),
  vcb (z := vav σ T) (by rw [veF]; exact hb.ne')]
 have he : (Complex.digamma (vaj σ T + 2) - (vaj σ T)⁻¹ -
   (vaj σ T + 1)⁻¹) - (Complex.digamma (vav σ T + 2) -
   (vav σ T)⁻¹ - (vav σ T + 1)⁻¹) =
   (Complex.digamma (vaj σ T + 2) - Complex.digamma (vav σ T + 2)) -
   ((vaj σ T)⁻¹ - (vav σ T)⁻¹) -
   ((vaj σ T + 1)⁻¹ - (vav σ T + 1)⁻¹) := by ring
 rw [he]
 refine (norm_sub_le _ _).trans ?_
 have htri := norm_sub_le (Complex.digamma (vaj σ T + 2) -
  Complex.digamma (vav σ T + 2)) ((vaj σ T)⁻¹ - (vav σ T)⁻¹)
 have hsmall : 2 * ((σ - 1 / 2) / (T / 2) ^ 2) ≤ 8 * (σ - 1 / 2) / T := by
  field_simp
  nlinarith
 calc
  _ ≤ (‖Complex.digamma (vaj σ T + 2) -
   Complex.digamma (vav σ T + 2)‖ +
   ‖(vaj σ T)⁻¹ - (vav σ T)⁻¹‖) +
   ‖(vaj σ T + 1)⁻¹ - (vav σ T + 1)⁻¹‖ :=
    add_le_add htri le_rfl
  _ ≤ (8 * (σ - 1 / 2) / T + (σ - 1 / 2) / (T / 2) ^ 2) +
   (σ - 1 / 2) / (T / 2) ^ 2 := add_le_add (add_le_add hshift hrec0) hrec1
  _ = 8 * (σ - 1 / 2) / T + 2 * ((σ - 1 / 2) / (T / 2) ^ 2) := by ring
  _ ≤ 8 * (σ - 1 / 2) / T + 8 * (σ - 1 / 2) / T := add_le_add le_rfl hsmall
  _ = _ := by ring
noncomputable def vbd (σ T : ℝ) : ℝ :=
 (1 / 2) * (Complex.digamma (vaj σ T) -
  Complex.digamma (vav σ T)).im
noncomputable def vbz (σ T : ℝ) : ℝ :=
 (logDeriv riemannZeta ((σ : ℂ) + T * I)).im -
  (logDeriv riemannZeta (((1 - σ : ℝ) : ℂ) + T * I)).im
lemma vdQ {T : ℝ} (hT : T ≠ 0) (σ : ℝ)
  (hζ : riemannZeta ((σ : ℂ) + T * I) ≠ 0)
  (hζ' : riemannZeta (((1 - σ : ℝ) : ℂ) + T * I) ≠ 0) :
  vbz σ T = vbd σ T :=
 vfH.vdX hT σ hζ hζ'
lemma veb {σ T : ℝ}
  (hT : 1 ≤ T) (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 5 / 4) :
  |vbd σ T| ≤ 8 * (σ - 1 / 2) / T := by
 unfold vbd
 rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
 calc
  _ ≤ (1 / 2) * ‖Complex.digamma (vaj σ T) -
    Complex.digamma (vav σ T)‖ :=
   mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (by norm_num)
  _ ≤ (1 / 2) * (16 * (σ - 1 / 2) / T) :=
   mul_le_mul_of_nonneg_left (vfT hT hσ0 hσ1) (by norm_num)
  _ = _ := by ring
lemma vgU (T δ : ℝ) :
  (∫ σ in (1 / 2 : ℝ)..(1 / 2 + δ), 8 * (σ - 1 / 2) / T) =
   4 * δ ^ 2 / T := by
 rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
  intervalIntegral.integral_sub
   (f := fun σ : ℝ => σ) (g := fun _ => (1 / 2 : ℝ))
   (continuous_id.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
  integral_id, intervalIntegral.integral_const]
 ring
lemma vcz {T δ : ℝ}
  (hT : 1 ≤ T) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4) :
  |∫ σ in (1 / 2 : ℝ)..(1 / 2 + δ), vbd σ T| ≤
   4 * δ ^ 2 / T := by
 rw [← Real.norm_eq_abs, ← vgU]
 apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
 ·filter_upwards [] with σ hσ
  rw [Real.norm_eq_abs]
  exact veb hT hσ.1.le (by linarith [hσ.2])
 ·exact (show Continuous (fun σ : ℝ => 8 * (σ - 1 / 2) / T) by
   fun_prop).intervalIntegrable _ _
lemma vcK {T δ : ℝ}
  (hT : 1 ≤ T) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4)
  (hζ : ∀ σ ∈ Icc (1 / 2) (1 / 2 + δ),
   riemannZeta ((σ : ℂ) + T * I) ≠ 0 ∧
   riemannZeta (((1 - σ : ℝ) : ℂ) + T * I) ≠ 0) :
  |∫ σ in (1 / 2 : ℝ)..(1 / 2 + δ), vbz σ T| ≤
   4 * δ ^ 2 / T := by
 have he : (∫ σ in (1 / 2 : ℝ)..(1 / 2 + δ), vbz σ T) =
   ∫ σ in (1 / 2 : ℝ)..(1 / 2 + δ), vbd σ T := by
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le (by linarith : (1 / 2 : ℝ) ≤ 1 / 2 + δ)]
  intro σ hσ
  exact vdQ (by linarith) σ (hζ σ hσ).1 (hζ σ hσ).2
 rw [he]
 exact vcz hT hδ0 hδ1
end vaa.vab.vcf
end
section
open Filter Complex Metric
open scoped Topology
namespace vaa.vab
lemma veM (u : Circle) :
  ∃ n : ℕ → ℕ, StrictMono n ∧
   Tendsto (fun j => (u : ℂ) ^ n j) atTop (𝓝 1) := by
 obtain ⟨n, hn, ht⟩ := (mapClusterPt_one_atTop_pow u).tendsto_subseq
 refine ⟨n, hn, ?_⟩
 have hc : Continuous ((↑) : Circle → ℂ) := continuous_subtype_val
 have h := (hc.tendsto (1 : Circle)).comp ht
 change Tendsto (fun j => ((u ^ n j : Circle) : ℂ)) atTop (𝓝 (1 : ℂ)) at h
 exact h
lemma vdW {z : ℂ} (hz : z ≠ 0) :
  ∃ n : ℕ → ℕ, StrictMono n ∧
   Tendsto (fun j => (z / (‖z‖ : ℂ)) ^ n j) atTop (𝓝 1) := by
 let u : Circle := ⟨z / (‖z‖ : ℂ), mem_sphere_zero_iff_norm.2 (by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
   abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr hz)])⟩
 exact veM u
lemma vhc {z : ℂ} {n : ℕ → ℕ}
  (hp : Tendsto (fun j => (z / (‖z‖ : ℂ)) ^ n j) atTop (𝓝 1)) :
  Tendsto (fun j => (z ^ n j).re / ‖z‖ ^ n j) atTop (𝓝 (1 : ℝ)) := by
 have h := (Complex.continuous_re.tendsto (1 : ℂ)).comp hp
 simpa only [Function.comp_def, div_pow, ← Complex.ofReal_pow,
  Complex.div_ofReal_re, Complex.one_re] using h
lemma vhb {z : ℂ} (hz : z ≠ 0) {n : ℕ → ℕ}
    (hn : StrictMono n)
    (hp : Tendsto (fun j => (z / (‖z‖ : ℂ)) ^ n j) atTop (𝓝 1)) :
    Tendsto (fun j => Real.log |(z ^ n j).re| / (n j : ℝ))
      atTop (𝓝 (Real.log ‖z‖)) := by
  let w : ℂ := z / (‖z‖ : ℂ)
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hrc : (‖z‖ : ℂ) ≠ 0 := by simpa using hr.ne'
  have hdecomp : z = (‖z‖ : ℂ) * w := (mul_div_cancel₀ z hrc).symm
  have hpow (m : ℕ) : (z ^ m).re = ‖z‖ ^ m * (w ^ m).re := by
    calc (z ^ m).re = (((‖z‖ : ℂ) * w) ^ m).re := congrArg (fun t : ℂ => (t ^ m).re) hdecomp
      _ = ‖z‖ ^ m * (w ^ m).re := by
        rw [mul_pow]
        have hc : (‖z‖ : ℂ) ^ m = ((‖z‖ ^ m : ℝ) : ℂ) :=
          (Complex.ofReal_pow ‖z‖ m).symm
        rw [hc]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero]
  have hre : Tendsto (fun j => (w ^ n j).re) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Function.comp_def, Complex.one_re] using
      (Complex.continuous_re.tendsto (1 : ℂ)).comp hp
  have hlog : Tendsto (fun j => Real.log ((w ^ n j).re)) atTop (𝓝 0) := by
    simpa using hre.log (one_ne_zero : (1 : ℝ) ≠ 0)
  have hnTop : Tendsto (fun j => (n j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn.tendsto_atTop
  have hlim : Tendsto (fun j => Real.log ‖z‖ + Real.log ((w ^ n j).re) / (n j : ℝ))
      atTop (𝓝 (Real.log ‖z‖)) := by
    have hconst : Tendsto (fun _ : ℕ => Real.log ‖z‖) atTop (𝓝 (Real.log ‖z‖)) :=
      tendsto_const_nhds
    simpa using hconst.add (hlog.div_atTop hnTop)
  have heq : (fun j => Real.log |(z ^ n j).re| / (n j : ℝ)) =ᶠ[atTop]
      (fun j => Real.log ‖z‖ + Real.log ((w ^ n j).re) / (n j : ℝ)) := by
    filter_upwards [hre.eventually (lt_mem_nhds (zero_lt_one : (0 : ℝ) < 1)),
      hnTop.eventually (eventually_gt_atTop (0 : ℝ))] with j hj hnj
    rw [Real.log_abs, hpow, Real.log_mul (pow_ne_zero _ hr.ne') hj.ne', Real.log_pow]
    rw [add_div, mul_div_cancel_left₀ _ hnj.ne']
  exact (Filter.tendsto_congr' heq).2 hlim
lemma vez {z : ℂ} (hz : z ≠ 0) :
  ∃ n : ℕ → ℕ, StrictMono n ∧
   Tendsto (fun j => (z / (‖z‖ : ℂ)) ^ n j) atTop (𝓝 1) ∧
   Tendsto (fun j => Real.log |(z ^ n j).re| / (n j : ℝ))
    atTop (𝓝 (Real.log ‖z‖)) := by
 obtain ⟨n, hn, hp⟩ := vdW hz
 exact ⟨n, hn, hp, vhb hz hn hp⟩
end vaa.vab
end
section
open Filter MeromorphicAt MeasureTheory MeromorphicOn Metric Real Set Topology Complex
open scoped ComplexConjugate
namespace vaa.vab.vaR
noncomputable def veh (f : ℂ → ℂ) (c : ℂ) (r : ℝ) : ℝ :=
 ∑ᶠ u, (divisor f (closedBall c r) u : ℝ)
lemma vbS {c : ℂ} {r R : ℝ} {f : ℂ → ℂ}
  (hr : 0 < r) (hrR : r < R)
  (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hfc : f c ≠ 0) :
  veh f c r * Real.log (R / r) ≤
   circleAverage (fun z => Real.log ‖f z‖) c R - Real.log ‖f c‖ := by
 have hR : 0 < R := hr.trans hrR
 have hfa : AnalyticOnNhd ℂ f (closedBall c |R|) := by simpa [abs_of_pos hR] using hf
 have hJ := hfa.circleAverage_log_norm hR.ne' hfc
 rw [abs_of_pos hR] at hJ
 rw [hJ, add_sub_cancel_right, veh, finsum_mul]
 refine finsum_le_finsum' ?_ ?_ fun u => ?_
 ·exact (divisor f (closedBall c r)).finiteSupport (isCompact_closedBall ..) |>.subset
   fun _ _ => (by simp_all)
 ·exact (divisor f (closedBall c R)).finiteSupport (isCompact_closedBall ..) |>.subset
   fun _ _ => (by simp_all)
 ·by_cases hbig : u ∈ closedBall c R
  ·by_cases hsmall : u ∈ closedBall c r
   ·simp only [hf.mono (closedBall_subset_closedBall hrR.le), hsmall,
     AnalyticOnNhd.divisor_apply, hf, hbig]
    by_cases huc : u = c
    ·rw [huc, (hf c (by simp; positivity)).analyticOrderAt_eq_zero.mpr hfc]
     simp
    have hdist : 0 < ‖c - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm huc))
    have hdistR : ‖c - u‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm'] using hsmall
    apply mul_le_mul_of_nonneg_left ?_ (by simp)
    apply Real.log_le_log (div_pos hR hr)
    rw [← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left hR.le hdist hdistR
   ·simp only [hsmall, not_false_eq_true,
     Function.locallyFinsuppWithin.apply_eq_zero_of_notMem, Int.cast_zero, zero_mul]
    refine mul_nonneg (mod_cast hf.divisor_nonneg ..) ?_
    have hdist : 0 < ‖c - u‖ := by
     have : r < ‖c - u‖ := by simpa [mem_closedBall, dist_eq_norm', not_le] using hsmall
     linarith
    apply Real.log_nonneg
    rw [← div_eq_mul_inv, one_le_div hdist]
    simpa [mem_closedBall, dist_eq_norm'] using hbig
  ·have hsmall : u ∉ closedBall c r := fun hu =>
    hbig (closedBall_subset_closedBall hrR.le hu)
   simp [hbig, hsmall]
noncomputable def vaw (f g : ℂ → ℂ) (n : ℕ) (s : ℂ) : ℂ :=
 (f s ^ n + g s ^ n) / 2
lemma vcU {f g : ℂ → ℂ} {c : ℂ}
  (hc : g c = conj (f c)) (n : ℕ) :
  vaw f g n c = ((f c ^ n).re : ℂ) := by
 unfold vaw
 rw [hc, ← map_pow]
 rw [Complex.add_conj]
 push_cast
 ring
lemma vgh {f g : ℂ → ℂ} {s : Set ℂ}
  (hf : AnalyticOnNhd ℂ f s) (hg : AnalyticOnNhd ℂ g s) (n : ℕ) :
  AnalyticOnNhd ℂ (vaw f g n) s := by
 intro z hz
 unfold vaw
 exact ((hf z hz).pow n |>.add ((hg z hz).pow n)).div_const (c := 2)
lemma viP {f g : ℂ → ℂ} {s : ℂ} {B : ℝ}
  (hf : ‖f s‖ ≤ Real.exp B) (hg : ‖g s‖ ≤ Real.exp B) (n : ℕ) :
  ‖vaw f g n s‖ ≤ Real.exp ((n : ℝ) * B) := by
 rw [vaw, norm_div, Complex.norm_ofNat]
 have h1 := norm_add_le (f s ^ n) (g s ^ n)
 rw [norm_pow, norm_pow] at h1
 have hp1 := pow_le_pow_left₀ (norm_nonneg (f s)) hf n
 have hp2 := pow_le_pow_left₀ (norm_nonneg (g s)) hg n
 rw [Real.exp_nat_mul]
 linarith
lemma vho {f g : ℂ → ℂ} {s : ℂ} {B : ℝ}
  (hB : 0 ≤ B) (hf : ‖f s‖ ≤ Real.exp B) (hg : ‖g s‖ ≤ Real.exp B) (n : ℕ) :
  Real.log ‖vaw f g n s‖ ≤ (n : ℝ) * B := by
 by_cases hz : vaw f g n s = 0
 ·simp [hz]
  positivity
 ·have h := Real.log_le_log (norm_pos_iff.mpr hz) (viP hf hg n)
  simpa using h
end vaa.vab.vaR
end
section
open Real Complex Metric MeasureTheory MeromorphicOn Set
namespace vaa.vab.veH
lemma vhY {f : ℂ → ℂ} {c u : ℂ} {R : ℝ}
  (hR : 0 ≤ R) (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hfc : f c ≠ 0)
  (hu : u ∈ closedBall c R) (hzero : f u = 0) :
  1 ≤ divisor f (closedBall c R) u := by
 rw [MeromorphicOn.divisor_apply hf.meromorphicOn hu, (hf u hu).meromorphicOrderAt_eq]
 have hz := (hf u hu).analyticOrderAt_ne_zero.mpr hzero
 have hc : c ∈ closedBall c R := by simpa using hR
 have hct : analyticOrderAt f c ≠ ⊤ := by
  rw [(hf c hc).analyticOrderAt_eq_zero.mpr hfc]
  exact ENat.natCast_ne_top 0
 have hut := hf.analyticOrderAt_ne_top_of_isPreconnected
  (convex_closedBall _ _).isPreconnected hc hu hct
 cases h : analyticOrderAt f u with
 | top => exact absurd h hut
 | coe n =>
  simp only [ENat.map_natCast, WithTop.untop₀_coe]
  have hn : 0 < n := by
   rw [h] at hz
   have : n ≠ 0 := by rintro rfl; exact hz rfl
   omega
  exact_mod_cast hn
lemma vcn {a b : ℝ}
  (ha : a < 5 / 4) (hb : 1 - a ≤ b) :
  (5 / 4 - a) * (5 / 4 - b) ≤ (3 / 4 : ℝ) ^ 2 := by
 have h := mul_le_mul_of_nonneg_left (show 5 / 4 - b ≤ 1 / 4 + a by linarith)
  (show 0 ≤ 5 / 4 - a by linarith)
 nlinarith [sq_nonneg (a - 1 / 2)]
lemma vkx {R a b : ℝ} (hR : 0 < R)
  (ha : a < 5 / 4) (hb : b ≤ 1 / 2) (hpair : 1 - a ≤ b) :
  2 * Real.log (R / (3 / 4)) ≤
   Real.log (R / (5 / 4 - a)) + Real.log (R / (5 / 4 - b)) := by
 have hu : 0 < 5 / 4 - a := by linarith
 have hv : 0 < 5 / 4 - b := by linarith
 have hp := vcn ha hpair
 have hh : (R / (3 / 4)) ^ 2 ≤ (R / (5 / 4 - a)) * (R / (5 / 4 - b)) := by
  rw [div_mul_div_comm, le_div_iff₀ (mul_pos hu hv)]
  nlinarith [mul_le_mul_of_nonneg_left hp (sq_nonneg R)]
 have hl := Real.log_le_log (show 0 < (R / (3 / 4)) ^ 2 by positivity) hh
 rw [Real.log_pow, Real.log_mul (ne_of_gt (div_pos hR hu))
  (ne_of_gt (div_pos hR hv))] at hl
 simpa using hl
lemma vmc {R a b : ℝ} (hR : 0 < R)
  (ha : a < 5 / 4) (hpair : 1 - a ≤ b) (hout : R < 5 / 4 - b) :
  2 * Real.log (R / (3 / 4)) ≤ Real.log (R / (5 / 4 - a)) := by
 have hu : 0 < 5 / 4 - a := by linarith
 have hp := vcn ha hpair
 have hRu : R * (5 / 4 - a) ≤ (3 / 4 : ℝ) ^ 2 := by
  nlinarith [mul_lt_mul_of_pos_left hout hu]
 have hh : (R / (3 / 4)) ^ 2 ≤ R / (5 / 4 - a) := by
  rw [le_div_iff₀ hu]
  nlinarith [mul_le_mul_of_nonneg_left hRu hR.le]
 have hl := Real.log_le_log (show 0 < (R / (3 / 4)) ^ 2 by positivity) hh
 simpa only [Real.log_pow, Nat.cast_ofNat] using hl
lemma vbW {f : ℂ → ℂ} {R : ℝ} (hR : 3 / 4 < R)
  (hf : AnalyticOnNhd ℂ f (closedBall (5 / 4 : ℂ) R))
  (hfc : f (5 / 4 : ℂ) ≠ 0) {k n : ℕ} {a b : ℕ → ℝ}
  (ha_zero : ∀ i, i < k + n → f (a i : ℂ) = 0)
  (ha_lo : ∀ i, i < k + n → 1 / 2 ≤ a i)
  (ha_hi : ∀ i, i < k + n → a i < 5 / 4)
  (ha_inj : ∀ i j, i < k + n → j < k + n → a i = a j → i = j)
  (hb_zero : ∀ i, i < n → f (b i : ℂ) = 0)
  (hb_pair : ∀ i, i < n → 1 - a (i + k) ≤ b i)
  (hb_hi : ∀ i, i < n → b i ≤ 1 / 2)
  (hb_inj : ∀ i j, i < n → j < n → b i = b j → i = j)
  (hdisj : ∀ i j, i < k + n → j < n → a i ≠ b j) :
  (2 * (n : ℝ) + k) * Real.log (R / (3 / 4)) ≤
   circleAverage (fun z => Real.log ‖f z‖) (5 / 4 : ℂ) R -
    Real.log ‖f (5 / 4 : ℂ)‖ := by
 classical
 have hR0 : 0 < R := by linarith
 let c : ℂ := 5 / 4
 let D := divisor f (closedBall c R)
 let w : ℂ → ℝ := fun u => (D u : ℝ) * Real.log (R * ‖c - u‖⁻¹)
 have hDfin : (D.support : Set ℂ).Finite := D.finiteSupport (isCompact_closedBall c R)
 have hwfin : w.support.Finite := hDfin.subset (by
  intro u hu
  simp only [Function.mem_support, w, ne_eq, mul_eq_zero, not_or, Int.cast_eq_zero] at hu
  exact hu.1)
 have hw_nonneg : ∀ u, 0 ≤ w u := by
  intro u
  by_cases hDu : D u = 0
  ·simp [w, hDu]
  have hu : u ∈ closedBall c R := D.supportWithinDomain (by
   simpa only [Function.mem_support] using hDu)
  have huc : c ≠ u := by
   intro he
   apply hDu
   subst u
   change divisor f (closedBall c R) c = 0
   rw [MeromorphicOn.divisor_apply hf.meromorphicOn hu,
    (hf c hu).meromorphicOrderAt_eq, (hf c hu).analyticOrderAt_eq_zero.mpr hfc]
   rfl
  have hd : 0 < ‖c - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huc)
  apply mul_nonneg (by exact_mod_cast (hf.divisor_nonneg u))
  apply Real.log_nonneg
  rw [← div_eq_mul_inv, one_le_div hd]
  simpa only [mem_closedBall, dist_eq_norm'] using hu
 have hj : (∑ᶠ u, w u) = circleAverage (fun z => Real.log ‖f z‖) c R - Real.log ‖f c‖ := by
  have hfa : AnalyticOnNhd ℂ f (closedBall c |R|) := by simpa [abs_of_pos hR0] using hf
  have h := hfa.circleAverage_log_norm hR0.ne' hfc
  rw [abs_of_pos hR0] at h
  simpa only [w, D] using (eq_sub_iff_add_eq.mpr h.symm)
 have hnrm (x : ℝ) (hx : x < 5 / 4) : ‖c - (x : ℂ)‖ = 5 / 4 - x := by
  have he : c - (x : ℂ) = ((5 / 4 - x : ℝ) : ℂ) := by dsimp [c]; push_cast; ring
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
 have hw_real (x : ℝ) (hx : x < 5 / 4) (hd : 5 / 4 - x ≤ R) (hz : f (x : ℂ) = 0) :
   Real.log (R / (5 / 4 - x)) ≤ w (x : ℂ) := by
  have hu : (x : ℂ) ∈ closedBall c R := by
   simpa only [mem_closedBall, dist_eq_norm', hnrm x hx] using hd
  have hD1 : (1 : ℝ) ≤ (D (x : ℂ) : ℝ) := by
   exact_mod_cast vhY hR0.le hf hfc hu hz
  have hl : 0 ≤ Real.log (R / (5 / 4 - x)) :=
   Real.log_nonneg ((one_le_div (by linarith)).mpr hd)
  dsimp [w]
  rw [hnrm x hx, ← div_eq_mul_inv]
  exact le_mul_of_one_le_left hl hD1
 have hp (i : ℕ) (hi : i < n) :
   2 * Real.log (R / (3 / 4)) ≤ w (a (i + k) : ℂ) + w (b i : ℂ) := by
  have hik : i + k < k + n := by omega
  have ha := hw_real (a (i + k)) (ha_hi (i + k) hik)
   (by linarith [ha_lo (i + k) hik]) (ha_zero (i + k) hik)
  by_cases hb : 5 / 4 - b i ≤ R
  ·have hbw := hw_real (b i) (by linarith [hb_hi i hi]) hb (hb_zero i hi)
   linarith [vkx hR0 (ha_hi (i + k) (by omega)) (hb_hi i hi) (hb_pair i hi)]
  ·have hw := hw_nonneg (b i : ℂ)
   linarith [vmc hR0 (ha_hi (i + k) (by omega)) (hb_pair i hi) (lt_of_not_ge hb)]
 let Za : Finset ℂ := (Finset.range (k + n)).image (fun i => (a i : ℂ))
 let Zb : Finset ℂ := (Finset.range n).image (fun i => (b i : ℂ))
 have hai : ∀ i ∈ Finset.range (k + n), ∀ j ∈ Finset.range (k + n), (a i : ℂ) = (a j : ℂ) → i = j := by
  intro i hi j hj he
  exact ha_inj i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) (by exact_mod_cast he)
 have hbi : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n, (b i : ℂ) = (b j : ℂ) → i = j := by
  intro i hi j hj he
  exact hb_inj i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) (by exact_mod_cast he)
 have hdj : Disjoint Za Zb := by
  rw [Finset.disjoint_left]
  intro z hza hzb
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hza
  obtain ⟨j, hj, he'⟩ := Finset.mem_image.mp hzb
  exact hdisj i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
   (by exact_mod_cast (he.trans he'.symm))
 have hsingle (i : ℕ) (hi : i < k) : Real.log (R / (3 / 4)) ≤ w (a i : ℂ) := by
  have hii : i < k + n := by omega
  have ha := hw_real (a i) (ha_hi i hii) (by linarith [ha_lo i hii]) (ha_zero i hii)
  have hd : 0 < 5 / 4 - a i := by linarith [ha_hi i hii]
  have hh : R / (3 / 4) ≤ R / (5 / 4 - a i) :=
   div_le_div_of_nonneg_left hR0.le hd (by linarith [ha_lo i hii])
  exact (Real.log_le_log (by positivity) hh).trans ha
 have hsingle_sum : (k : ℝ) * Real.log (R / (3 / 4)) ≤ ∑ i ∈ Finset.range k, w (a i : ℂ) := by
  have hh := Finset.sum_le_sum (fun i hi => hsingle i (Finset.mem_range.mp hi))
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hh
 have hpair_sum : 2 * (n : ℝ) * Real.log (R / (3 / 4)) ≤
   ∑ i ∈ Finset.range n, (w (a (i + k) : ℂ) + w (b i : ℂ)) := by
  have hh := Finset.sum_le_sum (fun i hi => hp i (Finset.mem_range.mp hi))
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc,
   mul_left_comm] using hh
 have hsum : (2 * (n : ℝ) + k) * Real.log (R / (3 / 4)) ≤ ∑ z ∈ Za ∪ Zb, w z := by
  rw [Finset.sum_union hdj, Finset.sum_image hai, Finset.sum_image hbi,
   Finset.sum_range_add, add_assoc, ← Finset.sum_add_distrib]
  simp only [Nat.add_comm k] at *
  nlinarith [hsingle_sum, hpair_sum]
 let F := hwfin.toFinset
 have hsum_le : ∑ z ∈ Za ∪ Zb, w z ≤ ∑ z ∈ F, w z := by
  calc
   _ ≤ ∑ z ∈ (Za ∪ Zb) ∪ F, w z :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun z _ _ => hw_nonneg z)
   _ = ∑ z ∈ F, w z := by
    symm
    apply Finset.sum_subset Finset.subset_union_right
    intro z _ hz
    have hz' : z ∉ w.support := by simpa only [F, Set.Finite.mem_toFinset] using hz
    simpa only [Function.mem_support, not_not] using hz'
 have hfinsum : (∑ᶠ u, w u) = ∑ z ∈ F, w z :=
  finsum_eq_sum_of_support_subset_of_finite w (le_refl _) hwfin
 exact hsum.trans (hsum_le.trans_eq (hfinsum.symm.trans hj))
end vaa.vab.veH
end
section
namespace vaa.vab.vem
open Set
lemma viY {φ : ℝ → ℝ} {a b ℓ : ℝ} (hab : a ≤ b)
  (hcont : ContinuousOn φ (Set.Icc a b)) (hlo : φ a < ℓ) (hhi : ℓ < φ b) :
  ∃ c ∈ Set.Ioo a b, φ c = ℓ ∧ ∀ x ∈ Set.Ico a c, φ x < ℓ := by
 set S : Set ℝ := Set.Icc a b ∩ φ ⁻¹' {ℓ} with hSdef
 have hSne : S.Nonempty := by
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc hab hcont ⟨hlo.le, hhi.le⟩
  exact ⟨x, hx, hfx⟩
 have hSclosed : IsClosed S :=
  hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
 have hSbdd : BddBelow S := ⟨a, fun x hx => hx.1.1⟩
 set c : ℝ := sInf S with hcdef
 have hcS : c ∈ S := hSclosed.csInf_mem hSne hSbdd
 have hcIcc : c ∈ Set.Icc a b := hcS.1
 have hφc : φ c = ℓ := hcS.2
 have hac : a < c := by
  refine hcIcc.1.lt_of_ne ?_
  intro h
  exact hlo.ne (by rw [h]; exact hφc)
 have hcb : c < b := by
  refine hcIcc.2.lt_of_ne ?_
  intro h
  exact hhi.ne' (by rw [← h]; exact hφc)
 refine ⟨c, ⟨hac, hcb⟩, hφc, ?_⟩
 intro x hx
 have hxb : x ∈ Set.Icc a b := ⟨hx.1, hx.2.le.trans hcIcc.2⟩
 by_contra hge
 push Not at hge
 have hne : φ x ≠ ℓ := by
  intro heq
  have hxS : x ∈ S := ⟨hxb, heq⟩
  exact absurd hx.2 (not_lt.mpr (csInf_le hSbdd hxS))
 have hlt : ℓ < φ x := lt_of_le_of_ne hge (Ne.symm hne)
 have hsub : Set.Icc a x ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl hxb.2
 obtain ⟨y, hy, hfy⟩ :=
  intermediate_value_Icc hx.1 (hcont.mono hsub) ⟨hlo.le, hlt.le⟩
 have hyS : y ∈ S := ⟨⟨hy.1, hy.2.trans hxb.2⟩, hfy⟩
 have hcy : c ≤ y := csInf_le hSbdd hyS
 exact absurd (hcy.trans hy.2) (not_le.mpr hx.2)
lemma vjC {φ : ℝ → ℝ} {a b ℓ : ℝ} (hab : a ≤ b)
  (hcont : ContinuousOn φ (Set.Icc a b)) (hlo : φ a < ℓ) (hhi : ℓ < φ b) :
  ∃ c ∈ Set.Ioo a b, φ c = ℓ ∧ ∀ x ∈ Set.Ioc c b, ℓ < φ x := by
 set S : Set ℝ := Set.Icc a b ∩ φ ⁻¹' {ℓ} with hSdef
 have hSne : S.Nonempty := by
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc hab hcont ⟨hlo.le, hhi.le⟩
  exact ⟨x, hx, hfx⟩
 have hSclosed : IsClosed S :=
  hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
 have hSbdd : BddAbove S := ⟨b, fun x hx => hx.1.2⟩
 set c : ℝ := sSup S with hcdef
 have hcS : c ∈ S := hSclosed.csSup_mem hSne hSbdd
 have hcIcc : c ∈ Set.Icc a b := hcS.1
 have hφc : φ c = ℓ := hcS.2
 have hac : a < c := by
  refine hcIcc.1.lt_of_ne ?_
  intro h
  exact hlo.ne (by rw [h]; exact hφc)
 have hcb : c < b := by
  refine hcIcc.2.lt_of_ne ?_
  intro h
  exact hhi.ne' (by rw [← h]; exact hφc)
 refine ⟨c, ⟨hac, hcb⟩, hφc, ?_⟩
 intro x hx
 have hxb : x ∈ Set.Icc a b := ⟨hcIcc.1.trans hx.1.le, hx.2⟩
 by_contra hge
 push Not at hge
 have hne : φ x ≠ ℓ := by
  intro heq
  have hxS : x ∈ S := ⟨hxb, heq⟩
  exact absurd hx.1 (not_lt.mpr (le_csSup hSbdd hxS))
 have hlt : φ x < ℓ := lt_of_le_of_ne hge hne
 have hsub : Set.Icc x b ⊆ Set.Icc a b := Set.Icc_subset_Icc hxb.1 le_rfl
 obtain ⟨y, hy, hfy⟩ :=
  intermediate_value_Icc hx.2 (hcont.mono hsub) ⟨hlt.le, hhi.le⟩
 have hyS : y ∈ S := ⟨⟨hxb.1.trans hy.1, hy.2⟩, hfy⟩
 have hyc : y ≤ c := le_csSup hSbdd hyS
 exact absurd (hy.1.trans hyc) (not_le.mpr hx.1)
lemma vfz {φ : ℝ → ℝ} {a b ℓ₀ : ℝ} {m : ℕ}
  (hab : a ≤ b) (hcont : ContinuousOn φ (Set.Icc a b))
  (hℓ₀ : φ a < ℓ₀) (htop : ℓ₀ + ((m : ℝ) - 1) * Real.pi < φ b) :
  ∃ c : ℕ → ℝ,
   (∀ i, i < m → c i ∈ Set.Ioo a b) ∧
   (∀ i j, i < j → j < m → c i < c j) ∧
   (∀ i, i < m → φ (c i) = ℓ₀ + (i : ℝ) * Real.pi) ∧
   (∀ i, i < m → ∀ x ∈ Set.Ico a (c i), φ x < ℓ₀ + (i : ℝ) * Real.pi) := by
 have hpi := Real.pi_pos
 have key : ∀ i : ℕ, i < m →
   ∃ c ∈ Set.Ioo a b, φ c = ℓ₀ + (i : ℝ) * Real.pi ∧
    ∀ x ∈ Set.Ico a c, φ x < ℓ₀ + (i : ℝ) * Real.pi := by
  intro i hi
  have hi0 : (0 : ℝ) ≤ (i : ℝ) * Real.pi :=
   mul_nonneg (Nat.cast_nonneg i) hpi.le
  have hlo : φ a < ℓ₀ + (i : ℝ) * Real.pi := by linarith
  have hcast : (i : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hi
  have hmul : (i : ℝ) * Real.pi ≤ ((m : ℝ) - 1) * Real.pi :=
   mul_le_mul_of_nonneg_right (by linarith) hpi.le
  have hhi : ℓ₀ + (i : ℝ) * Real.pi < φ b := by linarith
  exact viY hab hcont hlo hhi
 choose! c hmem hval hmin using key
 refine ⟨c, hmem, ?_, hval, hmin⟩
 intro i j hij hjm
 have him : i < m := hij.trans hjm
 have hstep : (i : ℝ) * Real.pi < (j : ℝ) * Real.pi := by
  have : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
  exact mul_lt_mul_of_pos_right this hpi
 by_contra hle
 push Not at hle
 rcases lt_or_eq_of_le hle with hlt | heq
 ·
  have h1 : φ (c j) < ℓ₀ + (i : ℝ) * Real.pi :=
   hmin i him (c j) ⟨(hmem j hjm).1.le, hlt⟩
  have h2 : φ (c j) = ℓ₀ + (j : ℝ) * Real.pi := hval j hjm
  linarith
 ·
  have h1 : φ (c i) = ℓ₀ + (i : ℝ) * Real.pi := hval i him
  have h2 : φ (c j) = ℓ₀ + (j : ℝ) * Real.pi := hval j hjm
  rw [heq] at h2
  linarith
lemma vfW {φ : ℝ → ℝ} {a b ℓ₀ : ℝ} {m : ℕ}
  (hab : a ≤ b) (hcont : ContinuousOn φ (Set.Icc a b))
  (hℓ₀ : ℓ₀ < φ b) (hbot : φ a < ℓ₀ - ((m : ℝ) - 1) * Real.pi) :
  ∃ c : ℕ → ℝ,
   (∀ i, i < m → c i ∈ Set.Ioo a b) ∧
   (∀ i j, i < j → j < m → c j < c i) ∧
   (∀ i, i < m → φ (c i) = ℓ₀ - (i : ℝ) * Real.pi) ∧
   (∀ i, i < m → ∀ x ∈ Set.Ioc (c i) b, ℓ₀ - (i : ℝ) * Real.pi < φ x) := by
 have hpi := Real.pi_pos
 have key : ∀ i : ℕ, i < m →
   ∃ c ∈ Set.Ioo a b, φ c = ℓ₀ - (i : ℝ) * Real.pi ∧
    ∀ x ∈ Set.Ioc c b, ℓ₀ - (i : ℝ) * Real.pi < φ x := by
  intro i hi
  have hi0 : (0 : ℝ) ≤ (i : ℝ) * Real.pi :=
   mul_nonneg (Nat.cast_nonneg i) hpi.le
  have hcast : (i : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hi
  have hmul : (i : ℝ) * Real.pi ≤ ((m : ℝ) - 1) * Real.pi :=
   mul_le_mul_of_nonneg_right (by linarith) hpi.le
  have hlo : φ a < ℓ₀ - (i : ℝ) * Real.pi := by linarith
  have hhi : ℓ₀ - (i : ℝ) * Real.pi < φ b := by linarith
  exact vjC hab hcont hlo hhi
 choose! c hmem hval hmax using key
 refine ⟨c, hmem, ?_, hval, hmax⟩
 intro i j hij hjm
 have him : i < m := hij.trans hjm
 have hstep : (i : ℝ) * Real.pi < (j : ℝ) * Real.pi := by
  have : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
  exact mul_lt_mul_of_pos_right this hpi
 by_contra hle
 push Not at hle
 rcases lt_or_eq_of_le hle with hlt | heq
 ·
  have h1 : ℓ₀ - (i : ℝ) * Real.pi < φ (c j) :=
   hmax i him (c j) ⟨hlt, (hmem j hjm).2.le⟩
  have h2 : φ (c j) = ℓ₀ - (j : ℝ) * Real.pi := hval j hjm
  linarith
 ·
  have h1 : φ (c i) = ℓ₀ - (i : ℝ) * Real.pi := hval i him
  have h2 : φ (c j) = ℓ₀ - (j : ℝ) * Real.pi := hval j hjm
  rw [← heq] at h2
  linarith
lemma vfI (x : ℝ) :
  ∃ ℓ : ℝ, (∃ k : ℤ, ℓ = Real.pi / 2 + (k : ℝ) * Real.pi) ∧
   x < ℓ ∧ ℓ ≤ x + Real.pi := by
 have hpi := Real.pi_pos
 set y : ℝ := (x - Real.pi / 2) / Real.pi with hy
 have hyπ : y * Real.pi = x - Real.pi / 2 := div_mul_cancel₀ _ hpi.ne'
 refine ⟨Real.pi / 2 + ((⌊y⌋ + 1 : ℤ) : ℝ) * Real.pi, ⟨⌊y⌋ + 1, rfl⟩, ?_, ?_⟩
 ·have h1 : y < (⌊y⌋ : ℝ) + 1 := Int.lt_floor_add_one y
  have h3 : y * Real.pi < ((⌊y⌋ : ℝ) + 1) * Real.pi :=
   mul_lt_mul_of_pos_right h1 hpi
  push_cast
  linarith
 ·have h1 : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
  have h3 : (⌊y⌋ : ℝ) * Real.pi ≤ y * Real.pi :=
   mul_le_mul_of_nonneg_right h1 hpi.le
  push_cast
  linarith
lemma vfQ (x : ℝ) :
  ∃ ℓ : ℝ, (∃ k : ℤ, ℓ = Real.pi / 2 + (k : ℝ) * Real.pi) ∧
   ℓ < x ∧ x - Real.pi ≤ ℓ := by
 have hpi := Real.pi_pos
 set y : ℝ := (x - Real.pi / 2) / Real.pi with hy
 have hyπ : y * Real.pi = x - Real.pi / 2 := div_mul_cancel₀ _ hpi.ne'
 refine ⟨Real.pi / 2 + ((⌈y⌉ - 1 : ℤ) : ℝ) * Real.pi, ⟨⌈y⌉ - 1, rfl⟩, ?_, ?_⟩
 ·have h1 : (⌈y⌉ : ℝ) < y + 1 := Int.ceil_lt_add_one y
  have h3 : ((⌈y⌉ : ℝ) - 1) * Real.pi < y * Real.pi :=
   mul_lt_mul_of_pos_right (by linarith) hpi
  push_cast
  linarith
 ·have h1 : y ≤ (⌈y⌉ : ℝ) := Int.le_ceil y
  have h3 : (y - 1) * Real.pi ≤ ((⌈y⌉ : ℝ) - 1) * Real.pi :=
   mul_le_mul_of_nonneg_right (by linarith) hpi.le
  push_cast
  linarith
lemma vdB {ℓ : ℝ}
  (h : ∃ k : ℤ, ℓ = Real.pi / 2 + (k : ℝ) * Real.pi) : Real.cos ℓ = 0 := by
 obtain ⟨k, rfl⟩ := h
 rw [Real.cos_eq_zero_iff]
 exact ⟨k, by ring⟩
lemma vjh {ℓ : ℝ}
  (h : ∃ k : ℤ, ℓ = Real.pi / 2 + (k : ℝ) * Real.pi) (n : ℕ) :
  ∃ k : ℤ, ℓ + (n : ℝ) * Real.pi = Real.pi / 2 + (k : ℝ) * Real.pi := by
 obtain ⟨k, rfl⟩ := h
 exact ⟨k + n, by push_cast; ring⟩
lemma vjg {ℓ : ℝ}
  (h : ∃ k : ℤ, ℓ = Real.pi / 2 + (k : ℝ) * Real.pi) (n : ℕ) :
  ∃ k : ℤ, ℓ - (n : ℝ) * Real.pi = Real.pi / 2 + (k : ℝ) * Real.pi := by
 obtain ⟨k, rfl⟩ := h
 exact ⟨k - n, by push_cast; ring⟩
end vaa.vab.vem
end
section
open Real Complex Metric MeasureTheory MeromorphicOn Set
open vaa.vab.vem
open vaa.vab.veH
namespace vaa.vab.vdN
lemma vgp {f : ℂ → ℂ} {R E : ℝ}
  (hR : 3 / 4 < R) (hE : 0 < E)
  (hf : AnalyticOnNhd ℂ f (closedBall (5 / 4 : ℂ) R))
  (hfc : f (5 / 4 : ℂ) ≠ 0) {ψ : ℝ → ℝ}
  (hψcont : ContinuousOn ψ (Icc (-1 / 4 : ℝ) (5 / 4 : ℝ)))
  (hψzero : ∀ x ∈ Icc (-1 / 4 : ℝ) (5 / 4 : ℝ),
   Real.cos (ψ x) = 0 → f (x : ℂ) = 0)
  (hψdelta : ∀ δ : ℝ, 0 < δ → δ ≤ 3 / 4 →
   |(ψ (1 / 2 + δ) - ψ (1 / 2)) - (ψ (1 / 2) - ψ (1 / 2 - δ))| ≤ E)
  {m₁ : ℕ} (hsweep : (m₁ : ℝ) * Real.pi < ψ (5 / 4) - ψ (1 / 2)) :
  (m₁ : ℝ) ≤ (circleAverage (fun z => Real.log ‖f z‖) (5 / 4 : ℂ) R -
   Real.log ‖f (5 / 4 : ℂ)‖) / (2 * Real.log (R / (3 / 4))) + 1 + E / (2 * Real.pi) := by
 let J := circleAverage (fun z => Real.log ‖f z‖) (5 / 4 : ℂ) R -
  Real.log ‖f (5 / 4 : ℂ)‖
 have hlog : 0 < Real.log (R / (3 / 4)) :=
  Real.log_pos ((one_lt_div (by norm_num)).mpr hR)
 have hJ : 0 ≤ J := by
  have hh := vaR.vbS
   (by norm_num : (0 : ℝ) < 3 / 4) hR hf hfc
  have hn : 0 ≤ vaR.veh f (5 / 4 : ℂ) (3 / 4) := by
   unfold vaR.veh
   apply finsum_nonneg
   intro u
   exact_mod_cast (hf.mono (closedBall_subset_closedBall hR.le)).divisor_nonneg u
  exact le_trans (mul_nonneg hn hlog.le) hh
 have hJnonneg : 0 ≤ J / (2 * Real.log (R / (3 / 4))) := div_nonneg hJ (by positivity)
 have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
 set D : ℕ := 1 + ⌈E / Real.pi⌉₊ with hD_def
 have hD_cast : (D : ℝ) = 1 + (⌈E / Real.pi⌉₊ : ℝ) := by
  rw [hD_def]; push_cast; ring
 have hceil_ge : E
   ≤ (⌈E / Real.pi⌉₊ : ℝ) * Real.pi := by
  have h1 : E / Real.pi
    ≤ (⌈E / Real.pi⌉₊ : ℝ) := Nat.le_ceil _
  have h2 := mul_le_mul_of_nonneg_right h1 hπ.le
  rwa [div_mul_cancel₀ _ hπ.ne'] at h2
 have hDπ_ge : E + Real.pi ≤ (D : ℝ) * Real.pi := by
  have hexp : (D : ℝ) * Real.pi
    = Real.pi + (⌈E / Real.pi⌉₊ : ℝ) * Real.pi := by
   rw [hD_cast]; ring
  linarith [hceil_ge]
 have hD_le : (D : ℝ) ≤ 2 + E / Real.pi := by
  have h0 : (0 : ℝ) ≤ E / Real.pi := by positivity
  have h1 : (⌈E / Real.pi⌉₊ : ℝ)
    < E / Real.pi + 1 := Nat.ceil_lt_add_one h0
  linarith [hD_cast, h1]
 obtain ⟨ℓ₀, hℓ₀_ht, hℓ₀_gt, hℓ₀_le⟩ := vfI (ψ (1 / 2))
 have hsub_right : Set.Icc (1 / 2 : ℝ) (5 / 4 : ℝ)
   ⊆ Set.Icc (-1 / 4 : ℝ) (5 / 4 : ℝ) := Set.Icc_subset_Icc (by norm_num) le_rfl
 have htop : ℓ₀ + ((m₁ : ℝ) - 1) * Real.pi < ψ (5 / 4) := by
  have hexp : ℓ₀ + ((m₁ : ℝ) - 1) * Real.pi
    = ℓ₀ + (m₁ : ℝ) * Real.pi - Real.pi := by ring
  linarith [hℓ₀_le, hsweep, hexp]
 obtain ⟨c, hc_mem, hc_mono, hc_val, _hc_min⟩ :=
  vfz (by norm_num : (1 / 2 : ℝ) ≤ 5 / 4)
   (hψcont.mono hsub_right) hℓ₀_gt htop
 have hc_zero : ∀ i, i < m₁ → f (c i : ℂ) = 0 := by
  intro i hi
  have hmem := hc_mem i hi
  refine hψzero (c i) ⟨by linarith [hmem.1], hmem.2.le⟩ ?_
  rw [hc_val i hi]
  exact vdB (vjh hℓ₀_ht i)
 have hc_inj : ∀ i j, i < m₁ → j < m₁ → c i = c j → i = j := by
  intro i j hi hj heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  ·exact (ne_of_lt (hc_mono i j hij hj)) heq
  ·exact (ne_of_lt (hc_mono j i hji hi)) heq.symm
 have hJmul : J / (2 * Real.log (R / (3 / 4))) * (2 * Real.log (R / (3 / 4))) = J :=
  div_mul_cancel₀ _ (by positivity)
 have hEdiv : E / (2 * Real.pi) = (E / Real.pi) / 2 := by ring
 by_cases hm₁D : m₁ ≤ D
 ·have hm₁R : (m₁ : ℝ) ≤ (D : ℝ) := by exact_mod_cast hm₁D
  have hj := vbW (k := m₁) (n := 0)
   (a := c) (b := fun _ => 0) hR hf hfc
   (fun i hi => hc_zero i (by simpa using hi))
   (fun i hi => (hc_mem i (by simpa using hi)).1.le)
   (fun i hi => (hc_mem i (by simpa using hi)).2)
   (fun i j hi hj he => hc_inj i j (by simpa using hi) (by simpa using hj) he)
   (by omega) (by omega) (by omega) (by omega) (by omega)
  have hcnt : (m₁ : ℝ) ≤ J / (2 * Real.log (R / (3 / 4))) + (D : ℝ) / 2 := by
   have hm := mul_le_mul_of_nonneg_right hm₁R hlog.le
   dsimp [J] at hJmul ⊢
   norm_num only [Nat.cast_zero, zero_mul, zero_add] at hj
   nlinarith
  linarith [hD_le, hEdiv]
 ·
  have hDlt : D < m₁ := not_le.mp hm₁D
  set n' : ℕ := m₁ - D with hn'_def
  have hn'_cast : (n' : ℝ) = (m₁ : ℝ) - (D : ℝ) := by
   have h : n' + D = m₁ := by omega
   have h2 : (n' : ℝ) + (D : ℝ) = (m₁ : ℝ) := by exact_mod_cast h
   linarith
  have hn'π : (n' : ℝ) * Real.pi = (m₁ : ℝ) * Real.pi - (D : ℝ) * Real.pi := by
   rw [hn'_cast]; ring
  have hdelta34 := hψdelta (3 / 4) (by norm_num) le_rfl
  rw [show (1 / 2 : ℝ) + 3 / 4 = 5 / 4 by norm_num,
   show (1 / 2 : ℝ) - 3 / 4 = -1 / 4 by norm_num] at hdelta34
  have hVL34 : (m₁ : ℝ) * Real.pi - E
    < ψ (1 / 2) - ψ (-1 / 4) := by
   have h2 := (abs_le.mp hdelta34).2
   linarith [hsweep]
  obtain ⟨ℓ'₀, hℓ'₀_ht, hℓ'₀_lt, hℓ'₀_ge⟩ := vfQ (ψ (1 / 2))
  have hsub_left : Set.Icc (-1 / 4 : ℝ) (1 / 2 : ℝ)
    ⊆ Set.Icc (-1 / 4 : ℝ) (5 / 4 : ℝ) := Set.Icc_subset_Icc le_rfl (by norm_num)
  have hbot : ψ (-1 / 4) < ℓ'₀ - ((n' : ℝ) - 1) * Real.pi := by
   have hexp : ℓ'₀ - ((n' : ℝ) - 1) * Real.pi
     = ℓ'₀ - (n' : ℝ) * Real.pi + Real.pi := by ring
   linarith [hℓ'₀_ge, hDπ_ge, hVL34, hn'π, hexp]
  obtain ⟨l, hl_mem, hl_anti, hl_val, hl_max⟩ :=
   vfW (by norm_num : (-1 / 4 : ℝ) ≤ 1 / 2)
    (hψcont.mono hsub_left) hℓ'₀_lt hbot
  have hl_zero : ∀ j, j < n' → f (l j : ℂ) = 0 := by
   intro j hj
   have hmem := hl_mem j hj
   refine hψzero (l j) ⟨hmem.1.le, by linarith [hmem.2]⟩ ?_
   rw [hl_val j hj]
   exact vdB (vjg hℓ'₀_ht j)
  have hinterlace : ∀ k, k < n' → 1 - c (k + D) ≤ l k := by
   intro k hk
   have hkD : k + D < m₁ := by omega
   have hmemc := hc_mem (k + D) hkD
   set δ : ℝ := c (k + D) - 1 / 2 with hδ_def
   have hδ_pos : 0 < δ := by rw [hδ_def]; linarith [hmemc.1]
   have hδ_le : δ ≤ 3 / 4 := by rw [hδ_def]; linarith [hmemc.2]
   have h12δ : (1 / 2 : ℝ) + δ = c (k + D) := by rw [hδ_def]; ring
   have hd := hψdelta δ hδ_pos hδ_le
   rw [h12δ] at hd
   have hval := hc_val (k + D) hkD
   have hcastπ : ((k + D : ℕ) : ℝ) * Real.pi
     = (k : ℝ) * Real.pi + (D : ℝ) * Real.pi := by push_cast; ring
   have hVL_gt : ((k : ℝ) + 1) * Real.pi < ψ (1 / 2) - ψ (1 / 2 - δ) := by
    have h2 := (abs_le.mp hd).2
    linarith [hℓ₀_gt, hDπ_ge, hval, hcastπ]
   have hlt : ψ (1 / 2 - δ) < ℓ'₀ - (k : ℝ) * Real.pi := by
    linarith [hVL_gt, hℓ'₀_ge]
   by_contra hcon
   push Not at hcon
   have h1c : (1 : ℝ) - c (k + D) = 1 / 2 - δ := by rw [hδ_def]; ring
   have hxmem : (1 / 2 - δ : ℝ) ∈ Set.Ioc (l k) (1 / 2 : ℝ) :=
    Set.mem_Ioc.mpr ⟨by rw [← h1c]; exact hcon, by linarith⟩
   have hgt := hl_max k hk (1 / 2 - δ) hxmem
   linarith [hlt, hgt]
  have ha_inj : ∀ i j, i < n' → j < n' → c (i + D) = c (j + D) → i = j := by
   intro i j hi hj heq
   by_contra hne'
   rcases Nat.lt_or_ge i j with hlt | hge
   ·exact absurd heq (ne_of_lt (hc_mono (i + D) (j + D) (by omega) (by omega)))
   ·have hgt : j < i := lt_of_le_of_ne hge (Ne.symm hne')
    exact absurd heq.symm
     (ne_of_lt (hc_mono (j + D) (i + D) (by omega) (by omega)))
  have ha'_inj : ∀ i j, i < n' → j < n' → l i = l j → i = j := by
   intro i j hi hj heq
   by_contra hne'
   rcases Nat.lt_or_ge i j with hlt | hge
   ·exact absurd heq (ne_of_gt (hl_anti i j hlt hj))
   ·have hgt : j < i := lt_of_le_of_ne hge (Ne.symm hne')
    exact absurd heq.symm (ne_of_gt (hl_anti j i hgt hi))
  have hdisj : ∀ i j, i < n' → j < n' → c (i + D) ≠ l j := by
   intro i j hi hj
   have h1 : (1 / 2 : ℝ) < c (i + D) := (hc_mem (i + D) (by omega)).1
   have h2 : l j < 1 / 2 := (hl_mem j hj).2
   exact ne_of_gt (lt_trans h2 h1)
  have hdisj_all : ∀ i j, i < D + n' → j < n' → c i ≠ l j := by
   intro i j hi hj
   have h1 := (hc_mem i (by omega)).1
   have h2 := (hl_mem j hj).2
   exact ne_of_gt (lt_trans h2 h1)
  have hj := vbW (k := D) (n := n')
   (a := c) (b := l) hR hf hfc
   (fun i hi => hc_zero i (by omega))
   (fun i hi => ((hc_mem i (by omega)).1).le)
   (fun i hi => (hc_mem i (by omega)).2)
   (fun i j hi hj he => hc_inj i j (by omega) (by omega) he)
   hl_zero hinterlace (fun i hi => ((hl_mem i hi).2).le) ha'_inj hdisj_all
  have hcnt : (m₁ : ℝ) ≤ J / (2 * Real.log (R / (3 / 4))) + (D : ℝ) / 2 := by
   dsimp [J] at hJmul ⊢
   nlinarith [hj, hn'_cast]
  linarith [hcnt, hD_le, hEdiv]
lemma vlM {f : ℂ → ℂ} {R E : ℝ}
  (hR : 3 / 4 < R) (hE : 0 < E)
  (hf : AnalyticOnNhd ℂ f (closedBall (5 / 4 : ℂ) R))
  (hfc : f (5 / 4 : ℂ) ≠ 0) {ψ : ℝ → ℝ}
  (hψcont : ContinuousOn ψ (Icc (-1 / 4 : ℝ) (5 / 4 : ℝ)))
  (hψzero : ∀ x ∈ Icc (-1 / 4 : ℝ) (5 / 4 : ℝ),
   Real.cos (ψ x) = 0 → f (x : ℂ) = 0)
  (hψdelta : ∀ δ : ℝ, 0 < δ → δ ≤ 3 / 4 →
   |(ψ (1 / 2 + δ) - ψ (1 / 2)) - (ψ (1 / 2) - ψ (1 / 2 - δ))| ≤ E) :
  |ψ (5 / 4) - ψ (1 / 2)| / Real.pi ≤
   (circleAverage (fun z => Real.log ‖f z‖) (5 / 4 : ℂ) R -
    Real.log ‖f (5 / 4 : ℂ)‖) / (2 * Real.log (R / (3 / 4))) + 2 + E / (2 * Real.pi) := by
 let B := (circleAverage (fun z => Real.log ‖f z‖) (5 / 4 : ℂ) R -
  Real.log ‖f (5 / 4 : ℂ)‖) / (2 * Real.log (R / (3 / 4))) + 1 + E / (2 * Real.pi)
 have hc (m : ℕ) (hm : (m : ℝ) * Real.pi < |ψ (5 / 4) - ψ (1 / 2)|) : (m : ℝ) ≤ B := by
  rcases lt_abs.mp hm with hp | hn
  ·exact vgp hR hE hf hfc hψcont hψzero hψdelta hp
  ·apply vgp hR hE hf hfc hψcont.neg
    (ψ := fun x => -ψ x)
   ·intro x hx hz
    exact hψzero x hx (by simpa only [Real.cos_neg] using hz)
   ·intro δ hδ0 hδ1
    convert hψdelta δ hδ0 hδ1 using 1
    rw [show (-ψ (1 / 2 + δ) - -ψ (1 / 2)) -
      (-ψ (1 / 2) - -ψ (1 / 2 - δ)) =
      -((ψ (1 / 2 + δ) - ψ (1 / 2)) -
       (ψ (1 / 2) - ψ (1 / 2 - δ))) by ring, abs_neg]
   ·linarith
 by_cases hz : |ψ (5 / 4) - ψ (1 / 2)| = 0
 ·have hlog : 0 < Real.log (R / (3 / 4)) := Real.log_pos ((one_lt_div (by norm_num)).mpr hR)
  have hh := vaR.vbS
   (by norm_num : (0 : ℝ) < 3 / 4) hR hf hfc
  have hn : 0 ≤ vaR.veh f (5 / 4 : ℂ) (3 / 4) := by
   unfold vaR.veh
   apply finsum_nonneg
   intro u
   exact_mod_cast (hf.mono (closedBall_subset_closedBall hR.le)).divisor_nonneg u
  have hj : 0 ≤ (circleAverage (fun z => Real.log ‖f z‖) (5 / 4 : ℂ) R -
    Real.log ‖f (5 / 4 : ℂ)‖) / (2 * Real.log (R / (3 / 4))) :=
   div_nonneg ((mul_nonneg hn hlog.le).trans hh) (by positivity)
  rw [hz, zero_div]
  positivity
 have hpos : 0 < |ψ (5 / 4) - ψ (1 / 2)| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hz)
 have hB : 0 ≤ B := by simpa only [Nat.cast_zero] using hc 0 (by simpa using hpos)
 have hfinal : |ψ (5 / 4) - ψ (1 / 2)| / Real.pi ≤ B + 1 := by
  by_contra hn
  have hlt : B + 1 < |ψ (5 / 4) - ψ (1 / 2)| / Real.pi := lt_of_not_ge hn
  have hfl := Nat.floor_le (show 0 ≤ B + 1 by linarith)
  have hfr := Nat.lt_floor_add_one (B + 1)
  have hsw : (⌊B + 1⌋₊ : ℝ) * Real.pi < |ψ (5 / 4) - ψ (1 / 2)| := by
   apply (lt_div_iff₀ Real.pi_pos).mp
   exact hfl.trans_lt hlt
  linarith [hc ⌊B + 1⌋₊ hsw]
 dsimp [B] at hfinal
 linarith
end vaa.vab.vdN
end
section
open Filter Real Complex Metric MeasureTheory MeromorphicOn Set Topology
open scoped ComplexConjugate
open vaa.vab.vaR
open vaa.vab.vdN
namespace vaa.vab.veZ
lemma vfn {f g : ℂ → ℂ} {B : ℂ → ℝ} {θ : ℝ → ℝ}
  {R E : ℝ} {n : ℕ} (hR : 3 / 4 < R) (hE : 0 < E) (hn : 0 < n)
  (hf : AnalyticOnNhd ℂ f (closedBall (5 / 4 : ℂ) R))
  (hg : AnalyticOnNhd ℂ g (closedBall (5 / 4 : ℂ) R))
  (hfc : vaw f g n (5 / 4 : ℂ) ≠ 0)
  (hB : CircleIntegrable B (5 / 4 : ℂ) R)
  (hB0 : ∀ z ∈ sphere (5 / 4 : ℂ) R, 0 ≤ B z)
  (hfb : ∀ z ∈ sphere (5 / 4 : ℂ) R, ‖f z‖ ≤ Real.exp (B z))
  (hgb : ∀ z ∈ sphere (5 / 4 : ℂ) R, ‖g z‖ ≤ Real.exp (B z))
  (hθ : ContinuousOn θ (Icc (-1 / 4 : ℝ) (5 / 4 : ℝ)))
  (hzero : ∀ x ∈ Icc (-1 / 4 : ℝ) (5 / 4 : ℝ),
   Real.cos ((n : ℝ) * θ x) = 0 → vaw f g n (x : ℂ) = 0)
  (hdelta : ∀ δ : ℝ, 0 < δ → δ ≤ 3 / 4 →
   |(θ (1 / 2 + δ) - θ (1 / 2)) - (θ (1 / 2) - θ (1 / 2 - δ))| ≤ E) :
  |θ (5 / 4) - θ (1 / 2)| / Real.pi ≤
   (circleAverage B (5 / 4 : ℂ) R -
    Real.log ‖vaw f g n (5 / 4 : ℂ)‖ / n) / (2 * Real.log (R / (3 / 4))) +
    2 / n + E / (2 * Real.pi) := by
 have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
 have hR0 : 0 < R := by linarith
 have hlog : 0 < Real.log (R / (3 / 4)) := Real.log_pos ((one_lt_div (by norm_num)).mpr hR)
 have hpow := vgh hf hg n
 have hpowa : AnalyticOnNhd ℂ (vaw f g n) (closedBall (5 / 4 : ℂ) |R|) := by
  simpa only [abs_of_pos hR0] using hpow
 have hi := (hpowa.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
 have hiB : CircleIntegrable (fun z => (n : ℝ) * B z) (5 / 4 : ℂ) R := by
  unfold CircleIntegrable at hB ⊢
  exact hB.const_mul (n : ℝ)
 have havg := circleAverage_mono hi hiB (by
  rw [abs_of_pos hR0]
  exact fun z hz => vho (hB0 z hz) (hfb z hz) (hgb z hz) n)
 rw [show circleAverage (fun z => (n : ℝ) * B z) (5 / 4 : ℂ) R =
  (n : ℝ) * circleAverage B (5 / 4 : ℂ) R by
   simpa only [smul_eq_mul] using (circleAverage_fun_smul (a := (n : ℝ))
    (f := B) (c := (5 / 4 : ℂ)) (R := R))] at havg
 have hh := vlM hR (mul_pos hn0 hE) hpow hfc (hθ.const_mul (n : ℝ)) hzero
  (fun δ hδ0 hδ1 => by
   rw [show ((n : ℝ) * θ (1 / 2 + δ) - n * θ (1 / 2)) -
    (n * θ (1 / 2) - n * θ (1 / 2 - δ)) =
    n * ((θ (1 / 2 + δ) - θ (1 / 2)) -
     (θ (1 / 2) - θ (1 / 2 - δ))) by ring, abs_mul, Nat.abs_cast]
   exact mul_le_mul_of_nonneg_left (hdelta δ hδ0 hδ1) hn0.le)
 rw [show (n : ℝ) * θ (5 / 4) - n * θ (1 / 2) =
  n * (θ (5 / 4) - θ (1 / 2)) by ring, abs_mul, Nat.abs_cast] at hh
 have hh' : (n : ℝ) * |θ (5 / 4) - θ (1 / 2)| / Real.pi ≤
   ((n : ℝ) * circleAverage B (5 / 4 : ℂ) R -
    Real.log ‖vaw f g n (5 / 4 : ℂ)‖) / (2 * Real.log (R / (3 / 4))) +
    2 + (n : ℝ) * E / (2 * Real.pi) := by
  exact hh.trans (by gcongr)
 have hh'' := div_le_div_of_nonneg_right hh' hn0.le
 convert hh'' using 1 <;> (try field_simp [hn0.ne', hlog.ne', Real.pi_ne_zero])
 all_goals try rfl
lemma vmd {f g : ℂ → ℂ} {B : ℂ → ℝ} {θ : ℝ → ℝ} {R E : ℝ}
  (hR : 3 / 4 < R) (hE : 0 < E)
  (hf : AnalyticOnNhd ℂ f (closedBall (5 / 4 : ℂ) R))
  (hg : AnalyticOnNhd ℂ g (closedBall (5 / 4 : ℂ) R))
  (hfc : f (5 / 4 : ℂ) ≠ 0) (hconj : g (5 / 4 : ℂ) = conj (f (5 / 4 : ℂ)))
  (hB : CircleIntegrable B (5 / 4 : ℂ) R)
  (hB0 : ∀ z ∈ sphere (5 / 4 : ℂ) R, 0 ≤ B z)
  (hfb : ∀ z ∈ sphere (5 / 4 : ℂ) R, ‖f z‖ ≤ Real.exp (B z))
  (hgb : ∀ z ∈ sphere (5 / 4 : ℂ) R, ‖g z‖ ≤ Real.exp (B z))
  (hθ : ContinuousOn θ (Icc (-1 / 4 : ℝ) (5 / 4 : ℝ)))
  (hzero : ∀ n : ℕ, ∀ x ∈ Icc (-1 / 4 : ℝ) (5 / 4 : ℝ),
   Real.cos ((n : ℝ) * θ x) = 0 → vaw f g n (x : ℂ) = 0)
  (hdelta : ∀ δ : ℝ, 0 < δ → δ ≤ 3 / 4 →
   |(θ (1 / 2 + δ) - θ (1 / 2)) - (θ (1 / 2) - θ (1 / 2 - δ))| ≤ E) :
  |θ (5 / 4) - θ (1 / 2)| / Real.pi ≤
   (circleAverage B (5 / 4 : ℂ) R - Real.log ‖f (5 / 4 : ℂ)‖) /
    (2 * Real.log (R / (3 / 4))) + E / (2 * Real.pi) := by
 obtain ⟨n, hn, hp, hl⟩ := vaa.vab.vez hfc
 have hnTop : Tendsto (fun j => (n j : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp hn.tendsto_atTop
 have hnpos : ∀ᶠ j in atTop, 0 < n j := by
  filter_upwards [hnTop.eventually (eventually_gt_atTop (0 : ℝ))] with j hj
  exact_mod_cast hj
 have hratio := vaa.vab.vhc hp
 have hnonzero : ∀ᶠ j in atTop, vaw f g (n j) (5 / 4 : ℂ) ≠ 0 := by
  filter_upwards [hratio.eventually (lt_mem_nhds (zero_lt_one : (0 : ℝ) < 1))]
   with j hj
  rw [vcU hconj]
  apply Complex.ofReal_ne_zero.mpr
  intro hz
  rw [hz, zero_div] at hj
  exact lt_irrefl _ hj
 have hnorm (j : ℕ) : ‖vaw f g (n j) (5 / 4 : ℂ)‖ =
   |(f (5 / 4 : ℂ) ^ n j).re| := by
  rw [vcU hconj, Complex.norm_real, Real.norm_eq_abs]
 have hlim : Tendsto
   (fun j => (circleAverage B (5 / 4 : ℂ) R -
    Real.log ‖vaw f g (n j) (5 / 4 : ℂ)‖ / (n j : ℝ)) /
    (2 * Real.log (R / (3 / 4))) + 2 / (n j : ℝ) + E / (2 * Real.pi))
   atTop (𝓝 ((circleAverage B (5 / 4 : ℂ) R - Real.log ‖f (5 / 4 : ℂ)‖) /
    (2 * Real.log (R / (3 / 4))) + E / (2 * Real.pi))) := by
  simp_rw [hnorm]
  have hz : Tendsto (fun j => (2 : ℝ) / (n j : ℝ)) atTop (𝓝 0) :=
   tendsto_const_nhds.div_atTop hnTop
  simpa using (((tendsto_const_nhds.sub hl).div_const _).add hz).add_const (E / (2 * Real.pi))
 apply ge_of_tendsto hlim
 filter_upwards [hnpos, hnonzero] with j hj hnz
 exact vfn hR hE hj hf hg hnz hB hB0 hfb hgb hθ (hzero (n j)) hdelta
end vaa.vab.veZ
end
section
noncomputable section
open Complex Real MeasureTheory
open scoped Topology ComplexConjugate
namespace vaa.vab.vgs
open vae
lemma vaN {T : ℝ} (hgood : vah T)
  (σ : ℝ) : riemannZeta ((σ : ℂ) + T * Complex.I) ≠ 0 := by
 intro h
 have := hgood _ h
 simp at this
lemma vgd (T σ : ℝ) :
  HasDerivAt (fun u : ℝ => (u : ℂ) + T * Complex.I) 1 σ := by
 have h : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 σ :=
  Complex.ofRealCLM.hasDerivAt (x := σ)
 simpa using h.add_const ((T : ℂ) * Complex.I)
lemma vbs {s : ℂ} (hs : s ≠ 1) :
  AnalyticAt ℂ riemannZeta s := by
 rw [Complex.analyticAt_iff_eventually_differentiableAt]
 filter_upwards [eventually_ne_nhds hs] with z hz
 exact differentiableAt_riemannZeta hz
lemma vcw {T : ℝ} (hT : T ≠ 0) (σ : ℝ) :
  (σ : ℂ) + T * Complex.I ≠ 1 := by
 intro h
 have him := congrArg Complex.im h
 simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re,
  Complex.one_im, zero_add] at him
 exact hT him
lemma viA {T : ℝ} (hT : T ≠ 0) (σ : ℝ) :
  HasDerivAt (fun u : ℝ => riemannZeta ((u : ℂ) + T * Complex.I))
   (deriv riemannZeta ((σ : ℂ) + T * Complex.I)) σ := by
 have hz : HasDerivAt riemannZeta
   (deriv riemannZeta ((σ : ℂ) + T * Complex.I)) ((σ : ℂ) + T * Complex.I) :=
  (differentiableAt_riemannZeta (vcw hT σ)).hasDerivAt
 have h := HasDerivAt.scomp (g₁ := riemannZeta) (h := fun u : ℝ => (u : ℂ) + T * Complex.I) σ
  hz (vgd T σ)
 rw [one_smul] at h
 exact h
lemma vbw {T : ℝ} (hT : T ≠ 0) (hgood : vah T) :
  Continuous (fun σ : ℝ => logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)) := by
 rw [continuous_iff_continuousAt]; intro σ
 have hline : ContinuousAt (fun u : ℝ => (u : ℂ) + T * Complex.I) σ :=
  (Complex.continuous_ofReal.add continuous_const).continuousAt
 have hana : AnalyticAt ℂ riemannZeta ((σ : ℂ) + T * Complex.I) :=
  vbs (vcw hT σ)
 have hζ : ContinuousAt (fun u : ℝ => riemannZeta ((u : ℂ) + T * Complex.I)) σ :=
  ContinuousAt.comp (g := riemannZeta) (f := fun u : ℝ => (u : ℂ) + T * Complex.I)
   hana.continuousAt hline
 have hζ' : ContinuousAt (fun u : ℝ => deriv riemannZeta ((u : ℂ) + T * Complex.I)) σ :=
  ContinuousAt.comp (g := deriv riemannZeta) (f := fun u : ℝ => (u : ℂ) + T * Complex.I)
   hana.deriv.continuousAt hline
 have hne := vaN hgood σ
 have : ContinuousAt (fun u : ℝ =>
   deriv riemannZeta ((u : ℂ) + T * Complex.I) /
    riemannZeta ((u : ℂ) + T * Complex.I)) σ := hζ'.div hζ hne
 simpa only [logDeriv_apply] using this
def vak (T a σ : ℝ) : ℝ :=
 (riemannZeta ((a : ℂ) + T * Complex.I)).arg
  + ∫ u in a..σ, (logDeriv riemannZeta ((u : ℂ) + T * Complex.I)).im
def vaL (T a σ : ℝ) : ℝ :=
 ∫ u in a..σ, (logDeriv riemannZeta ((u : ℂ) + T * Complex.I)).re
def vbu (T a σ : ℝ) : ℂ :=
 riemannZeta ((σ : ℂ) + T * Complex.I) * Complex.exp (-(vak T a σ : ℂ) * Complex.I)
def vlP (T a σ : ℝ) : ℂ :=
 vbu T a σ * Complex.exp (-(vaL T a σ : ℂ))
lemma veW {T : ℝ} (hT : T ≠ 0) (hgood : vah T) (a σ : ℝ) :
  HasDerivAt (vak T a)
   ((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im) σ := by
 have hcont : Continuous (fun u : ℝ => (logDeriv riemannZeta ((u : ℂ) + T * Complex.I)).im) :=
  Complex.continuous_im.comp (vbw hT hgood)
 have hFTC := (hcont.integral_hasStrictDerivAt a σ).hasDerivAt
 unfold vak
 exact hFTC.const_add _
lemma vix {T : ℝ} (hT : T ≠ 0) (hgood : vah T) (a σ : ℝ) :
  HasDerivAt (vaL T a)
   ((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).re) σ := by
 have hcont : Continuous (fun u : ℝ => (logDeriv riemannZeta ((u : ℂ) + T * Complex.I)).re) :=
  Complex.continuous_re.comp (vbw hT hgood)
 have hFTC := (hcont.integral_hasStrictDerivAt a σ).hasDerivAt
 unfold vaL
 exact hFTC
lemma vjs {T : ℝ} (hT : T ≠ 0) (hgood : vah T) (a σ : ℝ) :
  HasDerivAt (vbu T a)
   (((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).re : ℂ) * vbu T a σ) σ := by
 have hne := vaN hgood σ
 have hA : HasDerivAt (fun u : ℝ => riemannZeta ((u : ℂ) + T * Complex.I))
   (deriv riemannZeta ((σ : ℂ) + T * Complex.I)) σ := viA hT σ
 have hθ : HasDerivAt (vak T a)
   ((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im) σ :=
  veW hT hgood a σ
 have hθc : HasDerivAt (fun s => ((vak T a s : ℝ) : ℂ))
   (((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im : ℂ)) σ := hθ.ofReal_comp
 have hexpArg : HasDerivAt (fun s => (-(vak T a s : ℂ)) * Complex.I)
   ((-(((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im : ℂ))) * Complex.I) σ :=
  (hθc.neg).mul_const Complex.I
 have hB : HasDerivAt (fun s => Complex.exp ((-(vak T a s : ℂ)) * Complex.I))
   (Complex.exp ((-(vak T a σ : ℂ)) * Complex.I)
    * ((-(((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im : ℂ))) * Complex.I)) σ :=
  hexpArg.cexp
 have hmul := hA.mul hB
 have hDL : logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)
    * riemannZeta ((σ : ℂ) + T * Complex.I)
   = deriv riemannZeta ((σ : ℂ) + T * Complex.I) := by
  rw [logDeriv_apply]; field_simp
 have hkey : logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)
    - ((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im : ℂ) * Complex.I
   = ((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).re : ℂ) := by
  have := Complex.re_add_im (logDeriv riemannZeta ((σ : ℂ) + T * Complex.I))
  linear_combination -this
 have hval :
   deriv riemannZeta ((σ : ℂ) + T * Complex.I)
     * Complex.exp ((-(vak T a σ : ℂ)) * Complex.I)
    + riemannZeta ((σ : ℂ) + T * Complex.I)
     * (Complex.exp ((-(vak T a σ : ℂ)) * Complex.I)
      * ((-(((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im : ℂ))) * Complex.I))
   = ((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).re : ℂ) * vbu T a σ := by
  unfold vbu
  rw [← hDL]
  linear_combination
   (riemannZeta ((σ : ℂ) + T * Complex.I)
    * Complex.exp ((-(vak T a σ : ℂ)) * Complex.I)) * hkey
 rw [hval] at hmul
 exact hmul
lemma vky {T : ℝ} (hT : T ≠ 0) (hgood : vah T) (a σ : ℝ) :
  HasDerivAt (vlP T a) 0 σ := by
 have hP := vjs hT hgood a σ
 have hgg := vix hT hgood a σ
 have hggc : HasDerivAt (fun s => ((vaL T a s : ℝ) : ℂ))
   (((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).re : ℂ)) σ := hgg.ofReal_comp
 have hExpG : HasDerivAt (fun s => Complex.exp (-(vaL T a s : ℂ)))
   (Complex.exp (-(vaL T a σ : ℂ))
    * (-(((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).re : ℂ)))) σ :=
  (hggc.neg).cexp
 have hmul := hP.mul hExpG
 have hval :
   (((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).re : ℂ) * vbu T a σ)
     * Complex.exp (-(vaL T a σ : ℂ))
    + vbu T a σ
     * (Complex.exp (-(vaL T a σ : ℂ))
      * (-(((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).re : ℂ)))) = 0 := by ring
 rw [hval] at hmul
 exact hmul
lemma vji {T : ℝ} (hT : T ≠ 0) (hgood : vah T) (a σ : ℝ) :
    riemannZeta ((σ : ℂ) + T * Complex.I)
      = (‖riemannZeta ((σ : ℂ) + T * Complex.I)‖ : ℂ)
        * Complex.exp ((vak T a σ : ℂ) * Complex.I) := by
  have hGall : ∀ x, HasDerivAt (vlP T a) 0 x := fun x => vky hT hgood a x
  have hconst := is_const_of_deriv_eq_zero (𝕜 := ℝ)
    (fun x => (hGall x).differentiableAt) (fun x => (hGall x).deriv) σ a
  have hGa : vlP T a a = (‖riemannZeta ((a : ℂ) + T * Complex.I)‖ : ℂ) := by
    unfold vlP vbu vaL vak
    rw [intervalIntegral.integral_same, intervalIntegral.integral_same]
    simp only [Complex.ofReal_zero, neg_zero, Complex.exp_zero, mul_one, add_zero]
    set w := riemannZeta ((a : ℂ) + T * Complex.I) with hw
    nth_rewrite 1 [← Complex.norm_mul_exp_arg_mul_I w]
    rw [mul_assoc, ← Complex.exp_add]
    rw [show (Complex.arg w : ℂ) * Complex.I + (-(Complex.arg w : ℂ)) * Complex.I = 0 by ring]
    rw [Complex.exp_zero, mul_one]
  rw [hGa] at hconst
  have hEne : Complex.exp (-(vaL T a σ : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hGσ : vbu T a σ * Complex.exp (-(vaL T a σ : ℂ))
      = (‖riemannZeta ((a : ℂ) + T * Complex.I)‖ : ℂ) := hconst
  have hEinv : (Complex.exp (-(vaL T a σ : ℂ)))⁻¹
      = ((Real.exp (vaL T a σ)) : ℂ) := by
    rw [Complex.exp_neg, inv_inv, ← Complex.ofReal_exp]
  have hpsiσ : vbu T a σ
      = (‖riemannZeta ((a : ℂ) + T * Complex.I)‖ : ℂ) * ((Real.exp (vaL T a σ)) : ℂ) := by
    have h := eq_div_of_mul_eq hEne hGσ
    rwa [div_eq_mul_inv, hEinv] at h
  have hr_nonneg : 0 ≤ ‖riemannZeta ((a : ℂ) + T * Complex.I)‖ * Real.exp (vaL T a σ) := by
    positivity
  have hpsiσ' : vbu T a σ
      = ((‖riemannZeta ((a : ℂ) + T * Complex.I)‖ * Real.exp (vaL T a σ) : ℝ) : ℂ) := by
    rw [hpsiσ]; push_cast; ring
  have hnormψ : ‖vbu T a σ‖ = ‖riemannZeta ((σ : ℂ) + T * Complex.I)‖ := by
    unfold vbu
    rw [norm_mul, Complex.norm_exp]
    simp
  have hr_eq : ‖riemannZeta ((a : ℂ) + T * Complex.I)‖ * Real.exp (vaL T a σ)
      = ‖riemannZeta ((σ : ℂ) + T * Complex.I)‖ := by
    have h := hnormψ
    rw [hpsiσ', Complex.norm_real, Real.norm_of_nonneg hr_nonneg] at h
    exact h
  have hpsiσ_norm : vbu T a σ = (‖riemannZeta ((σ : ℂ) + T * Complex.I)‖ : ℂ) := by
    rw [hpsiσ', hr_eq]
  have h1 : riemannZeta ((σ : ℂ) + T * Complex.I)
      * Complex.exp (-(vak T a σ : ℂ) * Complex.I)
      = (‖riemannZeta ((σ : ℂ) + T * Complex.I)‖ : ℂ) := by
    have := hpsiσ_norm; unfold vbu at this; exact this
  calc riemannZeta ((σ : ℂ) + T * Complex.I)
      = riemannZeta ((σ : ℂ) + T * Complex.I)
          * Complex.exp (-(vak T a σ : ℂ) * Complex.I)
          * Complex.exp ((vak T a σ : ℂ) * Complex.I) := by
        rw [mul_assoc, ← Complex.exp_add]
        rw [show (-(vak T a σ : ℂ) * Complex.I) + (vak T a σ : ℂ) * Complex.I = 0 by ring]
        rw [Complex.exp_zero, mul_one]
    _ = (‖riemannZeta ((σ : ℂ) + T * Complex.I)‖ : ℂ)
          * Complex.exp ((vak T a σ : ℂ) * Complex.I) := by rw [h1]
lemma vmn {T : ℝ} (hT : T ≠ 0) (hgood : vah T) (a σ : ℝ) (N : ℕ) :
  ((riemannZeta ((σ : ℂ) + T * Complex.I)) ^ N).re
   = ‖riemannZeta ((σ : ℂ) + T * Complex.I)‖ ^ N
    * Real.cos ((N : ℝ) * vak T a σ) := by
 conv_lhs => rw [vji hT hgood a σ]
 rw [mul_pow, ← Complex.exp_nat_mul,
  show (N : ℂ) * ((vak T a σ : ℂ) * Complex.I)
    = ((N : ℝ) * vak T a σ : ℝ) * Complex.I by push_cast; ring,
  ← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
lemma vca {T : ℝ} (hT : T ≠ 0) (hgood : vah T)
  (a x y : ℝ) :
  vak T a x - vak T a y
   = ∫ σ in y..x, (logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im := by
 have hcontIm : Continuous
   (fun u : ℝ => (logDeriv riemannZeta ((u : ℂ) + T * Complex.I)).im) :=
  Complex.continuous_im.comp (vbw hT hgood)
 have hIx : IntervalIntegrable
   (fun u : ℝ => (logDeriv riemannZeta ((u : ℂ) + T * Complex.I)).im)
   volume a x := hcontIm.intervalIntegrable a x
 have hIy : IntervalIntegrable
   (fun u : ℝ => (logDeriv riemannZeta ((u : ℂ) + T * Complex.I)).im)
   volume a y := hcontIm.intervalIntegrable a y
 have hkey := intervalIntegral.integral_interval_sub_left hIx hIy
 unfold vak
 rw [← hkey]
 ring
lemma vjv {T : ℝ} (hT : T ≠ 0) (hgood : vah T)
  (a : ℝ) : Continuous (vak T a) :=
 continuous_iff_continuousAt.mpr fun σ =>
  (veW hT hgood a σ).continuousAt
lemma veY (T x : ℝ) :
  riemannZeta ((x : ℂ) - T * Complex.I) =
   conj (riemannZeta ((x : ℂ) + T * Complex.I)) := by
 rw [← riemannZeta_conj]
 congr 1
 simp [sub_eq_add_neg]
lemma vhX (T x : ℝ) (n : ℕ) :
  vaR.vaw
   (fun z => riemannZeta (z + T * Complex.I))
   (fun z => riemannZeta (z - T * Complex.I)) n (x : ℂ) =
    ((riemannZeta ((x : ℂ) + T * Complex.I) ^ n).re : ℂ) :=
 vaR.vcU (veY T x) n
lemma vee {T : ℝ} (hT : T ≠ 0)
  (hgood : vah T) (a x : ℝ) (n : ℕ)
  (hcos : Real.cos ((n : ℝ) * vak T a x) = 0) :
  vaR.vaw
   (fun z => riemannZeta (z + T * Complex.I))
   (fun z => riemannZeta (z - T * Complex.I)) n (x : ℂ) = 0 := by
 rw [vhX, vmn hT hgood a x n, hcos, mul_zero,
  Complex.ofReal_zero]
lemma vfg {T : ℝ} (hT : T ≠ 0)
  (hgood : vah T) (a δ : ℝ) :
  (vak T a (1 / 2 + δ) - vak T a (1 / 2)) -
   (vak T a (1 / 2) - vak T a (1 / 2 - δ)) =
   ∫ σ in (1 / 2 : ℝ)..(1 / 2 + δ),
    vcf.vbz σ T := by
 let f : ℝ → ℝ := fun σ =>
  (logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im
 have hc : Continuous f :=
  Complex.continuous_im.comp (vbw hT hgood)
 have hrc : Continuous (fun σ => f (1 - σ)) :=
  hc.comp (continuous_const.sub continuous_id)
 rw [vca hT hgood a (1 / 2 + δ) (1 / 2),
  vca hT hgood a (1 / 2) (1 / 2 - δ)]
 change (∫ σ in (1 / 2 : ℝ)..(1 / 2 + δ), f σ) -
   (∫ σ in (1 / 2 - δ : ℝ)..(1 / 2), f σ) =
   ∫ σ in (1 / 2 : ℝ)..(1 / 2 + δ), f σ - f (1 - σ)
 rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _)
  (hrc.intervalIntegrable _ _)]
 congr 1
 convert (intervalIntegral.integral_comp_sub_left f (a := (1 / 2 : ℝ))
  (b := 1 / 2 + δ) 1).symm using 1 <;> congr 1 <;> ring
lemma vhL {T δ : ℝ} (hT : 1 ≤ T)
  (hgood : vah T) (a : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4) :
  |(vak T a (1 / 2 + δ) - vak T a (1 / 2)) -
   (vak T a (1 / 2) - vak T a (1 / 2 - δ))| ≤ 4 * δ ^ 2 / T := by
 rw [vfg (by linarith : T ≠ 0) hgood a δ]
 exact vcf.vcK hT hδ0 hδ1
  (fun σ _ => ⟨vaN hgood σ,
   vaN hgood (1 - σ)⟩)
lemma vdU {T δ : ℝ} (hT : 1 ≤ T)
  (hgood : vah T) (a : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4) :
  |(vak T a (1 / 2 + δ) - vak T a (1 / 2)) -
   (vak T a (1 / 2) - vak T a (1 / 2 - δ))| ≤ 4 / T := by
 refine (vhL hT hgood a hδ0 hδ1).trans ?_
 apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ T)
 nlinarith
lemma vfe {T R : ℝ} (hRT : R < T) :
  AnalyticOnNhd ℂ (fun z => riemannZeta (z + T * Complex.I))
    (Metric.closedBall (5 / 4 : ℂ) R) ∧
   AnalyticOnNhd ℂ (fun z => riemannZeta (z - T * Complex.I))
    (Metric.closedBall (5 / 4 : ℂ) R) := by
 have him (z : ℂ) (hz : z ∈ Metric.closedBall (5 / 4 : ℂ) R) : |z.im| ≤ R := by
  have hd : ‖z - (5 / 4 : ℂ)‖ ≤ R := by
   simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have hi := Complex.abs_im_le_norm (z - (5 / 4 : ℂ))
  simpa using hi.trans hd
 constructor
 ·intro z hz
  have hp : z + T * Complex.I ≠ 1 := by
   intro he
   have hh := congrArg Complex.im he
   simp only [Complex.add_im, Complex.mul_I_im, Complex.ofReal_re, Complex.one_im] at hh
   have hb := (abs_le.mp (him z hz)).1
   linarith
  exact (vbs hp).comp
   (f := fun w : ℂ => w + T * Complex.I) (x := z)
   (analyticAt_id.add analyticAt_const)
 ·intro z hz
  have hp : z - T * Complex.I ≠ 1 := by
   intro he
   have hh := congrArg Complex.im he
   simp only [Complex.sub_im, Complex.mul_I_im, Complex.ofReal_re, Complex.one_im] at hh
   have hb := (abs_le.mp (him z hz)).2
   linarith
  exact (vbs hp).comp
   (f := fun w : ℂ => w - T * Complex.I) (x := z)
   (analyticAt_id.sub analyticAt_const)
lemma vgA {T R : ℝ} {B : ℂ → ℝ}
  (hT : 1 ≤ T) (hgood : vah T)
  (hR : 3 / 4 < R) (hRT : R < T)
  (hB : CircleIntegrable B (5 / 4 : ℂ) R)
  (hB0 : ∀ z ∈ Metric.sphere (5 / 4 : ℂ) R, 0 ≤ B z)
  (hfb : ∀ z ∈ Metric.sphere (5 / 4 : ℂ) R,
   ‖riemannZeta (z + T * Complex.I)‖ ≤ Real.exp (B z))
  (hgb : ∀ z ∈ Metric.sphere (5 / 4 : ℂ) R,
   ‖riemannZeta (z - T * Complex.I)‖ ≤ Real.exp (B z)) :
  |∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ),
   (logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im| / Real.pi ≤
   (circleAverage B (5 / 4 : ℂ) R -
    Real.log ‖riemannZeta ((5 / 4 : ℂ) + T * Complex.I)‖) /
     (2 * Real.log (R / (3 / 4))) + 2 / (Real.pi * T) := by
 have hT0 : 0 < T := by linarith
 obtain ⟨hf, hg⟩ := vfe hRT
 have h := veZ.vmd
  (f := fun z => riemannZeta (z + T * Complex.I))
  (g := fun z => riemannZeta (z - T * Complex.I))
  (θ := vak T (5 / 4)) (E := 4 / T) hR (by positivity) hf hg
  (by simpa using vaN hgood (5 / 4))
  (by simpa using veY T (5 / 4)) hB hB0 hfb hgb
  (vjv hT0.ne' hgood (5 / 4)).continuousOn
  (fun n x _ hx => vee hT0.ne' hgood (5 / 4) x n hx)
  (fun δ hδ0 hδ1 => vdU hT hgood (5 / 4) hδ0.le hδ1)
 rw [vca hT0.ne' hgood (5 / 4) (5 / 4) (1 / 2)] at h
 convert h using 1 <;> (try ring)
 all_goals try rfl
end vaa.vab.vgs
end
end
section
open Complex Filter Set MeasureTheory
open scoped Topology Interval
namespace vaa.vab.vam
lemma vfk {N : ℝ} (hN : 1 ≤ N) {z₁ z₂ : ℂ}
  (h1 : N ≤ z₁.re) (h2 : N ≤ z₂.re) :
  ‖Complex.digamma z₁ - Complex.digamma z₂‖ ≤ 2 * ‖z₁ - z₂‖ / N := by
 have hn1 := vac.vat
  (vac.van.mpr (by linarith : 0 < z₁.re))
 have hn2 := vac.vat
  (vac.van.mpr (by linarith : 0 < z₂.re))
 have hs1 := vac.vau hn1
 have hs2 := vac.vau hn2
 have hdiff : Complex.digamma z₁ - Complex.digamma z₂ =
   ∑' k, (vac.vaf z₁ k - vac.vaf z₂ k) := by
  rw [vac.vbc (by linarith),
   vac.vbc (by linarith),
   vac.gaussSum, vac.gaussSum, hs1.tsum_sub hs2]
  ring
 have hk : ∀ k : ℕ, ‖vac.vaf z₁ k - vac.vaf z₂ k‖ ≤
   ‖z₁ - z₂‖ * (2 * (((k : ℝ) + N) * ((k : ℝ) + N + 1))⁻¹) := by
  intro k
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hk1 : (0 : ℝ) < k + N := by linarith
  have hz1 : ((k : ℂ) + z₁) ≠ 0 := fun h => hn1 k (by linear_combination h)
  have hz2 : ((k : ℂ) + z₂) ≠ 0 := fun h => hn2 k (by linear_combination h)
  have he : vac.vaf z₁ k - vac.vaf z₂ k =
    (z₁ - z₂) / (((k : ℂ) + z₁) * ((k : ℂ) + z₂)) := by
   simp only [vac.vaf]
   field_simp
   ring
  have hnz1 : (k : ℝ) + N ≤ ‖(k : ℂ) + z₁‖ := by
   have hh := Complex.re_le_norm ((k : ℂ) + z₁)
   simp only [add_re, natCast_re] at hh
   linarith
  have hnz2 : (k : ℝ) + N ≤ ‖(k : ℂ) + z₂‖ := by
   have hh := Complex.re_le_norm ((k : ℂ) + z₂)
   simp only [add_re, natCast_re] at hh
   linarith
  have hp : ((k : ℝ) + N) ^ 2 ≤ ‖((k : ℂ) + z₁) * ((k : ℂ) + z₂)‖ := by
   rw [norm_mul, pow_two]
   exact mul_le_mul hnz1 hnz2 hk1.le (norm_nonneg _)
  have hc : 1 / ((k : ℝ) + N) ^ 2 ≤
    2 * (((k : ℝ) + N) * ((k : ℝ) + N + 1))⁻¹ := by
   change 1 / ((k : ℝ) + N) ^ 2 ≤
    2 / (((k : ℝ) + N) * ((k : ℝ) + N + 1))
   rw [div_le_div_iff₀ (sq_pos_of_pos hk1) (by positivity)]
   nlinarith
  rw [he, norm_div]
  calc
   _ ≤ ‖z₁ - z₂‖ / ((k : ℝ) + N) ^ 2 :=
    div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hk1) hp
   _ = ‖z₁ - z₂‖ * (1 / ((k : ℝ) + N) ^ 2) := by ring
   _ ≤ _ := mul_le_mul_of_nonneg_left hc (norm_nonneg _)
 have htele := vac.vdC (t := N) hN ‖z₁ - z₂‖
 have hsumn : Summable (fun k : ℕ =>
   ‖vac.vaf z₁ k - vac.vaf z₂ k‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hk htele.summable
 rw [hdiff]
 calc
  _ ≤ ∑' k, ‖vac.vaf z₁ k - vac.vaf z₂ k‖ :=
   norm_tsum_le_tsum_norm hsumn
  _ ≤ ‖z₁ - z₂‖ * (2 * N⁻¹) := by
   rw [← htele.tsum_eq]
   exact Summable.tsum_le_tsum hk hsumn htele.summable
  _ = _ := by simp only [div_eq_mul_inv]; ring
noncomputable def vba (a τ : ℝ) : ℝ :=
 ∫ t in (0 : ℝ)..τ, (Complex.digamma ((a : ℂ) + t * I)).re
lemma vcC {a : ℝ} (ha : 0 < a) :
  Continuous (fun t : ℝ ↦ Complex.digamma ((a : ℂ) + t * I)) := by
 rw [continuous_iff_continuousAt]
 intro t
 exact (vby (by simpa using ha)).continuousAt.comp
  (by fun_prop : ContinuousAt (fun t : ℝ ↦ (a : ℂ) + t * I) t)
lemma veB {N t : ℝ} (hN : 1 ≤ N) (ht : 0 ≤ t) :
  |(Complex.digamma (((N + 1 / 4 : ℝ) : ℂ) + t * I)).re - Real.log N| ≤
   (2 * t + 5 / 4) / N := by
 have hN0 : 0 < N := by linarith
 have hx : 0 < N + 1 / 4 := by linarith
 have hd := vfk hN
  (z₁ := (((N + 1 / 4 : ℝ) : ℂ) + t * I))
  (z₂ := ((N + 1 / 4 : ℝ) : ℂ))
  (by simp) (by simp)
 have hnorm : ‖(((N + 1 / 4 : ℝ) : ℂ) + t * I) - ((N + 1 / 4 : ℝ) : ℂ)‖ = t := by
  simp [norm_mul, Real.norm_eq_abs, abs_of_nonneg ht]
 rw [hnorm] at hd
 have hreal : |(Complex.digamma ((N + 1 / 4 : ℝ) : ℂ)).re - Real.log (N + 1 / 4)| ≤
   1 / (N + 1 / 4) := by
  rw [vac.vdo hx, Complex.ofReal_re]
  exact vac.vbB hx
 have hi : 1 / (N + 1 / 4) ≤ 1 / N :=
  one_div_le_one_div_of_le hN0 (by linarith)
 have hlog : |Real.log (N + 1 / 4) - Real.log N| ≤ (1 / 4) / N := by
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hN0 (by linarith)))]
  have hh := Real.log_le_sub_one_of_pos (div_pos hx hN0)
  rw [Real.log_div hx.ne' hN0.ne'] at hh
  have he : (N + 1 / 4) / N - 1 = (1 / 4) / N := by field_simp; ring
  rwa [he] at hh
 have hre := (Complex.abs_re_le_norm
  (Complex.digamma (((N + 1 / 4 : ℝ) : ℂ) + t * I) -
   Complex.digamma ((N + 1 / 4 : ℝ) : ℂ))).trans hd
 rw [Complex.sub_re] at hre
 have he : (2 * t + 5 / 4) / N = 2 * t / N + 1 / N + (1 / 4) / N := by ring
 rw [he, abs_le]
 rcases abs_le.mp hre with ⟨hrelo, hrehi⟩
 rcases abs_le.mp hreal with ⟨hrlo, hrhi⟩
 rcases abs_le.mp hlog with ⟨hllo, hlhi⟩
 constructor <;> linarith
lemma vfw {N τ : ℝ} (hN : 1 ≤ N) (hτ : 0 ≤ τ) :
  |vba (N + 1 / 4) τ - τ * Real.log N| ≤
   τ * (2 * τ + 5 / 4) / N := by
 have hx : 0 < N + 1 / 4 := by linarith
 have hi : IntervalIntegrable
   (fun t : ℝ ↦ (Complex.digamma (((N + 1 / 4 : ℝ) : ℂ) + t * I)).re) volume 0 τ :=
  (Complex.continuous_re.comp (vcC hx)).intervalIntegrable 0 τ
 have he : vba (N + 1 / 4) τ - τ * Real.log N =
   ∫ t in (0 : ℝ)..τ,
    ((Complex.digamma (((N + 1 / 4 : ℝ) : ℂ) + t * I)).re - Real.log N) := by
  rw [intervalIntegral.integral_sub hi intervalIntegrable_const]
  simp [vba, smul_eq_mul]
 rw [he, ← Real.norm_eq_abs]
 calc
  _ ≤ ∫ _t in (0 : ℝ)..τ, (2 * τ + 5 / 4) / N := by
   apply intervalIntegral.norm_integral_le_of_norm_le hτ
   ·filter_upwards with t ht
    rw [Real.norm_eq_abs]
    exact (veB hN ht.1.le).trans
     (div_le_div_of_nonneg_right (by linarith [ht.2]) (by linarith))
   ·exact intervalIntegrable_const
  _ = _ := by simp [smul_eq_mul]; ring
lemma veS {τ : ℝ} (hτ : 0 ≤ τ) :
  Tendsto (fun N : ℕ ↦ vba ((N : ℝ) + 1 / 4) τ - τ * Real.log N)
   atTop (𝓝 0) := by
 apply tendsto_zero_iff_norm_tendsto_zero.mpr
 apply squeeze_zero' (g := fun N : ℕ ↦ τ * (2 * τ + 5 / 4) / (N : ℝ))
  (Filter.Eventually.of_forall (fun _ ↦ norm_nonneg _))
 ·filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  rw [Real.norm_eq_abs]
  exact vfw (by exact_mod_cast hN) hτ
 ·exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
end vaa.vab.vam
end
section
open Complex Real Filter MeasureTheory intervalIntegral
open scoped Topology Interval
namespace vaa.vab.vam
lemma vfh {c : ℝ} (hc : 0 < c) (τ : ℝ) :
  ∫ t in (0:ℝ)..τ, c / (c ^ 2 + t ^ 2) = Real.arctan (τ / c) := by
 have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) τ,
   HasDerivAt (fun u : ℝ => Real.arctan (u / c)) (c / (c ^ 2 + t ^ 2)) t := by
  intro t _
  have h1 : HasDerivAt (fun u : ℝ => u / c) (1 / c) t := by
   simpa [-Complex.ofReal_arctan] using (hasDerivAt_id t).div_const c
  have h2 := h1.arctan
  convert h2 using 1
  have hden : (0:ℝ) < 1 + (t / c) ^ 2 := by positivity
  field_simp
 have hcont : ContinuousOn (fun t : ℝ => c / (c ^ 2 + t ^ 2)) (Set.uIcc 0 τ) := by
  apply ContinuousOn.div (g := fun t : ℝ => c ^ 2 + t ^ 2) continuousOn_const (by fun_prop)
  intro t _
  positivity
 have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
  hcont.intervalIntegrable
 simpa [-Complex.ofReal_arctan] using this
lemma vlL {a : ℝ} (ha : 0 < a) (τ : ℝ) :
  vba (a + 1) τ = vba a τ + Real.arctan (τ / a) := by
 have he : ∀ t : ℝ, (Complex.digamma (((a + 1 : ℝ) : ℂ) + t * I)).re =
   (Complex.digamma ((a : ℂ) + t * I)).re + a / (a ^ 2 + t ^ 2) := by
  intro t
  have hn := vac.vat
   (s := (a : ℂ) + t * I)
   (vac.van.mpr (by simpa [-Complex.ofReal_arctan] using ha))
  have hrec := Complex.digamma_apply_add_one ((a : ℂ) + t * I) hn
  have harg : (a : ℂ) + t * I + 1 = ((a + 1 : ℝ) : ℂ) + t * I := by
   push_cast
   ring
  rw [harg] at hrec
  rw [hrec, Complex.add_re, Complex.inv_re, Complex.normSq_apply]
  simp [-Complex.ofReal_arctan, pow_two]
 have hi : IntervalIntegrable (fun t : ℝ ↦ (Complex.digamma ((a : ℂ) + t * I)).re) volume 0 τ :=
  (Complex.continuous_re.comp (vcC ha)).intervalIntegrable 0 τ
 have hj : IntervalIntegrable (fun t : ℝ ↦ a / (a ^ 2 + t ^ 2)) volume 0 τ := by
  apply Continuous.intervalIntegrable
  apply Continuous.div (g := fun t : ℝ => a ^ 2 + t ^ 2) continuous_const (by fun_prop)
  intro t
  positivity
 unfold vba
 simp_rw [he]
 rw [intervalIntegral.integral_add hi hj, vfh ha τ]
lemma vlN {a : ℝ} (ha : 0 < a) (τ : ℝ) (N : ℕ) :
  vba (a + N) τ = vba a τ +
   ∑ k ∈ Finset.range N, Real.arctan (τ / (a + k)) := by
 induction N with
 | zero => simp [-Complex.ofReal_arctan]
 | succ N ih =>
  have hpos : 0 < a + (N : ℝ) := by positivity
  rw [Nat.cast_add_one, ← add_assoc, vlL hpos, ih, Finset.sum_range_succ]
  ring
lemma vga {τ : ℝ} (hτ : 0 ≤ τ) :
  Tendsto (fun N : ℕ ↦ τ * Real.log N -
    ∑ k ∈ Finset.range N, Real.arctan (τ / (1 / 4 + (k : ℝ))))
   atTop (𝓝 (vba (1 / 4) τ)) := by
 have hlim : Tendsto (fun N : ℕ ↦ vba (1 / 4) τ -
   (vba ((N : ℝ) + 1 / 4) τ - τ * Real.log N))
   atTop (𝓝 (vba (1 / 4) τ - 0)) :=
  tendsto_const_nhds.sub (veS hτ)
 have he : ∀ N : ℕ, vba (1 / 4) τ -
   (vba ((N : ℝ) + 1 / 4) τ - τ * Real.log N) =
   τ * Real.log N - ∑ k ∈ Finset.range N, Real.arctan (τ / (1 / 4 + (k : ℝ))) := by
  intro N
  rw [add_comm (N : ℝ) (1 / 4), vlN (by norm_num : (0 : ℝ) < 1 / 4)]
  ring
 simp only [sub_zero, he] at hlim
 exact hlim
lemma vly {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x := by
 have hmono : MonotoneOn (fun u : ℝ => u - Real.arctan u) (Set.Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  ·exact (continuous_id.sub Real.continuous_arctan).continuousOn
  ·exact (differentiable_id.sub Real.differentiable_arctan).differentiableOn
  ·intro u _
   have hd : HasDerivAt (fun u : ℝ => u - Real.arctan u)
     (1 - 1 / (1 + u ^ 2)) u := (hasDerivAt_id u).sub (Real.hasDerivAt_arctan u)
   rw [hd.deriv]
   have : (0:ℝ) < 1 + u ^ 2 := by positivity
   rw [sub_nonneg, div_le_one this]
   nlinarith
 have := hmono (Set.mem_Ici.mpr (le_refl (0 : ℝ))) (Set.mem_Ici.mpr hx) hx
 simpa [-Complex.ofReal_arctan, Real.arctan_zero] using this
end vaa.vab.vam
end
section
open Real Filter MeasureTheory intervalIntegral
open scoped Topology Interval
namespace vaa.vab.vam
lemma vbq {τ x : ℝ} (hx : 0 < x) :
  HasDerivAt (fun u : ℝ ↦ Real.arctan (τ / u)) (-τ / (x ^ 2 + τ ^ 2)) x := by
 have h := ((hasDerivAt_const x τ).div (hasDerivAt_id x) hx.ne').arctan
 simp only [Pi.div_apply, id_eq, zero_mul, zero_sub, mul_one] at h
 convert h using 1
 have hden : 0 < 1 + (τ / x) ^ 2 := by positivity
 field_simp <;> ring
lemma vdY {τ x : ℝ} (hx : 0 < x) :
  HasDerivAt (fun u : ℝ ↦ -τ / (u ^ 2 + τ ^ 2))
   (2 * τ * x / (x ^ 2 + τ ^ 2) ^ 2) x := by
 have hden : 0 < x ^ 2 + τ ^ 2 := by positivity
 have h := (hasDerivAt_const x (-τ)).div
  ((hasDerivAt_pow 2 x).add_const (τ ^ 2)) hden.ne'
 exact h.congr_deriv (by norm_num <;> ring)
noncomputable def vaq (τ x : ℝ) : ℝ :=
 x * Real.arctan (τ / x) + τ / 2 * Real.log (x ^ 2 + τ ^ 2)
lemma vgg {τ x : ℝ} (hx : 0 < x) :
  HasDerivAt (vaq τ) (Real.arctan (τ / x)) x := by
 have hden : 0 < x ^ 2 + τ ^ 2 := by positivity
 have hlog := (((hasDerivAt_pow 2 x).add_const (τ ^ 2)).log hden.ne').const_mul (τ / 2)
 have hp := (hasDerivAt_id x).mul (vbq (τ := τ) hx)
 refine (hp.add hlog).congr_deriv ?_
 simp only [id_eq]
 norm_num
 field_simp
 ring
lemma vhn {a : ℝ} (ha : 0 < a) (τ : ℝ) (N : ℕ) :
  (∫ x in a..(a + N), Real.arctan (τ / x)) =
   vaq τ (a + N) - vaq τ a := by
 have hle : a ≤ a + (N : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg N)
 apply intervalIntegral.integral_eq_sub_of_hasDerivAt
 ·intro x hx
  rw [Set.uIcc_of_le hle] at hx
  exact vgg (ha.trans_le hx.1)
 ·apply ContinuousOn.intervalIntegrable
  intro x hx
  rw [Set.uIcc_of_le hle] at hx
  exact (vbq (τ := τ) (ha.trans_le hx.1)).continuousAt.continuousWithinAt
lemma vfu {a τ : ℝ} (ha : 0 < a) (hτ : 0 < τ) :
  Tendsto (fun N : ℕ ↦ ((N : ℝ) + a) * Real.arctan (τ / ((N : ℝ) + a)))
   atTop (𝓝 τ) := by
 have hr : Tendsto (fun N : ℕ ↦ τ / ((N : ℝ) + a)) atTop (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  ·exact tendsto_const_nhds.div_atTop
    (tendsto_atTop_add_const_right _ a tendsto_natCast_atTop_atTop)
  ·exact Filter.Eventually.of_forall (fun N ↦ div_pos hτ (add_pos_of_nonneg_of_pos (Nat.cast_nonneg N) ha))
 have hs : Tendsto (fun u : ℝ ↦ Real.arctan u / u) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hh := (Real.hasDerivAt_arctan 0).tendsto_slope.mono_left
   (nhdsGT_le_nhdsNE (0 : ℝ))
  simpa [-Complex.ofReal_arctan, slope_fun_def_field] using hh
 have hm := (hs.comp hr).mul_const τ
 convert hm using 1
 ·funext N
  have hn : (N : ℝ) + a ≠ 0 := by positivity
  dsimp only [Function.comp_apply]
  field_simp [hn, hτ.ne'] <;> ring
 ·ring
lemma vet {a τ : ℝ} (ha : 0 < a) (hτ : 0 < τ) :
  Tendsto (fun N : ℕ ↦ vaq τ (a + N) - τ * Real.log N)
   atTop (𝓝 τ) := by
 have harg := vfu ha hτ
 have hd : Tendsto (fun N : ℕ ↦ Real.log ((N : ℝ) + a) - Real.log N)
   atTop (𝓝 0) :=
  (Real.tendsto_log_comp_add_sub_log a).comp tendsto_natCast_atTop_atTop
 have hr : Tendsto (fun N : ℕ ↦ τ / ((N : ℝ) + a)) atTop (𝓝 (0 : ℝ)) :=
  tendsto_const_nhds.div_atTop
   (tendsto_atTop_add_const_right _ a tendsto_natCast_atTop_atTop)
 have hl : Tendsto (fun N : ℕ ↦ Real.log (1 + (τ / ((N : ℝ) + a)) ^ 2))
   atTop (𝓝 0) := by
  have hh := (tendsto_const_nhds.add (hr.pow 2)).log (by norm_num : (1 : ℝ) + 0 ^ 2 ≠ 0)
  simpa [-Complex.ofReal_arctan] using hh
 have hm := (harg.add (hd.const_mul τ)).add (hl.const_mul (τ / 2))
 convert hm using 1
 ·funext N
  have hx : 0 < (N : ℝ) + a := by positivity
  have he : ((N : ℝ) + a) ^ 2 + τ ^ 2 =
    ((N : ℝ) + a) ^ 2 * (1 + (τ / ((N : ℝ) + a)) ^ 2) := by
   field_simp <;> ring
  dsimp [vaq]
  rw [add_comm a (N : ℝ), he, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  ring
 ·ring
lemma vjD {τ : ℝ} (hτ : 0 < τ) :
  vaq τ (1 / 4) - Real.arctan (τ / (1 / 4)) / 2 - τ -
    (τ * Real.log τ - τ - Real.pi / 8) =
   τ / 2 * Real.log (1 + ((1 / 4) / τ) ^ 2) +
    (1 / 4) * Real.arctan ((1 / 4) / τ) := by
 have he : (1 / 4 : ℝ) ^ 2 + τ ^ 2 = τ ^ 2 * (1 + ((1 / 4) / τ) ^ 2) := by
  field_simp
  ring
 have hat : Real.arctan (τ / (1 / 4)) = Real.pi / 2 - Real.arctan ((1 / 4) / τ) := by
  simpa only [inv_div] using Real.arctan_inv_of_pos (by positivity : 0 < (1 / 4 : ℝ) / τ)
 unfold vaq
 rw [hat, he, Real.log_mul (by positivity) (by positivity), Real.log_pow]
 ring
lemma vhC {τ : ℝ} (hτ : 0 < τ) :
  0 ≤ vaq τ (1 / 4) - Real.arctan (τ / (1 / 4)) / 2 - τ -
    (τ * Real.log τ - τ - Real.pi / 8) ∧
  vaq τ (1 / 4) - Real.arctan (τ / (1 / 4)) / 2 - τ -
    (τ * Real.log τ - τ - Real.pi / 8) ≤ 3 / (32 * τ) := by
 rw [vjD hτ]
 have hl0 : 0 ≤ Real.log (1 + ((1 / 4) / τ) ^ 2) :=
  Real.log_nonneg (by nlinarith [sq_nonneg ((1 / 4 : ℝ) / τ)])
 have ha0 : 0 ≤ Real.arctan ((1 / 4) / τ) := Real.arctan_nonneg.mpr (by positivity)
 have hlu : Real.log (1 + ((1 / 4) / τ) ^ 2) ≤ ((1 / 4) / τ) ^ 2 := by
  have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + ((1 / 4 : ℝ) / τ) ^ 2)
  linarith
 have hau := vly (by positivity : 0 ≤ (1 / 4 : ℝ) / τ)
 constructor
 ·positivity
 ·calc
   _ ≤ τ / 2 * (((1 / 4) / τ) ^ 2) + (1 / 4) * ((1 / 4) / τ) := by gcongr
   _ = 3 / (32 * τ) := by field_simp; ring
end vaa.vab.vam
end
section
open Set MeasureTheory intervalIntegral
open scoped Interval
namespace vaa.vab.vdD
noncomputable section
def kernel (a x : ℝ) : ℝ := (x - a) * (a + 1 - x) / 2
lemma vmz {a x : ℝ} (hx : x ∈ Icc a (a + 1)) :
  0 ≤ kernel a x := by
 unfold kernel
 exact div_nonneg (mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2))
  (by norm_num)
lemma voh {a x : ℝ} : kernel a x ≤ 1 / 8 := by
 unfold kernel
 nlinarith [sq_nonneg (x - a - 1 / 2)]
lemma vkr (a x : ℝ) :
  HasDerivAt (kernel a) (a + 1 / 2 - x) x := by
 change HasDerivAt (fun y : ℝ => (y - a) * (a + 1 - y) / 2) _ x
 exact ((((hasDerivAt_id x).sub_const a).mul
  ((hasDerivAt_id x).const_sub (a + 1))).div_const 2).congr_deriv (by simp only [id_eq]; ring)
lemma vhf {f f' f'' : ℝ → ℝ} {a : ℝ}
  (hf : ∀ x ∈ Icc a (a + 1), HasDerivAt f (f' x) x)
  (hf' : ∀ x ∈ Icc a (a + 1), HasDerivAt f' (f'' x) x)
  (hfi : IntervalIntegrable f'' volume a (a + 1)) :
  trapezoidal_error f 1 a (a + 1) =
   ∫ x in a..(a + 1), kernel a x * f'' x := by
 have hab : a ≤ a + 1 := by linarith
 have hu : [[a, a + 1]] = Icc a (a + 1) := uIcc_of_le hab
 have hf0 : ContinuousOn f [[a, a + 1]] := by
  rw [hu]; exact fun x hx => (hf x hx).continuousAt.continuousWithinAt
 have hf1 : ContinuousOn f' [[a, a + 1]] := by
  rw [hu]; exact fun x hx => (hf' x hx).continuousAt.continuousWithinAt
 have hK : Continuous (kernel a) := by unfold kernel; fun_prop
 have hL : Continuous (fun x : ℝ => a + 1 / 2 - x) := by fun_prop
 have h1 := integral_mul_deriv_eq_deriv_mul
  (a := a) (b := a + 1)
  (fun x _ => vkr a x)
  (fun x hx => hf' x (hu ▸ hx)) (hL.intervalIntegrable _ _) hfi
 have h2 := integral_mul_deriv_eq_deriv_mul
  (a := a) (b := a + 1)
  (fun x _ => (hasDerivAt_id x).const_sub (a + 1 / 2))
  (fun x hx => hf x (hu ▸ hx))
  (continuous_const.intervalIntegrable _ _) hf1.intervalIntegrable
 have hneg : (∫ x in a..(a + 1), (-1 : ℝ) * f x) =
   -(∫ x in a..(a + 1), f x) := by simp
 rw [hneg] at h2
 have hKa : kernel a a = 0 := by simp [kernel]
 have hKb : kernel a (a + 1) = 0 := by simp [kernel]
 rw [hKa, hKb, zero_mul, zero_mul, sub_self, zero_sub] at h1
 rw [trapezoidal_error, trapezoidal_integral_one]
 simp only [id_eq] at h2
 ring_nf at h1 h2 ⊢
 linarith
lemma vni {f f' f'' : ℝ → ℝ} {a : ℝ}
  (hf : ∀ x ∈ Icc a (a + 1), HasDerivAt f (f' x) x)
  (hf' : ∀ x ∈ Icc a (a + 1), HasDerivAt f' (f'' x) x)
  (hfi : IntervalIntegrable f'' volume a (a + 1))
  (hnn : ∀ x ∈ Icc a (a + 1), 0 ≤ f'' x) :
  0 ≤ trapezoidal_error f 1 a (a + 1) ∧
   trapezoidal_error f 1 a (a + 1) ≤ (f' (a + 1) - f' a) / 8 := by
 rw [vhf hf hf' hfi]
 have hab : a ≤ a + 1 := by linarith
 have hK : Continuous (kernel a) := by unfold kernel; fun_prop
 have hki : IntervalIntegrable (fun x => kernel a x * f'' x) volume a (a + 1) :=
  hfi.continuousOn_mul hK.continuousOn
 constructor
 ·exact integral_nonneg hab (fun x hx => mul_nonneg (vmz hx) (hnn x hx))
 ·have hbound := integral_mono_on hab hki (hfi.const_mul (1 / 8 : ℝ))
   (fun x hx => mul_le_mul_of_nonneg_right voh (hnn x hx))
  have he := integral_eq_sub_of_hasDerivAt
   (fun x hx => hf' x ((uIcc_of_le hab) ▸ hx)) hfi
  rw [intervalIntegral.integral_const_mul, he] at hbound
  linarith
lemma vmU {f : ℝ → ℝ} {a : ℝ} (N : ℕ)
  (hi : ∀ k < N, IntervalIntegrable f volume (a + k) (a + k + 1)) :
  (∑ k ∈ Finset.range N, trapezoidal_error f 1 (a + k) (a + k + 1)) =
   (∑ k ∈ Finset.range N, f (a + k)) + (f (a + N) - f a) / 2 -
    ∫ x in a..(a + N), f x := by
 have hi' := sum_integral_adjacent_intervals (a := fun k : ℕ => a + k)
  (f := f) (n := N) (fun k hk => by simpa [Nat.cast_add, add_assoc] using hi k hk)
 simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, ← add_assoc] at hi'
 have hs := Finset.sum_range_succ' (fun k : ℕ => f (a + k)) N
 rw [Finset.sum_range_succ] at hs
 simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, ← add_assoc] at hs
 simp_rw [trapezoidal_error, trapezoidal_integral_one,
  show ∀ k : ℕ, (a + k + 1 - (a + k)) / 2 = (1 / 2 : ℝ) by intro k; ring]
 rw [Finset.sum_sub_distrib, hi', ← Finset.mul_sum, Finset.sum_add_distrib]
 linarith
end
end vaa.vab.vdD
end
section
open Real Filter MeasureTheory intervalIntegral
open scoped Topology Interval
namespace vaa.vab.vam
lemma vgV {a τ : ℝ} (ha : 0 < a) (hτ : 0 < τ) :
  0 ≤ trapezoidal_error (fun x : ℝ ↦ Real.arctan (τ / x)) 1 a (a + 1) ∧
  trapezoidal_error (fun x : ℝ ↦ Real.arctan (τ / x)) 1 a (a + 1) ≤
   ((-τ / ((a + 1) ^ 2 + τ ^ 2)) - (-τ / (a ^ 2 + τ ^ 2))) / 8 := by
 apply vdD.vni
  (f' := fun x : ℝ ↦ -τ / (x ^ 2 + τ ^ 2))
  (f'' := fun x : ℝ ↦ 2 * τ * x / (x ^ 2 + τ ^ 2) ^ 2)
 ·intro x hx
  exact vbq (ha.trans_le hx.1)
 ·intro x hx
  exact vdY (ha.trans_le hx.1)
 ·apply Continuous.intervalIntegrable
  apply Continuous.div (f := fun x : ℝ ↦ 2 * τ * x) (g := fun x : ℝ ↦ (x ^ 2 + τ ^ 2) ^ 2)
   (by fun_prop) (by fun_prop)
  intro x
  positivity
 ·intro x hx
  have hx0 : 0 < x := ha.trans_le hx.1
  positivity
noncomputable def vbf (τ : ℝ) (N : ℕ) : ℝ :=
 ∑ k ∈ Finset.range N, trapezoidal_error (fun x : ℝ ↦ Real.arctan (τ / x)) 1
  (1 / 4 + (k : ℝ)) (1 / 4 + (k : ℝ) + 1)
lemma veJ {τ : ℝ} (hτ : 0 < τ) (N : ℕ) :
  0 ≤ vbf τ N ∧
   vbf τ N ≤
    ((-τ / ((1 / 4 + (N : ℝ)) ^ 2 + τ ^ 2)) -
     (-τ / ((1 / 4 : ℝ) ^ 2 + τ ^ 2))) / 8 := by
 induction N with
 | zero => simp [-Complex.ofReal_arctan, vbf]
 | succ N ih =>
  have hu := vgV (a := 1 / 4 + (N : ℝ)) (by positivity) hτ
  have he : vbf τ (N + 1) = vbf τ N +
    trapezoidal_error (fun x : ℝ ↦ Real.arctan (τ / x)) 1
     (1 / 4 + (N : ℝ)) (1 / 4 + (N : ℝ) + 1) := by
   simp [-Complex.ofReal_arctan, vbf, Finset.sum_range_succ]
  rw [he]
  push_cast
  constructor
  ·linarith [ih.1, hu.1]
  ·have hp : 1 / 4 + ((N : ℝ) + 1) = 1 / 4 + (N : ℝ) + 1 := by ring
   rw [hp]
   linarith [ih.2, hu.2]
lemma vli {τ : ℝ} (hτ : 0 < τ) (N : ℕ) :
  vbf τ N ≤ 1 / (8 * τ) := by
 have hu := (veJ hτ N).2
 have hn : -τ / ((1 / 4 + (N : ℝ)) ^ 2 + τ ^ 2) ≤ 0 := by
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
 have he : τ / ((1 / 4 : ℝ) ^ 2 + τ ^ 2) ≤ 1 / τ := by
  rw [div_le_div_iff₀ (by positivity) hτ]
  nlinarith
 have he' : 1 / (8 * τ) = (1 / τ) / 8 := by ring
 rw [he']
 simp only [neg_div] at hu hn
 linarith
lemma vkW (τ : ℝ) (N : ℕ) :
  vbf τ N =
   (∑ k ∈ Finset.range N, Real.arctan (τ / (1 / 4 + (k : ℝ)))) +
    (Real.arctan (τ / (1 / 4 + (N : ℝ))) - Real.arctan (τ / (1 / 4))) / 2 -
    (vaq τ (1 / 4 + (N : ℝ)) - vaq τ (1 / 4)) := by
 unfold vbf
 rw [vdD.vmU N]
 ·rw [vhn (by norm_num : (0 : ℝ) < 1 / 4)]
 ·intro k _
  apply ContinuousOn.intervalIntegrable
  intro x hx
  rw [Set.uIcc_of_le (by linarith : 1 / 4 + (k : ℝ) ≤ 1 / 4 + (k : ℝ) + 1)] at hx
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx.1
  exact (vbq (τ := τ) hx0).continuousAt.continuousWithinAt
lemma vio {τ : ℝ} (hτ : 0 < τ) :
  Tendsto (vbf τ) atTop
   (𝓝 (vaq τ (1 / 4) - Real.arctan (τ / (1 / 4)) / 2 - τ -
    vba (1 / 4) τ)) := by
 have hG := vga hτ.le
 have hP := vet (by norm_num : (0 : ℝ) < 1 / 4) hτ
 have hq : Tendsto (fun N : ℕ ↦ τ / (1 / 4 + (N : ℝ))) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop
   (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
 have hA : Tendsto (fun N : ℕ ↦ Real.arctan (τ / (1 / 4 + (N : ℝ)))) atTop (𝓝 0) := by
  simpa [-Complex.ofReal_arctan, Function.comp_def] using (Real.continuous_arctan.tendsto 0).comp hq
 have hC : Tendsto (fun _ : ℕ ↦ vaq τ (1 / 4) - Real.arctan (τ / (1 / 4)) / 2)
   atTop (𝓝 (vaq τ (1 / 4) - Real.arctan (τ / (1 / 4)) / 2)) :=
  tendsto_const_nhds
 convert ((hC.sub hG).sub hP).add (hA.div_const 2) using 1
 ·funext N
  rw [vkW]
  ring
 ·ring
lemma vhD {τ : ℝ} (hτ : 0 < τ) :
  |vba (1 / 4) τ - τ * Real.log τ + τ + Real.pi / 8| ≤ 1 / (8 * τ) := by
 have hlim := vio hτ
 have hE0 : 0 ≤ vaq τ (1 / 4) - Real.arctan (τ / (1 / 4)) / 2 - τ -
   vba (1 / 4) τ := by
  apply ge_of_tendsto hlim
  exact Filter.Eventually.of_forall (fun N ↦ (veJ hτ N).1)
 have hE1 : vaq τ (1 / 4) - Real.arctan (τ / (1 / 4)) / 2 - τ -
   vba (1 / 4) τ ≤ 1 / (8 * τ) :=
  le_of_tendsto' hlim (vli hτ)
 have hC := vhC hτ
 have hu : 3 / (32 * τ) ≤ 1 / (8 * τ) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith
 rw [abs_le]
 constructor <;> linarith [hC.1, hC.2]
lemma vfD {T : ℝ} (hT : 0 < T) :
  |vbp T - T / 2 * Real.log (T / 2) + T / 2 + Real.pi / 8| ≤
   1 / (4 * T) := by
 have hh := vhD (τ := T / 2) (by positivity)
 have he : vba (1 / 4) (T / 2) = vbp T := by
  simp [-Complex.ofReal_arctan, vba, vbp]
 rw [he] at hh
 convert hh using 1 <;> (try ring)
 all_goals try rfl
end vaa.vab.vam
end
section
open Complex MeasureTheory Real
open scoped Interval
namespace vaa.vab.vae
lemma vht {T R : ℝ} {B : ℂ → ℝ}
  (hT : 1 ≤ T) (hgood : vah T)
  (hR : 3 / 4 < R) (hRT : R < T)
  (hB : CircleIntegrable B (5 / 4 : ℂ) R)
  (hB0 : ∀ z ∈ Metric.sphere (5 / 4 : ℂ) R, 0 ≤ B z)
  (hfb : ∀ z ∈ Metric.sphere (5 / 4 : ℂ) R,
   ‖riemannZeta (z + T * I)‖ ≤ Real.exp (B z))
  (hgb : ∀ z ∈ Metric.sphere (5 / 4 : ℂ) R,
   ‖riemannZeta (z - T * I)‖ ≤ Real.exp (B z)) :
  |(N T : ℝ) - vcG T| ≤
   (circleAverage B (5 / 4 : ℂ) R + Real.log (3.426 : ℝ)) /
    (2 * Real.log (R / (3 / 4))) + 1 / 2 +
    2 / (Real.pi * T) + 1 / (4 * Real.pi * T) := by
 have hT0 : 0 < T := by linarith
 have hp : 0 < Real.pi := Real.pi_pos
 have hq : 0 < Real.log (R / (3 / 4)) :=
  Real.log_pos ((one_lt_div (by norm_num)).mpr hR)
 have hhor := vgs.vgA hT hgood hR hRT hB hB0 hfb hgb
 have hcenter : -Real.log (3.426 : ℝ) ≤
   Real.log ‖riemannZeta ((5 / 4 : ℂ) + T * I)‖ := by
  have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 3.426)
   (vdJ T)
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat] at hh
  simpa only [Real.log_div one_ne_zero (by norm_num : (3.426 : ℝ) ≠ 0),
   Real.log_one, zero_sub] using hh
 have hhor' :
   |∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ),
    (logDeriv riemannZeta ((σ : ℂ) + T * I)).im| / Real.pi ≤
   (circleAverage B (5 / 4 : ℂ) R + Real.log (3.426 : ℝ)) /
    (2 * Real.log (R / (3 / 4))) + 2 / (Real.pi * T) := by
  apply hhor.trans
  gcongr
  linarith
 have hv := viC.vhx T
 have ha : |vbV T| / Real.pi ≤
   1 / 2 +
   (circleAverage B (5 / 4 : ℂ) R + Real.log (3.426 : ℝ)) /
    (2 * Real.log (R / (3 / 4))) + 2 / (Real.pi * T) := by
  unfold vbV vcx
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
  have hh := abs_sub_le
   (∫ t in (0 : ℝ)..T, (logDeriv riemannZeta ((5 / 4 : ℂ) + t * I)).re)
   (0 : ℝ)
   (∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ),
    (logDeriv riemannZeta ((σ : ℂ) + T * I)).im)
  simp only [sub_zero, zero_sub, abs_neg] at hh
  have hd := div_le_div_of_nonneg_right hh hp.le
  have hv' := div_le_div_of_nonneg_right hv hp.le
  have he : (Real.pi / 2) / Real.pi = (1 / 2 : ℝ) := by field_simp
  rw [he] at hv'
  rw [add_div] at hd
  linarith
 have hg := div_le_div_of_nonneg_right
  (vam.vfD hT0) hp.le
 change |vaY T| / Real.pi ≤ (1 / (4 * T)) / Real.pi at hg
 rw [vhA hT0 hgood]
 have hh := abs_add_le (vbV T / Real.pi) (vaY T / Real.pi)
 rw [abs_div, abs_div, abs_of_pos hp] at hh
 have he : (1 / (4 * T)) / Real.pi = 1 / (4 * Real.pi * T) := by ring
 rw [he] at hg
 have he' : vcG T + vbV T / Real.pi + vaY T / Real.pi -
   vcG T = vbV T / Real.pi + vaY T / Real.pi := by ring
 rw [he']
 linarith
end vaa.vab.vae
end
section
open Set MeasureTheory
open scoped BigOperators
namespace vaa.vab
noncomputable def vnN (t : ℝ) : ℝ :=
 t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8
noncomputable def vme (C t : ℝ) : ℝ :=
 0.137 * Real.log t + 0.443 * Real.log (Real.log t) + C
lemma vkc {t : ℝ} (ht : 0 < t) :
  HasDerivAt vnN (Real.log (t / (2 * Real.pi)) / (2 * Real.pi)) t := by
 have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
 have hq : t / (2 * Real.pi) ≠ 0 := div_ne_zero ht.ne' hp
 have hdiv := (hasDerivAt_id t).div_const (2 * Real.pi)
 have hh := ((hdiv.mul (hdiv.log hq)).sub hdiv).add_const (7 / 8 : ℝ)
 refine (hh).congr_deriv ?_
 symm
 try dsimp only [id_eq]
 field_simp [hp, ht.ne']
 <;> ring
end vaa.vab
end
section
open Real
namespace vaa.vab.vgt
open vcT
structure vaS where
 k : ℕ
 a : ℕ
 b : ℕ
 deriving DecidableEq
def vaS.Valid (c : vaS) : Prop := 0 < c.a ∧ 0 < c.b ∧ c.b ≤ c.a
instance (c : vaS) : Decidable c.Valid := by unfold vaS.Valid; infer_instance
def vaS.ratio (c : vaS) : ℚ := (2 : ℚ) ^ c.k * (1 + (c.b : ℚ) / c.a)
def vaS.lower (c : vaS) : ℚ :=
 ((c.k : ℚ) * qLo 1 1 + qLo c.a c.b) / (10 ^ 30 : ℚ)
def vaS.upper (c : vaS) : ℚ :=
 ((c.k : ℚ) * qHi 1 1 + qHi c.a c.b) / (10 ^ 30 : ℚ)
lemma vaS.viZ {c : vaS} (hc : c.Valid) :
  (c.lower : ℝ) ≤ Real.log (c.ratio : ℝ) ∧
   Real.log (c.ratio : ℝ) ≤ (c.upper : ℝ) := by
 have ha : (0 : ℝ) < c.a := by exact_mod_cast hc.1
 have hb : (0 : ℝ) < c.b := by exact_mod_cast hc.2.1
 have h1 := vcI hc.1 hc.2.1 hc.2.2
 have h2 := vcI (a := 1) (b := 1) (by decide) (by decide) (by decide)
 norm_num only [Nat.cast_one, div_one] at h2
 have hk : (0 : ℝ) ≤ c.k := Nat.cast_nonneg _
 have hl := mul_le_mul_of_nonneg_left h2.1 hk
 have hu := mul_le_mul_of_nonneg_left h2.2 hk
 have he : Real.log (c.ratio : ℝ) =
   (c.k : ℝ) * Real.log 2 + Real.log (1 + (c.b : ℝ) / c.a) := by
  unfold vaS.ratio
  push_cast
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
 rw [he]
 unfold vaS.lower vaS.upper
 push_cast
 constructor
 ·rw [div_le_iff₀ (by positivity : (0 : ℝ) < 10 ^ 30)]
  nlinarith
 ·rw [le_div_iff₀ (by positivity : (0 : ℝ) < 10 ^ 30)]
  nlinarith
lemma vaS.vom {c : vaS} (hc : c.Valid) {l : ℚ} (hl : l < c.lower) :
  (l : ℝ) < Real.log (c.ratio : ℝ) :=
 (show (l : ℝ) < (c.lower : ℝ) by exact_mod_cast hl).trans_le (vaS.viZ hc).1
end vaa.vab.vgt
end
section
open Real
namespace vaa.vab.vbl
open vgt
lemma vms : (4.6 : ℝ) < Real.log 100 := by
 have h := vaS.vom (c := ⟨6, 16, 9⟩) (by decide)
  (l := (23 / 5 : ℚ)) (by decide +kernel)
 norm_num [vaS.ratio] at h ⊢
 exact h
lemma viE : (1.5 : ℝ) < Real.log (4.6 : ℝ) := by
 have h := vaS.vom (c := ⟨2, 20, 3⟩) (by decide)
  (l := (3 / 2 : ℚ)) (by decide +kernel)
 norm_num [vaS.ratio] at h ⊢
 exact h
noncomputable def vbO (T : ℝ) : ℝ :=
 0.1361 * Real.log (T + 33 / 25) +
 0.4423 * Real.log (Real.log (T + 33 / 25)) + 1.5803 +
 Real.log ((T - 33 / 25) ^ 2 / ((T - 33 / 25) ^ 2 - 4)) +
 2 / (Real.pi * T) + 1 / (4 * Real.pi * T)
lemma vgJ {T : ℝ} (hT : 100 ≤ T) :
  vbO T < vme 1.588 T := by
 have hT0 : 0 < T := by linarith
 have hp : 0 < Real.pi := Real.pi_pos
 have hl : (4.6 : ℝ) < Real.log T :=
  vms.trans_le (Real.log_le_log (by norm_num) hT)
 have hl0 : 0 < Real.log T := by linarith
 have hll : (1.5 : ℝ) < Real.log (Real.log T) :=
  viE.trans_le (Real.log_le_log (by norm_num) hl.le)
 have hs : Real.log (T + 33 / 25) ≤ Real.log T + (33 / 25) / T := by
  have hf : T + 33 / 25 = T * (1 + (33 / 25) / T) := by field_simp
  rw [hf, Real.log_mul hT0.ne' (by positivity)]
  have hh := Real.log_le_sub_one_of_pos
   (by positivity : (0 : ℝ) < 1 + (33 / 25) / T)
  linarith
 have hsp : 0 < Real.log (T + 33 / 25) := Real.log_pos (by linarith)
 have hss : Real.log (Real.log (T + 33 / 25)) ≤
   Real.log (Real.log T) + (33 / 25) / (T * Real.log T) := by
  apply (Real.log_le_log hsp hs).trans
  have hf : Real.log T + (33 / 25) / T =
    Real.log T * (1 + (33 / 25) / (T * Real.log T)) := by
   field_simp
  rw [hf, Real.log_mul hl0.ne' (by positivity)]
  have hh := Real.log_le_sub_one_of_pos
   (by positivity : (0 : ℝ) < 1 + (33 / 25) / (T * Real.log T))
  linarith
 have hA : 0.1361 * Real.log (T + 33 / 25) ≤
   0.1361 * Real.log T + 0.18 / T := by
  calc
   _ ≤ 0.1361 * (Real.log T + (33 / 25) / T) :=
    mul_le_mul_of_nonneg_left hs (by norm_num)
   _ = 0.1361 * Real.log T + (0.1361 * (33 / 25)) / T := by ring
   _ ≤ _ := by gcongr; norm_num
 have hBc : (0.4423 * (33 / 25)) / (T * Real.log T) ≤ 0.13 / T := by
  rw [div_le_div_iff₀ (mul_pos hT0 hl0) hT0]
  nlinarith [mul_nonneg hT0.le (sub_nonneg.mpr hl.le)]
 have hB : 0.4423 * Real.log (Real.log (T + 33 / 25)) ≤
   0.4423 * Real.log (Real.log T) + 0.13 / T := by
  calc
   _ ≤ 0.4423 * (Real.log (Real.log T) + (33 / 25) / (T * Real.log T)) :=
    mul_le_mul_of_nonneg_left hss (by norm_num)
   _ = 0.4423 * Real.log (Real.log T) +
     (0.4423 * (33 / 25)) / (T * Real.log T) := by ring
   _ ≤ _ := add_le_add le_rfl hBc
 let D : ℝ := (T - 33 / 25) ^ 2 - 4
 have hD : 80 * T ≤ D := by
  dsimp [D]
  nlinarith [mul_nonneg (sub_nonneg.mpr hT) hT0.le]
 have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hD
 have hV : Real.log ((T - 33 / 25) ^ 2 / D) ≤ 0.05 / T := by
  have hf : (T - 33 / 25) ^ 2 / D = 1 + 4 / D := by
   calc
    _ = (D + 4) / D := by congr 1; dsimp [D]; ring
    _ = _ := by rw [add_div, div_self hD0.ne']
  rw [hf]
  have hh := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 4 / D)
  have hdiv : 4 / D ≤ 0.05 / T := by
   rw [div_le_div_iff₀ hD0 hT0]
   linarith
  linarith
 have hpi2 : (2 : ℝ) / Real.pi ≤ 0.637 := by
  rw [div_le_iff₀ hp]
  linarith [Real.pi_gt_d2]
 have hG0 : (1 : ℝ) / (4 * Real.pi) ≤ 0.08 := by
  rw [div_le_iff₀ (by positivity)]
  linarith [Real.pi_gt_d2]
 have hP : 2 / (Real.pi * T) ≤ 0.637 / T := by
  convert div_le_div_of_nonneg_right hpi2 hT0.le using 1 <;> (try ring)
  all_goals try rfl
 have hG : 1 / (4 * Real.pi * T) ≤ 0.08 / T := by
  convert div_le_div_of_nonneg_right hG0 hT0.le using 1 <;> (try ring)
  all_goals try rfl
 have hsmall : (1.1 : ℝ) / T ≤ 0.011 := by
  rw [div_le_iff₀ hT0]
  linarith
 have hrec : 0 < 1 / T := by positivity
 change Real.log ((T - 33 / 25) ^ 2 / ((T - 33 / 25) ^ 2 - 4)) ≤ 0.05 / T at hV
 unfold vbO vme
 simp only [div_eq_mul_inv] at hA hB hV hP hG hsmall hrec ⊢
 linarith only [hA, hB, hV, hP, hG, hsmall, hrec, hl, hll]
end vaa.vab.vbl
end
section
open Complex Real MeasureTheory
namespace vaa.vab.vao
lemma vgP (T : ℝ) :
  CircleIntegrable (vcH T) (5 / 4 : ℂ) radius := by
 have hi : IntervalIntegrable
   (fun θ => scalar (vbk T) (vbC T) (vbt T)
    ((5 / 4 : ℝ) + radius * Real.cos θ)) volume 0 Real.pi := by
  have hi' := vas.vco
   (vbk T) (vbC T) (vbt T)
  unfold vas.arc vas.sigma
   vad.radius at hi'
  simpa only [radius] using hi'
 unfold vcH
 simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using vfb hi
lemma vjB (T : ℝ) :
  circleAverage (vcH T) (5 / 4 : ℂ) radius /
    (2 * vad.q) ≤
   0.1361 / vad.q +
    vad.vcQ * vbC T +
    vad.vfy * vbk T +
    (vad.beta - vad.alpha) * vbt T /
     (2 * Real.pi * vad.q) := by
 have hi := vas.vco
  (vbk T) (vbC T) (vbt T)
 unfold vas.arc vas.sigma
  vad.radius at hi
 have he := vgI (c := 5 / 4) (r := radius)
  (f := scalar (vbk T) (vbC T) (vbt T)) (by
   simpa only [radius] using hi)
 norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at he
 change circleAverage (vcH T) (5 / 4 : ℂ) radius = _ at he
 rw [he]
 have hb := vas.vii
  (vbk T) (vbC T) (vbt T)
 unfold vas.arc vas.sigma
  vad.radius at hb
 convert hb using 1
 dsimp [radius]
 field_simp [vad.q_pos.ne', Real.pi_ne_zero]
lemma veL :
  (vad.beta - vad.alpha) /
   (2 * Real.pi * vad.q) ≤ 1 := by
 have hq := vad.vcI.1
 have hα : 0 ≤ vad.alpha := Real.arccos_nonneg _
 have hβ : vad.beta ≤ Real.pi := Real.arccos_le_pi _
 have hm := mul_nonneg Real.pi_pos.le
  (show 0 ≤ 2 * vad.q - 1 by linarith)
 rw [div_le_one (by positivity [vad.q_pos])]
 nlinarith [Real.pi_pos]
lemma vgT {T : ℝ} (hT : 100 ≤ T)
  (hgood : vae.vah T) :
  |(vae.N T : ℝ) - vae.vcG T| ≤
   vbl.vbO T := by
 have hh := vae.vht
  (T := T) (R := radius) (B := vcH T) (by linarith) hgood
  (by norm_num [radius]) (by dsimp [radius]; linarith)
  (vgP T) (fun z _ => vlJ hT z)
  (fun _ hz => vgR hT hz)
  (fun _ hz => vfN hT hz)
 have hq : Real.log (radius / (3 / 4)) = vad.q := by
  unfold radius vad.q
  norm_num
 rw [hq, add_div] at hh
 have hmean := vjB T
 have hp : vbC T = Real.log (T + radius) - Real.log (2 * Real.pi) := by
  unfold vbC
  rw [Real.log_div (by dsimp [radius]; linarith) (by positivity)]
 have hraw : |(vae.N T : ℝ) - vae.vcG T| ≤
   vad.vcQ * Real.log (T + radius) +
   vad.vfy * vbk T +
   vad.vhT 0.1361 +
   (vad.beta - vad.alpha) * vbt T /
    (2 * Real.pi * vad.q) +
   2 / (Real.pi * T) + 1 / (4 * Real.pi * T) := by
  rw [hp] at hmean
  unfold vad.vhT
  linarith
 have hA := mul_le_mul_of_nonneg_right vad.vfJ.2
  (viD hT).le
 have hB := mul_le_mul_of_nonneg_right vad.vol
  (vhk hT)
 have hK := vad.vju
 have hV := mul_le_mul_of_nonneg_right veL (vhR hT)
 have hVe : ((vad.beta - vad.alpha) /
   (2 * Real.pi * vad.q)) * vbt T =
   (vad.beta - vad.alpha) * vbt T /
    (2 * Real.pi * vad.q) := by ring
 rw [hVe, one_mul] at hV
 change _ ≤ 0.1361 * Real.log (T + radius) + 0.4423 * vbk T + 1.5803 +
  vbt T + 2 / (Real.pi * T) + 1 / (4 * Real.pi * T)
 linarith
end vaa.vab.vao
end
section
open Complex MeasureTheory Set Filter
open scoped Real Topology Interval
namespace vaa.vab.vae
noncomputable def vbF (T : ℝ) : Finset ℂ :=
 (vaH (T + 1)).filter (fun ρ => ρ.im ≤ T)
noncomputable def N_le (T : ℝ) : ℕ :=
 ∑ ρ ∈ vbF T, (analyticOrderAt riemannZeta ρ).toNat
lemma vbL {T : ℝ} (hT : 0 < T) {ρ : ℂ} :
  ρ ∈ vbF T ↔ riemannZeta ρ = 0 ∧ 0 < ρ.im ∧ ρ.im ≤ T := by
 rw [vbF, Finset.mem_filter, vbo (by linarith)]
 constructor
 ·rintro ⟨⟨hz, h0, _⟩, hT⟩
  exact ⟨hz, h0, hT⟩
 ·rintro ⟨hz, h0, hT⟩
  exact ⟨⟨hz, h0, by linarith⟩, hT⟩
private lemma vkY (S : Finset ℂ) (T : ℝ) :
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ ρ ∈ S, T < ρ.im → T + δ ≤ ρ.im := by
 classical
 induction S using Finset.induction_on with
 | empty => exact ⟨1, by norm_num, le_rfl, by simp⟩
 | @insert a S ha ih =>
  obtain ⟨δ, hδ0, hδ1, hgap⟩ := ih
  by_cases haT : T < a.im
  ·refine ⟨min δ ((a.im - T) / 2), lt_min hδ0 (by linarith),
    (min_le_left _ _).trans hδ1, ?_⟩
   intro ρ hρ hρT
   rcases Finset.mem_insert.mp hρ with rfl | hρ
   ·linarith [min_le_right δ ((ρ.im - T) / 2)]
   ·exact (add_le_add le_rfl (min_le_left _ _)).trans (hgap ρ hρ hρT)
  ·refine ⟨δ, hδ0, hδ1, ?_⟩
   intro ρ hρ hρT
   rcases Finset.mem_insert.mp hρ with rfl | hρ
   ·exact (haT hρT).elim
   ·exact hgap ρ hρ hρT
lemma vef {T : ℝ} (hT : 0 < T) :
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ S ∈ Ioo T (T + δ),
   vah S ∧ N S = N_le T := by
 obtain ⟨δ, hδ0, hδ1, hgap⟩ := vkY (vaH (T + 1)) T
 refine ⟨δ, hδ0, hδ1, ?_⟩
 intro S hS
 have hS0 : 0 < S := hT.trans hS.1
 have hS1 : S < T + 1 := lt_of_lt_of_le hS.2 (by linarith)
 have hg : vah S := by
  intro ρ hz he
  have hρ : ρ ∈ vaH (T + 1) :=
   (vbo (by linarith)).mpr ⟨hz, by simpa [he] using hS0,
    by simpa [he] using hS1⟩
  have hh := hgap ρ hρ (by simpa [he] using hS.1)
  rw [he] at hh
  linarith [hS.2]
 refine ⟨hg, ?_⟩
 have hsets : vaH S = vbF T := by
  apply Finset.ext
  intro ρ
  rw [vbo hS0, vbL hT]
  constructor
  ·rintro ⟨hz, h0, hρS⟩
   refine ⟨hz, h0, ?_⟩
   by_contra h
   have hTρ : T < ρ.im := lt_of_not_ge h
   have hρ : ρ ∈ vaH (T + 1) :=
    (vbo (by linarith)).mpr ⟨hz, h0, hρS.trans hS1⟩
   linarith [hgap ρ hρ hTρ, hS.2]
  ·rintro ⟨hz, h0, hρT⟩
   exact ⟨hz, h0, hρT.trans_lt hS.1⟩
 rw [vgM hS0, hsets]
 rfl
lemma vcF {T : ℝ} (hT : 0 < T)
  {M B : ℝ → ℝ} (hM : ContinuousAt M T) (hB : ContinuousAt B T)
  (hbound : ∀ S : ℝ, T < S → vah S → |(N S : ℝ) - M S| ≤ B S) :
  |(N_le T : ℝ) - M T| ≤ B T := by
 obtain ⟨δ, hδ0, hδ1, hloc⟩ := vef hT
 let S : ℕ → ℝ := fun n => T + (δ / 2) * (1 / ((n : ℝ) + 1))
 have hSmem (n : ℕ) : S n ∈ Ioo T (T + δ) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hrec : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one hn).mpr hn1
  have hp : 0 < (δ / 2) * (1 / ((n : ℝ) + 1)) := by positivity
  have hq := mul_le_mul_of_nonneg_left hrec (show 0 ≤ δ / 2 by positivity)
  dsimp [S]
  constructor <;> nlinarith
 have hlim : Tendsto S atTop (𝓝 T) := by
  have hh : Tendsto (fun n : ℕ => T + (δ / 2) * (1 / ((n : ℝ) + 1))) atTop
    (𝓝 (T + (δ / 2) * 0)) := tendsto_const_nhds.add
   (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (δ / 2))
  simpa [S] using hh
 have hb : ∀ n : ℕ, |(N_le T : ℝ) - M (S n)| ≤ B (S n) := by
  intro n
  have hl := hloc (S n) (hSmem n)
  rw [← hl.2]
  exact hbound (S n) (hSmem n).1 hl.1
 exact le_of_tendsto_of_tendsto
  ((tendsto_const_nhds.sub (hM.tendsto.comp hlim)).abs)
  (hB.tendsto.comp hlim) (Eventually.of_forall hb)
lemma vcE {T : ℝ} (hT : 0 < T)
  {M B : ℝ → ℝ} {C : ℝ} (hM : ContinuousAt M T) (hB : ContinuousAt B T)
  (hbound : ∀ S : ℝ, T < S → vah S → |(N S : ℝ) - M S| ≤ B S)
  (hgap : B T < C) : |(N_le T : ℝ) - M T| < C :=
 (vcF hT hM hB hbound).trans_lt hgap
end vaa.vab.vae
end
section
open Complex Real MeasureTheory
namespace vaa.vab.veG
open vae
noncomputable def vcp (T : ℝ) : ℝ := by
 classical
 exact ∑' ρ : ℂ, if 0 < ρ.im ∧ ρ.im ≤ T then
  ((analyticOrderAt riemannZeta ρ).toNat : ℝ) else 0
lemma viH {T : ℝ} (hT : 0 < T) :
  vcp T = (N_le T : ℝ) := by
 classical
 have hs : ∀ ρ ∉ vbF T,
   (if 0 < ρ.im ∧ ρ.im ≤ T then
    ((analyticOrderAt riemannZeta ρ).toNat : ℝ) else 0) = 0 := by
  intro ρ hρ
  by_cases hi : 0 < ρ.im ∧ ρ.im ≤ T
  ·have hz : riemannZeta ρ ≠ 0 := by
    intro hz
    exact hρ ((vbL hT).mpr ⟨hz, hi.1, hi.2⟩)
   rw [if_pos hi, analyticOrderAt_eq_zero.mpr (Or.inr hz)]
   simp
  ·simp [hi]
 unfold vcp
 rw [tsum_eq_sum hs]
 unfold N_le
 push_cast
 apply Finset.sum_congr rfl
 intro ρ hρ
 have hi := (vbL hT).mp hρ
 simp only [if_pos (show 0 < ρ.im ∧ ρ.im ≤ T from ⟨hi.2.1, hi.2.2⟩)]
end vaa.vab.veG
end
section
open Complex Real MeasureTheory
namespace vaa.vab.vae
lemma vfX {T : ℝ} (hT : 100 ≤ T) :
  ContinuousAt vbl.vbO T := by
 have hT0 : 0 < T := by linarith
 have hTr : 0 < T - 33 / 25 := by linarith
 have hD : 0 < (T - 33 / 25) ^ 2 - 4 := by nlinarith
 have hL : 0 < Real.log (T + 33 / 25) := Real.log_pos (by linarith)
 unfold vbl.vbO
 fun_prop (disch := positivity)
lemma vkz {T : ℝ} (hT : 100 ≤ T) :
  |(N_le T : ℝ) - vcG T| < vme 1.588 T := by
 have hT0 : 0 < T := by linarith
 apply vcE hT0
  (M := vcG) (B := vbl.vbO)
 ·change ContinuousAt vnN T
  exact (vkc hT0).continuousAt
 ·exact vfX hT
 ·intro S hTS hg
  exact vao.vgT (hT.trans hTS.le) hg
 ·exact vbl.vgJ hT
end vaa.vab.vae
namespace vaa.vab.veG
lemma vhZ (T : ℝ) (hT : 100 ≤ T) :
  |vcp T -
   (T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8)| <
   0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588 := by
 rw [viH (by linarith)]
 exact vae.vkz hT
end vaa.vab.veG
end
theorem OMA.solution : OMA.R_OeisA38098_conjecture1_R1_H2_R1.H1 := by
 intro T hT
 have h := vaa.vab.veG.vhZ T hT
 unfold vaa.vab.veG.vcp at h
 convert h using 5

