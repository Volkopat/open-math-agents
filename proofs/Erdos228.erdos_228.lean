import FormalConjectures.ErdosProblems.«228»
import Mathlib

/-! Flat Littlewood polynomials exist, by Balister, Bollobás, Morris, Sahasrabudhe and Tiba.
Formalization by Boris Alexeev and OpenAI Codex in https://github.com/plby/lean-proofs.
Copyright (c) 2026 Boris Alexeev. All rights reserved. Released under the Apache 2.0 license.

The Rudin–Shapiro cosine block supplies the lower bound outside a family of exceptional
intervals. A discrepancy argument chooses signs for the odd sine terms so they supply the
lower bound on those intervals. The centered polynomial combines both estimates and
preserves the signs of all coefficients.

Ported from the single-file assembly at
https://github.com/Jayyhk/erdos-lean/blob/aaf98282ccdf700e0422c2ccbc0a131ec6180732/problems/228/Erdos228.lean
-/

namespace Erdos228

open Real (abs_cos_le_one abs_sin_le_one analyticAt_sin continuous_cos continuous_sin
  continuous_sinc cos cos_add_int_mul_two_pi cos_int_mul_two_pi_sub cos_neg
  cos_nonneg_of_mem_Icc exp_log hasDerivAt_sin log log_nonneg log_two_lt_d9 norm_eq_abs
  one_le_sqrt pi_gt_d2 pi_lt_d2 pi_lt_four pi_ne_zero pi_pos sin sin_add_pi
  sin_eq_zero_iff_of_lt_of_lt sin_ge_sub_cube sin_le sin_le_sin_of_le_of_le_pi_div_two
  sin_neg sin_nonneg_of_nonneg_of_le_pi sin_pi_div_two sin_pi_sub
  sin_pos_of_pos_of_lt_pi sin_zero sinc sinc_eq_dslope sinc_neg sinc_of_ne_zero sq_sqrt
  sqrt sqrt_le_iff sqrt_le_sqrt sqrt_mul sqrt_nonneg sqrt_pos sqrt_sq sqrt_sq_eq_abs
  tendsto_sqrt_atTop)
open Finset (abs_sum_le_sum_abs card_le_one card_union_le mem_filter orderIsoOfFin sum_add_distrib
  sum_attach sum_bij sum_congr sum_div sum_eq_single sum_eq_zero sum_image sum_le_sum
  sum_neg_distrib sum_range_add sum_range_sub sum_range_succ sum_sub_distrib sum_subtype
  sum_union)
open Polynomial (card_roots' coeff_C_mul coeff_X_pow_mul' coeff_add coeff_eq_zero_of_degree_lt
  coeff_monomial coeff_one coeff_sub degree_eq_of_le_of_coeff_ne_zero
  degree_le_iff_coeff_zero derivative eval_X eval_add eval_eq_sum eval_finsetSum
  eval_monomial eval_mul eval_pow eval_sub lcoeff lcoeff_apply mem_rootSet mem_roots
  mem_support_iff monomial natDegree_eq_of_le_of_coeff_ne_zero
  natDegree_le_iff_coeff_eq_zero natDegree_mul_le natDegree_sub_le sum_def)
open Complex (abs_im_le_norm abs_re_le_norm add_re exp_nat_mul imLm mul_im mul_re normSq
  normSq_apply normSq_eq_norm_sq norm_I norm_exp_ofReal_mul_I norm_natCast ofRealCLM
  ofReal_im ofReal_re re reCLM reLm sq_norm)
open Fintype (card_coe card_fin card_sum)
open intervalIntegral (integral_add_adjacent_intervals integral_comp_add_right integral_comp_sub_right
  integral_eq_sub_of_hasDerivAt integral_mono_on norm_integral_le_of_norm_le_const)
open Filter (atTop eventually_ge_atTop)
open scoped Real

section

namespace Bern

open scoped BigOperators

def freq (k : ℕ) : ℂ := (k : ℂ) * Complex.I

noncomputable def fourierDeriv (r : ℕ) (s : Finset ℕ) (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ s, a k * freq k ^ r *
    Complex.exp (((k : ℂ) * (x : ℂ)) * Complex.I)

@[simp]
theorem fourierDeriv_zero (s : Finset ℕ) (a : ℕ → ℂ) (x : ℝ) :
    fourierDeriv 0 s a x =
      ∑ k ∈ s, a k * Complex.exp (((k : ℂ) * (x : ℂ)) * Complex.I) := by
  simp [fourierDeriv]

theorem eval_reflect_mul_pow {p : Polynomial ℂ} {n : ℕ} (hdeg : p.natDegree ≤ n)
    {w : ℂ} (hw : w ≠ 0) :
    (p.reflect n).eval w⁻¹ * w ^ n = p.eval w := by
  let iw : Invertible w := invertibleOfNonzero hw
  simpa [invOf_eq_inv] using
    (@Polynomial.eval₂_reflect_mul_pow ℂ _ ℂ _ (RingHom.id ℂ) w iw n p hdeg)

theorem norm_reflect_eval_le_of_circ_bound {p : Polynomial ℂ} {n : ℕ}
    (hdeg : p.natDegree ≤ n) {M : ℝ}
    (hM : ∀ z : ℂ, ‖z‖ = 1 → ‖p.eval z‖ ≤ M)
    {u : ℂ} (hu : ‖u‖ ≤ 1) :
    ‖(p.reflect n).eval u‖ ≤ M := by
  let q := p.reflect n
  have hboundary : ∀ z : ℂ, ‖z‖ = 1 → ‖q.eval z‖ ≤ M := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro hzzero
      simp [hzzero] at hz
    have hzinv : ‖z⁻¹‖ = 1 := by simp [hz]
    have hrel := eval_reflect_mul_pow hdeg (w := z⁻¹) (inv_ne_zero hz0)
    have hnorm : ‖q.eval z‖ = ‖p.eval z⁻¹‖ := by
      have hpownorm : ‖(z⁻¹) ^ n‖ = 1 := by
        rw [norm_pow, hzinv, one_pow]
      calc
        ‖q.eval z‖ = ‖q.eval z‖ * 1 := by simp
        _ = ‖q.eval z‖ * ‖(z⁻¹) ^ n‖ := by rw [hpownorm]
        _ = ‖q.eval z * (z⁻¹) ^ n‖ := by rw [norm_mul]
        _ = ‖p.eval z⁻¹‖ := by
          rw [show q.eval z * (z⁻¹) ^ n = p.eval z⁻¹ by simpa [q] using hrel]
    rw [hnorm]
    exact hM z⁻¹ hzinv
  by_cases hueq : ‖u‖ = 1
  · exact hboundary u hueq
  have hult : ‖u‖ < 1 := lt_of_le_of_ne hu hueq
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
      Metric.isBounded_ball
      ((p.reflect n).differentiableOn.diffContOnCl_ball Set.Subset.rfl)
      (C := M)
  · intro z hz
    apply hboundary z
    have hzsphere : z ∈ Metric.sphere (0 : ℂ) 1 :=
      Metric.frontier_ball_subset_sphere hz
    simpa [Metric.mem_sphere, dist_zero_right] using hzsphere
  · exact subset_closure (by simpa [Metric.mem_ball, dist_zero_right] using hult)

theorem norm_eval_le_circ_bound_mul_pow {p : Polynomial ℂ} {n : ℕ}
    (hdeg : p.natDegree ≤ n) {M : ℝ}
    (hM : ∀ z : ℂ, ‖z‖ = 1 → ‖p.eval z‖ ≤ M)
    {w : ℂ} (hw : 1 ≤ ‖w‖) :
    ‖p.eval w‖ ≤ M * ‖w‖ ^ n := by
  have hw0 : w ≠ 0 := by
    apply norm_ne_zero_iff.mp
    linarith
  have hu : ‖w⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact (inv_le_one₀ (lt_of_lt_of_le zero_lt_one hw)).2 hw
  have hq := norm_reflect_eval_le_of_circ_bound hdeg hM hu
  have hrel := eval_reflect_mul_pow hdeg hw0
  calc
    ‖p.eval w‖ = ‖(p.reflect n).eval w⁻¹‖ * ‖w‖ ^ n := by
      rw [← hrel, norm_mul, norm_pow]
    _ ≤ M * ‖w‖ ^ n :=
      mul_le_mul_of_nonneg_right hq (by positivity)

theorem norm_coeff_le_of_circ_bound {p : Polynomial ℂ} {n : ℕ}
    (hdeg : p.natDegree ≤ n) {M : ℝ}
    (hM : ∀ z : ℂ, ‖z‖ = 1 → ‖p.eval z‖ ≤ M) :
    ‖p.coeff n‖ ≤ M := by
  have hq := norm_reflect_eval_le_of_circ_bound hdeg hM (u := (0 : ℂ)) (by norm_num)
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_reflect,
    Polynomial.revAt_zero] at hq
  exact hq

theorem norm_deriv_eval_le_degree_mul_circSup {p : Polynomial ℂ} {n : ℕ}
    (hdeg : p.natDegree ≤ n) {M : ℝ}
    (hM : ∀ w : ℂ, ‖w‖ = 1 → ‖p.eval w‖ ≤ M)
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖p.derivative.eval z‖ ≤ (n : ℝ) * M := by
  by_cases hn : n = 0
  · subst n
    have hpdeg : p.natDegree = 0 := Nat.eq_zero_of_le_zero hdeg
    rw [Polynomial.derivative_eq_zero.mpr hpdeg]
    simp
  have hnNat : 0 < n := Nat.pos_of_ne_zero hn
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hnNat
  by_contra hbound
  rw [not_le] at hbound
  have hz0 : z ≠ 0 := by
    intro hzero
    simp [hzero] at hz
  let β : ℂ := p.derivative.eval z / ((n : ℂ) * z ^ (n - 1))
  have hdenom : (n : ℂ) * z ^ (n - 1) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast hn) (pow_ne_zero _ hz0)
  have hβcancel : β * (n : ℂ) * z ^ (n - 1) = p.derivative.eval z := by
    dsimp [β]
    field_simp
  have hβnorm : ‖β‖ = ‖p.derivative.eval z‖ / (n : ℝ) := by
    dsimp [β]
    rw [norm_div, norm_mul, norm_pow, hz, one_pow, mul_one]
    simp
  have hβM : M < ‖β‖ := by
    rw [hβnorm, lt_div_iff₀ hnReal]
    simpa [mul_comm] using hbound
  let P : Polynomial ℂ := p - Polynomial.C β * Polynomial.X ^ n
  have hpcoeff : ‖p.coeff n‖ ≤ M := norm_coeff_le_of_circ_bound hdeg hM
  have hcoeffne : p.coeff n ≠ β := by
    intro heq
    rw [heq] at hpcoeff
    exact (not_le_of_gt hβM) hpcoeff
  have hPcoeff : P.coeff n ≠ 0 := by
    simpa [P, Polynomial.coeff_C_mul_X_pow] using sub_ne_zero.mpr hcoeffne
  have hPnatDegreePos : 0 < P.natDegree :=
    hnNat.trans_le (Polynomial.le_natDegree_of_ne_zero hPcoeff)
  have hPdegreePos : 0 < P.degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp hPnatDegreePos
  have hPderiv : P.derivative.eval z = 0 := by
    rw [show P.derivative.eval z = p.derivative.eval z -
        β * (n : ℂ) * z ^ (n - 1) by
      simp only [P, Polynomial.derivative_sub, Polynomial.derivative_C_mul_X_pow,
        eval_sub, Polynomial.eval_C_mul, Polynomial.eval_X_pow]]
    exact sub_eq_zero.mpr hβcancel.symm
  have hPderiv_ne : P.derivative ≠ 0 := by
    rw [Polynomial.derivative_ne_zero]
    exact hPnatDegreePos.ne'
  have hzDerivRoot : z ∈ P.derivative.rootSet ℂ := by
    rw [mem_rootSet]
    exact ⟨hPderiv_ne, hPderiv⟩
  have hroots : P.rootSet ℂ ⊆ Metric.ball 0 1 := by
    intro w hwroot
    rw [mem_rootSet] at hwroot
    have hPeval0 : P.eval w = 0 := by
      simpa [Polynomial.coe_aeval_eq_eval] using hwroot.2
    have hPeval : p.eval w = β * w ^ n := by
      apply sub_eq_zero.mp
      simpa [P] using hPeval0
    have hwlt : ‖w‖ < 1 := by
      by_contra hwlt
      have hwge : 1 ≤ ‖w‖ := le_of_not_gt hwlt
      have hout := norm_eval_le_circ_bound_mul_pow hdeg hM hwge
      have hmul : ‖β‖ * ‖w‖ ^ n ≤ M * ‖w‖ ^ n := by
        rw [hPeval, norm_mul, norm_pow] at hout
        exact hout
      have hpow : 0 < ‖w‖ ^ n := pow_pos (lt_of_lt_of_le zero_lt_one hwge) n
      have : ‖β‖ ≤ M := le_of_mul_le_mul_right hmul hpow
      exact (not_le_of_gt hβM) this
    simpa [Metric.mem_ball, dist_zero_right] using hwlt
  have hconvex : convexHull ℝ (P.rootSet ℂ) ⊆ Metric.ball 0 1 :=
    convexHull_min hroots (convex_ball 0 1)
  have hzHull : z ∈ convexHull ℝ (P.rootSet ℂ) :=
    Polynomial.rootSet_derivative_subset_convexHull_rootSet hPdegreePos hzDerivRoot
  have hzlt : ‖z‖ < 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hconvex hzHull
  linarith

noncomputable def eulerDeriv (p : Polynomial ℂ) : Polynomial ℂ :=
  Polynomial.X * p.derivative

@[simp]
theorem eval_eulerDeriv (p : Polynomial ℂ) (z : ℂ) :
    (eulerDeriv p).eval z = z * p.derivative.eval z := by
  simp [eulerDeriv]

theorem natDegree_eulerDeriv_le (p : Polynomial ℂ) :
    (eulerDeriv p).natDegree ≤ p.natDegree := by
  by_cases hp : p.natDegree = 0
  · simp [eulerDeriv, Polynomial.derivative_of_natDegree_zero hp, hp]
  have hd := Polynomial.natDegree_derivative_le p
  calc
    (eulerDeriv p).natDegree ≤
        Polynomial.X.natDegree + p.derivative.natDegree := by
      exact natDegree_mul_le
    _ ≤ 1 + (p.natDegree - 1) := by
      simp only [Polynomial.natDegree_X]
      exact Nat.add_le_add_left hd 1
    _ = p.natDegree := by omega

theorem natDegree_iterate_eulerDeriv_le (r : ℕ) (p : Polynomial ℂ) :
    (eulerDeriv^[r] p).natDegree ≤ p.natDegree := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply']
      exact (natDegree_eulerDeriv_le _).trans ih

theorem norm_iterate_eulerDeriv_eval_le_pow_mul_circSup
    {p : Polynomial ℂ} {n : ℕ} (hdeg : p.natDegree ≤ n) {M : ℝ}
    (hM : ∀ w : ℂ, ‖w‖ = 1 → ‖p.eval w‖ ≤ M)
    (r : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(eulerDeriv^[r] p).eval z‖ ≤ (n : ℝ) ^ r * M := by
  induction r generalizing z with
  | zero => simpa using hM z hz
  | succ r ih =>
      let q := eulerDeriv^[r] p
      have hqdeg : q.natDegree ≤ n :=
        (natDegree_iterate_eulerDeriv_le r p).trans hdeg
      have hqM : ∀ w : ℂ, ‖w‖ = 1 → ‖q.eval w‖ ≤ (n : ℝ) ^ r * M := by
        intro w hw
        exact ih hw
      have hderiv :=
        norm_deriv_eval_le_degree_mul_circSup hqdeg hqM hz
      rw [Function.iterate_succ_apply']
      calc
        ‖(eulerDeriv q).eval z‖ = ‖q.derivative.eval z‖ := by
          rw [eval_eulerDeriv, norm_mul, hz, one_mul]
        _ ≤ (n : ℝ) * ((n : ℝ) ^ r * M) := hderiv
        _ = (n : ℝ) ^ (r + 1) * M := by rw [pow_succ]; ring

end Bern

end

open Bern


section

namespace CosAlgebra

def leadingDeriv (k : ℕ) (A B : ℂ) : ℂ :=
  Complex.I ^ k * A + ((2 : ℂ) * Complex.I) ^ k * B

def leadingReal (k : ℕ) (A B : ℂ) : ℝ :=
  (leadingDeriv k A B).re

@[simp] theorem leadingReal_zero (A B : ℂ) :
    leadingReal 0 A B = A.re + B.re := by
  simp [leadingReal, leadingDeriv]

@[simp] theorem leadingReal_one (A B : ℂ) :
    leadingReal 1 A B = -A.im - 2 * B.im := by
  simp [leadingReal, leadingDeriv]
  ring

@[simp] theorem leadingReal_two (A B : ℂ) :
    leadingReal 2 A B = -A.re - 4 * B.re := by
  norm_num [leadingReal, leadingDeriv, pow_succ]
  ring

@[simp] theorem leadingReal_three (A B : ℂ) :
    leadingReal 3 A B = A.im + 8 * B.im := by
  norm_num [leadingReal, leadingDeriv, pow_succ]

theorem energy_le_of_leadingReal_le {A B : ℂ} {ε : ℝ}
    (hε : 0 ≤ ε)
    (h0 : |leadingReal 0 A B| ≤ ε)
    (h1 : |leadingReal 1 A B| ≤ ε)
    (h2 : |leadingReal 2 A B| ≤ ε)
    (h3 : |leadingReal 3 A B| ≤ ε) :
    ‖A‖ ^ 2 + ‖B‖ ^ 2 ≤ (55 / 9 : ℝ) * ε ^ 2 := by
  have h0' := abs_le.mp h0
  have h1' := abs_le.mp h1
  have h2' := abs_le.mp h2
  have h3' := abs_le.mp h3
  have hAre : |A.re| ≤ (5 / 3 : ℝ) * ε := by
    rw [abs_le]
    simp only [leadingReal_zero, leadingReal_two] at h0' h2'
    constructor <;> nlinarith
  have hAim : |A.im| ≤ (5 / 3 : ℝ) * ε := by
    rw [abs_le]
    simp only [leadingReal_one, leadingReal_three] at h1' h3'
    constructor <;> nlinarith
  have hBre : |B.re| ≤ (2 / 3 : ℝ) * ε := by
    rw [abs_le]
    simp only [leadingReal_zero, leadingReal_two] at h0' h2'
    constructor <;> nlinarith
  have hBim : |B.im| ≤ (1 / 3 : ℝ) * ε := by
    rw [abs_le]
    simp only [leadingReal_one, leadingReal_three] at h1' h3'
    constructor <;> nlinarith
  have hAreSq : A.re ^ 2 ≤ ((5 / 3 : ℝ) * ε) ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg A.re) (mul_nonneg (by norm_num) hε)).2 hAre
  have hAimSq : A.im ^ 2 ≤ ((5 / 3 : ℝ) * ε) ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg A.im) (mul_nonneg (by norm_num) hε)).2 hAim
  have hBreSq : B.re ^ 2 ≤ ((2 / 3 : ℝ) * ε) ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg B.re) (mul_nonneg (by norm_num) hε)).2 hBre
  have hBimSq : B.im ^ 2 ≤ ((1 / 3 : ℝ) * ε) ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg B.im) (mul_nonneg (by norm_num) hε)).2 hBim
  rw [sq_norm, sq_norm, normSq_apply, normSq_apply]
  nlinarith

theorem energy_le_fiftyFive_div_sixtyFour {A B : ℂ}
    (h : ∀ k : Fin 4, |leadingReal k A B| ≤ 3 / 8) :
    ‖A‖ ^ 2 + ‖B‖ ^ 2 ≤ (55 / 64 : ℝ) := by
  have hbound := energy_le_of_leadingReal_le (A := A) (B := B)
    (ε := (3 / 8 : ℝ)) (by norm_num)
    (by simpa using h ⟨0, by omega⟩)
    (by simpa using h ⟨1, by omega⟩)
    (by simpa using h ⟨2, by omega⟩)
    (by simpa using h ⟨3, by omega⟩)
  norm_num at hbound ⊢
  exact hbound

theorem exists_large_of_real_error {A B : ℂ} (D : Fin 4 → ℝ)
    (henergy : ‖A‖ ^ 2 + ‖B‖ ^ 2 = 1)
    (herror : ∀ k : Fin 4, |D k - leadingReal k A B| ≤ 1 / 8) :
    ∃ k : Fin 4, 1 / 4 ≤ |D k| := by
  by_contra hlarge
  push_neg at hlarge
  have hleading : ∀ k : Fin 4, |leadingReal k A B| ≤ 3 / 8 := by
    intro k
    calc
      |leadingReal k A B| = |D k - (D k - leadingReal k A B)| := by ring_nf
      _ ≤ |D k| + |D k - leadingReal k A B| := abs_sub _ _
      _ ≤ 3 / 8 := by
        have hk := herror k
        have hk' := hlarge k
        linarith
  have hsmall := energy_le_fiftyFive_div_sixtyFour hleading
  rw [henergy] at hsmall
  norm_num at hsmall

theorem exists_large_re_of_complex_error {A B : ℂ} (D : Fin 4 → ℂ)
    (henergy : ‖A‖ ^ 2 + ‖B‖ ^ 2 = 1)
    (herror : ∀ k : Fin 4, ‖D k - leadingDeriv k A B‖ ≤ 1 / 8) :
    ∃ k : Fin 4, 1 / 4 ≤ |(D k).re| := by
  apply exists_large_of_real_error (fun k ↦ (D k).re) henergy
  intro k
  have hre :
      |(D k - leadingDeriv k A B).re| ≤
        ‖D k - leadingDeriv k A B‖ :=
    abs_re_le_norm _
  have hid :
      (D k - leadingDeriv k A B).re =
        (D k).re - leadingReal k A B := by
    rfl
  rw [hid] at hre
  exact hre.trans (herror k)

theorem phase_energy {u v α beta : ℂ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (henergy : ‖α‖ ^ 2 + ‖beta‖ ^ 2 = 1) :
    ‖u * α‖ ^ 2 + ‖v * beta‖ ^ 2 = 1 := by
  rw [norm_mul, norm_mul, hu, hv, one_mul, one_mul]
  exact henergy

theorem exists_large_re_of_norm_modes {u v α beta : ℂ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (henergy : ‖α‖ ^ 2 + ‖beta‖ ^ 2 = 1)
    (D : Fin 4 → ℂ)
    (herror : ∀ k : Fin 4,
      ‖D k - leadingDeriv k (u * α) (v * beta)‖ ≤ 1 / 8) :
    ∃ k : Fin 4, 1 / 4 ≤ |(D k).re| :=
  exists_large_re_of_complex_error D (phase_energy hu hv henergy) herror

end CosAlgebra

end

section

open scoped BigOperators ComplexConjugate

noncomputable section

def unitPt (θ : ℝ) : ℂ :=
  Complex.exp ((θ : ℂ) * Complex.I)

@[simp]
theorem norm_unitPt (θ : ℝ) : ‖unitPt θ‖ = 1 := by
  simp [unitPt, Complex.norm_exp]

@[simp]
theorem unitPt_ne_zero (θ : ℝ) : unitPt θ ≠ 0 := by
  simp [unitPt]

@[simp]
theorem unitPt_neg (θ : ℝ) : unitPt (-θ) = (unitPt θ)⁻¹ := by
  simp [unitPt, Complex.exp_neg]

theorem unitPt_pow (θ : ℝ) (k : ℕ) :
    unitPt θ ^ k =
      (cos (k * θ) : ℂ) + (sin (k * θ) : ℂ) * Complex.I := by
  rw [unitPt, ← exp_nat_mul]
  have harg : (k : ℂ) * ((θ : ℂ) * Complex.I) =
      (((k : ℝ) * θ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, ← Complex.cos_add_sin_I]
  simp

theorem unitPt_inv_pow (θ : ℝ) (k : ℕ) :
    (unitPt θ)⁻¹ ^ k =
      (cos (k * θ) : ℂ) - (sin (k * θ) : ℂ) * Complex.I := by
  rw [← unitPt_neg, unitPt_pow]
  simp [cos_neg, sin_neg]
  ring_nf

theorem unitPt_pow_add_inv_pow (θ : ℝ) (k : ℕ) :
    unitPt θ ^ k + (unitPt θ)⁻¹ ^ k =
      (2 * cos (k * θ) : ℝ) := by
  rw [unitPt_pow, unitPt_inv_pow]
  push_cast
  ring

theorem unitPt_pow_sub_inv_pow (θ : ℝ) (k : ℕ) :
    unitPt θ ^ k - (unitPt θ)⁻¹ ^ k =
      (2 * sin (k * θ) : ℝ) * Complex.I := by
  rw [unitPt_pow, unitPt_inv_pow]
  push_cast
  ring

def cosSum (s : Finset ℕ) (eps : ℕ → ℝ) (θ : ℝ) : ℝ :=
  ∑ k ∈ s, eps k * cos (k * θ)

def sineSum (s : Finset ℕ) (eps : ℕ → ℝ) (θ : ℝ) : ℝ :=
  ∑ k ∈ s, eps k * sin (k * θ)

def pairLaurentValue (C Se So : Finset ℕ)
    (epsC epsE epsO : ℕ → ℝ) (θ : ℝ) : ℂ :=
  1 +
    ∑ k ∈ C, (epsC k : ℂ) *
      (unitPt θ ^ k + (unitPt θ)⁻¹ ^ k) +
    ∑ k ∈ Se, (epsE k : ℂ) *
      (unitPt θ ^ k - (unitPt θ)⁻¹ ^ k) +
    ∑ k ∈ So, (epsO k : ℂ) *
      (unitPt θ ^ k - (unitPt θ)⁻¹ ^ k)

def asmValue (c se so : ℝ) : ℂ :=
  ((1 + 2 * c : ℝ) : ℂ) + ((2 * (se + so) : ℝ) : ℂ) * Complex.I

@[simp]
theorem asmValue_re (c se so : ℝ) :
    (asmValue c se so).re = 1 + 2 * c := by
  simp [asmValue]

@[simp]
theorem asmValue_im (c se so : ℝ) :
    (asmValue c se so).im = 2 * (se + so) := by
  simp [asmValue]

theorem pairLaurentValue_eq_asmValue (C Se So : Finset ℕ)
    (epsC epsE epsO : ℕ → ℝ) (θ : ℝ) :
    pairLaurentValue C Se So epsC epsE epsO θ =
      asmValue (cosSum C epsC θ)
        (sineSum Se epsE θ) (sineSum So epsO θ) := by
  classical
  have hC :
      (∑ k ∈ C, (epsC k : ℂ) *
        (unitPt θ ^ k + (unitPt θ)⁻¹ ^ k)) =
        ((2 * cosSum C epsC θ : ℝ) : ℂ) := by
    rw [cosSum]
    push_cast
    simp only [Finset.mul_sum]
    apply sum_congr rfl
    intro k hk
    rw [unitPt_pow_add_inv_pow]
    push_cast
    ring
  have hE :
      (∑ k ∈ Se, (epsE k : ℂ) *
        (unitPt θ ^ k - (unitPt θ)⁻¹ ^ k)) =
        ((2 * sineSum Se epsE θ : ℝ) : ℂ) * Complex.I := by
    rw [sineSum]
    push_cast
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply sum_congr rfl
    intro k hk
    rw [unitPt_pow_sub_inv_pow]
    push_cast
    ring
  have hO :
      (∑ k ∈ So, (epsO k : ℂ) *
        (unitPt θ ^ k - (unitPt θ)⁻¹ ^ k)) =
        ((2 * sineSum So epsO θ : ℝ) : ℂ) * Complex.I := by
    rw [sineSum]
    push_cast
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply sum_congr rfl
    intro k hk
    rw [unitPt_pow_sub_inv_pow]
    push_cast
    ring
  rw [pairLaurentValue, hC, hE, hO]
  simp only [asmValue]
  push_cast
  ring

theorem two_mul_abs_sub_one_le_norm_asmValue (c se so : ℝ) :
    2 * |c| - 1 ≤ ‖asmValue c se so‖ := by
  have htriangle : |2 * c| ≤ |1 + 2 * c| + 1 := by
    calc
      |2 * c| = |(1 + 2 * c) - 1| := by ring_nf
      _ ≤ |1 + 2 * c| + |(1 : ℝ)| := abs_sub _ _
      _ = |1 + 2 * c| + 1 := by norm_num
  have hre : |1 + 2 * c| ≤ ‖asmValue c se so‖ := by
    simpa using abs_re_le_norm (asmValue c se so)
  rw [abs_mul] at htriangle
  norm_num at htriangle
  linarith

theorem two_mul_abs_sub_abs_le_norm_asmValue (c se so : ℝ) :
    2 * (|so| - |se|) ≤ ‖asmValue c se so‖ := by
  have htriangle : |so| ≤ |se + so| + |se| := by
    calc
      |so| = |(se + so) - se| := by ring_nf
      _ ≤ |se + so| + |se| := abs_sub _ _
  have him : |2 * (se + so)| ≤ ‖asmValue c se so‖ := by
    simpa using abs_im_le_norm (asmValue c se so)
  rw [abs_mul] at him
  norm_num at him
  linarith

theorem le_norm_asmValue_of_sin_gap {a c se so : ℝ}
    (hgap : a / 2 + |se| ≤ |so|) :
    a ≤ ‖asmValue c se so‖ := by
  have h := two_mul_abs_sub_abs_le_norm_asmValue c se so
  linarith

theorem norm_asmValue_le (c se so A B D : ℝ)
    (hA : |c| ≤ A) (hB : |se| ≤ B) (hD : |so| ≤ D) :
    ‖asmValue c se so‖ ≤ 1 + 2 * (A + B + D) := by
  calc
    ‖asmValue c se so‖ ≤ |1 + 2 * c| + |2 * (se + so)| := by
      simpa [asmValue] using
        Complex.norm_le_abs_re_add_abs_im (asmValue c se so)
    _ ≤ (1 + 2 * |c|) + 2 * (|se| + |so|) := by
      calc
        |1 + 2 * c| + |2 * (se + so)| ≤
            (|1| + |2 * c|) + |2| * (|se| + |so|) := by
              gcongr
              · exact abs_add_le _ _
              · rw [abs_mul]
                gcongr
                exact abs_add_le _ _
        _ = (1 + 2 * |c|) + 2 * (|se| + |so|) := by norm_num
    _ ≤ 1 + 2 * (A + B + D) := by linarith

theorem norm_asmValue_le_two_pow_twelve_sqrt {n : ℕ} {c se so : ℝ}
    (hn : 1 ≤ n)
    (hc : |c| ≤ sqrt n)
    (hse : |se| ≤ 6 * sqrt n)
    (hso : |so| ≤ 2 ^ 10 * sqrt n) :
    ‖asmValue c se so‖ ≤ 2 ^ 12 * sqrt n := by
  have hsqrt : 1 ≤ sqrt n := by
    rw [one_le_sqrt]
    exact_mod_cast hn
  have h := norm_asmValue_le c se so
    (sqrt n) (6 * sqrt n) (2 ^ 10 * sqrt n) hc hse hso
  norm_num at h ⊢
  nlinarith

theorem eight_sqrt_le_norm_asmValue_of_odd_sin {n : ℕ} {c se so : ℝ}
    (hse : |se| ≤ 6 * sqrt n)
    (hso : 10 * sqrt n ≤ |so|) :
    8 * sqrt n ≤ ‖asmValue c se so‖ := by
  apply le_norm_asmValue_of_sin_gap
  linarith

end

end

section

open scoped ComplexConjugate

noncomputable section

mutual

  def rudinShapiroP : ℕ → Polynomial ℂ
    | 0 => 1
    | t + 1 => rudinShapiroP t + Polynomial.X ^ (2 ^ t) * rudinShapiroQ t

  def rudinShapiroQ : ℕ → Polynomial ℂ
    | 0 => 1
    | t + 1 => rudinShapiroP t - Polynomial.X ^ (2 ^ t) * rudinShapiroQ t
end

@[simp] theorem rsP_zero : rudinShapiroP 0 = 1 := rfl
@[simp] theorem rsQ_zero : rudinShapiroQ 0 = 1 := rfl

@[simp] theorem rsP_succ (t : ℕ) :
    rudinShapiroP (t + 1) =
      rudinShapiroP t + Polynomial.X ^ (2 ^ t) * rudinShapiroQ t := rfl

@[simp] theorem rsQ_succ (t : ℕ) :
    rudinShapiroQ (t + 1) =
      rudinShapiroP t - Polynomial.X ^ (2 ^ t) * rudinShapiroQ t := rfl

@[simp] theorem eval_rsP_succ (t : ℕ) (z : ℂ) :
    (rudinShapiroP (t + 1)).eval z =
      (rudinShapiroP t).eval z + z ^ (2 ^ t) * (rudinShapiroQ t).eval z := by
  simp [rsP_succ]

@[simp] theorem eval_rsQ_succ (t : ℕ) (z : ℂ) :
    (rudinShapiroQ (t + 1)).eval z =
      (rudinShapiroP t).eval z - z ^ (2 ^ t) * (rudinShapiroQ t).eval z := by
  simp [rsQ_succ]

lemma normSq_add_mul_add_normSq_sub_mul (a b u : ℂ) :
    normSq (a + u * b) + normSq (a - u * b) =
      2 * (normSq a + normSq u * normSq b) := by
  rw [Complex.normSq_add, Complex.normSq_sub, Complex.normSq_mul]
  ring

theorem rs_energy (t : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(rudinShapiroP t).eval z‖ ^ 2 + ‖(rudinShapiroQ t).eval z‖ ^ 2 =
      (2 ^ (t + 1) : ℝ) := by
  induction t with
  | zero => norm_num
  | succ t ih =>
      rw [eval_rsP_succ, eval_rsQ_succ,
        ← normSq_eq_norm_sq, ← normSq_eq_norm_sq,
        normSq_add_mul_add_normSq_sub_mul]
      have hzu : normSq (z ^ (2 ^ t)) = 1 := by
        simp [normSq_eq_norm_sq, norm_pow, hz]
      rw [hzu, one_mul, normSq_eq_norm_sq, normSq_eq_norm_sq, ih]
      rw [show (2 ^ (t + 1 + 1) : ℝ) = 2 ^ (t + 1) * 2 by
        rw [pow_succ]]
      ring

theorem norm_eval_rsP_le (t : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(rudinShapiroP t).eval z‖ ≤ sqrt (2 ^ (t + 1) : ℝ) := by
  have h := rs_energy t hz
  have hsq : ‖(rudinShapiroP t).eval z‖ ^ 2 ≤ (2 ^ (t + 1) : ℝ) := by
    nlinarith [sq_nonneg ‖(rudinShapiroQ t).eval z‖]
  nlinarith [sq_sqrt (show 0 ≤ (2 ^ (t + 1) : ℝ) by positivity),
    sqrt_nonneg (2 ^ (t + 1) : ℝ)]

theorem norm_eval_rsQ_le (t : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(rudinShapiroQ t).eval z‖ ≤ sqrt (2 ^ (t + 1) : ℝ) := by
  have h := rs_energy t hz
  have hsq : ‖(rudinShapiroQ t).eval z‖ ^ 2 ≤ (2 ^ (t + 1) : ℝ) := by
    nlinarith [sq_nonneg ‖(rudinShapiroP t).eval z‖]
  nlinarith [sq_sqrt (show 0 ≤ (2 ^ (t + 1) : ℝ) by positivity),
    sqrt_nonneg (2 ^ (t + 1) : ℝ)]

structure RsCoeffFacts (t : ℕ) : Prop where
  p_sign : ∀ k < 2 ^ t, (rudinShapiroP t).coeff k = 1 ∨
    (rudinShapiroP t).coeff k = -1
  q_sign : ∀ k < 2 ^ t, (rudinShapiroQ t).coeff k = 1 ∨
    (rudinShapiroQ t).coeff k = -1
  p_zero : ∀ k, 2 ^ t ≤ k → (rudinShapiroP t).coeff k = 0
  q_zero : ∀ k, 2 ^ t ≤ k → (rudinShapiroQ t).coeff k = 0

theorem rs_coeffFacts (t : ℕ) : RsCoeffFacts t := by
  induction t with
  | zero =>
      constructor
      · intro k hk
        have : k = 0 := by omega
        subst k
        simp
      · intro k hk
        have : k = 0 := by omega
        subst k
        simp
      · intro k hk
        have : k ≠ 0 := by omega
        simp [coeff_one, this]
      · intro k hk
        have : k ≠ 0 := by omega
        simp [coeff_one, this]
  | succ t ih =>
      have hpow : 2 ^ (t + 1) = 2 ^ t + 2 ^ t := by
        simp [pow_succ, mul_two]
      constructor
      · intro k hk
        rw [rsP_succ, coeff_add,
          coeff_X_pow_mul']
        by_cases hlow : k < 2 ^ t
        · rw [if_neg (Nat.not_le.mpr hlow), add_zero]
          exact ih.p_sign k hlow
        · have hle : 2 ^ t ≤ k := Nat.le_of_not_gt hlow
          rw [if_pos hle, ih.p_zero k hle, zero_add]
          have hrest : k - 2 ^ t < 2 ^ t := by omega
          exact ih.q_sign (k - 2 ^ t) hrest
      · intro k hk
        rw [rsQ_succ, coeff_sub,
          coeff_X_pow_mul']
        by_cases hlow : k < 2 ^ t
        · rw [if_neg (Nat.not_le.mpr hlow), sub_zero]
          exact ih.p_sign k hlow
        · have hle : 2 ^ t ≤ k := Nat.le_of_not_gt hlow
          rw [if_pos hle, ih.p_zero k hle, zero_sub]
          have hrest : k - 2 ^ t < 2 ^ t := by omega
          rcases ih.q_sign (k - 2 ^ t) hrest with h | h
          · right
            rw [h]
          · left
            rw [h]
            simp
      · intro k hk
        rw [rsP_succ, coeff_add,
          coeff_X_pow_mul']
        have hle : 2 ^ t ≤ k := by omega
        rw [if_pos hle, ih.p_zero k hle, zero_add]
        apply ih.q_zero
        omega
      · intro k hk
        rw [rsQ_succ, coeff_sub,
          coeff_X_pow_mul']
        have hle : 2 ^ t ≤ k := by omega
        rw [if_pos hle, ih.p_zero k hle, zero_sub]
        rw [ih.q_zero]
        · simp
        · omega

theorem coeff_rsP_eq_one_or_neg_one {t k : ℕ} (hk : k < 2 ^ t) :
    (rudinShapiroP t).coeff k = 1 ∨ (rudinShapiroP t).coeff k = -1 :=
  (rs_coeffFacts t).p_sign k hk

theorem coeff_rsQ_eq_one_or_neg_one {t k : ℕ} (hk : k < 2 ^ t) :
    (rudinShapiroQ t).coeff k = 1 ∨ (rudinShapiroQ t).coeff k = -1 :=
  (rs_coeffFacts t).q_sign k hk

theorem coeff_rsP_eq_zero {t k : ℕ} (hk : 2 ^ t ≤ k) :
    (rudinShapiroP t).coeff k = 0 :=
  (rs_coeffFacts t).p_zero k hk

theorem coeff_rsQ_eq_zero {t k : ℕ} (hk : 2 ^ t ≤ k) :
    (rudinShapiroQ t).coeff k = 0 :=
  (rs_coeffFacts t).q_zero k hk

theorem natDegree_rsP (t : ℕ) :
    (rudinShapiroP t).natDegree = 2 ^ t - 1 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    apply coeff_rsP_eq_zero
    have hpos : 0 < 2 ^ t := by positivity
    omega
  · have hpos : 0 < 2 ^ t := by positivity
    have hlt : 2 ^ t - 1 < 2 ^ t := by omega
    rcases coeff_rsP_eq_one_or_neg_one hlt with h | h <;> simp [h]

theorem natDegree_rsQ (t : ℕ) :
    (rudinShapiroQ t).natDegree = 2 ^ t - 1 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    apply coeff_rsQ_eq_zero
    have hpos : 0 < 2 ^ t := by positivity
    omega
  · have hpos : 0 < 2 ^ t := by positivity
    have hlt : 2 ^ t - 1 < 2 ^ t := by omega
    rcases coeff_rsQ_eq_one_or_neg_one hlt with h | h <;> simp [h]

def polyPrefix (p : Polynomial ℂ) (m : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range m, Polynomial.C (p.coeff k) * Polynomial.X ^ k

@[simp] theorem polyPrefix_zero (p : Polynomial ℂ) : polyPrefix p 0 = 0 := by
  simp [polyPrefix]

theorem coeff_polyPrefix (p : Polynomial ℂ) (m k : ℕ) :
    (polyPrefix p m).coeff k = if k < m then p.coeff k else 0 := by
  simp [polyPrefix, coeff_C_mul]

theorem coeff_rsP_succ_of_lt {t k : ℕ} (hk : k < 2 ^ t) :
    (rudinShapiroP (t + 1)).coeff k = (rudinShapiroP t).coeff k := by
  rw [rsP_succ, coeff_add, coeff_X_pow_mul',
    if_neg (Nat.not_le.mpr hk), add_zero]

theorem coeff_rsQ_succ_of_lt {t k : ℕ} (hk : k < 2 ^ t) :
    (rudinShapiroQ (t + 1)).coeff k = (rudinShapiroP t).coeff k := by
  rw [rsQ_succ, coeff_sub, coeff_X_pow_mul',
    if_neg (Nat.not_le.mpr hk), sub_zero]

@[simp] theorem coeff_rsP_succ_add (t k : ℕ) :
    (rudinShapiroP (t + 1)).coeff (2 ^ t + k) = (rudinShapiroQ t).coeff k := by
  rw [rsP_succ, coeff_add, coeff_X_pow_mul',
    if_pos (Nat.le_add_right _ _), coeff_rsP_eq_zero]
  · simp
  · exact Nat.le_add_right _ _

@[simp] theorem coeff_rsQ_succ_add (t k : ℕ) :
    (rudinShapiroQ (t + 1)).coeff (2 ^ t + k) = -(rudinShapiroQ t).coeff k := by
  rw [rsQ_succ, coeff_sub, coeff_X_pow_mul',
    if_pos (Nat.le_add_right _ _), coeff_rsP_eq_zero]
  · simp
  · exact Nat.le_add_right _ _

theorem polyPrefix_rsP_succ_of_le {t m : ℕ} (hm : m ≤ 2 ^ t) :
    polyPrefix (rudinShapiroP (t + 1)) m =
      polyPrefix (rudinShapiroP t) m := by
  ext k
  rw [coeff_polyPrefix, coeff_polyPrefix]
  split_ifs with hk
  · exact coeff_rsP_succ_of_lt (lt_of_lt_of_le hk hm)
  · rfl

theorem polyPrefix_rsQ_succ_of_le {t m : ℕ} (hm : m ≤ 2 ^ t) :
    polyPrefix (rudinShapiroQ (t + 1)) m =
      polyPrefix (rudinShapiroP t) m := by
  ext k
  rw [coeff_polyPrefix, coeff_polyPrefix]
  split_ifs with hk
  · exact coeff_rsQ_succ_of_lt (lt_of_lt_of_le hk hm)
  · rfl

theorem polyPrefix_rsP_succ_add (t r : ℕ) :
    polyPrefix (rudinShapiroP (t + 1)) (2 ^ t + r) =
      rudinShapiroP t + Polynomial.X ^ (2 ^ t) * polyPrefix (rudinShapiroQ t) r := by
  ext k
  rw [coeff_polyPrefix, coeff_add, coeff_X_pow_mul',
    coeff_polyPrefix]
  by_cases hlow : k < 2 ^ t
  · have htotal : k < 2 ^ t + r := lt_of_lt_of_le hlow (Nat.le_add_right _ _)
    rw [if_pos htotal, if_neg (Nat.not_le.mpr hlow), add_zero]
    exact coeff_rsP_succ_of_lt hlow
  · have hle : 2 ^ t ≤ k := Nat.le_of_not_gt hlow
    rw [if_pos hle, coeff_rsP_eq_zero hle, zero_add]
    by_cases htotal : k < 2 ^ t + r
    · have hrest : k - 2 ^ t < r := by omega
      rw [if_pos htotal, if_pos hrest]
      rw [← Nat.add_sub_of_le hle, coeff_rsP_succ_add]
      simp
    · have hrest : ¬ k - 2 ^ t < r := by omega
      rw [if_neg htotal, if_neg hrest]

theorem polyPrefix_rsQ_succ_add (t r : ℕ) :
    polyPrefix (rudinShapiroQ (t + 1)) (2 ^ t + r) =
      rudinShapiroP t - Polynomial.X ^ (2 ^ t) * polyPrefix (rudinShapiroQ t) r := by
  ext k
  rw [coeff_polyPrefix, coeff_sub, coeff_X_pow_mul',
    coeff_polyPrefix]
  by_cases hlow : k < 2 ^ t
  · have htotal : k < 2 ^ t + r := lt_of_lt_of_le hlow (Nat.le_add_right _ _)
    rw [if_pos htotal, if_neg (Nat.not_le.mpr hlow), sub_zero]
    exact coeff_rsQ_succ_of_lt hlow
  · have hle : 2 ^ t ≤ k := Nat.le_of_not_gt hlow
    rw [if_pos hle, coeff_rsP_eq_zero hle, zero_sub]
    by_cases htotal : k < 2 ^ t + r
    · have hrest : k - 2 ^ t < r := by omega
      rw [if_pos htotal, if_pos hrest]
      rw [← Nat.add_sub_of_le hle, coeff_rsQ_succ_add]
      simp
    · have hrest : ¬ k - 2 ^ t < r := by omega
      rw [if_neg htotal, if_neg hrest, neg_zero]

private lemma sqrt_two_mul_add_five_sqrt_le_five_sqrt_add
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hyx : y ≤ x) :
    sqrt (2 * x) + 5 * sqrt y ≤ 5 * sqrt (x + y) := by
  have h2x : 0 ≤ 2 * x := by positivity
  have hxy : 0 ≤ x + y := by positivity
  have hs2x := sq_sqrt h2x
  have hsy := sq_sqrt hy
  have hsxy := sq_sqrt hxy
  have hn2x := sqrt_nonneg (2 * x)
  have hny := sqrt_nonneg y
  have hnxy := sqrt_nonneg (x + y)
  nlinarith [sq_nonneg (sqrt (2 * x) - sqrt y),
    sq_nonneg (sqrt (2 * x) + 5 * sqrt y - 5 * sqrt (x + y))]

theorem norm_eval_polyPrefix_rs (t m : ℕ) {z : ℂ}
    (hm : m ≤ 2 ^ t) (hz : ‖z‖ = 1) :
    ‖(polyPrefix (rudinShapiroP t) m).eval z‖ ≤ 5 * sqrt m ∧
      ‖(polyPrefix (rudinShapiroQ t) m).eval z‖ ≤ 5 * sqrt m := by
  induction t generalizing m with
  | zero =>
      have hm' : m ≤ 1 := by simpa using hm
      interval_cases m <;> norm_num [polyPrefix, rudinShapiroP, rudinShapiroQ]
  | succ t ih =>
      have hpow : 2 ^ (t + 1) = 2 ^ t + 2 ^ t := by simp [pow_succ, mul_two]
      by_cases hlow : m ≤ 2 ^ t
      · rw [polyPrefix_rsP_succ_of_le hlow,
          polyPrefix_rsQ_succ_of_le hlow]
        exact ⟨(ih m hlow).1, (ih m hlow).1⟩
      · have hAm : 2 ^ t ≤ m := by omega
        let r := m - 2 ^ t
        have hm_eq : 2 ^ t + r = m := by
          dsimp [r]
          omega
        have hr : r ≤ 2 ^ t := by omega
        have hir := ih r hr
        have hfull := norm_eval_rsP_le t hz
        have hcastpow : (2 ^ (t + 1) : ℝ) = 2 * (2 ^ t : ℝ) := by
          rw [pow_succ]
          ring
        have hsqrt : sqrt (2 ^ (t + 1) : ℝ) =
            sqrt (2 * (2 ^ t : ℝ)) := congrArg sqrt hcastpow
        have hsqrt_bound : sqrt (2 * (2 ^ t : ℝ)) + 5 * sqrt (r : ℝ) ≤
            5 * sqrt ((2 ^ t : ℝ) + r) := by
          apply sqrt_two_mul_add_five_sqrt_le_five_sqrt_add
          · positivity
          · positivity
          · exact_mod_cast hr
        constructor
        · rw [← hm_eq, polyPrefix_rsP_succ_add,
            eval_add, eval_mul, eval_pow, eval_X]
          calc
            ‖(rudinShapiroP t).eval z + z ^ 2 ^ t *
                (polyPrefix (rudinShapiroQ t) r).eval z‖
                ≤ ‖(rudinShapiroP t).eval z‖ +
                    ‖z ^ 2 ^ t * (polyPrefix (rudinShapiroQ t) r).eval z‖ :=
              norm_add_le _ _
            _ = ‖(rudinShapiroP t).eval z‖ +
                ‖(polyPrefix (rudinShapiroQ t) r).eval z‖ := by
              rw [norm_mul, norm_pow, hz, one_pow, one_mul]
            _ ≤ sqrt (2 * (2 ^ t : ℝ)) + 5 * sqrt (r : ℝ) := by
              rw [← hsqrt]
              exact add_le_add hfull hir.2
            _ ≤ 5 * sqrt ((2 ^ t : ℝ) + r) := hsqrt_bound
            _ = 5 * sqrt ((2 ^ t + r : ℕ) : ℝ) := by norm_num
        · rw [← hm_eq, polyPrefix_rsQ_succ_add,
            eval_sub, eval_mul, eval_pow, eval_X]
          calc
            ‖(rudinShapiroP t).eval z - z ^ 2 ^ t *
                (polyPrefix (rudinShapiroQ t) r).eval z‖
                ≤ ‖(rudinShapiroP t).eval z‖ +
                    ‖z ^ 2 ^ t * (polyPrefix (rudinShapiroQ t) r).eval z‖ :=
              norm_sub_le _ _
            _ = ‖(rudinShapiroP t).eval z‖ +
                ‖(polyPrefix (rudinShapiroQ t) r).eval z‖ := by
              rw [norm_mul, norm_pow, hz, one_pow, one_mul]
            _ ≤ sqrt (2 * (2 ^ t : ℝ)) + 5 * sqrt (r : ℝ) := by
              rw [← hsqrt]
              exact add_le_add hfull hir.2
            _ ≤ 5 * sqrt ((2 ^ t : ℝ) + r) := hsqrt_bound
            _ = 5 * sqrt ((2 ^ t + r : ℕ) : ℝ) := by norm_num

theorem norm_eval_polyPrefix_rsP_le (t m : ℕ) {z : ℂ}
    (hm : m ≤ 2 ^ t) (hz : ‖z‖ = 1) :
    ‖(polyPrefix (rudinShapiroP t) m).eval z‖ ≤ 5 * sqrt m :=
  (norm_eval_polyPrefix_rs t m hm hz).1

end

end

section

open scoped BigOperators ComplexConjugate

noncomputable section

def evenT (t : ℕ) : ℕ := 2 ^ (t + 10)

def gammaNum (t : ℕ) : ℕ :=
  2 ^ (t + 11) + 2 ^ t - 1

structure EvenParams (n t : ℕ) (γ : ℝ) : Prop where
  t_odd : Odd t
  gamma_pos : 0 < γ
  gamma_le : γ ≤ 1 / 2 ^ 40
  equation : γ * n = gammaNum t

def evenCPrime (t : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ t)).image (fun j => evenT t + j) ∪
    (Finset.range (2 ^ t)).image (fun j => 2 * evenT t + j)

def evenC (t : ℕ) : Finset ℕ :=
  (evenCPrime t).image (fun j => 2 * j)

def evenSPrime (n t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n) \ evenCPrime t

def evenS (n t : ℕ) : Finset ℕ :=
  (evenSPrime n t).image (fun j => 2 * j)

def cosBlk (t : ℕ) : Polynomial ℂ :=
  Polynomial.X ^ evenT t * rudinShapiroP t +
    Polynomial.X ^ (2 * evenT t) * rudinShapiroQ t

def deletedEvenBlk (t : ℕ) : Polynomial ℂ :=
  Polynomial.X ^ evenT t * rudinShapiroP t +
    Polynomial.X ^ (2 * evenT t) * rudinShapiroP t

def evenRemainder (n t u : ℕ) : Polynomial ℂ :=
  polyPrefix (rudinShapiroP u) (n + 1) - deletedEvenBlk t

def evenCos (t : ℕ) (θ : ℝ) : ℝ :=
  (cosBlk t).eval (unitPt (2 * θ)) |>.re

def evenSine (n t u : ℕ) (θ : ℝ) : ℝ :=
  (evenRemainder n t u).eval (unitPt (2 * θ)) |>.im

lemma evenT_eq_pow_mul (t : ℕ) : evenT t = 2 ^ t * 2 ^ 10 := by
  simp [evenT, pow_add]

lemma two_mul_evenT (t : ℕ) : 2 * evenT t = 2 ^ (t + 11) := by
  simp [evenT, pow_succ']

lemma evenT_add_pow_le_two_mul_evenT (t : ℕ) :
    evenT t + 2 ^ t ≤ 2 * evenT t := by
  rw [evenT_eq_pow_mul]
  have hpos : 0 < 2 ^ t := by positivity
  nlinarith [show (2 ^ 10 : ℕ) = 1024 by norm_num]

lemma pow_le_evenT (t : ℕ) : 2 ^ t ≤ evenT t := by
  rw [evenT_eq_pow_mul]
  have hpos : 0 < 2 ^ t := by positivity
  nlinarith [show (2 ^ 10 : ℕ) = 1024 by norm_num]

lemma gammaNum_add_one (t : ℕ) :
    gammaNum t + 1 = 2 * evenT t + 2 ^ t := by
  have hp : 0 < 2 ^ (t + 11) := by positivity
  have hone : 1 ≤ 2 ^ (t + 11) := hp
  have hsum : 1 ≤ 2 ^ (t + 11) + 2 ^ t :=
    hone.trans (Nat.le_add_right _ _)
  rw [gammaNum, Nat.sub_add_cancel hsum, two_mul_evenT]

lemma EvenParams.gamma_le_one {n t : ℕ} {γ : ℝ}
    (h : EvenParams n t γ) : γ ≤ 1 := by
  calc
    γ ≤ 1 / (2 : ℝ) ^ 40 := h.gamma_le
    _ ≤ 1 := by norm_num

lemma EvenParams.num_le_n {n t : ℕ} {γ : ℝ}
    (h : EvenParams n t γ) : gammaNum t ≤ n := by
  have hnonneg : 0 ≤ (n : ℝ) := by positivity
  have hreal : (gammaNum t : ℝ) ≤ n := by
    rw [← h.equation]
    nlinarith [h.gamma_le_one]
  exact_mod_cast hreal

lemma EvenParams.pow_t_add_eleven_le_n {n t : ℕ} {γ : ℝ}
    (h : EvenParams n t γ) : 2 ^ (t + 11) ≤ n := by
  apply le_trans _ h.num_le_n
  rw [gammaNum]
  have hpos : 0 < 2 ^ t := by positivity
  omega

lemma EvenParams.five_le_n {n t : ℕ} {γ : ℝ}
    (h : EvenParams n t γ) : 5 ≤ n := by
  have hp := h.pow_t_add_eleven_le_n
  have hbase : 2 ^ 11 ≤ 2 ^ (t + 11) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  norm_num at hbase
  omega

lemma EvenParams.pow_t_add_five_le_n {n t : ℕ} {γ : ℝ}
    (h : EvenParams n t γ) : 2 ^ (t + 5) ≤ n :=
  (Nat.pow_le_pow_right (by norm_num) (by omega)).trans h.pow_t_add_eleven_le_n

lemma EvenParams.blks_fit {n t : ℕ} {γ : ℝ}
    (h : EvenParams n t γ) :
    2 * evenT t + 2 ^ t ≤ n + 1 := by
  rw [← gammaNum_add_one]
  exact Nat.add_le_add_right h.num_le_n 1

@[simp] lemma mem_evenCPrime (t k : ℕ) :
    k ∈ evenCPrime t ↔
      (∃ j < 2 ^ t, k = evenT t + j) ∨
      ∃ j < 2 ^ t, k = 2 * evenT t + j := by
  simp [evenCPrime, eq_comm]

@[simp] lemma mem_evenC (t k : ℕ) :
    k ∈ evenC t ↔ ∃ j ∈ evenCPrime t, k = 2 * j := by
  simp [evenC, eq_comm]

@[simp] lemma mem_evenSPrime (n t k : ℕ) :
    k ∈ evenSPrime n t ↔ 1 ≤ k ∧ k ≤ n ∧ k ∉ evenCPrime t := by
  simp [evenSPrime, and_assoc]

@[simp] lemma mem_evenS (n t k : ℕ) :
    k ∈ evenS n t ↔ ∃ j ∈ evenSPrime n t, k = 2 * j := by
  simp [evenS, eq_comm]

lemma evenCPrime_subset_range {n t : ℕ}
    (hblock : 2 * evenT t + 2 ^ t ≤ n + 1) :
    evenCPrime t ⊆ Finset.range (n + 1) := by
  intro k hk
  rw [mem_evenCPrime] at hk
  simp only [Finset.mem_range]
  rcases hk with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · have hsep := evenT_add_pow_le_two_mul_evenT t
    omega
  · omega

lemma evenC_disjoint_evenS (n t : ℕ) : Disjoint (evenC t) (evenS n t) := by
  rw [Finset.disjoint_left]
  intro k hkC hkS
  rw [mem_evenC] at hkC
  rw [mem_evenS] at hkS
  obtain ⟨a, ha, rfl⟩ := hkC
  obtain ⟨b, hb, hab⟩ := hkS
  have : a = b := by omega
  subst b
  exact (mem_evenSPrime n t a).mp hb |>.2.2 ha

lemma coeff_cosBlk_first (t j : ℕ) (hj : j < 2 ^ t) :
    (cosBlk t).coeff (evenT t + j) =
      (rudinShapiroP t).coeff j := by
  rw [cosBlk, coeff_add,
    coeff_X_pow_mul', coeff_X_pow_mul']
  have hnot : ¬2 * evenT t ≤ evenT t + j := by
    have hsep := evenT_add_pow_le_two_mul_evenT t
    omega
  rw [if_pos (Nat.le_add_right _ _), if_neg hnot]
  simp

lemma coeff_cosBlk_second (t j : ℕ) (hj : j < 2 ^ t) :
    (cosBlk t).coeff (2 * evenT t + j) =
      (rudinShapiroQ t).coeff j := by
  rw [cosBlk, coeff_add,
    coeff_X_pow_mul', coeff_X_pow_mul']
  have hfirst : evenT t ≤ 2 * evenT t + j := by omega
  rw [if_pos hfirst, if_pos (Nat.le_add_right _ _)]
  have hsub : 2 * evenT t + j - evenT t = evenT t + j := by omega
  rw [hsub, coeff_rsP_eq_zero]
  · simp
  · exact (pow_le_evenT t).trans (Nat.le_add_right _ _)

lemma coeff_cosBlk_eq_zero_of_outside (t k : ℕ)
    (hk : k ∉ evenCPrime t) :
    (cosBlk t).coeff k = 0 := by
  rw [cosBlk, coeff_add,
    coeff_X_pow_mul', coeff_X_pow_mul']
  by_cases hT : evenT t ≤ k
  · rw [if_pos hT]
    by_cases h2T : 2 * evenT t ≤ k
    · rw [if_pos h2T]
      have hq : 2 ^ t ≤ k - 2 * evenT t := by
        by_contra hq
        have hq' : k - 2 * evenT t < 2 ^ t := Nat.lt_of_not_ge hq
        apply hk
        rw [mem_evenCPrime]
        right
        exact ⟨k - 2 * evenT t, hq', (Nat.add_sub_of_le h2T).symm⟩
      have hp : 2 ^ t ≤ k - evenT t := by omega
      rw [coeff_rsP_eq_zero hp, coeff_rsQ_eq_zero hq,
        zero_add]
    · rw [if_neg h2T, add_zero]
      apply coeff_rsP_eq_zero
      by_contra hp
      have hp' : k - evenT t < 2 ^ t := Nat.lt_of_not_ge hp
      apply hk
      rw [mem_evenCPrime]
      left
      exact ⟨k - evenT t, hp', (Nat.add_sub_of_le hT).symm⟩
  · rw [if_neg hT]
    have h2T : ¬2 * evenT t ≤ k := by omega
    rw [if_neg h2T, zero_add]

theorem support_cosBlk (t : ℕ) :
    (cosBlk t).support = evenCPrime t := by
  ext k
  simp only [mem_support_iff, ne_eq, mem_evenCPrime]
  constructor
  · intro hk
    by_contra hout
    apply hk
    apply coeff_cosBlk_eq_zero_of_outside t k
    rwa [mem_evenCPrime]
  · intro hk
    rcases hk with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · rw [coeff_cosBlk_first t j hj]
      rcases coeff_rsP_eq_one_or_neg_one hj with h | h <;>
        rw [h] <;> norm_num
    · rw [coeff_cosBlk_second t j hj]
      rcases coeff_rsQ_eq_one_or_neg_one hj with h | h <;>
        rw [h] <;> norm_num

lemma coeff_deletedEvenBlk_first (t j : ℕ) (hj : j < 2 ^ t) :
    (deletedEvenBlk t).coeff (evenT t + j) =
      (rudinShapiroP t).coeff j := by
  rw [deletedEvenBlk, coeff_add,
    coeff_X_pow_mul', coeff_X_pow_mul']
  have hnot : ¬2 * evenT t ≤ evenT t + j := by
    have hsep := evenT_add_pow_le_two_mul_evenT t
    omega
  rw [if_pos (Nat.le_add_right _ _), if_neg hnot]
  simp

lemma coeff_deletedEvenBlk_second (t j : ℕ) (hj : j < 2 ^ t) :
    (deletedEvenBlk t).coeff (2 * evenT t + j) =
      (rudinShapiroP t).coeff j := by
  rw [deletedEvenBlk, coeff_add,
    coeff_X_pow_mul', coeff_X_pow_mul']
  have hfirst : evenT t ≤ 2 * evenT t + j := by omega
  rw [if_pos hfirst, if_pos (Nat.le_add_right _ _)]
  have hsub : 2 * evenT t + j - evenT t = evenT t + j := by omega
  rw [hsub, coeff_rsP_eq_zero]
  · simp
  · exact (pow_le_evenT t).trans (Nat.le_add_right _ _)

lemma coeff_deletedEvenBlk_eq_zero_of_outside (t k : ℕ)
    (hk : k ∉ evenCPrime t) :
    (deletedEvenBlk t).coeff k = 0 := by
  rw [deletedEvenBlk, coeff_add,
    coeff_X_pow_mul', coeff_X_pow_mul']
  by_cases hT : evenT t ≤ k
  · rw [if_pos hT]
    by_cases h2T : 2 * evenT t ≤ k
    · rw [if_pos h2T]
      have hsecond : 2 ^ t ≤ k - 2 * evenT t := by
        by_contra hsecond
        apply hk
        rw [mem_evenCPrime]
        right
        exact ⟨k - 2 * evenT t, Nat.lt_of_not_ge hsecond,
          (Nat.add_sub_of_le h2T).symm⟩
      have hfirst : 2 ^ t ≤ k - evenT t := by omega
      rw [coeff_rsP_eq_zero hfirst,
        coeff_rsP_eq_zero hsecond, zero_add]
    · rw [if_neg h2T, add_zero]
      apply coeff_rsP_eq_zero
      by_contra hfirst
      apply hk
      rw [mem_evenCPrime]
      left
      exact ⟨k - evenT t, Nat.lt_of_not_ge hfirst,
        (Nat.add_sub_of_le hT).symm⟩
  · rw [if_neg hT]
    have h2T : ¬2 * evenT t ≤ k := by omega
    rw [if_neg h2T, zero_add]

lemma coeff_rsP_stable {a b k : ℕ} (hab : a ≤ b) (hk : k < 2 ^ a) :
    (rudinShapiroP b).coeff k = (rudinShapiroP a).coeff k := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
      have hpow : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hab
      rw [coeff_rsP_succ_of_lt (hk.trans_le hpow), ih]

lemma coeff_rsQ_add_ten (t j : ℕ) (hj : j < 2 ^ t) :
    (rudinShapiroQ (t + 10)).coeff j = (rudinShapiroP t).coeff j := by
  have hpow : 2 ^ t ≤ 2 ^ (t + 9) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [show t + 10 = (t + 9) + 1 by omega,
    coeff_rsQ_succ_of_lt (hj.trans_le hpow)]
  exact coeff_rsP_stable (by omega) hj

lemma coeff_rsQ_add_eleven (t j : ℕ) (hj : j < 2 ^ t) :
    (rudinShapiroQ (t + 11)).coeff j = (rudinShapiroP t).coeff j := by
  have hpow : 2 ^ t ≤ 2 ^ (t + 10) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [show t + 11 = (t + 10) + 1 by omega,
    coeff_rsQ_succ_of_lt (hj.trans_le hpow)]
  exact coeff_rsP_stable (by omega) hj

lemma coeff_rsP_late_first_blk {t u j : ℕ}
    (hu : t + 12 ≤ u) (hj : j < 2 ^ t) :
    (rudinShapiroP u).coeff (evenT t + j) =
      (rudinShapiroP t).coeff j := by
  have hindex : evenT t + j < 2 ^ (t + 11) := by
    rw [← two_mul_evenT]
    have hsep := evenT_add_pow_le_two_mul_evenT t
    omega
  calc
    (rudinShapiroP u).coeff (evenT t + j) =
        (rudinShapiroP (t + 11)).coeff (evenT t + j) :=
      coeff_rsP_stable (by omega) hindex
    _ = (rudinShapiroQ (t + 10)).coeff j := by
      simpa [evenT] using coeff_rsP_succ_add (t + 10) j
    _ = (rudinShapiroP t).coeff j := coeff_rsQ_add_ten t j hj

lemma coeff_rsP_late_second_blk {t u j : ℕ}
    (hu : t + 12 ≤ u) (hj : j < 2 ^ t) :
    (rudinShapiroP u).coeff (2 * evenT t + j) =
      (rudinShapiroP t).coeff j := by
  have hindex : 2 * evenT t + j < 2 ^ (t + 12) := by
    have hsmall := pow_le_evenT t
    rw [show 2 ^ (t + 12) = 2 * evenT t + 2 * evenT t by
      simp [evenT, pow_add]
      ring]
    omega
  calc
    (rudinShapiroP u).coeff (2 * evenT t + j) =
        (rudinShapiroP (t + 12)).coeff (2 * evenT t + j) :=
      coeff_rsP_stable hu hindex
    _ = (rudinShapiroQ (t + 11)).coeff j := by
      simpa [two_mul_evenT] using coeff_rsP_succ_add (t + 11) j
    _ = (rudinShapiroP t).coeff j := coeff_rsQ_add_eleven t j hj

lemma coeff_rsP_late_eq_deleted {t u k : ℕ}
    (hu : t + 12 ≤ u) (hk : k ∈ evenCPrime t) :
    (rudinShapiroP u).coeff k = (deletedEvenBlk t).coeff k := by
  rw [mem_evenCPrime] at hk
  rcases hk with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · rw [coeff_rsP_late_first_blk hu hj,
      coeff_deletedEvenBlk_first t j hj]
  · rw [coeff_rsP_late_second_blk hu hj,
      coeff_deletedEvenBlk_second t j hj]

lemma coeff_evenRemainder_of_mem_CPrime {n t u k : ℕ}
    (hu : t + 12 ≤ u) (hblock : 2 * evenT t + 2 ^ t ≤ n + 1)
    (hk : k ∈ evenCPrime t) :
    (evenRemainder n t u).coeff k = 0 := by
  have hkrange := evenCPrime_subset_range hblock hk
  simp only [Finset.mem_range] at hkrange
  rw [evenRemainder, coeff_sub,
    coeff_polyPrefix, if_pos hkrange,
    coeff_rsP_late_eq_deleted hu hk, sub_self]

lemma coeff_evenRemainder_sign_of_outside {n t u k : ℕ}
    (hprefix : n + 1 ≤ 2 ^ u) (hk : k < n + 1)
    (hkC : k ∉ evenCPrime t) :
    (evenRemainder n t u).coeff k = 1 ∨
      (evenRemainder n t u).coeff k = -1 := by
  rw [evenRemainder, coeff_sub,
    coeff_polyPrefix, if_pos hk,
    coeff_deletedEvenBlk_eq_zero_of_outside t k hkC, sub_zero]
  exact coeff_rsP_eq_one_or_neg_one (hk.trans_le hprefix)

theorem coeff_evenRemainder_sign_of_mem_evenSPrime {n t u k : ℕ}
    (hprefix : n + 1 ≤ 2 ^ u) (hk : k ∈ evenSPrime n t) :
    (evenRemainder n t u).coeff k = 1 ∨
      (evenRemainder n t u).coeff k = -1 := by
  rw [mem_evenSPrime] at hk
  exact coeff_evenRemainder_sign_of_outside hprefix (by omega) hk.2.2

theorem coeff_evenRemainder_eq_zero_on_CPrime {n t u k : ℕ}
    (hu : t + 12 ≤ u) (hblock : 2 * evenT t + 2 ^ t ≤ n + 1)
    (hk : k ∈ evenCPrime t) :
    (evenRemainder n t u).coeff k = 0 :=
  coeff_evenRemainder_of_mem_CPrime hu hblock hk

theorem evenCos_eq (t : ℕ) (θ : ℝ) :
    evenCos t θ =
      ((unitPt (2 * θ)) ^ evenT t *
          (rudinShapiroP t).eval (unitPt (2 * θ)) +
        (unitPt (2 * θ)) ^ (2 * evenT t) *
          (rudinShapiroQ t).eval (unitPt (2 * θ))).re := by
  simp [evenCos, cosBlk]

theorem evenSine_eq (n t u : ℕ) (θ : ℝ) :
    evenSine n t u θ =
      ((polyPrefix (rudinShapiroP u) (n + 1)).eval
          (unitPt (2 * θ)) -
        (unitPt (2 * θ)) ^ evenT t *
          (rudinShapiroP t).eval (unitPt (2 * θ)) -
        (unitPt (2 * θ)) ^ (2 * evenT t) *
          (rudinShapiroP t).eval (unitPt (2 * θ))).im := by
  simp [evenSine, evenRemainder, deletedEvenBlk]
  ring

private lemma two_mul_sqrt_pow_le_sqrt_nat {n t : ℕ}
    (hscale : 2 ^ (t + 3) ≤ n) :
    2 * sqrt (2 ^ (t + 1) : ℝ) ≤ sqrt n := by
  have hcast : (2 ^ (t + 3) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hscale
  have hpow : (2 ^ (t + 3) : ℝ) = 4 * (2 ^ (t + 1) : ℝ) := by
    rw [show t + 3 = (t + 1) + 2 by omega, pow_add]
    ring
  have hA : 0 ≤ (2 ^ (t + 1) : ℝ) := by positivity
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hsA := sq_sqrt hA
  have hsn := sq_sqrt hn
  have hsAn := sqrt_nonneg (2 ^ (t + 1) : ℝ)
  have hsnn := sqrt_nonneg (n : ℝ)
  rw [hpow] at hcast
  nlinarith

theorem abs_evenCos_le_sqrt (n t : ℕ)
    (hscale : 2 ^ (t + 3) ≤ n) (θ : ℝ) :
    |evenCos t θ| ≤ sqrt n := by
  let z := unitPt (2 * θ)
  have hz : ‖z‖ = 1 := norm_unitPt _
  have hP := norm_eval_rsP_le t hz
  have hQ := norm_eval_rsQ_le t hz
  rw [evenCos_eq]
  change |(z ^ evenT t * (rudinShapiroP t).eval z +
      z ^ (2 * evenT t) * (rudinShapiroQ t).eval z).re| ≤ _
  calc
    |(z ^ evenT t * (rudinShapiroP t).eval z +
        z ^ (2 * evenT t) * (rudinShapiroQ t).eval z).re| ≤
        ‖z ^ evenT t * (rudinShapiroP t).eval z +
          z ^ (2 * evenT t) * (rudinShapiroQ t).eval z‖ :=
      abs_re_le_norm _
    _ ≤ ‖z ^ evenT t * (rudinShapiroP t).eval z‖ +
        ‖z ^ (2 * evenT t) * (rudinShapiroQ t).eval z‖ := norm_add_le _ _
    _ = ‖(rudinShapiroP t).eval z‖ + ‖(rudinShapiroQ t).eval z‖ := by
      simp [norm_mul, norm_pow, hz]
    _ ≤ 2 * sqrt (2 ^ (t + 1) : ℝ) := by linarith
    _ ≤ sqrt n := two_mul_sqrt_pow_le_sqrt_nat hscale

private lemma sqrt_succ_le_eleven_tenths_sqrt {n : ℕ} (hn : 5 ≤ n) :
    sqrt ((n + 1 : ℕ) : ℝ) ≤ (11 / 10 : ℝ) * sqrt n := by
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hn1 : 0 ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  have hs0 := sq_sqrt hn0
  have hs1 := sq_sqrt hn1
  have hs0n := sqrt_nonneg (n : ℝ)
  have hs1n := sqrt_nonneg ((n + 1 : ℕ) : ℝ)
  have hncast : (5 : ℝ) ≤ n := by exact_mod_cast hn
  norm_num only [Nat.cast_add, Nat.cast_one] at hs1
  by_contra hnot
  have hlt : ((11 / 10 : ℝ) * sqrt n) ^ 2 <
      sqrt ((n + 1 : ℕ) : ℝ) ^ 2 :=
    (sq_lt_sq₀ (by positivity) hs1n).2 (lt_of_not_ge hnot)
  norm_num only [Nat.cast_add, Nat.cast_one] at hlt
  have hlt' : (121 / 100 : ℝ) * n < n + 1 := by
    nlinarith [hlt, hs0, hs1]
  nlinarith

private lemma two_mul_sqrt_pow_le_half_sqrt_nat {n t : ℕ}
    (hscale : 2 ^ (t + 5) ≤ n) :
    2 * sqrt (2 ^ (t + 1) : ℝ) ≤ (1 / 2 : ℝ) * sqrt n := by
  have hcast : (2 ^ (t + 5) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hscale
  have hpow : (2 ^ (t + 5) : ℝ) = 16 * (2 ^ (t + 1) : ℝ) := by
    rw [show t + 5 = (t + 1) + 4 by omega, pow_add]
    ring
  have hA : 0 ≤ (2 ^ (t + 1) : ℝ) := by positivity
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hsA := sq_sqrt hA
  have hsn := sq_sqrt hn
  have hsAn := sqrt_nonneg (2 ^ (t + 1) : ℝ)
  have hsnn := sqrt_nonneg (n : ℝ)
  rw [hpow] at hcast
  nlinarith

theorem abs_evenSine_le_six_sqrt (n t u : ℕ)
    (hprefix : n + 1 ≤ 2 ^ u) (hn : 5 ≤ n)
    (hscale : 2 ^ (t + 5) ≤ n) (θ : ℝ) :
    |evenSine n t u θ| ≤ 6 * sqrt n := by
  let z := unitPt (2 * θ)
  have hz : ‖z‖ = 1 := norm_unitPt _
  have hpref := norm_eval_polyPrefix_rsP_le u (n + 1) hprefix hz
  have hP := norm_eval_rsP_le t hz
  rw [evenSine_eq]
  change |((polyPrefix (rudinShapiroP u) (n + 1)).eval z -
      z ^ evenT t * (rudinShapiroP t).eval z -
      z ^ (2 * evenT t) * (rudinShapiroP t).eval z).im| ≤ _
  calc
    |((polyPrefix (rudinShapiroP u) (n + 1)).eval z -
        z ^ evenT t * (rudinShapiroP t).eval z -
        z ^ (2 * evenT t) * (rudinShapiroP t).eval z).im| ≤
        ‖(polyPrefix (rudinShapiroP u) (n + 1)).eval z -
          z ^ evenT t * (rudinShapiroP t).eval z -
          z ^ (2 * evenT t) * (rudinShapiroP t).eval z‖ :=
      abs_im_le_norm _
    _ ≤ ‖(polyPrefix (rudinShapiroP u) (n + 1)).eval z‖ +
          ‖z ^ evenT t * (rudinShapiroP t).eval z‖ +
          ‖z ^ (2 * evenT t) * (rudinShapiroP t).eval z‖ := by
      calc
        _ ≤ ‖(polyPrefix (rudinShapiroP u) (n + 1)).eval z -
              z ^ evenT t * (rudinShapiroP t).eval z‖ +
              ‖z ^ (2 * evenT t) * (rudinShapiroP t).eval z‖ := norm_sub_le _ _
        _ ≤ _ := by
          gcongr
          exact norm_sub_le _ _
    _ = ‖(polyPrefix (rudinShapiroP u) (n + 1)).eval z‖ +
          2 * ‖(rudinShapiroP t).eval z‖ := by
      simp [norm_mul, norm_pow, hz]
      ring
    _ ≤ 5 * sqrt ((n + 1 : ℕ) : ℝ) +
          2 * sqrt (2 ^ (t + 1) : ℝ) := by
      exact add_le_add hpref (mul_le_mul_of_nonneg_left hP (by norm_num))
    _ ≤ 5 * ((11 / 10 : ℝ) * sqrt n) +
          (1 / 2 : ℝ) * sqrt n := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (sqrt_succ_le_eleven_tenths_sqrt hn) (by norm_num))
        (two_mul_sqrt_pow_le_half_sqrt_nat hscale)
    _ = 6 * sqrt n := by ring

theorem abs_evenCos_le_sqrt_of_params {n t : ℕ} {γ : ℝ}
    (h : EvenParams n t γ) (θ : ℝ) :
    |evenCos t θ| ≤ sqrt n := by
  apply abs_evenCos_le_sqrt n t
  exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans
    h.pow_t_add_five_le_n

theorem abs_evenSin_le_six_sqrt_of_params {n t u : ℕ} {γ : ℝ}
    (h : EvenParams n t γ) (hprefix : n + 1 ≤ 2 ^ u)
    (θ : ℝ) :
    |evenSine n t u θ| ≤ 6 * sqrt n :=
  abs_evenSine_le_six_sqrt n t u hprefix h.five_le_n
    h.pow_t_add_five_le_n θ

end

end

section

namespace Interp

open scoped BigOperators

theorem exists_iteratedDeriv_eq_zero_of_strictMono :
    ∀ (k : ℕ) (g : ℝ → ℝ) (x : Fin (k + 1) → ℝ),
      ContDiff ℝ k g → StrictMono x → (∀ i, g (x i) = 0) →
      ∃ z ∈ Set.Icc (x 0) (x (Fin.last k)), iteratedDeriv k g z = 0 := by
  intro k
  induction k with
  | zero =>
      intro g x _hg _hx hzero
      refine ⟨x 0, ⟨le_rfl, ?_⟩, ?_⟩
      · simp
      · simpa using hzero 0
  | succ k ih =>
      intro g x hg hx hzero
      have hrolle (i : Fin (k + 1)) :
          ∃ c ∈ Set.Ioo (x i.castSucc) (x i.succ), deriv g c = 0 := by
        apply exists_deriv_eq_zero
        · exact hx Fin.castSucc_lt_succ
        · exact hg.continuous.continuousOn
        · rw [hzero i.castSucc, hzero i.succ]
      let c : Fin (k + 1) → ℝ := fun i ↦ Classical.choose (hrolle i)
      have hc_mem (i : Fin (k + 1)) :
          c i ∈ Set.Ioo (x i.castSucc) (x i.succ) :=
        (Classical.choose_spec (hrolle i)).1
      have hc_zero (i : Fin (k + 1)) : deriv g (c i) = 0 :=
        (Classical.choose_spec (hrolle i)).2
      have hc_mono : StrictMono c := by
        intro i j hij
        have hij' : i.succ ≤ j.castSucc := by
          apply Fin.mk_le_mk.mpr
          omega
        exact (hc_mem i).2.trans ((hx.monotone hij').trans_lt (hc_mem j).1)
      have hderiv : ContDiff ℝ k (deriv g) := hg.deriv'
      obtain ⟨z, hz, hz0⟩ := ih (deriv g) c hderiv hc_mono hc_zero
      refine ⟨z, ⟨?_, ?_⟩, ?_⟩
      · exact (hc_mem 0).1.le.trans hz.1
      · exact hz.2.trans (hc_mem (Fin.last k)).2.le
      · simpa only [iteratedDeriv_succ'] using hz0

noncomputable def derivWt (k : ℕ) (y : Fin (k + 1) → ℝ)
    (j : Fin (k + 1)) : ℝ :=
  (k.factorial : ℝ) /
    ∏ i ∈ (Finset.univ.erase j), (y j - y i)

theorem eval_iterate_deriv_interpolate_top (k : ℕ)
    (y : Fin (k + 1) → ℝ) (v : Fin (k + 1) → ℝ) (hy : Function.Injective y)
    (x : ℝ) :
    ((derivative^[k])
      (Lagrange.interpolate Finset.univ y v)).eval x =
      ∑ i, derivWt k y i * v i := by
  rw [Lagrange.iterate_derivative_interpolate v hy.injOn (by simp)]
  simp [derivWt, Finset.mul_sum, div_eq_mul_inv, mul_comm]
  simp [eval_finsetSum, mul_left_comm]

theorem iteratedDeriv_poly_eval (k : ℕ) (P : Polynomial ℝ) (x : ℝ) :
    iteratedDeriv k (fun t ↦ P.eval t) x =
      ((derivative^[k]) P).eval x := by
  induction k generalizing P with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ']
      have hfun : deriv (fun t ↦ P.eval t) = fun t ↦ P.derivative.eval t := by
        funext t
        exact P.deriv
      rw [hfun, ih]
      rw [Function.iterate_succ_apply']
      exact congrArg (Polynomial.eval x)
        ((Function.Commute.self_iterate
          (derivative : Polynomial ℝ → Polynomial ℝ) k) P).symm

theorem howell_deriv_approx (k : ℕ) (f : ℝ → ℝ)
    (y : Fin (k + 1) → ℝ) (x Δ M : ℝ)
    (hf : ContDiff ℝ (k + 1) f) (hy : StrictMono y)
    (_hDelta : 0 ≤ Δ) (hM : 0 ≤ M)
    (hyx : ∀ i, |y i - x| ≤ Δ)
    (hderiv : ∀ t, |iteratedDeriv (k + 1) f t| ≤ M) :
    |iteratedDeriv k f x -
      ∑ i, derivWt k y i * f (y i)| ≤ Δ * M := by
  let P : Polynomial ℝ := Lagrange.interpolate Finset.univ y (fun i ↦ f (y i))
  let g : ℝ → ℝ := fun t ↦ f t - P.eval t
  have hP : ContDiff ℝ (k + 1) (fun t ↦ P.eval t) := by
    induction P using Polynomial.induction_on' with
    | add p q hp hq => simpa only [eval_add] using hp.add hq
    | monomial n a =>
        simp only [eval_monomial]
        fun_prop
  have hg : ContDiff ℝ k g := by
    apply ContDiff.sub (hf.of_le (by norm_num)) (hP.of_le (by norm_num))
  have hzero : ∀ i, g (y i) = 0 := by
    intro i
    have hPi : P.eval (y i) = f (y i) := by
      dsimp only [P]
      exact Lagrange.eval_interpolate_at_node _ hy.injective.injOn (Finset.mem_univ i)
    dsimp only [g]
    rw [hPi, sub_self]
  obtain ⟨z, hz, hz0⟩ :=
    exists_iteratedDeriv_eq_zero_of_strictMono k g y hg hy hzero
  have hPAt : ContDiffAt ℝ k (fun t ↦ P.eval t) z := (hP.of_le (by norm_num)).contDiffAt
  have hfAt : ContDiffAt ℝ k f z := (hf.of_le (by norm_num)).contDiffAt
  have hzEq : iteratedDeriv k f z =
      ∑ i, derivWt k y i * f (y i) := by
    change iteratedDeriv k (f - fun t ↦ P.eval t) z = 0 at hz0
    rw [iteratedDeriv_sub hfAt hPAt, iteratedDeriv_poly_eval,
      eval_iterate_deriv_interpolate_top k y (fun i ↦ f (y i)) hy.injective z] at hz0
    linarith
  have hzDist : |z - x| ≤ Δ := by
    have hleft := (abs_le.mp (hyx (0 : Fin (k + 1)))).1
    have hright := (abs_le.mp (hyx (Fin.last k))).2
    rw [abs_le]
    constructor <;> linarith [hz.1, hz.2]
  have hdiff : Differentiable ℝ (iteratedDeriv k f) :=
    hf.differentiable_iteratedDeriv k (by exact_mod_cast Nat.lt_succ_self k)
  have hmean :
      |iteratedDeriv k f x - iteratedDeriv k f z| ≤ M * |x - z| := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (s := Set.univ) (f := iteratedDeriv k f) (x := z) (y := x)
      (fun t _ ↦ hdiff.differentiableAt)
      (fun t _ ↦ by
        rw [← iteratedDeriv_succ]
        simpa only [norm_eq_abs] using hderiv t)
      convex_univ (Set.mem_univ z) (Set.mem_univ x)
    simpa only [norm_eq_abs] using h
  rw [← hzEq]
  calc
    |iteratedDeriv k f x - iteratedDeriv k f z| ≤ M * |x - z| := hmean
    _ = M * |z - x| := by rw [abs_sub_comm]
    _ ≤ M * Δ := mul_le_mul_of_nonneg_left hzDist hM
    _ = Δ * M := mul_comm _ _

theorem pow_le_abs_prod_of_sep (k : ℕ) (y : Fin (k + 1) → ℝ) (eta : ℝ)
    (heta : 0 ≤ eta)
    (hsep : ∀ i j, i ≠ j → eta ≤ |y i - y j|)
    (j : Fin (k + 1)) :
    eta ^ k ≤ |∏ i ∈ (Finset.univ.erase j), (y j - y i)| := by
  classical
  rw [Finset.abs_prod]
  have hcard : (Finset.univ.erase j).card = k := by simp
  calc
    eta ^ k = eta ^ (Finset.univ.erase j).card := congrArg (eta ^ ·) hcard.symm
    _ = ∏ _i ∈ (Finset.univ.erase j), eta := by simp
    _ ≤ ∏ i ∈ (Finset.univ.erase j), |y j - y i| := by
      apply Finset.prod_le_prod (fun _i _hi ↦ heta)
      intro i hi
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      simpa only [abs_sub_comm] using hsep i j hij

theorem abs_derivWt_le (k : ℕ) (y : Fin (k + 1) → ℝ) (eta : ℝ)
    (heta : 0 < eta)
    (hsep : ∀ i j, i ≠ j → eta ≤ |y i - y j|)
    (j : Fin (k + 1)) :
    |derivWt k y j| ≤ (k.factorial : ℝ) / eta ^ k := by
  rw [derivWt, abs_div, abs_of_nonneg (Nat.cast_nonneg _)]
  have hprod := pow_le_abs_prod_of_sep k y eta heta.le hsep j
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hprod

theorem abs_sum_le_card_mul {n : ℕ} (u : Fin n → ℝ) (A : ℝ)
    (hA : ∀ i, |u i| ≤ A) :
    |∑ i, u i| ≤ n * A := by
  calc
    |∑ i, u i| ≤ ∑ i, |u i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, A := sum_le_sum fun i _ ↦ hA i
    _ = n * A := by simp [nsmul_eq_mul]

theorem abs_lagrange_sum_le (k : ℕ) (y : Fin (k + 1) → ℝ) (eta ε : ℝ)
    (heta : 0 < eta) (_hepsilon : 0 ≤ ε)
    (hsep : ∀ i j, i ≠ j → eta ≤ |y i - y j|)
    (v : Fin (k + 1) → ℝ) (hv : ∀ i, |v i| ≤ ε) :
    |∑ i, derivWt k y i * v i| ≤
      (k + 1) * ((k.factorial : ℝ) / eta ^ k * ε) := by
  have h := abs_sum_le_card_mul
    (fun i ↦ derivWt k y i * v i)
    ((k.factorial : ℝ) / eta ^ k * ε) (fun i ↦ by
      rw [abs_mul]
      exact mul_le_mul
        (abs_derivWt_le k y eta heta hsep i) (hv i)
        (abs_nonneg _) (by positivity))
  simpa [Nat.cast_add, Nat.cast_one] using h

theorem howell_bound_of_approx (k : ℕ) (y : Fin (k + 1) → ℝ)
    (eta ε remainder d : ℝ)
    (heta : 0 < eta) (hε : 0 ≤ ε) (_hremainder : 0 ≤ remainder)
    (hsep : ∀ i j, i ≠ j → eta ≤ |y i - y j|)
    (v : Fin (k + 1) → ℝ) (hv : ∀ i, |v i| ≤ ε)
    (happrox : |d - ∑ i, derivWt k y i * v i| ≤ remainder) :
    |d| ≤ remainder + (k + 1) * ((k.factorial : ℝ) / eta ^ k * ε) := by
  have hsum := abs_lagrange_sum_le k y eta ε heta hε hsep v hv
  calc
    |d| = |(d - ∑ i, derivWt k y i * v i) +
        ∑ i, derivWt k y i * v i| := by ring_nf
    _ ≤ |d - ∑ i, derivWt k y i * v i| +
        |∑ i, derivWt k y i * v i| := abs_add_le _ _
    _ ≤ remainder + (k + 1) * ((k.factorial : ℝ) / eta ^ k * ε) :=
      add_le_add happrox hsum

theorem howell_lt_quarter (k : ℕ) (hk₁ : 1 ≤ k) (hk₃ : k ≤ 3)
    (y : Fin (k + 1) → ℝ) (eta d : ℝ)
    (heta : 0 < eta) (hetaSmall : eta < (1 : ℝ) / 2048)
    (hsep : ∀ i j, i ≠ j → eta ≤ |y i - y j|)
    (v : Fin (k + 1) → ℝ) (hv : ∀ i, |v i| ≤ eta ^ 3 / 128)
    (happrox : |d - ∑ i, derivWt k y i * v i| ≤ 126 * eta) :
    |d| < 1 / 4 := by
  have hetaPow : 0 ≤ eta ^ 3 / 128 := by positivity
  have hbound := howell_bound_of_approx k y eta (eta ^ 3 / 128)
    (126 * eta) d heta hetaPow (by positivity) hsep v hv happrox
  have hetaOne : eta < 1 := by
    calc
      eta < (1 : ℝ) / 2048 := hetaSmall
      _ < 1 := by norm_num
  have hetaLeOne : eta ≤ 1 := hetaOne.le
  have hetaSqLeOne : eta ^ 2 ≤ 1 := by nlinarith [sq_nonneg eta]
  have hinterp :
      (k + 1 : ℝ) * ((k.factorial : ℝ) / eta ^ k * (eta ^ 3 / 128)) ≤ 3 / 16 := by
    interval_cases k <;> norm_num at hk₁ hk₃ ⊢
    · field_simp [ne_of_gt heta]
      nlinarith [sq_nonneg eta]
    · field_simp [ne_of_gt heta]
      nlinarith
    · field_simp [ne_of_gt heta]
      norm_num
  have hrem : 126 * eta < 1 / 16 := by
    norm_num at hetaSmall ⊢
    nlinarith
  nlinarith

theorem howell_lt_quarter_of_nodes (k : ℕ) (hk₁ : 1 ≤ k) (hk₃ : k ≤ 3)
    (f : ℝ → ℝ) (y : Fin (k + 1) → ℝ) (x eta : ℝ)
    (hf : ContDiff ℝ (k + 1) f) (hy : StrictMono y)
    (heta : 0 < eta) (hetaSmall : eta < (1 : ℝ) / 2048)
    (hsep : ∀ i j, i ≠ j → eta ≤ |y i - y j|)
    (hyx : ∀ i, |y i - x| ≤ 7 * eta)
    (hvalue : ∀ i, |f (y i)| ≤ eta ^ 3 / 128)
    (hderiv : ∀ t, |iteratedDeriv (k + 1) f t| ≤ 18) :
    |iteratedDeriv k f x| < 1 / 4 := by
  have happrox' := howell_deriv_approx k f y x (7 * eta) 18 hf hy
    (by positivity) (by norm_num) hyx hderiv
  have happrox :
      |iteratedDeriv k f x -
        ∑ i, derivWt k y i * f (y i)| ≤ 126 * eta := by
    convert happrox' using 1
    ring
  exact howell_lt_quarter k hk₁ hk₃ y eta (iteratedDeriv k f x) heta hetaSmall
    hsep (fun i ↦ f (y i)) hvalue happrox

end Interp

end

section

namespace Ivls

open Set

noncomputable def gridPt (n k : ℕ) : ℝ := (k : ℝ) * π / n

noncomputable def gridCell (n k : ℕ) : Set ℝ :=
  Icc (gridPt n k) (gridPt n (k + 1))

def idxBlk (start length : ℕ) : Finset ℕ :=
  (Finset.range length).image (start + ·)

@[simp] theorem mem_idxBlk {start length i : ℕ} :
    i ∈ idxBlk start length ↔ start ≤ i ∧ i < start + length := by
  constructor
  · simp only [idxBlk, Finset.mem_image, Finset.mem_range]
    rintro ⟨j, hj, rfl⟩
    omega
  · rintro ⟨hsi, hi⟩
    simp only [idxBlk, Finset.mem_image, Finset.mem_range]
    exact ⟨i - start, by omega, by omega⟩

@[simp] theorem card_idxBlk (start length : ℕ) :
    (idxBlk start length).card = length := by
  rw [idxBlk, Finset.card_image_of_injective]
  · simp
  · exact fun _ _ h ↦ Nat.add_left_cancel h

theorem gridPt_zero (n : ℕ) : gridPt n 0 = 0 := by
  simp [gridPt]

theorem gridPt_add (n k l : ℕ) :
    gridPt n (k + l) = gridPt n k + gridPt n l := by
  simp only [gridPt, Nat.cast_add]
  ring

theorem gridPt_succ (n k : ℕ) :
    gridPt n (k + 1) = gridPt n k + π / n := by
  rw [gridPt_add]
  simp [gridPt]

theorem gridPt_strictMono {n : ℕ} (hn : 0 < n) :
    StrictMono (gridPt n) := by
  intro i j hij
  simp only [gridPt]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpi : 0 < π / (n : ℝ) := div_pos pi_pos hn'
  simpa [mul_div_assoc] using (mul_lt_mul_of_pos_right (by exact_mod_cast hij) hpi)

theorem gridPt_mono {n : ℕ} (hn : 0 < n) :
    Monotone (gridPt n) := (gridPt_strictMono hn).monotone

def negIvl (I : ℝ × ℝ) : ℝ × ℝ := (-I.2, -I.1)

noncomputable def piMinusIvl (I : ℝ × ℝ) : ℝ × ℝ :=
  (π - I.2, π - I.1)

noncomputable def piPlusIvl (I : ℝ × ℝ) : ℝ × ℝ :=
  (π + I.1, π + I.2)

@[simp] theorem mem_Icc_negIvl {a b x : ℝ} :
    x ∈ Icc a b ↔ -x ∈ Icc (negIvl (a, b)).1 (negIvl (a, b)).2 := by
  change (a ≤ x ∧ x ≤ b) ↔ (-b ≤ -x ∧ -x ≤ -a)
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

@[simp] theorem mem_Icc_piMinusIvl {a b x : ℝ} :
    x ∈ Icc a b ↔
      π - x ∈ Icc (piMinusIvl (a, b)).1 (piMinusIvl (a, b)).2 := by
  change (a ≤ x ∧ x ≤ b) ↔
    (π - b ≤ π - x ∧ π - x ≤ π - a)
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

@[simp] theorem mem_Icc_piPlusIvl {a b x : ℝ} :
    x ∈ Icc a b ↔
      π + x ∈ Icc (piPlusIvl (a, b)).1 (piPlusIvl (a, b)).2 := by
  simp [piPlusIvl]

def changeIdxs (N : ℕ) (bad : ℕ → Prop) [DecidablePred bad] : Finset ℕ :=
  (Finset.range N).filter fun i ↦ i + 1 < N ∧ ¬ (bad i ↔ bad (i + 1))

def runStarts (N : ℕ) (bad : ℕ → Prop) [DecidablePred bad] : Finset ℕ :=
  (Finset.range N).filter fun i ↦ bad i ∧ (i = 0 ∨ ¬ bad (i - 1))

@[simp] theorem mem_changeIdxs {N i : ℕ} {bad : ℕ → Prop}
    [DecidablePred bad] :
    i ∈ changeIdxs N bad ↔ i + 1 < N ∧ ¬ (bad i ↔ bad (i + 1)) := by
  simp [changeIdxs]
  omega

@[simp] theorem mem_runStarts {N i : ℕ} {bad : ℕ → Prop}
    [DecidablePred bad] :
    i ∈ runStarts N bad ↔
      i < N ∧ bad i ∧ (i = 0 ∨ ¬ bad (i - 1)) := by
  simp [runStarts]

def IsMaximalBadRun (N : ℕ) (bad : ℕ → Prop) (a b : ℕ) : Prop :=
  a ≤ b ∧ b < N ∧
    (∀ i ∈ Finset.range N, a ≤ i → i ≤ b → bad i) ∧
    (a = 0 ∨ ¬ bad (a - 1)) ∧
    (b + 1 = N ∨ ¬ bad (b + 1))

instance instDecidableIsMaximalBadRun (N : ℕ) (bad : ℕ → Prop)
    [DecidablePred bad] (a b : ℕ) : Decidable (IsMaximalBadRun N bad a b) := by
  unfold IsMaximalBadRun
  infer_instance

def maximalBadRuns (N : ℕ) (bad : ℕ → Prop) [DecidablePred bad] :
    Finset (ℕ × ℕ) :=
  ((Finset.range N).product (Finset.range N)).filter fun I ↦
    IsMaximalBadRun N bad I.1 I.2

theorem IsMaximalBadRun.eq_of_start_eq {N a b c d : ℕ} {bad : ℕ → Prop}
    (h₁ : IsMaximalBadRun N bad a b) (h₂ : IsMaximalBadRun N bad c d)
    (hac : a = c) : (a, b) = (c, d) := by
  subst c
  congr 1
  apply le_antisymm
  · by_contra hnot
    have hdb : d < b := Nat.lt_of_not_ge hnot
    have hbad : bad (d + 1) :=
      h₁.2.2.1 (d + 1) (Finset.mem_range.2 (lt_of_le_of_lt hdb h₁.2.1))
        (Nat.le_succ_of_le h₂.1) hdb
    rcases h₂.2.2.2.2 with heq | hnbad
    · have hNb : N ≤ b := by omega
      exact (Nat.not_le_of_gt h₁.2.1) hNb
    · exact hnbad hbad
  · by_contra hnot
    have hbd : b < d := Nat.lt_of_not_ge hnot
    have hbad : bad (b + 1) :=
      h₂.2.2.1 (b + 1) (Finset.mem_range.2 (lt_of_le_of_lt hbd h₂.2.1))
        (Nat.le_succ_of_le h₁.1) hbd
    rcases h₁.2.2.2.2 with heq | hnbad
    · have hNd : N ≤ d := by omega
      exact (Nat.not_le_of_gt h₂.2.1) hNd
    · exact hnbad hbad

@[simp] theorem mem_maximalBadRuns {N a b : ℕ} {bad : ℕ → Prop}
    [DecidablePred bad] :
    (a, b) ∈ maximalBadRuns N bad ↔ IsMaximalBadRun N bad a b := by
  constructor
  · intro h
    exact (mem_filter.mp h).2
  · intro h
    apply mem_filter.mpr
    exact ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (h.1.trans_lt h.2.1), Finset.mem_range.mpr h.2.1⟩, h⟩

theorem exists_runStart_le {N i : ℕ} {bad : ℕ → Prop} [DecidablePred bad]
    (hiN : i < N) (hi : bad i) :
    ∃ a, a ≤ i ∧ a ∈ runStarts N bad ∧
      ∀ j, a ≤ j → j ≤ i → bad j := by
  induction i with
  | zero =>
      refine ⟨0, le_rfl, ?_, ?_⟩
      · rw [mem_runStarts]
        exact ⟨hiN, hi, Or.inl rfl⟩
      · intro j hj₀ hj₁
        have : j = 0 := by omega
        simpa [this] using hi
  | succ i ih =>
      by_cases hprev : bad i
      · obtain ⟨a, hai, hastart, harun⟩ := ih (by omega) hprev
        refine ⟨a, by omega, hastart, ?_⟩
        intro j haj hji
        by_cases hj : j = i + 1
        · simpa [hj] using hi
        · exact harun j haj (by omega)
      · refine ⟨i + 1, le_rfl, ?_, ?_⟩
        · rw [mem_runStarts]
          refine ⟨hiN, hi, Or.inr ?_⟩
          change ¬ bad i
          exact hprev
        · intro j hj₀ hj₁
          have : j = i + 1 := by omega
          simpa [this] using hi

theorem exists_maximalBadRun_containing {N i : ℕ} {bad : ℕ → Prop}
    [DecidablePred bad] (hiN : i < N) (hi : bad i) :
    ∃ a b, IsMaximalBadRun N bad a b ∧ a ≤ i ∧ i ≤ b := by
  obtain ⟨a, hai, hastart, harun⟩ := exists_runStart_le hiN hi
  let P : ℕ → Prop := fun b ↦
    b < N ∧ ∀ j ∈ Finset.range N, a ≤ j → j ≤ b → bad j
  let _ : DecidablePred P := fun _ ↦ inferInstance
  have hi_bound : i ≤ N - 1 := by omega
  have hPi : P i := by
    refine ⟨hiN, ?_⟩
    intro j hjN haj hji
    exact harun j haj hji
  let b := Nat.findGreatest P (N - 1)
  have hib : i ≤ b := by
    exact Nat.le_findGreatest hi_bound hPi
  have hPb : P b := by
    exact Nat.findGreatest_spec hi_bound hPi
  have hright : b + 1 = N ∨ ¬ bad (b + 1) := by
    by_cases heq : b + 1 = N
    · exact Or.inl heq
    · right
      intro hbad
      have hsuccN : b + 1 < N := by omega
      have hsuccBound : b + 1 ≤ N - 1 := by omega
      have hPsucc : P (b + 1) := by
        refine ⟨hsuccN, ?_⟩
        intro j hjN haj hjb
        by_cases hj : j = b + 1
        · simpa [hj] using hbad
        · exact hPb.2 j hjN haj (by omega)
      exact (Nat.findGreatest_is_greatest (P := P) (n := N - 1)
        (k := b + 1) (Nat.lt_succ_self b) hsuccBound) hPsucc
  refine ⟨a, b, ?_, hai, hib⟩
  refine ⟨hai.trans hib, hPb.1, hPb.2, ?_, hright⟩
  exact (mem_runStarts.mp hastart).2.2

theorem exists_mem_maximalBadRuns_containing {N i : ℕ} {bad : ℕ → Prop}
    [DecidablePred bad] (hiN : i < N) (hi : bad i) :
    ∃ I ∈ maximalBadRuns N bad, I.1 ≤ i ∧ i ≤ I.2 := by
  obtain ⟨a, b, hab, hai, hib⟩ := exists_maximalBadRun_containing hiN hi
  exact ⟨(a, b), mem_maximalBadRuns.mpr hab, hai, hib⟩

theorem exists_level_between {f : ℝ → ℝ} (hf : Continuous f)
    {x y level : ℝ} (hxy : x ≤ y)
    (hcross : (f x < level ∧ level ≤ f y) ∨
      (f y < level ∧ level ≤ f x)) :
    ∃ u ∈ Icc x y, f u = level := by
  rcases hcross with h | h
  · rcases intermediate_value_Icc hxy hf.continuousOn ⟨h.1.le, h.2⟩ with ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩
  · rcases intermediate_value_Icc' hxy hf.continuousOn ⟨h.1.le, h.2⟩ with ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩

theorem exists_abs_level_between {f : ℝ → ℝ} (hf : Continuous f)
    {x y level : ℝ} (hxy : x ≤ y)
    (hcross : (|f x| < level ∧ level ≤ |f y|) ∨
      (|f y| < level ∧ level ≤ |f x|)) :
    ∃ u ∈ Icc x y, |f u| = level :=
  exists_level_between hf.abs hxy hcross

end Ivls

end

open Ivls


section

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal

namespace GaussianWalk

noncomputable def radMeasure : Measure ℝ :=
  bernoulliMeasure 1 (-1) ⟨1 / 2, by norm_num⟩

noncomputable instance instIsProbabilityMeasureRademacher :
    IsProbabilityMeasure radMeasure := by
  unfold radMeasure
  infer_instance

theorem intg_id_radMeasure :
    ∫ x, x ∂radMeasure = 0 := by
  rw [radMeasure, integral_bernoulliMeasure]
  norm_num

theorem ae_mem_Icc_radMeasure :
    ∀ᵐ x ∂radMeasure, x ∈ Icc (-1 : ℝ) 1 := by
  rw [radMeasure, bernoulliMeasure_def]
  simp only [ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    exact (ae_dirac_iff measurableSet_Icc).2 (by norm_num)
  · apply Measure.ae_smul_measure
    exact (ae_dirac_iff measurableSet_Icc).2 (by norm_num)

theorem hasSubgaussianMGF_id_radMeasure :
    HasSubgaussianMGF id 1 radMeasure := by
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (μ := radMeasure) (X := id) measurable_id.aemeasurable
    ae_mem_Icc_radMeasure intg_id_radMeasure
  have hc : ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2) = (1 : ℝ≥0) := by
    norm_num
  rw [hc] at h
  exact h

theorem ae_abs_eq_one_radMeasure :
    ∀ᵐ x ∂radMeasure, |x| = 1 := by
  have hmeas : MeasurableSet {x : ℝ | |x| = 1} :=
    measurable_abs (measurableSet_singleton 1)
  rw [radMeasure, bernoulliMeasure_def]
  simp only [ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    exact (ae_dirac_iff hmeas).2 (by norm_num)
  · apply Measure.ae_smul_measure
    exact (ae_dirac_iff hmeas).2 (by norm_num)

noncomputable def radLaw (iota : Type*) [Fintype iota] :
    Measure (iota → ℝ) :=
  Measure.pi fun _ : iota ↦ radMeasure

noncomputable instance instIsProbabilityMeasureRademacherProduct
    (iota : Type*) [Fintype iota] :
    IsProbabilityMeasure (radLaw iota) := by
  unfold radLaw
  infer_instance

theorem iIndepFun_radLaw
    (iota : Type*) [Fintype iota] :
    iIndepFun (fun i : iota ↦ fun ω : iota → ℝ ↦ ω i)
      (radLaw iota) := by
  unfold radLaw
  exact iIndepFun_pi fun _ ↦ measurable_id.aemeasurable

theorem ae_forall_abs_eq_one_radLaw
    (iota : Type*) [Fintype iota] :
    ∀ᵐ ω ∂radLaw iota, ∀ i, |ω i| = 1 := by
  rw [ae_all_iff]
  intro i
  exact (measurePreserving_eval (μ := fun _ : iota ↦ radMeasure) i)
    |>.quasiMeasurePreserving.tendsto_ae ae_abs_eq_one_radMeasure

theorem hasSubgaussianMGF_radCoord
    (iota : Type*) [Fintype iota] (i : iota) :
    HasSubgaussianMGF (fun ω : iota → ℝ ↦ ω i) 1
      (radLaw iota) := by
  refine HasSubgaussianMGF.of_map (μ := radLaw iota) (X := id)
    (Y := fun ω : iota → ℝ ↦ ω i)
    (measurable_pi_apply i).aemeasurable ?_
  have hmap : (radLaw iota).map (fun ω : iota → ℝ ↦ ω i) =
      radMeasure := by
    unfold radLaw
    exact (measurePreserving_eval (μ := fun _ : iota ↦ radMeasure) i).map_eq
  rw [hmap]
  exact hasSubgaussianMGF_id_radMeasure

theorem iIndepFun_wtedRad
    (iota : Type*) [Fintype iota] (a : iota → ℝ) :
    iIndepFun (fun i : iota ↦ fun ω : iota → ℝ ↦ a i * ω i)
      (radLaw iota) := by
  have h := (iIndepFun_radLaw iota).comp
    (fun i x ↦ a i * x) (fun i ↦ measurable_const.mul measurable_id)
  simpa [Function.comp_def] using h

theorem hasSubgaussianMGF_wtedRadSum
    (iota : Type*) [Fintype iota] (a : iota → ℝ) :
    HasSubgaussianMGF
      (fun ω : iota → ℝ ↦ ∑ i, a i * ω i)
      (∑ i, ⟨a i ^ 2, sq_nonneg (a i)⟩)
      (radLaw iota) := by
  apply HasSubgaussianMGF.sum_of_iIndepFun
    (iIndepFun_wtedRad iota a) (s := Finset.univ)
  intro i hi
  have h := (hasSubgaussianMGF_radCoord iota i).const_mul (a i)
  have hc : (⟨a i ^ 2, sq_nonneg (a i)⟩ : ℝ≥0) * 1 =
      ⟨a i ^ 2, sq_nonneg (a i)⟩ := mul_one _
  exact hc ▸ h

def partialSum {Ω : Type*} (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, Y i ω

@[simp]
theorem partialSum_zero {Ω : Type*} (Y : ℕ → Ω → ℝ) :
    partialSum Y 0 = 0 := by
  funext ω
  simp [partialSum]

end GaussianWalk

end

open GaussianWalk


section

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal

namespace Martingale

structure HasConditionalGaussianMGF
    {Ω : Type*} (m : MeasurableSpace Ω)
    {mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    [StandardBorelSpace Ω]
    (X : Ω → ℝ) (variance : Ω → ℝ≥0)
    (mu : Measure Ω := by volume_tac) [IsFiniteMeasure mu] : Prop where
  integrable_exp_mul :
    ∀ t : ℝ, Integrable (fun ω ↦ exp (t * X ω)) mu
  mgf_eq :
    ∀ᵐ ω ∂(mu.trim hm), ∀ t : ℝ,
      mgf X (condExpKernel mu m ω) t =
        exp (variance ω * t ^ 2 / 2)

def partialSum {Ω : Type*} (increment : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, increment i ω

@[simp]
theorem partialSum_zero {Ω : Type*} (increment : ℕ → Ω → ℝ) :
    partialSum increment 0 = 0 := by
  funext ω
  simp [partialSum]

end Martingale

end

section

namespace ProjWalk

open scoped BigOperators

noncomputable section

variable {I K : Type*} [Fintype I]

abbrev WalkSp (I : Type*) [Fintype I] := EuclideanSpace ℝ I

def constrSpan (w : K → WalkSp I) : Submodule ℝ (WalkSp I) :=
  Submodule.span ℝ (Set.range w)

def incsubsp (w : K → WalkSp I) : Submodule ℝ (WalkSp I) :=
  (constrSpan w)ᗮ

theorem normal_mem_constrSpan (w : K → WalkSp I) (k : K) :
    w k ∈ constrSpan w :=
  Submodule.subset_span (Set.mem_range_self k)

theorem mem_incsubsp_iff (w : K → WalkSp I) (x : WalkSp I) :
    x ∈ incsubsp w ↔ ∀ k, inner ℝ (w k) x = 0 := by
  constructor
  · intro hx k
    exact (Submodule.mem_orthogonal (constrSpan w) x).1 hx
      (w k) (normal_mem_constrSpan w k)
  · intro hx
    rw [incsubsp, Submodule.mem_orthogonal]
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨k, rfl⟩ := hy
        exact hx k
    | zero => simp
    | add y z _ _ hy hz => rw [inner_add_left, hy, hz, add_zero]
    | smul a y _ hy => rw [inner_smul_left, hy, mul_zero]

variable [Fintype K]

theorem finrank_constrSpan_le_card (w : K → WalkSp I) :
    Module.finrank ℝ (constrSpan w) ≤ Fintype.card K :=
  finrank_range_le_card w

omit [Fintype K] in

theorem finrank_constrSpan_add_incsubsp (w : K → WalkSp I) :
    Module.finrank ℝ (constrSpan w) +
      Module.finrank ℝ (incsubsp w) = Fintype.card I := by
  calc
    Module.finrank ℝ (constrSpan w) +
        Module.finrank ℝ (incsubsp w) =
        Module.finrank ℝ (WalkSp I) := by
      exact Submodule.finrank_add_finrank_orthogonal (constrSpan w)
    _ = Fintype.card I := finrank_euclideanSpace

theorem card_sub_card_le_finrank_incsubsp (w : K → WalkSp I) :
    Fintype.card I - Fintype.card K ≤
      Module.finrank ℝ (incsubsp w) := by
  have hrank := finrank_constrSpan_le_card w
  have hsum := finrank_constrSpan_add_incsubsp w
  omega

variable {J : Type*} [DecidableEq I]

def coordNormal (i : I) : WalkSp I :=
  EuclideanSpace.single i 1

@[simp]
theorem inner_coordNormal (i : I) (x : WalkSp I) :
    inner ℝ (coordNormal i) x = x i := by
  rw [coordNormal, EuclideanSpace.inner_single_left]
  norm_num

def tightNormalFam (v : J → WalkSp I) (coordinates : Finset I)
    (discrepancies : Finset J) :
    Sum coordinates discrepancies → WalkSp I
  | Sum.inl i => coordNormal i.1
  | Sum.inr j => v j.1

def tightIncsubsp (v : J → WalkSp I) (coordinates : Finset I)
    (discrepancies : Finset J) : Submodule ℝ (WalkSp I) :=
  incsubsp (tightNormalFam v coordinates discrepancies)

theorem mem_tightIncsubsp_iff
    (v : J → WalkSp I) (coordinates : Finset I)
    (discrepancies : Finset J) (x : WalkSp I) :
    x ∈ tightIncsubsp v coordinates discrepancies ↔
      (∀ i ∈ coordinates, x i = 0) ∧
      (∀ j ∈ discrepancies, inner ℝ (v j) x = 0) := by
  rw [tightIncsubsp, mem_incsubsp_iff]
  constructor
  · intro h
    constructor
    · intro i hi
      simpa [tightNormalFam, inner_coordNormal] using
        h (Sum.inl ⟨i, hi⟩)
    · intro j hj
      simpa [tightNormalFam] using h (Sum.inr ⟨j, hj⟩)
  · rintro ⟨hcoord, hdisc⟩ k
    cases k with
    | inl i =>
        simpa [tightNormalFam, inner_coordNormal] using hcoord i.1 i.2
    | inr j =>
        simpa [tightNormalFam] using hdisc j.1 j.2

theorem card_sub_tight_card_le_finrank
    (v : J → WalkSp I) (coordinates : Finset I)
    (discrepancies : Finset J) :
    Fintype.card I - (coordinates.card + discrepancies.card) ≤
      Module.finrank ℝ (tightIncsubsp v coordinates discrepancies) := by
  have h := card_sub_card_le_finrank_incsubsp
    (tightNormalFam v coordinates discrepancies)
  rw [card_sum, card_coe, card_coe] at h
  exact h

end

end ProjWalk

end

open ProjWalk


section

open scoped BigOperators

noncomputable section

namespace Disc

variable {I J : Type*} [Fintype I] [Fintype J]

def dot (x v : I → ℝ) : ℝ := ∑ i, x i * v i

theorem dot_sub_left (x y v : I → ℝ) :
    dot (x - y) v = dot x v - dot y v := by
  simp only [dot, Pi.sub_apply, sub_mul, sum_sub_distrib]

def InCube (x : I → ℝ) : Prop := ∀ i, |x i| ≤ 1

def IsSign (x : I → ℝ) : Prop := ∀ i, x i = 1 ∨ x i = -1

def l2Norm (v : I → ℝ) : ℝ := sqrt (∑ i, (v i) ^ 2)

def toWalkSp (x : I → ℝ) : WalkSp I :=
  WithLp.toLp 2 x

@[simp] theorem toWalkSp_apply (x : I → ℝ) (i : I) :
    toWalkSp x i = x i := rfl

theorem norm_toWalkSp (v : I → ℝ) : ‖toWalkSp v‖ = l2Norm v := by
  rw [EuclideanSpace.norm_eq]
  simp only [toWalkSp_apply, norm_eq_abs, sq_abs, l2Norm]

theorem l2Norm_eq_zero_iff (v : I → ℝ) : l2Norm v = 0 ↔ v = 0 := by
  rw [← norm_toWalkSp, norm_eq_zero]
  constructor
  · intro h
    funext i
    have hi := congrArg (fun x : WalkSp I ↦ x i) h
    simpa [toWalkSp] using hi
  · rintro rfl
    rfl

theorem dot_eq_zero_of_l2Norm_eq_zero (x v : I → ℝ)
    (hv : l2Norm v = 0) : dot x v = 0 := by
  rw [(l2Norm_eq_zero_iff v).mp hv]
  simp [dot]

def fixCoords [DecidableEq I] (x : I → ℝ) : Finset I :=
  Finset.univ.filter fun i ↦ |x i| = 1

def dotOn (F : Finset I) (x v : I → ℝ) : ℝ :=
  ∑ i ∈ F, x i * v i

def restrict (F : Finset I) (x : I → ℝ) : F → ℝ := fun i ↦ x i

def restrictOutside [DecidableEq I] (F : Finset I) (x : I → ℝ) :
    ↥(Fᶜ : Finset I) → ℝ := fun i ↦ x i

def glue [DecidableEq I] (F : Finset I) (xF : F → ℝ)
    (xOutside : ↥(Fᶜ : Finset I) → ℝ) : I → ℝ :=
  fun i ↦ if hi : i ∈ F then xF ⟨i, hi⟩ else xOutside ⟨i, by simp [hi]⟩

section Glue

variable [DecidableEq I] (F : Finset I)

@[simp] theorem glue_apply_mem (xF : F → ℝ)
    (xOutside : ↥(Fᶜ : Finset I) → ℝ) {i : I} (hi : i ∈ F) :
    glue F xF xOutside i = xF ⟨i, hi⟩ := by
  simp [glue, hi]

@[simp] theorem glue_apply_not_mem (xF : F → ℝ)
    (xOutside : ↥(Fᶜ : Finset I) → ℝ) {i : I} (hi : i ∉ F) :
    glue F xF xOutside i = xOutside ⟨i, by simp [hi]⟩ := by
  simp [glue, hi]

@[simp] theorem restrict_glue (xF : F → ℝ)
    (xOutside : ↥(Fᶜ : Finset I) → ℝ) :
    restrict F (glue F xF xOutside) = xF := by
  funext i
  simp [restrict]

@[simp] theorem restrictOutside_glue (xF : F → ℝ)
    (xOutside : ↥(Fᶜ : Finset I) → ℝ) :
    restrictOutside F (glue F xF xOutside) = xOutside := by
  funext i
  have hi : (i : I) ∉ F := Finset.mem_compl.mp i.property
  change glue F xF xOutside i = xOutside i
  rw [glue_apply_not_mem F xF xOutside hi]

@[simp] theorem glue_restrict (x : I → ℝ) :
    glue F (restrict F x) (restrictOutside F x) = x := by
  funext i
  by_cases hi : i ∈ F <;> simp [glue, restrict, restrictOutside, hi]

theorem isSign_glue {xF : F → ℝ} {xOutside : ↥(Fᶜ : Finset I) → ℝ}
    (hF : IsSign xF) (hOutside : IsSign xOutside) :
    IsSign (glue F xF xOutside) := by
  intro i
  by_cases hi : i ∈ F
  · simpa [glue, hi] using hF ⟨i, hi⟩
  · simpa [glue, hi] using hOutside ⟨i, Finset.mem_compl.mpr hi⟩

end Glue

section RestrictedDot

variable [DecidableEq I]

theorem dot_eq_dotOn_add_dotOn_compl (F : Finset I) (x v : I → ℝ) :
    dot x v = dotOn F x v + dotOn Fᶜ x v := by
  simpa only [dot, dotOn] using
    (F.sum_add_sum_compl (fun i ↦ x i * v i)).symm

theorem dot_glue (F : Finset I) (xF : F → ℝ)
    (xOutside : ↥(Fᶜ : Finset I) → ℝ) (v : I → ℝ) :
    dot (glue F xF xOutside) v =
      dot xF (restrict F v) + dot xOutside (restrictOutside F v) := by
  rw [dot_eq_dotOn_add_dotOn_compl F]
  congr 1
  · rw [dotOn, dot, ← sum_attach]
    simp [glue, restrict]
  · rw [dotOn, dot, ← sum_attach]
    apply sum_congr rfl
    intro i _
    have hi : (i : I) ∉ F := Finset.mem_compl.mp i.property
    simp [glue, restrictOutside, hi]

theorem dot_restrict_add_outside (F : Finset I) (x v : I → ℝ) :
    dot x v = dot (restrict F x) (restrict F v) +
      dot (restrictOutside F x) (restrictOutside F v) := by
  simpa using dot_glue F (restrict F x) (restrictOutside F x) v

end RestrictedDot

def HasPartialColoring [DecidableEq I]
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ) : Prop :=
  ∃ x : I → ℝ,
    InCube x ∧
      Fintype.card I ≤ 2 * (fixCoords x).card ∧
      ∀ j, |dot (x - x₀) (v j)| ≤ c j * l2Norm (v j)

def PartialColoringPrinciple (I J : Type*)
    [Fintype I] [Fintype J] [DecidableEq I] : Prop :=
  ∀ (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ),
    InCube x₀ →
      (∀ j, 0 ≤ c j) →
      (∑ j, Real.exp (-(c j) ^ 2 / 16)) ≤ (Fintype.card I : ℝ) / 16 →
      HasPartialColoring v x₀ c

def HasFullColoring
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ) : Prop :=
  ∃ x : I → ℝ, IsSign x ∧
    ∀ j,
      |dot (x - x₀) (v j)| ≤
        (c j + 30) * sqrt (Fintype.card I) * ‖v j‖

def partialParam (c : J → ℝ) : J → ℝ := fun j ↦ 2 * c j / 7

theorem partialParam_nonneg {c : J → ℝ} (hc : ∀ j, 0 ≤ c j) :
    ∀ j, 0 ≤ partialParam c j := by
  intro j
  simp only [partialParam]
  exact div_nonneg (mul_nonneg (by norm_num) (hc j)) (by norm_num)

theorem partialParam_exponent (c : J → ℝ) (j : J) :
    -((partialParam c j) ^ 2) / 16 = -(c j) ^ 2 / 196 := by
  simp only [partialParam]
  ring

theorem partialParam_budget {c : J → ℝ}
    (hbudget : (∑ j, Real.exp (-(c j) ^ 2 / 196)) ≤
      (Fintype.card I : ℝ) / 16) :
    (∑ j, Real.exp (-((partialParam c j) ^ 2) / 16)) ≤
      (Fintype.card I : ℝ) / 16 := by
  simpa only [partialParam_exponent] using hbudget

theorem partialColoring_step [DecidableEq I]
    (hLM : PartialColoringPrinciple I J)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (hx₀ : InCube x₀) (hc : ∀ j, 0 ≤ c j)
    (hbudget : (∑ j, Real.exp (-(c j) ^ 2 / 196)) ≤
      (Fintype.card I : ℝ) / 16) :
    HasPartialColoring v x₀ (partialParam c) := by
  exact hLM v x₀ (partialParam c) hx₀
    (partialParam_nonneg hc) (partialParam_budget hbudget)

theorem induction_const_ineq (d : ℕ) (c : ℝ)
    (hd : 900 < d) (hc : 0 ≤ c) :
    2 * c / 7 * sqrt d +
        (sqrt (c ^ 2 + 196 * log ((d : ℝ) / (d / 2 : ℕ))) + 30) *
          sqrt (d / 2 : ℕ) ≤
      (c + 30) * sqrt d := by
  have he_pos_nat : 0 < d / 2 := by omega
  have he_ge_nat : 450 ≤ d / 2 := by omega
  have hd_le_nat : d ≤ 2 * (d / 2) + 1 := by omega
  have he_pos : 0 < ((d / 2 : ℕ) : ℝ) := by exact_mod_cast he_pos_nat
  have he_ge : (450 : ℝ) ≤ (d / 2 : ℕ) := by exact_mod_cast he_ge_nat
  have hd_le : (d : ℝ) ≤ 2 * (d / 2 : ℕ) + 1 := by exact_mod_cast hd_le_nat
  have hd_pos_nat : 0 < d := by omega
  have hd_pos : 0 < (d : ℝ) := by exact_mod_cast hd_pos_nat
  have hratio_pos : 0 < (d : ℝ) / (d / 2 : ℕ) := div_pos hd_pos he_pos
  have hratio_le : (d : ℝ) / (d / 2 : ℕ) ≤ (901 : ℝ) / 450 := by
    rw [div_le_iff₀ he_pos]
    nlinarith
  have hlog_aux : log ((901 : ℝ) / 450) ≤ log 2 + 1 / 900 := by
    rw [show (901 : ℝ) / 450 = 2 * (901 / 900) by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    gcongr
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 901 / 900 by norm_num)
    norm_num at h ⊢
    exact h
  have hlog : log ((d : ℝ) / (d / 2 : ℕ)) ≤ (36 : ℝ) / 49 := by
    calc
      log ((d : ℝ) / (d / 2 : ℕ))
          ≤ log ((901 : ℝ) / 450) := Real.log_le_log hratio_pos hratio_le
      _ ≤ log 2 + 1 / 900 := hlog_aux
      _ ≤ (36 : ℝ) / 49 := by
        have h := log_two_lt_d9.le
        norm_num at h ⊢
        linarith
  have ha :
      sqrt (c ^ 2 + 196 * log ((d : ℝ) / (d / 2 : ℕ))) ≤ c + 12 := by
    rw [sqrt_le_iff]
    constructor
    · linarith
    · nlinarith
  have he_le_nat : 2 * (d / 2) ≤ d := by omega
  have he_le : 2 * ((d / 2 : ℕ) : ℝ) ≤ d := by exact_mod_cast he_le_nat
  have hsqrt : sqrt (d / 2 : ℕ) ≤ (71 : ℝ) / 100 * sqrt d := by
    rw [sqrt_le_iff]
    constructor
    · positivity
    · have hsqd := sq_sqrt hd_pos.le
      nlinarith
  calc
    2 * c / 7 * sqrt d +
          (sqrt (c ^ 2 + 196 * log ((d : ℝ) / (d / 2 : ℕ))) + 30) *
            sqrt (d / 2 : ℕ)
        ≤ 2 * c / 7 * sqrt d + (c + 42) * sqrt (d / 2 : ℕ) := by
          exact add_le_add_right
            (mul_le_mul_of_nonneg_right (by linarith [ha]) (sqrt_nonneg _)) _
    _ ≤ 2 * c / 7 * sqrt d +
          (c + 42) * ((71 : ℝ) / 100 * sqrt d) := by
          exact add_le_add_right (mul_le_mul_of_nonneg_left hsqrt (by linarith)) _
    _ = (2 * c / 7 + (c + 42) * ((71 : ℝ) / 100)) * sqrt d := by ring
    _ ≤ (c + 30) * sqrt d := by
          apply mul_le_mul_of_nonneg_right _ (sqrt_nonneg _)
          nlinarith

@[simp] theorem dot_zero_left (v : I → ℝ) : dot 0 v = 0 := by
  simp [dot]

@[simp] theorem dot_zero_right (x : I → ℝ) : dot x 0 = 0 := by
  simp [dot]

theorem abs_dot_le_sum_abs_mul (x v : I → ℝ) :
    |dot x v| ≤ ∑ i, |x i| * |v i| := by
  rw [dot]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  exact sum_le_sum fun i _ ↦ by rw [abs_mul]

theorem abs_dot_le_card_mul_norm_of_abs_le
    {x v : I → ℝ} {a : ℝ} (ha : 0 ≤ a) (hx : ∀ i, |x i| ≤ a) :
    |dot x v| ≤ Fintype.card I * a * ‖v‖ := by
  calc
    |dot x v| ≤ ∑ i, |x i| * |v i| := abs_dot_le_sum_abs_mul x v
    _ ≤ ∑ _i : I, a * ‖v‖ := by
      refine sum_le_sum fun i _ ↦ mul_le_mul (hx i) (norm_le_pi_norm v i)
        (abs_nonneg _) ha
    _ = Fintype.card I * a * ‖v‖ := by simp [mul_assoc]

theorem sum_sq_le_card_mul_norm_sq (v : I → ℝ) :
    (∑ i, (v i) ^ 2) ≤ Fintype.card I * ‖v‖ ^ 2 := by
  calc
    (∑ i, (v i) ^ 2) ≤ ∑ _i : I, ‖v‖ ^ 2 := by
      refine sum_le_sum fun i _ ↦ ?_
      have hvi : |v i| ≤ ‖v‖ := by
        simpa only [norm_eq_abs] using norm_le_pi_norm v i
      rw [← sq_abs]
      nlinarith [abs_nonneg (v i), norm_nonneg v,
        mul_nonneg (sub_nonneg.mpr hvi) (add_nonneg (norm_nonneg v) (abs_nonneg (v i)))]
    _ = Fintype.card I * ‖v‖ ^ 2 := by simp

theorem l2Norm_le_sqrt_card_mul_norm (v : I → ℝ) :
    l2Norm v ≤ sqrt (Fintype.card I) * ‖v‖ := by
  have hsum_nonneg : 0 ≤ ∑ i, (v i) ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hcard_nonneg : 0 ≤ (Fintype.card I : ℝ) := Nat.cast_nonneg _
  have hnorm_nonneg : 0 ≤ ‖v‖ := norm_nonneg _
  rw [l2Norm, ← sqrt_sq hnorm_nonneg, ← sqrt_mul hcard_nonneg]
  exact sqrt_le_sqrt (sum_sq_le_card_mul_norm_sq v)

def nearestSign (x : I → ℝ) : I → ℝ :=
  fun i ↦ if 0 ≤ x i then 1 else -1

theorem nearestSign_isSign (x : I → ℝ) : IsSign (nearestSign x) := by
  intro i
  simp only [nearestSign]
  split_ifs <;> simp

theorem abs_nearestSign_sub_le_one {x : I → ℝ} (hx : InCube x) (i : I) :
    |nearestSign x i - x i| ≤ 1 := by
  have hxi := hx i
  simp only [abs_le] at hxi
  simp only [nearestSign]
  split_ifs with h
  · rw [abs_of_nonneg]
    · linarith
    · linarith
  · rw [abs_of_nonpos]
    · linarith
    · linarith

theorem nearestSign_dot_sub_le_card_mul_norm
    {x : I → ℝ} (hx : InCube x) (v : I → ℝ) :
    |dot (nearestSign x - x) v| ≤ Fintype.card I * ‖v‖ := by
  change |dot (fun i ↦ nearestSign x i - x i) v| ≤ Fintype.card I * ‖v‖
  simpa using abs_dot_le_card_mul_norm_of_abs_le (v := v) (a := 1)
    (by norm_num) (abs_nearestSign_sub_le_one hx)

theorem card_le_900_le_thirty_mul_sqrt_card
    (hcard : Fintype.card I ≤ 900) :
    (Fintype.card I : ℝ) ≤ 30 * sqrt (Fintype.card I) := by
  have h0 : 0 ≤ (Fintype.card I : ℝ) := Nat.cast_nonneg _
  have hsqrt : sqrt (Fintype.card I) ≤ 30 := by
    rw [sqrt_le_iff]
    constructor
    · norm_num
    · norm_num
      exact_mod_cast hcard
  nlinarith [sq_sqrt h0, sqrt_nonneg (Fintype.card I)]

theorem hasFullColoring_of_card_le_900
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (hx₀ : InCube x₀) (hc : ∀ j, 0 ≤ c j)
    (hcard : Fintype.card I ≤ 900) :
    HasFullColoring v x₀ c := by
  refine ⟨nearestSign x₀, nearestSign_isSign x₀, ?_⟩
  intro j
  have hround := nearestSign_dot_sub_le_card_mul_norm hx₀ (v j)
  have hdim := card_le_900_le_thirty_mul_sqrt_card (I := I) hcard
  calc
    |dot (nearestSign x₀ - x₀) (v j)|
        ≤ Fintype.card I * ‖v j‖ := hround
    _ ≤ 30 * sqrt (Fintype.card I) * ‖v j‖ := by
      exact mul_le_mul_of_nonneg_right hdim (norm_nonneg _)
    _ ≤ (c j + 30) * sqrt (Fintype.card I) * ‖v j‖ := by
      gcongr
      linarith [hc j]

end Disc

end
end

open Disc


section

open scoped BigOperators

noncomputable section

namespace Disc

universe uI uJ

variable {I : Type uI} {J : Type uJ} [Fintype I] [Fintype J]

def nextParam (d : ℕ) (c : J → ℝ) : J → ℝ :=
  fun j ↦ sqrt (c j ^ 2 + 196 * log ((d : ℝ) / (d / 2 : ℕ)))

omit [Fintype J] in
theorem nextParam_nonneg (d : ℕ) (c : J → ℝ) :
    ∀ j, 0 ≤ nextParam d c j := fun _ ↦ sqrt_nonneg _

theorem half_pos {d : ℕ} (hd : 900 < d) : 0 < d / 2 := by omega

theorem half_lt {d : ℕ} (hd : 900 < d) : d / 2 < d := by omega

theorem half_ratio_one_le {d : ℕ} (hd : 900 < d) :
    (1 : ℝ) ≤ (d : ℝ) / (d / 2 : ℕ) := by
  have hq : 0 < ((d / 2 : ℕ) : ℝ) := by exact_mod_cast half_pos hd
  rw [le_div_iff₀ hq]
  norm_num
  exact_mod_cast (show d / 2 ≤ d by omega)

omit [Fintype J] in
theorem nextParam_sq {d : ℕ} (hd : 900 < d) (c : J → ℝ) (j : J) :
    nextParam d c j ^ 2 =
      c j ^ 2 + 196 * log ((d : ℝ) / (d / 2 : ℕ)) := by
  rw [nextParam, sq_sqrt]
  have hlog : 0 ≤ log ((d : ℝ) / (d / 2 : ℕ)) :=
    log_nonneg (half_ratio_one_le hd)
  positivity

omit [Fintype J] in
theorem nextParam_exp_id {d : ℕ} (hd : 900 < d)
    (c : J → ℝ) (j : J) :
    Real.exp (-(nextParam d c j) ^ 2 / 196) =
      Real.exp (-(c j) ^ 2 / 196) * ((d / 2 : ℕ) : ℝ) / d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hqR : (0 : ℝ) < (d / 2 : ℕ) := by exact_mod_cast half_pos hd
  rw [nextParam_sq hd]
  rw [show -(c j ^ 2 + 196 * log ((d : ℝ) / (d / 2 : ℕ))) / 196 =
      -(c j) ^ 2 / 196 - log ((d : ℝ) / (d / 2 : ℕ)) by ring]
  rw [Real.exp_sub, exp_log (div_pos hdR hqR)]
  field_simp

theorem nextParam_budget {d : ℕ} (hd : 900 < d) (c : J → ℝ)
    (hbudget : (∑ j, Real.exp (-(c j) ^ 2 / 196)) ≤ (d : ℝ) / 16) :
    (∑ j, Real.exp (-(nextParam d c j) ^ 2 / 196)) ≤
      ((d / 2 : ℕ) : ℝ) / 16 := by
  simp_rw [nextParam_exp_id hd]
  simp_rw [mul_div_assoc]
  rw [← Finset.sum_mul]
  have hfactor : 0 ≤ (((d / 2 : ℕ) : ℝ) / d) := by positivity
  calc
    (∑ j, Real.exp (-(c j) ^ 2 / 196)) * (((d / 2 : ℕ) : ℝ) / d)
        ≤ ((d : ℝ) / 16) * (((d / 2 : ℕ) : ℝ) / d) := by
          exact mul_le_mul_of_nonneg_right hbudget hfactor
    _ = ((d / 2 : ℕ) : ℝ) / 16 := by
      have hd0 : (d : ℝ) ≠ 0 := by positivity
      field_simp

def padVec [DecidableEq I] (F : Finset I) (q : ℕ) (v : I → ℝ) :
    Sum ↥(Fᶜ : Finset I) (Fin (q - Fᶜ.card)) → ℝ
  | Sum.inl i => v i
  | Sum.inr _ => 0

def padPt [DecidableEq I] (F : Finset I) (q : ℕ) (x : I → ℝ) :
    Sum ↥(Fᶜ : Finset I) (Fin (q - Fᶜ.card)) → ℝ
  | Sum.inl i => x i
  | Sum.inr _ => 0

theorem inCube_padPt [DecidableEq I] (F : Finset I) (q : ℕ)
    {x : I → ℝ} (hx : InCube x) : InCube (padPt F q x) := by
  intro i
  cases i with
  | inl i => simpa [padPt] using hx i
  | inr i => simp [padPt]

theorem norm_padVec_le [DecidableEq I] (F : Finset I) (q : ℕ)
    (v : I → ℝ) : ‖padVec F q v‖ ≤ ‖v‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  cases i with
  | inl i => simpa [padVec] using norm_le_pi_norm v i
  | inr i => simp [padVec]

theorem card_pad [DecidableEq I] (F : Finset I) (q : ℕ)
    (hcard : Fᶜ.card ≤ q) :
    Fintype.card (Sum ↥(Fᶜ : Finset I) (Fin (q - Fᶜ.card))) = q := by
  rw [card_sum, card_coe, card_fin,
    Nat.add_sub_of_le hcard]

theorem dot_pad_sub [DecidableEq I] (F : Finset I) (q : ℕ)
    (y : Sum ↥(Fᶜ : Finset I) (Fin (q - Fᶜ.card)) → ℝ)
    (x v : I → ℝ) :
    dot (y - padPt F q x) (padVec F q v) =
      dot (fun i : ↥(Fᶜ : Finset I) ↦ y (Sum.inl i) - x i)
        (restrictOutside F v) := by
  simp [dot, padPt, padVec, restrictOutside]

theorem fix_restrict_isSign [DecidableEq I] (x : I → ℝ) :
    IsSign (restrict (fixCoords x) x) := by
  intro i
  have hi : |x i| = 1 := by
    simpa [fixCoords] using i.property
  simpa [restrict] using (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hi

theorem card_compl_fix_le_half [DecidableEq I] {x : I → ℝ}
    (hfixed : Fintype.card I ≤ 2 * (fixCoords x).card) :
    (fixCoords x)ᶜ.card ≤ Fintype.card I / 2 := by
  rw [Finset.card_compl]
  omega

theorem hasFullColoring_of_partialColoringPrinciple
    (hLM : ∀ (K : Type uI) [Fintype K] [DecidableEq K],
      PartialColoringPrinciple K J)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (hx₀ : InCube x₀) (hc : ∀ j, 0 ≤ c j)
    (hbudget : (∑ j, Real.exp (-(c j) ^ 2 / 196)) ≤
      (Fintype.card I : ℝ) / 16) :
    HasFullColoring v x₀ c := by
  classical
  generalize hdcard : Fintype.card I = d at hbudget ⊢
  induction d using Nat.strong_induction_on generalizing I c with
  | h d ih =>
      by_cases hdsmall : d ≤ 900
      · exact hasFullColoring_of_card_le_900 v x₀ c hx₀ hc
          (hdcard.trans_le hdsmall)
      · have hdlarge : 900 < d := by omega
        have hbudgetI :
            (∑ j, Real.exp (-(c j) ^ 2 / 196)) ≤
              (Fintype.card I : ℝ) / 16 := by simpa [hdcard] using hbudget
        obtain ⟨x, hxCube, hxFixed, hxError⟩ :=
          partialColoring_step (hLM I) v x₀ c hx₀ hc hbudgetI
        let F : Finset I := fixCoords x
        let q : ℕ := d / 2
        have hFcard : Fᶜ.card ≤ q := by
          dsimp only [F, q]
          have hhalf := card_compl_fix_le_half hxFixed
          simpa [hdcard] using hhalf
        let K := Sum ↥(Fᶜ : Finset I) (Fin (q - Fᶜ.card))
        let vK : J → K → ℝ := fun j ↦ padVec F q (v j)
        let xK : K → ℝ := padPt F q x
        have hcardK : Fintype.card K = q := by
          exact card_pad F q hFcard
        have hq_lt : q < d := by
          dsimp only [q]
          exact half_lt hdlarge
        have hxK : InCube xK := inCube_padPt F q hxCube
        have hbudgetK :
            (∑ j, Real.exp (-(nextParam d c j) ^ 2 / 196)) ≤
              (Fintype.card K : ℝ) / 16 := by
          rw [hcardK]
          exact nextParam_budget hdlarge c hbudget
        have hrecursive : HasFullColoring vK xK (nextParam d c) := by
          apply ih q hq_lt (I := K) vK xK (nextParam d c) hxK
            (nextParam_nonneg d c) hcardK
          simpa [hcardK] using hbudgetK
        obtain ⟨yK, hyKSign, hyKError⟩ := hrecursive
        let yOutside : ↥(Fᶜ : Finset I) → ℝ := fun i ↦ yK (Sum.inl i)
        let y : I → ℝ := glue F (restrict F x) yOutside
        have hyOutsideSign : IsSign yOutside := fun i ↦ hyKSign (Sum.inl i)
        have hySign : IsSign y := by
          exact isSign_glue F (fix_restrict_isSign x) hyOutsideSign
        refine ⟨y, hySign, ?_⟩
        intro j
        have hpartial :
            |dot (x - x₀) (v j)| ≤
              (2 * c j / 7 * sqrt d) * ‖v j‖ := by
          calc
            |dot (x - x₀) (v j)|
                ≤ partialParam c j * l2Norm (v j) := hxError j
            _ ≤ partialParam c j *
                (sqrt (Fintype.card I) * ‖v j‖) := by
                  exact mul_le_mul_of_nonneg_left
                    (l2Norm_le_sqrt_card_mul_norm (v j))
                    (partialParam_nonneg hc j)
            _ = (2 * c j / 7 * sqrt d) * ‖v j‖ := by
                  simp [partialParam, hdcard]
                  ring
        have hvKnorm : ‖vK j‖ ≤ ‖v j‖ := norm_padVec_le F q (v j)
        have hrecursiveError :
            |dot (yK - xK) (vK j)| ≤
              ((nextParam d c j + 30) * sqrt q) * ‖v j‖ := by
          calc
            |dot (yK - xK) (vK j)|
                ≤ (nextParam d c j + 30) *
                    sqrt (Fintype.card K) * ‖vK j‖ := hyKError j
            _ = ((nextParam d c j + 30) * sqrt q) * ‖vK j‖ := by
                  rw [hcardK]
            _ ≤ ((nextParam d c j + 30) * sqrt q) * ‖v j‖ := by
                  exact mul_le_mul_of_nonneg_left hvKnorm
                    (mul_nonneg (by linarith [nextParam_nonneg d c j])
                      (sqrt_nonneg _))
        have hyxDot :
            dot (y - x) (v j) = dot (yK - xK) (vK j) := by
          calc
            dot (y - x) (v j) =
                dot (yOutside - restrictOutside F x) (restrictOutside F (v j)) := by
              change dot (glue F (restrict F x) yOutside - x) (v j) = _
              rw [dot_sub_left, dot_glue, dot_restrict_add_outside F x,
                dot_sub_left]
              ring
            _ = dot (yK - xK) (vK j) := by
              symm
              exact dot_pad_sub F q yK x (v j)
        have hyx :
            |dot (y - x) (v j)| ≤
              ((nextParam d c j + 30) * sqrt q) * ‖v j‖ := by
          rw [hyxDot]
          exact hrecursiveError
        have hsplit :
            dot (y - x₀) (v j) = dot (x - x₀) (v j) + dot (y - x) (v j) := by
          rw [dot_sub_left, dot_sub_left, dot_sub_left]
          ring
        rw [hsplit]
        calc
          |dot (x - x₀) (v j) + dot (y - x) (v j)|
              ≤ |dot (x - x₀) (v j)| + |dot (y - x) (v j)| := abs_add_le _ _
          _ ≤ (2 * c j / 7 * sqrt d) * ‖v j‖ +
                ((nextParam d c j + 30) * sqrt q) * ‖v j‖ :=
              add_le_add hpartial hyx
          _ = (2 * c j / 7 * sqrt d +
                (nextParam d c j + 30) * sqrt q) * ‖v j‖ := by ring
          _ ≤ ((c j + 30) * sqrt d) * ‖v j‖ := by
              exact mul_le_mul_of_nonneg_right
                (by simpa [nextParam, q] using
                  induction_const_ineq d (c j) hdlarge (hc j))
                (norm_nonneg _)
          _ = (c j + 30) * sqrt (Fintype.card I) * ‖v j‖ := by
              rw [hdcard]

end Disc

end
end

section

namespace KernelClaims

open scoped BigOperators Interval
open Real Set MeasureTheory intervalIntegral

private lemma hasDerivAt_neg_cos_div (ω : ℝ) (hω : ω ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ -cos (ω * y) / ω)
      (sin (ω * x)) x := by
  simpa [hω] using ((hasDerivAt_const_mul ω).cos.neg.div_const ω)

theorem abs_intg_mul_sin_le_of_deriv_nonneg
    {h h' : ℝ → ℝ} {a b : ℝ} {n : ℕ}
    (hn : 0 < n) (hab : a ≤ b)
    (hderiv : ∀ x ∈ Icc a b, HasDerivAt h (h' x) x)
    (hcont : ContinuousOn h' (Icc a b))
    (hnonneg : ∀ x ∈ Icc a b, 0 ≤ h' x)
    (hcos : cos ((2 * (n : ℝ)) * b) = cos ((2 * (n : ℝ)) * a)) :
    |∫ x in a..b, h x * sin ((2 * (n : ℝ)) * x)| ≤
      |h b - h a| / n := by
  let ω : ℝ := 2 * (n : ℝ)
  have hω : ω ≠ 0 := by
    dsimp [ω]
    positivity
  let v : ℝ → ℝ := fun x ↦ -cos (ω * x) / ω
  have hvderiv : ∀ x ∈ Icc a b, HasDerivAt v (sin (ω * x)) x := by
    intro x hx
    exact hasDerivAt_neg_cos_div ω hω x
  have hh'int : IntervalIntegrable h' volume a b :=
    hcont.intervalIntegrable_of_Icc hab
  have hv'int : IntervalIntegrable (fun x ↦ sin (ω * x)) volume a b :=
    (continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hderivU : ∀ x ∈ uIcc a b, HasDerivAt h (h' x) x := by
    simpa [uIcc_of_le hab] using hderiv
  have hvderivU : ∀ x ∈ uIcc a b, HasDerivAt v (sin (ω * x)) x := by
    simpa [uIcc_of_le hab] using hvderiv
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := a) (b := b) hderivU hvderivU hh'int hv'int
  have hhprime : (∫ x in a..b, h' x) = h b - h a := by
    exact integral_eq_sub_of_hasDerivAt hderivU hh'int
  have hdiff_nonneg : 0 ≤ h b - h a := by
    rw [← hhprime]
    exact intervalIntegral.integral_nonneg hab hnonneg
  have hv_bound (x : ℝ) : |v x| ≤ 1 / ω := by
    dsimp [v]
    rw [abs_div, abs_neg, abs_of_pos (show 0 < ω by positivity)]
    exact div_le_div_of_nonneg_right (abs_cos_le_one _) (by positivity)
  have hj_bound : |∫ x in a..b, h' x * v x| ≤ (h b - h a) / ω := by
    calc
      |∫ x in a..b, h' x * v x| ≤ ∫ x in a..b, |h' x * v x| :=
        intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ x in a..b, h' x * (1 / ω) := by
        refine integral_mono_on hab ?_ ?_ ?_
        · exact (hh'int.mul_continuousOn
            (show ContinuousOn v (uIcc a b) from by
              simpa [uIcc_of_le hab] using
                ((continuous_cos.comp
                  (continuous_const.mul continuous_id)).neg.div_const _).continuousOn)).abs
        · exact hh'int.mul_const _
        · intro x hx
          rw [abs_mul, abs_of_nonneg (hnonneg x hx)]
          exact mul_le_mul_of_nonneg_left (hv_bound x) (hnonneg x hx)
      _ = (h b - h a) / ω := by
        rw [intervalIntegral.integral_mul_const, hhprime]
        ring
  have hboundary :
      h b * v b - h a * v a =
        (cos (ω * a) * (h a - h b)) / ω := by
    dsimp [v, ω] at hcos ⊢
    rw [hcos]
    ring
  change |∫ x in a..b, h x * sin (ω * x)| ≤ |h b - h a| / n
  rw [hparts, hboundary]
  have hboundary_abs :
      |cos (ω * a) * (h a - h b) / ω| ≤
        (h b - h a) / ω := by
    rw [abs_div, abs_mul, abs_sub_comm, abs_of_nonneg hdiff_nonneg,
      abs_of_pos (show 0 < ω by positivity)]
    exact div_le_div_of_nonneg_right
      (mul_le_of_le_one_left hdiff_nonneg (abs_cos_le_one _)) (by positivity)
  calc
    |cos (ω * a) * (h a - h b) / ω -
        ∫ x in a..b, h' x * v x| ≤
        |cos (ω * a) * (h a - h b) / ω| +
          |∫ x in a..b, h' x * v x| := abs_sub _ _
    _ ≤ (h b - h a) / ω + (h b - h a) / ω :=
      add_le_add hboundary_abs hj_bound
    _ = |h b - h a| / n := by
      rw [abs_of_nonneg hdiff_nonneg]
      dsimp [ω]
      field_simp
      ring

theorem abs_intg_mul_sin_le_of_deriv_nonpos
    {h h' : ℝ → ℝ} {a b : ℝ} {n : ℕ}
    (hn : 0 < n) (hab : a ≤ b)
    (hderiv : ∀ x ∈ Icc a b, HasDerivAt h (h' x) x)
    (hcont : ContinuousOn h' (Icc a b))
    (hnonpos : ∀ x ∈ Icc a b, h' x ≤ 0)
    (hcos : cos ((2 * (n : ℝ)) * b) = cos ((2 * (n : ℝ)) * a)) :
    |∫ x in a..b, h x * sin ((2 * (n : ℝ)) * x)| ≤
      |h b - h a| / n := by
  have h := abs_intg_mul_sin_le_of_deriv_nonneg
    (h := fun x ↦ -h x) (h' := fun x ↦ -h' x) hn hab
    (fun x hx ↦ (hderiv x hx).neg) hcont.neg
    (fun x hx ↦ neg_nonneg.mpr (hnonpos x hx)) hcos
  simpa only [neg_mul, intervalIntegral.integral_neg, abs_neg, neg_sub_neg,
    abs_sub_comm] using h

theorem sum_ivl_error_le_of_mono_endpts
    {m : ℕ} {A B E : ℕ → ℝ} {n : ℕ} (hn : 0 < n)
    (hlocal : ∀ k < m, E k ≤ (B k - A k) / n)
    (hchain : ∀ k < m, B k ≤ A (k + 1)) :
    ∑ k ∈ Finset.range m, E k ≤ (A m - A 0) / n := by
  calc
    ∑ k ∈ Finset.range m, E k ≤
        ∑ k ∈ Finset.range m, (B k - A k) / n := by
      exact sum_le_sum fun k hk ↦ hlocal k (Finset.mem_range.mp hk)
    _ ≤ ∑ k ∈ Finset.range m, (A (k + 1) - A k) / n := by
      refine sum_le_sum fun k hk ↦ div_le_div_of_nonneg_right ?_ (by positivity)
      exact sub_le_sub_right (hchain k (Finset.mem_range.mp hk)) _
    _ = (A m - A 0) / n := by
      rw [← sum_div]
      congr 1
      simpa using sum_range_sub A m

theorem norm_kernel_bounds {value main error : ℝ}
    (hvalue : value = main + error)
    (hmain_lower : 4 / 3 ≤ |main|)
    (hmain_upper : |main| ≤ 4)
    (herror : |error| ≤ 2 / 3) :
    2 / 3 ≤ |value| ∧ |value| ≤ 5 := by
  subst value
  constructor
  · have hreverse : |main| ≤ |main + error| + |error| := by
      calc
        |main| = |(main + error) - error| := by ring_nf
        _ ≤ |main + error| + |error| := abs_sub _ _
    linarith
  · have hforward : |main + error| ≤ |main| + |error| :=
      abs_add_le main error
    linarith

end KernelClaims

end

open KernelClaims


section

namespace Rounding

open scoped BigOperators

noncomputable section

def oddFreq (j : ℕ) : ℕ := 2 * j + 1

def oddSineSum (n : ℕ) (a : ℕ → ℝ) (θ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, a j * sin ((oddFreq j : ℝ) * θ)

def oddExpDeriv (l n : ℕ) (a : ℕ → ℝ) (θ : ℝ) : ℂ :=
  ∑ j ∈ Finset.range n, (a j : ℂ) *
    (((oddFreq j : ℝ) : ℂ) * Complex.I) ^ l *
      Complex.exp ((((oddFreq j : ℝ) * θ : ℝ) : ℂ) * Complex.I)

def oddSinDeriv (l n : ℕ) (a : ℕ → ℝ) (θ : ℝ) : ℝ :=
  (oddExpDeriv l n a θ).im

@[simp]
theorem oddSinDeriv_zero (n : ℕ) (a : ℕ → ℝ) (θ : ℝ) :
    oddSinDeriv 0 n a θ = oddSineSum n a θ := by
  classical
  simp only [oddSinDeriv, oddExpDeriv, oddSineSum, pow_zero,
    mul_one]
  change imLm
    (∑ j ∈ Finset.range n, (a j : ℂ) *
      Complex.exp ((((oddFreq j : ℝ) * θ : ℝ) : ℂ) * Complex.I)) = _
  rw [map_sum imLm]
  apply sum_congr rfl
  intro j hj
  change ((a j : ℂ) *
    Complex.exp ((((oddFreq j : ℝ) * θ : ℝ) : ℂ) * Complex.I)).im = _
  rw [mul_im]
  simp [Complex.exp_im]

theorem abs_oddSinDeriv_le (l n : ℕ) (a : ℕ → ℝ) (θ : ℝ) :
    |oddSinDeriv l n a θ| ≤
      ∑ j ∈ Finset.range n, |a j| * (oddFreq j : ℝ) ^ l := by
  classical
  calc
    |oddSinDeriv l n a θ| ≤ ‖oddExpDeriv l n a θ‖ :=
      abs_im_le_norm _
    _ ≤ ∑ j ∈ Finset.range n,
        ‖(a j : ℂ) *
          ((((oddFreq j : ℝ) : ℂ) * Complex.I) ^ l) *
          Complex.exp ((((oddFreq j : ℝ) * θ : ℝ) : ℂ) * Complex.I)‖ := by
      exact norm_sum_le _ _
    _ = ∑ j ∈ Finset.range n, |a j| * (oddFreq j : ℝ) ^ l := by
      apply sum_congr rfl
      intro j hj
      rw [norm_mul, norm_mul, norm_pow]
      have hexp :
          ‖Complex.exp ((((oddFreq j : ℝ) * θ : ℝ) : ℂ) * Complex.I)‖ = 1 :=
        norm_exp_ofReal_mul_I _
      have hfreq : 0 ≤ (oddFreq j : ℝ) := by positivity
      have hnormFreq : ‖((oddFreq j : ℝ) : ℂ)‖ = (oddFreq j : ℝ) :=
        Complex.norm_of_nonneg hfreq
      rw [hexp, mul_one, Complex.norm_mul, hnormFreq, norm_I, mul_one,
        Complex.norm_real, norm_eq_abs]

theorem oddFreq_le_two_mul {n j : ℕ} (hj : j ∈ Finset.range n) :
    oddFreq j ≤ 2 * n := by
  simp only [Finset.mem_range] at hj
  simp only [oddFreq]
  omega

theorem abs_oddSinDeriv_le_card_mul (l n : ℕ) (a : ℕ → ℝ) (A : ℝ)
    (hA : ∀ j < n, |a j| ≤ A) (hA0 : 0 ≤ A) (θ : ℝ) :
    |oddSinDeriv l n a θ| ≤
      n * A * (2 * n : ℝ) ^ l := by
  refine (abs_oddSinDeriv_le l n a θ).trans ?_
  calc
    (∑ j ∈ Finset.range n, |a j| * (oddFreq j : ℝ) ^ l) ≤
        ∑ _j ∈ Finset.range n, A * (2 * n : ℝ) ^ l := by
      apply sum_le_sum
      intro j hj
      have hj' : j < n := Finset.mem_range.mp hj
      have hfreq : (oddFreq j : ℝ) ≤ (2 * n : ℝ) := by
        exact_mod_cast oddFreq_le_two_mul hj
      exact mul_le_mul (hA j hj')
        (pow_le_pow_left₀ (by positivity) hfreq l) (by positivity) hA0
    _ = n * A * (2 * n : ℝ) ^ l := by
      simp [mul_assoc]

theorem hasSum_oddExpDeriv_taylor (n : ℕ) (a : ℕ → ℝ)
    (x h : ℝ) :
    HasSum (fun l : ℕ => oddExpDeriv l n a x * (h : ℂ) ^ l / l.factorial)
      (oddExpDeriv 0 n a (x + h)) := by
  classical
  have hj (j : ℕ) :
      HasSum
        (fun l : ℕ =>
          ((a j : ℂ) *
            Complex.exp ((((oddFreq j : ℝ) * x : ℝ) : ℂ) * Complex.I)) *
            (((((oddFreq j : ℝ) : ℂ) * Complex.I) * (h : ℂ)) ^ l /
              l.factorial))
        ((a j : ℂ) *
          Complex.exp ((((oddFreq j : ℝ) * x : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((oddFreq j : ℝ) : ℂ) * Complex.I * (h : ℂ))) := by
    let z : ℂ := (((oddFreq j : ℝ) : ℂ) * Complex.I) * (h : ℂ)
    let c : ℂ := (a j : ℂ) *
      Complex.exp ((((oddFreq j : ℝ) * x : ℝ) : ℂ) * Complex.I)
    have hz : HasSum (fun l : ℕ => z ^ l / l.factorial) (Complex.exp z) :=
      Complex.exp_eq_exp_ℂ ▸ NormedSpace.expSeries_div_hasSum_exp z
    simpa only [z, c] using hz.mul_left c
  have hsum := hasSum_sum (s := Finset.range n) (fun j _ => hj j)
  convert hsum using 1
  · funext l
    simp only [oddExpDeriv, Finset.sum_mul, sum_div]
    apply sum_congr rfl
    intro j hjmem
    rw [mul_pow]
    ring
  · simp only [oddExpDeriv, pow_zero, mul_one]
    apply sum_congr rfl
    intro j hjmem
    rw [show ((((oddFreq j : ℝ) * (x + h) : ℝ) : ℂ) * Complex.I) =
        ((((oddFreq j : ℝ) * x : ℝ) : ℂ) * Complex.I) +
          (((oddFreq j : ℝ) : ℂ) * Complex.I * (h : ℂ)) by
            push_cast; ring]
    rw [Complex.exp_add]
    ring

theorem hasSum_oddSinDeriv_taylor (n : ℕ) (a : ℕ → ℝ) (x h : ℝ) :
    HasSum (fun l : ℕ => oddSinDeriv l n a x * h ^ l / l.factorial)
      (oddSinDeriv 0 n a (x + h)) := by
  have him := Complex.hasSum_im (hasSum_oddExpDeriv_taylor n a x h)
  convert him using 1
  · funext l
    change (oddExpDeriv l n a x).im * h ^ l / l.factorial =
      (oddExpDeriv l n a x * (h : ℂ) ^ l / l.factorial).im
    have hcomponents : ((h : ℂ) ^ l).re = h ^ l ∧ ((h : ℂ) ^ l).im = 0 := by
      induction l with
      | zero => simp
      | succ l ih =>
          rw [pow_succ, pow_succ, mul_re, mul_im]
          simp [ih.1, ih.2]
    have hpow : (h : ℂ) ^ l = ((h ^ l : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hcomponents.1, hcomponents.2]
    rw [hpow]
    rw [Complex.div_im, Complex.normSq_natCast]
    have hfac : (l.factorial : ℝ) ≠ 0 := by positivity
    field_simp [hfac, Nat.factorial_ne_zero]
    rw [mul_im, mul_re]
    norm_num
    apply Or.inl
    rw [hcomponents.2, hcomponents.1]
    ring
  · rfl

theorem affine_le_thirty_five_mul_factorial {l : ℕ} (hl : 2 ≤ l) :
    65 + 2 * l ≤ 35 * l.factorial := by
  induction l using Nat.strong_induction_on with
  | h l ih =>
      by_cases hl2 : l = 2
      · subst l
        norm_num
      · have hl3 : 3 ≤ l := by omega
        have hlprev : 2 ≤ l - 1 := by omega
        have hih := ih (l - 1) (by omega) hlprev
        have hfac : 1 ≤ (l - 1).factorial := Nat.factorial_pos _
        have hthree : 3 * (l - 1).factorial ≤ l * (l - 1).factorial :=
          Nat.mul_le_mul_right _ hl3
        rw [show l = (l - 1) + 1 by omega, Nat.factorial_succ]
        calc
          65 + 2 * ((l - 1) + 1) = (65 + 2 * (l - 1)) + 2 := by omega
          _ ≤ 35 * (l - 1).factorial + 2 := Nat.add_le_add_right hih 2
          _ ≤ 35 * (3 * (l - 1).factorial) := by omega
          _ ≤ 35 * (l * (l - 1).factorial) := Nat.mul_le_mul_left 35 hthree
          _ = 35 * ((l - 1 + 1) * (l - 1).factorial) := by
            rw [Nat.sub_add_cancel (by omega : 1 ≤ l)]

theorem affine_le_sixty_seven_mul_factorial (l : ℕ) :
    65 + 2 * l ≤ 67 * l.factorial := by
  by_cases hl : l < 2
  · interval_cases l <;> norm_num
  · exact (affine_le_thirty_five_mul_factorial (l := l) (by omega)).trans
      (Nat.mul_le_mul_right l.factorial (by norm_num))

theorem summable_affine_factorial {q : ℝ} (hq0 : 0 ≤ q) (hq : q < 1) :
    Summable (fun l : ℕ => (65 + 2 * l : ℝ) * q ^ l / l.factorial) := by
  have habs : |q| < 1 := by simpa [abs_of_nonneg hq0]
  have hgeo0 : Summable (fun l : ℕ => q ^ l) :=
    summable_geometric_of_norm_lt_one (by simpa [norm_eq_abs] using habs)
  have hgeom : Summable (fun l : ℕ => (67 : ℝ) * q ^ l) := hgeo0.mul_left 67
  apply Summable.of_nonneg_of_le (fun l => by positivity) (fun l => ?_) hgeom
  have hcoef : (65 + 2 * l : ℝ) ≤ 67 * l.factorial := by
    exact_mod_cast affine_le_sixty_seven_mul_factorial l
  have hfact : (0 : ℝ) < l.factorial := by positivity
  calc
    (65 + 2 * l : ℝ) * q ^ l / l.factorial ≤
        (67 * l.factorial) * q ^ l / l.factorial := by gcongr
    _ = 67 * q ^ l := by field_simp

theorem tsum_affine_factorial_le_seventy_two {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ 11 / 112) :
    (∑' l : ℕ, (65 + 2 * l : ℝ) * q ^ l / l.factorial) ≤ 72 := by
  have hq1 : q < 1 := by linarith
  have hs := summable_affine_factorial hq0 hq1
  rw [← hs.sum_add_tsum_nat_add 2]
  have habs : |q| < 1 := by simpa [abs_of_nonneg hq0]
  have hgeo0 : Summable (fun l : ℕ => q ^ l) :=
    summable_geometric_of_norm_lt_one (by simpa [norm_eq_abs] using habs)
  have htailGeom : Summable (fun k : ℕ => (35 : ℝ) * q ^ (k + 2)) :=
    (hgeo0.mul_left (35 * q ^ 2)).congr
      (fun k => by rw [pow_add]; ring)
  have htail : (∑' k : ℕ,
      (65 + 2 * ((k + 2 : ℕ) : ℝ)) * q ^ (k + 2) / (k + 2).factorial) ≤
      ∑' k : ℕ, (35 : ℝ) * q ^ (k + 2) := by
    have hsTail : Summable (fun k : ℕ =>
        (65 + 2 * ((k + 2 : ℕ) : ℝ)) * q ^ (k + 2) / (k + 2).factorial) := by
      simpa only using (summable_nat_add_iff 2).2 hs
    apply Summable.tsum_le_tsum
    · intro k
      have hcoef : (65 + 2 * ((k + 2 : ℕ) : ℝ)) ≤ 35 * (k + 2).factorial := by
        exact_mod_cast affine_le_thirty_five_mul_factorial (l := k + 2) (by omega)
      have hfact : (0 : ℝ) < (k + 2).factorial := by positivity
      calc
        (65 + 2 * ((k + 2 : ℕ) : ℝ)) * q ^ (k + 2) / (k + 2).factorial ≤
            (35 * (k + 2).factorial) * q ^ (k + 2) / (k + 2).factorial := by
          gcongr
        _ = 35 * q ^ (k + 2) := by field_simp
    · exact hsTail
    · exact htailGeom
  calc
    (∑ l ∈ Finset.range 2, (65 + 2 * l : ℝ) * q ^ l / l.factorial) +
        ∑' k : ℕ, (65 + 2 * ((k + 2 : ℕ) : ℝ)) * q ^ (k + 2) /
          (k + 2).factorial ≤
        65 + 67 * q + ∑' k : ℕ, (35 : ℝ) * q ^ (k + 2) := by
      convert add_le_add_left htail (65 + 67 * q) using 1 <;>
        norm_num [sum_range_succ] <;> ring
    _ = 65 + 67 * q + 35 * q ^ 2 / (1 - q) := by
      rw [show (∑' k : ℕ, (35 : ℝ) * q ^ (k + 2)) =
          35 * q ^ 2 * ∑' k : ℕ, q ^ k by
            rw [← tsum_mul_left]
            apply tsum_congr
            intro k
            rw [pow_add]
            ring,
        tsum_geometric_of_norm_lt_one (by simpa [norm_eq_abs] using habs)]
      field_simp
    _ ≤ 72 := by
      have hmono : 0 ≤ ((11 / 112 : ℝ) - q) *
          (74 - 32 * ((11 / 112 : ℝ) + q)) := by
        apply mul_nonneg
        · linarith
        · nlinarith
      have hdiv : 35 * q ^ 2 / (1 - q) ≤ 72 - (65 + 67 * q) := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      linarith

theorem abs_oddSineSum_le_seventy_two_sqrt
    {n : ℕ} (hn : 0 < n) (a : ℕ → ℝ) (x θ : ℝ)
    (hnear : |θ - x| ≤ π / (64 * n))
    (hdisc : ∀ l : ℕ,
      |oddSinDeriv l n a x| ≤
        (65 + 2 * l) * sqrt n * (2 * n : ℝ) ^ l) :
    |oddSineSum n a θ| ≤ 72 * sqrt n := by
  let h : ℝ := θ - x
  have hθ : x + h = θ := by dsimp [h]; ring
  have hq0 : 0 ≤ |h| * (2 * n : ℝ) := mul_nonneg (abs_nonneg _) (by positivity)
  have hpi : π < 22 / 7 := by
    exact lt_of_lt_of_le Real.pi_lt_d20 (by norm_num)
  have hq : |h| * (2 * n : ℝ) ≤ 11 / 112 := by
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
    have hnear' : |h| ≤ π / (64 * n) := hnear
    calc
      |h| * (2 * n : ℝ) ≤ (π / (64 * n)) * (2 * n) := by
        gcongr
      _ = π / 32 := by field_simp; ring
      _ ≤ 11 / 112 := by linarith
  have htaylor := hasSum_oddSinDeriv_taylor n a x h
  let q : ℝ := |h| * (2 * n : ℝ)
  have hqdef : q = |h| * (2 * n : ℝ) := rfl
  have haff : Summable
      (fun l : ℕ => (65 + 2 * l : ℝ) * q ^ l / l.factorial) :=
    summable_affine_factorial (q := q) (hqdef ▸ hq0)
      (lt_of_le_of_lt (hqdef ▸ hq) (by norm_num : (11 / 112 : ℝ) < 1))
  have hbSummable : Summable (fun l : ℕ =>
      ((65 + 2 * l) * sqrt n * (2 * n : ℝ) ^ l) *
        |h| ^ l / l.factorial) := by
    refine (haff.mul_left (sqrt n)).congr (fun l => ?_)
    rw [hqdef, mul_pow]
    ring
  have hTaylorBound := htaylor.norm_le_of_bounded hbSummable.hasSum (fun l => by
    have hfacabs : |(l.factorial : ℝ)| = (l.factorial : ℝ) :=
      abs_of_nonneg (Nat.cast_nonneg _)
    rw [norm_eq_abs, abs_div, abs_mul, abs_pow, hfacabs]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hdisc l) (by positivity)) (by positivity))
  rw [norm_eq_abs, oddSinDeriv_zero, hθ] at hTaylorBound
  calc
    |oddSineSum n a θ| ≤ ∑' l : ℕ,
        ((65 + 2 * l) * sqrt n * (2 * n : ℝ) ^ l) *
          |h| ^ l / l.factorial := hTaylorBound
    _ = sqrt n *
        (∑' l : ℕ, (65 + 2 * l : ℝ) * q ^ l / l.factorial) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro l
      rw [hqdef]
      rw [mul_pow]
      ring
    _ ≤ sqrt n * 72 := by
      exact mul_le_mul_of_nonneg_left
        (tsum_affine_factorial_le_seventy_two (q := q) (hqdef ▸ hq0) (hqdef ▸ hq))
        (sqrt_nonneg n)
    _ = 72 * sqrt n := by ring

end

end Rounding

end

open Rounding


section

namespace OddSine

open scoped BigOperators Interval
open Set

noncomputable section

def K : ℝ := 2 ^ 7

@[simp] theorem K_eq : K = 128 := by norm_num [K]

abbrev RealIvl := ℝ × ℝ

def InIvl (I : RealIvl) (θ : ℝ) : Prop :=
  θ ∈ Icc I.1 I.2

structure IvlFam (n : ℕ) where
  base : Finset RealIvl
  ordered : ∀ I ∈ base, I.1 ≤ I.2

  nondegenerate : ∀ I ∈ base, I.1 < I.2
  in_first_quadrant : ∀ I ∈ base, 0 ≤ I.1 ∧ I.2 ≤ π / 2
  grid_endpoints : ∀ I ∈ base, ∃ a b : ℤ,
    I.1 = (a : ℝ) * π / n ∧ I.2 = (b : ℝ) * π / n
  short : ∀ I ∈ base, I.2 - I.1 ≤ 6 * π / n
  separated : Set.Pairwise ((↑base : Set RealIvl))
    (fun I J ↦ ∀ x ∈ Icc I.1 I.2, ∀ y ∈ Icc J.1 J.2,
      π / n ≤ |x - y|)
  away_from_axes : ∀ I ∈ base,
    100 * π / n ≤ I.1 ∧ I.2 ≤ π / 2 - 100 * π / n

def IsDangerous {n : ℕ} (F : IvlFam n) (θ : ℝ) : Prop :=
  ∃ I ∈ F.base,
    InIvl I θ ∨ InIvl I (-θ) ∨
      InIvl I (π - θ) ∨ InIvl I (θ - π)

def firstVec {n : ℕ} (F : IvlFam n) (j : Fin n) :
    ↥F.base → ℝ :=
  fun I ↦ 4 * K * sqrt n *
    ∫ θ in I.1.1..I.1.2,
      sin ((oddFreq j : ℝ) * θ)

theorem norm_firstVec_le {n : ℕ} (hn : 0 < n)
    (F : IvlFam n) (j : Fin n) :
    ‖firstVec F j‖ ≤
      24 * K * π * sqrt n / n := by
  rw [pi_norm_le_iff_of_nonneg]
  · intro I
    rw [norm_eq_abs]
    simp only [firstVec, abs_mul]
    have hintegral :
        ‖∫ θ in I.1.1..I.1.2,
            sin ((oddFreq j : ℝ) * θ)‖ ≤
          I.1.2 - I.1.1 := by
      have h := norm_integral_le_of_norm_le_const
        (a := I.1.1) (b := I.1.2) (C := (1 : ℝ))
        (f := fun θ : ℝ ↦
          sin ((oddFreq j : ℝ) * θ))
        (fun θ hθ ↦ by
          simpa [norm_eq_abs] using
            abs_sin_le_one
              ((oddFreq j : ℝ) * θ))
      simpa [abs_of_nonneg (sub_nonneg.2 (F.ordered I I.2))] using h
    have hwidth := F.short I I.2
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hK : (0 : ℝ) ≤ K := by norm_num [K]
    have hcoefficient : 0 ≤ 4 * K * sqrt n := by positivity
    calc
      |4| * |K| * |sqrt ↑n| *
          |∫ θ in I.1.1..I.1.2,
            sin ((oddFreq ↑j : ℝ) * θ)| ≤
          (4 * K * sqrt n) * (I.1.2 - I.1.1) := by
            rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
              abs_of_nonneg (by norm_num [K] : (0 : ℝ) ≤ K),
              abs_of_nonneg (sqrt_nonneg _)]
            exact mul_le_mul_of_nonneg_left hintegral hcoefficient
      _ ≤ (4 * K * sqrt n) * (6 * π / n) := by
            exact mul_le_mul_of_nonneg_left hwidth hcoefficient
      _ = 24 * K * π * sqrt n / n := by ring
  · have hK : (0 : ℝ) ≤ K := by norm_num [K]
    positivity

def fourierTarget {n : ℕ} (F : IvlFam n)
    (α : ↥F.base → ℝ) (j : ℕ) : ℝ :=
  if _hj : j < n then
    ∑ I : ↥F.base,
      α I * (4 * K * sqrt n *
        ∫ θ in I.1.1..I.1.2,
          sin ((oddFreq j : ℝ) * θ))
  else 0

theorem fourierTarget_eq_dot {n : ℕ} (F : IvlFam n)
    (α : ↥F.base → ℝ) (j : Fin n) :
    fourierTarget F α j = dot α (firstVec F j) := by
  simp [fourierTarget, firstVec, dot, j.isLt]

def targetSine {n : ℕ} (F : IvlFam n)
    (α : ↥F.base → ℝ) (θ : ℝ) : ℝ :=
  oddSineSum n (fourierTarget F α) θ

structure FirstColoringAdm {n : ℕ}
    (F : IvlFam n) (c : Fin n → ℝ) : Prop where
  parameter_nonneg : ∀ j, 0 ≤ c j
  budget : (∑ j, Real.exp (-(c j) ^ 2 / 196)) ≤
    (Fintype.card ↥F.base : ℝ) / 16
  unit_error : ∀ j,
    (c j + 30) * sqrt (Fintype.card ↥F.base) *
      ‖firstVec F j‖ ≤ 1

theorem firstColoringAdm_of_numeric {n : ℕ} (hn : 0 < n)
    (F : IvlFam n) (c : Fin n → ℝ)
    (hc : ∀ j, 0 ≤ c j)
    (hbudget : (∑ j, Real.exp (-(c j) ^ 2 / 196)) ≤
      (Fintype.card ↥F.base : ℝ) / 16)
    (hscalar : ∀ j,
      (c j + 30) * sqrt (Fintype.card ↥F.base) *
        (24 * K * π * sqrt n / n) ≤ 1) :
    FirstColoringAdm F c := by
  refine ⟨hc, hbudget, ?_⟩
  intro j
  have hleft : 0 ≤
      (c j + 30) * sqrt (Fintype.card ↥F.base) :=
    mul_nonneg (by linarith [hc j]) (sqrt_nonneg _)
  exact (mul_le_mul_of_nonneg_left (norm_firstVec_le hn F j) hleft).trans
    (hscalar j)

theorem exists_ivlColoring {n : ℕ} (F : IvlFam n)
    (c : Fin n → ℝ) (hc : FirstColoringAdm F c)
    (hLM : ∀ (I : Type) [Fintype I] [DecidableEq I],
      PartialColoringPrinciple I (Fin n)) :
    ∃ α : ↥F.base → ℝ,
      Disc.IsSign α ∧ ∀ j < n, |fourierTarget F α j| ≤ 1 := by
  classical
  have hzero : InCube (0 : ↥F.base → ℝ) := by
    intro I
    simp
  obtain ⟨α, hα, herror⟩ :=
    hasFullColoring_of_partialColoringPrinciple hLM
      (firstVec F) (0 : ↥F.base → ℝ) c hzero
      hc.parameter_nonneg hc.budget
  refine ⟨α, hα, ?_⟩
  intro j hj
  let jf : Fin n := ⟨j, hj⟩
  rw [fourierTarget_eq_dot F α jf]
  simpa [jf] using (herror jf).trans (hc.unit_error jf)

structure KernelCert {n : ℕ} (F : IvlFam n)
    (α : ↥F.base → ℝ) where
  main : ℝ → ℝ
  error : ℝ → ℝ
  decomposition : ∀ θ,
    targetSine F α θ =
      (K * sqrt n) * (main θ + error θ)
  main_lower : ∀ θ, IsDangerous F θ → 4 / 3 ≤ |main θ|
  main_upper : ∀ θ, |main θ| ≤ 4
  error_bound : ∀ θ, |error θ| ≤ 2 / 3

theorem targetSine_kernel_bounds {n : ℕ} (_hn : 0 < n)
    (F : IvlFam n) (α : ↥F.base → ℝ)
    (hkernel : KernelCert F α) :
    (∀ θ, IsDangerous F θ →
      (2 * K / 3) * sqrt n ≤ |targetSine F α θ|) ∧
    (∀ θ, |targetSine F α θ| ≤ 5 * K * sqrt n) := by
  constructor
  · intro θ hθ
    have hnormalized := norm_kernel_bounds
      (value := hkernel.main θ + hkernel.error θ)
      (main := hkernel.main θ) (error := hkernel.error θ)
      (hvalue := (rfl : hkernel.main θ + hkernel.error θ =
        hkernel.main θ + hkernel.error θ))
      (hmain_lower := hkernel.main_lower θ hθ)
      (hmain_upper := hkernel.main_upper θ)
      (herror := hkernel.error_bound θ)
    rw [hkernel.decomposition θ, abs_mul]
    have hK : 0 ≤ K := by norm_num [K]
    have hfactor : 0 ≤ K * sqrt n := mul_nonneg hK
      (sqrt_nonneg _)
    rw [abs_of_nonneg hfactor]
    calc
      (2 * K / 3) * sqrt n = (K * sqrt n) * (2 / 3) := by ring
      _ ≤ (K * sqrt n) * |hkernel.main θ + hkernel.error θ| :=
        mul_le_mul_of_nonneg_left hnormalized.1 hfactor
  · intro θ
    have hnormalized : |hkernel.main θ + hkernel.error θ| ≤ 5 := by
      calc
        |hkernel.main θ + hkernel.error θ| ≤
            |hkernel.main θ| + |hkernel.error θ| := abs_add_le _ _
        _ ≤ 4 + 2 / 3 :=
          add_le_add (hkernel.main_upper θ) (hkernel.error_bound θ)
        _ ≤ 5 := by norm_num
    rw [hkernel.decomposition θ, abs_mul]
    have hK : 0 ≤ K := by norm_num [K]
    have hfactor : 0 ≤ K * sqrt n := mul_nonneg hK
      (sqrt_nonneg _)
    rw [abs_of_nonneg hfactor]
    calc
      (K * sqrt n) * |hkernel.main θ + hkernel.error θ|
          ≤ (K * sqrt n) * 5 :=
        mul_le_mul_of_nonneg_left hnormalized hfactor
      _ = 5 * K * sqrt n := by ring

def derivVec (n l : ℕ) (θ : ℝ) : Fin n → ℝ :=
  fun j ↦
    ((((((oddFreq j : ℝ) : ℂ) * Complex.I) ^ l) *
      Complex.exp ((((oddFreq j : ℝ) * θ : ℝ) : ℂ) *
        Complex.I))).im

structure RoundingSetup (n : ℕ) (G : Type) [Fintype G] where
  point : G → ℝ
  parameter : G × Fin n → ℝ
  parameter_nonneg : ∀ q, 0 ≤ parameter q
  budget : (∑ q, Real.exp (-(parameter q) ^ 2 / 196)) ≤ (n : ℝ) / 16
  parameter_bound : ∀ g l, parameter (g, l) + 30 ≤ 65 + 2 * (l : ℕ)
  cover : ∀ (a : ℕ → ℝ) (θ : ℝ), ∃ g θ',
    |θ' - point g| ≤ π / (64 * n) ∧
      |oddSineSum n a θ| =
        |oddSineSum n a θ'|

theorem oddSinDeriv_eq_dot (n l : ℕ) (a : ℕ → ℝ) (θ : ℝ) :
    oddSinDeriv l n a θ =
      dot (fun j : Fin n ↦ a j)
        (derivVec n l θ) := by
  classical
  simp only [oddSinDeriv,
    oddExpDeriv,
    derivVec, dot]
  change imLm
      (∑ j ∈ Finset.range n, (a j : ℂ) *
        (((oddFreq j : ℝ) : ℂ) * Complex.I) ^ l *
          Complex.exp ((((oddFreq j : ℝ) * θ : ℝ) : ℂ) *
            Complex.I)) = _
  rw [map_sum imLm]
  change (∑ j ∈ Finset.range n,
    ((a j : ℂ) *
      (((oddFreq j : ℝ) : ℂ) * Complex.I) ^ l *
        Complex.exp ((((oddFreq j : ℝ) * θ : ℝ) : ℂ) *
          Complex.I)).im) = _
  rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ ↦
    ((a j : ℂ) *
      (((oddFreq j : ℝ) : ℂ) * Complex.I) ^ l *
        Complex.exp ((((oddFreq j : ℝ) * θ : ℝ) : ℂ) *
          Complex.I)).im) n]
  apply sum_congr rfl
  intro j hj
  rw [mul_assoc, mul_im]
  simp

theorem norm_derivVec_le {n l : ℕ} (θ : ℝ) :
    ‖derivVec n l θ‖ ≤ (2 * n : ℝ) ^ l := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro j
  rw [norm_eq_abs]
  have him := abs_im_le_norm
    ((((((oddFreq j : ℝ) : ℂ) * Complex.I) ^ l) *
      Complex.exp ((((oddFreq j : ℝ) * θ : ℝ) : ℂ) *
        Complex.I)))
  change |((((((oddFreq j : ℝ) : ℂ) * Complex.I) ^ l) *
      Complex.exp ((((oddFreq j : ℝ) * θ : ℝ) : ℂ) *
        Complex.I))).im| ≤ _
  refine him.trans ?_
  simp only [norm_mul, norm_pow, norm_I, mul_one,
      norm_exp_ofReal_mul_I]
  rw [Complex.norm_real, norm_eq_abs, abs_of_nonneg (by positivity)]
  have hfreq : (oddFreq j : ℝ) ≤ 2 * n := by
    exact_mod_cast oddFreq_le_two_mul
      (Finset.mem_range.2 j.isLt)
  exact pow_le_pow_left₀ (by positivity) hfreq l

theorem oddSineSum_sub (n : ℕ) (a b : ℕ → ℝ) (θ : ℝ) :
    oddSineSum n (a - b) θ =
      oddSineSum n a θ -
        oddSineSum n b θ := by
  classical
  simp only [oddSineSum, Pi.sub_apply, sub_mul,
    sum_sub_distrib]

theorem oddSineSum_neg (n : ℕ) (a : ℕ → ℝ) (θ : ℝ) :
    oddSineSum n a (-θ) =
      -oddSineSum n a θ := by
  classical
  simp [oddSineSum, mul_neg]

theorem oddSineSum_pi_sub (n : ℕ) (a : ℕ → ℝ) (θ : ℝ) :
    oddSineSum n a (π - θ) =
      oddSineSum n a θ := by
  classical
  simp only [oddSineSum]
  apply sum_congr rfl
  intro j hj
  congr 1
  rw [mul_sub]
  have hrewrite :
      (oddFreq j : ℝ) * π -
          (oddFreq j : ℝ) * θ =
        (oddFreq j : ℕ) * π -
          (oddFreq j : ℝ) * θ := by
    norm_num
  rw [hrewrite, Real.sin_nat_mul_pi_sub]
  simp [oddFreq, pow_add]

theorem oddSineSum_add_pi (n : ℕ) (a : ℕ → ℝ) (θ : ℝ) :
    oddSineSum n a (θ + π) =
      -oddSineSum n a θ := by
  classical
  simp only [oddSineSum, mul_add]
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro j hj
  rw [show (oddFreq j : ℝ) * θ +
      (oddFreq j : ℝ) * π =
      (oddFreq j : ℝ) * θ +
        (oddFreq j : ℕ) * π by norm_num,
    Real.sin_add_nat_mul_pi]
  simp [oddFreq, pow_add]

theorem exists_firstQuad_abs_oddSinSum_eq
    (n : ℕ) (a : ℕ → ℝ) (θ : ℝ) :
    ∃ θ' ∈ Icc 0 (π / 2),
      |oddSineSum n a θ| =
        |oddSineSum n a θ'| := by
  let x := toIcoMod pi_pos 0 θ
  have hxmem : x ∈ Ico (0 : ℝ) π := by
    simpa [x] using toIcoMod_mem_Ico pi_pos 0 θ
  have hperiodic : Function.Periodic
      (fun y : ℝ ↦ |oddSineSum n a y|) π := by
    intro y
    change |oddSineSum n a (y + π)| =
      |oddSineSum n a y|
    rw [oddSineSum_add_pi n a y, abs_neg]
  have hreduce : |oddSineSum n a θ| =
      |oddSineSum n a x| := by
    have heq := toIcoMod_add_toIcoDiv_zsmul pi_pos 0 θ
    rw [← heq]
    exact hperiodic.zsmul (toIcoDiv pi_pos 0 θ) x
  by_cases hx : x ≤ π / 2
  · exact ⟨x, ⟨show (0 : ℝ) ≤ x from hxmem.1, hx⟩, hreduce⟩
  · refine ⟨π - x, ?_, ?_⟩
    · constructor
      · linarith [hxmem.2]
      · linarith
    · rw [hreduce, oddSineSum_pi_sub]

theorem exists_rounding {n : ℕ} (hn : 0 < n) {G : Type} [Fintype G]
    [DecidableEq G] (setup : RoundingSetup n G) (hat : ℕ → ℝ)
    (hhat : ∀ j < n, |hat j| ≤ 1)
    (hLM : ∀ (I : Type) [Fintype I] [DecidableEq I],
      PartialColoringPrinciple I (G × Fin n)) :
    ∃ eps : ℕ → ℝ, (∀ j, eps j = 1 ∨ eps j = -1) ∧
      ∀ θ,
        |oddSineSum n eps θ -
          oddSineSum n hat θ| ≤
          72 * sqrt n := by
  classical
  let x₀ : Fin n → ℝ := fun j ↦ hat j
  let v : G × Fin n → Fin n → ℝ :=
    fun q ↦ derivVec n q.2 (setup.point q.1)
  have hx₀ : InCube x₀ := by
    intro j
    exact hhat j j.isLt
  have hbudget : (∑ q, Real.exp (-(setup.parameter q) ^ 2 / 196)) ≤
      (Fintype.card (Fin n) : ℝ) / 16 := by
    simpa using setup.budget
  obtain ⟨epsFin, hepsSign, hepsDisc⟩ :=
    hasFullColoring_of_partialColoringPrinciple
      hLM v x₀ setup.parameter
      hx₀ setup.parameter_nonneg hbudget
  let eps : ℕ → ℝ := fun j ↦ if hj : j < n then epsFin ⟨j, hj⟩ else 1
  refine ⟨eps, ?_, ?_⟩
  · intro j
    by_cases hj : j < n
    · simpa [eps, hj] using hepsSign ⟨j, hj⟩
    · simp [eps, hj]
  · intro θ
    let a : ℕ → ℝ := eps - hat
    obtain ⟨g, θ', hnear, habs⟩ := setup.cover a θ
    have hdisc : ∀ l : ℕ,
        |oddSinDeriv l n a (setup.point g)| ≤
          (65 + 2 * l) * sqrt n * (2 * n : ℝ) ^ l := by
      intro l
      by_cases hl : l < n
      · let lf : Fin n := ⟨l, hl⟩
        have hfull := hepsDisc (g, lf)
        have hdot : dot (epsFin - x₀) (v (g, lf)) =
            oddSinDeriv l n a (setup.point g) := by
          rw [oddSinDeriv_eq_dot]
          apply congrArg (fun z : Fin n → ℝ ↦
            dot z (derivVec n l (setup.point g)))
          funext j
          simp [a, eps, x₀, j.isLt]
        rw [← hdot]
        calc
          |dot (epsFin - x₀) (v (g, lf))| ≤
              (setup.parameter (g, lf) + 30) * sqrt n *
                ‖v (g, lf)‖ := by simpa [v] using hfull
          _ ≤ (65 + 2 * l) * sqrt n * (2 * n : ℝ) ^ l := by
            apply mul_le_mul
            · apply mul_le_mul_of_nonneg_right (setup.parameter_bound g lf)
                (sqrt_nonneg _)
            · simpa [v, lf] using
                (norm_derivVec_le (n := n) (l := l) (setup.point g))
            · exact norm_nonneg _
            · exact mul_nonneg (by linarith [setup.parameter_nonneg (g, lf)])
                (sqrt_nonneg _)
      · have hcoeff : ∀ j < n, |a j| ≤ 2 := by
          intro j hj
          have heps : |eps j| = 1 := by
            rcases (show eps j = 1 ∨ eps j = -1 by
              simp only [eps, dif_pos hj]
              exact hepsSign ⟨j, hj⟩) with h | h <;> simp [h]
          calc
            |a j| = |eps j - hat j| := rfl
            _ ≤ |eps j| + |hat j| := abs_sub _ _
            _ ≤ 2 := by linarith [hhat j hj]
        have htrivial :=
          abs_oddSinDeriv_le_card_mul l n a 2 hcoeff
          (by norm_num) (setup.point g)
        have hsqrt : 1 ≤ sqrt n := by
          rw [one_le_sqrt]
          exact_mod_cast hn
        have hln : n ≤ l := Nat.le_of_not_gt hl
        calc
          |oddSinDeriv l n a (setup.point g)| ≤
              n * 2 * (2 * n : ℝ) ^ l := htrivial
          _ ≤ (65 + 2 * l) * sqrt n * (2 * n : ℝ) ^ l := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have : (n : ℝ) ≤ l := by exact_mod_cast hln
            nlinarith
    have hround := abs_oddSineSum_le_seventy_two_sqrt hn a
      (setup.point g) θ' hnear hdisc
    rw [← oddSineSum_sub] at ⊢
    rw [habs]
    exact hround

end

end OddSine

end

open OddSine


section

namespace CosConstr

open Set
open scoped BigOperators

noncomputable section

def paramNum (t : ℕ) : ℕ := 2 ^ (t + 11) + 2 ^ t - 1

def cosDelta (γ : ℝ) : ℝ :=
  (1 / 2 ^ 8 : ℝ) * γ ^ 3 * sqrt γ

def thr (n : ℕ) (γ : ℝ) : ℝ :=
  cosDelta γ * sqrt n

structure Params (n t : ℕ) (γ : ℝ) : Prop where
  n_pos : 0 < n
  t_odd : Odd t
  equation : γ * n = paramNum t
  gamma_lower : (1 / 2 ^ 43 : ℝ) < γ
  gamma_upper : γ ≤ (1 / 2 ^ 40 : ℝ)

theorem Params.gamma_pos {n t : ℕ} {γ : ℝ}
    (h : Params n t γ) : 0 < γ :=
  lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / 2 ^ 43) h.gamma_lower.le

theorem cosDelta_pos {γ : ℝ} (hγ : 0 < γ) :
    0 < cosDelta γ := by
  simp only [cosDelta]
  positivity

theorem thr_pos {n : ℕ} {γ : ℝ}
    (hn : 0 < n) (hγ : 0 < γ) : 0 < thr n γ := by
  simp only [thr]
  exact mul_pos (cosDelta_pos hγ) (sqrt_pos.2 (by exact_mod_cast hn))

theorem Params.toEvenParams {n t : ℕ} {γ : ℝ}
    (h : Params n t γ) : EvenParams n t γ where
  t_odd := h.t_odd
  gamma_pos := h.gamma_pos
  gamma_le := h.gamma_upper
  equation := by simpa [paramNum, gammaNum] using h.equation

theorem Params.eta_pos {n t : ℕ} {γ : ℝ}
    (h : Params n t γ) :
    0 < 2 * (evenT t : ℝ) * π / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast h.n_pos
  have hTR : (0 : ℝ) < evenT t := by
    exact_mod_cast (show 0 < evenT t by simp [evenT])
  exact div_pos (mul_pos (mul_pos (by norm_num) hTR) pi_pos) hnR

theorem Params.eta_lt {n t : ℕ} {γ : ℝ}
    (h : Params n t γ) :
    2 * (evenT t : ℝ) * π / n < 1 / 2048 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast h.n_pos
  have hTle : (2 * evenT t : ℝ) ≤ γ * n := by
    rw [h.equation]
    exact_mod_cast (show 2 * evenT t ≤ paramNum t by
      rw [paramNum, two_mul_evenT]
      have hp : 0 < 2 ^ t := by positivity
      omega)
  have hpi : π < 4 := pi_lt_four
  have hgam : γ ≤ 1 / 2 ^ 40 := h.gamma_upper
  have hγ : 0 < γ := h.gamma_pos
  calc
    2 * (evenT t : ℝ) * π / n ≤
        (γ * n) * π / n := by
      gcongr
    _ = γ * π := by field_simp
    _ < γ * 4 := by gcongr
    _ ≤ (1 / 2 ^ 40 : ℝ) * 4 := by gcongr
    _ < 1 / 2048 := by norm_num

theorem Params.ratio_lo {n t : ℕ} {γ : ℝ}
    (h : Params n t γ) :
    (15 / 16 : ℝ) * (γ * n) < 2 * evenT t := by
  rw [h.equation]
  have hnat : 15 * paramNum t < 16 * (2 * evenT t) := by
    rw [paramNum, evenT]
    have hp : 0 < 2 ^ t := by positivity
    rw [show 2 ^ (t + 11) = 2 ^ t * 2 ^ 11 by rw [pow_add],
      show 2 ^ (t + 10) = 2 ^ t * 2 ^ 10 by rw [pow_add]]
    norm_num
    omega
  have hreal : (15 : ℝ) * paramNum t < 16 * (2 * evenT t) := by
    exact_mod_cast hnat
  norm_num at hreal ⊢
  nlinarith

private theorem sqrt_two_mul_evenT (t : ℕ) :
    sqrt (2 * (evenT t : ℝ)) =
      32 * sqrt (2 ^ (t + 1) : ℝ) := by
  have hpow : (2 * (evenT t : ℝ)) = (2 ^ (t + 1) : ℝ) * 32 ^ 2 := by
    norm_num [evenT, pow_add]
    ring
  rw [hpow, sqrt_mul (by positivity : (0 : ℝ) ≤ 2 ^ (t + 1)),
    sqrt_sq_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 32)]
  ring

theorem Params.thr_le_norm_good {n t : ℕ} {γ : ℝ}
    (h : Params n t γ) :
    thr n γ ≤
      sqrt (2 ^ (t + 1) : ℝ) *
        (2 * (evenT t : ℝ) * π / n) ^ 3 / 128 := by
  let A : ℝ := γ * n
  let B : ℝ := 2 * evenT t
  have hnR : (0 : ℝ) < n := by exact_mod_cast h.n_pos
  have hγ : 0 < γ := h.gamma_pos
  have hA : 0 < A := mul_pos hγ hnR
  have hB : 0 < B := by
    dsimp [B]
    have hT : (0 : ℝ) < evenT t := by
      exact_mod_cast (show 0 < evenT t by simp [evenT])
    positivity
  have hratio : (15 / 16 : ℝ) * A < B := by
    simpa [A, B] using h.ratio_lo
  have hratioSq : (15 / 16 : ℝ) ^ 2 * A < B := by
    have : (15 / 16 : ℝ) ^ 2 < 15 / 16 := by norm_num
    nlinarith
  have hsqrtRatio : (15 / 16 : ℝ) * sqrt A < sqrt B := by
    have hsA : 0 ≤ sqrt A := sqrt_nonneg _
    have hsB : 0 ≤ sqrt B := sqrt_nonneg _
    have hsA2 : (sqrt A) ^ 2 = A := sq_sqrt hA.le
    have hsB2 : (sqrt B) ^ 2 = B := sq_sqrt hB.le
    nlinarith
  have hcubes : (15 / 16 : ℝ) ^ 3 * A ^ 3 < B ^ 3 := by
    have hp := pow_lt_pow_left₀ hratio
      (mul_nonneg (by norm_num) hA.le) (by norm_num : (3 : ℕ) ≠ 0)
    simpa only [mul_pow] using hp
  have hprod : (15 / 16 : ℝ) ^ 4 * (A ^ 3 * sqrt A) <
      B ^ 3 * sqrt B := by
    have hsApos : 0 < sqrt A := sqrt_pos.2 hA
    have hrpos : (0 : ℝ) < 15 / 16 := by norm_num
    have hm := mul_lt_mul hcubes hsqrtRatio.le
      (mul_pos hrpos hsApos) (pow_nonneg hB.le 3)
    calc
      (15 / 16 : ℝ) ^ 4 * (A ^ 3 * sqrt A) =
          ((15 / 16 : ℝ) ^ 3 * A ^ 3) *
            ((15 / 16 : ℝ) * sqrt A) := by ring
      _ < B ^ 3 * sqrt B := hm
  have hnumeric : (16 : ℝ) < 3 ^ 3 * (15 / 16 : ℝ) ^ 4 := by norm_num
  have hpiCube : (3 : ℝ) ^ 3 < π ^ 3 := by
    nlinarith [Real.pi_gt_three, sq_nonneg (π - 3)]
  have hmain : 16 * (A ^ 3 * sqrt A) <
      π ^ 3 * (B ^ 3 * sqrt B) := by
    have hAprodpos : 0 < A ^ 3 * sqrt A :=
      mul_pos (pow_pos hA 3) (sqrt_pos.2 hA)
    have hrprodpos : 0 < (15 / 16 : ℝ) ^ 4 * (A ^ 3 * sqrt A) := by
      positivity
    have hpiCubePos : 0 < π ^ 3 := pow_pos pi_pos 3
    calc
      16 * (A ^ 3 * sqrt A) <
          (3 ^ 3 * (15 / 16 : ℝ) ^ 4) * (A ^ 3 * sqrt A) := by
        exact mul_lt_mul_of_pos_right hnumeric hAprodpos
      _ = 3 ^ 3 * ((15 / 16 : ℝ) ^ 4 * (A ^ 3 * sqrt A)) := by ring
      _ < π ^ 3 * ((15 / 16 : ℝ) ^ 4 * (A ^ 3 * sqrt A)) :=
        mul_lt_mul_of_pos_right hpiCube hrprodpos
      _ < π ^ 3 * (B ^ 3 * sqrt B) :=
        mul_lt_mul_of_pos_left hprod hpiCubePos
  have hsqrtA : sqrt A = sqrt γ * sqrt n := by
    dsimp [A]
    rw [sqrt_mul (le_of_lt hγ)]
  have hsqrtB : sqrt B = 32 * sqrt (2 ^ (t + 1) : ℝ) := by
    simpa [B] using sqrt_two_mul_evenT t
  have hscaled :
      (1 / 256 : ℝ) * γ ^ 3 * sqrt γ * sqrt n <
        sqrt (2 ^ (t + 1) : ℝ) *
          (B * π / n) ^ 3 / 128 := by
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
    have hlhs :
        (1 / 256 : ℝ) * γ ^ 3 * sqrt γ * sqrt n =
          (16 * (A ^ 3 * sqrt A)) / (4096 * n ^ 3) := by
      calc
        (1 / 256 : ℝ) * γ ^ 3 * sqrt γ * sqrt n =
            (1 / 256 : ℝ) * γ ^ 3 *
              (sqrt γ * sqrt n) := by ring
        _ = (1 / 256 : ℝ) * γ ^ 3 * sqrt A := by rw [← hsqrtA]
        _ = (16 * (A ^ 3 * sqrt A)) / (4096 * n ^ 3) := by
          dsimp [A]
          field_simp [hn0]
          ring
    have hs : sqrt (2 ^ (t + 1) : ℝ) = sqrt B / 32 := by
      rw [hsqrtB]
      ring
    have hrhs :
        sqrt (2 ^ (t + 1) : ℝ) * (B * π / n) ^ 3 / 128 =
          (π ^ 3 * (B ^ 3 * sqrt B)) / (4096 * n ^ 3) := by
      rw [hs]
      field_simp [hn0]
      ring
    rw [hlhs, hrhs]
    exact div_lt_div_of_pos_right hmain (by positivity)
  norm_num [thr, cosDelta, B] at hscaled ⊢
  exact hscaled.le

def rsNormalization (t : ℕ) : ℝ := (sqrt (2 ^ (t + 1) : ℝ))⁻¹

def scDerivP (r t : ℕ) (x : ℝ) : ℂ :=
  (rsNormalization t : ℂ) *
    (Complex.I / (evenT t : ℝ)) ^ r *
      ((eulerDeriv^[r]) (rudinShapiroP t)).eval
        (unitPt (x / evenT t))

def scDerivQ (r t : ℕ) (x : ℝ) : ℂ :=
  (rsNormalization t : ℂ) *
    (Complex.I / (evenT t : ℝ)) ^ r *
      ((eulerDeriv^[r]) (rudinShapiroQ t)).eval
        (unitPt (x / evenT t))

def normH (t : ℕ) (x : ℝ) : ℂ :=
  unitPt x * scDerivP 0 t x +
    unitPt (2 * x) * scDerivQ 0 t x

theorem rsNormalization_pos (t : ℕ) : 0 < rsNormalization t := by
  simp only [rsNormalization]
  positivity

theorem norm_energy (t : ℕ) (x : ℝ) :
    ‖scDerivP 0 t x‖ ^ 2 +
      ‖scDerivQ 0 t x‖ ^ 2 = 1 := by
  have henergy := rs_energy t (norm_unitPt (x / evenT t))
  have hEpos : (0 : ℝ) < (2 ^ (t + 1) : ℝ) := by positivity
  have hspos : 0 < sqrt (2 ^ (t + 1) : ℝ) := sqrt_pos.2 hEpos
  have hsquare := sq_sqrt hEpos.le
  simp only [scDerivP, scDerivQ, pow_zero, one_mul,
    Function.iterate_zero_apply, norm_one, norm_mul, Complex.norm_real, norm_eq_abs,
    abs_of_pos (rsNormalization_pos t)]
  rw [show
    (rsNormalization t * 1 * ‖(rudinShapiroP t).eval (unitPt (x / evenT t))‖) ^ 2 +
      (rsNormalization t * 1 * ‖(rudinShapiroQ t).eval (unitPt (x / evenT t))‖) ^ 2 =
      rsNormalization t ^ 2 *
        (‖(rudinShapiroP t).eval (unitPt (x / evenT t))‖ ^ 2 +
          ‖(rudinShapiroQ t).eval (unitPt (x / evenT t))‖ ^ 2) by ring,
    henergy]
  simp only [rsNormalization]
  field_simp
  exact hsquare.symm

private theorem normDeriv_bound
    (p : Polynomial ℂ) (t r : ℕ) (x : ℝ)
    (hdeg : p.natDegree ≤ 2 ^ t)
    (hcircle : ∀ z : ℂ, ‖z‖ = 1 →
      ‖p.eval z‖ ≤ sqrt (2 ^ (t + 1) : ℝ)) :
    ‖(rsNormalization t : ℂ) *
        (Complex.I / (evenT t : ℝ)) ^ r *
        ((eulerDeriv^[r]) p).eval
          (unitPt (x / evenT t))‖ ≤ (1 / 2 ^ 10 : ℝ) ^ r := by
  have heuler :=
    norm_iterate_eulerDeriv_eval_le_pow_mul_circSup
      hdeg hcircle r (norm_unitPt (x / evenT t))
  have hTnat : 0 < evenT t := by simp [evenT]
  have hTpos : (0 : ℝ) < evenT t := by exact_mod_cast hTnat
  have hspos : 0 < sqrt (2 ^ (t + 1) : ℝ) := by positivity
  have hpowcast : ((2 ^ t : ℕ) : ℝ) / evenT t = 1 / 2 ^ 10 := by
    rw [evenT_eq_pow_mul]
    push_cast
    field_simp
    norm_num
  have hnonneg : 0 ≤ (1 / (evenT t : ℝ)) ^ r := by positivity
  calc
    ‖(rsNormalization t : ℂ) *
        (Complex.I / (evenT t : ℝ)) ^ r *
        ((eulerDeriv^[r]) p).eval
          (unitPt (x / evenT t))‖ =
      rsNormalization t * (1 / (evenT t : ℝ)) ^ r *
        ‖((eulerDeriv^[r]) p).eval
          (unitPt (x / evenT t))‖ := by
      rw [norm_mul, norm_mul, norm_pow, norm_div, norm_I]
      simp only [Complex.norm_real, norm_eq_abs,
        abs_of_pos (rsNormalization_pos t), abs_of_pos hTpos, one_div]
    _ ≤ rsNormalization t * (1 / (evenT t : ℝ)) ^ r *
        (((2 ^ t : ℕ) : ℝ) ^ r * sqrt (2 ^ (t + 1) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left heuler
        (mul_nonneg (rsNormalization_pos t).le hnonneg)
    _ = (((2 ^ t : ℕ) : ℝ) / evenT t) ^ r := by
      rw [rsNormalization]
      field_simp
      ring
    _ = (1 / 2 ^ 10 : ℝ) ^ r := by rw [hpowcast]

theorem norm_scDerivP_le (r t : ℕ) (x : ℝ) :
    ‖scDerivP r t x‖ ≤ (1 / 2 ^ 10 : ℝ) ^ r := by
  apply normDeriv_bound (rudinShapiroP t) t r x
  · rw [natDegree_rsP]
    exact Nat.sub_le _ _
  · intro z hz
    exact norm_eval_rsP_le t hz

theorem norm_scDerivQ_le (r t : ℕ) (x : ℝ) :
    ‖scDerivQ r t x‖ ≤ (1 / 2 ^ 10 : ℝ) ^ r := by
  apply normDeriv_bound (rudinShapiroQ t) t r x
  · rw [natDegree_rsQ]
    exact Nat.sub_le _ _
  · intro z hz
    exact norm_eval_rsQ_le t hz

theorem evenCos_eq_normH (t : ℕ) (θ : ℝ) :
    evenCos t θ =
      sqrt (2 ^ (t + 1) : ℝ) * (normH t (2 * evenT t * θ)).re := by
  have hTnat : 0 < evenT t := by simp [evenT]
  have hT : (evenT t : ℝ) ≠ 0 := by exact_mod_cast hTnat.ne'
  have hs : sqrt (2 ^ (t + 1) : ℝ) ≠ 0 := by positivity
  have hdiv : (2 * (evenT t : ℝ) * θ) / evenT t = 2 * θ := by
    field_simp [hT]
  have hphase₁ : unitPt (2 * (evenT t : ℝ) * θ) =
      unitPt (2 * θ) ^ evenT t := by
    simp only [unitPt, ← exp_nat_mul]
    congr 1
    push_cast
    ring
  have hphase₂ : unitPt (2 * (2 * (evenT t : ℝ) * θ)) =
      unitPt (2 * θ) ^ (2 * evenT t) := by
    simp only [unitPt, ← exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [evenCos_eq]
  simp only [normH, scDerivP, scDerivQ, pow_zero,
    one_mul, mul_one, Function.iterate_zero_apply, hdiv, hphase₁, hphase₂, rsNormalization]
  rw [show
    unitPt (2 * θ) ^ evenT t *
          ((((sqrt (2 ^ (t + 1) : ℝ))⁻¹ : ℝ) : ℂ) *
            (rudinShapiroP t).eval (unitPt (2 * θ))) +
      unitPt (2 * θ) ^ (2 * evenT t) *
          ((((sqrt (2 ^ (t + 1) : ℝ))⁻¹ : ℝ) : ℂ) *
            (rudinShapiroQ t).eval (unitPt (2 * θ))) =
      (((sqrt (2 ^ (t + 1) : ℝ))⁻¹ : ℝ) : ℂ) *
        (unitPt (2 * θ) ^ evenT t *
            (rudinShapiroP t).eval (unitPt (2 * θ)) +
          unitPt (2 * θ) ^ (2 * evenT t) *
            (rudinShapiroQ t).eval (unitPt (2 * θ))) by ring]
  simp only [mul_re, Complex.inv_re, ofReal_re, ofReal_im,
    Complex.normSq_ofReal, zero_mul, sub_zero]
  field_simp

private theorem cosBlk_coeff_im_eq_zero {t k : ℕ}
    (hk : k ∈ (cosBlk t).support) :
    ((cosBlk t).coeff k).im = 0 := by
  rw [support_cosBlk] at hk
  rw [mem_evenCPrime] at hk
  rcases hk with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · rw [coeff_cosBlk_first t j hj]
    rcases coeff_rsP_eq_one_or_neg_one hj with h | h <;> simp [h]
  · rw [coeff_cosBlk_second t j hj]
    rcases coeff_rsQ_eq_one_or_neg_one hj with h | h <;> simp [h]

theorem evenCos_eq_sum_cos (t : ℕ) (θ : ℝ) :
    evenCos t θ =
      ∑ k ∈ (cosBlk t).support,
        ((cosBlk t).coeff k).re * cos (k * (2 * θ)) := by
  classical
  rw [evenCos, eval_eq_sum, sum_def]
  change reLm
      (∑ k ∈ (cosBlk t).support,
        (cosBlk t).coeff k * unitPt (2 * θ) ^ k) = _
  rw [map_sum]
  apply sum_congr rfl
  intro k hk
  have hre : (unitPt (2 * θ) ^ k).re = cos (k * (2 * θ)) := by
    have h := congrArg re (unitPt_pow (2 * θ) k)
    simpa only [add_re, ofReal_re, mul_re,
      ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, mul_one, add_zero] using h
  change ((cosBlk t).coeff k * unitPt (2 * θ) ^ k).re = _
  rw [mul_re, cosBlk_coeff_im_eq_zero hk, zero_mul, sub_zero, hre]

@[simp] theorem evenCos_neg (t : ℕ) (θ : ℝ) :
    evenCos t (-θ) = evenCos t θ := by
  classical
  rw [evenCos_eq_sum_cos, evenCos_eq_sum_cos]
  apply sum_congr rfl
  intro k hk
  congr 1
  rw [show (k : ℝ) * (2 * -θ) = -((k : ℝ) * (2 * θ)) by ring,
    cos_neg]

@[simp] theorem evenCos_pi_sub (t : ℕ) (θ : ℝ) :
    evenCos t (π - θ) = evenCos t θ := by
  classical
  rw [evenCos_eq_sum_cos, evenCos_eq_sum_cos]
  apply sum_congr rfl
  intro k hk
  congr 1
  rw [show (k : ℝ) * (2 * (π - θ)) =
      (k : ℝ) * (2 * π) - (k : ℝ) * (2 * θ) by ring,
    Real.cos_nat_mul_two_pi_sub]

@[simp] theorem evenCos_sub_pi (t : ℕ) (θ : ℝ) :
    evenCos t (θ - π) = evenCos t θ := by
  rw [show θ - π = -(π - θ) by ring, evenCos_neg,
    evenCos_pi_sub]

def HasGoodCellInEverySeven (f : ℝ → ℝ) (eta : ℝ) : Prop :=
  ∀ a : ℝ, ∃ j : ℕ, j < 7 ∧
    ∀ x ∈ Icc (a + (j : ℝ) * eta) (a + ((j : ℝ) + 1) * eta),
    eta ^ 3 / 128 ≤ |f x|

theorem hasGoodCellInEverySeven_of_deriv_bounds
    (f : ℝ → ℝ) (eta : ℝ)
    (heta : 0 < eta) (hetaSmall : eta < (1 : ℝ) / 2048)
    (hf : ContDiff ℝ 4 f)
    (hlarge : ∀ x, ∃ k : Fin 4, 1 / 4 ≤ |iteratedDeriv k f x|)
    (hderiv : ∀ r ≤ 4, ∀ x, |iteratedDeriv r f x| ≤ 18) :
    HasGoodCellInEverySeven f eta := by
  intro a
  by_contra hnone
  push_neg at hnone
  have hsample (j : Fin 7) :
      ∃ x ∈ Icc (a + (j : ℕ) * eta) (a + ((j : ℕ) + 1) * eta),
        |f x| < eta ^ 3 / 128 := by
    exact hnone (j : ℕ) j.isLt
  let sample : Fin 7 → ℝ := fun j ↦ Classical.choose (hsample j)
  have sample_mem (j : Fin 7) :
      sample j ∈ Icc (a + (j : ℕ) * eta) (a + ((j : ℕ) + 1) * eta) :=
    (Classical.choose_spec (hsample j)).1
  have sample_small (j : Fin 7) : |f (sample j)| < eta ^ 3 / 128 :=
    (Classical.choose_spec (hsample j)).2
  obtain ⟨k, hklarge⟩ := hlarge (sample 0)
  by_cases hk0 : (k : ℕ) = 0
  · have hsmall := sample_small (0 : Fin 7)
    simp only [hk0, iteratedDeriv_zero] at hklarge
    have hetaOne : eta < 1 := lt_trans hetaSmall (by norm_num)
    have hetaCube : eta ^ 3 < 1 := pow_lt_one₀ heta.le hetaOne (by norm_num)
    norm_num at hsmall hklarge
    nlinarith
  · have hk₁ : 1 ≤ (k : ℕ) := Nat.one_le_iff_ne_zero.mpr hk0
    have hk₃ : (k : ℕ) ≤ 3 := by omega
    let node : Fin ((k : ℕ) + 1) → ℝ := fun i ↦
      sample ⟨2 * (i : ℕ), by omega⟩
    have hnode_mem (i : Fin ((k : ℕ) + 1)) :
        node i ∈ Icc (a + (2 * (i : ℕ)) * eta)
          (a + (2 * (i : ℕ) + 1) * eta) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        (sample_mem ⟨2 * (i : ℕ), by omega⟩)
    have hnode_mono : StrictMono node := by
      intro i j hij
      have hi := hnode_mem i
      have hj := hnode_mem j
      have hijNat : (i : ℕ) < (j : ℕ) := by exact_mod_cast hij
      dsimp only [node]
      have hgap : a + (2 * (i : ℕ) + 1) * eta <
          a + (2 * (j : ℕ)) * eta := by
        have : (2 * (i : ℕ) + 1 : ℝ) < 2 * (j : ℕ) := by exact_mod_cast (by omega)
        nlinarith
      exact hi.2.trans_lt (hgap.trans_le hj.1)
    have hnode_sep : ∀ i j, i ≠ j → eta ≤ |node i - node j| := by
      intro i j hij
      rcases lt_or_gt_of_ne hij with hijlt | hjilt
      · have hi := hnode_mem i
        have hj := hnode_mem j
        have hijNat : (i : ℕ) < (j : ℕ) := by exact_mod_cast hijlt
        rw [abs_of_nonpos (sub_nonpos.mpr (hnode_mono hijlt).le)]
        dsimp only [node] at hi hj ⊢
        have hgap : a + (2 * (i : ℕ) + 1) * eta + eta ≤
            a + (2 * (j : ℕ)) * eta := by
          have : (2 * (i : ℕ) + 2 : ℝ) ≤ 2 * (j : ℕ) := by exact_mod_cast (by omega)
          nlinarith
        linarith [hi.2, hj.1]
      · have hi := hnode_mem i
        have hj := hnode_mem j
        have hjiNat : (j : ℕ) < (i : ℕ) := by exact_mod_cast hjilt
        rw [abs_of_nonneg (sub_nonneg.mpr (hnode_mono hjilt).le)]
        dsimp only [node] at hi hj ⊢
        have hgap : a + (2 * (j : ℕ) + 1) * eta + eta ≤
            a + (2 * (i : ℕ)) * eta := by
          have : (2 * (j : ℕ) + 2 : ℝ) ≤ 2 * (i : ℕ) := by exact_mod_cast (by omega)
          nlinarith
        linarith [hj.2, hi.1]
    have hnode_dist (i : Fin ((k : ℕ) + 1)) :
        |node i - sample 0| ≤ 7 * eta := by
      have hi := hnode_mem i
      have h0 := sample_mem (0 : Fin 7)
      have hleft : sample 0 ≤ node i := by
        by_cases hi0 : (i : ℕ) = 0
        · apply le_of_eq
          have hieq : i = 0 := Fin.ext hi0
          subst i
          apply congrArg sample
          exact Fin.ext rfl
        · have hiPos : 1 ≤ (i : ℕ) := Nat.one_le_iff_ne_zero.mpr hi0
          have hgap : a + eta ≤ a + (2 * (i : ℕ)) * eta := by
            have : (1 : ℝ) ≤ 2 * (i : ℕ) := by exact_mod_cast (by omega)
            nlinarith
          norm_num at h0
          exact h0.2.trans (hgap.trans hi.1)
      rw [abs_of_nonneg (sub_nonneg.mpr hleft)]
      have hik : (i : ℕ) ≤ (k : ℕ) := Nat.le_of_lt_succ i.isLt
      have hupper : node i ≤ a + 7 * eta := by
        calc
          node i ≤ a + (2 * (i : ℕ) + 1) * eta := hi.2
          _ ≤ a + 7 * eta := by
            have : (2 * (i : ℕ) + 1 : ℝ) ≤ 7 := by exact_mod_cast (by omega)
            nlinarith
      norm_num at h0
      linarith [h0.1]
    have hnode_value (i : Fin ((k : ℕ) + 1)) :
        |f (node i)| ≤ eta ^ 3 / 128 := by
      have hiLe : (i : ℕ) ≤ (k : ℕ) := Nat.le_of_lt_succ i.isLt
      have hkLt : (k : ℕ) < 4 := k.isLt
      have hidx : 2 * (i : ℕ) < 7 := by omega
      exact (sample_small ⟨2 * (i : ℕ), hidx⟩).le
    have hk4 : (k : ℕ) + 1 ≤ 4 := by omega
    have hquarter := Interp.howell_lt_quarter_of_nodes
      (k : ℕ) hk₁ hk₃ f node (sample 0) eta
      (hf.of_le (by exact_mod_cast hk4)) hnode_mono heta hetaSmall hnode_sep hnode_dist
      hnode_value
      (fun x ↦ hderiv ((k : ℕ) + 1) hk4 x)
    linarith

def BadCell (n t : ℕ) (γ : ℝ) (i : ℕ) : Prop :=
  ∃ θ ∈ gridCell n i,
    |evenCos t θ| < thr n γ

noncomputable instance instDecidablePredBadCell (n t : ℕ) (γ : ℝ) :
    DecidablePred (BadCell n t γ) := Classical.decPred _

noncomputable def dangerousRuns (n t : ℕ) (γ : ℝ) : Finset (ℕ × ℕ) :=
  @maximalBadRuns (2 * n) (BadCell n t γ)
    (Classical.decPred _)

@[simp] theorem mem_dangerousRuns {n t : ℕ} {γ : ℝ} {a b : ℕ} :
    (a, b) ∈ dangerousRuns n t γ ↔
      IsMaximalBadRun (2 * n) (BadCell n t γ) a b := by
  classical
  exact mem_maximalBadRuns

def runIvl (n : ℕ) (I : ℕ × ℕ) : Set ℝ :=
  Icc (gridPt n I.1)
    (gridPt n (I.2 + 1))

def runEndpts (n : ℕ) (I : ℕ × ℕ) : RealIvl :=
  (gridPt n I.1,
    gridPt n (I.2 + 1))

noncomputable def firstQuadRuns (n t : ℕ) (γ : ℝ) : Finset (ℕ × ℕ) :=
  (dangerousRuns n t γ).filter fun I ↦ 2 * (I.2 + 1) ≤ n

noncomputable def firstQuadIvls (n t : ℕ) (γ : ℝ) :
    Finset RealIvl :=
  (firstQuadRuns n t γ).image (runEndpts n)

@[simp] theorem mem_firstQuadRuns {n t : ℕ} {γ : ℝ} {I : ℕ × ℕ} :
    I ∈ firstQuadRuns n t γ ↔
      I ∈ dangerousRuns n t γ ∧ 2 * (I.2 + 1) ≤ n := by
  classical
  simp [firstQuadRuns]

theorem runEndpts_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (runEndpts n) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [runEndpts, Prod.mk.injEq] at h
  have hstrict := gridPt_strictMono hn
  have hac : a = c := hstrict.injective h.1
  have hbd : b + 1 = d + 1 := hstrict.injective h.2
  simp only [Prod.mk.injEq]
  exact ⟨hac, Nat.succ.inj hbd⟩

theorem card_firstQuadIvls {n t : ℕ} {γ : ℝ} (hn : 0 < n) :
    (firstQuadIvls n t γ).card =
      (firstQuadRuns n t γ).card := by
  classical
  exact Finset.card_image_of_injective _ (runEndpts_injective hn)

def SevenCellProperty (n t : ℕ) (γ : ℝ) : Prop :=
  ∀ a, a + 7 ≤ 2 * n →
    ∃ j < 7, ¬BadCell n t γ (a + j)

theorem sevenCellProperty_of_norm_good
    {n t : ℕ} {γ : ℝ} (hparam : Params n t γ)
    (hgood : HasGoodCellInEverySeven (fun x ↦ (normH t x).re)
      (2 * (evenT t : ℝ) * π / n)) :
    SevenCellProperty n t γ := by
  intro a ha
  let eta : ℝ := 2 * (evenT t : ℝ) * π / n
  obtain ⟨j, hj, hcell⟩ := hgood (a * eta)
  refine ⟨j, hj, ?_⟩
  rintro ⟨θ, hθ, hsmall⟩
  let x : ℝ := 2 * evenT t * θ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hparam.n_pos
  have hT : (0 : ℝ) < evenT t := by
    exact_mod_cast (show 0 < evenT t by simp [evenT])
  have hx : x ∈ Icc (a * eta + (j : ℝ) * eta)
      (a * eta + ((j : ℝ) + 1) * eta) := by
    rcases hθ with ⟨hθL, hθR⟩
    simp only [gridCell, gridPt] at hθL hθR
    dsimp [x, eta]
    constructor <;> push_cast at * <;>
      (field_simp [ne_of_gt hnR] at hθL hθR ⊢ <;> nlinarith [pi_pos])
  have hnorm : eta ^ 3 / 128 ≤ |(normH t x).re| := by
    simpa [eta] using hcell x hx
  have hsqrt : 0 ≤ sqrt (2 ^ (t + 1) : ℝ) := sqrt_nonneg _
  have hlower : thr n γ ≤
      sqrt (2 ^ (t + 1) : ℝ) * |(normH t x).re| := by
    calc
      thr n γ ≤
          sqrt (2 ^ (t + 1) : ℝ) * eta ^ 3 / 128 := by
        simpa [eta] using hparam.thr_le_norm_good
      _ ≤ sqrt (2 ^ (t + 1) : ℝ) * |(normH t x).re| := by
        have := mul_le_mul_of_nonneg_left hnorm hsqrt
        nlinarith
  have heq : |evenCos t θ| =
      sqrt (2 ^ (t + 1) : ℝ) * |(normH t x).re| := by
    rw [evenCos_eq_normH]
    dsimp [x]
    rw [abs_mul, abs_of_nonneg hsqrt]
  rw [← heq] at hlower
  exact (not_lt_of_ge hlower) hsmall

theorem dangerousRun_length_le_six {n t : ℕ} {γ : ℝ}
    (hseven : SevenCellProperty n t γ) {a b : ℕ}
    (hab : (a, b) ∈ dangerousRuns n t γ) :
    b + 1 - a ≤ 6 := by
  classical
  rw [mem_dangerousRuns] at hab
  by_contra hlong
  have hab7 : a + 7 ≤ b + 1 := by omega
  have hbN : b < 2 * n := hab.2.1
  have ha7N : a + 7 ≤ 2 * n := by omega
  obtain ⟨j, hj, hgood⟩ := hseven a ha7N
  apply hgood
  exact hab.2.2.1 (a + j) (Finset.mem_range.mpr (by omega)) (by omega) (by omega)

theorem dangerousRun_width_le {n t : ℕ} {γ : ℝ}
    (hn : 0 < n) (hseven : SevenCellProperty n t γ) {I : ℕ × ℕ}
    (hI : I ∈ dangerousRuns n t γ) :
    gridPt n (I.2 + 1) -
        gridPt n I.1 ≤ 6 * π / n := by
  rcases I with ⟨a, b⟩
  have hlen := dangerousRun_length_le_six hseven hI
  simp only [gridPt]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hba : a ≤ b + 1 := by
    rw [mem_dangerousRuns] at hI
    exact hI.1.trans (Nat.le_succ b)
  have hcast : ((b + 1 - a : ℕ) : ℝ) ≤ 6 := by exact_mod_cast hlen
  rw [Nat.cast_sub hba] at hcast
  rw [← sub_div]
  apply (div_le_div_iff_of_pos_right hnR).2
  nlinarith [pi_pos]

theorem dangerousRuns_sep {n t : ℕ} {γ : ℝ} {a b c d : ℕ}
    (h₁ : (a, b) ∈ dangerousRuns n t γ)
    (h₂ : (c, d) ∈ dangerousRuns n t γ)
    (hbc : b < c) : b + 2 ≤ c := by
  classical
  rw [mem_dangerousRuns] at h₁ h₂
  by_contra h
  have hc : c = b + 1 := by omega
  have hcN : c < 2 * n := h₂.1.trans_lt h₂.2.1
  have hbadc := h₂.2.2.1 c (Finset.mem_range.mpr hcN) le_rfl h₂.1
  rcases h₁.2.2.2.2 with hright | hgood
  · rw [hc, hright] at hcN
    omega
  · exact hgood (by simpa [hc] using hbadc)

structure GeometricCert (n t : ℕ) (γ : ℝ) : Prop where
  separated : Set.Pairwise
    (↑(firstQuadIvls n t γ) :
      Set RealIvl)
    (fun I J ↦ ∀ x ∈ Icc I.1 I.2, ∀ y ∈ Icc J.1 J.2,
      π / n ≤ |x - y|)
  away_from_axes : ∀ I ∈ firstQuadIvls n t γ,
    100 * π / n ≤ I.1 ∧
      I.2 ≤ π / 2 - 100 * π / n

def suitIvlFamOfDangerousRuns
    {n t : ℕ} {γ : ℝ} (hn : 0 < n)
    (hseven : SevenCellProperty n t γ)
    (hgeom : GeometricCert n t γ) :
    IvlFam n where
  base := firstQuadIvls n t γ
  ordered := by
    intro I hI
    classical
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    rw [mem_firstQuadRuns] at hJ
    rcases J with ⟨a, b⟩
    simp only [runEndpts]
    apply gridPt_mono hn
    rw [mem_dangerousRuns] at hJ
    exact Nat.le_succ_of_le hJ.1.1
  nondegenerate := by
    intro I hI
    classical
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    rw [mem_firstQuadRuns] at hJ
    rcases J with ⟨a, b⟩
    simp only [runEndpts]
    apply gridPt_strictMono hn
    rw [mem_dangerousRuns] at hJ
    exact Nat.lt_succ_of_le hJ.1.1
  in_first_quadrant := by
    intro I hI
    classical
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    rw [mem_firstQuadRuns] at hJ
    rcases J with ⟨a, b⟩
    simp only [runEndpts]
    constructor
    · exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) pi_pos.le)
        (Nat.cast_nonneg _)
    · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hidx : (2 * (b + 1) : ℝ) ≤ n := by exact_mod_cast hJ.2
      simp only [gridPt]
      norm_num [Nat.cast_add]
      apply (div_le_iff₀ hnR).2
      have hmul := mul_le_mul_of_nonneg_right hidx pi_pos.le
      norm_num [Nat.cast_add] at hmul
      nlinarith
  grid_endpoints := by
    intro I hI
    classical
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    rcases J with ⟨a, b⟩
    exact ⟨a, b + 1, by simp [runEndpts, gridPt],
      by simp [runEndpts, gridPt]⟩
  short := by
    intro I hI
    classical
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    rw [mem_firstQuadRuns] at hJ
    simpa only [runEndpts] using dangerousRun_width_le hn hseven hJ.1
  separated := hgeom.separated
  away_from_axes := hgeom.away_from_axes

def InBaseFam {n : ℕ} (F : IvlFam n)
    (θ : ℝ) : Prop :=
  ∃ I ∈ F.base, InIvl I θ

theorem lo_on_fundamental_of_lo_off_base
    {n t : ℕ} {γ : ℝ} (F : IvlFam n)
    (hfirst : ∀ θ ∈ Icc 0 (π / 2),
      ¬InBaseFam F θ →
        thr n γ ≤ |evenCos t θ|) :
    ∀ θ ∈ Icc (-π / 2) (3 * π / 2),
      ¬IsDangerous F θ →
        thr n γ ≤ |evenCos t θ| := by
  intro θ hθ hout
  rcases hθ with ⟨hθLower, hθUpper⟩
  by_cases h0 : θ ≤ 0
  · have hphi : -θ ∈ Icc 0 (π / 2) := by
      constructor <;> linarith
    have hbase : ¬InBaseFam F (-θ) := by
      rintro ⟨I, hI, hmem⟩
      exact hout ⟨I, hI, Or.inr (Or.inl hmem)⟩
    simpa using hfirst (-θ) hphi hbase
  · have hθ0 : 0 ≤ θ := le_of_not_ge h0
    by_cases hhalf : θ ≤ π / 2
    · exact hfirst θ ⟨hθ0, hhalf⟩ fun hbase ↦ by
        rcases hbase with ⟨I, hI, hmem⟩
        exact hout ⟨I, hI, Or.inl hmem⟩
    · have hhalf' : π / 2 ≤ θ := le_of_not_ge hhalf
      by_cases hpi : θ ≤ π
      · have hphi : π - θ ∈ Icc 0 (π / 2) := by
          constructor <;> linarith
        have hbase : ¬InBaseFam F (π - θ) := by
          rintro ⟨I, hI, hmem⟩
          exact hout ⟨I, hI, Or.inr (Or.inr (Or.inl hmem))⟩
        simpa using hfirst (π - θ) hphi hbase
      · have hpi' : π ≤ θ := le_of_not_ge hpi
        have hphi : θ - π ∈ Icc 0 (π / 2) := by
          constructor <;> linarith
        have hbase : ¬InBaseFam F (θ - π) := by
          rintro ⟨I, hI, hmem⟩
          exact hout ⟨I, hI, Or.inr (Or.inr (Or.inr hmem))⟩
        simpa using hfirst (θ - π) hphi hbase

theorem suitFam_base_card
    {n t : ℕ} {γ : ℝ} (hn : 0 < n)
    (hseven : SevenCellProperty n t γ)
    (hgeom : GeometricCert n t γ) :
    (suitIvlFamOfDangerousRuns hn hseven hgeom).base.card =
      (firstQuadRuns n t γ).card :=
  card_firstQuadIvls hn

end

end CosConstr

end

section

namespace CosConstr

open scoped BigOperators

noncomputable section

private theorem hasDerivAt_unitPt (c x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ unitPt (c * y))
      ((c : ℂ) * Complex.I * unitPt (c * x)) x := by
  have hinner : HasDerivAt (fun y : ℝ ↦ ((c : ℂ) * Complex.I) * (y : ℂ))
      ((c : ℂ) * Complex.I) x := by
    simpa using (ofRealCLM.hasDerivAt (x := x)).const_mul
      ((c : ℂ) * Complex.I)
  simpa only [unitPt, Complex.ofReal_mul, mul_assoc, mul_comm, mul_left_comm] using
    hinner.cexp

private theorem hasDerivAt_scDerivP (r t : ℕ) (x : ℝ) :
    HasDerivAt (scDerivP r t)
      (scDerivP (r + 1) t x) x := by
  have hTnat : 0 < evenT t := by simp [evenT]
  have hT : (evenT t : ℝ) ≠ 0 := by exact_mod_cast hTnat.ne'
  let p : Polynomial ℂ :=
    (eulerDeriv^[r]) (rudinShapiroP t)
  have hunit : HasDerivAt (fun y : ℝ ↦ unitPt (y / evenT t))
      ((Complex.I / (evenT t : ℝ)) * unitPt (x / evenT t)) x := by
    convert hasDerivAt_unitPt (1 / evenT t) x using 1
    · funext y
      congr 1
      field_simp
    · push_cast
      field_simp
  have hpoly := (p.hasDerivAt (unitPt (x / evenT t))).comp x hunit
  let C : ℂ := (rsNormalization t : ℂ) * (Complex.I / (evenT t : ℝ)) ^ r
  have hfun : scDerivP r t =
      fun y ↦ C * p.eval (unitPt (y / evenT t)) := by
    funext y
    rfl
  rw [hfun]
  have hnext : scDerivP (r + 1) t x =
      C * (p.derivative.eval (unitPt (x / evenT t)) *
        ((Complex.I / (evenT t : ℝ)) * unitPt (x / evenT t))) := by
    unfold scDerivP
    rw [Function.iterate_succ_apply', eval_eulerDeriv,
      pow_succ]
    dsimp only [C, p]
    ring
  rw [hnext]
  exact hpoly.const_mul C

private theorem hasDerivAt_scDerivQ (r t : ℕ) (x : ℝ) :
    HasDerivAt (scDerivQ r t)
      (scDerivQ (r + 1) t x) x := by
  have hTnat : 0 < evenT t := by simp [evenT]
  have hT : (evenT t : ℝ) ≠ 0 := by exact_mod_cast hTnat.ne'
  let p : Polynomial ℂ :=
    (eulerDeriv^[r]) (rudinShapiroQ t)
  have hunit : HasDerivAt (fun y : ℝ ↦ unitPt (y / evenT t))
      ((Complex.I / (evenT t : ℝ)) * unitPt (x / evenT t)) x := by
    convert hasDerivAt_unitPt (1 / evenT t) x using 1
    · funext y
      congr 1
      field_simp
    · push_cast
      field_simp
  have hpoly := (p.hasDerivAt (unitPt (x / evenT t))).comp x hunit
  let C : ℂ := (rsNormalization t : ℂ) * (Complex.I / (evenT t : ℝ)) ^ r
  have hfun : scDerivQ r t =
      fun y ↦ C * p.eval (unitPt (y / evenT t)) := by
    funext y
    rfl
  rw [hfun]
  have hnext : scDerivQ (r + 1) t x =
      C * (p.derivative.eval (unitPt (x / evenT t)) *
        ((Complex.I / (evenT t : ℝ)) * unitPt (x / evenT t))) := by
    unfold scDerivQ
    rw [Function.iterate_succ_apply', eval_eulerDeriv,
      pow_succ]
    dsimp only [C, p]
    ring
  rw [hnext]
  exact hpoly.const_mul C

private theorem contDiff_unitPt_mul (c : ℝ) :
    ContDiff ℝ ⊤ (fun x : ℝ ↦ unitPt (c * x)) := by
  have hr : ContDiff ℝ ⊤ (fun x : ℝ ↦ c * x) := contDiff_const.mul contDiff_id
  have hc : ContDiff ℝ ⊤ (fun x : ℝ ↦ ((c * x : ℝ) : ℂ)) :=
    ofRealCLM.contDiff.comp hr
  unfold unitPt
  exact (hc.mul contDiff_const).cexp

theorem contDiff_scDerivP (r t : ℕ) :
    ContDiff ℝ ⊤ (scDerivP r t) := by
  let p := (eulerDeriv^[r]) (rudinShapiroP t)
  have hp : ContDiff ℝ ⊤ (fun z : ℂ ↦ p.eval z) :=
    p.differentiable.contDiff.restrict_scalars ℝ
  have hu : ContDiff ℝ ⊤ (fun x : ℝ ↦ unitPt (x / evenT t)) := by
    simpa only [div_eq_mul_inv, mul_comm] using
      contDiff_unitPt_mul ((evenT t : ℝ)⁻¹)
  unfold scDerivP
  exact contDiff_const.mul (hp.comp hu)

theorem contDiff_scDerivQ (r t : ℕ) :
    ContDiff ℝ ⊤ (scDerivQ r t) := by
  let p := (eulerDeriv^[r]) (rudinShapiroQ t)
  have hp : ContDiff ℝ ⊤ (fun z : ℂ ↦ p.eval z) :=
    p.differentiable.contDiff.restrict_scalars ℝ
  have hu : ContDiff ℝ ⊤ (fun x : ℝ ↦ unitPt (x / evenT t)) := by
    simpa only [div_eq_mul_inv, mul_comm] using
      contDiff_unitPt_mul ((evenT t : ℝ)⁻¹)
  unfold scDerivQ
  exact contDiff_const.mul (hp.comp hu)

theorem iteratedDeriv_scDerivP (q r t : ℕ) :
    iteratedDeriv q (scDerivP r t) =
      scDerivP (r + q) t := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      simpa [Nat.add_assoc] using (hasDerivAt_scDerivP (r + q) t x).deriv

theorem iteratedDeriv_scDerivQ (q r t : ℕ) :
    iteratedDeriv q (scDerivQ r t) =
      scDerivQ (r + q) t := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      simpa [Nat.add_assoc] using (hasDerivAt_scDerivQ (r + q) t x).deriv

private theorem iteratedDeriv_unitPt_mul (q : ℕ) (c : ℝ) :
    iteratedDeriv q (fun x : ℝ ↦ unitPt (c * x)) =
      fun x ↦ ((c : ℂ) * Complex.I) ^ q * unitPt (c * x) := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      simpa only [pow_succ, mul_assoc] using
        (hasDerivAt_unitPt c x).const_mul (((c : ℂ) * Complex.I) ^ q) |>.deriv

def normHDeriv (r t : ℕ) (x : ℝ) : ℂ :=
  ∑ i ∈ Finset.range (r + 1),
      (r.choose i : ℂ) *
        (Complex.I ^ i * unitPt x) * scDerivP (r - i) t x +
    ∑ i ∈ Finset.range (r + 1),
      (r.choose i : ℂ) *
        (((2 : ℂ) * Complex.I) ^ i * unitPt (2 * x)) *
          scDerivQ (r - i) t x

theorem contDiff_normH (t : ℕ) :
    ContDiff ℝ ⊤ (normH t) := by
  unfold normH
  simpa only [one_mul] using
    (((contDiff_unitPt_mul 1).mul (contDiff_scDerivP 0 t)).add
      ((contDiff_unitPt_mul 2).mul (contDiff_scDerivQ 0 t)))

theorem iteratedDeriv_normH (r t : ℕ) (x : ℝ) :
    iteratedDeriv r (normH t) x = normHDeriv r t x := by
  have hu1 : ContDiff ℝ ⊤ (fun y : ℝ ↦ unitPt y) := by
    simpa only [one_mul] using contDiff_unitPt_mul 1
  have hu2 : ContDiff ℝ ⊤ (fun y : ℝ ↦ unitPt (2 * y)) :=
    contDiff_unitPt_mul 2
  have hp := contDiff_scDerivP 0 t
  have hq := contDiff_scDerivQ 0 t
  have hdu1 (i : ℕ) : iteratedDeriv i (fun y : ℝ ↦ unitPt y) x =
      Complex.I ^ i * unitPt x := by
    have h := congrFun (iteratedDeriv_unitPt_mul i 1) x
    norm_num at h
    exact h
  unfold normH normHDeriv
  change iteratedDeriv r
      ((fun y ↦ unitPt y * scDerivP 0 t y) +
        fun y ↦ unitPt (2 * y) * scDerivQ 0 t y) x = _
  rw [iteratedDeriv_add
    ((hu1.mul hp).contDiffAt.of_le (by simp))
    ((hu2.mul hq).contDiffAt.of_le (by simp))]
  congr 1
  · change iteratedDeriv r
        ((fun y ↦ unitPt y) * scDerivP 0 t) x = _
    rw [iteratedDeriv_mul
      (hu1.contDiffAt.of_le (by simp))
      (hp.contDiffAt.of_le (by simp))]
    simp_rw [hdu1,
      congrFun (iteratedDeriv_scDerivP _ _ _) x]
    simp only [Nat.zero_add]
  · change iteratedDeriv r
        ((fun y ↦ unitPt (2 * y)) * scDerivQ 0 t) x = _
    rw [iteratedDeriv_mul
      (hu2.contDiffAt.of_le (by simp))
      (hq.contDiffAt.of_le (by simp))]
    simp_rw [congrFun (iteratedDeriv_unitPt_mul _ 2) x,
      congrFun (iteratedDeriv_scDerivQ _ _ _) x]
    norm_num

theorem contDiff_normH_re (t : ℕ) :
    ContDiff ℝ ⊤ (fun x ↦ (normH t x).re) :=
  reCLM.contDiff.comp (contDiff_normH t)

private theorem hasDerivAt_re_of_hasDerivAt {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y ↦ (f y).re) f'.re x := by
  have hc : HasDerivAt (fun _ : ℝ ↦ reCLM) 0 x := hasDerivAt_const x _
  simpa using hc.clm_apply hf

theorem iteratedDeriv_normH_re (r t : ℕ) :
    iteratedDeriv r (fun x ↦ (normH t x).re) =
      fun x ↦ (iteratedDeriv r (normH t) x).re := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
      funext x
      have hd : DifferentiableAt ℝ (iteratedDeriv r (normH t)) x :=
        ((contDiff_normH t).differentiable_iteratedDeriv r (by simp)) x
      exact (hasDerivAt_re_of_hasDerivAt hd.hasDerivAt).deriv

theorem iteratedDeriv_normH_re_eq (r t : ℕ) (x : ℝ) :
    iteratedDeriv r (fun y ↦ (normH t y).re) x =
      (normHDeriv r t x).re := by
  rw [congrFun (iteratedDeriv_normH_re r t) x,
    iteratedDeriv_normH]

private theorem norm_normHDeriv_le_sum (r t : ℕ) (x : ℝ) :
    ‖normHDeriv r t x‖ ≤
      ∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℝ) * (1 / 2 ^ 10 : ℝ) ^ (r - i) +
        ∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℝ) * 2 ^ i * (1 / 2 ^ 10 : ℝ) ^ (r - i) := by
  unfold normHDeriv
  calc
    ‖∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℂ) * (Complex.I ^ i * unitPt x) *
              scDerivP (r - i) t x +
        ∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℂ) * (((2 : ℂ) * Complex.I) ^ i * unitPt (2 * x)) *
              scDerivQ (r - i) t x‖ ≤
        ‖∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℂ) * (Complex.I ^ i * unitPt x) *
              scDerivP (r - i) t x‖ +
        ‖∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℂ) * (((2 : ℂ) * Complex.I) ^ i * unitPt (2 * x)) *
              scDerivQ (r - i) t x‖ := norm_add_le _ _
    _ ≤
        ∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℝ) * (1 / 2 ^ 10 : ℝ) ^ (r - i) +
        ∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℝ) * 2 ^ i * (1 / 2 ^ 10 : ℝ) ^ (r - i) := by
      apply add_le_add
      · refine (norm_sum_le _ _).trans (sum_le_sum ?_)
        intro i hi
        simp only [norm_mul, norm_pow, norm_I, one_pow,
          norm_unitPt, mul_one, norm_natCast]
        exact mul_le_mul_of_nonneg_left
          (norm_scDerivP_le (r - i) t x) (by positivity)
      · refine (norm_sum_le _ _).trans (sum_le_sum ?_)
        intro i hi
        simp only [norm_mul, norm_pow, norm_I, norm_unitPt, mul_one,
          norm_natCast]
        rw [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
        exact mul_le_mul_of_nonneg_left
          (norm_scDerivQ_le (r - i) t x)
          (mul_nonneg (by positivity) (by positivity))

theorem norm_normHDeriv_le_eighteen {r : ℕ} (hr : r ≤ 4)
    (t : ℕ) (x : ℝ) :
    ‖normHDeriv r t x‖ ≤ 18 := by
  refine (norm_normHDeriv_le_sum r t x).trans ?_
  interval_cases r <;> norm_num [sum_range_succ, Nat.choose]

theorem abs_iteratedDeriv_normH_re_le_eighteen (r : ℕ) (hr : r ≤ 4)
    (t : ℕ) (x : ℝ) :
    |iteratedDeriv r (fun y ↦ (normH t y).re) x| ≤ 18 := by
  rw [iteratedDeriv_normH_re_eq]
  exact (abs_re_le_norm _).trans
    (norm_normHDeriv_le_eighteen hr t x)

private def normHDerivError (r t : ℕ) (x : ℝ) : ℂ :=
  ∑ i ∈ Finset.range r,
      (r.choose i : ℂ) *
        (Complex.I ^ i * unitPt x) * scDerivP (r - i) t x +
    ∑ i ∈ Finset.range r,
      (r.choose i : ℂ) *
        (((2 : ℂ) * Complex.I) ^ i * unitPt (2 * x)) *
          scDerivQ (r - i) t x

private theorem normHDeriv_sub_leading (r t : ℕ) (x : ℝ) :
    normHDeriv r t x -
        CosAlgebra.leadingDeriv r
          (unitPt x * scDerivP 0 t x)
          (unitPt (2 * x) * scDerivQ 0 t x) =
      normHDerivError r t x := by
  unfold normHDeriv normHDerivError
    CosAlgebra.leadingDeriv
  rw [sum_range_succ, sum_range_succ]
  simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self]
  ring

private theorem norm_normHDerivError_le_sum (r t : ℕ) (x : ℝ) :
    ‖normHDerivError r t x‖ ≤
      ∑ i ∈ Finset.range r,
          (r.choose i : ℝ) * (1 / 2 ^ 10 : ℝ) ^ (r - i) +
        ∑ i ∈ Finset.range r,
          (r.choose i : ℝ) * 2 ^ i * (1 / 2 ^ 10 : ℝ) ^ (r - i) := by
  unfold normHDerivError
  calc
    ‖∑ i ∈ Finset.range r,
          (r.choose i : ℂ) * (Complex.I ^ i * unitPt x) *
              scDerivP (r - i) t x +
        ∑ i ∈ Finset.range r,
          (r.choose i : ℂ) * (((2 : ℂ) * Complex.I) ^ i * unitPt (2 * x)) *
              scDerivQ (r - i) t x‖ ≤
        ‖∑ i ∈ Finset.range r,
          (r.choose i : ℂ) * (Complex.I ^ i * unitPt x) *
              scDerivP (r - i) t x‖ +
        ‖∑ i ∈ Finset.range r,
          (r.choose i : ℂ) * (((2 : ℂ) * Complex.I) ^ i * unitPt (2 * x)) *
              scDerivQ (r - i) t x‖ := norm_add_le _ _
    _ ≤
        ∑ i ∈ Finset.range r,
          (r.choose i : ℝ) * (1 / 2 ^ 10 : ℝ) ^ (r - i) +
        ∑ i ∈ Finset.range r,
          (r.choose i : ℝ) * 2 ^ i * (1 / 2 ^ 10 : ℝ) ^ (r - i) := by
      apply add_le_add
      · refine (norm_sum_le _ _).trans (sum_le_sum ?_)
        intro i hi
        simp only [norm_mul, norm_pow, norm_I, one_pow,
          norm_unitPt, mul_one, norm_natCast]
        exact mul_le_mul_of_nonneg_left
          (norm_scDerivP_le (r - i) t x) (by positivity)
      · refine (norm_sum_le _ _).trans (sum_le_sum ?_)
        intro i hi
        simp only [norm_mul, norm_pow, norm_I, norm_unitPt, mul_one,
          norm_natCast]
        rw [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
        exact mul_le_mul_of_nonneg_left
          (norm_scDerivQ_le (r - i) t x)
          (mul_nonneg (by positivity) (by positivity))

private theorem norm_normHDeriv_sub_leading_le_eighth {r : ℕ}
    (hr : r < 4) (t : ℕ) (x : ℝ) :
    ‖normHDeriv r t x -
        CosAlgebra.leadingDeriv r
          (unitPt x * scDerivP 0 t x)
          (unitPt (2 * x) * scDerivQ 0 t x)‖ ≤ 1 / 8 := by
  rw [normHDeriv_sub_leading]
  refine (norm_normHDerivError_le_sum r t x).trans ?_
  interval_cases r <;> norm_num [sum_range_succ, Nat.choose]

theorem exists_large_iteratedDeriv_normH_re (t : ℕ) (x : ℝ) :
    ∃ k : Fin 4,
      1 / 4 ≤ |iteratedDeriv k (fun y ↦ (normH t y).re) x| := by
  have hlarge := CosAlgebra.exists_large_re_of_norm_modes
    (u := unitPt x) (v := unitPt (2 * x))
    (α := scDerivP 0 t x) (beta := scDerivQ 0 t x)
    (norm_unitPt x) (norm_unitPt (2 * x)) (norm_energy t x)
    (fun k : Fin 4 ↦ normHDeriv k t x)
    (fun k ↦ norm_normHDeriv_sub_leading_le_eighth k.isLt t x)
  simpa only [iteratedDeriv_normH_re_eq] using hlarge

theorem normH_re_hasGoodCellInEverySeven (t : ℕ) {eta : ℝ}
    (heta : 0 < eta) (hetaSmall : eta < (1 : ℝ) / 2048) :
    HasGoodCellInEverySeven (fun x ↦ (normH t x).re) eta := by
  exact hasGoodCellInEverySeven_of_deriv_bounds
    (fun x ↦ (normH t x).re) eta heta hetaSmall
    ((contDiff_normH_re t).of_le (by simp))
    (exists_large_iteratedDeriv_normH_re t)
    (fun r hr x ↦ abs_iteratedDeriv_normH_re_le_eighteen r hr t x)

end

end CosConstr

end

section
namespace CosConstr

open Set

noncomputable section

private theorem maximalBadRuns_oriented {N a b c d : ℕ} {bad : ℕ → Prop}
    [DecidablePred bad]
    (h₁ : IsMaximalBadRun N bad a b)
    (h₂ : IsMaximalBadRun N bad c d)
    (hne : (a, b) ≠ (c, d)) :
    b < c ∨ d < a := by
  rcases lt_trichotomy a c with hac | hac | hca
  · left
    by_contra hbc
    have hcb : c ≤ b := Nat.le_of_not_gt hbc
    have hcpos : 0 < c := by omega
    have hcPredN : c - 1 < N :=
      lt_of_le_of_lt (Nat.sub_le c 1) (hcb.trans_lt h₁.2.1)
    have hbadPred : bad (c - 1) :=
      h₁.2.2.1 (c - 1) (Finset.mem_range.mpr hcPredN) (by omega) (by omega)
    rcases h₂.2.2.2.1 with hc0 | hgoodPred
    · omega
    · exact hgoodPred hbadPred
  · exact False.elim (hne (h₁.eq_of_start_eq h₂ hac))
  · right
    by_contra hda
    have had : a ≤ d := Nat.le_of_not_gt hda
    have hapos : 0 < a := by omega
    have haPredN : a - 1 < N :=
      lt_of_le_of_lt (Nat.sub_le a 1) (had.trans_lt h₂.2.1)
    have hbadPred : bad (a - 1) :=
      h₂.2.2.1 (a - 1) (Finset.mem_range.mpr haPredN) (by omega) (by omega)
    rcases h₁.2.2.2.1 with ha0 | hgoodPred
    · omega
    · exact hgoodPred hbadPred

theorem firstQuadIvls_pairwise_sep
    {n t : ℕ} {γ : ℝ} (hn : 0 < n) :
    Set.Pairwise
      (↑(firstQuadIvls n t γ) :
        Set RealIvl)
      (fun I J ↦ ∀ x ∈ Icc I.1 I.2, ∀ y ∈ Icc J.1 J.2,
        π / n ≤ |x - y|) := by
  classical
  intro I hI J hJ hne x hx y hy
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hI
  obtain ⟨⟨c, d⟩, hcd, rfl⟩ := Finset.mem_image.mp hJ
  have hrunsNe : (a, b) ≠ (c, d) := by
    intro heq
    apply hne
    exact congrArg (runEndpts n) heq
  rw [mem_firstQuadRuns] at hab hcd
  have horient := maximalBadRuns_oriented
    (show IsMaximalBadRun (2 * n) (BadCell n t γ) a b by
      simpa only [mem_dangerousRuns] using hab.1)
    (show IsMaximalBadRun (2 * n) (BadCell n t γ) c d by
      simpa only [mem_dangerousRuns] using hcd.1)
    hrunsNe
  simp only [runEndpts, mem_Icc] at hx hy ⊢
  have hmono := gridPt_mono hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmesh : 0 < π / (n : ℝ) := div_pos pi_pos hnR
  rcases horient with hbc | hda
  · have hgap : b + 2 ≤ c := dangerousRuns_sep hab.1 hcd.1 hbc
    have hgrid :
        gridPt n (b + 1) + π / n ≤
          gridPt n c := by
      rw [← gridPt_succ]
      exact hmono hgap
    rw [abs_of_nonpos (by linarith [hx.2, hy.1])]
    linarith [hx.2, hy.1]
  · have hgap : d + 2 ≤ a := dangerousRuns_sep hcd.1 hab.1 hda
    have hgrid :
        gridPt n (d + 1) + π / n ≤
          gridPt n a := by
      rw [← gridPt_succ]
      exact hmono hgap
    rw [abs_of_nonneg (by linarith [hx.1, hy.2])]
    linarith [hx.1, hy.2]

private theorem rs_odd_axis_values (k : ℕ) :
    (rudinShapiroP (2 * k + 1)).eval 1 = (2 ^ (k + 1) : ℕ) ∧
    (rudinShapiroQ (2 * k + 1)).eval 1 = 0 ∧
    (rudinShapiroP (2 * k + 1)).eval (-1) = 0 ∧
    (rudinShapiroQ (2 * k + 1)).eval (-1) = (2 ^ (k + 1) : ℕ) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rcases ih with ⟨hP1, hQ1, hPm1, hQm1⟩
      have hs : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
      rw [hs, show (2 * k + 1) + 2 = ((2 * k + 1) + 1) + 1 by omega]
      rw [eval_rsP_succ ((2 * k + 1) + 1) 1,
        eval_rsQ_succ ((2 * k + 1) + 1) 1,
        eval_rsP_succ ((2 * k + 1) + 1) (-1),
        eval_rsQ_succ ((2 * k + 1) + 1) (-1)]
      rw [eval_rsP_succ (2 * k + 1) 1,
        eval_rsQ_succ (2 * k + 1) 1,
        eval_rsP_succ (2 * k + 1) (-1),
        eval_rsQ_succ (2 * k + 1) (-1)]
      rw [hP1, hQ1, hPm1, hQm1]
      norm_num [pow_succ]
      ring

private theorem sqrt_two_pow_odd_succ (k : ℕ) :
    sqrt (2 ^ ((2 * k + 1) + 1) : ℝ) = (2 ^ (k + 1) : ℕ) := by
  rw [show (2 * k + 1) + 1 = (k + 1) * 2 by omega, pow_mul]
  rw [sqrt_sq_eq_abs, abs_of_nonneg]
  · norm_num
  · positivity

theorem normH_re_zero_of_odd {t : ℕ} (ht : Odd t) :
    (normH t 0).re = 1 := by
  obtain ⟨k, rfl⟩ := ht
  rcases rs_odd_axis_values k with ⟨hP1, hQ1, _hPm1, _hQm1⟩
  have hunit0 : unitPt 0 = 1 := by simp [unitPt]
  simp only [normH, scDerivP, scDerivQ, pow_zero,
    one_mul, Function.iterate_zero_apply, hunit0, zero_div, rsNormalization]
  rw [hP1, hQ1, sqrt_two_pow_odd_succ]
  norm_num

private theorem unitPt_evenT_mul_pi (t : ℕ) :
    unitPt ((evenT t : ℝ) * π) = 1 := by
  rw [show unitPt ((evenT t : ℝ) * π) = unitPt π ^ evenT t by
    simp only [unitPt, ← exp_nat_mul]
    congr 1
    push_cast
    ring]
  have hpi : unitPt π = -1 := by simp [unitPt]
  rw [hpi]
  rw [show evenT t = 2 * 2 ^ (t + 9) by simp [evenT, pow_succ']]
  rw [pow_mul]
  norm_num

theorem normH_re_evenT_mul_pi_of_odd {t : ℕ} (ht : Odd t) :
    (normH t ((evenT t : ℝ) * π)).re = 1 := by
  obtain ⟨k, rfl⟩ := ht
  rcases rs_odd_axis_values k with ⟨_hP1, _hQ1, hPm1, hQm1⟩
  have hTpos : (0 : ℝ) < evenT (2 * k + 1) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) ((2 * k + 1) + 10))
  have hdiv :
      ((evenT (2 * k + 1) : ℝ) * π) / evenT (2 * k + 1) =
        π := by
    field_simp
  have hphase₁ := unitPt_evenT_mul_pi (2 * k + 1)
  have hphase₂ :
      unitPt (2 * ((evenT (2 * k + 1) : ℝ) * π)) = 1 := by
    rw [show 2 * ((evenT (2 * k + 1) : ℝ) * π) =
      (evenT (2 * k + 1) : ℝ) * π +
        (evenT (2 * k + 1) : ℝ) * π by ring]
    rw [show unitPt
        ((evenT (2 * k + 1) : ℝ) * π +
          (evenT (2 * k + 1) : ℝ) * π) =
        unitPt ((evenT (2 * k + 1) : ℝ) * π) *
          unitPt ((evenT (2 * k + 1) : ℝ) * π) by
      simp [unitPt, Complex.exp_add, add_mul]]
    rw [hphase₁]
    norm_num
  simp only [normH, scDerivP, scDerivQ, pow_zero,
    one_mul, Function.iterate_zero_apply, hphase₁, hphase₂, hdiv,
    show unitPt π = -1 by simp [unitPt], rsNormalization]
  rw [hPm1, hQm1, sqrt_two_pow_odd_succ]
  norm_num

theorem thr_lt_half_normalization
    {n t : ℕ} {γ : ℝ} (hparam : Params n t γ) :
    thr n γ < sqrt (2 ^ (t + 1) : ℝ) / 2 := by
  have hγ0 : 0 ≤ γ := (hparam.gamma_pos).le
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hthreshold0 : 0 ≤ thr n γ := by
    exact (thr_pos hparam.n_pos hparam.gamma_pos).le
  have hscale0 : 0 < sqrt (2 ^ (t + 1) : ℝ) := by positivity
  have hscaleSq : (sqrt (2 ^ (t + 1) : ℝ)) ^ 2 = 2 ^ (t + 1) :=
    sq_sqrt (by positivity)
  have hthresholdSq :
      (thr n γ) ^ 2 =
        (1 / 2 ^ 16 : ℝ) * (γ ^ 7 * n) := by
    simp only [thr, cosDelta, mul_pow]
    rw [sq_sqrt hγ0, sq_sqrt hn0]
    ring
  have hγOne : γ ≤ 1 :=
    hparam.gamma_upper.trans (by norm_num)
  have hγPow : γ ^ 6 ≤ 1 := by
    exact pow_le_one₀ hγ0 hγOne
  have hnum : paramNum t < 2 ^ (t + 12) := by
    have hpowpos : 0 < 2 ^ t := by positivity
    simp only [paramNum, pow_add]
    norm_num
    omega
  have hnumR : (paramNum t : ℝ) < (2 : ℝ) ^ (t + 12) := by
    exact_mod_cast hnum
  have hγNum : γ ^ 7 * (n : ℝ) < (2 : ℝ) ^ (t + 12) := by
    calc
      γ ^ 7 * (n : ℝ) = γ ^ 6 * (γ * n) := by ring
      _ = γ ^ 6 * paramNum t := by rw [hparam.equation]
      _ ≤ 1 * paramNum t := by
        exact mul_le_mul_of_nonneg_right hγPow (by positivity)
      _ < (2 : ℝ) ^ (t + 12) := by simpa using hnumR
  have hsqLt :
      (thr n γ) ^ 2 <
        (sqrt (2 ^ (t + 1) : ℝ) / 2) ^ 2 := by
    rw [hthresholdSq, div_pow, hscaleSq]
    calc
      (1 / 2 ^ 16 : ℝ) * (γ ^ 7 * n) <
          (1 / 2 ^ 16 : ℝ) * 2 ^ (t + 12) := by gcongr
      _ < (2 ^ (t + 1) : ℝ) / 2 ^ 2 := by
        norm_num [pow_add]
        have hpow : (0 : ℝ) < 2 ^ t := by positivity
        nlinarith
  nlinarith

private theorem normH_re_gt_half_of_close
    {t : ℕ} {axis x : ℝ}
    (haxis : (normH t axis).re = 1)
    (hdiff : Differentiable ℝ (fun y ↦ (normH t y).re))
    (hderiv : ∀ y,
      |iteratedDeriv 1 (fun z ↦ (normH t z).re) y| ≤ 18)
    (hclose : 18 * |x - axis| < 1 / 2) :
    1 / 2 < (normH t x).re := by
  have hmean :
      |(normH t x).re - (normH t axis).re| ≤
        18 * |x - axis| := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (s := Set.univ) (f := fun y ↦ (normH t y).re)
      (x := axis) (y := x)
      (fun y _ ↦ hdiff.differentiableAt)
      (fun y _ ↦ by
        simpa only [norm_eq_abs, iteratedDeriv_succ', iteratedDeriv_zero]
          using hderiv y)
      convex_univ (Set.mem_univ axis) (Set.mem_univ x)
    simpa only [norm_eq_abs, abs_sub_comm] using h
  rw [haxis] at hmean
  have := (abs_le.mp hmean).1
  linarith

private theorem two_mul_evenT_div_n_lt_gamma
    {n t : ℕ} {γ : ℝ} (hparam : Params n t γ) :
    (2 * evenT t : ℝ) / n < γ := by
  obtain ⟨k, ht⟩ := hparam.t_odd
  have htpos : 0 < t := by omega
  have hpow : 1 < 2 ^ t := by
    exact one_lt_pow₀ (by norm_num) htpos.ne'
  have hnat : 2 * evenT t < paramNum t := by
    rw [paramNum, two_mul_evenT]
    omega
  have hreal : (2 * evenT t : ℝ) < γ * n := by
    rw [hparam.equation]
    exact_mod_cast hnat
  have hnR : (0 : ℝ) < n := by exact_mod_cast hparam.n_pos
  exact (div_lt_iff₀ hnR).2 hreal

private theorem axis_close_numeric
    {n t : ℕ} {γ : ℝ} (hparam : Params n t γ)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : C ≤ 101) :
    18 * C * π * ((2 * evenT t : ℝ) / n) < 1 / 2 := by
  have hratio := two_mul_evenT_div_n_lt_gamma hparam
  have hγ0 := hparam.gamma_pos.le
  calc
    18 * C * π * ((2 * evenT t : ℝ) / n) ≤
        18 * C * π * γ := by
      apply mul_le_mul_of_nonneg_left hratio.le
      positivity
    _ ≤ 18 * 101 * 4 * (1 / 2 ^ 40 : ℝ) := by
      gcongr
      · exact Real.pi_le_four
      · exact hparam.gamma_upper
    _ < 1 / 2 := by norm_num

theorem not_badCell_of_left_axis
    {n t i : ℕ} {γ : ℝ} (hparam : Params n t γ)
    (hdiff : Differentiable ℝ (fun y ↦ (normH t y).re))
    (hderiv : ∀ y,
      |iteratedDeriv 1 (fun z ↦ (normH t z).re) y| ≤ 18)
    (hi : i < 100) :
    ¬BadCell n t γ i := by
  rintro ⟨θ, hθ, hsmall⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hparam.n_pos
  have hmono := gridPt_mono hparam.n_pos
  have hθ0 : 0 ≤ θ := by
    have hgp : 0 ≤ gridPt n i := by
      rw [← gridPt_zero n]
      exact hmono (Nat.zero_le i)
    exact hgp.trans hθ.1
  have hθ100 : θ ≤ 100 * π / n := by
    calc
      θ ≤ gridPt n (i + 1) := hθ.2
      _ ≤ gridPt n 100 := hmono (by omega)
      _ = 100 * π / n := by simp [gridPt]
  let x : ℝ := 2 * evenT t * θ
  have hxclose : 18 * |x - 0| < 1 / 2 := by
    have hT0 : (0 : ℝ) ≤ 2 * evenT t := by positivity
    rw [sub_zero, abs_of_nonneg (mul_nonneg hT0 hθ0)]
    calc
      18 * (2 * (evenT t : ℝ) * θ) ≤
          18 * (2 * (evenT t : ℝ) * (100 * π / n)) := by gcongr
      _ = 18 * 100 * π * ((2 * evenT t : ℝ) / n) := by ring
      _ < 1 / 2 := axis_close_numeric hparam (by norm_num) (by norm_num)
  have hxhalf : 1 / 2 < (normH t x).re :=
    normH_re_gt_half_of_close
      (normH_re_zero_of_odd hparam.t_odd) hdiff hderiv hxclose
  have hscale : 0 < sqrt (2 ^ (t + 1) : ℝ) := by positivity
  have hthreshold := thr_lt_half_normalization hparam
  have hcos : thr n γ < evenCos t θ := by
    rw [evenCos_eq_normH]
    change thr n γ <
      sqrt (2 ^ (t + 1) : ℝ) * (normH t x).re
    nlinarith
  have habs : evenCos t θ ≤ |evenCos t θ| := le_abs_self _
  linarith

theorem not_badCell_of_right_axis
    {n t i : ℕ} {γ : ℝ} (hparam : Params n t γ)
    (hdiff : Differentiable ℝ (fun y ↦ (normH t y).re))
    (hderiv : ∀ y,
      |iteratedDeriv 1 (fun z ↦ (normH t z).re) y| ≤ 18)
    (hiFirst : 2 * (i + 1) ≤ n)
    (hiNear : ¬2 * (i + 1 + 100) ≤ n) :
    ¬BadCell n t γ i := by
  rintro ⟨θ, hθ, hsmall⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hparam.n_pos
  have hiFirstR : (2 : ℝ) * (i + 1) ≤ n := by exact_mod_cast hiFirst
  have hiNearNat : n < 2 * (i + 101) := by omega
  have hiNearR : (n : ℝ) < 2 * (i + 101) := by exact_mod_cast hiNearNat
  have hrightEndpoint :
      gridPt n (i + 1) ≤ π / 2 := by
    simp only [gridPt, Nat.cast_add, Nat.cast_one]
    apply (div_le_iff₀ hnR).2
    field_simp [hnR.ne']
    nlinarith [pi_pos]
  have hθAxis : θ ≤ π / 2 :=
    hθ.2.trans hrightEndpoint
  have hgridDist :
      π / 2 - gridPt n i <
        101 * π / n := by
    simp only [gridPt]
    apply (sub_lt_iff_lt_add).2
    rw [← add_div]
    apply (lt_div_iff₀ hnR).2
    nlinarith [pi_pos]
  have hθDist : π / 2 - θ < 101 * π / n := by
    linarith [hθ.1, hgridDist]
  have hθDist0 : 0 ≤ π / 2 - θ := sub_nonneg.mpr hθAxis
  let x : ℝ := 2 * evenT t * θ
  let axis : ℝ := evenT t * π
  have hxclose : 18 * |x - axis| < 1 / 2 := by
    have hT0 : (0 : ℝ) ≤ 2 * evenT t := by positivity
    rw [show x - axis =
        -(2 * (evenT t : ℝ)) * (π / 2 - θ) by
      dsimp only [x, axis]
      ring]
    rw [abs_mul, abs_neg, abs_of_nonneg hT0, abs_of_nonneg hθDist0]
    calc
      18 * (2 * (evenT t : ℝ) * (π / 2 - θ)) ≤
          18 * (2 * (evenT t : ℝ) * (101 * π / n)) := by
            gcongr
      _ = 18 * 101 * π * ((2 * evenT t : ℝ) / n) := by ring
      _ < 1 / 2 := axis_close_numeric hparam (by norm_num) (by norm_num)
  have hxhalf : 1 / 2 < (normH t x).re :=
    normH_re_gt_half_of_close
      (show (normH t axis).re = 1 by
        dsimp only [axis]
        exact normH_re_evenT_mul_pi_of_odd hparam.t_odd)
      hdiff hderiv hxclose
  have hscale : 0 < sqrt (2 ^ (t + 1) : ℝ) := by positivity
  have hthreshold := thr_lt_half_normalization hparam
  have hcos : thr n γ < evenCos t θ := by
    rw [evenCos_eq_normH]
    change thr n γ <
      sqrt (2 ^ (t + 1) : ℝ) * (normH t x).re
    nlinarith
  have habs : evenCos t θ ≤ |evenCos t θ| := le_abs_self _
  linarith

theorem not_badCell_middle_axis
    {n t : ℕ} {γ : ℝ} (hparam : Params n t γ)
    (hdiff : Differentiable ℝ (fun y ↦ (normH t y).re))
    (hderiv : ∀ y,
      |iteratedDeriv 1 (fun z ↦ (normH t z).re) y| ≤ 18) :
    ¬BadCell n t γ (n / 2) := by
  rintro ⟨θ, hθ, hsmall⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hparam.n_pos
  have hqLower : 2 * (n / 2) ≤ n := by omega
  have hqUpper : n < 2 * (n / 2 + 1) := by omega
  have hqLowerR : (2 : ℝ) * ((n / 2 : ℕ) : ℝ) ≤ n := by
    exact_mod_cast hqLower
  have hqUpperR : (n : ℝ) < 2 * (((n / 2 : ℕ) : ℝ) + 1) := by
    exact_mod_cast hqUpper
  have hgridLower :
      π / 2 - π / n ≤
        gridPt n (n / 2) := by
    simp only [gridPt]
    field_simp [hnR.ne']
    nlinarith [pi_pos]
  have hgridUpper :
      gridPt n (n / 2 + 1) ≤
        π / 2 + π / n := by
    simp only [gridPt, Nat.cast_add, Nat.cast_one]
    field_simp [hnR.ne']
    nlinarith [pi_pos]
  have hθDist : |θ - π / 2| ≤ π / n := by
    rw [abs_le]
    constructor <;> linarith [hθ.1, hθ.2, hgridLower, hgridUpper]
  let x : ℝ := 2 * evenT t * θ
  let axis : ℝ := evenT t * π
  have hxclose : 18 * |x - axis| < 1 / 2 := by
    have hT0 : (0 : ℝ) ≤ 2 * evenT t := by positivity
    rw [show x - axis =
        (2 * (evenT t : ℝ)) * (θ - π / 2) by
      dsimp only [x, axis]
      ring]
    rw [abs_mul, abs_of_nonneg hT0]
    calc
      18 * (2 * (evenT t : ℝ) * |θ - π / 2|) ≤
          18 * (2 * (evenT t : ℝ) * (π / n)) := by gcongr
      _ = 18 * 1 * π * ((2 * evenT t : ℝ) / n) := by ring
      _ < 1 / 2 := axis_close_numeric hparam (by norm_num) (by norm_num)
  have hxhalf : 1 / 2 < (normH t x).re :=
    normH_re_gt_half_of_close
      (show (normH t axis).re = 1 by
        dsimp only [axis]
        exact normH_re_evenT_mul_pi_of_odd hparam.t_odd)
      hdiff hderiv hxclose
  have hscale : 0 < sqrt (2 ^ (t + 1) : ℝ) := by positivity
  have hthreshold := thr_lt_half_normalization hparam
  have hcos : thr n γ < evenCos t θ := by
    rw [evenCos_eq_normH]
    change thr n γ <
      sqrt (2 ^ (t + 1) : ℝ) * (normH t x).re
    nlinarith
  have habs : evenCos t θ ≤ |evenCos t θ| := le_abs_self _
  linarith

theorem firstQuadIvls_away_from_axes_of_badCell_exclusion
    {n t : ℕ} {γ : ℝ} (hn : 0 < n)
    (hleft : ∀ i, i < 100 → ¬BadCell n t γ i)
    (hright : ∀ i, 2 * (i + 1) ≤ n → ¬2 * (i + 1 + 100) ≤ n →
      ¬BadCell n t γ i) :
    ∀ I ∈ firstQuadIvls n t γ,
      100 * π / n ≤ I.1 ∧
        I.2 ≤ π / 2 - 100 * π / n := by
  classical
  intro I hI
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hI
  rw [mem_firstQuadRuns] at hab
  have hrun :
      IsMaximalBadRun (2 * n) (BadCell n t γ) a b := by
    simpa only [mem_dangerousRuns] using hab.1
  have hbada : BadCell n t γ a :=
    hrun.2.2.1 a (Finset.mem_range.mpr (hrun.1.trans_lt hrun.2.1)) le_rfl hrun.1
  have hbadb : BadCell n t γ b :=
    hrun.2.2.1 b (Finset.mem_range.mpr hrun.2.1) hrun.1 le_rfl
  have ha100 : 100 ≤ a := by
    by_contra ha
    exact hleft a (by omega) hbada
  have hb100 : 2 * (b + 1 + 100) ≤ n := by
    by_contra hb
    exact hright b hab.2 hb hbadb
  simp only [runEndpts]
  constructor
  · rw [show 100 * π / (n : ℝ) =
        gridPt n 100 by
      simp [gridPt]]
    exact gridPt_mono hn ha100
  · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hb100R : (2 : ℝ) * (b + 1 + 100) ≤ n := by exact_mod_cast hb100
    simp only [gridPt, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat]
    apply (div_le_iff₀ hnR).2
    field_simp [hnR.ne']
    nlinarith [pi_pos]

theorem geometricCertOfBadCellExclusion
    {n t : ℕ} {γ : ℝ} (hn : 0 < n)
    (hleft : ∀ i, i < 100 → ¬BadCell n t γ i)
    (hright : ∀ i, 2 * (i + 1) ≤ n → ¬2 * (i + 1 + 100) ≤ n →
      ¬BadCell n t γ i) :
    GeometricCert n t γ where
  separated := firstQuadIvls_pairwise_sep hn
  away_from_axes :=
    firstQuadIvls_away_from_axes_of_badCell_exclusion hn hleft hright

theorem geometricCert_of_params
    {n t : ℕ} {γ : ℝ} (hparam : Params n t γ) :
    GeometricCert n t γ := by
  have hdiff : Differentiable ℝ (fun y ↦ (normH t y).re) :=
    (contDiff_normH_re t).differentiable (by norm_num)
  have hderiv : ∀ y,
      |iteratedDeriv 1 (fun z ↦ (normH t z).re) y| ≤ 18 := by
    intro y
    exact abs_iteratedDeriv_normH_re_le_eighteen 1 (by omega) t y
  apply geometricCertOfBadCellExclusion hparam.n_pos
  · intro i hi
    exact not_badCell_of_left_axis hparam hdiff hderiv hi
  · intro i hiFirst hiNear
    exact not_badCell_of_right_axis hparam hdiff hderiv hiFirst hiNear

theorem low_pt_covered_by_firstQuadIvls
    {n t : ℕ} {γ θ : ℝ} (hparam : Params n t γ)
    (hθ : θ ∈ Icc 0 (π / 2))
    (hsmall : |evenCos t θ| < thr n γ) :
    ∃ I ∈ firstQuadIvls n t γ,
      InIvl I θ := by
  classical
  have hdiff : Differentiable ℝ (fun y ↦ (normH t y).re) :=
    (contDiff_normH_re t).differentiable (by norm_num)
  have hderiv : ∀ y,
      |iteratedDeriv 1 (fun z ↦ (normH t z).re) y| ≤ 18 := by
    intro y
    exact abs_iteratedDeriv_normH_re_le_eighteen 1 (by omega) t y
  have hnR : (0 : ℝ) < n := by exact_mod_cast hparam.n_pos
  let P : ℕ → Prop := fun k ↦
    θ ≤ gridPt n (k + 1)
  have hqUpper : n < 2 * (n / 2 + 1) := by omega
  have hqUpperR : (n : ℝ) < 2 * (((n / 2 : ℕ) : ℝ) + 1) := by
    exact_mod_cast hqUpper
  have haxisGrid :
      π / 2 ≤ gridPt n (n / 2 + 1) := by
    simp only [gridPt, Nat.cast_add, Nat.cast_one]
    field_simp [hnR.ne']
    nlinarith [pi_pos]
  have hPex : ∃ k, P k :=
    ⟨n / 2, hθ.2.trans haxisGrid⟩
  let i : ℕ := Nat.find hPex
  have hiright : θ ≤ gridPt n (i + 1) := by
    simpa only [i, P] using Nat.find_spec hPex
  have hileft : gridPt n i ≤ θ := by
    by_cases hi0 : i = 0
    · rw [hi0, gridPt_zero]
      exact hθ.1
    · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
      have hnot := Nat.find_min hPex (show i - 1 < Nat.find hPex by
        simpa only [i] using Nat.sub_lt hipos Nat.one_pos)
      have hpred : i - 1 + 1 = i := by omega
      change ¬θ ≤ gridPt n (i - 1 + 1) at hnot
      rw [hpred] at hnot
      exact (lt_of_not_ge hnot).le
  have hiq : i ≤ n / 2 := by
    exact Nat.find_min' hPex (hθ.2.trans haxisGrid)
  have hiN : i < 2 * n := by
    have hnpos : 0 < n := hparam.n_pos
    have hn2 : n < 2 * n := by omega
    exact hiq.trans_lt ((Nat.div_le_self n 2).trans_lt hn2)
  have hbad : BadCell n t γ i :=
    ⟨θ, ⟨hileft, hiright⟩, hsmall⟩
  obtain ⟨⟨a, b⟩, hab, hai, hib⟩ :=
    exists_mem_maximalBadRuns_containing hiN hbad
  have hrun : (a, b) ∈ dangerousRuns n t γ := by
    simpa only [dangerousRuns] using hab
  have hfirst : 2 * (b + 1) ≤ n := by
    by_contra hcross
    have hqLower : 2 * (n / 2) ≤ n := by omega
    have haq : a ≤ n / 2 := hai.trans hiq
    have hqb : n / 2 ≤ b := by omega
    have hmax :
        IsMaximalBadRun
          (2 * n) (BadCell n t γ) a b :=
      mem_dangerousRuns.mp hrun
    have hbadMiddle : BadCell n t γ (n / 2) :=
      hmax.2.2.1 (n / 2)
        (Finset.mem_range.mpr (by omega)) haq hqb
    exact not_badCell_middle_axis hparam hdiff hderiv hbadMiddle
  have hfirstRun : (a, b) ∈ firstQuadRuns n t γ :=
    mem_firstQuadRuns.mpr ⟨hrun, hfirst⟩
  refine ⟨runEndpts n (a, b), ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨(a, b), hfirstRun, rfl⟩
  · simp only [InIvl, runEndpts, mem_Icc]
    have hmono := gridPt_mono hparam.n_pos
    exact ⟨(hmono hai).trans hileft,
      hiright.trans (hmono (by omega))⟩

end

end CosConstr

end

section

namespace CosConstr

open Filter

noncomputable section

private lemma paramNum_two_mul_add_one_add_one (k : ℕ) :
    paramNum (2 * k + 1) + 1 = 4098 * 4 ^ k := by
  have hpow : 0 < 2 ^ ((2 * k + 1) + 11) := by positivity
  have hone : 1 ≤ 2 ^ ((2 * k + 1) + 11) + 2 ^ (2 * k + 1) :=
    hpow.trans_le (Nat.le_add_right _ _)
  rw [paramNum, Nat.sub_add_cancel hone]
  simp [pow_add, pow_mul]
  ring

theorem eventually_exists_params :
    ∀ᶠ n : ℕ in atTop, ∃ t γ, Params n t γ := by
  filter_upwards [eventually_ge_atTop (2 ^ 40 * 4098)] with n hn
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hx : (1 : ℝ) ≤ (n : ℝ) / (2 ^ 40 * 4098) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 40 * 4098)]
    exact_mod_cast hn
  obtain ⟨k, hklo, hkhi⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 4)
  let t := 2 * k + 1
  let γ := (paramNum t : ℝ) / n
  refine ⟨t, γ, ?_⟩
  constructor
  · exact hnpos
  · exact ⟨k, by simp [t]⟩
  · dsimp only [γ]
    field_simp
  · dsimp only [γ, t]
    have hnum : ((paramNum (2 * k + 1) : ℕ) : ℝ) + 1 =
        4098 * 4 ^ k := by
      exact_mod_cast paramNum_two_mul_add_one_add_one k
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ))]
    have hkpow : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
    have hnupper : (n : ℝ) < (2 ^ 40 * 4098) * 4 ^ (k + 1) := by
      simpa [mul_comm] using (div_lt_iff₀
        (by positivity : (0 : ℝ) < 2 ^ 40 * 4098)).mp hkhi
    rw [show (4 : ℝ) ^ (k + 1) = 4 ^ k * 4 by rw [pow_succ]] at hnupper
    norm_num at hnupper ⊢
    nlinarith
  · dsimp only [γ, t]
    have hnum : ((paramNum (2 * k + 1) : ℕ) : ℝ) + 1 =
        4098 * 4 ^ k := by
      exact_mod_cast paramNum_two_mul_add_one_add_one k
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ))]
    have hnlower : (2 ^ 40 * 4098 : ℝ) * 4 ^ k ≤ n := by
      simpa [mul_comm] using (le_div_iff₀
        (by positivity : (0 : ℝ) < 2 ^ 40 * 4098)).mp hklo
    norm_num at hnlower ⊢
    nlinarith

end

end CosConstr

end

section
namespace CosConstr

open Set

noncomputable section

def realChebyshev (p : Polynomial ℂ) : Polynomial ℝ :=
  ∑ k ∈ p.support,
    Polynomial.C (p.coeff k).re * Polynomial.Chebyshev.T ℝ (k : ℤ)

theorem eval_realChebyshev_cos
    (p : Polynomial ℂ)
    (hreal : ∀ k ∈ p.support, (p.coeff k).im = 0)
    (x : ℝ) :
    (realChebyshev p).eval (cos x) =
      (p.eval (unitPt x)).re := by
  classical
  rw [realChebyshev, eval_finsetSum,
    eval_eq_sum, sum_def]
  change (∑ k ∈ p.support,
      (Polynomial.C (p.coeff k).re * Polynomial.Chebyshev.T ℝ (k : ℤ)).eval
        (cos x)) =
    reLm (∑ k ∈ p.support, p.coeff k * unitPt x ^ k)
  rw [map_sum]
  apply sum_congr rfl
  intro k hk
  rw [eval_mul, Polynomial.eval_C,
    Polynomial.Chebyshev.T_real_cos]
  have hpow := congrArg re (unitPt_pow x k)
  have hre : (unitPt x ^ k).re = cos (k * x) := by
    simpa only [add_re, ofReal_re, mul_re,
      ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, mul_one, add_zero] using hpow
  change (p.coeff k).re * cos ((k : ℤ) * x) =
    (p.coeff k * unitPt x ^ k).re
  rw [mul_re, hreal k hk, zero_mul, sub_zero, hre]
  norm_cast

theorem cosBlk_coeff_im (t k : ℕ) :
    ((cosBlk t).coeff k).im = 0 := by
  classical
  by_cases hk : k ∈ (cosBlk t).support
  · rw [support_cosBlk, mem_evenCPrime] at hk
    rcases hk with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · rw [coeff_cosBlk_first t j hj]
      rcases coeff_rsP_eq_one_or_neg_one hj with h | h <;> simp [h]
    · rw [coeff_cosBlk_second t j hj]
      rcases coeff_rsQ_eq_one_or_neg_one hj with h | h <;> simp [h]
  · have hcoeff : (cosBlk t).coeff k = 0 := by
      simpa [mem_support_iff] using hk
    simp [hcoeff]

def evenChebyshev (t : ℕ) : Polynomial ℝ :=
  realChebyshev (cosBlk t)

theorem eval_evenChebyshev (t : ℕ) (x : ℝ) :
    (evenChebyshev t).eval (cos (2 * x)) =
      evenCos t x := by
  simpa only [evenChebyshev, evenCos] using
    eval_realChebyshev_cos (cosBlk t)
      (fun k _ ↦ cosBlk_coeff_im t k) (2 * x)

theorem natDegree_evenChebyshev_le (t : ℕ) :
    (evenChebyshev t).natDegree ≤ paramNum t := by
  classical
  rw [evenChebyshev, realChebyshev]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  have hk' : k ∈ (cosBlk t).support := by simpa using hk
  have hkBound : k ≤ paramNum t := by
    rw [support_cosBlk, mem_evenCPrime] at hk'
    rcases hk' with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · rw [paramNum, ← two_mul_evenT,
        Nat.add_sub_assoc (Nat.one_le_iff_ne_zero.mpr (by positivity))]
      have hjle : j ≤ 2 ^ t - 1 := Nat.le_sub_one_of_lt hj
      omega
    · rw [paramNum, ← two_mul_evenT,
        Nat.add_sub_assoc (Nat.one_le_iff_ne_zero.mpr (by positivity))]
      exact Nat.add_le_add_left (Nat.le_sub_one_of_lt hj) _
  calc
    (Polynomial.C ((cosBlk t).coeff k).re *
        Polynomial.Chebyshev.T ℝ (k : ℤ)).natDegree ≤
        (Polynomial.C ((cosBlk t).coeff k).re).natDegree +
          (Polynomial.Chebyshev.T ℝ (k : ℤ)).natDegree :=
      natDegree_mul_le
    _ ≤ 0 + k := by simp
    _ = k := by omega
    _ ≤ paramNum t := hkBound

private theorem paramNum_eq_topIdx (t : ℕ) :
    paramNum t = 2 * evenT t + (2 ^ t - 1) := by
  rw [paramNum, ← two_mul_evenT,
    Nat.add_sub_assoc (Nat.one_le_iff_ne_zero.mpr (by positivity))]

private theorem topIdx_mem_cosBlk_support (t : ℕ) :
    paramNum t ∈ (cosBlk t).support := by
  rw [paramNum_eq_topIdx, support_cosBlk,
    mem_evenCPrime]
  right
  exact ⟨2 ^ t - 1, Nat.sub_lt (by positivity) (by norm_num), rfl⟩

theorem natDegree_evenChebyshev (t : ℕ) :
    (evenChebyshev t).natDegree = paramNum t := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_evenChebyshev_le t)
  let m := paramNum t
  have hm : m ∈ (cosBlk t).support :=
    topIdx_mem_cosBlk_support t
  have hj : 2 ^ t - 1 < 2 ^ t := by
    have : 0 < 2 ^ t := by positivity
    omega
  have htop : ((cosBlk t).coeff m).re ≠ 0 := by
    rw [show m = 2 * evenT t + (2 ^ t - 1) from paramNum_eq_topIdx t]
    rw [coeff_cosBlk_second t (2 ^ t - 1) hj]
    rcases coeff_rsQ_eq_one_or_neg_one hj with h | h <;> simp [h]
  have hTtop : (Polynomial.Chebyshev.T ℝ (m : ℤ)).coeff m ≠ 0 := by
    have hdeg : (Polynomial.Chebyshev.T ℝ (m : ℤ)).natDegree = m := by simp
    have hc := Polynomial.coeff_natDegree
      (p := Polynomial.Chebyshev.T ℝ (m : ℤ))
    rw [hdeg] at hc
    rw [hc, Polynomial.Chebyshev.leadingCoeff_T]
    positivity
  change (evenChebyshev t).coeff m ≠ 0
  rw [evenChebyshev, realChebyshev,
    Polynomial.finsetSum_coeff, sum_eq_single m]
  · rw [coeff_C_mul]
    exact mul_ne_zero htop hTtop
  · intro k hk hkm
    have hkBound : k ≤ m := by
      rw [support_cosBlk, mem_evenCPrime] at hk
      rcases hk with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
      · rw [show m = 2 * evenT t + (2 ^ t - 1) from paramNum_eq_topIdx t]
        have hjle := Nat.le_sub_one_of_lt hj
        omega
      · rw [show m = 2 * evenT t + (2 ^ t - 1) from paramNum_eq_topIdx t]
        exact Nat.add_le_add_left (Nat.le_sub_one_of_lt hj) _
    have hklt : k < m := lt_of_le_of_ne hkBound hkm
    have hTzero : (Polynomial.Chebyshev.T ℝ (k : ℤ)).coeff m = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hklt)
    rw [coeff_C_mul, hTzero, mul_zero]
  · intro hnot
    exact (hnot hm).elim

theorem evenChebyshev_sub_C_ne_zero (t : ℕ) (c : ℝ) :
    evenChebyshev t - Polynomial.C c ≠ 0 := by
  intro hzero
  have hconst : evenChebyshev t = Polynomial.C c :=
    sub_eq_zero.mp hzero
  have hdeg := natDegree_evenChebyshev t
  rw [hconst] at hdeg
  have hmpos : 0 < paramNum t := by
    rw [paramNum_eq_topIdx]
    have hT : 0 < evenT t := by simp [evenT]
    omega
  simp at hdeg
  omega

theorem cont_evenCos (t : ℕ) : Continuous (evenCos t) := by
  unfold evenCos unitPt
  fun_prop

private abbrev QuadRun (n t : ℕ) (γ : ℝ) :=
  ↑(firstQuadRuns n t γ)

private noncomputable def runBadWitness {n t : ℕ} {γ : ℝ}
    (I : QuadRun n t γ) : ℝ :=
  Classical.choose (show BadCell n t γ I.1.1 by
    have hI := (mem_firstQuadRuns.mp I.2).1
    rw [mem_dangerousRuns] at hI
    exact hI.2.2.1 I.1.1 (Finset.mem_range.mpr (hI.1.trans_lt hI.2.1))
      le_rfl hI.1)

private theorem runBadWitness_mem {n t : ℕ} {γ : ℝ}
    (I : QuadRun n t γ) :
    runBadWitness I ∈ gridCell n I.1.1 := by
  exact (Classical.choose_spec (show BadCell n t γ I.1.1 by
    have hI := (mem_firstQuadRuns.mp I.2).1
    rw [mem_dangerousRuns] at hI
    exact hI.2.2.1 I.1.1 (Finset.mem_range.mpr (hI.1.trans_lt hI.2.1))
      le_rfl hI.1)).1

private theorem runBadWitness_lt {n t : ℕ} {γ : ℝ}
    (I : QuadRun n t γ) :
    |evenCos t (runBadWitness I)| < thr n γ := by
  exact (Classical.choose_spec (show BadCell n t γ I.1.1 by
    have hI := (mem_firstQuadRuns.mp I.2).1
    rw [mem_dangerousRuns] at hI
    exact hI.2.2.1 I.1.1 (Finset.mem_range.mpr (hI.1.trans_lt hI.2.1))
      le_rfl hI.1)).2

private theorem left_endpt_ge {n t : ℕ} {γ : ℝ}
    (hzero : thr n γ ≤ |evenCos t 0|)
    (I : QuadRun n t γ) :
    thr n γ ≤
      |evenCos t (gridPt n I.1.1)| := by
  have hI := (mem_firstQuadRuns.mp I.2).1
  rw [mem_dangerousRuns] at hI
  have hn : 0 < n := by
    have hb : I.1.2 < 2 * n := hI.2.1
    exact Nat.pos_of_ne_zero (fun hn0 ↦ by simpa [hn0] using hb)
  by_cases ha : I.1.1 = 0
  · simpa [ha, gridPt_zero] using hzero
  · have hgood : ¬BadCell n t γ (I.1.1 - 1) :=
      hI.2.2.2.1.resolve_left ha
    by_contra hlt
    rw [not_le] at hlt
    apply hgood
    refine ⟨gridPt n I.1.1, ?_, hlt⟩
    simp only [gridCell, mem_Icc]
    constructor
    · exact (gridPt_mono (by omega)) (Nat.sub_le _ _)
    · rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr ha)]

private theorem right_endpt_ge {n t : ℕ} {γ : ℝ}
    (hn : 0 < n)
    (hhalf : thr n γ ≤ |evenCos t (π / 2)|)
    (I : QuadRun n t γ) :
    thr n γ ≤
      |evenCos t (gridPt n (I.1.2 + 1))| := by
  have hmem := mem_firstQuadRuns.mp I.2
  have hI := hmem.1
  rw [mem_dangerousRuns] at hI
  by_cases heq : 2 * (I.1.2 + 1) = n
  · have hnEven : (n : ℝ) = 2 * (I.1.2 + 1 : ℕ) := by exact_mod_cast heq.symm
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have harg : gridPt n (I.1.2 + 1) = π / 2 := by
      rw [gridPt, div_eq_iff hnR]
      rw [hnEven]
      ring
    rwa [harg]
  · have hstrict : 2 * (I.1.2 + 1) < n := lt_of_le_of_ne hmem.2 heq
    have hnotlast : I.1.2 + 1 ≠ 2 * n := by omega
    have hgood : ¬BadCell n t γ (I.1.2 + 1) :=
      hI.2.2.2.2.resolve_left hnotlast
    by_contra hlt
    rw [not_le] at hlt
    apply hgood
    refine ⟨gridPt n (I.1.2 + 1), ?_, hlt⟩
    simp only [gridCell, mem_Icc]
    exact ⟨le_rfl, (gridPt_mono hn) (by omega)⟩

private theorem exists_left_contact {n t : ℕ} {γ : ℝ}
    (hn : 0 < n)
    (hzero : thr n γ ≤ |evenCos t 0|)
    (I : QuadRun n t γ) :
    ∃ x ∈ Icc (gridPt n I.1.1) (runBadWitness I),
      |evenCos t x| = thr n γ := by
  apply exists_abs_level_between (cont_evenCos t)
  · exact (runBadWitness_mem I).1
  · exact Or.inr ⟨runBadWitness_lt I, left_endpt_ge hzero I⟩

private theorem exists_right_contact {n t : ℕ} {γ : ℝ}
    (hn : 0 < n)
    (hhalf : thr n γ ≤ |evenCos t (π / 2)|)
    (I : QuadRun n t γ) :
    ∃ x ∈ Icc (runBadWitness I)
        (gridPt n (I.1.2 + 1)),
      |evenCos t x| = thr n γ := by
  apply exists_abs_level_between (cont_evenCos t)
  · have hw := (runBadWitness_mem I).2
    have hI := (mem_firstQuadRuns.mp I.2).1
    rw [mem_dangerousRuns] at hI
    exact hw.trans ((gridPt_mono hn)
      (Nat.add_le_add_right hI.1 1))
  · exact Or.inl ⟨runBadWitness_lt I, right_endpt_ge hn hhalf I⟩

private noncomputable def leftContact {n t : ℕ} {γ : ℝ}
    (hn : 0 < n)
    (hzero : thr n γ ≤ |evenCos t 0|)
    (I : QuadRun n t γ) : ℝ :=
  Classical.choose (exists_left_contact hn hzero I)

private noncomputable def rightContact {n t : ℕ} {γ : ℝ}
    (hn : 0 < n)
    (hhalf : thr n γ ≤ |evenCos t (π / 2)|)
    (I : QuadRun n t γ) : ℝ :=
  Classical.choose (exists_right_contact hn hhalf I)

private theorem leftContact_spec {n t : ℕ} {γ : ℝ}
    (hn : 0 < n)
    (hzero : thr n γ ≤ |evenCos t 0|)
    (I : QuadRun n t γ) :
    leftContact hn hzero I ∈
        Icc (gridPt n I.1.1) (runBadWitness I) ∧
      |evenCos t (leftContact hn hzero I)| = thr n γ :=
  Classical.choose_spec (exists_left_contact hn hzero I)

private theorem rightContact_spec {n t : ℕ} {γ : ℝ}
    (hn : 0 < n)
    (hhalf : thr n γ ≤ |evenCos t (π / 2)|)
    (I : QuadRun n t γ) :
    rightContact hn hhalf I ∈
        Icc (runBadWitness I) (gridPt n (I.1.2 + 1)) ∧
      |evenCos t (rightContact hn hhalf I)| = thr n γ :=
  Classical.choose_spec (exists_right_contact hn hhalf I)

private theorem leftContact_lt_witness {n t : ℕ} {γ : ℝ}
    (hn : 0 < n)
    (hzero : thr n γ ≤ |evenCos t 0|)
    (I : QuadRun n t γ) :
    leftContact hn hzero I < runBadWitness I := by
  have hs := leftContact_spec hn hzero I
  refine hs.1.2.lt_of_ne ?_
  intro heq
  have hv := hs.2
  rw [heq] at hv
  exact (runBadWitness_lt I).ne hv

private theorem witness_lt_rightContact {n t : ℕ} {γ : ℝ}
    (hn : 0 < n)
    (hhalf : thr n γ ≤ |evenCos t (π / 2)|)
    (I : QuadRun n t γ) :
    runBadWitness I < rightContact hn hhalf I := by
  have hs := rightContact_spec hn hhalf I
  refine hs.1.1.lt_of_ne ?_
  intro heq
  have hv := hs.2
  rw [← heq] at hv
  exact (runBadWitness_lt I).ne hv

private noncomputable def pairContact {n t : ℕ} {γ : ℝ}
    (hn : 0 < n)
    (hzero : thr n γ ≤ |evenCos t 0|)
    (hhalf : thr n γ ≤ |evenCos t (π / 2)|) :
    QuadRun n t γ × Fin 2 → ℝ
  | (I, k) => if (k : ℕ) = 0 then leftContact hn hzero I else rightContact hn hhalf I

private theorem pairContact_bounds {n t : ℕ} {γ : ℝ}
    (hn : 0 < n)
    (hzero : thr n γ ≤ |evenCos t 0|)
    (hhalf : thr n γ ≤ |evenCos t (π / 2)|)
    (K : QuadRun n t γ) (k : Fin 2) :
    gridPt n K.1.1 ≤ pairContact hn hzero hhalf (K, k) ∧
    pairContact hn hzero hhalf (K, k) ≤
      gridPt n (K.1.2 + 1) := by
  by_cases hk : (k : ℕ) = 0
  · simp only [pairContact, if_pos hk]
    refine ⟨(leftContact_spec hn hzero K).1.1, ?_⟩
    have hrun := mem_dangerousRuns.mp (mem_firstQuadRuns.mp K.2).1
    exact (leftContact_spec hn hzero K).1.2.trans <|
      (runBadWitness_mem K).2.trans <|
        (gridPt_mono hn) (Nat.add_le_add_right hrun.1 1)
  · simp only [pairContact, if_neg hk]
    have hleft := (runBadWitness_mem K).1
    exact ⟨hleft.trans (rightContact_spec hn hhalf K).1.1,
      (rightContact_spec hn hhalf K).1.2⟩

private theorem pairContact_level {n t : ℕ} {γ : ℝ}
    (hn : 0 < n)
    (hzero : thr n γ ≤ |evenCos t 0|)
    (hhalf : thr n γ ≤ |evenCos t (π / 2)|)
    (K : QuadRun n t γ) (k : Fin 2) :
    |evenCos t (pairContact hn hzero hhalf (K, k))| =
      thr n γ := by
  by_cases hk : (k : ℕ) = 0
  · simpa only [pairContact, if_pos hk] using (leftContact_spec hn hzero K).2
  · simpa only [pairContact, if_neg hk] using (rightContact_spec hn hhalf K).2

private theorem pairContact_injective {n t : ℕ} {γ : ℝ}
    (hn : 0 < n)
    (hzero : thr n γ ≤ |evenCos t 0|)
    (hhalf : thr n γ ≤ |evenCos t (π / 2)|) :
    Function.Injective (pairContact hn hzero hhalf) := by
  rintro ⟨I, i⟩ ⟨J, j⟩ hij
  have contact_bounds (K : QuadRun n t γ) (k : Fin 2) :
      gridPt n K.1.1 ≤ pairContact hn hzero hhalf (K, k) ∧
      pairContact hn hzero hhalf (K, k) ≤
        gridPt n (K.1.2 + 1) := by
    by_cases hk : (k : ℕ) = 0
    · simp only [pairContact, if_pos hk]
      have hspec := leftContact_spec hn hzero K
      refine ⟨hspec.1.1, ?_⟩
      have hrun := mem_dangerousRuns.mp (mem_firstQuadRuns.mp K.2).1
      exact (leftContact_spec hn hzero K).1.2.trans <|
        (runBadWitness_mem K).2.trans <|
          (gridPt_mono hn) (Nat.add_le_add_right hrun.1 1)
    · simp only [pairContact, if_neg hk]
      exact ⟨(runBadWitness_mem K).1.trans (rightContact_spec hn hhalf K).1.1,
        (rightContact_spec hn hhalf K).1.2⟩
  have hIJ : I = J := by
    apply Subtype.ext
    rcases lt_trichotomy I.1.1 J.1.1 with hlt | heq | hgt
    · have hI := (mem_firstQuadRuns.mp I.2).1
      have hJ := (mem_firstQuadRuns.mp J.2).1
      have hbc : I.1.2 < J.1.1 := by
        by_contra hnot
        have hmaxI := (mem_dangerousRuns.mp hI)
        have hmaxJ := (mem_dangerousRuns.mp hJ)
        have hJpos : 0 < J.1.1 := by omega
        have hpred : J.1.1 - 1 ≥ I.1.1 := by omega
        have hpred_le : J.1.1 - 1 ≤ I.1.2 := by omega
        have hbad := hmaxI.2.2.1 (J.1.1 - 1)
          (Finset.mem_range.mpr (hpred_le.trans_lt hmaxI.2.1)) hpred hpred_le
        exact hmaxJ.2.2.2.1.resolve_left (Nat.ne_of_gt hJpos) hbad
      have hsep := dangerousRuns_sep hI hJ hbc
      have hidx : I.1.2 + 1 < J.1.1 := by
        calc
          I.1.2 + 1 < (I.1.2 + 1) + 1 := Nat.lt_succ_self _
          _ ≤ J.1.1 := by simpa [Nat.add_assoc] using hsep
      have hgrid : gridPt n (I.1.2 + 1) <
          gridPt n J.1.1 :=
        gridPt_strictMono hn hidx
      have hi := pairContact_bounds hn hzero hhalf I i
      have hj := pairContact_bounds hn hzero hhalf J j
      rw [hij] at hi
      linarith
    · have hmaxI := mem_dangerousRuns.mp (mem_firstQuadRuns.mp I.2).1
      have hmaxJ := mem_dangerousRuns.mp (mem_firstQuadRuns.mp J.2).1
      exact IsMaximalBadRun.eq_of_start_eq hmaxI hmaxJ heq
    · have hI := (mem_firstQuadRuns.mp I.2).1
      have hJ := (mem_firstQuadRuns.mp J.2).1
      have hdc : J.1.2 < I.1.1 := by
        by_contra hnot
        have hmaxI := (mem_dangerousRuns.mp hI)
        have hmaxJ := (mem_dangerousRuns.mp hJ)
        have hIpos : 0 < I.1.1 := by omega
        have hpred : I.1.1 - 1 ≥ J.1.1 := by omega
        have hpred_le : I.1.1 - 1 ≤ J.1.2 := by omega
        have hbad := hmaxJ.2.2.1 (I.1.1 - 1)
          (Finset.mem_range.mpr (hpred_le.trans_lt hmaxJ.2.1)) hpred hpred_le
        exact hmaxI.2.2.2.1.resolve_left (Nat.ne_of_gt hIpos) hbad
      have hsep := dangerousRuns_sep hJ hI hdc
      have hidx : J.1.2 + 1 < I.1.1 := by
        calc
          J.1.2 + 1 < (J.1.2 + 1) + 1 := Nat.lt_succ_self _
          _ ≤ I.1.1 := by simpa [Nat.add_assoc] using hsep
      have hgrid : gridPt n (J.1.2 + 1) <
          gridPt n I.1.1 :=
        gridPt_strictMono hn hidx
      have hi := pairContact_bounds hn hzero hhalf I i
      have hj := pairContact_bounds hn hzero hhalf J j
      rw [hij] at hi
      linarith
  subst J
  congr 1
  by_contra hne
  have hfin : ((i : ℕ) = 0 ∧ (j : ℕ) ≠ 0) ∨
      ((i : ℕ) ≠ 0 ∧ (j : ℕ) = 0) := by
    omega
  rcases hfin with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · simp only [pairContact, if_pos hi, if_neg hj] at hij
    exact (leftContact_lt_witness hn hzero I).trans
      (witness_lt_rightContact hn hhalf I) |>.ne hij
  · simp only [pairContact, if_neg hi, if_pos hj] at hij
    exact (leftContact_lt_witness hn hzero I).trans
      (witness_lt_rightContact hn hhalf I) |>.ne hij.symm

private noncomputable def absLevelRoots
    (q : Polynomial ℝ) (level : ℝ) : Finset ℝ :=
  (q - Polynomial.C level).roots.toFinset ∪
    (q - Polynomial.C (-level)).roots.toFinset

private theorem card_absLevelRoots_le
    (q : Polynomial ℝ) (level : ℝ) :
    (absLevelRoots q level).card ≤ 2 * q.natDegree := by
  have hplus : (q - Polynomial.C level).roots.toFinset.card ≤ q.natDegree :=
    (Multiset.toFinset_card_le _).trans <|
      (card_roots' _).trans <|
        (natDegree_sub_le _ _).trans <| by
          simp only [max_le_iff]
          exact ⟨le_rfl, by simp⟩
  have hminus : (q - Polynomial.C (-level)).roots.toFinset.card ≤ q.natDegree :=
    (Multiset.toFinset_card_le _).trans <|
      (card_roots' _).trans <|
        (natDegree_sub_le _ _).trans <| by
          simp only [max_le_iff]
          exact ⟨le_rfl, by simp⟩
  calc
    (absLevelRoots q level).card ≤
        (q - Polynomial.C level).roots.toFinset.card +
          (q - Polynomial.C (-level)).roots.toFinset.card :=
      card_union_le _ _
    _ ≤ q.natDegree + q.natDegree := Nat.add_le_add hplus hminus
    _ = 2 * q.natDegree := by omega

private theorem eval_mem_absLevelRoots
    {q : Polynomial ℝ} {level x : ℝ}
    (hlevel : 0 ≤ level)
    (hplus : q - Polynomial.C level ≠ 0)
    (hminus : q - Polynomial.C (-level) ≠ 0)
    (hx : |q.eval x| = level) :
    x ∈ absLevelRoots q level := by
  rw [abs_eq hlevel] at hx
  rw [absLevelRoots, Finset.mem_union]
  rcases hx with hx | hx
  · left
    rw [Multiset.mem_toFinset, mem_roots hplus, Polynomial.IsRoot.def]
    simp [hx]
  · right
    rw [Multiset.mem_toFinset, mem_roots hminus, Polynomial.IsRoot.def]
    simp [hx]

theorem card_firstQuadRuns_le_poly_degree
    {n t : ℕ} {γ : ℝ}
    (hn : 0 < n)
    (hlevel : 0 ≤ thr n γ)
    (hzero : thr n γ ≤ |evenCos t 0|)
    (hhalf : thr n γ ≤ |evenCos t (π / 2)|)
    (q : Polynomial ℝ)
    (hq : ∀ x, q.eval (cos (2 * x)) = evenCos t x)
    (hplus : q - Polynomial.C (thr n γ) ≠ 0)
    (hminus : q - Polynomial.C (-thr n γ) ≠ 0) :
    (firstQuadRuns n t γ).card ≤ q.natDegree := by
  let roots := absLevelRoots q (thr n γ)
  let f : QuadRun n t γ × Fin 2 → ↑roots := fun p ↦
    ⟨cos (2 * pairContact hn hzero hhalf p), by
      apply eval_mem_absLevelRoots hlevel hplus hminus
      rw [hq]
      exact pairContact_level hn hzero hhalf p.1 p.2⟩
  have hcos_inj : Set.InjOn (fun x : ℝ ↦ cos (2 * x))
      (Icc 0 (π / 2)) := by
    intro x hx y hy hxy
    have h2x : 2 * x ∈ Icc (0 : ℝ) π := by
      constructor
      · exact mul_nonneg (by norm_num) hx.1
      · calc
          2 * x ≤ 2 * (π / 2) := mul_le_mul_of_nonneg_left hx.2 (by norm_num)
          _ = π := by ring
    have h2y : 2 * y ∈ Icc (0 : ℝ) π := by
      constructor
      · exact mul_nonneg (by norm_num) hy.1
      · calc
          2 * y ≤ 2 * (π / 2) := mul_le_mul_of_nonneg_left hy.2 (by norm_num)
          _ = π := by ring
    have := Real.injOn_cos h2x h2y hxy
    linarith
  have hf : Function.Injective f := by
    intro p r hpr
    apply pairContact_injective hn hzero hhalf
    apply hcos_inj
    · constructor
      · exact (show 0 ≤ gridPt n p.1.1.1 by
          exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) pi_pos.le)
            (Nat.cast_nonneg _)).trans
          (pairContact_bounds hn hzero hhalf p.1 p.2).1
      · have hp := (mem_firstQuadRuns.mp p.1.2).2
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn
        have hcast : (2 : ℝ) * ((p.1.1.2 + 1 : ℕ) : ℝ) ≤ n := by
          exact_mod_cast hp
        apply (pairContact_bounds hn hzero hhalf p.1 p.2).2.trans
        simp only [gridPt]
        apply (div_le_iff₀ hnR).2
        nlinarith [pi_pos]
    · constructor
      · exact (show 0 ≤ gridPt n r.1.1.1 by
          exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) pi_pos.le)
            (Nat.cast_nonneg _)).trans
          (pairContact_bounds hn hzero hhalf r.1 r.2).1
      · have hr := (mem_firstQuadRuns.mp r.1.2).2
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn
        have hcast : (2 : ℝ) * ((r.1.1.2 + 1 : ℕ) : ℝ) ≤ n := by
          exact_mod_cast hr
        apply (pairContact_bounds hn hzero hhalf r.1 r.2).2.trans
        simp only [gridPt]
        apply (div_le_iff₀ hnR).2
        nlinarith [pi_pos]
    · exact Subtype.ext_iff.mp hpr
  have hcard := Fintype.card_le_of_injective f hf
  have hrootcard : roots.card ≤ 2 * q.natDegree :=
    card_absLevelRoots_le q (thr n γ)
  have htwice : 2 * (firstQuadRuns n t γ).card ≤ 2 * q.natDegree := by
    calc
      2 * (firstQuadRuns n t γ).card = Fintype.card (QuadRun n t γ × Fin 2) := by
        simp [Fintype.card_prod, mul_comm]
      _ ≤ Fintype.card ↑roots := hcard
      _ = roots.card := card_coe _
      _ ≤ 2 * q.natDegree := hrootcard
  omega

theorem card_firstQuadRuns_le_paramNum_of_poly
    {n t : ℕ} {γ : ℝ}
    (hn : 0 < n)
    (hlevel : 0 ≤ thr n γ)
    (hzero : thr n γ ≤ |evenCos t 0|)
    (hhalf : thr n γ ≤ |evenCos t (π / 2)|)
    (q : Polynomial ℝ)
    (hq : ∀ x, q.eval (cos (2 * x)) = evenCos t x)
    (hplus : q - Polynomial.C (thr n γ) ≠ 0)
    (hminus : q - Polynomial.C (-thr n γ) ≠ 0)
    (hdegree : q.natDegree ≤ paramNum t) :
    (firstQuadRuns n t γ).card ≤ paramNum t :=
  (card_firstQuadRuns_le_poly_degree hn hlevel hzero hhalf q hq hplus hminus).trans
    hdegree

theorem card_firstQuadRuns_le_paramNum
    {n t : ℕ} {γ : ℝ}
    (hn : 0 < n)
    (hlevel : 0 ≤ thr n γ)
    (hzero : thr n γ ≤ |evenCos t 0|)
    (hhalf : thr n γ ≤ |evenCos t (π / 2)|) :
    (firstQuadRuns n t γ).card ≤ paramNum t := by
  apply card_firstQuadRuns_le_paramNum_of_poly
    hn hlevel hzero hhalf (evenChebyshev t)
  · exact eval_evenChebyshev t
  · exact evenChebyshev_sub_C_ne_zero t _
  · exact evenChebyshev_sub_C_ne_zero t _
  · exact natDegree_evenChebyshev_le t

end

end CosConstr

end

section

open Filter

def IsSign (a : ℂ) : Prop := a = 1 ∨ a = -1

theorem IsSign.norm_eq_one {a : ℂ} (ha : IsSign a) : ‖a‖ = 1 := by
  rcases ha with rfl | rfl <;> simp

def IsLittlewood (n : ℕ) (p : Polynomial ℂ) : Prop :=
  p.degree = n ∧ ∀ i ≤ n, IsSign (p.coeff i)

noncomputable def ofCoeffs (n : ℕ) (a : Fin (n + 1) → ℂ) : Polynomial ℂ :=
  ∑ i : Fin (n + 1), monomial (i : ℕ) (a i)

theorem coeff_ofCoeffs_of_le (n i : ℕ) (a : Fin (n + 1) → ℂ) (hi : i ≤ n) :
    (ofCoeffs n a).coeff i = a ⟨i, Nat.lt_succ_iff.mpr hi⟩ := by
  classical
  change lcoeff ℂ i
      (∑ j : Fin (n + 1), monomial (j : ℕ) (a j)) = _
  rw [map_sum]
  rw [sum_eq_single ⟨i, Nat.lt_succ_iff.mpr hi⟩]
  · simp
  · intro j _ hj
    simp only [lcoeff_apply, coeff_monomial]
    rw [if_neg]
    intro hji
    apply hj
    exact Fin.ext hji
  · simp

theorem coeff_ofCoeffs_of_lt (n i : ℕ) (a : Fin (n + 1) → ℂ) (hi : n < i) :
    (ofCoeffs n a).coeff i = 0 := by
  classical
  change lcoeff ℂ i
      (∑ j : Fin (n + 1), monomial (j : ℕ) (a j)) = 0
  rw [map_sum]
  apply sum_eq_zero
  intro j _
  simp only [lcoeff_apply, coeff_monomial]
  rw [if_neg]
  exact ne_of_lt ((Nat.le_of_lt_succ j.isLt).trans_lt hi)

theorem eval_ofCoeffs (n : ℕ) (a : Fin (n + 1) → ℂ) (z : ℂ) :
    (ofCoeffs n a).eval z = ∑ i, a i * z ^ (i : ℕ) := by
  classical
  simpa [ofCoeffs] using eval_finsetSum (Finset.univ : Finset (Fin (n + 1)))
    (fun i : Fin (n + 1) ↦ monomial (i : ℕ) (a i)) z

theorem degree_ofCoeffs (n : ℕ) (a : Fin (n + 1) → ℂ) (ha : a ⟨n, Nat.lt_succ_self n⟩ ≠ 0) :
    (ofCoeffs n a).degree = n := by
  apply degree_eq_of_le_of_coeff_ne_zero
  · rw [degree_le_iff_coeff_zero]
    intro m hm
    exact coeff_ofCoeffs_of_lt n m a (by exact_mod_cast hm)
  · simpa [coeff_ofCoeffs_of_le n n a le_rfl] using ha

theorem isLittlewood_ofCoeffs (n : ℕ) (a : Fin (n + 1) → ℂ)
    (ha : ∀ i, IsSign (a i)) : IsLittlewood n (ofCoeffs n a) := by
  constructor
  · apply degree_ofCoeffs
    rcases ha ⟨n, Nat.lt_succ_self n⟩ with h | h <;> simp [h]
  · intro i hi
    rw [coeff_ofCoeffs_of_le n i a hi]
    exact ha ⟨i, Nat.lt_succ_iff.mpr hi⟩

def HasFlatBounds (δ Δ : ℝ) (n : ℕ) (p : Polynomial ℂ) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 →
    δ * sqrt n ≤ ‖p.eval z‖ ∧ ‖p.eval z‖ ≤ Δ * sqrt n

def HasStrictTargetBounds (c₁ c₂ : ℝ) (n : ℕ) (p : Polynomial ℂ) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 →
    sqrt n < c₁ * ‖p.eval z‖ ∧
      ‖p.eval z‖ < c₂ * sqrt n

theorem hasStrictTargetBounds_of_hasFlatBounds {δ Δ : ℝ} {n : ℕ}
    {p : Polynomial ℂ} (hδ : 0 < δ) (hΔ : 0 < Δ) (hn : 0 < n)
    (hp : HasFlatBounds δ Δ n p) :
    HasStrictTargetBounds (2 / δ) (2 * Δ) n p := by
  intro z hz
  have hsqrt : 0 < sqrt n := sqrt_pos.2 (by exact_mod_cast hn)
  obtain ⟨hlower, hupper⟩ := hp z hz
  constructor
  · have hmul : 2 * sqrt n ≤ (2 / δ) * ‖p.eval z‖ := by
      calc
        2 * sqrt n = (2 / δ) * (δ * sqrt n) := by field_simp
        _ ≤ (2 / δ) * ‖p.eval z‖ :=
          mul_le_mul_of_nonneg_left hlower (by positivity)
    linarith
  · have hstrict : Δ * sqrt n < (2 * Δ) * sqrt n := by
      have := mul_pos hΔ hsqrt
      nlinarith
    exact hupper.trans_lt hstrict

theorem eventually_strict_of_eventually_flat {δ Δ : ℝ}
    (hδ : 0 < δ) (hΔ : 0 < Δ)
    (hflat : ∀ᶠ n : ℕ in atTop, ∃ p : Polynomial ℂ,
      IsLittlewood n p ∧ HasFlatBounds δ Δ n p) :
    ∀ᶠ n : ℕ in atTop, ∃ p : Polynomial ℂ,
      p.degree = n ∧
      (∀ i ≤ n, p.coeff i = 1 ∨ p.coeff i = -1) ∧
      HasStrictTargetBounds (2 / δ) (2 * Δ) n p := by
  filter_upwards [hflat, eventually_gt_atTop (0 : ℕ)] with n hnflat hn
  obtain ⟨p, hpLittlewood, hpFlat⟩ := hnflat
  exact ⟨p, hpLittlewood.1, hpLittlewood.2,
    hasStrictTargetBounds_of_hasFlatBounds hδ hΔ hn hpFlat⟩

end

section

open Filter

noncomputable section

def signPoly (n : ℕ) (eps : Fin (n + 1) → ℂ) : Polynomial ℂ :=
  ∑ j : Fin (n + 1), monomial j.1 (eps j)

@[simp]
theorem coeff_signPoly_of_le (n i : ℕ) (eps : Fin (n + 1) → ℂ)
    (hi : i ≤ n) :
    (signPoly n eps).coeff i = eps ⟨i, Nat.lt_succ_iff.2 hi⟩ := by
  classical
  change (lcoeff ℂ i)
      (∑ j : Fin (n + 1), monomial j.1 (eps j)) = _
  rw [map_sum]
  simp only [lcoeff_apply, coeff_monomial]
  rw [Fintype.sum_eq_single ⟨i, Nat.lt_succ_iff.2 hi⟩]
  · rw [if_pos rfl]
  · intro b hb
    simp only [ite_eq_right_iff]
    intro hbi
    exact (hb (Fin.ext hbi)).elim

@[simp]
theorem coeff_signPoly_of_lt (n i : ℕ) (eps : Fin (n + 1) → ℂ)
    (hi : n < i) :
    (signPoly n eps).coeff i = 0 := by
  classical
  change (lcoeff ℂ i)
      (∑ j : Fin (n + 1), monomial j.1 (eps j)) = _
  rw [map_sum]
  simp only [lcoeff_apply, coeff_monomial]
  apply sum_eq_zero
  intro j hj
  simp only [ite_eq_right_iff]
  intro hji
  omega

@[simp]
theorem eval_signPoly (n : ℕ) (eps : Fin (n + 1) → ℂ) (z : ℂ) :
    (signPoly n eps).eval z = ∑ j : Fin (n + 1), eps j * z ^ j.1 := by
  simp [signPoly, eval_finsetSum, eval_monomial]

end

end

section

open Filter
open scoped BigOperators

noncomputable section

def InFundamentalAngle (θ : ℝ) : Prop :=
  θ ∈ Set.Icc (-π / 2) (3 * π / 2)

def oneTail (base r : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range r, monomial (base + 1 + j) 1

theorem coeff_oneTail (base r i : ℕ) :
    (oneTail base r).coeff i =
      if base < i ∧ i ≤ base + r then 1 else 0 := by
  classical
  change lcoeff ℂ i
      (∑ j ∈ Finset.range r, monomial (base + 1 + j) 1) = _
  rw [map_sum]
  simp only [lcoeff_apply, coeff_monomial]
  by_cases hi : base < i ∧ i ≤ base + r
  · rw [if_pos hi]
    have hj : i - (base + 1) < r := by omega
    rw [sum_eq_single (i - (base + 1))]
    · have heq : base + 1 + (i - (base + 1)) = i := by omega
      simp [heq]
    · intro b hb hne
      rw [if_neg]
      intro heq
      apply hne
      omega
    · simp [hj]
  · rw [if_neg hi]
    apply sum_eq_zero
    intro j hj
    rw [if_neg]
    intro heq
    apply hi
    simp only [Finset.mem_range] at hj
    omega

def appendOnes (base r : ℕ) (p : Polynomial ℂ) : Polynomial ℂ :=
  p + oneTail base r

theorem coeff_appendOnes_of_le {base r i : ℕ} {p : Polynomial ℂ}
    (hi : i ≤ base) :
    (appendOnes base r p).coeff i = p.coeff i := by
  rw [appendOnes, coeff_add, coeff_oneTail]
  simp [show ¬base < i by omega]

theorem coeff_appendOnes_of_lt_le {base r i : ℕ} {p : Polynomial ℂ}
    (hp : p.degree = base) (hlo : base < i) (hhi : i ≤ base + r) :
    (appendOnes base r p).coeff i = 1 := by
  rw [appendOnes, coeff_add, coeff_oneTail, if_pos ⟨hlo, hhi⟩]
  have hpzero : p.coeff i = 0 := by
    apply coeff_eq_zero_of_degree_lt
    rw [hp]
    exact_mod_cast hlo
  rw [hpzero, zero_add]

theorem degree_appendOnes {base r : ℕ} {p : Polynomial ℂ}
    (hp : p.degree = base) :
    (appendOnes base r p).degree = base + r := by
  apply degree_eq_of_le_of_coeff_ne_zero (n := base + r)
  · rw [degree_le_iff_coeff_zero]
    intro i hi
    have hisum : base + r < i := by exact_mod_cast hi
    rw [appendOnes, coeff_add, coeff_oneTail]
    have hibase : base < i := by omega
    have htail : ¬(base < i ∧ i ≤ base + r) := by omega
    rw [if_neg htail]
    simp only [add_zero]
    apply coeff_eq_zero_of_degree_lt
    rw [hp]
    exact_mod_cast hibase
  · by_cases hr : r = 0
    · subst r
      simpa only [Nat.add_zero, appendOnes, oneTail, Finset.range_zero,
        Finset.sum_empty, add_zero] using
        (show p.coeff base ≠ 0 by
          apply Polynomial.coeff_ne_zero_of_eq_degree hp)
    · rw [coeff_appendOnes_of_lt_le hp (Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero hr)) le_rfl]
      norm_num

theorem isLittlewood_appendOnes {base r : ℕ} {p : Polynomial ℂ}
    (hp : IsLittlewood base p) :
    IsLittlewood (base + r) (appendOnes base r p) := by
  constructor
  · exact degree_appendOnes hp.1
  · intro i hi
    by_cases hibase : i ≤ base
    · rw [coeff_appendOnes_of_le hibase]
      exact hp.2 i hibase
    · rw [coeff_appendOnes_of_lt_le hp.1 (Nat.lt_of_not_ge hibase) hi]
      exact Or.inl rfl

theorem eval_oneTail (base r : ℕ) (z : ℂ) :
    (oneTail base r).eval z = ∑ j ∈ Finset.range r, z ^ (base + 1 + j) := by
  simp [oneTail, eval_finsetSum, eval_monomial]

theorem norm_eval_oneTail_le {base r : ℕ} {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(oneTail base r).eval z‖ ≤ r := by
  rw [eval_oneTail]
  calc
    ‖∑ j ∈ Finset.range r, z ^ (base + 1 + j)‖ ≤
        ∑ j ∈ Finset.range r, ‖z ^ (base + 1 + j)‖ := norm_sum_le _ _
    _ = ∑ _j ∈ Finset.range r, (1 : ℝ) := by
      apply sum_congr rfl
      intro j hj
      simp [norm_pow, hz]
    _ = r := by simp

theorem norm_eval_appendOnes_up {base r : ℕ} {p : Polynomial ℂ}
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(appendOnes base r p).eval z‖ ≤ ‖p.eval z‖ + r := by
  rw [appendOnes, eval_add]
  calc
    ‖p.eval z + (oneTail base r).eval z‖ ≤
        ‖p.eval z‖ + ‖(oneTail base r).eval z‖ := norm_add_le _ _
    _ ≤ ‖p.eval z‖ + r := by
      gcongr
      exact norm_eval_oneTail_le hz

theorem norm_eval_appendOnes_lo {base r : ℕ} {p : Polynomial ℂ}
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖p.eval z‖ - r ≤ ‖(appendOnes base r p).eval z‖ := by
  have htri : ‖p.eval z‖ ≤
      ‖(appendOnes base r p).eval z‖ + ‖(oneTail base r).eval z‖ := by
    calc
      ‖p.eval z‖ =
          ‖(appendOnes base r p).eval z - (oneTail base r).eval z‖ := by
            congr 1
            simp [appendOnes]
      _ ≤ _ := norm_sub_le _ _
  linarith [norm_eval_oneTail_le (base := base) (r := r) hz]

structure CtrPairInput (n : ℕ) where
  coeff : Fin (4 * n + 1) → ℂ
  coeff_isSign : ∀ j, IsSign (coeff j)
  cosine : ℝ → ℝ
  evenSine : ℝ → ℝ
  oddSine : ℝ → ℝ
  dangerous : ℝ → Prop
  eval_eq : ∀ θ,
    (ofCoeffs (4 * n) coeff).eval (unitPt θ) =
      unitPt θ ^ (2 * n) *
        asmValue (cosine θ) (evenSine θ) (oddSine θ)
  cosine_upper : ∀ θ, |cosine θ| ≤ sqrt n
  evenSine_upper : ∀ θ, |evenSine θ| ≤ 6 * sqrt n
  oddSine_upper : ∀ θ, |oddSine θ| ≤ 2 ^ 10 * sqrt n
  cosine_lower_off_dangerous : ∀ θ, InFundamentalAngle θ →
    ¬ dangerous θ →
    (1 / 2 ^ 160 : ℝ) * sqrt n + 1 ≤ 2 * |cosine θ|
  oddSine_lower_on_dangerous : ∀ θ, InFundamentalAngle θ →
    dangerous θ →
    10 * sqrt n ≤ |oddSine θ|

def CtrPairInput.poly {n : ℕ} (A : CtrPairInput n) :
    Polynomial ℂ :=
  ofCoeffs (4 * n) A.coeff

theorem CtrPairInput.isLittlewood {n : ℕ}
    (A : CtrPairInput n) : IsLittlewood (4 * n) A.poly :=
  isLittlewood_ofCoeffs (4 * n) A.coeff A.coeff_isSign

theorem CtrPairInput.norm_eval_eq {n : ℕ}
    (A : CtrPairInput n) (θ : ℝ) :
    ‖A.poly.eval (unitPt θ)‖ =
      ‖asmValue (A.cosine θ) (A.evenSine θ) (A.oddSine θ)‖ := by
  rw [CtrPairInput.poly, A.eval_eq, norm_mul, norm_pow,
    norm_unitPt, one_pow, one_mul]

theorem CtrPairInput.flat_on_parametrized_circ {n : ℕ}
    (hn : 1 ≤ n) (A : CtrPairInput n) (θ : ℝ)
    (hθ : InFundamentalAngle θ) :
    (1 / 2 ^ 160 : ℝ) * sqrt n ≤
        ‖A.poly.eval (unitPt θ)‖ ∧
      ‖A.poly.eval (unitPt θ)‖ ≤
        2 ^ 12 * sqrt n := by
  rw [A.norm_eval_eq]
  constructor
  · by_cases hdanger : A.dangerous θ
    · have hbig := eight_sqrt_le_norm_asmValue_of_odd_sin
          (c := A.cosine θ)
          (A.evenSine_upper θ)
          (A.oddSine_lower_on_dangerous θ hθ hdanger)
      have hsqrt : 0 ≤ sqrt n := sqrt_nonneg _
      norm_num at hbig ⊢
      nlinarith
    · have hcos := two_mul_abs_sub_one_le_norm_asmValue
          (A.cosine θ) (A.evenSine θ) (A.oddSine θ)
      have hlower := A.cosine_lower_off_dangerous θ hθ hdanger
      norm_num at hlower ⊢
      linarith
  · exact norm_asmValue_le_two_pow_twelve_sqrt hn
      (A.cosine_upper θ) (A.evenSine_upper θ) (A.oddSine_upper θ)

@[simp] theorem unitPt_add_two_pi (θ : ℝ) :
    unitPt (θ + 2 * π) = unitPt θ := by
  unfold unitPt
  rw [show (((θ + 2 * π : ℝ) : ℂ) * Complex.I) =
      (θ : ℂ) * Complex.I + 2 * (π : ℂ) * Complex.I by
        push_cast
        ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem exists_fundamental_unitPt_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    ∃ θ : ℝ, InFundamentalAngle θ ∧ unitPt θ = z := by
  let a := z.arg
  have haLower : -π < a := Complex.neg_pi_lt_arg z
  have haUpper : a ≤ π := Complex.arg_le_pi z
  have haPoint : unitPt a = z := by
    calc
      unitPt a = Complex.exp ((a : ℂ) * Complex.I) := rfl
      _ = ‖z‖ * Complex.exp ((a : ℂ) * Complex.I) := by rw [hz]; simp
      _ = z := Complex.norm_mul_exp_arg_mul_I z
  by_cases ha : -π / 2 ≤ a
  · refine ⟨a, ⟨ha, ?_⟩, haPoint⟩
    nlinarith [pi_pos]
  · refine ⟨a + 2 * π, ⟨?_, ?_⟩, ?_⟩
    · nlinarith [pi_pos]
    · nlinarith [lt_of_not_ge ha]
    · rw [unitPt_add_two_pi]
      exact haPoint

theorem CtrPairInput.flat_on_circ {n : ℕ}
    (hn : 1 ≤ n) (A : CtrPairInput n) :
    ∀ z : ℂ, ‖z‖ = 1 →
      (1 / 2 ^ 160 : ℝ) * sqrt n ≤ ‖A.poly.eval z‖ ∧
      ‖A.poly.eval z‖ ≤ 2 ^ 12 * sqrt n := by
  intro z hz
  obtain ⟨θ, hθ, rfl⟩ :=
    exists_fundamental_unitPt_of_norm_eq_one hz
  exact A.flat_on_parametrized_circ hn θ hθ

private theorem sqrt_sixteen_mul (n : ℕ) :
    sqrt (16 * (n : ℝ)) = 4 * sqrt n := by
  rw [sqrt_mul (by positivity : (0 : ℝ) ≤ 16)]
  norm_num

private theorem sqrt_mono_nat {a b : ℕ} (h : a ≤ b) :
    sqrt a ≤ sqrt b :=
  sqrt_le_sqrt (by exact_mod_cast h)

theorem extend_ctr_to_degree (d : ℕ)
    (hn : 1 ≤ d / 4) (A : CtrPairInput (d / 4))
    (habsorb : 3 ≤ (1 / 2 ^ 163 : ℝ) * sqrt d) :
    ∃ p : Polynomial ℂ, IsLittlewood d p ∧
      HasFlatBounds (1 / 2 ^ 163) (2 ^ 13) d p := by
  let n := d / 4
  let r := d % 4
  let q := A.poly
  let p := appendOnes (4 * n) r q
  have hr : r ≤ 3 := by
    dsimp [r]
    omega
  have hdecomp : 4 * n + r = d := by
    dsimp [n, r]
    omega
  have hqLittlewood : IsLittlewood (4 * n) q := by
    exact A.isLittlewood
  have hpLittlewood : IsLittlewood d p := by
    rw [← hdecomp]
    exact isLittlewood_appendOnes hqLittlewood
  refine ⟨p, hpLittlewood, ?_⟩
  intro z hz
  have hqflat := A.flat_on_circ hn z hz
  have hnle : n ≤ d := by
    dsimp [n]
    omega
  have hdle : d ≤ 16 * n := by
    rw [← hdecomp]
    omega
  have hsqrt_nd : sqrt n ≤ sqrt d := sqrt_mono_nat hnle
  have hsqrt_dn : sqrt d ≤ 4 * sqrt n := by
    calc
      sqrt d ≤ sqrt (16 * (n : ℝ)) := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using sqrt_mono_nat hdle
      _ = 4 * sqrt n := sqrt_sixteen_mul n
  have hsqrt_nonneg : 0 ≤ sqrt d := sqrt_nonneg _
  have hsqrt_three : 3 ≤ sqrt d := by
    have hfactor : (1 / 2 ^ 163 : ℝ) ≤ 1 := by norm_num
    nlinarith [mul_le_mul_of_nonneg_right hfactor hsqrt_nonneg]
  constructor
  · have htail := norm_eval_appendOnes_lo
        (base := 4 * n) (r := r) (p := q) hz
    change ‖q.eval z‖ - (r : ℝ) ≤ ‖p.eval z‖ at htail
    have hrR : (r : ℝ) ≤ 3 := by exact_mod_cast hr
    have hscale : (1 / 2 ^ 162 : ℝ) * sqrt d ≤
        (1 / 2 ^ 160 : ℝ) * sqrt n := by
      norm_num at ⊢
      nlinarith
    norm_num at hqflat habsorb ⊢
    nlinarith
  · have htail := norm_eval_appendOnes_up
        (base := 4 * n) (r := r) (p := q) hz
    change ‖p.eval z‖ ≤ ‖q.eval z‖ + (r : ℝ) at htail
    have hrR : (r : ℝ) ≤ 3 := by exact_mod_cast hr
    norm_num at hqflat ⊢
    nlinarith

def EventuallyCtrPair : Prop :=
  ∀ᶠ n : ℕ in atTop, Nonempty (CtrPairInput n)

private theorem eventually_absorb_three :
    ∀ᶠ d : ℕ in atTop,
      3 ≤ (1 / 2 ^ 163 : ℝ) * sqrt d := by
  have hsqrt : Filter.Tendsto (fun d : ℕ ↦ sqrt (d : ℝ))
      atTop atTop :=
    tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hscaled : Filter.Tendsto
      (fun d : ℕ ↦ (1 / 2 ^ 163 : ℝ) * sqrt d)
      atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) hsqrt
  exact hscaled (eventually_ge_atTop 3)

theorem eventually_flat_of_eventually_ctr
    (hcentered : EventuallyCtrPair) :
    ∀ᶠ d : ℕ in atTop, ∃ p : Polynomial ℂ,
      IsLittlewood d p ∧
      HasFlatBounds (1 / 2 ^ 163) (2 ^ 13) d p := by
  rw [EventuallyCtrPair, eventually_atTop] at hcentered
  obtain ⟨N, hN⟩ := hcentered
  filter_upwards [eventually_ge_atTop (4 * max N 1), eventually_absorb_three]
    with d hd habsorb
  have hnN : N ≤ d / 4 := by omega
  have hn1 : 1 ≤ d / 4 := by omega
  obtain ⟨A⟩ := hN (d / 4) hnN
  exact extend_ctr_to_degree d hn1 A habsorb

theorem target_of_eventually_ctr (hcentered : EventuallyCtrPair) :
    ∃ (c₁ : ℝ) (c₂ : ℝ), ∀ᶠ n : ℕ in atTop,
    ∃ p : Polynomial ℂ, p.degree = n ∧
    (∀ i ≤ n, p.coeff i = 1 ∨ p.coeff i = -1) ∧
    ∀ z : ℂ, ‖z‖ = 1 →
    (sqrt n < c₁ * ‖p.eval z‖ ∧
      ‖p.eval z‖ < c₂ * sqrt n) := by
  refine Iff.mp ?_ trivial
  constructor
  · intro _
    have hflat := eventually_flat_of_eventually_ctr hcentered
    have hstrict := eventually_strict_of_eventually_flat
      (δ := (1 / 2 ^ 163 : ℝ)) (Δ := (2 ^ 13 : ℝ))
      (by positivity) (by positivity) hflat
    exact ⟨2 / (1 / 2 ^ 163 : ℝ), 2 * (2 ^ 13 : ℝ), hstrict⟩
  · intro _
    trivial

end

end

section

namespace CosConstr

open Filter Set

noncomputable section

structure CosPackage (n : ℕ) where
  t : ℕ
  γ : ℝ
  parameters : Params n t γ
  family : IvlFam n
  base_card : (family.base.card : ℝ) ≤ γ * n
  upper : ∀ θ, |evenCos t θ| ≤ sqrt n
  lower : ∀ θ, InFundamentalAngle θ →
    ¬IsDangerous family θ →
      cosDelta γ * sqrt n ≤ |evenCos t θ|

theorem sevenCellProperty_of_params
    {n t : ℕ} {γ : ℝ} (hparam : Params n t γ) :
    SevenCellProperty n t γ := by
  apply sevenCellProperty_of_norm_good hparam
  exact normH_re_hasGoodCellInEverySeven t hparam.eta_pos hparam.eta_lt

theorem endpt_thr_bounds
    {n t : ℕ} {γ : ℝ} (hparam : Params n t γ) :
    thr n γ ≤ |evenCos t 0| ∧
      thr n γ ≤ |evenCos t (π / 2)| := by
  have hthreshold := thr_lt_half_normalization hparam
  have hscale : 0 < sqrt (2 ^ (t + 1) : ℝ) := by positivity
  constructor
  · rw [evenCos_eq_normH]
    simp only [mul_zero]
    rw [normH_re_zero_of_odd hparam.t_odd]
    simp only [abs_mul, abs_one, mul_one, abs_of_pos hscale]
    linarith
  · rw [evenCos_eq_normH]
    have harg : 2 * (evenT t : ℝ) * (π / 2) =
        (evenT t : ℝ) * π := by ring
    rw [harg, normH_re_evenT_mul_pi_of_odd hparam.t_odd]
    simp only [abs_mul, abs_one, mul_one, abs_of_pos hscale]
    linarith

theorem suitFam_base_card_le
    {n t : ℕ} {γ : ℝ} (hparam : Params n t γ)
    (hseven : SevenCellProperty n t γ)
    (hgeom : GeometricCert n t γ) :
    ((suitIvlFamOfDangerousRuns hparam.n_pos hseven hgeom).base.card : ℝ) ≤
      γ * n := by
  have hend := endpt_thr_bounds hparam
  have hcard := card_firstQuadRuns_le_paramNum hparam.n_pos
    (thr_pos hparam.n_pos hparam.gamma_pos).le hend.1 hend.2
  rw [suitFam_base_card hparam.n_pos hseven hgeom]
  have hcardR : ((firstQuadRuns n t γ).card : ℝ) ≤
      paramNum t := by exact_mod_cast hcard
  rwa [hparam.equation]

def cosPackageOfParams
    {n t : ℕ} {γ : ℝ} (hparam : Params n t γ) :
    CosPackage n := by
  let hseven : SevenCellProperty n t γ :=
    sevenCellProperty_of_params hparam
  let hgeom : GeometricCert n t γ :=
    geometricCert_of_params hparam
  let F : IvlFam n :=
    suitIvlFamOfDangerousRuns hparam.n_pos hseven hgeom
  refine
    { t := t
      γ := γ
      parameters := hparam
      family := F
      base_card := ?_
      upper := ?_
      lower := ?_ }
  · simpa only [F] using suitFam_base_card_le hparam hseven hgeom
  · intro θ
    exact abs_evenCos_le_sqrt_of_params hparam.toEvenParams θ
  · intro θ hθ hout
    have hfirst : ∀ x ∈ Icc 0 (π / 2),
        ¬InBaseFam F x → thr n γ ≤ |evenCos t x| := by
      intro x hx hbase
      apply le_of_not_gt
      intro hsmall
      apply hbase
      obtain ⟨I, hI, hxI⟩ :=
        low_pt_covered_by_firstQuadIvls hparam hx hsmall
      refine ⟨I, ?_, hxI⟩
      change I ∈ firstQuadIvls n t γ
      exact hI
    have hlower := lo_on_fundamental_of_lo_off_base F hfirst θ
      (by simpa only [InFundamentalAngle] using hθ) hout
    simpa only [thr] using hlower

theorem eventually_exists_cosPackage :
    ∀ᶠ n : ℕ in atTop, Nonempty (CosPackage n) := by
  filter_upwards [eventually_exists_params] with n hparam
  obtain ⟨t, γ, hparam⟩ := hparam
  exact ⟨cosPackageOfParams hparam⟩

end

end CosConstr

end

section

namespace OddSine

open scoped BigOperators

noncomputable section

def firstParam (n N : ℕ) : ℝ :=
  14 * sqrt (log ((16 * n : ℕ) / (N : ℝ)))

private lemma firstColoring_ratio_ge
    {n N : ℕ} {γ : ℝ} (hn : 0 < n) (hN : 0 < N)
    (hγ : γ ≤ 1 / (2 : ℝ) ^ 40)
    (hcard : (N : ℝ) ≤ γ * n) :
    (2 : ℝ) ^ 44 ≤ (16 * n : ℕ) / (N : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsmall : (N : ℝ) ≤ (n : ℝ) / 2 ^ 40 := by
    calc
      (N : ℝ) ≤ γ * n := hcard
      _ ≤ (1 / (2 : ℝ) ^ 40) * n :=
        mul_le_mul_of_nonneg_right hγ hnR.le
      _ = (n : ℝ) / 2 ^ 40 := by ring
  apply (le_div_iff₀ hNR).2
  push_cast
  norm_num at hsmall ⊢
  nlinarith

private lemma firstColoring_log_ratio_nonneg
    {n N : ℕ} {γ : ℝ} (hn : 0 < n) (hN : 0 < N)
    (hγ : γ ≤ 1 / (2 : ℝ) ^ 40)
    (hcard : (N : ℝ) ≤ γ * n) :
    0 ≤ log ((16 * n : ℕ) / (N : ℝ)) := by
  apply log_nonneg
  exact (by norm_num : (1 : ℝ) ≤ 2 ^ 44).trans
    (firstColoring_ratio_ge hn hN hγ hcard)

private lemma log_ratio_div_ratio_le
    {n N : ℕ} {γ : ℝ} (hn : 0 < n) (hN : 0 < N)
    (hγ : γ ≤ 1 / (2 : ℝ) ^ 40)
    (hcard : (N : ℝ) ≤ γ * n) :
    log ((16 * n : ℕ) / (N : ℝ)) /
        ((16 * n : ℕ) / (N : ℝ)) ≤
      (28 / 5 : ℝ) ^ 2 / 2 ^ 44 := by
  let q : ℝ := (16 * n : ℕ) / (N : ℝ)
  have hq : (2 : ℝ) ^ 44 ≤ q := firstColoring_ratio_ge hn hN hγ hcard
  have hexp : Real.exp 1 ≤ (2 : ℝ) ^ 44 := by
    exact Real.exp_one_lt_d9.le.trans (by norm_num)
  have hmono : log q / q ≤ log ((2 : ℝ) ^ 44) / (2 : ℝ) ^ 44 :=
    Real.log_div_self_antitoneOn hexp (hexp.trans hq) hq
  have hlog2 : log 2 ≤ (7 / 10 : ℝ) :=
    log_two_lt_d9.le.trans (by norm_num)
  have hlogpow : log ((2 : ℝ) ^ 44) ≤ 44 * (7 / 10 : ℝ) := by
    rw [Real.log_pow]
    nlinarith
  dsimp only [q] at hmono
  calc
    log ((16 * n : ℕ) / (N : ℝ)) /
          ((16 * n : ℕ) / (N : ℝ)) ≤
        log ((2 : ℝ) ^ 44) / (2 : ℝ) ^ 44 := hmono
    _ ≤ (28 / 5 : ℝ) ^ 2 / 2 ^ 44 := by
      apply div_le_div_of_nonneg_right (hlogpow.trans (by norm_num)) (by positivity)

private lemma sqrt_card_scale_le
    {n N : ℕ} {γ : ℝ} (hn : 0 < n) (hN : 0 < N)
    (hγ : γ ≤ 1 / (2 : ℝ) ^ 40)
    (hcard : (N : ℝ) ≤ γ * n) :
    sqrt N * sqrt n / n ≤ (1 : ℝ) / 2 ^ 20 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNR : (0 : ℝ) ≤ N := by positivity
  have hsmall : (N : ℝ) ≤ (n : ℝ) / 2 ^ 40 := by
    calc
      (N : ℝ) ≤ γ * n := hcard
      _ ≤ (1 / (2 : ℝ) ^ 40) * n :=
        mul_le_mul_of_nonneg_right hγ hnR.le
      _ = (n : ℝ) / 2 ^ 40 := by ring
  have hsqrtn_sq : (sqrt n) ^ 2 = (n : ℝ) := sq_sqrt hnR.le
  have hsqrtN_sq : (sqrt N) ^ 2 = (N : ℝ) := sq_sqrt hNR
  have hscale_nonneg : 0 ≤ sqrt N * sqrt n / (n : ℝ) := by positivity
  have hsquare :
      (sqrt N * sqrt n / (n : ℝ)) ^ 2 = (N : ℝ) / n := by
    rw [div_pow, mul_pow, hsqrtN_sq, hsqrtn_sq]
    field_simp
  have htarget_nonneg : (0 : ℝ) ≤ 1 / 2 ^ 20 := by positivity
  have hratio : (N : ℝ) / n ≤ (1 : ℝ) / 2 ^ 40 := by
    apply (div_le_iff₀ hnR).2
    calc
      (N : ℝ) ≤ (n : ℝ) / 2 ^ 40 := hsmall
      _ = ((1 : ℝ) / 2 ^ 40) * n := by ring
  nlinarith [sq_nonneg
    (sqrt N * sqrt n / (n : ℝ) + (1 : ℝ) / 2 ^ 20)]

private lemma sqrt_log_mul_sqrt_card_scale_le
    {n N : ℕ} {γ : ℝ} (hn : 0 < n) (hN : 0 < N)
    (hγ : γ ≤ 1 / (2 : ℝ) ^ 40)
    (hcard : (N : ℝ) ≤ γ * n) :
    sqrt (log ((16 * n : ℕ) / (N : ℝ))) *
        (sqrt N * sqrt n / n) ≤
      (28 / 5 : ℝ) / 2 ^ 20 := by
  let q : ℝ := (16 * n : ℕ) / (N : ℝ)
  let a : ℝ := sqrt N * sqrt n / n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hqpos : 0 < q := by
    dsimp [q]
    positivity
  have hlog : 0 ≤ log q := by
    dsimp only [q]
    exact firstColoring_log_ratio_nonneg hn hN hγ hcard
  have ha_nonneg : 0 ≤ a := by dsimp [a]; positivity
  have hsqrta : a ^ 2 = 16 / q := by
    have hsqrtn_sq : (sqrt n) ^ 2 = (n : ℝ) := sq_sqrt hnR.le
    have hsqrtN_sq : (sqrt N) ^ 2 = (N : ℝ) := sq_sqrt hNR.le
    dsimp [a, q]
    rw [div_pow, mul_pow, hsqrtN_sq, hsqrtn_sq]
    push_cast
    field_simp
  have hquot := log_ratio_div_ratio_le hn hN hγ hcard
  change log q / q ≤ (28 / 5 : ℝ) ^ 2 / 2 ^ 44 at hquot
  have hsqrtlog_sq : (sqrt (log q)) ^ 2 = log q :=
    sq_sqrt hlog
  have hleft_nonneg : 0 ≤ sqrt (log q) * a := by positivity
  have hright_nonneg : (0 : ℝ) ≤ (28 / 5 : ℝ) / 2 ^ 20 := by positivity
  have hsquare :
      (sqrt (log q) * a) ^ 2 = 16 * (log q / q) := by
    rw [mul_pow, hsqrtlog_sq, hsqrta]
    field_simp
  nlinarith

theorem exp_neg_firstParam_sq
    {n N : ℕ} {γ : ℝ} (hn : 0 < n) (hN : 0 < N)
    (hγ : γ ≤ 1 / (2 : ℝ) ^ 40)
    (hcard : (N : ℝ) ≤ γ * n) :
    Real.exp (-(firstParam n N) ^ 2 / 196) =
      (N : ℝ) / (16 * n) := by
  have hlog := firstColoring_log_ratio_nonneg hn hN hγ hcard
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [firstParam, mul_pow, sq_sqrt hlog]
  have hqpos : (0 : ℝ) < (16 * n : ℕ) / (N : ℝ) := by positivity
  rw [show -((14 : ℝ) ^ 2 * log ((16 * n : ℕ) / (N : ℝ))) / 196 =
      -log ((16 * n : ℕ) / (N : ℝ)) by ring]
  rw [Real.exp_neg, exp_log hqpos]
  push_cast
  field_simp

theorem firstColoringAdm_of_card_le
    {n : ℕ} (hn : 0 < n) (F : IvlFam n) {γ : ℝ}
    (hγ : γ ≤ 1 / (2 : ℝ) ^ 40)
    (hbase : 0 < F.base.card)
    (hcard : (F.base.card : ℝ) ≤ γ * n) :
    FirstColoringAdm F
      (fun _ ↦ firstParam n F.base.card) := by
  classical
  apply firstColoringAdm_of_numeric hn
  · intro j
    exact mul_nonneg (by norm_num) (sqrt_nonneg _)
  · simp_rw [exp_neg_firstParam_sq hn hbase hγ hcard]
    simp
    field_simp
    norm_num
  · intro j
    have hscale := sqrt_card_scale_le hn hbase hγ hcard
    have hlogscale :=
      sqrt_log_mul_sqrt_card_scale_le hn hbase hγ hcard
    have hpi : π ≤ (22 / 7 : ℝ) :=
      Real.pi_lt_d4.le.trans (by norm_num)
    rw [firstParam]
    simp only [K_eq]
    have hnonneg :
        0 ≤ (14 * sqrt (log ((16 * n : ℕ) / (F.base.card : ℝ))) + 30) *
          (sqrt F.base.card * sqrt n / n) := by
      have hlog := firstColoring_log_ratio_nonneg hn hbase hγ hcard
      positivity
    calc
      (14 * sqrt (log ((16 * n : ℕ) / (F.base.card : ℝ))) + 30) *
          sqrt (Fintype.card ↥F.base) *
          (24 * 128 * π * sqrt n / n) =
        (24 * 128 * π) *
          ((14 * sqrt (log ((16 * n : ℕ) / (F.base.card : ℝ))) + 30) *
            (sqrt F.base.card * sqrt n / n)) := by
          simp only [card_coe]
          ring
      _ ≤ (24 * 128 * (22 / 7 : ℝ)) *
          ((14 * sqrt (log ((16 * n : ℕ) / (F.base.card : ℝ))) + 30) *
            (sqrt F.base.card * sqrt n / n)) := by
          gcongr
      _ ≤ (24 * 128 * (22 / 7 : ℝ)) *
          (14 * ((28 / 5 : ℝ) / 2 ^ 20) + 30 * ((1 : ℝ) / 2 ^ 20)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc
            (14 * sqrt (log ((16 * n : ℕ) / (F.base.card : ℝ))) + 30) *
                (sqrt F.base.card * sqrt n / n) =
              14 * (sqrt (log ((16 * n : ℕ) / (F.base.card : ℝ))) *
                (sqrt F.base.card * sqrt n / n)) +
              30 * (sqrt F.base.card * sqrt n / n) := by ring
            _ ≤ 14 * ((28 / 5 : ℝ) / 2 ^ 20) +
                30 * ((1 : ℝ) / 2 ^ 20) := by gcongr
      _ ≤ 1 := by norm_num

theorem exists_ivlColoring_of_base_card_eq_zero
    {n : ℕ} (F : IvlFam n) (hbase : F.base.card = 0) :
    ∃ α : ↥F.base → ℝ,
      Disc.IsSign α ∧
        ∀ j < n, |fourierTarget F α j| ≤ 1 := by
  classical
  have hempty : F.base = ∅ := Finset.card_eq_zero.mp hbase
  have hisEmpty : IsEmpty ↥F.base := Finset.isEmpty_coe_sort.mpr hempty
  let α : ↥F.base → ℝ := fun _ ↦ 1
  refine ⟨α, fun I ↦ Or.inl rfl, ?_⟩
  intro j hj
  simp [fourierTarget, hj]

end

end OddSine

end

section

namespace Kernel

open scoped BigOperators Interval
open Real Set MeasureTheory intervalIntegral

lemma two_mul_sin_mul_oddCosSum (n : ℕ) (t : ℝ) :
    2 * sin t * (∑ j ∈ Finset.range n,
      cos (((2 * j + 1 : ℕ) : ℝ) * t)) =
      sin ((2 * n : ℕ) * t) := by
  have hterm (j : ℕ) :
      2 * sin t * cos (((2 * j + 1 : ℕ) : ℝ) * t) =
        sin (((2 * (j + 1) : ℕ) : ℝ) * t) -
          sin (((2 * j : ℕ) : ℝ) * t) := by
    rw [Real.two_mul_sin_mul_cos]
    have hsub : t - ((2 * j + 1 : ℕ) : ℝ) * t =
        -(((2 * j : ℕ) : ℝ) * t) := by
      push_cast
      ring
    have hadd : t + ((2 * j + 1 : ℕ) : ℝ) * t =
        ((2 * (j + 1) : ℕ) : ℝ) * t := by
      push_cast
      ring
    rw [hsub, hadd, sin_neg]
    ring
  calc
    2 * sin t * (∑ j ∈ Finset.range n,
        cos (((2 * j + 1 : ℕ) : ℝ) * t)) =
        ∑ j ∈ Finset.range n,
          (2 * sin t * cos (((2 * j + 1 : ℕ) : ℝ) * t)) := by
            rw [Finset.mul_sum]
    _ = ∑ j ∈ Finset.range n,
        (sin (((2 * (j + 1) : ℕ) : ℝ) * t) -
          sin (((2 * j : ℕ) : ℝ) * t)) := by
            apply sum_congr rfl
            intro j hj
            exact hterm j
    _ = sin (((2 * n : ℕ) : ℝ) * t) - sin 0 := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero, mul_zero, zero_mul,
        sin_zero] using
        (sum_range_sub
          (fun j : ℕ => sin (((2 * j : ℕ) : ℝ) * t)) n)
    _ = sin ((2 * n : ℕ) * t) := by simp

lemma two_mul_oddCosSum_eq (n : ℕ) {t : ℝ} (ht : sin t ≠ 0) :
    2 * (∑ j ∈ Finset.range n,
      cos (((2 * j + 1 : ℕ) : ℝ) * t)) =
      sin ((2 * n : ℕ) * t) / sin t := by
  have h := two_mul_sin_mul_oddCosSum n t
  apply (eq_div_iff ht).2
  rw [← h]
  ring

lemma two_mul_sin_mul_sin (u v : ℝ) :
    2 * sin u * sin v = cos (u - v) - cos (u + v) := by
  rw [Real.cos_sub, Real.cos_add]
  ring

theorem odd_dirichlet_kernel (n : ℕ) {θ θ₀ : ℝ}
    (hsub : sin (θ - θ₀) ≠ 0) (hadd : sin (θ + θ₀) ≠ 0) :
    4 * (∑ j ∈ Finset.range n,
      sin (((2 * j + 1 : ℕ) : ℝ) * θ₀) *
        sin (((2 * j + 1 : ℕ) : ℝ) * θ)) =
      sin ((2 * n : ℕ) * (θ - θ₀)) / sin (θ - θ₀) -
        sin ((2 * n : ℕ) * (θ + θ₀)) / sin (θ + θ₀) := by
  rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_assoc, Finset.mul_sum]
  have hprod (j : ℕ) :
      2 * (sin (((2 * j + 1 : ℕ) : ℝ) * θ₀) *
        sin (((2 * j + 1 : ℕ) : ℝ) * θ)) =
        cos (((2 * j + 1 : ℕ) : ℝ) * (θ - θ₀)) -
          cos (((2 * j + 1 : ℕ) : ℝ) * (θ + θ₀)) := by
    calc
      2 * (sin (((2 * j + 1 : ℕ) : ℝ) * θ₀) *
          sin (((2 * j + 1 : ℕ) : ℝ) * θ)) =
          2 * sin (((2 * j + 1 : ℕ) : ℝ) * θ₀) *
            sin (((2 * j + 1 : ℕ) : ℝ) * θ) := by ring
      _ = cos ((((2 * j + 1 : ℕ) : ℝ) * θ₀) -
            (((2 * j + 1 : ℕ) : ℝ) * θ)) -
          cos ((((2 * j + 1 : ℕ) : ℝ) * θ₀) +
            (((2 * j + 1 : ℕ) : ℝ) * θ)) :=
        two_mul_sin_mul_sin _ _
      _ = cos (((2 * j + 1 : ℕ) : ℝ) * (θ - θ₀)) -
          cos (((2 * j + 1 : ℕ) : ℝ) * (θ + θ₀)) := by
            have hneg : (((2 * j + 1 : ℕ) : ℝ) * θ₀) -
                (((2 * j + 1 : ℕ) : ℝ) * θ) =
                -(((2 * j + 1 : ℕ) : ℝ) * (θ - θ₀)) := by ring
            have hplus : (((2 * j + 1 : ℕ) : ℝ) * θ₀) +
                (((2 * j + 1 : ℕ) : ℝ) * θ) =
                ((2 * j + 1 : ℕ) : ℝ) * (θ + θ₀) := by ring
            rw [hneg, cos_neg, hplus]
  rw [sum_congr rfl (fun j _ => hprod j), sum_sub_distrib,
    mul_sub, two_mul_oddCosSum_eq n hsub, two_mul_oddCosSum_eq n hadd]

lemma cos_le_taylor_four {x : ℝ} (hx : 0 ≤ x) :
    cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  let f (t : ℝ) := 1 - t ^ 2 / 2 + t ^ 4 / 24 - cos t
  have hderiv (t : ℝ) :
      deriv f t = -t + t ^ 3 / 6 + sin t := by
    simp (disch := fun_prop) [f]
    ring
  have hmono : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [hderiv]
    have ht0 : 0 ≤ t := by
      rw [interior_Ici, mem_Ioi] at ht
      exact ht.le
    linarith [sin_ge_sub_cube ht0]
  have h := hmono (show (0 : ℝ) ∈ Ici 0 by simp) (show x ∈ Ici 0 by exact hx) hx
  dsimp [f] at h
  norm_num at h
  exact h

lemma sin_le_taylor_five {x : ℝ} (hx : 0 ≤ x) :
    sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  let f (t : ℝ) := t - t ^ 3 / 6 + t ^ 5 / 120 - sin t
  have hderiv (t : ℝ) :
      deriv f t = 1 - t ^ 2 / 2 + t ^ 4 / 24 - cos t := by
    simp (disch := fun_prop) [f]
    ring
  have hmono : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [hderiv]
    have ht0 : 0 ≤ t := by
      rw [interior_Ici, mem_Ioi] at ht
      exact ht.le
    linarith [cos_le_taylor_four ht0]
  have h := hmono (show (0 : ℝ) ∈ Ici 0 by simp) (show x ∈ Ici 0 by exact hx) hx
  dsimp [f] at h
  norm_num at h
  exact h

lemma sinc_le_taylor_four {x : ℝ} (hx : 0 ≤ x) :
    sinc x ≤ 1 - x ^ 2 / 6 + x ^ 4 / 120 := by
  obtain rfl | hxpos := hx.eq_or_lt
  · norm_num
  rw [sinc_of_ne_zero hxpos.ne']
  apply (div_le_iff₀ hxpos).2
  nlinarith [sin_le_taylor_five hxpos.le]

noncomputable def sinIntg (b : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..b, sinc x

lemma sinIntg_up {b : ℝ} (hb : 0 ≤ b) :
    sinIntg b ≤ b - b ^ 3 / 18 + b ^ 5 / 600 := by
  have hs : IntervalIntegrable sinc volume 0 b :=
    continuous_sinc.intervalIntegrable 0 b
  have hp1 : IntervalIntegrable (fun x : ℝ => 1 - x ^ 2 / 6) volume 0 b :=
    (by fun_prop : Continuous (fun x : ℝ => 1 - x ^ 2 / 6)).intervalIntegrable 0 b
  have hp2 : IntervalIntegrable (fun x : ℝ => x ^ 4 / 120) volume 0 b :=
    (by fun_prop : Continuous (fun x : ℝ => x ^ 4 / 120)).intervalIntegrable 0 b
  have hp : IntervalIntegrable
      (fun x : ℝ => 1 - x ^ 2 / 6 + x ^ 4 / 120) volume 0 b := hp1.add hp2
  have hmono := integral_mono_on hb hs hp
    (fun x hx => sinc_le_taylor_four hx.1)
  calc
    sinIntg b = ∫ x in (0 : ℝ)..b, sinc x := rfl
    _ ≤ ∫ x in (0 : ℝ)..b, (1 - x ^ 2 / 6 + x ^ 4 / 120) := hmono
    _ = b - b ^ 3 / 18 + b ^ 5 / 600 := by
      rw [intervalIntegral.integral_add hp1 hp2]
      simp [intervalIntegral.integral_sub, intervalIntegral.integral_div, integral_pow]
      ring

theorem sinIntg_pi_lt_two : sinIntg π < 2 := by
  have hSi := sinIntg_up pi_pos.le
  have hpi : π < (3.15 : ℝ) := pi_lt_d2
  have hcube : (3.14 : ℝ) ^ 3 < π ^ 3 :=
    pow_lt_pow_left₀ pi_gt_d2 (by norm_num) (by norm_num)
  have hfifth : π ^ 5 < (3.15 : ℝ) ^ 5 :=
    pow_lt_pow_left₀ pi_lt_d2 pi_pos.le (by norm_num)
  norm_num at hpi hcube hfifth ⊢
  nlinarith

end Kernel

end

open Kernel


section

namespace OddKernelId

open scoped BigOperators Interval
open Set MeasureTheory

noncomputable section

def oddKernel (n : ℕ) (x θ : ℝ) : ℝ :=
  4 * ∑ j ∈ Finset.range n,
    sin ((oddFreq j : ℝ) * x) *
      sin ((oddFreq j : ℝ) * θ)

def integratedOddKernel (n : ℕ) (I : RealIvl)
    (θ : ℝ) : ℝ :=
  ∫ x in I.1..I.2, oddKernel n x θ

theorem integratedOddKernel_eq_sum (n : ℕ)
    (I : RealIvl) (θ : ℝ) :
    integratedOddKernel n I θ =
      4 * ∑ j ∈ Finset.range n,
        (∫ x in I.1..I.2,
          sin ((oddFreq j : ℝ) * x)) *
            sin ((oddFreq j : ℝ) * θ) := by
  classical
  simp only [integratedOddKernel, oddKernel,
    intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_mul_const]
  · intro j hj
    exact (by fun_prop : Continuous (fun x : ℝ ↦
      sin ((oddFreq j : ℝ) * x) *
        sin ((oddFreq j : ℝ) * θ))).intervalIntegrable _ _

theorem targetSine_eq_sum_integratedOddKernel {n : ℕ}
    (F : IvlFam n)
    (α : ↥F.base → ℝ) (θ : ℝ) :
    targetSine F α θ =
      (K * sqrt n) *
        ∑ I : ↥F.base, α I * integratedOddKernel n I.1 θ := by
  classical
  rw [show targetSine F α θ =
      ∑ j ∈ Finset.range n,
        (∑ I : ↥F.base,
          α I * (4 * K * sqrt n *
            ∫ x in I.1.1..I.1.2,
              sin ((oddFreq j : ℝ) * x))) *
          sin ((oddFreq j : ℝ) * θ) by
    simp only [targetSine,
      oddSineSum]
    apply sum_congr rfl
    intro j hj
    rw [fourierTarget,
      dif_pos (Finset.mem_range.mp hj)]
  ]
  simp_rw [integratedOddKernel_eq_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro I hI
  apply sum_congr rfl
  intro j hj
  ring

theorem targetSine_div_eq_sum_integratedOddKernel {n : ℕ} (hn : 0 < n)
    (F : IvlFam n)
    (α : ↥F.base → ℝ) (θ : ℝ) :
    targetSine F α θ /
        (K * sqrt n) =
      ∑ I : ↥F.base, α I * integratedOddKernel n I.1 θ := by
  rw [targetSine_eq_sum_integratedOddKernel]
  exact mul_div_cancel_left₀ _ (mul_ne_zero (by norm_num [K])
    (Real.sqrt_ne_zero'.2 (by exact_mod_cast hn)))

theorem oddKernel_eq_quotient (n : ℕ) {x θ : ℝ}
    (hsub : sin (x - θ) ≠ 0)
    (hadd : sin (x + θ) ≠ 0) :
    oddKernel n x θ =
      sin ((2 * n : ℕ) * (x - θ)) / sin (x - θ) -
        sin ((2 * n : ℕ) * (x + θ)) / sin (x + θ) := by
  simpa [oddKernel, oddFreq, mul_comm] using
    (odd_dirichlet_kernel n
      (θ := x) (θ₀ := θ) hsub hadd)

theorem oddKernel_eq_quotient_of_theta_mem_Icc (n : ℕ) {x θ : ℝ}
    (hx₀ : 0 < x) (hx₁ : x < π / 2)
    (hθ : θ ∈ Icc 0 (π / 2))
    (hxt : x ≠ θ) :
    oddKernel n x θ =
      sin ((2 * n : ℕ) * (x - θ)) / sin (x - θ) -
        sin ((2 * n : ℕ) * (x + θ)) / sin (x + θ) := by
  rcases hθ with ⟨ht₀, ht₁⟩
  apply oddKernel_eq_quotient
  · intro hzero
    have hdiff : x - θ = 0 :=
      (sin_eq_zero_iff_of_lt_of_lt (by linarith [pi_pos])
        (by linarith [pi_pos])).mp hzero
    exact hxt (sub_eq_zero.mp hdiff)
  · intro hzero
    have hsum : x + θ = 0 :=
      (sin_eq_zero_iff_of_lt_of_lt (by linarith [pi_pos])
        (by linarith [pi_pos])).mp hzero
    linarith

theorem intg_oddKernel_eq_quotient_of_theta_mem_Icc (n : ℕ)
    {a b θ : ℝ} (hab : a ≤ b) (ha : 0 < a) (hb : b < π / 2)
    (hθ : θ ∈ Icc 0 (π / 2)) :
    (∫ x in a..b, oddKernel n x θ) =
      ∫ x in a..b,
        (sin ((2 * n : ℕ) * (x - θ)) / sin (x - θ) -
          sin ((2 * n : ℕ) * (x + θ)) / sin (x + θ)) := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume θ] with x hxt hx
  rw [uIoc_of_le hab] at hx
  exact oddKernel_eq_quotient_of_theta_mem_Icc n
    (ha.trans hx.1) (hx.2.trans_lt hb) hθ hxt

theorem integratedOddKernel_eq_quotient_of_mem_base_theta_mem_Icc {n : ℕ}
    (hn : 0 < n) (F : IvlFam n)
    (I : RealIvl) (hI : I ∈ F.base)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (π / 2)) :
    integratedOddKernel n I θ =
      ∫ x in I.1..I.2,
        (sin ((2 * n : ℕ) * (x - θ)) / sin (x - θ) -
          sin ((2 * n : ℕ) * (x + θ)) / sin (x + θ)) := by
  have hnℝ : (0 : ℝ) < n := by exact_mod_cast hn
  have hmesh : 0 < 100 * π / (n : ℝ) := by positivity
  apply intg_oddKernel_eq_quotient_of_theta_mem_Icc n
  · exact F.ordered I hI
  · linarith [F.away_from_axes I hI |>.1]
  · linarith [F.away_from_axes I hI |>.2]
  · exact hθ

theorem targetSin_div_eq_sum_quotientIntg_of_theta_mem_Icc {n : ℕ}
    (hn : 0 < n) (F : IvlFam n)
    (α : ↥F.base → ℝ) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (π / 2)) :
    targetSine F α θ /
        (K * sqrt n) =
      ∑ I : ↥F.base, α I *
        ∫ x in I.1.1..I.1.2,
          (sin ((2 * n : ℕ) * (x - θ)) / sin (x - θ) -
            sin ((2 * n : ℕ) * (x + θ)) /
              sin (x + θ)) := by
  rw [targetSine_div_eq_sum_integratedOddKernel hn]
  apply sum_congr rfl
  intro I hI
  rw [integratedOddKernel_eq_quotient_of_mem_base_theta_mem_Icc
    hn F I.1 I.2 hθ]

end

end OddKernelId

end

section

namespace KernelNearGeometry

open scoped BigOperators
open Set

noncomputable section

open OddSine

def ivlGap (θ : ℝ) (I : RealIvl) : ℝ :=
  max (I.1 - θ) (max (θ - I.2) 0)

theorem ivlGap_eq_zero_of_mem {θ : ℝ} {I : RealIvl}
    (hθ : InIvl I θ) :
    ivlGap θ I = 0 := by
  rw [InIvl, mem_Icc] at hθ
  simp only [ivlGap]
  rw [max_eq_right (sub_nonpos.mpr hθ.2)]
  rw [max_eq_right (sub_nonpos.mpr hθ.1)]

theorem ivlGap_eq_left {θ : ℝ} {I : RealIvl}
    (hI : I.1 ≤ I.2) (hθ : θ ≤ I.1) :
    ivlGap θ I = I.1 - θ := by
  have hθ' : θ ≤ I.2 := hθ.trans hI
  simp only [ivlGap]
  rw [max_eq_right (sub_nonpos.mpr hθ')]
  rw [max_eq_left (sub_nonneg.mpr hθ)]

theorem ivlGap_eq_right {θ : ℝ} {I : RealIvl}
    (hI : I.1 ≤ I.2) (hθ : I.2 ≤ θ) :
    ivlGap θ I = θ - I.2 := by
  have hθ' : I.1 ≤ θ := hI.trans hθ
  simp only [ivlGap]
  rw [max_eq_left (sub_nonneg.mpr hθ)]
  rw [max_eq_right]
  exact (sub_nonpos.mpr hθ').trans (sub_nonneg.mpr hθ)

def Near (n : ℕ) (θ : ℝ) (I : RealIvl) : Prop :=
  ivlGap θ I < π / n

noncomputable def nearIvls {n : ℕ} (F : IvlFam n) (θ : ℝ) :
    Finset RealIvl :=
  @Finset.filter _ (Near n θ) (Classical.decPred _) F.base

def InBaseUnion {n : ℕ} (F : IvlFam n) (θ : ℝ) : Prop :=
  ∃ I ∈ F.base, InIvl I θ

noncomputable def nearLeftIvls {n : ℕ} (F : IvlFam n) (θ : ℝ) :
    Finset RealIvl :=
  @Finset.filter _ (fun I ↦ Near n θ I ∧ I.2 < θ)
    (Classical.decPred _) F.base

noncomputable def nearRightIvls {n : ℕ} (F : IvlFam n) (θ : ℝ) :
    Finset RealIvl :=
  @Finset.filter _ (fun I ↦ Near n θ I ∧ θ < I.1)
    (Classical.decPred _) F.base

noncomputable def nearBaseIvls {n : ℕ} (F : IvlFam n)
    (θ : ℝ) : Finset ↥F.base :=
  @Finset.filter ↥F.base (fun I ↦ Near n θ I.1)
    (Classical.decPred _) Finset.univ

theorem nearIvls_eq_image_nearBaseIvls {n : ℕ}
    (F : IvlFam n) (θ : ℝ) :
    nearIvls F θ =
      (nearBaseIvls F θ).image (fun I ↦ I.1) := by
  classical
  ext I
  simp [nearIvls, nearBaseIvls, and_comm]

theorem eq_of_mem_ivls {n : ℕ} (hn : 0 < n)
    (F : IvlFam n) {θ : ℝ} {I J : RealIvl}
    (hI : I ∈ F.base) (hJ : J ∈ F.base)
    (hθI : InIvl I θ) (hθJ : InIvl J θ) :
    I = J := by
  by_contra hne
  have hsep := F.separated hI hJ hne θ hθI θ hθJ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpi : 0 < π / (n : ℝ) := div_pos pi_pos hnR
  exact (not_le_of_gt hpi) (by simpa using hsep)

theorem ivlGap_ge_of_mem_of_ne {n : ℕ} (hn : 0 < n)
    (F : IvlFam n) {θ : ℝ} {I J : RealIvl}
    (hI : I ∈ F.base) (hJ : J ∈ F.base) (hne : I ≠ J)
    (hθ : InIvl I θ) :
    π / n ≤ ivlGap θ J := by
  have hnotJ : ¬InIvl J θ := by
    intro hθJ
    exact hne (eq_of_mem_ivls hn F hI hJ hθ hθJ)
  rw [InIvl, mem_Icc] at hnotJ
  rcases not_and_or.mp hnotJ with hleft | hright
  · have hleft' : θ < J.1 := lt_of_not_ge hleft
    rw [ivlGap_eq_left (F.ordered J hJ) hleft'.le]
    have hsep := F.separated hI hJ hne θ hθ J.1
      ⟨le_rfl, F.ordered J hJ⟩
    rw [abs_of_neg (sub_neg.mpr hleft')] at hsep
    linarith
  · have hright' : J.2 < θ := lt_of_not_ge hright
    rw [ivlGap_eq_right (F.ordered J hJ) hright'.le]
    have hsep := F.separated hI hJ hne θ hθ J.2
      ⟨F.ordered J hJ, le_rfl⟩
    rw [abs_of_pos (sub_pos.mpr hright')] at hsep
    exact hsep

theorem nearBaseIvls_eq_singleton_of_mem {n : ℕ} (hn : 0 < n)
    (F : IvlFam n) {θ : ℝ} {I : RealIvl}
    (hI : I ∈ F.base) (hθ : InIvl I θ) :
    nearBaseIvls F θ = {⟨I, hI⟩} := by
  classical
  ext J
  simp only [nearBaseIvls, mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro hnear
    apply Subtype.ext
    by_contra hne
    have hgap := ivlGap_ge_of_mem_of_ne hn F hI J.property
      (fun h ↦ hne h.symm) hθ
    exact (not_lt_of_ge hgap) hnear
  · intro hJI
    subst J
    rw [Near, ivlGap_eq_zero_of_mem hθ]
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact div_pos pi_pos hnR

theorem card_nearBaseIvls_eq_card_nearIvls {n : ℕ}
    (F : IvlFam n) (θ : ℝ) :
    (nearBaseIvls F θ).card = (nearIvls F θ).card := by
  rw [nearIvls_eq_image_nearBaseIvls]
  exact (Finset.card_image_of_injective _ Subtype.val_injective).symm

theorem nearIvls_eq_left_union_right_of_not_inBaseUnion {n : ℕ}
    (F : IvlFam n) {θ : ℝ}
    (hout : ¬InBaseUnion F θ) :
    nearIvls F θ =
      nearLeftIvls F θ ∪ nearRightIvls F θ := by
  classical
  ext I
  simp only [nearIvls, nearLeftIvls, nearRightIvls,
    mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hI, hnear⟩
    have hnot : ¬InIvl I θ := fun h ↦ hout ⟨I, hI, h⟩
    rw [InIvl, mem_Icc] at hnot
    rcases not_and_or.mp hnot with hright | hleft
    · exact Or.inr ⟨hI, hnear, lt_of_not_ge hright⟩
    · exact Or.inl ⟨hI, hnear, lt_of_not_ge hleft⟩
  · rintro (hleft | hright)
    · exact ⟨hleft.1, hleft.2.1⟩
    · exact ⟨hright.1, hright.2.1⟩

theorem card_nearLeftIvls_le_one {n : ℕ} (_hn : 0 < n)
    (F : IvlFam n) (θ : ℝ) :
    (nearLeftIvls F θ).card ≤ 1 := by
  classical
  rw [card_le_one]
  intro I hI J hJ
  simp only [nearLeftIvls, mem_filter] at hI hJ
  by_contra hne
  have hsep := F.separated hI.1 hJ.1 hne I.2
    ⟨F.ordered I hI.1, le_rfl⟩ J.2 ⟨F.ordered J hJ.1, le_rfl⟩
  have hgapI : θ - I.2 < π / n := by
    rw [← ivlGap_eq_right (F.ordered I hI.1) hI.2.2.le]
    exact hI.2.1
  have hgapJ : θ - J.2 < π / n := by
    rw [← ivlGap_eq_right (F.ordered J hJ.1) hJ.2.2.le]
    exact hJ.2.1
  have habs : |I.2 - J.2| < π / n := by
    rw [abs_lt]
    constructor <;> linarith [hI.2.2, hJ.2.2]
  exact (not_lt_of_ge hsep) habs

theorem card_nearRightIvls_le_one {n : ℕ} (_hn : 0 < n)
    (F : IvlFam n) (θ : ℝ) :
    (nearRightIvls F θ).card ≤ 1 := by
  classical
  rw [card_le_one]
  intro I hI J hJ
  simp only [nearRightIvls, mem_filter] at hI hJ
  by_contra hne
  have hsep := F.separated hI.1 hJ.1 hne I.1
    ⟨le_rfl, F.ordered I hI.1⟩ J.1 ⟨le_rfl, F.ordered J hJ.1⟩
  have hgapI : I.1 - θ < π / n := by
    rw [← ivlGap_eq_left (F.ordered I hI.1) hI.2.2.le]
    exact hI.2.1
  have hgapJ : J.1 - θ < π / n := by
    rw [← ivlGap_eq_left (F.ordered J hJ.1) hJ.2.2.le]
    exact hJ.2.1
  have habs : |I.1 - J.1| < π / n := by
    rw [abs_lt]
    constructor <;> linarith [hI.2.2, hJ.2.2]
  exact (not_lt_of_ge hsep) habs

theorem card_nearIvls_le_two_of_not_inBaseUnion {n : ℕ} (hn : 0 < n)
    (F : IvlFam n) {θ : ℝ}
    (hout : ¬InBaseUnion F θ) :
    (nearIvls F θ).card ≤ 2 := by
  rw [nearIvls_eq_left_union_right_of_not_inBaseUnion F hout]
  calc
    (nearLeftIvls F θ ∪ nearRightIvls F θ).card ≤
        (nearLeftIvls F θ).card +
          (nearRightIvls F θ).card :=
      card_union_le _ _
    _ ≤ 1 + 1 := Nat.add_le_add
      (card_nearLeftIvls_le_one hn F θ)
      (card_nearRightIvls_le_one hn F θ)
    _ = 2 := rfl

theorem card_nearBaseIvls_le_two_of_not_inBaseUnion {n : ℕ}
    (hn : 0 < n) (F : IvlFam n) {θ : ℝ}
    (hout : ¬InBaseUnion F θ) :
    (nearBaseIvls F θ).card ≤ 2 := by
  rw [card_nearBaseIvls_eq_card_nearIvls]
  exact card_nearIvls_le_two_of_not_inBaseUnion hn F hout

theorem existsUnique_baseIvl_of_dangerous_firstQuad {n : ℕ}
    (hn : 0 < n) (F : IvlFam n) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (π / 2))
    (hdangerous : IsDangerous F θ) :
    ∃! I : RealIvl, I ∈ F.base ∧ InIvl I θ := by
  rcases hdangerous with ⟨I, hI, hmain | hneg | hreflect | htranslate⟩
  · refine ⟨I, ⟨hI, hmain⟩, ?_⟩
    rintro J ⟨hJ, hθJ⟩
    exact eq_of_mem_ivls hn F hJ hI hθJ hmain
  · have hquadI := F.in_first_quadrant I hI
    rw [InIvl, mem_Icc] at hneg
    have hθ0 : θ = 0 := by linarith [hθ.1, hquadI.1, hneg.1]
    have hmain : InIvl I θ := by
      rw [InIvl, mem_Icc]
      simpa [hθ0] using hneg
    refine ⟨I, ⟨hI, hmain⟩, ?_⟩
    rintro J ⟨hJ, hθJ⟩
    exact eq_of_mem_ivls hn F hJ hI hθJ hmain
  · have hquadI := F.in_first_quadrant I hI
    rw [InIvl, mem_Icc] at hreflect
    have hθMid : θ = π / 2 := by
      linarith [hθ.2, hquadI.2, hreflect.2]
    have harg : π - θ = θ := by
      rw [hθMid]
      ring
    have hmain : InIvl I θ := by
      rw [InIvl, mem_Icc, ← harg]
      exact hreflect
    refine ⟨I, ⟨hI, hmain⟩, ?_⟩
    rintro J ⟨hJ, hθJ⟩
    exact eq_of_mem_ivls hn F hJ hI hθJ hmain
  · have hquadI := F.in_first_quadrant I hI
    rw [InIvl, mem_Icc] at htranslate
    exfalso
    nlinarith [hθ.2, hquadI.1, htranslate.1, pi_pos]

theorem existsUnique_baseSubtype_of_dangerous_firstQuad {n : ℕ}
    (hn : 0 < n) (F : IvlFam n) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (π / 2))
    (hdangerous : IsDangerous F θ) :
    ∃! I : ↥F.base, InIvl I.1 θ := by
  obtain ⟨I, hI, hunique⟩ :=
    existsUnique_baseIvl_of_dangerous_firstQuad hn F hθ hdangerous
  refine ⟨⟨I, hI.1⟩, hI.2, ?_⟩
  intro J hθJ
  apply Subtype.ext
  exact hunique J.1 ⟨J.property, hθJ⟩

theorem sum_nearBaseIvls_eq_of_mem {n : ℕ} (hn : 0 < n)
    (F : IvlFam n) {θ : ℝ} {I : RealIvl}
    (hI : I ∈ F.base) (hθ : InIvl I θ)
    (f : ↥F.base → ℝ) :
    ∑ J ∈ nearBaseIvls F θ, f J = f ⟨I, hI⟩ := by
  rw [nearBaseIvls_eq_singleton_of_mem hn F hI hθ]
  simp

theorem abs_sum_nearBaseIvls_le_two_mul_of_not_inBaseUnion {n : ℕ}
    (hn : 0 < n) (F : IvlFam n) {θ C : ℝ}
    (hout : ¬InBaseUnion F θ) (hC : 0 ≤ C)
    (f : ↥F.base → ℝ)
    (hf : ∀ I ∈ nearBaseIvls F θ, |f I| ≤ C) :
    |∑ I ∈ nearBaseIvls F θ, f I| ≤ 2 * C := by
  classical
  have hcard := card_nearBaseIvls_le_two_of_not_inBaseUnion hn F hout
  calc
    |∑ I ∈ nearBaseIvls F θ, f I| ≤
        ∑ I ∈ nearBaseIvls F θ, |f I| := by
          exact abs_sum_le_sum_abs _ _
    _ ≤ ∑ _I ∈ nearBaseIvls F θ, C := by
      exact sum_le_sum fun I hI ↦ hf I hI
    _ = ((nearBaseIvls F θ).card : ℝ) * C := by simp
    _ ≤ 2 * C := by
      gcongr
      exact_mod_cast hcard

end

end KernelNearGeometry

end

open KernelNearGeometry


section
namespace SinIntgGrid

open scoped Interval
open Real Set MeasureTheory intervalIntegral

noncomputable section

private def loSincPoly (x : ℝ) : ℝ :=
  1 - x ^ 2 / 6 + x ^ 4 / 120 - x ^ 6 / 5040

private def geometricLo (x : ℝ) : ℝ :=
  1 - x / π + (x / π) ^ 2 - (x / π) ^ 3

private lemma sin_taylor_seven_le {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 ≤ sin x := by
  let q (t : ℝ) := cos t -
    (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720)
  have hqderiv (t : ℝ) :
      deriv q t = -sin t + t - t ^ 3 / 6 + t ^ 5 / 120 := by
    simp (disch := fun_prop) [q]
    ring
  have hqmono : MonotoneOn q (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [hqderiv]
    have ht0 : 0 ≤ t := by
      rw [interior_Ici, mem_Ioi] at ht
      exact ht.le
    linarith [sin_le_taylor_five ht0]
  have hq {t : ℝ} (ht : 0 ≤ t) :
      1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 ≤ cos t := by
    have h := hqmono (show (0 : ℝ) ∈ Ici 0 by simp)
      (show t ∈ Ici 0 by exact ht) ht
    dsimp [q] at h
    norm_num at h
    linarith
  let f (t : ℝ) := sin t -
    (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040)
  have hfderiv (t : ℝ) :
      deriv f t = cos t -
        (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720) := by
    simp (disch := fun_prop) [f]
    ring
  have hfmono : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [hfderiv]
    have ht0 : 0 ≤ t := by
      rw [interior_Ici, mem_Ioi] at ht
      exact ht.le
    linarith [hq ht0]
  have h := hfmono (show (0 : ℝ) ∈ Ici 0 by simp)
    (show x ∈ Ici 0 by exact hx) hx
  dsimp [f] at h
  norm_num at h
  linarith

private lemma loSincPoly_le_sinc {x : ℝ} (hx : 0 ≤ x) :
    loSincPoly x ≤ sinc x := by
  obtain rfl | hxpos := hx.eq_or_lt
  · norm_num [loSincPoly]
  rw [sinc_of_ne_zero hxpos.ne']
  apply (le_div_iff₀ hxpos).2
  have h := sin_taylor_seven_le hxpos.le
  dsimp [loSincPoly]
  nlinarith

private lemma sinc_nonneg_on_zero_pi {x : ℝ} (hx0 : 0 ≤ x)
    (hxpi : x ≤ π) : 0 ≤ sinc x := by
  obtain rfl | hxpos := hx0.eq_or_lt
  · simp
  rw [sinc_of_ne_zero hxpos.ne']
  exact div_nonneg (sin_nonneg_of_nonneg_of_le_pi hx0 hxpi) hx0

private lemma geometricLo_nonneg {x : ℝ} (hx0 : 0 ≤ x)
    (hxpi : x ≤ π) : 0 ≤ geometricLo x := by
  have hpi : 0 < π := pi_pos
  have hu0 : 0 ≤ x / π := div_nonneg hx0 hpi.le
  have hu1 : x / π ≤ 1 := (div_le_one hpi).2 hxpi
  dsimp [geometricLo]
  nlinarith [sq_nonneg (x / π)]

private lemma geometricLo_le_wt {x : ℝ} (hx0 : 0 ≤ x)
    (hxpi : x ≤ π) :
    geometricLo x ≤ π / (x + π) := by
  have hpi : 0 < π := pi_pos
  have hxpi_pos : 0 < x + π := add_pos_of_nonneg_of_pos hx0 hpi
  apply (le_div_iff₀ hxpi_pos).2
  dsimp [geometricLo]
  field_simp
  ring_nf
  nlinarith [sq_nonneg (x ^ 2)]

private lemma sinc_add_pi_eq_wt (x : ℝ) (hx0 : 0 ≤ x)
    (hxpi : x ≤ π) :
    sinc x + sinc (x + π) =
      sinc x * (π / (x + π)) := by
  by_cases hx : x = 0
  · subst x
    simp [sinc_of_ne_zero pi_ne_zero]
  have hxpi0 : x + π ≠ 0 := by positivity
  rw [sinc_of_ne_zero hx, sinc_of_ne_zero hxpi0, sin_add_pi]
  field_simp
  ring

private lemma poly_pair_le (x : ℝ) (hx : x ∈ Icc (0 : ℝ) π) :
    loSincPoly x * geometricLo x ≤
      sinc x + sinc (x + π) := by
  have hsinc0 := sinc_nonneg_on_zero_pi hx.1 hx.2
  have hpoly := loSincPoly_le_sinc hx.1
  have hgeom0 := geometricLo_nonneg hx.1 hx.2
  have hweight := geometricLo_le_wt hx.1 hx.2
  rw [sinc_add_pi_eq_wt x hx.1 hx.2]
  exact (mul_le_mul_of_nonneg_right hpoly hgeom0).trans
    (mul_le_mul_of_nonneg_left hweight hsinc0)

private lemma intg_poly_pair :
    (∫ x in (0 : ℝ)..π,
      loSincPoly x * geometricLo x) =
      -(73 * π ^ 7) / 12700800 +
        43 * π ^ 5 / 100800 - 7 * π ^ 3 / 360 +
          7 * π / 12 := by
  let F (x : ℝ) :=
    -x ^ 7 / 35280 + x ^ 5 / 600 - x ^ 3 / 18 + x +
    x ^ 8 / (40320 * π) - x ^ 6 / (720 * π) +
    x ^ 4 / (24 * π) - x ^ 2 / (2 * π) -
    x ^ 9 / (45360 * π ^ 2) + x ^ 7 / (840 * π ^ 2) -
    x ^ 5 / (30 * π ^ 2) + x ^ 3 / (3 * π ^ 2) +
    x ^ 10 / (50400 * π ^ 3) - x ^ 8 / (960 * π ^ 3) +
    x ^ 6 / (36 * π ^ 3) - x ^ 4 / (4 * π ^ 3)
  rw [integral_eq_sub_of_hasDerivAt
    (f := F) (f' := fun x => loSincPoly x * geometricLo x)]
  · dsimp [F]
    field_simp [pi_ne_zero]
    ring
  · intro x hx
    have hdiff : DifferentiableAt ℝ F x := by
      dsimp [F]
      fun_prop
    have hderiv : deriv F x =
        loSincPoly x * geometricLo x := by
      simp (disch := fun_prop) [F, loSincPoly, geometricLo]
      field_simp [pi_ne_zero]
      ring
    rw [← hderiv]
    exact hdiff.hasDerivAt
  · exact (by fun_prop : Continuous
      (fun x : ℝ => (1 - x ^ 2 / 6 + x ^ 4 / 120 - x ^ 6 / 5040) *
        (1 - x / π + (x / π) ^ 2 - (x / π) ^ 3))).intervalIntegrable _ _

private lemma four_thirds_lt_intg_poly_pair :
    (4 : ℝ) / 3 < ∫ x in (0 : ℝ)..π,
      loSincPoly x * geometricLo x := by
  rw [intg_poly_pair]
  have hpi : (3.14 : ℝ) < π := pi_gt_d2
  have hpi' : π < (3.15 : ℝ) := pi_lt_d2
  have h3 : π ^ 3 < (3.15 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hpi' pi_pos.le (by norm_num)
  have h5 : (3.14 : ℝ) ^ 5 < π ^ 5 :=
    pow_lt_pow_left₀ hpi (by norm_num) (by norm_num)
  have h7 : π ^ 7 < (3.15 : ℝ) ^ 7 :=
    pow_lt_pow_left₀ hpi' pi_pos.le (by norm_num)
  norm_num at hpi hpi' h3 h5 h7 ⊢
  linarith

theorem four_thirds_lt_sinIntg_two_pi :
    (4 : ℝ) / 3 < sinIntg (2 * π) := by
  have hsinc : IntervalIntegrable sinc volume (0 : ℝ) π :=
    continuous_sinc.intervalIntegrable _ _
  have hsinc' : IntervalIntegrable (fun x : ℝ => sinc (x + π))
      volume (0 : ℝ) π :=
    (continuous_sinc.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
  have hpoly : IntervalIntegrable
      (fun x : ℝ => loSincPoly x * geometricLo x)
      volume (0 : ℝ) π :=
    (by fun_prop : Continuous
      (fun x : ℝ => (1 - x ^ 2 / 6 + x ^ 4 / 120 - x ^ 6 / 5040) *
        (1 - x / π + (x / π) ^ 2 - (x / π) ^ 3))).intervalIntegrable _ _
  have hmono := integral_mono_on pi_pos.le hpoly
    (hsinc.add hsinc') poly_pair_le
  calc
    (4 : ℝ) / 3 < ∫ x in (0 : ℝ)..π,
        loSincPoly x * geometricLo x :=
      four_thirds_lt_intg_poly_pair
    _ ≤ ∫ x in (0 : ℝ)..π,
        (sinc x + sinc (x + π)) := hmono
    _ = sinIntg (2 * π) := by
      rw [intervalIntegral.integral_add hsinc hsinc']
      rw [integral_comp_add_right sinc Real.pi]
      have hadd := integral_add_adjacent_intervals hsinc
        (continuous_sinc.intervalIntegrable π (2 * π))
      unfold sinIntg
      convert hadd using 1 <;> ring

private def evenPt (k : ℕ) : ℝ := (k : ℝ) * (2 * π)

private lemma evenPt_nonneg (k : ℕ) : 0 ≤ evenPt k :=
  mul_nonneg (Nat.cast_nonneg k) (by positivity)

private lemma evenPt_pos {k : ℕ} (hk : 0 < k) : 0 < evenPt k := by
  dsimp [evenPt]
  exact mul_pos (by exact_mod_cast hk) (by positivity)

private lemma sin_evenPt_add (k : ℕ) (x : ℝ) :
    sin (evenPt k + x) = sin x := by
  rw [add_comm]
  exact Real.sin_add_nat_mul_two_pi x k

private lemma sinc_even_pair_nonneg {k : ℕ} (hk : 0 < k)
    {x : ℝ} (hx0 : 0 ≤ x) (hxpi : x ≤ π) :
    0 ≤ sinc (evenPt k + x) +
      sinc (evenPt k + π + x) := by
  have hc : 0 < evenPt k := evenPt_pos hk
  have hcx : 0 < evenPt k + x := add_pos_of_pos_of_nonneg hc hx0
  have hcxpi : 0 < evenPt k + π + x := by positivity
  have hsin : 0 ≤ sin x :=
    sin_nonneg_of_nonneg_of_le_pi hx0 hxpi
  rw [sinc_of_ne_zero hcx.ne', sinc_of_ne_zero hcxpi.ne']
  rw [sin_evenPt_add]
  have hphase : evenPt k + π + x = evenPt k + (x + π) := by ring
  rw [hphase, sin_evenPt_add, sin_add_pi]
  have hden : evenPt k + x ≤ evenPt k + (x + π) := by
    linarith [pi_pos]
  have hrecip := one_div_le_one_div_of_le hcx hden
  calc
    0 ≤ sin x *
        (1 / (evenPt k + x) - 1 / (evenPt k + (x + π))) :=
      mul_nonneg hsin (sub_nonneg.2 hrecip)
    _ = sin x / (evenPt k + x) +
        -sin x / (evenPt k + (x + π)) := by ring

private lemma sinc_odd_pair_nonpos (k : ℕ)
    {x : ℝ} (hx0 : 0 ≤ x) (hxpi : x ≤ π) :
    sinc (evenPt k + π + x) +
      sinc (evenPt (k + 1) + x) ≤ 0 := by
  have hfirst : 0 < evenPt k + π + x := by
    have := evenPt_nonneg k
    positivity
  have hsecond : 0 < evenPt (k + 1) + x := by
    apply add_pos_of_pos_of_nonneg
    · exact evenPt_pos (Nat.succ_pos k)
    · exact hx0
  have hsin : 0 ≤ sin x :=
    sin_nonneg_of_nonneg_of_le_pi hx0 hxpi
  rw [sinc_of_ne_zero hfirst.ne', sinc_of_ne_zero hsecond.ne']
  have hphase1 : evenPt k + π + x = evenPt k + (x + π) := by ring
  rw [hphase1, sin_evenPt_add, sin_add_pi, sin_evenPt_add]
  have heven : evenPt (k + 1) = evenPt k + 2 * π := by
    simp [evenPt]
    ring
  have hden : evenPt k + (x + π) ≤ evenPt (k + 1) + x := by
    rw [heven]
    linarith [pi_pos]
  have hfirst' : 0 < evenPt k + (x + π) := by
    linarith
  have hrecip := one_div_le_one_div_of_le hfirst' hden
  calc
    -sin x / (evenPt k + (x + π)) +
        sin x / (evenPt (k + 1) + x) =
        sin x *
          (1 / (evenPt (k + 1) + x) -
            1 / (evenPt k + (x + π))) := by ring
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hsin (sub_nonpos.2 hrecip)

private lemma intg_nonpos_of_nonpos {a b : ℝ} (hab : a ≤ b)
    {f : ℝ → ℝ} (hf : ∀ x ∈ Icc a b, f x ≤ 0) :
    (∫ x in a..b, f x) ≤ 0 := by
  have h := intervalIntegral.integral_nonneg (μ := volume) hab
    (fun x hx => neg_nonneg.2 (hf x hx))
  rw [intervalIntegral.integral_neg] at h
  linarith

private lemma even_full_blk_nonneg {k : ℕ} (hk : 0 < k) :
    0 ≤ ∫ x in evenPt k..evenPt (k + 1), sinc x := by
  have hs : IntervalIntegrable sinc volume
      (evenPt k) (evenPt k + π) :=
    continuous_sinc.intervalIntegrable _ _
  have hs' : IntervalIntegrable sinc volume
      (evenPt k + π) (evenPt (k + 1)) :=
    continuous_sinc.intervalIntegrable _ _
  have hshift1 := integral_comp_add_right sinc (evenPt k)
    (a := (0 : ℝ)) (b := π)
  have hshift2 := integral_comp_add_right sinc
    (evenPt k + π) (a := (0 : ℝ)) (b := π)
  have hp : 0 ≤ ∫ x in (0 : ℝ)..π,
      (sinc (evenPt k + x) +
        sinc (evenPt k + π + x)) := by
    apply intervalIntegral.integral_nonneg pi_pos.le
    intro x hx
    exact sinc_even_pair_nonneg hk hx.1 hx.2
  have hadd := integral_add_adjacent_intervals hs hs'
  have hi1 : (∫ x in evenPt k..evenPt k + π, sinc x) =
      ∫ x in (0 : ℝ)..π, sinc (evenPt k + x) := by
    rw [add_comm (evenPt k)]
    convert hshift1.symm using 1 <;> ring
  have hi2 : (∫ x in evenPt k + Real.pi..evenPt (k + 1), sinc x) =
      ∫ x in (0 : ℝ)..π, sinc (evenPt k + π + x) := by
    convert hshift2.symm using 1 <;> simp [evenPt] <;> ring
  rw [← hadd]
  rw [hi1, hi2]
  have ha : IntervalIntegrable (fun x : ℝ => sinc (evenPt k + x))
      volume (0 : ℝ) π := by
    exact (continuous_sinc.comp
      (continuous_const.add continuous_id)).intervalIntegrable _ _
  have hb : IntervalIntegrable
      (fun x : ℝ => sinc (evenPt k + π + x))
      volume (0 : ℝ) π := by
    exact (continuous_sinc.comp
      ((continuous_const.add continuous_const).add continuous_id)).intervalIntegrable _ _
  have hsum := intervalIntegral.integral_add ha hb
  rw [← hsum]
  exact hp

private lemma odd_full_blk_nonpos (k : ℕ) :
    (∫ x in evenPt k + Real.pi..evenPt (k + 1) + π,
      sinc x) ≤ 0 := by
  have hs : IntervalIntegrable sinc volume
      (evenPt k + π) (evenPt (k + 1)) :=
    continuous_sinc.intervalIntegrable _ _
  have hs' : IntervalIntegrable sinc volume
      (evenPt (k + 1)) (evenPt (k + 1) + π) :=
    continuous_sinc.intervalIntegrable _ _
  have hshift1 := integral_comp_add_right sinc
    (evenPt k + π) (a := (0 : ℝ)) (b := π)
  have hshift2 := integral_comp_add_right sinc
    (evenPt (k + 1)) (a := (0 : ℝ)) (b := π)
  have hp : (∫ x in (0 : ℝ)..π,
      (sinc (evenPt k + π + x) +
        sinc (evenPt (k + 1) + x))) ≤ 0 := by
    apply intg_nonpos_of_nonpos pi_pos.le
    intro x hx
    exact sinc_odd_pair_nonpos k hx.1 hx.2
  have hadd := integral_add_adjacent_intervals hs hs'
  have hi1 : (∫ x in evenPt k + Real.pi..evenPt (k + 1), sinc x) =
      ∫ x in (0 : ℝ)..π, sinc (evenPt k + π + x) := by
    convert hshift1.symm using 1 <;> simp [evenPt] <;> ring
  have hi2 : (∫ x in evenPt (k + 1)..evenPt (k + 1) + π,
      sinc x) =
      ∫ x in (0 : ℝ)..π, sinc (evenPt (k + 1) + x) := by
    rw [add_comm (evenPt (k + 1))]
    convert hshift2.symm using 1 <;> ring
  rw [← hadd]
  rw [hi1, hi2]
  have ha : IntervalIntegrable
      (fun x : ℝ => sinc (evenPt k + π + x))
      volume (0 : ℝ) π := by
    exact (continuous_sinc.comp
      ((continuous_const.add continuous_const).add continuous_id)).intervalIntegrable _ _
  have hb : IntervalIntegrable
      (fun x : ℝ => sinc (evenPt (k + 1) + x))
      volume (0 : ℝ) π := by
    exact (continuous_sinc.comp
      (continuous_const.add continuous_id)).intervalIntegrable _ _
  have hsum := intervalIntegral.integral_add ha hb
  rw [← hsum]
  exact hp

private lemma sinc_nonneg_even_half (k : ℕ) {x : ℝ}
    (hlo : evenPt k ≤ x) (hhi : x ≤ evenPt k + π) :
    0 ≤ sinc x := by
  by_cases hx : x = 0
  · subst x
    simp
  have hx0 : 0 ≤ x := (evenPt_nonneg k).trans hlo
  have ht0 : 0 ≤ x - evenPt k := sub_nonneg.2 hlo
  have htpi : x - evenPt k ≤ π := by linarith
  have hsin_t : 0 ≤ sin (x - evenPt k) :=
    sin_nonneg_of_nonneg_of_le_pi ht0 htpi
  have hphase : evenPt k + (x - evenPt k) = x := by ring
  have hsin : sin x = sin (x - evenPt k) := by
    calc
      sin x = sin (evenPt k + (x - evenPt k)) :=
        congrArg sin hphase.symm
      _ = sin (x - evenPt k) := sin_evenPt_add _ _
  rw [sinc_of_ne_zero hx, hsin]
  exact div_nonneg hsin_t hx0

private lemma sinc_nonpos_odd_half (k : ℕ) {x : ℝ}
    (hlo : evenPt k + π ≤ x) (hhi : x ≤ evenPt (k + 1)) :
    sinc x ≤ 0 := by
  have hc0 := evenPt_nonneg k
  have hxpos : 0 < x := lt_of_lt_of_le (by linarith [pi_pos] :
    0 < evenPt k + π) hlo
  let t := x - (evenPt k + π)
  have ht0 : 0 ≤ t := sub_nonneg.2 hlo
  have heven : evenPt (k + 1) = evenPt k + 2 * π := by
    simp [evenPt]
    ring
  have htpi : t ≤ π := by
    dsimp [t]
    rw [heven] at hhi
    linarith
  have hsint : 0 ≤ sin t :=
    sin_nonneg_of_nonneg_of_le_pi ht0 htpi
  have hphase : x = evenPt k + (t + π) := by
    dsimp [t]
    ring
  have hden : 0 ≤ evenPt k + (t + π) := by
    rw [← hphase]
    exact hxpos.le
  rw [sinc_of_ne_zero hxpos.ne', hphase, sin_evenPt_add,
    sin_add_pi]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hsint) hden

private lemma even_partial_blk_nonneg {k : ℕ} (hk : 0 < k) {x : ℝ}
    (hlo : evenPt k ≤ x) (hhi : x ≤ evenPt (k + 1)) :
    0 ≤ ∫ t in evenPt k..x, sinc t := by
  by_cases hmid : x ≤ evenPt k + π
  · apply intervalIntegral.integral_nonneg (μ := volume) hlo
    intro t ht
    exact sinc_nonneg_even_half k ht.1 (ht.2.trans hmid)
  · have hxmid : evenPt k + π ≤ x := le_of_not_ge hmid
    have htail : (∫ t in x..evenPt (k + 1), sinc t) ≤ 0 := by
      apply intg_nonpos_of_nonpos hhi
      intro t ht
      exact sinc_nonpos_odd_half k (hxmid.trans ht.1) ht.2
    have hadd := integral_add_adjacent_intervals (μ := volume)
      (continuous_sinc.intervalIntegrable (evenPt k) x)
      (continuous_sinc.intervalIntegrable x (evenPt (k + 1)))
    linarith [even_full_blk_nonneg hk]

private lemma odd_partial_blk_nonpos (k : ℕ) {x : ℝ}
    (hlo : evenPt k + π ≤ x)
    (hhi : x ≤ evenPt (k + 1) + π) :
    (∫ t in evenPt k + Real.pi..x, sinc t) ≤ 0 := by
  by_cases hmid : x ≤ evenPt (k + 1)
  · apply intg_nonpos_of_nonpos hlo
    intro t ht
    exact sinc_nonpos_odd_half k ht.1 (ht.2.trans hmid)
  · have hxmid : evenPt (k + 1) ≤ x := le_of_not_ge hmid
    have htail : 0 ≤ ∫ t in x..evenPt (k + 1) + π,
        sinc t := by
      apply intervalIntegral.integral_nonneg (μ := volume) hhi
      intro t ht
      exact sinc_nonneg_even_half (k + 1) (hxmid.trans ht.1) ht.2
    have hadd := integral_add_adjacent_intervals (μ := volume)
      (continuous_sinc.intervalIntegrable (evenPt k + π) x)
      (continuous_sinc.intervalIntegrable x (evenPt (k + 1) + π))
    linarith [odd_full_blk_nonpos k]

private lemma even_grid_tail_nonneg (k : ℕ) :
    0 ≤ ∫ x in evenPt 1..evenPt (k + 1), sinc x := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hadd := integral_add_adjacent_intervals (μ := volume)
        (continuous_sinc.intervalIntegrable (evenPt 1) (evenPt (k + 1)))
        (continuous_sinc.intervalIntegrable (evenPt (k + 1))
          (evenPt (k + 2)))
      have hblock := even_full_blk_nonneg (k := k + 1) (Nat.succ_pos k)
      rw [← hadd]
      exact add_nonneg ih hblock

private lemma odd_grid_tail_nonpos (k : ℕ) :
    (∫ x in Real.pi..evenPt k + π, sinc x) ≤ 0 := by
  induction k with
  | zero => simp [evenPt]
  | succ k ih =>
      have hadd := integral_add_adjacent_intervals (μ := volume)
        (continuous_sinc.intervalIntegrable π (evenPt k + π))
        (continuous_sinc.intervalIntegrable (evenPt k + π)
          (evenPt (k + 1) + π))
      have hblock := odd_full_blk_nonpos k
      rw [← hadd]
      exact add_nonpos ih hblock

private lemma even_tail_nonneg_of_le_fourteen_pi {x : ℝ}
    (hlo : evenPt 1 ≤ x) (hhi : x ≤ evenPt 7) :
    0 ≤ ∫ t in evenPt 1..x, sinc t := by
  have join (k : ℕ) (hk : 0 < k) (hklow : evenPt k ≤ x)
      (hkhi : x ≤ evenPt (k + 1)) :
      0 ≤ ∫ t in evenPt 1..x, sinc t := by
    have hadd := integral_add_adjacent_intervals (μ := volume)
      (continuous_sinc.intervalIntegrable (evenPt 1) (evenPt k))
      (continuous_sinc.intervalIntegrable (evenPt k) x)
    rw [← hadd]
    exact add_nonneg (by simpa [Nat.sub_add_cancel hk] using even_grid_tail_nonneg (k - 1))
      (even_partial_blk_nonneg hk hklow hkhi)
  by_cases h2 : x ≤ evenPt 2
  · exact join 1 (by norm_num) hlo h2
  by_cases h3 : x ≤ evenPt 3
  · exact join 2 (by norm_num) (le_of_not_ge h2) h3
  by_cases h4 : x ≤ evenPt 4
  · exact join 3 (by norm_num) (le_of_not_ge h3) h4
  by_cases h5 : x ≤ evenPt 5
  · exact join 4 (by norm_num) (le_of_not_ge h4) h5
  by_cases h6 : x ≤ evenPt 6
  · exact join 5 (by norm_num) (le_of_not_ge h5) h6
  exact join 6 (by norm_num) (le_of_not_ge h6) hhi

private lemma odd_tail_nonpos_of_le_fourteen_pi {x : ℝ}
    (hlo : π ≤ x) (hhi : x ≤ evenPt 7) :
    (∫ t in Real.pi..x, sinc t) ≤ 0 := by
  have join (k : ℕ) (hklow : evenPt k + π ≤ x)
      (hkhi : x ≤ evenPt (k + 1) + π) :
      (∫ t in Real.pi..x, sinc t) ≤ 0 := by
    have hadd := integral_add_adjacent_intervals (μ := volume)
      (continuous_sinc.intervalIntegrable π (evenPt k + π))
      (continuous_sinc.intervalIntegrable (evenPt k + π) x)
    rw [← hadd]
    exact add_nonpos (odd_grid_tail_nonpos k)
      (odd_partial_blk_nonpos k hklow hkhi)
  by_cases h1 : x ≤ evenPt 1 + π
  · exact join 0 (by simpa [evenPt] using hlo) h1
  by_cases h2 : x ≤ evenPt 2 + π
  · exact join 1 (le_of_not_ge h1) h2
  by_cases h3 : x ≤ evenPt 3 + π
  · exact join 2 (le_of_not_ge h2) h3
  by_cases h4 : x ≤ evenPt 4 + π
  · exact join 3 (le_of_not_ge h3) h4
  by_cases h5 : x ≤ evenPt 5 + π
  · exact join 4 (le_of_not_ge h4) h5
  by_cases h6 : x ≤ evenPt 6 + π
  · exact join 5 (le_of_not_ge h5) h6
  have hlast : x ≤ evenPt 7 + π := hhi.trans (le_add_of_nonneg_right pi_pos.le)
  exact join 6 (le_of_not_ge h6) hlast

theorem sinIntg_mem_zero_two {x : ℝ} (hx0 : 0 ≤ x)
    (hx14 : x ≤ 14 * π) :
    sinIntg x ∈ Icc (0 : ℝ) 2 := by
  have hxEven : x ≤ evenPt 7 := by
    dsimp [evenPt]
    convert hx14 using 1 <;> ring
  constructor
  · by_cases hxpi : x ≤ π
    · apply intervalIntegral.integral_nonneg hx0
      intro t ht
      exact sinc_nonneg_on_zero_pi ht.1 (ht.2.trans hxpi)
    by_cases hx2 : x ≤ evenPt 1
    · have htail : (∫ t in x..evenPt 1, sinc t) ≤ 0 := by
        apply intg_nonpos_of_nonpos hx2
        intro t ht
        have htpi : π ≤ t := (le_of_not_ge hxpi).trans ht.1
        exact sinc_nonpos_odd_half 0 (by simpa [evenPt] using htpi) ht.2
      have hadd := integral_add_adjacent_intervals (μ := volume)
        (continuous_sinc.intervalIntegrable (0 : ℝ) x)
        (continuous_sinc.intervalIntegrable x (evenPt 1))
      have hfirst := four_thirds_lt_sinIntg_two_pi
      unfold sinIntg at hfirst ⊢
      have heq : evenPt 1 = 2 * π := by simp [evenPt]
      rw [heq] at hadd htail
      linarith
    · have htail := even_tail_nonneg_of_le_fourteen_pi (le_of_not_ge hx2) hxEven
      have hadd := integral_add_adjacent_intervals (μ := volume)
        (continuous_sinc.intervalIntegrable (0 : ℝ) (evenPt 1))
        (continuous_sinc.intervalIntegrable (evenPt 1) x)
      have hfirst := four_thirds_lt_sinIntg_two_pi
      unfold sinIntg at hfirst ⊢
      have heq : evenPt 1 = 2 * π := by simp [evenPt]
      rw [heq] at hadd htail
      linarith
  · by_cases hxpi : x ≤ π
    · have htail : 0 ≤ ∫ t in x..π, sinc t := by
        apply intervalIntegral.integral_nonneg hxpi
        intro t ht
        exact sinc_nonneg_on_zero_pi (hx0.trans ht.1) ht.2
      have hadd := integral_add_adjacent_intervals (μ := volume)
        (continuous_sinc.intervalIntegrable (0 : ℝ) x)
        (continuous_sinc.intervalIntegrable x π)
      have hpi := sinIntg_pi_lt_two
      unfold sinIntg at hpi ⊢
      linarith
    · have htail := odd_tail_nonpos_of_le_fourteen_pi (le_of_not_ge hxpi) hxEven
      have hadd := integral_add_adjacent_intervals (μ := volume)
        (continuous_sinc.intervalIntegrable (0 : ℝ) π)
        (continuous_sinc.intervalIntegrable π x)
      have hpi := sinIntg_pi_lt_two
      unfold sinIntg at hpi ⊢
      linarith

theorem four_thirds_le_sinIntg_of_two_pi_le {x : ℝ}
    (hx2 : 2 * π ≤ x) (hx14 : x ≤ 14 * π) :
    (4 : ℝ) / 3 ≤ sinIntg x := by
  have hlo : evenPt 1 ≤ x := by simpa [evenPt] using hx2
  have hhi : x ≤ evenPt 7 := by
    dsimp [evenPt]
    convert hx14 using 1 <;> ring
  have htail := even_tail_nonneg_of_le_fourteen_pi hlo hhi
  have hadd := integral_add_adjacent_intervals (μ := volume)
    (continuous_sinc.intervalIntegrable (0 : ℝ) (evenPt 1))
    (continuous_sinc.intervalIntegrable (evenPt 1) x)
  have hfirst := four_thirds_lt_sinIntg_two_pi
  unfold sinIntg at hfirst ⊢
  have heq : evenPt 1 = 2 * π := by simp [evenPt]
  rw [heq] at hadd htail
  linarith

theorem sinIntg_neg (x : ℝ) :
    sinIntg (-x) = -sinIntg x := by
  unfold sinIntg
  have h := intervalIntegral.integral_comp_neg (f := sinc)
    (a := (0 : ℝ)) (b := x)
  simp only [sinc_neg] at h
  calc
    (∫ y in (0 : ℝ)..-x, sinc y) =
        -(∫ y in -x..(0 : ℝ), sinc y) :=
      intervalIntegral.integral_symm (-x) 0
    _ = -(∫ y in (0 : ℝ)..x, sinc y) := by
      simpa using (congrArg Neg.neg h).symm

theorem intg_sc_sinc_eq_sinIntg_sub (n : ℕ) (hn : 0 < n)
    (u v θ : ℝ) :
    (∫ x in u..v,
      2 * (n : ℝ) * sinc (2 * (n : ℝ) * (x - θ))) =
      sinIntg (2 * (n : ℝ) * (v - θ)) -
        sinIntg (2 * (n : ℝ) * (u - θ)) := by
  let c : ℝ := 2 * (n : ℝ)
  have hc : c ≠ 0 := by
    dsimp [c]
    positivity
  have hcomp := intervalIntegral.integral_comp_mul_add sinc hc (-c * θ)
    (a := u) (b := v)
  have hscale : (∫ x in u..v, c * sinc (c * x + -c * θ)) =
      ∫ y in c * u + -c * θ..c * v + -c * θ, sinc y := by
    rw [intervalIntegral.integral_const_mul]
    rw [hcomp]
    simp [hc]
  have hadd := integral_add_adjacent_intervals (μ := volume)
    (continuous_sinc.intervalIntegrable (0 : ℝ) (c * u + -c * θ))
    (continuous_sinc.intervalIntegrable (c * u + -c * θ)
      (c * v + -c * θ))
  unfold sinIntg
  rw [show (∫ x in u..v,
      2 * (n : ℝ) * sinc (2 * (n : ℝ) * (x - θ))) =
      ∫ x in u..v, c * sinc (c * x + -c * θ) by
        congr 1
        funext x
        dsimp [c]
        ring]
  rw [hscale]
  have hu : c * u + -c * θ = c * (u - θ) := by ring
  have hv : c * v + -c * θ = c * (v - θ) := by ring
  rw [hu, hv] at hadd ⊢
  linarith

private lemma four_thirds_le_sinIntg_add_of_add_eq_two_pi
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (huv : u + v = 2 * π) :
    (4 : ℝ) / 3 ≤ sinIntg u +
      sinIntg v := by
  have hbound (z w : ℝ) (hzpi : π ≤ z) (hz2 : z ≤ 2 * π)
      (hw0 : 0 ≤ w) (hw14 : w ≤ 14 * π) :
      (4 : ℝ) / 3 ≤ sinIntg w +
        sinIntg z := by
    have htail : (∫ t in z..2 * π, sinc t) ≤ 0 := by
      apply intg_nonpos_of_nonpos hz2
      intro t ht
      exact sinc_nonpos_odd_half 0 (by simpa [evenPt] using hzpi.trans ht.1)
        (by simpa [evenPt] using ht.2)
    have hadd := integral_add_adjacent_intervals (μ := volume)
      (continuous_sinc.intervalIntegrable (0 : ℝ) z)
      (continuous_sinc.intervalIntegrable z (2 * π))
    have hw := sinIntg_mem_zero_two hw0 hw14
    rcases hw with ⟨hw_nonneg, hw_le⟩
    have hfirst := four_thirds_lt_sinIntg_two_pi
    unfold sinIntg at hfirst hw_nonneg hw_le ⊢
    linarith
  by_cases hupi : u ≤ π
  · have hvpi : π ≤ v := by linarith
    have hv2 : v ≤ 2 * π := by linarith
    have hu14 : u ≤ 14 * π := by nlinarith [pi_pos]
    exact hbound v u hvpi hv2 hu hu14
  · have hvpi : v ≤ π := by linarith
    have hupi' : π ≤ u := le_of_not_ge hupi
    have hu2 : u ≤ 2 * π := by linarith
    have hv14 : v ≤ 14 * π := by nlinarith [pi_pos]
    simpa [add_comm] using hbound u v hupi' hu2 hv hv14

theorem pr_grid_ivl_inside (n : ℕ) (hn : 0 < n)
    (a b : ℤ) (hab : a < b)
    (hshort : (b : ℝ) * π / n - (a : ℝ) * π / n ≤
      6 * π / n)
    {θ : ℝ}
    (hθ : θ ∈ Icc ((a : ℝ) * π / n)
      ((b : ℝ) * π / n)) :
    (∫ x in (a : ℝ) * π / n..(b : ℝ) * π / n,
      2 * (n : ℝ) * sinc (2 * (n : ℝ) * (x - θ))) ∈
      Icc ((4 : ℝ) / 3) 4 := by
  let L : ℝ := (a : ℝ) * π / n
  let U : ℝ := (b : ℝ) * π / n
  let c : ℝ := 2 * (n : ℝ)
  let u : ℝ := c * (θ - L)
  let v : ℝ := c * (U - θ)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < c := by dsimp [c]; positivity
  have hu : 0 ≤ u := mul_nonneg hc.le (sub_nonneg.2 hθ.1)
  have hv : 0 ≤ v := mul_nonneg hc.le (sub_nonneg.2 hθ.2)
  have huv : u + v = c * (U - L) := by
    dsimp [u, v]
    ring
  have htotal : u + v = 2 * ((b - a : ℤ) : ℝ) * π := by
    rw [huv]
    dsimp [c, U, L]
    push_cast
    field_simp
  have hsum12 : u + v ≤ 12 * π := by
    have hm := mul_le_mul_of_nonneg_left hshort hc.le
    calc
      u + v = c * (U - L) := huv
      _ ≤ c * (6 * π / n) := by simpa [U, L] using hm
      _ = 12 * π := by
        dsimp [c]
        field_simp
        norm_num
  have hu14 : u ≤ 14 * π := by
    nlinarith [pi_pos]
  have hv14 : v ≤ 14 * π := by
    nlinarith [pi_pos]
  have huMem := sinIntg_mem_zero_two hu hu14
  have hvMem := sinIntg_mem_zero_two hv hv14
  rcases huMem with ⟨huSi0, huSi2⟩
  rcases hvMem with ⟨hvSi0, hvSi2⟩
  have hlower : (4 : ℝ) / 3 ≤ sinIntg u +
      sinIntg v := by
    by_cases hgap : b - a = 1
    · apply four_thirds_le_sinIntg_add_of_add_eq_two_pi hu hv
      rw [htotal, hgap]
      norm_num
    · have hgap2 : (2 : ℤ) ≤ b - a := by omega
      have htotal4 : 4 * π ≤ u + v := by
        rw [htotal]
        have hcast : (2 : ℝ) ≤ ((b - a : ℤ) : ℝ) := by exact_mod_cast hgap2
        nlinarith [pi_pos]
      by_cases hu2 : 2 * π ≤ u
      · have hmain := four_thirds_le_sinIntg_of_two_pi_le hu2 hu14
        linarith
      · have hv2 : 2 * π ≤ v := by linarith
        have hmain := four_thirds_le_sinIntg_of_two_pi_le hv2 hv14
        linarith
  have hupper : sinIntg u +
      sinIntg v ≤ 4 := by linarith
  have hid := intg_sc_sinc_eq_sinIntg_sub n hn L U θ
  have hL : 2 * (n : ℝ) * (L - θ) = -u := by
    dsimp [c, u]
    ring
  have hU : 2 * (n : ℝ) * (U - θ) = v := by rfl
  dsimp [L, U] at hid ⊢
  rw [hid, hL, hU, sinIntg_neg]
  constructor <;> linarith

theorem pr_grid_ivl_outside_near (n : ℕ) (hn : 0 < n)
    (a b : ℤ) (hab : a < b)
    (hshort : (b : ℝ) * π / n - (a : ℝ) * π / n ≤
      6 * π / n)
    {θ : ℝ}
    (hnear :
      (θ ≤ (a : ℝ) * π / n ∧
        (a : ℝ) * π / n - θ ≤ π / n) ∨
      ((b : ℝ) * π / n ≤ θ ∧
        θ - (b : ℝ) * π / n ≤ π / n)) :
    |∫ x in (a : ℝ) * π / n..(b : ℝ) * π / n,
      2 * (n : ℝ) * sinc (2 * (n : ℝ) * (x - θ))| ≤ 2 := by
  let L : ℝ := (a : ℝ) * π / n
  let U : ℝ := (b : ℝ) * π / n
  let c : ℝ := 2 * (n : ℝ)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < c := by dsimp [c]; positivity
  have hwidth : c * (U - L) ≤ 12 * π := by
    have hm := mul_le_mul_of_nonneg_left hshort hc.le
    dsimp [c, U, L] at hm ⊢
    field_simp at hm ⊢
    nlinarith
  have hUL0 : 0 ≤ U - L := by
    have habR : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
    dsimp [U, L]
    have hmul : (a : ℝ) * π ≤ (b : ℝ) * π :=
      mul_le_mul_of_nonneg_right habR.le pi_pos.le
    exact sub_nonneg.2 (div_le_div_of_nonneg_right hmul hnR.le)
  have hid := intg_sc_sinc_eq_sinIntg_sub n hn L U θ
  rcases hnear with hleft | hright
  · let z : ℝ := c * (L - θ)
    let w : ℝ := c * (U - θ)
    have hz0 : 0 ≤ z := mul_nonneg hc.le (sub_nonneg.2 hleft.1)
    have hzw : w = z + c * (U - L) := by dsimp [z, w]; ring
    have hw0 : 0 ≤ w := by
      rw [hzw]
      exact add_nonneg hz0 (mul_nonneg hc.le hUL0)
    have hz2 : z ≤ 2 * π := by
      have hm := mul_le_mul_of_nonneg_left hleft.2 hc.le
      dsimp [c, z, L] at hm ⊢
      field_simp at hm ⊢
      nlinarith
    have hw14 : w ≤ 14 * π := by rw [hzw]; linarith
    have hzMem := sinIntg_mem_zero_two hz0 (hz2.trans (by nlinarith [pi_pos]))
    have hwMem := sinIntg_mem_zero_two hw0 hw14
    rcases hzMem with ⟨hzSi0, hzSi2⟩
    rcases hwMem with ⟨hwSi0, hwSi2⟩
    have hL : 2 * (n : ℝ) * (L - θ) = z := by rfl
    have hU : 2 * (n : ℝ) * (U - θ) = w := by rfl
    dsimp [L, U] at hid ⊢
    rw [hid, hL, hU]
    rw [abs_le]
    constructor <;> linarith
  · let z : ℝ := c * (θ - U)
    let w : ℝ := c * (θ - L)
    have hz0 : 0 ≤ z := mul_nonneg hc.le (sub_nonneg.2 hright.1)
    have hzw : w = z + c * (U - L) := by dsimp [z, w]; ring
    have hw0 : 0 ≤ w := by
      rw [hzw]
      exact add_nonneg hz0 (mul_nonneg hc.le hUL0)
    have hz2 : z ≤ 2 * π := by
      have hm := mul_le_mul_of_nonneg_left hright.2 hc.le
      dsimp [c, z, U] at hm ⊢
      field_simp at hm ⊢
      nlinarith
    have hw14 : w ≤ 14 * π := by rw [hzw]; linarith
    have hzMem := sinIntg_mem_zero_two hz0 (hz2.trans (by nlinarith [pi_pos]))
    have hwMem := sinIntg_mem_zero_two hw0 hw14
    rcases hzMem with ⟨hzSi0, hzSi2⟩
    rcases hwMem with ⟨hwSi0, hwSi2⟩
    have hL : 2 * (n : ℝ) * (L - θ) = -w := by dsimp [c, w]; ring
    have hU : 2 * (n : ℝ) * (U - θ) = -z := by dsimp [c, z]; ring
    dsimp [L, U] at hid ⊢
    rw [hid, hL, hU, sinIntg_neg z, sinIntg_neg w]
    rw [abs_le]
    constructor <;> linarith

end

end SinIntgGrid

end

section

namespace KernelFarClaim

open scoped BigOperators Interval
open Real Set MeasureTheory intervalIntegral

noncomputable section

open OddSine

def prIntg (n : ℕ) (I : RealIvl) (θ : ℝ) : ℝ :=
  ∫ x in I.1..I.2,
    2 * (n : ℝ) * sinc (2 * (n : ℝ) * (x - θ))

def farBaseIvls {n : ℕ} (F : IvlFam n)
    (θ : ℝ) : Finset ↥F.base :=
  @Finset.filter ↥F.base
    (fun I ↦ ¬Near n θ I.1)
    (Classical.decPred _) Finset.univ

theorem farBaseIvls_eq_sdiff {n : ℕ}
    (F : IvlFam n) (θ : ℝ) :
    farBaseIvls F θ =
      Finset.univ \
        nearBaseIvls F θ := by
  classical
  ext I
  simp [farBaseIvls,
    nearBaseIvls]

private def farIvls {n : ℕ} (F : IvlFam n)
    (θ : ℝ) : Finset RealIvl :=
  @Finset.filter RealIvl
    (fun I ↦ ¬Near n θ I)
    (Classical.decPred _) F.base

private lemma sum_farBaseIvls_eq_sum_farIvls {n : ℕ}
    (F : IvlFam n) (θ : ℝ) (f : RealIvl → ℝ) :
    ∑ I ∈ farBaseIvls F θ, f I.1 =
      ∑ I ∈ farIvls F θ, f I := by
  classical
  apply sum_bij (fun I _ ↦ I.1)
  · intro I hI
    simp only [farBaseIvls, mem_filter, Finset.mem_univ,
      true_and] at hI
    simp [farIvls, I.property, hI]
  · intro I hI J hJ hIJ
    exact Subtype.ext hIJ
  · intro I hI
    simp only [farIvls, mem_filter] at hI
    refine ⟨⟨I, hI.1⟩, ?_, rfl⟩
    simp [farBaseIvls, hI.2]
  · intro I hI
    rfl

private lemma sh_endpt_cos_eq {n : ℕ} (hn : 0 < n)
    {I : RealIvl}
    (hgrid : ∃ a b : ℤ,
      I.1 = (a : ℝ) * π / n ∧ I.2 = (b : ℝ) * π / n)
    (θ : ℝ) :
    cos ((2 * (n : ℝ)) * (I.2 - θ)) =
      cos ((2 * (n : ℝ)) * (I.1 - θ)) := by
  obtain ⟨a, b, ha, hb⟩ := hgrid
  rw [ha, hb]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  calc
    cos ((2 * (n : ℝ)) * ((b : ℝ) * π / n - θ)) =
        cos ((b : ℝ) * (2 * π) - (2 * (n : ℝ)) * θ) := by
          congr 1
          field_simp [hn0]
    _ = cos ((2 * (n : ℝ)) * θ) :=
      cos_int_mul_two_pi_sub _ b
    _ = cos ((a : ℝ) * (2 * π) - (2 * (n : ℝ)) * θ) :=
      (cos_int_mul_two_pi_sub _ a).symm
    _ = cos ((2 * (n : ℝ)) * ((a : ℝ) * π / n - θ)) := by
          congr 1
          field_simp [hn0]

theorem prIntg_eq_reciprocal_sin_of_zero_not_mem
    {n : ℕ} (hn : 0 < n)
    {I : RealIvl} {θ : ℝ}
    (hzero : ∀ u ∈ uIcc (I.1 - θ) (I.2 - θ), u ≠ 0) :
    prIntg n I θ =
      ∫ u in (I.1 - θ)..(I.2 - θ),
        u⁻¹ * sin ((2 * (n : ℝ)) * u) := by
  rw [prIntg]
  rw [integral_comp_sub_right
    (fun u : ℝ ↦ 2 * (n : ℝ) * sinc (2 * (n : ℝ) * u)) θ]
  apply intervalIntegral.integral_congr
  intro u hu
  have hn0 : (2 * (n : ℝ)) ≠ 0 := by positivity
  have hu0 := hzero u hu
  change 2 * (n : ℝ) * sinc (2 * (n : ℝ) * u) =
    u⁻¹ * sin (2 * (n : ℝ) * u)
  rw [sinc_of_ne_zero (mul_ne_zero hn0 hu0)]
  field_simp [hn0, hu0]

theorem abs_prIntg_le_endptVar {n : ℕ} (hn : 0 < n)
    {I : RealIvl} {θ : ℝ} (hord : I.1 ≤ I.2)
    (hgrid : ∃ a b : ℤ,
      I.1 = (a : ℝ) * π / n ∧ I.2 = (b : ℝ) * π / n)
    (hside : I.2 ≤ θ - π / n ∨
      θ + π / n ≤ I.1) :
    |prIntg n I θ| ≤
      ((I.1 - θ)⁻¹ - (I.2 - θ)⁻¹) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpiN : 0 < π / (n : ℝ) := div_pos pi_pos hnR
  have hleftOrRight : I.2 < θ ∨ θ < I.1 := by
    rcases hside with hleft | hright
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hzero : ∀ u ∈ uIcc (I.1 - θ) (I.2 - θ), u ≠ 0 := by
    intro u hu
    rw [uIcc_of_le (sub_le_sub_right hord θ)] at hu
    rcases hleftOrRight with hleft | hright
    · have : u < 0 := lt_of_le_of_lt hu.2 (sub_neg.mpr hleft)
      exact this.ne
    · have : 0 < u := lt_of_lt_of_le (sub_pos.mpr hright) hu.1
      exact this.ne'
  rw [prIntg_eq_reciprocal_sin_of_zero_not_mem hn hzero]
  have hlocal :=
    abs_intg_mul_sin_le_of_deriv_nonpos
      (h := fun u : ℝ ↦ u⁻¹) (h' := fun u : ℝ ↦ -(u ^ 2)⁻¹)
      hn (sub_le_sub_right hord θ)
      (fun u hu ↦ hasDerivAt_inv (hzero u (by
        simpa [uIcc_of_le (sub_le_sub_right hord θ)] using hu)))
      (by
        apply ContinuousOn.neg
        apply ContinuousOn.inv₀ (by fun_prop)
        intro u hu
        exact pow_ne_zero 2 (hzero u (by
          simpa [uIcc_of_le (sub_le_sub_right hord θ)] using hu)))
      (fun u hu ↦ neg_nonpos.mpr (inv_nonneg.mpr (sq_nonneg u)))
      (sh_endpt_cos_eq hn hgrid θ)
  have hanti : (I.2 - θ)⁻¹ ≤ (I.1 - θ)⁻¹ := by
    rcases hleftOrRight with hleft | hright
    · exact inv_antitoneOn_Iio
        (show I.1 - θ ∈ Iio 0 by exact sub_neg.mpr (hord.trans_lt hleft))
        (show I.2 - θ ∈ Iio 0 by exact sub_neg.mpr hleft)
        (sub_le_sub_right hord θ)
    · exact inv_antitoneOn_Ioi
        (show I.1 - θ ∈ Ioi 0 by exact sub_pos.mpr hright)
        (show I.2 - θ ∈ Ioi 0 by exact sub_pos.mpr (hright.trans_le hord))
        (sub_le_sub_right hord θ)
  rw [abs_of_nonpos (sub_nonpos.mpr hanti)] at hlocal
  convert hlocal using 1
  ring

private lemma endpt_var_le_of_mono
    (s : Finset RealIvl) (f : ℝ → ℝ) (L U : ℝ)
    (hord : ∀ I ∈ s, I.1 < I.2)
    (hLU : L ≤ U)
    (hinside : ∀ I ∈ s, L ≤ I.1 ∧ I.2 ≤ U)
    (hsep : Set.Pairwise (↑s : Set RealIvl)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1))
    (hmono : MonotoneOn f (Icc L U)) :
    ∑ I ∈ s, (f I.2 - f I.1) ≤ f U - f L := by
  classical
  let t : Finset (Lex RealIvl) := s.image toLex
  let m := t.card
  let e : Fin m ≃o ↑t := orderIsoOfFin t rfl
  have emem (k : Fin m) : ofLex ((e k : ↑t) : Lex RealIvl) ∈ s := by
    have hk := (e k).property
    change ((e k : ↑t) : Lex RealIvl) ∈ s.image toLex at hk
    rw [Finset.mem_image] at hk
    rcases hk with ⟨I, hI, hEq⟩
    simpa [← hEq] using hI
  let A : ℕ → ℝ := fun k ↦
    if hk : k < m then
      f (ofLex ((e ⟨k, hk⟩ : ↑t) : Lex RealIvl)).1 else f U
  let B : ℕ → ℝ := fun k ↦
    if hk : k < m then
      f (ofLex ((e ⟨k, hk⟩ : ↑t) : Lex RealIvl)).2 else f U
  let E : ℕ → ℝ := fun k ↦ B k - A k
  have hchain : ∀ k < m, B k ≤ A (k + 1) := by
    intro k hk
    simp only [B, A, dif_pos hk]
    by_cases hks : k + 1 < m
    · rw [dif_pos hks]
      apply hmono
      · exact ⟨(hinside _ (emem ⟨k, hk⟩)).1.trans
            (hord _ (emem ⟨k, hk⟩)).le,
          (hinside _ (emem ⟨k, hk⟩)).2⟩
      · exact ⟨(hinside _ (emem ⟨k + 1, hks⟩)).1,
          (hord _ (emem ⟨k + 1, hks⟩)).le.trans
            (hinside _ (emem ⟨k + 1, hks⟩)).2⟩
      have horder : e ⟨k, hk⟩ ≤ e ⟨k + 1, hks⟩ :=
        e.le_iff_le.mpr (by simp)
      have hleft : (ofLex ((e ⟨k, hk⟩ : ↑t) : Lex RealIvl)).1 ≤
          (ofLex ((e ⟨k + 1, hks⟩ : ↑t) : Lex RealIvl)).1 := by
        exact (Prod.Lex.le_iff.mp horder).elim (fun h ↦ h.le) (fun h ↦ h.1.le)
      have hne : ofLex ((e ⟨k, hk⟩ : ↑t) : Lex RealIvl) ≠
          ofLex ((e ⟨k + 1, hks⟩ : ↑t) : Lex RealIvl) := by
        intro heq
        have heq' : e ⟨k, hk⟩ = e ⟨k + 1, hks⟩ := by
          apply Subtype.ext
          exact ofLex.injective heq
        have : (⟨k, hk⟩ : Fin m) = ⟨k + 1, hks⟩ := e.injective heq'
        simp at this
      rcases hsep (emem ⟨k, hk⟩) (emem ⟨k + 1, hks⟩) hne with hgood | hbad
      · exact hgood
      · have hstrict := hord _ (emem ⟨k + 1, hks⟩)
        linarith
    · rw [dif_neg hks]
      exact hmono
        ⟨(hinside _ (emem ⟨k, hk⟩)).1.trans (hord _ (emem ⟨k, hk⟩)).le,
          (hinside _ (emem ⟨k, hk⟩)).2⟩
        ⟨hLU, le_rfl⟩ (hinside _ (emem ⟨k, hk⟩)).2
  have htelescope :=
    sum_ivl_error_le_of_mono_endpts
      (n := 1) (m := m) (A := A) (B := B) (E := E) (by norm_num)
      (fun k hk ↦ by simp [E]) hchain
  have hsum : (∑ I ∈ s, (f I.2 - f I.1)) =
      ∑ k ∈ Finset.range m, E k := by
    calc
      (∑ I ∈ s, (f I.2 - f I.1)) =
          ∑ J ∈ t, (f (ofLex J).2 - f (ofLex J).1) := by
            symm
            simpa [t] using (sum_image (s := s)
              (f := fun J : Lex RealIvl ↦
                f (ofLex J).2 - f (ofLex J).1) toLex.injective.injOn)
      _ = ∑ J : ↑t, (f (ofLex (J.1 : Lex RealIvl)).2 -
          f (ofLex (J.1 : Lex RealIvl)).1) := by
            symm
            exact (sum_subtype (M := ℝ) (s := t) (p := fun J ↦ J ∈ t)
              (by simp) (fun J : Lex RealIvl ↦
                f (ofLex J).2 - f (ofLex J).1)).symm
      _ = ∑ i : Fin m, (f (ofLex ((e i : ↑t) : Lex RealIvl)).2 -
          f (ofLex ((e i : ↑t) : Lex RealIvl)).1) := by
            exact (e.toEquiv.sum_comp (fun J : ↑t ↦
              f (ofLex (J.1 : Lex RealIvl)).2 -
                f (ofLex (J.1 : Lex RealIvl)).1)).symm
      _ = ∑ i : Fin m, E i := by
            apply sum_congr rfl
            intro i _
            simp [E, A, B, i.isLt]
      _ = ∑ k ∈ Finset.range m, E k := Fin.sum_univ_eq_sum_range E m
  rw [hsum]
  by_cases hm : m = 0
  · simpa [hm] using sub_nonneg.mpr
      (hmono ⟨le_rfl, hLU⟩ ⟨hLU, le_rfl⟩ hLU)
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hA0 : A 0 =
        f (ofLex ((e ⟨0, hmpos⟩ : ↑t) : Lex RealIvl)).1 := by
      simp [A, hmpos]
    have hAm : A m = f U := by simp [A]
    rw [hA0, hAm] at htelescope
    simp only [Nat.cast_one, div_one] at htelescope
    exact htelescope.trans (sub_le_sub_left
      (hmono ⟨le_rfl, hLU⟩
        ⟨(hinside _ (emem ⟨0, hmpos⟩)).1,
          (hord _ (emem ⟨0, hmpos⟩)).le.trans
            (hinside _ (emem ⟨0, hmpos⟩)).2⟩
        (hinside _ (emem ⟨0, hmpos⟩)).1) _)

private lemma endpt_var_le_of_anti
    (s : Finset RealIvl) (f : ℝ → ℝ) (L U : ℝ)
    (hord : ∀ I ∈ s, I.1 < I.2)
    (hLU : L ≤ U)
    (hinside : ∀ I ∈ s, L ≤ I.1 ∧ I.2 ≤ U)
    (hsep : Set.Pairwise (↑s : Set RealIvl)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1))
    (hanti : AntitoneOn f (Icc L U)) :
    ∑ I ∈ s, (f I.1 - f I.2) ≤ f L - f U := by
  have h := endpt_var_le_of_mono s (-f) L U hord hLU hinside hsep
    (fun _ hx _ hy hxy ↦ neg_le_neg (hanti hx hy hxy))
  simpa only [Pi.neg_apply, neg_sub_neg] using h

private lemma pairwise_disjoint_base {n : ℕ} (hn : 0 < n)
    (F : IvlFam n) :
    Set.Pairwise (↑F.base : Set RealIvl)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1) := by
  intro I hI J hJ hne
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpiN : 0 < π / (n : ℝ) := div_pos pi_pos hnR
  rcases le_total I.1 J.1 with hle | hle
  · left
    by_contra hnot
    have hJlt : J.1 < I.2 := lt_of_not_ge hnot
    have hsep := F.separated hI hJ hne J.1
      ⟨hle, hJlt.le⟩ J.1 ⟨le_rfl, F.ordered J hJ⟩
    have : π / (n : ℝ) ≤ 0 := by simpa using hsep
    exact (not_le_of_gt hpiN) this
  · right
    by_contra hnot
    have hIlt : I.1 < J.2 := lt_of_not_ge hnot
    have hsep := F.separated hI hJ hne I.1
      ⟨le_rfl, F.ordered I hI⟩ I.1 ⟨hle, hIlt.le⟩
    have : π / (n : ℝ) ≤ 0 := by simpa using hsep
    exact (not_le_of_gt hpiN) this

private def leftFarIvls {n : ℕ} (F : IvlFam n)
    (θ : ℝ) : Finset RealIvl :=
  @Finset.filter RealIvl (fun I ↦ I.2 ≤ θ)
    (Classical.decPred _) (farIvls F θ)

private def rightFarIvls {n : ℕ} (F : IvlFam n)
    (θ : ℝ) : Finset RealIvl :=
  @Finset.filter RealIvl (fun I ↦ ¬I.2 ≤ θ)
    (Classical.decPred _) (farIvls F θ)

private lemma leftFar_up {n : ℕ} (_hn : 0 < n)
    (F : IvlFam n) {θ : ℝ} {I : RealIvl}
    (hI : I ∈ leftFarIvls F θ) :
    I.2 ≤ θ - π / n := by
  simp only [leftFarIvls, farIvls, mem_filter] at hI
  have hgap : π / (n : ℝ) ≤
      ivlGap θ I := by
    exact le_of_not_gt hI.1.2
  rw [ivlGap_eq_right
    (F.ordered I hI.1.1) hI.2] at hgap
  linarith

private lemma rightFar_lo {n : ℕ} (hn : 0 < n)
    (F : IvlFam n) {θ : ℝ} {I : RealIvl}
    (hI : I ∈ rightFarIvls F θ) :
    θ + π / n ≤ I.1 := by
  simp only [rightFarIvls, farIvls, mem_filter] at hI
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpiN : 0 < π / (n : ℝ) := div_pos pi_pos hnR
  have hright : θ ≤ I.1 := by
    by_contra hnot
    have hleft : I.1 < θ := lt_of_not_ge hnot
    have hright : θ < I.2 := lt_of_not_ge hI.2
    apply hI.1.2
    rw [Near,
      ivlGap_eq_zero_of_mem]
    · exact hpiN
    · exact ⟨hleft.le, hright.le⟩
  have hgap : π / (n : ℝ) ≤
      ivlGap θ I := by
    exact le_of_not_gt hI.1.2
  rw [ivlGap_eq_left
    (F.ordered I hI.1.1) hright] at hgap
  linarith

private lemma side_pairwise_disjoint {n : ℕ} (hn : 0 < n)
    (F : IvlFam n) (s : Finset RealIvl)
    (hs : s ⊆ F.base) :
    Set.Pairwise (↑s : Set RealIvl)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1) := by
  intro I hI J hJ hne
  exact pairwise_disjoint_base hn F (hs hI) (hs hJ) hne

private lemma sum_left_endptVar_le {n : ℕ} (hn : 0 < n)
    (F : IvlFam n) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (π / 2)) :
    ∑ I ∈ leftFarIvls F θ,
        ((I.1 - θ)⁻¹ - (I.2 - θ)⁻¹) ≤
      (n : ℝ) / π := by
  classical
  let s := leftFarIvls F θ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hpiN : 0 < π / (n : ℝ) := div_pos pi_pos hnR
  by_cases hs : s.Nonempty
  · obtain ⟨I, hI⟩ := hs
    have hbase : ∀ J ∈ s, J ∈ F.base := by
      intro J hJ
      have hJ' : (J ∈ F.base ∧
          ¬Near n θ J) ∧ J.2 ≤ θ := by
        simpa only [s, leftFarIvls, farIvls,
          mem_filter] using hJ
      exact hJ'.1.1
    have hinside : ∀ J ∈ s,
        (0 : ℝ) ≤ J.1 ∧ J.2 ≤ θ - π / n := by
      intro J hJ
      exact ⟨(F.in_first_quadrant J (hbase J hJ)).1,
        leftFar_up hn F (by simpa [s] using hJ)⟩
    have hLU : (0 : ℝ) ≤ θ - π / n :=
      (hinside I hI).1.trans
        ((F.ordered I (hbase I hI)).trans (hinside I hI).2)
    have htel := endpt_var_le_of_anti s
      (fun x : ℝ ↦ (x - θ)⁻¹) 0 (θ - π / n)
      (fun J hJ ↦ F.nondegenerate J (hbase J hJ)) hLU hinside
      (side_pairwise_disjoint hn F s hbase)
      (sub_inv_antitoneOn_Icc_left (by linarith))
    have hzeroEndpoint : (0 - θ)⁻¹ ≤ 0 :=
      inv_nonpos.mpr (sub_nonpos.mpr hθ.1)
    have hfarEndpoint :
        (θ - π / (n : ℝ) - θ)⁻¹ =
          -(n : ℝ) / π := by
      field_simp [hn0, pi_ne_zero]
      ring
    rw [hfarEndpoint] at htel
    dsimp [s] at htel
    calc
      ∑ I ∈ leftFarIvls F θ,
          ((I.1 - θ)⁻¹ - (I.2 - θ)⁻¹) ≤
          (0 - θ)⁻¹ - (-(n : ℝ) / π) := htel
      _ ≤ 0 - (-(n : ℝ) / π) :=
        sub_le_sub_right hzeroEndpoint _
      _ = (n : ℝ) / π := by ring
  · have hs0 : leftFarIvls F θ = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      simpa [s] using hs
    rw [hs0]
    simp
    positivity

private lemma sum_right_endptVar_le {n : ℕ} (hn : 0 < n)
    (F : IvlFam n) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (π / 2)) :
    ∑ I ∈ rightFarIvls F θ,
        ((I.1 - θ)⁻¹ - (I.2 - θ)⁻¹) ≤
      (n : ℝ) / π := by
  classical
  let s := rightFarIvls F θ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hpiN : 0 < π / (n : ℝ) := div_pos pi_pos hnR
  by_cases hs : s.Nonempty
  · obtain ⟨I, hI⟩ := hs
    have hbase : ∀ J ∈ s, J ∈ F.base := by
      intro J hJ
      have hJ' : (J ∈ F.base ∧
          ¬Near n θ J) ∧ ¬J.2 ≤ θ := by
        simpa only [s, rightFarIvls, farIvls,
          mem_filter] using hJ
      exact hJ'.1.1
    have hinside : ∀ J ∈ s,
        θ + π / n ≤ J.1 ∧ J.2 ≤ π / 2 := by
      intro J hJ
      exact ⟨rightFar_lo hn F (by simpa [s] using hJ),
        (F.in_first_quadrant J (hbase J hJ)).2⟩
    have hLU : θ + π / n ≤ π / 2 :=
      (hinside I hI).1.trans
        ((F.ordered I (hbase I hI)).trans (hinside I hI).2)
    have htel := endpt_var_le_of_anti s
      (fun x : ℝ ↦ (x - θ)⁻¹)
      (θ + π / n) (π / 2)
      (fun J hJ ↦ F.nondegenerate J (hbase J hJ)) hLU hinside
      (side_pairwise_disjoint hn F s hbase)
      (sub_inv_antitoneOn_Icc_right (by linarith))
    have hlastEndpoint : 0 ≤ (π / 2 - θ)⁻¹ :=
      inv_nonneg.mpr (sub_nonneg.mpr hθ.2)
    have hnearEndpoint :
        (θ + π / (n : ℝ) - θ)⁻¹ =
          (n : ℝ) / π := by
      field_simp [hn0, pi_ne_zero]
      ring
    rw [hnearEndpoint] at htel
    dsimp [s] at htel
    calc
      ∑ I ∈ rightFarIvls F θ,
          ((I.1 - θ)⁻¹ - (I.2 - θ)⁻¹) ≤
          (n : ℝ) / π - (π / 2 - θ)⁻¹ := htel
      _ ≤ (n : ℝ) / π - 0 :=
        sub_le_sub_left hlastEndpoint _
      _ = (n : ℝ) / π := by ring
  · have hs0 : rightFarIvls F θ = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      simpa [s] using hs
    rw [hs0]
    simp
    positivity

private lemma sum_left_abs_prIntg_le {n : ℕ} (hn : 0 < n)
    (F : IvlFam n) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (π / 2)) :
    ∑ I ∈ leftFarIvls F θ, |prIntg n I θ| ≤
      1 / π := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  calc
    ∑ I ∈ leftFarIvls F θ, |prIntg n I θ| ≤
        ∑ I ∈ leftFarIvls F θ,
          (((I.1 - θ)⁻¹ - (I.2 - θ)⁻¹) / n) := by
      apply sum_le_sum
      intro I hI
      have hI' : (I ∈ F.base ∧
          ¬Near n θ I) ∧ I.2 ≤ θ := by
        simpa only [leftFarIvls, farIvls,
          mem_filter] using hI
      exact abs_prIntg_le_endptVar hn
        (F.ordered I hI'.1.1) (F.grid_endpoints I hI'.1.1)
        (Or.inl (leftFar_up hn F hI))
    _ = (∑ I ∈ leftFarIvls F θ,
          ((I.1 - θ)⁻¹ - (I.2 - θ)⁻¹)) / n := by
      rw [sum_div]
    _ ≤ ((n : ℝ) / π) / n :=
      div_le_div_of_nonneg_right
        (sum_left_endptVar_le hn F hθ) hnR.le
    _ = 1 / π := by
      field_simp [hn0, pi_ne_zero]

private lemma sum_right_abs_prIntg_le {n : ℕ} (hn : 0 < n)
    (F : IvlFam n) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (π / 2)) :
    ∑ I ∈ rightFarIvls F θ, |prIntg n I θ| ≤
      1 / π := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  calc
    ∑ I ∈ rightFarIvls F θ, |prIntg n I θ| ≤
        ∑ I ∈ rightFarIvls F θ,
          (((I.1 - θ)⁻¹ - (I.2 - θ)⁻¹) / n) := by
      apply sum_le_sum
      intro I hI
      have hI' : (I ∈ F.base ∧
          ¬Near n θ I) ∧ ¬I.2 ≤ θ := by
        simpa only [rightFarIvls, farIvls,
          mem_filter] using hI
      exact abs_prIntg_le_endptVar hn
        (F.ordered I hI'.1.1) (F.grid_endpoints I hI'.1.1)
        (Or.inr (rightFar_lo hn F hI))
    _ = (∑ I ∈ rightFarIvls F θ,
          ((I.1 - θ)⁻¹ - (I.2 - θ)⁻¹)) / n := by
      rw [sum_div]
    _ ≤ ((n : ℝ) / π) / n :=
      div_le_div_of_nonneg_right
        (sum_right_endptVar_le hn F hθ) hnR.le
    _ = 1 / π := by
      field_simp [hn0, pi_ne_zero]

theorem sum_abs_prIntg_far_le_two_div_pi {n : ℕ}
    (hn : 0 < n) (F : IvlFam n) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (π / 2)) :
    ∑ I ∈ farBaseIvls F θ,
        |prIntg n I.1 θ| ≤ 2 / π := by
  classical
  rw [sum_farBaseIvls_eq_sum_farIvls F θ
    (fun I ↦ |prIntg n I θ|)]
  have hsplit :
      (∑ I ∈ farIvls F θ, |prIntg n I θ|) =
        (∑ I ∈ leftFarIvls F θ,
          |prIntg n I θ|) +
        ∑ I ∈ rightFarIvls F θ,
          |prIntg n I θ| := by
    rw [leftFarIvls, rightFarIvls,
      Finset.sum_filter_add_sum_filter_not]
  rw [hsplit]
  calc
    (∑ I ∈ leftFarIvls F θ, |prIntg n I θ|) +
        ∑ I ∈ rightFarIvls F θ,
          |prIntg n I θ| ≤
        1 / π + 1 / π :=
      add_le_add (sum_left_abs_prIntg_le hn F hθ)
        (sum_right_abs_prIntg_le hn F hθ)
    _ = 2 / π := by ring

end

end KernelFarClaim

end

open KernelFarClaim


section

namespace KernelMonotonicity

open Real Set

noncomputable section

def amp : ℝ → ℝ :=
  dslope (fun u : ℝ ↦ (sinc u)⁻¹) 0

@[simp] theorem amp_zero : amp 0 = 0 := by
  rw [amp, dslope_same]
  have hsinc : AnalyticAt ℝ sinc 0 := by
    rw [sinc_eq_dslope]
    exact analyticAt_sin.hasFPowerSeriesAt.has_fpower_series_dslope_fslope.analyticAt
  have hinv : DifferentiableAt ℝ (fun u : ℝ ↦ (sinc u)⁻¹) 0 :=
    (hsinc.inv (by simp)).differentiableAt
  let d := deriv (fun u : ℝ ↦ (sinc u)⁻¹) 0
  have hd : HasDerivAt (fun u : ℝ ↦ (sinc u)⁻¹) d 0 := hinv.hasDerivAt
  have hdneg : HasDerivAt (fun u : ℝ ↦ (sinc (-u))⁻¹) (-d) 0 := by
    have hcomp := HasDerivAt.comp_of_eq (x := (0 : ℝ)) hd
      (hasDerivAt_neg 0) (by simp)
    simpa [d, Function.comp_def] using hcomp
  have hdneg' : HasDerivAt (fun u : ℝ ↦ (sinc u)⁻¹) (-d) 0 := by
    simpa only [sinc_neg] using hdneg
  have := hd.unique hdneg'
  dsimp [d] at this ⊢
  linarith

theorem amp_eq {u : ℝ} (hu : u ≠ 0)
    (hsu : sin u ≠ 0) :
    amp u = 1 / sin u - 1 / u := by
  have hmul : u * amp u = (sinc u)⁻¹ - 1 := by
    simpa [amp] using
      (sub_smul_dslope (fun x : ℝ ↦ (sinc x)⁻¹) 0 u)
  apply (mul_left_cancel₀ hu)
  rw [hmul, sinc_of_ne_zero hu]
  field_simp [hu, hsu]

private lemma analyticAt_sinc_zero : AnalyticAt ℝ sinc 0 := by
  rw [sinc_eq_dslope]
  exact analyticAt_sin.hasFPowerSeriesAt.has_fpower_series_dslope_fslope.analyticAt

theorem analyticAt_amp_zero :
    AnalyticAt ℝ amp 0 := by
  have hinv : AnalyticAt ℝ (fun u : ℝ ↦ (sinc u)⁻¹) 0 :=
    analyticAt_sinc_zero.inv (by simp)
  exact hinv.hasFPowerSeriesAt.has_fpower_series_dslope_fslope.analyticAt

theorem sin_ne_zero_of_mem_half {u : ℝ}
    (hu : u ∈ Icc (-(π / 2)) (π / 2))
    (hu0 : u ≠ 0) : sin u ≠ 0 := by
  intro hsu
  apply hu0
  exact (sin_eq_zero_iff_of_lt_of_lt
    (by linarith [hu.1, pi_pos])
    (by linarith [hu.2, pi_pos])).mp hsu

theorem analyticAt_amp {u : ℝ}
    (hu : u ∈ Icc (-(π / 2)) (π / 2)) :
    AnalyticAt ℝ amp u := by
  by_cases hu0 : u = 0
  · simpa [hu0] using analyticAt_amp_zero
  have hsu := sin_ne_zero_of_mem_half hu hu0
  have hrhs : AnalyticAt ℝ (fun x : ℝ ↦ 1 / sin x - 1 / x) u := by
    fun_prop
  apply hrhs.congr
  filter_upwards [eventually_ne_nhds hu0,
      (continuous_sin.tendsto u) (isOpen_ne.mem_nhds hsu)] with x hx0 hsx
  exact (amp_eq hx0 hsx).symm

theorem differentiableAt_amp {u : ℝ}
    (hu : u ∈ Icc (-(π / 2)) (π / 2)) :
    DifferentiableAt ℝ amp u :=
  (analyticAt_amp hu).differentiableAt

theorem hasDerivAt_amp {u : ℝ}
    (hu : u ∈ Icc (-(π / 2)) (π / 2)) :
    HasDerivAt amp (deriv amp u) u :=
  (differentiableAt_amp hu).hasDerivAt

theorem amp_mul_self_nonneg {u : ℝ}
    (hu : u ∈ Icc (-(π / 2)) (π / 2)) :
    0 ≤ amp u * u := by
  rcases lt_trichotomy u 0 with hu0 | rfl | hu0
  · have hsu : sin u < 0 := by
      rw [← neg_pos, ← sin_neg]
      exact sin_pos_of_pos_of_lt_pi (neg_pos.mpr hu0)
        (by linarith [hu.1, pi_pos])
    rw [amp_eq hu0.ne (ne_of_lt hsu)]
    have hsle : u ≤ sin u := by
      have := sin_le (show 0 ≤ -u by linarith)
      rw [sin_neg] at this
      linarith
    rw [show (1 / sin u - 1 / u) * u =
        (u - sin u) / sin u by
      field_simp [hu0.ne, ne_of_lt hsu]
      ]
    exact div_nonneg_of_nonpos (sub_nonpos.mpr hsle) hsu.le
  · simp
  · have hsu : 0 < sin u :=
      sin_pos_of_pos_of_lt_pi hu0 (by linarith [hu.2, pi_pos])
    rw [amp_eq hu0.ne' (ne_of_gt hsu)]
    have hsle := sin_le hu0.le
    rw [show (1 / sin u - 1 / u) * u =
        (u - sin u) / sin u by
      field_simp [hu0.ne', ne_of_gt hsu]
      ]
    exact div_nonneg (sub_nonneg.mpr hsle) hsu.le

theorem deriv_amp_nonneg {u : ℝ}
    (hu : u ∈ Icc (-(π / 2)) (π / 2)) :
    0 ≤ deriv amp u := by
  by_cases hu0 : u = 0
  · subst u
    have hd := analyticAt_amp_zero.differentiableAt.hasDerivAt
    rw [hasDerivAt_iff_tendsto_slope] at hd
    apply ge_of_tendsto hd
    have hIcc : Icc (-(π / 2)) (π / 2) ∈ nhds (0 : ℝ) :=
      Icc_mem_nhds (by linarith [pi_pos]) (by linarith [pi_pos])
    have hIcc' : Icc (-(π / 2)) (π / 2) ∈
        nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ :=
      mem_nhdsWithin_of_mem_nhds hIcc
    filter_upwards [self_mem_nhdsWithin, hIcc'] with x hx hxmem
    have hx0 : x ≠ 0 := by simpa using hx
    simp only [slope, amp_zero, sub_zero, vsub_eq_sub,
      smul_eq_mul]
    rw [show x⁻¹ * amp x =
        (amp x * x) / x ^ 2 by
      field_simp [hx0]
      ]
    exact div_nonneg (amp_mul_self_nonneg hxmem) (sq_nonneg x)
  · have hsu := sin_ne_zero_of_mem_half hu hu0
    have heq : amp =ᶠ[nhds u]
        (fun x : ℝ ↦ 1 / sin x - 1 / x) := by
      filter_upwards [eventually_ne_nhds hu0,
        (continuous_sin.tendsto u) (isOpen_ne.mem_nhds hsu)] with x hx0 hsx
      exact amp_eq hx0 hsx
    have hbase := ((hasDerivAt_sin u).inv hsu).sub
      ((hasDerivAt_id u).inv hu0)
    have hbase' : HasDerivAt (fun x : ℝ ↦ 1 / sin x - 1 / x)
        (1 / u ^ 2 - cos u / sin u ^ 2) u := by
      have hfun : (fun x : ℝ ↦ 1 / sin x - 1 / x) =
          sin⁻¹ - id⁻¹ := by
        funext x
        simp only [one_div, Pi.sub_apply, Pi.inv_apply, id_eq]
      have hcoef : 1 / u ^ 2 - cos u / sin u ^ 2 =
          -cos u / sin u ^ 2 - -1 / id u ^ 2 := by
        simp only [id_eq]
        ring
      rw [hfun, hcoef]
      exact hbase
    have hderiv : HasDerivAt amp
        (1 / u ^ 2 - cos u / sin u ^ 2) u := by
      exact heq.hasDerivAt_iff.mpr hbase'
    rw [hderiv.deriv]
    have habs : |u| ≤ π / 2 := (abs_le).2 hu
    have hcos0 : 0 ≤ cos u := cos_nonneg_of_mem_Icc hu
    have hsin_sq : u ^ 2 * cos u ≤ sin u ^ 2 := by
      have ht0 : 0 ≤ |u| := abs_nonneg u
      have ht2 : |u| < 2 := by
        exact lt_of_le_of_lt habs (by linarith [pi_lt_four])
      have htsq : |u| ^ 2 < (2 : ℝ) ^ 2 :=
        (sq_lt_sq₀ ht0 (by norm_num)).2 ht2
      have hsmall : |u| ^ 2 ≤ 12 := by norm_num at htsq ⊢; linarith
      have hslo := sin_ge_sub_cube (abs_nonneg u)
      have hcosup := cos_le_taylor_four (abs_nonneg u)
      rw [Real.cos_abs] at hcosup
      have hbase : 0 ≤ |u| - |u| ^ 3 / 6 := by
        rw [show |u| - |u| ^ 3 / 6 = |u| * (1 - |u| ^ 2 / 6) by ring]
        exact mul_nonneg ht0 (by nlinarith [htsq])
      have habspi : |u| ≤ π := by linarith [habs, pi_pos]
      have hsine0 : 0 ≤ sin |u| :=
        sin_nonneg_of_nonneg_of_le_pi ht0 habspi
      have hsloSq : (|u| - |u| ^ 3 / 6) ^ 2 ≤ sin |u| ^ 2 :=
        (sq_le_sq₀ hbase hsine0).2 hslo
      have habssin := Real.abs_sin_eq_sin_abs_of_abs_le_pi habspi
      have hsinSqEq : sin |u| ^ 2 = sin u ^ 2 := by
        rw [← habssin, sq_abs]
      have hcosmult : |u| ^ 2 * cos u ≤
          |u| ^ 2 * (1 - |u| ^ 2 / 2 + |u| ^ 4 / 24) :=
        mul_le_mul_of_nonneg_left hcosup (sq_nonneg |u|)
      have hprod : 0 ≤ |u| ^ 4 * (12 - |u| ^ 2) :=
        mul_nonneg (pow_nonneg ht0 4) (sub_nonneg.mpr hsmall)
      have hpoly : |u| ^ 2 * (1 - |u| ^ 2 / 2 + |u| ^ 4 / 24) ≤
          (|u| - |u| ^ 3 / 6) ^ 2 := by
        nlinarith
      rw [← sq_abs u, ← hsinSqEq]
      exact hcosmult.trans (hpoly.trans hsloSq)
    have hden : 0 < u ^ 2 * sin u ^ 2 :=
      mul_pos (sq_pos_of_ne_zero hu0) (sq_pos_of_ne_zero hsu)
    rw [show 1 / u ^ 2 - cos u / sin u ^ 2 =
        (sin u ^ 2 - u ^ 2 * cos u) /
          (u ^ 2 * sin u ^ 2) by
      field_simp [hu0, hsu]
      ]
    exact div_nonneg (sub_nonneg.mpr hsin_sq) hden.le

theorem amp_deriv_data :
    (∀ u ∈ Icc (-(π / 2)) (π / 2),
      HasDerivAt amp (deriv amp u) u) ∧
    ContinuousOn (deriv amp)
      (Icc (-(π / 2)) (π / 2)) ∧
    (∀ u ∈ Icc (-(π / 2)) (π / 2),
      0 ≤ deriv amp u) := by
  refine ⟨fun u hu ↦ hasDerivAt_amp hu, ?_,
    fun u hu ↦ deriv_amp_nonneg hu⟩
  intro u hu
  exact (analyticAt_amp hu).deriv.continuousAt.continuousWithinAt

theorem monoOn_amp :
    MonotoneOn amp
      (Icc (-(π / 2)) (π / 2)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · exact fun u hu ↦
      (analyticAt_amp hu).continuousAt.continuousWithinAt
  · exact fun u hu ↦
      (differentiableAt_amp (interior_subset hu)).differentiableWithinAt
  · intro u hu
    exact deriv_amp_nonneg (interior_subset hu)

@[simp] theorem amp_pi_div_two :
    amp (π / 2) = 1 - 2 / π := by
  rw [amp_eq (by positivity) (by simp), sin_pi_div_two]
  field_simp [pi_ne_zero]

@[simp] theorem amp_neg_pi_div_two :
    amp (-(π / 2)) = -(1 - 2 / π) := by
  rw [amp_eq
      (neg_ne_zero.mpr (div_ne_zero pi_ne_zero (by norm_num))) (by simp), sin_neg,
    sin_pi_div_two]
  field_simp [pi_ne_zero]
  ring

theorem amp_endpt_var :
    amp (π / 2) -
      amp (-(π / 2)) = 2 - 4 / π := by
  rw [amp_pi_div_two, amp_neg_pi_div_two]
  ring

end

end KernelMonotonicity

end

open KernelMonotonicity


section

namespace KernelReflClaim

open scoped BigOperators Interval
open Real Set MeasureTheory intervalIntegral

noncomputable section

open OddSine

def reflIntg (n : ℕ) (I : RealIvl) (θ : ℝ) : ℝ :=
  ∫ x in I.1..I.2,
    sin (((2 * n : ℕ) : ℝ) * (x + θ)) / sin (x + θ)

private def eta (n : ℕ) : ℝ := 100 * π / n

private def amp (θ x : ℝ) : ℝ := (sin (x + θ))⁻¹

private def turnPt (θ : ℝ) : ℝ := π / 2 - θ

private noncomputable def leftIvls {n : ℕ}
    (F : IvlFam n) (θ : ℝ) : Finset RealIvl :=
  F.base.filter fun I ↦ I.2 ≤ turnPt θ

private noncomputable def rightIvls {n : ℕ}
    (F : IvlFam n) (θ : ℝ) : Finset RealIvl :=
  F.base.filter fun I ↦ turnPt θ ≤ I.1

private noncomputable def crossingIvls {n : ℕ}
    (F : IvlFam n) (θ : ℝ) : Finset RealIvl :=
  F.base.filter fun I ↦ I.1 < turnPt θ ∧ turnPt θ < I.2

private lemma eta_pos {n : ℕ} (hn : 0 < n) : 0 < eta n :=
  div_pos (mul_pos (by norm_num) pi_pos) (by exact_mod_cast hn)

private lemma eta_le_pi_div_two {n : ℕ} (hn : 4096 ≤ n) :
    eta n ≤ π / 2 := by
  have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hnR
  dsimp [eta]
  apply (div_le_iff₀ hnpos).2
  nlinarith [pi_pos]

private lemma sh_mem_band {n : ℕ} (F : IvlFam n)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (π / 2))
    {I : RealIvl} (hI : I ∈ F.base) {x : ℝ}
    (hx : x ∈ Icc I.1 I.2) :
    eta n ≤ x + θ ∧ x + θ ≤ π - eta n := by
  have haway := F.away_from_axes I hI
  constructor
  · exact (show eta n ≤ I.1 from haway.1) |>.trans hx.1 |>.trans
      (le_add_of_nonneg_right hθ.1)
  · exact (add_le_add hx.2 hθ.2).trans
      (show I.2 + π / 2 ≤ π - eta n by
        dsimp [eta]
        linarith [haway.2])

private lemma sin_sh_pos {n : ℕ} (hn : 0 < n)
    (F : IvlFam n) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (π / 2))
    {I : RealIvl} (hI : I ∈ F.base) {x : ℝ}
    (hx : x ∈ Icc I.1 I.2) : 0 < sin (x + θ) := by
  have hband := sh_mem_band F hθ hI hx
  have heta := eta_pos hn
  exact sin_pos_of_pos_of_lt_pi (heta.trans_le hband.1)
    (by linarith [hband.2, heta])

private lemma sin_pos_of_mem_sh_ivl {n : ℕ} (hn : 0 < n)
    (F : IvlFam n) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (π / 2))
    {I : RealIvl} (hI : I ∈ F.base) {u : ℝ}
    (hu : u ∈ Icc (I.1 + θ) (I.2 + θ)) :
    0 < sin u := by
  have hx : u - θ ∈ Icc I.1 I.2 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  simpa only [sub_add_cancel] using
    sin_sh_pos hn F hθ hI hx

private lemma endptSep {n : ℕ} (hn : 0 < n)
    (F : IvlFam n) :
    Set.Pairwise (↑F.base : Set RealIvl)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1) := by
  intro I hI J hJ hne
  have hgrid : 0 < π / (n : ℝ) := by
    exact div_pos pi_pos (by exact_mod_cast hn)
  by_cases hfirst : I.1 ≤ J.1
  · left
    by_contra hnot
    have hJinI : J.1 ∈ Icc I.1 I.2 := ⟨hfirst, (lt_of_not_ge hnot).le⟩
    have hsep := F.separated hI hJ hne J.1 hJinI J.1
      ⟨le_rfl, F.ordered J hJ⟩
    have : π / (n : ℝ) ≤ 0 := by simpa using hsep
    exact (not_le_of_gt hgrid) this
  · right
    have hsecond : J.1 ≤ I.1 := (lt_of_not_ge hfirst).le
    by_contra hnot
    have hIinJ : I.1 ∈ Icc J.1 J.2 := ⟨hsecond, (lt_of_not_ge hnot).le⟩
    have hsep := F.separated hI hJ hne I.1
      ⟨le_rfl, F.ordered I hI⟩ I.1 hIinJ
    have : π / (n : ℝ) ≤ 0 := by simpa using hsep
    exact (not_le_of_gt hgrid) this

private abbrev Ivl := ℝ × ℝ

private lemma endpt_var_le_of_mono
    (s : Finset Ivl) (f : ℝ → ℝ) (L U : ℝ)
    (hord : ∀ I ∈ s, I.1 < I.2)
    (hLU : L ≤ U)
    (hinside : ∀ I ∈ s, L ≤ I.1 ∧ I.2 ≤ U)
    (hsep : Set.Pairwise (↑s : Set Ivl)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1))
    (hmono : MonotoneOn f (Icc L U)) :
    ∑ I ∈ s, (f I.2 - f I.1) ≤ f U - f L := by
  classical
  let t : Finset (Lex Ivl) := s.image toLex
  let m := t.card
  let e : Fin m ≃o ↥t := orderIsoOfFin t rfl
  have emem (k : Fin m) : ofLex ((e k : ↥t) : Lex Ivl) ∈ s := by
    have hk := (e k).property
    change ((e k : ↥t) : Lex Ivl) ∈ s.image toLex at hk
    rw [Finset.mem_image] at hk
    rcases hk with ⟨I, hI, hEq⟩
    simpa [← hEq] using hI
  let A : ℕ → ℝ := fun k ↦
    if hk : k < m then f (ofLex ((e ⟨k, hk⟩ : ↥t) : Lex Ivl)).1 else f U
  let B : ℕ → ℝ := fun k ↦
    if hk : k < m then f (ofLex ((e ⟨k, hk⟩ : ↥t) : Lex Ivl)).2 else f U
  let E : ℕ → ℝ := fun k ↦ B k - A k
  have hchain : ∀ k < m, B k ≤ A (k + 1) := by
    intro k hk
    simp only [B, A, dif_pos hk]
    by_cases hks : k + 1 < m
    · rw [dif_pos hks]
      apply hmono
      · exact ⟨(hinside _ (emem ⟨k, hk⟩)).1.trans
            (hord _ (emem ⟨k, hk⟩)).le,
          (hinside _ (emem ⟨k, hk⟩)).2⟩
      · exact ⟨(hinside _ (emem ⟨k + 1, hks⟩)).1,
          (hord _ (emem ⟨k + 1, hks⟩)).le.trans
            (hinside _ (emem ⟨k + 1, hks⟩)).2⟩
      have horder : e ⟨k, hk⟩ ≤ e ⟨k + 1, hks⟩ :=
        e.le_iff_le.mpr (by simp)
      have hleft : (ofLex ((e ⟨k, hk⟩ : ↥t) : Lex Ivl)).1 ≤
          (ofLex ((e ⟨k + 1, hks⟩ : ↥t) : Lex Ivl)).1 := by
        exact (Prod.Lex.le_iff.mp horder).elim (fun h ↦ h.le) (fun h ↦ h.1.le)
      have hne : ofLex ((e ⟨k, hk⟩ : ↥t) : Lex Ivl) ≠
          ofLex ((e ⟨k + 1, hks⟩ : ↥t) : Lex Ivl) := by
        intro heq
        have heq' : e ⟨k, hk⟩ = e ⟨k + 1, hks⟩ := by
          apply Subtype.ext
          exact ofLex.injective heq
        have : (⟨k, hk⟩ : Fin m) = ⟨k + 1, hks⟩ := e.injective heq'
        simp at this
      rcases hsep (emem ⟨k, hk⟩) (emem ⟨k + 1, hks⟩) hne with hgood | hbad
      · exact hgood
      · have hstrict := hord _ (emem ⟨k + 1, hks⟩)
        linarith
    · rw [dif_neg hks]
      exact hmono
        ⟨(hinside _ (emem ⟨k, hk⟩)).1.trans (hord _ (emem ⟨k, hk⟩)).le,
          (hinside _ (emem ⟨k, hk⟩)).2⟩
        ⟨hLU, le_rfl⟩ (hinside _ (emem ⟨k, hk⟩)).2
  have htelescope :=
    sum_ivl_error_le_of_mono_endpts
      (n := 1) (m := m) (A := A) (B := B) (E := E) (by norm_num)
      (fun k hk ↦ by simp [E]) hchain
  have hsum : (∑ I ∈ s, (f I.2 - f I.1)) =
      ∑ k ∈ Finset.range m, E k := by
    calc
      (∑ I ∈ s, (f I.2 - f I.1)) =
          ∑ J ∈ t, (f (ofLex J).2 - f (ofLex J).1) := by
            symm
            simpa [t] using (sum_image (s := s)
              (f := fun J : Lex Ivl ↦ f (ofLex J).2 - f (ofLex J).1)
              toLex.injective.injOn)
      _ = ∑ J : ↥t, (f (ofLex (J.1 : Lex Ivl)).2 -
          f (ofLex (J.1 : Lex Ivl)).1) := by
            symm
            exact (sum_subtype (M := ℝ) (s := t) (p := fun J ↦ J ∈ t)
              (by simp) (fun J : Lex Ivl ↦
                f (ofLex J).2 - f (ofLex J).1)).symm
      _ = ∑ i : Fin m, (f (ofLex ((e i : ↥t) : Lex Ivl)).2 -
          f (ofLex ((e i : ↥t) : Lex Ivl)).1) := by
            exact (e.toEquiv.sum_comp (fun J : ↥t ↦
              f (ofLex (J.1 : Lex Ivl)).2 -
                f (ofLex (J.1 : Lex Ivl)).1)).symm
      _ = ∑ i : Fin m, E i := by
            apply sum_congr rfl
            intro i _
            simp [E, A, B, i.isLt]
      _ = ∑ k ∈ Finset.range m, E k := Fin.sum_univ_eq_sum_range E m
  rw [hsum]
  by_cases hm : m = 0
  · simpa [hm] using sub_nonneg.mpr (hmono ⟨le_rfl, hLU⟩ ⟨hLU, le_rfl⟩ hLU)
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hA0 : A 0 = f (ofLex ((e ⟨0, hmpos⟩ : ↥t) : Lex Ivl)).1 := by
      simp [A, hmpos]
    have hAm : A m = f U := by simp [A]
    rw [hA0, hAm] at htelescope
    simp only [Nat.cast_one, div_one] at htelescope
    exact htelescope.trans (sub_le_sub_left
      (hmono ⟨le_rfl, hLU⟩
        ⟨(hinside _ (emem ⟨0, hmpos⟩)).1,
          (hord _ (emem ⟨0, hmpos⟩)).le.trans
            (hinside _ (emem ⟨0, hmpos⟩)).2⟩
        (hinside _ (emem ⟨0, hmpos⟩)).1) _)

private lemma endpt_var_le_of_anti
    (s : Finset Ivl) (f : ℝ → ℝ) (L U : ℝ)
    (hord : ∀ I ∈ s, I.1 < I.2)
    (hLU : L ≤ U)
    (hinside : ∀ I ∈ s, L ≤ I.1 ∧ I.2 ≤ U)
    (hsep : Set.Pairwise (↑s : Set Ivl)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1))
    (hanti : AntitoneOn f (Icc L U)) :
    ∑ I ∈ s, (f I.1 - f I.2) ≤ f L - f U := by
  have h := endpt_var_le_of_mono s (-f) L U hord hLU hinside hsep
    (fun _ hx _ hy hxy ↦ neg_le_neg (hanti hx hy hxy))
  simpa only [Pi.neg_apply, neg_sub_neg] using h

private lemma endpt_cos_eq {n : ℕ} (hn : 0 < n)
    (F : IvlFam n) {θ : ℝ} {I : RealIvl}
    (hI : I ∈ F.base) :
    cos ((2 * (n : ℝ)) * (I.2 + θ)) =
      cos ((2 * (n : ℝ)) * (I.1 + θ)) := by
  obtain ⟨a, b, ha, hb⟩ := F.grid_endpoints I hI
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [ha, hb]
  have hphase (k : ℤ) :
      (2 * (n : ℝ)) * ((k : ℝ) * π / n + θ) =
        (2 * (n : ℝ)) * θ + (k : ℝ) * (2 * π) := by
    field_simp [hnR]
    ring
  rw [hphase a, hphase b, cos_add_int_mul_two_pi,
    cos_add_int_mul_two_pi]

private lemma sh_intg_eq {n : ℕ} (I : RealIvl) (θ : ℝ) :
    reflIntg n I θ =
      ∫ u in I.1 + θ..I.2 + θ,
        (sin u)⁻¹ * sin ((2 * (n : ℝ)) * u) := by
  have hshift := integral_comp_add_right
    (fun u : ℝ ↦ (sin u)⁻¹ * sin ((2 * (n : ℝ)) * u))
    θ (a := I.1) (b := I.2)
  rw [← hshift]
  unfold reflIntg
  apply intervalIntegral.integral_congr
  intro x hx
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  rw [div_eq_mul_inv]
  ring

private lemma local_left_bound {n : ℕ} (hn : 4096 ≤ n)
    (F : IvlFam n) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (π / 2))
    {I : RealIvl} (hI : I ∈ leftIvls F θ) :
    |reflIntg n I θ| ≤
      (amp θ I.1 - amp θ I.2) / n := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hbase : I ∈ F.base := (mem_filter.mp hI).1
  have hside : I.2 ≤ turnPt θ := (mem_filter.mp hI).2
  have hab : I.1 + θ ≤ I.2 + θ := by
    linarith [F.ordered I hbase]
  have hderiv : ∀ u ∈ Icc (I.1 + θ) (I.2 + θ),
      HasDerivAt sin⁻¹ (-cos u / sin u ^ 2) u := by
    intro u hu
    exact (hasDerivAt_sin u).inv
      (ne_of_gt (sin_pos_of_mem_sh_ivl hn0 F hθ hbase hu))
  have hcont : ContinuousOn (fun u : ℝ ↦ -cos u / sin u ^ 2)
      (Icc (I.1 + θ) (I.2 + θ)) := by
    intro u hu
    have hsin : sin u ≠ 0 := ne_of_gt
      (sin_pos_of_mem_sh_ivl hn0 F hθ hbase hu)
    exact ((continuous_cos.continuousAt.neg).div
      (continuous_sin.continuousAt.pow 2) (pow_ne_zero 2 hsin)).continuousWithinAt
  have hnonpos : ∀ u ∈ Icc (I.1 + θ) (I.2 + θ),
      -cos u / sin u ^ 2 ≤ 0 := by
    intro u hu
    have huHalf : u ≤ π / 2 := by
      dsimp [turnPt] at hside
      linarith [hu.2]
    have huNonneg : -(π / 2) ≤ u := by
      have hx : u - θ ∈ Icc I.1 I.2 :=
        ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have hband := sh_mem_band F hθ hbase hx
      linarith [hband.1, eta_pos hn0, pi_pos]
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (cos_nonneg_of_mem_Icc ⟨huNonneg, huHalf⟩))
      (sq_nonneg _)
  have hosc := abs_intg_mul_sin_le_of_deriv_nonpos
    (h := sin⁻¹) (h' := fun u : ℝ ↦ -cos u / sin u ^ 2)
    hn0 hab hderiv hcont hnonpos (endpt_cos_eq hn0 F hbase)
  rw [sh_intg_eq]
  have hamp : amp θ I.2 ≤ amp θ I.1 := by
    have hsinA : 0 < sin (I.1 + θ) :=
      sin_sh_pos hn0 F hθ hbase ⟨le_rfl, F.ordered I hbase⟩
    have hbandA := sh_mem_band F hθ hbase
      ⟨le_rfl, F.ordered I hbase⟩
    have hsinmono : sin (I.1 + θ) ≤ sin (I.2 + θ) :=
      sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [hbandA.1, eta_pos hn0, pi_pos])
        (by dsimp [turnPt] at hside; linarith)
        (by linarith [F.ordered I hbase])
    simpa only [amp, one_div] using
      one_div_le_one_div_of_le hsinA hsinmono
  change |∫ u in I.1 + θ..I.2 + θ,
      (sin u)⁻¹ * sin ((2 * (n : ℝ)) * u)| ≤
    |(sin (I.2 + θ))⁻¹ - (sin (I.1 + θ))⁻¹| / n at hosc
  have hamp' : (sin (I.2 + θ))⁻¹ ≤
      (sin (I.1 + θ))⁻¹ := by simpa only [amp] using hamp
  rw [abs_of_nonpos (sub_nonpos.mpr hamp')] at hosc
  simpa only [amp, neg_sub] using hosc

private lemma local_right_bound {n : ℕ} (hn : 4096 ≤ n)
    (F : IvlFam n) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (π / 2))
    {I : RealIvl} (hI : I ∈ rightIvls F θ) :
    |reflIntg n I θ| ≤
      (amp θ I.2 - amp θ I.1) / n := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hbase : I ∈ F.base := (mem_filter.mp hI).1
  have hside : turnPt θ ≤ I.1 := (mem_filter.mp hI).2
  have hab : I.1 + θ ≤ I.2 + θ := by
    linarith [F.ordered I hbase]
  have hderiv : ∀ u ∈ Icc (I.1 + θ) (I.2 + θ),
      HasDerivAt sin⁻¹ (-cos u / sin u ^ 2) u := by
    intro u hu
    exact (hasDerivAt_sin u).inv
      (ne_of_gt (sin_pos_of_mem_sh_ivl hn0 F hθ hbase hu))
  have hcont : ContinuousOn (fun u : ℝ ↦ -cos u / sin u ^ 2)
      (Icc (I.1 + θ) (I.2 + θ)) := by
    intro u hu
    have hsin : sin u ≠ 0 := ne_of_gt
      (sin_pos_of_mem_sh_ivl hn0 F hθ hbase hu)
    exact ((continuous_cos.continuousAt.neg).div
      (continuous_sin.continuousAt.pow 2) (pow_ne_zero 2 hsin)).continuousWithinAt
  have hnonneg : ∀ u ∈ Icc (I.1 + θ) (I.2 + θ),
      0 ≤ -cos u / sin u ^ 2 := by
    intro u hu
    have huHalf : π / 2 ≤ u := by
      dsimp [turnPt] at hside
      linarith [hu.1]
    have huTop : u ≤ π + π / 2 := by
      have hx : u - θ ∈ Icc I.1 I.2 :=
        ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have hband := sh_mem_band F hθ hbase hx
      linarith [hband.2, eta_pos hn0, pi_pos]
    exact div_nonneg (neg_nonneg.mpr
      (Real.cos_nonpos_of_pi_div_two_le_of_le huHalf huTop)) (sq_nonneg _)
  have hosc := abs_intg_mul_sin_le_of_deriv_nonneg
    (h := sin⁻¹) (h' := fun u : ℝ ↦ -cos u / sin u ^ 2)
    hn0 hab hderiv hcont hnonneg (endpt_cos_eq hn0 F hbase)
  rw [sh_intg_eq]
  have hamp : amp θ I.1 ≤ amp θ I.2 := by
    have hsinB : 0 < sin (I.2 + θ) :=
      sin_sh_pos hn0 F hθ hbase ⟨F.ordered I hbase, le_rfl⟩
    have hcompOrder : π - (I.2 + θ) ≤
        π - (I.1 + θ) := by linarith [F.ordered I hbase]
    have hcompTop : π - (I.1 + θ) ≤ π / 2 := by
      dsimp [turnPt] at hside
      linarith
    have hcompLow : -(π / 2) ≤ π - (I.2 + θ) := by
      have hband := sh_mem_band F hθ hbase
        ⟨F.ordered I hbase, le_rfl⟩
      linarith [hband.2, eta_pos hn0, pi_pos]
    have hsinmono := sin_le_sin_of_le_of_le_pi_div_two
      hcompLow hcompTop hcompOrder
    rw [sin_pi_sub, sin_pi_sub] at hsinmono
    simpa only [amp, one_div] using
      one_div_le_one_div_of_le hsinB hsinmono
  change |∫ u in I.1 + θ..I.2 + θ,
      (sin u)⁻¹ * sin ((2 * (n : ℝ)) * u)| ≤
    |(sin (I.2 + θ))⁻¹ - (sin (I.1 + θ))⁻¹| / n at hosc
  have hamp' : (sin (I.1 + θ))⁻¹ ≤
      (sin (I.2 + θ))⁻¹ := by simpa only [amp] using hamp
  rw [abs_of_nonneg (sub_nonneg.mpr hamp')] at hosc
  simpa only [amp] using hosc

private lemma amp_anti_left {n : ℕ} (hn : 4096 ≤ n)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (π / 2))
    (hbranch : eta n ≤ turnPt θ) :
    AntitoneOn (amp θ) (Icc (eta n) (turnPt θ)) := by
  intro x hx y hy hxy
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hsinX : 0 < sin (x + θ) := by
    apply sin_pos_of_pos_of_lt_pi
    · linarith [hx.1, eta_pos hn0, hθ.1]
    · dsimp [turnPt] at hy
      linarith [hy.2, pi_pos]
  have hsinmono : sin (x + θ) ≤ sin (y + θ) :=
    sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [hx.1, eta_pos hn0, hθ.1, pi_pos])
      (by dsimp [turnPt] at hy; linarith [hy.2])
      (by linarith)
  simpa only [amp, one_div] using
    one_div_le_one_div_of_le hsinX hsinmono

private lemma amp_mono_right {n : ℕ} (hn : 4096 ≤ n)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (π / 2))
    (hbranch : turnPt θ ≤ π / 2 - eta n) :
    MonotoneOn (amp θ)
      (Icc (turnPt θ) (π / 2 - eta n)) := by
  intro x hx y hy hxy
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hsinY : 0 < sin (y + θ) := by
    apply sin_pos_of_pos_of_lt_pi
    · dsimp [turnPt] at hx
      linarith [hx.1, pi_pos]
    · linarith [hy.2, eta_pos hn0, hθ.2]
  have hcompOrder : π - (y + θ) ≤ π - (x + θ) := by
    linarith
  have hcompTop : π - (x + θ) ≤ π / 2 := by
    dsimp [turnPt] at hx
    linarith [hx.1]
  have hcompLow : -(π / 2) ≤ π - (y + θ) := by
    linarith [hy.2, eta_pos hn0, hθ.2, pi_pos]
  have hsinmono := sin_le_sin_of_le_of_le_pi_div_two
    hcompLow hcompTop hcompOrder
  rw [sin_pi_sub, sin_pi_sub] at hsinmono
  simpa only [amp, one_div] using
    one_div_le_one_div_of_le hsinY hsinmono

private lemma sum_left_le {n : ℕ} (hn : 4096 ≤ n)
    (F : IvlFam n) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (π / 2)) :
    ∑ I ∈ leftIvls F θ, |reflIntg n I θ| ≤
      1 / ((n : ℝ) * sin (eta n)) := by
  classical
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  by_cases hbranch : eta n ≤ turnPt θ
  · have hvar := endpt_var_le_of_anti
      (leftIvls F θ) (amp θ) (eta n) (turnPt θ)
      (fun I hI ↦ F.nondegenerate I (mem_filter.mp hI).1)
      hbranch
      (fun I hI ↦ ⟨(F.away_from_axes I (mem_filter.mp hI).1).1,
        (mem_filter.mp hI).2⟩)
      (fun I hI J hJ hne ↦ endptSep hn0 F
        (mem_filter.mp hI).1 (mem_filter.mp hJ).1 hne)
      (amp_anti_left hn hθ hbranch)
    have hturn : amp θ (turnPt θ) = 1 := by
      simp [amp, turnPt]
    have hampEta : amp θ (eta n) ≤ 1 / sin (eta n) := by
      have hsineta : 0 < sin (eta n) :=
        sin_pos_of_pos_of_lt_pi (eta_pos hn0)
          ((eta_le_pi_div_two hn).trans_lt (by linarith [pi_pos]))
      have hsinmono : sin (eta n) ≤ sin (eta n + θ) :=
        sin_le_sin_of_le_of_le_pi_div_two
          (by linarith [eta_pos hn0, pi_pos])
          (by dsimp [turnPt] at hbranch; linarith)
          (by linarith [hθ.1])
      simpa only [amp, one_div] using
        one_div_le_one_div_of_le hsineta hsinmono
    calc
      ∑ I ∈ leftIvls F θ, |reflIntg n I θ| ≤
          ∑ I ∈ leftIvls F θ,
            (amp θ I.1 - amp θ I.2) / n :=
        sum_le_sum fun I hI ↦ local_left_bound hn F hθ hI
      _ = (∑ I ∈ leftIvls F θ,
            (amp θ I.1 - amp θ I.2)) / n := by
        rw [sum_div]
      _ ≤ (1 / sin (eta n)) / n := by
        apply (div_le_div_iff_of_pos_right (by exact_mod_cast hn0)).2
        rw [hturn] at hvar
        linarith
      _ = 1 / ((n : ℝ) * sin (eta n)) := by
        field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hn0]
  · have hempty : leftIvls F θ = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro I hmem
      have hI := (mem_filter.mp hmem).1
      have hside := (mem_filter.mp hmem).2
      have haway := (F.away_from_axes I hI).1
      have hstrict := F.nondegenerate I hI
      dsimp [eta, turnPt] at hbranch hside
      linarith
    rw [hempty]
    simp
    have hsineta : 0 < sin (eta n) :=
      sin_pos_of_pos_of_lt_pi (eta_pos hn0)
        ((eta_le_pi_div_two hn).trans_lt (by linarith [pi_pos]))
    exact mul_nonneg (inv_nonneg.mpr hsineta.le)
      (inv_nonneg.mpr (show (0 : ℝ) ≤ n by positivity))

private lemma sum_right_le {n : ℕ} (hn : 4096 ≤ n)
    (F : IvlFam n) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (π / 2)) :
    ∑ I ∈ rightIvls F θ, |reflIntg n I θ| ≤
      1 / ((n : ℝ) * sin (eta n)) := by
  classical
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  by_cases hbranch : turnPt θ ≤ π / 2 - eta n
  · have hvar := endpt_var_le_of_mono
      (rightIvls F θ) (amp θ) (turnPt θ)
        (π / 2 - eta n)
      (fun I hI ↦ F.nondegenerate I (mem_filter.mp hI).1)
      hbranch
      (fun I hI ↦ ⟨(mem_filter.mp hI).2,
        (F.away_from_axes I (mem_filter.mp hI).1).2⟩)
      (fun I hI J hJ hne ↦ endptSep hn0 F
        (mem_filter.mp hI).1 (mem_filter.mp hJ).1 hne)
      (amp_mono_right hn hθ hbranch)
    have hturn : amp θ (turnPt θ) = 1 := by
      simp [amp, turnPt]
    have hampU : amp θ (π / 2 - eta n) ≤
        1 / sin (eta n) := by
      have hsineta : 0 < sin (eta n) :=
        sin_pos_of_pos_of_lt_pi (eta_pos hn0)
          ((eta_le_pi_div_two hn).trans_lt (by linarith [pi_pos]))
      have hcompOrder : eta n ≤
          π - ((π / 2 - eta n) + θ) := by
        linarith [hθ.2]
      have hcompTop : π - ((π / 2 - eta n) + θ) ≤
          π / 2 := by
        dsimp [turnPt] at hbranch
        linarith
      have hsinmono := sin_le_sin_of_le_of_le_pi_div_two
        (x := eta n)
        (y := π - ((π / 2 - eta n) + θ))
        (by linarith [eta_pos hn0, pi_pos]) hcompTop hcompOrder
      rw [sin_pi_sub] at hsinmono
      simpa only [amp, one_div] using
        one_div_le_one_div_of_le hsineta hsinmono
    calc
      ∑ I ∈ rightIvls F θ, |reflIntg n I θ| ≤
          ∑ I ∈ rightIvls F θ,
            (amp θ I.2 - amp θ I.1) / n :=
        sum_le_sum fun I hI ↦ local_right_bound hn F hθ hI
      _ = (∑ I ∈ rightIvls F θ,
            (amp θ I.2 - amp θ I.1)) / n := by
        rw [sum_div]
      _ ≤ (1 / sin (eta n)) / n := by
        apply (div_le_div_iff_of_pos_right (by exact_mod_cast hn0)).2
        rw [hturn] at hvar
        linarith
      _ = 1 / ((n : ℝ) * sin (eta n)) := by
        field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hn0]
  · have hempty : rightIvls F θ = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro I hmem
      have hI := (mem_filter.mp hmem).1
      have hside := (mem_filter.mp hmem).2
      have haway := (F.away_from_axes I hI).2
      have hstrict := F.nondegenerate I hI
      dsimp [eta, turnPt] at hbranch hside
      linarith
    rw [hempty]
    simp
    have hsineta : 0 < sin (eta n) :=
      sin_pos_of_pos_of_lt_pi (eta_pos hn0)
        ((eta_le_pi_div_two hn).trans_lt (by linarith [pi_pos]))
    exact mul_nonneg (inv_nonneg.mpr hsineta.le)
      (inv_nonneg.mpr (show (0 : ℝ) ≤ n by positivity))

private lemma crossing_ptwise_bound {n : ℕ} (hn : 4096 ≤ n)
    (F : IvlFam n) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (π / 2))
    {I : RealIvl} (hI : I ∈ crossingIvls F θ) :
    |reflIntg n I θ| ≤ 12 * π / n := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnRpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hbase : I ∈ F.base := (mem_filter.mp hI).1
  have hcross := (mem_filter.mp hI).2
  have hnorm := norm_integral_le_of_norm_le_const
    (a := I.1) (b := I.2) (C := (2 : ℝ))
    (f := fun x : ℝ ↦
      sin (((2 * n : ℕ) : ℝ) * (x + θ)) / sin (x + θ))
    (fun x hx ↦ by
      rw [Set.uIoc_of_le (F.ordered I hbase)] at hx
      have hxI : x ∈ Icc I.1 I.2 := ⟨hx.1.le, hx.2⟩
      have hdist : |(x + θ) - π / 2| ≤ 6 * π / n := by
        have hwidth := F.short I hbase
        dsimp [turnPt] at hcross
        rw [abs_le]
        constructor <;> linarith [hxI.1, hxI.2]
      have hsmall : |(x + θ) - π / 2| ≤ 1 := by
        have hpi4 : π < 4 := pi_lt_four
        have hfrac : 6 * π / (n : ℝ) < 1 := by
          apply (div_lt_iff₀ hnRpos).2
          nlinarith
        exact hdist.trans hfrac.le
      have hcos : (1 : ℝ) / 2 ≤ cos ((x + θ) - π / 2) := by
        have hlow := Real.one_sub_sq_div_two_le_cos
          (x := (x + θ) - π / 2)
        have hsq : ((x + θ) - π / 2) ^ 2 ≤ 1 := by
          have habs0 : 0 ≤ |(x + θ) - π / 2| := abs_nonneg _
          nlinarith [sq_abs ((x + θ) - π / 2)]
        linarith
      have hsin : (1 : ℝ) / 2 ≤ sin (x + θ) := by
        rw [← Real.cos_sub_pi_div_two]
        exact hcos
      rw [norm_eq_abs, abs_div, abs_of_nonneg (by linarith : 0 ≤ sin (x + θ))]
      apply (div_le_iff₀ (by linarith : 0 < sin (x + θ))).2
      nlinarith [abs_sin_le_one
        (((2 * n : ℕ) : ℝ) * (x + θ))])
  unfold reflIntg
  rw [norm_eq_abs] at hnorm
  calc
    |∫ x in I.1..I.2,
        sin (((2 * n : ℕ) : ℝ) * (x + θ)) /
          sin (x + θ)| ≤ 2 * |I.2 - I.1| := hnorm
    _ = 2 * (I.2 - I.1) := by
      rw [abs_of_nonneg (sub_nonneg.mpr (F.ordered I hbase))]
    _ ≤ 2 * (6 * π / n) := by
      gcongr
      exact F.short I hbase
    _ = 12 * π / n := by ring

private lemma card_crossing_le_one {n : ℕ} (hn : 0 < n)
    (F : IvlFam n) (θ : ℝ) :
    (crossingIvls F θ).card ≤ 1 := by
  classical
  rw [card_le_one]
  intro I hI J hJ
  have hbaseI := (mem_filter.mp hI).1
  have hbaseJ := (mem_filter.mp hJ).1
  by_contra hne
  have hcrossI := (mem_filter.mp hI).2
  have hcrossJ := (mem_filter.mp hJ).2
  have hsep := F.separated hbaseI hbaseJ hne (turnPt θ)
    ⟨hcrossI.1.le, hcrossI.2.le⟩ (turnPt θ)
    ⟨hcrossJ.1.le, hcrossJ.2.le⟩
  have hpi : 0 < π / (n : ℝ) :=
    div_pos pi_pos (by exact_mod_cast hn)
  have : π / (n : ℝ) ≤ 0 := by simpa using hsep
  exact (not_le_of_gt hpi) this

private lemma sum_crossing_le {n : ℕ} (hn : 4096 ≤ n)
    (F : IvlFam n) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (π / 2)) :
    ∑ I ∈ crossingIvls F θ, |reflIntg n I θ| ≤
      12 * π / n := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  calc
    ∑ I ∈ crossingIvls F θ, |reflIntg n I θ| ≤
        ∑ _I ∈ crossingIvls F θ, 12 * π / n :=
      sum_le_sum fun I hI ↦ crossing_ptwise_bound hn F hθ hI
    _ = ((crossingIvls F θ).card : ℝ) * (12 * π / n) := by simp
    _ ≤ 1 * (12 * π / n) := by
      gcongr
      exact_mod_cast card_crossing_le_one hn0 F θ
    _ = 12 * π / n := one_mul _

private lemma base_part {n : ℕ} (F : IvlFam n) (θ : ℝ) :
    F.base = (leftIvls F θ ∪ rightIvls F θ) ∪
      crossingIvls F θ := by
  classical
  ext I
  simp only [leftIvls, rightIvls, crossingIvls, mem_filter,
    Finset.mem_union]
  constructor
  · intro hI
    by_cases hleft : I.2 ≤ turnPt θ
    · exact Or.inl (Or.inl ⟨hI, hleft⟩)
    · by_cases hright : turnPt θ ≤ I.1
      · exact Or.inl (Or.inr ⟨hI, hright⟩)
      · exact Or.inr ⟨hI, lt_of_not_ge hright, lt_of_not_ge hleft⟩
  · rintro ((⟨hI, _⟩ | ⟨hI, _⟩) | ⟨hI, _⟩) <;> exact hI

private lemma disjoint_left_right {n : ℕ} (F : IvlFam n)
    (θ : ℝ) : Disjoint (leftIvls F θ) (rightIvls F θ) := by
  classical
  rw [Finset.disjoint_left]
  intro I hleft hright
  have hbase := (mem_filter.mp hleft).1
  have hstrict := F.nondegenerate I hbase
  linarith [(mem_filter.mp hleft).2, (mem_filter.mp hright).2]

private lemma disjoint_sides_crossing {n : ℕ} (F : IvlFam n)
    (θ : ℝ) :
    Disjoint (leftIvls F θ ∪ rightIvls F θ)
      (crossingIvls F θ) := by
  classical
  rw [Finset.disjoint_left]
  intro I hsides hcross
  simp only [Finset.mem_union] at hsides
  have hc := (mem_filter.mp hcross).2
  rcases hsides with hleft | hright
  · linarith [(mem_filter.mp hleft).2, hc.2]
  · linarith [(mem_filter.mp hright).2, hc.1]

theorem sum_abs_reflIntg_le {n : ℕ} (hn : 4096 ≤ n)
    (F : IvlFam n) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (π / 2)) :
    ∑ I : ↥F.base, |reflIntg n I.1 θ| ≤
      2 / ((n : ℝ) * sin (100 * π / n)) + 12 * π / n := by
  classical
  rw [← sum_subtype F.base (by simp)
    (fun I ↦ |reflIntg n I θ|)]
  rw [base_part F θ,
    sum_union (disjoint_sides_crossing F θ),
    sum_union (disjoint_left_right F θ)]
  have hleft := sum_left_le hn F hθ
  have hright := sum_right_le hn F hθ
  have hcross := sum_crossing_le hn F hθ
  dsimp [eta] at hleft hright
  calc
    (∑ I ∈ leftIvls F θ, |reflIntg n I θ|) +
          (∑ I ∈ rightIvls F θ, |reflIntg n I θ|) +
        ∑ I ∈ crossingIvls F θ, |reflIntg n I θ| ≤
      1 / ((n : ℝ) * sin (100 * π / n)) +
        1 / ((n : ℝ) * sin (100 * π / n)) +
          12 * π / n := by linarith
    _ = 2 / ((n : ℝ) * sin (100 * π / n)) +
          12 * π / n := by ring

end

end KernelReflClaim

end

section

namespace ConcreteKernelClaims

open scoped BigOperators Interval
open Real Set MeasureTheory intervalIntegral

noncomputable section

open OddSine

private abbrev Ivl := ℝ × ℝ

theorem endpt_var_le_of_mono
    (s : Finset Ivl) (f : ℝ → ℝ) (L U : ℝ)
    (hord : ∀ I ∈ s, I.1 < I.2)
    (hLU : L ≤ U)
    (hinside : ∀ I ∈ s, L ≤ I.1 ∧ I.2 ≤ U)
    (hsep : Set.Pairwise (↑s : Set Ivl)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1))
    (hmono : MonotoneOn f (Icc L U)) :
    ∑ I ∈ s, (f I.2 - f I.1) ≤ f U - f L := by
  classical
  let t : Finset (Lex Ivl) := s.image toLex
  let m := t.card
  let e : Fin m ≃o ↥t := orderIsoOfFin t rfl
  have emem (k : Fin m) : ofLex ((e k : ↥t) : Lex Ivl) ∈ s := by
    have hk := (e k).property
    change ((e k : ↥t) : Lex Ivl) ∈ s.image toLex at hk
    rw [Finset.mem_image] at hk
    rcases hk with ⟨I, hI, hEq⟩
    simpa [← hEq] using hI
  let A : ℕ → ℝ := fun k ↦
    if hk : k < m then f (ofLex ((e ⟨k, hk⟩ : ↥t) : Lex Ivl)).1 else f U
  let B : ℕ → ℝ := fun k ↦
    if hk : k < m then f (ofLex ((e ⟨k, hk⟩ : ↥t) : Lex Ivl)).2 else f U
  let E : ℕ → ℝ := fun k ↦ B k - A k
  have hchain : ∀ k < m, B k ≤ A (k + 1) := by
    intro k hk
    simp only [B, A, dif_pos hk]
    by_cases hks : k + 1 < m
    · rw [dif_pos hks]
      apply hmono
      · exact ⟨(hinside _ (emem ⟨k, hk⟩)).1.trans
            (hord _ (emem ⟨k, hk⟩)).le,
          (hinside _ (emem ⟨k, hk⟩)).2⟩
      · exact ⟨(hinside _ (emem ⟨k + 1, hks⟩)).1,
          (hord _ (emem ⟨k + 1, hks⟩)).le.trans
            (hinside _ (emem ⟨k + 1, hks⟩)).2⟩
      have horder : e ⟨k, hk⟩ ≤ e ⟨k + 1, hks⟩ :=
        e.le_iff_le.mpr (by simp)
      have hleft : (ofLex ((e ⟨k, hk⟩ : ↥t) : Lex Ivl)).1 ≤
          (ofLex ((e ⟨k + 1, hks⟩ : ↥t) : Lex Ivl)).1 := by
        exact (Prod.Lex.le_iff.mp horder).elim (fun h ↦ h.le) (fun h ↦ h.1.le)
      have hne : ofLex ((e ⟨k, hk⟩ : ↥t) : Lex Ivl) ≠
          ofLex ((e ⟨k + 1, hks⟩ : ↥t) : Lex Ivl) := by
        intro heq
        have heq' : e ⟨k, hk⟩ = e ⟨k + 1, hks⟩ := by
          apply Subtype.ext
          exact ofLex.injective heq
        have : (⟨k, hk⟩ : Fin m) = ⟨k + 1, hks⟩ := e.injective heq'
        simp at this
      rcases hsep (emem ⟨k, hk⟩) (emem ⟨k + 1, hks⟩) hne with hgood | hbad
      · exact hgood
      · have hstrict := hord _ (emem ⟨k + 1, hks⟩)
        linarith
    · rw [dif_neg hks]
      exact hmono
        ⟨(hinside _ (emem ⟨k, hk⟩)).1.trans (hord _ (emem ⟨k, hk⟩)).le,
          (hinside _ (emem ⟨k, hk⟩)).2⟩
        ⟨hLU, le_rfl⟩ (hinside _ (emem ⟨k, hk⟩)).2
  have htelescope :=
    sum_ivl_error_le_of_mono_endpts
      (n := 1) (m := m) (A := A) (B := B) (E := E) (by norm_num)
      (fun k hk ↦ by simp [E]) hchain
  have hsum : (∑ I ∈ s, (f I.2 - f I.1)) = ∑ k ∈ Finset.range m, E k := by
    calc
      (∑ I ∈ s, (f I.2 - f I.1)) =
          ∑ J ∈ t, (f (ofLex J).2 - f (ofLex J).1) := by
            symm
            simpa [t] using (sum_image (s := s)
              (f := fun J : Lex Ivl ↦ f (ofLex J).2 - f (ofLex J).1)
              toLex.injective.injOn)
      _ = ∑ J : ↥t, (f (ofLex (J.1 : Lex Ivl)).2 -
          f (ofLex (J.1 : Lex Ivl)).1) := by
            symm
            exact (sum_subtype (M := ℝ) (s := t) (p := fun J ↦ J ∈ t)
              (by simp) (fun J : Lex Ivl ↦
                f (ofLex J).2 - f (ofLex J).1)).symm
      _ = ∑ i : Fin m, (f (ofLex ((e i : ↥t) : Lex Ivl)).2 -
          f (ofLex ((e i : ↥t) : Lex Ivl)).1) := by
            exact (e.toEquiv.sum_comp (fun J : ↥t ↦
              f (ofLex (J.1 : Lex Ivl)).2 -
                f (ofLex (J.1 : Lex Ivl)).1)).symm
      _ = ∑ i : Fin m, E i := by
            apply sum_congr rfl
            intro i _
            simp [E, A, B, i.isLt]
      _ = ∑ k ∈ Finset.range m, E k := Fin.sum_univ_eq_sum_range E m
  rw [hsum]
  by_cases hm : m = 0
  · simpa [hm] using sub_nonneg.mpr (hmono ⟨le_rfl, hLU⟩ ⟨hLU, le_rfl⟩ hLU)
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hA0 : A 0 = f (ofLex ((e ⟨0, hmpos⟩ : ↥t) : Lex Ivl)).1 := by
      simp [A, hmpos]
    have hAm : A m = f U := by simp [A]
    rw [hA0, hAm] at htelescope
    simp only [Nat.cast_one, div_one] at htelescope
    exact htelescope.trans (sub_le_sub_left
      (hmono ⟨le_rfl, hLU⟩
        ⟨(hinside _ (emem ⟨0, hmpos⟩)).1,
          (hord _ (emem ⟨0, hmpos⟩)).le.trans
            (hinside _ (emem ⟨0, hmpos⟩)).2⟩
        (hinside _ (emem ⟨0, hmpos⟩)).1) _)

def replacementIntg (n : ℕ) (I : RealIvl) (θ : ℝ) : ℝ :=
  ∫ x in I.1..I.2,
    amp (x - θ) *
      sin ((2 * (n : ℝ)) * (x - θ))

private lemma endptSep {n : ℕ} (hn : 0 < n)
    (F : IvlFam n) :
    Set.Pairwise (↑F.base : Set RealIvl)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1) := by
  intro I hI J hJ hne
  have hgrid : 0 < π / (n : ℝ) :=
    div_pos pi_pos (by exact_mod_cast hn)
  by_cases hfirst : I.1 ≤ J.1
  · left
    by_contra hnot
    have hJinI : J.1 ∈ Icc I.1 I.2 :=
      ⟨hfirst, (lt_of_not_ge hnot).le⟩
    have hsep := F.separated hI hJ hne J.1 hJinI J.1
      ⟨le_rfl, F.ordered J hJ⟩
    have : π / (n : ℝ) ≤ 0 := by simpa using hsep
    exact (not_le_of_gt hgrid) this
  · right
    have hsecond : J.1 ≤ I.1 := (lt_of_not_ge hfirst).le
    by_contra hnot
    have hIinJ : I.1 ∈ Icc J.1 J.2 :=
      ⟨hsecond, (lt_of_not_ge hnot).le⟩
    have hsep := F.separated hI hJ hne I.1
      ⟨le_rfl, F.ordered I hI⟩ I.1 hIinJ
    have : π / (n : ℝ) ≤ 0 := by simpa using hsep
    exact (not_le_of_gt hgrid) this

private lemma sh_mem_half {n : ℕ} (F : IvlFam n)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (π / 2))
    {I : RealIvl} (hI : I ∈ F.base) {u : ℝ}
    (hu : u ∈ Icc (I.1 - θ) (I.2 - θ)) :
    u ∈ Icc (-(π / 2)) (π / 2) := by
  have hquadrant := F.in_first_quadrant I hI
  constructor
  · linarith [hu.1, hquadrant.1, hθ.2]
  · linarith [hu.2, hquadrant.2, hθ.1]

private lemma sh_endpt_cos_eq {n : ℕ} (hn : 0 < n)
    (F : IvlFam n) {θ : ℝ} {I : RealIvl}
    (hI : I ∈ F.base) :
    cos ((2 * (n : ℝ)) * (I.2 - θ)) =
      cos ((2 * (n : ℝ)) * (I.1 - θ)) := by
  obtain ⟨a, b, ha, hb⟩ := F.grid_endpoints I hI
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [ha, hb]
  calc
    cos ((2 * (n : ℝ)) * ((b : ℝ) * π / n - θ)) =
        cos ((b : ℝ) * (2 * π) - (2 * (n : ℝ)) * θ) := by
          congr 1
          field_simp [hn0]
    _ = cos ((2 * (n : ℝ)) * θ) :=
      cos_int_mul_two_pi_sub _ b
    _ = cos ((a : ℝ) * (2 * π) - (2 * (n : ℝ)) * θ) :=
      (cos_int_mul_two_pi_sub _ a).symm
    _ = cos ((2 * (n : ℝ)) * ((a : ℝ) * π / n - θ)) := by
          congr 1
          field_simp [hn0]

private lemma replacementIntg_sh (n : ℕ) (I : RealIvl)
    (θ : ℝ) :
    replacementIntg n I θ =
      ∫ u in I.1 - θ..I.2 - θ,
        amp u *
          sin ((2 * (n : ℝ)) * u) := by
  exact integral_comp_sub_right
    (fun u : ℝ ↦
      amp u *
        sin ((2 * (n : ℝ)) * u)) θ

private lemma abs_replacementIntg_le {n : ℕ} (hn : 0 < n)
    (F : IvlFam n) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (π / 2))
    {I : RealIvl} (hI : I ∈ F.base) :
    |replacementIntg n I θ| ≤
      (amp (I.2 - θ) -
        amp (I.1 - θ)) / n := by
  rw [replacementIntg_sh]
  have hdata :=
    amp_deriv_data
  have hosc := abs_intg_mul_sin_le_of_deriv_nonneg
    (h := amp)
    (h' := deriv amp)
    hn (sub_le_sub_right (F.ordered I hI) θ)
    (fun u hu ↦ hdata.1 u (sh_mem_half F hθ hI hu))
    (hdata.2.1.mono (fun u hu ↦ sh_mem_half F hθ hI hu))
    (fun u hu ↦ hdata.2.2 u (sh_mem_half F hθ hI hu))
    (sh_endpt_cos_eq hn F hI)
  have hmono := monoOn_amp
    (sh_mem_half F hθ hI
      ⟨le_rfl, sub_le_sub_right (F.ordered I hI) θ⟩)
    (sh_mem_half F hθ hI
      ⟨sub_le_sub_right (F.ordered I hI) θ, le_rfl⟩)
    (sub_le_sub_right (F.ordered I hI) θ)
  rw [abs_of_nonneg (sub_nonneg.mpr hmono)] at hosc
  exact hosc

theorem sum_abs_replacementIntg_le {n : ℕ} (hn : 4096 ≤ n)
    (F : IvlFam n) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (π / 2)) :
    ∑ I ∈ F.base, |replacementIntg n I θ| ≤
      (2 - 4 / π) / n := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  let f : ℝ → ℝ := fun x ↦
    amp (x - θ)
  have hfmono : MonotoneOn f (Icc 0 (π / 2)) := by
    intro x hx y hy hxy
    exact monoOn_amp
      ⟨by linarith [hx.1, hθ.2], by linarith [hx.2, hθ.1]⟩
      ⟨by linarith [hy.1, hθ.2], by linarith [hy.2, hθ.1]⟩
      (sub_le_sub_right hxy θ)
  have htel := endpt_var_le_of_mono F.base f 0 (π / 2)
    F.nondegenerate (by positivity) F.in_first_quadrant
    (endptSep hn0 F) hfmono
  have hglobal : f (π / 2) - f 0 ≤
      amp (π / 2) -
        amp (-(π / 2)) := by
    apply sub_le_sub
    · exact monoOn_amp
        ⟨by linarith [hθ.2, pi_pos], by linarith [hθ.1]⟩
        ⟨by linarith [pi_pos], le_rfl⟩ (by linarith [hθ.1])
    · exact monoOn_amp
        ⟨le_rfl, by linarith [pi_pos]⟩
        ⟨by linarith [hθ.2], by linarith [hθ.1, pi_pos]⟩
        (by linarith [hθ.2])
  calc
    ∑ I ∈ F.base, |replacementIntg n I θ| ≤
        ∑ I ∈ F.base, (f I.2 - f I.1) / n := by
          apply sum_le_sum
          intro I hI
          exact abs_replacementIntg_le hn0 F hθ hI
    _ = (∑ I ∈ F.base, (f I.2 - f I.1)) / n := by
          rw [sum_div]
    _ ≤ (f (π / 2) - f 0) / n := by
          exact div_le_div_of_nonneg_right htel (Nat.cast_nonneg n)
    _ ≤ (amp (π / 2) -
        amp (-(π / 2))) / n := by
          exact div_le_div_of_nonneg_right hglobal (Nat.cast_nonneg n)
    _ = (2 - 4 / π) / n := by
          rw [amp_endpt_var]

theorem sum_abs_replacementIntg_subtype_le {n : ℕ} (hn : 4096 ≤ n)
    (F : IvlFam n) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (π / 2)) :
    ∑ I : ↥F.base, |replacementIntg n I.1 θ| ≤
      (2 - 4 / π) / n := by
  rw [Finset.univ_eq_attach]
  calc
    ∑ I ∈ F.base.attach, |replacementIntg n I.1 θ| =
        ∑ I ∈ F.base, |replacementIntg n I θ| :=
      sum_attach F.base (fun I ↦ |replacementIntg n I θ|)
    _ ≤ (2 - 4 / π) / n :=
      sum_abs_replacementIntg_le hn F hθ

def quotientIntg (n : ℕ) (I : RealIvl) (θ : ℝ) : ℝ :=
  ∫ x in I.1..I.2,
    (sin ((2 * n : ℕ) * (x - θ)) / sin (x - θ) -
      sin ((2 * n : ℕ) * (x + θ)) / sin (x + θ))

private lemma quotientFirst_eq_pr_add_replacement {n : ℕ} (hn : 0 < n)
    {u : ℝ} (huHalf : u ∈ Icc (-(π / 2)) (π / 2))
    (hu : u ≠ 0) :
    sin ((2 * n : ℕ) * u) / sin u =
      2 * (n : ℝ) * sinc (2 * (n : ℝ) * u) +
        amp u *
          sin (2 * (n : ℝ) * u) := by
  have hsin := sin_ne_zero_of_mem_half
    huHalf hu
  have hscale : (2 * (n : ℝ)) ≠ 0 := by positivity
  have harg : 2 * (n : ℝ) * u ≠ 0 := mul_ne_zero hscale hu
  rw [sinc_of_ne_zero harg,
    amp_eq hu hsin]
  norm_cast
  field_simp [hu, hsin, hscale]
  ring

theorem quotientIntg_eq_pr_add_replacement_sub_refl
    {n : ℕ} (hn : 0 < n) (F : IvlFam n)
    {I : RealIvl} (hI : I ∈ F.base) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (π / 2)) :
    quotientIntg n I θ =
      prIntg n I θ +
        replacementIntg n I θ -
          KernelReflClaim.reflIntg n I θ := by
  let p : ℝ → ℝ := fun x ↦
    2 * (n : ℝ) * sinc (2 * (n : ℝ) * (x - θ))
  let r : ℝ → ℝ := fun x ↦
    amp (x - θ) *
      sin (2 * (n : ℝ) * (x - θ))
  let q : ℝ → ℝ := fun x ↦
    sin ((2 * n : ℕ) * (x - θ)) / sin (x - θ)
  let s : ℝ → ℝ := fun x ↦
    sin ((2 * n : ℕ) * (x + θ)) / sin (x + θ)
  have hord := F.ordered I hI
  have hpint : IntervalIntegrable p volume I.1 I.2 := by
    apply Continuous.intervalIntegrable
    dsimp [p]
    fun_prop
  have hrcont : ContinuousOn r (uIcc I.1 I.2) := by
    intro x hx
    have hxI : x ∈ Icc I.1 I.2 := by
      simpa [uIcc_of_le hord] using hx
    have hxHalf : x - θ ∈ Icc (-(π / 2)) (π / 2) :=
      sh_mem_half F hθ hI
        ⟨sub_le_sub_right hxI.1 θ, sub_le_sub_right hxI.2 θ⟩
    have hamp : ContinuousAt
        (fun y : ℝ ↦
          amp (y - θ)) x := by
      have hsub : ContinuousAt (fun y : ℝ ↦ y - θ) x :=
        continuousAt_id.sub continuousAt_const
      simpa only [Function.comp_def] using
        (analyticAt_amp
          hxHalf).continuousAt.comp_of_eq hsub rfl
    exact (hamp.mul (by fun_prop)).continuousWithinAt
  have hrint : IntervalIntegrable r volume I.1 I.2 := hrcont.intervalIntegrable
  have hscont : ContinuousOn s (uIcc I.1 I.2) := by
    intro x hx
    have hxI : x ∈ Icc I.1 I.2 := by
      simpa [uIcc_of_le hord] using hx
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hmesh : 0 < 100 * π / (n : ℝ) := by positivity
    have haxes := F.away_from_axes I hI
    have hsumPos : 0 < x + θ := by
      linarith [hxI.1, haxes.1, hθ.1]
    have hsumLt : x + θ < π := by
      linarith [hxI.2, haxes.2, hθ.2]
    have hsin : sin (x + θ) ≠ 0 :=
      ne_of_gt (sin_pos_of_pos_of_lt_pi hsumPos hsumLt)
    have hnum : ContinuousAt
        (fun y : ℝ ↦ sin ((2 * n : ℕ) * (y + θ))) x := by
      fun_prop
    have hden : ContinuousAt (fun y : ℝ ↦ sin (y + θ)) x := by
      fun_prop
    exact (hnum.div hden hsin).continuousWithinAt
  have hsint : IntervalIntegrable s volume I.1 I.2 := hscont.intervalIntegrable
  have hqr : ∀ᵐ x ∂volume, x ∈ uIoc I.1 I.2 → q x = p x + r x := by
    filter_upwards [Measure.ae_ne volume θ] with x hxt hx
    have hxIoc : x ∈ Ioc I.1 I.2 := by
      simpa [uIoc_of_le hord] using hx
    have hxI : x ∈ Icc I.1 I.2 := ⟨hxIoc.1.le, hxIoc.2⟩
    have hu : x - θ ≠ 0 := sub_ne_zero.mpr hxt
    have huHalf : x - θ ∈ Icc (-(π / 2)) (π / 2) :=
      sh_mem_half F hθ hI
        ⟨sub_le_sub_right hxI.1 θ, sub_le_sub_right hxI.2 θ⟩
    exact quotientFirst_eq_pr_add_replacement hn huHalf hu
  have hqrRestrict : p + r =ᵐ[volume.restrict (uIoc I.1 I.2)] q := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      ae_restrict_of_ae (Measure.ae_ne volume θ)] with x hx hxt
    have hxIoc : x ∈ Ioc I.1 I.2 := by
      simpa [uIoc_of_le hord] using hx
    have hxI : x ∈ Icc I.1 I.2 := ⟨hxIoc.1.le, hxIoc.2⟩
    have hu : x - θ ≠ 0 := sub_ne_zero.mpr hxt
    have huHalf : x - θ ∈ Icc (-(π / 2)) (π / 2) :=
      sh_mem_half F hθ hI
        ⟨sub_le_sub_right hxI.1 θ, sub_le_sub_right hxI.2 θ⟩
    exact (quotientFirst_eq_pr_add_replacement hn huHalf hu).symm
  have hqint : IntervalIntegrable q volume I.1 I.2 :=
    (hpint.add hrint).congr_ae hqrRestrict
  have hfirst : (∫ x in I.1..I.2, q x) =
      (∫ x in I.1..I.2, p x) + ∫ x in I.1..I.2, r x := by
    rw [intervalIntegral.integral_congr_ae hqr,
      intervalIntegral.integral_add hpint hrint]
  rw [quotientIntg, show (fun x : ℝ ↦
      sin ((2 * n : ℕ) * (x - θ)) / sin (x - θ) -
        sin ((2 * n : ℕ) * (x + θ)) / sin (x + θ)) =
      fun x ↦ q x - s x by rfl,
    intervalIntegral.integral_sub hqint hsint, hfirst]
  rfl

theorem total_kernel_error_le_two_thirds {n : ℕ} (hn : 4096 ≤ n) :
    2 / π + 2 / (n * sin (100 * π / n)) +
        12 * π / n + (2 - 4 / π) / n ≤ 2 / 3 := by
  have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hnR
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  let x : ℝ := 100 * π / n
  have hxpos : 0 < x := by positivity
  have hxle : x ≤ 1 / 10 := by
    rw [show x = 100 * π / n by rfl, div_le_iff₀ hnpos]
    nlinarith [pi_lt_four]
  have hxsq : x ^ 2 ≤ 1 / 100 := by nlinarith [sq_nonneg x]
  have hsin0 := sin_ge_sub_cube hxpos.le
  have hsin : (99 / 100) * x ≤ sin x := by
    nlinarith [mul_nonneg hxpos.le (sub_nonneg.mpr hxsq)]
  have hden : 300 ≤ (n : ℝ) * sin x := by
    calc
      (300 : ℝ) ≤ 99 * π := by
        nlinarith [pi_gt_d2]
      _ = (n : ℝ) * ((99 / 100) * x) := by
        dsimp [x]
        field_simp [hn0]
      _ ≤ (n : ℝ) * sin x := mul_le_mul_of_nonneg_left hsin hnpos.le
  have hdenpos : 0 < (n : ℝ) * sin x := lt_of_lt_of_le (by norm_num) hden
  have hreflectedPole : 2 / ((n : ℝ) * sin x) ≤ 1 / 150 := by
    apply (div_le_iff₀ hdenpos).2
    nlinarith
  have hprincipal : 2 / π ≤ 100 / 157 := by
    apply (div_le_iff₀ pi_pos).2
    nlinarith [pi_gt_d2]
  have hcrossing : 12 * π / (n : ℝ) ≤ 189 / 20480 := by
    apply (div_le_iff₀ hnpos).2
    nlinarith [pi_lt_d2]
  have hreplacement : (2 - 4 / π) / (n : ℝ) ≤ 1 / 2048 := by
    apply (div_le_iff₀ hnpos).2
    have : 0 ≤ 4 / π := div_nonneg (by norm_num) pi_pos.le
    nlinarith
  change 2 / π + 2 / ((n : ℝ) * sin x) +
      12 * π / n + (2 - 4 / π) / n ≤ 2 / 3
  calc
    2 / π + 2 / ((n : ℝ) * sin x) +
          12 * π / n + (2 - 4 / π) / n ≤
        100 / 157 + 1 / 150 + 189 / 20480 + 1 / 2048 := by linarith
    _ ≤ 2 / 3 := by norm_num

theorem signed_kernel_residual_le_two_thirds {n : ℕ} (hn : 4096 ≤ n)
    (F : IvlFam n) (α : ↥F.base → ℝ)
    (hα : Disc.IsSign α) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (π / 2)) :
    |(∑ I : ↥F.base, α I * quotientIntg n I.1 θ) -
        (∑ I ∈ nearBaseIvls F θ,
          α I * prIntg n I.1 θ)| ≤
      2 / 3 := by
  classical
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  let principal : ↥F.base → ℝ := fun I ↦
    prIntg n I.1 θ
  let replacement : ↥F.base → ℝ := fun I ↦
    replacementIntg n I.1 θ
  let reflected : ↥F.base → ℝ := fun I ↦
    KernelReflClaim.reflIntg n I.1 θ
  have hαAbs (I : ↥F.base) : |α I| = 1 := by
    rcases hα I with hI | hI <;> simp [hI]
  have hquotient :
      (∑ I : ↥F.base, α I * quotientIntg n I.1 θ) =
        (∑ I : ↥F.base, α I * principal I) +
          (∑ I : ↥F.base, α I * replacement I) -
            ∑ I : ↥F.base, α I * reflected I := by
    simp_rw [quotientIntg_eq_pr_add_replacement_sub_refl
      hn0 F (hI := Subtype.property _) hθ]
    simp_rw [mul_sub, mul_add, sum_sub_distrib,
      sum_add_distrib]
    rfl
  have hpartition :
      (∑ I : ↥F.base, α I * principal I) =
        (∑ I ∈ nearBaseIvls F θ,
          α I * principal I) +
        ∑ I ∈ farBaseIvls F θ,
          α I * principal I := by
    rw [farBaseIvls_eq_sdiff]
    calc
      (∑ I : ↥F.base, α I * principal I) =
          (∑ I ∈ Finset.univ \
              nearBaseIvls F θ,
            α I * principal I) +
          ∑ I ∈ nearBaseIvls F θ,
            α I * principal I :=
        (Finset.sum_sdiff
          (Finset.subset_univ
            (nearBaseIvls F θ))).symm
      _ = (∑ I ∈ nearBaseIvls F θ,
            α I * principal I) +
          ∑ I ∈ Finset.univ \
              nearBaseIvls F θ,
            α I * principal I := add_comm _ _
  have hresidual :
      (∑ I : ↥F.base, α I * quotientIntg n I.1 θ) -
          (∑ I ∈ nearBaseIvls F θ,
            α I * prIntg n I.1 θ) =
        (∑ I ∈ farBaseIvls F θ,
          α I * principal I) +
        (∑ I : ↥F.base, α I * replacement I) -
          ∑ I : ↥F.base, α I * reflected I := by
    rw [hquotient, hpartition]
    dsimp only [principal]
    ring
  have hprincipal :
      |∑ I ∈ farBaseIvls F θ,
          α I * principal I| ≤ 2 / π := by
    calc
      |∑ I ∈ farBaseIvls F θ,
          α I * principal I| ≤
          ∑ I ∈ farBaseIvls F θ,
            |α I * principal I| := abs_sum_le_sum_abs _ _
      _ = ∑ I ∈ farBaseIvls F θ,
            |principal I| := by
          apply sum_congr rfl
          intro I hI
          rw [abs_mul, hαAbs, one_mul]
      _ ≤ 2 / π :=
        sum_abs_prIntg_far_le_two_div_pi
          hn0 F hθ
  have hreplacement :
      |∑ I : ↥F.base, α I * replacement I| ≤
        (2 - 4 / π) / n := by
    calc
      |∑ I : ↥F.base, α I * replacement I| ≤
          ∑ I : ↥F.base, |α I * replacement I| :=
        abs_sum_le_sum_abs _ _
      _ = ∑ I : ↥F.base, |replacement I| := by
          apply sum_congr rfl
          intro I hI
          rw [abs_mul, hαAbs, one_mul]
      _ ≤ (2 - 4 / π) / n :=
        sum_abs_replacementIntg_subtype_le hn F hθ
  have hreflected :
      |∑ I : ↥F.base, α I * reflected I| ≤
        2 / ((n : ℝ) * sin (100 * π / n)) +
          12 * π / n := by
    calc
      |∑ I : ↥F.base, α I * reflected I| ≤
          ∑ I : ↥F.base, |α I * reflected I| :=
        abs_sum_le_sum_abs _ _
      _ = ∑ I : ↥F.base, |reflected I| := by
          apply sum_congr rfl
          intro I hI
          rw [abs_mul, hαAbs, one_mul]
      _ ≤ 2 / ((n : ℝ) * sin (100 * π / n)) +
          12 * π / n :=
        KernelReflClaim.sum_abs_reflIntg_le hn F hθ
  rw [hresidual]
  calc
    |(∑ I ∈ farBaseIvls F θ,
          α I * principal I) +
        (∑ I : ↥F.base, α I * replacement I) -
          ∑ I : ↥F.base, α I * reflected I| ≤
        |∑ I ∈ farBaseIvls F θ,
          α I * principal I| +
        |∑ I : ↥F.base, α I * replacement I| +
        |∑ I : ↥F.base, α I * reflected I| := by
          linarith [abs_add_le
            (∑ I ∈ farBaseIvls F θ,
              α I * principal I)
            (∑ I : ↥F.base, α I * replacement I),
            abs_sub
              ((∑ I ∈ farBaseIvls F θ,
                α I * principal I) +
                ∑ I : ↥F.base, α I * replacement I)
              (∑ I : ↥F.base, α I * reflected I)]
    _ ≤ 2 / π + (2 - 4 / π) / n +
        (2 / ((n : ℝ) * sin (100 * π / n)) +
          12 * π / n) := by linarith
    _ ≤ 2 / 3 := by
      linarith [total_kernel_error_le_two_thirds hn]

end

end ConcreteKernelClaims

end

section

namespace KernelCert

open scoped BigOperators Interval
open Set

noncomputable section

open OddSine

open scoped Classical

def normTarget {n : ℕ} (F : IvlFam n)
    (α : ↥F.base → ℝ) (θ : ℝ) : ℝ :=
  targetSine F α θ / (K * sqrt n)

private def clippedMagnitude (dangerous : Prop) [Decidable dangerous]
    (a : ℝ) : ℝ :=
  min 4 (max (if dangerous then 4 / 3 else 0) a)

private lemma clippedMagnitude_nonneg (dangerous : Prop) [Decidable dangerous]
    {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ clippedMagnitude dangerous a := by
  unfold clippedMagnitude
  apply le_min (by norm_num)
  exact le_max_of_le_right ha

private lemma clippedMagnitude_le_four (dangerous : Prop) [Decidable dangerous]
    (a : ℝ) :
    clippedMagnitude dangerous a ≤ 4 :=
  min_le_left _ _

private lemma four_thirds_le_clippedMagnitude {dangerous : Prop}
    [Decidable dangerous] {a : ℝ} (hdangerous : dangerous) :
    4 / 3 ≤ clippedMagnitude dangerous a := by
  unfold clippedMagnitude
  rw [if_pos hdangerous]
  apply le_min (by norm_num)
  exact le_max_left _ _

private lemma abs_sub_clippedMagnitude_le {dangerous : Prop}
    [Decidable dangerous] {a : ℝ} (ha : 0 ≤ a)
    (haUpper : a ≤ 14 / 3)
    (haLower : dangerous → 2 / 3 ≤ a) :
    |a - clippedMagnitude dangerous a| ≤ 2 / 3 := by
  classical
  unfold clippedMagnitude
  by_cases hdangerous : dangerous
  · rw [if_pos hdangerous]
    have halower := haLower hdangerous
    by_cases ha4 : a ≤ 4
    · rw [min_eq_right]
      · by_cases ha43 : 4 / 3 ≤ a
        · rw [max_eq_right ha43]
          norm_num
        · rw [max_eq_left (le_of_not_ge ha43)]
          rw [abs_of_nonpos]
          · linarith
          · linarith
      · exact max_le (by norm_num) ha4
    · have h4a : 4 ≤ max (4 / 3) a := by
        exact le_max_of_le_right (le_of_not_ge ha4)
      rw [min_eq_left h4a, abs_of_nonneg (sub_nonneg.2 (le_of_not_ge ha4))]
      linarith
  · rw [if_neg hdangerous, max_eq_right ha]
    by_cases ha4 : a ≤ 4
    · rw [min_eq_right ha4]
      norm_num
    · rw [min_eq_left (le_of_not_ge ha4),
        abs_of_nonneg (sub_nonneg.2 (le_of_not_ge ha4))]
      linarith

private def clippedMain {n : ℕ} (F : IvlFam n)
    (α : ↥F.base → ℝ) (θ : ℝ) : ℝ :=
  let m := clippedMagnitude (IsDangerous F θ)
    |normTarget F α θ|
  if 0 ≤ normTarget F α θ then m else -m

private def clippedError {n : ℕ} (F : IvlFam n)
    (α : ↥F.base → ℝ) (θ : ℝ) : ℝ :=
  normTarget F α θ - clippedMain F α θ

private lemma abs_clippedMain {n : ℕ} (F : IvlFam n)
    (α : ↥F.base → ℝ) (θ : ℝ) :
    |clippedMain F α θ| =
      clippedMagnitude (IsDangerous F θ)
        |normTarget F α θ| := by
  classical
  simp only [clippedMain]
  by_cases hv : 0 ≤ normTarget F α θ
  · rw [if_pos hv,
      abs_of_nonneg (clippedMagnitude_nonneg _ (abs_nonneg _))]
  · rw [if_neg hv, abs_neg,
      abs_of_nonneg (clippedMagnitude_nonneg _ (abs_nonneg _))]

private lemma abs_clippedError {n : ℕ} (F : IvlFam n)
    (α : ↥F.base → ℝ) (θ : ℝ) :
    |clippedError F α θ| =
      |(|normTarget F α θ| -
        clippedMagnitude (IsDangerous F θ)
          |normTarget F α θ|)| := by
  classical
  unfold clippedError clippedMain
  by_cases hv : 0 ≤ normTarget F α θ
  · rw [if_pos hv, abs_of_nonneg hv]
  · rw [if_neg hv, abs_of_neg (lt_of_not_ge hv)]
    have heq : normTarget F α θ +
        clippedMagnitude (IsDangerous F θ)
            (-normTarget F α θ) =
          -(-normTarget F α θ -
            clippedMagnitude (IsDangerous F θ)
              (-normTarget F α θ)) := by ring
    rw [sub_neg_eq_add, heq, abs_neg]

noncomputable def kernelCert_of_norm_bounds {n : ℕ} (hn : 0 < n)
    (F : IvlFam n)
    (α : ↥F.base → ℝ)
    (hlower : ∀ θ, IsDangerous F θ →
      2 / 3 ≤ |normTarget F α θ|)
    (hupper : ∀ θ, |normTarget F α θ| ≤ 14 / 3) :
    KernelCert F α := by
  classical
  refine
    { main := clippedMain F α
      error := clippedError F α
      decomposition := ?_
      main_lower := ?_
      main_upper := ?_
      error_bound := ?_ }
  · intro θ
    have hscale : K * sqrt n ≠ 0 := by
      apply mul_ne_zero
      · norm_num [K]
      · exact ne_of_gt (sqrt_pos.2 (by exact_mod_cast hn))
    rw [show clippedMain F α θ + clippedError F α θ =
        normTarget F α θ by
      simp only [clippedError]
      ring]
    simp only [normTarget]
    rw [mul_comm]
    exact (div_mul_cancel₀ _ hscale).symm
  · intro θ hθ
    rw [abs_clippedMain]
    exact four_thirds_le_clippedMagnitude hθ
  · intro θ
    rw [abs_clippedMain]
    exact clippedMagnitude_le_four _ _
  · intro θ
    rw [abs_clippedError]
    exact abs_sub_clippedMagnitude_le (abs_nonneg _)
      (hupper θ) (hlower θ)

theorem norm_bounds_of_firstQuad {n : ℕ}
    (F : IvlFam n)
    (α : ↥F.base → ℝ)
    (hlower : ∀ θ ∈ Icc 0 (π / 2),
      IsDangerous F θ → 2 / 3 ≤ |normTarget F α θ|)
    (hupper : ∀ θ ∈ Icc 0 (π / 2),
      |normTarget F α θ| ≤ 14 / 3) :
    (∀ θ, IsDangerous F θ →
      2 / 3 ≤ |normTarget F α θ|) ∧
    (∀ θ, |normTarget F α θ| ≤ 14 / 3) := by
  constructor
  · intro θ hθ
    obtain ⟨I, hI, hmem | hmem | hmem | hmem⟩ := hθ
    · exact hlower θ
        ⟨(F.in_first_quadrant I hI).1.trans hmem.1,
          hmem.2.trans (F.in_first_quadrant I hI).2⟩
        ⟨I, hI, Or.inl hmem⟩
    · have hqmem : -θ ∈ Icc 0 (π / 2) :=
        ⟨(F.in_first_quadrant I hI).1.trans hmem.1,
          hmem.2.trans (F.in_first_quadrant I hI).2⟩
      have hqdanger : IsDangerous F (-θ) :=
        ⟨I, hI, Or.inl hmem⟩
      have hq := hlower (-θ) hqmem hqdanger
      simpa only [normTarget, targetSine,
        oddSineSum_neg, abs_div, abs_neg] using hq
    · have hqmem : π - θ ∈ Icc 0 (π / 2) :=
        ⟨(F.in_first_quadrant I hI).1.trans hmem.1,
          hmem.2.trans (F.in_first_quadrant I hI).2⟩
      have hqdanger : IsDangerous F (π - θ) :=
        ⟨I, hI, Or.inl hmem⟩
      have hq := hlower (π - θ) hqmem hqdanger
      simpa only [normTarget, targetSine,
        oddSineSum_pi_sub, abs_div] using hq
    · have hqmem : θ - π ∈ Icc 0 (π / 2) :=
        ⟨(F.in_first_quadrant I hI).1.trans hmem.1,
          hmem.2.trans (F.in_first_quadrant I hI).2⟩
      have hqdanger : IsDangerous F (θ - π) :=
        ⟨I, hI, Or.inl hmem⟩
      have hq := hlower (θ - π) hqmem hqdanger
      have heq : θ = (θ - π) + π := by ring
      rw [heq]
      simpa only [normTarget, targetSine,
        oddSineSum_add_pi, abs_div, abs_neg] using hq
  · intro θ
    obtain ⟨θ', hθ', heq⟩ :=
      exists_firstQuad_abs_oddSinSum_eq n (fourierTarget F α) θ
    have hq := hupper θ' hθ'
    simp only [normTarget, targetSine, abs_div] at hq ⊢
    rw [heq]
    exact hq

theorem exists_gridIdxs_lt {n : ℕ} (hn : 0 < n)
    (F : IvlFam n) (I : ↥F.base) :
    ∃ a b : ℤ, a < b ∧
      I.1.1 = (a : ℝ) * π / n ∧
      I.1.2 = (b : ℝ) * π / n := by
  obtain ⟨a, b, ha, hb⟩ := F.grid_endpoints I.1 I.property
  refine ⟨a, b, ?_, ha, hb⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hscalePos : 0 < π / (n : ℝ) := div_pos pi_pos hnR
  have hscaled : (a : ℝ) * (π / (n : ℝ)) <
      (b : ℝ) * (π / (n : ℝ)) := by
    simpa only [mul_div_assoc, ha, hb] using
      F.nondegenerate I.1 I.property
  have habR : (a : ℝ) < b := by
    nlinarith [hscalePos]
  exact_mod_cast habR

theorem prIntg_self_mem {n : ℕ} (hn : 0 < n)
    (F : IvlFam n) {θ : ℝ}
    (I : ↥F.base) (hθ : InIvl I.1 θ) :
    prIntg n I.1 θ ∈
      Icc ((4 : ℝ) / 3) 4 := by
  obtain ⟨a, b, hab, ha, hb⟩ := exists_gridIdxs_lt hn F I
  have hshort : (b : ℝ) * π / n - (a : ℝ) * π / n ≤
      6 * π / n := by
    rw [← ha, ← hb]
    exact F.short I.1 I.property
  have hθ' : θ ∈ Icc ((a : ℝ) * π / n)
      ((b : ℝ) * π / n) := by
    change θ ∈ Icc I.1.1 I.1.2 at hθ
    simpa only [← ha, ← hb] using hθ
  have hmain := SinIntgGrid.pr_grid_ivl_inside
    n hn a b hab hshort hθ'
  simpa only [prIntg, ha, hb] using hmain

theorem abs_prIntg_le_two_of_near_of_not_mem {n : ℕ}
    (hn : 0 < n) (F : IvlFam n) {θ : ℝ}
    (I : ↥F.base)
    (hnear : I ∈ nearBaseIvls F θ)
    (hout : ¬InIvl I.1 θ) :
    |prIntg n I.1 θ| ≤ 2 := by
  obtain ⟨a, b, hab, ha, hb⟩ := exists_gridIdxs_lt hn F I
  have hshort : (b : ℝ) * π / n - (a : ℝ) * π / n ≤
      6 * π / n := by
    rw [← ha, ← hb]
    exact F.short I.1 I.property
  have hnearGap : Near n θ I.1 := by
    simpa only [nearBaseIvls,
      mem_filter, Finset.mem_univ, true_and] using hnear
  rw [InIvl, mem_Icc] at hout
  have hside :
      (θ ≤ (a : ℝ) * π / n ∧
        (a : ℝ) * π / n - θ ≤ π / n) ∨
      ((b : ℝ) * π / n ≤ θ ∧
        θ - (b : ℝ) * π / n ≤ π / n) := by
    rcases not_and_or.mp hout with hleft | hright
    · left
      have hθ : θ ≤ I.1.1 := (lt_of_not_ge hleft).le
      have hgap := hnearGap
      rw [Near,
        ivlGap_eq_left
          (F.ordered I.1 I.property) hθ] at hgap
      rw [← ha]
      exact ⟨hθ, hgap.le⟩
    · right
      have hθ : I.1.2 ≤ θ := (lt_of_not_ge hright).le
      have hgap := hnearGap
      rw [Near,
        ivlGap_eq_right
          (F.ordered I.1 I.property) hθ] at hgap
      rw [← hb]
      exact ⟨hθ, hgap.le⟩
  have hoff := SinIntgGrid.pr_grid_ivl_outside_near
    n hn a b hab hshort hside
  simpa only [prIntg, ha, hb] using hoff

theorem firstQuad_norm_bounds_of_decomposition {n : ℕ}
    (hn : 0 < n) (F : IvlFam n)
    (α : ↥F.base → ℝ)
    (hα : Disc.IsSign α)
    (principal : ↥F.base → ℝ → ℝ) (error : ℝ → ℝ)
    (hdecomposition : ∀ θ ∈ Icc 0 (π / 2),
      normTarget F α θ =
        (∑ I ∈ nearBaseIvls F θ,
          α I * principal I θ) + error θ)
    (herror : ∀ θ ∈ Icc 0 (π / 2),
      |error θ| ≤ 2 / 3)
    (hself_lower : ∀ θ ∈ Icc 0 (π / 2),
      ∀ I : ↥F.base, InIvl I.1 θ →
        4 / 3 ≤ |principal I θ|)
    (hself_upper : ∀ θ ∈ Icc 0 (π / 2),
      ∀ I : ↥F.base, InIvl I.1 θ →
        |principal I θ| ≤ 4)
    (hoff_upper : ∀ θ ∈ Icc 0 (π / 2),
      ∀ I ∈ nearBaseIvls F θ,
        ¬InIvl I.1 θ → |principal I θ| ≤ 2) :
    (∀ θ ∈ Icc 0 (π / 2), IsDangerous F θ →
      2 / 3 ≤ |normTarget F α θ|) ∧
    (∀ θ ∈ Icc 0 (π / 2),
      |normTarget F α θ| ≤ 14 / 3) := by
  classical
  have hα_abs (I : ↥F.base) : |α I| = 1 := by
    rcases hα I with hI | hI <;> simp [hI]
  constructor
  · intro θ hθ hdangerous
    obtain ⟨I, hθI, _hunique⟩ :=
      existsUnique_baseSubtype_of_dangerous_firstQuad
        hn F hθ hdangerous
    have hnear := sum_nearBaseIvls_eq_of_mem hn F
      I.property hθI (fun J ↦ α J * principal J θ)
    have hmainLower : 4 / 3 ≤ |α I * principal I θ| := by
      rw [abs_mul, hα_abs, one_mul]
      exact hself_lower θ hθ I hθI
    have hreverse : |α I * principal I θ| ≤
        |normTarget F α θ| + |error θ| := by
      rw [hdecomposition θ hθ, hnear]
      calc
        |α I * principal I θ| =
            |(α I * principal I θ + error θ) - error θ| := by
              ring_nf
        _ ≤ _ := abs_sub _ _
    linarith [herror θ hθ]
  · intro θ hθ
    have hmainUpper :
        |∑ I ∈ nearBaseIvls F θ,
          α I * principal I θ| ≤ 4 := by
      by_cases hin : InBaseUnion F θ
      · obtain ⟨I, hI, hθI⟩ := hin
        rw [sum_nearBaseIvls_eq_of_mem hn F hI hθI]
        rw [abs_mul, hα_abs, one_mul]
        exact hself_upper θ hθ ⟨I, hI⟩ hθI
      · have htwo :=
          abs_sum_nearBaseIvls_le_two_mul_of_not_inBaseUnion
            hn F hin (show (0 : ℝ) ≤ 2 by norm_num)
            (fun I ↦ α I * principal I θ) (by
              intro I hI
              rw [abs_mul, hα_abs, one_mul]
              exact hoff_upper θ hθ I hI
                (fun hmem ↦ hin ⟨I.1, I.property, hmem⟩))
        norm_num at htwo ⊢
        exact htwo
    rw [hdecomposition θ hθ]
    calc
      |(∑ I ∈ nearBaseIvls F θ,
            α I * principal I θ) + error θ| ≤
          |∑ I ∈ nearBaseIvls F θ,
            α I * principal I θ| + |error θ| := abs_add_le _ _
      _ ≤ 4 + 2 / 3 := add_le_add hmainUpper (herror θ hθ)
      _ = 14 / 3 := by norm_num

def concreteError {n : ℕ} (F : IvlFam n)
    (α : ↥F.base → ℝ) (θ : ℝ) : ℝ :=
  normTarget F α θ -
    ∑ I ∈ nearBaseIvls F θ,
      α I * prIntg n I.1 θ

theorem concrete_decomposition {n : ℕ} (F : IvlFam n)
    (α : ↥F.base → ℝ) (θ : ℝ) :
    normTarget F α θ =
      (∑ I ∈ nearBaseIvls F θ,
        α I * prIntg n I.1 θ) +
        concreteError F α θ := by
  simp only [concreteError]
  ring

theorem abs_concreteError_le_two_thirds {n : ℕ} (hn : 4096 ≤ n)
    (F : IvlFam n)
    (α : ↥F.base → ℝ)
    (hα : Disc.IsSign α) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (π / 2)) :
    |concreteError F α θ| ≤ 2 / 3 := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have htarget :=
    OddKernelId.targetSin_div_eq_sum_quotientIntg_of_theta_mem_Icc
      hnpos F α hθ
  rw [concreteError]
  change normTarget F α θ =
      ∑ I : ↥F.base, α I *
        ConcreteKernelClaims.quotientIntg n I.1 θ at htarget
  rw [htarget]
  exact ConcreteKernelClaims.signed_kernel_residual_le_two_thirds
    hn F α hα hθ

theorem concrete_firstQuad_norm_bounds {n : ℕ} (hn : 4096 ≤ n)
    (F : IvlFam n)
    (α : ↥F.base → ℝ)
    (hα : Disc.IsSign α) :
    (∀ θ ∈ Icc 0 (π / 2), IsDangerous F θ →
      2 / 3 ≤ |normTarget F α θ|) ∧
    (∀ θ ∈ Icc 0 (π / 2),
      |normTarget F α θ| ≤ 14 / 3) := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  apply firstQuad_norm_bounds_of_decomposition hnpos F α hα
    (fun I θ ↦ prIntg n I.1 θ)
    (concreteError F α)
  · exact fun θ _ ↦ concrete_decomposition F α θ
  · exact fun _ hθ ↦ abs_concreteError_le_two_thirds hn F α hα hθ
  · intro θ _ I hθ
    have hmain := prIntg_self_mem hnpos F I hθ
    rw [abs_of_nonneg (by linarith [hmain.1])]
    exact hmain.1
  · intro θ _ I hθ
    have hmain := prIntg_self_mem hnpos F I hθ
    rw [abs_of_nonneg (by linarith [hmain.1])]
    exact hmain.2
  · intro θ _ I hnear hout
    exact abs_prIntg_le_two_of_near_of_not_mem hnpos F I hnear hout

noncomputable def kernelCert {n : ℕ} (hn : 4096 ≤ n)
    (F : IvlFam n)
    (α : ↥F.base → ℝ)
    (hα : Disc.IsSign α) :
    KernelCert F α := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hfirst := concrete_firstQuad_norm_bounds hn F α hα
  have hglobal := norm_bounds_of_firstQuad F α hfirst.1 hfirst.2
  exact kernelCert_of_norm_bounds hnpos F α hglobal.1 hglobal.2

end

end KernelCert

end

section

namespace OddSine

open scoped BigOperators Interval
open Set

noncomputable section

def roundingMeshSize (n : ℕ) : ℕ := 16 * n

def roundingMeshPt (n : ℕ) (g : Fin (roundingMeshSize n)) : ℝ :=
  (2 * (g : ℕ) + 1 : ℕ) * π / (64 * n)

def roundingParam (l : ℕ) : ℝ :=
  14 * sqrt ((9 + l : ℕ) * log 2)

@[simp] theorem roundingMeshSize_eq (n : ℕ) : roundingMeshSize n = 16 * n := rfl

theorem roundingParam_nonneg (l : ℕ) : 0 ≤ roundingParam l :=
  mul_nonneg (by norm_num) (sqrt_nonneg _)

theorem roundingParam_sq (l : ℕ) :
    (roundingParam l) ^ 2 = 196 * ((9 + l : ℕ) * log 2) := by
  rw [roundingParam, mul_pow, sq_sqrt]
  · norm_num
  · exact mul_nonneg (by positivity) (log_nonneg (by norm_num))

theorem exp_roundingParam (l : ℕ) :
    Real.exp (-(roundingParam l) ^ 2 / 196) =
      (1 / 2 : ℝ) ^ (9 + l) := by
  rw [roundingParam_sq]
  have hcancel :
      -(196 * (((9 + l : ℕ) : ℝ) * log 2)) / 196 =
        -(((9 + l : ℕ) : ℝ) * log 2) := by ring
  rw [hcancel]
  calc
    Real.exp (-(((9 + l : ℕ) : ℝ) * log 2)) =
        Real.exp (((9 + l : ℕ) : ℝ) * (-log 2)) := by ring_nf
    _ = Real.exp (-log 2) ^ (9 + l) := Real.exp_nat_mul _ _
    _ = (1 / 2 : ℝ) ^ (9 + l) := by
      rw [Real.exp_neg, exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num

theorem sum_exp_roundingParam_le (n : ℕ) :
    (∑ l : Fin n, Real.exp (-(roundingParam l) ^ 2 / 196)) ≤
      (1 / 256 : ℝ) := by
  simp_rw [exp_roundingParam]
  calc
    (∑ l : Fin n, (1 / 2 : ℝ) ^ (9 + (l : ℕ))) =
        (1 / 512 : ℝ) * ∑ l : Fin n, (1 / 2 : ℝ) ^ (l : ℕ) := by
          simp_rw [pow_add]
          norm_num
          rw [Finset.mul_sum]
    _ ≤ (1 / 512 : ℝ) * 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [Fin.sum_univ_eq_sum_range]
      exact sum_geometric_two_le n
    _ = 1 / 256 := by norm_num

theorem roundingParam_add_thirty_le (l : ℕ) :
    roundingParam l + 30 ≤ 65 + 2 * l := by
  have htwo_exp : (2 : ℝ) < Real.exp (25 / 36) := by
    refine lt_of_lt_of_le ?_
      (Real.sum_le_exp_of_nonneg (x := (25 / 36 : ℝ)) (by norm_num) 5)
    norm_num [sum_range_succ, Nat.factorial]
  have hlog : log 2 < 25 / 36 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)]
    exact htwo_exp
  have hradicand :
      ((9 + l : ℕ) : ℝ) * log 2 ≤
        ((35 + 2 * (l : ℝ)) / 14) ^ 2 := by
    push_cast
    have hmul := mul_le_mul_of_nonneg_left (le_of_lt hlog)
      (show (0 : ℝ) ≤ ((9 + l : ℕ) : ℝ) by positivity)
    push_cast at hmul
    nlinarith [sq_nonneg (l : ℝ)]
  have hsqrt := sqrt_le_sqrt hradicand
  have hright : 0 ≤ (35 + 2 * (l : ℝ)) / 14 := by positivity
  rw [sqrt_sq hright] at hsqrt
  unfold roundingParam
  nlinarith

theorem exists_roundingMeshPt {n : ℕ} (hn : 0 < n) (θ : ℝ)
    (hθ : θ ∈ Icc 0 (π / 2)) :
    ∃ g : Fin (roundingMeshSize n),
      |θ - roundingMeshPt n g| ≤ π / (64 * n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpi : (0 : ℝ) < π := pi_pos
  have hmesh : 0 < roundingMeshSize n := by
    simp [roundingMeshSize, hn]
  by_cases hend : θ = π / 2
  · let g : Fin (roundingMeshSize n) :=
      ⟨roundingMeshSize n - 1, Nat.sub_lt hmesh (by omega)⟩
    refine ⟨g, ?_⟩
    have hsub : (roundingMeshSize n - 1 : ℕ) + 1 = roundingMeshSize n := by
      omega
    have hdifference :
        θ - roundingMeshPt n g = π / (64 * n) := by
      rw [hend]
      simp only [roundingMeshPt, g]
      rw [show 2 * (roundingMeshSize n - 1) + 1 =
          2 * roundingMeshSize n - 1 by omega]
      simp only [roundingMeshSize]
      push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * (16 * n))]
      field_simp
      ring
    rw [hdifference, abs_of_nonneg (by positivity)]
  · have hθ_lt : θ < π / 2 :=
      lt_of_le_of_ne hθ.2 hend
    let y : ℝ := θ * (32 * n) / π
    have hy_nonneg : 0 ≤ y := by
      exact div_nonneg (mul_nonneg hθ.1 (by positivity)) hpi.le
    have hy_lt : y < (roundingMeshSize n : ℕ) := by
      rw [roundingMeshSize]
      apply (div_lt_iff₀ hpi).2
      have hmul := mul_lt_mul_of_pos_right hθ_lt
        (show (0 : ℝ) < 32 * n by positivity)
      push_cast at hmul ⊢
      nlinarith
    let k : ℕ := ⌊y⌋₊
    have hk_le : (k : ℝ) ≤ y := Nat.floor_le hy_nonneg
    have hy_succ : y < (k : ℝ) + 1 := by
      simpa [k] using Nat.lt_floor_add_one y
    have hk_mesh : k < roundingMeshSize n := by
      exact_mod_cast lt_of_le_of_lt hk_le hy_lt
    let g : Fin (roundingMeshSize n) := ⟨k, hk_mesh⟩
    refine ⟨g, ?_⟩
    have habs : |y - ((k : ℝ) + 1 / 2)| ≤ 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith
    have hdifference :
        θ - roundingMeshPt n g =
          (y - ((k : ℝ) + 1 / 2)) * (π / (32 * n)) := by
      simp only [roundingMeshPt, g]
      dsimp only [y]
      push_cast
      field_simp
      ring
    rw [hdifference, abs_mul, abs_of_nonneg (by positivity :
      0 ≤ π / (32 * (n : ℝ)))]
    calc
      |y - ((k : ℝ) + 1 / 2)| * (π / (32 * n)) ≤
          (1 / 2) * (π / (32 * n)) :=
        mul_le_mul_of_nonneg_right habs (by positivity)
      _ = π / (64 * n) := by ring

def explicitRoundingSetup {n : ℕ} (hn : 0 < n) :
    RoundingSetup n (Fin (roundingMeshSize n)) where
  point := roundingMeshPt n
  parameter := fun q ↦ roundingParam q.2
  parameter_nonneg := fun q ↦ roundingParam_nonneg q.2
  budget := by
    rw [Fintype.sum_prod_type]
    simp only
    calc
      (∑ _g : Fin (roundingMeshSize n),
          ∑ l : Fin n, Real.exp (-(roundingParam l) ^ 2 / 196)) =
          (roundingMeshSize n : ℝ) *
            ∑ l : Fin n, Real.exp (-(roundingParam l) ^ 2 / 196) := by
        simp only [Finset.sum_const, Finset.card_univ, card_fin,
          nsmul_eq_mul]
      _ ≤ (roundingMeshSize n : ℝ) * (1 / 256 : ℝ) := by
        apply mul_le_mul_of_nonneg_left (sum_exp_roundingParam_le n)
        positivity
      _ = (n : ℝ) / 16 := by
        simp [roundingMeshSize]
        ring
  parameter_bound := fun _g l ↦ roundingParam_add_thirty_le l
  cover := by
    intro a θ
    obtain ⟨θ', hθ', habs⟩ :=
      exists_firstQuad_abs_oddSinSum_eq n a θ
    obtain ⟨g, hnear⟩ := exists_roundingMeshPt hn θ' hθ'
    exact ⟨g, θ', hnear, habs⟩

theorem exists_roundingSetup {n : ℕ} (hn : 0 < n) :
    Nonempty (RoundingSetup n (Fin (16 * n))) :=
  ⟨explicitRoundingSetup hn⟩

end

end OddSine

end

section

open Filter Set
open scoped BigOperators Topology

noncomputable section

namespace Disc

variable {I J : Type*} [Fintype I] [Fintype J]

def approxFixCoords [DecidableEq I]
    (ε : ℝ) (x : I → ℝ) : Finset I :=
  Finset.univ.filter fun i ↦ 1 - ε ≤ |x i|

@[simp]
theorem mem_approxFixCoords [DecidableEq I]
    {ε : ℝ} {x : I → ℝ} {i : I} :
    i ∈ approxFixCoords ε x ↔ 1 - ε ≤ |x i| := by
  simp [approxFixCoords]

omit [Fintype I] in

theorem isCompact_inCube : IsCompact {x : I → ℝ | InCube x} := by
  have hset : {x : I → ℝ | InCube x} =
      Set.pi Set.univ (fun _ : I ↦ Set.Icc (-1 : ℝ) 1) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const, mem_Icc]
    constructor
    · intro hx i
      simpa only [abs_le] using hx i
    · intro hx i
      simpa only [abs_le] using hx i
  rw [hset]
  exact isCompact_univ_pi fun _ ↦ isCompact_Icc

omit [Fintype J] in

theorem hasPartialColoring_of_approx [DecidableEq I]
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ x : I → ℝ,
        InCube x ∧
          Fintype.card I ≤
            2 * (approxFixCoords ε x).card ∧
          ∀ j, |dot (x - x₀) (v j)| ≤ c j * l2Norm (v j)) :
    HasPartialColoring v x₀ c := by
  let ε : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hε_pos (n : ℕ) : 0 < ε n := by
    dsimp only [ε]
    positivity
  have hwitness : ∀ n : ℕ, ∃ x : I → ℝ,
      InCube x ∧
        Fintype.card I ≤
          2 * (approxFixCoords (ε n) x).card ∧
        ∀ j, |dot (x - x₀) (v j)| ≤ c j * l2Norm (v j) := by
    intro n
    exact happrox (ε n) (hε_pos n)
  choose x hxCube hxCard hxDiscrepancy using hwitness
  obtain ⟨xLimit, hxLimitCube, phi, hphi, hxLimit⟩ :=
    isCompact_inCube.tendsto_subseq hxCube
  refine ⟨xLimit, hxLimitCube, ?_, ?_⟩
  · have hε_tendsto :
        Tendsto ε atTop (nhds (0 : ℝ)) := by
      simpa only [ε, Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (nhds 0))
    have hε_subseq :
        Tendsto (fun n ↦ ε (phi n)) atTop (nhds (0 : ℝ)) :=
      hε_tendsto.comp hphi.tendsto_atTop
    have hxCoordinate (i : I) :
        Tendsto (fun n ↦ x (phi n) i) atTop (nhds (xLimit i)) :=
      tendsto_pi_nhds.mp hxLimit i
    have hnotApprox (i : I) (hi : i ∉ fixCoords xLimit) :
        ∀ᶠ n in atTop,
          i ∉ approxFixCoords (ε (phi n)) (x (phi n)) := by
      have habs_le : |xLimit i| ≤ 1 := hxLimitCube i
      have habs_ne : |xLimit i| ≠ 1 := by
        simpa [fixCoords] using hi
      have hgap : 0 < 1 - |xLimit i| := sub_pos.mpr (lt_of_le_of_ne habs_le habs_ne)
      have htendsto :
          Tendsto
            (fun n ↦ 1 - ε (phi n) - |x (phi n) i|)
            atTop (nhds (1 - |xLimit i|)) := by
        simpa using
          (tendsto_const_nhds.sub hε_subseq).sub
            ((hxCoordinate i).abs)
      have hpositive :
          ∀ᶠ n in atTop, 0 < 1 - ε (phi n) - |x (phi n) i| :=
        htendsto.eventually (isOpen_Ioi.mem_nhds hgap)
      filter_upwards [hpositive] with n hn
      simp only [mem_approxFixCoords, not_le]
      linarith
    have hsubset_eventually :
        ∀ᶠ n in atTop,
          approxFixCoords (ε (phi n)) (x (phi n)) ⊆
            fixCoords xLimit := by
      have hall :
          ∀ᶠ n in atTop, ∀ i : I,
            i ∈ approxFixCoords (ε (phi n)) (x (phi n)) →
              i ∈ fixCoords xLimit := by
        apply Filter.eventually_all.mpr
        intro i
        by_cases hfixed : i ∈ fixCoords xLimit
        · exact Eventually.of_forall fun _ _ ↦ hfixed
        · exact (hnotApprox i hfixed).mono fun _ hnot hmem ↦
            False.elim (hnot hmem)
      exact hall.mono fun _ hn _ hi ↦ hn _ hi
    obtain ⟨n, hsubset⟩ := hsubset_eventually.exists
    have hcardSubset := Finset.card_le_card hsubset
    exact (hxCard (phi n)).trans (Nat.mul_le_mul_left 2 hcardSubset)
  · intro j
    have hxCoordinate (i : I) :
        Tendsto (fun n ↦ x (phi n) i) atTop (nhds (xLimit i)) :=
      tendsto_pi_nhds.mp hxLimit i
    have hdot :
        Tendsto (fun n ↦ dot (x (phi n) - x₀) (v j)) atTop
          (nhds (dot (xLimit - x₀) (v j))) := by
      unfold dot
      apply tendsto_finsetSum
      intro i hi
      exact ((hxCoordinate i).sub tendsto_const_nhds).mul_const (v j i)
    exact le_of_tendsto' hdot.abs fun n ↦ hxDiscrepancy (phi n) j

end Disc

end
end

section

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal

noncomputable section

namespace EdgeWalk

open Disc GaussianWalk ProjWalk

variable {I J : Type*} [Fintype I] [Fintype J]

abbrev toWalk (v : I → ℝ) : WalkSp I := WithLp.toLp 2 v

theorem norm_walkSp_sq (v : WalkSp I) :
    ‖v‖ ^ 2 = ∑ i, v i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [norm_eq_abs, sq_abs]

theorem l2Norm_eq_norm (v : I → ℝ) : l2Norm v = ‖toWalk v‖ := by
  rw [l2Norm, EuclideanSpace.norm_eq]
  simp only [PiLp.toLp_apply, norm_eq_abs, sq_abs]

theorem dot_eq_inner (x v : I → ℝ) :
    dot x v = inner ℝ (toWalk v) (toWalk x) := by
  simp [dot, toWalk, EuclideanSpace.inner_eq_star_dotProduct,
    RCLike.star_def, dotProduct, mul_comm]

def normConstr (v : I → ℝ) : WalkSp I :=
  (l2Norm v)⁻¹ • toWalk v

theorem norm_normConstr_le_one (v : I → ℝ) :
    ‖normConstr v‖ ≤ 1 := by
  by_cases hv : l2Norm v = 0
  · simp [normConstr, hv]
  · rw [normConstr, norm_smul, norm_eq_abs,
      abs_inv, l2Norm_eq_norm]
    have hnorm : ‖toWalk v‖ ≠ 0 := by
      rw [← l2Norm_eq_norm]
      exact hv
    rw [abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hnorm]

def scDisc (v : I → ℝ) (x₀ : I → ℝ)
    (x : WalkSp I) : ℝ :=
  inner ℝ (normConstr v) (x - toWalk x₀)

theorem scDisc_mul_l2Norm {v : I → ℝ}
    (hv : 0 < l2Norm v) (x₀ : I → ℝ) (x : WalkSp I) :
    scDisc v x₀ x * l2Norm v =
      dot (fun i ↦ x i - x₀ i) v := by
  calc
    scDisc v x₀ x * l2Norm v =
        inner ℝ (toWalk v) (x - toWalk x₀) := by
      rw [scDisc, normConstr, inner_smul_left]
      simp only [starRingEnd_apply, star_trivial]
      field_simp [hv.ne']
    _ = inner ℝ (toWalk v) (toWalk (fun i ↦ x i - x₀ i)) := by
      congr 1
    _ = dot (fun i ↦ x i - x₀ i) v :=
      (dot_eq_inner _ _).symm

def actCoords [DecidableEq I] (δ : ℝ) (x : WalkSp I) : Finset I :=
  Finset.univ.filter fun i ↦ 1 - δ ≤ |x i|

def actDiscrepancies [DecidableEq J] (δ : ℝ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSp I) : Finset J :=
  Finset.univ.filter fun j ↦
    0 < l2Norm (v j) ∧ c j - δ ≤ |scDisc (v j) x₀ x|

@[simp] theorem mem_actCoords [DecidableEq I]
    {δ : ℝ} {x : WalkSp I} {i : I} :
    i ∈ actCoords δ x ↔ 1 - δ ≤ |x i| := by
  simp [actCoords]

@[simp] theorem mem_actDiscrepancies [DecidableEq J]
    {δ : ℝ} {v : J → I → ℝ} {x₀ : I → ℝ} {c : J → ℝ}
    {x : WalkSp I} {j : J} :
    j ∈ actDiscrepancies δ v x₀ c x ↔
      0 < l2Norm (v j) ∧
        c j - δ ≤ |scDisc (v j) x₀ x| := by
  simp [actDiscrepancies]

def sampVec (ω : I → ℝ) : WalkSp I := toWalk ω

def projectedCoeffs (K : Submodule ℝ (WalkSp I))
    (v : WalkSp I) : I → ℝ := fun i ↦ K.starProjection v i

theorem inner_starProj_samp_eq_sum
    (K : Submodule ℝ (WalkSp I)) (v : WalkSp I) (ω : I → ℝ) :
    inner ℝ v (K.starProjection (sampVec ω)) =
      ∑ i, projectedCoeffs K v i * ω i := by
  rw [real_inner_comm, K.inner_starProjection_left_eq_right, real_inner_comm]
  simp [PiLp.inner_apply, projectedCoeffs, sampVec, toWalk, mul_comm]

theorem integrable_exp_inner_starProj_samp
    (K : Submodule ℝ (WalkSp I)) (v : WalkSp I) (t : ℝ) :
    Integrable (fun ω : I → ℝ ↦
      exp (t * inner ℝ v (K.starProjection (sampVec ω))))
      (radLaw I) := by
  rw [show (fun ω : I → ℝ ↦
      exp (t * inner ℝ v (K.starProjection (sampVec ω)))) =
      (fun ω ↦ exp (t * ∑ i, projectedCoeffs K v i * ω i)) by
    funext ω
    rw [inner_starProj_samp_eq_sum]]
  exact (hasSubgaussianMGF_wtedRadSum I
    (projectedCoeffs K v)).integrable_exp_mul t

theorem sum_projectedCoeffs_sq
    (K : Submodule ℝ (WalkSp I)) (v : WalkSp I) :
    ∑ i, projectedCoeffs K v i ^ 2 = ‖K.starProjection v‖ ^ 2 := by
  simpa [projectedCoeffs, EuclideanSpace.norm_sq_eq]

theorem sum_projectedCoeffs_sq_le
    (K : Submodule ℝ (WalkSp I)) (v : WalkSp I) :
    ∑ i, projectedCoeffs K v i ^ 2 ≤ ‖v‖ ^ 2 := by
  rw [sum_projectedCoeffs_sq]
  nlinarith [norm_nonneg (K.starProjection v), norm_nonneg v,
    K.norm_starProjection_apply_le v]

theorem intg_exp_inner_starProj_samp_le
    (K : Submodule ℝ (WalkSp I)) (v : WalkSp I) (t : ℝ) :
    ∫ ω : I → ℝ,
        exp (t * inner ℝ v (K.starProjection (sampVec ω)))
      ∂(radLaw I) ≤ exp (t ^ 2 * ‖v‖ ^ 2 / 2) := by
  rw [show (fun ω : I → ℝ ↦
      exp (t * inner ℝ v (K.starProjection (sampVec ω)))) =
      (fun ω ↦ exp (t * ∑ i, projectedCoeffs K v i * ω i)) by
    funext ω
    rw [inner_starProj_samp_eq_sum]]
  have hmgf := (hasSubgaussianMGF_wtedRadSum I
    (projectedCoeffs K v)).mgf_le t
  rw [mgf] at hmgf
  let q : I → ℝ≥0 := fun i ↦ ⟨projectedCoeffs K v i ^ 2,
    sq_nonneg (projectedCoeffs K v i)⟩
  let variance : ℝ≥0 := ∑ i, q i
  change (∫ ω : I → ℝ,
      exp (t * ∑ i, projectedCoeffs K v i * ω i)
    ∂(radLaw I)) ≤ exp ((variance : ℝ) * t ^ 2 / 2) at hmgf
  have hcoe : (variance : ℝ) = ∑ i, projectedCoeffs K v i ^ 2 := by
    calc
      (variance : ℝ) = ↑(∑ i, q i) := rfl
      _ = ∑ i, (q i : ℝ) := by
        simpa using NNReal.coe_sum Finset.univ q
      _ = ∑ i, projectedCoeffs K v i ^ 2 := by
        apply sum_congr rfl
        intro i hi
        rfl
  calc
    ∫ ω : I → ℝ,
        exp (t * ∑ i, projectedCoeffs K v i * ω i)
      ∂(radLaw I) ≤
        exp ((variance : ℝ) * t ^ 2 / 2) := hmgf
    _ ≤ exp (t ^ 2 * ‖v‖ ^ 2 / 2) := by
      apply exp_le_exp.mpr
      rw [hcoe]
      nlinarith [sum_projectedCoeffs_sq_le K v, sq_nonneg t]

theorem memLp_id_radMeasure : MemLp id 2 radMeasure := by
  exact memLp_of_bounded ae_mem_Icc_radMeasure
    measurable_id.aestronglyMeasurable 2

theorem memLp_wted_rad_coord (a : I → ℝ) (i : I) :
    MemLp (fun ω : I → ℝ ↦ a i * ω i) 2 (radLaw I) := by
  exact (memLp_id_radMeasure.comp_measurePreserving
    (measurePreserving_eval (μ := fun _ : I ↦ radMeasure) i)).const_mul (a i)

theorem intg_wted_rad_sum (a : I → ℝ) :
    ∫ ω, (∑ i, a i * ω i) ∂radLaw I = 0 := by
  rw [integral_finset_sum]
  · apply sum_eq_zero
    intro i hi
    rw [integral_const_mul]
    have hmap : (radLaw I).map (fun ω : I → ℝ ↦ ω i) =
        radMeasure := by
      unfold radLaw
      exact (measurePreserving_eval (μ := fun _ : I ↦ radMeasure) i).map_eq
    rw [← integral_map (μ := radLaw I) (f := fun x : ℝ ↦ x)
      (measurable_pi_apply i).aemeasurable measurable_id.aestronglyMeasurable, hmap]
    rw [intg_id_radMeasure]
    ring
  · intro i hi
    exact (memLp_wted_rad_coord a i).integrable (by norm_num)

theorem intg_inner_starProj_samp_eq_zero
    (K : Submodule ℝ (WalkSp I)) (v : WalkSp I) :
    ∫ ω, inner ℝ v (K.starProjection (sampVec ω))
      ∂radLaw I = 0 := by
  simp_rw [inner_starProj_samp_eq_sum]
  exact intg_wted_rad_sum (projectedCoeffs K v)

theorem memLp_wted_rad_sum (a : I → ℝ) :
    MemLp (fun ω : I → ℝ ↦ ∑ i, a i * ω i) 2
      (radLaw I) := by
  have h := memLp_finsetSum Finset.univ
    (fun i _ ↦ memLp_wted_rad_coord a i)
  simpa only [Finset.sum_apply] using h

theorem intg_sq_wted_rad_sum (a : I → ℝ) :
    ∫ ω, (∑ i, a i * ω i) ^ 2 ∂radLaw I = ∑ i, a i ^ 2 := by
  have hvar : Var[fun ω : I → ℝ ↦ ∑ i, a i * ω i;
      radLaw I] = ∑ i, a i ^ 2 := by
    have hfun : (fun ω : I → ℝ ↦ ∑ i, a i * ω i) =
        ∑ i, fun ω : I → ℝ ↦ a i * ω i := by
      funext ω
      simp
    rw [hfun]
    unfold radLaw
    rw [variance_sum_pi]
    · apply sum_congr rfl
      intro i hi
      rw [variance_const_mul]
      have hid : Var[id; radMeasure] = 1 := by
        rw [variance_eq_sub memLp_id_radMeasure]
        simp only [Pi.pow_apply, id_eq, intg_id_radMeasure, sub_zero]
        have hsq : (fun x : ℝ ↦ x ^ 2) =ᵐ[radMeasure] fun _ ↦ 1 := by
          filter_upwards [ae_abs_eq_one_radMeasure] with x hx
          rw [← sq_abs, hx]
          norm_num
        rw [integral_congr_ae hsq]
        simp
      change a i ^ 2 * Var[id; radMeasure] = a i ^ 2
      rw [hid, mul_one]
    · intro i
      exact memLp_id_radMeasure.const_mul (a i)
  rw [← hvar]
  rw [variance_of_integral_eq_zero]
  · exact (Finset.measurable_fun_sum Finset.univ fun i _ ↦
      measurable_const.mul (measurable_pi_apply i)).aemeasurable
  · exact intg_wted_rad_sum a

theorem norm_sq_starProj_eq_sum_inner_sq
    (K : Submodule ℝ (WalkSp I)) (ω : I → ℝ) :
    ‖K.starProjection (sampVec ω)‖ ^ 2 =
      ∑ k : Fin (Module.finrank ℝ K),
        inner ℝ ((stdOrthonormalBasis ℝ K k : K) : WalkSp I)
          (sampVec ω) ^ 2 := by
  let b : OrthonormalBasis (Fin (Module.finrank ℝ K)) ℝ K :=
    stdOrthonormalBasis ℝ K
  let y : K := ⟨K.starProjection (sampVec ω),
    K.starProjection_apply_mem (sampVec ω)⟩
  change ‖y‖ ^ 2 = _
  rw [← real_inner_self_eq_norm_sq y, ← b.sum_inner_mul_inner y y]
  apply sum_congr rfl
  intro k hk
  have hproj : inner ℝ (b k) y =
      inner ℝ ((b k : K) : WalkSp I) (sampVec ω) := by
    change inner ℝ (b k) (K.orthogonalProjectionOnto (sampVec ω)) = _
    exact K.inner_orthogonalProjectionOnto_eq_of_mem_left (b k) (sampVec ω)
  have hcomm : inner ℝ y (b k) = inner ℝ (b k) y :=
    (real_inner_comm y (b k)).symm
  rw [hcomm, hproj]
  ring

theorem intg_norm_sq_starProj (K : Submodule ℝ (WalkSp I)) :
    ∫ ω, ‖K.starProjection (sampVec ω)‖ ^ 2
      ∂radLaw I = (Module.finrank ℝ K : ℝ) := by
  simp_rw [norm_sq_starProj_eq_sum_inner_sq K]
  rw [integral_finsetSum]
  · have hsquare (w : WalkSp I) :
        ∫ ω, inner ℝ w (sampVec ω) ^ 2 ∂radLaw I = ‖w‖ ^ 2 := by
      simp_rw [show ∀ ω, inner ℝ w (sampVec ω) =
          ∑ i, w i * ω i by
        intro ω
        simp [PiLp.inner_apply, sampVec, toWalk, mul_comm]]
      rw [intg_sq_wted_rad_sum]
      exact (EuclideanSpace.real_norm_sq_eq w).symm
    simp_rw [hsquare]
    calc
      (∑ k : Fin (Module.finrank ℝ K),
          ‖((stdOrthonormalBasis ℝ K k : K) : WalkSp I)‖ ^ 2) =
          ∑ _k : Fin (Module.finrank ℝ K), (1 : ℝ) := by
        apply sum_congr rfl
        intro k hk
        change ‖stdOrthonormalBasis ℝ K k‖ ^ 2 = 1
        rw [OrthonormalBasis.norm_eq_one]
        norm_num
      _ = (Module.finrank ℝ K : ℝ) := by simp
  · intro k hk
    have hmem : MemLp
        (fun ω ↦ inner ℝ
          ((stdOrthonormalBasis ℝ K k : K) : WalkSp I) (sampVec ω))
        2 (radLaw I) := by
      simp_rw [show ∀ ω, inner ℝ
          ((stdOrthonormalBasis ℝ K k : K) : WalkSp I) (sampVec ω) =
          ∑ i, (((stdOrthonormalBasis ℝ K k : K) : WalkSp I) i) * ω i by
        intro ω
        simp [PiLp.inner_apply, sampVec, toWalk, mul_comm]]
      exact memLp_wted_rad_sum _
    exact hmem.integrable_sq

variable [DecidableEq I] [DecidableEq J]

def edgeSubsp (δ : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSp I) : Submodule ℝ (WalkSp I) :=
  tightIncsubsp (fun j ↦ normConstr (v j))
    (actCoords δ x) (actDiscrepancies δ v x₀ c x)

def edgeInc (δ : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSp I) (ω : I → ℝ) : WalkSp I :=
  (edgeSubsp δ v x₀ c x).starProjection (sampVec ω)

def edgeStep (δ γ : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSp I) (ω : I → ℝ) : WalkSp I :=
  x + γ • edgeInc δ v x₀ c x ω

theorem edgeInc_mem (δ : ℝ) (v : J → I → ℝ)
    (x₀ : I → ℝ) (c : J → ℝ) (x : WalkSp I) (ω : I → ℝ) :
    edgeInc δ v x₀ c x ω ∈ edgeSubsp δ v x₀ c x :=
  (edgeSubsp δ v x₀ c x).starProjection_apply_mem _

theorem edgeInc_apply_eq_zero_of_act
    (δ : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSp I) (ω : I → ℝ)
    {i : I} (hi : i ∈ actCoords δ x) :
    edgeInc δ v x₀ c x ω i = 0 := by
  exact (mem_tightIncsubsp_iff
    (fun j ↦ normConstr (v j))
    (actCoords δ x) (actDiscrepancies δ v x₀ c x) _).1
      (edgeInc_mem δ v x₀ c x ω) |>.1 i hi

theorem inner_edgeInc_eq_zero_of_act
    (δ : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSp I) (ω : I → ℝ)
    {j : J} (hj : j ∈ actDiscrepancies δ v x₀ c x) :
    inner ℝ (normConstr (v j))
      (edgeInc δ v x₀ c x ω) = 0 := by
  exact (mem_tightIncsubsp_iff
    (fun j ↦ normConstr (v j))
    (actCoords δ x) (actDiscrepancies δ v x₀ c x) _).1
      (edgeInc_mem δ v x₀ c x ω) |>.2 j hj

theorem norm_edgeInc_le (δ : ℝ) (v : J → I → ℝ)
    (x₀ : I → ℝ) (c : J → ℝ) (x : WalkSp I) (ω : I → ℝ) :
    ‖edgeInc δ v x₀ c x ω‖ ≤ ‖sampVec ω‖ :=
  (edgeSubsp δ v x₀ c x).norm_starProjection_apply_le _

theorem norm_sampVec_sq_of_signs {ω : I → ℝ}
    (hω : ∀ i, |ω i| = 1) :
    ‖sampVec ω‖ ^ 2 = Fintype.card I := by
  rw [norm_walkSp_sq]
  simp only [sampVec, toWalk, PiLp.toLp_apply]
  calc
    ∑ i, ω i ^ 2 = ∑ _i : I, (1 : ℝ) := by
      apply sum_congr rfl
      intro i hi
      nlinarith [sq_abs (ω i), hω i]
    _ = Fintype.card I := by simp

theorem norm_sampVec_le_sqrt_card {ω : I → ℝ}
    (hω : ∀ i, |ω i| = 1) :
    ‖sampVec ω‖ ≤ sqrt (Fintype.card I) := by
  have hsq := norm_sampVec_sq_of_signs hω
  rw [← sqrt_sq (norm_nonneg _), hsq]

theorem scDisc_edgeStep
    (δ γ : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSp I) (ω : I → ℝ) (j : J) :
    scDisc (v j) x₀ (edgeStep δ γ v x₀ c x ω) =
      scDisc (v j) x₀ x +
        γ * inner ℝ (normConstr (v j))
          (edgeInc δ v x₀ c x ω) := by
  rw [scDisc, scDisc, edgeStep]
  have hsub : x + γ • edgeInc δ v x₀ c x ω - toWalk x₀ =
      (x - toWalk x₀) + γ • edgeInc δ v x₀ c x ω := by
    abel
  rw [hsub, inner_add_right, inner_smul_right]

def entropyWt (a : ℝ) : ℝ := exp (-a ^ 2 / 16)

def signedRowPot (sigma γ : ℝ) (t : ℕ) (a y : ℝ) : ℝ :=
  entropyWt a *
    exp (sigma * (a / 5) * y - (a / 5) ^ 2 * γ ^ 2 * t / 2)

def rowPot (γ : ℝ) (t : ℕ) (a y : ℝ) : ℝ :=
  signedRowPot 1 γ t a y + signedRowPot (-1) γ t a y

def discPot (γ : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSp I) : ℝ :=
  ∑ j, rowPot γ t (c j) (scDisc (v j) x₀ x)

def edgeScore (γ : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSp I) : ℝ :=
  ‖x‖ ^ 2 - 5 * discPot γ t v x₀ c x

theorem discPot_zero (γ : ℝ) (v : J → I → ℝ)
    (x₀ : I → ℝ) (c : J → ℝ) :
    discPot γ 0 v x₀ c (toWalk x₀) =
      2 * ∑ j, entropyWt (c j) := by
  simp [discPot, rowPot, signedRowPot,
    scDisc, entropyWt, Finset.mul_sum, two_mul]

theorem signedRowPot_nonneg (sigma γ : ℝ) (t : ℕ) (a y : ℝ) :
    0 ≤ signedRowPot sigma γ t a y :=
  mul_nonneg (le_of_lt (exp_pos _)) (le_of_lt (exp_pos _))

theorem rowPot_nonneg (γ : ℝ) (t : ℕ) (a y : ℝ) :
    0 ≤ rowPot γ t a y :=
  add_nonneg (signedRowPot_nonneg _ _ _ _ _)
    (signedRowPot_nonneg _ _ _ _ _)

theorem intg_signedRowPot_step_le
    (sigma γ δ : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSp I) (j : J) (hsigma : sigma ^ 2 = 1) :
    ∫ ω,
        signedRowPot sigma γ (t + 1) (c j)
          (scDisc (v j) x₀
            (edgeStep δ γ v x₀ c x ω))
      ∂radLaw I ≤
        signedRowPot sigma γ t (c j)
          (scDisc (v j) x₀ x) := by
  let S := edgeSubsp δ v x₀ c x
  let w := normConstr (v j)
  let a := c j / 5
  let y := scDisc (v j) x₀ x
  let q := sigma * a * γ
  let base := sigma * a * y - a ^ 2 * γ ^ 2 * t / 2 -
    a ^ 2 * γ ^ 2 / 2
  let B := entropyWt (c j) * exp base
  have hrewrite (ω : I → ℝ) :
      signedRowPot sigma γ (t + 1) (c j)
          (scDisc (v j) x₀
            (edgeStep δ γ v x₀ c x ω)) =
        B * exp (q * inner ℝ w (S.starProjection (sampVec ω))) := by
    rw [scDisc_edgeStep]
    unfold signedRowPot
    change entropyWt (c j) * exp _ =
      (entropyWt (c j) * exp base) * exp _
    calc
      entropyWt (c j) * exp _ =
          entropyWt (c j) *
            (exp base * exp (q * inner ℝ w
              (S.starProjection (sampVec ω)))) := by
        congr 1
        rw [← exp_add]
        congr 1
        dsimp only [base, a, y, q, S, w, edgeInc]
        push_cast
        ring
      _ = (entropyWt (c j) * exp base) *
          exp (q * inner ℝ w (S.starProjection (sampVec ω))) := by
        ring
  simp_rw [hrewrite]
  rw [integral_const_mul]
  have hB : 0 ≤ B := mul_nonneg (le_of_lt (exp_pos _)) (le_of_lt (exp_pos _))
  calc
    B * ∫ ω, exp (q * inner ℝ w (S.starProjection (sampVec ω)))
        ∂radLaw I ≤ B * exp (q ^ 2 * ‖w‖ ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left
        (intg_exp_inner_starProj_samp_le S w q) hB
    _ ≤ B * exp (q ^ 2 / 2) := by
      gcongr
      have hwSq : ‖w‖ ^ 2 ≤ 1 := by
        nlinarith [mul_self_le_mul_self (norm_nonneg w)
          (norm_normConstr_le_one (v j))]
      nlinarith [hwSq, sq_nonneg q]
    _ = signedRowPot sigma γ t (c j) y := by
      dsimp only [B, base, q, a]
      unfold signedRowPot
      rw [mul_assoc, ← exp_add]
      congr 2
      push_cast
      nlinarith

theorem integrable_signedRowPot_step
    (sigma γ δ : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSp I) (j : J) :
    Integrable (fun ω ↦
      signedRowPot sigma γ (t + 1) (c j)
        (scDisc (v j) x₀
          (edgeStep δ γ v x₀ c x ω)))
      (radLaw I) := by
  let S := edgeSubsp δ v x₀ c x
  let w := normConstr (v j)
  let q := sigma * (c j / 5) * γ
  let base := sigma * (c j / 5) * scDisc (v j) x₀ x -
    (c j / 5) ^ 2 * γ ^ 2 * t / 2 -
    (c j / 5) ^ 2 * γ ^ 2 / 2
  let B := entropyWt (c j) * exp base
  have heq : (fun ω ↦
      signedRowPot sigma γ (t + 1) (c j)
        (scDisc (v j) x₀
          (edgeStep δ γ v x₀ c x ω))) =
      (fun ω ↦ B * exp (q * inner ℝ w
        (S.starProjection (sampVec ω)))) := by
    funext ω
    rw [scDisc_edgeStep]
    unfold signedRowPot
    change entropyWt (c j) * exp _ =
      (entropyWt (c j) * exp base) * exp _
    calc
      entropyWt (c j) * exp _ =
          entropyWt (c j) *
            (exp base * exp (q * inner ℝ w
              (S.starProjection (sampVec ω)))) := by
        congr 1
        rw [← exp_add]
        congr 1
        dsimp only [base, q, S, w, edgeInc]
        push_cast
        ring
      _ = (entropyWt (c j) * exp base) *
          exp (q * inner ℝ w (S.starProjection (sampVec ω))) := by
        ring
  rw [heq]
  exact (integrable_exp_inner_starProj_samp S w q).const_mul B

theorem intg_rowPot_step_le
    (γ δ : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSp I) (j : J) :
    ∫ ω,
        rowPot γ (t + 1) (c j)
          (scDisc (v j) x₀
            (edgeStep δ γ v x₀ c x ω))
      ∂radLaw I ≤
        rowPot γ t (c j)
          (scDisc (v j) x₀ x) := by
  unfold rowPot
  rw [integral_add]
  · exact add_le_add
      (intg_signedRowPot_step_le 1 γ δ t v x₀ c x j (by norm_num))
      (intg_signedRowPot_step_le (-1) γ δ t v x₀ c x j (by norm_num))
  · exact integrable_signedRowPot_step 1 γ δ t v x₀ c x j
  · exact integrable_signedRowPot_step (-1) γ δ t v x₀ c x j

theorem integrable_discPot_step
    (γ δ : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSp I) :
    Integrable (fun ω ↦ discPot γ (t + 1) v x₀ c
      (edgeStep δ γ v x₀ c x ω)) (radLaw I) := by
  unfold discPot
  exact integrable_finset_sum Finset.univ fun j hj ↦
    integrable_signedRowPot_step 1 γ δ t v x₀ c x j |>.add
      (integrable_signedRowPot_step (-1) γ δ t v x₀ c x j)

theorem intg_discPot_step_le
    (γ δ : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSp I) :
    ∫ ω, discPot γ (t + 1) v x₀ c
        (edgeStep δ γ v x₀ c x ω)
      ∂radLaw I ≤ discPot γ t v x₀ c x := by
  unfold discPot
  rw [integral_finsetSum]
  exact sum_le_sum fun j hj ↦
    intg_rowPot_step_le γ δ t v x₀ c x j
  intro j hj
  exact (integrable_signedRowPot_step 1 γ δ t v x₀ c x j).add
    (integrable_signedRowPot_step (-1) γ δ t v x₀ c x j)

theorem integrable_inner_starProj_samp
    (K : Submodule ℝ (WalkSp I)) (v : WalkSp I) :
    Integrable (fun ω ↦ inner ℝ v (K.starProjection (sampVec ω)))
      (radLaw I) := by
  simp_rw [inner_starProj_samp_eq_sum]
  exact (memLp_wted_rad_sum (projectedCoeffs K v)).integrable
    (by norm_num)

theorem integrable_norm_sq_starProj
    (K : Submodule ℝ (WalkSp I)) :
    Integrable (fun ω ↦ ‖K.starProjection (sampVec ω)‖ ^ 2)
      (radLaw I) := by
  simp_rw [norm_sq_starProj_eq_sum_inner_sq K]
  exact integrable_finset_sum Finset.univ fun k hk ↦
    ((memLp_wted_rad_sum
      (fun i ↦ (((stdOrthonormalBasis ℝ K k : K) : WalkSp I) i))).integrable_sq.congr
        (Filter.Eventually.of_forall fun ω ↦ by
          congr 1
          simp [PiLp.inner_apply, sampVec, toWalk, mul_comm]))

theorem norm_edgeStep_sq
    (γ δ : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSp I) (ω : I → ℝ) :
    ‖edgeStep δ γ v x₀ c x ω‖ ^ 2 = ‖x‖ ^ 2 +
      2 * γ * inner ℝ x (edgeInc δ v x₀ c x ω) +
      γ ^ 2 * ‖edgeInc δ v x₀ c x ω‖ ^ 2 := by
  rw [edgeStep, norm_add_sq_real]
  simp only [norm_smul, norm_eq_abs, inner_smul_right,
    starRingEnd_apply, star_trivial]
  rw [mul_pow, sq_abs]
  ring

theorem intg_norm_edgeStep_sq
    (γ δ : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSp I) :
    ∫ ω, ‖edgeStep δ γ v x₀ c x ω‖ ^ 2
      ∂radLaw I = ‖x‖ ^ 2 +
        γ ^ 2 * Module.finrank ℝ (edgeSubsp δ v x₀ c x) := by
  simp_rw [norm_edgeStep_sq]
  have hconst : Integrable (fun _omega : I → ℝ ↦ ‖x‖ ^ 2)
      (radLaw I) := integrable_const _
  have hlinear : Integrable (fun ω : I → ℝ ↦
      2 * γ * inner ℝ x (edgeInc δ v x₀ c x ω))
      (radLaw I) :=
    (integrable_inner_starProj_samp
      (edgeSubsp δ v x₀ c x) x).const_mul (2 * γ)
  have hquadratic : Integrable (fun ω : I → ℝ ↦
      γ ^ 2 * ‖edgeInc δ v x₀ c x ω‖ ^ 2)
      (radLaw I) :=
    (integrable_norm_sq_starProj
      (edgeSubsp δ v x₀ c x)).const_mul (γ ^ 2)
  have hzero : ∫ ω,
      inner ℝ x (edgeInc δ v x₀ c x ω)
        ∂radLaw I = 0 := by
    exact intg_inner_starProj_samp_eq_zero
      (edgeSubsp δ v x₀ c x) x
  have hsquare : ∫ ω,
      ‖edgeInc δ v x₀ c x ω‖ ^ 2
        ∂radLaw I =
        (Module.finrank ℝ (edgeSubsp δ v x₀ c x) : ℝ) := by
    exact intg_norm_sq_starProj (edgeSubsp δ v x₀ c x)
  have hmeasure : (radLaw I).real Set.univ = 1 := by
    rw [Measure.real, IsProbabilityMeasure.measure_univ, ENNReal.toReal_one]
  rw [integral_add]
  · rw [integral_add]
    · rw [integral_const, integral_const_mul,
    hzero, mul_zero, integral_const_mul, hsquare]
      rw [hmeasure]
      simp only [mul_one, add_zero]
      ring
    · exact hconst
    · exact hlinear
  · exact hconst.add hlinear
  · exact hquadratic

theorem integrable_norm_edgeStep_sq
    (γ δ : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSp I) :
    Integrable (fun ω ↦ ‖edgeStep δ γ v x₀ c x ω‖ ^ 2)
      (radLaw I) := by
  simp_rw [norm_edgeStep_sq]
  exact (integrable_const _).add
    ((integrable_inner_starProj_samp
      (edgeSubsp δ v x₀ c x) x).const_mul (2 * γ)) |>.add
        ((integrable_norm_sq_starProj
          (edgeSubsp δ v x₀ c x)).const_mul (γ ^ 2))

theorem integrable_edgeScore_step
    (γ δ : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSp I) :
    Integrable (fun ω ↦ edgeScore γ (t + 1) v x₀ c
      (edgeStep δ γ v x₀ c x ω)) (radLaw I) := by
  unfold edgeScore
  exact (integrable_norm_edgeStep_sq γ δ v x₀ c x).sub
    ((integrable_discPot_step γ δ t v x₀ c x).const_mul 5)

theorem intg_edgeScore_step_ge
    (γ δ : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSp I) :
    edgeScore γ t v x₀ c x +
        γ ^ 2 * Module.finrank ℝ (edgeSubsp δ v x₀ c x) ≤
      ∫ ω, edgeScore γ (t + 1) v x₀ c
        (edgeStep δ γ v x₀ c x ω) ∂radLaw I := by
  rw [edgeScore]
  simp_rw [edgeScore]
  rw [integral_sub, integral_const_mul, intg_norm_edgeStep_sq]
  · have hp := intg_discPot_step_le γ δ t v x₀ c x
    linarith
  · exact integrable_norm_edgeStep_sq γ δ v x₀ c x
  · exact (integrable_discPot_step γ δ t v x₀ c x).const_mul 5

theorem measure_not_signs_eq_zero :
    radLaw I {ω | ¬ ∀ i, |ω i| = 1} = 0 := by
  rw [← ae_iff]
  simpa only [Set.mem_setOf_eq, not_not] using
    (ae_forall_abs_eq_one_radLaw I)

theorem exists_sign_edgeScore_step
    (γ δ : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSp I) :
    ∃ ω : I → ℝ, (∀ i, |ω i| = 1) ∧
      edgeScore γ t v x₀ c x +
          γ ^ 2 * Module.finrank ℝ (edgeSubsp δ v x₀ c x) ≤
        edgeScore γ (t + 1) v x₀ c
          (edgeStep δ γ v x₀ c x ω) := by
  let N : Set (I → ℝ) := {ω | ¬ ∀ i, |ω i| = 1}
  obtain ⟨ω, hωN, hω⟩ :=
    exists_notMem_null_integral_le
      (μ := radLaw I)
      (f := fun ω ↦ edgeScore γ (t + 1) v x₀ c
        (edgeStep δ γ v x₀ c x ω))
      (integrable_edgeScore_step γ δ t v x₀ c x)
      (show radLaw I N = 0 by exact measure_not_signs_eq_zero)
  refine ⟨ω, ?_, (intg_edgeScore_step_ge γ δ t v x₀ c x).trans hω⟩
  simpa only [N, Set.mem_setOf_eq, not_not] using hωN

end EdgeWalk

end
end

section

open Real Set
open scoped BigOperators

noncomputable section

namespace EdgeWalk

open Disc ProjWalk

universe u v

variable {I : Type u} {J : Type v} [Fintype I] [Fintype J]
variable [DecidableEq I] [DecidableEq J]

def edgeChoice (γ δ : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSp I) : I → ℝ :=
  Classical.choose (exists_sign_edgeScore_step γ δ t v x₀ c x)

theorem edgeChoice_isSign (γ δ : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSp I) :
    ∀ i, |edgeChoice γ δ t v x₀ c x i| = 1 :=
  (Classical.choose_spec
    (exists_sign_edgeScore_step γ δ t v x₀ c x)).1

theorem edgeChoice_score (γ δ : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSp I) :
    edgeScore γ t v x₀ c x +
        γ ^ 2 * Module.finrank ℝ (edgeSubsp δ v x₀ c x) ≤
      edgeScore γ (t + 1) v x₀ c
        (edgeStep δ γ v x₀ c x
          (edgeChoice γ δ t v x₀ c x)) :=
  (Classical.choose_spec
    (exists_sign_edgeScore_step γ δ t v x₀ c x)).2

def edgeWalk (δ γ : ℝ) (v : J → I → ℝ)
    (x₀ : I → ℝ) (c : J → ℝ) : ℕ → WalkSp I
  | 0 => toWalk x₀
  | t + 1 => edgeStep δ γ v x₀ c (edgeWalk δ γ v x₀ c t)
      (edgeChoice γ δ t v x₀ c (edgeWalk δ γ v x₀ c t))

@[simp] theorem edgeWalk_zero (δ γ : ℝ) (v : J → I → ℝ)
    (x₀ : I → ℝ) (c : J → ℝ) :
    edgeWalk δ γ v x₀ c 0 = toWalk x₀ := rfl

@[simp] theorem edgeWalk_succ (δ γ : ℝ) (v : J → I → ℝ)
    (x₀ : I → ℝ) (c : J → ℝ) (t : ℕ) :
    edgeWalk δ γ v x₀ c (t + 1) =
      edgeStep δ γ v x₀ c (edgeWalk δ γ v x₀ c t)
        (edgeChoice γ δ t v x₀ c (edgeWalk δ γ v x₀ c t)) := rfl

theorem edgeWalk_score_step (δ γ : ℝ) (v : J → I → ℝ)
    (x₀ : I → ℝ) (c : J → ℝ) (t : ℕ) :
    edgeScore γ t v x₀ c (edgeWalk δ γ v x₀ c t) +
        γ ^ 2 * Module.finrank ℝ
          (edgeSubsp δ v x₀ c (edgeWalk δ γ v x₀ c t)) ≤
      edgeScore γ (t + 1) v x₀ c
        (edgeWalk δ γ v x₀ c (t + 1)) := by
  simpa only [edgeWalk_succ] using
    edgeChoice_score γ δ t v x₀ c (edgeWalk δ γ v x₀ c t)

theorem abs_apply_le_norm_walkSp (x : WalkSp I) (i : I) :
    |x i| ≤ ‖x‖ := by
  have hi : x i ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [norm_walkSp_sq]
    exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (x j)) (Finset.mem_univ i)
  nlinarith [sq_abs (x i), abs_nonneg (x i), norm_nonneg x]

theorem abs_edgeInc_le_sqrt_card
    (δ : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSp I) (ω : I → ℝ)
    (hω : ∀ i, |ω i| = 1) (i : I) :
    |edgeInc δ v x₀ c x ω i| ≤
      sqrt (Fintype.card I) := by
  exact (abs_apply_le_norm_walkSp _ i).trans
    ((norm_edgeInc_le δ v x₀ c x ω).trans
      (norm_sampVec_le_sqrt_card hω))

theorem abs_inner_edgeInc_le_sqrt_card
    (δ : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSp I) (ω : I → ℝ)
    (hω : ∀ i, |ω i| = 1) (j : J) :
    |inner ℝ (normConstr (v j))
        (edgeInc δ v x₀ c x ω)| ≤
      sqrt (Fintype.card I) := by
  calc
    |inner ℝ (normConstr (v j))
        (edgeInc δ v x₀ c x ω)| ≤
        ‖normConstr (v j)‖ *
          ‖edgeInc δ v x₀ c x ω‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ 1 * sqrt (Fintype.card I) := by
      gcongr
      · exact norm_normConstr_le_one (v j)
      · exact (norm_edgeInc_le δ v x₀ c x ω).trans
          (norm_sampVec_le_sqrt_card hω)
    _ = sqrt (Fintype.card I) := one_mul _

theorem edgeStep_inCube
    (δ γ : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSp I) (ω : I → ℝ)
    (hx : InCube x) (hω : ∀ i, |ω i| = 1)
    (hγ : 0 ≤ γ)
    (hδ : δ = γ * sqrt (Fintype.card I)) :
    InCube (edgeStep δ γ v x₀ c x ω) := by
  intro i
  by_cases hi : i ∈ actCoords δ x
  · rw [edgeStep]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      edgeInc_apply_eq_zero_of_act δ v x₀ c x ω hi,
      mul_zero, add_zero]
    exact hx i
  · have hxi : |x i| < 1 - δ := by
      simpa only [mem_actCoords, not_le] using hi
    have hinc := abs_edgeInc_le_sqrt_card
      δ v x₀ c x ω hω i
    rw [edgeStep]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    calc
      |x i + γ * edgeInc δ v x₀ c x ω i| ≤
          |x i| + |γ * edgeInc δ v x₀ c x ω i| :=
        abs_add_le _ _
      _ = |x i| + γ * |edgeInc δ v x₀ c x ω i| := by
        rw [abs_mul, abs_of_nonneg hγ]
      _ ≤ |x i| + γ * sqrt (Fintype.card I) := by gcongr
      _ ≤ 1 := by rw [← hδ]; linarith

theorem edgeStep_scDisc_le
    (δ γ : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSp I) (ω : I → ℝ)
    (hx : ∀ j, |scDisc (v j) x₀ x| ≤ c j)
    (hω : ∀ i, |ω i| = 1) (hγ : 0 ≤ γ)
    (hδ : δ = γ * sqrt (Fintype.card I)) :
    ∀ j, |scDisc (v j) x₀
      (edgeStep δ γ v x₀ c x ω)| ≤ c j := by
  intro j
  by_cases hv : l2Norm (v j) = 0
  · simpa [scDisc, normConstr, hv] using hx j
  by_cases hj : j ∈ actDiscrepancies δ v x₀ c x
  · rw [scDisc_edgeStep,
      inner_edgeInc_eq_zero_of_act δ v x₀ c x ω hj,
      mul_zero, add_zero]
    exact hx j
  · have hvpos : 0 < l2Norm (v j) :=
      lt_of_le_of_ne (sqrt_nonneg _) (Ne.symm hv)
    have hy : |scDisc (v j) x₀ x| < c j - δ := by
      simpa only [mem_actDiscrepancies, hvpos, true_and, not_le] using hj
    have hinc := abs_inner_edgeInc_le_sqrt_card
      δ v x₀ c x ω hω j
    rw [scDisc_edgeStep]
    calc
      |scDisc (v j) x₀ x + γ *
          inner ℝ (normConstr (v j))
            (edgeInc δ v x₀ c x ω)| ≤
          |scDisc (v j) x₀ x| +
            |γ * inner ℝ (normConstr (v j))
              (edgeInc δ v x₀ c x ω)| := abs_add_le _ _
      _ = |scDisc (v j) x₀ x| + γ *
            |inner ℝ (normConstr (v j))
              (edgeInc δ v x₀ c x ω)| := by
        rw [abs_mul, abs_of_nonneg hγ]
      _ ≤ |scDisc (v j) x₀ x| +
            γ * sqrt (Fintype.card I) := by gcongr
      _ ≤ c j := by rw [← hδ]; linarith

theorem edgeWalk_inCube
    (δ γ : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (hx₀ : InCube x₀) (hγ : 0 ≤ γ)
    (hδ : δ = γ * sqrt (Fintype.card I)) :
    ∀ t, InCube (edgeWalk δ γ v x₀ c t) := by
  intro t
  induction t with
  | zero => simpa [edgeWalk] using hx₀
  | succ t ht =>
      rw [edgeWalk_succ]
      exact edgeStep_inCube δ γ v x₀ c _ _ ht
        (edgeChoice_isSign γ δ t v x₀ c _) hγ hδ

theorem edgeWalk_scDisc_le
    (δ γ : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (hc : ∀ j, 0 ≤ c j) (hγ : 0 ≤ γ)
    (hδ : δ = γ * sqrt (Fintype.card I)) :
    ∀ t j, |scDisc (v j) x₀
      (edgeWalk δ γ v x₀ c t)| ≤ c j := by
  intro t
  induction t with
  | zero =>
      intro j
      simpa [edgeWalk, scDisc] using hc j
  | succ t ht =>
      rw [edgeWalk_succ]
      exact edgeStep_scDisc_le δ γ v x₀ c _ _ ht
        (edgeChoice_isSign γ δ t v x₀ c _) hγ hδ

theorem actCoords_mono_edgeStep
    (δ γ : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSp I) (ω : I → ℝ) :
    actCoords δ x ⊆
      actCoords δ (edgeStep δ γ v x₀ c x ω) := by
  intro i hi
  rw [mem_actCoords]
  rw [edgeStep]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    edgeInc_apply_eq_zero_of_act δ v x₀ c x ω hi,
    mul_zero, add_zero]
  exact mem_actCoords.mp hi

theorem actDiscrepancies_mono_edgeStep
    (δ γ : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSp I) (ω : I → ℝ) :
    actDiscrepancies δ v x₀ c x ⊆
      actDiscrepancies δ v x₀ c
        (edgeStep δ γ v x₀ c x ω) := by
  intro j hj
  rw [mem_actDiscrepancies]
  have hj' := (mem_actDiscrepancies.mp hj)
  refine ⟨hj'.1, ?_⟩
  rw [scDisc_edgeStep,
    inner_edgeInc_eq_zero_of_act δ v x₀ c x ω hj,
    mul_zero, add_zero]
  exact hj'.2

theorem actCoords_mono_edgeWalk
    (δ γ : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) {s t : ℕ} (hst : s ≤ t) :
    actCoords δ (edgeWalk δ γ v x₀ c s) ⊆
      actCoords δ (edgeWalk δ γ v x₀ c t) := by
  induction t, hst using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ t hst ih =>
      exact ih.trans (by
        rw [edgeWalk_succ]
        exact actCoords_mono_edgeStep δ γ v x₀ c _ _)

theorem actDiscrepancies_mono_edgeWalk
    (δ γ : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) {s t : ℕ} (hst : s ≤ t) :
    actDiscrepancies δ v x₀ c (edgeWalk δ γ v x₀ c s) ⊆
      actDiscrepancies δ v x₀ c (edgeWalk δ γ v x₀ c t) := by
  induction t, hst using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ t hst ih =>
      exact ih.trans (by
        rw [edgeWalk_succ]
        exact actDiscrepancies_mono_edgeStep δ γ v x₀ c _ _)

theorem one_le_rowPot_of_near_boundary
    (γ δ : ℝ) (t : ℕ) (a y : ℝ)
    (ha : 0 ≤ a) (hδ : 0 ≤ δ) (hδSmall : δ ≤ 1 / 4)
    (htime : γ ^ 2 * (t : ℝ) ≤ 5)
    (hnear : a - δ ≤ |y|) :
    1 ≤ rowPot γ t a y := by
  let Q : ℝ := (a / 5) ^ 2 * γ ^ 2 * (t : ℝ) / 2
  have hQ : Q ≤ a ^ 2 / 10 := by
    have hmul := mul_le_mul_of_nonneg_left htime
      (div_nonneg (sq_nonneg (a / 5)) (by norm_num : (0 : ℝ) ≤ 2))
    dsimp only [Q]
    nlinarith
  by_cases hlarge : 16 * δ ≤ 3 * a
  · have hprod : 16 * a * δ ≤ 3 * a ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hlarge ha]
    by_cases hy : 0 ≤ y
    · have hay : a - δ ≤ y := by simpa [abs_of_nonneg hy] using hnear
      have haymul : a * (a - δ) ≤ a * y :=
        mul_le_mul_of_nonneg_left hay ha
      have hexponent :
          0 ≤ -a ^ 2 / 16 + a / 5 * y - Q := by
        nlinarith
      have hone : 1 ≤ signedRowPot 1 γ t a y := by
        rw [signedRowPot, entropyWt, ← exp_add]
        have heq : -a ^ 2 / 16 +
            (1 * (a / 5) * y - (a / 5) ^ 2 * γ ^ 2 * (t : ℝ) / 2) =
            -a ^ 2 / 16 + a / 5 * y - Q := by
          dsimp only [Q]
          ring
        rw [heq]
        simpa only [exp_zero] using exp_le_exp.mpr hexponent
      exact hone.trans (le_add_of_nonneg_right
        (signedRowPot_nonneg (-1) γ t a y))
    · have hy' : y ≤ 0 := le_of_not_ge hy
      have hay : a - δ ≤ -y := by simpa [abs_of_nonpos hy'] using hnear
      have haymul : a * (a - δ) ≤ a * (-y) :=
        mul_le_mul_of_nonneg_left hay ha
      have hexponent :
          0 ≤ -a ^ 2 / 16 + (-1) * (a / 5) * y - Q := by
        nlinarith
      have hone : 1 ≤ signedRowPot (-1) γ t a y := by
        rw [signedRowPot, entropyWt, ← exp_add]
        have heq : -a ^ 2 / 16 +
            ((-1) * (a / 5) * y - (a / 5) ^ 2 * γ ^ 2 * (t : ℝ) / 2) =
            -a ^ 2 / 16 + (-1) * (a / 5) * y - Q := by
          dsimp only [Q]
          ring
        rw [heq]
        simpa only [exp_zero] using exp_le_exp.mpr hexponent
      exact hone.trans (le_add_of_nonneg_left
        (signedRowPot_nonneg 1 γ t a y))
  · have haUpper : a < 4 / 3 := by
      have : 3 * a < 16 * δ := lt_of_not_ge hlarge
      nlinarith
    have haSq : 13 * a ^ 2 / 80 ≤ 1 / 2 := by
      nlinarith [sq_nonneg (a - 4 / 3)]
    have hbase : -1 / 2 ≤ -a ^ 2 / 16 - Q := by
      nlinarith
    let z : ℝ := a / 5 * y
    let base : ℝ := -a ^ 2 / 16 - Q
    have hsum : 1 ≤ (1 + (base + z)) + (1 + (base - z)) := by
      dsimp only [base]
      nlinarith
    calc
      1 ≤ (1 + (base + z)) + (1 + (base - z)) := hsum
      _ ≤ exp (base + z) + exp (base - z) :=
        add_le_add (by simpa [add_comm] using add_one_le_exp (base + z))
          (by simpa [add_comm] using add_one_le_exp (base - z))
      _ = rowPot γ t a y := by
        unfold rowPot signedRowPot entropyWt
        rw [← exp_add, ← exp_add]
        dsimp only [base, z, Q]
        congr 1 <;> ring

theorem edgeWalk_score_sum
    (δ γ : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (t : ℕ) :
    edgeScore γ 0 v x₀ c (toWalk x₀) +
        γ ^ 2 * ∑ s ∈ Finset.range t,
          (Module.finrank ℝ
            (edgeSubsp δ v x₀ c (edgeWalk δ γ v x₀ c s)) : ℝ) ≤
      edgeScore γ t v x₀ c (edgeWalk δ γ v x₀ c t) := by
  induction t with
  | zero => simp
  | succ t ht =>
      rw [sum_range_succ]
      calc
        edgeScore γ 0 v x₀ c (toWalk x₀) + γ ^ 2 *
            ((∑ s ∈ Finset.range t,
              (Module.finrank ℝ (edgeSubsp δ v x₀ c
                (edgeWalk δ γ v x₀ c s)) : ℝ)) +
              (Module.finrank ℝ (edgeSubsp δ v x₀ c
                (edgeWalk δ γ v x₀ c t)) : ℝ)) =
            (edgeScore γ 0 v x₀ c (toWalk x₀) + γ ^ 2 *
              ∑ s ∈ Finset.range t,
                (Module.finrank ℝ (edgeSubsp δ v x₀ c
                  (edgeWalk δ γ v x₀ c s)) : ℝ)) +
              γ ^ 2 * (Module.finrank ℝ (edgeSubsp δ v x₀ c
                (edgeWalk δ γ v x₀ c t)) : ℝ) := by ring
        _ ≤ edgeScore γ t v x₀ c (edgeWalk δ γ v x₀ c t) +
              γ ^ 2 * (Module.finrank ℝ (edgeSubsp δ v x₀ c
                (edgeWalk δ γ v x₀ c t)) : ℝ) :=
          add_le_add ht (le_refl _)
        _ ≤ edgeScore γ (t + 1) v x₀ c
              (edgeWalk δ γ v x₀ c (t + 1)) :=
          edgeWalk_score_step δ γ v x₀ c t

theorem card_le_finrank_add_act
    (δ : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSp I) :
    Fintype.card I ≤
      Module.finrank ℝ (edgeSubsp δ v x₀ c x) +
        (actCoords δ x).card +
        (actDiscrepancies δ v x₀ c x).card := by
  have h := card_sub_tight_card_le_finrank
    (fun j ↦ normConstr (v j))
    (actCoords δ x) (actDiscrepancies δ v x₀ c x)
  change Fintype.card I -
      ((actCoords δ x).card +
        (actDiscrepancies δ v x₀ c x).card) ≤
    Module.finrank ℝ (edgeSubsp δ v x₀ c x) at h
  omega

theorem card_actDiscrepancies_le_pot
    (γ δ : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ) (x : WalkSp I)
    (hc : ∀ j, 0 ≤ c j) (hδ : 0 ≤ δ)
    (hδSmall : δ ≤ 1 / 4)
    (htime : γ ^ 2 * (t : ℝ) ≤ 5) :
    ((actDiscrepancies δ v x₀ c x).card : ℝ) ≤
      discPot γ t v x₀ c x := by
  let A := actDiscrepancies δ v x₀ c x
  calc
    (A.card : ℝ) = ∑ _j ∈ A, (1 : ℝ) := by simp [A]
    _ ≤ ∑ j ∈ A,
        rowPot γ t (c j) (scDisc (v j) x₀ x) := by
      apply sum_le_sum
      intro j hj
      exact one_le_rowPot_of_near_boundary γ δ t (c j)
        (scDisc (v j) x₀ x) (hc j) hδ hδSmall htime
        ((mem_actDiscrepancies.mp hj).2)
    _ ≤ ∑ j,
        rowPot γ t (c j) (scDisc (v j) x₀ x) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
        (fun j hj₁ hj₂ ↦ rowPot_nonneg γ t (c j)
          (scDisc (v j) x₀ x))
    _ = discPot γ t v x₀ c x := rfl

theorem norm_sq_le_card_of_inCube (x : WalkSp I) (hx : InCube x) :
    ‖x‖ ^ 2 ≤ Fintype.card I := by
  rw [norm_walkSp_sq]
  calc
    ∑ i, x i ^ 2 ≤ ∑ _i : I, (1 : ℝ) := by
      apply sum_le_sum
      intro i hi
      have hsq := mul_self_le_mul_self (abs_nonneg (x i)) (hx i)
      nlinarith [sq_abs (x i)]
    _ = Fintype.card I := by simp

theorem edgeWalk_terminal_half
    (δ γ : ℝ) (T : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (hx₀ : InCube x₀) (hc : ∀ j, 0 ≤ c j)
    (hentropy : (∑ j, exp (-(c j) ^ 2 / 16)) ≤
      (Fintype.card I : ℝ) / 16)
    (hγ : 0 ≤ γ)
    (hδEq : δ = γ * sqrt (Fintype.card I))
    (hδ : 0 ≤ δ) (hδSmall : δ ≤ 1 / 4)
    (htime : γ ^ 2 * (T : ℝ) = 5) :
    Fintype.card I ≤ 2 *
      (actCoords δ (edgeWalk δ γ v x₀ c T)).card := by
  let xT := edgeWalk δ γ v x₀ c T
  let C := (actCoords δ xT).card
  let D := (actDiscrepancies δ v x₀ c xT).card
  let N : ℝ := Fintype.card I
  by_contra hhalf
  have hClt : 2 * C < Fintype.card I := by
    exact Nat.lt_of_not_ge hhalf
  have hNpos : 0 < N := by
    dsimp only [N]
    exact_mod_cast (lt_of_le_of_lt (Nat.zero_le (2 * C)) hClt)
  have hrank (s : ℕ) (hs : s ∈ Finset.range T) :
      N - C - D ≤
        (Module.finrank ℝ
          (edgeSubsp δ v x₀ c (edgeWalk δ γ v x₀ c s)) : ℝ) := by
    have hsT : s ≤ T := Nat.le_of_lt (Finset.mem_range.mp hs)
    have hcoord := Finset.card_le_card
      (actCoords_mono_edgeWalk δ γ v x₀ c hsT)
    have hdisc := Finset.card_le_card
      (actDiscrepancies_mono_edgeWalk δ γ v x₀ c hsT)
    have hdim := card_le_finrank_add_act δ v x₀ c
      (edgeWalk δ γ v x₀ c s)
    have hcoordR :
        ((actCoords δ (edgeWalk δ γ v x₀ c s)).card : ℝ) ≤ C := by
      exact_mod_cast hcoord
    have hdiscR :
        ((actDiscrepancies δ v x₀ c
          (edgeWalk δ γ v x₀ c s)).card : ℝ) ≤ D := by
      exact_mod_cast hdisc
    have hdimR : N ≤
        (Module.finrank ℝ
          (edgeSubsp δ v x₀ c (edgeWalk δ γ v x₀ c s)) : ℝ) +
        (actCoords δ (edgeWalk δ γ v x₀ c s)).card +
        (actDiscrepancies δ v x₀ c
          (edgeWalk δ γ v x₀ c s)).card := by
      dsimp only [N]
      exact_mod_cast hdim
    linarith
  have hrankSum : (T : ℝ) * (N - C - D) ≤
      ∑ s ∈ Finset.range T,
        (Module.finrank ℝ
          (edgeSubsp δ v x₀ c (edgeWalk δ γ v x₀ c s)) : ℝ) := by
    calc
      (T : ℝ) * (N - C - D) =
          ∑ _s ∈ Finset.range T, (N - C - D) := by
        simp
        ring
      _ ≤ _ := sum_le_sum fun s hs ↦ hrank s hs
  have hscore := edgeWalk_score_sum δ γ v x₀ c T
  have hprogress :
      edgeScore γ 0 v x₀ c (toWalk x₀) + 5 * (N - C - D) ≤
        edgeScore γ T v x₀ c xT := by
    have hmul := mul_le_mul_of_nonneg_left hrankSum (sq_nonneg γ)
    calc
      edgeScore γ 0 v x₀ c (toWalk x₀) + 5 * (N - C - D) =
          edgeScore γ 0 v x₀ c (toWalk x₀) +
            γ ^ 2 * ((T : ℝ) * (N - C - D)) := by
        rw [← htime]
        ring
      _ ≤ edgeScore γ 0 v x₀ c (toWalk x₀) + γ ^ 2 *
          ∑ s ∈ Finset.range T,
            (Module.finrank ℝ (edgeSubsp δ v x₀ c
              (edgeWalk δ γ v x₀ c s)) : ℝ) := by linarith
      _ ≤ edgeScore γ T v x₀ c xT := hscore
  have hD : (D : ℝ) ≤ discPot γ T v x₀ c xT := by
    exact card_actDiscrepancies_le_pot γ δ T v x₀ c xT hc
      hδ hδSmall htime.le
  have hP0 : discPot γ 0 v x₀ c (toWalk x₀) ≤ N / 8 := by
    rw [discPot_zero]
    change 2 * ∑ j, exp (-(c j) ^ 2 / 16) ≤ N / 8
    linarith
  have hxTCube : InCube xT :=
    edgeWalk_inCube δ γ v x₀ c hx₀ hγ hδEq T
  have hxTNorm : ‖xT‖ ^ 2 ≤ N :=
    norm_sq_le_card_of_inCube xT hxTCube
  have hx₀Norm : 0 ≤ ‖toWalk x₀‖ ^ 2 := sq_nonneg _
  have hlower : -5 * (N / 8) + 5 * (N - C) ≤ ‖xT‖ ^ 2 := by
    dsimp only [xT] at hprogress hD hxTNorm ⊢
    simp only [edgeScore] at hprogress
    nlinarith
  have hCltR : 2 * (C : ℝ) < N := by
    dsimp only [N]
    exact_mod_cast hClt
  nlinarith

theorem exists_walk_params (ε : ℝ) (hε : 0 < ε) :
    ∃ q : ℕ, 0 < q ∧
      let γ : ℝ := 1 / (q : ℝ)
      let δ : ℝ := γ * sqrt (Fintype.card I)
      let T : ℕ := 5 * q ^ 2
      0 ≤ γ ∧ 0 ≤ δ ∧ δ ≤ 1 / 4 ∧ δ ≤ ε ∧
        γ ^ 2 * (T : ℝ) = 5 := by
  obtain ⟨q, hq⟩ := exists_nat_gt
    (max 1 (max (4 * sqrt (Fintype.card I))
      (sqrt (Fintype.card I) / ε)))
  have hqOne : (1 : ℝ) < q := lt_of_le_of_lt (le_max_left _ _) hq
  have hqposR : (0 : ℝ) < q := lt_trans (by norm_num) hqOne
  have hqpos : 0 < q := by exact_mod_cast hqposR
  have hqFour : 4 * sqrt (Fintype.card I) < (q : ℝ) := by
    exact lt_of_le_of_lt (le_trans (le_max_left _ _)
      (le_max_right 1 _)) hq
  have hqEpsilon : sqrt (Fintype.card I) / ε < (q : ℝ) := by
    exact lt_of_le_of_lt (le_trans (le_max_right _ _)
      (le_max_right _ _)) hq
  refine ⟨q, hqpos, ?_⟩
  dsimp only
  have hγ : 0 ≤ (1 : ℝ) / q := by positivity
  have hδ : 0 ≤ (1 / (q : ℝ)) * sqrt (Fintype.card I) := by positivity
  have hδForm : (1 / (q : ℝ)) * sqrt (Fintype.card I) =
      sqrt (Fintype.card I) / q := by ring
  have hδSmall : (1 / (q : ℝ)) * sqrt (Fintype.card I) ≤ 1 / 4 := by
    rw [hδForm, div_le_iff₀ hqposR]
    nlinarith
  have hδEpsilon :
      (1 / (q : ℝ)) * sqrt (Fintype.card I) ≤ ε := by
    rw [hδForm, div_le_iff₀ hqposR]
    have hsqrt : sqrt (Fintype.card I) < (q : ℝ) * ε := by
      have := (div_lt_iff₀ hε).mp hqEpsilon
      nlinarith
    linarith
  refine ⟨hγ, hδ, hδSmall, hδEpsilon, ?_⟩
  push_cast
  field_simp

theorem exists_approx_partialColoring
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (hx₀ : InCube x₀) (hc : ∀ j, 0 ≤ c j)
    (hentropy : (∑ j, exp (-(c j) ^ 2 / 16)) ≤
      (Fintype.card I : ℝ) / 16)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ x : I → ℝ,
      InCube x ∧
        Fintype.card I ≤ 2 * (approxFixCoords ε x).card ∧
        ∀ j, |dot (x - x₀) (v j)| ≤ c j * l2Norm (v j) := by
  obtain ⟨q, hq, hγ, hδ, hδSmall, hδEpsilon, htime⟩ :=
    exists_walk_params (I := I) ε hε
  let γ : ℝ := 1 / (q : ℝ)
  let δ : ℝ := γ * sqrt (Fintype.card I)
  let T : ℕ := 5 * q ^ 2
  let xT : WalkSp I := edgeWalk δ γ v x₀ c T
  have hγ' : 0 ≤ γ := hγ
  have hδ' : 0 ≤ δ := hδ
  have hδSmall' : δ ≤ 1 / 4 := hδSmall
  have hδEpsilon' : δ ≤ ε := hδEpsilon
  have htime' : γ ^ 2 * (T : ℝ) = 5 := htime
  have hhalf : Fintype.card I ≤
      2 * (actCoords δ xT).card := by
    exact edgeWalk_terminal_half δ γ T v x₀ c hx₀ hc hentropy
      hγ' rfl hδ' hδSmall' htime'
  have hxTCube : InCube xT :=
    edgeWalk_inCube δ γ v x₀ c hx₀ hγ' rfl T
  have hnormalized : ∀ j,
      |scDisc (v j) x₀ xT| ≤ c j :=
    edgeWalk_scDisc_le δ γ v x₀ c hc hγ' rfl T
  let x : I → ℝ := fun i ↦ xT i
  refine ⟨x, hxTCube, ?_, ?_⟩
  · have hsubset : actCoords δ xT ⊆
        approxFixCoords ε x := by
      intro i hi
      rw [mem_approxFixCoords]
      have hi' := mem_actCoords.mp hi
      dsimp only [x]
      linarith
    exact hhalf.trans (Nat.mul_le_mul_left 2 (Finset.card_le_card hsubset))
  · intro j
    by_cases hv : l2Norm (v j) = 0
    · rw [dot_eq_zero_of_l2Norm_eq_zero (x - x₀) (v j) hv, hv]
      simp
    · have hvpos : 0 < l2Norm (v j) :=
        lt_of_le_of_ne (sqrt_nonneg _) (Ne.symm hv)
      have hscale := scDisc_mul_l2Norm hvpos x₀ xT
      have hnormNonneg : 0 ≤ l2Norm (v j) := sqrt_nonneg _
      change |dot (fun i ↦ xT i - x₀ i) (v j)| ≤ c j * l2Norm (v j)
      rw [← hscale, abs_mul, abs_of_nonneg hnormNonneg]
      exact mul_le_mul_of_nonneg_right (hnormalized j) hnormNonneg

omit [DecidableEq J] in

theorem partialColoringPrinciple (I : Type u) (J : Type v)
    [Fintype I] [Fintype J] [DecidableEq I] :
    PartialColoringPrinciple I J := by
  letI : DecidableEq J := Classical.decEq J
  intro v x₀ c hx₀ hc hentropy
  apply hasPartialColoring_of_approx v x₀ c
  intro ε hε
  exact exists_approx_partialColoring v x₀ c hx₀ hc hentropy ε hε

end EdgeWalk

end
end

section

open scoped BigOperators

noncomputable section

structure PairSignData (n : ℕ) where
  C : Finset ℕ
  Se : Finset ℕ
  So : Finset ℕ
  cover : C ∪ Se ∪ So = Finset.Icc 1 (2 * n)
  disjoint_C_Se : Disjoint C Se
  disjoint_C_So : Disjoint C So
  disjoint_Se_So : Disjoint Se So
  epsC : ℕ → ℝ
  epsE : ℕ → ℝ
  epsO : ℕ → ℝ
  epsC_isSign : ∀ k ∈ C, epsC k = 1 ∨ epsC k = -1
  epsE_isSign : ∀ k ∈ Se, epsE k = 1 ∨ epsE k = -1
  epsO_isSign : ∀ k ∈ So, epsO k = 1 ∨ epsO k = -1

def PairSignData.posCoeff {n : ℕ} (D : PairSignData n)
    (k : ℕ) : ℂ :=
  if k ∈ D.C then D.epsC k
  else if k ∈ D.Se then D.epsE k
  else D.epsO k

def PairSignData.negCoeff {n : ℕ} (D : PairSignData n)
    (k : ℕ) : ℂ :=
  if k ∈ D.C then D.epsC k
  else if k ∈ D.Se then -D.epsE k
  else -D.epsO k

def PairSignData.coeff {n : ℕ} (D : PairSignData n) :
    Fin (4 * n + 1) → ℂ := fun j ↦
  if (j : ℕ) < 2 * n then D.negCoeff (2 * n - j)
  else if (j : ℕ) = 2 * n then 1
  else D.posCoeff ((j : ℕ) - 2 * n)

private theorem PairSignData.disjoint_CSe_So {n : ℕ}
    (D : PairSignData n) : Disjoint (D.C ∪ D.Se) D.So := by
  rw [Finset.disjoint_left]
  intro k hk hko
  simp only [Finset.mem_union] at hk
  rcases hk with hkc | hke
  · exact (Finset.disjoint_left.mp D.disjoint_C_So) hkc hko
  · exact (Finset.disjoint_left.mp D.disjoint_Se_So) hke hko

private theorem PairSignData.C_subset {n : ℕ} (D : PairSignData n) :
    D.C ⊆ Finset.Icc 1 (2 * n) := by
  intro k hk
  rw [← D.cover]
  simp [hk]

private theorem PairSignData.Se_subset {n : ℕ} (D : PairSignData n) :
    D.Se ⊆ Finset.Icc 1 (2 * n) := by
  intro k hk
  rw [← D.cover]
  simp [hk]

private theorem PairSignData.So_subset {n : ℕ} (D : PairSignData n) :
    D.So ⊆ Finset.Icc 1 (2 * n) := by
  intro k hk
  rw [← D.cover]
  simp [hk]

theorem PairSignData.coeff_isSign {n : ℕ} (D : PairSignData n) :
    ∀ j, IsSign (D.coeff j) := by
  intro j
  by_cases hjlt : (j : ℕ) < 2 * n
  · have hk : 2 * n - (j : ℕ) ∈ Finset.Icc 1 (2 * n) := by
      simp only [Finset.mem_Icc]
      omega
    rw [← D.cover] at hk
    simp only [Finset.mem_union] at hk
    simp only [PairSignData.coeff, if_pos hjlt,
      PairSignData.negCoeff]
    by_cases hC : 2 * n - (j : ℕ) ∈ D.C
    · rw [if_pos hC]
      rcases D.epsC_isSign _ hC with h | h <;> simp [h, IsSign]
    · rw [if_neg hC]
      by_cases hE : 2 * n - (j : ℕ) ∈ D.Se
      · rw [if_pos hE]
        rcases D.epsE_isSign _ hE with h | h <;> simp [h, IsSign]
      · rw [if_neg hE]
        have hO : 2 * n - (j : ℕ) ∈ D.So := by
          rcases hk with (hC' | hE') | hO
          · exact (hC hC').elim
          · exact (hE hE').elim
          · exact hO
        rcases D.epsO_isSign _ hO with h | h <;> simp [h, IsSign]
  · by_cases hjeq : (j : ℕ) = 2 * n
    · simp [PairSignData.coeff, hjeq, IsSign]
    · have hjgt : 2 * n < (j : ℕ) := by omega
      have hk : (j : ℕ) - 2 * n ∈ Finset.Icc 1 (2 * n) := by
        simp only [Finset.mem_Icc]
        have hjtop : (j : ℕ) ≤ 4 * n := by omega
        omega
      rw [← D.cover] at hk
      simp only [Finset.mem_union] at hk
      simp only [PairSignData.coeff, if_neg hjlt, if_neg hjeq,
        PairSignData.posCoeff]
      by_cases hC : (j : ℕ) - 2 * n ∈ D.C
      · rw [if_pos hC]
        rcases D.epsC_isSign _ hC with h | h <;> simp [h, IsSign]
      · rw [if_neg hC]
        by_cases hE : (j : ℕ) - 2 * n ∈ D.Se
        · rw [if_pos hE]
          rcases D.epsE_isSign _ hE with h | h <;> simp [h, IsSign]
        · rw [if_neg hE]
          have hO : (j : ℕ) - 2 * n ∈ D.So := by
            rcases hk with (hC' | hE') | hO
            · exact (hC hC').elim
            · exact (hE hE').elim
            · exact hO
          rcases D.epsO_isSign _ hO with h | h <;> simp [h, IsSign]

private theorem sum_range_center_sub {n : ℕ} (D : PairSignData n)
    (z : ℂ) :
    (∑ j ∈ Finset.range (2 * n),
        D.negCoeff (2 * n - j) * z ^ j) =
      ∑ k ∈ Finset.Icc 1 (2 * n),
        D.negCoeff k * z ^ (2 * n - k) := by
  classical
  apply sum_bij (fun j _ ↦ 2 * n - j)
  · intro j hj
    simp only [Finset.mem_range] at hj
    simp only [Finset.mem_Icc]
    omega
  · intro a ha b hb hab
    simp only [Finset.mem_range] at ha hb
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    refine ⟨2 * n - k, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    congr 2
    omega

private theorem sum_range_center_add {n : ℕ} (D : PairSignData n)
    (z : ℂ) :
    (∑ j ∈ Finset.range (2 * n),
        D.posCoeff (j + 1) * z ^ (2 * n + (j + 1))) =
      ∑ k ∈ Finset.Icc 1 (2 * n),
        D.posCoeff k * z ^ (2 * n + k) := by
  classical
  apply sum_bij (fun j _ ↦ j + 1)
  · intro j hj
    simp only [Finset.mem_range] at hj
    simp only [Finset.mem_Icc]
    omega
  · intro a ha b hb hab
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    refine ⟨k - 1, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro j hj
    rfl

private theorem PairSignData.sum_pos_part {n : ℕ}
    (D : PairSignData n) (f : ℕ → ℂ) :
    (∑ k ∈ Finset.Icc 1 (2 * n), D.posCoeff k * f k) =
      (∑ k ∈ D.C, (D.epsC k : ℂ) * f k) +
      (∑ k ∈ D.Se, (D.epsE k : ℂ) * f k) +
      ∑ k ∈ D.So, (D.epsO k : ℂ) * f k := by
  classical
  rw [← D.cover, sum_union D.disjoint_CSe_So,
    sum_union D.disjoint_C_Se]
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· + ·)
    · apply sum_congr rfl
      intro k hk
      simp [PairSignData.posCoeff, hk]
    · apply sum_congr rfl
      intro k hk
      have hnotC : k ∉ D.C := fun hC ↦
        (Finset.disjoint_left.mp D.disjoint_C_Se) hC hk
      simp [PairSignData.posCoeff, hk, hnotC]
  · apply sum_congr rfl
    intro k hk
    have hnotC : k ∉ D.C := fun hC ↦
      (Finset.disjoint_left.mp D.disjoint_C_So) hC hk
    have hnotE : k ∉ D.Se := fun hE ↦
      (Finset.disjoint_left.mp D.disjoint_Se_So) hE hk
    simp [PairSignData.posCoeff, hnotC, hnotE]

private theorem PairSignData.sum_neg_part {n : ℕ}
    (D : PairSignData n) (f : ℕ → ℂ) :
    (∑ k ∈ Finset.Icc 1 (2 * n), D.negCoeff k * f k) =
      (∑ k ∈ D.C, (D.epsC k : ℂ) * f k) -
      (∑ k ∈ D.Se, (D.epsE k : ℂ) * f k) -
      ∑ k ∈ D.So, (D.epsO k : ℂ) * f k := by
  classical
  rw [← D.cover, sum_union D.disjoint_CSe_So,
    sum_union D.disjoint_C_Se]
  simp only [sub_eq_add_neg, ← sum_neg_distrib]
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· + ·)
    · apply sum_congr rfl
      intro k hk
      simp [PairSignData.negCoeff, hk]
    · apply sum_congr rfl
      intro k hk
      have hnotC : k ∉ D.C := fun hC ↦
        (Finset.disjoint_left.mp D.disjoint_C_Se) hC hk
      simp [PairSignData.negCoeff, hk, hnotC]
  · apply sum_congr rfl
    intro k hk
    have hnotC : k ∉ D.C := fun hC ↦
      (Finset.disjoint_left.mp D.disjoint_C_So) hC hk
    have hnotE : k ∉ D.Se := fun hE ↦
      (Finset.disjoint_left.mp D.disjoint_Se_So) hE hk
    simp [PairSignData.negCoeff, hnotC, hnotE]

private theorem sum_center_sub_factor {n : ℕ} (s : Finset ℕ)
    (eps : ℕ → ℝ) (hs : s ⊆ Finset.Icc 1 (2 * n))
    (z : ℂ) (hz : z ≠ 0) :
    (∑ k ∈ s, (eps k : ℂ) * z ^ (2 * n - k)) =
      z ^ (2 * n) * ∑ k ∈ s, (eps k : ℂ) * z⁻¹ ^ k := by
  classical
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro k hk
  have hkn : k ≤ 2 * n := (Finset.mem_Icc.mp (hs hk)).2
  rw [pow_sub₀ z hz hkn, inv_pow]
  ring

private theorem sum_center_add_factor {n : ℕ} (s : Finset ℕ)
    (eps : ℕ → ℝ) (z : ℂ) :
    (∑ k ∈ s, (eps k : ℂ) * z ^ (2 * n + k)) =
      z ^ (2 * n) * ∑ k ∈ s, (eps k : ℂ) * z ^ k := by
  classical
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro k hk
  rw [pow_add]
  ring

theorem PairSignData.eval_eq {n : ℕ} (D : PairSignData n)
    (θ : ℝ) :
    (ofCoeffs (4 * n) D.coeff).eval (unitPt θ) =
      unitPt θ ^ (2 * n) *
        pairLaurentValue D.C D.Se D.So D.epsC D.epsE D.epsO θ := by
  classical
  let z := unitPt θ
  have hz : z ≠ 0 := unitPt_ne_zero θ
  rw [eval_ofCoeffs]
  change (∑ i : Fin (4 * n + 1), D.coeff i * z ^ (i : ℕ)) = _
  let term : ℕ → ℂ := fun j ↦
    if hj : j < 4 * n + 1 then D.coeff ⟨j, hj⟩ * z ^ j else 0
  have hfin :
      (∑ i : Fin (4 * n + 1), D.coeff i * z ^ (i : ℕ)) =
        ∑ j ∈ Finset.range (4 * n + 1), term j := by
    rw [← Fin.sum_univ_eq_sum_range term (4 * n + 1)]
    apply sum_congr rfl
    intro i hi
    rw [show term (i : ℕ) = D.coeff i * z ^ (i : ℕ) by
      simp only [term, dif_pos i.isLt]]
  rw [hfin]
  rw [show 4 * n + 1 = 2 * n + (1 + 2 * n) by omega,
    sum_range_add]
  rw [sum_range_add (fun j ↦
    term (2 * n + j)) 1 (2 * n)]
  simp only [Finset.sum_range_one, Nat.add_zero]
  have hnegative :
      (∑ j ∈ Finset.range (2 * n),
          term j) =
        ∑ k ∈ Finset.Icc 1 (2 * n),
          D.negCoeff k * z ^ (2 * n - k) := by
    rw [← sum_range_center_sub D z]
    apply sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    have hjtop : j < 4 * n + 1 := by omega
    rw [show term j = D.coeff ⟨j, hjtop⟩ * z ^ j by
      simp only [term, dif_pos hjtop]]
    simp only [PairSignData.coeff, if_pos hj]
  have hcenter : term (2 * n) = z ^ (2 * n) := by
    have hjtop : 2 * n < 4 * n + 1 := by omega
    rw [show term (2 * n) = D.coeff ⟨2 * n, hjtop⟩ * z ^ (2 * n) by
      simp only [term, dif_pos hjtop]]
    simp [PairSignData.coeff]
  have hpositive :
      (∑ j ∈ Finset.range (2 * n),
          term (2 * n + (1 + j))) =
        ∑ k ∈ Finset.Icc 1 (2 * n),
          D.posCoeff k * z ^ (2 * n + k) := by
    rw [← sum_range_center_add D z]
    apply sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    have hjtop : 2 * n + (1 + j) < 4 * n + 1 := by omega
    have hne : 2 * n + (1 + j) ≠ 2 * n := by omega
    rw [show term (2 * n + (1 + j)) =
        D.coeff ⟨2 * n + (1 + j), hjtop⟩ * z ^ (2 * n + (1 + j)) by
      simp only [term, dif_pos hjtop]]
    simp only [PairSignData.coeff, if_neg (by omega : ¬2 * n + (1 + j) < 2 * n),
      if_neg hne]
    congr 2 <;> omega
  rw [hnegative, hcenter, hpositive]
  rw [D.sum_neg_part (fun k ↦ z ^ (2 * n - k)),
    D.sum_pos_part (fun k ↦ z ^ (2 * n + k))]
  rw [sum_center_sub_factor D.C D.epsC D.C_subset z hz,
    sum_center_sub_factor D.Se D.epsE D.Se_subset z hz,
    sum_center_sub_factor D.So D.epsO D.So_subset z hz,
    sum_center_add_factor D.C D.epsC z,
    sum_center_add_factor D.Se D.epsE z,
    sum_center_add_factor D.So D.epsO z]
  simp only [pairLaurentValue, z]
  simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
  ring

def PairSignData.toCtrPairInput {n : ℕ} (D : PairSignData n)
    (dangerous : ℝ → Prop)
    (hcosUpper : ∀ θ, |cosSum D.C D.epsC θ| ≤ sqrt n)
    (hevenUpper : ∀ θ, |sineSum D.Se D.epsE θ| ≤ 6 * sqrt n)
    (hoddUpper : ∀ θ, |sineSum D.So D.epsO θ| ≤ 2 ^ 10 * sqrt n)
    (hcosLower : ∀ θ, InFundamentalAngle θ → ¬dangerous θ →
      (1 / 2 ^ 160 : ℝ) * sqrt n + 1 ≤
        2 * |cosSum D.C D.epsC θ|)
    (hoddLower : ∀ θ, InFundamentalAngle θ → dangerous θ →
      10 * sqrt n ≤ |sineSum D.So D.epsO θ|) :
    CtrPairInput n where
  coeff := D.coeff
  coeff_isSign := D.coeff_isSign
  cosine := cosSum D.C D.epsC
  evenSine := sineSum D.Se D.epsE
  oddSine := sineSum D.So D.epsO
  dangerous := dangerous
  eval_eq := fun θ ↦ D.eval_eq θ |>.trans
    (congrArg (unitPt θ ^ (2 * n) * ·)
      (pairLaurentValue_eq_asmValue
        D.C D.Se D.So D.epsC D.epsE D.epsO θ))
  cosine_upper := hcosUpper
  evenSine_upper := hevenUpper
  oddSine_upper := hoddUpper
  cosine_lower_off_dangerous := hcosLower
  oddSine_lower_on_dangerous := hoddLower

def oddS (n : ℕ) : Finset ℕ :=
  (Finset.range n).image oddFreq

@[simp] theorem mem_oddS {n k : ℕ} :
    k ∈ oddS n ↔ ∃ j < n, k = 2 * j + 1 := by
  simp [oddS, oddFreq, eq_comm]

private theorem evenC_union_evenS {n t : ℕ}
    (hblock : 2 * evenT t + 2 ^ t ≤ n + 1) :
    evenC t ∪ evenS n t =
      (Finset.Icc 1 n).image (fun j ↦ 2 * j) := by
  classical
  ext k
  simp only [Finset.mem_union, mem_evenC, mem_evenS, Finset.mem_image,
    Finset.mem_Icc]
  constructor
  · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
    · refine ⟨j, ?_, rfl⟩
      have hjrange := evenCPrime_subset_range hblock hj
      simp only [Finset.mem_range] at hjrange
      have hjpos : 1 ≤ j := by
        rw [mem_evenCPrime] at hj
        rcases hj with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
        · have hT : 0 < evenT t := by simp [evenT]
          omega
        · have hT : 0 < evenT t := by simp [evenT]
          omega
      exact ⟨hjpos, by omega⟩
    · have hj' := (mem_evenSPrime n t j).mp hj
      exact ⟨j, ⟨hj'.1, hj'.2.1⟩, rfl⟩
  · rintro ⟨j, ⟨hjpos, hjn⟩, rfl⟩
    by_cases hjC : j ∈ evenCPrime t
    · exact Or.inl ⟨j, hjC, rfl⟩
    · exact Or.inr ⟨j, (mem_evenSPrime n t j).mpr ⟨hjpos, hjn, hjC⟩, rfl⟩

private theorem evenOdd_cover {n t : ℕ}
    (hblock : 2 * evenT t + 2 ^ t ≤ n + 1) :
    evenC t ∪ evenS n t ∪ oddS n = Finset.Icc 1 (2 * n) := by
  classical
  rw [evenC_union_evenS hblock]
  ext k
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Icc, mem_oddS]
  constructor
  · rintro (⟨j, ⟨hjpos, hjn⟩, rfl⟩ | ⟨j, hjn, rfl⟩)
    · omega
    · omega
  · intro hk
    obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' k
    · left
      refine ⟨j, ?_, hj.symm⟩
      omega
    · right
      exact ⟨j, by omega, hj⟩

private theorem evenC_disjoint_oddS (n t : ℕ) :
    Disjoint (evenC t) (oddS n) := by
  rw [Finset.disjoint_left]
  intro k hkC hkO
  rw [mem_evenC] at hkC
  rw [mem_oddS] at hkO
  obtain ⟨a, ha, rfl⟩ := hkC
  obtain ⟨b, hb, hab⟩ := hkO
  omega

private theorem evenS_disjoint_oddS (n t : ℕ) :
    Disjoint (evenS n t) (oddS n) := by
  rw [Finset.disjoint_left]
  intro k hkE hkO
  rw [mem_evenS] at hkE
  rw [mem_oddS] at hkO
  obtain ⟨a, ha, rfl⟩ := hkE
  obtain ⟨b, hb, hab⟩ := hkO
  omega

def evenCosCoeff (t k : ℕ) : ℝ :=
  ((cosBlk t).coeff (k / 2)).re

def evenSinCoeff (n t u k : ℕ) : ℝ :=
  ((evenRemainder n t u).coeff (k / 2)).re

def oddSinCoeff (eps : ℕ → ℝ) (k : ℕ) : ℝ :=
  eps (k / 2)

private theorem evenCosCoeff_isSign {t k : ℕ} (hk : k ∈ evenC t) :
    evenCosCoeff t k = 1 ∨ evenCosCoeff t k = -1 := by
  rw [mem_evenC] at hk
  obtain ⟨j, hj, rfl⟩ := hk
  have hdiv : 2 * j / 2 = j := by omega
  simp only [evenCosCoeff, hdiv]
  rw [mem_evenCPrime] at hj
  rcases hj with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · rw [coeff_cosBlk_first t a ha]
    rcases coeff_rsP_eq_one_or_neg_one ha with h | h <;>
      simp [h]
  · rw [coeff_cosBlk_second t a ha]
    rcases coeff_rsQ_eq_one_or_neg_one ha with h | h <;>
      simp [h]

private theorem evenSinCoeff_isSign {n t u k : ℕ}
    (hprefix : n + 1 ≤ 2 ^ u) (hk : k ∈ evenS n t) :
    evenSinCoeff n t u k = 1 ∨ evenSinCoeff n t u k = -1 := by
  rw [mem_evenS] at hk
  obtain ⟨j, hj, rfl⟩ := hk
  have hdiv : 2 * j / 2 = j := by omega
  simp only [evenSinCoeff, hdiv]
  rcases coeff_evenRemainder_sign_of_mem_evenSPrime hprefix hj with h | h <;>
    simp [h]

private theorem oddSinCoeff_isSign {n k : ℕ} {eps : ℕ → ℝ}
    (heps : ∀ j, eps j = 1 ∨ eps j = -1) (hk : k ∈ oddS n) :
    oddSinCoeff eps k = 1 ∨ oddSinCoeff eps k = -1 := by
  rw [mem_oddS] at hk
  obtain ⟨j, hj, rfl⟩ := hk
  have hdiv : (2 * j + 1) / 2 = j := by omega
  simpa [oddSinCoeff, hdiv] using heps j

def concretePairSignData (n t u : ℕ) (eps : ℕ → ℝ)
    (hblock : 2 * evenT t + 2 ^ t ≤ n + 1)
    (hprefix : n + 1 ≤ 2 ^ u)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1) : PairSignData n where
  C := evenC t
  Se := evenS n t
  So := oddS n
  cover := evenOdd_cover hblock
  disjoint_C_Se := evenC_disjoint_evenS n t
  disjoint_C_So := evenC_disjoint_oddS n t
  disjoint_Se_So := evenS_disjoint_oddS n t
  epsC := evenCosCoeff t
  epsE := evenSinCoeff n t u
  epsO := oddSinCoeff eps
  epsC_isSign := fun _ hk ↦ evenCosCoeff_isSign hk
  epsE_isSign := fun _ hk ↦ evenSinCoeff_isSign hprefix hk
  epsO_isSign := fun _ hk ↦ oddSinCoeff_isSign heps hk

private theorem eval_unitPt_re_eq_cos_support (p : Polynomial ℂ)
    (hreal : ∀ k ∈ p.support, (p.coeff k).im = 0) (θ : ℝ) :
    (p.eval (unitPt θ)).re =
      ∑ k ∈ p.support, (p.coeff k).re * cos (k * θ) := by
  classical
  rw [eval_eq_sum, sum_def]
  change reLm (∑ k ∈ p.support, p.coeff k * unitPt θ ^ k) = _
  rw [map_sum]
  apply sum_congr rfl
  intro k hk
  have hre : (unitPt θ ^ k).re = cos (k * θ) := by
    have h := congrArg re (unitPt_pow θ k)
    simpa only [add_re, ofReal_re, mul_re,
      ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, mul_one, add_zero] using h
  change (p.coeff k * unitPt θ ^ k).re = _
  rw [mul_re, hreal k hk, zero_mul, sub_zero, hre]

private theorem eval_unitPt_im_eq_sin_support (p : Polynomial ℂ)
    (hreal : ∀ k ∈ p.support, (p.coeff k).im = 0) (θ : ℝ) :
    (p.eval (unitPt θ)).im =
      ∑ k ∈ p.support, (p.coeff k).re * sin (k * θ) := by
  classical
  rw [eval_eq_sum, sum_def]
  change imLm (∑ k ∈ p.support, p.coeff k * unitPt θ ^ k) = _
  rw [map_sum]
  apply sum_congr rfl
  intro k hk
  have him : (unitPt θ ^ k).im = sin (k * θ) := by
    have h := congrArg Complex.im (unitPt_pow θ k)
    simpa only [Complex.add_im, ofReal_re, mul_im,
      ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      mul_one, add_zero, zero_add] using h
  change (p.coeff k * unitPt θ ^ k).im = _
  rw [mul_im, hreal k hk, zero_mul, add_zero, him]

private theorem cosBlk_coeff_im_eq_zero {t k : ℕ}
    (hk : k ∈ (cosBlk t).support) :
    ((cosBlk t).coeff k).im = 0 := by
  rw [support_cosBlk] at hk
  rw [mem_evenCPrime] at hk
  rcases hk with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · rw [coeff_cosBlk_first t j hj]
    rcases coeff_rsP_eq_one_or_neg_one hj with h | h <;> simp [h]
  · rw [coeff_cosBlk_second t j hj]
    rcases coeff_rsQ_eq_one_or_neg_one hj with h | h <;> simp [h]

theorem cosSum_evenC_eq_evenCos (t : ℕ) (θ : ℝ) :
    cosSum (evenC t) (evenCosCoeff t) θ =
      evenCos t θ := by
  classical
  rw [cosSum, evenC, sum_image]
  · rw [evenCos]
    rw [eval_unitPt_re_eq_cos_support
      (cosBlk t) (fun k hk ↦ cosBlk_coeff_im_eq_zero hk)]
    rw [support_cosBlk]
    apply sum_congr rfl
    intro j hj
    have hdiv : 2 * j / 2 = j := by omega
    simp only [evenCosCoeff, hdiv]
    congr 2
    push_cast
    ring
  · intro a ha b hb hab
    dsimp only at hab
    omega

private theorem coeff_evenRemainder_zero {n t u : ℕ} :
    (evenRemainder n t u).coeff 0 = 1 := by
  have hzero : 0 ∉ evenCPrime t := by
    rw [mem_evenCPrime]
    push Not
    constructor
    · intro j hj
      have hT : 0 < evenT t := by simp [evenT]
      omega
    · intro j hj
      have hT : 0 < evenT t := by simp [evenT]
      omega
  rw [evenRemainder, coeff_sub,
    coeff_polyPrefix, if_pos (by omega),
    coeff_deletedEvenBlk_eq_zero_of_outside t 0 hzero, sub_zero]
  have hstable := coeff_rsP_stable
    (a := 0) (b := u) (k := 0) (Nat.zero_le u) (by norm_num)
  simpa [rudinShapiroP] using hstable

private theorem support_evenRemainder {n t u : ℕ}
    (hu : t + 12 ≤ u) (hblock : 2 * evenT t + 2 ^ t ≤ n + 1)
    (hprefix : n + 1 ≤ 2 ^ u) :
    (evenRemainder n t u).support =
      insert 0 (evenSPrime n t) := by
  classical
  ext k
  simp only [mem_support_iff, Finset.mem_insert, ne_eq]
  constructor
  · intro hk
    by_cases hk0 : k = 0
    · exact Or.inl hk0
    · right
      rw [mem_evenSPrime]
      have hklt : k < n + 1 := by
        by_contra hnot
        have hlarge : n + 1 ≤ k := Nat.le_of_not_gt hnot
        have hkC : k ∉ evenCPrime t := by
          intro hkC
          have hkrange := evenCPrime_subset_range hblock hkC
          simp only [Finset.mem_range] at hkrange
          omega
        apply hk
        rw [evenRemainder, coeff_sub,
          coeff_polyPrefix, if_neg (by omega),
          coeff_deletedEvenBlk_eq_zero_of_outside t k hkC,
          sub_zero]
      refine ⟨by omega, by omega, ?_⟩
      intro hkC
      exact hk (coeff_evenRemainder_eq_zero_on_CPrime hu hblock hkC)
  · rintro (rfl | hk)
    · rw [coeff_evenRemainder_zero]
      norm_num
    · rcases coeff_evenRemainder_sign_of_mem_evenSPrime hprefix hk with h | h <;>
        rw [h] <;> norm_num

private theorem evenRemainder_coeff_im_eq_zero {n t u k : ℕ}
    (hu : t + 12 ≤ u) (hblock : 2 * evenT t + 2 ^ t ≤ n + 1)
    (hprefix : n + 1 ≤ 2 ^ u)
    (hk : k ∈ (evenRemainder n t u).support) :
    ((evenRemainder n t u).coeff k).im = 0 := by
  rw [support_evenRemainder hu hblock hprefix] at hk
  simp only [Finset.mem_insert] at hk
  rcases hk with rfl | hk
  · simp [coeff_evenRemainder_zero]
  · rcases coeff_evenRemainder_sign_of_mem_evenSPrime hprefix hk with h | h <;>
      simp [h]

theorem sinSum_evenS_eq_evenSin (n t u : ℕ)
    (hu : t + 12 ≤ u) (hblock : 2 * evenT t + 2 ^ t ≤ n + 1)
    (hprefix : n + 1 ≤ 2 ^ u) (θ : ℝ) :
    sineSum (evenS n t) (evenSinCoeff n t u) θ =
      evenSine n t u θ := by
  classical
  rw [sineSum, evenS, sum_image]
  · rw [evenSine]
    rw [eval_unitPt_im_eq_sin_support
      (evenRemainder n t u)
      (fun k hk ↦ evenRemainder_coeff_im_eq_zero hu hblock hprefix hk)]
    rw [support_evenRemainder hu hblock hprefix]
    rw [Finset.sum_insert]
    · simp only [Nat.cast_zero, zero_mul, sin_zero, mul_zero, zero_add]
      apply sum_congr rfl
      intro j hj
      have hdiv : 2 * j / 2 = j := by omega
      simp only [evenSinCoeff, hdiv]
      congr 2
      push_cast
      ring
    · simp [mem_evenSPrime]
  · intro a ha b hb hab
    dsimp only at hab
    omega

theorem sinSum_oddS_eq_oddSinSum (n : ℕ) (eps : ℕ → ℝ) (θ : ℝ) :
    sineSum (oddS n) (oddSinCoeff eps) θ =
      oddSineSum n eps θ := by
  classical
  rw [sineSum, oddS, sum_image]
  · apply sum_congr rfl
    intro j hj
    have hdiv : (2 * j + 1) / 2 = j := by omega
    simp [oddSinCoeff, hdiv, oddFreq]
  · intro a ha b hb hab
    simp only [oddFreq] at hab
    omega

private theorem exists_oddSin_of_ivlColoring {n : ℕ} (hn : 0 < n)
    (F : IvlFam n)
    (α : ↥F.base → ℝ)
    (htarget : ∀ j < n, |fourierTarget F α j| ≤ 1)
    (hkernel : KernelCert F α)
    {G : Type} [Fintype G]
    (setup : RoundingSetup n G) :
    ∃ eps : ℕ → ℝ, (∀ j, eps j = 1 ∨ eps j = -1) ∧
      (∀ θ, IsDangerous F θ →
        10 * sqrt n < |oddSineSum n eps θ|) ∧
      (∀ θ, |oddSineSum n eps θ| ≤
        2 ^ 10 * sqrt n) := by
  classical
  obtain ⟨eps, heps, hround⟩ := exists_rounding hn setup
    (fourierTarget F α) htarget
    (fun I _ _ ↦ EdgeWalk.partialColoringPrinciple I (G × Fin n))
  obtain ⟨hkernelLower, hkernelUpper⟩ :=
    targetSine_kernel_bounds hn F α hkernel
  refine ⟨eps, heps, ?_, ?_⟩
  · intro θ hθ
    have htri : |targetSine F α θ| ≤
        |oddSineSum n eps θ| +
          |oddSineSum n eps θ -
            targetSine F α θ| := by
      calc
        |targetSine F α θ| =
            |oddSineSum n eps θ -
              (oddSineSum n eps θ -
                targetSine F α θ)| := by ring_nf
        _ ≤ _ := abs_sub _ _
    have hlower := hkernelLower θ hθ
    have herror := hround θ
    change |oddSineSum n eps θ -
      targetSine F α θ| ≤ 72 * sqrt n at herror
    rw [K_eq] at hlower
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    nlinarith [sqrt_pos.2 hnR]
  · intro θ
    have htri := abs_add_le (targetSine F α θ)
      (oddSineSum n eps θ -
        targetSine F α θ)
    have heq : targetSine F α θ +
        (oddSineSum n eps θ -
          targetSine F α θ) =
          oddSineSum n eps θ := by ring
    rw [heq] at htri
    have hu := hkernelUpper θ
    have he := hround θ
    change |oddSineSum n eps θ -
      targetSine F α θ| ≤ 72 * sqrt n at he
    rw [K_eq] at hu
    norm_num at ⊢
    nlinarith [sqrt_nonneg n]

theorem exists_concrete_oddSine {n : ℕ} (hn : 0 < n)
    (F : IvlFam n) {γ : ℝ}
    (hγ : γ ≤ 1 / (2 : ℝ) ^ 40)
    (hcard : (F.base.card : ℝ) ≤ γ * n)
    (hkernel : ∀ α : ↥F.base → ℝ,
      Disc.IsSign α →
        KernelCert F α) :
    ∃ eps : ℕ → ℝ, (∀ j, eps j = 1 ∨ eps j = -1) ∧
      (∀ θ, IsDangerous F θ →
        10 * sqrt n < |oddSineSum n eps θ|) ∧
      (∀ θ, |oddSineSum n eps θ| ≤
        2 ^ 10 * sqrt n) := by
  classical
  obtain ⟨α, hα, htarget⟩ :
      ∃ α : ↥F.base → ℝ,
        Disc.IsSign α ∧
          ∀ j < n, |fourierTarget F α j| ≤ 1 := by
    by_cases hbase : F.base.card = 0
    · exact exists_ivlColoring_of_base_card_eq_zero F hbase
    · have hbasePos : 0 < F.base.card := Nat.pos_of_ne_zero hbase
      have hadmissible := firstColoringAdm_of_card_le
        hn F hγ hbasePos hcard
      exact exists_ivlColoring F
        (fun _ ↦ firstParam n F.base.card)
        hadmissible
        (fun I _ _ ↦ EdgeWalk.partialColoringPrinciple I (Fin n))
  obtain ⟨setup⟩ := exists_roundingSetup hn
  exact exists_oddSin_of_ivlColoring hn F α htarget
    (hkernel α hα) setup

private theorem nat_succ_le_two_pow (m : ℕ) : m + 1 ≤ 2 ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [pow_succ]
      omega

private theorem cosDelta_gt_two_pow_neg_160 {γ : ℝ}
    (hγLower : (1 / 2 ^ 43 : ℝ) < γ) :
    (1 / 2 ^ 160 : ℝ) < CosConstr.cosDelta γ := by
  have hγ : 0 < γ := by
    exact lt_trans (by positivity : (0 : ℝ) < 1 / 2 ^ 43) hγLower
  have hcube : (1 / 2 ^ 43 : ℝ) ^ 3 < γ ^ 3 := by
    gcongr
  have hsmallSq : (1 / 2 ^ 22 : ℝ) ^ 2 < γ := by
    have : (1 / 2 ^ 22 : ℝ) ^ 2 < (1 / 2 ^ 43 : ℝ) := by norm_num
    exact this.trans hγLower
  have hsqrtSq := sq_sqrt hγ.le
  have hsqrt : (1 / 2 ^ 22 : ℝ) < sqrt γ := by
    nlinarith [sqrt_nonneg γ]
  rw [CosConstr.cosDelta]
  calc
    (1 / 2 ^ 160 : ℝ) < (1 / 2 ^ 159 : ℝ) := by norm_num
    _ = (1 / 2 ^ 8 : ℝ) * (1 / 2 ^ 43 : ℝ) ^ 3 * (1 / 2 ^ 22 : ℝ) := by
      norm_num
    _ < (1 / 2 ^ 8 : ℝ) * γ ^ 3 * sqrt γ := by
      gcongr

theorem exists_ctrPairInput_of_comps
    {n t : ℕ} {γ : ℝ}
    (hparam : CosConstr.Params n t γ)
    (F : IvlFam n)
    (hcard : (F.base.card : ℝ) ≤ γ * n)
    (hcosUpper : ∀ θ, |evenCos t θ| ≤ sqrt n)
    (hcosLower : ∀ θ, InFundamentalAngle θ →
      ¬IsDangerous F θ →
      CosConstr.cosDelta γ * sqrt n ≤
        |evenCos t θ|)
    (hkernel : ∀ α : ↥F.base → ℝ,
      Disc.IsSign α →
        KernelCert F α)
    (habsorb : 1 ≤ (1 / 2 ^ 160 : ℝ) * sqrt n) :
    Nonempty (CtrPairInput n) := by
  have heven := hparam.toEvenParams
  have hu : t + 12 ≤ n := by
    have ht : t + 12 ≤ 2 ^ (t + 11) := by
      simpa only [Nat.reduceAdd] using nat_succ_le_two_pow (t + 11)
    exact ht.trans heven.pow_t_add_eleven_le_n
  have hprefix : n + 1 ≤ 2 ^ n := nat_succ_le_two_pow n
  obtain ⟨eps, heps, hoddLower, hoddUpper⟩ :=
    exists_concrete_oddSine hparam.n_pos F hparam.gamma_upper hcard hkernel
  let D := concretePairSignData n t n eps heven.blks_fit hprefix heps
  refine ⟨D.toCtrPairInput (IsDangerous F) ?_ ?_ ?_ ?_ ?_⟩
  · intro θ
    rw [show cosSum D.C D.epsC θ = evenCos t θ by
      exact cosSum_evenC_eq_evenCos t θ]
    exact hcosUpper θ
  · intro θ
    rw [show sineSum D.Se D.epsE θ = evenSine n t n θ by
      exact sinSum_evenS_eq_evenSin n t n hu heven.blks_fit hprefix θ]
    exact abs_evenSin_le_six_sqrt_of_params heven hprefix θ
  · intro θ
    rw [show sineSum D.So D.epsO θ =
        oddSineSum n eps θ by
      exact sinSum_oddS_eq_oddSinSum n eps θ]
    exact hoddUpper θ
  · intro θ hθ hsafe
    rw [show cosSum D.C D.epsC θ = evenCos t θ by
      exact cosSum_evenC_eq_evenCos t θ]
    have hlower := hcosLower θ hθ hsafe
    have hδ := cosDelta_gt_two_pow_neg_160 hparam.gamma_lower
    have hsqrt : 0 ≤ sqrt n := sqrt_nonneg _
    nlinarith
  · intro θ _htheta hdanger
    rw [show sineSum D.So D.epsO θ =
        oddSineSum n eps θ by
      exact sinSum_oddS_eq_oddSinSum n eps θ]
    exact (hoddLower θ hdanger).le

private theorem eventually_absorb_one :
    ∀ᶠ n : ℕ in atTop,
      1 ≤ (1 / 2 ^ 160 : ℝ) * sqrt n := by
  have hsqrt : Filter.Tendsto (fun n : ℕ ↦ sqrt (n : ℝ))
      atTop atTop :=
    tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hscaled : Filter.Tendsto
      (fun n : ℕ ↦ (1 / 2 ^ 160 : ℝ) * sqrt n)
      atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) hsqrt
  exact hscaled (eventually_ge_atTop 1)

theorem eventuallyCtrPair : EventuallyCtrPair := by
  rw [EventuallyCtrPair]
  filter_upwards [CosConstr.eventually_exists_cosPackage,
    eventually_ge_atTop 4096, eventually_absorb_one]
    with n hpackage hn habsorb
  obtain ⟨P⟩ := hpackage
  exact exists_ctrPairInput_of_comps P.parameters P.family
    P.base_card P.upper P.lower
    (KernelCert.kernelCert hn P.family) habsorb

end

end

end Erdos228

theorem OMA.solution : type_of% @Erdos228.erdos_228 :=
  Erdos228.target_of_eventually_ctr Erdos228.eventuallyCtrPair
