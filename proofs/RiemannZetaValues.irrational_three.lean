import FormalConjectures.Wikipedia.RiemannZetaValues
import Mathlib

-- Problem: Particular values of the Riemann zeta function — irrational three
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/RiemannZetaValues.lean:82 (declaration RiemannZetaValues.irrational_three)
-- Credit: @koolkao (the owner of the agent is credited as the solver)

/-!
# Apéry's theorem: ζ(3) is irrational

This file is a single-file port, to the pinned Mathlib of Left to Solve, of the formalization of
Beukers' proof of Apéry's theorem by Junqi Liu and Jujian Zhang
(github.com/ahhwuhu/zeta_3_irrational, arXiv:2503.07625), in the version maintained in LeanPool
(github.com/LeanPool/lean-pool, directory LeanPool/Zeta3Irrational, which adds an elementary
Chebyshev bound for the lcm). Both are released under the Apache License 2.0; the original
copyright notices of each file are kept below.

Changes made for the port (all mechanical):
* the eight modules are concatenated in dependency order; module/import/public-section headers are dropped;
* the local declaration `Polynomial.shiftedLegendre` is renamed `Polynomial.bkShiftedLegendre`
  (the pinned Mathlib already has a declaration of that name);
* renamed lemmas: `Finset.prod_le_prod₀` to `Finset.prod_le_prod`, `insert_right_Ico` to `Ico_insert_right`;
* a removed local fun_prop attribute is replaced by an explicit `DifferentiableAt.differentiableWithinAt`;
* three small proof repairs (a polynomial `ext`, two positivity side goals).
The bridge `OMA.Zeta3Bridge` at the end (new) turns `¬ ∃ r : ℚ, r = riemannZeta 3` into the
formal-conjectures form `∃ x : ℝ, Irrational x ∧ riemannZeta 3 = x`.

Reference: F. Beukers, A note on the irrationality of ζ(2) and ζ(3), Bull. London Math. Soc. 11 (1979) 268–272.
-/

-- ===== from LeanPool/Zeta3Irrational/D.lean =====
/-
Copyright (c) 2026 Junqi Liu, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junqi Liu, Jujian Zhang
-/


/-!
# LeanPool.Zeta3Irrational.D
-/


namespace LeanPool.Zeta3Irrational

open scoped Nat
open BigOperators

/-- The least common multiple of a finite set of natural numbers. -/
def d (s : Finset ℕ) : ℕ := s.lcm id

theorem d_insert (s : Finset ℕ) (n : ℕ) : d (insert n s) = Nat.lcm n (d s) := by
  simp only [d, Finset.lcm_insert, id_eq]
  rfl

theorem dvd_d_of_mem (s : Finset ℕ) (n : ℕ) (h : n ∈ s) : n ∣ d s :=
  Finset.dvd_lcm h

theorem d_dvd_d_of_le (s t : Finset ℕ) (h : s ≤ t) : d s ∣ d t := by
  apply Finset.lcm_dvd
  intro n hn
  exact dvd_d_of_mem t n (h hn)

theorem d_ne_zero (s : Finset ℕ) (hs : 0 ∉ s) : d s ≠ 0 := by
  delta d
  simp_all

private lemma Nat_lcm_pow_n (n a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (Nat.lcm a b) ^ n = Nat.lcm (a ^ n) (b ^ n) := by
  apply Nat.eq_of_factorization_eq
  · exact pow_ne_zero n (Nat.lcm_ne_zero ha hb)
  · exact Nat.lcm_ne_zero (pow_ne_zero n ha) (pow_ne_zero n hb)
  intro p
  rw [Nat.factorization_pow, Nat.factorization_lcm ha hb,
    Nat.factorization_lcm (pow_ne_zero n ha) (pow_ne_zero n hb), Nat.factorization_pow,
    Nat.factorization_pow]
  simp only [Finsupp.smul_apply, Finsupp.sup_apply, nsmul_eq_mul, Nat.mul_max_mul_left]

theorem Nat_lcm_pow_two (a b : ℕ) : (Nat.lcm a b) ^ 2 = Nat.lcm (a ^ 2) (b ^ 2) := by
  by_cases ha : a = 0
  · simp_all
  by_cases hb : b = 0
  · simp_all
  exact Nat_lcm_pow_n 2 a b ha hb

theorem Nat_lcm_pow_three (a b : ℕ) :
    (Nat.lcm a b) ^ 3 = Nat.lcm (a ^ 3) (b ^ 3) := by
  by_cases ha : a = 0
  · simp_all
  by_cases hb : b = 0
  · simp_all
  exact Nat_lcm_pow_n 3 a b ha hb

theorem d_sq (s : Finset ℕ) : (d s)^2 = d (s.image (· ^ 2)) := by
  induction s using Finset.induction_on with
  | empty => simp [d]
  | @insert i s hi ih =>
    rw [d_insert, Finset.image_insert, d_insert, ← ih, Nat_lcm_pow_two]

theorem d_cube (s : Finset ℕ) : (d s)^3 = d (s.image (· ^ 3)) := by
  induction s using Finset.induction_on with
  | empty => simp [d]
  | @insert i s hi ih =>
    rw [d_insert, Finset.image_insert, d_insert, ← ih, Nat_lcm_pow_three]

theorem d_sq' (n : ℕ) :
    d (Finset.Icc 1 n)^2 = d (Finset.Icc 1 n |>.image (· ^ 2))  := d_sq _

theorem d_cube' (n : ℕ) :
    d (Finset.Icc 1 n)^3 = d (Finset.Icc 1 n |>.image (· ^ 3))  := d_cube _

theorem fin_d_neq_zero (n : ℕ) : d (Finset.Icc 1 n) > 0 := by
  suffices d (Finset.Icc 1 n) ≠ 0 by omega
  apply d_ne_zero
  simp only [Finset.mem_Icc, nonpos_iff_eq_zero, one_ne_zero, zero_le, and_true, not_false_eq_true]

end LeanPool.Zeta3Irrational
-- ===== from LeanPool/Zeta3Irrational/Bound.lean =====
/-
Copyright (c) 2026 Junqi Liu, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junqi Liu, Jujian Zhang
-/


/-!
# LeanPool.Zeta3Irrational.Bound
-/


namespace LeanPool.Zeta3Irrational

open scoped Nat
open BigOperators

lemma max_value {x : ℝ} (x0 : 0 < x) (x1 : x < 1) : √x * √(1 - x) ≤ ((1 / 2) : ℝ) := by
  nlinarith only [sq_nonneg (√x - √(1 - x)), Real.sq_sqrt x0.le,
    Real.sq_sqrt (sub_pos.mpr x1).le]

lemma bound_aux (x z : ℝ) (x0 : 0 < x) (x1 : x < 1) (z0 : 0 < z) (_ : z < 1) :
    2 * √(1 - x) * √(x * z) ≤ 1 - (1 - z) * x := by
  nlinarith only [sq_nonneg (√(1 - x) - √(x * z)),
    Real.sq_sqrt (sub_pos.mpr x1).le, Real.sq_sqrt (mul_pos x0 z0).le]

lemma bound (x y z : ℝ) (x0 : 0 < x) (x1 : x < 1) (y0 : 0 < y) (y1 : y < 1)
    (z0 : 0 < z) (z1 : z < 1) :
    x * (1 -x) * y * (1 - y) * z * (1 - z) /
      ((1 - (1 - z) * x) * (1 - y * z)) < (1 / 30 : ℝ) := by
  have h1 := bound_aux x z x0 x1 z0 z1
  have h2 : 2 * √(1 - y) * √((1 - z) * y) ≤ 1 - y * z := by
    convert bound_aux y (1 - z) y0 y1 (sub_pos.mpr z1) (sub_lt_self 1 z0) using 2
    · rw [mul_comm]
    · ring
  have hx : 0 < 1 - x := sub_pos.mpr x1
  have hy : 0 < 1 - y := sub_pos.mpr y1
  have hz : 0 < 1 - z := sub_pos.mpr z1
  have hden : 0 ≤ 1 - (1 - z) * x :=
    (by positivity : 0 ≤ 2 * √(1 - x) * √(x * z)).trans h1
  calc
    _ ≤ x * (1 - x) * y * (1 - y) * z * (1 - z) /
        (2 * √(1 - x) * √(x * z) * 2 * √(1 - y) * √((1 - z) * y)) := by
      refine div_le_div₀ (by positivity) (le_refl _) (by positivity) ?_
      simpa only [mul_assoc] using
        mul_le_mul h1 h2 (by positivity) hden
    _ = √x * √(1 -x) * (√y * √(1 - y)) * (√z * √(1 - z)) / 4 := by
      rw [Real.sqrt_mul (le_of_lt x0) z, Real.sqrt_mul hz.le y]
      calc _
        _ =
            ((x * (1 - x)) * (y * (1 - y)) * (z * (1 - z))) /
              (4 * (√x * √(1 - x)) * (√y * √(1 - y)) * (√z * √(1 - z))) := by
          ring
        _ =
            (x / √x) * ((1 - x) / √(1 - x)) * (y / √y) *
              ((1 - y) / √(1 -y)) * (z / √z) * ((1 - z) / √(1 - z)) / 4 := by
          ring
        _ = _ := by
          simpa only [Real.div_sqrt] using (by ring)
    _ ≤ (1 / 2) * (1 / 2) * (1 / 2) / 4 := by
      gcongr
      · exact max_value x0 x1
      · exact max_value y0 y1
      · exact max_value z0 z1
    _ < (1 / 30 : ℝ) := by norm_num

lemma bound'' (x y z : ℝ) (x0 : 0 < x) (x1 : x < 1) (y0 : 0 < y) (y1 : y < 1)
    (z0 : 0 < z) (z1 : z < 1) :
    x * (1 - x) * y * (1 - y) * z * (1 - z) / (1 - (1 - x * y) * z) <
      (1 / 30 : ℝ) := by
  let s := √(x * y)
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s ≤ 1 := by
    change √(x * y) ≤ 1
    rw [Real.sqrt_le_one]
    nlinarith
  have hs_sq : s ^ 2 = x * y := by
    change (√(x * y)) ^ 2 = x * y
    rw [pow_two, Real.mul_self_sqrt]
    positivity
  have hxy_le : (1 - x) * (1 - y) ≤ (1 - s) ^ 2 := by
    have h_amgm : 2 * s ≤ x + y := by
      have hsqrtx : √x * √x = x := Real.mul_self_sqrt (le_of_lt x0)
      have hsqrty : √y * √y = y := Real.mul_self_sqrt (le_of_lt y0)
      have hsqrtxy : √x * √y = s := by
        change √x * √y = √(x * y)
        rw [← Real.sqrt_mul (le_of_lt x0) y]
      nlinarith only [sq_nonneg (√x - √y), hsqrtx, hsqrty, hsqrtxy]
    nlinarith only [h_amgm, hs_sq]
  have hden_pos : 0 < 1 - (1 - x * y) * z := by
    nlinarith only [z1, mul_pos (mul_pos x0 y0) z0]
  have hden_pos_s : 0 < 1 - (1 - s ^ 2) * z := by
    rw [hs_sq]
    exact hden_pos
  have hfrac :
      z * (1 - z) / (1 - (1 - s ^ 2) * z) ≤ 1 / (1 + s) ^ 2 := by
    rw [div_le_div_iff₀ hden_pos_s (by positivity : 0 < (1 + s) ^ 2)]
    ring_nf
    nlinarith only [sq_nonneg (1 - (1 + s) * z)]
  have hratio_nonneg : 0 ≤ s * (1 - s) / (1 + s) := by positivity
  have hratio_le : s * (1 - s) / (1 + s) ≤ (2 / 11 : ℝ) := by
    rw [div_le_iff₀ (by positivity : 0 < 1 + s)]
    have hquad : 0 ≤ 11 * s ^ 2 - 9 * s + 2 := by
      nlinarith only [sq_nonneg (22 * s - 9)]
    nlinarith only [hquad]
  have hratio_sq_le : (s * (1 - s) / (1 + s)) ^ 2 ≤ (2 / 11 : ℝ) ^ 2 := by
    exact pow_le_pow_left₀ hratio_nonneg hratio_le 2
  have hnum_le :
      x * (1 - x) * y * (1 - y) * z * (1 - z) ≤
        s ^ 2 * (1 - s) ^ 2 * z * (1 - z) := by
    calc
      x * (1 - x) * y * (1 - y) * z * (1 - z)
          = s ^ 2 * ((1 - x) * (1 - y)) * (z * (1 - z)) := by
            rw [hs_sq]
            ring
      _ ≤ s ^ 2 * (1 - s) ^ 2 * (z * (1 - z)) := by
        gcongr
      _ = s ^ 2 * (1 - s) ^ 2 * z * (1 - z) := by ring
  calc
    x * (1 - x) * y * (1 - y) * z * (1 - z) / (1 - (1 - x * y) * z)
        ≤ s ^ 2 * (1 - s) ^ 2 * z * (1 - z) / (1 - (1 - s ^ 2) * z) := by
          rw [← hs_sq]
          refine div_le_div₀ ?_ hnum_le hden_pos_s (le_refl _)
          positivity
    _ = s ^ 2 * (1 - s) ^ 2 * (z * (1 - z) / (1 - (1 - s ^ 2) * z)) := by
      ring
    _ ≤ s ^ 2 * (1 - s) ^ 2 * (1 / (1 + s) ^ 2) := by
      gcongr
    _ = (s * (1 - s) / (1 + s)) ^ 2 := by
      field_simp [(by positivity : 0 < 1 + s).ne']
    _ ≤ (2 / 11 : ℝ) ^ 2 := hratio_sq_le
    _ < (1 / 30 : ℝ) := by norm_num

end LeanPool.Zeta3Irrational
-- ===== from LeanPool/Zeta3Irrational/Chebyshev.lean =====
/-
Copyright (c) 2026 Junqi Liu, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junqi Liu, Jujian Zhang
-/


/-!
# Chebyshev estimates needed for the ζ(3) irrationality argument

This file ports the elementary, `sorry`-free Chebyshev estimate used by the
upstream PrimeNumberTheoremAnd development. It gives an eventual bound
`ψ x ≤ 1.13 x`, enough to control the lcm denominator in Beukers' proof.
-/


namespace LeanPool.Zeta3Irrational
namespace ChebyshevAux

open Real Finsupp Finset
open ArithmeticFunction hiding log
open Asymptotics Filter
open scoped Chebyshev

-- (removed: attribute local fun_prop DifferentiableAt.differentiableWithinAt)

private lemma Finset.Ioc_eq_Icc (M N : ℕ) : Finset.Ioc N M = Finset.Icc (N + 1) M := by
  ext n
  simp_all

private lemma Ioc_eq_Icc (M N : ℕ) : Finset.Ioc N M = Finset.Icc (N + 1) M :=
  Finset.Ioc_eq_Icc M N

/-- The logarithm of `⌊x⌋₊!`, written as a sum of `log n` for `1 ≤ n ≤ x`. -/
noncomputable def T (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, log n

theorem T.le (x : ℝ) (hx : 1 ≤ x) : T x ≤ x * log x - x + 1 + log x := by
  rw [T, ← Ico_insert_right <| Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr hx).ne',
    sum_insert right_notMem_Ico]
  have : MonotoneOn log (Set.Icc (1 : ℕ) ⌊x⌋₊) :=
    fun a ha _ _ hab ↦ log_le_log (lt_of_lt_of_le one_pos (by grind)) hab
  have : ∑ n ∈ Finset.Ico 1 ⌊x⌋₊, log n ≤ ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 :=
    calc ∑ n ∈ Finset.Ico 1 ⌊x⌋₊, log n
        ≤ ∫ t in (1 : ℕ)..(⌊x⌋₊ : ℕ), log t := this.sum_le_integral_Ico <|
          Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr hx).ne'
      _ = ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by simp
  have h1 : (1 : ℝ) ≤ ⌊x⌋₊ := by simp_all
  have h3 : ∀ t ∈ interior (Set.Ici 1),
      DifferentiableWithinAt ℝ (_root_.id * log - _root_.id) (interior (Set.Ici 1)) t := by
    intro t ht
    simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at ht
    apply DifferentiableAt.differentiableWithinAt
    fun_prop (disch := exact ne_of_gt (by linarith))
  have h4 : ∀ t ∈ interior (Set.Ici 1), 0 ≤ deriv (fun t ↦ t * log t - t) t := by
    intro t ht
    simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at ht
    have : DifferentiableAt ℝ (fun t ↦ t * log t) t := by fun_prop (disch := positivity)
    have hderiv : deriv (fun t ↦ t * log t - t) t = log t := by
      simp [show (fun t ↦ t * log t - t) = (fun t ↦ t * log t) - _root_.id by rfl,
        deriv_sub this differentiableAt_id, deriv_mul_log (by linarith)]
    exact hderiv ▸ log_nonneg (le_of_lt ht)
  have h5 : ContinuousOn (fun t ↦ t * log t - t) (Set.Ici 1) := by fun_prop
  have h2 : MonotoneOn (fun t ↦ t * log t - t) (Set.Ici 1) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 1) h5 h3 h4
  have : (⌊x⌋₊ : ℝ) * log ⌊x⌋₊ - ⌊x⌋₊ ≤ x * log x - x := by
    exact h2 (Set.mem_Ici.mpr h1) (Set.mem_Ici.mpr hx) <| Nat.floor_le (by grind)
  linarith [log_le_log (by positivity) <| Nat.floor_le (by linarith)]

theorem T.ge (x : ℝ) (hx : 1 ≤ x) : T x ≥ x * log x - x + 1 - log x := by
  have hone_le_floor : 1 ≤ ⌊x⌋₊ := Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr hx).ne'
  simp only [T, ← Ico_insert_right hone_le_floor, sum_insert right_notMem_Ico]
  have mono_log : MonotoneOn log (Set.Icc (1 : ℕ) ⌊x⌋₊) := fun a ha _ _ hab ↦
    log_le_log (lt_of_lt_of_le one_pos (by simpa using ha.1)) hab
  have h1 : ∀ n ≥ 1, ∑ i ∈ Ico 1 n, log (i + 1 : ℕ) = log n + ∑ i ∈ Ico 1 n, log i := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih => grind [Nat.Ico_succ_right_eq_insert_Ico]
  have sum_shift : ∑ i ∈ Ico 1 ⌊x⌋₊, log (i + 1 : ℕ) =
      log ⌊x⌋₊ + ∑ i ∈ Ico 1 ⌊x⌋₊, log i :=
    h1 ⌊x⌋₊ hone_le_floor
  have int_le_T :
      ∫ t in (1 : ℕ)..(⌊x⌋₊ : ℕ), log t ≤ log ⌊x⌋₊ + ∑ n ∈ Ico 1 ⌊x⌋₊, log n := by
    linarith [MonotoneOn.integral_le_sum_Ico hone_le_floor mono_log, sum_shift]
  have int_eq : ∫ t in (1 : ℕ)..(⌊x⌋₊ : ℕ), log t =
      ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by
    simp
  have h2 : ∫ t in (⌊x⌋₊ : ℝ)..x, log t ≤ (x - ⌊x⌋₊) * log x := by
    calc ∫ t in (⌊x⌋₊ : ℝ)..x, log t
      ≤ ∫ _ in (⌊x⌋₊ : ℝ)..x, log x :=
          intervalIntegral.integral_mono_on (Nat.floor_le <| by linarith)
            intervalIntegral.intervalIntegrable_log' intervalIntegrable_const fun t ht ↦
              log_le_log (lt_of_lt_of_le (by positivity) ht.1) ht.2
      _ = (x - ⌊x⌋₊) * log x := by simp
  have target_le_int : x * log x - x + 1 - log x ≤
      ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by
    calc x * log x - x + 1 - log x
        ≤ (x * log x - x + 1) - (x - ⌊x⌋₊) * log x := by
          nlinarith [log_nonneg hx, Nat.lt_floor_add_one x]
      _ ≤ (x * log x - x + 1) - ∫ t in (⌊x⌋₊ : ℝ)..x, log t := by grind
      _ = ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by grind [integral_log]
  linarith

theorem T.eq_sum_Lambda (x : ℝ) : T x = ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * ⌊x / n⌋₊ := by
  unfold T
  simp_rw [← log_apply, ← vonMangoldt_mul_zeta]
  rw [← Ioc_eq_Icc, sum_Ioc_mul_zeta_eq_sum]
  simp [Nat.floor_div_natCast]

/-- The floor-sum transform associated to a finitely supported weight `ν`. -/
noncomputable def E (ν : ℕ →₀ ℝ) (x : ℝ) : ℝ :=
  ν.sum (fun m w ↦ w * ⌊x / m⌋₊)

theorem T.weighted_eq_sum (ν : ℕ →₀ ℝ) (x : ℝ) :
    ν.sum (fun m w ↦ w * T (x / m)) = ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * E ν (x / n) := by
  simp_rw [T.eq_sum_Lambda, E, Finsupp.mul_sum]
  rw [← sum_finsetSum_comm]
  apply Finsupp.sum_congr fun y hy ↦ ?_
  rw [Finset.mul_sum]
  by_cases hy : y = 0
  · simp [hy]
  have one_le_y : 1 ≤ (y : ℝ) := by grind [Nat.one_le_cast]
  by_cases hx : x < 1
  · simp [hx, show x / y < 1 from div_lt_one (by linarith) |>.mpr (by linarith)]
  apply sum_subset_zero_on_sdiff
  · apply Icc_subset_Icc_right
    gcongr
    exact div_le_self (by linarith) one_le_y
  · intro t ht
    simp only [Finset.mem_sdiff, Finset.mem_Icc, not_and, not_le] at ht
    simp only [mul_eq_zero, Nat.cast_eq_zero, Nat.floor_eq_zero]
    right
    right
    apply div_lt_one (by linarith) |>.mpr
    have := ht.2 ht.1.1
    apply div_lt_iff₀ (by simp; grind) |>.mpr
    rw [Nat.floor_lt <| div_nonneg (by linarith) (by linarith)] at this
    have := div_lt_iff₀ (by linarith) |>.mp this
    rwa [mul_comm] at this
  · grind

open Finsupp in
/-- Chebyshev's finite-difference weight used to compare `ψ x` with `ψ (x / 6)`. -/
noncomputable def ν : ℕ →₀ ℝ :=
  single 1 1 - single 2 1 - single 3 1 - single 5 1 + single 30 1

private lemma ν_support : ν.support = {1, 2, 3, 5, 30} := by
  norm_num [ν, Finset.ext_iff]
  grind

private lemma ν_sum_mul (f : ℕ → ℝ) :
    ν.sum (fun m w ↦ w * f m) = f 1 - f 2 - f 3 - f 5 + f 30 := by
  rw [ν, sum_add_index (by simp) (by intros; ring)]
  grind only [sum_single_index, sum_sub_index]

private lemma E_nu_expand (y : ℝ) :
    E ν y = ⌊y⌋₊ - ⌊y / 2⌋₊ - ⌊y / 3⌋₊ - ⌊y / 5⌋₊ + ⌊y / 30⌋₊ := by
  rw [E, ν, sum_add_index' (by grind) (by grind)]
  grind [sum_single_index, sum_sub_index]

private lemma floor_div_bounds {y : ℝ} (hy : 0 ≤ y) {k : ℕ} (hk : 1 ≤ k) :
    k * ⌊y / k⌋₊ ≤ ⌊y⌋₊ ∧ ⌊y⌋₊ < k * ⌊y / k⌋₊ + k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hdivnn : 0 ≤ y / k := div_nonneg hy hk'.le
  refine ⟨Nat.le_floor ?_, ?_⟩
  · push_cast
    exact (mul_le_mul_of_nonneg_left (Nat.floor_le hdivnn) hk'.le).trans_eq
      (mul_div_cancel₀ _ hk'.ne')
  · have hlt : y / k < ⌊y / k⌋₊ + 1 := Nat.lt_floor_add_one (y / k)
    have hy_lt : y < (k : ℝ) * (⌊y / k⌋₊ + 1) := by
      simpa only [mul_comm] using (div_lt_iff₀ hk').mp hlt
    have : (⌊y⌋₊ : ℝ) < (k : ℝ) * (⌊y / k⌋₊ + 1) := (Nat.floor_le hy).trans_lt hy_lt
    exact_mod_cast this

theorem E_nu_eq_one (x : ℝ) (hx : x ∈ Set.Ico 1 6) : E ν x = 1 := by
  obtain ⟨h1, h6⟩ := hx
  have hx0 : (0 : ℝ) ≤ x := by linarith
  simp only [E_nu_expand, Nat.floor_eq_zero.mpr (by linarith : x / 30 < 1)]
  have hflb : 1 ≤ ⌊x⌋₊ := by rwa [Nat.one_le_floor_iff]
  have hfub : ⌊x⌋₊ ≤ 5 := Nat.lt_succ_iff.mp (Nat.floor_lt' (by grind) |>.mpr h6)
  have h2 := floor_div_bounds hx0 (k := 2) (by norm_num)
  have h3 := floor_div_bounds hx0 (k := 3) (by norm_num)
  have h5 := floor_div_bounds hx0 (k := 5) (by norm_num)
  push_cast at h2 h3 h5
  rw [show ⌊x⌋₊ = ⌊x / 2⌋₊ + ⌊x / 3⌋₊ + ⌊x / 5⌋₊ + 1 by omega]
  grind

theorem E_nu_period (x : ℝ) (hx : x ≥ 0) : E ν (x + 30) = E ν x := by
  have h (k : ℝ) : (x + 30) / k = x / k + 30 / k := by ring
  simp_rw [E_nu_expand, h 2, h 3, h 5, h 30]
  norm_num
  repeat rw [Nat.floor_add_ofNat (by positivity)]
  rw [Nat.floor_add_one (by positivity)]
  grind

theorem E_nu_bound (x : ℝ) (hx : x ≥ 0) : 0 ≤ E ν x ∧ E ν x ≤ 1 := by
  have base (y : ℝ) (hy0 : 0 ≤ y) (hy30 : y < 30) : 0 ≤ E ν y ∧ E ν y ≤ 1 := by
    simp only [E_nu_expand, Nat.floor_eq_zero.mpr (by linarith : y / 30 < 1), Nat.cast_zero,
      add_zero]
    have h2 := floor_div_bounds hy0 (k := 2) (by norm_num)
    have h3 := floor_div_bounds hy0 (k := 3) (by norm_num)
    have h5 := floor_div_bounds hy0 (k := 5) (by norm_num)
    push_cast at h2 h3 h5
    have hfy : ⌊y⌋₊ < 30 := Nat.floor_lt' (by norm_num) |>.mpr (by exact_mod_cast hy30)
    have hlb : ⌊y / 2⌋₊ + ⌊y / 3⌋₊ + ⌊y / 5⌋₊ ≤ ⌊y⌋₊ := by omega
    have hub : ⌊y⌋₊ ≤ ⌊y / 2⌋₊ + ⌊y / 3⌋₊ + ⌊y / 5⌋₊ + 1 := by omega
    have hlb' : ((⌊y / 2⌋₊ + ⌊y / 3⌋₊ + ⌊y / 5⌋₊ : ℕ) : ℝ) ≤ (⌊y⌋₊ : ℝ) := by
      exact_mod_cast hlb
    have hub' : (⌊y⌋₊ : ℝ) ≤ ((⌊y / 2⌋₊ + ⌊y / 3⌋₊ + ⌊y / 5⌋₊ + 1 : ℕ) : ℝ) := by
      exact_mod_cast hub
    push_cast at hlb' hub'
    refine ⟨by linarith, by linarith⟩
  let y := x - ⌊x / 30⌋₊ * 30
  have hy : 0 ≤ y ∧ y < 30 := ⟨by linarith [Nat.floor_le (by positivity : 0 ≤ x / 30)], by
    linarith [Nat.lt_floor_add_one (x / 30)]⟩
  have hxy : E ν x = E ν y := by
    have : x = y + ⌊x / 30⌋₊ * 30 := by ring
    rw [this]
    induction ⌊x / 30⌋₊ with
    | zero => simp
    | succ n ih =>
        simp [add_mul, ← add_assoc, E_nu_period _ (by linarith : y + n * 30 ≥ 0), ih]
  exact hxy ▸ base y hy.1 hy.2

/-- The weighted logarithmic factorial sum used to bound increments of `ψ`. -/
noncomputable def U (x : ℝ) : ℝ :=
  ν.sum (fun m w ↦ w * T (x / m))

theorem psi_diff_le_weighted (x : ℝ) (hx : x > 0) : ψ x - ψ (x / 6) ≤ U x := by
  unfold U Chebyshev.psi
  rw [T.weighted_eq_sum, ← Ioc_eq_Icc]
  have subset : Ioc 0 ⌊x / 6⌋₊ ⊆ Ioc 0 ⌊x⌋₊ := by
    apply Ioc_subset_Ioc_right
    gcongr
    exact div_le_self hx.le (by norm_num)
  rw [← sum_sdiff_eq_sub subset, ← sum_sdiff subset]
  refine le_add_of_le_of_nonneg (sum_le_sum fun n hn ↦ ?_)
    (sum_nonneg fun n hn ↦ mul_nonneg vonMangoldt_nonneg ?_)
  · rw [E_nu_eq_one, mul_one]
    simp_all only [gt_iff_lt, Finset.mem_sdiff, Finset.mem_Ioc, not_and, not_le, Set.mem_Ico]
    refine ⟨one_le_div (by simp; grind) |>.mpr <| Nat.le_floor_iff hx.le |>.mp hn.1.2, ?_⟩
    have := hn.2 hn.1.1
    apply div_lt_iff₀ (by simp; grind) |>.mpr
    rw [Nat.floor_lt <| div_nonneg (by linarith) (by linarith)] at this
    have := div_lt_iff₀ (by linarith) |>.mp this
    rwa [mul_comm] at this
  · exact E_nu_bound _ (div_nonneg hx.le (by simp)) |>.1

/-- The main linear coefficient in the Chebyshev increment estimate. -/
noncomputable def a : ℝ :=
  -ν.sum (fun m w ↦ w * log m / m)

lemma a_simpl : a = (7 / 15) * Real.log 2 + (3 / 10) * Real.log 3 + (1 / 6) * Real.log 5 := by
  norm_num [a, Finsupp.sum, single_apply, ν_support]
  norm_num [Finset.sum, ν]
  grind [show (30 : ℝ) = 2 * 3 * 5 by ring, log_mul, log_mul]

theorem a_bound : a ∈ Set.Icc 0.92129 0.92130 := by
  norm_num [ChebyshevAux.a_simpl]
  constructor
  · linarith only [Real.log_two_gt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9]
  · linarith only [Real.log_two_lt_d9, Real.log_three_lt_d9, Real.log_five_lt_d9]

/-- The error term in Stirling's integral approximation for `T x`. -/
noncomputable def e (x : ℝ) : ℝ :=
  T x - (x * log x - x + 1)

lemma U_bound.lemma_1 (x : ℝ) : T x = x * log x - x + 1 + e x := by
  unfold e
  ring

lemma U_bound.lemma_2 (x : ℝ) (hx : 1 ≤ x) : |e x| ≤ log x := by
  rw [abs_le]
  unfold e
  constructor <;> linarith [T.ge x hx, T.le x hx]

lemma U_bound.lemma_3 (x : ℝ) :
    U x = ν.sum (fun m w ↦ w * ((x / m) * log (x / m))) -
          ν.sum (fun m w ↦ w * (x / m)) +
          ν.sum (fun _m w ↦ w) +
          ν.sum (fun m w ↦ w * e (x / m)) := by
  simp [U, Finsupp.sum, U_bound.lemma_1, sub_eq_add_neg, add_mul, mul_comm, sum_add_distrib]

lemma U_bound.lemma_4 (x : ℝ) (hx : 0 < x) :
    ν.sum (fun m w ↦ w * ((x / m) * log (x / m))) = a * x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have ha : a = -(log 1 / 1 - log 2 / 2 - log 3 / 3 - log 5 / 5 + log 30 / 30) := by
    simp_rw [a, mul_div_assoc]
    rw [ν_sum_mul (fun m ↦ log m / m)]
    simp_all
  rw [ν_sum_mul (fun m ↦ (x / m) * log (x / m)), ha]
  simp [Real.log_div hx0]
  ring

lemma U_bound.lemma_5 (x : ℝ) : ν.sum (fun m w ↦ w * (x / m)) = 0 := by
  rw [ν_sum_mul (fun m ↦ x / m)]
  push_cast
  ring

lemma U_bound.lemma_6 : ν.sum (fun _ w ↦ w) = (-1 : ℝ) := by
  have := ν_sum_mul (fun _ ↦ (1 : ℝ))
  simp_all

lemma Finsupp.abs_sum_le (A : Type*) (ν : A →₀ ℝ) (g : A → ℝ → ℝ) : |ν.sum g| ≤ ν.sum |g| := by
  simp_rw [Finsupp.sum.eq_1]
  exact abs_sum_le_sum_abs (fun i ↦ g i (ν i)) ν.support

private lemma log_30_gt : (3.401197 : ℝ) < log 30 := by
  have h30 : log (30 : ℝ) = log 2 + log 3 + log 5 := by
    rw [show (30 : ℝ) = (2 * 3) * 5 by norm_num, log_mul, log_mul] <;> norm_num
  linarith only [h30, Real.log_two_gt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9]

theorem U_bound (x : ℝ) (hx : 30 ≤ x) : |U x - a * x| ≤ 5 * log x - 5 := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  rw [U_bound.lemma_3, U_bound.lemma_4 x hxpos]
  ring_nf
  have hlin : ν.sum (fun m w ↦ x * w * (↑m)⁻¹) = 0 := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm] using U_bound.lemma_5 x
  rw [hlin]
  ring_nf
  rw [U_bound.lemma_6]
  grw [abs_add_le, Finsupp.abs_sum_le]
  norm_num
  have hsupp_eq : ν.support = {1, 2, 3, 5, 30} := ν_support
  have hmem_of_supp : ∀ i ∈ ν.support, 0 < i ∧ i ≤ 30 := fun i hi ↦ by
    have : i ∈ ({1, 2, 3, 5, 30} : Finset ℕ) := hsupp_eq ▸ hi
    simp only [mem_insert, mem_singleton] at this
    constructor <;> omega
  have h : ν.sum |fun m w ↦ w * e (x * (↑m)⁻¹)| ≤
      ν.sum (fun m w ↦ |w| * log (x * (↑m)⁻¹)) := by
    apply Finsupp.sum_le_sum
    intro i hi
    simp only [Pi.abs_apply, abs_mul]
    obtain ⟨hi_pos, hi_le⟩ := hmem_of_supp i hi
    have hxi : 1 ≤ x * (↑i)⁻¹ := by
      rw [le_mul_inv_iff₀ (by exact_mod_cast hi_pos)]
      linarith [show (i : ℝ) ≤ 30 from by exact_mod_cast hi_le]
    gcongr
    exact U_bound.lemma_2 _ hxi
  grw [h]
  have hlog_split : ν.sum (fun m w ↦ |w| * log (x * (m : ℝ)⁻¹)) =
      log x * ν.sum (fun m w ↦ |w|) - ν.sum (fun m w ↦ |w| * log (↑m : ℝ)) := by
    simp only [Finsupp.sum]
    conv_rhs => rw [Finset.mul_sum, ← sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    have hm_pos : (0 : ℝ) < m := by exact_mod_cast (hmem_of_supp m hm).1
    rw [← div_eq_mul_inv, Real.log_div (ne_of_gt hxpos) (ne_of_gt hm_pos)]
    ring
  rw [hlog_split]
  have expand_sum : ∀ f : ℕ → ℝ → ℝ, (∀ n, f n 0 = 0) →
      ν.sum f = f 1 1 + f 2 (-1) + f 3 (-1) + f 5 (-1) + f 30 1 := by
    intro f hf
    rw [Finsupp.sum_of_support_subset _ hsupp_eq.le _ (by intros; simp [hf])]
    simp only [sum_insert (by decide : (1 : ℕ) ∉ ({2, 3, 5, 30} : Finset ℕ)),
      sum_insert (by decide : (2 : ℕ) ∉ ({3, 5, 30} : Finset ℕ)),
      sum_insert (by decide : (3 : ℕ) ∉ ({5, 30} : Finset ℕ)),
      sum_insert (by decide : (5 : ℕ) ∉ ({30} : Finset ℕ)), sum_singleton, ν,
      Finsupp.sub_apply, Finsupp.add_apply, Finsupp.single_apply]
    norm_num
    ring
  have habs : ν.sum (fun m w ↦ |w|) = 5 := by
    rw [expand_sum _ (by intros; simp)]
    norm_num
  have hgeq6 : ν.sum (fun m w ↦ |w| * log m) ≥ 6 := by
    have hsum_eq : ν.sum (fun m w ↦ |w| * log (m : ℝ)) =
        log 2 + log 3 + log 5 + log 30 := by
      simp_all
    linarith [Real.log_two_gt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9, log_30_gt]
  grw [hgeq6]
  rw [habs]
  linarith

theorem psi_diff_upper (x : ℝ) (hx : 30 ≤ x) : ψ x - ψ (x / 6) ≤ a * x + 5 * log x - 5 := by
  have h2 := abs_sub_le_iff.mp (U_bound x hx)
  linarith [psi_diff_le_weighted x (by linarith), h2.2]

theorem psi_upper_coarse (x : ℝ) (hx : 30 ≤ x) :
    ψ x ≤ 6 * a * x / 5 +
      (⌊log (x / 5) / log 6⌋₊ : ℝ) * (5 * log x - 5) + 180 := by
  have rpow_key : (30 : ℝ) * 6 ^ (log (x / 5) / log 6 - 1) = x := by
    rw [rpow_def_of_pos (by norm_num)]
    field_simp
    rw [exp_sub, exp_log, exp_log] <;> linarith
  have telescope (n : ℕ) : ψ x - ψ (x / 6 ^ n) =
      ∑ i ∈ Ico 0 n, (ψ (x / 6 ^ i) - ψ (x / 6 ^ (i + 1))) := by
    induction n with
    | zero => simp
    | succ n hn =>
      rw [sum_Ico_succ_top <| Nat.zero_le n, ← hn]
      ring
  have bound (n : ℕ) (h : ∀ i < n, 30 ≤ x / 6 ^ i) :
      ψ x - ψ (x / 6 ^ n) ≤
        ∑ i ∈ Ico 0 n, (a * x / 6 ^ i + 5 * log (x / 6 ^ i) - 5) := by
    rw [telescope]
    refine Finset.sum_le_sum fun i hi ↦ ?_
    convert! psi_diff_upper (x / 6 ^ i) (by grind) using 3
    · field
    · ring
  replace bound (n : ℕ) (h : ∀ i < n, 30 ≤ x / 6 ^ i) :
      ψ x - ψ (x / 6 ^ n) ≤ ∑ i ∈ Ico 0 n, (a * x / 6 ^ i + 5 * log x - 5) := by
    grw [bound n h]
    apply Finset.sum_le_sum fun i hi ↦ ?_
    gcongr
    bound
  let n := ⌊log (x / 5) / log 6⌋₊
  specialize bound n ?_
  · intro i hi
    apply le_div_iff₀ (by simp) |>.mpr
    trans (30 * 6 ^ (n - 1))
    · gcongr <;> grind
    · trans (30 * 6 ^ (log (x / 5) / log 6 - 1))
      · rw [← rpow_natCast, Nat.cast_sub]
        · gcongr
          · norm_num
          · refine Nat.floor_le <| div_nonneg ?_ ?_ <;> apply log_nonneg <;> linarith
          · norm_cast
        · apply Nat.le_floor
          norm_cast
          apply le_div_iff₀ (log_pos (by norm_num : (1 : ℝ) < 6)) |>.mpr
          rw [one_mul]
          gcongr
          linarith
      · exact rpow_key.le
  simp_rw [← add_sub, sum_add_distrib, sum_const, Nat.Ico_zero_eq_range, Finset.card_range,
    nsmul_eq_mul, tsub_le_iff_right] at bound
  apply bound.trans
  conv => lhs; arg 1; arg 1; arg 2; ext i; rw [← mul_one_div, ← one_div_pow]
  rw [← Finset.mul_sum, geom_sum_eq (by norm_num)]
  norm_num
  have h_tail : x / 6 ^ n ≤ 30 := by
    apply div_le_iff₀ (by simp) |>.mpr
    trans 30 * 6 ^ (log (x / 5) / log 6 - 1)
    · exact rpow_key.ge
    · rw [← rpow_natCast]
      gcongr
      · norm_num
      · exact Nat.sub_one_lt_floor _ |>.le
  have h_tail_nonneg : 0 ≤ x / 6 ^ n := by positivity
  calc
    a * x * (((1 / 6 : ℝ) ^ n - 1) / -(5 / 6)) + ↑n * (5 * log x - 5) +
        ψ (x / 6 ^ n)
        = ψ (x / 6 ^ n) + (a * x * (1 - (1 / 6) ^ n) / (1 - 1 / 6) +
          ↑n * (5 * log x - 5)) := by ring
    _ ≤ 6 * (x / 6 ^ n) +
          (a * x * (1 - (1 / 6) ^ n) / (1 - 1 / 6) +
        ↑n * (5 * log x - 5)) := by
          gcongr
          exact (Chebyshev.psi_le_const_mul_self h_tail_nonneg).trans (by
            have : log 4 ≤ (2 : ℝ) := by
              rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 4)]
              have h : (4 : ℝ) < Real.exp 2 := by
                rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
                nlinarith [Real.exp_one_gt_two]
              exact h.le
            nlinarith)
    _ ≤ 6 * a * x / 5 + ↑n * (5 * log x - 5) + 180 := by
      have hnonneg : 0 ≤ a * x * (1 / 6) ^ n := by
        have ha_nonneg : 0 ≤ a := by linarith [a_bound.1]
        positivity
      have htail6 : 6 * (x / 6 ^ n) ≤ 180 := by linarith only [h_tail]
      have hmain :
          a * x * (1 - (1 / 6 : ℝ) ^ n) / (1 - 1 / 6) ≤ 6 * a * x / 5 := by
        norm_num
        linarith only [hnonneg]
      linarith only [htail6, hmain]

theorem eventually_psi_le_mul :
    ∀ᶠ x : ℝ in atTop, ψ x ≤ (113 / 100 : ℝ) * x := by
  have h_logsq : (fun x : ℝ ↦ 5 * (log x) ^ 2 + 180) =o[atTop] (fun x : ℝ ↦ x) :=
    ((Real.isLittleO_pow_log_id_atTop (n := 2)).const_mul_left (5 : ℝ)).add
      (isLittleO_const_id_atTop (180 : ℝ))
  have hsmall := h_logsq.bound (c := 1 / 50) (by norm_num)
  filter_upwards [hsmall, eventually_ge_atTop (30 : ℝ), eventually_ge_atTop (5 : ℝ),
    eventually_ge_atTop (3 : ℝ)] with x hxsmall hx30 hx5 hx3
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx30
  have hlog_nonneg : 0 ≤ log x := log_nonneg (by linarith)
  have hlog1 : 1 ≤ log x := by
    rw [le_log_iff_exp_le hxpos]
    exact le_trans Real.exp_one_lt_three.le hx3
  have hlog6 : 1 ≤ log 6 := by
    rw [le_log_iff_exp_le (by norm_num : (0 : ℝ) < 6)]
    exact le_trans Real.exp_one_lt_three.le (by norm_num)
  have hrem_small : 5 * (log x) ^ 2 + 180 ≤ (1 / 50 : ℝ) * x := by
    have hnonneg : 0 ≤ 5 * (log x) ^ 2 + 180 := by positivity
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_of_nonneg hxpos.le] using hxsmall
  have hfloor_le :
      (⌊log (x / 5) / log 6⌋₊ : ℝ) ≤ log (x / 5) / log 6 := by
    apply Nat.floor_le
    apply div_nonneg
    · apply log_nonneg
      exact one_le_div (by norm_num : (0 : ℝ) < 5) |>.mpr hx5
    · linarith
  have hlog_div_le : log (x / 5) ≤ log x := by
    apply log_le_log
    · positivity
    · exact div_le_self hxpos.le (by norm_num : (1 : ℝ) ≤ 5)
  have hmiddle :
      (⌊log (x / 5) / log 6⌋₊ : ℝ) * (5 * log x - 5) ≤ 5 * (log x) ^ 2 := by
    have hfactor_nonneg : 0 ≤ 5 * log x - 5 := by linarith only [hlog1]
    have hdiv_le_log : log (x / 5) / log 6 ≤ log x :=
      div_le_of_le_mul₀ (by linarith only [hlog6]) hlog_nonneg
        (hlog_div_le.trans (le_mul_of_one_le_right hlog_nonneg hlog6))
    calc
      (⌊log (x / 5) / log 6⌋₊ : ℝ) * (5 * log x - 5)
          ≤ (log (x / 5) / log 6) * (5 * log x - 5) :=
            mul_le_mul_of_nonneg_right hfloor_le hfactor_nonneg
      _ ≤ log x * (5 * log x - 5) := by
        exact mul_le_mul_of_nonneg_right hdiv_le_log hfactor_nonneg
      _ ≤ 5 * (log x) ^ 2 := by nlinarith only [hlog_nonneg]
  calc
    ψ x ≤ 6 * a * x / 5 + (⌊log (x / 5) / log 6⌋₊ : ℝ) * (5 * log x - 5) + 180 :=
      psi_upper_coarse x hx30
    _ ≤ (111 / 100 : ℝ) * x + (5 * (log x) ^ 2 + 180) := by
      have ha : 6 * a / 5 ≤ (111 / 100 : ℝ) := by linarith only [a_bound.2]
      linarith only [mul_le_mul_of_nonneg_right ha hxpos.le, hmiddle]
    _ ≤ (111 / 100 : ℝ) * x + (1 / 50 : ℝ) * x := by gcongr
    _ = (113 / 100 : ℝ) * x := by ring

end ChebyshevAux
end LeanPool.Zeta3Irrational
-- ===== from LeanPool/Zeta3Irrational/LegendrePoly.lean =====
/-
Copyright (c) 2026 Junqi Liu, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junqi Liu, Jujian Zhang
-/

/-!
# Legendre Polynomials

In this file, we define the bkShiftedLegendre polynomials `bkShiftedLegendre n` for `n : ℕ` as a
polynomial in `ℤ[X]`. We prove some basic properties of the bkShiftedLegendre polynomials.

-/


open scoped Nat
open BigOperators Finset

variable {R : Type*}

namespace Polynomial

/-- `bkShiftedLegendre n` is the polynomial defined in terms of derivatives of order n. -/
noncomputable def bkShiftedLegendre (n : ℕ) : ℝ[X] :=
  C (n ! : ℝ)⁻¹ * derivative^[n] (X ^ n * (1 - X) ^ n)

lemma Finsum_iterate_deriv [CommRing R] (k : ℕ) (h : ℕ → ℕ) :
    derivative^[k] (∑ m ∈ Finset.range (k + 1), (h m) • ((-1) ^ m : R[X]) * X ^ (k + m)) =
    ∑ m ∈ Finset.range (k + 1), (h m) • (-1) ^ m * derivative^[k] (X ^ (k + m)) := by
  induction k + 1 with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, iterate_map_zero]
  | succ n hn =>
    rw[Finset.sum_range, Finset.sum_range, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at *
    simp only [Fin.val_castSucc, Fin.val_last, iterate_map_add, hn, add_right_inj]
    rw [nsmul_eq_mul, mul_assoc, ← nsmul_eq_mul, Polynomial.iterate_derivative_smul, nsmul_eq_mul,
      mul_assoc]
    rcases n.even_or_odd with (hn1 | hn2)
    · simp_all only [nsmul_eq_mul, Even.neg_pow, one_pow, one_mul]
    · simp_all

/-- The expand of `bkShiftedLegendre n`. -/
theorem bkShiftedLegendre_eq_sum (n : ℕ) : bkShiftedLegendre n = ∑ k ∈ Finset.range (n + 1),
  C ((-1) ^ k : ℝ) * (Nat.choose n k : ℝ[X]) * (Nat.choose (n + k) n : ℝ[X]) * X ^ k := by
  have h : ((X : ℝ[X]) - X ^ 2) ^ n =
    ∑ m ∈ range (n + 1), n.choose m • (- 1) ^ m * X ^ (n + m) := by
    rw[sub_eq_add_neg, add_comm, add_pow]
    congr! 1 with m hm
    rw[neg_pow, pow_two, mul_pow,← mul_assoc, mul_comm, mul_assoc, pow_mul_pow_sub, mul_assoc,
      ← pow_add, ← mul_assoc, nsmul_eq_mul, add_comm]
    simp_all
  rw [bkShiftedLegendre, ← mul_pow, mul_one_sub, ← pow_two, h, Finsum_iterate_deriv,
    Finset.mul_sum]
  congr! 1 with x _
  rw [← mul_assoc, Polynomial.iterate_derivative_X_pow_eq_smul, Nat.descFactorial_eq_div
    (by omega), show n + x - n = x by omega, nsmul_eq_mul, ← mul_assoc, mul_assoc,
    mul_comm]
  simp only [map_pow, map_neg, map_one]
  rw [Algebra.smul_def, algebraMap_eq, map_natCast, ← mul_assoc, ← mul_assoc, add_comm,
    Nat.add_choose, mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_comm]
  nth_rewrite 5 [mul_comm]
  congr 1
  nth_rewrite 2 [mul_comm]
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc]
  congr 1
  nth_rewrite 3 [mul_comm]
  congr 1
  ext m
  simp only [coeff_mul_C, coeff_natCast_ite, Nat.cast_ite, CharP.cast_eq_zero, ite_mul,
    zero_mul]
  by_cases h : m = 0
  · subst m
    simp only [↓reduceIte]
    rw [Nat.cast_div]
    · rw [← one_div, ← div_mul_eq_div_mul_one_div]
      norm_cast
      rw [Nat.cast_div]
      · exact Nat.factorial_mul_factorial_dvd_factorial_add x n
      · norm_cast
        apply mul_ne_zero (Nat.factorial_ne_zero x) (Nat.factorial_ne_zero n)
    · exact Nat.factorial_dvd_factorial (by omega)
    · norm_cast; exact Nat.factorial_ne_zero x
  · simp only [h, ↓reduceIte]

/-- `bkShiftedLegendre n` is an integer polynomial. -/
lemma bkShiftedLegendre_eq_int_poly (n : ℕ) : ∃ a : ℕ → ℤ, bkShiftedLegendre n =
    ∑ k ∈ Finset.range (n + 1), (a k : ℝ[X]) * X ^ k := by
  simp_rw [bkShiftedLegendre_eq_sum]
  use fun k => (- 1) ^ k * (Nat.choose n k) * (Nat.choose (n + k) n)
  simp_all

theorem differentiableAt_inv_special' (c x y z : ℝ) (n : ℕ) (hc : c ≠ 0)
    (hx : x ∈ Set.Ioo 0 1)
    (hz : z ∈ Set.Ioo 0 1) (h1 : 1 - (1 - x * y) * z = 0) :
    ¬DifferentiableAt ℝ (fun y ↦ c / (1 - (1 - x * y) * z) ^ (n + 1)) y := by
  intro h
  obtain q := h.continuousAt
  simp only [Metric.continuousAt_iff, Real.dist_eq, h1, ne_eq, Nat.succ_ne_zero,
    not_false_eq_true, zero_pow, div_zero, sub_zero, abs_div, abs_pow] at q
  simp only [Set.mem_Ioo] at hx hz
  have h₁ : |c| > 0 := by simp [hc]
  specialize q (|c|) h₁
  rcases q with ⟨q, ⟨qq, qqq⟩⟩
  set d := min (q / 2 + y) (1 / |x * z| + y)
  set d' := min (q / 2) (1 / |x * z|)
  have h' : d = d' + y := by
    simp only [d, d']
    rw [min_add_add_right]
  have hd : |d - y| < q := by
    rw [h', show d' + y - y = d' by ring]
    suffices |d'| ≤ q / 2 by linarith
    rw [abs_of_nonneg (by positivity)]
    exact min_le_left (q / 2) (1 / |x * z|)
  have hd' : 1 - (1 - x * d) * z ≠ 0 := by
    suffices 1 - (1 - x * d) * z > 0 by linarith
    rw [h',
      show 1 - (1 - x * (d' + y)) * z = 1 - (1 - x * y) * z + x * z * d' by
        ring,
      h1, zero_add]
    apply mul_pos
    · apply mul_pos <;> linarith
    simp only [d']
    apply lt_min (by positivity)
    simp only [one_div, inv_pos, abs_pos, ne_eq, mul_eq_zero, not_or]
    constructor <;> linarith
  specialize qqq hd
  rw [div_lt_iff₀] at qqq
  · rw [lt_mul_iff_one_lt_right h₁, h', show 1 - (1 - x * (d' + y)) * z =
      1 - (1 - x * y) * z + x * z * d' by ring, h1, zero_add,
      one_lt_pow_iff_of_nonneg (by positivity) (by norm_num)] at qqq
    have contra : |x * z * d'| ≤ 1 := by
      calc
      _ = |x * z| * |d'| := by rw [abs_mul]
      _ ≤ |x * z| * (1 / |x * z|) := by
        apply mul_le_mul (by linarith) _ (abs_nonneg _) (abs_nonneg _)
        rw [← abs_one_div]
        apply abs_le_abs_of_nonneg (by positivity)
        simp only [d']
        rw [abs_of_nonneg (a := x * z)]
        · exact min_le_right (q / 2) (1 / (x * z))
        · exact mul_nonneg (by linarith) (by linarith)
      _ = 1 := by
        rw [mul_div, mul_one, div_self]
        simp only [ne_eq, abs_eq_zero, mul_eq_zero, not_or]
        constructor <;> linarith
    linarith
  · simp_all

lemma n_derivative' {x z : ℝ} (n : ℕ) (hx : x ∈ Set.Ioo 0 1) (hz : z ∈ Set.Ioo 0 1) :
    (deriv^[n] fun y ↦ 1 / (1 - (1 - x * y) * z)) =
    (fun y ↦ (-1) ^ n * (n) ! * (x * z) ^ n / (1 - (1 - x * y) * z) ^ (n + 1)) := by
  induction n with
  | zero =>
    simp
  | succ n hn =>
    ext y
    rcases eq_or_ne (1 - (1 - x * y) * z) 0 with (h | hne)
    · simp only [h, ne_eq, add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
      zero_pow, div_zero]
      simp only [Set.mem_Ioo] at hx hz
      rw [Function.iterate_succ_apply', hn]
      apply deriv_zero_of_not_differentiableAt
      set c := (-1) ^ n * ↑n ! * (x * z) ^ n
      have hc : c ≠ 0 := by
        simp only [c]
        apply mul_ne_zero
        · simp only [ne_eq, mul_eq_zero, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, false_and,
            Nat.cast_eq_zero, Nat.factorial_ne_zero, or_self, not_false_eq_true]
        · apply pow_ne_zero
          nlinarith
      exact differentiableAt_inv_special' c x y z n hc hx hz h
    · rw [Function.iterate_succ_apply', hn, deriv_fun_div]
      · simp only [deriv_const', zero_mul, zero_sub]
        have h :
            (fun y ↦ (1 - (1 - x * y) * z) ^ (n + 1)) =
              fun y ↦ (1 - z + x * z * y) ^ (n + 1) := by
          ext _; ring
        rw [div_eq_div_iff]
        · rw [h, deriv_fun_pow, deriv_const_add, deriv_const_mul]
          · simp only [Nat.cast_add, Nat.cast_one, add_tsub_cancel_right, deriv_id'', mul_one,
              ← neg_mul]
            rw [show -(-1) ^ n = (-1 : ℝ) ^ (n + 1) by ring,
              show ((n + 1)! : ℝ) = (((n : ℕ) + 1) : ℝ) * (n !) by
                rw [Nat.factorial_succ]
                norm_cast]
            ring
          · apply differentiableAt_id
          · apply DifferentiableAt.add
            · apply differentiableAt_const
            · apply DifferentiableAt.mul
              · apply differentiableAt_const
              · apply differentiableAt_id
        · simp_all
        · exact pow_ne_zero (n + 1 + 1) hne
      · apply differentiableAt_const
      · apply DifferentiableAt.pow
        apply DifferentiableAt.const_sub
        apply DifferentiableAt.mul_const
        apply DifferentiableAt.const_sub
        apply DifferentiableAt.const_mul differentiableAt_id
      · exact pow_ne_zero (n + 1) hne

lemma bkShiftedLegendre_poly_eval_zero_eq_zero {m : ℕ} (h : m < n) :
    eval 0 ((⇑derivative)^[m] (X ^ n * (1 - X) ^ n) : ℝ[X]) = 0 := by
  rw [Polynomial.iterate_derivative_mul, Polynomial.eval_finsetSum]
  apply Finset.sum_eq_zero
  intro x hx
  simp_all only [Nat.succ_eq_add_one, Finset.mem_range, nsmul_eq_mul, eval_mul, eval_natCast,
    mul_eq_zero, Nat.cast_eq_zero]
  right; left
  simp only [Polynomial.iterate_derivative_X_pow_eq_smul, eval_smul, eval_pow, eval_X,
    smul_eq_mul, mul_eq_zero, Nat.cast_eq_zero, Nat.descFactorial_eq_zero_iff_lt,
    pow_eq_zero_iff', ne_eq, true_and]
  right
  suffices n - (m - x) > 0 by linarith
  simp only [gt_iff_lt, tsub_pos_iff_lt]
  rw [Nat.lt_add_one_iff] at hx
  calc
    m - x ≤ m := by simp
    _ < n := by exact h

lemma bkShiftedLegendre_poly_eval_one_eq_zero {m : ℕ} (h : m < n) :
    eval 1 ((⇑derivative)^[m] (X ^ n * (1 - X) ^ n) : ℝ[X]) = 0 := by
  rw [Polynomial.iterate_derivative_mul, Polynomial.eval_finsetSum]
  apply Finset.sum_eq_zero
  intro x hx
  simp_all only [Nat.succ_eq_add_one, Finset.mem_range, nsmul_eq_mul, eval_mul, eval_natCast,
    mul_eq_zero, Nat.cast_eq_zero]
  right; right
  rw [show (1 - X : ℝ[X]) ^ n = (X ^ n : ℝ[X]).comp (1 - X) by simp,
    Polynomial.iterate_derivative_comp_one_sub_X (p := X ^ n),
    Polynomial.iterate_derivative_X_pow_eq_smul]
  simp only [smul_comp, pow_comp, X_comp, Algebra.mul_smul_comm, eval_smul, eval_mul, eval_pow,
    eval_neg, eval_one, eval_sub, eval_X, sub_self, smul_eq_mul, mul_eq_zero, Nat.cast_eq_zero,
    Nat.descFactorial_eq_zero_iff_lt, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, ne_eq, false_and,
    true_and, false_or]
  right
  suffices n - x > 0 by linarith
  simp only [gt_iff_lt, tsub_pos_iff_lt]
  linarith

lemma bkShiftedLegendre_continuousOn {n m : ℕ} : ContinuousOn
    (fun x ↦ eval x ((⇑derivative)^[n - m] (X ^ n * (1 - X) ^ n : ℝ[X]))) (Set.uIcc 0 1) := by
  simp_rw [Polynomial.iterate_derivative_mul, Polynomial.eval_finsetSum]
  apply continuousOn_finsetSum
  intro i _
  simp_rw [Algebra.smul_def, eval_mul]
  apply ContinuousOn.mul
  · simp only [eq_natCast, eval_natCast, zero_le_one, Set.uIcc_of_le]
    apply continuousOn_const
  · apply ContinuousOn.mul
    · simp_rw [Polynomial.iterate_derivative_X_pow_eq_smul]
      simp only [eval_smul, eval_pow, eval_X, smul_eq_mul, zero_le_one,
        Set.uIcc_of_le]
      apply ContinuousOn.mul continuousOn_const (ContinuousOn.pow continuousOn_id _)
    · rw [show (1 - X : ℝ[X]) ^ n = (X ^ n : ℝ[X]).comp (1 - X) by simp,
        Polynomial.iterate_derivative_comp_one_sub_X (p := X ^ n),
        Polynomial.iterate_derivative_X_pow_eq_smul]
      simp only [smul_comp, pow_comp, X_comp, Algebra.mul_smul_comm, eval_smul, eval_mul,
        eval_pow, eval_neg, eval_one, eval_sub, eval_X, smul_eq_mul, zero_le_one,
        Set.uIcc_of_le]
      refine ContinuousOn.mul continuousOn_const (ContinuousOn.mul continuousOn_const ?_)
      apply ContinuousOn.pow (ContinuousOn.sub continuousOn_const continuousOn_id)

lemma special_deriv_div_continuousOn {m : ℕ} {x z : ℝ} (hx : x ∈ Set.Ioo 0 1)
    (hz : z ∈ Set.Ioo 0 1) :
    ContinuousOn (fun u ↦ (deriv^[m] fun y ↦ 1 / (1 - (1 - x * y) * z)) u) (Set.uIcc 0 1) := by
  simp_rw [n_derivative' m hx hz]
  apply ContinuousOn.div continuousOn_const
  · apply ContinuousOn.pow
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.mul _ continuousOn_const
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.mul continuousOn_const continuousOn_id
  · intro y hy
    simp only [zero_le_one, Set.uIcc_of_le, Set.mem_Icc, Set.mem_Ioo] at hy hx hz
    apply pow_ne_zero
    suffices 1 - (1 - x * y) * z > 0 by linarith
    simp only [sub_pos]
    suffices (1 - x * y) * z ≤ z by linarith
    simp_all

lemma integral_bkShiftedLegendre_mul_smooth_eq_aux {x z : ℝ} (n m : ℕ) (h : m ≤ n)
    (hx : x ∈ Set.Ioo 0 1) (hz : z ∈ Set.Ioo 0 1) : ∫ (y : ℝ) in (0)..1,
    eval y ((⇑derivative)^[n] (X ^ n * (1 - X) ^ n)) * (fun y ↦ 1 / (1 - (1 - x * y) * z)) y =
    (- 1) ^ m * ∫ (y : ℝ) in (0)..1, eval y ((⇑derivative)^[n - m] (X ^ n * (1 - X) ^ n)) *
    (deriv^[m] fun y ↦ 1 / (1 - (1 - x * y) * z)) y:= by
  induction m with
  | zero =>
    simp
  | succ m hm =>
    have h₀ : m < n := by linarith
    have h₁ : n - (m + 1) < n := by omega
    rw [hm (LT.lt.le h₀), pow_add, pow_one, mul_assoc]
    congr
    symm
    rw [show n - m = n - (m + 1) + 1 by omega, Function.iterate_succ_apply']
    rw [neg_one_mul, neg_eq_iff_eq_neg,
      intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (u := fun u ↦ eval u ((⇑derivative)^[n - (m + 1)] (X ^ n * (1 - X) ^ n : ℝ[X])))
      (u' := fun u ↦
        eval u
          (derivative
            ((⇑derivative)^[n - (m + 1)] (X ^ n * (1 - X) ^ n : ℝ[X]))))
      (v := fun u ↦ (deriv^[m] fun y ↦ 1 / (1 - (1 - x * y) * z)) u)]
    · rw [bkShiftedLegendre_poly_eval_one_eq_zero h₁, bkShiftedLegendre_poly_eval_zero_eq_zero h₁]
      simp only [one_div, zero_mul, sub_self, zero_sub, Function.iterate_succ_apply']
    · apply bkShiftedLegendre_continuousOn
    · apply special_deriv_div_continuousOn hx hz
    · intro x _
      simp_rw [Polynomial.iterate_derivative_mul, Polynomial.eval_finsetSum]
      simp only [Nat.succ_eq_add_one, nsmul_eq_mul, eval_mul, eval_natCast, map_sum,
        eval_finsetSum]
      apply HasDerivAt.fun_sum
      intro i _
      simp only [derivative_mul, derivative_natCast, zero_mul, zero_add, eval_mul, eval_natCast,
        eval_add]
      apply HasDerivAt.const_mul
      apply HasDerivAt.mul
      · rw [Polynomial.iterate_derivative_X_pow_eq_smul]
        simp only [eval_smul, eval_pow, eval_X, smul_eq_mul, LinearMapClass.map_smul,
          derivative_X_pow, map_natCast, eval_mul, eval_natCast]
        apply HasDerivAt.const_mul
        apply hasDerivAt_pow
      · rw [show (1 - X : ℝ[X]) ^ n = (X ^ n : ℝ[X]).comp (1 - X) by simp,
          Polynomial.iterate_derivative_comp_one_sub_X (p := X ^ n),
          Polynomial.iterate_derivative_X_pow_eq_smul]
        simp only [smul_comp, pow_comp, X_comp, Algebra.mul_smul_comm, eval_smul, eval_mul,
          eval_pow, eval_neg, eval_one, eval_sub, eval_X, smul_eq_mul, LinearMapClass.map_smul]
        apply HasDerivAt.const_mul
        simp only [derivative_mul, eval_add, eval_mul, eval_pow, eval_sub, eval_one, eval_X,
          eval_neg]
        have h1 : (derivative ((-1) ^ i : ℝ[X])) = 0 := by
          rw [show ((-1) ^ i : ℝ[X]) = C ((-1) ^ i) by simp, derivative_C]
        rw [h1, eval_zero, zero_mul, zero_add]
        apply HasDerivAt.const_mul
        rw [show (1 - X : ℝ[X]) ^ (n - i) = (X ^ (n - i) : ℝ[X]).comp (1 - X) by simp,
          Polynomial.derivative_comp_one_sub_X (p := X ^ (n - i)),
          Polynomial.derivative_X_pow]
        simp only [mul_comp, pow_comp, X_comp, eval_mul, map_natCast, natCast_comp, eval_neg,
          eval_mul, eval_natCast, eval_pow, eval_sub, eval_one, eval_X]
        rw [← mul_neg_one]
        apply HasDerivAt.pow
        apply HasDerivAt.const_sub
        apply hasDerivAt_id
    · intro y hy
      simp only [Set.mem_Ioo, zero_le_one, min_eq_left, max_eq_right] at hx hy hz
      have hh : 1 - (1 - x * y) * z ≠ 0 := by
        suffices 1 - (1 - x * y) * z > 0 by linarith
        simp only [sub_pos]
        suffices (1 - x * y) * z ≤ z by linarith
        apply mul_le_of_le_one_left (by linarith)
        simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
        nlinarith
      have (u : ℝ) : deriv (deriv^[m] fun y ↦ 1 / (1 - (1 - x * y) * z)) u =
        Function.eval u (deriv (deriv^[m] fun y ↦ 1 / (1 - (1 - x * y) * z))) := by
        simp only [one_div, Function.eval]
      simp_rw [this]
      simp_rw [← Function.iterate_succ_apply', Nat.succ_eq_add_one, Function.eval,
        n_derivative' _ hx hz]
      have :
          (-1) ^ (m + 1) * ↑(m + 1)! * (x * z) ^ (m + 1) /
            (1 - (1 - x * y) * z) ^ (m + 1 + 1)
        = (0 * (1 - (1 - x * y) * z) ^ (m + 1) -
          (-1) ^ m * ↑m ! * (x * z) ^ m *
            ((m + 1) * (x * z) * (1 - (1 - x * y) * z) ^ m)) /
          ((1 - (1 - x * y) * z) ^ (m + 1)) ^ 2 := by
        simp only [zero_mul, zero_sub]
        rw [div_eq_div_iff]
        · simp only [pow_add, ← neg_mul]
          rw [show -(-1 : ℝ) ^ m = (-1 : ℝ) ^ m * (-1) ^ 1 by ring,
            show ((m + 1)! : ℝ) = (((m : ℕ) + 1) : ℝ) * (m !) by
              rw [Nat.factorial_succ]
              norm_cast]
          ring
        · apply pow_ne_zero _ hh
        · simp_all
      rw [this]
      apply HasDerivAt.div
      · apply hasDerivAt_const
      · have :
            (↑m + 1) * (x * z) * (1 - (1 - x * y) * z) ^ m =
              deriv (fun y ↦ (1 - (1 - x * y) * z) ^ (m + 1)) y := by
          simp only [show 1 - (1 - x * y) * z = 1 - z + x * z * y by ring]
          rw [deriv_fun_pow,
            show (fun y ↦ 1 - (1 - x * y) * z) = (fun y ↦ 1 - z + x * z * y) by
              ext _
              ring]
          · rw[deriv_const_add, deriv_const_mul]
            · simp only [Nat.cast_add, Nat.cast_one, add_tsub_cancel_right, deriv_id'', mul_one]
              norm_cast
              ring
            · exact differentiableAt_id
          · apply DifferentiableAt.const_sub
            apply DifferentiableAt.mul_const
            · apply DifferentiableAt.const_sub
              apply DifferentiableAt.const_mul differentiableAt_id
        simp only [this, hasDerivAt_deriv_iff]
        apply DifferentiableAt.pow
        apply DifferentiableAt.const_sub
        apply DifferentiableAt.mul_const
        · apply DifferentiableAt.const_sub
          apply DifferentiableAt.const_mul differentiableAt_id
      · apply pow_ne_zero _ hh
    · simp_rw [← Function.iterate_succ_apply', Polynomial.iterate_derivative_mul,
        Polynomial.eval_finsetSum]
      simp only [Nat.succ_eq_add_one, nsmul_eq_mul, eval_mul, eval_natCast]
      apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
      apply continuousOn_finsetSum
      intro i _
      apply ContinuousOn.mul continuousOn_const
      · apply ContinuousOn.mul
        · simp_rw [Polynomial.iterate_derivative_X_pow_eq_smul]
          simp only [eval_smul, eval_pow, eval_X, smul_eq_mul]
          apply ContinuousOn.mul continuousOn_const (ContinuousOn.pow continuousOn_id _)
        · rw [show (1 - X : ℝ[X]) ^ n = (X ^ n : ℝ[X]).comp (1 - X) by simp,
            Polynomial.iterate_derivative_comp_one_sub_X (p := X ^ n),
            Polynomial.iterate_derivative_X_pow_eq_smul]
          simp only [smul_comp, pow_comp, X_comp, Algebra.mul_smul_comm, eval_smul, eval_mul,
            eval_pow, eval_neg, eval_one, eval_sub, eval_X, smul_eq_mul]
          refine ContinuousOn.mul continuousOn_const (ContinuousOn.mul continuousOn_const ?_)
          apply ContinuousOn.pow (ContinuousOn.sub continuousOn_const continuousOn_id)
    · have : deriv (deriv^[m] fun y ↦ 1 / (1 - (1 - x * y) * z)) =
        (Function.eval · (deriv (deriv^[m] fun y ↦ 1 / (1 - (1 - x * y) * z)))) := by
        simp_all
      rw [this]
      simp_rw [← Function.iterate_succ_apply', Nat.succ_eq_add_one, Function.eval]
      apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
      rw [← Set.uIcc_of_le (by norm_num)]
      apply special_deriv_div_continuousOn hx hz

lemma integral_legendre_mul_smooth_eq {x z : ℝ} (n : ℕ) (hx : x ∈ Set.Ioo 0 1)
    (hz : z ∈ Set.Ioo 0 1) :
    ∫ (y : ℝ) in (0)..1, eval y (bkShiftedLegendre n) * (fun y ↦ 1 / (1 - (1 - x * y) * z)) y =
    (- 1) ^ n / n ! * ∫ (y : ℝ) in (0)..1, y ^ n * (1 - y) ^ n *
    (deriv^[n] fun y ↦ 1 / (1 - (1 - x * y) * z)) y := by
  simp only [eval_mul, one_div, eval_C, bkShiftedLegendre]
  simp_rw [mul_assoc, intervalIntegral.integral_const_mul]
  rw [← mul_one_div, one_div]
  nth_rw 4 [mul_comm]
  rw [mul_assoc]
  congr
  obtain h := integral_bkShiftedLegendre_mul_smooth_eq_aux (n := n) (m := n) (by norm_num) hx hz
  simp only [one_div, le_refl, tsub_eq_zero_of_le, Function.iterate_zero, id_eq,
    eval_mul, eval_pow, eval_X, eval_sub, eval_one] at h
  rw [h]
  simp_rw [← mul_assoc]

private lemma one_sub_pow_pos {x z : ℝ} (n : ℕ) (hx : x ∈ Set.Ioo 0 1)
    (hz : z ∈ Set.Ioo 0 1) (y : ℝ) (hy : y ∈ Set.Icc 0 1) :
    (1 - (1 - x * y) * z) ^ (n + 1) > 0 := by
  simp only [Set.mem_Ioo] at hx hz
  simp only [Set.mem_Icc] at hy
  apply pow_pos
  simp only [sub_pos]
  suffices (1 - x * y) * z ≤ z by linarith
  simp_all

lemma legendre_integral_special {x z : ℝ} (n : ℕ) (hx : x ∈ Set.Ioo 0 1)
    (hz : z ∈ Set.Ioo 0 1) :
    ∫ (y : ℝ) in (0)..1, eval y (bkShiftedLegendre n) * (1 / (1 - (1 - x * y) * z)) =
    ∫ (y : ℝ) in (0)..1,
      (x * y * z) ^ n * (1 - y) ^ n / (1 - (1 - x * y) * z) ^ (n + 1) := by
  rw [integral_legendre_mul_smooth_eq n hx hz, ← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_of_le (by norm_num),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  apply MeasureTheory.setIntegral_congr_fun (by simp)
  intro y hy
  simp only
  rw [n_derivative' n hx hz]
  simp_all only [Set.mem_Ioo, Set.mem_Icc]
  rw [← mul_assoc, mul_div, div_eq_div_iff]
  · rw [mul_assoc, mul_assoc, mul_assoc, mul_comm, mul_div]
    symm
    rw [eq_div_iff]
    · symm
      calc
      _ = y ^ n * ((1 - y) ^ n * (↑n ! * (x * z) ^ n * (1 - (1 - x * y) * z) ^ (n + 1))) *
        ((-1) ^ n * (-1) ^ n) := by
        ring
      _ = (x * y * z) ^ n * (1 - y) ^ n * (1 - (1 - x * y) * z) ^ (n + 1) * ↑n ! := by
        rw [← pow_add, ← two_mul, pow_mul]
        simp only [even_two, Even.neg_pow, one_pow, mul_one]
        ring
    · norm_cast
      exact Nat.factorial_ne_zero n
  · linarith [one_sub_pow_pos n hx hz y hy]
  · linarith [one_sub_pow_pos n hx hz y hy]

end Polynomial
-- ===== from LeanPool/Zeta3Irrational/Integral.lean =====
/-
Copyright (c) 2026 Junqi Liu, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junqi Liu, Jujian Zhang
-/


/-!
# LeanPool.Zeta3Irrational.Integral
-/


namespace LeanPool.Zeta3Irrational

open scoped Nat
open BigOperators Finset

lemma Nat_Ico_succ_right (a b : ℕ) : Finset.Ico a (b + 1) = Finset.Icc a b := by
  ext x
  simp_all

lemma Nat_Ico_succ_succ (a b : ℕ) :
    Finset.Ico (a + 1) (b + 1) = Finset.Ioc a b := by
  ext x
  simp_all

/-- The two-variable Apéry integral with monomial weights. -/
noncomputable abbrev J (r s : ℕ) : ℝ :=
  ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
  -(x.1 * x.2).log / (1 - x.1 * x.2) * x.1 ^ r * x.2 ^ s

/-- The extended nonnegative version of `J`. -/
noncomputable abbrev JENN (r s : ℕ) : ENNReal :=
  ∫⁻ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
  ENNReal.ofReal (- (x.1 * x.2).log / (1 - x.1 * x.2) * x.1 ^ r * x.2 ^ s)

lemma log_rpow_integral_aux (n : ℝ) (a : ℝ) (ha : 0 < a ∧ a ≤ 1) :
    ∫ (x : ℝ) in Set.Ioc a 1, |-x.log * x ^ n| =
      ∫ (x : ℝ) in Set.Ioc a 1, -x.log * x ^ n := by
  apply MeasureTheory.setIntegral_congr_fun (by measurability)
  intro x hx
  simp only [Set.mem_Ioc, neg_mul, abs_neg, abs_eq_neg_self] at *
  rw [mul_nonpos_iff]
  right
  constructor
  · apply Real.log_nonpos <;> linarith
  · apply Real.rpow_nonneg
    linarith

lemma log_rpow_integral' (n : ℝ) (hn : n > -1) (a : ℝ) (ha : 0 < a ∧ a ≤ 1) :
    ∫ (x : ℝ) in Set.Ioc a 1, -x.log * x ^ n =
    1 / (n + 1) ^ 2 - (a ^ (n + 1) / (n + 1) ^ 2 - a ^ (n + 1) * a.log / (n + 1)) := by
  let f := fun x : ℝ => x ^ (n + 1) /(n + 1) ^ 2 - x ^ (n + 1) * x.log /(n + 1)
  rw [show 1 / (n + 1) ^ 2 - (a ^ (n + 1) / (n + 1) ^ 2 - a ^ (n + 1) * a.log / (n + 1)) =
    f 1 - f a by simp[f], ← intervalIntegral.integral_of_le ha.2]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha.2 (a := a) (b := 1) (f := f)
    (f' := fun x : ℝ => -x.log * x ^ n ) ?_ ?_ ?_
  · change ContinuousOn
      (fun x : ℝ => x ^ (n + 1) / (n + 1) ^ 2 - x ^ (n + 1) * x.log / (n + 1))
      (Set.Icc a 1)
    refine ContinuousOn.sub (ContinuousOn.div_const ?_ (((n : ℝ) + 1) ^ 2)) ?_
    · apply ContinuousOn.rpow_const continuousOn_id
      intro x hx
      left
      simp only [gt_iff_lt, Set.mem_Icc, id_eq, ne_eq] at *
      linarith
    · apply ContinuousOn.div_const
      apply ContinuousOn.mul
      · apply ContinuousOn.rpow_const continuousOn_id
        intro x hx
        left
        simp only [gt_iff_lt, Set.mem_Icc, id_eq, ne_eq] at *
        linarith
      · apply ContinuousOn.log continuousOn_id
        intro x hx
        simp only [Set.mem_Icc, id_eq] at hx ⊢
        linarith
  · intro x hx
    simp only [Set.mem_Ioo] at hx
    simp only [f]
    rw [show -x.log * x ^ n = x ^ n / (↑n + 1) - (x ^ n * x.log + x ^ n / (↑n + 1)) by ring]
    apply HasDerivAt.sub
    · have h : x ^ n / (↑n + 1) = x ^ n * (↑n + 1) / (↑n + 1) ^ 2 := by
        rw[div_eq_div_iff (by linarith)]
        · ring
        · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]
          linarith
      rw [h]
      apply HasDerivAt.div_const
      rw [mul_comm]
      nth_rw 3 [show n = n + 1 - 1 by simp]
      norm_cast
      apply Real.hasDerivAt_rpow_const
      left
      linarith
    · have h :
          x ^ n * x.log + x ^ n / (↑n + 1) =
            ((↑n + 1) * x ^ n * x.log + x ^ n) / (↑n + 1) := by
        rw [add_div]
        congr 1
        rw [eq_div_iff (by linarith)]
        ring
      rw[h]
      apply HasDerivAt.div_const
      nth_rw 2 [show x ^ n = x ^ (n + 1) * (1 / x) by
        rw [mul_div, eq_div_iff (by linarith), Real.rpow_add (by linarith), mul_one,
          Real.rpow_one]]
      apply HasDerivAt.mul
      · nth_rw 3 [show n = n + 1 - 1 by simp]
        norm_cast
        apply Real.hasDerivAt_rpow_const
        left
        linarith
      · apply HasDerivAt.log (hasDerivAt_id' x) (by linarith)
  · apply IntervalIntegrable.continuousOn_mul
    · apply intervalIntegral.intervalIntegrable_rpow
      simp_all
    · apply ContinuousOn.neg
      apply ContinuousOn.log continuousOn_id
      intro x hx
      rw [Set.uIcc_of_le ha.2] at hx
      simp only [Set.mem_Icc, id_eq, ne_eq] at hx ⊢
      nlinarith

lemma log_rpow_integrable (n : ℝ) (hn : n > -1) :
    IntervalIntegrable (fun x ↦ -Real.log x * x ^ n) MeasureTheory.volume 0 1 := by
  let f := fun (x : ℝ) => -x.log * x ^ n
  apply MeasureTheory.IntegrableOn.intervalIntegrable
  rw [Set.uIcc_of_le (by norm_num), integrableOn_Icc_iff_integrableOn_Ioc]
  apply MeasureTheory.integrableOn_Ioc_of_intervalIntegral_norm_bounded_left (f := f)
    (l := Filter.atTop) (a := fun (n : ℕ) => 1 / (n + 1 : ℝ)) (a₀ := 0) (b := 1)
    (I := 1 / (n + 1) ^ 2)
  · intro i
    simp only [one_div, f]
    have hi :  0 < ((i : ℝ) + 1)⁻¹ ∧ ((i : ℝ) + 1)⁻¹ ≤ 1 := by
      constructor
      · simp only [inv_pos]; linarith
      · rw [← one_div, div_le_iff₀] <;> linarith
    rw [← Set.uIoc_of_le hi.2, ← intervalIntegrable_iff]
    apply IntervalIntegrable.continuousOn_mul
    · apply intervalIntegral.intervalIntegrable_rpow
      simp_all
    · apply ContinuousOn.neg
      apply ContinuousOn.log continuousOn_id
      intro x hx
      rw [Set.uIcc_of_le hi.2] at hx
      simp only [Set.mem_Icc, id_eq, ne_eq] at hx ⊢
      nlinarith
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
  · rw [Filter.eventually_atTop]
    use 0
    intro b _
    simp only [Real.norm_eq_abs, f]
    rw [log_rpow_integral_aux n]
    · rw [log_rpow_integral' n hn]
      · set k := _
        change _ - k ≤ _
        simp only [tsub_le_iff_right, le_add_iff_nonneg_right,
          sub_nonneg, k]
        rw [div_le_div_iff₀ (by linarith) (by nlinarith), mul_assoc, mul_le_mul_iff_of_pos_left]
        · trans 0
          · rw [mul_nonpos_iff]
            right
            constructor
            · apply Real.log_nonpos
              · simp only [one_div, inv_nonneg]
                linarith
              · rw [div_le_iff₀] <;> linarith
            · positivity
          · linarith
        · apply Real.rpow_pos_of_pos
          simp only [one_div, inv_pos]
          linarith
      · constructor
        · positivity
        · rw [div_le_one] <;> linarith
    · constructor
      · positivity
      · rw [div_le_one] <;> linarith

lemma log_rpow_integral (n : ℝ) (hn : n > -1) :
    ∫ (x : ℝ) in (0)..1, -x.log * x ^ n = 1 / (n + 1) ^ 2 := by
  let F := fun (x : ℝ) => x ^ (n + 1) * (1 - (n + 1) * x.log) / (n + 1) ^ 2
  have h1 : 1 /(n + 1) ^ 2 = F 1 - F 0 := by
    simp only [F, one_div]
    rw [Real.zero_rpow (by linarith), zero_mul, zero_div, sub_zero]
    simp_all
  rw [h1]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (by norm_num) (a := 0) (b := 1)
    (f := F) (f' := fun x : ℝ => -x.log * x ^ n ) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Set.mem_Ioo] at hx
    simp only [F, mul_sub, mul_one]
    have : -Real.log x * x ^ n = -Real.log x * x ^ n * (n + 1) ^ 2 / (n + 1) ^ 2 := by
      rw [eq_div_iff]
      nlinarith
    rw [this]
    apply HasDerivAt.div_const
    rw [show -Real.log x * x ^ n * (n + 1) ^ 2 =
      (n + 1) * x ^ n - ((n + 1) * x ^ n + Real.log x * x ^ n * (n + 1) ^ 2) by ring]
    apply HasDerivAt.sub
    · rw [show (n + 1) * x ^ n = 1 * (n + 1) * x ^ (n + 1 - 1) by simp only [one_mul,
      add_sub_cancel_right]]
      apply HasDerivAt.rpow_const (hasDerivAt_id' x)
      left; linarith
    · have : (n + 1) * x ^ n + Real.log x * x ^ n * (n + 1) ^ 2 =
        (n + 1) * x ^ n * ((n + 1) * Real.log x) +  x ^ (n + 1) * ((n + 1) / x) := by
        rw [← mul_comm_div, ← Real.rpow_sub_one (by linarith)]
        ring_nf
      rw [this]
      apply HasDerivAt.mul
      · rw [show (n + 1) * x ^ n = 1 * (n + 1) * x ^ (n + 1 - 1) by simp only [one_mul,
          add_sub_cancel_right]]
        apply HasDerivAt.rpow_const (hasDerivAt_id' x)
        left; linarith
      · apply HasDerivAt.const_mul
        rw [← one_div]
        apply HasDerivAt.log (hasDerivAt_id' x) (by linarith)
  · exact log_rpow_integrable n hn
  · simp only [Real.log_zero, mul_zero, sub_zero, mul_one, F]
    rw [Real.zero_rpow (by linarith), zero_div]
    simp_rw [mul_sub, sub_div]
    nth_rw 3 [show (0 : ℝ) = 0 / (n + 1) ^ 2 - 0 / (n + 1) ^ 2 by simp]
    refine Filter.Tendsto.sub (a := 0 / (n + 1) ^ 2) (b := 0 / (n + 1) ^ 2) ?_ ?_
    · apply Filter.Tendsto.div_const
      simp_rw [mul_one]
      nth_rw 3 [show (0 : ℝ) = 0 ^ (n + 1) by rw [Real.zero_rpow (by linarith)]]
      apply Filter.Tendsto.rpow_const
      · apply tendsto_nhdsWithin_of_tendsto_nhds
        exact fun ⦃U⦄ a ↦ a
      · right; linarith
    · apply Filter.Tendsto.div_const
      rw [show (fun a : ℝ => a ^ (n + 1) * ((n + 1) * Real.log a)) =
          (fun a => Real.log a * a ^ (n + 1) * (n + 1)) by
        funext a
        ring]
      nth_rw 3 [show (0 : ℝ) = 0 * (n + 1) by simp]
      apply Filter.Tendsto.mul_const
      apply tendsto_log_mul_rpow_nhdsGT_zero
      linarith
  · apply tendsto_nhds_of_tendsto_nhdsWithin (s := ⊤)
    apply ContinuousWithinAt.tendsto_nhdsWithin
    · apply ContinuousAt.continuousWithinAt
      simp only [F]
      apply ContinuousAt.div_const
      apply ContinuousAt.mul
      · apply ContinuousAt.rpow_const continuousAt_id
        right; linarith
      · apply ContinuousAt.sub continuousAt_const
        apply ContinuousAt.mul continuousAt_const
        apply ContinuousAt.log continuousAt_id (by norm_num)
    · simp_all

lemma ENN_log_rpow_integral (n : ℝ) (hn : n > -1) : ∫⁻ (x : ℝ) in Set.Ioo 0 1,
    ENNReal.ofReal (-x.log * x ^ n) = ENNReal.ofReal (1 / (n + 1) ^ 2) := by
  calc
  _ = ∫⁻ (x : ℝ),
      ENNReal.ofReal ((Set.Ioo 0 1).indicator (fun x => -Real.log x * x ^ n) x) := by
    rw [← MeasureTheory.lintegral_indicator]
    · congr
      ext x
      rw [Set.indicator_apply, Set.indicator_apply]
      aesop
    · measurability
  _ = ENNReal.ofReal (1 / (n + 1) ^ 2) := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
    · rw [MeasureTheory.integral_indicator (by measurability),
        ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by norm_num), log_rpow_integral n hn]
    · apply MeasureTheory.IntegrableOn.integrable_indicator _ (by measurability)
      rw [← integrableOn_Ioc_iff_integrableOn_Ioo, ← Set.uIoc_of_le (by norm_num),
        ← intervalIntegrable_iff]
      exact log_rpow_integrable n hn
    · refine MeasureTheory.ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite ?_ ?_
      · rintro s - -
        apply MeasureTheory.Integrable.integrableOn
        apply MeasureTheory.IntegrableOn.integrable_indicator _ (by measurability)
        rw [← integrableOn_Ioc_iff_integrableOn_Ioo, ← Set.uIoc_of_le (by norm_num),
          ← intervalIntegrable_iff]
        exact log_rpow_integrable n hn
      · rintro s hs -
        apply MeasureTheory.setIntegral_nonneg hs
        suffices  ∀ x, 0 ≤ (Set.Ioo 0 1).indicator (fun x ↦ -Real.log x * x ^ n) x by aesop
        intro x
        rw [Set.indicator_apply]
        by_cases h : x ∈ Set.Ioo 0 1
        · simp only [h, ↓reduceIte, neg_mul, Left.nonneg_neg_iff]
          simp only [Set.mem_Ioo] at h
          rw [mul_nonpos_iff]
          right
          constructor
          · apply Real.log_nonpos <;> linarith
          · apply Real.rpow_nonneg; linarith
        · simp only [h, ↓reduceIte, le_refl]

lemma ENN_log_pow_integral (n : ℕ) : ∫⁻ (x : ℝ) in Set.Ioo 0 1,
    ENNReal.ofReal (-x.log * x ^ n) = ENNReal.ofReal (1 / (n + 1) ^ 2) := by
  rw [← ENN_log_rpow_integral]
  · norm_cast
  · suffices 0 ≤ n by linarith
    omega

lemma ENN_pow_integral (n : ℕ) : ∫⁻ (x : ℝ) in Set.Ioo 0 1,
    ENNReal.ofReal (x ^ n) = ENNReal.ofReal (1 / (n + 1)) := by
  have h := @integral_pow 0 1 n
  rw [zero_pow, one_pow, sub_zero, intervalIntegral.integral_of_le (by norm_num),
    MeasureTheory.integral_Ioc_eq_integral_Ioo] at h
  · rw [← h, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
    · apply MeasureTheory.IntegrableOn.integrable
      rw [← integrableOn_Ioc_iff_integrableOn_Ioo, ← Set.uIoc_of_le (by norm_num),
        ← intervalIntegrable_iff]
      exact intervalIntegral.intervalIntegrable_pow n
    · apply MeasureTheory.ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter
      · rw [← integrableOn_Ioc_iff_integrableOn_Ioo, ← Set.uIoc_of_le (by norm_num),
          ← intervalIntegrable_iff]
        exact intervalIntegral.intervalIntegrable_pow n
      · rintro s hs -
        apply MeasureTheory.setIntegral_nonneg (by measurability)
        intro x hs
        simp only [Set.mem_inter_iff, Set.mem_Ioo] at hs
        by_cases h : x ∈ s
        · simp only [h, true_and] at hs
          apply pow_nonneg
          linarith
        · tauto
  · omega

lemma AEMeasurable_aux : AEMeasurable (fun (x : ℝ × ℝ × ℝ) ↦
    1 / (1 - (1 - x.2.1 * x.2.2) * x.1) * x.2.1 ^ r * x.2.2 ^ s) MeasureTheory.volume := by
  measurability

lemma integral1 {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∫ (z : ℝ) in (0)..1, 1 / (1 - (1 - a) * z) = - a.log / (1 - a) := by
  rw[← sub_pos] at ha1
  have eq1 := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) (c := 1 - a)
    (f := fun z ↦ (1 - z)⁻¹) (by positivity)
  have eq2 := intervalIntegral.mul_integral_comp_sub_mul (a := 0) (b := 1 - a)
    (f := fun x ↦ (x)⁻¹)
    (c := 1) (d := 1)
  have eq3 := integral_inv_of_pos (a := a) (b := 1) ha (by norm_num)
  simp only [mul_zero, mul_one, smul_eq_mul] at eq1
  simp only [one_div]
  rw [eq1, inv_mul_eq_div]
  simp_all

lemma sub_mul_mul_ne_zero (y : ℝ) (x : ℝ × ℝ)
    (hy : y ∈ Set.Icc 0 1) (h1 : 0 < 1 - (1 - x.1 * x.2)) : 1 - (1 - x.1 * x.2) * y ≠ 0 := by
  suffices 1 - (1 - x.1 * x.2) * y > 0 by linarith
  simp only [gt_iff_lt, sub_pos]
  by_cases hy' : y = 0
  · simp_all
  · simp only [sub_pos, Set.mem_Icc] at *
    suffices (1 - x.1 * x.2) * y < y by linarith
    rwa [mul_lt_iff_lt_one_left]
    rcases hy with ⟨hy1, _⟩
    by_contra! h
    suffices y = 0 by tauto
    linarith

lemma integrableOn_aux (x : ℝ × ℝ)
    (h1 : 0 < 1 - (1 - x.1 * x.2)) (h2 : 1 - (1 - x.1 * x.2) < 1) :
    MeasureTheory.IntegrableOn (fun t ↦ 1 / (1 - (1 - x.1 * x.2) * t))
    (Set.Ioo 0 1) MeasureTheory.volume := by
  rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
  apply intervalIntegral.integrableOn_deriv_of_nonneg
    (g := fun t => -Real.log (1 - (1 - x.1 * x.2) * t) / (1 - x.1 * x.2))
  · apply ContinuousOn.div_const
    apply ContinuousOn.neg
    apply ContinuousOn.log
    · apply ContinuousOn.sub continuousOn_const
      apply ContinuousOn.mul continuousOn_const continuousOn_id
    · intro y hy
      exact sub_mul_mul_ne_zero y x hy h1
  · intro y hy
    have h : 1 / (1 - (1 - x.1 * x.2) * y) =
      -(-(1 - x.1 * x.2)) / (1 - (1 - x.1 * x.2) * y) / (1 - x.1 * x.2) := by
      rw [neg_neg, div_div, div_eq_div_iff]
      · ring
      · exact sub_mul_mul_ne_zero y x (Set.mem_Icc_of_Ioo hy) h1
      · apply mul_ne_zero (sub_mul_mul_ne_zero y x (Set.mem_Icc_of_Ioo hy) h1)
        suffices 1 - x.1 * x.2 > 0 by linarith
        linarith
    rw [h]
    apply HasDerivAt.div_const
    rw [neg_div]
    apply HasDerivAt.neg
    apply HasDerivAt.log
    · apply HasDerivAt.const_sub
      nth_rw 2 [← mul_one (a := 1 - x.1 * x.2)]
      apply HasDerivAt.const_mul _ (hasDerivAt_id' y)
    · exact sub_mul_mul_ne_zero y x (Set.mem_Icc_of_Ioo hy) h1
  · intro y hy
    simp at hy
    apply div_nonneg (by norm_num)
    simp only [sub_nonneg]
    exact (mul_le_of_le_one_left (by linarith) (by linarith)).trans (by linarith)

lemma JENN_eq_triple_aux' (x : ℝ × ℝ) (hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) :
    ∫⁻ (w : ℝ) in Set.Ioo 0 1, ENNReal.ofReal (1 / (1 - (1 - x.1 * x.2) * w)) =
    ENNReal.ofReal (-Real.log (1 - (1 - x.1 * x.2)) / (1 - x.1 * x.2)) := by
  have h1 : 0 < 1 - (1 - x.1 * x.2) := by
    simp_all
  have h2 : 1 - (1 - x.1 * x.2) < 1 := by
    simp only [Set.mem_prod, Set.mem_Ioo, sub_sub_cancel] at *
    suffices x.1 * x.2 < x.2 by linarith
    aesop
  nth_rw 3 [show 1 - x.1 * x.2 = 1 - (1 - (1 - x.1 * x.2)) by simp]
  rw [←  integral1 (a := 1 - (1 - x.1 * x.2)) h1 h2,
    show 1 - (1 - (1 - x.1 * x.2)) = 1 - x.1 * x.2 by simp]
  rw [intervalIntegral.integral_of_le (by norm_num),
    MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
  · apply MeasureTheory.IntegrableOn.integrable
    exact integrableOn_aux x h1 h2
  · apply MeasureTheory.ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter
    · exact integrableOn_aux x h1 h2
    · rintro s hs -
      apply MeasureTheory.setIntegral_nonneg (by measurability)
      intro y hs
      simp only [Set.mem_inter_iff, Set.mem_Ioo] at hs
      by_cases h : y ∈ s
      · simp only [h, true_and] at hs
        apply div_nonneg (by norm_num)
        simp only [sub_nonneg]
        exact (mul_le_of_le_one_left (by linarith) (by linarith)).trans (by linarith)
      · tauto

lemma JENN_eq_triple_aux (x : ℝ × ℝ) (hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) :
    ∫⁻ (w : ℝ) in Set.Ioo 0 1,
      ENNReal.ofReal (1 / (1 - (1 - x.1 * x.2) * w) * x.1 ^ r * x.2 ^ s) =
    ENNReal.ofReal (-Real.log (x.1 * x.2) / (1 - x.1 * x.2) * x.1 ^ r * x.2 ^ s) := by
  calc
  _ = ENNReal.ofReal (x.1 ^ r * x.2 ^ s) *
    ENNReal.ofReal (-Real.log (1 - (1 - x.1 * x.2)) / (1 - x.1 * x.2)) := by
    rw [← JENN_eq_triple_aux' x hx]
    rw [← MeasureTheory.lintegral_const_mul]
    · congr
      ext y
      rw [← ENNReal.ofReal_mul]
      · congr 1
        field_simp
      rcases x with ⟨x1, x2⟩
      rcases hx with ⟨⟨hx1, hx1'⟩, ⟨hx2,hx2'⟩⟩
      positivity
    · apply Measurable.ennreal_ofReal
      apply Measurable.const_div
      apply Measurable.const_sub
      apply Measurable.const_mul measurable_id
  _ = ENNReal.ofReal (-Real.log (x.1 * x.2) / (1 - x.1 * x.2) * x.1 ^ r * x.2 ^ s) := by
    simp only [Set.mem_prod, Set.mem_Ioo, sub_sub_cancel] at *
    rw [mul_comm, ← ENNReal.ofReal_mul, ← mul_assoc]
    apply div_nonneg
    · simp only [Left.nonneg_neg_iff]
      apply Real.log_nonpos
      · apply mul_nonneg (by linarith) (by linarith)
      · exact (mul_le_of_le_one_left (by linarith) (by linarith)).trans (by linarith)
    · simp only [sub_nonneg]
      exact (mul_le_of_le_one_left (by linarith) (by linarith)).trans (by linarith)

lemma JENN_eq_triple (r s : ℕ) : JENN r s =
    ∫⁻ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    ENNReal.ofReal (1 / (1 - (1 - x.2.1 * x.2.2) * x.1) * x.2.1 ^ r * x.2.2 ^ s) := by
  symm
  calc
  _ = ∫⁻ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1, ∫⁻ (w : ℝ) in Set.Ioo 0 1,
    ENNReal.ofReal (1 / (1 - (1 - x.1 * x.2) * w) * x.1 ^ r * x.2 ^ s) := by
    rw [MeasureTheory.Measure.volume_eq_prod, ← MeasureTheory.Measure.prod_restrict,
      MeasureTheory.lintegral_prod, MeasureTheory.lintegral_lintegral_swap]
    · simp only
      rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod,
        ← aemeasurable_indicator_iff (by measurability)]
      apply AEMeasurable.indicator _ (by measurability)
      apply AEMeasurable.ennreal_ofReal
      exact AEMeasurable_aux
    · rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod,
        ← aemeasurable_indicator_iff (by measurability)]
      apply AEMeasurable.indicator _ (by measurability)
      apply AEMeasurable.ennreal_ofReal
      exact AEMeasurable_aux
  _ = ∫⁻ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      ENNReal.ofReal (- (x.1 * x.2).log / (1 - x.1 * x.2) * x.1 ^ r * x.2 ^ s) := by
    apply MeasureTheory.setLIntegral_congr_fun (by measurability)
    intro x hx
    exact JENN_eq_triple_aux _ hx

lemma AEMeasurable_aux' : AEMeasurable
    (fun x ↦ ENNReal.ofReal (-Real.log (x.1 * x.2) * x.1 ^ (k + r) * x.2 ^ (k + s)))
    (MeasureTheory.volume.restrict (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1)) := by
  apply AEMeasurable.ennreal_ofReal
  apply Measurable.aemeasurable
  apply Measurable.mul _ (Measurable.pow_const measurable_snd _)
  · apply Measurable.mul _ (Measurable.pow_const measurable_fst _)
    · apply Measurable.neg
      apply Measurable.log
      apply Measurable.mul measurable_fst measurable_snd

lemma aux_lintegral1 (k r s : ℕ) (x : ℝ) (hx : 0 < x ∧ x < 1) :
    ∫⁻ (a : ℝ) in Set.Ioo 0 1,
    ENNReal.ofReal (-(Real.log x * x ^ (k + r) * a ^ (k + s)))
    = ENNReal.ofReal (- x.log * x ^ (k + r) / (k + s + 1)) := by
  calc
  _ = ENNReal.ofReal (-Real.log x * x ^ (k + r)) * ∫⁻ (a : ℝ) in Set.Ioo 0 1,
    ENNReal.ofReal (a ^ (k + s)) := by
    rw [← MeasureTheory.lintegral_const_mul]
    · congr
      ext y
      rw [← ENNReal.ofReal_mul]
      · field_simp
      rcases hx with ⟨hx1, hx2⟩
      simp only [neg_mul, Left.nonneg_neg_iff]
      rw [mul_nonpos_iff]
      right
      exact ⟨Real.log_nonpos (by linarith) (by linarith), by positivity⟩
    · apply Measurable.ennreal_ofReal
      apply Measurable.pow measurable_id measurable_const
  _ = ENNReal.ofReal (- x.log * x ^ (k + r) / (k + s + 1)) := by
    rw [ENN_pow_integral, ← ENNReal.ofReal_mul, mul_one_div]
    · norm_cast
    · simp only [neg_mul, Left.nonneg_neg_iff]
      rw [mul_nonpos_iff]
      right
      constructor
      · apply Real.log_nonpos (by linarith) (by nlinarith)
      · apply pow_nonneg (by linarith)

lemma aux_lintegral2 (k r s : ℕ) (x : ℝ) (hx : 0 < x ∧ x < 1) :
    ∫⁻ (a : ℝ) in Set.Ioo 0 1,
    ENNReal.ofReal (-(Real.log a * x ^ (k + r) * a ^ (k + s)))
    = ENNReal.ofReal (x ^ (k + r) / (k + s + 1) ^ 2) := by
  calc
  _ = ENNReal.ofReal (x ^ (k + r)) * ∫⁻ (a : ℝ) in Set.Ioo 0 1,
    ENNReal.ofReal (-a.log * a ^ (k + s)) := by
    rw [← MeasureTheory.lintegral_const_mul]
    · congr
      ext y
      cases hx
      rw [← ENNReal.ofReal_mul]
      · congr 1
        ring
      positivity
    · apply Measurable.ennreal_ofReal
      apply Measurable.mul
      · apply Measurable.neg
        apply Measurable.log measurable_id
      · apply Measurable.pow measurable_id measurable_const
  _ = ENNReal.ofReal (x ^ (k + r) / (k + s + 1) ^ 2) := by
    rw [ENN_log_pow_integral, ← ENNReal.ofReal_mul, mul_one_div]
    · norm_cast
    · apply pow_nonneg (by linarith)

lemma aux_lintegral3 (k r s : ℕ) : ∫⁻ (x : ℝ) in Set.Ioo 0 1,
    ENNReal.ofReal (-x.log * x ^ (k + r) / (k + s + 1))
    = ENNReal.ofReal (1 / ((k + r + 1) ^ 2 * (k + s + 1))) := by
  calc
  _ =
      (∫⁻ (x : ℝ) in Set.Ioo 0 1, ENNReal.ofReal (-x.log * x ^ (k + r))) *
        ENNReal.ofReal (1 / (k + s + 1)) := by
    rw [← MeasureTheory.lintegral_mul_const]
    · apply MeasureTheory.setLIntegral_congr_fun (by measurability)
      rintro y ⟨hy1, hy2⟩
      change ENNReal.ofReal (-Real.log y * y ^ (k + r) / (↑k + ↑s + 1)) =
        ENNReal.ofReal (-Real.log y * y ^ (k + r)) * ENNReal.ofReal (1 / (↑k + ↑s + 1))
      rw [← ENNReal.ofReal_mul]
      · field_simp
      simp only [neg_mul, Left.nonneg_neg_iff]
      rw [mul_nonpos_iff]
      right
      refine ⟨Real.log_nonpos (by linarith) (by nlinarith), by positivity⟩
    · apply Measurable.ennreal_ofReal
      apply Measurable.mul
      · apply Measurable.neg
        apply Measurable.log measurable_id
      · apply Measurable.pow measurable_id measurable_const
  _ = ENNReal.ofReal (1 / ((k + r + 1) ^ 2 * (k + s + 1))) := by
    rw [ENN_log_pow_integral, ← ENNReal.ofReal_mul, mul_one_div, div_div]
    · norm_cast
    · positivity

lemma aux_lintegral4 (k r s : ℕ) : ∫⁻ (x : ℝ) in Set.Ioo 0 1,
    ENNReal.ofReal (x ^ (k + r) / (k + s + 1) ^ 2)
    = ENNReal.ofReal (1 / ((k + r + 1) * (k + s + 1) ^ 2)) :=
  calc
  _ =
      (∫⁻ (x : ℝ) in Set.Ioo 0 1, ENNReal.ofReal (x ^ (k + r))) *
        ENNReal.ofReal (1 / (k + s + 1) ^ 2) := by
      rw [← MeasureTheory.lintegral_mul_const]
      · apply MeasureTheory.setLIntegral_congr_fun (by measurability)
        rintro y ⟨hy1, hy2⟩
        change ENNReal.ofReal (y ^ (k + r) / (↑k + ↑s + 1) ^ 2) =
          ENNReal.ofReal (y ^ (k + r)) * ENNReal.ofReal (1 / (↑k + ↑s + 1) ^ 2)
        rw [← ENNReal.ofReal_mul]
        · field_simp
        positivity
      · measurability
  _ = ENNReal.ofReal (1 / ((k + r + 1) * (k + s + 1) ^ 2)) := by
    rw [ENN_pow_integral, ← ENNReal.ofReal_mul, mul_one_div, div_div]
    · norm_cast
    · positivity

lemma J_ENN_rs_eq_tsum_aux_intergal (r s k : ℕ) :
    ∫⁻ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    ENNReal.ofReal (- (x.1 * x.2).log * x.1 ^ (k + r) * x.2 ^ (k + s)) =
    ENNReal.ofReal
      (1 / ((k + r + 1) ^ 2 * (k + s + 1)) +
        1 / ((k + r + 1) * (k + s + 1) ^ 2)) := by
  rw [MeasureTheory.Measure.volume_eq_prod, ← MeasureTheory.Measure.prod_restrict,
      MeasureTheory.lintegral_prod]
  · calc
    _ = ∫⁻ (x : ℝ) in Set.Ioo 0 1,
      ENNReal.ofReal (- x.log * x ^ (k + r) / (k + s + 1) + x ^ (k + r) / (k + s + 1) ^ 2) := by
      apply MeasureTheory.setLIntegral_congr_fun (by measurability)
      intro x hx
      simp only [neg_mul]
      have h2 :
          ∫⁻ (y : ℝ) in Set.Ioo 0 1,
            ENNReal.ofReal (-((x * y).log * x ^ (k + r) * y ^ (k + s))) =
          ∫⁻ (y : ℝ) in Set.Ioo 0 1,
            ENNReal.ofReal (-(x.log * x ^ (k + r) * y ^ (k + s))) +
              ENNReal.ofReal (-(y.log * x ^ (k + r) * y ^ (k + s))) := by
        apply MeasureTheory.setLIntegral_congr_fun (by measurability)
        intro y hy
        simp only [← neg_mul]
        simp only [Set.mem_Ioo] at hx hy
        rw [Real.log_mul (by linarith) (by linarith), neg_add, add_mul, add_mul,
          ENNReal.ofReal_add]
        · apply mul_nonneg _ (by apply pow_nonneg (by linarith))
          apply mul_nonneg _ (by apply pow_nonneg (by linarith))
          simp only [Left.nonneg_neg_iff]
          apply Real.log_nonpos (by nlinarith) (by nlinarith)
        · apply mul_nonneg _ (by apply pow_nonneg (by linarith))
          apply mul_nonneg _ (by apply pow_nonneg (by linarith))
          simp only [Left.nonneg_neg_iff]
          apply Real.log_nonpos (by nlinarith) (by nlinarith)
      rw [h2, MeasureTheory.lintegral_add_left']
      · simp only [Set.mem_Ioo] at hx
        rw [aux_lintegral1 k r s x hx, aux_lintegral2 k r s x hx, ENNReal.ofReal_add, neg_mul]
        · apply div_nonneg _ (by positivity)
          simp only [Left.nonneg_neg_iff]
          rw [mul_nonpos_iff]
          right
          constructor
          · apply Real.log_nonpos (by linarith) (by nlinarith)
          · apply pow_nonneg (by linarith)
        · apply div_nonneg _ (by positivity)
          apply pow_nonneg (by linarith)
      · apply AEMeasurable.ennreal_ofReal
        apply Measurable.aemeasurable
        apply Measurable.neg
        apply Measurable.const_mul
        exact Measurable.pow_const measurable_id _
    _ = ENNReal.ofReal
      (1 / ((k + r + 1) ^ 2 * (k + s + 1)) + 1 / ((k + r + 1) * (k + s + 1) ^ 2)) := by
      have h2 : ∫⁻ (x : ℝ) in Set.Ioo 0 1,
        ENNReal.ofReal
          (- x.log * x ^ (k + r) / (k + s + 1) + x ^ (k + r) / (k + s + 1) ^ 2)
        = ∫⁻ (x : ℝ) in Set.Ioo 0 1,
        ENNReal.ofReal (-x.log * x ^ (k + r) / (k + s + 1)) +
          ENNReal.ofReal (x ^ (k + r) / (k + s + 1) ^ 2) := by
        apply MeasureTheory.setLIntegral_congr_fun (by measurability)
        rintro x ⟨hx1, hx2⟩
        change ENNReal.ofReal
            (-Real.log x * x ^ (k + r) / (↑k + ↑s + 1) + x ^ (k + r) / (↑k + ↑s + 1) ^ 2) =
          ENNReal.ofReal (-Real.log x * x ^ (k + r) / (↑k + ↑s + 1)) +
            ENNReal.ofReal (x ^ (k + r) / (↑k + ↑s + 1) ^ 2)
        rw [ENNReal.ofReal_add]
        · apply div_nonneg _ (by positivity)
          apply mul_nonneg _ (by apply pow_nonneg (by linarith))
          simp only [Left.nonneg_neg_iff]
          apply Real.log_nonpos (by nlinarith) (by nlinarith)
        · apply div_nonneg _ (by positivity)
          apply pow_nonneg (by linarith)
      rw [h2, MeasureTheory.lintegral_add_left']
      · rw [aux_lintegral3 k r s, aux_lintegral4 k r s, ENNReal.ofReal_add]
        · apply div_nonneg (by norm_num) (by positivity)
        · apply div_nonneg (by norm_num) (by positivity)
      · apply AEMeasurable.ennreal_ofReal
        apply Measurable.aemeasurable
        apply Measurable.div_const
        apply Measurable.mul
        · apply Measurable.neg
          apply Measurable.log measurable_id
        · exact Measurable.pow_const measurable_id _
  · rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
    exact AEMeasurable_aux'

lemma J_ENN_rs_eq_tsum (r s : ℕ) : JENN r s = ∑' (k : ℕ), ENNReal.ofReal
    (1 / ((k + r + 1) ^ 2 * (k + s + 1)) + 1 / ((k + r + 1) * (k + s + 1) ^ 2)) := by
  calc
  _ = ∫⁻ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    ∑' (k : ℕ), ENNReal.ofReal (- (x.1 * x.2).log * x.1 ^ (k + r) * x.2 ^ (k + s)) := by
    rw [JENN, ← MeasureTheory.lintegral_indicator (by measurability),
        ← MeasureTheory.lintegral_indicator (by measurability)]
    congr
    ext y
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases h1 : y ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
    · simp only [h1, ↓reduceIte, div_eq_mul_inv]
      simp only [Set.mem_prod, Set.mem_Ioo] at h1
      rw [← tsum_geometric_of_lt_one]
      · rw [← tsum_mul_left, ← tsum_mul_right, ← tsum_mul_right,
          ENNReal.ofReal_tsum_of_nonneg]
        · simp only [neg_mul, pow_add, mul_pow, ← mul_assoc]
          congr
          ext k
          nth_rw 2 [mul_assoc]
          nth_rw 4 [mul_assoc]
          nth_rw 5 [mul_comm]
        · intro n
          rw [mul_pow, ← mul_assoc]
          apply mul_nonneg _ (by apply pow_nonneg (by linarith))
          apply mul_nonneg _ (by apply pow_nonneg (by linarith))
          apply mul_nonneg _ (by apply pow_nonneg (by linarith))
          apply mul_nonneg _ (by apply pow_nonneg (by linarith))
          simp only [Left.nonneg_neg_iff]
          apply Real.log_nonpos (by nlinarith) (by nlinarith)
        · simp_rw [← smul_eq_mul]
          apply Summable.smul_const (a := y.2 ^ s)
          apply Summable.smul_const (a := y.1 ^ r)
          apply Summable.const_smul (b := -(y.1 • y.2).log)
          apply summable_geometric_of_lt_one <;> rw [smul_eq_mul] <;> nlinarith
      · nlinarith
      · nlinarith
    · simp only [h1, ↓reduceIte]
  _ = ∑' (k : ℕ), ∫⁻ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    ENNReal.ofReal (- (x.1 * x.2).log * x.1 ^ (k + r) * x.2 ^ (k + s)) := by
    rw [MeasureTheory.lintegral_tsum]
    intro n
    exact AEMeasurable_aux'
  _ = ∑' (k : ℕ), ENNReal.ofReal
    (1 / ((k + r + 1) ^ 2 * (k + s + 1)) + 1 / ((k + r + 1) * (k + s + 1) ^ 2)) := by
    simp_rw [J_ENN_rs_eq_tsum_aux_intergal r s]

lemma J_ENN_rr (r : ℕ) : JENN r r = ENNReal.ofReal
    (2 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 -
      2 * ∑ m ∈ Finset.Icc 1 r, 1 / (m : ℝ) ^ 3) := by
  have h : JENN r r = ∑' (k : ℕ), ENNReal.ofReal (2 / ((k + r + 1) ^ 3)) := by
    rw [J_ENN_rs_eq_tsum r r]
    congr
    ext k
    rw [← pow_one (a := (k : ℝ) + r + 1), ← pow_mul, ← pow_add, ← pow_add, one_mul]
    simp only [Nat.reduceAdd, pow_one, ← two_mul, mul_one_div]
  rw [h]
  have h1 : ∑' (k : ℕ), 2 / (((k : ℝ) + r + 1) ^ 3) =
      2 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 -
        2 * ∑ m ∈ Finset.Icc 1 r, 1 / (m : ℝ) ^ 3 := by
    symm
    apply sub_eq_of_eq_add
    have hsum_inv_cube : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 3) := by
      simpa [Nat.cast_add, Nat.cast_one, add_comm] using
        ((summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 3) 1).2
          ((Real.summable_one_div_nat_pow (p := 3)).2 (by norm_num)))
    rw [← hsum_inv_cube.sum_add_tsum_nat_add r, mul_add, add_comm, ← tsum_mul_left]
    · simp only [mul_one_div]
      congr 1
      · norm_cast
      · congr 1
        have h1 := Finset.sum_Ico_eq_sum_range (m := 1) (n := r + 1)
          (f := fun k => 1 / (k : ℝ) ^ 3)
        simpa [Nat_Ico_succ_right, Nat.cast_add, Nat.cast_one, add_comm] using h1.symm
  rw [← h1, ENNReal.ofReal_tsum_of_nonneg]
  · intro n
    positivity
  · norm_cast
    simp only [add_assoc, Nat.cast_pow]
    rw [summable_nat_add_iff (k := r + 1) (f := fun k => 2 / (k ^ 3 : ℝ))]
    have h2 := Real.summable_one_div_nat_pow (p := 3)
    simp only [Nat.one_lt_ofNat] at h2
    apply Iff.symm at h2
    rw [true_iff, ← summable_mul_left_iff (a := 2) (by norm_num)] at h2
    simp only [mul_one_div] at h2
    exact h2

lemma fun_of_J_nonneg (r s : ℕ) (x : ℝ × ℝ) (hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) :
    0 ≤ -Real.log (x.1 * x.2) / (1 - x.1 * x.2) * x.1 ^ r * x.2 ^ s := by
  simp only [Set.mem_prod, Set.mem_Ioo] at hx
  have hxy : x.1 * x.2 ≤ 1 :=
    (mul_le_mul_of_nonneg_right hx.1.2.le hx.2.1.le).trans
      (by simpa only [one_mul] using hx.2.2.le)
  apply mul_nonneg
  · apply mul_nonneg
    · rw [div_nonneg_iff]
      left
      constructor
      · simp only [Left.nonneg_neg_iff]
        exact Real.log_nonpos (mul_nonneg hx.1.1.le hx.2.1.le) hxy
      · exact sub_nonneg.mpr hxy
    · exact pow_nonneg hx.1.1.le r
  · exact pow_nonneg hx.2.1.le s

lemma integrableOn_J_rr (r : ℕ) : MeasureTheory.IntegrableOn
    (fun x ↦ -Real.log (x.1 * x.2) / (1 - x.1 * x.2) * x.1 ^ r * x.2 ^ r)
    (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) MeasureTheory.volume := by
  have h := J_ENN_rr r
  simp only [JENN] at h
  rw [MeasureTheory.IntegrableOn, MeasureTheory.Integrable]
  constructor
  · apply AEMeasurable.aestronglyMeasurable
    apply Measurable.aemeasurable
    · apply Measurable.mul
      · apply Measurable.mul
        · apply Measurable.div
          · apply Measurable.neg (Measurable.log (Measurable.mul measurable_fst measurable_snd))
          · apply Measurable.const_sub (Measurable.mul measurable_fst measurable_snd)
        · apply Measurable.pow measurable_fst measurable_const
      · apply Measurable.pow measurable_snd measurable_const
  · rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    have h1 : ∫⁻ (a : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      ENNReal.ofReal ‖-Real.log (a.1 * a.2) / (1 - a.1 * a.2) * a.1 ^ r * a.2 ^ r‖ =
      ∫⁻ (a : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      ENNReal.ofReal (-Real.log (a.1 * a.2) / (1 - a.1 * a.2) * a.1 ^ r * a.2 ^ r) := by
      rw [← MeasureTheory.lintegral_indicator (by measurability),
        ← MeasureTheory.lintegral_indicator (by measurability)]
      congr
      ext x
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · simp only [hx, ↓reduceIte, norm_mul, norm_div, norm_neg, Real.norm_eq_abs, norm_pow]
        simp only [Set.mem_prod, Set.mem_Ioo] at hx
        rw [ENNReal.ofReal_eq_ofReal_iff]
        · congr 3
          · simp only [abs_eq_neg_self]
            exact Real.log_nonpos (mul_nonneg hx.1.1.le hx.2.1.le)
              ((mul_le_mul_of_nonneg_right hx.1.2.le hx.2.1.le).trans
                (by simpa only [one_mul] using hx.2.2.le))
          · simp only [abs_eq_self, sub_nonneg]
            exact (mul_le_mul_of_nonneg_right hx.1.2.le hx.2.1.le).trans
              (by simpa only [one_mul] using hx.2.2.le)
          · simp only [abs_eq_self]; exact hx.1.1.le
          · simp only [abs_eq_self]; exact hx.2.1.le
        · positivity
        · exact fun_of_J_nonneg r r x hx
      · simp only [hx, ↓reduceIte]
    rw [h1, h]
    exact ENNReal.ofReal_lt_top

theorem J_rr (r : ℕ) :
    J r r =
      2 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 -
        2 * ∑ m ∈ Finset.Icc 1 r, 1 / (m : ℝ) ^ 3 := by
  have h := J_ENN_rr r
  simp only [JENN] at h
  rw [J, MeasureTheory.integral_eq_lintegral_of_nonneg_ae, h, ENNReal.toReal_ofReal_eq_iff]
  · simp only [sub_nonneg]
    have hsum_eq : (∑ m ∈ Finset.Icc 1 r, 1 / (m : ℝ) ^ 3) =
        ∑ i ∈ Finset.range r, 1 / ((i : ℝ) + 1) ^ 3 := by
      have h := Finset.sum_Ico_eq_sum_range (m := 1) (n := r + 1)
        (f := fun k => 1 / (k : ℝ) ^ 3)
      simpa [Nat_Ico_succ_right, Nat.cast_add, Nat.cast_one, add_comm] using h
    rw [hsum_eq]
    apply mul_le_mul_of_nonneg_left
    · apply Summable.sum_le_tsum
      · intro i _
        positivity
      · norm_cast
        simp only [Nat.cast_pow]
        rw [summable_nat_add_iff (k := 1) (f := fun k => 1 / (k ^ 3 : ℝ)),
          Real.summable_one_div_nat_pow (p := 3)]
        norm_num
    · norm_num
  · apply MeasureTheory.ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter
    · exact integrableOn_J_rr r
    · rintro x hx -
      apply MeasureTheory.setIntegral_nonneg (by measurability)
      intro y hy
      by_cases h : y ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · exact fun_of_J_nonneg r r y h
      · simp_all
  · apply AEMeasurable.aestronglyMeasurable
    apply Measurable.aemeasurable
    · apply Measurable.mul
      · apply Measurable.mul
        · apply Measurable.div
          · apply Measurable.neg (Measurable.log (Measurable.mul measurable_fst measurable_snd))
          · apply Measurable.const_sub (Measurable.mul measurable_fst measurable_snd)
        · apply Measurable.pow measurable_fst measurable_const
      · apply Measurable.pow measurable_snd measurable_const

theorem zeta3 : J 0 0 = 2 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 := by
  simp only [J_rr, one_div, zero_lt_one, Finset.Icc_eq_empty_of_lt, Finset.sum_empty, mul_zero,
    sub_zero]

lemma positivity_aux (r s : ℕ) (h : r > s) :
    ∀ (i : ℕ), 0 ≤ 1 / ((r : ℝ) - s) * (1 / (i + s + 1) ^ 2 - 1 / (i + r + 1) ^ 2) := by
  intro n
  apply mul_nonneg
  · simp only [one_div, inv_nonneg, sub_nonneg, Nat.cast_le]; linarith
  · simp only [sub_nonneg]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    simp only [one_mul]
    apply pow_le_pow_left₀ (by linarith)
    simp only [add_le_add_iff_right, add_le_add_iff_left, Nat.cast_le]
    linarith

lemma summable_aux (r : ℕ) : Summable fun (b : ℕ) ↦ 1 / ((b : ℝ) + r + 1) ^ 2 := by
  norm_cast
  simp only [add_assoc, Nat.cast_pow]
  rw [summable_nat_add_iff (k := r + 1) (f := fun k => 1 / (k ^ 2 : ℝ)),
    Real.summable_one_div_nat_pow (p := 2)]
  norm_num

lemma J_ENN_rs (r s : ℕ) (h : r > s) :
    JENN r s = ENNReal.ofReal ((∑ k ∈ Finset.Ioc s r, 1 / (k : ℝ) ^ 2) / (r - s)) := by
  calc
  _ = ∑' (k : ℕ),
      ENNReal.ofReal
        (1 / (r - s) * (1 / (k + s + 1) ^ 2 - 1 / (k + r + 1) ^ 2)) := by
    rw [J_ENN_rs_eq_tsum]
    congr
    ext k
    set x := (k : ℝ) + r + 1
    set y := (k : ℝ) + s + 1
    have hy : y > 0 := by positivity
    have hxy : x - y > 0 := by
      rw [show (x : ℝ) - y = r - s by ring]
      simp_all
    rw [show r - s = (x : ℝ) - y by ring, ENNReal.ofReal_eq_ofReal_iff]
    · rw [div_add_div]
      · rw [div_sub_div]
        · rw [div_mul_div_comm, div_eq_div_iff]
          · ring
          · suffices 0 < x ^ 2 * y * (x * y ^ 2) by linarith
            positivity
          · suffices (x - y) * (y ^ 2 * x ^ 2) > 0 by linarith
            positivity
        · positivity
        · positivity
      · suffices x ^ 2 * y > 0 by linarith
        positivity
      · suffices x * y ^ 2 > 0 by linarith
        positivity
    · positivity
    · apply mul_nonneg (by positivity)
      simp only [sub_nonneg]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      simp only [one_mul]
      apply pow_le_pow_left₀ (by linarith) (by linarith)
  _ = ENNReal.ofReal ((∑ k ∈ Finset.Ioc s r, 1 / (k : ℝ) ^ 2) / (r - s)) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg]
    · rw [ENNReal.ofReal_eq_ofReal_iff]
      · simp only [mul_sub]
        · have hsumm_s : Summable
              (fun n : ℕ => 1 / (r - s) * (1 / (n + (s : ℝ) + 1) ^ 2)) := by
            simp_rw [← smul_eq_mul]
            apply Summable.const_smul
            exact summable_aux s
          have hsumm_r : Summable
              (fun n : ℕ => 1 / (r - s) * (1 / (n + (r : ℝ) + 1) ^ 2)) := by
            simp_rw [← smul_eq_mul]
            apply Summable.const_smul
            exact summable_aux r
          rw [hsumm_s.tsum_sub hsumm_r]
          simp only [sum_div, div_div, ← one_div_mul_one_div_rev]
          apply sub_eq_of_eq_add
          rw [← hsumm_s.sum_add_tsum_nat_add (r - s)]
          congr 1
          · simp only [← Nat.cast_add, add_comm]
            rw [← Finset.sum_Ico_eq_sum_range (n := r) (m := s)
              (f := fun k => 1 / (r - s) * (1 / ((k : ℝ) + 1) ^ 2)),
              ← Nat_Ico_succ_succ s r, ← Finset.sum_Ico_add' (c := 1) (b := r) (a := s)]
            norm_cast
          · congr
            ext n
            congr 1
            norm_cast
            rw [show n + (r - s) + s + 1 = n + r + 1 by omega]
      · apply tsum_nonneg
        exact positivity_aux r s h
      · rw [sum_div]
        apply sum_nonneg
        intro i _
        rw [div_nonneg_iff]
        left
        simp only [one_div, inv_nonneg, Nat.cast_nonneg, pow_nonneg, sub_nonneg, Nat.cast_le,
          true_and]
        linarith
    · exact positivity_aux r s h
    · simp_rw [← smul_eq_mul]
      apply Summable.const_smul
      apply Summable.sub
      · exact summable_aux s
      · exact summable_aux r

lemma integrableOn_J_rs' (r s : ℕ) (h : r > s) : MeasureTheory.IntegrableOn
    (fun x ↦ -Real.log (x.1 * x.2) / (1 - x.1 * x.2) * x.1 ^ r * x.2 ^ s)
    (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) MeasureTheory.volume := by
  have h₀ := J_ENN_rs r s h
  simp only [JENN] at h₀
  rw [MeasureTheory.IntegrableOn, MeasureTheory.Integrable]
  constructor
  · apply AEMeasurable.aestronglyMeasurable
    apply Measurable.aemeasurable
    · apply Measurable.mul
      · apply Measurable.mul
        · apply Measurable.div
          · apply Measurable.neg (Measurable.log (Measurable.mul measurable_fst measurable_snd))
          · apply Measurable.const_sub (Measurable.mul measurable_fst measurable_snd)
        · apply Measurable.pow measurable_fst measurable_const
      · apply Measurable.pow measurable_snd measurable_const
  · rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    have h1 : ∫⁻ (a : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      ENNReal.ofReal ‖-Real.log (a.1 * a.2) / (1 - a.1 * a.2) * a.1 ^ r * a.2 ^ s‖ =
      ∫⁻ (a : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      ENNReal.ofReal (-Real.log (a.1 * a.2) / (1 - a.1 * a.2) * a.1 ^ r * a.2 ^ s) := by
      rw [← MeasureTheory.lintegral_indicator (by measurability),
        ← MeasureTheory.lintegral_indicator (by measurability)]
      congr
      ext x
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · simp only [hx, ↓reduceIte, norm_mul, norm_div, norm_neg, Real.norm_eq_abs, norm_pow]
        simp only [Set.mem_prod, Set.mem_Ioo] at hx
        rw [ENNReal.ofReal_eq_ofReal_iff]
        · congr 3
          · simp only [abs_eq_neg_self]
            exact Real.log_nonpos (mul_nonneg hx.1.1.le hx.2.1.le)
              ((mul_le_mul_of_nonneg_right hx.1.2.le hx.2.1.le).trans
                (by simpa only [one_mul] using hx.2.2.le))
          · simp only [abs_eq_self, sub_nonneg]
            exact (mul_le_mul_of_nonneg_right hx.1.2.le hx.2.1.le).trans
              (by simpa only [one_mul] using hx.2.2.le)
          · simp only [abs_eq_self]; exact hx.1.1.le
          · simp only [abs_eq_self]; exact hx.2.1.le
        · positivity
        · exact fun_of_J_nonneg r s x hx
      · simp only [hx, ↓reduceIte]
    rw [h1, h₀]
    exact ENNReal.ofReal_lt_top

lemma J_rs' (r s : ℕ) (h : r > s) :
    J r s = (∑ k ∈ Finset.Ioc s r, 1 / (k : ℝ) ^ 2) / (r - s) := by
  have h₀ := J_ENN_rs r s h
  simp only [JENN] at h₀
  rw [J, MeasureTheory.integral_eq_lintegral_of_nonneg_ae, h₀, ENNReal.toReal_ofReal_eq_iff]
  · rw [sum_div]
    apply sum_nonneg
    intro i _
    rw [div_nonneg_iff]
    left
    simp only [one_div, inv_nonneg, Nat.cast_nonneg, pow_nonneg, sub_nonneg, Nat.cast_le,
      true_and]
    linarith
  · apply MeasureTheory.ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter
    · exact integrableOn_J_rs' r s h
    · rintro x hx -
      apply MeasureTheory.setIntegral_nonneg (by measurability)
      intro y hy
      by_cases h : y ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · exact fun_of_J_nonneg r s y h
      · simp_all
  · apply AEMeasurable.aestronglyMeasurable
    apply Measurable.aemeasurable
    · apply Measurable.mul
      · apply Measurable.mul
        · apply Measurable.div
          · apply Measurable.neg (Measurable.log (Measurable.mul measurable_fst measurable_snd))
          · apply Measurable.const_sub (Measurable.mul measurable_fst measurable_snd)
        · apply Measurable.pow measurable_fst measurable_const
      · apply Measurable.pow measurable_snd measurable_const

lemma J_ENN_rs_symm (r s : ℕ) : JENN r s = JENN s r := by
  simp only [J_ENN_rs_eq_tsum, add_comm, mul_comm]

lemma integrableOn_J_rs (r s : ℕ) : MeasureTheory.IntegrableOn
    (fun x ↦ -Real.log (x.1 * x.2) / (1 - x.1 * x.2) * x.1 ^ r * x.2 ^ s)
    (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) MeasureTheory.volume := by
  by_cases h : r > s
  · exact integrableOn_J_rs' r s h
  · by_cases h1 : s = r
    · rw [h1]
      exact integrableOn_J_rr r
    · have h2 : s > r := by
        by_contra!; apply h1; linarith
      rw [MeasureTheory.IntegrableOn, MeasureTheory.Integrable]
      constructor
      · apply AEMeasurable.aestronglyMeasurable
        apply Measurable.aemeasurable
        · apply Measurable.mul
          · apply Measurable.mul
            · apply Measurable.div
              · apply Measurable.neg
                apply Measurable.log
                apply Measurable.mul measurable_fst measurable_snd
              · apply Measurable.const_sub (Measurable.mul measurable_fst measurable_snd)
            · apply Measurable.pow measurable_fst measurable_const
          · apply Measurable.pow measurable_snd measurable_const
      · rw [MeasureTheory.hasFiniteIntegral_iff_norm]
        have h1 : ∫⁻ (a : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
          ENNReal.ofReal ‖-Real.log (a.1 * a.2) / (1 - a.1 * a.2) * a.1 ^ r * a.2 ^ s‖ =
          ∫⁻ (a : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
          ENNReal.ofReal (-Real.log (a.1 * a.2) / (1 - a.1 * a.2) * a.1 ^ r * a.2 ^ s) := by
          rw [← MeasureTheory.lintegral_indicator (by measurability),
            ← MeasureTheory.lintegral_indicator (by measurability)]
          congr
          ext x
          rw [Set.indicator_apply, Set.indicator_apply]
          by_cases hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
          · simp only [hx, ↓reduceIte, norm_mul, norm_div, norm_neg, Real.norm_eq_abs, norm_pow]
            simp only [Set.mem_prod, Set.mem_Ioo] at hx
            rw [ENNReal.ofReal_eq_ofReal_iff]
            · congr 3
              · simp only [abs_eq_neg_self]
                apply Real.log_nonpos <;> nlinarith
              · simp only [abs_eq_self, sub_nonneg]; nlinarith
              · simp only [abs_eq_self]; nlinarith
              · simp only [abs_eq_self]; nlinarith
            · positivity
            · exact fun_of_J_nonneg r s x hx
          · simp only [hx, ↓reduceIte]
        have h₀ := J_ENN_rs s r h2
        rw [J_ENN_rs_symm s r] at h₀
        simp only [JENN] at h₀
        rw [h1, h₀]
        exact ENNReal.ofReal_lt_top

lemma J_eq_toReal_J_ENN (r s : ℕ) : J r s = (JENN r s).toReal := by
  rw [J, JENN, MeasureTheory.integral_eq_lintegral_of_nonneg_ae]
  · apply MeasureTheory.ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter
    · exact integrableOn_J_rs r s
    · rintro x hx -
      apply MeasureTheory.setIntegral_nonneg (by measurability)
      intro y hy
      by_cases h : y ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · exact fun_of_J_nonneg r s y h
      · simp_all
  · apply AEMeasurable.aestronglyMeasurable
    apply Measurable.aemeasurable
    · apply Measurable.mul
      · apply Measurable.mul
        · apply Measurable.div
          · apply Measurable.neg (Measurable.log (Measurable.mul measurable_fst measurable_snd))
          · apply Measurable.const_sub (Measurable.mul measurable_fst measurable_snd)
        · apply Measurable.pow measurable_fst measurable_const
      · apply Measurable.pow measurable_snd measurable_const

lemma J_rs_symm (r s : ℕ) : J r s = J s r := by
  rw [J_eq_toReal_J_ENN, J_eq_toReal_J_ENN, J_ENN_rs_symm]

theorem J_rs {r s : ℕ} (h : r ≠ s) : J r s =
    (∑ m ∈ Icc 1 r, 1 / (m : ℝ) ^ 2 - ∑ m ∈ Icc 1 s, 1 / (m : ℝ) ^ 2) / (r - s) := by
  by_cases h1 : r > s
  · simp only [J_rs' r s h1, sub_div, sum_div]
    rw [← Nat_Ico_succ_succ, Finset.sum_Ico_eq_sub]
    · congr 1
      · rw [← Finset.sum_range_add_sum_Ico (n := r + 1) (m := 1) _ (by omega)]
        simp only [range_one, one_div, sum_singleton, CharP.cast_eq_zero, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, inv_zero, zero_div, zero_add]
        rw [Nat_Ico_succ_right]
      · rw [← Finset.sum_range_add_sum_Ico (n := s + 1) (m := 1) _ (by omega)]
        simp only [range_one, one_div, sum_singleton, CharP.cast_eq_zero, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, inv_zero, zero_div, zero_add]
        rw [Nat_Ico_succ_right]
    · linarith
  · simp only [gt_iff_lt, not_lt] at h1
    have h2 : s > r := by
      by_contra!; apply h; linarith
    rw [J_rs_symm, J_rs' s r h2]
    nth_rw 2 [← neg_div_neg_eq]
    simp only [neg_sub]
    congr 1
    rw [← Nat_Ico_succ_succ, Finset.sum_Ico_eq_sub]
    · congr 1
      · rw [← Finset.sum_range_add_sum_Ico (n := s + 1) (m := 1) _ (by omega)]
        simp only [range_one, one_div, sum_singleton, CharP.cast_eq_zero, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, inv_zero, zero_add]
        rw [Nat_Ico_succ_right]
      · rw [← Finset.sum_range_add_sum_Ico (n := r + 1) (m := 1) _ (by omega)]
        simp only [range_one, one_div, sum_singleton, CharP.cast_eq_zero, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, inv_zero, zero_add]
        rw [Nat_Ico_succ_right]
    · linarith

end LeanPool.Zeta3Irrational
-- ===== from LeanPool/Zeta3Irrational/LinearForm.lean =====
/-
Copyright (c) 2026 Junqi Liu, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junqi Liu, Jujian Zhang
-/


/-!
# LeanPool.Zeta3Irrational.LinearForm
-/


namespace LeanPool.Zeta3Irrational

open scoped Nat
open BigOperators

lemma d_cube_ne_zero {r : ℕ} : ((d (Finset.Icc 1 r) ^ 3) : ℝ) ≠ (0 : ℝ) := by
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, Nat.cast_eq_zero]
  apply d_ne_zero; simp

lemma J_rr_linear (r : ℕ) :
    ∃ a : ℤ,
      J r r = 2 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 -
        a / (d (Finset.Icc 1 r)) ^ 3 := by
  if h : r = 0 then
    rw [h, zeta3]; use 0; simp
  else
    rw [J_rr]
    simp only [sub_right_inj]
    simp_rw [eq_div_iff d_cube_ne_zero, Finset.mul_sum, Finset.sum_mul]
    use ∑ i ∈ Finset.Icc 1 r, 2 * ↑(d (Finset.Icc 1 r)) ^ 3 / ↑i ^ 3
    simp only [Int.cast_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [mul_assoc]
    nth_rewrite 2 [mul_comm]
    rw [mul_one_div, Int.cast_div]
    · simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_pow, Int.cast_natCast, mul_div_assoc']
    · rw [← Nat.cast_pow, ← Nat.cast_pow, d_cube', Nat.cast_pow]
      apply Dvd.dvd.mul_left
      norm_cast
      apply dvd_d_of_mem
      simp_all
    · simp_all only [Finset.mem_Icc, Int.cast_pow, Int.cast_natCast, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, pow_eq_zero_iff, Nat.cast_eq_zero]
      linarith

lemma Icc_diff_Icc {r s : ℕ} (_ : r > s) (_ : ¬s = 0) :
    Finset.Icc 1 r \ Finset.Icc 1 s = Finset.Icc (s + 1) r := by
  ext x
  constructor
  · simp_all
  · intro hx
    simp_all only [gt_iff_lt, Finset.mem_Icc, Finset.mem_sdiff, and_true, not_and, not_le]
    constructor
    · linarith
    · simp_all

lemma one_div_sum_eq {r s : ℕ} (h : r > s) :
    ∑ m ∈ Finset.Icc 1 r, (1 / m ^ 2 : ℝ) - ∑ m ∈ Finset.Icc 1 s, (1 / m ^ 2 : ℝ) =
    ∑ m ∈ Finset.Icc 1 (r - s), (1 / (s + m) ^ 2 : ℝ) := by
  rw [← Finset.sum_sdiff_eq_sub]
  · if h1 : s = 0 then
      simp_all
    else
      simp_rw [← Nat.cast_add]
      rw [Icc_diff_Icc h h1, ← Nat_Ico_succ_right, ← Nat_Ico_succ_right,
        Finset.sum_Ico_add (f := fun (x : ℕ) => 1 / ((x ^ 2) : ℝ)) (c := s),
        show s + 1 = 1 + s by omega, show r - s + 1 + s = r + 1 by omega]
  · exact Finset.Icc_subset_Icc_right (LT.lt.le (gt_iff_lt.1 h))

lemma J_rs_linear {r s : ℕ} (h : r > s) : ∃ a : ℤ, J r s = a / (d (Finset.Icc 1 r)) ^ 3 := by
  rw [J_rs (by linarith)]
  simp_rw [eq_div_iff d_cube_ne_zero, one_div_sum_eq h]
  use (∑ m ∈ Finset.Icc 1 (r - s), (d (Finset.Icc 1 r)) ^ 2 / (s + m) ^ 2 *
    (d (Finset.Icc 1 r)) / (r - s))
  rw [Finset.sum_div, Finset.sum_mul, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show 3 = 1 + 2 by omega, pow_add, pow_one, mul_comm, mul_assoc, mul_div_assoc', mul_one_div,
    mul_div_assoc', mul_comm, ← mul_div_assoc', Int.cast_div]
  · rw [Int.cast_mul, Int.cast_div]
    · simp_all only [gt_iff_lt, Finset.mem_Icc, Int.cast_pow, Int.cast_natCast, Int.cast_add,
      Int.cast_sub]
      rw [mul_div_assoc']
    · norm_cast
      rw [d_sq']
      apply dvd_d_of_mem
      simp_all only [gt_iff_lt, Finset.mem_Icc, Finset.mem_image, zero_le, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, pow_left_inj₀, exists_eq_right]
      omega
    · simp_all only [gt_iff_lt, Finset.mem_Icc, Int.cast_pow, Int.cast_add, Int.cast_natCast,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]
      rw [← Nat.cast_add]
      norm_cast; omega
  · apply Dvd.dvd.mul_left
    rw [← Nat.cast_sub (by linarith)]
    norm_cast
    apply dvd_d_of_mem
    simp_all only [gt_iff_lt, Finset.mem_Icc, tsub_le_iff_right, le_add_iff_nonneg_right, zero_le,
      and_true]
    linarith
  · simp_all only [gt_iff_lt, Finset.mem_Icc, Int.cast_sub, Int.cast_natCast]
    rw [← Nat.cast_sub (by linarith)]
    norm_cast; linarith

/-- Constant monomial weights preserve integrability of the Apéry integrand. -/
lemma integrableOn_weighted_J (r s : ℕ) (p q : ℝ) :
    MeasureTheory.IntegrableOn
      (fun (x : ℝ × ℝ) ↦ -Real.log (x.1 * x.2) / (1 - x.1 * x.2) *
        p * x.1 ^ r * q * x.2 ^ s)
      (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) := by
  unfold MeasureTheory.IntegrableOn
  convert (integrableOn_J_rs r s).mul_const (p * q) using 1
  funext x
  ring

lemma multi_integral_sum_comm (c : ℕ → ℤ) :
    ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    ∑ x_1 ∈ Finset.range (n + 1), ∑ x_2 ∈ Finset.range (n + 1),
    -(x.1 * x.2).log / (1 - x.1 * x.2) * ↑(c x_1) * x.1 ^ x_1 *
      ↑(c x_2) * x.2 ^ x_2
    = ∑ x_1 ∈ Finset.range (n + 1), ∑ x_2 ∈ Finset.range (n + 1),
      ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      -(x.1 * x.2).log / (1 - x.1 * x.2) * ↑(c x_1) * x.1 ^ x_1 *
        ↑(c x_2) * x.2 ^ x_2 := by
    symm
    calc
    _ = ∑ x_1 ∈ Finset.range (n + 1),
      ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      ∑ x_2 ∈ Finset.range (n + 1),
      -(x.1 * x.2).log / (1 - x.1 * x.2) * ↑(c x_1) * x.1 ^ x_1 *
        ↑(c x_2) * x.2 ^ x_2 := by
      congr! 1 with a _
      rw [← MeasureTheory.integral_finsetSum]
      intro i _
      exact integrableOn_weighted_J a i (c a) (c i)
    _ = ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      ∑ x_1 ∈ Finset.range (n + 1), ∑ x_2 ∈ Finset.range (n + 1),
      -(x.1 * x.2).log / (1 - x.1 * x.2) * ↑(c x_1) * x.1 ^ x_1 *
        ↑(c x_2) * x.2 ^ x_2 := by
      rw [← MeasureTheory.integral_finsetSum]
      intro i _
      apply MeasureTheory.integrable_finsetSum
      intro j _
      exact integrableOn_weighted_J i j (c i) (c j)

lemma multi_integral_mul_const (c d : ℕ) (p q : ℝ) :
    ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      -(x.1 * x.2).log / (1 - x.1 * x.2) * p * x.1 ^ c * q * x.2 ^ d =
    p * q * J c d := by
  simp only [J]
  symm
  rw [mul_comm, ← smul_eq_mul, ← integral_smul_const]
  apply MeasureTheory.setIntegral_congr_fun (by measurability)
  intro x _
  simp only [smul_eq_mul]
  ring

/-- The integer coefficient of the rational part of `J r s`. -/
noncomputable def p (r s : ℕ) : ℤ :=
  if h : r > s then (J_rs_linear h).choose
  else if h : r < s then (J_rs_linear h).choose
  else -(J_rr_linear r).choose

/-- The integer coefficient of the zeta part of `J r s`. -/
noncomputable def q (r s : ℕ) : ℤ :=
  if r > s then 0
  else if r < s then 0
  else 2

lemma J_symm (r s : ℕ) : J r s = J s r := by
  if h : r = s then rw [h]
  else
    rw [J_rs (by tauto), J_rs (by tauto), ← neg_div_neg_eq]; ring

lemma linear_int_aux : ∃ a b : ℕ → ℕ → ℤ, ∀ r s : ℕ, J r s =
    b r s * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 +
      a r s / (d (Finset.Icc 1 (Nat.max r s))) ^ 3 := by
  use p
  use q
  intro x y
  if h : x > y then
    rcases J_rs_linear h with ⟨a, ha⟩
    simp only [p, q]
    simp_all only [gt_iff_lt, one_div, ite_true, Int.cast_zero, zero_mul, dite_true,
      zero_add]
    rw [(J_rs_linear h).choose_spec] at ha
    rw [show x.max y = x by exact max_eq_left_iff.2 (LT.lt.le h)]
    simp_all
  else if h1 : x < y then
    rcases J_rs_linear h1 with ⟨a, ha⟩
    simp only [p, q]
    obtain h2 := J_symm x y
    simp_all only [gt_iff_lt, one_div, ite_true, ite_self, Int.cast_zero, zero_mul, dite_true,
      zero_add, dite_false]
    rw [(J_rs_linear h1).choose_spec] at ha
    simp_all
  else
    have h : x = y := by linarith
    rcases J_rr_linear y with ⟨a, ha⟩
    simp only [p, q]
    simp_all only [gt_iff_lt, lt_self_iff_false, not_false_eq_true, ite_false,
      Int.cast_ofNat, not_isEmpty_of_nonempty, tsum_empty, mul_zero, zero_sub, sub_right_inj,
      dite_false, Int.cast_neg, max_self]
    rw [(J_rr_linear y).choose_spec, ← Mathlib.Tactic.RingNF.add_neg, ← neg_div] at ha
    simp_all

end LeanPool.Zeta3Irrational
-- ===== from LeanPool/Zeta3Irrational/Equality.lean =====
/-
Copyright (c) 2026 Junqi Liu, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junqi Liu, Jujian Zhang
-/


/-!
# LeanPool.Zeta3Irrational.Equality
-/


namespace LeanPool.Zeta3Irrational

open scoped Nat
open BigOperators Polynomial

end LeanPool.Zeta3Irrational
-- ===== from LeanPool/Zeta3Irrational/Basic.lean =====
/-
Copyright (c) 2026 Junqi Liu, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junqi Liu, Jujian Zhang
-/


/-!
# LeanPool.Zeta3Irrational.Basic
-/


namespace LeanPool.Zeta3Irrational

open scoped Nat
open BigOperators Polynomial

/-- The Apéry integral after inserting two shifted Legendre polynomials. -/
noncomputable abbrev JJ (n : ℕ) : ℝ :=
    ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    (-(x.1 * x.2).log / (1 - x.1 * x.2) *
      (bkShiftedLegendre n).eval x.1 * (bkShiftedLegendre n).eval x.2)

/-- The transformed three-variable form of the Apéry integral. -/
noncomputable abbrev JJ' (n : ℕ) : ℝ :=
    ∫ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    (x.2.1 * (1 - x.2.1) * x.2.2 * (1 - x.2.2) * x.1 * (1 - x.1) /
    (1 - (1 - x.2.1 * x.2.2) * x.1)) ^ n / (1 - (1 - x.2.1 * x.2.2) * x.1)

/-- The extended nonnegative integral associated to `JJ'`. -/
noncomputable abbrev JJENN (n : ℕ) : ENNReal :=
    ∫⁻ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1, ENNReal.ofReal
    ((x.2.1 * (1 - x.2.1) * x.2.2 * (1 - x.2.2) * x.1 * (1 - x.1) /
    (1 - (1 - x.2.1 * x.2.2) * x.1)) ^ n / (1 - (1 - x.2.1 * x.2.2) * x.1))

/-- The denominator-cleared Apéry linear form. -/
noncomputable abbrev fun1 (n : ℕ) : ℝ := (d (Finset.Icc 1 n)) ^ 3 * JJ n

theorem linear_int (n : ℕ) : ∃ a b : ℕ → ℤ,
    fun1 n =
      a n + b n * (d (Finset.Icc 1 n) : ℤ) ^ 3 *
        ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 := by
  delta fun1 JJ
  obtain ⟨c, hc⟩ := bkShiftedLegendre_eq_int_poly n
  simp_rw [hc, Polynomial.eval_finsetSum, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  simp only [eval_mul, eval_intCast, eval_pow, eval_X]
  simp_rw [← mul_assoc, multi_integral_sum_comm, multi_integral_mul_const]
  simp only [Finset.mul_sum]
  obtain ⟨qq', ⟨pp', hqq'⟩⟩ := linear_int_aux
  use fun n => ∑ x ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n + 1),
    d (Finset.Icc 1 n) ^ 3 * c x * c i * qq' x i / d (Finset.Icc 1 (Nat.max x i)) ^ 3
  use fun n => ∑ x ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n + 1), c x * c i * pp' x i
  rw [← Nat.cast_pow, ← Int.cast_pow , ← Int.cast_mul, Finset.sum_mul]
  simp only [Nat.cast_pow, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  specialize hqq' x y
  rw [hqq', mul_add, mul_add, add_comm]
  congr 1
  · rw [Int.cast_div]
    · rw [mul_div_assoc', ← mul_div_assoc, div_eq_div_iff]
      · norm_cast
        rw [← mul_assoc, ← mul_assoc]
      · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
        Nat.cast_eq_zero]
        apply d_ne_zero
        simp
      · simp only [Int.cast_pow, Int.cast_natCast, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        pow_eq_zero_iff, Nat.cast_eq_zero]
        apply d_ne_zero
        simp
    · rw [mul_assoc, mul_assoc]
      apply Dvd.dvd.mul_right
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, IsIntegrallyClosed.pow_dvd_pow_iff]
      norm_cast
      apply d_dvd_d_of_le
      simp_all only [Finset.mem_range]
      intro a b
      simp_all only [Finset.mem_Icc, true_and]
      simp only [le_max_iff] at b
      rcases b with ⟨_ ,(c | c)⟩
      <;>
      linarith
    · simp only [Int.cast_pow, Int.cast_natCast, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      pow_eq_zero_iff, Nat.cast_eq_zero]
      apply d_ne_zero
      simp
  · ring

lemma pos_aux (x : ℝ × ℝ × ℝ)
    (hx : (0 < x.1 ∧ x.1 < 1) ∧ (0 < x.2.1 ∧ x.2.1 < 1) ∧
      0 < x.2.2 ∧ x.2.2 < 1) :
    0 < (1 - (1 - x.2.1 * x.2.2) * x.1) := by
  simp only [sub_pos]
  exact (mul_lt_mul_of_pos_right
    (sub_lt_self 1 (mul_pos hx.2.1.1 hx.2.2.1)) hx.1.1).trans_le
      (by simpa only [one_mul] using hx.1.2.le)

private lemma JJ'_nonneg (x : ℝ × ℝ × ℝ) (hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1)
    (n : ℕ) :
    0 ≤ (x.2.1 * (1 - x.2.1) * x.2.2 * (1 - x.2.2) * x.1 * (1 - x.1) /
      (1 - (1 - x.2.1 * x.2.2) * x.1)) ^ n /
      (1 - (1 - x.2.1 * x.2.2) * x.1) := by
  simp only [Set.mem_prod, Set.mem_Ioo] at hx
  obtain ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩, hz0, hz1⟩ := hx
  have hden := (pos_aux x ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩, hz0, hz1⟩).le
  have hnum := mul_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hy0.le (sub_pos.mpr hy1).le)
      hz0.le) (sub_pos.mpr hz1).le) hx0.le) (sub_pos.mpr hx1).le
  exact div_nonneg (pow_nonneg (div_nonneg hnum hden) n) hden

lemma JJENN_upper (n : ℕ) : JJENN n ≤
    ENNReal.ofReal (2 * (1 / 30) ^ n * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3) := by
  calc
  _ ≤ ∫⁻ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    ENNReal.ofReal ((1 / 30) ^ n / (1 - (1 - x.2.1 * x.2.2) * x.1)) := by
    rw [JJENN, ← MeasureTheory.lintegral_indicator (by measurability),
        ← MeasureTheory.lintegral_indicator (by measurability)]
    apply MeasureTheory.lintegral_mono
    intro x
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases h : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
    · simp only [h, ↓reduceIte]
      simp only [Set.mem_prod, Set.mem_Ioo] at h
      apply ENNReal.ofReal_le_ofReal
      rw [div_le_div_iff_of_pos_right]
      · apply pow_le_pow_left₀
        · apply div_nonneg
          · apply mul_nonneg _ (by linarith)
            apply mul_nonneg _ (by linarith)
            apply mul_nonneg _ (by linarith)
            apply mul_nonneg _ (by linarith)
            apply mul_nonneg (by linarith) (by linarith)
          · linarith [pos_aux x h]
        · suffices x.2.1 * (1 - x.2.1) * x.2.2 * (1 - x.2.2) * x.1 * (1 - x.1) /
            (1 - (1 - x.2.1 * x.2.2) * x.1) < (1 / 30 : ℝ)by linarith
          apply bound'' <;> linarith
      · exact pos_aux x h
    · simp only [h, ↓reduceIte, le_refl]
  _ = ENNReal.ofReal ((1 / 30) ^ n) *
      ∫⁻ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    ENNReal.ofReal (1 / (1 - (1 - x.2.1 * x.2.2) * x.1)) := by
    rw [← MeasureTheory.lintegral_const_mul]
    · rw [← MeasureTheory.lintegral_indicator (by measurability),
        ← MeasureTheory.lintegral_indicator (by measurability)]
      congr
      ext x
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases h : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · simp only [h, ↓reduceIte]
        rw [← ENNReal.ofReal_mul, ← mul_one_div]
        apply pow_nonneg (by norm_num)
      · simp only [h, ↓reduceIte]
    · apply Measurable.ennreal_ofReal
      apply Measurable.const_div
      apply Measurable.const_sub
      apply Measurable.mul _ measurable_fst
      apply Measurable.const_sub
      apply Measurable.mul
      · exact Measurable.fun_comp measurable_fst measurable_snd
      · exact Measurable.fun_comp measurable_snd measurable_snd
  _ = ENNReal.ofReal (2 * (1 / 30) ^ n * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3) := by
    have h := JENN_eq_triple 0 0
    simp only [pow_zero, mul_one] at h
    rw [← h, J_ENN_rr]
    simp only [one_div, inv_pow, zero_lt_one, Finset.Icc_eq_empty_of_lt, Finset.sum_empty, mul_zero,
      sub_zero]
    rw [← ENNReal.ofReal_mul (by norm_num), ← mul_assoc]
    nth_rw 2 [mul_comm]

lemma integrableOn_JJ' (n : ℕ) : MeasureTheory.Integrable (fun (x : ℝ × ℝ × ℝ) ↦
    (x.2.1 * (1 - x.2.1) * x.2.2 * (1 - x.2.2) * x.1 * (1 - x.1) /
      (1 - (1 - x.2.1 * x.2.2) * x.1)) ^ n /
    (1 - (1 - x.2.1 * x.2.2) * x.1))
    (MeasureTheory.volume.restrict (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1)) := by
  rw [MeasureTheory.Integrable]
  constructor
  · apply AEMeasurable.aestronglyMeasurable
    measurability
  · rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    set k := _
    change k < ⊤
    have : k = JJENN n := by
      simp only [k, JJENN]
      rw [← MeasureTheory.lintegral_indicator (by measurability),
        ← MeasureTheory.lintegral_indicator (by measurability)]
      congr
      ext x
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · simp only [hx, ↓reduceIte, norm_mul, norm_div, Real.norm_eq_abs, norm_pow]
        simp only [Set.mem_prod, Set.mem_Ioo] at hx
        rw [ENNReal.ofReal_eq_ofReal_iff]
        · congr 3
          · rw [abs_eq_self.2, abs_eq_self.2, abs_eq_self.2, abs_eq_self.2, abs_eq_self.2,
              abs_eq_self.2] <;>
              linarith only [hx.1.1, hx.1.2, hx.2.1.1, hx.2.1.2, hx.2.2.1, hx.2.2.2]
          · simp only [abs_eq_self, sub_nonneg]
            exact (sub_pos.mp (pos_aux x hx)).le
          · simp only [abs_eq_self, sub_nonneg]
            exact (sub_pos.mp (pos_aux x hx)).le
        · positivity
        · exact JJ'_nonneg x hx n
      · simp only [hx, ↓reduceIte]
    rw [this]
    apply LE.le.trans_lt (JJENN_upper n)
    simp only [one_div, inv_pow, ENNReal.ofReal_lt_top]

lemma bkShiftedLegendre_bound (n : ℕ) (x : ℝ) (hx : 0 < x ∧ x < 1) :
  |eval x (bkShiftedLegendre n)| ≤
    ∑ x_1 ∈ Finset.range (n + 1), (n.choose x_1 : ℝ) * ((n + x_1).choose n) := by
  simp only [bkShiftedLegendre_eq_sum, map_pow, map_neg, map_one, eval_finsetSum,
    eval_mul, eval_pow, eval_neg, eval_one, eval_natCast, eval_X]
  have := Finset.abs_sum_le_sum_abs
    (f := fun y => (-1) ^ y * ↑(n.choose y) * ↑((n + y).choose n) * x ^ y)
    (s := Finset.range (n + 1))
  trans
  · apply this
  · apply Finset.sum_le_sum
    intro i _
    simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast, one_mul]
    trans ↑(n.choose i) * ↑((n + i).choose n) * 1
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply pow_le_one₀
      · simp
      · rw [abs_eq_self.2 (by linarith)]
        linarith
    · simp

lemma Measurable_one_div_aux :
    Measurable fun (x : ℝ × ℝ × ℝ) ↦
      ENNReal.ofReal (1 / (1 - (1 - x.2.1 * x.2.2) * x.1)) := by
  apply Measurable.ennreal_ofReal
  apply Measurable.const_div
  apply Measurable.const_sub
  apply Measurable.mul _ measurable_fst
  apply Measurable.const_sub
  apply Measurable.mul
  · exact Measurable.fun_comp measurable_fst measurable_snd
  · exact Measurable.fun_comp measurable_snd measurable_snd

lemma integrableOn_JJ1 (n : ℕ) : MeasureTheory.Integrable
  (Function.uncurry fun z x ↦
    eval x.1 (bkShiftedLegendre n) * eval x.2 (bkShiftedLegendre n) *
      (1 / (1 - (1 - x.1 * x.2) * z)))
  ((MeasureTheory.volume.restrict (Set.Ioo 0 1)).prod
    (MeasureTheory.volume.restrict (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1))) := by
  rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod,
    MeasureTheory.Integrable]
  constructor
  · apply AEMeasurable.aestronglyMeasurable
    measurability
  · rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    set k := _
    set C := ∑ x_1 ∈ Finset.range (n + 1), (n.choose x_1 : ℝ) * ((n + x_1).choose n)
    change k < ⊤
    have : k ≤ ENNReal.ofReal (C ^ 2) *
        ∫⁻ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      ENNReal.ofReal (1 / (1 - (1 - x.2.1 * x.2.2) * x.1)) := by
      simp only [k]
      rw [← MeasureTheory.lintegral_const_mul _ Measurable_one_div_aux]
      rw [← MeasureTheory.lintegral_indicator (by measurability),
        ← MeasureTheory.lintegral_indicator (by measurability)]
      apply MeasureTheory.lintegral_mono
      intro x
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · simp only [hx, ↓reduceIte, Real.norm_eq_abs]
        simp only [Set.mem_prod, Set.mem_Ioo] at hx
        rw [← ENNReal.ofReal_mul]
        · rw [ENNReal.ofReal_le_ofReal_iff]
          · rw [Function.uncurry_apply_pair, mul_one_div, mul_one_div, abs_div, div_le_div_iff₀]
            · apply mul_le_mul _ _ (by linarith [pos_aux x hx]) (by positivity)
              · rw [abs_mul, pow_two]
                apply mul_le_mul _ _ (by positivity) (by positivity)
                · apply bkShiftedLegendre_bound _ _ hx.2.1
                · apply bkShiftedLegendre_bound _ _ hx.2.2
              · exact le_abs_self (1 - (1 - x.2.1 * x.2.2) * x.1)
            · simp only [abs_pos]; linarith [pos_aux x hx]
            · exact pos_aux x hx
          · rw [mul_one_div]
            apply div_nonneg (by positivity)
            linarith [pos_aux x hx]
        · positivity
      · simp [hx]
    apply LE.le.trans_lt this
    have h := JENN_eq_triple 0 0
    simp only [pow_zero, mul_one] at h
    rw [← h, J_ENN_rr, ← ENNReal.ofReal_mul]
    · exact ENNReal.ofReal_lt_top
    · positivity

lemma integrableOn_JJ2 (n : ℕ) : MeasureTheory.Integrable (Function.uncurry fun z x ↦
  eval x.1 (bkShiftedLegendre n) * (x.1 * x.2 * z) ^ n * (1 - x.2) ^ n /
    (1 - (1 - x.1 * x.2) * z) ^ (n + 1))
  ((MeasureTheory.volume.restrict (Set.Ioo 0 1)).prod
    (MeasureTheory.volume.restrict (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1))) := by
  rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod,
    MeasureTheory.Integrable]
  constructor
  · apply AEMeasurable.aestronglyMeasurable
    measurability
  · rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    set k := _
    set C := ∑ x_1 ∈ Finset.range (n + 1), (n.choose x_1 : ℝ) * ((n + x_1).choose n)
    change k < ⊤
    have : k ≤ ENNReal.ofReal (|C|) *
        ∫⁻ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      ENNReal.ofReal (1 / (1 - (1 - x.2.1 * x.2.2) * x.1)) := by
      simp only [k]
      rw [← MeasureTheory.lintegral_const_mul _ Measurable_one_div_aux]
      rw [← MeasureTheory.lintegral_indicator (by measurability),
        ← MeasureTheory.lintegral_indicator (by measurability)]
      apply MeasureTheory.lintegral_mono
      intro x
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · simp only [hx, ↓reduceIte, Real.norm_eq_abs]
        simp only [Set.mem_prod, Set.mem_Ioo] at hx
        rw [← ENNReal.ofReal_mul]
        · rw [ENNReal.ofReal_le_ofReal_iff]
          · rw [Function.uncurry_apply_pair, pow_add, ← div_div, abs_div, mul_one_div,
              div_le_div_iff₀]
            · apply mul_le_mul _ _ (by linarith [pos_aux x hx]) (by positivity)
              · rw [← mul_div, mul_assoc, abs_mul, ← mul_one (a := |C|)]
                apply mul_le_mul _ _ (by positivity) (by positivity)
                · suffices |C| = C by
                    rw [this]
                    apply bkShiftedLegendre_bound _ _ hx.2.1
                  rw [abs_eq_self]
                  positivity
                · rcases x with ⟨x, ⟨y, z⟩⟩
                  simp only at hx ⊢
                  rcases hx with ⟨⟨hx0, hx1⟩, ⟨hy0, _⟩, ⟨hz0, hz1⟩⟩
                  rw [← div_pow, ← mul_pow, abs_pow]
                  suffices ineq1 : |y * z * x * ((1 - z) / (1 - (1 - y * z) * x))| ≤ 1 from
                    pow_le_one₀ (abs_nonneg _) ineq1
                  rw [show (1 - (1 - y * z) * x) = 1 - x + y * z * x by ring]
                  have hprod : 0 ≤ y * z * x := mul_nonneg (mul_nonneg hy0.le hz0.le) hx0.le
                  have hden : 0 < 1 - x + y * z * x :=
                    add_pos_of_pos_of_nonneg (sub_pos.mpr hx1) hprod
                  rw [abs_of_nonneg (mul_nonneg hprod
                    (div_nonneg (sub_pos.mpr hz1).le hden.le)),
                    ← mul_div_assoc, div_le_one hden]
                  exact (mul_le_of_le_one_right hprod (sub_le_self 1 hz0.le)).trans
                    (le_add_of_nonneg_left (sub_pos.mpr hx1).le)
              · simp only [pow_one]
                exact le_abs_self (1 - (1 - x.2.1 * x.2.2) * x.1)
            · simp only [abs_pos]; linarith [pos_aux x hx]
            · exact pos_aux x hx
          · rw [mul_one_div]
            apply div_nonneg (by positivity)
            linarith [pos_aux x hx]
        · positivity
      · simp [hx]
    apply LE.le.trans_lt this
    have h := JENN_eq_triple 0 0
    simp only [pow_zero, mul_one] at h
    rw [← h, J_ENN_rr, ← ENNReal.ofReal_mul]
    · exact ENNReal.ofReal_lt_top
    · positivity

lemma integrableOn_JJ3 (n : ℕ) : MeasureTheory.Integrable
  (Function.uncurry fun z x ↦
    eval x.1 (bkShiftedLegendre n) * (1 - z) ^ n * (1 - x.2) ^ n /
      (1 - (1 - x.1 * x.2) * z))
  ((MeasureTheory.volume.restrict (Set.Ioo 0 1)).prod
    (MeasureTheory.volume.restrict (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1))) := by
  rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod,
    MeasureTheory.Integrable]
  constructor
  · apply AEMeasurable.aestronglyMeasurable
    measurability
  · rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    set k := _
    set C := ∑ x_1 ∈ Finset.range (n + 1), (n.choose x_1 : ℝ) * ((n + x_1).choose n)
    change k < ⊤
    have : k ≤
        ENNReal.ofReal (|C|) *
          ∫⁻ (x : ℝ × ℝ × ℝ) in
            Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
            ENNReal.ofReal (1 / (1 - (1 - x.2.1 * x.2.2) * x.1)) := by
      simp only [k]
      rw [← MeasureTheory.lintegral_const_mul _ Measurable_one_div_aux]
      rw [← MeasureTheory.lintegral_indicator (by measurability),
        ← MeasureTheory.lintegral_indicator (by measurability)]
      apply MeasureTheory.lintegral_mono
      intro x
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · simp only [hx, ↓reduceIte, Real.norm_eq_abs]
        simp only [Set.mem_prod, Set.mem_Ioo] at hx
        rw [← ENNReal.ofReal_mul]
        · rw [ENNReal.ofReal_le_ofReal_iff]
          · rw [Function.uncurry_apply_pair, mul_one_div, abs_div, div_le_div_iff₀]
            · apply mul_le_mul _ _ (by linarith [pos_aux x hx]) (by positivity)
              · rw [abs_mul, ← mul_one (a := |C|)]
                apply mul_le_mul _ _ (by positivity) (by positivity)
                · rw [abs_mul, ← mul_one (a := |C|)]
                  apply mul_le_mul _ _ (by positivity) (by positivity)
                  · suffices |C| = C by
                      rw [this]
                      apply bkShiftedLegendre_bound _ _ hx.2.1
                    rw [abs_eq_self]
                    positivity
                  · simp only [abs_pow]
                    apply pow_le_one₀
                    · simp only [abs_nonneg]
                    · rw [abs_eq_self.2 (by linarith)]
                      linarith
                · simp only [abs_pow]
                  apply pow_le_one₀
                  · simp only [abs_nonneg]
                  · rw [abs_eq_self.2 (by linarith)]
                    linarith
              · exact le_abs_self (1 - (1 - x.2.1 * x.2.2) * x.1)
            · simp only [abs_pos]; linarith [pos_aux x hx]
            · exact pos_aux x hx
          · rw [mul_one_div]
            apply div_nonneg (by positivity)
            linarith [pos_aux x hx]
        · positivity
      · simp [hx]
    apply LE.le.trans_lt this
    have h := JENN_eq_triple 0 0
    simp only [pow_zero, mul_one] at h
    rw [← h, J_ENN_rr, ← ENNReal.ofReal_mul]
    · exact ENNReal.ofReal_lt_top
    · positivity

lemma eq1_integrableOn_aux1 (n : ℕ) (z : ℝ) (hz : z ∈ Set.Ioo 0 1) :
    MeasureTheory.Integrable
      (fun x ↦
        eval x.1 (bkShiftedLegendre n) * eval x.2 (bkShiftedLegendre n) *
          (1 / (1 - (1 - x.1 * x.2) * z)))
      ((MeasureTheory.volume.restrict (Set.Ioo 0 1)).prod
        (MeasureTheory.volume.restrict (Set.Ioo 0 1))) := by
  rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
  apply MeasureTheory.IntegrableOn.integrable
  apply MeasureTheory.IntegrableOn.mono_set (t := Set.Icc 0 1 ×ˢ Set.Icc 0 1)
  · apply ContinuousOn.integrableOn_compact
    · simp only [Set.Icc_prod_Icc, Prod.mk_zero_zero, Prod.mk_one_one, isCompact_Icc]
    · simp only [bkShiftedLegendre_eq_sum, map_pow, map_neg, map_one]
      apply ContinuousOn.mul
      · apply ContinuousOn.mul
        · simp only [eval_finsetSum, eval_mul, eval_pow, eval_neg, eval_one, eval_natCast, eval_X]
          apply continuousOn_finsetSum
          intro i _
          apply ContinuousOn.mul continuousOn_const
          apply ContinuousOn.pow continuousOn_fst
        · simp only [eval_finsetSum, eval_mul, eval_pow, eval_neg, eval_one, eval_natCast, eval_X]
          apply continuousOn_finsetSum
          intro i _
          apply ContinuousOn.mul continuousOn_const
          apply ContinuousOn.pow continuousOn_snd
      · apply ContinuousOn.div continuousOn_const
        · apply ContinuousOn.sub continuousOn_const
          apply ContinuousOn.mul _ continuousOn_const
          apply ContinuousOn.sub continuousOn_const
          apply ContinuousOn.mul continuousOn_fst continuousOn_snd
        · intro x hx
          suffices 1 - (1 - x.1 * x.2) * z > 0 by linarith
          simp only [Set.mem_prod, Set.mem_Icc] at hx
          simp only [Set.mem_Ioo, gt_iff_lt, sub_pos] at hz ⊢
          suffices (1 - x.1 * x.2) * z ≤ z by linarith
          apply mul_le_of_le_one_left (by linarith)
          simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
          nlinarith
  · apply Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self

lemma eq1_integrableOn_aux2 (n : ℕ) (z : ℝ) (hz : z ∈ Set.Ioo 0 1) :
    MeasureTheory.Integrable
      (fun x ↦
        eval x.1 (bkShiftedLegendre n) * (x.1 * x.2 * z) ^ n * (1 - x.2) ^ n /
          (1 - (1 - x.1 * x.2) * z) ^ (n + 1))
      ((MeasureTheory.volume.restrict (Set.Ioo 0 1)).prod
        (MeasureTheory.volume.restrict (Set.Ioo 0 1))) := by
  rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
  apply MeasureTheory.IntegrableOn.integrable
  apply MeasureTheory.IntegrableOn.mono_set (t := Set.Icc 0 1 ×ˢ Set.Icc 0 1)
  · apply ContinuousOn.integrableOn_compact
    · simp only [Set.Icc_prod_Icc, Prod.mk_zero_zero, Prod.mk_one_one, isCompact_Icc]
    · simp only [bkShiftedLegendre_eq_sum, map_pow, map_neg, map_one]
      apply ContinuousOn.div
      · apply ContinuousOn.mul
        · apply ContinuousOn.mul
          · simp only [eval_finsetSum, eval_mul, eval_pow, eval_neg, eval_one,
              eval_natCast, eval_X]
            apply continuousOn_finsetSum
            intro i _
            apply ContinuousOn.mul continuousOn_const
            apply ContinuousOn.pow continuousOn_fst
          · apply ContinuousOn.pow
            apply ContinuousOn.mul _ continuousOn_const
            apply ContinuousOn.mul continuousOn_fst continuousOn_snd
        · apply ContinuousOn.pow
          apply ContinuousOn.sub continuousOn_const continuousOn_snd
      · apply ContinuousOn.pow
        apply ContinuousOn.sub continuousOn_const
        apply ContinuousOn.mul _ continuousOn_const
        apply ContinuousOn.sub continuousOn_const
        apply ContinuousOn.mul continuousOn_fst continuousOn_snd
      · intro x hx
        suffices 1 - (1 - x.1 * x.2) * z > 0 by positivity
        simp only [Set.mem_prod, Set.mem_Icc] at hx
        simp only [Set.mem_Ioo, gt_iff_lt, sub_pos] at hz ⊢
        suffices (1 - x.1 * x.2) * z ≤ z by linarith
        apply mul_le_of_le_one_left (by linarith)
        simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
        nlinarith
  · apply Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self

lemma double_integral_eq1 (n : ℕ) (z : ℝ) (hz : z ∈ Set.Ioo 0 1) :
    ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      eval x.1 (bkShiftedLegendre n) * eval x.2 (bkShiftedLegendre n) *
        (1 / (1 - (1 - x.1 * x.2) * z)) =
    ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      eval x.1 (bkShiftedLegendre n) * (x.1 * x.2 * z) ^ n * (1 - x.2) ^ n /
        (1 - (1 - x.1 * x.2) * z) ^ (n + 1) := by
  calc
  _ = ∫ (x : ℝ) in Set.Ioo 0 1, eval x (bkShiftedLegendre n) * ∫ (y : ℝ) in Set.Ioo 0 1,
     eval y (bkShiftedLegendre n) * (1 / (1 - (1 - x * y) * z)) := by
    rw [MeasureTheory.Measure.volume_eq_prod, ← MeasureTheory.Measure.prod_restrict,
        MeasureTheory.integral_prod]
    · apply MeasureTheory.setIntegral_congr_fun (by measurability)
      intro x _
      simp only
      rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by norm_num),
        ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by norm_num),
        ← intervalIntegral.integral_const_mul]
      simp only [one_div, ← mul_assoc]
    · exact eq1_integrableOn_aux1 n z hz
  _ = ∫ (x : ℝ) in Set.Ioo 0 1, eval x (bkShiftedLegendre n) * ∫ (y : ℝ) in Set.Ioo 0 1,
    (x * y * z) ^ n * (1 - y) ^ n / (1 - (1 - x * y) * z) ^ (n + 1) := by
    apply MeasureTheory.setIntegral_congr_fun (by measurability)
    intro x hx
    simp only
    congr 1
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by norm_num),
      ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by norm_num)]
    rw [legendre_integral_special n hx hz]
  _ = ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    eval x.1 (bkShiftedLegendre n) * (x.1 * x.2 * z) ^ n * (1 - x.2) ^ n /
      (1 - (1 - x.1 * x.2) * z) ^ (n + 1) := by
    rw [MeasureTheory.Measure.volume_eq_prod, ← MeasureTheory.Measure.prod_restrict,
        MeasureTheory.integral_prod]
    · apply MeasureTheory.setIntegral_congr_fun (by measurability)
      intro x _
      simp only
      rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by norm_num),
        ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by norm_num),
        ← intervalIntegral.integral_const_mul]
      simp only [mul_div, ← mul_assoc]
    · exact eq1_integrableOn_aux2 n z hz

lemma ineq_aux (x : ℝ × ℝ) (z : ℝ)
    (hx : (0 < x.1 ∧ x.1 < 1) ∧ 0 < x.2 ∧ x.2 < 1) (hz : 0 ≤ z ∧ z ≤ 1) :
    0 ≤ (1 - z) / (1 - (1 - x.1 * x.2) * z) ∧
      (1 - z) / (1 - (1 - x.1 * x.2) * z) ≤ 1 := by
  constructor
  · apply div_nonneg (by linarith)
    simp only [sub_nonneg]
    refine (mul_le_of_le_one_left (by linarith) ?_).trans (by linarith)
    simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
    nlinarith
  · rw [div_le_iff₀]
    · simp only [one_mul, tsub_le_iff_right, sub_add, le_sub_self_iff, zero_add]
      by_cases h0 : z = 0
      · simp [h0]
      · suffices (1 - x.1 * x.2) * z < z by linarith
        rw [mul_lt_iff_lt_one_left]
        · simp only [sub_lt_self_iff]; nlinarith
        · by_contra!
          have : z = 0 := by linarith
          exact h0 this
    · simp only [sub_pos]
      rw [mul_comm]
      suffices z * (1 - x.1 * x.2) ≤ (1 - x.1 * x.2) by nlinarith
      apply mul_le_of_le_one_left (by nlinarith) hz.2

lemma ineq_aux1 (x : ℝ × ℝ) (z : ℝ)
    (hx : (0 < x.1 ∧ x.1 < 1) ∧ 0 < x.2 ∧ x.2 < 1) (hz : 0 ≤ z ∧ z ≤ 1) :
    1 - (1 - x.1 * x.2) * z ≠ 0 := by
  suffices (1 - x.1 * x.2) * z < 1 by linarith
  rw [mul_comm]
  suffices z * (1 - x.1 * x.2) ≤ (1 - x.1 * x.2) by nlinarith
  apply mul_le_of_le_one_left (by nlinarith) hz.2

lemma fun_eq_aux (x : ℝ × ℝ) (y : ℝ)
    (hx : (0 < x.1 ∧ x.1 < 1) ∧ 0 < x.2 ∧ x.2 < 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    deriv (fun z => (1 - z) / (1 - (1 - x.1 * x.2) * z)) y =
    (fun z => - x.1 * x.2 / (1 - (1 - x.1 * x.2) * z) ^ 2) y := by
  rw [deriv_fun_div]
  · rw [deriv_const_sub, deriv_const_sub, deriv_const_mul _ differentiableAt_id]
    simp only [deriv_id'', neg_mul, one_mul, neg_sub, mul_one]
    congr
    ring
  · apply DifferentiableAt.const_sub differentiableAt_id _
  · apply DifferentiableAt.const_sub (DifferentiableAt.const_mul differentiableAt_id _)
  · exact ineq_aux1 x y hx hy

lemma double_integral_eq2 (n : ℕ) (x : ℝ × ℝ)
    (hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) :
    ∫ (z : ℝ) in Set.Ioo 0 1,
      eval x.1 (bkShiftedLegendre n) * (x.1 * x.2 * z) ^ n * (1 - x.2) ^ n /
        (1 - (1 - x.1 * x.2) * z) ^ (n + 1) =
    ∫ (z : ℝ) in Set.Ioo 0 1,
      eval x.1 (bkShiftedLegendre n) * (1 - z) ^ n * (1 - x.2) ^ n /
        (1 - (1 - x.1 * x.2) * z) := by
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num),
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num)]
  simp only [← mul_div, mul_assoc]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  congr 1
  simp only [mul_div, ← mul_assoc]
  simp_rw [mul_comm (b := (1 - x.2) ^ n), ← mul_div]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  congr 1
  set g := fun z => (1 - z) / (1 - (1 - x.1 * x.2) * z)
  set g' := fun z => - x.1 * x.2 / (1 - (1 - x.1 * x.2) * z) ^ 2
  have hg : ContinuousOn (deriv g) (Set.uIcc 0 1) := by
    rw [continuousOn_congr (f := g')]
    · simp only [g']
      apply ContinuousOn.div continuousOn_const
      · apply ContinuousOn.pow
        apply ContinuousOn.sub continuousOn_const
        apply ContinuousOn.mul continuousOn_const continuousOn_id
      · intro y hy
        simp only [Set.mem_prod, Set.mem_Ioo, zero_le_one, Set.uIcc_of_le,
          Set.mem_Icc] at hx hy ⊢
        apply pow_ne_zero
        exact ineq_aux1 x y hx hy
    · intro y hy
      simp only [Set.mem_prod, Set.mem_Ioo, zero_le_one, Set.uIcc_of_le, Set.mem_Icc] at hx hy
      exact fun_eq_aux x y hx hy
  simp only [Set.mem_prod, Set.mem_Ioo] at hx
  symm
  calc
  _ = -∫ (y : ℝ) in (g 0)..g 1, (1 - y) ^ n / (1 - (1 - x.1 * x.2) * y) := by
    simp only [sub_zero, mul_zero, ne_eq, one_ne_zero, not_false_eq_true, div_self, sub_self,
      mul_one, sub_sub_cancel, zero_div, g]
    rw [intervalIntegral.integral_symm]
  _ = -∫ (y : ℝ) in (0)..1, (deriv g) y * (1 - g y) ^ n / (1 - (1 - x.1 * x.2) * g y) := by
    rw [neg_inj, ← intervalIntegral.integral_comp_mul_deriv' (f' := deriv g) (h' := hg)]
    · simp only [Function.comp_apply, div_mul_eq_mul_div, mul_comm]
    · intro y hy
      simp only [hasDerivAt_deriv_iff, g]
      apply DifferentiableAt.div (DifferentiableAt.const_sub differentiableAt_id _)
      · apply DifferentiableAt.const_sub (DifferentiableAt.const_mul differentiableAt_id _)
      · simp only [zero_le_one, Set.uIcc_of_le, Set.mem_Icc] at hy
        exact ineq_aux1 x y hx hy
    · have h1 : g '' Set.uIcc 0 1 = Set.Icc 0 1 := by
        simp only [zero_le_one, Set.uIcc_of_le, g]
        ext y
        constructor
        · intro hy
          simp only [Set.mem_image, Set.mem_Icc] at hy
          obtain ⟨z, hz, hz'⟩ := hy
          simp only [Set.mem_Icc]
          rw [← hz']
          exact ineq_aux x z hx hz
        · intro hy
          simp only [Set.mem_Icc] at hy
          simp only [Set.mem_image, Set.mem_Icc]
          use (1 - y) / (1 - (1 - x.1 * x.2) * y)
          constructor
          · exact ineq_aux x y hx hy
          · have eq1 :
                ((1 - (1 - x.1 * x.2) * y) - (1 - y)) /
                  (1 - (1 - x.1 * x.2) * y) =
                1 - (1 - y) / (1 - (1 - x.1 * x.2) * y) := by
                rw [sub_div, div_self (ineq_aux1 x y hx hy)]
            have eq2 : ((1 - (1 - x.1 * x.2) * y) - (1 - x.1 * x.2) * (1 - y)) /
                (1 - (1 - x.1 * x.2) * y) =
              1 - (1 - x.1 * x.2) * ((1 - y) /
                (1 - (1 - x.1 * x.2) * y)) := by
              rw [sub_div, div_self (ineq_aux1 x y hx hy), mul_div]
            rw [div_eq_iff]
            · rw [← eq1, ← eq2, mul_div,
                div_eq_div_iff (ineq_aux1 x y hx hy) (ineq_aux1 x y hx hy)]
              ring
            · rw [← eq2]
              apply div_ne_zero _ (ineq_aux1 x y hx hy)
              rw [mul_sub]
              simp only [mul_one, sub_sub_sub_cancel_right, sub_sub_cancel, ne_eq, mul_eq_zero,
                not_or]
              constructor <;> linarith
      rw [h1]
      apply ContinuousOn.div
      · apply ContinuousOn.pow
        apply ContinuousOn.sub continuousOn_const continuousOn_id
      · apply ContinuousOn.sub continuousOn_const
        apply ContinuousOn.mul continuousOn_const continuousOn_id
      · intro y hy
        simp only [Set.mem_Icc] at hy
        exact ineq_aux1 x y hx hy
  _ = ∫ (y : ℝ) in (0)..1,
    x.1 * x.2 / (1 - (1 - x.1 * x.2) * y) ^ 2 * (1 - g y) ^ n /
      (1 - (1 - x.1 * x.2) * g y) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro y hy
    simp only [zero_le_one, Set.uIcc_of_le, Set.mem_Icc] at hy ⊢
    simp only [g]
    rw [fun_eq_aux x y hx hy]
    simp [neg_div]
  _ = ∫ (y : ℝ) in (0)..1, (x.1 * x.2 * y) ^ n / (1 - (1 - x.1 * x.2) * y) ^ (n + 1) := by
    apply intervalIntegral.integral_congr
    intro y hy
    simp only [zero_le_one, Set.uIcc_of_le, Set.mem_Icc] at hy ⊢
    have eq1 : ((1 - (1 - x.1 * x.2) * y) - (1 - y)) / (1 - (1 - x.1 * x.2) * y) =
        1 - (1 - y) / (1 - (1 - x.1 * x.2) * y) := by
        rw [sub_div, div_self (ineq_aux1 x y hx hy)]
    have eq2 : ((1 - (1 - x.1 * x.2) * y) - (1 - x.1 * x.2) * (1 - y)) /
      (1 - (1 - x.1 * x.2) * y) = 1 - (1 - x.1 * x.2) * ((1 - y) / (1 - (1 - x.1 * x.2) * y)) := by
      rw [sub_div, div_self (ineq_aux1 x y hx hy), mul_div]
    rw [div_mul_eq_mul_div, div_div, div_eq_div_iff]
    · simp only [← eq1, sub_sub_sub_cancel_left, div_pow, ← eq2, g]
      rw [mul_div, mul_comm, mul_div, mul_div, mul_div, div_eq_div_iff]
      · ring
      · apply pow_ne_zero
        exact ineq_aux1 x y hx hy
      · exact ineq_aux1 x y hx hy
    · apply mul_ne_zero
      · apply pow_ne_zero
        exact ineq_aux1 x y hx hy
      · simp only [g, ← eq2]
        apply div_ne_zero _ (ineq_aux1 x y hx hy)
        rw [mul_sub]
        simp only [mul_one, sub_sub_sub_cancel_right, sub_sub_cancel, ne_eq, mul_eq_zero,
          not_or]
        constructor <;> linarith
    · apply pow_ne_zero
      exact ineq_aux1 x y hx hy

lemma eq3_integrableOn_aux (n : ℕ) (z : ℝ) (hz : z ∈ Set.Ioo 0 1) :
    MeasureTheory.Integrable
      (fun x ↦
        eval x.1 (bkShiftedLegendre n) * (1 - x.2) ^ n /
          (1 - (1 - x.1 * x.2) * z))
      ((MeasureTheory.volume.restrict (Set.Ioo 0 1)).prod
        (MeasureTheory.volume.restrict (Set.Ioo 0 1))) := by
  rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
  apply MeasureTheory.IntegrableOn.integrable
  apply MeasureTheory.IntegrableOn.mono_set (t := Set.Icc 0 1 ×ˢ Set.Icc 0 1)
  · apply ContinuousOn.integrableOn_compact
    · simp only [Set.Icc_prod_Icc, Prod.mk_zero_zero, Prod.mk_one_one, isCompact_Icc]
    · simp only [bkShiftedLegendre_eq_sum, map_pow, map_neg, map_one]
      apply ContinuousOn.div
      · apply ContinuousOn.mul
        · simp only [eval_finsetSum, eval_mul, eval_pow, eval_neg, eval_one,
            eval_natCast, eval_X]
          apply continuousOn_finsetSum
          intro i _
          apply ContinuousOn.mul continuousOn_const
          apply ContinuousOn.pow continuousOn_fst
        · apply ContinuousOn.pow (ContinuousOn.sub continuousOn_const continuousOn_snd)
      · apply ContinuousOn.sub continuousOn_const
        apply ContinuousOn.mul _ continuousOn_const
        apply ContinuousOn.sub continuousOn_const
        apply ContinuousOn.mul continuousOn_fst continuousOn_snd
      · intro x hx
        suffices 1 - (1 - x.1 * x.2) * z > 0 by linarith
        simp only [Set.mem_prod, Set.mem_Icc] at hx
        simp only [Set.mem_Ioo, gt_iff_lt, sub_pos] at hz ⊢
        suffices (1 - x.1 * x.2) * z ≤ z by linarith
        apply mul_le_of_le_one_left (by linarith)
        simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
        nlinarith
  · apply Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self

lemma double_integral_eq3 (n : ℕ) (z : ℝ) (hz : z ∈ Set.Ioo 0 1) :
    ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      (x.1 * x.2 * z * (1 - x.1) * (1 - x.2)) ^ n /
        (1 - (1 - x.1 * x.2) * z) ^ (n + 1) =
    ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      eval x.1 (bkShiftedLegendre n) * (1 - x.2) ^ n /
        (1 - (1 - x.1 * x.2) * z) := by
  symm
  rw [MeasureTheory.Measure.volume_eq_prod, ← MeasureTheory.Measure.prod_restrict,
      MeasureTheory.integral_prod, MeasureTheory.integral_integral_swap]
  · rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
    simp only
    calc
    _ = ∫ (y : ℝ) in Set.Ioo 0 1, (1 - y) ^ n * ∫ (x : ℝ) in Set.Ioo 0 1,
      eval x (bkShiftedLegendre n) / (1 - (1 - x * y) * z) := by
      apply MeasureTheory.setIntegral_congr_fun (by measurability)
      intro y hy
      simp only [Set.mem_Ioo] at hy ⊢
      rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by norm_num),
        ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by norm_num),
        ← intervalIntegral.integral_const_mul]
      simp [mul_div, mul_comm]
    _ = ∫ (y : ℝ) in Set.Ioo 0 1, (1 - y) ^ n *
        ∫ (x : ℝ) in (0)..1,
          (y * x * z) ^ n * (1 - x) ^ n /
            (1 - (1 - y * x) * z) ^ (n + 1) := by
      apply MeasureTheory.setIntegral_congr_fun (by measurability)
      intro y hy
      simp only
      congr 1
      rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by norm_num)]
      have := legendre_integral_special n hy hz
      simp only [mul_one_div] at this
      simp only [← this]
      simp only [mul_comm]
    _ = ∫ (y : ℝ) in Set.Ioo 0 1, ∫ (x : ℝ) in Set.Ioo 0 1,
      (1 - y) ^ n * (y * x * z) ^ n * (1 - x) ^ n /
        (1 - (1 - y * x) * z) ^ (n + 1) := by
      apply MeasureTheory.setIntegral_congr_fun (by measurability)
      intro y _
      simp only
      rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le (by norm_num),
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
      simp_rw [mul_div, ← mul_assoc]
    _ = ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      (x.1 * x.2 * z * (1 - x.1) * (1 - x.2)) ^ n / (1 - (1 - x.1 * x.2) * z) ^ (n + 1) := by
      rw [MeasureTheory.Measure.volume_eq_prod, ← MeasureTheory.Measure.prod_restrict,
        MeasureTheory.integral_prod]
      · simp [mul_pow, mul_comm]
      · rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
        apply MeasureTheory.IntegrableOn.integrable
        apply MeasureTheory.IntegrableOn.mono_set (t := Set.Icc 0 1 ×ˢ Set.Icc 0 1)
        · apply ContinuousOn.integrableOn_compact
          · simp only [Set.Icc_prod_Icc, Prod.mk_zero_zero, Prod.mk_one_one, isCompact_Icc]
          · apply ContinuousOn.div
            · apply ContinuousOn.pow
              apply ContinuousOn.mul _ (ContinuousOn.sub continuousOn_const continuousOn_snd)
              apply ContinuousOn.mul _ (ContinuousOn.sub continuousOn_const continuousOn_fst)
              apply ContinuousOn.mul _ continuousOn_const
              apply ContinuousOn.mul continuousOn_fst continuousOn_snd
            · apply ContinuousOn.pow
              apply ContinuousOn.sub continuousOn_const _
              apply ContinuousOn.mul _ continuousOn_const
              apply ContinuousOn.sub continuousOn_const _
              apply ContinuousOn.mul continuousOn_fst continuousOn_snd
            · intro x hx
              simp only [Set.mem_prod, Set.mem_Icc, Set.mem_Ioo] at hx hz
              apply pow_ne_zero
              suffices (1 - x.1 * x.2) * z ≤ z by linarith
              apply mul_le_of_le_one_left (by linarith)
              simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
              nlinarith
        · apply Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self
  · exact eq3_integrableOn_aux n z hz
  · exact eq3_integrableOn_aux n z hz

theorem JJ_eq_form (n : ℕ) : JJ n = JJ' n := by
  simp only [JJ, JJ']
  calc
  _ = ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    (∫ (z : ℝ) in Set.Ioo 0 1,
      eval x.1 (bkShiftedLegendre n) * eval x.2 (bkShiftedLegendre n) *
        (1 / (1 - (1 - x.1 * x.2) * z))) := by
    apply MeasureTheory.setIntegral_congr_fun (by measurability)
    intro x hx
    simp only [Set.mem_prod, Set.mem_Ioo] at hx ⊢
    rw [mul_assoc, mul_comm, ← integral1, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by norm_num),
      intervalIntegral.integral_const_mul] <;> nlinarith
  _ = ∫ (z : ℝ) in Set.Ioo 0 1, ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    eval x.1 (bkShiftedLegendre n) * eval x.2 (bkShiftedLegendre n) *
      (1 / (1 - (1 - x.1 * x.2) * z)) := by
    symm
    rw [MeasureTheory.integral_integral_swap]
    exact integrableOn_JJ1 n
  _ = ∫ (z : ℝ) in Set.Ioo 0 1, ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    eval x.1 (bkShiftedLegendre n) * (x.1 * x.2 * z) ^ n * (1 - x.2) ^ n /
      (1 - (1 - x.1 * x.2) * z) ^ (n + 1) := by
    apply MeasureTheory.setIntegral_congr_fun (by measurability)
    intro z hz
    simp only
    exact double_integral_eq1 n z hz
  _ = ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1, ∫ (z : ℝ) in Set.Ioo 0 1,
    eval x.1 (bkShiftedLegendre n) * (x.1 * x.2 * z) ^ n * (1 - x.2) ^ n /
      (1 - (1 - x.1 * x.2) * z) ^ (n + 1) := by
    rw [MeasureTheory.integral_integral_swap]
    exact integrableOn_JJ2 n
  _ = ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1, ∫ (z : ℝ) in Set.Ioo 0 1,
    eval x.1 (bkShiftedLegendre n) * (1 - z) ^ n * (1 - x.2) ^ n / (1 - (1 - x.1 * x.2) * z) := by
    apply MeasureTheory.setIntegral_congr_fun (by measurability)
    intro x hx
    simp only
    exact double_integral_eq2 n x hx
  _ = ∫ (z : ℝ) in Set.Ioo 0 1, ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    eval x.1 (bkShiftedLegendre n) * (1 - z) ^ n * (1 - x.2) ^ n / (1 - (1 - x.1 * x.2) * z) := by
    symm
    rw [MeasureTheory.integral_integral_swap]
    exact integrableOn_JJ3 n
  _ = ∫ (z : ℝ) in Set.Ioo 0 1, (1 - z) ^ n *
      ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    (x.1 * x.2 * z * (1 - x.1) * (1 - x.2)) ^ n / (1 - (1 - x.1 * x.2) * z) ^ (n + 1) := by
    apply MeasureTheory.setIntegral_congr_fun (by measurability)
    intro z hz
    simp only
    rw [double_integral_eq3 n z hz, mul_comm, ← smul_eq_mul, ← integral_smul_const]
    apply MeasureTheory.setIntegral_congr_fun (by measurability)
    intro x _
    simp only
    rw [smul_eq_mul]
    ring
  _ = ∫ (z : ℝ) in Set.Ioo 0 1, ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    (x.1 * x.2 * z * (1 - x.1) * (1 - x.2) * (1 - z)) ^ n /
      (1 - (1 - x.1 * x.2) * z) ^ (n + 1) := by
    apply MeasureTheory.setIntegral_congr_fun (by measurability)
    intro z hz
    simp only
    rw [mul_comm, ← smul_eq_mul, ← integral_smul_const]
    apply MeasureTheory.setIntegral_congr_fun (by measurability)
    intro x _
    simp only
    rw [smul_eq_mul, mul_comm, mul_div, ← mul_pow]
    ring
  _ = ∫ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    (x.2.1 * (1 - x.2.1) * x.2.2 * (1 - x.2.2) * x.1 * (1 - x.1) /
      (1 - (1 - x.2.1 * x.2.2) * x.1)) ^ n /
      (1 - (1 - x.2.1 * x.2.2) * x.1) := by
    symm
    rw [MeasureTheory.Measure.volume_eq_prod, ← MeasureTheory.Measure.prod_restrict,
      MeasureTheory.integral_prod]
    · apply MeasureTheory.setIntegral_congr_fun (by measurability)
      intro x hx
      simp only
      apply MeasureTheory.setIntegral_congr_fun (by measurability)
      intro y _
      simp only
      rw [pow_add, ← div_div, div_pow]
      ring
    · rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
      exact integrableOn_JJ' n

theorem JJ_pos (n : ℕ) : 0 < JJ n := by
  rw [JJ_eq_form, JJ']
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae]
  · set F := _;
    change 0 < MeasureTheory.volume.restrict _ (Function.support F)
    have subset : Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ⊆ Function.support F := by
      intro a ha
      change F a ≠ 0
      simp only [div_pow, ne_eq, _root_.div_eq_zero_iff, pow_eq_zero_iff', mul_eq_zero, not_or,
        not_and, Decidable.not_not, F]
      simp only [Set.mem_prod, Set.mem_Ioo] at ha
      rcases ha with ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩, hz0, hz1⟩
      constructor
      · constructor
        · intro h
          rcases h with (h | h)
          · rcases h with (h | h)
            · rcases h with (h | h)
              · rcases h with (h | h)
                · rcases h with (h | h) <;> nlinarith
                · nlinarith
              · nlinarith
            · nlinarith
          · nlinarith
        · intro h
          suffices ¬1 - (1 - a.2.1 * a.2.2) * a.1 = 0 by tauto
          suffices 1 - (1 - a.2.1 * a.2.2) * a.1 > 0 by linarith
          simp only [gt_iff_lt, sub_pos]
          suffices (1 - a.2.1 * a.2.2) * a.1 < a.1 by linarith
          simp_all
      · suffices 1 - (1 - a.2.1 * a.2.2) * a.1 > 0 by linarith
        simp only [gt_iff_lt, sub_pos]
        suffices (1 - a.2.1 * a.2.2) * a.1 < a.1 by linarith
        simp_all
    rw [MeasureTheory.Measure.restrict_apply']
    · rw [Set.inter_eq_right.2 subset]
      simp only [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
      simp only [Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, mul_one, zero_lt_one]
    · measurability
  · apply MeasureTheory.ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter
    · rw [MeasureTheory.IntegrableOn]
      exact integrableOn_JJ' n
    · rintro s hs -
      apply MeasureTheory.setIntegral_nonneg (by measurability)
      intro x hx
      by_cases h : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · exact JJ'_nonneg x h n
      · simp_all
  · exact integrableOn_JJ' n

lemma Summable_of_zeta_two' : Summable (fun (n : ℕ) ↦ 1 / ((n : ℝ) + 1) ^ 2) := by
  norm_cast
  simp only [Nat.cast_pow]
  rw [summable_nat_add_iff (k := 1) (f := fun k => 1 / (k ^ 2 : ℝ))]
  simp

lemma zeta3_pos : 0 < ∑' (n : ℕ), 1 / ((n : ℝ) + 1) ^ 3 := by
  apply Summable.tsum_pos (g := fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 3) (i := 1)
  · apply summable_of_sum_range_le (c := Real.pi ^ 2 / 6)
    · intro _
      positivity
    · intro n
      suffices
          ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1) ^ 3 ≤
            ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1) ^ 2 by
        have : ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1) ^ 2 ≤ Real.pi ^ 2 / 6 := by
          suffices
              ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1) ^ 2 ≤
                ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 2 by
            have h : ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 2 = (riemannZeta 2).re := by
              rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simp)]
              simp_rw [← Complex.ofReal_natCast]
              norm_cast
            rw [h, riemannZeta_two] at this
            norm_cast at *
          apply Summable.sum_le_tsum
          · intro i _
            positivity
          · exact Summable_of_zeta_two'
        linarith
      apply Finset.sum_le_sum
      intro i _
      rw [div_le_div_iff₀, one_mul, one_mul]
      · apply pow_le_pow_right₀ <;> linarith
      · positivity
      · positivity
  · intro m
    simp only [one_div, pow_succ]
    positivity
  · positivity

theorem JJ_upper (n : ℕ) :
    JJ n ≤ 2 * (1 / 30) ^ n * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 := by
  rw [JJ_eq_form, JJ', MeasureTheory.integral_eq_lintegral_of_nonneg_ae]
  · trans
      (ENNReal.ofReal
        (2 * (1 / 30 : ℝ) ^ n * ∑' (n : ℕ), 1 / ((n : ℝ) + 1) ^ 3)).toReal
    · apply ENNReal.toReal_mono
      · exact ENNReal.ofReal_ne_top
      · exact JJENN_upper n
    · rw [ENNReal.toReal_ofReal]
      apply mul_nonneg (by norm_num)
      exact zeta3_pos.le
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with x hx
    exact JJ'_nonneg x hx n
  · apply AEMeasurable.aestronglyMeasurable
    measurability

private lemma log_30_gt_339_div_100 : (339 / 100 : ℝ) < Real.log 30 := by
  have h30 : Real.log (30 : ℝ) = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (30 : ℝ) = (2 * 3) * 5 by norm_num, Real.log_mul, Real.log_mul] <;>
      norm_num
  nlinarith [Real.log_two_gt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9]

private lemma exp_339_div_100_div_30_lt_one : Real.exp (339 / 100 : ℝ) / 30 < 1 := by
  have h_exp : Real.exp (339 / 100 : ℝ) < 30 := by
    exact (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 30)).mp log_30_gt_339_div_100
  nlinarith

lemma eventually_d_pow_three_le_exp :
    ∀ᶠ n : ℕ in Filter.atTop,
      (d (Finset.Icc 1 n) : ℝ) ^ 3 ≤ (Real.exp (339 / 100 : ℝ)) ^ n := by
  have hpsi_nat :
      ∀ᶠ n : ℕ in Filter.atTop,
        Chebyshev.psi (n : ℝ) ≤ (113 / 100 : ℝ) * (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually ChebyshevAux.eventually_psi_le_mul
  filter_upwards [hpsi_nat] with n hn
  have hlog : Real.log (Nat.lcmUpto n : ℝ) ≤ (113 / 100 : ℝ) * (n : ℝ) := by
    simpa [Chebyshev.psi_eq_log_lcmUpto n] using hn
  have hlcm : (Nat.lcmUpto n : ℝ) ≤ Real.exp ((113 / 100 : ℝ) * (n : ℝ)) :=
    (Real.log_le_iff_le_exp (by exact_mod_cast Nat.lcmUpto_pos n)).mp hlog
  change (Nat.lcmUpto n : ℝ) ^ 3 ≤ (Real.exp (339 / 100 : ℝ)) ^ n
  calc
    (Nat.lcmUpto n : ℝ) ^ 3 ≤ (Real.exp ((113 / 100 : ℝ) * (n : ℝ))) ^ 3 := by
      gcongr
    _ = (Real.exp (339 / 100 : ℝ)) ^ n := by
      rw [← Real.exp_nat_mul ((113 / 100 : ℝ) * (n : ℝ)) 3,
        ← Real.exp_nat_mul (339 / 100 : ℝ) n]
      congr 1
      ring

theorem fun1_tendsto_zero :
    Filter.Tendsto (fun n ↦ ENNReal.ofReal (fun1 n)) Filter.atTop (nhds 0) := by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  if h : ε = ⊤ then
    simp [h]
  else
    delta fun1
    rw [show ε = ENNReal.ofReal ε.toReal by simp [h]]
    obtain hden := eventually_d_pow_three_le_exp
    obtain hpow := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (r := ENNReal.ofReal (Real.exp (339 / 100 : ℝ) / 30))
      (by
        simp only [ENNReal.ofReal_lt_one]
        exact exp_339_div_100_div_30_lt_one)
    rw [ENNReal.tendsto_atTop_zero] at hpow
    specialize hpow (ε / (ENNReal.ofReal (2 * (∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3))))
      (by
        simp only [one_div, gt_iff_lt, ENNReal.div_pos_iff, ne_eq, ENNReal.ofReal_ne_top,
          not_false_eq_true, and_true]
        aesop)
    rw [Filter.eventually_atTop] at hden
    obtain ⟨N1, hN1⟩ := hden
    obtain ⟨N2, hN2⟩ := hpow
    use N1.max N2
    intro n hn
    rw [ENNReal.ofReal_le_ofReal_iff (by simp)]
    suffices
        (d (Finset.Icc 1 n) : ℝ) ^ 3 * 2 * (1 / 30 : ℝ) ^ n *
            ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 ≤ ε.toReal by
      trans
        (d (Finset.Icc 1 n) : ℝ) ^ 3 * 2 * (1 / 30 : ℝ) ^ n *
          ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3
      · rw [mul_assoc, mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (by simp)
        linarith [JJ_upper n]
      · exact this
    calc
      (d (Finset.Icc 1 n) : ℝ) ^ 3 * 2 * (1 / 30 : ℝ) ^ n *
          ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3
          ≤ 2 * (Real.exp (339 / 100 : ℝ) / 30) ^ n *
              (∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3) := by
            apply mul_le_mul_of_nonneg_right _ (by linarith [zeta3_pos])
            nth_rewrite 2 [mul_comm, div_eq_mul_one_div]
            rw [mul_pow, ← mul_assoc]
            simp_all
      _ ≤ ε.toReal := by
        specialize hN2 n (le_of_max_le_right hn)
        rw [← ENNReal.ofReal_toReal_eq_iff.2 h,
          ← ENNReal.ofReal_div_of_pos (by linarith [zeta3_pos]),
          ← ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_le_ofReal_iff] at hN2
        · rw [le_div_iff₀ (by linarith [zeta3_pos])] at hN2
          linarith
        · suffices 0 < ε.toReal / (2 * ∑' (n : ℕ), 1 / ((n : ℝ) + 1) ^ 3) by
            linarith
          apply div_pos _ (by linarith [zeta3_pos])
          apply ENNReal.toReal_pos (by aesop) (by aesop)

theorem zeta3_irrational : ¬ ∃ r : ℚ, r = riemannZeta 3 := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simp)]
  simp_rw [← Complex.ofReal_natCast]
  norm_cast
  simp_rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  intro r
  rcases r with ⟨r, hr⟩
  let q := r.den
  let hq := Rat.den_nz r
  have prop1 := ENNReal.Tendsto.mul_const (b := (q : ENNReal)) fun1_tendsto_zero (by simp)
  rw [zero_mul] at prop1
  have prop2 : ∀ n : ℕ, fun1 n * q > 1 / 2 := by
    suffices ∀ n : ℕ, fun1 n * q ≥ 1 by
      intro n
      linarith [this n]
    intro n
    obtain ⟨a, b, h⟩ := linear_int n
    have : fun1 n * q > 0 := by
      delta fun1
      rw [mul_comm, ← mul_assoc]
      refine mul_pos ?_ (JJ_pos n)
      norm_cast
      apply mul_pos (by omega)
      exact pow_pos (fin_d_neq_zero n) 3
    rw [h, add_mul, mul_assoc, ← hr] at this ⊢
    simp only [ge_iff_le, q] at this ⊢
    norm_cast at this ⊢
    rw [Rat.mul_den_eq_num] at this ⊢
    norm_cast at this ⊢
  rw [ENNReal.tendsto_atTop_zero] at prop1
  specialize prop1 (1 / 2) (by simp)
  rcases prop1 with ⟨a, ha⟩
  specialize prop2 (a + 1)
  specialize ha (a + 1) (by simp)
  rw [gt_iff_lt, ← ENNReal.ofReal_lt_ofReal_iff, ENNReal.ofReal_mul' (by simp)] at prop2
  · suffices ENNReal.ofReal (fun1 (a + 1)) * ↑q < ENNReal.ofReal (fun1 (a + 1)) * ↑q by
      exact (lt_irrefl _ this).elim
    rw [show ENNReal.ofReal ↑q = (q : ENNReal) by simp only [ENNReal.ofReal_natCast],
      show ENNReal.ofReal (1 / 2) = 1 / 2 by
        simp_all] at prop2
    apply LE.le.trans_lt (b := (1 / 2 : ENNReal)) ha prop2
  · apply mul_pos _ (by simp; omega)
    apply mul_pos _ (JJ_pos (a + 1))
    apply pow_pos
    simp only [Nat.cast_pos]
    exact fin_d_neq_zero (a + 1)

end LeanPool.Zeta3Irrational

-- ===== Bridge to the formal-conjectures statement (new) =====
namespace OMA.Zeta3Bridge

open LeanPool.Zeta3Irrational

theorem riemannZeta_three_eq_ofReal :
    riemannZeta 3 = ((∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3 : ℝ) : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by norm_num), Complex.ofReal_tsum]
  congr 1
  funext n
  have h3 : (3 : ℂ) = ((3 : ℕ) : ℂ) := by norm_num
  rw [h3, Complex.cpow_natCast]
  push_cast
  ring

theorem exists_irrational_eq_riemannZeta_three :
    ∃ x : ℝ, Irrational x ∧ riemannZeta 3 = x := by
  refine ⟨_, ?_, riemannZeta_three_eq_ofReal⟩
  rintro ⟨q, hq⟩
  apply zeta3_irrational
  refine ⟨q, ?_⟩
  rw [riemannZeta_three_eq_ofReal, ← hq]
  push_cast
  rfl

end OMA.Zeta3Bridge

theorem OMA.solution : type_of% @RiemannZetaValues.irrational_three :=
  OMA.Zeta3Bridge.exists_irrational_eq_riemannZeta_three
