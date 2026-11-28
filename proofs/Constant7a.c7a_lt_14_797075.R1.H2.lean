-- SPDX-License-Identifier: Apache-2.0
import OMAReductions.R_Constant7a_c7a_lt_14_797075_R1
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FinCases

/-!
# Exponential bounds for the Rhin–Viola integral

Weighted AM–GM bounds the kernel on the unit square. A smaller rectangle
gives a lower bound with a different exponential rate.
-/

-- Credit: @grp06
-- The integral is from G. Rhin and C. Viola, Acta Arithmetica 77 (1996),
-- Theorem 5.1, https://doi.org/10.4064/aa-77-1-23-56.
-- The logarithmic reindexing is from @physbuzz's reduction:
-- https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/12855

open Filter MeasureTheory Set
open scoped Topology BigOperators Interval

noncomputable section

namespace Constant7aH2Proof

private def kernel (x y : ℝ) : ℝ :=
  (x ^ 12 * (1 - x) ^ 12 * y ^ 14 * (1 - y) ^ 14) / (1 - x * y) ^ 13

private def q : ℝ :=
  ((7 / 11) ^ 7 * (4 / 11) ^ 4) * ((3 / 5) ^ 9 * (2 / 5) ^ 6) *
    ((5 / 13) ^ 5 * (5 / 13) ^ 5 * (3 / 13) ^ 3)

private def r : ℝ := ((3 / 5) * (7 / 20)) ^ 26 / (16 / 25) ^ 13

private theorem weighted3 (m n p : ℕ) (h : 0 < m + n + p)
    {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x ^ m * y ^ n * z ^ p ≤
      ((↑m * x + ↑n * y + ↑p * z) / (↑(m + n + p) : ℝ)) ^ (m + n + p) := by
  let w : Fin 3 → ℝ := ![(m : ℝ), (n : ℝ), (p : ℝ)]
  let v : Fin 3 → ℝ := ![x, y, z]
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ w i := by
    intro i _
    fin_cases i <;> simp [w] <;> positivity
  have hv : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ v i := by
    intro i _
    fin_cases i <;> simp [v, hx, hy, hz]
  have hs : ∑ i, w i = ((m + n + p : ℕ) : ℝ) := by
    simp only [w, Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Nat.cast_add, add_zero, add_assoc]
  have hs0 : (0 : ℝ) < ((m + n + p : ℕ) : ℝ) := by exact_mod_cast h
  have ha := Real.geom_mean_le_arith_mean Finset.univ w v hw
    (by rw [hs]; exact hs0) hv
  rw [hs] at ha
  have ha' :
      (x ^ m * y ^ n * z ^ p) ^ ((↑(m + n + p) : ℝ)⁻¹) ≤
        (↑m * x + ↑n * y + ↑p * z) / (↑(m + n + p) : ℝ) := by
    simpa only [w, v, Fin.sum_univ_succ, Fin.prod_univ_succ, Finset.univ_eq_empty,
      Finset.sum_empty, Finset.prod_empty, Matrix.cons_val_zero, Matrix.cons_val_succ,
      add_zero, mul_one, Real.rpow_natCast, add_assoc, mul_assoc] using ha
  have hp := pow_le_pow_left₀
    (Real.rpow_nonneg (show 0 ≤ x ^ m * y ^ n * z ^ p by positivity) _)
    ha' (m + n + p)
  have he : ((x ^ m * y ^ n * z ^ p) ^ ((↑(m + n + p) : ℝ)⁻¹)) ^ (m + n + p) =
      x ^ m * y ^ n * z ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      inv_mul_cancel₀ hs0.ne', Real.rpow_one]
  rwa [he] at hp

private theorem simplex_bound (m n p : ℕ) (hm : 0 < m) (hn : 0 < n) (hp : 0 < p)
    {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hs : x + y + z = 1) :
    x ^ m * y ^ n * z ^ p ≤
      ((m : ℝ) / (↑(m + n + p) : ℝ)) ^ m *
      ((n : ℝ) / (↑(m + n + p) : ℝ)) ^ n *
      ((p : ℝ) / (↑(m + n + p) : ℝ)) ^ p := by
  let t : ℝ := ↑(m + n + p)
  let M : ℝ := ↑m / t
  let N : ℝ := ↑n / t
  let P : ℝ := ↑p / t
  have ht : 0 < t := by dsimp [t]; positivity
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hM : 0 < M := div_pos hm' ht
  have hN : 0 < N := div_pos hn' ht
  have hP : 0 < P := div_pos hp' ht
  have hmean : (↑m * (x / M) + ↑n * (y / N) + ↑p * (z / P)) / t = 1 := by
    have cancel (a u : ℝ) (ha : a ≠ 0) : a * (u / (a / t)) = u * t := by
      rw [div_div_eq_mul_div, ← mul_div_assoc, mul_comm a (u * t),
        mul_div_cancel_right₀ _ ha]
    dsimp only [M, N, P]
    rw [cancel _ _ hm'.ne', cancel _ _ hn'.ne', cancel _ _ hp'.ne',
      ← add_mul, ← add_mul, hs, one_mul, div_self ht.ne']
  have ha := weighted3 m n p (by omega) (div_nonneg hx hM.le) (div_nonneg hy hN.le)
    (div_nonneg hz hP.le)
  change (x / M) ^ m * (y / N) ^ n * (z / P) ^ p ≤
    ((↑m * (x / M) + ↑n * (y / N) + ↑p * (z / P)) / t) ^ (m + n + p) at ha
  rw [hmean, one_pow] at ha
  simp only [div_pow, div_mul_div_comm] at ha
  exact (div_le_one (by positivity)).mp ha

private theorem segment_bound (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hs : x + y = 1) :
    x ^ m * y ^ n ≤
      ((m : ℝ) / (↑(m + n) : ℝ)) ^ m * ((n : ℝ) / (↑(m + n) : ℝ)) ^ n := by
  let t : ℝ := ↑(m + n)
  let M : ℝ := ↑m / t
  let N : ℝ := ↑n / t
  have ht : 0 < t := by dsimp [t]; positivity
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hM : 0 < M := div_pos hm' ht
  have hN : 0 < N := div_pos hn' ht
  have hmean : (↑m * (x / M) + ↑n * (y / N)) / t = 1 := by
    have cancel (a u : ℝ) (ha : a ≠ 0) : a * (u / (a / t)) = u * t := by
      rw [div_div_eq_mul_div, ← mul_div_assoc, mul_comm a (u * t),
        mul_div_cancel_right₀ _ ha]
    dsimp only [M, N]
    rw [cancel _ _ hm'.ne', cancel _ _ hn'.ne', ← add_mul, hs, one_mul, div_self ht.ne']
  have ha := weighted3 m n 0 (by omega) (div_nonneg hx hM.le) (div_nonneg hy hN.le)
    (show (0 : ℝ) ≤ 1 by norm_num)
  simp only [Nat.cast_zero, add_zero, pow_zero, mul_one] at ha
  change (x / M) ^ m * (y / N) ^ n ≤
    ((↑m * (x / M) + ↑n * (y / N)) / t) ^ (m + n) at ha
  rw [hmean, one_pow] at ha
  simp only [div_pow, div_mul_div_comm] at ha
  exact (div_le_one (by positivity)).mp ha

private theorem kernel_upper {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) : kernel x y ≤ q := by
  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy0, hy1⟩
  have hu : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  have hv : 0 ≤ 1 - y := sub_nonneg.mpr hy1
  let d := 1 - x * y
  have hd : 0 ≤ d := sub_nonneg.mpr (mul_le_one₀ hx1 hy0 hy1)
  rcases hd.eq_or_lt with he | hd
  · have hd0 : 1 - x * y = 0 := he.symm
    rw [kernel, hd0, zero_pow (by decide : 13 ≠ 0), div_zero]
    unfold q
    positivity
  -- These three fractions are the normalized odds-coordinate terms.
  let a := x * (1 - y) / d
  let b := y * (1 - x) / d
  let c := (1 - x) * (1 - y) / d
  have ha : 0 ≤ a := div_nonneg (mul_nonneg hx0 hv) hd.le
  have hb : 0 ≤ b := div_nonneg (mul_nonneg hy0 hu) hd.le
  have hc : 0 ≤ c := div_nonneg (mul_nonneg hu hv) hd.le
  have hs : a + b + c = 1 := by
    dsimp only [a, b, c]
    rw [← add_div, ← add_div]
    apply (div_eq_iff hd.ne').2
    dsimp [d]
    ring
  have h₁ : x ^ 7 * (1 - x) ^ 4 ≤ (7 / 11 : ℝ) ^ 7 * (4 / 11 : ℝ) ^ 4 := by
    have h := segment_bound 7 4 (by decide) (by decide) hx0 hu (by ring)
    norm_num at h ⊢
    exact h
  have h₂ : y ^ 9 * (1 - y) ^ 6 ≤ (3 / 5 : ℝ) ^ 9 * (2 / 5 : ℝ) ^ 6 := by
    have h := segment_bound 9 6 (by decide) (by decide) hy0 hv (by ring)
    norm_num at h ⊢
    exact h
  have h₃ : a ^ 5 * b ^ 5 * c ^ 3 ≤
      (5 / 13 : ℝ) ^ 5 * (5 / 13 : ℝ) ^ 5 * (3 / 13 : ℝ) ^ 3 := by
    have h := simplex_bound 5 5 3 (by decide) (by decide) (by decide) ha hb hc hs
    norm_num at h ⊢
    exact h
  calc
    kernel x y = (x ^ 7 * (1 - x) ^ 4) * (y ^ 9 * (1 - y) ^ 6) *
        (a ^ 5 * b ^ 5 * c ^ 3) := by
      dsimp only [kernel, a, b, c, d]
      generalize 1 - x = u, 1 - y = v, 1 - x * y = w
      simp only [div_eq_mul_inv, mul_pow, ← inv_pow]
      ring
    _ ≤ _ := mul_le_mul (mul_le_mul h₁ h₂ (by positivity) (by positivity)) h₃
      (by positivity) (by positivity)

private theorem denominator_nonneg {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) : 0 ≤ 1 - x * y :=
  sub_nonneg.mpr (mul_le_one₀ hx.2 hy.1 hy.2)

private theorem kernel_nonneg {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) : 0 ≤ kernel x y := by
  have hx0 : 0 ≤ x := hx.1
  have hy0 : 0 ≤ y := hy.1
  have hu : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
  have hv : 0 ≤ 1 - y := sub_nonneg.mpr hy.2
  have hd := denominator_nonneg hx hy
  unfold kernel
  positivity

private theorem kernel_div_upper {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) : kernel x y / (1 - x * y) ≤ 1 := by
  let d := 1 - x * y
  have hd : 0 ≤ d := denominator_nonneg hx hy
  rcases hd.eq_or_lt with hzero | hd
  · change kernel x y / d ≤ 1
    rw [← hzero, div_zero]
    norm_num
  have hu : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
  have hv : 0 ≤ 1 - y := sub_nonneg.mpr hy.2
  have hx0 : 0 ≤ x := hx.1
  have hy0 : 0 ≤ y := hy.1
  -- Use seven powers of each endpoint factor to control the denominator.
  have hud : 1 - x ≤ d := sub_le_sub_left (mul_le_of_le_one_right hx0 hy.2) 1
  have hvd : 1 - y ≤ d := sub_le_sub_left (mul_le_of_le_one_left hy0 hx.2) 1
  have h₁ : x ^ 12 * (1 - x) ^ 12 ≤ (1 - x) ^ 7 := calc
    _ ≤ 1 * (1 - x) ^ 12 :=
      mul_le_mul_of_nonneg_right (pow_le_one₀ hx0 hx.2) (pow_nonneg hu _)
    _ ≤ _ := by
      rw [one_mul]
      exact pow_le_pow_of_le_one hu (by linarith) (by decide)
  have h₂ : y ^ 14 * (1 - y) ^ 14 ≤ (1 - y) ^ 7 := calc
    _ ≤ 1 * (1 - y) ^ 14 :=
      mul_le_mul_of_nonneg_right (pow_le_one₀ hy0 hy.2) (pow_nonneg hv _)
    _ ≤ _ := by
      rw [one_mul]
      exact pow_le_pow_of_le_one hv (by linarith) (by decide)
  change (x ^ 12 * (1 - x) ^ 12 * y ^ 14 * (1 - y) ^ 14) / d ^ 13 / d ≤ 1
  rw [div_div, ← pow_succ d 13]
  apply (div_le_one (pow_pos hd _)).2
  calc
    _ = (x ^ 12 * (1 - x) ^ 12) * (y ^ 14 * (1 - y) ^ 14) := by ac_rfl
    _ ≤ (1 - x) ^ 7 * (1 - y) ^ 7 := mul_le_mul h₁ h₂ (by positivity) (by positivity)
    _ ≤ d ^ 7 * d ^ 7 :=
      mul_le_mul (pow_le_pow_left₀ hu hud _) (pow_le_pow_left₀ hv hvd _)
        (pow_nonneg hv _) (pow_nonneg hd.le _)
    _ = _ := by rw [← pow_add]

private theorem small_subset :
    Icc (3 / 5 : ℝ) (13 / 20) ⊆ Icc (0 : ℝ) 1 :=
  Icc_subset_Icc (by norm_num) (by norm_num)

private theorem kernel_lower {x y : ℝ} (hx : x ∈ Icc (3 / 5 : ℝ) (13 / 20))
    (hy : y ∈ Icc (3 / 5 : ℝ) (13 / 20)) : r ≤ kernel x y := by
  have hx0 : (3 / 5 : ℝ) ≤ x := hx.1
  have hy0 : (3 / 5 : ℝ) ≤ y := hy.1
  have hx1 : x ≤ (13 / 20 : ℝ) := hx.2
  have hy1 : y ≤ (13 / 20 : ℝ) := hy.2
  have hx' : (3 / 5 : ℝ) * (7 / 20) ≤ x * (1 - x) :=
    mul_le_mul hx0 (by linarith) (by norm_num) (by linarith)
  have hy' : (3 / 5 : ℝ) * (7 / 20) ≤ y * (1 - y) :=
    mul_le_mul hy0 (by linarith) (by norm_num) (by linarith)
  have hd : 0 < 1 - x * y := by
    have hm : x * y ≤ (13 / 20 : ℝ) * (13 / 20) :=
      mul_le_mul hx1 hy1 (by linarith) (by norm_num)
    linarith
  have hd' : 1 - x * y ≤ (16 / 25 : ℝ) := by
    have hm : (3 / 5 : ℝ) * (3 / 5) ≤ x * y :=
      mul_le_mul hx0 hy0 (by norm_num) (by linarith)
    linarith
  have hn : ((3 / 5 : ℝ) * (7 / 20)) ^ 26 ≤ (x * (1 - x)) ^ 12 * (y * (1 - y)) ^ 14 := by
    rw [show (26 : ℕ) = 12 + 14 by decide, pow_add]
    exact mul_le_mul (pow_le_pow_left₀ (by norm_num) hx' _)
      (pow_le_pow_left₀ (by norm_num) hy' _) (by norm_num) (by positivity)
  unfold r kernel
  calc
    _ ≤ ((3 / 5 : ℝ) * (7 / 20)) ^ 26 / (1 - x * y) ^ 13 :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hd _)
        (pow_le_pow_left₀ hd.le hd' _)
    _ ≤ _ := div_le_div_of_nonneg_right (by
      simpa only [mul_pow, mul_assoc] using hn) (pow_nonneg hd.le _)

private def integrand (k : ℕ) (x y : ℝ) : ℝ :=
  kernel x y ^ k / (1 - x * y)

private theorem integrand_measurable {α : Type*} [MeasurableSpace α]
    (k : ℕ) {x y : α → ℝ} (hx : Measurable x) (hy : Measurable y) :
    Measurable (fun t => integrand k (x t) (y t)) := by
  have hu : Measurable (fun t => 1 - x t) := measurable_const.sub hx
  have hv : Measurable (fun t => 1 - y t) := measurable_const.sub hy
  have hd : Measurable (fun t => 1 - x t * y t) := measurable_const.sub (hx.mul hy)
  unfold integrand kernel
  exact (((((hx.pow_const (12 : ℕ)).mul (hu.pow_const (12 : ℕ))).mul
    (hy.pow_const (14 : ℕ))).mul (hv.pow_const (14 : ℕ))).div
    (hd.pow_const (13 : ℕ))).pow_const k |>.div hd

private theorem integrand_nonneg (k : ℕ) {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) : 0 ≤ integrand k x y :=
  div_nonneg (pow_nonneg (kernel_nonneg hx hy) _) (denominator_nonneg hx hy)

private theorem integrand_upper (n : ℕ) {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) : integrand (n + 1) x y ≤ q ^ n := by
  have hK := kernel_nonneg hx hy
  have hq : 0 ≤ q := hK.trans (kernel_upper hx hy)
  unfold integrand
  rw [pow_succ, mul_div_assoc]
  calc
    _ ≤ q ^ n * 1 :=
      mul_le_mul (pow_le_pow_left₀ hK (kernel_upper hx hy) _) (kernel_div_upper hx hy)
        (div_nonneg hK (denominator_nonneg hx hy)) (pow_nonneg hq _)
    _ = _ := mul_one _

private theorem integrand_lower (k : ℕ) {x y : ℝ}
    (hx : x ∈ Icc (3 / 5 : ℝ) (13 / 20)) (hy : y ∈ Icc (3 / 5 : ℝ) (13 / 20)) :
    r ^ k ≤ integrand k x y := by
  have hx' := small_subset hx
  have hy' := small_subset hy
  have hx1 : x ≤ (13 / 20 : ℝ) := hx.2
  have hy1 : y ≤ (13 / 20 : ℝ) := hy.2
  have hy0 : 0 ≤ y := hy'.1
  have hxy : x * y ≤ (13 / 20 : ℝ) * (13 / 20) :=
    mul_le_mul hx1 hy1 hy0 (by norm_num)
  have hd : 0 < 1 - x * y := by linarith
  have hd' : 1 - x * y ≤ 1 := sub_le_self _ (mul_nonneg hx'.1 hy'.1)
  exact (pow_le_pow_left₀ (by unfold r; positivity) (kernel_lower hx hy) k).trans
    (le_div_self (pow_nonneg (kernel_nonneg hx' hy') _) hd hd')

private theorem bounded_integral {f : ℝ → ℝ} {C : ℝ} (hf : Measurable f)
    (h₀ : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x)
    (h₁ : ∀ x ∈ Icc (0 : ℝ) 1, f x ≤ C) :
    IntervalIntegrable f volume 0 1 ∧ 0 ≤ (∫ x in (0 : ℝ)..1, f x) ∧
      (∫ x in (0 : ℝ)..1, f x) ≤ C := by
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  have hC : IntervalIntegrable (fun _ : ℝ => C) volume 0 1 := intervalIntegrable_const
  have hfi : IntervalIntegrable f volume 0 1 := by
    apply hC.mono_fun' hf.aestronglyMeasurable
    rw [uIoc_of_le h01]
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with x hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (h₀ x hx')] using h₁ x hx'
  refine ⟨hfi, intervalIntegral.integral_nonneg h01 h₀, ?_⟩
  calc
    _ ≤ ∫ _ in (0 : ℝ)..1, C := intervalIntegral.integral_mono_on h01 hfi hC h₁
    _ = C := by simp

private theorem lower_integral {f : ℝ → ℝ} {L : ℝ}
    (hf : IntervalIntegrable f volume 0 1)
    (h₀ : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x)
    (hL : ∀ x ∈ Icc (3 / 5 : ℝ) (13 / 20), L ≤ f x) :
    L / 20 ≤ ∫ x in (0 : ℝ)..1, f x := by
  have hab : (3 / 5 : ℝ) ≤ 13 / 20 := by norm_num
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  have ha : (0 : ℝ) ≤ 3 / 5 := by norm_num
  have hb : (13 / 20 : ℝ) ≤ 1 := by norm_num
  have hsub : IntervalIntegrable f volume (3 / 5) (13 / 20) := by
    apply hf.mono_set'
    rw [uIoc_of_le hab, uIoc_of_le h01]
    exact Ioc_subset_Ioc ha hb
  have hL' : IntervalIntegrable (fun _ : ℝ => L) volume (3 / 5) (13 / 20) :=
    intervalIntegrable_const
  calc
    L / 20 = ∫ _ in (3 / 5 : ℝ)..(13 / 20), L := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    _ ≤ ∫ x in (3 / 5 : ℝ)..(13 / 20), f x :=
      intervalIntegral.integral_mono_on hab hL' hsub hL
    _ ≤ ∫ x in (0 : ℝ)..1, f x := by
      refine intervalIntegral.integral_mono_interval ha hab hb ?_ hf
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with x hx
      exact h₀ x (Ioc_subset_Icc_self hx)

private def integralValue (k : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, integrand k x y

private theorem integral_bounds (n : ℕ) :
    r ^ (n + 1) / 400 ≤ integralValue (n + 1) ∧ integralValue (n + 1) ≤ q ^ n := by
  let f := integrand (n + 1)
  let F : ℝ → ℝ := fun x => ∫ y in (0 : ℝ)..1, f x y
  -- A fixed restricted measure makes the inner integral measurable in x.
  have hF : Measurable F := by
    have hf : Measurable (fun p : ℝ × ℝ => f p.1 p.2) :=
      integrand_measurable (n + 1) measurable_fst measurable_snd
    have hsm := hf.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc (0 : ℝ) 1))
    simpa only [F, intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
      using hsm.measurable
  have hinner (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :=
    bounded_integral (integrand_measurable (n + 1) (measurable_const (a := x)) measurable_id)
      (fun y hy => integrand_nonneg (n + 1) hx hy)
      (fun y hy => integrand_upper n hx hy)
  have houter := bounded_integral hF
    (fun x hx => (hinner x hx).2.1)
    (fun x hx => (hinner x hx).2.2)
  refine ⟨?_, houter.2.2⟩
  change r ^ (n + 1) / 400 ≤ ∫ x in (0 : ℝ)..1, F x
  calc
    _ = (r ^ (n + 1) / 20) / 20 := by ring
    _ ≤ _ := lower_integral houter.1 (fun x hx => (hinner x hx).2.1) (fun x hx =>
      lower_integral (hinner x (small_subset hx)).1
        (fun y hy => integrand_nonneg (n + 1) (small_subset hx) hy)
        (fun y hy => integrand_lower (n + 1) hx hy))

private theorem eventual_estimates :
    ∀ᶠ b : ℕ in atTop,
      2 ≤ integralValue (Nat.log 32768 b) * (b : ℝ) ^ 4 ∧
      2 * integralValue (Nat.log 32768 b) * (b : ℝ) ^ 3 ≤ 1 := by
  let B : ℝ := 32768
  have hB : 0 < B := by norm_num [B]
  have hq : 0 < q := by unfold q; positivity
  have hr : 0 < r := by unfold r; positivity
  have hqB : q * B ^ 3 < 1 := by norm_num [q, B]
  have hrB : 1 < r * B ^ 4 := by norm_num [r, B]
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (mul_nonneg hq.le (by positivity)) hqB
  have hu : ∀ᶠ n : ℕ in atTop, (q * B ^ 3) ^ n < 1 / (2 * B ^ 6) :=
    (tendsto_order.1 hlim).2 _ (by positivity)
  have hl : ∀ᶠ k : ℕ in atTop, (800 : ℝ) ≤ (r * B ^ 4) ^ k :=
    (tendsto_pow_atTop_atTop_of_one_lt hrB).eventually_ge_atTop _
  obtain ⟨U, hU⟩ := eventually_atTop.1 hu
  obtain ⟨L, hL⟩ := eventually_atTop.1 hl
  filter_upwards [eventually_ge_atTop ((32768 : ℕ) ^ max (U + 1) L)] with b hb
  let k := Nat.log 32768 b
  let n := k - 1
  have hk₀ : max (U + 1) L ≤ k := Nat.le_log_of_pow_le (by decide) hb
  have hkU : U + 1 ≤ k := (le_max_left _ _).trans hk₀
  have hkL : L ≤ k := (le_max_right _ _).trans hk₀
  have hk : k = n + 1 := by dsimp [n]; omega
  have hnU : U ≤ n := by dsimp [n]; omega
  have hb0 : b ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by positivity) hb)
  have hlo : B ^ k ≤ (b : ℝ) := by
    dsimp only [B, k]
    exact_mod_cast Nat.pow_log_le_self 32768 hb0
  have hhi : (b : ℝ) ≤ B ^ (k + 1) := by
    dsimp only [B, k]
    exact_mod_cast (Nat.lt_pow_succ_log_self (by decide : 1 < 32768) b).le
  obtain ⟨hi₀, hi₁⟩ : r ^ k / 400 ≤ integralValue k ∧ integralValue k ≤ q ^ n := by
    simpa only [← hk] using integral_bounds n
  have hi : 0 ≤ integralValue k := (by positivity : 0 ≤ r ^ k / 400).trans hi₀
  change 2 ≤ integralValue k * (b : ℝ) ^ 4 ∧
    2 * integralValue k * (b : ℝ) ^ 3 ≤ 1
  constructor
  · calc
      (2 : ℝ) ≤ (r * B ^ 4) ^ k / 400 := by
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 400)).2
        rw [show (2 : ℝ) * 400 = 800 by norm_num]
        exact hL k hkL
      _ = (r ^ k / 400) * (B ^ k) ^ 4 := by
        rw [mul_pow, ← pow_mul B 4 k, ← pow_mul B k 4, Nat.mul_comm 4 k]
        ring
      _ ≤ _ :=
        mul_le_mul hi₀ (pow_le_pow_left₀ (pow_nonneg hB.le _) hlo _)
          (by positivity) hi
  · calc
      _ ≤ (2 * q ^ n) * (B ^ (k + 1)) ^ 3 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hi₁ (by norm_num))
          (pow_le_pow_left₀ (Nat.cast_nonneg b) hhi _) (by positivity) (by positivity)
      _ = (2 * B ^ 6) * (q * B ^ 3) ^ n := by
        rw [hk, show n + 1 + 1 = n + 2 by omega, pow_add B n 2]
        simp only [mul_pow, ← pow_mul]
        rw [Nat.mul_comm n 3]
        ring
      _ ≤ 1 := by
        have h := mul_le_mul_of_nonneg_left (hU n hnU).le
          (show 0 ≤ 2 * B ^ 6 by positivity)
        exact h.trans_eq (mul_one_div_cancel (ne_of_gt (by positivity)))

end Constant7aH2Proof

theorem OMA.solution : OMA.R_Constant7a_c7a_lt_14_797075_R1.H2 :=
  Constant7aH2Proof.eventual_estimates
