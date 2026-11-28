import OMAStatements.S_oeis_a208548
import Mathlib

/-!
The explicit Chebyshev estimates below are reused from the merged A119659 proof
(proofs/oeis-a119659.lean, commit f3d7e65ae).
Source: PrimeNumberTheoremAnd (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
PrimeNumberTheoremAnd/IEANTN/Chebyshev.lean at commit
471f10c8164d59ed782680c5cd5d884e632e43c9, Apache-2.0.
Adaptation: remove blueprint metadata and external numerical log table imports,
and use only Mathlib's certified log estimates.
-/

namespace Chebyshev

open Real Finsupp Finset
open ArithmeticFunction hiding log

private lemma Ioc_eq_Icc (n : ℕ) : Ioc 0 n = Icc 1 n := by
  ext k
  simp
  omega

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
  have h3 : ∀ t ∈ interior (Set.Ici 1), DifferentiableWithinAt ℝ (_root_.id * log - _root_.id) (interior (Set.Ici 1)) t := by
    intro t ht
    simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at ht
    have hd : DifferentiableAt ℝ (_root_.id * log - _root_.id) t := by
      fun_prop (disch := positivity)
    exact hd.differentiableWithinAt
  have h4 : ∀ t ∈ interior (Set.Ici 1), 0 ≤ deriv (fun t ↦ t * log t - t) t := by
    intro t ht
    simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at ht
    have : DifferentiableAt ℝ (fun t ↦ t * log t) t := by fun_prop ( disch := positivity )
    have hderiv : deriv (fun t ↦ t * log t - t) t = log t := by
      simp [show (fun t ↦ t * log t - t) = (fun t ↦ t * log t) - _root_.id by rfl,
        deriv_sub this differentiableAt_id, deriv_mul_log (by linarith)]
    exact hderiv ▸ log_nonneg (le_of_lt ht)
  have h5 : ContinuousOn (fun t ↦ t * log t - t) (Set.Ici 1) := by
    intro t ht
    have ht' : (1 : ℝ) ≤ t := ht
    have hd : DifferentiableAt ℝ (fun u ↦ u * log u - u) t := by
      fun_prop (disch := positivity)
    exact hd.continuousAt.continuousWithinAt
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
  have sum_shift : ∑ i ∈ Ico 1 ⌊x⌋₊, log (i + 1 : ℕ) = log ⌊x⌋₊ + ∑ i ∈ Ico 1 ⌊x⌋₊, log i := by
    exact h1 ⌊x⌋₊ hone_le_floor
  have int_le_T : ∫ t in (1 : ℕ)..(⌊x⌋₊ : ℕ), log t ≤ log ⌊x⌋₊ + ∑ n ∈ Ico 1 ⌊x⌋₊, log n := by
    linarith [mono_log.integral_le_sum_Ico hone_le_floor]
  have int_eq : ∫ t in (1 : ℕ)..(⌊x⌋₊ : ℕ), log t = ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by simp
  have h2 : ∫ t in (⌊x⌋₊ : ℝ)..x, log t ≤ (x - ⌊x⌋₊) * log x := by
    calc ∫ t in (⌊x⌋₊ : ℝ)..x, log t
      ≤ ∫ _ in (⌊x⌋₊ : ℝ)..x, log x := (intervalIntegral.integral_mono_on (Nat.floor_le <| by linarith) intervalIntegral.intervalIntegrable_log'
            intervalIntegrable_const fun t ht ↦ log_le_log (lt_of_lt_of_le (by positivity) ht.1) ht.2)
      _ = (x - ⌊x⌋₊) * log x := by simp
  have target_le_int : x * log x - x + 1 - log x ≤ ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by
    calc x * log x - x + 1 - log x
        ≤ (x * log x - x + 1) - (x - ⌊x⌋₊) * log x := by nlinarith [log_nonneg hx, Nat.lt_floor_add_one x]
      _ ≤ (x * log x - x + 1) - ∫ t in (⌊x⌋₊ : ℝ)..x, log t := by grind
      _ = ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by grind [integral_log]
  linarith

theorem T.eq_sum_Lambda (x : ℝ) : T x = ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * ⌊x / n⌋₊ := by
  unfold T
  simp_rw [← log_apply, ← vonMangoldt_mul_zeta]
  rw [← Ioc_eq_Icc, sum_Ioc_mul_zeta_eq_sum]
  simp [Nat.floor_div_natCast]

noncomputable def E (ν : ℕ →₀ ℝ) (x : ℝ) : ℝ := ν.sum (fun m w ↦ w * ⌊ x / m ⌋₊)

theorem T.weighted_eq_sum (ν : ℕ →₀ ℝ) (x : ℝ) : ν.sum (fun m w ↦ w * T (x/m)) = ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * E ν (x/n) := by
  simp_rw [T.eq_sum_Lambda, E, Finsupp.mul_sum]
  rw [← sum_finsetSum_comm]
  apply Finsupp.sum_congr fun y hy ↦ ?_
  rw [Finset.mul_sum]
  by_cases hy : y = 0
  · simp [hy]
  have one_le_y : 1 ≤ (y : ℝ) := by grind [Nat.one_le_cast]
  by_cases hx : x < 1
  · simp [hx, show x / y < 1 from div_lt_one (by linarith)|>.mpr (by linarith)]
  apply sum_subset_zero_on_sdiff
  · apply Icc_subset_Icc_right
    gcongr
    exact div_le_self (by linarith) one_le_y
  · intro t ht
    simp only [mem_sdiff, mem_Icc, not_and, not_le] at ht
    simp only [mul_eq_zero, Nat.cast_eq_zero, Nat.floor_eq_zero]
    right
    right
    apply div_lt_one (by linarith)|>.mpr
    have := ht.2 ht.1.1
    apply div_lt_iff₀ (by simp; grind)|>.mpr
    rw [Nat.floor_lt <| div_nonneg (by linarith) (by linarith)] at this
    have := div_lt_iff₀ (by linarith)|>.mp this
    rwa [mul_comm] at this
  · grind

open Finsupp in
noncomputable def ν : ℕ →₀ ℝ := single 1 1 - single 2 1 - single 3 1 - single 5 1 + single 30 1

/-- The support of `ν` is `{1, 2, 3, 5, 30}`. Used whenever we need to unfold `ν.sum`. -/
private lemma ν_support : ν.support = {1, 2, 3, 5, 30} := by
  norm_num [ν, Finset.ext_iff]; grind

/-- Unfold `ν.sum (fun m w ↦ w * f m)` into its five-term expansion.
This avoids repeating the `sum_add_index` / `sum_sub_index` chain every time
we need to compute a `ν`-weighted sum. -/
private lemma ν_sum_mul (f : ℕ → ℝ) :
    ν.sum (fun m w ↦ w * f m) = f 1 - f 2 - f 3 - f 5 + f 30 := by
  rw [ν, sum_add_index (by simp) (by intros; ring)]
  grind only [sum_single_index, sum_sub_index]

/-- Unfold `E ν y` into an explicit expression in terms of floors of `y / k`.
This is the key formula repeatedly used to analyse `E ν`. -/
private lemma E_nu_expand (y : ℝ) :
    E ν y = ⌊y⌋₊ - ⌊y / 2⌋₊ - ⌊y / 3⌋₊ - ⌊y / 5⌋₊ + ⌊y / 30⌋₊ := by
  rw [E, ν, sum_add_index' (by grind) (by grind)]
  grind [sum_single_index, sum_sub_index]

/-- The classical sandwich `k * ⌊y/k⌋₊ ≤ ⌊y⌋₊ < k * ⌊y/k⌋₊ + k` for `k ≥ 1` and `y ≥ 0`. -/
private lemma floor_div_bounds {y : ℝ} (hy : 0 ≤ y) {k : ℕ} (hk : 1 ≤ k) :
    k * ⌊y / k⌋₊ ≤ ⌊y⌋₊ ∧ ⌊y⌋₊ < k * ⌊y / k⌋₊ + k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hdivnn : 0 ≤ y / k := div_nonneg hy hk'.le
  refine ⟨Nat.le_floor ?_, ?_⟩
  · push_cast
    have := Nat.floor_le hdivnn
    calc ((k : ℝ) * ⌊y / k⌋₊) = k * (y / k) - k * (y / k - ⌊y / k⌋₊) := by ring
      _ ≤ k * (y / k) := by nlinarith [Nat.floor_le hdivnn]
      _ = y := mul_div_cancel₀ _ hk'.ne'
  · have hlt : y / k < ⌊y / k⌋₊ + 1 := Nat.lt_floor_add_one (y / k)
    have hy_lt : y < (k : ℝ) * (⌊y / k⌋₊ + 1) := by linarith [(div_lt_iff₀ hk').mp hlt]
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
  have h (k : ℝ) : (x + 30) / k = x / k + (30 / k) := by ring
  simp_rw [E_nu_expand, h 2, h 3, h 5, h 30]
  norm_num
  repeat rw [Nat.floor_add_ofNat (by positivity)]
  rw [Nat.floor_add_one (by positivity)]
  grind

theorem E_nu_bound (x : ℝ) (hx : x ≥ 0) : 0 ≤ E ν x ∧ E ν x ≤ 1 := by
  have : ∀ y, 0 ≤ y → y < 30 → 0 ≤ E ν y ∧ E ν y ≤ 1 := fun y hy0 hy30 ↦ by
    simp only [E_nu_expand, Nat.floor_eq_zero.mpr (by linarith : y / 30 < 1), Nat.cast_zero, add_zero]
    have h2 := floor_div_bounds hy0 (k := 2) (by norm_num)
    have h3 := floor_div_bounds hy0 (k := 3) (by norm_num)
    have h5 := floor_div_bounds hy0 (k := 5) (by norm_num)
    push_cast at h2 h3 h5
    have hfy : ⌊y⌋₊ < 30 := Nat.floor_lt' (by norm_num) |>.mpr (by exact_mod_cast hy30)
    have hlb : ⌊y/2⌋₊ + ⌊y/3⌋₊ + ⌊y/5⌋₊ ≤ ⌊y⌋₊ := by omega
    have hub : ⌊y⌋₊ ≤ ⌊y/2⌋₊ + ⌊y/3⌋₊ + ⌊y/5⌋₊ + 1 := by omega
    have hlb' : ((⌊y/2⌋₊ + ⌊y/3⌋₊ + ⌊y/5⌋₊ : ℕ) : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hlb
    have hub' : ((⌊y⌋₊ : ℕ) : ℝ) ≤ ((⌊y/2⌋₊ + ⌊y/3⌋₊ + ⌊y/5⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hub
    push_cast at hlb' hub'
    refine ⟨by linarith, by linarith⟩
  let y := x - ⌊x / 30⌋₊ * 30
  have hy : 0 ≤ y ∧ y < 30 := ⟨by linarith [Nat.floor_le (by positivity : 0 ≤ x/30)], by
    linarith [Nat.lt_floor_add_one (x/30)]⟩
  have hxy : E ν x = E ν y := by
    have : x = y + ⌊x/30⌋₊ * 30 := by ring
    rw [this]; induction ⌊x/30⌋₊ with
    | zero => simp
    | succ n ih => simp [add_mul, ← add_assoc, E_nu_period _ (by linarith : y + n * 30 ≥ 0), ih]
  exact hxy ▸ this y hy.1 hy.2

noncomputable def U (x : ℝ) : ℝ := ν.sum (fun m w ↦ w * T (x/m))

theorem psi_ge_weighted (x : ℝ) (hx : x > 0) : ψ x ≥ U x := by
  unfold U psi
  rw [T.weighted_eq_sum, ← Ioc_eq_Icc]
  gcongr with i
  have := E_nu_bound (x / i) (div_nonneg hx.le (by simp))
  grw [this.2, mul_one]

theorem psi_diff_le_weighted (x : ℝ) (hx : x > 0) : ψ x - ψ (x / 6) ≤ U x := by
  unfold U psi
  rw [T.weighted_eq_sum, ← Ioc_eq_Icc]
  have subset : Ioc 0 ⌊x / 6⌋₊ ⊆ Ioc 0 ⌊x⌋₊ := by
    apply Ioc_subset_Ioc_right
    gcongr
    exact div_le_self hx.le (by norm_num)
  rw [← sum_sdiff_eq_sub subset, ← sum_sdiff subset]
  refine le_add_of_le_of_nonneg (sum_le_sum fun n hn ↦ ?_) (sum_nonneg fun n hn ↦ mul_nonneg vonMangoldt_nonneg ?_)
  · rw [E_nu_eq_one, mul_one]
    simp_all only [gt_iff_lt, Finset.mem_sdiff, Finset.mem_Ioc, not_and, not_le, Set.mem_Ico]
    refine ⟨one_le_div (by simp; grind)|>.mpr <| Nat.le_floor_iff hx.le |>.mp hn.1.2, ?_⟩
    have := hn.2 hn.1.1
    apply div_lt_iff₀ (by simp; grind)|>.mpr
    rw [Nat.floor_lt <| div_nonneg (by linarith) (by linarith)] at this
    have := div_lt_iff₀ (by linarith)|>.mp this
    rwa [mul_comm] at this
  · exact E_nu_bound _ (div_nonneg hx.le (by simp))|>.1

noncomputable def a : ℝ := - ν.sum (fun m w ↦ w * log m / m)

lemma a_simpl : a = (7/15) * Real.log 2 + (3/10) * Real.log 3 + (1/6) * Real.log 5 := by
  norm_num [a, Finsupp.sum, single_apply, ν_support]
  norm_num [Finset.sum, ν]
  grind [show (30 : ℝ) = 2 * 3 * 5 by ring, log_mul, log_mul]

theorem a_bound : a ∈ Set.Icc 0.92129 0.92130 := by
  norm_num [Chebyshev.a_simpl]
  constructor <;> nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9, Real.log_three_gt_d9, Real.log_three_lt_d9, Real.log_five_gt_d9, Real.log_five_lt_d9]

noncomputable def e (x : ℝ) : ℝ :=
  (T x - (x * log x - x + 1))

lemma U_bound.lemma_1 (x : ℝ) : T x = x * log x - x + 1 + (e x) := by
  unfold e
  ring

lemma U_bound.lemma_2 (x : ℝ) (hx : 1 ≤ x) : |e x| ≤ log x := by
  rw [abs_le]
  unfold e
  constructor <;> linarith [T.ge x hx, T.le x hx]

lemma U_bound.lemma_3 (x : ℝ) :
    U x = ν.sum (fun m w ↦ w * ((x / m) * (log (x / m))))
          - ν.sum (fun m w ↦ w * (x / m))
          + ν.sum (fun _m w ↦ w)
          + ν.sum (fun m w ↦ w * e (x / m)) := by
  simp [U, Finsupp.sum, U_bound.lemma_1, sub_eq_add_neg, add_mul, mul_comm, sum_add_distrib]

lemma U_bound.lemma_4 (x : ℝ) (hx : 0 < x) :
    ν.sum (fun m w ↦ w * ((x / m) * log (x / m))) = a * x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have ha : a = -(log 1 / 1 - log 2 / 2 - log 3 / 3 - log 5 / 5 + log 30 / 30) := by
    simp_rw [a, mul_div_assoc]; rw [ν_sum_mul (fun m ↦ log m / m)]; push_cast; rfl
  rw [ν_sum_mul (fun m ↦ (x / m) * log (x / m)), ha]
  simp [Real.log_div hx0]
  ring

lemma U_bound.lemma_5 (x : ℝ) : ν.sum (fun m w ↦ w * (x / m)) = 0 := by
  rw [ν_sum_mul (fun m ↦ x / m)]; push_cast; ring

lemma U_bound.lemma_6 : ν.sum (fun _ w ↦ w) = (-1 : ℝ) := by
  have := ν_sum_mul (fun _ ↦ (1 : ℝ)); simp at this; linarith

lemma Finsupp.abs_sum_le (A : Type*) (ν : A →₀ ℝ) (g : A → ℝ → ℝ) : |ν.sum g| ≤ ν.sum |g| := by
  simp_rw [Finsupp.sum.eq_1]
  exact abs_sum_le_sum_abs (fun i ↦ g i (ν i)) ν.support

theorem U_bound (x : ℝ) (hx : 30 ≤ x) : |U x - a * x| ≤ 5 * log x - 5 := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  rw [U_bound.lemma_3, U_bound.lemma_4 x hxpos]
  ring_nf
  have hlin : ν.sum (fun m w ↦ x * w * (↑m)⁻¹) = 0 :=
    by simpa [div_eq_mul_inv, mul_assoc, mul_left_comm] using U_bound.lemma_5 x
  rw [hlin]; ring_nf; rw [U_bound.lemma_6]
  grw [abs_add_le, Finsupp.abs_sum_le]
  norm_num
  have hsupp_eq : ν.support = {1, 2, 3, 5, 30} := ν_support
  have hmem_of_supp : ∀ i ∈ ν.support, 0 < i ∧ i ≤ 30 := fun i hi ↦ by
    have : i ∈ ({1, 2, 3, 5, 30} : Finset ℕ) := hsupp_eq ▸ hi
    simp only [mem_insert, mem_singleton] at this
    constructor <;> omega
  have h : ν.sum |fun m w ↦ w * e (x * (↑m)⁻¹)| ≤ ν.sum (fun m w ↦ |w| * log (x * (↑m)⁻¹)) := by
    apply Finsupp.sum_le_sum
    intro i hi
    simp only [Pi.abs_apply, abs_mul]
    obtain ⟨hi_pos, hi_le⟩ := hmem_of_supp i hi
    have hxi : 1 ≤ x * (↑i)⁻¹ := by
      rw [le_mul_inv_iff₀ (by exact_mod_cast hi_pos)]
      linarith [show (i : ℝ) ≤ 30 from by exact_mod_cast hi_le]
    gcongr; exact U_bound.lemma_2 _ hxi
  grw [h]
  have hlog_split : ν.sum (fun m w ↦ |w| * log (x * (m : ℝ)⁻¹)) =
      log x * ν.sum (fun m w ↦ |w|) - ν.sum (fun m w ↦ |w| * log (↑m : ℝ)) := by
    simp only [Finsupp.sum]
    conv_rhs => rw [Finset.mul_sum, ← sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    have hm_pos : (0 : ℝ) < m := by exact_mod_cast (hmem_of_supp m hm).1
    rw [← div_eq_mul_inv, Real.log_div (ne_of_gt hxpos) (ne_of_gt hm_pos)]; ring
  rw [hlog_split]
  -- Once the support of `ν` is known explicitly, both `habs` and `hsum_eq`
  -- reduce to concrete arithmetic over a five-element finset.
  have expand_sum : ∀ f : ℕ → ℝ → ℝ, (∀ n, f n 0 = 0) →
      ν.sum f = f 1 1 + f 2 (-1) + f 3 (-1) + f 5 (-1) + f 30 1 := by
    intro f hf
    rw [Finsupp.sum_of_support_subset _ hsupp_eq.le _ (by intros; simp [hf])]
    simp only [sum_insert (by decide : (1:ℕ) ∉ ({2,3,5,30} : Finset ℕ)),
               sum_insert (by decide : (2:ℕ) ∉ ({3,5,30} : Finset ℕ)),
               sum_insert (by decide : (3:ℕ) ∉ ({5,30} : Finset ℕ)),
               sum_insert (by decide : (5:ℕ) ∉ ({30} : Finset ℕ)),
               sum_singleton, ν, Finsupp.sub_apply, Finsupp.add_apply, Finsupp.single_apply]
    norm_num
    ring
  have habs : ν.sum (fun m w ↦ |w|) = 5 := by
    rw [expand_sum _ (by intros; simp)]; norm_num
  have hgeq6 : ν.sum (fun m w ↦ |w| * log m) ≥ 6 := by
    have hsum_eq : ν.sum (fun m w ↦ |w| * log (m : ℝ)) = log 2 + log 3 + log 5 + log 30 := by
      rw [expand_sum _ (by intros; simp)]
      simp [log_one]
    have hlog30 : log (30 : ℝ) = log 2 + log 3 + log 5 := by
      rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_two_gt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9]
  grw [hgeq6]; rw [habs]; linarith

theorem psi_lower (x : ℝ) (hx : 30 ≤ x) : ψ x ≥ a * x - 5 * log x + 5 := by
  have h2 := abs_sub_le_iff.mp (U_bound x hx)
  linarith [psi_ge_weighted x (by linarith), h2.1]

theorem psi_diff_upper (x : ℝ) (hx : 30 ≤ x) : ψ x - ψ (x / 6) ≤ a * x + 5 * log x - 5 := by
  have h2 := abs_sub_le_iff.mp (U_bound x hx)
  linarith [psi_diff_le_weighted x (by linarith), h2.2]

/- Elementary coarse explicit upper bound, avoiding finite computations and any
extra numerical log tables. -/
theorem log_four_add_four_le : Real.log 4 + 4 ≤ (5.5 : ℝ) := by
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
  norm_num
  linarith [Real.log_two_lt_d9]

theorem psi_coarse_upper_nat (n : ℕ) (hn : 1 ≤ n) :
    ψ (n : ℝ) ≤ (6*a/5) * n + 5 * (Real.log n)^2 + 165 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have ha : 0 ≤ a := by linarith [a_bound.1]
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    by_cases hsmall : n < 30
    · have hpsi := psi_le_const_mul_self (x := (n : ℝ)) (by positivity)
      have hmult := mul_le_mul_of_nonneg_right log_four_add_four_le (show (0 : ℝ) ≤ n by positivity)
      have hnn : (n : ℝ) ≤ 30 := by exact_mod_cast hsmall.le
      nlinarith [sq_nonneg (Real.log n), mul_nonneg ha (show (0 : ℝ) ≤ n by positivity)]
    · let m := ⌊(n : ℝ)/6⌋₊
      have hn30 : (30 : ℝ) ≤ n := by exact_mod_cast Nat.le_of_not_gt hsmall
      have hmR : (m : ℝ) ≤ n / 6 := Nat.floor_le (by positivity)
      have hm1 : 1 ≤ m := (Nat.one_le_floor_iff _).mpr (by linarith)
      have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      have hmn : m < n := by
        have : (m : ℝ) < n := by linarith
        exact_mod_cast this
      have hm_log : log m ≤ log ((n : ℝ)/6) := log_le_log (by positivity) hmR
      have hm_log0 : 0 ≤ log m := log_nonneg hm1R
      have hlog6 : 1 ≤ log 6 := by
        rw [show (6 : ℝ) = 2 * 3 by norm_num, log_mul (by norm_num) (by norm_num)]
        linarith [log_two_gt_d9, log_three_gt_d9]
      have hlogn : log (n : ℝ) ≥ log 6 := log_le_log (by norm_num) (by linarith)
      have hlogdiv : log ((n : ℝ)/6) = log n - log 6 := Real.log_div (by positivity) (by norm_num)
      have hlogdiff : 5 * (log m)^2 + 5 * log n - 5 ≤ 5 * (log n)^2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hm_log) (show 0 ≤ log ((n:ℝ)/6) + log m by linarith),
          mul_nonneg (sub_nonneg.mpr hlogn) (sub_nonneg.mpr hlog6),
          mul_nonneg (sub_nonneg.mpr hlog6) (show 0 ≤ log n by linarith),
          sq_nonneg (log 6 - 1)]
      have hs := psi_diff_upper (n : ℝ) hn30
      rw [psi_eq_psi_coe_floor ((n : ℝ)/6)] at hs
      change ψ (n : ℝ) - ψ (m : ℝ) ≤ _ at hs
      have ih' := ih m hmn hm1
      nlinarith [mul_le_mul_of_nonneg_right hmR ha]

theorem psi_coarse_upper (x : ℝ) (hx : 1 ≤ x) :
    ψ x ≤ (6*a/5) * x + 5 * (Real.log x)^2 + 165 := by
  let n := ⌊x⌋₊
  have hn : 1 ≤ n := (Nat.one_le_floor_iff _).mpr hx
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnx : (n : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hlog := Real.log_le_log (show (0 : ℝ) < n by linarith) hnx
  have ha : 0 ≤ a := by linarith [a_bound.1]
  rw [psi_eq_psi_coe_floor x]
  change ψ (n : ℝ) ≤ _
  nlinarith [psi_coarse_upper_nat n hn, mul_le_mul_of_nonneg_right hnx ha,
    mul_nonneg (sub_nonneg.mpr hlog) (add_nonneg (Real.log_nonneg hx) (Real.log_nonneg hnR))]

theorem log_le_sqrt_scaled (x : ℝ) (hx : (262144 : ℝ) ≤ x) :
    Real.log x ≤ (13.5 / 512) * Real.sqrt x := by
  have hx0 : 0 ≤ x := by linarith
  have hs : (512 : ℝ) ≤ Real.sqrt x := by
    calc (512 : ℝ) = Real.sqrt 262144 := by norm_num
      _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
  have hs0 : 0 < Real.sqrt x := by linarith
  have hlog512 : Real.log 512 ≤ 6.75 := by
    rw [show (512 : ℝ) = 2 ^ (9 : ℕ) by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_two_lt_d9]
  have hlog := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt x / 512 by positivity)
  rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt hx0] at hlog
  linarith

theorem sqrt_threshold (x : ℝ) (hx : (262144 : ℝ) ≤ x) :
    (512 : ℝ) ≤ Real.sqrt x := by
  calc (512 : ℝ) = Real.sqrt 262144 := by norm_num
    _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hx

theorem psi_explicit_upper_large (x : ℝ) (hx : (262144 : ℝ) ≤ x) :
    ψ x ≤ (1.11 : ℝ) * x := by
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlog := log_le_sqrt_scaled x hx
  have hlog0 := Real.log_nonneg hx1
  have hs0 := Real.sqrt_nonneg x
  have hsq := Real.sq_sqrt hx0
  have hsqlog : (Real.log x)^2 ≤ (13.5/512 : ℝ)^2 * x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlog) (show 0 ≤ (13.5/512 : ℝ) * Real.sqrt x + Real.log x by positivity)]
  have hax := mul_le_mul_of_nonneg_right a_bound.2 hx0
  nlinarith [psi_coarse_upper x hx1]

theorem rpow_third_le_sqrt_quarter (x : ℝ) (hx : (262144 : ℝ) ≤ x) :
    x ^ (3 : ℝ)⁻¹ ≤ Real.sqrt x / 4 := by
  have hx0 : 0 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hbase : (4 : ℝ) ≤ x ^ ((6 : ℝ)⁻¹) := by
    have hpow : ((4 : ℝ) ^ (6 : ℕ)) ^ ((6 : ℝ)⁻¹) = 4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [← hpow]
    exact Real.rpow_le_rpow (by positivity) (by norm_num; linarith) (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left hbase (Real.rpow_nonneg hx0 ((3 : ℝ)⁻¹))
  rw [← Real.rpow_add hxpos, show (3 : ℝ)⁻¹ + (6 : ℝ)⁻¹ = 1/2 by norm_num,
    ← Real.sqrt_eq_rpow] at hmul
  linarith

theorem theta_explicit_lower_large (x : ℝ) (hx : (262144 : ℝ) ≤ x) :
    (0.9 : ℝ) * x ≤ θ x := by
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlog := log_le_sqrt_scaled x hx
  have hlog0 := Real.log_nonneg hx1
  have hs := sqrt_threshold x hx
  have hsq := Real.sq_sqrt hx0
  have hpow3 := rpow_third_le_sqrt_quarter x hx
  have hpow5 : x ^ (5 : ℝ)⁻¹ ≤ Real.sqrt x / 4 :=
    (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (5 : ℝ)⁻¹ ≤ (3 : ℝ)⁻¹)).trans hpow3
  have hpow2 : x ^ (2 : ℝ)⁻¹ = Real.sqrt x := by rw [Real.sqrt_eq_rpow]; norm_num
  have hψ2 : ψ (x ^ (2 : ℝ)⁻¹) ≤ 5.5 * Real.sqrt x := by
    rw [hpow2]
    exact (psi_le_const_mul_self (Real.sqrt_nonneg x)).trans
      (mul_le_mul_of_nonneg_right log_four_add_four_le (Real.sqrt_nonneg x))
  have hψ3 : ψ (x ^ (3 : ℝ)⁻¹) ≤ 5.5 * (Real.sqrt x / 4) := by
    have hn := Real.rpow_nonneg hx0 ((3 : ℝ)⁻¹)
    exact (psi_le_const_mul_self hn).trans ((mul_le_mul_of_nonneg_right log_four_add_four_le hn).trans
      (mul_le_mul_of_nonneg_left hpow3 (by norm_num)))
  have hψ5 : ψ (x ^ (5 : ℝ)⁻¹) ≤ 5.5 * (Real.sqrt x / 4) := by
    have hn := Real.rpow_nonneg hx0 ((5 : ℝ)⁻¹)
    exact (psi_le_const_mul_self hn).trans ((mul_le_mul_of_nonneg_right log_four_add_four_le hn).trans
      (mul_le_mul_of_nonneg_left hpow5 (by norm_num)))
  have hψlower := psi_lower x (by linarith)
  have ha := mul_le_mul_of_nonneg_right a_bound.1 hx0
  have hθ := psi_sub_theta_le_psi_add_psi_add_psi x
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) (Real.sqrt_nonneg x)]

theorem theta_explicit_upper_large (x : ℝ) (hx : (262144 : ℝ) ≤ x) :
    θ x ≤ (1.11 : ℝ) * x := (theta_le_psi x).trans (psi_explicit_upper_large x hx)

end Chebyshev

namespace PrimeGap
open Chebyshev

/-- Strict growth of theta on this interval forces a prime in it. -/
lemma large (p : ℕ) (hp : 262144 ≤ p)
    (lo : ∀ x : ℝ, 262144 ≤ x → 0.9 * x ≤ theta x)
    (hi : ∀ x : ℝ, 262144 ≤ x → theta x ≤ 1.11 * x) :
    ∃ q, Nat.Prime q ∧ p < q ∧ 3 * q ≤ 4 * p + 5 := by
  let b := (4 * p + 5) / 3
  have hb : p ≤ b := by dsimp [b]; omega
  have hbp : 4 * p ≤ 3 * b := by dsimp [b]; omega
  have h₁ := lo b (by exact_mod_cast hp.trans hb)
  have h₂ := hi p (by exact_mod_cast hp)
  have h₃ : (4 : ℝ) * p ≤ 3 * b := by exact_mod_cast hbp
  have h₄ : (262144 : ℝ) ≤ p := by exact_mod_cast hp
  have hlt : theta (p : ℝ) < theta (b : ℝ) := by linarith
  by_contra! h
  have heq : Nat.primesLE b = Nat.primesLE p := by
    ext q
    rw [Nat.mem_primesLE, Nat.mem_primesLE]
    constructor
    · rintro ⟨hqb, hq⟩
      refine ⟨?_, hq⟩
      by_contra! hpq
      have := h q hq hpq
      dsimp [b] at hqb
      omega
    · exact fun ⟨hqp,hq⟩ => ⟨hqp.trans hb,hq⟩
  rw [theta_eq_sum_primesLE_log, theta_eq_sum_primesLE_log, heq] at hlt
  exact lt_irrefl _ hlt

lemma next_bound (n q : ℕ) (h : Nat.nth Nat.Prime n < q) (hq : q.Prime) :
    Nat.nth Nat.Prime (n+1) ≤ q := by
  by_contra! h'
  exact h.not_ge (Nat.le_nth_of_lt_nth_succ h' hq)
end PrimeGap

namespace PrimeGap

/-- Each successive prime covers every starting point from the previous endpoint up to it. -/
def Covers (lo cap : ℕ) : List ℕ → Prop
  | [] => cap ≤ lo
  | q :: qs => q.Prime ∧ lo < q ∧ 3 * q ≤ 4 * lo + 5 ∧ Covers q cap qs

lemma covers_sound {xs : List ℕ} {lo cap : ℕ} (cert : Covers lo cap xs)
    (p : ℕ) (hl : lo ≤ p) (hu : p < cap) :
    ∃ q, q.Prime ∧ p < q ∧ 3 * q ≤ 4 * p + 5 := by
  induction xs generalizing lo with
  | nil => change cap ≤ lo at cert; omega
  | cons q qs ih =>
    obtain ⟨hq, _, hfit, htail⟩ := cert
    by_cases h : p < q
    · exact ⟨q,hq,h,by omega⟩
    · exact ih htail (by omega)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma small (p : ℕ) (hp : 2 ≤ p) (hs : p < 262144) :
    ∃ q, q.Prime ∧ p < q ∧ 3 * q ≤ 4 * p + 5 := by
  apply covers_sound (xs :=
    [3, 5, 7, 11, 13, 19, 23, 31, 43, 59, 79, 107, 139, 181, 241, 317, 421, 563, 751, 997,
     1327, 1759, 2347, 3121, 4159, 5531, 7369, 9817, 13063, 17419, 23227, 30971, 41281,
     55021, 73363, 97813, 130411, 173867, 231823, 309091]) (lo := 2) (cap := 262144) _ p hp hs
  norm_num [Covers]

end PrimeGap

open OMA.S_oeis_a208548

theorem OMA.solution : type_of% @OMA.S_oeis_a208548.main := by
  intro n hn
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let p := Nat.nth Nat.Prime i
  have hp : 2 ≤ p := (Nat.prime_nth_prime i).two_le
  have cover : ∃ q, Nat.Prime q ∧ p < q ∧ 3 * q ≤ 4 * p + 5 := by
    by_cases hs : p < 262144
    · exact PrimeGap.small p hp hs
    · exact PrimeGap.large p (by omega) Chebyshev.theta_explicit_lower_large
        Chebyshev.theta_explicit_upper_large
  obtain ⟨q, hq, hpq, hfit⟩ := cover
  have hnext := PrimeGap.next_bound i q hpq hq
  have h : 3 * Nat.nth Nat.Prime (i + 1) ≤ 4 * p + 5 := by omega
  have hr : (3 : ℚ) * Nat.nth Nat.Prime (i + 1) ≤ 4 * p + 5 := by exact_mod_cast h
  change (0 : ℤ) < ⌊(4 / 3 : ℚ) * (2 + (p : ℚ)) - (Nat.nth Nat.Prime (i+1) : ℚ)⌋
  rw [Int.lt_floor_iff]
  push_cast
  linarith
