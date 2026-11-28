import FormalConjectures.ErdosProblems.«408»
import Mathlib.NumberTheory.SelbergSieve

/-!
Proof of Ford-Konyagin-Luca (2010), Theorem 5 (Erdos Problem 408 variant):
for every epsilon > 0 and delta > 0, there exists k such that for all sufficiently large x,
at least (1 - epsilon) * x integers n in [1, x] satisfy P+(phi^[k](n)) <= x^delta.
-/

namespace Erdos408FKL

/- ==================== Section 1: Basic ==================== -/
section
open Finset Real Nat

/- Elementary analytic inequalities -/

lemma exp_sub_one_le_two_mul {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    Real.exp u - 1 ≤ 2 * u := by
  have h := Real.exp_bound (x := u) (n := 1) (by rw [abs_of_nonneg hu0]; linarith) (by norm_num)
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    pow_one, Nat.factorial_one, Nat.succ_eq_add_one] at h
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp hu0)), abs_of_nonneg hu0] at h
  linarith

lemma one_add_inv_pow_le_exp {p s : ℕ} (hp : 2 ≤ p) :
    ((p : ℝ) / (p - 1)) ^ s ≤ Real.exp ((s : ℝ) / (p - 1)) := by
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have h1 : (p : ℝ) / (p - 1) = 1 + 1 / ((p : ℝ) - 1) := by field_simp; ring
  rw [h1]
  calc (1 + 1 / ((p : ℝ) - 1)) ^ s
      ≤ (Real.exp (1 / ((p : ℝ) - 1))) ^ s := by
        gcongr
        linarith [Real.add_one_le_exp (1 / ((p : ℝ) - 1))]
    _ = Real.exp ((s : ℝ) / (p - 1)) := by
        rw [← Real.exp_nat_mul]
        congr 1; ring

lemma beta_prime_le {p s r : ℕ} (hp : r < p) (hr : 2 * s ≤ r) (hs : 1 ≤ s) :
    ((p : ℝ) / (p - 1)) ^ s - 1 ≤ 4 * (s : ℝ) / p := by
  have hp2 : 2 ≤ p := by omega
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    linarith
  have hp1_ge : (p : ℝ) / 2 ≤ (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    linarith
  have hu0 : 0 ≤ (s : ℝ) / ((p : ℝ) - 1) := by positivity
  have hu1 : (s : ℝ) / ((p : ℝ) - 1) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hp1_pos (by norm_num)]
    have hle : 2 * s ≤ p - 1 := by omega
    have hcast : ((2 * s : ℕ) : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hle
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hcast
    linarith
  calc ((p : ℝ) / (p - 1)) ^ s - 1
      ≤ Real.exp ((s : ℝ) / (p - 1)) - 1 := by linarith [one_add_inv_pow_le_exp (s := s) hp2]
    _ ≤ 2 * ((s : ℝ) / (p - 1)) := exp_sub_one_le_two_mul hu0 hu1
    _ ≤ 2 * ((s : ℝ) / ((p : ℝ) / 2)) := by gcongr
    _ = 4 * (s : ℝ) / p := by ring

lemma one_sub_mul_le_pow_one_sub {t : ℝ} (ht1 : t ≤ 1) (k : ℕ) :
    1 - (k : ℝ) * t ≤ (1 - t) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    push_cast
    have h1 : 0 ≤ 1 - t := by linarith
    have h2 : (1 - (k : ℝ) * t) * (1 - t) ≤ (1 - t) ^ k * (1 - t) :=
      mul_le_mul_of_nonneg_right ih h1
    rw [pow_succ]
    have h3 : (k : ℝ) * t ^ 2 ≥ 0 := by positivity
    nlinarith

lemma euler_factor_le_one {p k : ℕ} (hp : k < p) :
    (1 - (k : ℝ) / p) * (1 - 1 / (p : ℝ))⁻¹ ^ k ≤ 1 := by
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hp1 : 1 ≤ p := by omega
  rcases eq_or_lt_of_le hp1 with rfl | hgt
  · have hk0 : k = 0 := by omega
    subst hk0; simp
  · have h1p : (0 : ℝ) < 1 - 1 / (p : ℝ) := by
      have : (1 : ℝ) < p := by exact_mod_cast hgt
      rw [sub_pos, div_lt_one hp_pos]; exact this
    rw [inv_pow, ← div_eq_mul_inv, div_le_one (pow_pos h1p k)]
    have h := one_sub_mul_le_pow_one_sub (t := 1 / (p : ℝ))
      (by rw [div_le_one hp_pos]; exact_mod_cast hp1) k
    have hrew : (k : ℝ) * (1 / (p : ℝ)) = (k : ℝ) / p := by ring
    linarith

lemma euler_factor_ge_one_sub_sq {p k x : ℕ} (hp : k < p) (hx : x ≤ k) :
    1 - (k : ℝ) ^ 2 / (p : ℝ) ^ 2 ≤ (1 - (x : ℝ) / p) * (1 - 1 / (p : ℝ))⁻¹ ^ k := by
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  by_cases hp1 : p = 1
  · subst hp1
    have hk0 : k = 0 := by omega
    have hx0 : x = 0 := by omega
    subst hk0; subst hx0; simp
  have hp_gt1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have h1p : (0 : ℝ) < 1 - 1 / (p : ℝ) := by rw [sub_pos, div_lt_one hp_pos]; exact hp_gt1
  have hinv : 1 + 1 / (p : ℝ) ≤ (1 - 1 / (p : ℝ))⁻¹ := by
    have hmul : (1 + 1 / (p : ℝ)) * (1 - 1 / (p : ℝ)) ≤ 1 := by
      have : (1 + 1 / (p : ℝ)) * (1 - 1 / (p : ℝ)) = 1 - 1 / (p : ℝ) ^ 2 := by ring
      rw [this]; linarith [show (0 : ℝ) ≤ 1 / (p : ℝ) ^ 2 by positivity]
    rwa [← mul_le_mul_iff_left₀ h1p, inv_mul_cancel₀ h1p.ne']
  have hpow : 1 + (k : ℝ) / p ≤ (1 - 1 / (p : ℝ))⁻¹ ^ k := by
    calc 1 + (k : ℝ) / p
        = 1 + (k : ℝ) * (1 / (p : ℝ)) := by ring
      _ ≤ (1 + 1 / (p : ℝ)) ^ k :=
          one_add_mul_le_pow (by linarith [show (0 : ℝ) ≤ 1 / (p : ℝ) by positivity]) k
      _ ≤ (1 - 1 / (p : ℝ))⁻¹ ^ k := by gcongr
  have hxk : (0 : ℝ) ≤ 1 - (k : ℝ) / p := by
    rw [sub_nonneg, div_le_one hp_pos]; exact_mod_cast hp.le
  have hxle : 1 - (k : ℝ) / p ≤ 1 - (x : ℝ) / p := by gcongr
  calc 1 - (k : ℝ) ^ 2 / (p : ℝ) ^ 2
      = (1 - (k : ℝ) / p) * (1 + (k : ℝ) / p) := by ring
    _ ≤ (1 - (x : ℝ) / p) * (1 - 1 / (p : ℝ))⁻¹ ^ k :=
        mul_le_mul hxle hpow (by positivity) (by linarith)

lemma prod_one_sub_ge_one_sub_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    have hj0 : 0 ≤ a j := ha0 j (mem_insert_self j s)
    have hj1 : a j ≤ 1 := ha1 j (mem_insert_self j s)
    have hih := ih (fun i hi => ha0 i (mem_insert_of_mem hi))
      (fun i hi => ha1 i (mem_insert_of_mem hi))
    have hsum_nonneg : 0 ≤ ∑ i ∈ s, a i :=
      Finset.sum_nonneg (fun i hi => ha0 i (mem_insert_of_mem hi))
    nlinarith

lemma prod_one_add_le_exp_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha0 : ∀ i ∈ s, 0 ≤ a i) :
    ∏ i ∈ s, (1 + a i) ≤ Real.exp (∑ i ∈ s, a i) := by
  rw [Real.exp_sum]
  exact Finset.prod_le_prod (fun i hi => by linarith [ha0 i hi])
    (fun i _ => by linarith [Real.add_one_le_exp (a i)])

lemma factorial_ge_div_e_pow (n : ℕ) : ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := by
  have h1 : (n : ℝ) ^ n / (n.factorial : ℝ) ≤ Real.exp (n : ℝ) :=
    Real.pow_div_factorial_le_exp (n : ℝ) (by positivity) n
  have hfac : (0 : ℝ) < n.factorial := by positivity
  rw [div_pow, ← Real.exp_nat_mul, mul_one, div_le_iff₀ (Real.exp_pos _)]
  rw [div_le_iff₀ hfac] at h1
  linarith

/- Harmonic and p-series finite sum bounds -/

lemma sum_inv_Icc_le_log_add_one (N : ℕ) :
    ∑ n ∈ Icc 1 N, (1 / (n : ℝ)) ≤ Real.log (max N 1) + 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rcases eq_or_ne N 0 with rfl | hN
    · simp
    · have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hm1 : max (N : ℝ) 1 = (N : ℝ) := max_eq_left (by exact_mod_cast hN1)
      have hm2 : max ((N + 1 : ℕ) : ℝ) 1 = ((N + 1 : ℕ) : ℝ) :=
        max_eq_left (by exact_mod_cast (by omega : 1 ≤ N + 1))
      rw [hm1] at ih
      rw [hm2]
      have hlog : 1 / ((N + 1 : ℕ) : ℝ) ≤ Real.log (N + 1 : ℕ) - Real.log N := by
        have hposN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
        have hposN1 : (0 : ℝ) < (N + 1 : ℕ) := by positivity
        have h := Real.log_le_sub_one_of_pos (x := (N : ℝ) / ((N + 1 : ℕ) : ℝ)) (by positivity)
        rw [Real.log_div hposN.ne' hposN1.ne'] at h
        push_cast at h ⊢
        have : 1 - (N : ℝ) / (N + 1) = 1 / (N + 1) := by field_simp; ring
        linarith
      linarith

lemma sum_inv_Icc_le_log_add_one_of_pos {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Icc 1 N, (1 / (n : ℝ)) ≤ Real.log N + 1 := by
  have h := sum_inv_Icc_le_log_add_one N
  rwa [max_eq_left (by exact_mod_cast hN)] at h

lemma sum_inv_Icc_ge_log (N : ℕ) (hN : 1 ≤ N) :
    Real.log ((N : ℝ) + 1) ≤ ∑ n ∈ Icc 1 N, (1 / (n : ℝ)) := by
  induction N with
  | zero => omega
  | succ N ih =>
    rcases eq_or_ne N 0 with rfl | hN0
    · simp only [zero_add, Nat.cast_one, Icc_self, sum_singleton, div_one]
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      norm_num at h ⊢; linarith
    · have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hih := ih hN1
      have hstep : Real.log (((N + 1 : ℕ) : ℝ) + 1) - Real.log ((N : ℝ) + 1) ≤
          1 / ((N + 1 : ℕ) : ℝ) := by
        rw [← Real.log_div (by positivity) (by positivity)]
        have h := Real.log_le_sub_one_of_pos
          (x := (((N + 1 : ℕ) : ℝ) + 1) / ((N : ℝ) + 1)) (by positivity)
        push_cast at h ⊢
        have : ((N : ℝ) + 1 + 1) / (N + 1) - 1 = 1 / (N + 1) := by field_simp; ring
        linarith
      linarith

lemma sum_inv_sq_tail (A N : ℕ) (hA : 1 ≤ A) :
    ∑ n ∈ Icc (A + 1) N, (1 / (n : ℝ) ^ 2) ≤ 1 / (A : ℝ) := by
  by_cases hAN : N < A + 1
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; positivity
  have h1 : ∀ n ∈ Icc (A + 1) N, (1 / (n : ℝ) ^ 2) ≤ 1 / ((n - 1 : ℕ) : ℝ) - 1 / (n : ℝ) := by
    intro n hn
    rw [mem_Icc] at hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hnm1 : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
    rw [Nat.cast_sub (by omega), Nat.cast_one] at hnm1 ⊢
    rw [div_sub_div _ _ hnm1.ne' hnpos.ne']
    have : 1 * (n : ℝ) - ((n : ℝ) - 1) * 1 = 1 := by ring
    rw [this]
    gcongr
    nlinarith
  have htelesc : ∀ M, A + 1 ≤ M →
      ∑ n ∈ Icc (A + 1) M, (1 / ((n - 1 : ℕ) : ℝ) - 1 / (n : ℝ)) = 1 / (A : ℝ) - 1 / (M : ℝ) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      simp only [Nat.add_sub_cancel]
      ring
  calc ∑ n ∈ Icc (A + 1) N, (1 / (n : ℝ) ^ 2)
      ≤ ∑ n ∈ Icc (A + 1) N, (1 / ((n - 1 : ℕ) : ℝ) - 1 / (n : ℝ)) := Finset.sum_le_sum h1
    _ = 1 / (A : ℝ) - 1 / (N : ℝ) := htelesc N (by omega)
    _ ≤ 1 / (A : ℝ) := by linarith [show (0 : ℝ) ≤ 1 / (N : ℝ) by positivity]

lemma sum_inv_rpow_le (N : ℕ) {s : ℝ} (hs : 0 < s) :
    ∑ h ∈ Icc 2 N, (h : ℝ) ^ (-1 - s) ≤ 1 / s := by
  by_cases hN : N < 2
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; positivity
  have hstep : ∀ h ∈ Icc 2 N,
      (h : ℝ) ^ (-1 - s) ≤ (((h - 1 : ℕ) : ℝ) ^ (-s) - (h : ℝ) ^ (-s)) / s := by
    intro h hh
    rw [mem_Icc] at hh
    have hh2 : 2 ≤ h := hh.1
    have hpos1 : (0 : ℝ) < ((h - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < h - 1 by omega)
    have hlt : ((h - 1 : ℕ) : ℝ) < (h : ℝ) := by exact_mod_cast (show h - 1 < h by omega)
    have hdiff : ∀ x ∈ Set.Icc (((h - 1 : ℕ) : ℝ)) (h : ℝ),
        HasDerivAt (fun t : ℝ => t ^ (-s)) ((-s) * x ^ (-s - 1)) x := by
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le hpos1 hx.1
      simpa using Real.hasDerivAt_rpow_const (p := -s) (Or.inl hxpos.ne')
    obtain ⟨c, hc, hcmvt⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => t ^ (-s))
      (fun x => (-s) * x ^ (-s - 1)) hlt
      (fun x hx => (hdiff x hx).continuousAt.continuousWithinAt)
      (fun x hx => hdiff x (Set.Ioo_subset_Icc_self hx))
    have hsub : (h : ℝ) - ((h - 1 : ℕ) : ℝ) = 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]; ring
    rw [hsub, div_one] at hcmvt
    have hc_le : (h : ℝ) ^ (-1 - s) ≤ c ^ (-1 - s) := by
      have hcpos : 0 < c := lt_trans hpos1 hc.1
      have : (-1 - s) ≤ 0 := by linarith
      exact Real.rpow_le_rpow_of_nonpos hcpos hc.2.le this
    rw [le_div_iff₀ hs]
    have hrew : -s - 1 = -1 - s := by ring
    rw [hrew] at hcmvt
    nlinarith
  have htelesc : ∀ M, 2 ≤ M →
      ∑ h ∈ Icc 2 M, (((h - 1 : ℕ) : ℝ) ^ (-s) - (h : ℝ) ^ (-s)) = 1 - (M : ℝ) ^ (-s) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      simp only [Nat.add_sub_cancel]
      ring
  calc ∑ h ∈ Icc 2 N, (h : ℝ) ^ (-1 - s)
      ≤ ∑ h ∈ Icc 2 N, (((h - 1 : ℕ) : ℝ) ^ (-s) - (h : ℝ) ^ (-s)) / s :=
        Finset.sum_le_sum hstep
    _ = (1 / s) * ∑ h ∈ Icc 2 N, (((h - 1 : ℕ) : ℝ) ^ (-s) - (h : ℝ) ^ (-s)) := by
        rw [Finset.mul_sum]; congr 1 with h; ring
    _ = (1 / s) * (1 - (N : ℝ) ^ (-s)) := by rw [htelesc N (by omega)]
    _ ≤ 1 / s := by
        have : 0 ≤ (N : ℝ) ^ (-s) := by positivity
        nlinarith [show 0 < 1 / s by positivity]

lemma sum_inv_congr_one (X d : ℕ) (hd : 1 ≤ d) :
    ∑ u ∈ (Icc 1 X).filter (fun u => d ∣ u - 1 ∧ 1 < u), (1 / (u : ℝ)) ≤
      (Real.log (max X 1) + 1) / d := by
  let S := (Icc 1 X).filter (fun u => d ∣ u - 1 ∧ 1 < u)
  let f : ℕ → ℕ := fun u => (u - 1) / d
  have hmaps : ∀ u ∈ S, f u ∈ Icc 1 X := by
    intro u hu
    rw [Finset.mem_filter, Finset.mem_Icc] at hu
    obtain ⟨⟨_, huX⟩, hdvd, hu1⟩ := hu
    rw [mem_Icc]
    have hpos : 1 ≤ (u - 1) / d := by
      obtain ⟨c, hc⟩ := hdvd
      have hc1 : 1 ≤ c := by
        rcases eq_or_ne c 0 with rfl | _ <;> omega
      rw [hc, Nat.mul_div_cancel_left c (by omega)]
      exact hc1
    exact ⟨hpos, (Nat.div_le_self _ _).trans (by omega)⟩
  have hinj : Set.InjOn f S := by
    intro u₁ hu₁ u₂ hu₂ heq
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hu₁ hu₂
    have h1 : d * ((u₁ - 1) / d) = u₁ - 1 := Nat.mul_div_cancel' hu₁.2.1
    have h2 : d * ((u₂ - 1) / d) = u₂ - 1 := Nat.mul_div_cancel' hu₂.2.1
    have hsub : u₁ - 1 = u₂ - 1 := by
      rw [← h1, ← h2]
      exact congrArg (d * ·) heq
    omega
  have hterm : ∀ u ∈ S, (1 / (u : ℝ)) ≤ (1 / (d : ℝ)) * (1 / (f u : ℝ)) := by
    intro u hu
    rw [Finset.mem_filter, Finset.mem_Icc] at hu
    have hmul : d * f u = u - 1 := Nat.mul_div_cancel' hu.2.1
    have hpos_f : 0 < f u := by
      have := hmaps u (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hu.1, hu.2⟩)
      rw [mem_Icc] at this; omega
    have hle : (d : ℝ) * (f u : ℝ) ≤ (u : ℝ) := by
      have : d * f u ≤ u := by omega
      exact_mod_cast this
    rw [one_div_mul_one_div]
    exact one_div_le_one_div_of_le (by positivity) hle
  have hsum_img : ∑ u ∈ S, (1 / (f u : ℝ)) ≤ ∑ c ∈ Icc 1 X, (1 / (c : ℝ)) := by
    rw [← Finset.sum_image (f := fun c : ℕ => (1 : ℝ) / c) (fun x hx y hy h => hinj hx hy h)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hmaps)
      (fun _ _ _ => by positivity)
  calc ∑ u ∈ S, (1 / (u : ℝ))
      ≤ ∑ u ∈ S, (1 / (d : ℝ)) * (1 / (f u : ℝ)) := Finset.sum_le_sum hterm
    _ = (1 / (d : ℝ)) * ∑ u ∈ S, (1 / (f u : ℝ)) := (Finset.mul_sum _ _ _).symm
    _ ≤ (1 / (d : ℝ)) * ∑ c ∈ Icc 1 X, (1 / (c : ℝ)) := by gcongr
    _ ≤ (1 / (d : ℝ)) * (Real.log (max X 1) + 1) := by
        gcongr
        exact sum_inv_Icc_le_log_add_one X
    _ = (Real.log (max X 1) + 1) / d := by ring

/- Elementary prime sum bounds from Chebyshev -/

lemma sum_biUnion_le_sum {α β : Type*} [DecidableEq β] (s : Finset α) (t : α → Finset β)
    (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    ∑ b ∈ s.biUnion t, f b ≤ ∑ a ∈ s, ∑ b ∈ t a, f b := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have h1 : ∑ b ∈ t a ∪ s.biUnion t, f b ≤ ∑ b ∈ t a, f b + ∑ b ∈ s.biUnion t, f b := by
      rw [← Finset.sum_union_inter]
      linarith [Finset.sum_nonneg (s := t a ∩ s.biUnion t) (fun b _ => hf b)]
    linarith

lemma prod_primes_le_four_pow (r : ℕ) :
    (∏ p ∈ (r + 1).primesBelow, (p : ℝ)) ≤ (4 : ℝ) ^ r := by
  have hth := Chebyshev.theta_le_log4_mul_x (x := (r : ℝ)) (by positivity)
  have hpri := Chebyshev.theta_eq_log_primorial (x := (r : ℝ))
  rw [Nat.floor_natCast] at hpri
  have hprim_eq : (primorial r : ℝ) = ∏ p ∈ (r + 1).primesBelow, (p : ℝ) := by
    rw [primorial, Nat.cast_prod, Nat.primesBelow]
  have hpos : (0 : ℝ) < ∏ p ∈ (r + 1).primesBelow, (p : ℝ) :=
    Finset.prod_pos (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).pos)
  rw [hpri, hprim_eq] at hth
  calc ∏ p ∈ (r + 1).primesBelow, (p : ℝ)
      = Real.exp (Real.log (∏ p ∈ (r + 1).primesBelow, (p : ℝ))) := (Real.exp_log hpos).symm
    _ ≤ Real.exp (Real.log 4 * r) := Real.exp_le_exp.mpr hth
    _ = (Real.exp (Real.log 4)) ^ r := by rw [mul_comm, Real.exp_nat_mul]
    _ = (4 : ℝ) ^ r := by rw [Real.exp_log (by norm_num)]

lemma theta_eq_sum_primesBelow (n : ℕ) :
    Chebyshev.theta (n : ℝ) = ∑ p ∈ (n + 1).primesBelow, Real.log (p : ℕ) := by
  rw [Chebyshev.theta_eq_sum_Icc]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesBelow, Nat.floor_natCast,
    Nat.lt_succ_iff]
  exact ⟨fun ⟨⟨_, hle⟩, hp⟩ => ⟨hle, hp⟩, fun ⟨hle, hp⟩ => ⟨⟨Nat.zero_le p, hle⟩, hp⟩⟩

lemma sum_prime_log_div_le_dyadic (M : ℕ) :
    ∑ p ∈ (2 ^ M).primesBelow, Real.log (p : ℕ) / (p : ℕ) ≤ 4 * (M : ℝ) * Real.log 2 := by
  induction M with
  | zero =>
    have h0 : (2 ^ 0).primesBelow = ∅ := by decide
    rw [h0]; simp
  | succ M ih =>
    have hsplit : (2 ^ (M + 1)).primesBelow =
        (2 ^ M).primesBelow ∪ ((2 ^ (M + 1)).primesBelow.filter (fun p => 2 ^ M ≤ p)) := by
      ext p
      simp only [Finset.mem_union, Finset.mem_filter, Nat.mem_primesBelow]
      constructor
      · intro ⟨hlt, hp⟩
        by_cases h : p < 2 ^ M
        · exact Or.inl ⟨h, hp⟩
        · exact Or.inr ⟨⟨hlt, hp⟩, by omega⟩
      · rintro (⟨h, hp⟩ | ⟨⟨hlt, hp⟩, _⟩)
        · exact ⟨lt_trans h (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self M)), hp⟩
        · exact ⟨hlt, hp⟩
    have hdisj : Disjoint (2 ^ M).primesBelow
        ((2 ^ (M + 1)).primesBelow.filter (fun p => 2 ^ M ≤ p)) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Nat.mem_primesBelow, Finset.mem_filter] at hp1 hp2
      omega
    rw [hsplit, Finset.sum_union hdisj]
    have hblock : ∑ p ∈ (2 ^ (M + 1)).primesBelow.filter (fun p => 2 ^ M ≤ p),
        Real.log (p : ℕ) / (p : ℕ) ≤ 4 * Real.log 2 := by
      have h1 : ∑ p ∈ (2 ^ (M + 1)).primesBelow.filter (fun p => 2 ^ M ≤ p),
          Real.log (p : ℕ) / (p : ℕ) ≤
          (1 / ((2 ^ M : ℕ) : ℝ)) *
            ∑ p ∈ (2 ^ (M + 1)).primesBelow.filter (fun p => 2 ^ M ≤ p), Real.log (p : ℕ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro p hp
        simp only [Finset.mem_filter, Nat.mem_primesBelow] at hp
        rw [one_div_mul_eq_div]
        exact div_le_div_of_nonneg_left (Real.log_nonneg (by exact_mod_cast hp.1.2.one_le))
          (by positivity) (by exact_mod_cast hp.2)
      have h2 : ∑ p ∈ (2 ^ (M + 1)).primesBelow.filter (fun p => 2 ^ M ≤ p), Real.log (p : ℕ) ≤
          Chebyshev.theta ((2 ^ (M + 1) : ℕ) : ℝ) := by
        rw [theta_eq_sum_primesBelow]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          simp only [Finset.mem_filter, Nat.mem_primesBelow] at hp ⊢
          exact ⟨Nat.lt_succ_of_lt hp.1.1, hp.1.2⟩
        · intro p hp _
          exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_le)
      have h3 := Chebyshev.theta_le_log4_mul_x (x := ((2 ^ (M + 1) : ℕ) : ℝ)) (by positivity)
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
      have h5 : ((2 ^ (M + 1) : ℕ) : ℝ) = 2 * ((2 ^ M : ℕ) : ℝ) := by
        push_cast [pow_succ]; ring
      calc ∑ p ∈ (2 ^ (M + 1)).primesBelow.filter (fun p => 2 ^ M ≤ p),
              Real.log (p : ℕ) / (p : ℕ)
          ≤ (1 / ((2 ^ M : ℕ) : ℝ)) * Chebyshev.theta ((2 ^ (M + 1) : ℕ) : ℝ) :=
            h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
        _ ≤ (1 / ((2 ^ M : ℕ) : ℝ)) * (Real.log 4 * ((2 ^ (M + 1) : ℕ) : ℝ)) := by gcongr
        _ = 4 * Real.log 2 := by rw [h4, h5]; field_simp; ring
    push_cast
    linarith

lemma sum_prime_log_div_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ p ∈ (⌊x⌋₊ + 1).primesBelow, Real.log (p : ℕ) / (p : ℕ) ≤ 4 * Real.log x + 4 := by
  let M := Nat.clog 2 (⌊x⌋₊ + 1)
  have hsub : (⌊x⌋₊ + 1).primesBelow ⊆ (2 ^ M).primesBelow := by
    intro p hp
    simp only [Nat.mem_primesBelow] at hp ⊢
    exact ⟨lt_of_lt_of_le hp.1 (Nat.le_pow_clog (by norm_num) _), hp.2⟩
  have hle : ∑ p ∈ (⌊x⌋₊ + 1).primesBelow, Real.log (p : ℕ) / (p : ℕ) ≤
      ∑ p ∈ (2 ^ M).primesBelow, Real.log (p : ℕ) / (p : ℕ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ =>
      div_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_le))
        (by positivity))
  have hdy := sum_prime_log_div_le_dyadic M
  have hM : (M : ℝ) * Real.log 2 ≤ Real.log x + Real.log 2 := by
    have hfl1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
    have hM1 : 1 ≤ M := Nat.clog_pos (by norm_num) (by omega)
    have hlt : 2 ^ (M - 1) < ⌊x⌋₊ + 1 := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
    have hle2 : (2 : ℝ) ^ (M - 1) ≤ x := by
      have : 2 ^ (M - 1) ≤ ⌊x⌋₊ := by omega
      exact le_trans (by exact_mod_cast this) (Nat.floor_le (by linarith))
    have hlog : ((M - 1 : ℕ) : ℝ) * Real.log 2 ≤ Real.log x := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) hle2
    rw [Nat.cast_sub hM1, Nat.cast_one] at hlog
    linarith
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  linarith

lemma sum_prime_inv_le_dyadic (M : ℕ) (hM : 1 ≤ M) :
    ∑ p ∈ (2 ^ M).primesBelow, ((1 : ℝ) / (p : ℕ)) ≤ 8 * Real.log M + 8 := by
  have h1 : ∑ p ∈ (2 ^ M).primesBelow, ((1 : ℝ) / (p : ℕ)) ≤
      ∑ m ∈ Icc 1 M,
        ∑ p ∈ (2 ^ m).primesBelow.filter (fun p => 2 ^ (m - 1) ≤ p), ((1 : ℝ) / (p : ℕ)) := by
    have hcov : (2 ^ M).primesBelow ⊆
        (Icc 1 M).biUnion (fun m => (2 ^ m).primesBelow.filter (fun p => 2 ^ (m - 1) ≤ p)) := by
      intro p hp
      simp only [Nat.mem_primesBelow, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_filter] at hp ⊢
      let m := Nat.log 2 p + 1
      have hm1 : 1 ≤ m := by omega
      have hlt : p < 2 ^ m := Nat.lt_pow_succ_log_self (by norm_num) p
      have hge : 2 ^ (m - 1) ≤ p := by
        simp only [m, Nat.add_sub_cancel]
        exact Nat.pow_log_le_self 2 hp.2.ne_zero
      have hmM : m ≤ M := by
        by_contra hgt
        push Not at hgt
        have : 2 ^ M ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      exact ⟨m, ⟨hm1, hmM⟩, ⟨hlt, hp.2⟩, hge⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg hcov (fun _ _ _ => by positivity)).trans
      (sum_biUnion_le_sum _ _ (fun p : ℕ => (1 : ℝ) / (p : ℕ)) (fun _ => by positivity))
  have hblock : ∀ m ∈ Icc 1 M,
      ∑ p ∈ (2 ^ m).primesBelow.filter (fun p => 2 ^ (m - 1) ≤ p), ((1 : ℝ) / (p : ℕ)) ≤
        8 / (m : ℝ) := by
    intro m hm
    rw [mem_Icc] at hm
    rcases eq_or_lt_of_le hm.1 with rfl | hm2
    · have hempty : (2 ^ 1).primesBelow.filter (fun p => 2 ^ 0 ≤ p) = ∅ := by decide
      rw [hempty]; simp
    · have hm1 : 1 ≤ m - 1 := by omega
      have h2m : m ≤ 2 * (m - 1) := by omega
      have hstep : ∀ p ∈ (2 ^ m).primesBelow.filter (fun p => 2 ^ (m - 1) ≤ p),
          ((1 : ℝ) / (p : ℕ)) ≤
            (1 / (((m - 1 : ℕ) : ℝ) * Real.log 2 * ((2 ^ (m - 1) : ℕ) : ℝ))) * Real.log (p : ℕ) := by
        intro p hp
        simp only [Finset.mem_filter, Nat.mem_primesBelow] at hp
        have hlp : ((m - 1 : ℕ) : ℝ) * Real.log 2 ≤ Real.log (p : ℕ) := by
          rw [← Real.log_pow]
          exact Real.log_le_log (by positivity) (by exact_mod_cast hp.2)
        have hden : 0 < ((m - 1 : ℕ) : ℝ) * Real.log 2 * ((2 ^ (m - 1) : ℕ) : ℝ) := by
          have : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < m - 1 by omega)
          have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
          positivity
        rw [one_div_mul_eq_div, div_le_div_iff₀ (by exact_mod_cast hp.1.2.pos) hden, one_mul]
        calc ((m - 1 : ℕ) : ℝ) * Real.log 2 * ((2 ^ (m - 1) : ℕ) : ℝ)
            ≤ Real.log (p : ℕ) * ((2 ^ (m - 1) : ℕ) : ℝ) := by gcongr
          _ ≤ Real.log (p : ℕ) * (p : ℝ) :=
              mul_le_mul_of_nonneg_left (by exact_mod_cast hp.2)
                (Real.log_nonneg (by exact_mod_cast hp.1.2.one_le))
      calc ∑ p ∈ (2 ^ m).primesBelow.filter (fun p => 2 ^ (m - 1) ≤ p), ((1 : ℝ) / (p : ℕ))
          ≤ (1 / (((m - 1 : ℕ) : ℝ) * Real.log 2 * ((2 ^ (m - 1) : ℕ) : ℝ))) *
              ∑ p ∈ (2 ^ m).primesBelow.filter (fun p => 2 ^ (m - 1) ≤ p), Real.log (p : ℕ) := by
            rw [Finset.mul_sum]; exact Finset.sum_le_sum hstep
        _ ≤ (1 / (((m - 1 : ℕ) : ℝ) * Real.log 2 * ((2 ^ (m - 1) : ℕ) : ℝ))) *
              Chebyshev.theta ((2 ^ m : ℕ) : ℝ) := by
            gcongr
            rw [theta_eq_sum_primesBelow]
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro p hp
              simp only [Finset.mem_filter, Nat.mem_primesBelow] at hp ⊢
              exact ⟨Nat.lt_succ_of_lt hp.1.1, hp.1.2⟩
            · intro p hp _
              exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_le)
        _ ≤ (1 / (((m - 1 : ℕ) : ℝ) * Real.log 2 * ((2 ^ (m - 1) : ℕ) : ℝ))) *
              (Real.log 4 * ((2 ^ m : ℕ) : ℝ)) := by
            gcongr; exact Chebyshev.theta_le_log4_mul_x (by positivity)
        _ = 4 / ((m - 1 : ℕ) : ℝ) := by
            have h4 : Real.log 4 = 2 * Real.log 2 := by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
            have hpow : ((2 ^ m : ℕ) : ℝ) = 2 * ((2 ^ (m - 1) : ℕ) : ℝ) := by
              have : 2 ^ m = 2 * 2 ^ (m - 1) := by
                conv_lhs => rw [show m = (m - 1) + 1 by omega, _root_.pow_succ']
              exact_mod_cast this
            have hl2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
            rw [h4, hpow]; field_simp; ring
        _ ≤ 8 / (m : ℝ) := by
            rw [div_le_div_iff₀ (by exact_mod_cast (show 0 < m - 1 by omega))
              (by exact_mod_cast (show 0 < m by omega))]
            have : (m : ℝ) ≤ 2 * ((m - 1 : ℕ) : ℝ) := by exact_mod_cast h2m
            linarith
  calc ∑ p ∈ (2 ^ M).primesBelow, ((1 : ℝ) / (p : ℕ))
      ≤ ∑ m ∈ Icc 1 M, (8 / (m : ℝ)) := h1.trans (Finset.sum_le_sum hblock)
    _ = 8 * ∑ m ∈ Icc 1 M, ((1 : ℝ) / (m : ℕ)) := by
        rw [Finset.mul_sum]; congr 1 with m; ring
    _ ≤ 8 * (Real.log M + 1) := by
        gcongr; exact sum_inv_Icc_le_log_add_one_of_pos hM
    _ = 8 * Real.log M + 8 := by ring

lemma sum_prime_inv_le {x : ℝ} (hx : 2 ≤ x) :
    ∑ p ∈ (⌊x⌋₊ + 1).primesBelow, ((1 : ℝ) / (p : ℕ)) ≤ 8 * Real.log (Real.log x + 2) + 16 := by
  let M := Nat.clog 2 (⌊x⌋₊ + 1)
  have hfl2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hM1 : 1 ≤ M := Nat.clog_pos (by norm_num) (by omega)
  have hsub : (⌊x⌋₊ + 1).primesBelow ⊆ (2 ^ M).primesBelow := by
    intro p hp
    simp only [Nat.mem_primesBelow] at hp ⊢
    exact ⟨lt_of_lt_of_le hp.1 (Nat.le_pow_clog (by norm_num) _), hp.2⟩
  have hle : ∑ p ∈ (⌊x⌋₊ + 1).primesBelow, ((1 : ℝ) / (p : ℕ)) ≤
      ∑ p ∈ (2 ^ M).primesBelow, ((1 : ℝ) / (p : ℕ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have hdy := sum_prime_inv_le_dyadic M hM1
  have hlt : 2 ^ (M - 1) < ⌊x⌋₊ + 1 := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  have hle2 : (2 : ℝ) ^ (M - 1) ≤ x := by
    have : 2 ^ (M - 1) ≤ ⌊x⌋₊ := by omega
    exact le_trans (by exact_mod_cast this) (Nat.floor_le (by linarith))
  have hlog : ((M - 1 : ℕ) : ℝ) * Real.log 2 ≤ Real.log x := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hle2
  have hl2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hM_le : (M : ℝ) ≤ 2 * (Real.log x + 2) := by
    rw [Nat.cast_sub hM1, Nat.cast_one] at hlog
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    nlinarith
  have hlogM : Real.log M ≤ Real.log (Real.log x + 2) + 1 := by
    calc Real.log (M : ℝ)
        ≤ Real.log (2 * (Real.log x + 2)) :=
          Real.log_le_log (by positivity) hM_le
      _ = Real.log 2 + Real.log (Real.log x + 2) :=
          Real.log_mul (by norm_num) (by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ x)])
      _ ≤ Real.log (Real.log x + 2) + 1 := by
          linarith [Real.log_two_lt_d9]
  linarith

lemma prod_one_sub_inv_le {x : ℝ} (hx : 2 ≤ x) :
    ∏ p ∈ (⌊x⌋₊ + 1).primesBelow, (1 - 1 / (p : ℝ))⁻¹ ≤
      Real.exp (16 * Real.log (Real.log x + 2) + 32) := by
  have hterm : ∀ p ∈ (⌊x⌋₊ + 1).primesBelow,
      (1 - 1 / (p : ℝ))⁻¹ ≤ Real.exp (2 / (p : ℝ)) := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primesBelow hp).two_le
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      linarith
    have h1 : (1 - 1 / (p : ℝ))⁻¹ = 1 / ((p : ℝ) - 1) + 1 := by field_simp; ring
    have h3 : 1 / ((p : ℝ) - 1) ≤ 2 / (p : ℝ) := by
      rw [div_le_div_iff₀ hp1 hp_pos]
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      linarith
    rw [h1]
    exact (Real.add_one_le_exp _).trans (Real.exp_le_exp.mpr h3)
  calc ∏ p ∈ (⌊x⌋₊ + 1).primesBelow, (1 - 1 / (p : ℝ))⁻¹
      ≤ ∏ p ∈ (⌊x⌋₊ + 1).primesBelow, Real.exp (2 / (p : ℝ)) :=
        Finset.prod_le_prod (fun p hp => by
          have hp2 : 2 ≤ p := (Nat.prime_of_mem_primesBelow hp).two_le
          have hp_pos : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
          have : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
          have : 0 < 1 - 1 / (p : ℝ) := by rw [sub_pos, div_lt_one hp_pos]; exact this
          positivity) hterm
    _ = Real.exp (∑ p ∈ (⌊x⌋₊ + 1).primesBelow, 2 / (p : ℝ)) := (Real.exp_sum _ _).symm
    _ = Real.exp (2 * ∑ p ∈ (⌊x⌋₊ + 1).primesBelow, ((1 : ℝ) / (p : ℕ))) := by
        congr 1; rw [Finset.mul_sum]; congr 1 with p; ring
    _ ≤ Real.exp (16 * Real.log (Real.log x + 2) + 32) := by
        apply Real.exp_le_exp.mpr
        linarith [sum_prime_inv_le hx]

lemma prod_one_sub_inv_ge_log (Y : ℕ) (hY : 1 ≤ Y) :
    Real.log ((Y : ℝ) + 1) ≤ ∏ p ∈ (Y + 1).primesBelow, (1 - 1 / (p : ℝ))⁻¹ := by
  let P := (Y + 1).primesBelow
  have hgeom : ∀ p ∈ P, ∑ e ∈ range (Y + 1), (1 / (p : ℝ)) ^ e ≤ (1 - 1 / (p : ℝ))⁻¹ := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primesBelow hp).two_le
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    have hlt1 : 1 / (p : ℝ) < 1 := by
      rw [div_lt_one hp_pos]; exact_mod_cast (show 1 < p by omega)
    rw [geom_sum_eq hlt1.ne, ← neg_div_neg_eq, neg_sub, neg_sub, div_eq_mul_inv]
    have hpos : 0 < (1 - 1 / (p : ℝ))⁻¹ := inv_pos.mpr (by linarith)
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1 / p by positivity) (Y + 1)]
  have hprod_ge : ∏ p ∈ P, ∑ e ∈ range (Y + 1), (1 / (p : ℝ)) ^ e ≤
      ∏ p ∈ P, (1 - 1 / (p : ℝ))⁻¹ :=
    Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity)) hgeom
  let F := Fintype.piFinset (fun _ : P => range (Y + 1))
  have hexpand : ∏ p ∈ P, ∑ e ∈ range (Y + 1), (1 / (p : ℝ)) ^ e =
      ∑ f ∈ F, ∏ p : P, (1 / ((p : ℕ) : ℝ)) ^ (f p) := by
    rw [← Finset.prod_attach P]
    exact Finset.prod_univ_sum (t := fun _ : P => range (Y + 1))
      (f := fun (p : P) (e : ℕ) => (1 / ((p : ℕ) : ℝ)) ^ e)
  let g : ℕ → (P → ℕ) := fun n p => padicValNat (p : ℕ) n
  have hg_mem : ∀ n ∈ Icc 1 Y, g n ∈ F := by
    intro n hn
    rw [mem_Icc] at hn
    rw [Fintype.mem_piFinset]
    intro p
    rw [mem_range]
    have hp : (p : ℕ).Prime := Nat.prime_of_mem_primesBelow p.2
    have hne : n ≠ 0 := by omega
    have : Fact (p : ℕ).Prime := ⟨hp⟩
    have hpow : (p : ℕ) ^ padicValNat (p : ℕ) n ≤ n :=
      Nat.le_of_dvd (by omega) pow_padicValNat_dvd
    have hlt : padicValNat (p : ℕ) n < (p : ℕ) ^ padicValNat (p : ℕ) n :=
      Nat.lt_pow_self hp.one_lt
    simp only [g]; omega
  have hg_prod : ∀ n ∈ Icc 1 Y, ∏ p : P, (p : ℕ) ^ (g n p) = n := by
    intro n hn
    rw [mem_Icc] at hn
    have hne : n ≠ 0 := by omega
    have hsub : n.primeFactors ⊆ P := by
      intro p hp
      rw [Nat.mem_primeFactors] at hp
      rw [Nat.mem_primesBelow]
      exact ⟨Nat.lt_succ_of_le ((Nat.le_of_dvd (by omega) hp.2.1).trans hn.2), hp.1⟩
    calc ∏ p : P, (p : ℕ) ^ (g n p)
        = ∏ p ∈ P, p ^ padicValNat p n := Finset.prod_attach P (fun p => p ^ padicValNat p n)
      _ = ∏ p ∈ n.primeFactors, p ^ padicValNat p n := by
          symm
          apply Finset.prod_subset hsub
          intro p hp hnot
          have hp_pr : p.Prime := Nat.prime_of_mem_primesBelow hp
          have hndvd : ¬ p ∣ n := by
            intro hd
            exact hnot (Nat.mem_primeFactors.mpr ⟨hp_pr, hd, hne⟩)
          simp [padicValNat.eq_zero_of_not_dvd hndvd]
      _ = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
          refine Finset.prod_congr rfl fun p hp => ?_
          have hp_pr : p.Prime := Nat.prime_of_mem_primeFactors hp
          have : Fact p.Prime := ⟨hp_pr⟩
          rw [Nat.factorization_def n hp_pr]
      _ = n := Nat.prod_factorization_pow_eq_self hne
  have hg_inj : Set.InjOn g (Icc 1 Y) := by
    intro n₁ hn₁ n₂ hn₂ heq
    rw [← hg_prod n₁ hn₁, ← hg_prod n₂ hn₂]
    exact Finset.prod_congr rfl fun p _ => by rw [congr_fun heq p]
  have hsum_le : ∑ n ∈ Icc 1 Y, (1 / (n : ℝ)) ≤
      ∑ f ∈ F, ∏ p : P, (1 / ((p : ℕ) : ℝ)) ^ (f p) := by
    have hterm : ∀ n ∈ Icc 1 Y,
        (1 / (n : ℝ)) = ∏ p : P, (1 / ((p : ℕ) : ℝ)) ^ (g n p) := by
      intro n hn
      have hpr := hg_prod n hn
      have hcast : (n : ℝ) = ∏ p : P, ((p : ℕ) : ℝ) ^ (g n p) := by
        exact_mod_cast hpr.symm
      rw [hcast, one_div, ← Finset.prod_inv_distrib]
      congr 1 with p
      rw [one_div, inv_pow]
    calc ∑ n ∈ Icc 1 Y, (1 / (n : ℝ))
        = ∑ n ∈ Icc 1 Y, ∏ p : P, (1 / ((p : ℕ) : ℝ)) ^ (g n p) := Finset.sum_congr rfl hterm
      _ = ∑ f ∈ (Icc 1 Y).image g, ∏ p : P, (1 / ((p : ℕ) : ℝ)) ^ (f p) :=
          (Finset.sum_image (f := fun f : P → ℕ => ∏ p : P, (1 / ((p : ℕ) : ℝ)) ^ (f p))
            (fun x hx y hy h => hg_inj hx hy h)).symm
      _ ≤ ∑ f ∈ F, ∏ p : P, (1 / ((p : ℕ) : ℝ)) ^ (f p) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hg_mem)
            (fun _ _ _ => Finset.prod_nonneg (fun _ _ => by positivity))
  exact (sum_inv_Icc_ge_log Y hY).trans (hsum_le.trans (hexpand ▸ hprod_ge))

/- Weighted Hölder inequality for finite sums -/

lemma holder_finset {ι κ : Type*} (s : Finset κ) (t : Finset ι)
    (w : ι → ℝ) (f : ι → κ → ℝ)
    (hw_pos : ∀ i ∈ t, 0 < w i) (hw_sum : ∑ i ∈ t, w i = 1)
    (hf_nonneg : ∀ i ∈ t, ∀ x ∈ s, 0 ≤ f i x) :
    ∑ x ∈ s, ∏ i ∈ t, f i x ≤
      ∏ i ∈ t, (∑ x ∈ s, (f i x) ^ (w i)⁻¹) ^ (w i) := by
  let A : ι → ℝ := fun i => (∑ x ∈ s, (f i x) ^ (w i)⁻¹) ^ (w i)
  have hA_nonneg : ∀ i ∈ t, 0 ≤ A i := fun i _ =>
    Real.rpow_nonneg (Finset.sum_nonneg (fun x hx => Real.rpow_nonneg (hf_nonneg i ‹_› x hx) _)) _
  by_cases hzero : ∃ i ∈ t, A i = 0
  · obtain ⟨i₀, hi₀, hA0⟩ := hzero
    have hsum0 : ∑ x ∈ s, (f i₀ x) ^ (w i₀)⁻¹ = 0 := by
      have hpos : 0 < w i₀ := hw_pos i₀ hi₀
      have hnn : 0 ≤ ∑ x ∈ s, (f i₀ x) ^ (w i₀)⁻¹ :=
        Finset.sum_nonneg (fun x hx => Real.rpow_nonneg (hf_nonneg i₀ hi₀ x hx) _)
      by_contra hne
      have hgt : 0 < ∑ x ∈ s, (f i₀ x) ^ (w i₀)⁻¹ := lt_of_le_of_ne hnn (Ne.symm hne)
      exact (Real.rpow_pos_of_pos hgt (w i₀)).ne' hA0
    have hall0 : ∀ x ∈ s, f i₀ x = 0 := by
      intro x hx
      have h1 : (f i₀ x) ^ (w i₀)⁻¹ = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun y hy => Real.rpow_nonneg (hf_nonneg i₀ hi₀ y hy) _)).mp hsum0 x hx
      by_contra hne
      have hpos : 0 < f i₀ x := lt_of_le_of_ne (hf_nonneg i₀ hi₀ x hx) (Ne.symm hne)
      exact (Real.rpow_pos_of_pos hpos _).ne' h1
    have hlhs : ∑ x ∈ s, ∏ i ∈ t, f i x = 0 :=
      Finset.sum_eq_zero (fun x hx => Finset.prod_eq_zero hi₀ (hall0 x hx))
    rw [hlhs]
    exact Finset.prod_nonneg hA_nonneg
  · push Not at hzero
    have hA_pos : ∀ i ∈ t, 0 < A i :=
      fun i hi => lt_of_le_of_ne (hA_nonneg i hi) (Ne.symm (hzero i hi))
    have hP_pos : 0 < ∏ i ∈ t, A i := Finset.prod_pos hA_pos
    rw [← div_le_one hP_pos, Finset.sum_div]
    have hpoint : ∀ x ∈ s, (∏ i ∈ t, f i x) / (∏ i ∈ t, A i) ≤
        ∑ i ∈ t, w i * (f i x / A i) ^ (w i)⁻¹ := by
      intro x hx
      rw [← Finset.prod_div_distrib]
      have hrew : ∏ i ∈ t, (f i x / A i) =
          ∏ i ∈ t, ((f i x / A i) ^ (w i)⁻¹) ^ (w i) := by
        refine Finset.prod_congr rfl fun i hi => ?_
        rw [← Real.rpow_mul (div_nonneg (hf_nonneg i hi x hx) (hA_nonneg i hi)),
          inv_mul_cancel₀ (hw_pos i hi).ne', Real.rpow_one]
      rw [hrew]
      exact Real.geom_mean_le_arith_mean_weighted t w (fun i => (f i x / A i) ^ (w i)⁻¹)
        (fun i hi => (hw_pos i hi).le) hw_sum
        (fun i hi => Real.rpow_nonneg (div_nonneg (hf_nonneg i hi x hx) (hA_nonneg i hi)) _)
    calc ∑ x ∈ s, (∏ i ∈ t, f i x) / (∏ i ∈ t, A i)
        ≤ ∑ x ∈ s, ∑ i ∈ t, w i * (f i x / A i) ^ (w i)⁻¹ := Finset.sum_le_sum hpoint
      _ = ∑ i ∈ t, w i * ∑ x ∈ s, (f i x / A i) ^ (w i)⁻¹ := by
          rw [Finset.sum_comm]; congr 1 with i; rw [Finset.mul_sum]
      _ = ∑ i ∈ t, w i * 1 := by
          refine Finset.sum_congr rfl fun i hi => ?_
          congr 1
          have hAi : A i ^ (w i)⁻¹ = ∑ x ∈ s, (f i x) ^ (w i)⁻¹ := by
            simp only [A]
            rw [← Real.rpow_mul
              (Finset.sum_nonneg (fun x hx => Real.rpow_nonneg (hf_nonneg i hi x hx) _)),
              mul_inv_cancel₀ (hw_pos i hi).ne', Real.rpow_one]
          have hsum_pos : 0 < ∑ x ∈ s, (f i x) ^ (w i)⁻¹ := by
            rw [← hAi]; exact Real.rpow_pos_of_pos (hA_pos i hi) _
          calc ∑ x ∈ s, (f i x / A i) ^ (w i)⁻¹
              = ∑ x ∈ s, (f i x) ^ (w i)⁻¹ / (A i) ^ (w i)⁻¹ := by
                refine Finset.sum_congr rfl fun x hx => ?_
                exact Real.div_rpow (hf_nonneg i hi x hx) (hA_nonneg i hi) _
            _ = (∑ x ∈ s, (f i x) ^ (w i)⁻¹) / (A i) ^ (w i)⁻¹ := (Finset.sum_div _ _ _).symm
            _ = 1 := by rw [hAi, div_self hsum_pos.ne']
      _ = 1 := by simp [hw_sum]

end

/- ==================== Section 2: Forms ==================== -/
section
open Finset Real Nat

lemma modEq_finset_prod {ι : Type*} (s : Finset ι) (f g : ι → ℕ) (d : ℕ)
    (h : ∀ i ∈ s, f i ≡ g i [MOD d]) :
    ∏ i ∈ s, f i ≡ ∏ i ∈ s, g i [MOD d] := by
  classical
  induction s using Finset.induction with
  | empty => simp [Nat.ModEq.refl]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma prod_le_prod_of_subset_ge_one {ι : Type*} [DecidableEq ι] {s t : Finset ι}
    (hst : s ⊆ t) (f : ι → ℝ) (hf_nonneg : ∀ i ∈ s, 0 ≤ f i) (hf_ge : ∀ i ∈ t \ s, 1 ≤ f i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ t, f i := by
  rw [← Finset.prod_sdiff hst]
  have h1 : ∀ u : Finset ι, (∀ i ∈ u, 1 ≤ f i) → 1 ≤ ∏ i ∈ u, f i := by
    intro u
    induction u using Finset.induction with
    | empty => intro _; simp
    | @insert a u ha ih =>
      intro hu
      rw [Finset.prod_insert ha]
      have h1a := hu a (Finset.mem_insert_self a u)
      have h1u := ih (fun i hi => hu i (Finset.mem_insert_of_mem hi))
      nlinarith
  have hge := h1 (t \ s) hf_ge
  have h0 : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg hf_nonneg
  nlinarith

/- Prime chain linear forms -/

/-- Recursive linear forms for a multiplier vector `m : Fin K → ℕ`:
`chainForm m 0 n = n`, `chainForm m (j + 1) n = m j * chainForm m j n + 1`. -/
def chainForm {K : ℕ} (m : Fin K → ℕ) : ℕ → ℕ → ℕ
  | 0, n => n
  | j + 1, n => (if h : j < K then m ⟨j, h⟩ else 1) * chainForm m j n + 1

def coeffA {K : ℕ} (m : Fin K → ℕ) : ℕ → ℕ
  | 0 => 1
  | j + 1 => (if h : j < K then m ⟨j, h⟩ else 1) * coeffA m j

def coeffB {K : ℕ} (m : Fin K → ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => (if h : j < K then m ⟨j, h⟩ else 1) * coeffB m j + 1

lemma chainForm_eq_linear {K : ℕ} (m : Fin K → ℕ) (j n : ℕ) :
    chainForm m j n = coeffA m j * n + coeffB m j := by
  induction j with
  | zero => simp [chainForm, coeffA, coeffB]
  | succ j ih =>
    simp only [chainForm, coeffA, coeffB, ih]
    ring

lemma coeffA_eq_prod {K : ℕ} (m : Fin K → ℕ) (j : ℕ) :
    coeffA m j = ∏ u ∈ range j, (if h : u < K then m ⟨u, h⟩ else 1) := by
  induction j with
  | zero => simp [coeffA]
  | succ j ih =>
    rw [coeffA, ih, Finset.prod_range_succ, mul_comm]

lemma coeffA_pos {K : ℕ} (m : Fin K → ℕ) (hm : ∀ i, 1 ≤ m i) (j : ℕ) :
    1 ≤ coeffA m j := by
  induction j with
  | zero => simp [coeffA]
  | succ j ih =>
    rw [coeffA]
    have h1 : 1 ≤ (if h : j < K then m ⟨j, h⟩ else 1) := by
      split_ifs with h
      · exact hm ⟨j, h⟩
      · exact le_rfl
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))

lemma chainForm_ge_self {K : ℕ} (m : Fin K → ℕ) (hm : ∀ i, 1 ≤ m i) (j n : ℕ) :
    n ≤ chainForm m j n := by
  rw [chainForm_eq_linear]
  have hA := coeffA_pos m hm j
  calc n = 1 * n := (one_mul n).symm
    _ ≤ coeffA m j * n := Nat.mul_le_mul_right n hA
    _ ≤ coeffA m j * n + coeffB m j := Nat.le_add_right _ _

lemma chainForm_strictMono {K : ℕ} (m : Fin K → ℕ) (hm : ∀ i, 1 ≤ m i) (j : ℕ) :
    StrictMono (chainForm m j) := by
  intro a b hab
  rw [chainForm_eq_linear, chainForm_eq_linear]
  have hA := coeffA_pos m hm j
  nlinarith

/-- Transition constants `gForm m j h` satisfying
`chainForm m h n = (∏ u ∈ Ico j h, m u) * chainForm m j n + gForm m j h`. -/
def gForm {K : ℕ} (m : Fin K → ℕ) (j : ℕ) : ℕ → ℕ
  | 0 => 0
  | h + 1 => if h < j then 0 else (if hlt : h < K then m ⟨h, hlt⟩ else 1) * gForm m j h + 1

lemma gForm_self {K : ℕ} (m : Fin K → ℕ) (j : ℕ) : gForm m j j = 0 := by
  cases j with
  | zero => rfl
  | succ j => simp [gForm]

lemma gForm_succ_eq {K : ℕ} (m : Fin K → ℕ) {j h : ℕ} (hjh : j ≤ h) :
    gForm m j (h + 1) = (if hlt : h < K then m ⟨h, hlt⟩ else 1) * gForm m j h + 1 := by
  simp [gForm, Nat.not_lt.mpr hjh]

lemma gForm_succ_self {K : ℕ} (m : Fin K → ℕ) (j : ℕ) : gForm m j (j + 1) = 1 := by
  rw [gForm_succ_eq m le_rfl, gForm_self, mul_zero, zero_add]

lemma gForm_pos {K : ℕ} (m : Fin K → ℕ) {j h : ℕ} (hjh : j < h) : 1 ≤ gForm m j h := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt hjh
  rw [show j + t + 1 = (j + t) + 1 by omega, gForm_succ_eq m (by omega)]
  omega

lemma chainForm_eq_mul_add_gForm {K : ℕ} (m : Fin K → ℕ) {j h : ℕ} (hjh : j ≤ h) (n : ℕ) :
    chainForm m h n =
      (∏ u ∈ Ico j h, (if hlt : u < K then m ⟨u, hlt⟩ else 1)) * chainForm m j n + gForm m j h := by
  induction h, hjh using Nat.le_induction with
  | base => simp [gForm_self]
  | succ h hjh ih =>
    rw [chainForm, ih, gForm_succ_eq m hjh, Finset.prod_Ico_succ_top hjh]
    ring

lemma gForm_eq_mul_add_gForm {K : ℕ} (m : Fin K → ℕ) {j l h : ℕ} (hjl : j ≤ l) (hlh : l ≤ h) :
    gForm m j h =
      (∏ u ∈ Ico l h, (if hlt : u < K then m ⟨u, hlt⟩ else 1)) * gForm m j l + gForm m l h := by
  induction h, hlh using Nat.le_induction with
  | base => simp [gForm_self]
  | succ h hlh ih =>
    rw [gForm_succ_eq m (hjl.trans hlh), ih, gForm_succ_eq m hlh, Finset.prod_Ico_succ_top hlh]
    ring

lemma gForm_congr_on_Ico {K : ℕ} {m₁ m₂ : Fin K → ℕ} {j h : ℕ}
    (hagree : ∀ u (hu : u < K), j ≤ u → u < h → m₁ ⟨u, hu⟩ = m₂ ⟨u, hu⟩) :
    gForm m₁ j h = gForm m₂ j h := by
  induction h with
  | zero => rfl
  | succ h ih =>
    simp only [gForm]
    split_ifs with hlt hK
    · rfl
    · have heq := hagree h hK (by omega) (by omega)
      rw [heq, ih (fun u hu hju huh => hagree u hu hju (by omega))]
    · rw [ih (fun u hu hju huh => hagree u hu hju (by omega))]

lemma gForm_le_pow {K : ℕ} (m : Fin K → ℕ) {j h B : ℕ} (hjh : j < h) (hK : h ≤ K)
    (hB : ∀ u (hu : u < K), j ≤ u → u < h → m ⟨u, hu⟩ ≤ B) :
    gForm m j h ≤ (B + 1) ^ (h - j - 1) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hjh
  clear hjh
  induction d with
  | zero => simp [gForm_succ_self]
  | succ d ih =>
    have hstep : gForm m j (j + (d + 1) + 1) =
        m ⟨j + d + 1, by omega⟩ * gForm m j (j + d + 1) + 1 := by
      rw [show j + (d + 1) + 1 = (j + d + 1) + 1 by omega, gForm_succ_eq m (by omega)]
      simp [show j + d + 1 < K by omega]
    have hih := ih (by omega) (fun u hu h1 h2 => hB u hu h1 (by omega))
    have hge : 1 ≤ gForm m j (j + d + 1) := gForm_pos m (by omega)
    have hmle : m ⟨j + d + 1, by omega⟩ ≤ B := hB (j + d + 1) (by omega) (by omega) (by omega)
    rw [hstep, show j + (d + 1) + 1 - j - 1 = d + 1 by omega, _root_.pow_succ']
    have h1 : m ⟨j + d + 1, by omega⟩ * gForm m j (j + d + 1) + 1 ≤
        B * gForm m j (j + d + 1) + gForm m j (j + d + 1) := by
      have := Nat.mul_le_mul_right (gForm m j (j + d + 1)) hmle
      omega
    have h2 : B * gForm m j (j + d + 1) + gForm m j (j + d + 1) =
        (B + 1) * gForm m j (j + d + 1) := by ring
    have h3 : (B + 1) * gForm m j (j + d + 1) ≤ (B + 1) * (B + 1) ^ d :=
      Nat.mul_le_mul_left _ (by simpa [show j + d + 1 - j - 1 = d by omega] using hih)
    omega

/-- Product of all `K + 1` chain forms. -/
def chainProd {K : ℕ} (m : Fin K → ℕ) (n : ℕ) : ℕ :=
  ∏ j ∈ range (K + 1), chainForm m j n

lemma chainProd_strictMono {K : ℕ} (m : Fin K → ℕ) (hm : ∀ i, 1 ≤ m i) :
    StrictMono (chainProd m) := by
  intro a b hab
  unfold chainProd
  have hle : ∀ j ∈ range (K + 1), chainForm m j a ≤ chainForm m j b :=
    fun j _ => (chainForm_strictMono m hm j hab).le
  have hlt0 : chainForm m 0 a < chainForm m 0 b := chainForm_strictMono m hm 0 hab
  have hpos : ∀ j ∈ range (K + 1), j ≠ 0 → 0 < chainForm m j b := by
    intro j _ hj
    cases j with
    | zero => exact absurd rfl hj
    | succ j => simp [chainForm]
  rw [Finset.prod_range_succ', Finset.prod_range_succ']
  have hprod_le : ∏ j ∈ range K, chainForm m (j + 1) a ≤ ∏ j ∈ range K, chainForm m (j + 1) b :=
    Finset.prod_le_prod' (fun j _ => (chainForm_strictMono m hm (j + 1) hab).le)
  have hprod_pos : 0 < ∏ j ∈ range K, chainForm m (j + 1) b :=
    Finset.prod_pos (fun j _ => by simp [chainForm])
  have h1 : (∏ j ∈ range K, chainForm m (j + 1) a) * chainForm m 0 a ≤
      (∏ j ∈ range K, chainForm m (j + 1) b) * chainForm m 0 a :=
    Nat.mul_le_mul_right _ hprod_le
  have h2 : (∏ j ∈ range K, chainForm m (j + 1) b) * chainForm m 0 a <
      (∏ j ∈ range K, chainForm m (j + 1) b) * chainForm m 0 b :=
    Nat.mul_lt_mul_of_pos_left hlt0 hprod_pos
  exact lt_of_le_of_lt h1 h2

/-- Number of roots of `chainProd m n ≡ 0 (mod p)` in `{0, ..., p - 1}`. -/
def xi {K : ℕ} (m : Fin K → ℕ) (p : ℕ) : ℕ :=
  ((range p).filter (fun n => p ∣ chainProd m n)).card

lemma xi_le_p {K : ℕ} (m : Fin K → ℕ) (p : ℕ) : xi m p ≤ p := by
  unfold xi
  exact (Finset.card_filter_le _ _).trans (by simp)

lemma xi_ge_one {K : ℕ} (m : Fin K → ℕ) {p : ℕ} (hp : 1 ≤ p) : 1 ≤ xi m p := by
  unfold xi
  refine Finset.card_pos.mpr ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
  unfold chainProd
  have h0 : 0 ∈ range (K + 1) := Finset.mem_range.mpr (by omega)
  rw [Finset.prod_eq_zero (f := fun j => chainForm m j 0) h0 rfl]
  exact dvd_zero p

lemma xi_mod_congr {K : ℕ} (m₁ m₂ : Fin K → ℕ) (p : ℕ)
    (hmod : ∀ i : Fin K, m₁ i ≡ m₂ i [MOD p]) :
    xi m₁ p = xi m₂ p := by
  unfold xi
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_range]
  refine and_congr_right fun _ => ?_
  have hform : ∀ j, chainForm m₁ j n ≡ chainForm m₂ j n [MOD p] := by
    intro j
    induction j with
    | zero => exact Nat.ModEq.refl n
    | succ j ih =>
      simp only [chainForm]
      split_ifs with h
      · exact ((hmod ⟨j, h⟩).mul ih).add_right 1
      · exact ((Nat.ModEq.refl 1).mul ih).add_right 1
  have hprod : chainProd m₁ n ≡ chainProd m₂ n [MOD p] := by
    unfold chainProd
    exact modEq_finset_prod (range (K + 1)) _ _ p (fun j _ => hform j)
  exact ⟨fun h => (Nat.modEq_zero_iff_dvd.mp (hprod.symm.trans (Nat.modEq_zero_iff_dvd.mpr h))),
    fun h => (Nat.modEq_zero_iff_dvd.mp (hprod.trans (Nat.modEq_zero_iff_dvd.mpr h)))⟩

/-- A multiplier vector is bad if some prime divides `chainProd m n` for every `n`. -/
def badVec {K : ℕ} (m : Fin K → ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ xi m p = p

lemma xi_lt_p_of_not_badVec {K : ℕ} {m : Fin K → ℕ} (hb : ¬ badVec m) {p : ℕ} (hp : p.Prime) :
    xi m p < p :=
  lt_of_le_of_ne (xi_le_p m p) (fun h => hb ⟨p, hp, h⟩)

lemma xi_le_K_add_one_of_not_badVec {K : ℕ} {m : Fin K → ℕ} (hb : ¬ badVec m)
    {p : ℕ} (hp : p.Prime) :
    xi m p ≤ K + 1 := by
  have hsub : (range p).filter (fun n => p ∣ chainProd m n) ⊆
      (range (K + 1)).biUnion (fun j => (range p).filter (fun n => p ∣ chainForm m j n)) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_biUnion] at hn ⊢
    obtain ⟨j, hj, hdvd⟩ := (hp.prime.dvd_finsetProd_iff _).mp hn.2
    exact ⟨j, Finset.mem_range.mp hj, hn.1, hdvd⟩
  have hcard1 : ∀ j ∈ range (K + 1),
      ((range p).filter (fun n => p ∣ chainForm m j n)).card ≤ 1 := by
    intro j hj
    by_cases hA : p ∣ coeffA m j
    · by_cases hB : p ∣ coeffB m j
      · exfalso
        apply hb
        refine ⟨p, hp, ?_⟩
        unfold xi
        have hall : (range p).filter (fun n => p ∣ chainProd m n) = range p := by
          rw [Finset.filter_eq_self]
          intro n _
          have hd1 : p ∣ chainForm m j n := by
            rw [chainForm_eq_linear]
            exact dvd_add (dvd_mul_of_dvd_left hA n) hB
          exact dvd_trans hd1 (Finset.dvd_prod_of_mem _ hj)
        rw [hall, Finset.card_range]
      · have hempty : (range p).filter (fun n => p ∣ chainForm m j n) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro n _ hdvd
          rw [chainForm_eq_linear] at hdvd
          exact hB ((Nat.dvd_add_right (dvd_mul_of_dvd_left hA n)).mp hdvd)
        simp [hempty]
    · rw [Finset.card_le_one]
      intro n₁ hn₁ n₂ hn₂
      simp only [Finset.mem_filter, Finset.mem_range] at hn₁ hn₂
      have h1 : (coeffA m j : ZMod p) * (n₁ : ZMod p) + (coeffB m j : ZMod p) = 0 := by
        have := (ZMod.natCast_eq_zero_iff (chainForm m j n₁) p).mpr hn₁.2
        rwa [chainForm_eq_linear, Nat.cast_add, Nat.cast_mul] at this
      have h2 : (coeffA m j : ZMod p) * (n₂ : ZMod p) + (coeffB m j : ZMod p) = 0 := by
        have := (ZMod.natCast_eq_zero_iff (chainForm m j n₂) p).mpr hn₂.2
        rwa [chainForm_eq_linear, Nat.cast_add, Nat.cast_mul] at this
      have : Fact p.Prime := ⟨hp⟩
      have hAne : (coeffA m j : ZMod p) ≠ 0 := by
        intro h0
        exact hA ((ZMod.natCast_eq_zero_iff (coeffA m j) p).mp h0)
      have hsub0 : (coeffA m j : ZMod p) * ((n₁ : ZMod p) - (n₂ : ZMod p)) = 0 := by
        linear_combination h1 - h2
      have hneq : (n₁ : ZMod p) = (n₂ : ZMod p) :=
        sub_eq_zero.mp ((mul_eq_zero.mp hsub0).resolve_left hAne)
      have hval := congrArg ZMod.val hneq
      rw [ZMod.val_natCast_of_lt hn₁.1, ZMod.val_natCast_of_lt hn₂.1] at hval
      exact hval
  calc xi m p
      ≤ ((range (K + 1)).biUnion (fun j => (range p).filter (fun n => p ∣ chainForm m j n))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ j ∈ range (K + 1), ((range p).filter (fun n => p ∣ chainForm m j n)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ range (K + 1), 1 := Finset.sum_le_sum hcard1
    _ = K + 1 := by simp

/-- Discriminant-like modulus `Nm m` whose non-divisors have `xi m p = K + 1`. -/
def Nm {K : ℕ} (m : Fin K → ℕ) : ℕ :=
  (∏ i : Fin K, m i) * ∏ j ∈ range (K + 1), ∏ h ∈ Ioc j K, gForm m j h

lemma Nm_pos {K : ℕ} (m : Fin K → ℕ) (hm : ∀ i, 1 ≤ m i) : 1 ≤ Nm m := by
  unfold Nm
  refine Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero ?_ ?_)
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => by have := hm i; omega)
  · exact Finset.prod_ne_zero_iff.mpr (fun j _ =>
      Finset.prod_ne_zero_iff.mpr (fun h hh => by
        have := gForm_pos m (Finset.mem_Ioc.mp hh).1
        omega))

lemma xi_eq_of_not_dvd_Nm {K : ℕ} (m : Fin K → ℕ) {p : ℕ} (hp : p.Prime) (hnd : ¬ p ∣ Nm m) :
    xi m p = K + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hnd_m : ¬ p ∣ ∏ i : Fin K, m i := fun h => hnd (dvd_mul_of_dvd_left h _)
  have hnd_g : ∀ j ∈ range (K + 1), ∀ h ∈ Ioc j K, ¬ p ∣ gForm m j h := by
    intro j hj h hh hd
    apply hnd
    refine dvd_mul_of_dvd_right ?_ _
    exact dvd_trans (dvd_trans hd (Finset.dvd_prod_of_mem _ hh)) (Finset.dvd_prod_of_mem _ hj)
  have hnd_A : ∀ j ≤ K, ¬ p ∣ coeffA m j := by
    intro j hj hd
    rw [coeffA_eq_prod] at hd
    obtain ⟨u, hu, hpu⟩ := (hp.prime.dvd_finsetProd_iff _).mp hd
    rw [Finset.mem_range] at hu
    have huK : u < K := by omega
    simp only [huK, dite_true] at hpu
    exact hnd_m (dvd_trans hpu (Finset.dvd_prod_of_mem _ (Finset.mem_univ (⟨u, huK⟩ : Fin K))))
  let r : Fin (K + 1) → ℕ := fun j =>
    (-(coeffB m j : ZMod p) * (coeffA m j : ZMod p)⁻¹).val
  have hr_lt : ∀ j : Fin (K + 1), r j < p := fun j => ZMod.val_lt _
  have hr_dvd : ∀ j : Fin (K + 1), p ∣ chainForm m j (r j) := by
    intro j
    rw [← ZMod.natCast_eq_zero_iff, chainForm_eq_linear, Nat.cast_add, Nat.cast_mul]
    simp only [r, ZMod.natCast_zmod_val]
    have hAne : (coeffA m j : ZMod p) ≠ 0 := fun h0 =>
      hnd_A j (Nat.lt_succ_iff.mp j.2) ((ZMod.natCast_eq_zero_iff _ p).mp h0)
    calc (coeffA m j : ZMod p) * (-(coeffB m j : ZMod p) * (coeffA m j : ZMod p)⁻¹) +
          (coeffB m j : ZMod p)
        = -(coeffB m j : ZMod p) * ((coeffA m j : ZMod p) * (coeffA m j : ZMod p)⁻¹) +
          (coeffB m j : ZMod p) := by ring
      _ = 0 := by rw [mul_inv_cancel₀ hAne]; ring
  have hr_inj : Function.Injective r := by
    have hlt_ne : ∀ (a b : Fin (K + 1)), (a : ℕ) < (b : ℕ) → r a ≠ r b := by
      intro a b hlt heq
      have h1 := hr_dvd a
      have h2 : p ∣ chainForm m b (r a) := by rw [heq]; exact hr_dvd b
      rw [chainForm_eq_mul_add_gForm m hlt.le] at h2
      have hgdvd : p ∣ gForm m a b := (Nat.dvd_add_right (dvd_mul_of_dvd_right h1 _)).mp h2
      exact hnd_g a (Finset.mem_range.mpr a.2) b
        (Finset.mem_Ioc.mpr ⟨hlt, Nat.lt_succ_iff.mp b.2⟩) hgdvd
    intro j₁ j₂ heq
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · exact hlt_ne j₁ j₂ hlt heq
    · exact hlt_ne j₂ j₁ hlt heq.symm
  have hset : (range p).filter (fun n => p ∣ chainProd m n) = Finset.univ.image r := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hnp, hdvd⟩
      obtain ⟨j, hj, hjdvd⟩ := (hp.prime.dvd_finsetProd_iff _).mp hdvd
      rw [Finset.mem_range] at hj
      refine ⟨⟨j, hj⟩, ?_⟩
      have h1 : (coeffA m j : ZMod p) * (n : ZMod p) + (coeffB m j : ZMod p) = 0 := by
        have := (ZMod.natCast_eq_zero_iff (chainForm m j n) p).mpr hjdvd
        rwa [chainForm_eq_linear, Nat.cast_add, Nat.cast_mul] at this
      have hAne : (coeffA m j : ZMod p) ≠ 0 := fun h0 =>
        hnd_A j (Nat.lt_succ_iff.mp hj) ((ZMod.natCast_eq_zero_iff _ p).mp h0)
      have hzn : (n : ZMod p) = -(coeffB m j : ZMod p) * (coeffA m j : ZMod p)⁻¹ := by
        have hmul : (coeffA m j : ZMod p) * (n : ZMod p) = -(coeffB m j : ZMod p) :=
          eq_neg_of_add_eq_zero_left h1
        calc (n : ZMod p) = (coeffA m j : ZMod p) * (n : ZMod p) * (coeffA m j : ZMod p)⁻¹ := by
              rw [mul_comm (coeffA m j : ZMod p), mul_assoc, mul_inv_cancel₀ hAne, mul_one]
          _ = -(coeffB m j : ZMod p) * (coeffA m j : ZMod p)⁻¹ := by rw [hmul]
      simp only [r, ← hzn, ZMod.val_natCast_of_lt hnp]
    · rintro ⟨j, rfl⟩
      exact ⟨hr_lt j, dvd_trans (hr_dvd j) (Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr j.2))⟩
  unfold xi
  rw [hset, Finset.card_image_of_injective _ hr_inj, Finset.card_univ, Fintype.card_fin]

open Classical in
lemma badVec_card_le {K : ℕ} (m : Fin K → ℕ) (hm : ∀ i, 1 ≤ m i) (hb : badVec m) (X Z : ℕ) :
    ((Icc 1 X).filter (fun n => ∀ j ∈ range (K + 1), (chainForm m j n).Prime)).card ≤ Z + K + 1 := by
  obtain ⟨p, hp, hxi⟩ := hb
  have hall : ∀ n, p ∣ chainProd m n := by
    intro n
    have hmem : n % p ∈ (range p).filter (fun r => p ∣ chainProd m r) := by
      have hcard : ((range p).filter (fun r => p ∣ chainProd m r)).card = (range p).card := by
        simpa [xi] using hxi
      have heq := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) hcard.ge
      rw [heq]
      exact Finset.mem_range.mpr (Nat.mod_lt n hp.pos)
    have hd1 : p ∣ chainProd m (n % p) := (Finset.mem_filter.mp hmem).2
    have hmod : ∀ j, chainForm m j (n % p) ≡ chainForm m j n [MOD p] := by
      intro j
      induction j with
      | zero => exact Nat.mod_modEq n p
      | succ j ih =>
        simp only [chainForm]
        exact ((Nat.ModEq.refl _).mul ih).add_right 1
    have hpm : chainProd m (n % p) ≡ chainProd m n [MOD p] :=
      modEq_finset_prod (range (K + 1)) _ _ p (fun j _ => hmod j)
    exact Nat.modEq_zero_iff_dvd.mp (hpm.symm.trans (Nat.modEq_zero_iff_dvd.mpr hd1))
  by_cases hpZ : p ≤ Z
  · have hsub : (Icc 1 X).filter (fun n => ∀ j ∈ range (K + 1), (chainForm m j n).Prime) ⊆
        Icc 1 Z := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      obtain ⟨j, hj, hpdvd⟩ := (hp.prime.dvd_finsetProd_iff _).mp (hall n)
      have hpr := hn.2 j hj
      have heq : p = chainForm m j n := (Nat.prime_dvd_prime_iff_eq hp hpr).mp hpdvd
      have hle : n ≤ chainForm m j n := chainForm_ge_self m hm j n
      exact ⟨hn.1.1, by omega⟩
    exact (Finset.card_le_card hsub).trans (by simp; omega)
  · have hsub : (Icc 1 X).filter (fun n => ∀ j ∈ range (K + 1), (chainForm m j n).Prime) ⊆
        (range (K + 1)).biUnion (fun j => (Icc 1 X).filter (fun n => chainForm m j n = p)) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_Icc] at hn ⊢
      obtain ⟨j, hj, hpdvd⟩ := (hp.prime.dvd_finsetProd_iff _).mp (hall n)
      have hpr := hn.2 j hj
      exact ⟨j, hj, hn.1, ((Nat.prime_dvd_prime_iff_eq hp hpr).mp hpdvd).symm⟩
    have hcard1 : ∀ j ∈ range (K + 1),
        ((Icc 1 X).filter (fun n => chainForm m j n = p)).card ≤ 1 := by
      intro j _
      rw [Finset.card_le_one]
      intro a ha b hb'
      simp only [Finset.mem_filter] at ha hb'
      exact (chainForm_strictMono m hm j).injective (ha.2.trans hb'.2.symm)
    calc ((Icc 1 X).filter (fun n => ∀ j ∈ range (K + 1), (chainForm m j n).Prime)).card
        ≤ ((range (K + 1)).biUnion (fun j => (Icc 1 X).filter (fun n => chainForm m j n = p))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ j ∈ range (K + 1), ((Icc 1 X).filter (fun n => chainForm m j n = p)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ range (K + 1), 1 := Finset.sum_le_sum hcard1
      _ = K + 1 := by simp
      _ ≤ Z + K + 1 := by omega

/- Lemma rhopm: exact average of `xi m p` over `(Fin K → ZMod p)` -/

lemma sum_xi_eq_pow_sub_pow (K p : ℕ) (hp : p.Prime) :
    ∑ m ∈ Fintype.piFinset (fun _ : Fin K => range p), xi m p =
      p ^ (K + 1) - (p - 1) ^ (K + 1) := by
  induction K with
  | zero =>
    have h1 : Fintype.piFinset (fun _ : Fin 0 => range p) = {Fin.elim0} := by
      ext m; simp only [Fintype.mem_piFinset, Finset.mem_singleton]
      exact ⟨fun _ => by ext i; exact Fin.elim0 i, fun _ i => Fin.elim0 i⟩
    rw [h1, Finset.sum_singleton, pow_one, pow_one]
    have hxi0 : xi (Fin.elim0 : Fin 0 → ℕ) p = 1 := by
      unfold xi chainProd
      have : (range p).filter (fun n => p ∣ ∏ j ∈ range 1, chainForm (Fin.elim0 : Fin 0 → ℕ) j n) = {0} := by
        ext n
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, Finset.prod_range_one,
          chainForm]
        exact ⟨fun ⟨hlt, hd⟩ => Nat.eq_zero_of_dvd_of_lt hd hlt, fun h => by rw [h]; exact ⟨hp.pos, dvd_zero p⟩⟩
      rw [this, Finset.card_singleton]
    rw [hxi0]
    have := hp.two_le; omega
  | succ K ih =>
    -- Split `m : Fin (K + 1) → ℕ` into `(m_init : Fin K → ℕ, m_last : ℕ)`
    let e : (Fin K → ℕ) × ℕ → (Fin (K + 1) → ℕ) := fun ⟨m₀, a⟩ => Fin.snoc m₀ a
    let S := Fintype.piFinset (fun _ : Fin K => range p)
    have himg : Fintype.piFinset (fun _ : Fin (K + 1) => range p) = (S ×ˢ range p).image e := by
      ext m
      simp only [Fintype.mem_piFinset, Finset.mem_image, Finset.mem_product, Finset.mem_range, S, e]
      constructor
      · intro hm
        refine ⟨⟨Fin.init m, m (Fin.last K)⟩, ⟨fun i => hm i.castSucc, hm (Fin.last K)⟩, ?_⟩
        exact Fin.snoc_init_self m
      · rintro ⟨⟨m₀, a⟩, ⟨hm₀, ha⟩, rfl⟩ i
        refine Fin.lastCases ?_ ?_ i
        · simpa using ha
        · intro j; simpa using hm₀ j
    have hinj : Set.InjOn e ↑(S ×ˢ range p) := by
      intro ⟨m₁, a₁⟩ _ ⟨m₂, a₂⟩ _ heq
      simp only [e] at heq
      have ha : a₁ = a₂ := by
        have := congr_fun heq (Fin.last K)
        simpa using this
      have hm : m₁ = m₂ := by
        ext j
        have := congr_fun heq j.castSucc
        simpa using this
      exact Prod.ext hm ha
    rw [himg, Finset.sum_image hinj, Finset.sum_product]
    have hinner : ∀ m₀ ∈ S,
        ∑ a ∈ range p, xi (Fin.snoc m₀ a) p = p + (p - 1) * xi m₀ p := by
      intro m₀ _
      have hform_eq : ∀ j ≤ K, ∀ a n, chainForm (Fin.snoc m₀ a) j n = chainForm m₀ j n := by
        intro j hj a n
        induction j with
        | zero => rfl
        | succ j ihj =>
          simp only [chainForm, show j < K + 1 by omega, show j < K by omega, dite_true]
          rw [ihj (by omega)]
          have : (⟨j, by omega⟩ : Fin (K + 1)) = (⟨j, by omega⟩ : Fin K).castSucc := rfl
          rw [this, Fin.snoc_castSucc]
      have hprod_eq : ∀ a n,
          chainProd (Fin.snoc m₀ a) n =
            chainProd m₀ n * (a * chainForm m₀ K n + 1) := by
        intro a n
        unfold chainProd
        rw [Finset.prod_range_succ]
        congr 1
        · exact Finset.prod_congr rfl fun j hj =>
            hform_eq j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) a n
        · simp only [chainForm, Nat.lt_succ_self, dite_true]
          rw [hform_eq K le_rfl a n]
          have : (⟨K, Nat.lt_succ_self K⟩ : Fin (K + 1)) = Fin.last K := rfl
          rw [this, Fin.snoc_last]
      -- Swap sum over `a ∈ range p` and `n ∈ range p`
      have hswap : ∑ a ∈ range p, xi (Fin.snoc m₀ a) p =
          ∑ n ∈ range p, ((range p).filter (fun a => p ∣ chainProd (Fin.snoc m₀ a) n)).card := by
        simp only [xi, Finset.card_filter]
        rw [Finset.sum_comm]
      rw [hswap]
      have hsplit : ∀ n ∈ range p,
          ((range p).filter (fun a => p ∣ chainProd (Fin.snoc m₀ a) n)).card =
            if p ∣ chainProd m₀ n then p else 1 := by
        intro n _
        split_ifs with hdvd
        · have hall : (range p).filter (fun a => p ∣ chainProd (Fin.snoc m₀ a) n) = range p := by
            rw [Finset.filter_eq_self]
            intro a _
            rw [hprod_eq]
            exact dvd_mul_of_dvd_left hdvd _
          rw [hall, Finset.card_range]
        · have hndK : ¬ p ∣ chainForm m₀ K n := fun h =>
            hdvd (dvd_trans h (Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (Nat.lt_succ_self K))))
          have : Fact p.Prime := ⟨hp⟩
          have hcne : (chainForm m₀ K n : ZMod p) ≠ 0 := fun h0 =>
            hndK ((ZMod.natCast_eq_zero_iff _ p).mp h0)
          let a₀ : ℕ := (-(1 : ZMod p) * (chainForm m₀ K n : ZMod p)⁻¹).val
          have hunique : (range p).filter (fun a => p ∣ chainProd (Fin.snoc m₀ a) n) = {a₀} := by
            ext a
            simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
            constructor
            · rintro ⟨hap, hpd⟩
              rw [hprod_eq] at hpd
              have h2 : p ∣ a * chainForm m₀ K n + 1 := (hp.dvd_mul.mp hpd).resolve_left hdvd
              have hz : (a : ZMod p) * (chainForm m₀ K n : ZMod p) + 1 = 0 := by
                have := (ZMod.natCast_eq_zero_iff _ p).mpr h2
                simpa [Nat.cast_add, Nat.cast_mul] using this
              have hza : (a : ZMod p) = -(1 : ZMod p) * (chainForm m₀ K n : ZMod p)⁻¹ := by
                have hm : (a : ZMod p) * (chainForm m₀ K n : ZMod p) = -1 :=
                  eq_neg_of_add_eq_zero_left hz
                calc (a : ZMod p) = (a : ZMod p) * (chainForm m₀ K n : ZMod p) *
                        (chainForm m₀ K n : ZMod p)⁻¹ := by
                      rw [mul_assoc, mul_inv_cancel₀ hcne, mul_one]
                  _ = -(1 : ZMod p) * (chainForm m₀ K n : ZMod p)⁻¹ := by rw [hm]
              simp only [a₀, ← hza, ZMod.val_natCast_of_lt hap]
            · rintro rfl
              refine ⟨ZMod.val_lt _, ?_⟩
              rw [hprod_eq]
              refine dvd_mul_of_dvd_right ?_ _
              rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
              simp only [a₀, ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hcne, mul_one]
              ring
          rw [hunique, Finset.card_singleton]
      rw [Finset.sum_congr rfl hsplit]
      have hcard_sum : ∑ n ∈ range p, (if p ∣ chainProd m₀ n then p else 1) =
          p * xi m₀ p + (p - xi m₀ p) := by
        rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, mul_one]
        have hcomp : ((range p).filter (fun n => ¬ p ∣ chainProd m₀ n)).card = p - xi m₀ p := by
          have hdisj : Disjoint ((range p).filter (fun n => p ∣ chainProd m₀ n))
              ((range p).filter (fun n => ¬ p ∣ chainProd m₀ n)) := by
            rw [Finset.disjoint_left]; intro n h1 h2
            exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
          have hunion : (range p).filter (fun n => p ∣ chainProd m₀ n) ∪
              (range p).filter (fun n => ¬ p ∣ chainProd m₀ n) = range p := by
            ext n; simp only [Finset.mem_union, Finset.mem_filter]; tauto
          have hadd : ((range p).filter (fun n => p ∣ chainProd m₀ n)).card +
              ((range p).filter (fun n => ¬ p ∣ chainProd m₀ n)).card = p := by
            rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_range]
          unfold xi; omega
        rw [hcomp]; unfold xi; ring
      rw [hcard_sum]
      have hxi_le : xi m₀ p ≤ p := xi_le_p m₀ p
      have hp1 : 1 ≤ p := hp.one_le
      zify [hxi_le, hp1]; ring
    rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
      ← Finset.mul_sum, ih]
    have hScard : S.card = p ^ K := by
      simp [S, Fintype.card_piFinset]
    rw [hScard]
    have hp1 : 1 ≤ p := hp.one_le
    have hpow_le : (p - 1) ^ (K + 1) ≤ p ^ (K + 1) := Nat.pow_le_pow_left (by omega) _
    have hpow_le2 : (p - 1) ^ (K + 2) ≤ p ^ (K + 2) := Nat.pow_le_pow_left (by omega) _
    zify [hp1, hpow_le, hpow_le2]
    ring

/- Singular series definition and global upper bound (`singupper`) -/

def LParam (K : ℕ) : ℕ := Nat.clog 2 (K + 1) + 4

def rParam (K : ℕ) : ℕ := 4 * (K + 1) ^ 2 * LParam K

/-- Finite-product singular series matching `∏_{p ∈ Nm(m).primeFactors ∪ primes ≤ rParam K}`. -/
noncomputable def singSeries {K : ℕ} (m : Fin K → ℕ) : ℝ := by
  classical
  exact if badVec m then 0
  else ∏ p ∈ (Nm m).primeFactors ∪ (rParam K + 1).primesBelow,
    (1 - (xi m p : ℝ) / p) * (1 - 1 / (p : ℝ))⁻¹ ^ (K + 1)

lemma singSeries_nonneg {K : ℕ} (m : Fin K → ℕ) : 0 ≤ singSeries m := by
  classical
  unfold singSeries
  split_ifs with hb
  · exact le_rfl
  · refine Finset.prod_nonneg fun p hp => ?_
    have hp_pr : p.Prime := by
      rcases Finset.mem_union.mp hp with h1 | h2
      · exact Nat.prime_of_mem_primeFactors h1
      · exact Nat.prime_of_mem_primesBelow h2
    have hxi : xi m p < p := xi_lt_p_of_not_badVec hb hp_pr
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
    have h1 : 0 ≤ 1 - (xi m p : ℝ) / p := by
      rw [sub_nonneg, div_le_one hp_pos]; exact_mod_cast hxi.le
    have h2 : 0 < 1 - 1 / (p : ℝ) := by
      rw [sub_pos, div_lt_one hp_pos]; exact_mod_cast hp_pr.one_lt
    positivity

lemma prod_one_sub_inv_primeFactors_le {N : ℕ} (hN : 2 ≤ N) :
    ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℝ))⁻¹ ≤
      Real.exp (16 * Real.log (Real.log (Real.log N + 2) + 2) + 36) := by
  let B : ℝ := Real.log N + 2
  have hB2 : 2 ≤ B := by
    have : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    linarith
  let S1 := N.primeFactors.filter (fun p => p ≤ ⌊B⌋₊)
  let S2 := N.primeFactors.filter (fun p => ⌊B⌋₊ < p)
  have hunion : N.primeFactors = S1 ∪ S2 := by
    ext p; simp only [S1, S2, Finset.mem_union, Finset.mem_filter]; constructor
    · intro hp; by_cases h : p ≤ ⌊B⌋₊ <;> [exact Or.inl ⟨hp, h⟩; exact Or.inr ⟨hp, by omega⟩]
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
  have hdisj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]; intro p h1 h2
    simp only [S1, S2, Finset.mem_filter] at h1 h2; omega
  rw [hunion, Finset.prod_union hdisj]
  have hS1 : ∏ p ∈ S1, (1 - 1 / (p : ℝ))⁻¹ ≤
      Real.exp (16 * Real.log (Real.log B + 2) + 32) := by
    have hsub : S1 ⊆ (⌊B⌋₊ + 1).primesBelow := by
      intro p hp
      simp only [S1, Finset.mem_filter, Nat.mem_primeFactors, Nat.mem_primesBelow] at hp ⊢
      exact ⟨Nat.lt_succ_of_le hp.2, hp.1.1⟩
    calc ∏ p ∈ S1, (1 - 1 / (p : ℝ))⁻¹
        ≤ ∏ p ∈ (⌊B⌋₊ + 1).primesBelow, (1 - 1 / (p : ℝ))⁻¹ :=
          prod_le_prod_of_subset_ge_one hsub _ (fun p hp => by
            have hp_pr := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
            have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
            have : 0 < 1 - 1 / (p : ℝ) := by
              rw [sub_pos, div_lt_one hp_pos]; exact_mod_cast hp_pr.one_lt
            positivity) (fun p hp => by
            have hp_pr := Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hp).1
            have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
            have hlt1 : 1 - 1 / (p : ℝ) ≤ 1 := by linarith [show (0 : ℝ) ≤ 1 / p by positivity]
            have hpos1 : 0 < 1 - 1 / (p : ℝ) := by
              rw [sub_pos, div_lt_one hp_pos]; exact_mod_cast hp_pr.one_lt
            exact (one_le_inv₀ hpos1).mpr hlt1)
      _ ≤ Real.exp (16 * Real.log (Real.log B + 2) + 32) := prod_one_sub_inv_le hB2
  have hS2_card : (S2.card : ℝ) ≤ 2 * Real.log N := by
    have h2pow : 2 ^ S2.card ≤ N := by
      calc 2 ^ S2.card = ∏ _p ∈ S2, 2 := by simp
        _ ≤ ∏ p ∈ S2, p := Finset.prod_le_prod' (fun p hp =>
            (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).two_le)
        _ ≤ ∏ p ∈ N.primeFactors, p :=
            Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _)
              (fun p hp _ => (Nat.prime_of_mem_primeFactors hp).one_le)
        _ ≤ N := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd N)
    have hlog : (S2.card : ℝ) * Real.log 2 ≤ Real.log N := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) (by exact_mod_cast h2pow)
    have hl2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    nlinarith
  have hS2 : ∏ p ∈ S2, (1 - 1 / (p : ℝ))⁻¹ ≤ Real.exp 4 := by
    have hterm : ∀ p ∈ S2, (1 - 1 / (p : ℝ))⁻¹ ≤ Real.exp (2 / B) := by
      intro p hp
      simp only [S2, Finset.mem_filter] at hp
      have hp_pr := Nat.prime_of_mem_primeFactors hp.1
      have hp2 : 2 ≤ p := hp_pr.two_le
      have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
      have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
        have h2p : (2 : ℝ) ≤ p := by exact_mod_cast hp2
        linarith
      have h1 : (1 - 1 / (p : ℝ))⁻¹ = 1 / ((p : ℝ) - 1) + 1 := by field_simp; ring
      have h2 : 1 / ((p : ℝ) - 1) ≤ 2 / (p : ℝ) := by
        rw [div_le_div_iff₀ hp1 hp_pos]
        have h2p : (2 : ℝ) ≤ p := by exact_mod_cast hp2
        linarith
      have hBp : B ≤ (p : ℝ) := by
        have : ⌊B⌋₊ + 1 ≤ p := hp.2
        have hlt := Nat.lt_floor_add_one B
        have hcast : ((⌊B⌋₊ + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast this
        push_cast at hcast; linarith
      have h3 : 2 / (p : ℝ) ≤ 2 / B := div_le_div_of_nonneg_left (by norm_num) (by linarith) hBp
      rw [h1]
      exact (Real.add_one_le_exp _).trans (Real.exp_le_exp.mpr (h2.trans h3))
    calc ∏ p ∈ S2, (1 - 1 / (p : ℝ))⁻¹
        ≤ ∏ _p ∈ S2, Real.exp (2 / B) :=
          Finset.prod_le_prod (fun p hp => by
            have hp_pr := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
            have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
            have : 0 < 1 - 1 / (p : ℝ) := by
              rw [sub_pos, div_lt_one hp_pos]; exact_mod_cast hp_pr.one_lt
            positivity) hterm
      _ = Real.exp ((S2.card : ℝ) * (2 / B)) := by
          rw [Finset.prod_const, ← Real.exp_nat_mul]
      _ ≤ Real.exp 4 := by
          apply Real.exp_le_exp.mpr
          have hBpos : 0 < B := by linarith
          calc (S2.card : ℝ) * (2 / B) ≤ (2 * Real.log N) * (2 / B) := by gcongr
            _ = 4 * Real.log N / B := by ring
            _ ≤ 4 * B / B := by
                gcongr; simp only [B]; linarith
            _ = 4 := by field_simp
  calc (∏ p ∈ S1, (1 - 1 / (p : ℝ))⁻¹) * (∏ p ∈ S2, (1 - 1 / (p : ℝ))⁻¹)
      ≤ Real.exp (16 * Real.log (Real.log B + 2) + 32) * Real.exp 4 :=
        mul_le_mul hS1 hS2 (Finset.prod_nonneg (fun p hp => by
          have hp_pr := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
          have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
          have : 0 < 1 - 1 / (p : ℝ) := by
            rw [sub_pos, div_lt_one hp_pos]; exact_mod_cast hp_pr.one_lt
          positivity)) (by positivity)
    _ = Real.exp (16 * Real.log (Real.log (Real.log N + 2) + 2) + 36) := by
        rw [← Real.exp_add]; congr 1; ring

lemma singSeries_upper {K : ℕ} (m : Fin K → ℕ) (hm : ∀ i, 1 ≤ m i)
    {M : ℝ} (hM : 2 ≤ M) (hprod : (∏ i : Fin K, (m i : ℝ)) ≤ M) :
    singSeries m ≤
      (Real.exp (16 * Real.log (Real.log ((K + 1 : ℝ) ^ 3 * Real.log (2 * M) + 2) + 2) + 36)) ^ K := by
  classical
  unfold singSeries
  split_ifs with hb
  · positivity
  · have hstep1 : ∏ p ∈ (Nm m).primeFactors ∪ (rParam K + 1).primesBelow,
        (1 - (xi m p : ℝ) / p) * (1 - 1 / (p : ℝ))⁻¹ ^ (K + 1) ≤
        ∏ p ∈ (Nm m).primeFactors, (1 - 1 / (p : ℝ))⁻¹ ^ K := by
      have hsplit : (Nm m).primeFactors ∪ (rParam K + 1).primesBelow =
          (Nm m).primeFactors ∪ ((rParam K + 1).primesBelow \ (Nm m).primeFactors) := by
        ext p; by_cases h : p ∈ (Nm m).primeFactors <;> simp [h]
      rw [hsplit, Finset.prod_union disjoint_sdiff_self_right]
      have h1 : ∏ p ∈ (Nm m).primeFactors,
          (1 - (xi m p : ℝ) / p) * (1 - 1 / (p : ℝ))⁻¹ ^ (K + 1) ≤
          ∏ p ∈ (Nm m).primeFactors, (1 - 1 / (p : ℝ))⁻¹ ^ K := by
        apply Finset.prod_le_prod
        · intro p hp
          have hp_pr := Nat.prime_of_mem_primeFactors hp
          have hxi := xi_lt_p_of_not_badVec hb hp_pr
          have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
          have : 0 ≤ 1 - (xi m p : ℝ) / p := by
            rw [sub_nonneg, div_le_one hp_pos]; exact_mod_cast hxi.le
          have : 0 < 1 - 1 / (p : ℝ) := by
            rw [sub_pos, div_lt_one hp_pos]; exact_mod_cast hp_pr.one_lt
          positivity
        · intro p hp
          have hp_pr := Nat.prime_of_mem_primeFactors hp
          have hxi1 : 1 ≤ xi m p := xi_ge_one m hp_pr.one_le
          have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
          have h1p : 0 < 1 - 1 / (p : ℝ) := by
            rw [sub_pos, div_lt_one hp_pos]; exact_mod_cast hp_pr.one_lt
          calc (1 - (xi m p : ℝ) / p) * (1 - 1 / (p : ℝ))⁻¹ ^ (K + 1)
              ≤ (1 - 1 / (p : ℝ)) * (1 - 1 / (p : ℝ))⁻¹ ^ (K + 1) := by
                gcongr; exact_mod_cast hxi1
            _ = (1 - 1 / (p : ℝ))⁻¹ ^ K := by
                rw [_root_.pow_succ', ← mul_assoc, mul_inv_cancel₀ h1p.ne', one_mul]
      have h2 : ∏ p ∈ (rParam K + 1).primesBelow \ (Nm m).primeFactors,
          (1 - (xi m p : ℝ) / p) * (1 - 1 / (p : ℝ))⁻¹ ^ (K + 1) ≤ 1 := by
        refine Finset.prod_le_one (fun p hp => ?_) (fun p hp => ?_)
        · have hp_pr := Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hp).1
          have hxi := xi_lt_p_of_not_badVec hb hp_pr
          have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
          have : 0 ≤ 1 - (xi m p : ℝ) / p := by
            rw [sub_nonneg, div_le_one hp_pos]; exact_mod_cast hxi.le
          have : 0 < 1 - 1 / (p : ℝ) := by
            rw [sub_pos, div_lt_one hp_pos]; exact_mod_cast hp_pr.one_lt
          positivity
        · rw [Finset.mem_sdiff] at hp
          have hp_pr := Nat.prime_of_mem_primesBelow hp.1
          have hnd : ¬ p ∣ Nm m := fun hd =>
            hp.2 (Nat.mem_primeFactors.mpr ⟨hp_pr, hd, Nat.one_le_iff_ne_zero.mp (Nm_pos m hm)⟩)
          have hxeq : xi m p = K + 1 := xi_eq_of_not_dvd_Nm m hp_pr hnd
          have hxlt : xi m p < p := xi_lt_p_of_not_badVec hb hp_pr
          rw [hxeq]
          exact euler_factor_le_one (by omega)
      calc _ ≤ (∏ p ∈ (Nm m).primeFactors, (1 - 1 / (p : ℝ))⁻¹ ^ K) * 1 :=
            mul_le_mul h1 h2 (Finset.prod_nonneg (fun p hp => by
              have hp_pr := Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hp).1
              have hxi := xi_lt_p_of_not_badVec hb hp_pr
              have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
              have : 0 ≤ 1 - (xi m p : ℝ) / p := by
                rw [sub_nonneg, div_le_one hp_pos]; exact_mod_cast hxi.le
              have : 0 < 1 - 1 / (p : ℝ) := by
                rw [sub_pos, div_lt_one hp_pos]; exact_mod_cast hp_pr.one_lt
              positivity)) (Finset.prod_nonneg (fun p hp => by
              have hp_pr := Nat.prime_of_mem_primeFactors hp
              have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
              have : 0 < 1 - 1 / (p : ℝ) := by
                rw [sub_pos, div_lt_one hp_pos]; exact_mod_cast hp_pr.one_lt
              positivity))
        _ = _ := mul_one _
    rw [Finset.prod_pow] at hstep1
    refine hstep1.trans ?_
    refine pow_le_pow_left₀ (Finset.prod_nonneg fun p hp => by
      have hp_pr := Nat.prime_of_mem_primeFactors hp
      have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
      have : 0 < 1 - 1 / (p : ℝ) := by
        rw [sub_pos, div_lt_one hp_pos]; exact_mod_cast hp_pr.one_lt
      positivity) ?_ K
    by_cases hNm2 : 2 ≤ Nm m
    · refine (prod_one_sub_inv_primeFactors_le hNm2).trans ?_
      apply Real.exp_le_exp.mpr
      have hNm_le : (Nm m : ℝ) ≤ (2 * M) ^ ((K + 1) ^ 3) := by
        have hmi_le : ∀ i : Fin K, (m i : ℝ) ≤ M := fun i => by
          have h1 : (m i : ℝ) = ∏ j ∈ ({i} : Finset (Fin K)), (m j : ℝ) := by simp
          calc (m i : ℝ)
              = ∏ j ∈ ({i} : Finset (Fin K)), (m j : ℝ) := h1
            _ ≤ ∏ j ∈ (Finset.univ : Finset (Fin K)), (m j : ℝ) :=
                prod_le_prod_of_subset_ge_one (Finset.singleton_subset_iff.mpr (Finset.mem_univ i)) _
                  (fun j _ => by positivity) (fun j _ => by exact_mod_cast hm j)
            _ ≤ M := hprod
        have hgle : ∀ j ∈ range (K + 1), ∀ h ∈ Ioc j K, (gForm m j h : ℝ) ≤ (2 * M) ^ K := by
          intro j hj h hh
          rw [Finset.mem_Ioc] at hh
          have hB : ∀ u (hu : u < K), j ≤ u → u < h → m ⟨u, hu⟩ ≤ ⌊M⌋₊ := fun u hu _ _ =>
            Nat.le_floor (hmi_le ⟨u, hu⟩)
          have hg := gForm_le_pow m hh.1 hh.2 hB
          calc (gForm m j h : ℝ)
              ≤ ((⌊M⌋₊ + 1 : ℕ) : ℝ) ^ (h - j - 1) := by exact_mod_cast hg
            _ ≤ (2 * M) ^ (h - j - 1) := by
                gcongr
                push_cast
                linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ M)]
            _ ≤ (2 * M) ^ K := pow_le_pow_right₀ (by linarith) (by omega)
        unfold Nm
        push_cast
        calc (∏ i : Fin K, (m i : ℝ)) *
              ∏ j ∈ range (K + 1), ∏ h ∈ Ioc j K, (gForm m j h : ℝ)
            ≤ M * ∏ j ∈ range (K + 1), ∏ _h ∈ Ioc j K, (2 * M) ^ K := by
              gcongr with j hj h hh
              exact hgle j hj h hh
          _ ≤ (2 * M) ^ 1 * ∏ j ∈ range (K + 1), ((2 * M) ^ K) ^ K := by
              gcongr with j hj
              · rw [pow_one]; linarith
              · rw [Finset.prod_const]
                refine pow_le_pow_right₀ (one_le_pow₀ (by linarith)) ?_
                simp [Nat.card_Ioc]
          _ = (2 * M) ^ (1 + (K + 1) * K * K) := by
              rw [Finset.prod_const, Finset.card_range, ← pow_mul, ← pow_mul, ← pow_add]
              ring_nf
          _ ≤ (2 * M) ^ ((K + 1) ^ 3) := by
              refine pow_le_pow_right₀ (by linarith) ?_
              have : (K + 1) ^ 3 = K ^ 3 + 3 * K ^ 2 + 3 * K + 1 := by ring
              have : 1 + (K + 1) * K * K = K ^ 3 + K ^ 2 + 1 := by ring
              omega
      have hlogNm : Real.log (Nm m : ℝ) ≤ (K + 1 : ℝ) ^ 3 * Real.log (2 * M) := by
        calc Real.log (Nm m : ℝ) ≤ Real.log ((2 * M) ^ ((K + 1) ^ 3)) :=
              Real.log_le_log (by exact_mod_cast (Nm_pos m hm)) hNm_le
          _ = ((K + 1) ^ 3 : ℕ) * Real.log (2 * M) := Real.log_pow _ _
          _ = (K + 1 : ℝ) ^ 3 * Real.log (2 * M) := by push_cast; ring
      have h1ge : 1 ≤ Real.log (Nm m : ℝ) + 2 := by
        have := Real.log_nonneg (show (1 : ℝ) ≤ Nm m by exact_mod_cast (Nm_pos m hm))
        linarith
      have h1 : 0 < Real.log (Nm m : ℝ) + 2 := by linarith
      have h2 : 0 < Real.log (Real.log (Nm m : ℝ) + 2) + 2 := by
        have := Real.log_nonneg h1ge
        linarith
      have hll : Real.log (Real.log (Nm m : ℝ) + 2) ≤
          Real.log ((K + 1 : ℝ) ^ 3 * Real.log (2 * M) + 2) :=
        Real.log_le_log h1 (by linarith)
      have hlll : Real.log (Real.log (Real.log (Nm m : ℝ) + 2) + 2) ≤
          Real.log (Real.log ((K + 1 : ℝ) ^ 3 * Real.log (2 * M) + 2) + 2) :=
        Real.log_le_log h2 (by linarith)
      linarith
    · have hNm1 : Nm m = 1 := by have := Nm_pos m hm; omega
      simp [hNm1]
      have : 0 ≤ Real.log (Real.log ((K + 1 : ℝ) ^ 3 * Real.log (2 * M) + 2) + 2) :=
        Real.log_nonneg (by
          have : 0 ≤ Real.log ((K + 1 : ℝ) ^ 3 * Real.log (2 * M) + 2) :=
            Real.log_nonneg (by
              have : 0 ≤ Real.log (2 * M) := Real.log_nonneg (by linarith)
              have : (0 : ℝ) ≤ (K + 1 : ℝ) ^ 3 := by positivity
              nlinarith)
          linarith)
      linarith

end

/- ==================== Section 3: Sieve ==================== -/
section
open Finset Real Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/- Residue class counting and CRT multiplicativity for `chainProd` -/

lemma card_Icc_modEq_sub_div_le (X d r : ℕ) (hd : 1 ≤ d) (hr : r < d) :
    |(((Icc 1 X).filter (fun n => n % d = r)).card : ℝ) - (X : ℝ) / d| ≤ 1 := by
  let q := X / d
  let rem := X % d
  have hX : X = q * d + rem := (Nat.div_add_mod X d).symm.trans (by ring)
  have hrem_lt : rem < d := Nat.mod_lt X (by omega)
  have hblock : ∀ k : ℕ, ((Icc (k * d + 1) ((k + 1) * d)).filter (fun n => n % d = r)).card = 1 := by
    intro k
    let target := if r = 0 then (k + 1) * d else k * d + r
    have hset : (Icc (k * d + 1) ((k + 1) * d)).filter (fun n => n % d = r) = {target} := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨h1, h2⟩, hmod⟩
        have hnd : n = (n / d) * d + r := by
          have := (Nat.div_add_mod n d).symm
          rw [hmod] at this
          linarith
        simp only [target]
        split_ifs with hr0
        · subst hr0
          have hdiv : n / d = k + 1 := by nlinarith
          nlinarith
        · have hdiv : n / d = k := by
            apply le_antisymm
            · by_contra hgt
              have hge : (k + 1) * d ≤ n / d * d := Nat.mul_le_mul_right d (by omega)
              omega
            · by_contra hlt
              have hle : (n / d + 1) * d ≤ k * d := Nat.mul_le_mul_right d (by omega)
              have hmul : (n / d + 1) * d = n / d * d + d := by ring
              omega
          nlinarith
      · rintro rfl
        simp only [target]
        split_ifs with hr0
        · subst hr0
          refine ⟨⟨by nlinarith, le_rfl⟩, Nat.mul_mod_left (k + 1) d⟩
        · refine ⟨⟨by omega, by nlinarith⟩, ?_⟩
          rw [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hr]
    rw [hset, Finset.card_singleton]
  have hqd : ∀ m : ℕ, ((Icc 1 (m * d)).filter (fun n => n % d = r)).card = m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hmd : m * d ≤ (m + 1) * d := Nat.mul_le_mul_right d (Nat.le_succ m)
      have hunion : Icc 1 ((m + 1) * d) = Icc 1 (m * d) ∪ Icc (m * d + 1) ((m + 1) * d) := by
        ext n; simp only [Finset.mem_union, Finset.mem_Icc]; omega
      have hdisj : Disjoint (Icc 1 (m * d)) (Icc (m * d + 1) ((m + 1) * d)) := by
        rw [Finset.disjoint_left]; intro n h1 h2; rw [Finset.mem_Icc] at h1 h2; omega
      rw [hunion, Finset.filter_union, Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter hdisj), ih, hblock m]
  have htail : ((Icc (q * d + 1) X).filter (fun n => n % d = r)).card ≤ 1 := by
    have hsub : (Icc (q * d + 1) X).filter (fun n => n % d = r) ⊆
        (Icc (q * d + 1) ((q + 1) * d)).filter (fun n => n % d = r) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      exact ⟨⟨hn.1.1, by nlinarith⟩, hn.2⟩
    exact (Finset.card_le_card hsub).trans (hblock q).le
  have hsplit : Icc 1 X = Icc 1 (q * d) ∪ Icc (q * d + 1) X := by
    ext n; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Icc 1 (q * d)) (Icc (q * d + 1) X) := by
    rw [Finset.disjoint_left]; intro n h1 h2; rw [Finset.mem_Icc] at h1 h2; omega
  have hcard_eq : ((Icc 1 X).filter (fun n => n % d = r)).card =
      q + ((Icc (q * d + 1) X).filter (fun n => n % d = r)).card := by
    rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter hdisj), hqd q]
  have hq_le : (q : ℝ) ≤ (X : ℝ) / d := by
    rw [le_div_iff₀ (by exact_mod_cast (show 0 < d by omega))]
    exact_mod_cast (show q * d ≤ X by omega)
  have hq_lt : (X : ℝ) / d ≤ (q : ℝ) + 1 := by
    rw [div_le_iff₀ (by exact_mod_cast (show 0 < d by omega))]
    have : X ≤ (q + 1) * d := by nlinarith
    exact_mod_cast this
  rw [hcard_eq, Nat.cast_add, abs_le]
  have ht0 : (0 : ℝ) ≤ ((Icc (q * d + 1) X).filter (fun n => n % d = r)).card := Nat.cast_nonneg _
  have ht1 : (((Icc (q * d + 1) X).filter (fun n => n % d = r)).card : ℝ) ≤ 1 := by
    exact_mod_cast htail
  constructor <;> linarith

lemma chainProd_modEq {K : ℕ} (m : Fin K → ℕ) {a b d : ℕ} (h : a ≡ b [MOD d]) :
    chainProd m a ≡ chainProd m b [MOD d] := by
  have hform : ∀ j, chainForm m j a ≡ chainForm m j b [MOD d] := by
    intro j
    induction j with
    | zero => exact h
    | succ j ih =>
      simp only [chainForm]
      exact ((Nat.ModEq.refl _).mul ih).add_right 1
  unfold chainProd
  exact modEq_finset_prod (range (K + 1)) _ _ d (fun j _ => hform j)

def xiD {K : ℕ} (m : Fin K → ℕ) (d : ℕ) : ℕ :=
  ((range d).filter (fun n => d ∣ chainProd m n)).card

lemma xiD_one {K : ℕ} (m : Fin K → ℕ) : xiD m 1 = 1 := by
  unfold xiD
  have : (range 1).filter (fun n => 1 ∣ chainProd m n) = {0} := by
    ext n; simp
  rw [this, Finset.card_singleton]

lemma xiD_mul_of_coprime {K : ℕ} (m : Fin K → ℕ) {d₁ d₂ : ℕ} (hcop : d₁.Coprime d₂) :
    xiD m (d₁ * d₂) = xiD m d₁ * xiD m d₂ := by
  unfold xiD
  rw [← Finset.card_product]
  refine Finset.card_bij (fun n _ => (n % d₁, n % d₂)) ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_product] at hn ⊢
    have hd1 : 0 < d₁ := by
      rcases Nat.eq_zero_or_pos d₁ with rfl | h
      · simp at hn
      · exact h
    have hd2 : 0 < d₂ := by
      rcases Nat.eq_zero_or_pos d₂ with rfl | h
      · simp at hn
      · exact h
    have hm1 : chainProd m (n % d₁) ≡ chainProd m n [MOD d₁] :=
      chainProd_modEq m (Nat.mod_modEq n d₁)
    have hm2 : chainProd m (n % d₂) ≡ chainProd m n [MOD d₂] :=
      chainProd_modEq m (Nat.mod_modEq n d₂)
    exact ⟨⟨Nat.mod_lt n hd1,
        Nat.modEq_zero_iff_dvd.mp (hm1.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_of_mul_right_dvd hn.2)))⟩,
      ⟨Nat.mod_lt n hd2,
        Nat.modEq_zero_iff_dvd.mp (hm2.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_of_mul_left_dvd hn.2)))⟩⟩
  · intro a ha b hb heq
    simp only [Finset.mem_filter, Finset.mem_range] at ha hb
    have h1 : a ≡ b [MOD d₁] := congrArg Prod.fst heq
    have h2 : a ≡ b [MOD d₂] := congrArg Prod.snd heq
    have h12 : a ≡ b [MOD d₁ * d₂] := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h1, h2⟩
    rwa [Nat.ModEq, Nat.mod_eq_of_lt ha.1, Nat.mod_eq_of_lt hb.1] at h12
  · intro ⟨r₁, r₂⟩ hr
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hr
    obtain ⟨⟨hr1, hd1⟩, ⟨hr2, hd2⟩⟩ := hr
    have hpos : 0 < d₁ * d₂ := Nat.mul_pos (by omega) (by omega)
    let cr := Nat.chineseRemainder hcop r₁ r₂
    let n := cr.1 % (d₁ * d₂)
    refine ⟨n, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.mod_lt _ hpos, ?_⟩
      have hmod1 : n ≡ r₁ [MOD d₁] :=
        (Nat.ModEq.of_mul_right d₂ (Nat.mod_modEq cr.1 (d₁ * d₂))).trans cr.2.1
      have hmod2 : n ≡ r₂ [MOD d₂] :=
        (Nat.ModEq.of_mul_left d₁ (Nat.mod_modEq cr.1 (d₁ * d₂))).trans cr.2.2
      have hdv1 : d₁ ∣ chainProd m n :=
        Nat.modEq_zero_iff_dvd.mp ((chainProd_modEq m hmod1).trans (Nat.modEq_zero_iff_dvd.mpr hd1))
      have hdv2 : d₂ ∣ chainProd m n :=
        Nat.modEq_zero_iff_dvd.mp ((chainProd_modEq m hmod2).trans (Nat.modEq_zero_iff_dvd.mpr hd2))
      exact hcop.mul_dvd_of_dvd_of_dvd hdv1 hdv2
    · have hmod1 : n ≡ r₁ [MOD d₁] :=
        (Nat.ModEq.of_mul_right d₂ (Nat.mod_modEq cr.1 (d₁ * d₂))).trans cr.2.1
      have hmod2 : n ≡ r₂ [MOD d₂] :=
        (Nat.ModEq.of_mul_left d₁ (Nat.mod_modEq cr.1 (d₁ * d₂))).trans cr.2.2
      rw [Nat.ModEq] at hmod1 hmod2
      ext
      · exact hmod1.trans (Nat.mod_eq_of_lt hr1)
      · exact hmod2.trans (Nat.mod_eq_of_lt hr2)

lemma xiD_eq_prod_primeFactors {K : ℕ} (m : Fin K → ℕ) {d : ℕ} (hd : Squarefree d) :
    xiD m d = ∏ p ∈ d.primeFactors, xi m p := by
  have hd_ne : d ≠ 0 := hd.ne_zero
  induction d using Nat.strongRecOn with
  | ind d ih =>
    by_cases hd1 : d = 1
    · subst hd1; simp [xiD_one]
    · obtain ⟨p, hp_pr, hpdvd⟩ := Nat.exists_prime_and_dvd hd1
      obtain ⟨e, rfl⟩ := hpdvd
      have he_ne : e ≠ 0 := right_ne_zero_of_mul hd_ne
      have hcop : p.Coprime e := (Nat.squarefree_mul_iff.mp hd).1
      have he_sq : Squarefree e := (Nat.squarefree_mul_iff.mp hd).2.2
      have he_lt : e < p * e := lt_mul_of_one_lt_left (Nat.pos_of_ne_zero he_ne) hp_pr.one_lt
      rw [xiD_mul_of_coprime m hcop, ih e he_lt he_sq he_ne,
        Nat.primeFactors_mul hp_pr.ne_zero he_ne, hp_pr.primeFactors,
        Finset.prod_union (by
          rw [Finset.disjoint_singleton_left]
          intro hmem
          have := Nat.dvd_of_mem_primeFactors hmem
          exact hp_pr.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd dvd_rfl this)),
        Finset.prod_singleton]
      rfl

/- Building the `BoundingSieve` for `chainProd m` -/

lemma squarefree_prod_primesBelow (n : ℕ) :
    Squarefree (∏ p ∈ n.primesBelow, p) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro q hq hqq
  have h1 : q ∣ ∏ p ∈ n.primesBelow, p := dvd_trans (dvd_mul_left q q) hqq
  obtain ⟨p, hp, hqp⟩ := (hq.prime.dvd_finsetProd_iff _).mp h1
  have hp_pr := Nat.prime_of_mem_primesBelow hp
  have heq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp_pr).mp hqp
  subst heq
  rw [← Finset.mul_prod_erase _ _ hp] at hqq
  have h2 : q ∣ ∏ x ∈ n.primesBelow.erase q, x :=
    (mul_dvd_mul_iff_left hq.ne_zero).mp hqq
  obtain ⟨r, hr, hqr⟩ := (hq.prime.dvd_finsetProd_iff _).mp h2
  have hr_ne : r ≠ q := (Finset.mem_erase.mp hr).1
  have hr_pr := Nat.prime_of_mem_primesBelow (Finset.mem_erase.mp hr).2
  exact hr_ne ((Nat.prime_dvd_prime_iff_eq hq hr_pr).mp hqr).symm

noncomputable def chainNu {K : ℕ} (m : Fin K → ℕ) (P : ℕ) : ArithmeticFunction ℝ where
  toFun d := if d = 0 then 0 else ∏ p ∈ d.primeFactors, (if p ∣ P then (xi m p : ℝ) / p else 0)
  map_zero' := rfl

lemma chainNu_isMultiplicative {K : ℕ} (m : Fin K → ℕ) (P : ℕ) :
    (chainNu m P).IsMultiplicative := by
  constructor
  · simp [chainNu]
  · intro a b hcop
    by_cases ha : a = 0
    · simp [ha, chainNu]
    by_cases hb : b = 0
    · simp [hb, chainNu]
    simp only [chainNu, ArithmeticFunction.coe_mk, mul_eq_zero, ha, hb, or_self, ite_false]
    rw [Nat.primeFactors_mul ha hb, Finset.prod_union hcop.disjoint_primeFactors]

lemma chainNu_prime {K : ℕ} (m : Fin K → ℕ) {P p : ℕ} (hp : p.Prime) (hpd : p ∣ P) :
    chainNu m P p = (xi m p : ℝ) / p := by
  simp [chainNu, hp.ne_zero, hp.primeFactors, hpd]

noncomputable def chainSieve {K : ℕ} (m : Fin K → ℕ) (hb : ¬ badVec m) (X Z : ℕ) :
    BoundingSieve where
  support := (Icc 1 X).image (chainProd m)
  prodPrimes := ∏ p ∈ (Z + 1).primesBelow, p
  prodPrimes_squarefree := squarefree_prod_primesBelow (Z + 1)
  weights := fun _ => 1
  weights_nonneg := fun _ => by norm_num
  totalMass := (X : ℝ)
  nu := chainNu m (∏ p ∈ (Z + 1).primesBelow, p)
  nu_mult := chainNu_isMultiplicative m _
  nu_pos_of_prime := fun p hp hpd => by
    rw [chainNu_prime m hp hpd]
    have h1 : (0 : ℝ) < xi m p := by exact_mod_cast (xi_ge_one m hp.one_le)
    have h2 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    exact div_pos h1 h2
  nu_lt_one_of_prime := fun p hp hpd => by
    rw [chainNu_prime m hp hpd]
    have hlt : xi m p < p := xi_lt_p_of_not_badVec hb hp
    rw [div_lt_one (by exact_mod_cast hp.pos)]
    exact_mod_cast hlt

lemma chainSieve_rem_abs_le {K : ℕ} (m : Fin K → ℕ) (hm : ∀ i, 1 ≤ m i) (hb : ¬ badVec m)
    (X Z : ℕ) {d : ℕ} (hd : d ∣ (chainSieve m hb X Z).prodPrimes) :
    |(chainSieve m hb X Z).rem d| ≤ (d : ℝ) := by
  let s := chainSieve m hb X Z
  have hd_sq : Squarefree d := s.squarefree_of_dvd_prodPrimes hd
  have hd_pos : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd_sq.ne_zero
  have hmult : s.multSum d = (((Icc 1 X).filter (fun n => d ∣ chainProd m n)).card : ℝ) := by
    simp only [BoundingSieve.multSum, s, chainSieve, ← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 1
    rw [Finset.filter_image]
    exact Finset.card_image_of_injective _ (chainProd_strictMono m hm).injective
  have hnu : s.nu d = (xiD m d : ℝ) / d := by
    have h1 := (s.prod_primeFactors_nu hd).symm
    have h2 := xiD_eq_prod_primeFactors m hd_sq
    have h3 : ∏ p ∈ d.primeFactors, p = d := Nat.prod_primeFactors_of_squarefree hd_sq
    rw [h1, h2, Nat.cast_prod]
    conv_rhs => arg 2; rw [← h3]
    rw [Nat.cast_prod, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp_pr := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ s.prodPrimes := (Nat.dvd_of_mem_primeFactors hp).trans hd
    exact chainNu_prime m hp_pr hpd
  let R := (range d).filter (fun r => d ∣ chainProd m r)
  have hpart : ((Icc 1 X).filter (fun n => d ∣ chainProd m n)).card =
      ∑ r ∈ R, ((Icc 1 X).filter (fun n => n % d = r)).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext n
      simp only [Finset.mem_filter, Finset.mem_biUnion, R, Finset.mem_range]
      constructor
      · intro ⟨hn, hdvd⟩
        refine ⟨n % d, ⟨Nat.mod_lt n (by omega), ?_⟩, hn, rfl⟩
        exact Nat.modEq_zero_iff_dvd.mp
          ((chainProd_modEq m (Nat.mod_modEq n d)).trans (Nat.modEq_zero_iff_dvd.mpr hdvd))
      · rintro ⟨r, ⟨_, hdvdr⟩, hn, rfl⟩
        refine ⟨hn, ?_⟩
        exact Nat.modEq_zero_iff_dvd.mp
          ((chainProd_modEq m (Nat.mod_modEq n d)).symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvdr))
    · intro r₁ _ r₂ _ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro n h1 h2
      rw [Finset.mem_filter] at h1 h2
      exact hne (h1.2.symm.trans h2.2)
  have hrem_eq : s.rem d =
      ∑ r ∈ R, ((((Icc 1 X).filter (fun n => n % d = r)).card : ℝ) - (X : ℝ) / d) := by
    rw [BoundingSieve.rem, hmult, hpart, Nat.cast_sum, hnu]
    simp only [s, chainSieve]
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have : R.card = xiD m d := rfl
    rw [this]; ring
  calc |s.rem d|
      = |∑ r ∈ R, ((((Icc 1 X).filter (fun n => n % d = r)).card : ℝ) - (X : ℝ) / d)| := by
        rw [hrem_eq]
    _ ≤ ∑ r ∈ R, |(((Icc 1 X).filter (fun n => n % d = r)).card : ℝ) - (X : ℝ) / d| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ R, (1 : ℝ) := Finset.sum_le_sum (fun r hr =>
        card_Icc_modEq_sub_div_le X d r hd_pos (Finset.mem_range.mp (Finset.mem_filter.mp hr).1))
    _ = (xiD m d : ℝ) := by simp [R, xiD]
    _ ≤ (d : ℝ) := by
        exact_mod_cast (show xiD m d ≤ d from (Finset.card_filter_le _ _).trans (by simp))

/- Optimal Selberg weights and main/error term evaluation -/

noncomputable def selbergG (s : BoundingSieve) (Z : ℕ) : ℝ :=
  ∑ l ∈ (divisors s.prodPrimes).filter (· ≤ Z), s.selbergTerms l

lemma one_le_selbergG (s : BoundingSieve) {Z : ℕ} (hZ : 1 ≤ Z) : 1 ≤ selbergG s Z := by
  unfold selbergG
  have h1mem : 1 ∈ (divisors s.prodPrimes).filter (· ≤ Z) := by
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨one_dvd _, s.prodPrimes_ne_zero⟩, hZ⟩
  have h1val : s.selbergTerms 1 = 1 := s.selbergTerms_isMultiplicative.1
  calc (1 : ℝ) = s.selbergTerms 1 := h1val.symm
    _ ≤ ∑ l ∈ (divisors s.prodPrimes).filter (· ≤ Z), s.selbergTerms l :=
        Finset.single_le_sum (fun l hl =>
          (s.selbergTerms_pos (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hl).1)).le) h1mem

noncomputable def selbergW (s : BoundingSieve) (Z : ℕ) (d : ℕ) : ℝ :=
  if d ∣ s.prodPrimes ∧ d ≤ Z then
    ((μ d : ℤ) : ℝ) / (s.nu d * selbergG s Z) *
      ∑ l ∈ (divisors s.prodPrimes).filter (fun l => d ∣ l ∧ l ≤ Z), s.selbergTerms l
  else 0

lemma selbergW_one (s : BoundingSieve) {Z : ℕ} (hZ : 1 ≤ Z) : selbergW s Z 1 = 1 := by
  have hGpos : 0 < selbergG s Z := lt_of_lt_of_le zero_lt_one (one_le_selbergG s hZ)
  unfold selbergW
  rw [if_pos ⟨one_dvd _, hZ⟩]
  simp only [moebius_apply_one, Int.cast_one, s.nu_mult.1, one_mul, one_dvd, true_and]
  change 1 / selbergG s Z * selbergG s Z = 1
  rw [one_div]
  exact inv_mul_cancel₀ hGpos.ne'

lemma abs_selbergW_le_one (s : BoundingSieve) {Z : ℕ} (hZ : 1 ≤ Z) (d : ℕ) :
    |selbergW s Z d| ≤ 1 := by
  unfold selbergW
  split_ifs with hd
  · obtain ⟨hdP, hdZ⟩ := hd
    have hGpos : 0 < selbergG s Z := lt_of_lt_of_le zero_lt_one (one_le_selbergG s hZ)
    have hnu_pos : 0 < s.nu d := s.nu_pos_of_dvd_prodPrimes hdP
    have hd_sq : Squarefree d := s.squarefree_of_dvd_prodPrimes hdP
    have hmu : |((μ d : ℤ) : ℝ)| = 1 := by
      have hsq := ArithmeticFunction.moebius_apply_of_squarefree hd_sq
      rw [hsq, Int.cast_pow, Int.cast_neg, Int.cast_one, abs_pow, abs_neg, abs_one, one_pow]
    have hsum_nonneg : 0 ≤ ∑ l ∈ (divisors s.prodPrimes).filter (fun l => d ∣ l ∧ l ≤ Z),
        s.selbergTerms l :=
      Finset.sum_nonneg (fun l hl =>
        (s.selbergTerms_pos (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hl).1)).le)
    rw [abs_mul, abs_div, hmu, abs_of_pos (mul_pos hnu_pos hGpos), abs_of_nonneg hsum_nonneg,
      one_div_mul_eq_div, div_le_one (mul_pos hnu_pos hGpos)]
    -- Rewrite the sum over `l` as `selbergTerms d * ∑_{m | P, Coprime d m, m ≤ Z / d} selbergTerms m`
    let M := (divisors s.prodPrimes).filter (fun m => d.Coprime m ∧ m ≤ Z / d)
    have hbij : ∑ l ∈ (divisors s.prodPrimes).filter (fun l => d ∣ l ∧ l ≤ Z), s.selbergTerms l =
        s.selbergTerms d * ∑ m ∈ M, s.selbergTerms m := by
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun l _ => l / d) ?_ ?_ ?_ ?_
      · intro l hl
        simp only [M, Finset.mem_filter, Nat.mem_divisors] at hl ⊢
        have hl_sq : Squarefree l := s.squarefree_of_dvd_prodPrimes hl.1.1
        have hdm : d * (l / d) = l := Nat.mul_div_cancel' hl.2.1
        have hcop : d.Coprime (l / d) := (Nat.squarefree_mul_iff.mp (hdm.symm ▸ hl_sq)).1
        have hdvdP : l / d ∣ s.prodPrimes := dvd_trans (Nat.div_dvd_of_dvd hl.2.1) hl.1.1
        exact ⟨⟨hdvdP, hl.1.2⟩, hcop, Nat.div_le_div_right hl.2.2⟩
      · intro l₁ hl₁ l₂ hl₂ heq
        simp only [Finset.mem_filter] at hl₁ hl₂
        rw [← Nat.mul_div_cancel' hl₁.2.1, ← Nat.mul_div_cancel' hl₂.2.1, heq]
      · intro m hm
        simp only [M, Finset.mem_filter, Nat.mem_divisors] at hm
        refine ⟨d * m, ?_, Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hd_sq.ne_zero)⟩
        simp only [Finset.mem_filter, Nat.mem_divisors]
        exact ⟨⟨hm.2.1.mul_dvd_of_dvd_of_dvd hdP hm.1.1, hm.1.2⟩, dvd_mul_right d m,
          (Nat.mul_le_mul_left d hm.2.2).trans (Nat.mul_div_le Z d)⟩
      · intro l hl
        simp only [Finset.mem_filter, Nat.mem_divisors] at hl
        have hl_sq : Squarefree l := s.squarefree_of_dvd_prodPrimes hl.1.1
        have hdm : d * (l / d) = l := Nat.mul_div_cancel' hl.2.1
        have hcop : d.Coprime (l / d) := (Nat.squarefree_mul_iff.mp (hdm.symm ▸ hl_sq)).1
        conv_lhs => rw [← hdm]
        exact s.selbergTerms_isMultiplicative.2 hcop
    rw [hbij, ← mul_le_mul_iff_right₀ (inv_pos.mpr hnu_pos)]
    have hleft : (s.nu d)⁻¹ * (s.selbergTerms d * ∑ m ∈ M, s.selbergTerms m) =
        (s.selbergTerms d * (s.nu d)⁻¹) * ∑ m ∈ M, s.selbergTerms m := by ring
    have hright : (s.nu d)⁻¹ * (s.nu d * selbergG s Z) = selbergG s Z := by
      rw [← mul_assoc, inv_mul_cancel₀ hnu_pos.ne', one_mul]
    rw [hleft, hright, ← s.sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv hdP]
    simp_rw [← Finset.sum_filter]
    rw [Finset.sum_mul_sum]
    let D := (divisors s.prodPrimes).filter (fun e => e ∣ d)
    have hprod_le : ∑ x ∈ D ×ˢ M, s.selbergTerms x.1 * s.selbergTerms x.2 ≤ selbergG s Z := by
      unfold selbergG
      have hterm : ∀ x ∈ D ×ˢ M, s.selbergTerms x.1 * s.selbergTerms x.2 =
          s.selbergTerms (x.1 * x.2) := by
        intro ⟨e, m⟩ hx
        simp only [D, M, Finset.mem_product, Finset.mem_filter] at hx
        have hcop : e.Coprime m := hx.2.2.1.coprime_dvd_left hx.1.2
        exact (s.selbergTerms_isMultiplicative.2 hcop).symm
      rw [Finset.sum_congr rfl hterm]
      have hinj : Set.InjOn (fun x : ℕ × ℕ => x.1 * x.2) ↑(D ×ˢ M) := by
        intro ⟨e₁, m₁⟩ hx₁ ⟨e₂, m₂⟩ hx₂ heq
        dsimp only at heq
        rw [Finset.mem_coe, Finset.mem_product] at hx₁ hx₂
        have hx₁D := Finset.mem_filter.mp hx₁.1
        have hx₁M := Finset.mem_filter.mp hx₁.2
        have hx₂D := Finset.mem_filter.mp hx₂.1
        have hx₂M := Finset.mem_filter.mp hx₂.2
        have h1 : Nat.gcd (e₁ * m₁) d = e₁ := by
          rw [Nat.Coprime.gcd_mul_right_cancel e₁ hx₁M.2.1.symm, Nat.gcd_eq_left hx₁D.2]
        have h2 : Nat.gcd (e₂ * m₂) d = e₂ := by
          rw [Nat.Coprime.gcd_mul_right_cancel e₂ hx₂M.2.1.symm, Nat.gcd_eq_left hx₂D.2]
        have he : e₁ = e₂ := by rw [← h1, ← h2, heq]
        have he_pos : 0 < e₁ := Nat.pos_of_ne_zero (s.squarefree_of_dvd_prodPrimes
          (Nat.dvd_of_mem_divisors hx₁D.1)).ne_zero
        have hm : m₁ = m₂ := Nat.eq_of_mul_eq_mul_left he_pos (by rwa [← he] at heq)
        exact Prod.ext he hm
      have hmaps : (D ×ˢ M).image (fun x : ℕ × ℕ => x.1 * x.2) ⊆
          (divisors s.prodPrimes).filter (· ≤ Z) := by
        intro l hl
        rw [Finset.mem_image] at hl
        obtain ⟨⟨e, m⟩, hx, rfl⟩ := hl
        simp only [D, M, Finset.mem_product, Finset.mem_filter, Nat.mem_divisors] at hx ⊢
        have hcop : e.Coprime m := hx.2.2.1.coprime_dvd_left hx.1.2
        have he_le : e ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hd_sq.ne_zero) hx.1.2
        exact ⟨⟨hcop.mul_dvd_of_dvd_of_dvd hx.1.1.1 hx.2.1.1, hx.1.1.2⟩,
          (Nat.mul_le_mul he_le hx.2.2.2).trans (Nat.mul_div_le Z d)⟩
      rw [← Finset.sum_image (f := fun l => s.selbergTerms l) (fun x hx y hy h => hinj hx hy h)]
      exact Finset.sum_le_sum_of_subset_of_nonneg hmaps (fun l hl _ =>
        (s.selbergTerms_pos (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hl).1)).le)
    rw [Finset.sum_product] at hprod_le
    exact hprod_le
  · simp

lemma selberg_mainSum_eq_inv_G (s : BoundingSieve) {Z : ℕ} (hZ : 1 ≤ Z) :
    s.mainSum (BoundingSieve.lambdaSquared (selbergW s Z)) = (selbergG s Z)⁻¹ := by
  have hGpos : 0 < selbergG s Z := lt_of_lt_of_le zero_lt_one (one_le_selbergG s hZ)
  rw [s.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  have hinner : ∀ l ∈ divisors s.prodPrimes,
      (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * selbergW s Z d else 0) =
        if l ≤ Z then ((μ l : ℤ) : ℝ) * s.selbergTerms l / selbergG s Z else 0 := by
    intro l hl
    have hlP : l ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hl
    have hl_sq : Squarefree l := s.squarefree_of_dvd_prodPrimes hlP
    by_cases hlZ : l ≤ Z
    · rw [if_pos hlZ]
      have hstep1 : (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * selbergW s Z d else 0) =
          (selbergG s Z)⁻¹ * ∑ d ∈ (divisors s.prodPrimes).filter (fun d => l ∣ d ∧ d ≤ Z),
            ((μ d : ℤ) : ℝ) *
              ∑ m ∈ (divisors s.prodPrimes).filter (fun m => d ∣ m ∧ m ≤ Z), s.selbergTerms m := by
        rw [Finset.mul_sum]
        have hzero : ∀ d ∈ divisors s.prodPrimes,
            (if l ∣ d then s.nu d * selbergW s Z d else 0) =
              if l ∣ d ∧ d ≤ Z then
                (selbergG s Z)⁻¹ * (((μ d : ℤ) : ℝ) *
                  ∑ m ∈ (divisors s.prodPrimes).filter (fun m => d ∣ m ∧ m ≤ Z), s.selbergTerms m)
              else 0 := by
          intro d hd
          have hdP : d ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hd
          have hnu_ne : s.nu d ≠ 0 := s.nu_ne_zero hdP
          by_cases hld : l ∣ d
          · by_cases hdZ : d ≤ Z
            · rw [if_pos hld, if_pos ⟨hld, hdZ⟩]
              unfold selbergW
              rw [if_pos ⟨hdP, hdZ⟩]
              field_simp [hnu_ne, hGpos.ne']
            · rw [if_pos hld, if_neg (fun h => hdZ h.2)]
              simp [selbergW, hdZ]
          · rw [if_neg hld, if_neg (fun h => hld h.1)]
        rw [Finset.sum_congr rfl hzero, ← Finset.sum_filter]
      rw [hstep1]
      -- Swap sums over `d` and `m`
      have hswap' : ∑ d ∈ (divisors s.prodPrimes).filter (fun d => l ∣ d ∧ d ≤ Z),
            ((μ d : ℤ) : ℝ) *
              ∑ m ∈ (divisors s.prodPrimes).filter (fun m => d ∣ m ∧ m ≤ Z), s.selbergTerms m =
          ∑ m ∈ (divisors s.prodPrimes).filter (fun m => l ∣ m ∧ m ≤ Z),
            s.selbergTerms m *
              ∑ d ∈ (divisors s.prodPrimes).filter (fun d => l ∣ d ∧ d ∣ m), ((μ d : ℤ) : ℝ) := by
        trans ∑ d ∈ divisors s.prodPrimes, ∑ m ∈ divisors s.prodPrimes,
            if l ∣ d ∧ d ∣ m ∧ m ≤ Z then ((μ d : ℤ) : ℝ) * s.selbergTerms m else 0
        · rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun d hd => ?_
          split_ifs with h1
          · rw [Finset.mul_sum, Finset.sum_filter]
            refine Finset.sum_congr rfl fun m _ => ?_
            by_cases h2 : d ∣ m ∧ m ≤ Z
            · rw [if_pos h2, if_pos ⟨h1.1, h2.1, h2.2⟩]
            · rw [if_neg h2, if_neg (fun h => h2 ⟨h.2.1, h.2.2⟩)]
          · symm
            refine Finset.sum_eq_zero fun m hm => ?_
            split_ifs with h3
            · exfalso
              have hm_pos : 0 < m := Nat.pos_of_ne_zero (s.squarefree_of_dvd_prodPrimes
                (Nat.dvd_of_mem_divisors hm)).ne_zero
              exact h1 ⟨h3.1, (Nat.le_of_dvd hm_pos h3.2.1).trans h3.2.2⟩
            · rfl
        · rw [Finset.sum_comm, Finset.sum_filter]
          refine Finset.sum_congr rfl fun m hm => ?_
          split_ifs with h1
          · rw [Finset.mul_sum, Finset.sum_filter]
            refine Finset.sum_congr rfl fun d _ => ?_
            by_cases h2 : l ∣ d ∧ d ∣ m
            · rw [if_pos ⟨h2.1, h2.2, h1.2⟩, if_pos h2]; ring
            · rw [if_neg (fun h => h2 ⟨h.1, h.2.1⟩), if_neg h2]
          · refine Finset.sum_eq_zero fun d _ => ?_
            split_ifs with h2
            · exfalso; exact h1 ⟨dvd_trans h2.1 h2.2.1, h2.2.2⟩
            · rfl
      rw [hswap']
      have hmob : ∀ m ∈ (divisors s.prodPrimes).filter (fun m => l ∣ m ∧ m ≤ Z),
          (∑ d ∈ (divisors s.prodPrimes).filter (fun d => l ∣ d ∧ d ∣ m), ((μ d : ℤ) : ℝ)) =
            if m = l then ((μ l : ℤ) : ℝ) else 0 := by
        intro m hm
        simp only [Finset.mem_filter, Nat.mem_divisors] at hm
        have hm_sq : Squarefree m := s.squarefree_of_dvd_prodPrimes hm.1.1
        have hlm : l * (m / l) = m := Nat.mul_div_cancel' hm.2.1
        have hcop_ml : l.Coprime (m / l) := (Nat.squarefree_mul_iff.mp (hlm.symm ▸ hm_sq)).1
        have hbij : (∑ d ∈ (divisors s.prodPrimes).filter (fun d => l ∣ d ∧ d ∣ m), ((μ d : ℤ) : ℝ)) =
            ((μ l : ℤ) : ℝ) * ∑ t ∈ (m / l).divisors, ((μ t : ℤ) : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_bij (fun d _ => d / l) ?_ ?_ ?_ ?_
          · intro d hd
            simp only [Finset.mem_filter, Nat.mem_divisors] at hd ⊢
            refine ⟨?_, right_ne_zero_of_mul (hlm.symm ▸ hm_sq.ne_zero)⟩
            exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hl_sq.ne_zero)).mp
              (by rw [Nat.mul_div_cancel' hd.2.1, hlm]; exact hd.2.2)
          · intro d₁ hd₁ d₂ hd₂ heq
            simp only [Finset.mem_filter] at hd₁ hd₂
            rw [← Nat.mul_div_cancel' hd₁.2.1, ← Nat.mul_div_cancel' hd₂.2.1, heq]
          · intro t ht
            rw [Nat.mem_divisors] at ht
            refine ⟨l * t, ?_, Nat.mul_div_cancel_left t (Nat.pos_of_ne_zero hl_sq.ne_zero)⟩
            simp only [Finset.mem_filter, Nat.mem_divisors]
            have hltm : l * t ∣ m := hlm ▸ mul_dvd_mul_left l ht.1
            exact ⟨⟨dvd_trans hltm hm.1.1, hm.1.2⟩, dvd_mul_right l t, hltm⟩
          · intro d hd
            simp only [Finset.mem_filter] at hd
            have hdl : l * (d / l) = d := Nat.mul_div_cancel' hd.2.1
            have htdvd : d / l ∣ m / l :=
              (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hl_sq.ne_zero)).mp
                (by rw [hdl, hlm]; exact hd.2.2)
            have hcop_lt : l.Coprime (d / l) := hcop_ml.coprime_dvd_right htdvd
            have hmu_mul : μ (l * (d / l)) = μ l * μ (d / l) :=
              ArithmeticFunction.isMultiplicative_moebius.2 hcop_lt
            conv_lhs => rw [← hdl, hmu_mul, Int.cast_mul]
        rw [hbij]
        have hsum_mu : (∑ t ∈ (m / l).divisors, ((μ t : ℤ) : ℝ)) = if m / l = 1 then 1 else 0 := by
          have h1 : (∑ t ∈ (m / l).divisors, μ t) = if m / l = 1 then 1 else 0 := by
            have hz := ArithmeticFunction.moebius_mul_coe_zeta
            have heval := congrFun (congrArg DFunLike.coe hz) (m / l)
            simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply] at heval
            rw [Nat.sum_divisorsAntidiagonal (f := fun x y => μ x * ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) y))] at heval
            rw [← heval]
            refine Finset.sum_congr rfl fun t ht => ?_
            have hne : m / l / t ≠ 0 := by
              rw [Nat.mem_divisors] at ht
              have hpos : 0 < m / l := Nat.pos_of_ne_zero ht.2
              exact (Nat.div_pos (Nat.le_of_dvd hpos ht.1)
                (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero ht.2 ht.1))).ne'
            simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hne]
          have hcast : (∑ t ∈ (m / l).divisors, ((μ t : ℤ) : ℝ)) =
              ((∑ t ∈ (m / l).divisors, μ t : ℤ) : ℝ) := by push_cast; rfl
          rw [hcast, h1]
          split_ifs <;> simp
        rw [hsum_mu]
        have hiff : m / l = 1 ↔ m = l := by
          constructor
          · intro h1; rw [← hlm, h1, mul_one]
          · intro h1; rw [h1, Nat.div_self (Nat.pos_of_ne_zero hl_sq.ne_zero)]
        by_cases hml1 : m / l = 1
        · rw [if_pos hml1, if_pos (hiff.mp hml1), mul_one]
        · rw [if_neg hml1, if_neg (fun h => hml1 (hiff.mpr h)), mul_zero]
      have hterm_eq : ∑ m ∈ (divisors s.prodPrimes).filter (fun m => l ∣ m ∧ m ≤ Z),
            s.selbergTerms m *
              ∑ d ∈ (divisors s.prodPrimes).filter (fun d => l ∣ d ∧ d ∣ m), ((μ d : ℤ) : ℝ) =
          s.selbergTerms l * ((μ l : ℤ) : ℝ) := by
        rw [Finset.sum_congr rfl (fun m hm => by rw [hmob m hm])]
        simp_rw [mul_ite, mul_zero]
        rw [Finset.sum_ite_eq']
        rw [if_pos (Finset.mem_filter.mpr ⟨hl, dvd_rfl, hlZ⟩)]
      rw [hterm_eq]; ring
    · rw [if_neg hlZ]
      refine Finset.sum_eq_zero fun d hd => ?_
      split_ifs with hld
      · have hdgt : ¬ d ≤ Z := fun hdZ => by
          have hd_pos : 0 < d := Nat.pos_of_ne_zero (s.squarefree_of_dvd_prodPrimes
            (Nat.dvd_of_mem_divisors hd)).ne_zero
          have := Nat.le_of_dvd hd_pos hld
          omega
        simp [selbergW, hdgt]
      · rfl
  rw [Finset.sum_congr rfl (fun l hl => by rw [hinner l hl])]
  have hsq_term : ∀ l ∈ divisors s.prodPrimes,
      (s.selbergTerms l)⁻¹ * (if l ≤ Z then ((μ l : ℤ) : ℝ) * s.selbergTerms l / selbergG s Z else 0) ^ 2 =
        if l ≤ Z then s.selbergTerms l / (selbergG s Z) ^ 2 else 0 := by
    intro l hl
    split_ifs with hlZ
    · have hlP : l ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hl
      have hl_sq : Squarefree l := s.squarefree_of_dvd_prodPrimes hlP
      have hg_pos : 0 < s.selbergTerms l := s.selbergTerms_pos hlP
      have hmu_sq : ((μ l : ℤ) : ℝ) ^ 2 = 1 := by
        have hsq := ArithmeticFunction.moebius_apply_of_squarefree hl_sq
        rw [hsq, Int.cast_pow, Int.cast_neg, Int.cast_one, ← pow_mul, mul_comm, pow_mul]
        norm_num
      field_simp [hg_pos.ne', hGpos.ne']
      exact hmu_sq
    · simp
  rw [Finset.sum_congr rfl hsq_term, ← Finset.sum_filter, ← Finset.sum_div]
  change selbergG s Z / (selbergG s Z) ^ 2 = (selbergG s Z)⁻¹
  field_simp [hGpos.ne']

lemma selberg_errSum_le {K : ℕ} (m : Fin K → ℕ) (hm : ∀ i, 1 ≤ m i) (hb : ¬ badVec m)
    (X Z : ℕ) (hZ : 1 ≤ Z) :
    (chainSieve m hb X Z).errSum (BoundingSieve.lambdaSquared (selbergW (chainSieve m hb X Z) Z)) ≤
      (Z : ℝ) ^ 4 := by
  let s := chainSieve m hb X Z
  let w := selbergW s Z
  have hw_le : ∀ d, |w d| ≤ 1 := abs_selbergW_le_one s hZ
  have hw_zero : ∀ d, Z < d → w d = 0 := fun d hd => by
    unfold w selbergW; rw [if_neg (fun h => by omega)]
  have h1 : ∀ d ∈ divisors s.prodPrimes,
      |BoundingSieve.lambdaSquared w d| * |s.rem d| ≤
        ∑ d₁ ∈ (divisors s.prodPrimes).filter (· ≤ Z),
          ∑ d₂ ∈ (divisors s.prodPrimes).filter (· ≤ Z),
            if d = Nat.lcm d₁ d₂ then (Z : ℝ) ^ 2 else 0 := by
    intro d hd
    have hdP : d ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hd
    have hrem : |s.rem d| ≤ (d : ℝ) := chainSieve_rem_abs_le m hm hb X Z hdP
    have hlam : |BoundingSieve.lambdaSquared w d| ≤
        ∑ d₁ ∈ d.divisors, ∑ d₂ ∈ d.divisors,
          if d = Nat.lcm d₁ d₂ then |w d₁| * |w d₂| else 0 := by
      unfold BoundingSieve.lambdaSquared
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d₁ _ => ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d₂ _ => ?_)
      split_ifs <;> simp [abs_mul]
    have hmul : |BoundingSieve.lambdaSquared w d| * |s.rem d| ≤
        ∑ d₁ ∈ d.divisors, ∑ d₂ ∈ d.divisors,
          if d = Nat.lcm d₁ d₂ then |w d₁| * |w d₂| * (d : ℝ) else 0 := by
      calc |BoundingSieve.lambdaSquared w d| * |s.rem d|
          ≤ (∑ d₁ ∈ d.divisors, ∑ d₂ ∈ d.divisors,
              if d = Nat.lcm d₁ d₂ then |w d₁| * |w d₂| else 0) * (d : ℝ) :=
            mul_le_mul hlam hrem (abs_nonneg _) (Finset.sum_nonneg (fun _ _ =>
              Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)))
        _ = ∑ d₁ ∈ d.divisors, ∑ d₂ ∈ d.divisors,
              if d = Nat.lcm d₁ d₂ then |w d₁| * |w d₂| * (d : ℝ) else 0 := by
            simp_rw [Finset.sum_mul, ite_mul, zero_mul]
    refine hmul.trans ?_
    have hterm : ∀ d₁ ∈ d.divisors, ∀ d₂ ∈ d.divisors,
        (if d = Nat.lcm d₁ d₂ then |w d₁| * |w d₂| * (d : ℝ) else 0) ≤
          if d₁ ≤ Z ∧ d₂ ≤ Z ∧ d = Nat.lcm d₁ d₂ then (Z : ℝ) ^ 2 else 0 := by
      intro d₁ hd₁ d₂ hd₂
      by_cases heq : d = Nat.lcm d₁ d₂
      · by_cases h1Z : d₁ ≤ Z
        · by_cases h2Z : d₂ ≤ Z
          · rw [if_pos heq, if_pos ⟨h1Z, h2Z, heq⟩]
            have hd1_pos : 0 < d₁ := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero
              (Nat.mem_divisors.mp hd₁).2 (Nat.mem_divisors.mp hd₁).1)
            have hd2_pos : 0 < d₂ := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero
              (Nat.mem_divisors.mp hd₂).2 (Nat.mem_divisors.mp hd₂).1)
            have hdlcm : d ≤ d₁ * d₂ :=
              heq ▸ Nat.le_of_dvd (Nat.mul_pos hd1_pos hd2_pos)
                (Nat.lcm_dvd (dvd_mul_right d₁ d₂) (dvd_mul_left d₂ d₁))
            have hdZ2 : (d : ℝ) ≤ (Z : ℝ) ^ 2 := by
              have : d ≤ Z * Z := hdlcm.trans (Nat.mul_le_mul h1Z h2Z)
              simpa [sq] using (show (d : ℝ) ≤ ((Z * Z : ℕ) : ℝ) by exact_mod_cast this)
            calc |w d₁| * |w d₂| * (d : ℝ) ≤ 1 * 1 * (Z : ℝ) ^ 2 :=
                  mul_le_mul (mul_le_mul (hw_le d₁) (hw_le d₂) (abs_nonneg _) zero_le_one)
                    hdZ2 (by positivity) (by norm_num)
              _ = (Z : ℝ) ^ 2 := by ring
          · rw [if_pos heq, if_neg (fun h => h2Z h.2.1), hw_zero d₂ (by omega), abs_zero]
            simp
        · rw [if_pos heq, if_neg (fun h => h1Z h.1), hw_zero d₁ (by omega), abs_zero]
          simp
      · rw [if_neg heq, if_neg (fun h => heq h.2.2)]
    calc ∑ d₁ ∈ d.divisors, ∑ d₂ ∈ d.divisors,
            (if d = Nat.lcm d₁ d₂ then |w d₁| * |w d₂| * (d : ℝ) else 0)
        ≤ ∑ d₁ ∈ d.divisors, ∑ d₂ ∈ d.divisors,
            (if d₁ ≤ Z ∧ d₂ ≤ Z ∧ d = Nat.lcm d₁ d₂ then (Z : ℝ) ^ 2 else 0) :=
          Finset.sum_le_sum (fun d₁ hd₁ => Finset.sum_le_sum (fun d₂ hd₂ => hterm d₁ hd₁ d₂ hd₂))
      _ ≤ ∑ d₁ ∈ divisors s.prodPrimes, ∑ d₂ ∈ divisors s.prodPrimes,
            (if d₁ ≤ Z ∧ d₂ ≤ Z ∧ d = Nat.lcm d₁ d₂ then (Z : ℝ) ^ 2 else 0) := by
          have hsub : d.divisors ⊆ divisors s.prodPrimes := Nat.divisors_subset_of_dvd s.prodPrimes_ne_zero hdP
          refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ =>
            Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity))).trans ?_
          exact Finset.sum_le_sum (fun _ _ =>
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by split_ifs <;> positivity))
      _ = ∑ d₁ ∈ (divisors s.prodPrimes).filter (· ≤ Z),
            ∑ d₂ ∈ (divisors s.prodPrimes).filter (· ≤ Z),
              (if d = Nat.lcm d₁ d₂ then (Z : ℝ) ^ 2 else 0) := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun d₁ _ => ?_
          split_ifs with h1Z
          · rw [Finset.sum_filter]
            refine Finset.sum_congr rfl fun d₂ _ => ?_
            by_cases h2Z : d₂ ≤ Z
            · by_cases heq : d = Nat.lcm d₁ d₂
              · rw [if_pos ⟨h1Z, h2Z, heq⟩, if_pos h2Z, if_pos heq]
              · rw [if_neg (fun h => heq h.2.2), if_pos h2Z, if_neg heq]
            · rw [if_neg (fun h => h2Z h.2.1), if_neg h2Z]
          · refine Finset.sum_eq_zero fun d₂ _ => ?_
            rw [if_neg (fun h => h1Z h.1)]
  calc s.errSum (BoundingSieve.lambdaSquared w)
      = ∑ d ∈ divisors s.prodPrimes, |BoundingSieve.lambdaSquared w d| * |s.rem d| := rfl
    _ ≤ ∑ d ∈ divisors s.prodPrimes,
          ∑ d₁ ∈ (divisors s.prodPrimes).filter (· ≤ Z),
            ∑ d₂ ∈ (divisors s.prodPrimes).filter (· ≤ Z),
              (if d = Nat.lcm d₁ d₂ then (Z : ℝ) ^ 2 else 0) := Finset.sum_le_sum h1
    _ = ∑ d₁ ∈ (divisors s.prodPrimes).filter (· ≤ Z),
          ∑ d₂ ∈ (divisors s.prodPrimes).filter (· ≤ Z),
            ∑ d ∈ divisors s.prodPrimes, (if d = Nat.lcm d₁ d₂ then (Z : ℝ) ^ 2 else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ ≤ ∑ d₁ ∈ (divisors s.prodPrimes).filter (· ≤ Z),
          ∑ d₂ ∈ (divisors s.prodPrimes).filter (· ≤ Z), (Z : ℝ) ^ 2 := by
        refine Finset.sum_le_sum fun d₁ _ => Finset.sum_le_sum fun d₂ _ => ?_
        rw [Finset.sum_ite_eq']
        split_ifs
        · exact le_rfl
        · positivity
    _ = (((divisors s.prodPrimes).filter (· ≤ Z)).card : ℝ) ^ 2 * (Z : ℝ) ^ 2 := by
        simp [sq]; ring
    _ ≤ (Z : ℝ) ^ 2 * (Z : ℝ) ^ 2 := by
        gcongr
        have hcard : ((divisors s.prodPrimes).filter (· ≤ Z)).card ≤ Z := by
          have hsub : (divisors s.prodPrimes).filter (· ≤ Z) ⊆ Icc 1 Z := by
            intro d hd
            simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc] at hd ⊢
            have hdpos : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr
              (s.squarefree_of_dvd_prodPrimes hd.1.1).ne_zero
            exact ⟨hdpos, hd.2⟩
          exact (Finset.card_le_card hsub).trans (by simp)
        exact_mod_cast hcard
    _ = (Z : ℝ) ^ 4 := by ring

/- Rankin lower bound for `selbergG` -/

lemma sum_divisors_prod_primes_eq_prod_one_add {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (f : ArithmeticFunction ℝ) (hf : f.IsMultiplicative) :
    ∑ d ∈ (∏ p ∈ P, p).divisors, f d = ∏ p ∈ P, (1 + f p) := by
  classical
  induction P using Finset.induction with
  | empty => simp [hf.1]
  | @insert p P hp ih =>
    have hp_pr : p.Prime := hP p (Finset.mem_insert_self p P)
    have hP_pr : ∀ q ∈ P, q.Prime := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hcop : p.Coprime (∏ q ∈ P, q) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      have hq_pr := hP_pr q hq
      exact (Nat.coprime_primes hp_pr hq_pr).mpr (fun heq => hp (heq ▸ hq))
    have hne : ∏ q ∈ P, q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun q hq => (hP_pr q hq).ne_zero)
    rw [Finset.prod_insert hp, Finset.prod_insert hp, ← ih hP_pr]
    have hpne : p * ∏ q ∈ P, q ≠ 0 := Nat.mul_ne_zero hp_pr.ne_zero hne
    have hdiv_eq : (p * ∏ q ∈ P, q).divisors =
        (∏ q ∈ P, q).divisors ∪ ((∏ q ∈ P, q).divisors.image (p * ·)) := by
      ext d
      simp only [Nat.mem_divisors, Finset.mem_union, Finset.mem_image]
      constructor
      · intro ⟨hd, _⟩
        by_cases hpd : p ∣ d
        · refine Or.inr ⟨d / p, ⟨?_, hne⟩, Nat.mul_div_cancel' hpd⟩
          exact (Nat.mul_dvd_mul_iff_left hp_pr.pos).mp (by rwa [Nat.mul_div_cancel' hpd])
        · exact Or.inl ⟨(hp_pr.coprime_iff_not_dvd.mpr hpd).symm.dvd_of_dvd_mul_left hd, hne⟩
      · rintro (⟨hd, _⟩ | ⟨e, ⟨he, _⟩, rfl⟩)
        · exact ⟨dvd_mul_of_dvd_right hd p, hpne⟩
        · exact ⟨mul_dvd_mul_left p he, hpne⟩
    have hdisj : Disjoint (∏ q ∈ P, q).divisors ((∏ q ∈ P, q).divisors.image (p * ·)) := by
      rw [Finset.disjoint_left]
      intro d hd1 hd2
      rw [Finset.mem_image] at hd2
      obtain ⟨e, _, rfl⟩ := hd2
      rw [Nat.mem_divisors] at hd1
      have hpd : p ∣ ∏ q ∈ P, q := dvd_trans (dvd_mul_right p e) hd1.1
      exact hp_pr.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd dvd_rfl hpd)
    rw [hdiv_eq, Finset.sum_union hdisj,
      Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp_pr.pos h)]
    have hmul_sum : ∑ e ∈ (∏ q ∈ P, q).divisors, f (p * e) =
        f p * ∑ e ∈ (∏ q ∈ P, q).divisors, f e := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e he => ?_
      exact hf.2 (hcop.coprime_dvd_right (Nat.dvd_of_mem_divisors he))
    rw [hmul_sum]; ring

lemma singSeries_pos_of_not_badVec {K : ℕ} (m : Fin K → ℕ) (hb : ¬ badVec m) :
    0 < singSeries m := by
  classical
  unfold singSeries
  rw [if_neg hb]
  refine Finset.prod_pos fun p hp => ?_
  have hp_pr : p.Prime := by
    rcases Finset.mem_union.mp hp with h1 | h2
    · exact Nat.prime_of_mem_primeFactors h1
    · exact Nat.prime_of_mem_primesBelow h2
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
  have h1 : 0 < 1 - (xi m p : ℝ) / p := by
    rw [sub_pos, div_lt_one hp_pos]; exact_mod_cast xi_lt_p_of_not_badVec hb hp_pr
  have h2 : 0 < 1 - 1 / (p : ℝ) := by
    rw [sub_pos, div_lt_one hp_pos]; exact_mod_cast hp_pr.one_lt
  positivity

lemma selbergG_ge_half_prod {K : ℕ} (m : Fin K → ℕ) (hb : ¬ badVec m)
    (X : ℕ) {Z Y : ℕ} (hYZ : Y ≤ Z)
    (hY2 : 2 ≤ Y)
    (hY_log : 4 * ((K + 1 : ℕ) : ℝ) * Real.log (2 * ((K + 1 : ℕ) : ℝ)) + 8 ≤ Real.log (Y : ℝ))
    (hZY : 30 * ((K + 1 : ℕ) : ℝ) * Real.log (Y : ℝ) ≤ Real.log (Z : ℝ)) :
    (1 / 2) * ∏ p ∈ (Y + 1).primesBelow, (1 - (xi m p : ℝ) / p)⁻¹ ≤
      selbergG (chainSieve m hb X Z) Z := by
  let s := chainSieve m hb X Z
  let k := K + 1
  have hk1 : 1 ≤ k := Nat.succ_pos K
  have hZ2 : 2 ≤ Z := hY2.trans hYZ
  have hlogY_pos : 0 < Real.log (Y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  let PY := ∏ p ∈ (Y + 1).primesBelow, p
  have hPY_dvd : PY ∣ s.prodPrimes := by
    have hsub : (Y + 1).primesBelow ⊆ (Z + 1).primesBelow :=
      Nat.primesBelow_mono (Nat.succ_le_succ hYZ)
    exact Finset.prod_dvd_prod_of_subset _ _ _ hsub
  have hg_prime : ∀ p ∈ (Y + 1).primesBelow,
      s.selbergTerms p = (xi m p : ℝ) / ((p : ℝ) - (xi m p : ℝ)) := by
    intro p hp
    have hp_pr := Nat.prime_of_mem_primesBelow hp
    have hpP : p ∣ s.prodPrimes :=
      dvd_trans (Finset.dvd_prod_of_mem _ hp) hPY_dvd
    rw [s.selbergTerms_apply, hp_pr.primeFactors, Finset.prod_singleton]
    have hnu_p : s.nu p = (xi m p : ℝ) / p := chainNu_prime m hp_pr hpP
    rw [hnu_p]
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
    have hxi_lt : (xi m p : ℝ) < p := by exact_mod_cast xi_lt_p_of_not_badVec hb hp_pr
    have hsub_ne : (p : ℝ) - xi m p ≠ 0 := by linarith
    field_simp [hp_pos.ne', hsub_ne]
  have hone_add_g : ∀ p ∈ (Y + 1).primesBelow,
      1 + s.selbergTerms p = (1 - (xi m p : ℝ) / p)⁻¹ := by
    intro p hp
    have hp_pr := Nat.prime_of_mem_primesBelow hp
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
    have hxi_lt : (xi m p : ℝ) < p := by exact_mod_cast xi_lt_p_of_not_badVec hb hp_pr
    rw [hg_prime p hp]
    have h1 : (p : ℝ) - xi m p ≠ 0 := by linarith
    field_simp [hp_pos.ne', h1]; ring
  have hprod_eq : ∑ d ∈ PY.divisors, s.selbergTerms d =
      ∏ p ∈ (Y + 1).primesBelow, (1 + s.selbergTerms p) :=
    sum_divisors_prod_primes_eq_prod_one_add (fun p hp => Nat.prime_of_mem_primesBelow hp)
      s.selbergTerms s.selbergTerms_isMultiplicative
  have hG_ge_diff : ∏ p ∈ (Y + 1).primesBelow, (1 + s.selbergTerms p) -
      ∑ d ∈ PY.divisors.filter (Z < ·), s.selbergTerms d ≤ selbergG s Z := by
    have hsplit : ∑ d ∈ PY.divisors, s.selbergTerms d =
        ∑ d ∈ PY.divisors.filter (· ≤ Z), s.selbergTerms d +
        ∑ d ∈ PY.divisors.filter (Z < ·), s.selbergTerms d := by
      have hunion : PY.divisors = PY.divisors.filter (· ≤ Z) ∪ PY.divisors.filter (Z < ·) := by
        ext d; simp only [Finset.mem_union, Finset.mem_filter]
        exact ⟨fun h => by by_cases hd : d ≤ Z <;> [exact Or.inl ⟨h, hd⟩; exact Or.inr ⟨h, by omega⟩],
          by rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h⟩
      have hdisj : Disjoint (PY.divisors.filter (· ≤ Z)) (PY.divisors.filter (Z < ·)) := by
        rw [Finset.disjoint_left]; intro d h1 h2
        simp only [Finset.mem_filter] at h1 h2; omega
      conv_lhs => rw [hunion]
      exact Finset.sum_union hdisj
    have hsub : PY.divisors.filter (· ≤ Z) ⊆ (divisors s.prodPrimes).filter (· ≤ Z) := by
      intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors] at hd ⊢
      exact ⟨⟨dvd_trans hd.1.1 hPY_dvd, s.prodPrimes_ne_zero⟩, hd.2⟩
    have hle : ∑ d ∈ PY.divisors.filter (· ≤ Z), s.selbergTerms d ≤ selbergG s Z :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d hd _ =>
        (s.selbergTerms_pos (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1)).le)
    linarith
  let σ : ℝ := 1 / Real.log (Y : ℝ)
  have hσ_pos : 0 < σ := by positivity
  let fσ : ArithmeticFunction ℝ :=
    { toFun := fun d => if d = 0 then 0 else s.selbergTerms d * (d : ℝ) ^ σ
      map_zero' := rfl }
  have hfσ_mult : fσ.IsMultiplicative := by
    constructor
    · simp [fσ, s.selbergTerms_isMultiplicative.1]
    · intro a b hcop
      by_cases ha : a = 0
      · simp [fσ, ha]
      by_cases hb0 : b = 0
      · simp [fσ, hb0]
      have hab : a * b ≠ 0 := Nat.mul_ne_zero ha hb0
      simp only [fσ, ArithmeticFunction.coe_mk, ha, hb0, hab, ite_false]
      rw [s.selbergTerms_isMultiplicative.2 hcop, Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
      ring
  have htail_le : ∑ d ∈ PY.divisors.filter (Z < ·), s.selbergTerms d ≤
      (Z : ℝ) ^ (-σ) * ∏ p ∈ (Y + 1).primesBelow, (1 + s.selbergTerms p * (p : ℝ) ^ σ) := by
    have hterm : ∀ d ∈ PY.divisors.filter (Z < ·),
        s.selbergTerms d ≤ (Z : ℝ) ^ (-σ) * fσ d := by
      intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors] at hd
      have hd_pos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
      have hZ_pos : (0 : ℝ) < Z := by exact_mod_cast (show 0 < Z by omega)
      have hd_ne : d ≠ 0 := by omega
      simp only [fσ, ArithmeticFunction.coe_mk, hd_ne, ite_false]
      have hg_nn : 0 ≤ s.selbergTerms d := (s.selbergTerms_pos (dvd_trans hd.1.1 hPY_dvd)).le
      have hZd : (Z : ℝ) ^ σ ≤ (d : ℝ) ^ σ :=
        Real.rpow_le_rpow hZ_pos.le (by exact_mod_cast hd.2.le) hσ_pos.le
      have h1 : 1 ≤ (Z : ℝ) ^ (-σ) * (d : ℝ) ^ σ := by
        rw [Real.rpow_neg hZ_pos.le, inv_mul_eq_div, one_le_div (Real.rpow_pos_of_pos hZ_pos _)]
        exact hZd
      calc s.selbergTerms d = s.selbergTerms d * 1 := (mul_one _).symm
        _ ≤ s.selbergTerms d * ((Z : ℝ) ^ (-σ) * (d : ℝ) ^ σ) :=
            mul_le_mul_of_nonneg_left h1 hg_nn
        _ = (Z : ℝ) ^ (-σ) * (s.selbergTerms d * (d : ℝ) ^ σ) := by ring
    calc ∑ d ∈ PY.divisors.filter (Z < ·), s.selbergTerms d
        ≤ ∑ d ∈ PY.divisors.filter (Z < ·), (Z : ℝ) ^ (-σ) * fσ d := Finset.sum_le_sum hterm
      _ = (Z : ℝ) ^ (-σ) * ∑ d ∈ PY.divisors.filter (Z < ·), fσ d := (Finset.mul_sum _ _ _).symm
      _ ≤ (Z : ℝ) ^ (-σ) * ∑ d ∈ PY.divisors, fσ d := by
          refine mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun d hd _ => ?_)
            (by positivity)
          simp only [fσ, ArithmeticFunction.coe_mk]
          split_ifs
          · exact le_rfl
          · exact mul_nonneg (s.selbergTerms_pos (dvd_trans (Nat.dvd_of_mem_divisors hd) hPY_dvd)).le
              (by positivity)
      _ = (Z : ℝ) ^ (-σ) * ∏ p ∈ (Y + 1).primesBelow, (1 + fσ p) := by
          rw [sum_divisors_prod_primes_eq_prod_one_add (fun p hp => Nat.prime_of_mem_primesBelow hp)
            fσ hfσ_mult]
      _ = (Z : ℝ) ^ (-σ) * ∏ p ∈ (Y + 1).primesBelow, (1 + s.selbergTerms p * (p : ℝ) ^ σ) := by
          congr 1
          refine Finset.prod_congr rfl fun p hp => ?_
          simp [fσ, (Nat.prime_of_mem_primesBelow hp).ne_zero]
  have hprod_pos : 0 < ∏ p ∈ (Y + 1).primesBelow, (1 + s.selbergTerms p) :=
    Finset.prod_pos (fun p hp => by
      have hpP : p ∣ s.prodPrimes := dvd_trans (Finset.dvd_prod_of_mem _ hp) hPY_dvd
      linarith [s.selbergTerms_pos hpP])
  have hratio : (Z : ℝ) ^ (-σ) * ∏ p ∈ (Y + 1).primesBelow, (1 + s.selbergTerms p * (p : ℝ) ^ σ) ≤
      (1 / 2) * ∏ p ∈ (Y + 1).primesBelow, (1 + s.selbergTerms p) := by
    rw [← div_le_iff₀ hprod_pos, mul_div_assoc, ← Finset.prod_div_distrib]
    have hstep_p : ∀ p ∈ (Y + 1).primesBelow,
        (1 + s.selbergTerms p * (p : ℝ) ^ σ) / (1 + s.selbergTerms p) ≤
          1 + s.selbergTerms p * ((p : ℝ) ^ σ - 1) := by
      intro p hp
      have hpP : p ∣ s.prodPrimes := dvd_trans (Finset.dvd_prod_of_mem _ hp) hPY_dvd
      have hgp : 0 < s.selbergTerms p := s.selbergTerms_pos hpP
      have hp1 : (1 : ℝ) ≤ (p : ℝ) ^ σ :=
        Real.one_le_rpow (by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_le) hσ_pos.le
      rw [div_le_iff₀ (by linarith)]
      have : 0 ≤ s.selbergTerms p ^ 2 * ((p : ℝ) ^ σ - 1) := by nlinarith
      nlinarith
    have hsum_bound : ∑ p ∈ (Y + 1).primesBelow, s.selbergTerms p * ((p : ℝ) ^ σ - 1) ≤
        28 * (k : ℝ) := by
      have hp_exp : ∀ p ∈ (Y + 1).primesBelow,
          (p : ℝ) ^ σ - 1 ≤ Real.exp 1 * σ * Real.log (p : ℕ) := by
        intro p hp
        have hp_pr := Nat.prime_of_mem_primesBelow hp
        have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
        have hpY : (p : ℝ) ≤ Y := by exact_mod_cast (Nat.lt_succ_iff.mp (Nat.mem_primesBelow.mp hp).1)
        have hu0 : 0 ≤ σ * Real.log (p : ℝ) :=
          mul_nonneg hσ_pos.le (Real.log_nonneg (by exact_mod_cast hp_pr.one_le))
        have hu1 : σ * Real.log (p : ℝ) ≤ 1 := by
          simp only [σ, one_div]
          rw [inv_mul_le_iff₀ hlogY_pos, mul_one]
          exact Real.log_le_log hp_pos hpY
        rw [Real.rpow_def_of_pos hp_pos, mul_comm (Real.log (p : ℝ)) σ]
        have hmvt : Real.exp (σ * Real.log (p : ℝ)) - 1 ≤ Real.exp 1 * (σ * Real.log (p : ℝ)) := by
          by_cases hu0' : σ * Real.log (p : ℝ) = 0
          · simp [hu0']
          · have hpos : 0 < σ * Real.log (p : ℝ) := lt_of_le_of_ne hu0 (Ne.symm hu0')
            obtain ⟨c, hc, hcm⟩ := exists_hasDerivAt_eq_slope Real.exp Real.exp hpos
              (fun x _ => Real.continuous_exp.continuousAt.continuousWithinAt)
              (fun x _ => Real.hasDerivAt_exp x)
            rw [Real.exp_zero, sub_zero, eq_div_iff hpos.ne'] at hcm
            have hce : Real.exp c ≤ Real.exp 1 := Real.exp_le_exp.mpr (hc.2.le.trans hu1)
            nlinarith
        linarith
      have hterm_le : ∀ p ∈ (Y + 1).primesBelow,
          s.selbergTerms p * ((p : ℝ) ^ σ - 1) ≤
            Real.exp 1 * σ *
              ((if p ≤ 2 * k then (p : ℝ) * Real.log (p : ℕ) else 0) +
               2 * (k : ℝ) * (Real.log (p : ℕ) / (p : ℕ))) := by
        intro p hp
        have hp_pr := Nat.prime_of_mem_primesBelow hp
        have hpP : p ∣ s.prodPrimes := dvd_trans (Finset.dvd_prod_of_mem _ hp) hPY_dvd
        have hgp_nn : 0 ≤ s.selbergTerms p := (s.selbergTerms_pos hpP).le
        have h1 := mul_le_mul_of_nonneg_left (hp_exp p hp) hgp_nn
        have hlogp_nn : 0 ≤ Real.log (p : ℕ) := Real.log_nonneg (by exact_mod_cast hp_pr.one_le)
        rw [hg_prime p hp] at h1
        have hxi_lt : xi m p < p := xi_lt_p_of_not_badVec hb hp_pr
        have hxi_le : xi m p ≤ k := xi_le_K_add_one_of_not_badVec hb hp_pr
        by_cases hp2k : p ≤ 2 * k
        · rw [if_pos hp2k, hg_prime p hp]
          have hfrac : (xi m p : ℝ) / ((p : ℝ) - xi m p) ≤ (p : ℝ) := by
            have hden : (1 : ℝ) ≤ (p : ℝ) - xi m p := by
              have : 1 ≤ p - xi m p := by omega
              have hc : ((1 : ℕ) : ℝ) ≤ ((p - xi m p : ℕ) : ℝ) := by exact_mod_cast this
              rw [Nat.cast_sub hxi_lt.le, Nat.cast_one] at hc; exact hc
            have hnum : (xi m p : ℝ) ≤ p := by exact_mod_cast hxi_lt.le
            calc (xi m p : ℝ) / ((p : ℝ) - xi m p) ≤ (xi m p : ℝ) / 1 :=
                  div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
              _ ≤ p := by linarith
          have h2 : (xi m p : ℝ) / ((p : ℝ) - xi m p) * (Real.exp 1 * σ * Real.log (p : ℕ)) ≤
              Real.exp 1 * σ * ((p : ℝ) * Real.log (p : ℕ)) := by
            have : 0 ≤ Real.exp 1 * σ * Real.log (p : ℕ) := by positivity
            nlinarith
          have h3 : 0 ≤ Real.exp 1 * σ * (2 * (k : ℝ) * (Real.log (p : ℕ) / (p : ℕ))) := by
            positivity
          linarith
        · rw [if_neg hp2k, zero_add, hg_prime p hp]
          have hden : (p : ℝ) / 2 ≤ (p : ℝ) - xi m p := by
            have : 2 * xi m p ≤ p := by omega
            have hc : (2 : ℝ) * xi m p ≤ p := by exact_mod_cast this
            linarith
          have hfrac : (xi m p : ℝ) / ((p : ℝ) - xi m p) ≤ 2 * (k : ℝ) / (p : ℝ) := by
            have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
            calc (xi m p : ℝ) / ((p : ℝ) - xi m p)
                ≤ (k : ℝ) / ((p : ℝ) / 2) :=
                  div_le_div₀ (by positivity) (by exact_mod_cast hxi_le) (by positivity) hden
              _ = 2 * (k : ℝ) / (p : ℝ) := by ring
          have h2 : (xi m p : ℝ) / ((p : ℝ) - xi m p) * (Real.exp 1 * σ * Real.log (p : ℕ)) ≤
              Real.exp 1 * σ * (2 * (k : ℝ) * (Real.log (p : ℕ) / (p : ℕ))) := by
            have : 0 ≤ Real.exp 1 * σ * Real.log (p : ℕ) := by positivity
            calc _ ≤ (2 * (k : ℝ) / (p : ℝ)) * (Real.exp 1 * σ * Real.log (p : ℕ)) :=
                  mul_le_mul_of_nonneg_right hfrac this
              _ = Real.exp 1 * σ * (2 * (k : ℝ) * (Real.log (p : ℕ) / (p : ℕ))) := by ring
          linarith
      have hsmall : ∑ p ∈ (Y + 1).primesBelow, (if p ≤ 2 * k then (p : ℝ) * Real.log (p : ℕ) else 0) ≤
          (k : ℝ) * Real.log (Y : ℝ) := by
        rw [← Finset.sum_filter]
        have hsub : (Y + 1).primesBelow.filter (· ≤ 2 * k) ⊆ Icc 1 (2 * k) := by
          intro p hp
          simp only [Finset.mem_filter, Nat.mem_primesBelow, Finset.mem_Icc] at hp ⊢
          exact ⟨hp.1.2.one_le, hp.2⟩
        have hle1 : ∑ p ∈ (Y + 1).primesBelow.filter (· ≤ 2 * k), (p : ℝ) * Real.log (p : ℕ) ≤
            ∑ _p ∈ Icc 1 (2 * k), (2 * (k : ℝ)) * Real.log (2 * (k : ℝ)) := by
          calc ∑ p ∈ (Y + 1).primesBelow.filter (· ≤ 2 * k), (p : ℝ) * Real.log (p : ℕ)
              ≤ ∑ p ∈ (Y + 1).primesBelow.filter (· ≤ 2 * k), (2 * (k : ℝ)) * Real.log (2 * (k : ℝ)) := by
                refine Finset.sum_le_sum fun p hp => ?_
                have hp_pr := Nat.prime_of_mem_primesBelow (Finset.mem_filter.mp hp).1
                have hp2k : (p : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2
                have hlp : Real.log (p : ℕ) ≤ Real.log (2 * (k : ℝ)) :=
                  Real.log_le_log (by exact_mod_cast hp_pr.pos) hp2k
                exact mul_le_mul hp2k hlp (Real.log_nonneg (by exact_mod_cast hp_pr.one_le)) (by positivity)
            _ ≤ ∑ _p ∈ Icc 1 (2 * k), (2 * (k : ℝ)) * Real.log (2 * (k : ℝ)) := by
                refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => ?_)
                have : (1 : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast (show 1 ≤ 2 * k by omega)
                exact mul_nonneg (by positivity) (Real.log_nonneg this)
        simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul,
          Nat.cast_mul, Nat.cast_ofNat] at hle1
        have h4 : (2 * (k : ℝ)) * (2 * (k : ℝ) * Real.log (2 * (k : ℝ))) =
            (k : ℝ) * (4 * (k : ℝ) * Real.log (2 * (k : ℝ))) := by ring
        rw [h4] at hle1
        have hY' : 4 * (k : ℝ) * Real.log (2 * (k : ℝ)) ≤ Real.log (Y : ℝ) := by linarith only [hY_log]
        exact hle1.trans (mul_le_mul_of_nonneg_left hY' (by positivity))
      have hbig : ∑ p ∈ (Y + 1).primesBelow, (2 * (k : ℝ) * (Real.log (p : ℕ) / (p : ℕ))) ≤
          9 * (k : ℝ) * Real.log (Y : ℝ) := by
        rw [← Finset.mul_sum]
        have hch := sum_prime_log_div_le (x := (Y : ℝ)) (by exact_mod_cast (show 1 ≤ Y by omega))
        rw [Nat.floor_natCast] at hch
        have hY8 : (8 : ℝ) ≤ Real.log (Y : ℝ) := by
          have : 0 ≤ 4 * (k : ℝ) * Real.log (2 * (k : ℝ)) := by
            have : (1 : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast (show 1 ≤ 2 * k by omega)
            exact mul_nonneg (by positivity) (Real.log_nonneg this)
          linarith only [hY_log, this]
        nlinarith only [hch, hY8, show (0 : ℝ) ≤ 2 * (k : ℝ) by positivity]
      calc ∑ p ∈ (Y + 1).primesBelow, s.selbergTerms p * ((p : ℝ) ^ σ - 1)
          ≤ ∑ p ∈ (Y + 1).primesBelow,
              Real.exp 1 * σ *
                ((if p ≤ 2 * k then (p : ℝ) * Real.log (p : ℕ) else 0) +
                 2 * (k : ℝ) * (Real.log (p : ℕ) / (p : ℕ))) := Finset.sum_le_sum hterm_le
        _ = Real.exp 1 * σ *
              ((∑ p ∈ (Y + 1).primesBelow, if p ≤ 2 * k then (p : ℝ) * Real.log (p : ℕ) else 0) +
               ∑ p ∈ (Y + 1).primesBelow, 2 * (k : ℝ) * (Real.log (p : ℕ) / (p : ℕ))) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib]
        _ ≤ Real.exp 1 * σ * ((k : ℝ) * Real.log (Y : ℝ) + 9 * (k : ℝ) * Real.log (Y : ℝ)) := by
            gcongr
        _ = 10 * Real.exp 1 * (k : ℝ) := by
            simp only [σ]; field_simp [hlogY_pos.ne']; ring
        _ ≤ 28 * (k : ℝ) := by
            have he := Real.exp_one_lt_d9
            nlinarith only [he, show (0 : ℝ) ≤ (k : ℝ) by positivity]
    have hZpos : (0 : ℝ) < Z := by exact_mod_cast (show 0 < Z by omega)
    calc (Z : ℝ) ^ (-σ) * ∏ p ∈ (Y + 1).primesBelow,
            (1 + s.selbergTerms p * (p : ℝ) ^ σ) / (1 + s.selbergTerms p)
        ≤ (Z : ℝ) ^ (-σ) * ∏ p ∈ (Y + 1).primesBelow,
            (1 + s.selbergTerms p * ((p : ℝ) ^ σ - 1)) := by
          refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun p hp => ?_) hstep_p) (by positivity)
          have hpP : p ∣ s.prodPrimes := dvd_trans (Finset.dvd_prod_of_mem _ hp) hPY_dvd
          have hgp : 0 < s.selbergTerms p := s.selbergTerms_pos hpP
          positivity
      _ ≤ (Z : ℝ) ^ (-σ) * Real.exp (∑ p ∈ (Y + 1).primesBelow,
            s.selbergTerms p * ((p : ℝ) ^ σ - 1)) := by
          gcongr
          refine prod_one_add_le_exp_sum _ _ (fun p hp => ?_)
          have hpP : p ∣ s.prodPrimes := dvd_trans (Finset.dvd_prod_of_mem _ hp) hPY_dvd
          have hgp : 0 < s.selbergTerms p := s.selbergTerms_pos hpP
          have hp1 : (1 : ℝ) ≤ (p : ℝ) ^ σ :=
            Real.one_le_rpow (by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_le) hσ_pos.le
          nlinarith only [hgp, hp1]
      _ = Real.exp (-σ * Real.log (Z : ℝ) + ∑ p ∈ (Y + 1).primesBelow,
            s.selbergTerms p * ((p : ℝ) ^ σ - 1)) := by
          rw [Real.rpow_def_of_pos hZpos, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-2) := by
          apply Real.exp_le_exp.mpr
          have hσZ : 30 * (k : ℝ) ≤ σ * Real.log (Z : ℝ) := by
            simp only [σ, one_div]
            rw [le_inv_mul_iff₀ hlogY_pos]
            linarith only [hZY]
          have hk_ge1 : (1 : ℝ) ≤ k := by exact_mod_cast hk1
          linarith only [hσZ, hsum_bound, hk_ge1]
      _ ≤ 1 / 2 := by
          have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
          have h2 : (4 : ℝ) ≤ Real.exp 2 := by
            rw [show (2 : ℝ) = (2 : ℕ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]
            nlinarith only [he]
          rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
          norm_num; linarith only [h2]
  have hprod_rew : ∏ p ∈ (Y + 1).primesBelow, (1 - (xi m p : ℝ) / p)⁻¹ =
      ∏ p ∈ (Y + 1).primesBelow, (1 + s.selbergTerms p) :=
    Finset.prod_congr rfl fun p hp => (hone_add_g p hp).symm
  rw [hprod_rew]
  linarith only [hG_ge_diff, htail_le, hratio]

lemma prod_inv_one_sub_xi_ge {K : ℕ} (m : Fin K → ℕ) (hm : ∀ i, 1 ≤ m i) (hb : ¬ badVec m)
    {Y : ℕ} (hY_min : max (4 * (K + 1) ^ 2) 2 ≤ Y) :
    (Real.log ((Y : ℝ) + 1)) ^ (K + 1) / (2 * singSeries m) ≤
      ∏ p ∈ (Y + 1).primesBelow, (1 - (xi m p : ℝ) / p)⁻¹ := by
  let k := K + 1
  have hY2 : 2 ≤ Y := le_trans (le_max_right _ _) hY_min
  have hY4k2 : 4 * k ^ 2 ≤ Y := le_trans (le_max_left _ _) hY_min
  have hk_le_Y : k ≤ Y := by
    have hkk : k ≤ k ^ 2 := Nat.le_self_pow (by norm_num) k
    omega
  let M_big := max (max Y (Nm m)) (rParam K)
  have hY_le_M : Y ≤ M_big := le_trans (le_max_left _ _) (le_max_left _ _)
  have hNm_le_M : Nm m ≤ M_big := le_trans (le_max_right _ _) (le_max_left _ _)
  have hr_le_M : rParam K ≤ M_big := le_max_right _ _
  let ef : ℕ → ℝ := fun p => (1 - (xi m p : ℝ) / p) * (1 - 1 / (p : ℝ))⁻¹ ^ k
  have hef_pos : ∀ p, p.Prime → 0 < ef p := by
    intro p hp_pr
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
    have hxi_lt : (xi m p : ℝ) < p := by exact_mod_cast xi_lt_p_of_not_badVec hb hp_pr
    have h1 : 0 < 1 - (xi m p : ℝ) / p := by rw [sub_pos, div_lt_one hp_pos]; exact hxi_lt
    have h2 : 0 < 1 - 1 / (p : ℝ) := by
      rw [sub_pos, div_lt_one hp_pos]; exact_mod_cast hp_pr.one_lt
    positivity
  have hprod_M_le : ∏ p ∈ (M_big + 1).primesBelow, ef p ≤ singSeries m := by
    classical
    unfold singSeries
    rw [if_neg hb]
    let P0 := (Nm m).primeFactors ∪ (rParam K + 1).primesBelow
    have hP0_sub : P0 ⊆ (M_big + 1).primesBelow := by
      intro p hp
      rw [Nat.mem_primesBelow]
      rcases Finset.mem_union.mp hp with h1 | h2
      · rw [Nat.mem_primeFactors] at h1
        have hle : p ≤ Nm m := Nat.le_of_dvd (Nat.pos_of_ne_zero h1.2.2) h1.2.1
        exact ⟨Nat.lt_succ_of_le (hle.trans hNm_le_M), h1.1⟩
      · rw [Nat.mem_primesBelow] at h2
        exact ⟨Nat.lt_succ_of_le ((Nat.lt_succ_iff.mp h2.1).trans hr_le_M), h2.2⟩
    rw [← Finset.prod_sdiff hP0_sub]
    have htail_le1 : ∏ p ∈ (M_big + 1).primesBelow \ P0, ef p ≤ 1 := by
      refine Finset.prod_le_one (fun p hp => (hef_pos p (Nat.prime_of_mem_primesBelow
        (Finset.mem_sdiff.mp hp).1)).le) (fun p hp => ?_)
      rw [Finset.mem_sdiff] at hp
      have hp_pr := Nat.prime_of_mem_primesBelow hp.1
      have hnd : ¬ p ∣ Nm m := fun hd =>
        hp.2 (Finset.mem_union_left _ (Nat.mem_primeFactors.mpr
          ⟨hp_pr, hd, Nat.one_le_iff_ne_zero.mp (Nm_pos m hm)⟩))
      have hxeq : xi m p = k := xi_eq_of_not_dvd_Nm m hp_pr hnd
      have hxlt : xi m p < p := xi_lt_p_of_not_badVec hb hp_pr
      simp only [ef, hxeq]
      exact euler_factor_le_one (by omega)
    have hP0_nn : 0 ≤ ∏ p ∈ P0, ef p :=
      Finset.prod_nonneg (fun p hp => (hef_pos p (by
        rcases Finset.mem_union.mp hp with h1 | h2
        · exact Nat.prime_of_mem_primeFactors h1
        · exact Nat.prime_of_mem_primesBelow h2)).le)
    nlinarith only [htail_le1, hP0_nn]
  have htail_ge_half : (1 / 2 : ℝ) ≤ ∏ p ∈ (M_big + 1).primesBelow \ (Y + 1).primesBelow, ef p := by
    have hterm : ∀ p ∈ (M_big + 1).primesBelow \ (Y + 1).primesBelow,
        1 - (k : ℝ) ^ 2 / (p : ℝ) ^ 2 ≤ ef p := by
      intro p hp
      rw [Finset.mem_sdiff, Nat.mem_primesBelow, Nat.mem_primesBelow] at hp
      have hp_pr := hp.1.2
      have hp_gtY : Y < p := by
        by_contra hle; push Not at hle
        exact hp.2 ⟨Nat.lt_succ_of_le hle, hp_pr⟩
      exact euler_factor_ge_one_sub_sq (lt_of_le_of_lt hk_le_Y hp_gtY)
        (xi_le_K_add_one_of_not_badVec hb hp_pr)
    have ha0 : ∀ p ∈ (M_big + 1).primesBelow \ (Y + 1).primesBelow,
        0 ≤ (k : ℝ) ^ 2 / (p : ℝ) ^ 2 := fun _ _ => by positivity
    have ha1 : ∀ p ∈ (M_big + 1).primesBelow \ (Y + 1).primesBelow,
        (k : ℝ) ^ 2 / (p : ℝ) ^ 2 ≤ 1 := by
      intro p hp
      rw [Finset.mem_sdiff, Nat.mem_primesBelow, Nat.mem_primesBelow] at hp
      have hp_gtY : Y < p := by
        by_contra hle; push Not at hle
        exact hp.2 ⟨Nat.lt_succ_of_le hle, hp.1.2⟩
      have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.1.2.pos
      rw [div_le_one (by positivity)]
      have hkp : (k : ℝ) ≤ p := by exact_mod_cast (le_of_lt (lt_of_le_of_lt hk_le_Y hp_gtY))
      exact pow_le_pow_left₀ (by positivity) hkp 2
    have hsum_tail : ∑ p ∈ (M_big + 1).primesBelow \ (Y + 1).primesBelow,
        (k : ℝ) ^ 2 / (p : ℝ) ^ 2 ≤ 1 / 2 := by
      have hsub : (M_big + 1).primesBelow \ (Y + 1).primesBelow ⊆ Icc (Y + 1) M_big := by
        intro p hp
        rw [Finset.mem_sdiff, Nat.mem_primesBelow, Nat.mem_primesBelow] at hp
        rw [Finset.mem_Icc]
        have hp_gtY : Y < p := by
          by_contra hle; push Not at hle
          exact hp.2 ⟨Nat.lt_succ_of_le hle, hp.1.2⟩
        exact ⟨hp_gtY, Nat.lt_succ_iff.mp hp.1.1⟩
      calc ∑ p ∈ (M_big + 1).primesBelow \ (Y + 1).primesBelow, (k : ℝ) ^ 2 / (p : ℝ) ^ 2
          ≤ ∑ n ∈ Icc (Y + 1) M_big, (k : ℝ) ^ 2 / (n : ℝ) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
        _ = (k : ℝ) ^ 2 * ∑ n ∈ Icc (Y + 1) M_big, (1 / (n : ℝ) ^ 2) := by
            rw [Finset.mul_sum]; congr 1 with n; ring
        _ ≤ (k : ℝ) ^ 2 * (1 / (Y : ℝ)) := by
            gcongr; exact sum_inv_sq_tail Y M_big (by omega)
        _ ≤ 1 / 2 := by
            rw [mul_one_div, div_le_div_iff₀ (by exact_mod_cast (show 0 < Y by omega)) (by norm_num)]
            have : (4 : ℝ) * (k : ℝ) ^ 2 ≤ Y := by exact_mod_cast hY4k2
            linarith only [this]
    calc (1 / 2 : ℝ) ≤ 1 - ∑ p ∈ (M_big + 1).primesBelow \ (Y + 1).primesBelow,
            (k : ℝ) ^ 2 / (p : ℝ) ^ 2 := by linarith only [hsum_tail]
      _ ≤ ∏ p ∈ (M_big + 1).primesBelow \ (Y + 1).primesBelow,
            (1 - (k : ℝ) ^ 2 / (p : ℝ) ^ 2) :=
          prod_one_sub_ge_one_sub_sum _ _ ha0 ha1
      _ ≤ ∏ p ∈ (M_big + 1).primesBelow \ (Y + 1).primesBelow, ef p :=
          Finset.prod_le_prod (fun p hp => by linarith only [ha1 p hp]) hterm
  have hY_ef_pos : 0 < ∏ p ∈ (Y + 1).primesBelow, ef p :=
    Finset.prod_pos (fun p hp => hef_pos p (Nat.prime_of_mem_primesBelow hp))
  have hY_ef_le : ∏ p ∈ (Y + 1).primesBelow, ef p ≤ 2 * singSeries m := by
    have hsub : (Y + 1).primesBelow ⊆ (M_big + 1).primesBelow :=
      Nat.primesBelow_mono (Nat.succ_le_succ hY_le_M)
    have hsplit := Finset.prod_sdiff hsub (f := ef)
    have hprod_ge : (1 / 2) * (∏ p ∈ (Y + 1).primesBelow, ef p) ≤
        ∏ p ∈ (M_big + 1).primesBelow, ef p := by
      rw [← hsplit]
      exact mul_le_mul_of_nonneg_right htail_ge_half hY_ef_pos.le
    linarith only [hprod_ge, hprod_M_le]
  have hprod_id : ∏ p ∈ (Y + 1).primesBelow, (1 - (xi m p : ℝ) / p)⁻¹ =
      (∏ p ∈ (Y + 1).primesBelow, (1 - 1 / (p : ℝ))⁻¹) ^ k /
        ∏ p ∈ (Y + 1).primesBelow, ef p := by
    rw [eq_div_iff hY_ef_pos.ne', ← Finset.prod_mul_distrib, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun p hp => ?_
    simp only [ef]
    have hp_pr := Nat.prime_of_mem_primesBelow hp
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
    have hxi_lt : (xi m p : ℝ) < p := by exact_mod_cast xi_lt_p_of_not_badVec hb hp_pr
    have hne : 1 - (xi m p : ℝ) / p ≠ 0 := by
      have : (xi m p : ℝ) / p < 1 := (div_lt_one hp_pos).mpr hxi_lt
      linarith only [this]
    rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hlogY1 : Real.log ((Y : ℝ) + 1) ≤ ∏ p ∈ (Y + 1).primesBelow, (1 - 1 / (p : ℝ))⁻¹ :=
    prod_one_sub_inv_ge_log Y (by omega)
  have hlogY1_nn : 0 ≤ Real.log ((Y : ℝ) + 1) := by
    apply Real.log_nonneg
    have hY1 : (1 : ℝ) ≤ Y := by exact_mod_cast (show 1 ≤ Y by omega)
    linarith only [hY1]
  rw [hprod_id]
  exact div_le_div₀ (pow_nonneg (le_trans hlogY1_nn hlogY1) k)
    (pow_le_pow_left₀ hlogY1_nn hlogY1 k) hY_ef_pos hY_ef_le

lemma selbergG_lower_bound {K : ℕ} (m : Fin K → ℕ) (hm : ∀ i, 1 ≤ m i) (hb : ¬ badVec m)
    (X : ℕ) {Z Y : ℕ} (hYZ : Y ≤ Z)
    (hY_min : max (4 * (K + 1) ^ 2) 2 ≤ Y)
    (hY_log : 4 * ((K + 1 : ℕ) : ℝ) * Real.log (2 * ((K + 1 : ℕ) : ℝ)) + 8 ≤ Real.log (Y : ℝ))
    (hZY : 30 * ((K + 1 : ℕ) : ℝ) * Real.log (Y : ℝ) ≤ Real.log (Z : ℝ)) :
    (Real.log ((Y : ℝ) + 1)) ^ (K + 1) / (4 * singSeries m) ≤
      selbergG (chainSieve m hb X Z) Z := by
  have h1 := selbergG_ge_half_prod m hb X hYZ (le_trans (le_max_right _ _) hY_min) hY_log hZY
  have h2 := prod_inv_one_sub_xi_ge m hm hb hY_min
  calc (Real.log ((Y : ℝ) + 1)) ^ (K + 1) / (4 * singSeries m)
      = (1 / 2) * ((Real.log ((Y : ℝ) + 1)) ^ (K + 1) / (2 * singSeries m)) := by ring
    _ ≤ (1 / 2) * ∏ p ∈ (Y + 1).primesBelow, (1 - (xi m p : ℝ) / p)⁻¹ :=
        mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ ≤ selbergG (chainSieve m hb X Z) Z := h1

/- Final Selberg upper bound theorem for prime chains -/

open Classical in
theorem sieve_upper_bound (K : ℕ) :
    ∃ X₀ : ℝ, 4 ≤ X₀ ∧ ∀ X : ℕ, X₀ ≤ (X : ℝ) →
      ∀ m : Fin K → ℕ, (∀ i, 1 ≤ m i) →
        (((Icc 1 X).filter (fun n => ∀ j ∈ range (K + 1), (chainForm m j n).Prime)).card : ℝ) ≤
          4 * (200 * (K + 1 : ℝ)) ^ (K + 1) * singSeries m * X / (Real.log X) ^ (K + 1) +
            2 * (X : ℝ) ^ ((4 : ℝ) / 5) := by
  let k := K + 1
  -- Pick X₀ large enough so Z = ⌊X^(1/5)⌋₊ and Y = ⌊Z^(1/(30*k))⌋₊ satisfy all side conditions
  let c_log : ℝ := max (max (4 * (k : ℝ) * Real.log (2 * (k : ℝ)) + 8) (Real.log (4 * (k : ℝ) ^ 2 + 2)))
    (max (Real.log (K + 2 : ℝ)) 400)
  let X₀ : ℝ := max 4 (Real.exp (300 * (k : ℝ) * c_log))
  refine ⟨X₀, le_max_left _ _, fun X hX m hm => ?_⟩
  have hX4 : (4 : ℝ) ≤ X := le_trans (le_max_left _ _) hX
  have hX_pos : (0 : ℝ) < X := by linarith
  have hlogX_ge : 300 * (k : ℝ) * c_log ≤ Real.log (X : ℝ) := by
    have h1 : Real.exp (300 * (k : ℝ) * c_log) ≤ X := le_trans (le_max_right _ _) hX
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  have hc_log_ge400 : (400 : ℝ) ≤ c_log := le_trans (le_max_right _ _) (le_max_right _ _)
  have hk_ge1 : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.succ_pos K)
  have hlogX_pos : 0 < Real.log (X : ℝ) := by nlinarith
  let Z : ℕ := ⌊(X : ℝ) ^ ((1 : ℝ) / 5)⌋₊
  have hX15_ge : Real.exp (60 * (k : ℝ) * c_log) ≤ (X : ℝ) ^ ((1 : ℝ) / 5) := by
    rw [Real.rpow_def_of_pos hX_pos]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hZ_ge_exp : Real.exp (60 * (k : ℝ) * c_log) - 1 ≤ (Z : ℝ) := by
    linarith [Nat.lt_floor_add_one ((X : ℝ) ^ ((1 : ℝ) / 5))]
  have hZ_ge_half : (1 / 2) * Real.exp (60 * (k : ℝ) * c_log) ≤ (Z : ℝ) := by
    have hexp_ge2 : (2 : ℝ) ≤ Real.exp (60 * (k : ℝ) * c_log) := by
      have : (1 : ℝ) ≤ 60 * (k : ℝ) * c_log := by nlinarith
      linarith [Real.add_one_le_exp (60 * (k : ℝ) * c_log)]
    linarith
  have hZ_le_X15 : (Z : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 5) := Nat.floor_le (by positivity)
  have hZ1 : 1 ≤ Z := by
    have : (1 : ℝ) ≤ Z := by
      have : (2 : ℝ) ≤ Real.exp (60 * (k : ℝ) * c_log) := by
        have : (1 : ℝ) ≤ 60 * (k : ℝ) * c_log := by nlinarith
        linarith [Real.add_one_le_exp (60 * (k : ℝ) * c_log)]
      linarith
    exact_mod_cast this
  have hZ_add_le : (Z : ℝ) + (K : ℝ) + 1 ≤ (X : ℝ) ^ ((4 : ℝ) / 5) := by
    have hX15_le : (X : ℝ) ^ ((1 : ℝ) / 5) ≤ (1 / 2) * (X : ℝ) ^ ((4 : ℝ) / 5) := by
      have hdiv : (X : ℝ) ^ ((4 : ℝ) / 5) / (X : ℝ) ^ ((1 : ℝ) / 5) = (X : ℝ) ^ ((3 : ℝ) / 5) := by
        rw [← Real.rpow_sub hX_pos]; norm_num
      have h35 : (2 : ℝ) ≤ (X : ℝ) ^ ((3 : ℝ) / 5) := by
        rw [Real.rpow_def_of_pos hX_pos]
        have : (1 : ℝ) ≤ Real.log (X : ℝ) * (3 / 5) := by nlinarith
        linarith [Real.add_one_le_exp (Real.log (X : ℝ) * (3 / 5))]
      rw [← hdiv, le_div_iff₀ (by positivity)] at h35
      linarith
    have hK_le : (K : ℝ) + 1 ≤ (1 / 2) * (X : ℝ) ^ ((4 : ℝ) / 5) := by
      have hK_exp : (K : ℝ) + 2 ≤ Real.exp c_log := by
        have hle : Real.log (K + 2 : ℝ) ≤ c_log :=
          le_trans (le_max_left _ _) (le_max_right _ _)
        calc (K : ℝ) + 2 = Real.exp (Real.log (K + 2 : ℝ)) := (Real.exp_log (by positivity)).symm
          _ ≤ Real.exp c_log := Real.exp_le_exp.mpr hle
      have hexp_le : Real.exp c_log ≤ (1 / 2) * (X : ℝ) ^ ((4 : ℝ) / 5) := by
        rw [Real.rpow_def_of_pos hX_pos]
        have : Real.log 2 + c_log ≤ Real.log (X : ℝ) * (4 / 5) := by
          have := Real.log_two_lt_d9; nlinarith
        have h1 := Real.exp_le_exp.mpr this
        rw [Real.exp_add, Real.exp_log (by norm_num)] at h1
        linarith
      linarith
    linarith
  by_cases hb : badVec m
  · have hcard := badVec_card_le m hm hb X Z
    have hcardR : (((Icc 1 X).filter (fun n => ∀ j ∈ range (K + 1), (chainForm m j n).Prime)).card : ℝ) ≤
        (Z : ℝ) + K + 1 := by exact_mod_cast hcard
    have hmain_nn : 0 ≤ 4 * (200 * (K + 1 : ℝ)) ^ (K + 1) * singSeries m * X / (Real.log X) ^ (K + 1) := by
      have := singSeries_nonneg m
      positivity
    have h45_nn : 0 ≤ (X : ℝ) ^ ((4 : ℝ) / 5) := by positivity
    linarith
  · -- Non-bad case: apply Selberg sieve!
    let s := chainSieve m hb X Z
    have hprime_le : (((Icc 1 X).filter (fun n => ∀ j ∈ range (K + 1), (chainForm m j n).Prime)).card : ℝ) ≤
        (Z : ℝ) + s.siftedSum := by
      let A := (Icc 1 X).filter (fun n => ∀ j ∈ range (K + 1), (chainForm m j n).Prime)
      let A1 := A.filter (· ≤ Z)
      let A2 := A.filter (Z < ·)
      have hunion : A = A1 ∪ A2 := by
        ext n; simp only [A1, A2, Finset.mem_union, Finset.mem_filter]
        exact ⟨fun h => by by_cases hn : n ≤ Z <;> [exact Or.inl ⟨h, hn⟩; exact Or.inr ⟨h, by omega⟩],
          by rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h⟩
      have hdisj : Disjoint A1 A2 := by
        rw [Finset.disjoint_left]; intro n h1 h2
        simp only [A1, A2, Finset.mem_filter] at h1 h2; omega
      have hA1 : A1.card ≤ Z := by
        have hsub : A1 ⊆ Icc 1 Z := by
          intro n hn
          simp only [A1, A, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
          exact ⟨hn.1.1.1, hn.2⟩
        exact (Finset.card_le_card hsub).trans (by simp)
      have hA2 : (A2.card : ℝ) ≤ s.siftedSum := by
        unfold BoundingSieve.siftedSum
        simp only [s, chainSieve, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
        norm_cast
        have hsub : A2.image (chainProd m) ⊆
            ((Icc 1 X).image (chainProd m)).filter (fun y => Nat.Coprime (∏ p ∈ (Z + 1).primesBelow, p) y) := by
          intro y hy
          rw [Finset.mem_image] at hy
          obtain ⟨n, hn, rfl⟩ := hy
          simp only [A2, A, Finset.mem_filter] at hn
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_image_of_mem _ hn.1.1, ?_⟩
          refine Nat.Coprime.prod_left fun p hp => ?_
          have hp_pr := Nat.prime_of_mem_primesBelow hp
          have hp_leZ : p ≤ Z := Nat.lt_succ_iff.mp (Nat.mem_primesBelow.mp hp).1
          rw [hp_pr.coprime_iff_not_dvd]
          intro hdvd
          obtain ⟨j, hj, hpdvd⟩ := (hp_pr.prime.dvd_finsetProd_iff _).mp hdvd
          have hfj_pr := hn.1.2 j hj
          have heq : p = chainForm m j n := (Nat.prime_dvd_prime_iff_eq hp_pr hfj_pr).mp hpdvd
          have hle : n ≤ chainForm m j n := chainForm_ge_self m hm j n
          omega
        calc A2.card = (A2.image (chainProd m)).card :=
              (Finset.card_image_of_injective _ (chainProd_strictMono m hm).injective).symm
          _ ≤ _ := Finset.card_le_card hsub
      have hcard_eq : A.card = A1.card + A2.card := by
        rw [hunion, Finset.card_union_of_disjoint hdisj]
      have hA1R : (A1.card : ℝ) ≤ Z := by exact_mod_cast hA1
      rw [show ((Icc 1 X).filter (fun n => ∀ j ∈ range (K + 1), (chainForm m j n).Prime)).card = A.card from rfl,
        hcard_eq, Nat.cast_add]
      linarith
    have hsieve := s.siftedSum_le_mainSum_errSum_of_upperMoebius
      (BoundingSieve.lambdaSquared (selbergW s Z))
      (BoundingSieve.upperMoebius_lambdaSquared (selbergW s Z) (selbergW_one s hZ1))
    rw [selberg_mainSum_eq_inv_G s hZ1] at hsieve
    have herr := selberg_errSum_le m hm hb X Z hZ1
    have hZ4_le : (Z : ℝ) ^ 4 ≤ (X : ℝ) ^ ((4 : ℝ) / 5) := by
      calc (Z : ℝ) ^ 4 ≤ ((X : ℝ) ^ ((1 : ℝ) / 5)) ^ 4 := by gcongr
        _ = (X : ℝ) ^ ((1 : ℝ) / 5 * (4 : ℕ)) := (Real.rpow_natCast _ 4) ▸ (Real.rpow_mul hX_pos.le _ _).symm
        _ = (X : ℝ) ^ ((4 : ℝ) / 5) := by norm_num
    -- Lower bound on G using Y = ⌊Z^(1/(30*k))⌋₊
    let Y : ℕ := ⌊(Z : ℝ) ^ (1 / (30 * (k : ℝ)))⌋₊
    have hZ_pos : (0 : ℝ) < Z := by exact_mod_cast (show 0 < Z by omega)
    have hlogZ_ge : 59 * (k : ℝ) * c_log ≤ Real.log (Z : ℝ) := by
      have h1 := Real.log_le_log (by positivity) hZ_ge_half
      rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at h1
      have h2 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
      have h3 := Real.log_two_lt_d9
      nlinarith
    have hlogZ_le : Real.log (Z : ℝ) ≤ (1 / 5) * Real.log (X : ℝ) := by
      calc Real.log (Z : ℝ) ≤ Real.log ((X : ℝ) ^ ((1 : ℝ) / 5)) := Real.log_le_log hZ_pos hZ_le_X15
        _ = (1 / 5) * Real.log (X : ℝ) := by rw [Real.log_rpow hX_pos]
    have hlogZ_ge_X : (1 / 6) * Real.log (X : ℝ) ≤ Real.log (Z : ℝ) := by
      have h1 : (1 / 2) * (X : ℝ) ^ ((1 : ℝ) / 5) ≤ Z := by
        have hX15_ge2 : (2 : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 5) := by
          have : (1 : ℝ) ≤ 60 * (k : ℝ) * c_log := by nlinarith
          linarith [Real.add_one_le_exp (60 * (k : ℝ) * c_log)]
        linarith [Nat.lt_floor_add_one ((X : ℝ) ^ ((1 : ℝ) / 5))]
      have h2 := Real.log_le_log (by positivity) h1
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hX_pos, one_div, Real.log_inv] at h2
      have h3 := Real.log_two_lt_d9
      nlinarith
    have hY_le_Z : Y ≤ Z := by
      have h1 : (Z : ℝ) ^ (1 / (30 * (k : ℝ))) ≤ Z := by
        have hZ1' : (1 : ℝ) ≤ Z := by exact_mod_cast hZ1
        have hexp : 1 / (30 * (k : ℝ)) ≤ 1 := by
          rw [div_le_one (by positivity)]; nlinarith
        simpa using Real.rpow_le_rpow_of_exponent_le hZ1' hexp
      exact Nat.floor_le_of_le (by exact_mod_cast h1)
    have hZrpow_ge : Real.exp ((59 / 30) * c_log) ≤ (Z : ℝ) ^ (1 / (30 * (k : ℝ))) := by
      rw [Real.rpow_def_of_pos hZ_pos]
      apply Real.exp_le_exp.mpr
      have : (59 / 30 : ℝ) * c_log * (30 * (k : ℝ)) = 59 * (k : ℝ) * c_log := by ring
      rw [mul_one_div, le_div_iff₀ (by positivity)]
      linarith
    have hY_ge_half : (1 / 2) * Real.exp ((59 / 30) * c_log) ≤ (Y : ℝ) := by
      have hge2 : (2 : ℝ) ≤ Real.exp ((59 / 30) * c_log) := by
        have : (1 : ℝ) ≤ (59 / 30) * c_log := by nlinarith
        linarith [Real.add_one_le_exp ((59 / 30) * c_log)]
      linarith [Nat.lt_floor_add_one ((Z : ℝ) ^ (1 / (30 * (k : ℝ))))]
    have hY_pos : (0 : ℝ) < Y := by
      have : 0 < (1 / 2) * Real.exp ((59 / 30) * c_log) := by positivity
      linarith
    have hlogY_ge_c : c_log ≤ Real.log (Y : ℝ) := by
      have h1 := Real.log_le_log (by positivity) hY_ge_half
      rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp, one_div, Real.log_inv] at h1
      have h3 := Real.log_two_lt_d9
      linarith
    have hY_min : max (4 * k ^ 2) 2 ≤ Y := by
      have h1 : (4 * (k : ℝ) ^ 2 + 2) ≤ (Y : ℝ) := by
        have hc2 : Real.log (4 * (k : ℝ) ^ 2 + 2) ≤ c_log :=
          le_trans (le_max_right _ _) (le_max_left _ _)
        calc 4 * (k : ℝ) ^ 2 + 2 = Real.exp (Real.log (4 * (k : ℝ) ^ 2 + 2)) :=
              (Real.exp_log (by positivity)).symm
          _ ≤ Real.exp (Real.log (Y : ℝ)) := Real.exp_le_exp.mpr (hc2.trans hlogY_ge_c)
          _ = Y := Real.exp_log hY_pos
      have hnat : 4 * k ^ 2 + 2 ≤ Y := by exact_mod_cast h1
      omega
    have hY_log : 4 * (k : ℝ) * Real.log (2 * (k : ℝ)) + 8 ≤ Real.log (Y : ℝ) :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hlogY_ge_c
    have hZY : 30 * (k : ℝ) * Real.log (Y : ℝ) ≤ Real.log (Z : ℝ) := by
      have hY_le : (Y : ℝ) ≤ (Z : ℝ) ^ (1 / (30 * (k : ℝ))) := Nat.floor_le (by positivity)
      have h1 := Real.log_le_log hY_pos hY_le
      rw [Real.log_rpow hZ_pos, one_div_mul_eq_div, le_div_iff₀ (by positivity)] at h1
      linarith
    have hG_lb : (Real.log ((Y : ℝ) + 1)) ^ k / (4 * singSeries m) ≤ selbergG s Z :=
      selbergG_lower_bound m hm hb X hY_le_Z hY_min hY_log hZY
    have hlogY1_ge : Real.log (X : ℝ) / (200 * (k : ℝ)) ≤ Real.log ((Y : ℝ) + 1) := by
      have h1 : (Z : ℝ) ^ (1 / (30 * (k : ℝ))) ≤ (Y : ℝ) + 1 :=
        (Nat.lt_floor_add_one _).le
      have h2 := Real.log_le_log (by positivity) h1
      rw [Real.log_rpow hZ_pos] at h2
      have h3 : Real.log (X : ℝ) / (200 * (k : ℝ)) ≤ (1 / (30 * (k : ℝ))) * Real.log (Z : ℝ) := by
        rw [one_div_mul_eq_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith only [hlogZ_ge_X, hk_ge1, hlogX_pos]
      linarith only [h2, h3]
    have hG_pos : 0 < selbergG s Z := lt_of_lt_of_le zero_lt_one (one_le_selbergG s hZ1)
    have hS_pos : 0 < singSeries m := singSeries_pos_of_not_badVec m hb
    have hmain_le : (X : ℝ) * (selbergG s Z)⁻¹ ≤
        4 * (200 * (k : ℝ)) ^ k * singSeries m * X / (Real.log (X : ℝ)) ^ k := by
      have hlb2 : (Real.log (X : ℝ) / (200 * (k : ℝ))) ^ k / (4 * singSeries m) ≤ selbergG s Z := by
        refine le_trans ?_ hG_lb
        gcongr
      have hlb_pos : 0 < (Real.log (X : ℝ) / (200 * (k : ℝ))) ^ k / (4 * singSeries m) := by
        positivity
      have hinv : (selbergG s Z)⁻¹ ≤
          ((Real.log (X : ℝ) / (200 * (k : ℝ))) ^ k / (4 * singSeries m))⁻¹ :=
        inv_anti₀ hlb_pos hlb2
      calc (X : ℝ) * (selbergG s Z)⁻¹
          ≤ (X : ℝ) * ((Real.log (X : ℝ) / (200 * (k : ℝ))) ^ k / (4 * singSeries m))⁻¹ :=
            mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = 4 * (200 * (k : ℝ)) ^ k * singSeries m * X / (Real.log (X : ℝ)) ^ k := by
            rw [inv_div, div_pow]; field_simp
    have hZ_le_X45 : (Z : ℝ) ≤ (X : ℝ) ^ ((4 : ℝ) / 5) := by linarith only [hZ_add_le, hk_ge1]
    have hs_mass : s.totalMass = (X : ℝ) := rfl
    rw [hs_mass] at hsieve
    have hk_eq : (k : ℝ) = (K : ℝ) + 1 := by simp [k]
    rw [hk_eq] at hmain_le
    linarith only [hprime_le, hsieve, herr, hZ4_le, hZ_le_X45, hmain_le]

end

/- ==================== Section 4: SingularAvg ==================== -/
section
open Finset Real Nat ArithmeticFunction

/- Elementary `psiR` and `betaS` convolution -/

noncomputable def psiR (r n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors.filter (r < ·), ((p : ℝ) / ((p : ℝ) - 1))

lemma psiR_pos (r n : ℕ) : 0 < psiR r n := by
  unfold psiR
  refine Finset.prod_pos fun p hp => ?_
  have hp_pr := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp_pr.two_le
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  positivity

noncomputable def betaS (r s : ℕ) : ArithmeticFunction ℝ where
  toFun d :=
    if d ≠ 0 ∧ Squarefree d ∧ ∀ p ∈ d.primeFactors, r < p then
      ∏ p ∈ d.primeFactors, (((p : ℝ) / ((p : ℝ) - 1)) ^ s - 1)
    else 0
  map_zero' := by simp

lemma betaS_nonneg (r s d : ℕ) : 0 ≤ betaS r s d := by
  simp only [betaS, ArithmeticFunction.coe_mk]
  split_ifs with h
  · refine Finset.prod_nonneg fun p hp => ?_
    have hp_pr := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp_pr.two_le
    have hge1 : (1 : ℝ) ≤ (p : ℝ) / ((p : ℝ) - 1) := by
      rw [one_le_div (by linarith)]; linarith
    have hpow : (1 : ℝ) ≤ ((p : ℝ) / ((p : ℝ) - 1)) ^ s := one_le_pow₀ hge1
    linarith
  · exact le_rfl

lemma betaS_isMultiplicative (r s : ℕ) : (betaS r s).IsMultiplicative := by
  constructor
  · simp [betaS]
  · intro a b hcop
    by_cases ha : a = 0
    · simp [betaS, ha]
    by_cases hb : b = 0
    · simp [betaS, hb]
    have hab : a * b ≠ 0 := Nat.mul_ne_zero ha hb
    have hpf : (a * b).primeFactors = a.primeFactors ∪ b.primeFactors := Nat.primeFactors_mul ha hb
    have hdisj : Disjoint a.primeFactors b.primeFactors := hcop.disjoint_primeFactors
    have hsq_iff : Squarefree (a * b) ↔ Squarefree a ∧ Squarefree b := by
      rw [Nat.squarefree_mul_iff]; exact ⟨fun h => h.2, fun h => ⟨hcop, h⟩⟩
    have hgt_iff : (∀ p ∈ (a * b).primeFactors, r < p) ↔
        (∀ p ∈ a.primeFactors, r < p) ∧ (∀ p ∈ b.primeFactors, r < p) := by
      rw [hpf]; simp only [Finset.mem_union]
      exact ⟨fun h => ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩,
        fun ⟨h1, h2⟩ p hp => hp.elim (h1 p) (h2 p)⟩
    simp only [betaS, ArithmeticFunction.coe_mk, hab, ha, hb, ne_eq, not_false_eq_true, true_and]
    by_cases h1 : Squarefree a ∧ ∀ p ∈ a.primeFactors, r < p
    · by_cases h2 : Squarefree b ∧ ∀ p ∈ b.primeFactors, r < p
      · rw [if_pos ⟨hsq_iff.mpr ⟨h1.1, h2.1⟩, hgt_iff.mpr ⟨h1.2, h2.2⟩⟩, if_pos h1, if_pos h2,
          hpf, Finset.prod_union hdisj]
      · rw [if_neg (fun h => h2 ⟨(hsq_iff.mp h.1).2, (hgt_iff.mp h.2).2⟩), if_neg h2, mul_zero]
    · rw [if_neg (fun h => h1 ⟨(hsq_iff.mp h.1).1, (hgt_iff.mp h.2).1⟩), if_neg h1, zero_mul]

lemma betaS_prime (r s p : ℕ) (hp : p.Prime) :
    betaS r s p = if r < p then ((p : ℝ) / ((p : ℝ) - 1)) ^ s - 1 else 0 := by
  simp only [betaS, ArithmeticFunction.coe_mk, hp.ne_zero, ne_eq, not_false_eq_true,
    hp.squarefree, hp.primeFactors, Finset.mem_singleton, forall_eq, true_and, Finset.prod_singleton]

lemma psiR_pow_eq_sum_betaS (r s n : ℕ) (hn : 1 ≤ n) :
    (psiR r n) ^ s = ∑ d ∈ n.divisors, betaS r s d := by
  let Pn := n.primeFactors.filter (r < ·)
  let Q := ∏ p ∈ Pn, p
  have hQ_dvd : Q ∣ n := by
    calc Q ∣ ∏ p ∈ n.primeFactors, p :=
          Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
      _ ∣ n := Nat.prod_primeFactors_dvd n
  have hQ_ne : Q ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero)
  have hsub : Q.divisors ⊆ n.divisors := Nat.divisors_subset_of_dvd (by omega) hQ_dvd
  have hsum_eq : ∑ d ∈ n.divisors, betaS r s d = ∑ d ∈ Q.divisors, betaS r s d := by
    symm
    refine Finset.sum_subset hsub fun d hd hnot => ?_
    simp only [betaS, ArithmeticFunction.coe_mk]
    rw [if_neg]
    intro ⟨hd_ne, hd_sq, hd_gt⟩
    apply hnot
    rw [Nat.mem_divisors]
    refine ⟨?_, hQ_ne⟩
    rw [← Nat.prod_primeFactors_of_squarefree hd_sq]
    refine Finset.prod_dvd_prod_of_subset _ _ _ fun p hp => ?_
    rw [Finset.mem_filter]
    have hp_pr := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ n := dvd_trans (Nat.dvd_of_mem_primeFactors hp) (Nat.dvd_of_mem_divisors hd)
    exact ⟨Nat.mem_primeFactors.mpr ⟨hp_pr, hpd, by omega⟩, hd_gt p hp⟩
  rw [hsum_eq, sum_divisors_prod_primes_eq_prod_one_add
    (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
    (betaS r s) (betaS_isMultiplicative r s)]
  unfold psiR
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp_pr := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hgt : r < p := (Finset.mem_filter.mp hp).2
  rw [betaS_prime r s p hp_pr, if_pos hgt]
  ring

/- Residue class counting in `Ioc N (N + M)` -/

lemma card_Ioc_modEq_le (N M d r : ℕ) (hd : 1 ≤ d) :
    ((Ioc N (N + M)).filter (fun x => x % d = r)).card ≤ M / d + 1 := by
  by_cases hr : d ≤ r
  · have hempty : (Ioc N (N + M)).filter (fun x => x % d = r) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x _ hmod
      have := Nat.mod_lt x (show 0 < d by omega)
      omega
    simp [hempty]
  · have hr_lt : r < d := by omega
    have hshift : ((Ioc N (N + M)).filter (fun x => x % d = r)).card =
        ((Icc 1 M).filter (fun y => y % d = (r + d - N % d) % d)).card := by
      refine Finset.card_bij (fun x _ => x - N) ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hx ⊢
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        have h1 : (x - N + N) % d = r := by rw [Nat.sub_add_cancel (by omega)]; exact hx.2
        have h2 : (x - N) % d < d := Nat.mod_lt _ (by omega)
        have h3 : N % d < d := Nat.mod_lt _ (by omega)
        have h4 : ((x - N) % d + N % d) % d = r := by rwa [← Nat.add_mod]
        have h5 : ((x - N) % d + N % d) % d = (r + d - N % d + N % d) % d := by
          rw [h4, show r + d - N % d + N % d = r + d by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hr_lt]
        have h6 : (x - N) % d ≡ (r + d - N % d) % d [MOD d] := by
          have hadd : (x - N) % d + N % d ≡ (r + d - N % d) + N % d [MOD d] := h5
          have hadd2 : (x - N) % d + N % d ≡ (r + d - N % d) % d + N % d [MOD d] :=
            hadd.trans (Nat.ModEq.add_right (N % d) (Nat.mod_modEq (r + d - N % d) d).symm)
          exact Nat.ModEq.add_right_cancel' (N % d) hadd2
        rwa [Nat.ModEq, Nat.mod_eq_of_lt h2, Nat.mod_mod] at h6
      · intro a ha b hb heq
        simp only [Finset.mem_filter, Finset.mem_Ioc] at ha hb
        omega
      · intro y hy
        simp only [Finset.mem_filter, Finset.mem_Icc] at hy
        refine ⟨N + y, ?_, Nat.add_sub_cancel_left N y⟩
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        have h3 : N % d < d := Nat.mod_lt _ (by omega)
        rw [Nat.add_mod, hy.2, Nat.add_mod_mod, show N % d + (r + d - N % d) = r + d by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt hr_lt]
    rw [hshift]
    have hrem_lt : (r + d - N % d) % d < d := Nat.mod_lt _ (by omega)
    have hbound := card_Icc_modEq_sub_div_le M d ((r + d - N % d) % d) hd hrem_lt
    rw [abs_le] at hbound
    have hdiv : (M : ℝ) / d < ((M / d : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ (by exact_mod_cast (show 0 < d by omega))]
      have h1 : M < (M / d + 1) * d := by
        have := Nat.div_add_mod M d
        have := Nat.mod_lt M (show 0 < d by omega)
        nlinarith
      exact_mod_cast h1
    have hlt2 : (((Icc 1 M).filter (fun y => y % d = (r + d - N % d) % d)).card : ℝ) <
        ((M / d + 2 : ℕ) : ℝ) := by
      push_cast; linarith
    have hnat : ((Icc 1 M).filter (fun y => y % d = (r + d - N % d) % d)).card < M / d + 2 := by
      exact_mod_cast hlt2
    omega

/- Holder2 bound: moment of `psiR r m` over an interval `Ioc N (N + M)` -/

lemma sum_betaS_div_le (r s B : ℕ) (hs : 1 ≤ s) (hr : 2 * s ≤ r) :
    ∑ d ∈ Icc 1 B, betaS r s d / (d : ℝ) ≤ Real.exp 2 := by
  let P := ∏ p ∈ (B + 1).primesBelow, p
  let f : ArithmeticFunction ℝ :=
    { toFun := fun d => if d = 0 then 0 else betaS r s d / (d : ℝ)
      map_zero' := rfl }
  have hf_mult : f.IsMultiplicative := by
    constructor
    · simp [f, (betaS_isMultiplicative r s).1]
    · intro a b hcop
      by_cases ha : a = 0
      · simp [f, ha]
      by_cases hb : b = 0
      · simp [f, hb]
      have hab : a * b ≠ 0 := Nat.mul_ne_zero ha hb
      simp only [f, ArithmeticFunction.coe_mk, ha, hb, hab, ite_false,
        (betaS_isMultiplicative r s).2 hcop, Nat.cast_mul]
      ring
  have hle1 : ∑ d ∈ Icc 1 B, betaS r s d / (d : ℝ) ≤ ∑ d ∈ P.divisors, f d := by
    have hterm : ∀ d ∈ Icc 1 B, betaS r s d / (d : ℝ) = if d ∈ P.divisors then f d else 0 := by
      intro d hd
      rw [Finset.mem_Icc] at hd
      have hd_ne : d ≠ 0 := by omega
      by_cases hmem : d ∈ P.divisors
      · simp [hmem, f, hd_ne]
      · rw [if_neg hmem]
        simp only [betaS, ArithmeticFunction.coe_mk]
        split_ifs with hsq
        · exfalso
          apply hmem
          rw [Nat.mem_divisors]
          refine ⟨?_, Finset.prod_ne_zero_iff.mpr (fun p hp => (Nat.prime_of_mem_primesBelow hp).ne_zero)⟩
          rw [← Nat.prod_primeFactors_of_squarefree hsq.2.1]
          refine Finset.prod_dvd_prod_of_subset _ _ _ fun p hp => ?_
          rw [Nat.mem_primesBelow]
          have hp_pr := Nat.prime_of_mem_primeFactors hp
          exact ⟨Nat.lt_succ_of_le ((Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)).trans hd.2), hp_pr⟩
        · simp
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun d hd => (Finset.mem_filter.mp hd).2)
      (fun d _ _ => ?_)
    simp only [f, ArithmeticFunction.coe_mk]
    split_ifs
    · exact le_rfl
    · exact div_nonneg (betaS_nonneg r s d) (by positivity)
  rw [sum_divisors_prod_primes_eq_prod_one_add (fun p hp => Nat.prime_of_mem_primesBelow hp) f hf_mult] at hle1
  have hprod : ∏ p ∈ (B + 1).primesBelow, (1 + f p) ≤ Real.exp 2 := by
    calc ∏ p ∈ (B + 1).primesBelow, (1 + f p)
        ≤ Real.exp (∑ p ∈ (B + 1).primesBelow, f p) :=
          prod_one_add_le_exp_sum _ _ (fun p hp => by
            simp only [f, ArithmeticFunction.coe_mk, (Nat.prime_of_mem_primesBelow hp).ne_zero, ite_false]
            exact div_nonneg (betaS_nonneg r s p) (by positivity))
      _ ≤ Real.exp 2 := by
          apply Real.exp_le_exp.mpr
          have hterm : ∀ p ∈ (B + 1).primesBelow,
              f p ≤ if r < p then 4 * (s : ℝ) / (p : ℝ) ^ 2 else 0 := by
            intro p hp
            have hp_pr := Nat.prime_of_mem_primesBelow hp
            simp only [f, ArithmeticFunction.coe_mk, hp_pr.ne_zero, ite_false, betaS_prime r s p hp_pr]
            split_ifs with hgt
            · have hb := beta_prime_le hgt hr hs
              have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
              calc (((p : ℝ) / ((p : ℝ) - 1)) ^ s - 1) / (p : ℝ)
                  ≤ (4 * (s : ℝ) / (p : ℝ)) / (p : ℝ) := div_le_div_of_nonneg_right hb hp_pos.le
                _ = 4 * (s : ℝ) / (p : ℝ) ^ 2 := by ring
            · simp
          calc ∑ p ∈ (B + 1).primesBelow, f p
              ≤ ∑ p ∈ (B + 1).primesBelow, (if r < p then 4 * (s : ℝ) / (p : ℝ) ^ 2 else 0) :=
                Finset.sum_le_sum hterm
            _ = ∑ p ∈ (B + 1).primesBelow.filter (r < ·), 4 * (s : ℝ) / (p : ℝ) ^ 2 :=
                (Finset.sum_filter _ _).symm
            _ ≤ ∑ n ∈ Icc (r + 1) B, 4 * (s : ℝ) / (n : ℝ) ^ 2 := by
                refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
                intro p hp
                simp only [Finset.mem_filter, Nat.mem_primesBelow, Finset.mem_Icc] at hp ⊢
                exact ⟨hp.2, Nat.lt_succ_iff.mp hp.1.1⟩
            _ = 4 * (s : ℝ) * ∑ n ∈ Icc (r + 1) B, (1 / (n : ℝ) ^ 2) := by
                rw [Finset.mul_sum]; congr 1 with n; ring
            _ ≤ 4 * (s : ℝ) * (1 / (r : ℝ)) := by
                gcongr; exact sum_inv_sq_tail r B (by omega)
            _ ≤ 2 := by
                rw [mul_one_div, div_le_iff₀ (by exact_mod_cast (show 0 < r by omega))]
                have : (2 * s : ℝ) ≤ r := by exact_mod_cast hr
                linarith
  exact hle1.trans hprod

lemma holder2_bound (K r s N M : ℕ) (hs : 1 ≤ s) (hr : 2 * s ≤ r) (hM : 1 ≤ M)
    (hN : N ≤ 2 * (K + 1) * M) :
    ∑ m ∈ Ioc N (N + M), (psiR r m) ^ s ≤ (2 * (K + 1 : ℝ) + 1) * Real.exp 2 * (M : ℝ) := by
  have h1 : ∑ m ∈ Ioc N (N + M), (psiR r m) ^ s =
      ∑ m ∈ Ioc N (N + M), ∑ d ∈ Icc 1 (N + M), if d ∣ m then betaS r s d else 0 := by
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_Ioc] at hm
    rw [psiR_pow_eq_sum_betaS r s m (by omega), ← Finset.sum_filter]
    congr 1
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hd, hne⟩
      have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (ne_zero_of_dvd_ne_zero hne hd)
      exact ⟨⟨hd1, (Nat.le_of_dvd (by omega) hd).trans hm.2⟩, hd⟩
    · rintro ⟨_, hd⟩
      exact ⟨hd, by omega⟩
  rw [h1, Finset.sum_comm]
  have hcard : ∀ d ∈ Icc 1 (N + M),
      ∑ m ∈ Ioc N (N + M), (if d ∣ m then betaS r s d else 0) ≤
        betaS r s d * ((N + M : ℝ) / d) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (betaS_nonneg r s d)
    have hsub : (Ioc N (N + M)).filter (d ∣ ·) ⊆ (Icc 1 (N + M)).filter (d ∣ ·) :=
      Finset.filter_subset_filter _ (fun m hm => by
        rw [Finset.mem_Ioc] at hm; rw [Finset.mem_Icc]; omega)
    have hcard_dvd : ((Icc 1 (N + M)).filter (d ∣ ·)).card ≤ (N + M) / d := by
      have hbij : ((Icc 1 (N + M)).filter (d ∣ ·)).card = (Icc 1 ((N + M) / d)).card := by
        refine Finset.card_bij (fun m _ => m / d) ?_ ?_ ?_
        · intro m hm
          simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
          exact ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hm.2) (by omega), Nat.div_le_div_right hm.1.2⟩
        · intro a ha b hb heq
          simp only [Finset.mem_filter] at ha hb
          rw [← Nat.mul_div_cancel' ha.2, ← Nat.mul_div_cancel' hb.2, heq]
        · intro c hc
          rw [Finset.mem_Icc] at hc
          refine ⟨d * c, ?_, Nat.mul_div_cancel_left c (by omega)⟩
          simp only [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨Nat.mul_pos (by omega) (by omega),
            (Nat.mul_le_mul_left d hc.2).trans (Nat.mul_div_le (N + M) d)⟩, dvd_mul_right d c⟩
      rw [hbij]; simp
    have hle_nat : ((Ioc N (N + M)).filter (d ∣ ·)).card ≤ (N + M) / d :=
      (Finset.card_le_card hsub).trans hcard_dvd
    have hle_real : (((N + M) / d : ℕ) : ℝ) ≤ (N + M : ℝ) / d := by
      rw [le_div_iff₀ (by exact_mod_cast (show 0 < d by omega))]
      exact_mod_cast Nat.div_mul_le_self (N + M) d
    exact (Nat.cast_le.mpr hle_nat).trans hle_real
  calc ∑ d ∈ Icc 1 (N + M), ∑ m ∈ Ioc N (N + M), (if d ∣ m then betaS r s d else 0)
      ≤ ∑ d ∈ Icc 1 (N + M), betaS r s d * ((N + M : ℝ) / d) := Finset.sum_le_sum hcard
    _ = (N + M : ℝ) * ∑ d ∈ Icc 1 (N + M), betaS r s d / (d : ℝ) := by
        rw [Finset.mul_sum]; congr 1 with d; ring
    _ ≤ (N + M : ℝ) * Real.exp 2 := by
        gcongr; exact sum_betaS_div_le r s (N + M) hs hr
    _ ≤ ((2 * (K + 1 : ℝ) + 1) * (M : ℝ)) * Real.exp 2 := by
        gcongr
        have hNM : (N : ℝ) ≤ 2 * (K + 1 : ℝ) * (M : ℝ) := by exact_mod_cast hN
        linarith
    _ = (2 * (K + 1 : ℝ) + 1) * Real.exp 2 * (M : ℝ) := by ring

/- Holder3 bound: moment of `psiR r (Gprime ...)` -/

def Gprime (r K j h l : ℕ) (m : Fin K → ℕ) : ℕ :=
  ∏ p ∈ (gForm m j h).primeFactors.filter (fun p => r < p ∧ ¬ p ∣ (∏ i : Fin K, m i) * gForm m l h), p

lemma Gprime_pos (r K j h l : ℕ) (m : Fin K → ℕ) : 1 ≤ Gprime r K j h l m := by
  unfold Gprime
  exact Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun p hp =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero))

lemma Gprime_dvd_gForm (r K j h l : ℕ) (m : Fin K → ℕ) : Gprime r K j h l m ∣ gForm m j h := by
  unfold Gprime
  exact dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _))
    (Nat.prod_primeFactors_dvd _)

lemma sum_betaS_le (r s B : ℕ) (hs : 1 ≤ s) (hr : 2 * s ≤ r) (hB : 2 ≤ B) :
    ∑ d ∈ Icc 1 B, betaS r s d ≤
      Real.exp (4 * (s : ℝ) * (8 * Real.log (Real.log (B : ℝ) + 2) + 16)) := by
  let P := ∏ p ∈ (B + 1).primesBelow, p
  have hle1 : ∑ d ∈ Icc 1 B, betaS r s d ≤ ∑ d ∈ P.divisors, betaS r s d := by
    have hterm : ∀ d ∈ Icc 1 B, betaS r s d = if d ∈ P.divisors then betaS r s d else 0 := by
      intro d hd
      rw [Finset.mem_Icc] at hd
      by_cases hmem : d ∈ P.divisors
      · rw [if_pos hmem]
      · rw [if_neg hmem]
        simp only [betaS, ArithmeticFunction.coe_mk]
        rw [if_neg]
        intro ⟨_, hd_sq, _⟩
        apply hmem
        rw [Nat.mem_divisors]
        refine ⟨?_, Finset.prod_ne_zero_iff.mpr (fun p hp => (Nat.prime_of_mem_primesBelow hp).ne_zero)⟩
        rw [← Nat.prod_primeFactors_of_squarefree hd_sq]
        refine Finset.prod_dvd_prod_of_subset _ _ _ fun p hp => ?_
        rw [Nat.mem_primesBelow]
        have hp_pr := Nat.prime_of_mem_primeFactors hp
        exact ⟨Nat.lt_succ_of_le ((Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)).trans hd.2), hp_pr⟩
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
    exact Finset.sum_le_sum_of_subset_of_nonneg (fun d hd => (Finset.mem_filter.mp hd).2)
      (fun d _ _ => betaS_nonneg r s d)
  rw [sum_divisors_prod_primes_eq_prod_one_add (fun p hp => Nat.prime_of_mem_primesBelow hp)
    (betaS r s) (betaS_isMultiplicative r s)] at hle1
  have hprod : ∏ p ∈ (B + 1).primesBelow, (1 + betaS r s p) ≤
      Real.exp (4 * (s : ℝ) * (8 * Real.log (Real.log (B : ℝ) + 2) + 16)) := by
    calc ∏ p ∈ (B + 1).primesBelow, (1 + betaS r s p)
        ≤ Real.exp (∑ p ∈ (B + 1).primesBelow, betaS r s p) :=
          prod_one_add_le_exp_sum _ _ (fun p _ => betaS_nonneg r s p)
      _ ≤ Real.exp (4 * (s : ℝ) * (8 * Real.log (Real.log (B : ℝ) + 2) + 16)) := by
          apply Real.exp_le_exp.mpr
          have hterm : ∀ p ∈ (B + 1).primesBelow, betaS r s p ≤ 4 * (s : ℝ) * ((1 : ℝ) / (p : ℕ)) := by
            intro p hp
            have hp_pr := Nat.prime_of_mem_primesBelow hp
            rw [betaS_prime r s p hp_pr]
            split_ifs with hgt
            · have := beta_prime_le hgt hr hs; rw [mul_one_div]; exact this
            · positivity
          calc ∑ p ∈ (B + 1).primesBelow, betaS r s p
              ≤ ∑ p ∈ (B + 1).primesBelow, 4 * (s : ℝ) * ((1 : ℝ) / (p : ℕ)) := Finset.sum_le_sum hterm
            _ = 4 * (s : ℝ) * ∑ p ∈ (B + 1).primesBelow, ((1 : ℝ) / (p : ℕ)) := (Finset.mul_sum _ _ _).symm
            _ ≤ 4 * (s : ℝ) * (8 * Real.log (Real.log (B : ℝ) + 2) + 16) := by
                gcongr
                have h := sum_prime_inv_le (x := (B : ℝ)) (by exact_mod_cast hB)
                rwa [Nat.floor_natCast] at h
  exact hle1.trans hprod

lemma log_le_two_sqrt {u : ℝ} (hu : 0 < u) : Real.log u ≤ 2 * Real.sqrt u := by
  have hsq : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu.le
  have hpos : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have h1 : Real.log (Real.sqrt u) ≤ Real.sqrt u - 1 := Real.log_le_sub_one_of_pos hpos
  have h2 : Real.log u = 2 * Real.log (Real.sqrt u) := by
    conv_lhs => rw [← hsq, Real.log_pow]
    ring
  linarith

lemma gForm_congr_on_Ioo {K : ℕ} {m₁ m₂ : Fin K → ℕ} {j h : ℕ}
    (hagree : ∀ u (hu : u < K), j < u → u < h → m₁ ⟨u, hu⟩ = m₂ ⟨u, hu⟩) :
    gForm m₁ j h = gForm m₂ j h := by
  induction h with
  | zero => rfl
  | succ h ih =>
    by_cases hlt : h < j
    · simp [gForm, hlt]
    · by_cases heq : h = j
      · subst heq; rw [gForm_succ_self, gForm_succ_self]
      · have hgt : j < h := by omega
        rw [gForm_succ_eq m₁ hgt.le, gForm_succ_eq m₂ hgt.le,
          ih (fun u hu h1 h2 => hagree u hu h1 (by omega))]
        split_ifs with hK
        · rw [hagree h hK hgt (Nat.lt_succ_self h)]
        · rfl

lemma clog_two_le (n : ℕ) : Nat.clog 2 n ≤ n :=
  (Nat.clog_le_iff_le_pow (by norm_num)).mpr (Nat.lt_two_pow_self (n := n)).le

lemma holder3_one_var {K r s j h : ℕ} (hK : 3 ≤ K) (hjh : j + 2 ≤ h) (hhK : h ≤ K)
    (l : Fin K) (hl1 : j < (l : ℕ)) (hl2 : (l : ℕ) < h)
    (N M : Fin K → ℕ) (hN : ∀ i, N i ≤ 2 * (K + 1) * M i)
    (hM_max : ∀ u (hu : u < K), j < u → u < h → M ⟨u, hu⟩ ≤ M l)
    (hM_big : 2 ^ (10 ^ 6 * (K + 1) ^ 7) ≤ M l)
    (hs : 1 ≤ s) (hs_le : s ≤ (K + 1) ^ 2 * LParam K) (hr : 2 * s ≤ r)
    (m : Fin K → ℕ) (hm_box : ∀ i, i ≠ l → m i ∈ Ioc (N i) (N i + M i)) :
    ∑ x ∈ Ioc (N l) (N l + M l), (psiR r (Gprime r K j h l (Function.update m l x))) ^ s ≤
      (Real.exp 2 + 1) * (M l : ℝ) := by
  let B : ℕ := (4 * (K + 1) * M l) ^ (K + 1)
  have hMl_ge : 2 ^ (10 ^ 6 * (K + 1) ^ 7) ≤ M l := hM_big
  have hMl_pos : 2 ≤ M l := by
    have hexp1 : 1 ≤ 10 ^ 6 * (K + 1) ^ 7 :=
      Nat.mul_pos (by norm_num) (Nat.pow_pos (Nat.succ_pos K))
    have : 2 ^ 1 ≤ 2 ^ (10 ^ 6 * (K + 1) ^ 7) := Nat.pow_le_pow_right (by norm_num) hexp1
    omega
  have hB2 : 2 ≤ B := by
    have hbase : 2 ≤ 4 * (K + 1) * M l := by nlinarith only [hMl_pos]
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ (4 * (K + 1) * M l) ^ 1 := Nat.pow_le_pow_left hbase 1
      _ ≤ (4 * (K + 1) * M l) ^ (K + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hG_le_B : ∀ x ∈ Ioc (N l) (N l + M l),
      Gprime r K j h l (Function.update m l x) ≤ B := by
    intro x hx
    rw [Finset.mem_Ioc] at hx
    let m' := Function.update m l x
    let m'' := Function.update m' ⟨j, by omega⟩ 0
    have hcongr : gForm m' j h = gForm m'' j h :=
      gForm_congr_on_Ioo (fun u hu h1 _ => by
        have hne : (⟨u, hu⟩ : Fin K) ≠ ⟨j, by omega⟩ := fun heq => by
          have hv : u = j := congrArg Fin.val heq; omega
        simp only [m'', Function.update_of_ne hne])
    have hm''_le : ∀ u (hu : u < K), j ≤ u → u < h → m'' ⟨u, hu⟩ ≤ 3 * (K + 1) * M l := by
      intro u hu hju huh
      by_cases huj : u = j
      · have : (⟨u, hu⟩ : Fin K) = ⟨j, by omega⟩ := Fin.ext huj
        simp [m'', this]
      · have hgt : j < u := by omega
        have hne_j : (⟨u, hu⟩ : Fin K) ≠ ⟨j, by omega⟩ := fun heq => huj (congrArg Fin.val heq)
        simp only [m'', Function.update_of_ne hne_j]
        by_cases hul : (⟨u, hu⟩ : Fin K) = l
        · simp only [m', hul, Function.update_self]
          have := hN l; nlinarith only [hx.2, this]
        · simp only [m', Function.update_of_ne hul]
          have hm_in := Finset.mem_Ioc.mp (hm_box ⟨u, hu⟩ hul)
          have hNu := hN ⟨u, hu⟩
          have hMu := hM_max u hu hgt huh
          nlinarith only [hm_in.2, hNu, hMu]
    have hg_le : gForm m' j h ≤ (3 * (K + 1) * M l + 1) ^ (h - j - 1) := by
      rw [hcongr]
      exact gForm_le_pow m'' (by omega) hhK hm''_le
    calc Gprime r K j h l m'
        ≤ gForm m' j h := Nat.le_of_dvd (gForm_pos m' (by omega)) (Gprime_dvd_gForm r K j h l m')
      _ ≤ (3 * (K + 1) * M l + 1) ^ (h - j - 1) := hg_le
      _ ≤ (4 * (K + 1) * M l) ^ (h - j - 1) :=
          Nat.pow_le_pow_left (by nlinarith only [hMl_pos]) _
      _ ≤ (4 * (K + 1) * M l) ^ (K + 1) :=
          Nat.pow_le_pow_right (by nlinarith only [hMl_pos]) (by omega)
  -- Linear form in `x`: `gForm (update m l x) j h = x * C₁ + C₂`
  let C₁ : ℕ := (∏ u ∈ Ico ((l : ℕ) + 1) h, (if hlt : u < K then m ⟨u, hlt⟩ else 1)) * gForm m j l
  let C₂ : ℕ := gForm m l h
  have hlin : ∀ x : ℕ, gForm (Function.update m l x) j h = x * C₁ + C₂ := by
    intro x
    let m' := Function.update m l x
    have hsplit := gForm_eq_mul_add_gForm m' hl1.le hl2.le
    have hprod_split : ∏ u ∈ Ico (l : ℕ) h, (if hlt : u < K then m' ⟨u, hlt⟩ else 1) =
        x * ∏ u ∈ Ico ((l : ℕ) + 1) h, (if hlt : u < K then m ⟨u, hlt⟩ else 1) := by
      rw [← Finset.mul_prod_erase (Ico (l : ℕ) h) _ (Finset.mem_Ico.mpr ⟨le_rfl, hl2⟩)]
      have hdiff : (Ico (l : ℕ) h).erase (l : ℕ) = Ico ((l : ℕ) + 1) h := by
        ext u; simp only [Finset.mem_erase, Finset.mem_Ico]; omega
      rw [hdiff, dif_pos l.2]
      have hself : m' ⟨(l : ℕ), l.2⟩ = x := by simp [m']
      rw [hself]
      congr 1
      refine Finset.prod_congr rfl fun u hu => ?_
      rw [Finset.mem_Ico] at hu
      split_ifs with hlt
      · exact Function.update_of_ne (fun heq => by have hv : u = (l : ℕ) := congrArg Fin.val heq; omega) _ _
      · rfl
    have hg1 : gForm m' j l = gForm m j l :=
      gForm_congr_on_Ioo (fun u hu _ h2 =>
        Function.update_of_ne (fun heq => by have hv : u = (l : ℕ) := congrArg Fin.val heq; omega) _ _)
    have hg2 : gForm m' l h = gForm m l h :=
      gForm_congr_on_Ioo (fun u hu h1 _ =>
        Function.update_of_ne (fun heq => by have hv : u = (l : ℕ) := congrArg Fin.val heq; omega) _ _)
    rw [hsplit, hprod_split, hg1, hg2]
    simp only [C₁, C₂]; ring
  -- Any `d` dividing `Gprime` for some `x` is coprime to `C₁`, so at most `M l / d + 1` solutions
  have hcard_d : ∀ d ∈ Icc 1 B,
      ((Ioc (N l) (N l + M l)).filter (fun x => d ∣ Gprime r K j h l (Function.update m l x))).card ≤
        M l / d + 1 := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    let S := (Ioc (N l) (N l + M l)).filter (fun x => d ∣ Gprime r K j h l (Function.update m l x))
    by_cases hS : S.Nonempty
    · obtain ⟨x₀, hx₀⟩ := hS
      have hx₀_dvd : d ∣ Gprime r K j h l (Function.update m l x₀) := (Finset.mem_filter.mp hx₀).2
      have hcop : d.Coprime C₁ := by
        rw [Nat.coprime_iff_gcd_eq_one]
        by_contra hne
        obtain ⟨p, hp_pr, hpd⟩ := Nat.exists_prime_and_dvd hne
        have hpd_d : p ∣ d := dvd_trans hpd (Nat.gcd_dvd_left d C₁)
        have hpd_C1 : p ∣ C₁ := dvd_trans hpd (Nat.gcd_dvd_right d C₁)
        have hpd_G : p ∣ Gprime r K j h l (Function.update m l x₀) := dvd_trans hpd_d hx₀_dvd
        obtain ⟨q, hq, hpq⟩ := (hp_pr.prime.dvd_finsetProd_iff _).mp hpd_G
        rw [Finset.mem_filter] at hq
        have hq_pr := Nat.prime_of_mem_primeFactors hq.1
        have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp_pr hq_pr).mp hpq
        subst heq
        have hnd_prod : ¬ p ∣ ∏ i : Fin K, Function.update m l x₀ i :=
          fun hd1 => hq.2.2 (dvd_mul_of_dvd_left hd1 _)
        have hnd_glh : ¬ p ∣ gForm (Function.update m l x₀) l h :=
          fun hd1 => hq.2.2 (dvd_mul_of_dvd_right hd1 _)
        have hglh_eq : gForm (Function.update m l x₀) l h = C₂ :=
          gForm_congr_on_Ioo (fun u hu h1 _ =>
            Function.update_of_ne (fun heq => by have hv : u = (l : ℕ) := congrArg Fin.val heq; omega) _ _)
        rw [hglh_eq] at hnd_glh
        rcases hp_pr.dvd_mul.mp hpd_C1 with h1 | h2
        · obtain ⟨u, hu, hpu⟩ := (hp_pr.prime.dvd_finsetProd_iff _).mp h1
          rw [Finset.mem_Ico] at hu
          have huK : u < K := by omega
          simp only [huK, dite_true] at hpu
          have hne_l : (⟨u, huK⟩ : Fin K) ≠ l := fun heq => by
            have hv : u = (l : ℕ) := congrArg Fin.val heq; omega
          have hupd : Function.update m l x₀ ⟨u, huK⟩ = m ⟨u, huK⟩ :=
            Function.update_of_ne hne_l _ _
          exact hnd_prod (dvd_trans (hupd.symm ▸ hpu) (Finset.dvd_prod_of_mem _ (Finset.mem_univ _)))
        · have hpd_gjh : p ∣ gForm (Function.update m l x₀) j h :=
            Nat.dvd_of_mem_primeFactors hq.1
          rw [hlin x₀] at hpd_gjh
          have hpd_mul : p ∣ x₀ * C₁ := dvd_mul_of_dvd_right (dvd_mul_of_dvd_right h2 _) x₀
          exact hnd_glh ((Nat.dvd_add_right hpd_mul).mp hpd_gjh)
      have hsub : S ⊆ (Ioc (N l) (N l + M l)).filter (fun x => x % d = x₀ % d) := by
        intro x hx
        simp only [S, Finset.mem_filter] at hx ⊢
        refine ⟨hx.1, ?_⟩
        have hd1 : d ∣ x * C₁ + C₂ := by
          rw [← hlin x]; exact dvd_trans hx.2 (Gprime_dvd_gForm r K j h l _)
        have hd0 : d ∣ x₀ * C₁ + C₂ := by
          rw [← hlin x₀]; exact dvd_trans hx₀_dvd (Gprime_dvd_gForm r K j h l _)
        have hmod : x * C₁ ≡ x₀ * C₁ [MOD d] := by
          have h1 : x * C₁ + C₂ ≡ x₀ * C₁ + C₂ [MOD d] :=
            (Nat.modEq_zero_iff_dvd.mpr hd1).trans (Nat.modEq_zero_iff_dvd.mpr hd0).symm
          exact Nat.ModEq.add_right_cancel' C₂ h1
        exact Nat.ModEq.cancel_right_of_coprime hcop hmod
      exact (Finset.card_le_card hsub).trans (card_Ioc_modEq_le (N l) (M l) d (x₀ % d) hd.1)
    · rw [Finset.not_nonempty_iff_eq_empty] at hS
      simp [S, hS]
  -- Swap sums over `x` and `d`
  have hswap : ∑ x ∈ Ioc (N l) (N l + M l), (psiR r (Gprime r K j h l (Function.update m l x))) ^ s =
      ∑ d ∈ Icc 1 B, betaS r s d *
        (((Ioc (N l) (N l + M l)).filter (fun x => d ∣ Gprime r K j h l (Function.update m l x))).card : ℝ) := by
    have h1 : ∑ x ∈ Ioc (N l) (N l + M l), (psiR r (Gprime r K j h l (Function.update m l x))) ^ s =
        ∑ x ∈ Ioc (N l) (N l + M l), ∑ d ∈ Icc 1 B,
          if d ∣ Gprime r K j h l (Function.update m l x) then betaS r s d else 0 := by
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [psiR_pow_eq_sum_betaS r s _ (Gprime_pos r K j h l _), ← Finset.sum_filter]
      congr 1
      ext d
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      have hGp := Gprime_pos r K j h l (Function.update m l x)
      have hGB := hG_le_B x hx
      constructor
      · rintro ⟨hdvd, hne⟩
        have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (ne_zero_of_dvd_ne_zero hne hdvd)
        exact ⟨⟨hd1, (Nat.le_of_dvd (by omega) hdvd).trans hGB⟩, hdvd⟩
      · rintro ⟨_, hdvd⟩
        exact ⟨hdvd, by omega⟩
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- Bound the second term `∑_{d ≤ B} betaS r s d ≤ M l`
  have hsecond_le : ∑ d ∈ Icc 1 B, betaS r s d ≤ (M l : ℝ) := by
    refine (sum_betaS_le r s B hs hr hB2).trans ?_
    have hMl_r : (2 : ℝ) ^ (10 ^ 6 * (K + 1) ^ 7) ≤ (M l : ℝ) := by exact_mod_cast hMl_ge
    have hlogM_ge : (500000 : ℝ) * ((K + 1 : ℕ) : ℝ) ^ 7 ≤ Real.log (M l : ℝ) := by
      have h1 := Real.log_le_log (by positivity) hMl_r
      rw [Real.log_pow] at h1
      have hl2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
      have hk7_nn : (0 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) ^ 7 := by positivity
      have hcast : ((10 ^ 6 * (K + 1) ^ 7 : ℕ) : ℝ) = 1000000 * ((K + 1 : ℕ) : ℝ) ^ 7 := by
        push_cast; ring
      rw [hcast] at h1
      nlinarith only [h1, hl2, hk7_nn]
    have hk_ge4 : (4 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by exact_mod_cast (show 4 ≤ K + 1 by omega)
    have hlogM_pos : 0 < Real.log (M l : ℝ) := by
      have : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) ^ 7 := by positivity
      nlinarith only [hlogM_ge, this]
    have hlogB : Real.log (B : ℝ) + 2 ≤ 3 * ((K + 1 : ℕ) : ℝ) * Real.log (M l : ℝ) := by
      have h4k_le : 4 * ((K + 1 : ℕ) : ℝ) ≤ (M l : ℝ) := by
        have h1 : 4 * ((K + 1 : ℕ) : ℝ) ≤ Real.log (M l : ℝ) := by
          have hk7 : ((K + 1 : ℕ) : ℝ) ≤ ((K + 1 : ℕ) : ℝ) ^ 7 :=
            le_self_pow₀ (by linarith only [hk_ge4]) (by norm_num)
          nlinarith only [hlogM_ge, hk7, hk_ge4]
        linarith only [h1, Real.log_le_sub_one_of_pos (show (0 : ℝ) < M l by exact_mod_cast (show 0 < M l by omega))]
      have hB_eq : Real.log (B : ℝ) = ((K + 1 : ℕ) : ℝ) * Real.log (4 * ((K + 1 : ℕ) : ℝ) * (M l : ℝ)) := by
        simp only [B, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
        rw [Real.log_pow]
      have hlog4kM : Real.log (4 * ((K + 1 : ℕ) : ℝ) * (M l : ℝ)) ≤ 2 * Real.log (M l : ℝ) := by
        rw [Real.log_mul (by positivity) (by exact_mod_cast (show M l ≠ 0 by omega))]
        have := Real.log_le_log (by positivity) h4k_le
        linarith only [this]
      have h2_le : (2 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) * Real.log (M l : ℝ) := by
        have : (1 : ℝ) ≤ Real.log (M l : ℝ) := by
          have : (1 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) ^ 7 := one_le_pow₀ (by linarith only [hk_ge4])
          nlinarith only [hlogM_ge, this]
        nlinarith only [hk_ge4, this]
      rw [hB_eq]
      nlinarith only [hlog4kM, h2_le, hk_ge4]
    have hL_le : (LParam K : ℝ) ≤ 2 * ((K + 1 : ℕ) : ℝ) := by
      have hclog : Nat.clog 2 (K + 1) ≤ K + 1 := clog_two_le (K + 1)
      have : LParam K ≤ 2 * (K + 1) := by unfold LParam; omega
      exact_mod_cast this
    have h4s_le : 4 * (s : ℝ) ≤ 8 * ((K + 1 : ℕ) : ℝ) ^ 3 := by
      have hs_r : (s : ℝ) ≤ ((K + 1 : ℕ) : ℝ) ^ 2 * (LParam K : ℝ) := by exact_mod_cast hs_le
      nlinarith only [hs_r, hL_le, show (0 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) ^ 2 by positivity]
    have hloglog : Real.log (Real.log (B : ℝ) + 2) ≤
        2 * Real.sqrt (3 * ((K + 1 : ℕ) : ℝ) * Real.log (M l : ℝ)) := by
      have h1 : Real.log (Real.log (B : ℝ) + 2) ≤
          Real.log (3 * ((K + 1 : ℕ) : ℝ) * Real.log (M l : ℝ)) :=
        Real.log_le_log (by linarith only [Real.log_nonneg (show (1 : ℝ) ≤ B by exact_mod_cast (show 1 ≤ B by omega))]) hlogB
      exact h1.trans (log_le_two_sqrt (by positivity))
    have hexp_le : 4 * (s : ℝ) * (8 * Real.log (Real.log (B : ℝ) + 2) + 16) ≤ Real.log (M l : ℝ) := by
      have hterm1 : 8 * ((K + 1 : ℕ) : ℝ) ^ 3 * 16 ≤ (1 / 2) * Real.log (M l : ℝ) := by
        have hk37 : ((K + 1 : ℕ) : ℝ) ^ 3 ≤ ((K + 1 : ℕ) : ℝ) ^ 7 :=
          pow_le_pow_right₀ (by linarith only [hk_ge4]) (by norm_num)
        have hk3_nn : (0 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) ^ 3 := by positivity
        nlinarith only [hlogM_ge, hk37, hk3_nn]
      have hterm2 : 8 * ((K + 1 : ℕ) : ℝ) ^ 3 *
          (16 * Real.sqrt (3 * ((K + 1 : ℕ) : ℝ) * Real.log (M l : ℝ))) ≤ (1 / 2) * Real.log (M l : ℝ) := by
        have hsq : (128 * ((K + 1 : ℕ) : ℝ) ^ 3 * Real.sqrt (3 * ((K + 1 : ℕ) : ℝ) * Real.log (M l : ℝ))) ^ 2 ≤
            ((1 / 2) * Real.log (M l : ℝ)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by positivity)]
          have hlhs : (128 * ((K + 1 : ℕ) : ℝ) ^ 3) ^ 2 * (3 * ((K + 1 : ℕ) : ℝ) * Real.log (M l : ℝ)) =
              49152 * ((K + 1 : ℕ) : ℝ) ^ 7 * Real.log (M l : ℝ) := by ring
          rw [hlhs]
          have hrhs : ((1 / 2) * Real.log (M l : ℝ)) ^ 2 = (1 / 4) * Real.log (M l : ℝ) * Real.log (M l : ℝ) := by ring
          rw [hrhs]
          have hcoef : 49152 * ((K + 1 : ℕ) : ℝ) ^ 7 ≤ (1 / 4) * Real.log (M l : ℝ) := by
            have hk7_nn : (0 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) ^ 7 := by positivity
            nlinarith only [hlogM_ge, hk7_nn]
          exact mul_le_mul_of_nonneg_right hcoef hlogM_pos.le
        have h1 := Real.sqrt_le_sqrt hsq
        rw [Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)] at h1
        linarith only [h1]
      have hfactor_nn : 0 ≤ 8 * Real.log (Real.log (B : ℝ) + 2) + 16 := by
        have h2 : (1 : ℝ) ≤ Real.log (B : ℝ) + 2 := by
          linarith only [Real.log_nonneg (show (1 : ℝ) ≤ B by exact_mod_cast (show 1 ≤ B by omega))]
        linarith only [Real.log_nonneg h2]
      calc 4 * (s : ℝ) * (8 * Real.log (Real.log (B : ℝ) + 2) + 16)
          ≤ 8 * ((K + 1 : ℕ) : ℝ) ^ 3 * (8 * Real.log (Real.log (B : ℝ) + 2) + 16) :=
            mul_le_mul_of_nonneg_right h4s_le hfactor_nn
        _ ≤ 8 * ((K + 1 : ℕ) : ℝ) ^ 3 *
              (16 * Real.sqrt (3 * ((K + 1 : ℕ) : ℝ) * Real.log (M l : ℝ)) + 16) := by
            exact mul_le_mul_of_nonneg_left (by linarith only [hloglog]) (by positivity)
        _ = 8 * ((K + 1 : ℕ) : ℝ) ^ 3 *
              (16 * Real.sqrt (3 * ((K + 1 : ℕ) : ℝ) * Real.log (M l : ℝ))) +
            8 * ((K + 1 : ℕ) : ℝ) ^ 3 * 16 := by ring
        _ ≤ Real.log (M l : ℝ) := by linarith only [hterm1, hterm2]
    calc Real.exp (4 * (s : ℝ) * (8 * Real.log (Real.log (B : ℝ) + 2) + 16))
        ≤ Real.exp (Real.log (M l : ℝ)) := Real.exp_le_exp.mpr hexp_le
      _ = (M l : ℝ) := Real.exp_log (by exact_mod_cast (show 0 < M l by omega))
  rw [hswap]
  calc ∑ d ∈ Icc 1 B, betaS r s d *
        (((Ioc (N l) (N l + M l)).filter (fun x => d ∣ Gprime r K j h l (Function.update m l x))).card : ℝ)
      ≤ ∑ d ∈ Icc 1 B, betaS r s d * ((M l : ℝ) / d + 1) := by
        refine Finset.sum_le_sum fun d hd => ?_
        refine mul_le_mul_of_nonneg_left ?_ (betaS_nonneg r s d)
        have hc := hcard_d d hd
        have hd_pos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by rw [Finset.mem_Icc] at hd; omega)
        have hdiv : ((M l / d : ℕ) : ℝ) ≤ (M l : ℝ) / d := by
          rw [le_div_iff₀ hd_pos]; exact_mod_cast Nat.div_mul_le_self (M l) d
        have hcR : (((Ioc (N l) (N l + M l)).filter
            (fun x => d ∣ Gprime r K j h l (Function.update m l x))).card : ℝ) ≤
            ((M l / d : ℕ) : ℝ) + 1 := by exact_mod_cast hc
        linarith only [hcR, hdiv]
    _ = (M l : ℝ) * (∑ d ∈ Icc 1 B, betaS r s d / (d : ℝ)) + ∑ d ∈ Icc 1 B, betaS r s d := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun d _ => by ring
    _ ≤ (M l : ℝ) * Real.exp 2 + (M l : ℝ) := by
        gcongr
        exact sum_betaS_div_le r s B hs hr
    _ = (Real.exp 2 + 1) * (M l : ℝ) := by ring

/- Pointwise upper bound on `singSeries` for `K ≥ 3` -/

def pairsK (K : ℕ) : Finset (ℕ × ℕ) :=
  (range (K + 1) ×ˢ range (K + 1)).filter (fun q => q.1 + 2 ≤ q.2)

lemma pairsK_card (K : ℕ) : (pairsK K).card = K * (K - 1) / 2 := by
  have hsum : (pairsK K).card = ∑ h ∈ range (K + 1), (if 2 ≤ h then h - 1 else 0) := by
    unfold pairsK
    rw [Finset.card_filter, Finset.sum_product_right]
    refine Finset.sum_congr rfl fun h hh => ?_
    rw [Finset.mem_range] at hh
    rw [← Finset.card_filter]
    by_cases h2 : 2 ≤ h
    · rw [if_pos h2]
      have heq : (range (K + 1)).filter (fun j => j + 2 ≤ h) = range (h - 1) := by
        ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
      rw [heq, Finset.card_range]
    · rw [if_neg h2]
      have heq : (range (K + 1)).filter (fun j => j + 2 ≤ h) = ∅ := by
        ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false, not_and]; omega
      rw [heq, Finset.card_empty]
  rw [hsum]
  clear hsum
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    cases K with
    | zero => simp
    | succ K =>
      simp only [Nat.add_sub_cancel]
      have h1 : (K + 1) * K / 2 + (K + 1) = (K + 2) * (K + 1) / 2 := by
        have hmul : (K + 2) * (K + 1) = (K + 1) * K + 2 * (K + 1) := by ring
        rw [hmul, Nat.add_mul_div_left _ _ (by norm_num)]
      simpa using h1

lemma pairsK_card_pos {K : ℕ} (hK : 3 ≤ K) : 1 ≤ (pairsK K).card := by
  rw [pairsK_card]
  have : 2 ≤ K * (K - 1) := by
    have : 2 ≤ K - 1 := by omega
    nlinarith only [hK, this]
  omega

lemma pairsK_card_le {K : ℕ} : 2 * (pairsK K).card ≤ (K + 1) ^ 2 := by
  rw [pairsK_card]
  have h1 : 2 * (K * (K - 1) / 2) ≤ K * (K - 1) := Nat.mul_div_le _ 2
  have h2 : K * (K - 1) ≤ (K + 1) ^ 2 := by
    have : K - 1 ≤ K + 1 := by omega
    nlinarith only [this]
  omega

noncomputable def ef (K : ℕ) (m : Fin K → ℕ) (p : ℕ) : ℝ :=
  (1 - (xi m p : ℝ) / p) * (1 - 1 / (p : ℝ))⁻¹ ^ (K + 1)

lemma ef_nonneg {K : ℕ} (m : Fin K → ℕ) {p : ℕ} (hp : p.Prime) : 0 ≤ ef K m p := by
  unfold ef
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have h1 : 0 ≤ 1 - (xi m p : ℝ) / p := by
    rw [sub_nonneg, div_le_one hp_pos]; exact_mod_cast xi_le_p m p
  have h2 : 0 < 1 - 1 / (p : ℝ) := by
    rw [sub_pos, div_lt_one hp_pos]; exact_mod_cast hp.one_lt
  positivity

lemma singSeries_pointwise_le {K : ℕ} (_hK : 3 ≤ K) (m : Fin K → ℕ) (hm : ∀ i, 1 ≤ m i)
    (argMax : ℕ × ℕ → Fin K)
    (harg : ∀ q ∈ pairsK K, q.1 < (argMax q : ℕ) ∧ (argMax q : ℕ) < q.2) :
    singSeries m ≤
      (∏ p ∈ (rParam K + 1).primesBelow, ef K m p) *
      (∏ i : Fin K, psiR (rParam K) (m i) ^ K) *
      (∏ q ∈ pairsK K, psiR (rParam K) (Gprime (rParam K) K q.1 q.2 (argMax q) m)) := by
  classical
  let r := rParam K
  unfold singSeries
  split_ifs with hb
  · refine mul_nonneg (mul_nonneg ?_ ?_) ?_
    · exact Finset.prod_nonneg (fun p hp => ef_nonneg m (Nat.prime_of_mem_primesBelow hp))
    · exact Finset.prod_nonneg (fun i _ => pow_nonneg (psiR_pos r (m i)).le K)
    · exact Finset.prod_nonneg (fun q _ => (psiR_pos r _).le)
  · have hunion : (Nm m).primeFactors ∪ (r + 1).primesBelow =
        (r + 1).primesBelow ∪ ((Nm m).primeFactors.filter (r < ·)) := by
      ext p
      simp only [Finset.mem_union, Finset.mem_filter, Nat.mem_primesBelow, Nat.mem_primeFactors]
      constructor
      · rintro (⟨hp, h1, h2⟩ | ⟨hlt, hp⟩)
        · by_cases hle : p ≤ r
          · exact Or.inl ⟨Nat.lt_succ_of_le hle, hp⟩
          · exact Or.inr ⟨⟨hp, h1, h2⟩, by omega⟩
        · exact Or.inl ⟨hlt, hp⟩
      · rintro (⟨hlt, hp⟩ | ⟨⟨hp, h1, h2⟩, _⟩)
        · exact Or.inr ⟨hlt, hp⟩
        · exact Or.inl ⟨hp, h1, h2⟩
    have hdisj : Disjoint (r + 1).primesBelow ((Nm m).primeFactors.filter (r < ·)) := by
      rw [Finset.disjoint_left]; intro p h1 h2
      rw [Nat.mem_primesBelow] at h1; rw [Finset.mem_filter] at h2; omega
    rw [show (Nm m).primeFactors ∪ (rParam K + 1).primesBelow =
        (r + 1).primesBelow ∪ ((Nm m).primeFactors.filter (r < ·)) from hunion,
      Finset.prod_union hdisj]
    have hsmall_nn : 0 ≤ ∏ p ∈ (r + 1).primesBelow, ef K m p :=
      Finset.prod_nonneg (fun p hp => ef_nonneg m (Nat.prime_of_mem_primesBelow hp))
    change (∏ p ∈ (r + 1).primesBelow, ef K m p) *
        (∏ p ∈ (Nm m).primeFactors.filter (r < ·), ef K m p) ≤ _
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hsmall_nn
    -- Split `P_big := (Nm m).primeFactors.filter (r < ·)` into `p ∣ ∏ m_i` and `p ∤ ∏ m_i`
    let Pbig := (Nm m).primeFactors.filter (r < ·)
    let P1 := Pbig.filter (fun p => p ∣ ∏ i : Fin K, m i)
    let P2 := Pbig.filter (fun p => ¬ p ∣ ∏ i : Fin K, m i)
    have hPsplit : Pbig = P1 ∪ P2 := by
      ext p; simp only [P1, P2, Finset.mem_union, Finset.mem_filter]; tauto
    have hPdisj : Disjoint P1 P2 := by
      rw [Finset.disjoint_left]; intro p h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    change ∏ p ∈ Pbig, ef K m p ≤ _
    rw [hPsplit, Finset.prod_union hPdisj]
    have hP1 : ∏ p ∈ P1, ef K m p ≤ ∏ i : Fin K, psiR r (m i) ^ K := by
      have hterm : ∀ p ∈ P1, ef K m p ≤ ∏ i : Fin K, (if p ∣ m i then ((p : ℝ) / ((p : ℝ) - 1)) ^ K else 1) := by
        intro p hp
        have hp_big := (Finset.mem_filter.mp hp).1
        have hp_dvd := (Finset.mem_filter.mp hp).2
        have hp_pr := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp_big).1
        have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
        have h1p : 0 < 1 - 1 / (p : ℝ) := by
          rw [sub_pos, div_lt_one hp_pos]; exact_mod_cast hp_pr.one_lt
        have hef_le : ef K m p ≤ ((p : ℝ) / ((p : ℝ) - 1)) ^ K := by
          unfold ef
          have hxi1 : 1 ≤ xi m p := xi_ge_one m hp_pr.one_le
          have hinv : (1 - 1 / (p : ℝ))⁻¹ = (p : ℝ) / ((p : ℝ) - 1) := by
            have : (p : ℝ) - 1 ≠ 0 := by
              have : (2 : ℝ) ≤ p := by exact_mod_cast hp_pr.two_le
              linarith
            field_simp [hp_pos.ne', this]
          calc (1 - (xi m p : ℝ) / p) * (1 - 1 / (p : ℝ))⁻¹ ^ (K + 1)
              ≤ (1 - 1 / (p : ℝ)) * (1 - 1 / (p : ℝ))⁻¹ ^ (K + 1) := by
                gcongr; exact_mod_cast hxi1
            _ = (1 - 1 / (p : ℝ))⁻¹ ^ K := by
                rw [_root_.pow_succ', ← mul_assoc, mul_inv_cancel₀ h1p.ne', one_mul]
            _ = ((p : ℝ) / ((p : ℝ) - 1)) ^ K := by rw [hinv]
        obtain ⟨i₀, _, hi₀⟩ := (hp_pr.prime.dvd_finsetProd_iff _).mp hp_dvd
        have hge1 : ∀ i : Fin K, 1 ≤ (if p ∣ m i then ((p : ℝ) / ((p : ℝ) - 1)) ^ K else 1) := by
          intro i; split_ifs
          · refine one_le_pow₀ ?_
            have : (2 : ℝ) ≤ p := by exact_mod_cast hp_pr.two_le
            rw [one_le_div (by linarith)]; linarith
          · exact le_rfl
        have hsingle : ((p : ℝ) / ((p : ℝ) - 1)) ^ K =
            ∏ i ∈ ({i₀} : Finset (Fin K)), (if p ∣ m i then ((p : ℝ) / ((p : ℝ) - 1)) ^ K else 1) := by
          simp [hi₀]
        calc ef K m p ≤ ((p : ℝ) / ((p : ℝ) - 1)) ^ K := hef_le
          _ = ∏ i ∈ ({i₀} : Finset (Fin K)), (if p ∣ m i then ((p : ℝ) / ((p : ℝ) - 1)) ^ K else 1) := hsingle
          _ ≤ ∏ i : Fin K, (if p ∣ m i then ((p : ℝ) / ((p : ℝ) - 1)) ^ K else 1) :=
              prod_le_prod_of_subset_ge_one (Finset.singleton_subset_iff.mpr (Finset.mem_univ i₀)) _
                (fun i _ => by linarith only [hge1 i]) (fun i _ => hge1 i)
      calc ∏ p ∈ P1, ef K m p
          ≤ ∏ p ∈ P1, ∏ i : Fin K, (if p ∣ m i then ((p : ℝ) / ((p : ℝ) - 1)) ^ K else 1) :=
            Finset.prod_le_prod (fun p hp => ef_nonneg m (Nat.prime_of_mem_primeFactors
              (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1)) hterm
        _ = ∏ i : Fin K, ∏ p ∈ P1, (if p ∣ m i then ((p : ℝ) / ((p : ℝ) - 1)) ^ K else 1) :=
            Finset.prod_comm
        _ ≤ ∏ i : Fin K, psiR r (m i) ^ K := by
            refine Finset.prod_le_prod (fun i _ => Finset.prod_nonneg (fun p hp => by
              split_ifs
              · have hp_pr := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
                have : (2 : ℝ) ≤ p := by exact_mod_cast hp_pr.two_le
                have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
                positivity
              · norm_num)) (fun i _ => ?_)
            rw [← Finset.prod_filter]
            unfold psiR
            rw [← Finset.prod_pow]
            have hsub : P1.filter (fun p => p ∣ m i) ⊆ (m i).primeFactors.filter (r < ·) := by
              intro p hp
              simp only [P1, Pbig, Finset.mem_filter, Nat.mem_primeFactors] at hp ⊢
              exact ⟨⟨hp.1.1.1.1, hp.2, by have := hm i; omega⟩, hp.1.1.2⟩
            exact prod_le_prod_of_subset_ge_one hsub _ (fun p hp => by
              have hp_pr := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
              have : (2 : ℝ) ≤ p := by exact_mod_cast hp_pr.two_le
              have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
              positivity) (fun p hp => by
              have hp_pr := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).1
              have : (2 : ℝ) ≤ p := by exact_mod_cast hp_pr.two_le
              refine one_le_pow₀ ?_
              rw [one_le_div (by linarith)]; linarith)
    have hP2 : ∏ p ∈ P2, ef K m p ≤
        ∏ q ∈ pairsK K, psiR r (Gprime r K q.1 q.2 (argMax q) m) := by
      have hterm : ∀ p ∈ P2, ef K m p ≤
          ∏ q ∈ pairsK K, (if p ∣ Gprime r K q.1 q.2 (argMax q) m then (p : ℝ) / ((p : ℝ) - 1) else 1) := by
        intro p hp
        have hp_big := (Finset.mem_filter.mp hp).1
        have hnd_m : ¬ p ∣ ∏ i : Fin K, m i := (Finset.mem_filter.mp hp).2
        have hp_pr := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp_big).1
        have hp_gtr : r < p := (Finset.mem_filter.mp hp_big).2
        have hxi_le : xi m p ≤ K + 1 := xi_le_K_add_one_of_not_badVec hb hp_pr
        have hK_lt_p : K + 1 < p := by
          have : 1 ≤ LParam K := by unfold LParam; omega
          have : K + 1 ≤ r := by
            change K + 1 ≤ 4 * (K + 1) ^ 2 * LParam K
            nlinarith only [this]
          omega
        -- Step 1: `ef K m p ≤ (p / (p - 1)) ^ (K + 1 - xi m p)`
        have hef_le : ef K m p ≤ ((p : ℝ) / ((p : ℝ) - 1)) ^ (K + 1 - xi m p) := by
          unfold ef
          have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
          have h1p : 0 < 1 - 1 / (p : ℝ) := by
            rw [sub_pos, div_lt_one hp_pos]; exact_mod_cast hp_pr.one_lt
          have hinv : (1 - 1 / (p : ℝ))⁻¹ = (p : ℝ) / ((p : ℝ) - 1) := by
            have : (p : ℝ) - 1 ≠ 0 := by
              have : (2 : ℝ) ≤ p := by exact_mod_cast hp_pr.two_le
              linarith
            field_simp [hp_pos.ne', this]
          have hpow_split : (1 - 1 / (p : ℝ))⁻¹ ^ (K + 1) =
              (1 - 1 / (p : ℝ))⁻¹ ^ (xi m p) * (1 - 1 / (p : ℝ))⁻¹ ^ (K + 1 - xi m p) := by
            rw [← pow_add, Nat.add_sub_of_le hxi_le]
          rw [hpow_split, ← mul_assoc, hinv]
          have heul : (1 - (xi m p : ℝ) / p) * (1 - 1 / (p : ℝ))⁻¹ ^ (xi m p) ≤ 1 :=
            euler_factor_le_one (by omega)
          rw [hinv] at heul
          have hpow_nn : 0 ≤ ((p : ℝ) / ((p : ℝ) - 1)) ^ (K + 1 - xi m p) := by
            have : (2 : ℝ) ≤ p := by exact_mod_cast hp_pr.two_le
            have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
            positivity
          nlinarith only [heul, hpow_nn]
        -- Step 2: `K + 1 - xi m p ≤ #{q ∈ pairsK K : p ∣ Gprime r K q.1 q.2 (argMax q) m}`
        have hcount_le : K + 1 - xi m p ≤
            ((pairsK K).filter (fun q => p ∣ Gprime r K q.1 q.2 (argMax q) m)).card := by
          have : Fact p.Prime := ⟨hp_pr⟩
          have hnd_A : ∀ j ≤ K, ¬ p ∣ coeffA m j := by
            intro j hj hd
            rw [coeffA_eq_prod] at hd
            obtain ⟨u, hu, hpu⟩ := (hp_pr.prime.dvd_finsetProd_iff _).mp hd
            rw [Finset.mem_range] at hu
            have huK : u < K := by omega
            simp only [huK, dite_true] at hpu
            exact hnd_m (dvd_trans hpu (Finset.dvd_prod_of_mem _ (Finset.mem_univ (⟨u, huK⟩ : Fin K))))
          let rt : ℕ → ℕ := fun j => (-(coeffB m j : ZMod p) * (coeffA m j : ZMod p)⁻¹).val
          have hrt_lt : ∀ j, rt j < p := fun j => ZMod.val_lt _
          have hrt_dvd : ∀ j ≤ K, p ∣ chainForm m j (rt j) := by
            intro j hj
            rw [← ZMod.natCast_eq_zero_iff, chainForm_eq_linear, Nat.cast_add, Nat.cast_mul]
            simp only [rt, ZMod.natCast_zmod_val]
            have hAne : (coeffA m j : ZMod p) ≠ 0 := fun h0 =>
              hnd_A j hj ((ZMod.natCast_eq_zero_iff _ p).mp h0)
            calc (coeffA m j : ZMod p) * (-(coeffB m j : ZMod p) * (coeffA m j : ZMod p)⁻¹) +
                  (coeffB m j : ZMod p)
                = -(coeffB m j : ZMod p) * ((coeffA m j : ZMod p) * (coeffA m j : ZMod p)⁻¹) +
                  (coeffB m j : ZMod p) := by ring
              _ = 0 := by rw [mul_inv_cancel₀ hAne]; ring
          have hrt_eq_iff : ∀ j h, j < h → h ≤ K → (rt j = rt h ↔ p ∣ gForm m j h) := by
            intro j h hjh hhK
            constructor
            · intro heq
              have h1 := hrt_dvd j (by omega)
              have h2 : p ∣ chainForm m h (rt j) := heq ▸ hrt_dvd h hhK
              rw [chainForm_eq_mul_add_gForm m hjh.le] at h2
              exact (Nat.dvd_add_right (dvd_mul_of_dvd_right h1 _)).mp h2
            · intro hgdvd
              have h1 := hrt_dvd j (by omega)
              have h2 : p ∣ chainForm m h (rt j) := by
                rw [chainForm_eq_mul_add_gForm m hjh.le]
                exact dvd_add (dvd_mul_of_dvd_right h1 _) hgdvd
              have hz1 : (coeffA m h : ZMod p) * (rt j : ZMod p) + (coeffB m h : ZMod p) = 0 := by
                have := (ZMod.natCast_eq_zero_iff (chainForm m h (rt j)) p).mpr h2
                rwa [chainForm_eq_linear, Nat.cast_add, Nat.cast_mul] at this
              have hz2 : (coeffA m h : ZMod p) * (rt h : ZMod p) + (coeffB m h : ZMod p) = 0 := by
                have := (ZMod.natCast_eq_zero_iff (chainForm m h (rt h)) p).mpr (hrt_dvd h hhK)
                rwa [chainForm_eq_linear, Nat.cast_add, Nat.cast_mul] at this
              have hAne : (coeffA m h : ZMod p) ≠ 0 := fun h0 =>
                hnd_A h hhK ((ZMod.natCast_eq_zero_iff _ p).mp h0)
              have hsub0 : (coeffA m h : ZMod p) * ((rt j : ZMod p) - (rt h : ZMod p)) = 0 := by
                linear_combination hz1 - hz2
              have hzeq : (rt j : ZMod p) = (rt h : ZMod p) :=
                sub_eq_zero.mp ((mul_eq_zero.mp hsub0).resolve_left hAne)
              have hval := congrArg ZMod.val hzeq
              rwa [ZMod.val_natCast_of_lt (hrt_lt j), ZMod.val_natCast_of_lt (hrt_lt h)] at hval
          -- Image of `range (K + 1)` under `rt` has size `≤ xi m p`
          have himg_le : ((range (K + 1)).image rt).card ≤ xi m p := by
            unfold xi
            refine Finset.card_le_card fun n hn => ?_
            rw [Finset.mem_image] at hn
            obtain ⟨j, hj, rfl⟩ := hn
            rw [Finset.mem_filter, Finset.mem_range]
            exact ⟨hrt_lt j, dvd_trans (hrt_dvd j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
              (Finset.dvd_prod_of_mem _ hj)⟩
          -- Collisions `Hcoll := {h ∈ range (K + 1) | ∃ j < h, rt j = rt h}` has size `K + 1 - ((range (K + 1)).image rt).card`
          let Hnew := (range (K + 1)).filter (fun h => ∀ j < h, rt j ≠ rt h)
          let Hcoll := (range (K + 1)).filter (fun h => ∃ j < h, rt j = rt h)
          have hHnew_eq : Hnew.card = ((range (K + 1)).image rt).card := by
            refine Finset.card_bij (fun h _ => rt h) ?_ ?_ ?_
            · intro h hh; exact Finset.mem_image_of_mem _ (Finset.mem_filter.mp hh).1
            · intro a ha b hb heq
              simp only [Hnew, Finset.mem_filter] at ha hb
              by_contra hne
              rcases lt_or_gt_of_ne hne with hlt | hlt
              · exact hb.2 a hlt heq
              · exact ha.2 b hlt heq.symm
            · intro y hy
              rw [Finset.mem_image] at hy
              have hex : ∃ j, j ∈ range (K + 1) ∧ rt j = y := hy
              let h₀ := Nat.find hex
              have hh₀ := Nat.find_spec hex
              refine ⟨h₀, Finset.mem_filter.mpr ⟨hh₀.1, fun j hj heqj => ?_⟩, hh₀.2⟩
              have hjmem : j ∈ range (K + 1) :=
                Finset.mem_range.mpr (lt_trans hj (Finset.mem_range.mp hh₀.1))
              exact Nat.find_min hex hj ⟨hjmem, heqj.trans hh₀.2⟩
          have hHsum : Hnew.card + Hcoll.card = K + 1 := by
            have hdisjH : Disjoint Hnew Hcoll := by
              rw [Finset.disjoint_left]; intro h h1 h2
              simp only [Hnew, Hcoll, Finset.mem_filter] at h1 h2
              obtain ⟨j, hj, heq⟩ := h2.2
              exact h1.2 j hj heq
            have hunionH : Hnew ∪ Hcoll = range (K + 1) := by
              ext h; simp only [Hnew, Hcoll, Finset.mem_union, Finset.mem_filter]
              by_cases hc : ∃ j < h, rt j = rt h
              · exact ⟨by rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> exact h1, fun h1 => Or.inr ⟨h1, hc⟩⟩
              · push Not at hc
                exact ⟨by rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> exact h1, fun h1 => Or.inl ⟨h1, hc⟩⟩
            rw [← Finset.card_union_of_disjoint hdisjH, hunionH, Finset.card_range]
          -- Injection from `Hcoll` into `(pairsK K).filter (fun q => p ∣ Gprime ...)`
          have hinj_coll : Hcoll.card ≤
              ((pairsK K).filter (fun q => p ∣ Gprime r K q.1 q.2 (argMax q) m)).card := by
            let f : ℕ → ℕ × ℕ := fun h =>
              if hc : ((range h).filter (fun j => rt j = rt h)).Nonempty then
                (((range h).filter (fun j => rt j = rt h)).max' hc, h)
              else (0, h)
            refine Finset.card_le_card_of_injOn f ?_ ?_
            · intro h hh
              rw [Finset.mem_coe] at hh ⊢
              simp only [Hcoll, Finset.mem_filter, Finset.mem_range] at hh
              have hne : ((range h).filter (fun j => rt j = rt h)).Nonempty := by
                obtain ⟨j, hj, heq⟩ := hh.2
                exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, heq⟩⟩
              simp only [f, dif_pos hne]
              let j := ((range h).filter (fun j => rt j = rt h)).max' hne
              have hj_mem : j ∈ (range h).filter (fun j => rt j = rt h) := Finset.max'_mem _ hne
              simp only [Finset.mem_filter, Finset.mem_range] at hj_mem
              have hjh_dvd : p ∣ gForm m j h := (hrt_eq_iff j h hj_mem.1 (by omega)).mp hj_mem.2
              have hj2 : j + 2 ≤ h := by
                by_contra hlt
                have heq1 : h = j + 1 := by omega
                rw [heq1, gForm_succ_self] at hjh_dvd
                exact hp_pr.not_dvd_one hjh_dvd
              have hq_mem : (j, h) ∈ pairsK K := by
                unfold pairsK
                simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
                exact ⟨⟨by omega, hh.1⟩, hj2⟩
              rw [Finset.mem_filter]
              refine ⟨hq_mem, ?_⟩
              unfold Gprime
              refine Finset.dvd_prod_of_mem _ ?_
              rw [Finset.mem_filter, Nat.mem_primeFactors]
              refine ⟨⟨hp_pr, hjh_dvd, Nat.one_le_iff_ne_zero.mp (gForm_pos m hj_mem.1)⟩, hp_gtr, ?_⟩
              intro hdvd_prod
              rcases hp_pr.dvd_mul.mp hdvd_prod with h1 | h2
              · exact hnd_m h1
              · have hl := harg (j, h) hq_mem
                have hrt_eq : rt (argMax (j, h)) = rt h :=
                  (hrt_eq_iff (argMax (j, h)) h hl.2 (by omega)).mpr h2
                have hl_in : (argMax (j, h) : ℕ) ∈ (range h).filter (fun i => rt i = rt h) :=
                  Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hl.2, hrt_eq⟩
                have hl_le : (argMax (j, h) : ℕ) ≤ j := Finset.le_max' _ _ hl_in
                omega
            · intro h₁ _ h₂ _ heq
              have h2 := congrArg Prod.snd heq
              simp only [f] at h2
              split_ifs at h2 <;> exact h2
          omega
        -- Step 3: conclude pointwise bound for `p ∈ P2`
        rw [← Finset.prod_filter, Finset.prod_const]
        have hge1 : (1 : ℝ) ≤ (p : ℝ) / ((p : ℝ) - 1) := by
          have : (2 : ℝ) ≤ p := by exact_mod_cast hp_pr.two_le
          rw [one_le_div (by linarith)]; linarith
        exact hef_le.trans (pow_le_pow_right₀ hge1 hcount_le)
      calc ∏ p ∈ P2, ef K m p
          ≤ ∏ p ∈ P2, ∏ q ∈ pairsK K,
              (if p ∣ Gprime r K q.1 q.2 (argMax q) m then (p : ℝ) / ((p : ℝ) - 1) else 1) :=
            Finset.prod_le_prod (fun p hp => ef_nonneg m (Nat.prime_of_mem_primeFactors
              (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1)) hterm
        _ = ∏ q ∈ pairsK K, ∏ p ∈ P2,
              (if p ∣ Gprime r K q.1 q.2 (argMax q) m then (p : ℝ) / ((p : ℝ) - 1) else 1) :=
            Finset.prod_comm
        _ ≤ ∏ q ∈ pairsK K, psiR r (Gprime r K q.1 q.2 (argMax q) m) := by
            refine Finset.prod_le_prod (fun q _ => Finset.prod_nonneg (fun p hp => by
              split_ifs
              · have hp_pr := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
                have : (2 : ℝ) ≤ p := by exact_mod_cast hp_pr.two_le
                have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
                positivity
              · norm_num)) (fun q _ => ?_)
            rw [← Finset.prod_filter]
            unfold psiR
            have hsub : P2.filter (fun p => p ∣ Gprime r K q.1 q.2 (argMax q) m) ⊆
                (Gprime r K q.1 q.2 (argMax q) m).primeFactors.filter (r < ·) := by
              intro p hp
              simp only [P2, Pbig, Finset.mem_filter, Nat.mem_primeFactors] at hp ⊢
              exact ⟨⟨hp.1.1.1.1, hp.2, Nat.one_le_iff_ne_zero.mp (Gprime_pos r K q.1 q.2 (argMax q) m)⟩, hp.1.1.2⟩
            exact prod_le_prod_of_subset_ge_one hsub _ (fun p hp => by
              have hp_pr := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
              have : (2 : ℝ) ≤ p := by exact_mod_cast hp_pr.two_le
              have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
              positivity) (fun p hp => by
              have hp_pr := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).1
              have : (2 : ℝ) ≤ p := by exact_mod_cast hp_pr.two_le
              rw [one_le_div (by linarith)]; linarith)
    exact mul_le_mul hP1 hP2
      (Finset.prod_nonneg (fun p hp => ef_nonneg m (Nat.prime_of_mem_primeFactors
        (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1)))
      (Finset.prod_nonneg (fun i _ => pow_nonneg (psiR_pos r (m i)).le K))

/- CRT average of small primes product -/

lemma sum_ef_mod_prime (K p : ℕ) (hp : p.Prime) :
    ∑ m ∈ Fintype.piFinset (fun _ : Fin K => range p), ef K m p = (p : ℝ) ^ K := by
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  have h1p : (1 - 1 / (p : ℝ))⁻¹ = (p : ℝ) / ((p : ℝ) - 1) := by field_simp [hp_pos.ne', hp1_pos.ne']
  unfold ef
  simp_rw [h1p, ← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    mul_one, ← Finset.sum_div]
  have hcard : (Fintype.piFinset (fun _ : Fin K => range p)).card = p ^ K := by
    simp [Fintype.card_piFinset]
  rw [hcard, ← Nat.cast_sum, sum_xi_eq_pow_sub_pow K p hp]
  have hpow_le : (p - 1) ^ (K + 1) ≤ p ^ (K + 1) := Nat.pow_le_pow_left (by omega) _
  rw [Nat.cast_sub hpow_le]
  push_cast [Nat.cast_sub hp.one_le]
  rw [div_pow]
  have hp1_pow : ((p : ℝ) - 1) ^ (K + 1) ≠ 0 := pow_ne_zero _ hp1_pos.ne'
  field_simp [hp_pos.ne', hp1_pow]
  ring

lemma crt_sum_prod_ef (K : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∑ m ∈ Fintype.piFinset (fun _ : Fin K => range (∏ p ∈ P, p)),
      ∏ p ∈ P, ef K m p = ((∏ p ∈ P, p : ℕ) : ℝ) ^ K := by
  classical
  induction P using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_one, one_pow]
    have : (Fintype.piFinset (fun _ : Fin K => range 1)).card = 1 := by simp
    rw [this]; simp
  | @insert p P hp ih =>
    have hp_pr : p.Prime := hP p (Finset.mem_insert_self p P)
    have hP_pr : ∀ q ∈ P, q.Prime := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    let Q := ∏ q ∈ P, q
    have hcop : p.Coprime Q := Nat.Coprime.prod_right fun q hq =>
      (Nat.coprime_primes hp_pr (hP_pr q hq)).mpr (fun heq => hp (heq ▸ hq))
    have hQ_pos : 0 < Q := Finset.prod_pos (fun q hq => (hP_pr q hq).pos)
    rw [Finset.prod_insert hp]
    -- Bijection between `Fin K → range (p * Q)` and `(Fin K → range p) × (Fin K → range Q)`
    let S := Fintype.piFinset (fun _ : Fin K => range (p * Q))
    let S₁ := Fintype.piFinset (fun _ : Fin K => range p)
    let S₂ := Fintype.piFinset (fun _ : Fin K => range Q)
    have hbij : ∑ m ∈ S, ∏ q ∈ insert p P, ef K m q =
        ∑ x ∈ S₁ ×ˢ S₂, ef K x.1 p * ∏ q ∈ P, ef K x.2 q := by
      refine Finset.sum_bij (fun m _ => (fun i => m i % p, fun i => m i % Q)) ?_ ?_ ?_ ?_
      · intro m _
        simp only [S₁, S₂, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_range]
        exact ⟨fun i => Nat.mod_lt _ hp_pr.pos, fun i => Nat.mod_lt _ hQ_pos⟩
      · intro m₁ hm₁ m₂ hm₂ heq
        simp only [S, Fintype.mem_piFinset, Finset.mem_range] at hm₁ hm₂
        ext i
        have h1 : m₁ i ≡ m₂ i [MOD p] := congrFun (congrArg Prod.fst heq) i
        have h2 : m₁ i ≡ m₂ i [MOD Q] := congrFun (congrArg Prod.snd heq) i
        have h12 : m₁ i ≡ m₂ i [MOD p * Q] := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h1, h2⟩
        rwa [Nat.ModEq, Nat.mod_eq_of_lt (hm₁ i), Nat.mod_eq_of_lt (hm₂ i)] at h12
      · intro ⟨m₁, m₂⟩ hx
        simp only [S₁, S₂, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_range] at hx
        let m : Fin K → ℕ := fun i => (Nat.chineseRemainder hcop (m₁ i) (m₂ i)).1 % (p * Q)
        refine ⟨m, ?_, ?_⟩
        · simp only [S, Fintype.mem_piFinset, Finset.mem_range]
          exact fun i => Nat.mod_lt _ (Nat.mul_pos hp_pr.pos hQ_pos)
        · ext i
          · have hmod := (Nat.ModEq.of_mul_right Q (Nat.mod_modEq _ (p * Q))).trans
              (Nat.chineseRemainder hcop (m₁ i) (m₂ i)).2.1
            rw [Nat.ModEq] at hmod; exact hmod.trans (Nat.mod_eq_of_lt (hx.1 i))
          · have hmod := (Nat.ModEq.of_mul_left p (Nat.mod_modEq _ (p * Q))).trans
              (Nat.chineseRemainder hcop (m₁ i) (m₂ i)).2.2
            rw [Nat.ModEq] at hmod; exact hmod.trans (Nat.mod_eq_of_lt (hx.2 i))
      · intro m _
        rw [Finset.prod_insert hp]
        congr 1
        · unfold ef
          rw [xi_mod_congr m (fun i => m i % p) p (fun i => (Nat.mod_modEq (m i) p).symm)]
        · refine Finset.prod_congr rfl fun q hq => ?_
          unfold ef
          have hqQ : q ∣ Q := Finset.dvd_prod_of_mem _ hq
          rw [xi_mod_congr m (fun i => m i % Q) q (fun i =>
            ((Nat.mod_modEq (m i) Q).of_dvd hqQ).symm)]
    rw [hbij, Finset.sum_product]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, sum_ef_mod_prime K p hp_pr, ih hP_pr]
    rw [Nat.cast_mul, mul_pow]

lemma small_primes_crt_avg {K : ℕ} (hK : 3 ≤ K) (N M : Fin K → ℕ)
    (hM_big : ∀ i, 2 ^ (10 ^ 6 * (K + 1) ^ 7) ≤ M i) :
    ∑ m ∈ Fintype.piFinset (fun i : Fin K => Ioc (N i) (N i + M i)),
      ∏ p ∈ (rParam K + 1).primesBelow, ef K m p ≤
        Real.exp 1 * ∏ i : Fin K, (M i : ℝ) := by
  let r := rParam K
  let P := (r + 1).primesBelow
  let M' := ∏ p ∈ P, p
  have hM'_pos : 1 ≤ M' :=
    Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun p hp => (Nat.prime_of_mem_primesBelow hp).ne_zero))
  have hM'_le : (K + 1) * M' ≤ 2 ^ (10 ^ 6 * (K + 1) ^ 7) := by
    have h4r : (M' : ℝ) ≤ (4 : ℝ) ^ r := by
      have := prod_primes_le_four_pow r
      simpa [M', P, Nat.cast_prod] using this
    have hM'_nat : M' ≤ 2 ^ (2 * r) := by
      have h4eq : (4 : ℝ) ^ r = ((2 ^ (2 * r) : ℕ) : ℝ) := by
        push_cast; rw [pow_mul]; norm_num
      rw [h4eq] at h4r
      exact_mod_cast h4r
    have hL_le : LParam K ≤ 2 * (K + 1) := by
      have := clog_two_le (K + 1); unfold LParam; omega
    have h2r_le : 2 * r ≤ 16 * (K + 1) ^ 3 := by
      change 2 * (4 * (K + 1) ^ 2 * LParam K) ≤ 16 * (K + 1) ^ 3
      have : 4 * (K + 1) ^ 2 * LParam K ≤ 4 * (K + 1) ^ 2 * (2 * (K + 1)) :=
        Nat.mul_le_mul_left _ hL_le
      nlinarith only [this]
    have hK_pow : K + 1 ≤ 2 ^ (K + 1) := (Nat.lt_two_pow_self (n := K + 1)).le
    have hexp : (K + 1) + 2 * r ≤ 10 ^ 6 * (K + 1) ^ 7 := by
      have h1 : (K + 1) ^ 3 ≤ (K + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by norm_num)
      have h2 : K + 1 ≤ (K + 1) ^ 7 := le_self_pow₀ (by omega) (by norm_num)
      nlinarith only [h2r_le, h1, h2]
    calc (K + 1) * M' ≤ 2 ^ (K + 1) * 2 ^ (2 * r) := Nat.mul_le_mul hK_pow hM'_nat
      _ = 2 ^ ((K + 1) + 2 * r) := (pow_add 2 _ _).symm
      _ ≤ 2 ^ (10 ^ 6 * (K + 1) ^ 7) := Nat.pow_le_pow_right (by norm_num) hexp
  let Box := Fintype.piFinset (fun i : Fin K => Ioc (N i) (N i + M i))
  let ModBox := Fintype.piFinset (fun _ : Fin K => range M')
  -- Group `Box` by `m ↦ (fun i => m i % M') ∈ ModBox`
  have hgroup : ∑ m ∈ Box, ∏ p ∈ P, ef K m p =
      ∑ rvec ∈ ModBox,
        ((Box.filter (fun m => (fun i => m i % M') = rvec)).card : ℝ) *
          ∏ p ∈ P, ef K rvec p := by
    have hpart : Box = ModBox.biUnion (fun rvec => Box.filter (fun m => (fun i => m i % M') = rvec)) := by
      ext m
      simp only [Finset.mem_biUnion, Finset.mem_filter, ModBox, Fintype.mem_piFinset, Finset.mem_range]
      constructor
      · intro hm; exact ⟨fun i => m i % M', fun i => Nat.mod_lt _ (by omega), hm, rfl⟩
      · rintro ⟨_, _, hm, _⟩; exact hm
    have hdisj : Set.PairwiseDisjoint (ModBox : Set (Fin K → ℕ))
        (fun rvec => Box.filter (fun m => (fun i => m i % M') = rvec)) := by
      intro r₁ _ r₂ _ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]; intro m h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    conv_lhs => rw [hpart]
    rw [Finset.sum_biUnion hdisj]
    refine Finset.sum_congr rfl fun rvec _ => ?_
    have hcongr : ∀ m ∈ Box.filter (fun m => (fun i => m i % M') = rvec),
        ∏ p ∈ P, ef K m p = ∏ p ∈ P, ef K rvec p := by
      intro m hm
      have hmod := (Finset.mem_filter.mp hm).2
      refine Finset.prod_congr rfl fun p hp => ?_
      unfold ef
      have hpM' : p ∣ M' := Finset.dvd_prod_of_mem _ hp
      rw [xi_mod_congr m rvec p (fun i => by
        rw [← congrFun hmod i]
        exact ((Nat.mod_modEq (m i) M').of_dvd hpM').symm)]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul]
  -- Each fiber has size `≤ ∏ i, (M i / M' + 1) ≤ e * (∏ i, M i) / (M') ^ K`
  have hfiber : ∀ rvec ∈ ModBox,
      ((Box.filter (fun m => (fun i => m i % M') = rvec)).card : ℝ) ≤
        Real.exp 1 * (∏ i : Fin K, (M i : ℝ)) / (M' : ℝ) ^ K := by
    intro rvec _
    have hsub : Box.filter (fun m => (fun i => m i % M') = rvec) =
        Fintype.piFinset (fun i : Fin K => (Ioc (N i) (N i + M i)).filter (fun x => x % M' = rvec i)) := by
      ext m
      simp only [Box, Finset.mem_filter, Fintype.mem_piFinset]
      constructor
      · rintro ⟨hm, heq⟩ i; exact ⟨hm i, congrFun heq i⟩
      · intro h; exact ⟨fun i => (h i).1, funext fun i => (h i).2⟩
    rw [hsub, Fintype.card_piFinset, Nat.cast_prod]
    have hcoord : ∀ i : Fin K,
        (((Ioc (N i) (N i + M i)).filter (fun x => x % M' = rvec i)).card : ℝ) ≤
          (1 + 1 / ((K + 1 : ℕ) : ℝ)) * ((M i : ℝ) / (M' : ℝ)) := by
      intro i
      have hc := card_Ioc_modEq_le (N i) (M i) M' (rvec i) hM'_pos
      have hM'_r : (0 : ℝ) < M' := by exact_mod_cast hM'_pos
      have hdiv : ((M i / M' : ℕ) : ℝ) ≤ (M i : ℝ) / (M' : ℝ) := by
        rw [le_div_iff₀ hM'_r]; exact_mod_cast Nat.div_mul_le_self (M i) M'
      have h1_le : (1 : ℝ) ≤ (1 / ((K + 1 : ℕ) : ℝ)) * ((M i : ℝ) / (M' : ℝ)) := by
        have hMi : (K + 1) * M' ≤ M i := hM'_le.trans (hM_big i)
        have hMi_r : ((K + 1 : ℕ) : ℝ) * (M' : ℝ) ≤ (M i : ℝ) := by exact_mod_cast hMi
        rw [one_div_mul_eq_div, div_div, one_le_div (by positivity)]
        linarith only [hMi_r]
      have hcR : (((Ioc (N i) (N i + M i)).filter (fun x => x % M' = rvec i)).card : ℝ) ≤
          ((M i / M' : ℕ) : ℝ) + 1 := by exact_mod_cast hc
      linarith only [hcR, hdiv, h1_le]
    calc ∏ i : Fin K, (((Ioc (N i) (N i + M i)).filter (fun x => x % M' = rvec i)).card : ℝ)
        ≤ ∏ i : Fin K, ((1 + 1 / ((K + 1 : ℕ) : ℝ)) * ((M i : ℝ) / (M' : ℝ))) :=
          Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i _ => hcoord i)
      _ = (1 + 1 / ((K + 1 : ℕ) : ℝ)) ^ K * ((∏ i : Fin K, (M i : ℝ)) / (M' : ℝ) ^ K) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ Real.exp 1 * ((∏ i : Fin K, (M i : ℝ)) / (M' : ℝ) ^ K) := by
          refine mul_le_mul_of_nonneg_right ?_
            (div_nonneg (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)) (pow_nonneg (Nat.cast_nonneg _) _))
          calc (1 + 1 / ((K + 1 : ℕ) : ℝ)) ^ K
              ≤ (Real.exp (1 / ((K + 1 : ℕ) : ℝ))) ^ K :=
                pow_le_pow_left₀ (by positivity)
                  (by linarith only [Real.add_one_le_exp (1 / ((K + 1 : ℕ) : ℝ))]) K
            _ = Real.exp ((K : ℝ) / ((K + 1 : ℕ) : ℝ)) := by
                rw [← Real.exp_nat_mul]; congr 1; ring
            _ ≤ Real.exp 1 := by
                apply Real.exp_le_exp.mpr
                rw [div_le_one (by positivity)]; push_cast; linarith
      _ = Real.exp 1 * (∏ i : Fin K, (M i : ℝ)) / (M' : ℝ) ^ K := by ring
  rw [hgroup]
  calc ∑ rvec ∈ ModBox,
        ((Box.filter (fun m => (fun i => m i % M') = rvec)).card : ℝ) * ∏ p ∈ P, ef K rvec p
      ≤ ∑ rvec ∈ ModBox,
          (Real.exp 1 * (∏ i : Fin K, (M i : ℝ)) / (M' : ℝ) ^ K) * ∏ p ∈ P, ef K rvec p := by
        refine Finset.sum_le_sum fun rvec hr => ?_
        exact mul_le_mul_of_nonneg_right (hfiber rvec hr)
          (Finset.prod_nonneg (fun p hp => ef_nonneg rvec (Nat.prime_of_mem_primesBelow hp)))
    _ = (Real.exp 1 * (∏ i : Fin K, (M i : ℝ)) / (M' : ℝ) ^ K) *
          ∑ rvec ∈ ModBox, ∏ p ∈ P, ef K rvec p := (Finset.mul_sum _ _ _).symm
    _ = (Real.exp 1 * (∏ i : Fin K, (M i : ℝ)) / (M' : ℝ) ^ K) * (M' : ℝ) ^ K := by
        rw [crt_sum_prod_ef K P (fun p hp => Nat.prime_of_mem_primesBelow hp)]
    _ = Real.exp 1 * ∏ i : Fin K, (M i : ℝ) := by
        have hM'ne : (M' : ℝ) ^ K ≠ 0 := pow_ne_zero K (by exact_mod_cast (show M' ≠ 0 by omega))
        field_simp [hM'ne]

/- Helper lemmas for the three Hölder factors in `singular_avg` -/

lemma singular_avg_fac0 {K : ℕ} (hK : 3 ≤ K) (N M : Fin K → ℕ)
    (hM_big : ∀ i, 2 ^ (10 ^ 6 * (K + 1) ^ 7) ≤ M i) :
    (∑ m ∈ Fintype.piFinset (fun i : Fin K => Ioc (N i) (N i + M i)),
      (∏ p ∈ (rParam K + 1).primesBelow, ef K m p) ^ (1 - 1 / (LParam K : ℝ))⁻¹) ^
      (1 - 1 / (LParam K : ℝ)) ≤
      Real.exp (80 * (K + 1 : ℝ)) * Real.exp 1 * (∏ i : Fin K, (M i : ℝ)) ^ (1 - 1 / (LParam K : ℝ)) := by
  let r := rParam K
  let L := LParam K
  let Box := Fintype.piFinset (fun i : Fin K => Ioc (N i) (N i + M i))
  have hL4 : 4 ≤ L := by unfold L LParam; omega
  have hL_r : (4 : ℝ) ≤ L := by exact_mod_cast hL4
  have hLm1_pos : (0 : ℝ) < (L : ℝ) - 1 := by linarith only [hL_r]
  have hK1sq : 1 ≤ (K + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos K)
  have hU_nn : ∀ m, 0 ≤ ∏ p ∈ (r + 1).primesBelow, ef K m p := fun m =>
    Finset.prod_nonneg (fun p hp => ef_nonneg m (Nat.prime_of_mem_primesBelow hp))
  have hU_max : ∀ m ∈ Box,
      (∏ p ∈ (r + 1).primesBelow, ef K m p) ^ (1 / ((L : ℝ) - 1)) ≤ Real.exp (80 * (K + 1 : ℝ)) := by
    intro m _
    have hU_le : ∏ p ∈ (r + 1).primesBelow, ef K m p ≤
        (Real.exp (16 * Real.log (Real.log (r : ℝ) + 2) + 32)) ^ (K + 1) := by
      have h1 : ∏ p ∈ (r + 1).primesBelow, ef K m p ≤
          ∏ p ∈ (r + 1).primesBelow, (1 - 1 / (p : ℝ))⁻¹ ^ (K + 1) := by
        refine Finset.prod_le_prod (fun p hp => ef_nonneg m (Nat.prime_of_mem_primesBelow hp)) (fun p hp => ?_)
        unfold ef
        have hp_pr := Nat.prime_of_mem_primesBelow hp
        have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
        have hle1 : 1 - (xi m p : ℝ) / p ≤ 1 := by linarith [show (0 : ℝ) ≤ (xi m p : ℝ) / p by positivity]
        have hpos : 0 < (1 - 1 / (p : ℝ))⁻¹ ^ (K + 1) := by
          have : 0 < 1 - 1 / (p : ℝ) := by rw [sub_pos, div_lt_one hp_pos]; exact_mod_cast hp_pr.one_lt
          positivity
        nlinarith only [hle1, hpos]
      rw [Finset.prod_pow] at h1
      refine h1.trans (pow_le_pow_left₀ (Finset.prod_nonneg (fun p hp => by
        have hp_pr := Nat.prime_of_mem_primesBelow hp
        have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
        have : 0 < 1 - 1 / (p : ℝ) := by rw [sub_pos, div_lt_one hp_pos]; exact_mod_cast hp_pr.one_lt
        positivity)) ?_ (K + 1))
      have hr2 : (2 : ℝ) ≤ r := by
        have : 2 ≤ r := by change 2 ≤ 4 * (K + 1) ^ 2 * L; nlinarith only [hL4, hK1sq]
        exact_mod_cast this
      simpa [Nat.floor_natCast] using prod_one_sub_inv_le hr2
    calc (∏ p ∈ (r + 1).primesBelow, ef K m p) ^ (1 / ((L : ℝ) - 1))
        ≤ ((Real.exp (16 * Real.log (Real.log (r : ℝ) + 2) + 32)) ^ (K + 1)) ^ (1 / ((L : ℝ) - 1)) :=
          Real.rpow_le_rpow (hU_nn m) hU_le (by positivity)
      _ = Real.exp ((K + 1 : ℝ) * ((16 * Real.log (Real.log (r : ℝ) + 2) + 32) / ((L : ℝ) - 1))) := by
          rw [← Real.exp_nat_mul, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
          congr 1; push_cast; ring
      _ ≤ Real.exp (80 * (K + 1 : ℝ)) := by
          apply Real.exp_le_exp.mpr
          have hlogr_le : Real.log (r : ℝ) + 2 ≤ 3 * ((L : ℝ) - 1) := by
            have hL_le : L ≤ 2 * (K + 1) := by
              have := clog_two_le (K + 1); unfold L LParam; omega
            have hr_le : (r : ℝ) ≤ 8 * ((K + 1 : ℕ) : ℝ) ^ 3 := by
              have : r ≤ 8 * (K + 1) ^ 3 := by
                change 4 * (K + 1) ^ 2 * L ≤ 8 * (K + 1) ^ 3
                have := Nat.mul_le_mul_left (4 * (K + 1) ^ 2) hL_le
                nlinarith only [this]
              exact_mod_cast this
            have hr_pos : (0 : ℝ) < r := by
              have : 1 ≤ r := by change 1 ≤ 4 * (K + 1) ^ 2 * L; nlinarith only [hL4, hK1sq]
              exact_mod_cast this
            have h1 : Real.log (r : ℝ) ≤ Real.log 8 + 3 * Real.log ((K + 1 : ℕ) : ℝ) := by
              have h0 := Real.log_le_log hr_pos hr_le
              rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Nat.cast_ofNat] at h0
              exact h0
            have h8 : Real.log 8 ≤ 3 := by
              rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
              push_cast
              have := Real.log_two_lt_d9; linarith
            have hlogK_le : Real.log ((K + 1 : ℕ) : ℝ) ≤ (Nat.clog 2 (K + 1) : ℝ) := by
              have hle : ((K + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (Nat.clog 2 (K + 1)) := by
                exact_mod_cast Nat.le_pow_clog (by norm_num) (K + 1)
              have hl := Real.log_le_log (by positivity) hle
              rw [Real.log_pow] at hl
              have := Real.log_two_lt_d9
              nlinarith only [hl, this, show (0 : ℝ) ≤ Nat.clog 2 (K + 1) by positivity]
            have hLm1_eq : (L : ℝ) - 1 = (Nat.clog 2 (K + 1) : ℝ) + 3 := by
              simp only [L, LParam, Nat.cast_add, Nat.cast_ofNat]; ring
            linarith only [h1, h8, hlogK_le, hLm1_eq]
          have hll : Real.log (Real.log (r : ℝ) + 2) ≤ Real.log (r : ℝ) + 2 := by
            have hr1 : (1 : ℝ) ≤ r := by
              have : 1 ≤ r := by change 1 ≤ 4 * (K + 1) ^ 2 * L; nlinarith only [hL4, hK1sq]
              exact_mod_cast this
            linarith only [Real.log_le_sub_one_of_pos (show 0 < Real.log (r : ℝ) + 2 by
              linarith only [Real.log_nonneg hr1])]
          have hdiv_le : (16 * Real.log (Real.log (r : ℝ) + 2) + 32) / ((L : ℝ) - 1) ≤ 80 := by
            rw [div_le_iff₀ hLm1_pos]
            nlinarith only [hlogr_le, hll, hL_r]
          nlinarith only [hdiv_le, show (0 : ℝ) ≤ (K + 1 : ℝ) by positivity]
  have hw0_eq : (1 - 1 / (L : ℝ))⁻¹ = 1 + 1 / ((L : ℝ) - 1) := by
    field_simp [show (L : ℝ) ≠ 0 by linarith only [hL_r], hLm1_pos.ne']; ring
  have hsum0 : ∑ m ∈ Box, (∏ p ∈ (r + 1).primesBelow, ef K m p) ^ (1 - 1 / (L : ℝ))⁻¹ ≤
      Real.exp (80 * (K + 1 : ℝ)) * (Real.exp 1 * ∏ i : Fin K, (M i : ℝ)) := by
    calc ∑ m ∈ Box, (∏ p ∈ (r + 1).primesBelow, ef K m p) ^ (1 - 1 / (L : ℝ))⁻¹
        = ∑ m ∈ Box, (∏ p ∈ (r + 1).primesBelow, ef K m p) *
            (∏ p ∈ (r + 1).primesBelow, ef K m p) ^ (1 / ((L : ℝ) - 1)) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [hw0_eq]
          by_cases h0 : (∏ p ∈ (r + 1).primesBelow, ef K m p) = 0
          · rw [h0, Real.zero_rpow (by positivity), zero_mul]
          · have hpos : 0 < ∏ p ∈ (r + 1).primesBelow, ef K m p :=
              lt_of_le_of_ne (hU_nn m) (Ne.symm h0)
            rw [Real.rpow_add hpos, Real.rpow_one]
      _ ≤ ∑ m ∈ Box, (∏ p ∈ (r + 1).primesBelow, ef K m p) * Real.exp (80 * (K + 1 : ℝ)) := by
          refine Finset.sum_le_sum fun m hm => mul_le_mul_of_nonneg_left (hU_max m hm) (hU_nn m)
      _ = Real.exp (80 * (K + 1 : ℝ)) * ∑ m ∈ Box, ∏ p ∈ (r + 1).primesBelow, ef K m p := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m _ => by ring
      _ ≤ Real.exp (80 * (K + 1 : ℝ)) * (Real.exp 1 * ∏ i : Fin K, (M i : ℝ)) :=
          mul_le_mul_of_nonneg_left (small_primes_crt_avg hK N M hM_big) (Real.exp_pos _).le
  have hw0_nn : 0 ≤ 1 - 1 / (L : ℝ) := by
    have : 1 / (L : ℝ) ≤ 1 := by rw [div_le_one (by linarith only [hL_r])]; linarith only [hL_r]
    linarith only [this]
  have hw0_le1 : 1 - 1 / (L : ℝ) ≤ 1 := by
    linarith only [show (0 : ℝ) ≤ 1 / (L : ℝ) by positivity]
  have hP_nn : 0 ≤ ∏ i : Fin K, (M i : ℝ) := Finset.prod_nonneg (fun _ _ => by positivity)
  have hbase_ge1 : (1 : ℝ) ≤ Real.exp (80 * (K + 1 : ℝ)) * Real.exp 1 := by
    have h1 : (1 : ℝ) ≤ Real.exp (80 * (K + 1 : ℝ)) := Real.one_le_exp (by positivity)
    have h2 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    nlinarith only [h1, h2]
  calc (∑ m ∈ Box, (∏ p ∈ (r + 1).primesBelow, ef K m p) ^ (1 - 1 / (L : ℝ))⁻¹) ^
          (1 - 1 / (L : ℝ))
      ≤ (Real.exp (80 * (K + 1 : ℝ)) * (Real.exp 1 * ∏ i : Fin K, (M i : ℝ))) ^
          (1 - 1 / (L : ℝ)) :=
        Real.rpow_le_rpow (Finset.sum_nonneg (fun m _ => Real.rpow_nonneg (hU_nn m) _))
          hsum0 hw0_nn
    _ = (Real.exp (80 * (K + 1 : ℝ)) * Real.exp 1) ^ (1 - 1 / (L : ℝ)) *
          (∏ i : Fin K, (M i : ℝ)) ^ (1 - 1 / (L : ℝ)) := by
        rw [← mul_assoc, Real.mul_rpow (by positivity) hP_nn]
    _ ≤ (Real.exp (80 * (K + 1 : ℝ)) * Real.exp 1) ^ (1 : ℝ) *
          (∏ i : Fin K, (M i : ℝ)) ^ (1 - 1 / (L : ℝ)) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hbase_ge1 hw0_le1)
          (Real.rpow_nonneg hP_nn _)
    _ = Real.exp (80 * (K + 1 : ℝ)) * Real.exp 1 * (∏ i : Fin K, (M i : ℝ)) ^ (1 - 1 / (L : ℝ)) := by
        rw [Real.rpow_one]

lemma singular_avg_fac1 {K : ℕ} (hK : 3 ≤ K) (N M : Fin K → ℕ)
    (hN : ∀ i, N i ≤ 2 * (K + 1) * M i)
    (hMi_pos : ∀ i, 1 ≤ M i) :
    ∏ i : Fin K, (∑ m ∈ Fintype.piFinset (fun j : Fin K => Ioc (N j) (N j + M j)),
      (psiR (rParam K) (m i) ^ K) ^ (1 / (2 * (LParam K : ℝ) * (K : ℝ)))⁻¹) ^
      (1 / (2 * (LParam K : ℝ) * (K : ℝ))) ≤
      ((2 * (K + 1 : ℝ) + 1) * Real.exp 2) ^ (1 / (2 * (LParam K : ℝ))) *
        (∏ i : Fin K, (M i : ℝ)) ^ (1 / (2 * (LParam K : ℝ))) := by
  classical
  let r := rParam K
  let L := LParam K
  let Box := Fintype.piFinset (fun j : Fin K => Ioc (N j) (N j + M j))
  have hL4 : 4 ≤ L := by unfold L LParam; omega
  have h1coord : ∀ i : Fin K,
      ∑ m ∈ Box, (psiR r (m i) ^ K) ^ (1 / (2 * (L : ℝ) * (K : ℝ)))⁻¹ ≤
        ((2 * (K + 1 : ℝ) + 1) * Real.exp 2) * ∏ j : Fin K, (M j : ℝ) := by
    intro i
    have hexp : ∀ m ∈ Box, (psiR r (m i) ^ K) ^ (1 / (2 * (L : ℝ) * (K : ℝ)))⁻¹ =
        (psiR r (m i)) ^ (2 * L * K * K) := by
      intro m _
      rw [one_div, inv_inv, ← Real.rpow_natCast, ← Real.rpow_mul (psiR_pos r (m i)).le,
        ← Real.rpow_natCast]
      congr 1; push_cast; ring
    rw [Finset.sum_congr rfl hexp]
    let BoxOther := Fintype.piFinset (fun j : {j : Fin K // j ≠ i} => Ioc (N j.1) (N j.1 + M j.1))
    have hsplit_sum : ∑ m ∈ Box, (psiR r (m i)) ^ (2 * L * K * K) =
        (BoxOther.card : ℝ) * ∑ x ∈ Ioc (N i) (N i + M i), (psiR r x) ^ (2 * L * K * K) := by
      have hbij : ∑ m ∈ Box, (psiR r (m i)) ^ (2 * L * K * K) =
          ∑ p ∈ BoxOther ×ˢ Ioc (N i) (N i + M i), (psiR r p.2) ^ (2 * L * K * K) := by
        refine Finset.sum_bij (fun m _ => (fun j => m j.1, m i)) ?_ ?_ ?_ ?_
        · intro m hm
          simp only [Box, BoxOther, Finset.mem_product, Fintype.mem_piFinset] at hm ⊢
          exact ⟨fun j => hm j.1, hm i⟩
        · intro m₁ _ m₂ _ heq
          ext j
          by_cases hji : j = i
          · subst hji; exact congrArg Prod.snd heq
          · exact congrFun (congrArg Prod.fst heq) ⟨j, hji⟩
        · intro ⟨mO, x⟩ hp
          simp only [BoxOther, Finset.mem_product, Fintype.mem_piFinset] at hp
          let m : Fin K → ℕ := fun j => if hj : j = i then x else mO ⟨j, hj⟩
          refine ⟨m, ?_, ?_⟩
          · simp only [Box, Fintype.mem_piFinset]
            intro j; simp only [m]; split_ifs with hj
            · subst hj; exact hp.2
            · exact hp.1 ⟨j, hj⟩
          · exact Prod.ext (funext fun j => by simp [m, j.2]) (by simp [m])
        · intro _ _; rfl
      rw [hbij, Finset.sum_product]
      dsimp only
      rw [Finset.sum_const, nsmul_eq_mul]
    have hBoxOther_card : (BoxOther.card : ℝ) * (M i : ℝ) = ∏ j : Fin K, (M j : ℝ) := by
      have h1 : (BoxOther.card : ℝ) = ∏ j ∈ (Finset.univ : Finset (Fin K)).erase i, (M j : ℝ) := by
        simp only [BoxOther, Fintype.card_piFinset, Nat.card_Ioc, Nat.add_sub_cancel_left, Nat.cast_prod]
        exact (Finset.prod_subtype ((Finset.univ : Finset (Fin K)).erase i) (p := fun j => j ≠ i)
          (by simp) (fun j => (M j : ℝ))).symm
      rw [h1, mul_comm]
      exact Finset.mul_prod_erase Finset.univ (fun j => (M j : ℝ)) (Finset.mem_univ i)
    rw [hsplit_sum]
    have h2s_le_r : 2 * (2 * L * K * K) ≤ r := by
      change 2 * (2 * L * K * K) ≤ 4 * (K + 1) ^ 2 * L
      nlinarith only [hL4]
    have h2s_pos : 1 ≤ 2 * L * K * K :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega)) (by omega)
    have h2 := holder2_bound K r (2 * L * K * K) (N i) (M i) h2s_pos h2s_le_r (hMi_pos i) (hN i)
    calc (BoxOther.card : ℝ) * ∑ x ∈ Ioc (N i) (N i + M i), (psiR r x) ^ (2 * L * K * K)
        ≤ (BoxOther.card : ℝ) * ((2 * (K + 1 : ℝ) + 1) * Real.exp 2 * (M i : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
      _ = ((2 * (K + 1 : ℝ) + 1) * Real.exp 2) * ((BoxOther.card : ℝ) * (M i : ℝ)) := by ring
      _ = ((2 * (K + 1 : ℝ) + 1) * Real.exp 2) * ∏ j : Fin K, (M j : ℝ) := by rw [hBoxOther_card]
  calc ∏ i : Fin K, (∑ m ∈ Box, (psiR r (m i) ^ K) ^ (1 / (2 * (L : ℝ) * (K : ℝ)))⁻¹) ^
          (1 / (2 * (L : ℝ) * (K : ℝ)))
      ≤ ∏ _i : Fin K, (((2 * (K + 1 : ℝ) + 1) * Real.exp 2) * ∏ j : Fin K, (M j : ℝ)) ^
          (1 / (2 * (L : ℝ) * (K : ℝ))) := by
        refine Finset.prod_le_prod (fun i _ => Real.rpow_nonneg
          (Finset.sum_nonneg (fun m _ => Real.rpow_nonneg (pow_nonneg (psiR_pos r (m i)).le K) _)) _)
          (fun i _ => Real.rpow_le_rpow
            (Finset.sum_nonneg (fun m _ => Real.rpow_nonneg (pow_nonneg (psiR_pos r (m i)).le K) _))
            (h1coord i) (by positivity))
    _ = (((2 * (K + 1 : ℝ) + 1) * Real.exp 2) * ∏ j : Fin K, (M j : ℝ)) ^
          ((K : ℝ) * (1 / (2 * (L : ℝ) * (K : ℝ)))) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1; ring
    _ = ((2 * (K + 1 : ℝ) + 1) * Real.exp 2) ^ (1 / (2 * (L : ℝ))) *
          (∏ i : Fin K, (M i : ℝ)) ^ (1 / (2 * (L : ℝ))) := by
        have hKne : (K : ℝ) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
        have hex : (K : ℝ) * (1 / (2 * (L : ℝ) * (K : ℝ))) = 1 / (2 * (L : ℝ)) := by
          field_simp [hKne]
        rw [hex, Real.mul_rpow (by positivity) (Finset.prod_nonneg (fun _ _ => by positivity))]

lemma sum_piFinset_split_coord {K : ℕ} (N M : Fin K → ℕ) (l : Fin K) (f : (Fin K → ℕ) → ℝ) :
    ∑ m ∈ Fintype.piFinset (fun j : Fin K => Ioc (N j) (N j + M j)), f m =
      ∑ mO ∈ Fintype.piFinset (fun j : {j : Fin K // j ≠ l} => Ioc (N j.1) (N j.1 + M j.1)),
        ∑ x ∈ Ioc (N l) (N l + M l),
          f (Function.update (fun j => if hj : j = l then 0 else mO ⟨j, hj⟩) l x) := by
  classical
  let Box := Fintype.piFinset (fun j : Fin K => Ioc (N j) (N j + M j))
  let BoxOther := Fintype.piFinset (fun j : {j : Fin K // j ≠ l} => Ioc (N j.1) (N j.1 + M j.1))
  let g : ({j : Fin K // j ≠ l} → ℕ) × ℕ → ℝ :=
    fun p => f (Function.update (fun j => if hj : j = l then 0 else p.1 ⟨j, hj⟩) l p.2)
  change ∑ m ∈ Box, f m = ∑ mO ∈ BoxOther, ∑ x ∈ Ioc (N l) (N l + M l), g (mO, x)
  rw [← Finset.sum_product BoxOther (Ioc (N l) (N l + M l)) g]
  refine Finset.sum_bij (fun m _ => (fun j => m j.1, m l)) ?_ ?_ ?_ ?_
  · intro m hm
    simp only [Box, BoxOther, Finset.mem_product, Fintype.mem_piFinset] at hm ⊢
    exact ⟨fun j => hm j.1, hm l⟩
  · intro m₁ _ m₂ _ heq
    ext j
    by_cases hjl : j = l
    · subst hjl; exact congrArg Prod.snd heq
    · exact congrFun (congrArg Prod.fst heq) ⟨j, hjl⟩
  · intro ⟨mO, x⟩ hp
    simp only [BoxOther, Finset.mem_product, Fintype.mem_piFinset] at hp
    let m : Fin K → ℕ := fun j => if hj : j = l then x else mO ⟨j, hj⟩
    refine ⟨m, ?_, ?_⟩
    · simp only [Box, Fintype.mem_piFinset]
      intro j; simp only [m]; split_ifs with hj
      · subst hj; exact hp.2
      · exact hp.1 ⟨j, hj⟩
    · exact Prod.ext (funext fun j => by simp [m, j.2]) (by simp [m])
  · intro m _
    simp only [g]
    congr 1
    ext j
    by_cases hjl : j = l
    · subst hjl; simp
    · simp [hjl]

lemma singular_avg_fac2 {K : ℕ} (hK : 3 ≤ K) (N M : Fin K → ℕ)
    (hN : ∀ i, N i ≤ 2 * (K + 1) * M i)
    (hM_big : ∀ i, 2 ^ (10 ^ 6 * (K + 1) ^ 7) ≤ M i)
    (argMax : ℕ × ℕ → Fin K)
    (harg : ∀ q ∈ pairsK K, q.1 < (argMax q : ℕ) ∧ (argMax q : ℕ) < q.2 ∧
      ∀ u (hu : u < K), q.1 < u → u < q.2 → M ⟨u, hu⟩ ≤ M (argMax q)) :
    ∏ q : {q : ℕ × ℕ // q ∈ pairsK K},
      (∑ m ∈ Fintype.piFinset (fun j : Fin K => Ioc (N j) (N j + M j)),
        (psiR (rParam K) (Gprime (rParam K) K q.1.1 q.1.2 (argMax q.1) m)) ^
          (1 / (2 * ((pairsK K).card : ℝ) * (LParam K : ℝ)))⁻¹) ^
      (1 / (2 * ((pairsK K).card : ℝ) * (LParam K : ℝ))) ≤
      (Real.exp 2 + 1) ^ (1 / (2 * (LParam K : ℝ))) *
        (∏ i : Fin K, (M i : ℝ)) ^ (1 / (2 * (LParam K : ℝ))) := by
  classical
  let r := rParam K
  let L := LParam K
  let J := (pairsK K).card
  let Box := Fintype.piFinset (fun j : Fin K => Ioc (N j) (N j + M j))
  have hL4 : 4 ≤ L := by unfold L LParam; omega
  have hJ1 : 1 ≤ J := pairsK_card_pos hK
  have hJ2 : 2 * J ≤ (K + 1) ^ 2 := pairsK_card_le
  have h1pair : ∀ q : {q : ℕ × ℕ // q ∈ pairsK K},
      ∑ m ∈ Box, (psiR r (Gprime r K q.1.1 q.1.2 (argMax q.1) m)) ^
          (1 / (2 * (J : ℝ) * (L : ℝ)))⁻¹ ≤
        (Real.exp 2 + 1) * ∏ j : Fin K, (M j : ℝ) := by
    intro q
    let l := argMax q.1
    have hl_spec := harg q.1 q.2
    have hq_mem := q.2
    simp only [pairsK, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq_mem
    have hexp : ∀ m ∈ Box, (psiR r (Gprime r K q.1.1 q.1.2 l m)) ^
        (1 / (2 * (J : ℝ) * (L : ℝ)))⁻¹ =
        (psiR r (Gprime r K q.1.1 q.1.2 l m)) ^ (2 * J * L) := by
      intro m _
      rw [one_div, inv_inv, ← Real.rpow_natCast]
      congr 1; push_cast; ring
    rw [Finset.sum_congr rfl hexp]
    let BoxOther := Fintype.piFinset (fun j : {j : Fin K // j ≠ l} => Ioc (N j.1) (N j.1 + M j.1))
    have hbij := sum_piFinset_split_coord N M l
      (fun m => (psiR r (Gprime r K q.1.1 q.1.2 l m)) ^ (2 * J * L))
    rw [hbij]
    have hinner : ∀ mO ∈ BoxOther,
        ∑ x ∈ Ioc (N l) (N l + M l),
          (psiR r (Gprime r K q.1.1 q.1.2 l
            (Function.update (fun j => if hj : j = l then 0 else mO ⟨j, hj⟩) l x))) ^ (2 * J * L) ≤
          (Real.exp 2 + 1) * (M l : ℝ) := by
      intro mO hmO
      refine holder3_one_var hK hq_mem.2 (Nat.lt_succ_iff.mp hq_mem.1.2) l hl_spec.1 hl_spec.2.1
        N M hN hl_spec.2.2 (hM_big l) (by nlinarith only [hJ1, hL4])
        (by exact Nat.mul_le_mul_right L hJ2)
        (by change 2 * (2 * J * L) ≤ 4 * (K + 1) ^ 2 * L; nlinarith only [hJ2, hL4])
        (fun j => if hj : j = l then 0 else mO ⟨j, hj⟩) (fun i hi => by
          simp only [hi, dite_false]
          exact Fintype.mem_piFinset.mp hmO ⟨i, hi⟩)
    have hBoxOther_card : (BoxOther.card : ℝ) * (M l : ℝ) = ∏ j : Fin K, (M j : ℝ) := by
      have h1 : (BoxOther.card : ℝ) = ∏ j ∈ (Finset.univ : Finset (Fin K)).erase l, (M j : ℝ) := by
        simp only [BoxOther, Fintype.card_piFinset, Nat.card_Ioc, Nat.add_sub_cancel_left, Nat.cast_prod]
        exact (Finset.prod_subtype ((Finset.univ : Finset (Fin K)).erase l) (p := fun j => j ≠ l)
          (by simp) (fun j => (M j : ℝ))).symm
      rw [h1, mul_comm]
      exact Finset.mul_prod_erase Finset.univ (fun j => (M j : ℝ)) (Finset.mem_univ l)
    calc ∑ mO ∈ BoxOther, _
        ≤ ∑ _mO ∈ BoxOther, ((Real.exp 2 + 1) * (M l : ℝ)) := Finset.sum_le_sum hinner
      _ = (Real.exp 2 + 1) * ((BoxOther.card : ℝ) * (M l : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ = (Real.exp 2 + 1) * ∏ j : Fin K, (M j : ℝ) := by rw [hBoxOther_card]
  calc ∏ q : {q : ℕ × ℕ // q ∈ pairsK K},
          (∑ m ∈ Box, (psiR r (Gprime r K q.1.1 q.1.2 (argMax q.1) m)) ^
            (1 / (2 * (J : ℝ) * (L : ℝ)))⁻¹) ^ (1 / (2 * (J : ℝ) * (L : ℝ)))
      ≤ ∏ _q : {q : ℕ × ℕ // q ∈ pairsK K},
          ((Real.exp 2 + 1) * ∏ j : Fin K, (M j : ℝ)) ^ (1 / (2 * (J : ℝ) * (L : ℝ))) := by
        refine Finset.prod_le_prod (fun q _ => Real.rpow_nonneg
          (Finset.sum_nonneg (fun m _ => Real.rpow_nonneg (psiR_pos r _).le _)) _)
          (fun q _ => Real.rpow_le_rpow
            (Finset.sum_nonneg (fun m _ => Real.rpow_nonneg (psiR_pos r _).le _))
            (h1pair q) (by positivity))
    _ = ((Real.exp 2 + 1) * ∏ j : Fin K, (M j : ℝ)) ^ ((J : ℝ) * (1 / (2 * (J : ℝ) * (L : ℝ)))) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe,
          ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1; ring
    _ = (Real.exp 2 + 1) ^ (1 / (2 * (L : ℝ))) *
          (∏ i : Fin K, (M i : ℝ)) ^ (1 / (2 * (L : ℝ))) := by
        have hJne : (J : ℝ) ≠ 0 := by exact_mod_cast (show J ≠ 0 by omega)
        have hex : (J : ℝ) * (1 / (2 * (J : ℝ) * (L : ℝ))) = 1 / (2 * (L : ℝ)) := by
          field_simp [hJne]
        rw [hex, Real.mul_rpow (by positivity) (Finset.prod_nonneg (fun _ _ => by positivity))]

/- Main theorem of this file: `singular_avg` (FKL10 Lemma `singular`, `b = 0`) -/

theorem singular_avg {K : ℕ} (hK : 3 ≤ K) (N M : Fin K → ℕ)
    (hN2 : ∀ i, 2 ≤ N i) (hN : ∀ i, N i ≤ 2 * (K + 1) * M i)
    (hM_big : ∀ i, 2 ^ (10 ^ 6 * (K + 1) ^ 7) ≤ M i) :
    ∑ m ∈ Fintype.piFinset (fun i : Fin K => Ioc (N i) (N i + M i)), singSeries m ≤
      Real.exp (100 * (K + 1 : ℝ)) * ∏ i : Fin K, (M i : ℝ) := by
  let r := rParam K
  let L := LParam K
  let J := (pairsK K).card
  let Box := Fintype.piFinset (fun i : Fin K => Ioc (N i) (N i + M i))
  have hL4 : 4 ≤ L := by unfold L LParam; omega
  have hJ1 : 1 ≤ J := pairsK_card_pos hK
  have hMi_pos : ∀ i : Fin K, 1 ≤ M i := fun i => by
    have := hM_big i
    have h1 : 1 ≤ 2 ^ (10 ^ 6 * (K + 1) ^ 7) := Nat.one_le_two_pow
    omega
  have hex_argMax : ∀ q ∈ pairsK K, ∃ l : Fin K, q.1 < (l : ℕ) ∧ (l : ℕ) < q.2 ∧
      ∀ u (hu : u < K), q.1 < u → u < q.2 → M ⟨u, hu⟩ ≤ M l := by
    intro q hq
    simp only [pairsK, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq
    let S := (Finset.univ : Finset (Fin K)).filter (fun i : Fin K => q.1 < (i : ℕ) ∧ (i : ℕ) < q.2)
    have hSne : S.Nonempty :=
      ⟨⟨q.1 + 1, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.lt_succ_self _,
        show q.1 + 1 < q.2 by omega⟩⟩
    obtain ⟨l, hlS, hlmax⟩ := Finset.exists_max_image S M hSne
    have hl := (Finset.mem_filter.mp hlS).2
    refine ⟨l, hl.1, hl.2, fun u hu h1 h2 => hlmax ⟨u, hu⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩)⟩
  classical
  let argMax : ℕ × ℕ → Fin K := fun q =>
    if hq : q ∈ pairsK K then (hex_argMax q hq).choose else ⟨0, by omega⟩
  have harg : ∀ q ∈ pairsK K, q.1 < (argMax q : ℕ) ∧ (argMax q : ℕ) < q.2 ∧
      ∀ u (hu : u < K), q.1 < u → u < q.2 → M ⟨u, hu⟩ ≤ M (argMax q) := fun q hq => by
    simp only [argMax, dif_pos hq]
    exact (hex_argMax q hq).choose_spec
  let ι := Unit ⊕ Fin K ⊕ {q : ℕ × ℕ // q ∈ pairsK K}
  let w : ι → ℝ := fun idx => match idx with
    | Sum.inl () => 1 - 1 / (L : ℝ)
    | Sum.inr (Sum.inl _) => 1 / (2 * (L : ℝ) * (K : ℝ))
    | Sum.inr (Sum.inr _) => 1 / (2 * (J : ℝ) * (L : ℝ))
  let F : ι → (Fin K → ℕ) → ℝ := fun idx m => match idx with
    | Sum.inl () => ∏ p ∈ (r + 1).primesBelow, ef K m p
    | Sum.inr (Sum.inl i) => psiR r (m i) ^ K
    | Sum.inr (Sum.inr q) => psiR r (Gprime r K q.1.1 q.1.2 (argMax q.1) m)
  have hw_pos : ∀ idx ∈ (Finset.univ : Finset ι), 0 < w idx := by
    intro idx _
    rcases idx with ⟨⟩ | i | q
    · simp only [w]
      have hL_r : (4 : ℝ) ≤ L := by exact_mod_cast hL4
      have : 1 / (L : ℝ) < 1 := by rw [div_lt_one (by linarith only [hL_r])]; linarith only [hL_r]
      linarith only [this]
    · simp only [w]
      have : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
      have : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
      positivity
    · simp only [w]
      have : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
      have : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
      positivity
  have hw_sum : ∑ idx : ι, w idx = 1 := by
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_unique]
    simp only [w, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_coe, nsmul_eq_mul]
    have hLne : (L : ℝ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
    have hKne : (K : ℝ) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
    have hJne : (J : ℝ) ≠ 0 := by exact_mod_cast (show J ≠ 0 by omega)
    field_simp [hLne, hKne, hJne]
    ring
  have hF_nn : ∀ idx ∈ (Finset.univ : Finset ι), ∀ m ∈ Box, 0 ≤ F idx m := by
    intro idx _ m _
    rcases idx with ⟨⟩ | i | q
    · exact Finset.prod_nonneg (fun p hp => ef_nonneg m (Nat.prime_of_mem_primesBelow hp))
    · exact pow_nonneg (psiR_pos r (m i)).le K
    · exact (psiR_pos r _).le
  have hpoint : ∀ m ∈ Box, singSeries m ≤ ∏ idx : ι, F idx m := by
    intro m hm
    have hm1 : ∀ i, 1 ≤ m i := fun i => by
      have := Finset.mem_Ioc.mp (Fintype.mem_piFinset.mp hm i)
      have := hN2 i; omega
    have hpt := singSeries_pointwise_le hK m hm1 argMax (fun q hq => ⟨(harg q hq).1, (harg q hq).2.1⟩)
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_unique]
    simp only [F]
    rw [Finset.prod_coe_sort (pairsK K) (fun q => psiR r (Gprime r K q.1 q.2 (argMax q) m)),
      ← mul_assoc]
    exact hpt
  have hholder := holder_finset Box Finset.univ w F hw_pos hw_sum hF_nn
  have hfac0 := singular_avg_fac0 hK N M hM_big
  have hfac1 := singular_avg_fac1 hK N M hN hMi_pos
  have hfac2 := singular_avg_fac2 hK N M hN hM_big argMax harg
  have hM_prod_pos : 0 < ∏ i : Fin K, (M i : ℝ) :=
    Finset.prod_pos (fun i _ => by exact_mod_cast (hMi_pos i))
  have hcombine_M : (∏ i : Fin K, (M i : ℝ)) ^ (1 - 1 / (L : ℝ)) *
      (∏ i : Fin K, (M i : ℝ)) ^ (1 / (2 * (L : ℝ))) *
      (∏ i : Fin K, (M i : ℝ)) ^ (1 / (2 * (L : ℝ))) = ∏ i : Fin K, (M i : ℝ) := by
    rw [← Real.rpow_add hM_prod_pos, ← Real.rpow_add hM_prod_pos]
    have hLne : (L : ℝ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
    have hsum1 : (1 - 1 / (L : ℝ)) + 1 / (2 * (L : ℝ)) + 1 / (2 * (L : ℝ)) = 1 := by
      field_simp [hLne]; ring
    rw [hsum1, Real.rpow_one]
  have hconst_le : Real.exp (80 * (K + 1 : ℝ)) * Real.exp 1 *
      ((2 * (K + 1 : ℝ) + 1) * Real.exp 2) ^ (1 / (2 * (L : ℝ))) *
      (Real.exp 2 + 1) ^ (1 / (2 * (L : ℝ))) ≤ Real.exp (100 * (K + 1 : ℝ)) := by
    have hL_r : (4 : ℝ) ≤ L := by exact_mod_cast hL4
    have h12L : 1 / (2 * (L : ℝ)) ≤ 1 := by
      rw [div_le_one (by linarith only [hL_r])]; linarith only [hL_r]
    have hc1 : ((2 * (K + 1 : ℝ) + 1) * Real.exp 2) ^ (1 / (2 * (L : ℝ))) ≤
        Real.exp (3 * (K + 1 : ℝ)) := by
      have hbase : (2 * (K + 1 : ℝ) + 1) * Real.exp 2 ≤ Real.exp (3 * (K + 1 : ℝ)) := by
        have h1 : 2 * (K + 1 : ℝ) + 1 ≤ Real.exp (2 * (K + 1 : ℝ)) := by
          linarith only [Real.add_one_le_exp (2 * (K + 1 : ℝ))]
        have h2 : Real.exp 2 ≤ Real.exp (K + 1 : ℝ) := Real.exp_le_exp.mpr (by
          have : (4 : ℝ) ≤ K + 1 := by exact_mod_cast (show 4 ≤ K + 1 by omega)
          linarith only [this])
        calc (2 * (K + 1 : ℝ) + 1) * Real.exp 2
            ≤ Real.exp (2 * (K + 1 : ℝ)) * Real.exp (K + 1 : ℝ) :=
              mul_le_mul h1 h2 (Real.exp_pos _).le (Real.exp_pos _).le
          _ = Real.exp (3 * (K + 1 : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
      have hge1 : (1 : ℝ) ≤ (2 * (K + 1 : ℝ) + 1) * Real.exp 2 := by
        have : (1 : ℝ) ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
        nlinarith only [this, show (0 : ℝ) ≤ (K + 1 : ℝ) by positivity]
      calc ((2 * (K + 1 : ℝ) + 1) * Real.exp 2) ^ (1 / (2 * (L : ℝ)))
          ≤ ((2 * (K + 1 : ℝ) + 1) * Real.exp 2) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hge1 h12L
        _ = (2 * (K + 1 : ℝ) + 1) * Real.exp 2 := Real.rpow_one _
        _ ≤ Real.exp (3 * (K + 1 : ℝ)) := hbase
    have hc2 : (Real.exp 2 + 1) ^ (1 / (2 * (L : ℝ))) ≤ Real.exp 3 := by
      have hbase : Real.exp 2 + 1 ≤ Real.exp 3 := by
        have h1 : Real.exp 2 + 1 ≤ Real.exp 2 * 2 := by
          have : (1 : ℝ) ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
          linarith only [this]
        have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
        calc Real.exp 2 + 1 ≤ Real.exp 2 * 2 := h1
          _ ≤ Real.exp 2 * Real.exp 1 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
          _ = Real.exp 3 := by rw [← Real.exp_add]; norm_num
      calc (Real.exp 2 + 1) ^ (1 / (2 * (L : ℝ)))
          ≤ (Real.exp 2 + 1) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith only [Real.one_le_exp (show (0 : ℝ) ≤ 2 by norm_num)]) h12L
        _ = Real.exp 2 + 1 := Real.rpow_one _
        _ ≤ Real.exp 3 := hbase
    calc Real.exp (80 * (K + 1 : ℝ)) * Real.exp 1 *
          ((2 * (K + 1 : ℝ) + 1) * Real.exp 2) ^ (1 / (2 * (L : ℝ))) *
          (Real.exp 2 + 1) ^ (1 / (2 * (L : ℝ)))
        ≤ Real.exp (80 * (K + 1 : ℝ)) * Real.exp 1 *
            Real.exp (3 * (K + 1 : ℝ)) * Real.exp 3 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hc1 (by positivity)) hc2
            (by positivity) (by positivity)
      _ = Real.exp (83 * (K + 1 : ℝ) + 4) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (100 * (K + 1 : ℝ)) := by
          apply Real.exp_le_exp.mpr
          have : (4 : ℝ) ≤ K + 1 := by exact_mod_cast (show 4 ≤ K + 1 by omega)
          linarith only [this]
  calc ∑ m ∈ Box, singSeries m
      ≤ ∑ m ∈ Box, ∏ idx : ι, F idx m := Finset.sum_le_sum hpoint
    _ ≤ ∏ idx : ι, (∑ m ∈ Box, (F idx m) ^ (w idx)⁻¹) ^ (w idx) := hholder
    _ = ((∑ m ∈ Box, (F (Sum.inl ()) m) ^ (w (Sum.inl ()))⁻¹) ^ (w (Sum.inl ()))) *
        (∏ i : Fin K, (∑ m ∈ Box, (F (Sum.inr (Sum.inl i)) m) ^ (w (Sum.inr (Sum.inl i)))⁻¹) ^
          (w (Sum.inr (Sum.inl i)))) *
        (∏ q : {q : ℕ × ℕ // q ∈ pairsK K},
          (∑ m ∈ Box, (F (Sum.inr (Sum.inr q)) m) ^ (w (Sum.inr (Sum.inr q)))⁻¹) ^
            (w (Sum.inr (Sum.inr q)))) := by
        rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_unique, mul_assoc]
    _ ≤ (Real.exp (80 * (K + 1 : ℝ)) * Real.exp 1 * (∏ i : Fin K, (M i : ℝ)) ^ (1 - 1 / (L : ℝ))) *
        (((2 * (K + 1 : ℝ) + 1) * Real.exp 2) ^ (1 / (2 * (L : ℝ))) *
          (∏ i : Fin K, (M i : ℝ)) ^ (1 / (2 * (L : ℝ)))) *
        ((Real.exp 2 + 1) ^ (1 / (2 * (L : ℝ))) *
          (∏ i : Fin K, (M i : ℝ)) ^ (1 / (2 * (L : ℝ)))) := by
        dsimp only [F, w]
        have h1_nn : 0 ≤ ∏ i : Fin K,
            (∑ m ∈ Box, (psiR r (m i) ^ K) ^ (1 / (2 * (L : ℝ) * (K : ℝ)))⁻¹) ^
              (1 / (2 * (L : ℝ) * (K : ℝ))) :=
          Finset.prod_nonneg (fun i _ => Real.rpow_nonneg
            (Finset.sum_nonneg (fun m _ => Real.rpow_nonneg (pow_nonneg (psiR_pos r (m i)).le K) _)) _)
        have h2_nn : 0 ≤ ∏ q : {q : ℕ × ℕ // q ∈ pairsK K},
            (∑ m ∈ Box, (psiR r (Gprime r K q.1.1 q.1.2 (argMax q.1) m)) ^
              (1 / (2 * (J : ℝ) * (L : ℝ)))⁻¹) ^ (1 / (2 * (J : ℝ) * (L : ℝ))) :=
          Finset.prod_nonneg (fun q _ => Real.rpow_nonneg
            (Finset.sum_nonneg (fun m _ => Real.rpow_nonneg (psiR_pos r _).le _)) _)
        refine mul_le_mul (mul_le_mul hfac0 hfac1 h1_nn (by positivity)) hfac2 h2_nn (by positivity)
    _ = (Real.exp (80 * (K + 1 : ℝ)) * Real.exp 1 *
          ((2 * (K + 1 : ℝ) + 1) * Real.exp 2) ^ (1 / (2 * (L : ℝ))) *
          (Real.exp 2 + 1) ^ (1 / (2 * (L : ℝ)))) *
        ((∏ i : Fin K, (M i : ℝ)) ^ (1 - 1 / (L : ℝ)) *
          (∏ i : Fin K, (M i : ℝ)) ^ (1 / (2 * (L : ℝ))) *
          (∏ i : Fin K, (M i : ℝ)) ^ (1 / (2 * (L : ℝ)))) := by ring
    _ = (Real.exp (80 * (K + 1 : ℝ)) * Real.exp 1 *
          ((2 * (K + 1 : ℝ) + 1) * Real.exp 2) ^ (1 / (2 * (L : ℝ))) *
          (Real.exp 2 + 1) ^ (1 / (2 * (L : ℝ)))) *
        (∏ i : Fin K, (M i : ℝ)) := by rw [hcombine_M]
    _ ≤ Real.exp (100 * (K + 1 : ℝ)) * ∏ i : Fin K, (M i : ℝ) :=
        mul_le_mul_of_nonneg_right hconst_le hM_prod_pos.le

end

/- ==================== Section 5: CondensedChain ==================== -/
section
open scoped BigOperators
open Filter Finset Nat

/- Elementary helpers -/

lemma log_le_rpow_div_self {t β : ℝ} (ht : 0 < t) (hβ : 0 < β) :
    Real.log t ≤ t ^ β / β := by
  have h1 : Real.log (t ^ β) ≤ t ^ β - 1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos ht β)
  rw [Real.log_rpow ht] at h1
  rw [le_div_iff₀ hβ]
  linarith

lemma sum_piFinset_prod : ∀ {K : ℕ} (t : Fin K → Finset ℕ) (f : Fin K → ℕ → ℝ),
    ∑ m ∈ Fintype.piFinset t, ∏ i : Fin K, f i (m i) = ∏ i : Fin K, ∑ a ∈ t i, f i a := by
  intro K
  induction K with
  | zero =>
    intro t f
    have hcard : Fintype.piFinset t = {Fin.elim0} := by
      ext m; simp only [Fintype.mem_piFinset, Finset.mem_singleton]
      exact ⟨fun _ => funext fun i => i.elim0, fun _ i => i.elim0⟩
    rw [hcard, Finset.sum_singleton]; simp
  | succ K ih =>
    intro t f
    have hbij : ∑ m ∈ Fintype.piFinset t, ∏ i : Fin (K + 1), f i (m i) =
        ∑ p ∈ (t 0) ×ˢ Fintype.piFinset (fun i : Fin K => t i.succ),
          f 0 p.1 * ∏ i : Fin K, f i.succ (p.2 i) := by
      refine Finset.sum_bij (fun m _ => (m 0, fun i => m i.succ)) ?_ ?_ ?_ ?_
      · intro m hm
        simp only [Finset.mem_product, Fintype.mem_piFinset] at hm ⊢
        exact ⟨hm 0, fun i => hm i.succ⟩
      · intro m₁ _ m₂ _ heq
        ext i
        refine Fin.cases (congrArg Prod.fst heq) (fun k => congrFun (congrArg Prod.snd heq) k) i
      · intro ⟨a, m'⟩ hp
        simp only [Finset.mem_product, Fintype.mem_piFinset] at hp
        refine ⟨Fin.cons a m', ?_, ?_⟩
        · rw [Fintype.mem_piFinset]
          intro i; refine Fin.cases hp.1 (fun k => hp.2 k) i
        · simp
      · intro m _
        exact Fin.prod_univ_succ (fun i => f i (m i))
    rw [hbij, Finset.sum_product]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, ih (fun i => t i.succ) (fun i => f i.succ), Fin.prod_univ_succ]

lemma biUnion_Ico_eq_range_mul (j l a : ℕ) (hl : 1 ≤ l) (haj : a ≤ j) :
    (Ico a j).biUnion (fun b => Ico ((j - 1 - b) * l) ((j - b) * l)) = range ((j - a) * l) := by
  ext u
  simp only [Finset.mem_biUnion, Finset.mem_Ico, Finset.mem_range]
  constructor
  · rintro ⟨b, ⟨hab, _⟩, _, hub⟩
    have : (j - b) * l ≤ (j - a) * l := Nat.mul_le_mul_right l (by omega)
    omega
  · intro hu
    have hq_lt : u / l < j - a := (Nat.div_lt_iff_lt_mul (by omega)).mpr hu
    generalize hq_def : u / l = q at hq_lt
    refine ⟨j - 1 - q, ⟨by omega, by omega⟩, ?_, ?_⟩
    · have hsub : j - 1 - (j - 1 - q) = q := by omega
      rw [hsub, ← hq_def]; exact Nat.div_mul_le_self u l
    · have hsub : j - (j - 1 - q) = q + 1 := by omega
      rw [hsub, ← hq_def, Nat.add_mul, one_mul]
      exact Nat.lt_div_mul_add (a := u) (b := l) (by omega)

lemma pairwiseDisjoint_Ico_blocks (j l a : ℕ) :
    Set.PairwiseDisjoint (Ico a j : Set ℕ) (fun b => Ico ((j - 1 - b) * l) ((j - b) * l)) := by
  intro b₁ hb₁ b₂ hb₂ hne
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro u hu₁ hu₂
  have hb₁' := Finset.mem_Ico.mp (Finset.mem_coe.mp hb₁)
  have hb₂' := Finset.mem_Ico.mp (Finset.mem_coe.mp hb₂)
  rw [Finset.mem_Ico] at hu₁ hu₂
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have : (j - b₂) * l ≤ (j - 1 - b₁) * l := Nat.mul_le_mul_right l (by omega)
    omega
  · have : (j - b₁) * l ≤ (j - 1 - b₂) * l := Nat.mul_le_mul_right l (by omega)
    omega

/- Prime chains and conversion to reversed chainForm vectors -/

def IsPrimeChain (K : ℕ) (p : Fin (K + 1) → ℕ) : Prop :=
  (∀ i : Fin (K + 1), (p i).Prime) ∧
  ∀ i : Fin K, p i.succ ∣ p i.castSucc - 1

def HasPrimeChain (K : ℕ) (p0 : ℕ) (lb : ℝ) : Prop :=
  ∃ p : Fin (K + 1) → ℕ, IsPrimeChain K p ∧ p 0 = p0 ∧ lb ≤ (p (Fin.last K) : ℝ)

lemma isPrimeChain_strictAnti {K : ℕ} {p : Fin (K + 1) → ℕ} (hp : IsPrimeChain K p) :
    ∀ {a b : Fin (K + 1)}, a < b → p b < p a := by
  have hstep : ∀ i : Fin K, p i.succ < p i.castSucc := by
    intro i
    have hpr0 := hp.1 i.castSucc
    have hdvd := hp.2 i
    have hle : p i.succ ≤ p i.castSucc - 1 := Nat.le_of_dvd (by have := hpr0.two_le; omega) hdvd
    have := hpr0.two_le; omega
  intro a b hab
  have hnat : ∀ d : ℕ, ∀ (ha : (a : ℕ) + d < K + 1), 1 ≤ d →
      p ⟨(a : ℕ) + d, ha⟩ < p a := by
    intro d
    induction d with
    | zero => intro _ h; omega
    | succ d ih =>
      intro ha _
      by_cases hd0 : d = 0
      · subst hd0
        exact hstep ⟨(a : ℕ), by omega⟩
      · have hprev := ih (by omega) (by omega)
        have h1 := hstep ⟨(a : ℕ) + d, by omega⟩
        exact lt_trans h1 hprev
  have hdiff : (a : ℕ) + ((b : ℕ) - (a : ℕ)) = (b : ℕ) := by omega
  have h1 := hnat ((b : ℕ) - (a : ℕ)) (by omega) (by omega)
  convert h1 using 2
  exact Fin.ext hdiff.symm

lemma isPrimeChain_ge_last {K : ℕ} {p : Fin (K + 1) → ℕ} (hp : IsPrimeChain K p) (i : Fin (K + 1)) :
    p (Fin.last K) ≤ p i := by
  by_cases h : i = Fin.last K
  · subst h; exact le_rfl
  · exact (isPrimeChain_strictAnti hp (lt_of_le_of_ne (Fin.le_last i) h)).le

def chainMult {K : ℕ} (p : Fin (K + 1) → ℕ) : Fin K → ℕ :=
  fun t => (p ⟨K - 1 - (t : ℕ), by omega⟩ - 1) / p ⟨K - (t : ℕ), by omega⟩

lemma chainMult_ge_two {K : ℕ} {p : Fin (K + 1) → ℕ} (hp : IsPrimeChain K p)
    (hlast : 3 ≤ p (Fin.last K)) (t : Fin K) :
    2 ≤ chainMult p t := by
  unfold chainMult
  let i : Fin K := ⟨K - 1 - (t : ℕ), by omega⟩
  have hi_succ : i.succ = ⟨K - (t : ℕ), by omega⟩ := by ext; simp [i]; omega
  have hi_cast : i.castSucc = ⟨K - 1 - (t : ℕ), by omega⟩ := rfl
  have hdvd : p ⟨K - (t : ℕ), by omega⟩ ∣ p ⟨K - 1 - (t : ℕ), by omega⟩ - 1 := by
    rw [← hi_succ, ← hi_cast]; exact hp.2 i
  have hpr1 : (p ⟨K - (t : ℕ), by omega⟩).Prime := hp.1 _
  have hpr0 : (p ⟨K - 1 - (t : ℕ), by omega⟩).Prime := hp.1 _
  have hge3_1 : 3 ≤ p ⟨K - (t : ℕ), by omega⟩ :=
    le_trans hlast (isPrimeChain_ge_last hp _)
  have hge3_0 : 3 ≤ p ⟨K - 1 - (t : ℕ), by omega⟩ :=
    le_trans hlast (isPrimeChain_ge_last hp _)
  obtain ⟨c, hc⟩ := hdvd
  have hdiv : (p ⟨K - 1 - (t : ℕ), by omega⟩ - 1) / p ⟨K - (t : ℕ), by omega⟩ = c := by
    rw [hc, Nat.mul_div_cancel_left c hpr1.pos]
  rw [hdiv]
  by_contra hc2
  push Not at hc2
  interval_cases c
  · omega
  · have heq : p ⟨K - 1 - (t : ℕ), by omega⟩ = p ⟨K - (t : ℕ), by omega⟩ + 1 := by omega
    have hodd1 : p ⟨K - (t : ℕ), by omega⟩ % 2 = 1 :=
      Nat.Prime.eq_two_or_odd hpr1 |>.resolve_left (by omega)
    have hodd0 : p ⟨K - 1 - (t : ℕ), by omega⟩ % 2 = 1 :=
      Nat.Prime.eq_two_or_odd hpr0 |>.resolve_left (by omega)
    omega

lemma chainForm_chainMult {K : ℕ} {p : Fin (K + 1) → ℕ} (hp : IsPrimeChain K p) :
    ∀ t (ht : t ≤ K), chainForm (chainMult p) t (p (Fin.last K)) = p ⟨K - t, by omega⟩ := by
  intro t
  induction t with
  | zero =>
    intro _
    simp [chainForm, Fin.last]
  | succ t ih =>
    intro ht
    have htK : t < K := by omega
    rw [chainForm, dif_pos htK, ih (by omega)]
    unfold chainMult
    let i : Fin K := ⟨K - 1 - t, by omega⟩
    have hi_succ : i.succ = ⟨K - t, by omega⟩ := by ext; simp [i]; omega
    have hdvd : p ⟨K - t, by omega⟩ ∣ p ⟨K - 1 - t, by omega⟩ - 1 := by
      rw [← hi_succ]; exact hp.2 i
    have hmul : ((p ⟨K - 1 - t, by omega⟩ - 1) / p ⟨K - t, by omega⟩) * p ⟨K - t, by omega⟩ =
        p ⟨K - 1 - t, by omega⟩ - 1 := Nat.div_mul_cancel hdvd
    have hpos0 : 1 ≤ p ⟨K - 1 - t, by omega⟩ := (hp.1 _).one_le
    have heq_idx : (⟨K - 1 - t, by omega⟩ : Fin (K + 1)) = ⟨K - (t + 1), by omega⟩ := by
      ext; simp; omega
    rw [hmul, Nat.sub_add_cancel hpos0, heq_idx]

lemma chainMult_block_prod_le {K : ℕ} {p : Fin (K + 1) → ℕ} (hp : IsPrimeChain K p)
    {c : ℕ} (hc : c ≤ K) :
    (∏ u ∈ range (K - c), (if hlt : u < K then chainMult p ⟨u, hlt⟩ else 1)) * p (Fin.last K) ≤
      p ⟨c, by omega⟩ := by
  have h1 := chainForm_eq_mul_add_gForm (chainMult p) (Nat.zero_le (K - c)) (p (Fin.last K))
  rw [chainForm_chainMult hp (K - c) (by omega)] at h1
  have h0 : chainForm (chainMult p) 0 (p (Fin.last K)) = p (Fin.last K) := rfl
  rw [h0] at h1
  have hidx : (⟨K - (K - c), by omega⟩ : Fin (K + 1)) = ⟨c, by omega⟩ := by ext; simp; omega
  rw [hidx] at h1
  have hIco : Ico 0 (K - c) = range (K - c) := by ext; simp
  rw [hIco] at h1
  omega

lemma chainMult_full_prod_le {K : ℕ} {p : Fin (K + 1) → ℕ} (hp : IsPrimeChain K p) :
    (∏ i : Fin K, chainMult p i) * p (Fin.last K) ≤ p 0 := by
  have h := chainMult_block_prod_le hp (Nat.zero_le K)
  simp only [Nat.sub_zero] at h
  have hprod : ∏ i : Fin K, chainMult p i =
      ∏ u ∈ range K, (if hlt : u < K then chainMult p ⟨u, hlt⟩ else 1) := by
    have h1 := Fin.prod_univ_eq_prod_range (fun u => if hlt : u < K then chainMult p ⟨u, hlt⟩ else 1) K
    rw [← h1]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [i.2]
  rw [hprod]
  exact h

/- Parameters for FKL10 Theorem `condensed_chain` -/

noncomputable def etaFKL : ℝ := Real.exp (-120)

lemma etaFKL_pos : 0 < etaFKL := Real.exp_pos _

lemma etaFKL_le_one : etaFKL ≤ 1 := by
  unfold etaFKL; exact Real.exp_le_one_iff.mpr (by norm_num)

noncomputable def yExp (y : ℝ) (i : ℕ) : ℝ := y ^ ((i + 1 : ℝ) ^ (-etaFKL))

lemma yExp_zero (y : ℝ) : yExp y 0 = y := by
  unfold yExp
  have : ((0 : ℕ) + 1 : ℝ) ^ (-etaFKL) = 1 := by norm_num
  rw [this, Real.rpow_one]

lemma yExp_pos {y : ℝ} (hy : 0 < y) (i : ℕ) : 0 < yExp y i :=
  Real.rpow_pos_of_pos hy _

lemma log_yExp {y : ℝ} (hy : 0 < y) (i : ℕ) :
    Real.log (yExp y i) = (i + 1 : ℝ) ^ (-etaFKL) * Real.log y := by
  unfold yExp
  rw [Real.log_rpow hy]

noncomputable def C_cond : ℝ := 2 * (1600 * Real.exp 101 + 3)

/- Geometric grid `Hgrid` and `Mgrid` for box decomposition -/

def BK (K : ℕ) : ℕ := 2 ^ (10 ^ 6 * (K + 1) ^ 7)

def AK (K : ℕ) : ℕ := 2 * (K + 1) * BK K

noncomputable def Hgrid (K t : ℕ) : ℕ :=
  ⌊(AK K : ℝ) * (1 + 1 / ((K + 1 : ℕ) : ℝ)) ^ t⌋₊

noncomputable def Mgrid (K t : ℕ) : ℕ := Hgrid K (t + 1) - Hgrid K t

lemma BK_ge_two (K : ℕ) : 2 ≤ BK K := by
  unfold BK
  have hexp : 1 ≤ 10 ^ 6 * (K + 1) ^ 7 := Nat.mul_pos (by norm_num) (Nat.pow_pos (Nat.succ_pos K))
  calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ (10 ^ 6 * (K + 1) ^ 7) := Nat.pow_le_pow_right (by norm_num) hexp

lemma AK_ge_two (K : ℕ) : 2 ≤ AK K := by
  have hB := BK_ge_two K
  change 2 ≤ 2 * (K + 1) * BK K
  nlinarith only [hB]

lemma Hgrid_zero (K : ℕ) : Hgrid K 0 = AK K := by
  unfold Hgrid
  rw [pow_zero, mul_one, Nat.floor_natCast]

lemma AK_cast (K : ℕ) : (AK K : ℝ) = 2 * ((K + 1 : ℕ) : ℝ) * (BK K : ℝ) := by
  change ((2 * (K + 1) * BK K : ℕ) : ℝ) = _
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat]

lemma Mgrid_ge_big (K t : ℕ) : 2 ^ (10 ^ 6 * (K + 1) ^ 7) ≤ Mgrid K t := by
  change BK K ≤ Mgrid K t
  have hB2 : 2 ≤ BK K := BK_ge_two K
  let s : ℝ := 1 + 1 / ((K + 1 : ℕ) : ℝ)
  have hs1 : (1 : ℝ) ≤ s := by
    simp only [s]; linarith [div_nonneg zero_le_one (Nat.cast_nonneg (K + 1) : (0 : ℝ) ≤ ((K + 1 : ℕ) : ℝ))]
  have hpow1 : (1 : ℝ) ≤ s ^ t := one_le_pow₀ hs1
  have hdiff : (AK K : ℝ) * s ^ (t + 1) - (AK K : ℝ) * s ^ t = 2 * (BK K : ℝ) * s ^ t := by
    have hKne : ((K + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero K)
    rw [pow_succ, AK_cast]; simp only [s]; field_simp [hKne]; ring
  have hlt1 : (AK K : ℝ) * s ^ (t + 1) - 1 < (Hgrid K (t + 1) : ℝ) := by
    unfold Hgrid; linarith [Nat.lt_floor_add_one ((AK K : ℝ) * s ^ (t + 1))]
  have hle0 : (Hgrid K t : ℝ) ≤ (AK K : ℝ) * s ^ t :=
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith only [hs1]) _))
  have hB_r : (2 : ℝ) ≤ (BK K : ℝ) := by exact_mod_cast hB2
  have hge_r : (BK K : ℝ) ≤ (Hgrid K (t + 1) : ℝ) - (Hgrid K t : ℝ) := by
    nlinarith only [hdiff, hlt1, hle0, hpow1, hB_r]
  have hle_nat : Hgrid K t ≤ Hgrid K (t + 1) := by
    have : (Hgrid K t : ℝ) ≤ (Hgrid K (t + 1) : ℝ) := by linarith only [hge_r, hB_r]
    exact Nat.cast_le.mp this
  have hcast : ((Mgrid K t : ℕ) : ℝ) = (Hgrid K (t + 1) : ℝ) - (Hgrid K t : ℝ) := by
    unfold Mgrid; exact Nat.cast_sub hle_nat
  exact Nat.cast_le.mp (hcast.symm ▸ hge_r)

lemma Hgrid_strictMono (K : ℕ) : StrictMono (Hgrid K) := by
  refine strictMono_nat_of_lt_succ fun t => ?_
  have hM : BK K ≤ Mgrid K t := Mgrid_ge_big K t
  have hB2 : 2 ≤ BK K := BK_ge_two K
  unfold Mgrid at hM; omega

lemma Hgrid_ge_two (K t : ℕ) : 2 ≤ Hgrid K t := by
  have h0 : Hgrid K 0 ≤ Hgrid K t := (Hgrid_strictMono K).monotone (Nat.zero_le t)
  rw [Hgrid_zero] at h0
  exact le_trans (AK_ge_two K) h0

lemma Hgrid_ge_add (K t : ℕ) : AK K + t ≤ Hgrid K t := by
  induction t with
  | zero => rw [Hgrid_zero]; omega
  | succ t ih =>
    have hlt : Hgrid K t < Hgrid K (t + 1) := Hgrid_strictMono K (Nat.lt_succ_self t)
    omega

lemma Hgrid_le_mul_Mgrid (K t : ℕ) : Hgrid K t ≤ 2 * (K + 1) * Mgrid K t := by
  have hB2 : 2 ≤ BK K := BK_ge_two K
  let s : ℝ := 1 + 1 / ((K + 1 : ℕ) : ℝ)
  have hs1 : (1 : ℝ) ≤ s := by
    simp only [s]; linarith [div_nonneg zero_le_one (Nat.cast_nonneg (K + 1) : (0 : ℝ) ≤ ((K + 1 : ℕ) : ℝ))]
  have hpow1 : (1 : ℝ) ≤ s ^ t := one_le_pow₀ hs1
  have hdiff : (AK K : ℝ) * s ^ (t + 1) - (AK K : ℝ) * s ^ t = 2 * (BK K : ℝ) * s ^ t := by
    have hKne : ((K + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero K)
    rw [pow_succ, AK_cast]; simp only [s]; field_simp [hKne]; ring
  have hlt1 : (AK K : ℝ) * s ^ (t + 1) - 1 < (Hgrid K (t + 1) : ℝ) := by
    unfold Hgrid; linarith [Nat.lt_floor_add_one ((AK K : ℝ) * s ^ (t + 1))]
  have hle0 : (Hgrid K t : ℝ) ≤ (AK K : ℝ) * s ^ t :=
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith only [hs1]) _))
  have hB_r : (2 : ℝ) ≤ (BK K : ℝ) := by exact_mod_cast hB2
  have hM_r : (BK K : ℝ) * s ^ t ≤ (Mgrid K t : ℝ) := by
    have hle_nat : Hgrid K t ≤ Hgrid K (t + 1) := (Hgrid_strictMono K).monotone (Nat.le_succ t)
    unfold Mgrid
    rw [Nat.cast_sub hle_nat]
    nlinarith only [hdiff, hlt1, hle0, hpow1, hB_r]
  have hbound : (Hgrid K t : ℝ) ≤ 2 * ((K + 1 : ℕ) : ℝ) * (Mgrid K t : ℝ) := by
    have h1 : (AK K : ℝ) * s ^ t = 2 * ((K + 1 : ℕ) : ℝ) * ((BK K : ℝ) * s ^ t) := by
      rw [AK_cast]; ring
    have hK_nn : (0 : ℝ) ≤ 2 * ((K + 1 : ℕ) : ℝ) := mul_nonneg (by norm_num) (Nat.cast_nonneg _)
    nlinarith only [hle0, h1, hM_r, hK_nn]
  exact_mod_cast hbound

lemma Hgrid_succ_le_two_mul {K : ℕ} (hK : 1 ≤ K) (t : ℕ) : Hgrid K (t + 1) ≤ 2 * Hgrid K t := by
  let s : ℝ := 1 + 1 / ((K + 1 : ℕ) : ℝ)
  have hs1 : (1 : ℝ) ≤ s := by
    simp only [s]; linarith [show (0 : ℝ) ≤ 1 / ((K + 1 : ℕ) : ℝ) by positivity]
  have hs_le : s ≤ 3 / 2 := by
    have hK2 : (2 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ K + 1 by omega)
    have hinv : 1 / ((K + 1 : ℕ) : ℝ) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) hK2
    simp only [s]; linarith only [hinv]
  have hlt0 : (AK K : ℝ) * s ^ t < (Hgrid K t : ℝ) + 1 := by
    unfold Hgrid; exact Nat.lt_floor_add_one _
  have hle1 : (Hgrid K (t + 1) : ℝ) ≤ (AK K : ℝ) * s ^ (t + 1) :=
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith only [hs1]) _))
  have hH_ge4 : (4 : ℝ) ≤ (Hgrid K t : ℝ) := by
    have hAK4 : 4 ≤ AK K := by
      have hB := BK_ge_two K
      change 4 ≤ 2 * (K + 1) * BK K
      nlinarith only [hK, hB]
    have hle := (Hgrid_strictMono K).monotone (Nat.zero_le t)
    rw [Hgrid_zero] at hle
    exact_mod_cast (le_trans hAK4 hle)
  have hbound : (Hgrid K (t + 1) : ℝ) ≤ 2 * (Hgrid K t : ℝ) := by
    have hpow : (AK K : ℝ) * s ^ (t + 1) = s * ((AK K : ℝ) * s ^ t) := by rw [pow_succ]; ring
    have h0_nn : (0 : ℝ) ≤ (AK K : ℝ) * s ^ t :=
      mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith only [hs1]) _)
    have h2 : s * ((AK K : ℝ) * s ^ t) ≤ (3 / 2) * ((AK K : ℝ) * s ^ t) :=
      mul_le_mul_of_nonneg_right hs_le h0_nn
    linarith only [hle1, hpow, h2, hlt0, hH_ge4]
  exact_mod_cast hbound

lemma exists_Hgrid_interval {K m : ℕ} (hm : AK K < m) :
    ∃ t < m, m ∈ Ioc (Hgrid K t) (Hgrid K t + Mgrid K t) := by
  classical
  have hex : ∃ s : ℕ, m ≤ Hgrid K s := ⟨m, le_trans (by omega) (Hgrid_ge_add K m)⟩
  let s := Nat.find hex
  have hs_le : m ≤ Hgrid K s := Nat.find_spec hex
  have hs_pos : 1 ≤ s := by
    by_contra h0
    have hs0 : s = 0 := by omega
    rw [hs0, Hgrid_zero] at hs_le
    omega
  let t := s - 1
  have ht_lt : Hgrid K t < m := by
    have hnot := Nat.find_min hex (show t < s by omega)
    omega
  have ht_succ : t + 1 = s := by omega
  have ht_lt_m : t < m := by
    have := Hgrid_ge_add K t; omega
  refine ⟨t, ht_lt_m, Finset.mem_Ioc.mpr ⟨ht_lt, ?_⟩⟩
  have hle : Hgrid K t ≤ Hgrid K (t + 1) := (Hgrid_strictMono K).monotone (Nat.le_succ t)
  unfold Mgrid
  rw [Nat.add_sub_cancel' hle, ht_succ]
  exact hs_le

lemma sum_Mgrid_mul_Hgrid_rpow_le {K : ℕ} (hK : 1 ≤ K) (T : ℕ) {σ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) :
    ∑ t ∈ range T, (Mgrid K t : ℝ) / (Hgrid K t : ℝ) * (Hgrid K t : ℝ) ^ (-σ) ≤ 4 / σ := by
  have hstep : ∀ t ∈ range T,
      (Mgrid K t : ℝ) / (Hgrid K t : ℝ) * (Hgrid K t : ℝ) ^ (-σ) ≤
        4 * ∑ n ∈ Ioc (Hgrid K t) (Hgrid K (t + 1)), (n : ℝ) ^ (-1 - σ) := by
    intro t _
    have hH2 : 2 ≤ Hgrid K t := Hgrid_ge_two K t
    have hH_pos : (0 : ℝ) < (Hgrid K t : ℝ) := by exact_mod_cast (show 0 < Hgrid K t by omega)
    have hcard : ((Ioc (Hgrid K t) (Hgrid K (t + 1))).card : ℝ) = (Mgrid K t : ℝ) := by
      simp [Mgrid]
    have hterm : ∀ n ∈ Ioc (Hgrid K t) (Hgrid K (t + 1)),
        (Hgrid K t : ℝ) ^ (-1 - σ) ≤ 4 * (n : ℝ) ^ (-1 - σ) := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hn_le : (n : ℝ) ≤ 2 * (Hgrid K t : ℝ) := by
        exact_mod_cast (hn.2.trans (Hgrid_succ_le_two_mul hK t))
      have hpow_le : (2 * (Hgrid K t : ℝ)) ^ (-1 - σ) ≤ (n : ℝ) ^ (-1 - σ) :=
        Real.rpow_le_rpow_of_nonpos hn_pos hn_le (by linarith only [hσ0])
      rw [Real.mul_rpow (by norm_num) hH_pos.le] at hpow_le
      have h2pow : (1 / 4 : ℝ) ≤ (2 : ℝ) ^ (-1 - σ) := by
        calc (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℝ) := by
              rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by norm_num),
                Real.rpow_natCast]; norm_num
          _ ≤ (2 : ℝ) ^ (-1 - σ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hσ1])
      have hHpow_nn : 0 ≤ (Hgrid K t : ℝ) ^ (-1 - σ) := Real.rpow_nonneg hH_pos.le _
      nlinarith only [hpow_le, h2pow, hHpow_nn]
    have hlhs : (Mgrid K t : ℝ) / (Hgrid K t : ℝ) * (Hgrid K t : ℝ) ^ (-σ) =
        ∑ _n ∈ Ioc (Hgrid K t) (Hgrid K (t + 1)), (Hgrid K t : ℝ) ^ (-1 - σ) := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard, div_eq_mul_inv, mul_assoc,
        ← Real.rpow_neg_one (Hgrid K t : ℝ), ← Real.rpow_add hH_pos, ← sub_eq_add_neg]
    rw [hlhs, Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hdisj : Set.PairwiseDisjoint (range T : Set ℕ) (fun t => Ioc (Hgrid K t) (Hgrid K (t + 1))) := by
    intro a _ b _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro n ha hb
    rw [Finset.mem_Ioc] at ha hb
    rcases lt_or_gt_of_ne hne with hab | hba
    · have : Hgrid K (a + 1) ≤ Hgrid K b := (Hgrid_strictMono K).monotone (show a + 1 ≤ b by omega)
      omega
    · have : Hgrid K (b + 1) ≤ Hgrid K a := (Hgrid_strictMono K).monotone (show b + 1 ≤ a by omega)
      omega
  have hsub : (range T).biUnion (fun t => Ioc (Hgrid K t) (Hgrid K (t + 1))) ⊆ Icc 2 (Hgrid K T) := by
    intro n hn
    rw [Finset.mem_biUnion] at hn
    obtain ⟨t, ht, hn⟩ := hn
    rw [Finset.mem_range] at ht
    rw [Finset.mem_Ioc] at hn
    rw [Finset.mem_Icc]
    have h2 : 2 ≤ Hgrid K t := Hgrid_ge_two K t
    have hT : Hgrid K (t + 1) ≤ Hgrid K T := (Hgrid_strictMono K).monotone (show t + 1 ≤ T by omega)
    omega
  calc ∑ t ∈ range T, (Mgrid K t : ℝ) / (Hgrid K t : ℝ) * (Hgrid K t : ℝ) ^ (-σ)
      ≤ ∑ t ∈ range T, 4 * ∑ n ∈ Ioc (Hgrid K t) (Hgrid K (t + 1)), (n : ℝ) ^ (-1 - σ) :=
        Finset.sum_le_sum hstep
    _ = 4 * ∑ t ∈ range T, ∑ n ∈ Ioc (Hgrid K t) (Hgrid K (t + 1)), (n : ℝ) ^ (-1 - σ) :=
        (Finset.mul_sum _ _ _).symm
    _ = 4 * ∑ n ∈ (range T).biUnion (fun t => Ioc (Hgrid K t) (Hgrid K (t + 1))),
          (n : ℝ) ^ (-1 - σ) := by
        rw [Finset.sum_biUnion hdisj]
    _ ≤ 4 * ∑ n ∈ Icc 2 (Hgrid K T), (n : ℝ) ^ (-1 - σ) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) (by norm_num)
        intro n _ _; positivity
    _ ≤ 4 * (1 / σ) := mul_le_mul_of_nonneg_left (sum_inv_rpow_le (Hgrid K T) hσ0) (by norm_num)
    _ = 4 / σ := by ring

/- Rankin telescoping weights `Tweight` -/

noncomputable def Tweight (a : ℕ) : ℝ :=
  1 / ((a + 1 : ℝ) ^ (-etaFKL) - (a + 2 : ℝ) ^ (-etaFKL))

lemma diff_rpow_bounds (a : ℕ) :
    etaFKL * ((a + 2 : ℝ) ^ (-1 - etaFKL)) < (a + 1 : ℝ) ^ (-etaFKL) - (a + 2 : ℝ) ^ (-etaFKL) ∧
    (a + 1 : ℝ) ^ (-etaFKL) - (a + 2 : ℝ) ^ (-etaFKL) < etaFKL * ((a + 1 : ℝ) ^ (-1 - etaFKL)) := by
  have ha1 : (0 : ℝ) < (a + 1 : ℝ) := by positivity
  have hlt : (a + 1 : ℝ) < (a + 2 : ℝ) := by linarith
  have hdiff : ∀ x ∈ Set.Icc (a + 1 : ℝ) (a + 2 : ℝ),
      HasDerivAt (fun t : ℝ => t ^ (-etaFKL)) ((-etaFKL) * x ^ (-etaFKL - 1)) x := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le ha1 hx.1
    simpa using Real.hasDerivAt_rpow_const (p := -etaFKL) (Or.inl hxpos.ne')
  obtain ⟨c, hc, hcmvt⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => t ^ (-etaFKL))
    (fun x => (-etaFKL) * x ^ (-etaFKL - 1)) hlt
    (fun x hx => (hdiff x hx).continuousAt.continuousWithinAt)
    (fun x hx => hdiff x (Set.Ioo_subset_Icc_self hx))
  have hsub : (a + 2 : ℝ) - (a + 1 : ℝ) = 1 := by ring
  rw [hsub, div_one] at hcmvt
  have heq : (a + 1 : ℝ) ^ (-etaFKL) - (a + 2 : ℝ) ^ (-etaFKL) = etaFKL * c ^ (-1 - etaFKL) := by
    have hrew : -etaFKL - 1 = -1 - etaFKL := by ring
    rw [hrew] at hcmvt; linarith
  rw [heq]
  have hc_pos : 0 < c := lt_trans ha1 hc.1
  have hexp_neg : -1 - etaFKL < 0 := by linarith [etaFKL_pos]
  constructor
  · exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow_of_neg hc_pos hc.2 hexp_neg) etaFKL_pos
  · exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow_of_neg ha1 hc.1 hexp_neg) etaFKL_pos

lemma Tweight_pos (a : ℕ) : 0 < Tweight a := by
  unfold Tweight
  have h := (diff_rpow_bounds a).1
  have hpos : 0 < etaFKL * ((a + 2 : ℝ) ^ (-1 - etaFKL)) :=
    mul_pos etaFKL_pos (Real.rpow_pos_of_pos (by positivity) _)
  exact div_pos zero_lt_one (lt_trans hpos h)

lemma Tweight_strictMono : StrictMono Tweight := by
  refine strictMono_nat_of_lt_succ fun a => ?_
  unfold Tweight
  have h1 := (diff_rpow_bounds a).1
  have h2 := (diff_rpow_bounds (a + 1)).2
  have hpos2 : 0 < ((a + 1 : ℕ) + 1 : ℝ) ^ (-etaFKL) - ((a + 1 : ℕ) + 2 : ℝ) ^ (-etaFKL) := by
    have h := (diff_rpow_bounds (a + 1)).1
    have hp : 0 < etaFKL * (((a + 1 : ℕ) + 2 : ℝ) ^ (-1 - etaFKL)) :=
      mul_pos etaFKL_pos (Real.rpow_pos_of_pos (by positivity) _)
    exact lt_trans hp h
  have hcast : ((a + 1 : ℕ) + 1 : ℝ) = (a + 2 : ℝ) := by push_cast; ring
  rw [hcast] at h2
  have hlt_denom : ((a + 1 : ℕ) + 1 : ℝ) ^ (-etaFKL) - ((a + 1 : ℕ) + 2 : ℝ) ^ (-etaFKL) <
      (a + 1 : ℝ) ^ (-etaFKL) - (a + 2 : ℝ) ^ (-etaFKL) := by
    rw [hcast]; exact lt_trans h2 h1
  exact one_div_lt_one_div_of_lt hpos2 hlt_denom

lemma Tweight_ge (a : ℕ) : (a + 1 : ℝ) ^ (1 + etaFKL) / etaFKL ≤ Tweight a := by
  unfold Tweight
  have h2 := (diff_rpow_bounds a).2
  have hpos : 0 < (a + 1 : ℝ) ^ (-etaFKL) - (a + 2 : ℝ) ^ (-etaFKL) := by
    have h := (diff_rpow_bounds a).1
    have hp : 0 < etaFKL * ((a + 2 : ℝ) ^ (-1 - etaFKL)) :=
      mul_pos etaFKL_pos (Real.rpow_pos_of_pos (by positivity) _)
    exact lt_trans hp h
  have hinv_eq : (a + 1 : ℝ) ^ (1 + etaFKL) / etaFKL = 1 / (etaFKL * (a + 1 : ℝ) ^ (-1 - etaFKL)) := by
    have ha1 : (0 : ℝ) < (a + 1 : ℝ) := by positivity
    rw [show (-1 - etaFKL : ℝ) = -(1 + etaFKL) by ring, Real.rpow_neg ha1.le]
    field_simp [etaFKL_pos.ne', (Real.rpow_pos_of_pos ha1 (1 + etaFKL)).ne']
  rw [hinv_eq]
  exact one_div_le_one_div_of_le hpos h2.le

lemma telescoping_Tweight (j : ℕ) (x : ℕ → ℝ) (y : ℝ)
    (hbound : ∀ a ∈ range j,
      ∑ b ∈ Ico a j, x b ≤ ((a + 1 : ℝ) ^ (-etaFKL) - (j + 1 : ℝ) ^ (-etaFKL)) * Real.log y) :
    ∑ b ∈ range j, Tweight b * x b ≤ (j : ℝ) * Real.log y := by
  let delta : ℕ → ℝ := fun a => if a = 0 then Tweight 0 else Tweight a - Tweight (a - 1)
  have hdelta_pos : ∀ a, 0 < delta a := by
    intro a
    by_cases ha : a = 0
    · simp only [delta, ha, ↓reduceIte]; exact Tweight_pos 0
    · simp only [delta, ha, ↓reduceIte]
      have hlt : Tweight (a - 1) < Tweight a := Tweight_strictMono (by omega)
      linarith
  have hsum_delta : ∀ b : ℕ, ∑ a ∈ range (b + 1), delta a = Tweight b := by
    intro b
    induction b with
    | zero => simp [delta]
    | succ b ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [delta, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      ring
  have hswap : ∀ f : ℕ → ℝ,
      ∑ b ∈ range j, Tweight b * f b = ∑ a ∈ range j, delta a * ∑ b ∈ Ico a j, f b := by
    intro f
    have h1 : ∑ b ∈ range j, Tweight b * f b =
        ∑ b ∈ range j, ∑ a ∈ range (b + 1), delta a * f b := by
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← hsum_delta b, Finset.sum_mul]
    rw [h1]
    have h2 : ∑ b ∈ range j, ∑ a ∈ range (b + 1), delta a * f b =
        ∑ b ∈ range j, ∑ a ∈ range j, if a ≤ b then delta a * f b else 0 := by
      refine Finset.sum_congr rfl fun b hb => ?_
      rw [Finset.mem_range] at hb
      rw [← Finset.sum_filter]
      congr 1; ext a; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [h2, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mem_range] at ha
    rw [← Finset.sum_filter, Finset.mul_sum]
    congr 1; ext b; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  have hdiff_telesc : ∀ a ∈ range j,
      ∑ b ∈ Ico a j, ((b + 1 : ℝ) ^ (-etaFKL) - (b + 2 : ℝ) ^ (-etaFKL)) =
        (a + 1 : ℝ) ^ (-etaFKL) - (j + 1 : ℝ) ^ (-etaFKL) := by
    intro a ha
    rw [Finset.mem_range] at ha
    have hgen : ∀ n, a ≤ n →
        ∑ b ∈ Ico a n, ((b + 1 : ℝ) ^ (-etaFKL) - (b + 2 : ℝ) ^ (-etaFKL)) =
          (a + 1 : ℝ) ^ (-etaFKL) - (n + 1 : ℝ) ^ (-etaFKL) := by
      intro n han
      induction n, han using Nat.le_induction with
      | base => simp
      | succ k hak ih =>
        rw [Finset.sum_Ico_succ_top hak, ih]
        push_cast; ring
    exact hgen j ha.le
  calc ∑ b ∈ range j, Tweight b * x b
      = ∑ a ∈ range j, delta a * ∑ b ∈ Ico a j, x b := hswap x
    _ ≤ ∑ a ∈ range j, delta a * (((a + 1 : ℝ) ^ (-etaFKL) - (j + 1 : ℝ) ^ (-etaFKL)) * Real.log y) := by
        refine Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left (hbound a ha) (hdelta_pos a).le
    _ = (∑ a ∈ range j, delta a * ((a + 1 : ℝ) ^ (-etaFKL) - (j + 1 : ℝ) ^ (-etaFKL))) * Real.log y := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun a _ => by ring
    _ = (∑ a ∈ range j, delta a * ∑ b ∈ Ico a j, ((b + 1 : ℝ) ^ (-etaFKL) - (b + 2 : ℝ) ^ (-etaFKL))) *
          Real.log y := by
        congr 1; refine Finset.sum_congr rfl fun a ha => by rw [hdiff_telesc a ha]
    _ = (∑ b ∈ range j, Tweight b * ((b + 1 : ℝ) ^ (-etaFKL) - (b + 2 : ℝ) ^ (-etaFKL))) * Real.log y := by
        rw [← hswap]
    _ = (∑ _b ∈ range j, (1 : ℝ)) * Real.log y := by
        congr 1; refine Finset.sum_congr rfl fun b _ => ?_
        unfold Tweight
        have hpos : (b + 1 : ℝ) ^ (-etaFKL) - (b + 2 : ℝ) ^ (-etaFKL) ≠ 0 := by
          have h := (diff_rpow_bounds b).1
          have hp : 0 < etaFKL * ((b + 2 : ℝ) ^ (-1 - etaFKL)) :=
            mul_pos etaFKL_pos (Real.rpow_pos_of_pos (by positivity) _)
          exact (lt_trans hp h).ne'
        field_simp [hpos]
    _ = (j : ℝ) * Real.log y := by simp

/- Sieve error term bound shared by `Q_{j,1}` and `Q_{j,2}` -/

lemma sieve_error_sum_le (K j : ℕ) (hK : 1 ≤ K) :
    ∀ᶠ y : ℝ in atTop,
      ∑ m ∈ (Fintype.piFinset (fun _ : Fin K => Icc 2 ⌊y⌋₊)).filter
          (fun m => (∏ i : Fin K, (m i : ℝ)) ≤ y / yExp y j),
        2 * (y / ∏ i : Fin K, (m i : ℝ)) ^ ((4 : ℝ) / 5) ≤
        (1 / 2 : ℝ) ^ K * (y / Real.log y) := by
  let α : ℝ := (1 / 5 : ℝ) * (j + 1 : ℝ) ^ (-etaFKL)
  have hα_pos : 0 < α := mul_pos (by norm_num) (Real.rpow_pos_of_pos (by positivity) _)
  let β : ℝ := α / (2 * ((K + 1 : ℕ) : ℝ))
  have hβ_pos : 0 < β := div_pos hα_pos (by positivity)
  let C₀ : ℝ := 2 * (2 / β) ^ (K + 1) * (2 : ℝ) ^ K
  have hC₀_pos : 0 < C₀ := by positivity
  let Y₀ : ℝ := max (Real.exp 2) (C₀ ^ (2 / α))
  filter_upwards [Filter.eventually_ge_atTop Y₀] with y hy
  have hy_exp2 : Real.exp 2 ≤ y := le_trans (le_max_left _ _) hy
  have hy_pos : 0 < y := lt_of_lt_of_le (Real.exp_pos 2) hy_exp2
  have hlogy_ge2 : (2 : ℝ) ≤ Real.log y := by
    have := Real.log_le_log (Real.exp_pos 2) hy_exp2; rwa [Real.log_exp] at this
  have hlogy_pos : 0 < Real.log y := by linarith only [hlogy_ge2]
  have hy1 : 1 ≤ y := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hfloor_pos : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy1)
  let BoxAll := Fintype.piFinset (fun _ : Fin K => Icc 2 ⌊y⌋₊)
  have hterm : ∀ m ∈ BoxAll.filter (fun m => (∏ i : Fin K, (m i : ℝ)) ≤ y / yExp y j),
      2 * (y / ∏ i : Fin K, (m i : ℝ)) ^ ((4 : ℝ) / 5) ≤
        (2 * y / (yExp y j) ^ ((1 : ℝ) / 5)) * ∏ i : Fin K, (1 / (m i : ℝ)) := by
    intro m hm
    rw [Finset.mem_filter] at hm
    have hm_pos : ∀ i : Fin K, (0 : ℝ) < (m i : ℝ) := fun i => by
      have := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hm.1 i)
      exact_mod_cast (show 0 < m i by omega)
    have hP_pos : 0 < ∏ i : Fin K, (m i : ℝ) := Finset.prod_pos (fun i _ => hm_pos i)
    have hdiv_ge : yExp y j ≤ y / ∏ i : Fin K, (m i : ℝ) := by
      rw [le_div_iff₀ hP_pos]
      have h1 := (le_div_iff₀ (yExp_pos hy_pos j)).mp hm.2
      linarith only [h1]
    have h15_le : (yExp y j) ^ ((1 : ℝ) / 5) ≤ (y / ∏ i : Fin K, (m i : ℝ)) ^ ((1 : ℝ) / 5) :=
      Real.rpow_le_rpow (yExp_pos hy_pos j).le hdiv_ge (by norm_num)
    have hsplit : (y / ∏ i : Fin K, (m i : ℝ)) ^ ((4 : ℝ) / 5) =
        (y / ∏ i : Fin K, (m i : ℝ)) / (y / ∏ i : Fin K, (m i : ℝ)) ^ ((1 : ℝ) / 5) := by
      rw [eq_div_iff (Real.rpow_pos_of_pos (div_pos hy_pos hP_pos) _).ne',
        ← Real.rpow_add (div_pos hy_pos hP_pos)]
      norm_num
    rw [hsplit]
    have hprod_inv : ∏ i : Fin K, (1 / (m i : ℝ)) = 1 / ∏ i : Fin K, (m i : ℝ) := by
      rw [Finset.prod_div_distrib, Finset.prod_const_one]
    rw [hprod_inv]
    have h15_pos : 0 < (yExp y j) ^ ((1 : ℝ) / 5) := Real.rpow_pos_of_pos (yExp_pos hy_pos j) _
    calc 2 * ((y / ∏ i : Fin K, (m i : ℝ)) / (y / ∏ i : Fin K, (m i : ℝ)) ^ ((1 : ℝ) / 5))
        ≤ 2 * ((y / ∏ i : Fin K, (m i : ℝ)) / (yExp y j) ^ ((1 : ℝ) / 5)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (div_nonneg hy_pos.le hP_pos.le) h15_pos h15_le)
            (by norm_num)
      _ = (2 * y / (yExp y j) ^ ((1 : ℝ) / 5)) * (1 / ∏ i : Fin K, (m i : ℝ)) := by ring
  have hsum_inv : ∑ m ∈ BoxAll, ∏ i : Fin K, (1 / (m i : ℝ)) ≤ (2 * Real.log y) ^ K := by
    rw [sum_piFinset_prod (fun _ : Fin K => Icc 2 ⌊y⌋₊) (fun _ a => (1 / (a : ℝ)))]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => by positivity)) ?_ K
    have hsub : Icc 2 ⌊y⌋₊ ⊆ Icc 1 ⌊y⌋₊ := Finset.Icc_subset_Icc (by norm_num) le_rfl
    have h1 : ∑ a ∈ Icc 2 ⌊y⌋₊, (1 / (a : ℝ)) ≤ ∑ a ∈ Icc 1 ⌊y⌋₊, (1 / (a : ℝ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    have h2 : ∑ a ∈ Icc 1 ⌊y⌋₊, (1 / (a : ℝ)) ≤ Real.log (⌊y⌋₊ : ℝ) + 1 :=
      sum_inv_Icc_le_log_add_one_of_pos hfloor_pos
    have h3 : Real.log (⌊y⌋₊ : ℝ) ≤ Real.log y :=
      Real.log_le_log (by exact_mod_cast hfloor_pos) (Nat.floor_le hy_pos.le)
    linarith only [h1, h2, h3, hlogy_ge2]
  have hyExp_rpow : (yExp y j) ^ ((1 : ℝ) / 5) = y ^ α := by
    unfold yExp
    rw [← Real.rpow_mul hy_pos.le]
    congr 1; simp only [α]; ring
  have hlog_pow : (2 * Real.log y) ^ (K + 1) ≤ (2 / β) ^ (K + 1) * y ^ (α / 2) := by
    have h1 := log_le_rpow_div_self hy_pos hβ_pos
    have h2 : 2 * Real.log y ≤ (2 / β) * y ^ β := by
      have : 2 * (y ^ β / β) = (2 / β) * y ^ β := by ring
      linarith only [h1, this]
    calc (2 * Real.log y) ^ (K + 1)
        ≤ ((2 / β) * y ^ β) ^ (K + 1) := pow_le_pow_left₀ (by positivity) h2 (K + 1)
      _ = (2 / β) ^ (K + 1) * (y ^ β) ^ (K + 1) := mul_pow _ _ _
      _ = (2 / β) ^ (K + 1) * y ^ (α / 2) := by
          rw [← Real.rpow_natCast (y ^ β), ← Real.rpow_mul hy_pos.le]
          congr 2; simp only [β]
          have hKne : ((K + 1 : ℕ) : ℝ) ≠ 0 := by positivity
          field_simp [hKne]
  have hy_alpha2 : C₀ ≤ y ^ (α / 2) := by
    have h1 : C₀ ^ (2 / α) ≤ y := le_trans (le_max_right _ _) hy
    have h2 := Real.rpow_le_rpow (by positivity) h1 (show (0 : ℝ) ≤ α / 2 by positivity)
    rw [← Real.rpow_mul hC₀_pos.le] at h2
    have hexp : (2 / α) * (α / 2) = 1 := by field_simp [hα_pos.ne']
    rwa [hexp, Real.rpow_one] at h2
  calc ∑ m ∈ BoxAll.filter (fun m => (∏ i : Fin K, (m i : ℝ)) ≤ y / yExp y j),
        2 * (y / ∏ i : Fin K, (m i : ℝ)) ^ ((4 : ℝ) / 5)
      ≤ ∑ m ∈ BoxAll.filter (fun m => (∏ i : Fin K, (m i : ℝ)) ≤ y / yExp y j),
          (2 * y / (yExp y j) ^ ((1 : ℝ) / 5)) * ∏ i : Fin K, (1 / (m i : ℝ)) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ m ∈ BoxAll, (2 * y / (yExp y j) ^ ((1 : ℝ) / 5)) * ∏ i : Fin K, (1 / (m i : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by
          exact mul_nonneg (div_nonneg (by positivity) (Real.rpow_nonneg (yExp_pos hy_pos j).le _))
            (Finset.prod_nonneg (fun _ _ => by positivity)))
    _ = (2 * y / y ^ α) * ∑ m ∈ BoxAll, ∏ i : Fin K, (1 / (m i : ℝ)) := by
        rw [← Finset.mul_sum, hyExp_rpow]
    _ ≤ (2 * y / y ^ α) * (2 * Real.log y) ^ K :=
        mul_le_mul_of_nonneg_left hsum_inv (div_nonneg (by positivity) (Real.rpow_nonneg hy_pos.le α))
    _ ≤ (1 / 2 : ℝ) ^ K * (y / Real.log y) := by
        have hya_split : y ^ α = y ^ (α / 2) * y ^ (α / 2) := by
          rw [← Real.rpow_add hy_pos]; congr 1; ring
        have hmul_log : (2 * Real.log y) ^ K * Real.log y ≤ (2 * Real.log y) ^ (K + 1) := by
          rw [pow_succ]; nlinarith only [show (0 : ℝ) ≤ (2 * Real.log y) ^ K by positivity, hlogy_pos]
        rw [div_mul_eq_mul_div, ← mul_div_assoc, div_le_div_iff₀ (Real.rpow_pos_of_pos hy_pos α) hlogy_pos]
        have hprod1 : 2 * y * (2 * Real.log y) ^ K * Real.log y ≤
            2 * y * ((2 / β) ^ (K + 1) * y ^ (α / 2)) := by
          have : (2 * Real.log y) ^ K * Real.log y ≤ (2 / β) ^ (K + 1) * y ^ (α / 2) :=
            hmul_log.trans hlog_pow
          nlinarith only [this, hy_pos]
        have hprod2 : 2 * y * ((2 / β) ^ (K + 1) * y ^ (α / 2)) ≤
            (1 / 2 : ℝ) ^ K * y * y ^ α := by
          rw [hya_split]
          have h2K : (1 / 2 : ℝ) ^ K * (2 : ℝ) ^ K = 1 := by rw [← mul_pow]; norm_num
          have hCeq : 2 * (2 / β) ^ (K + 1) = (1 / 2 : ℝ) ^ K * C₀ := by
            simp only [C₀]; rw [show (1 / 2 : ℝ) ^ K * (2 * (2 / β) ^ (K + 1) * 2 ^ K) =
              ((1 / 2 : ℝ) ^ K * 2 ^ K) * (2 * (2 / β) ^ (K + 1)) by ring, h2K, one_mul]
          calc 2 * y * ((2 / β) ^ (K + 1) * y ^ (α / 2))
              = ((1 / 2 : ℝ) ^ K * C₀) * y * y ^ (α / 2) := by rw [← hCeq]; ring
            _ = (1 / 2 : ℝ) ^ K * y * (C₀ * y ^ (α / 2)) := by ring
            _ ≤ (1 / 2 : ℝ) ^ K * y * (y ^ (α / 2) * y ^ (α / 2)) := by gcongr
        linarith only [hprod1, hprod2]

/- Bound on `Q_{j,1}`: chains with at least one small multiplier `m_i ≤ AK K` -/

open Classical in
lemma bound_Qj1 (j l : ℕ) (hj : 1 ≤ j) (hl : 4 ≤ l) :
    ∀ᶠ y : ℝ in atTop,
      (((Icc 1 ⌊y⌋₊).filter (fun p0 =>
        ∃ p : Fin (j * l + 1) → ℕ, IsPrimeChain (j * l) p ∧ p 0 = p0 ∧
          yExp y j ≤ (p (Fin.last (j * l)) : ℝ) ∧
          ∃ i : Fin (j * l), chainMult p i ≤ AK (j * l))).card : ℝ) ≤
        2 * (1 / 2 : ℝ) ^ (j * l) * (y / Real.log y) := by
  let K := j * l
  have hK4 : 4 ≤ K := by show 4 ≤ j * l; nlinarith only [hj, hl]
  obtain ⟨X₀, hX₀4, hsieve⟩ := sieve_upper_bound K
  let αj : ℝ := (j + 1 : ℝ) ^ (-etaFKL)
  have hαj_pos : 0 < αj := Real.rpow_pos_of_pos (by positivity) _
  let C_sieve : ℝ := 4 * (400 * (K + 1 : ℝ)) ^ (K + 1) * ((j + 1 : ℝ) ^ etaFKL) ^ (K + 1)
  let C_comb : ℝ := C_sieve * (Real.exp 36) ^ K * (K : ℝ) * (AK K : ℝ) * (2 : ℝ) ^ (K - 1) * (2 : ℝ) ^ K
  have hAK_pos : (0 : ℝ) < (AK K : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) (AK_ge_two K))
  have hC_sieve_pos : 0 < C_sieve := by positivity
  have hC_comb_pos : 0 < C_comb := by
    have hK_pos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
    exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos hC_sieve_pos (pow_pos (Real.exp_pos 36) K)) hK_pos)
      hAK_pos) (pow_pos (by norm_num) _)) (pow_pos (by norm_num) _)
  let β_ll : ℝ := 1 / (32 * (K : ℝ))
  have hβ_ll_pos : 0 < β_ll := by positivity
  let C_ll : ℝ := (2 * (K + 1 : ℝ) ^ 3 + 6) / β_ll
  have hC_ll_pos : 0 < C_ll := by positivity
  let Y_log : ℝ := max (Real.exp 4) (Real.exp ((C_comb * C_ll ^ (16 * K)) ^ 2))
  let Y_sieve : ℝ := (max X₀ 4 + 2) ^ (1 / αj)
  let Y_min : ℝ := max (max Y_log Y_sieve) (Real.exp (4 / αj))
  filter_upwards [sieve_error_sum_le K j (by omega), Filter.eventually_ge_atTop Y_min] with y herr hy
  have hy_Ylog : Y_log ≤ y := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hy)
  have hy_Ysieve : Y_sieve ≤ y := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hy)
  have hy_exp4 : Real.exp 4 ≤ y := le_trans (le_max_left _ _) hy_Ylog
  have hy_pos : 0 < y := lt_of_lt_of_le (Real.exp_pos 4) hy_exp4
  have hlogy_ge4 : (4 : ℝ) ≤ Real.log y := by
    have := Real.log_le_log (Real.exp_pos 4) hy_exp4; rwa [Real.log_exp] at this
  have hlogy_pos : 0 < Real.log y := by linarith only [hlogy_ge4]
  have hy_ge_exp4α : Real.exp (4 / αj) ≤ y := le_trans (le_max_right _ _) hy
  have hlogy_ge4α : 4 / αj ≤ Real.log y := by
    have := Real.log_le_log (Real.exp_pos _) hy_ge_exp4α; rwa [Real.log_exp] at this
  have hyExp_ge : max X₀ 4 + 2 ≤ yExp y j := by
    have h1 := Real.rpow_le_rpow (by positivity) hy_Ysieve hαj_pos.le
    rw [← Real.rpow_mul (by positivity)] at h1
    have hexp : (1 / αj) * αj = 1 := by field_simp [hαj_pos.ne']
    rw [hexp, Real.rpow_one] at h1
    exact h1
  have hyExp_ge3 : (3 : ℝ) ≤ yExp y j := by linarith only [hyExp_ge, le_max_right X₀ 4]
  have hy2 : 2 ≤ y := by linarith only [hy_exp4, Real.add_one_le_exp (4 : ℝ)]
  have hfloor_pos : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by norm_num; linarith only [hy2])
  let BoxAll := Fintype.piFinset (fun _ : Fin K => Icc 2 ⌊y⌋₊)
  let V₁ := BoxAll.filter (fun m =>
    (∏ i : Fin K, (m i : ℝ)) ≤ y / yExp y j ∧ ∃ i : Fin K, m i ≤ AK K)
  let Q₁ := (Icc 1 ⌊y⌋₊).filter (fun p0 =>
    ∃ p : Fin (K + 1) → ℕ, IsPrimeChain K p ∧ p 0 = p0 ∧
      yExp y j ≤ (p (Fin.last K) : ℝ) ∧ ∃ i : Fin K, chainMult p i ≤ AK K)
  have hcover : Q₁ ⊆ V₁.biUnion (fun m =>
      ((Icc 1 ⌊y / ∏ i : Fin K, (m i : ℝ)⌋₊).filter
        (fun n => ∀ t ∈ range (K + 1), (chainForm m t n).Prime)).image
        (fun n => chainForm m K n)) := by
    intro p0 hp0
    rw [Finset.mem_filter, Finset.mem_Icc] at hp0
    obtain ⟨⟨_, hp0_le⟩, p, hp_ch, hp0_eq, hlast_ge, hex_small⟩ := hp0
    let m := chainMult p
    have hlast3 : 3 ≤ p (Fin.last K) := by
      have : (3 : ℝ) ≤ (p (Fin.last K) : ℝ) := le_trans hyExp_ge3 hlast_ge
      exact_mod_cast this
    have hm2 : ∀ i : Fin K, 2 ≤ m i := fun i => chainMult_ge_two hp_ch hlast3 i
    have hprod_mul : (∏ i : Fin K, (m i : ℝ)) * (p (Fin.last K) : ℝ) ≤ y := by
      have hcast : (∏ i : Fin K, (m i : ℝ)) * (p (Fin.last K) : ℝ) ≤ (p 0 : ℝ) := by
        exact_mod_cast chainMult_full_prod_le hp_ch
      have hp0_y : (p 0 : ℝ) ≤ y := by
        rw [hp0_eq]; exact le_trans (by exact_mod_cast hp0_le) (Nat.floor_le hy_pos.le)
      exact hcast.trans hp0_y
    have hprod_le : (∏ i : Fin K, (m i : ℝ)) ≤ y / yExp y j := by
      rw [le_div_iff₀ (yExp_pos hy_pos j)]
      exact (mul_le_mul_of_nonneg_left hlast_ge
        (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))).trans hprod_mul
    have hm_le_y : ∀ i : Fin K, m i ≤ ⌊y⌋₊ := fun i => by
      have h1 : m i ≤ ∏ u : Fin K, m u := by
        have hpos : ∀ u : Fin K, 1 ≤ m u := fun u => by have := hm2 u; omega
        calc m i = m i * 1 := (mul_one _).symm
          _ ≤ m i * ∏ u ∈ (Finset.univ : Finset (Fin K)).erase i, m u :=
              Nat.mul_le_mul_left _ (Finset.one_le_prod' fun u _ => hpos u)
          _ = ∏ u : Fin K, m u := Finset.mul_prod_erase _ _ (Finset.mem_univ i)
      have h2 : (m i : ℝ) ≤ y := by
        have hge1 : (1 : ℝ) ≤ yExp y j := by linarith only [hyExp_ge3]
        have h3 : (∏ u : Fin K, (m u : ℝ)) ≤ y :=
          hprod_le.trans (by rw [div_le_iff₀ (yExp_pos hy_pos j)]; nlinarith only [hy_pos, hge1])
        exact le_trans (by exact_mod_cast h1) h3
      exact Nat.le_floor h2
    rw [Finset.mem_biUnion]
    refine ⟨m, Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun i =>
      Finset.mem_Icc.mpr ⟨hm2 i, hm_le_y i⟩), hprod_le, hex_small⟩, ?_⟩
    rw [Finset.mem_image]
    refine ⟨p (Fin.last K), ?_, ?_⟩
    · simp only [Finset.mem_filter]
      refine ⟨Finset.mem_Icc.mpr ⟨by omega, ?_⟩, ?_⟩
      · apply Nat.le_floor
        have hP_pos : 0 < ∏ i : Fin K, (m i : ℝ) :=
          Finset.prod_pos (fun i _ => by exact_mod_cast (show 0 < m i by have := hm2 i; omega))
        rw [le_div_iff₀ hP_pos]; linarith only [hprod_mul]
      · intro t ht
        rw [Finset.mem_range] at ht
        rw [chainForm_chainMult hp_ch t (by omega)]
        exact hp_ch.1 _
    · rw [chainForm_chainMult hp_ch K le_rfl]
      have : (⟨K - K, by omega⟩ : Fin (K + 1)) = 0 := by ext; simp
      rw [this, hp0_eq]
  have hcard_le : (Q₁.card : ℝ) ≤
      ∑ m ∈ V₁, (((Icc 1 ⌊y / ∏ i : Fin K, (m i : ℝ)⌋₊).filter
        (fun n => ∀ t ∈ range (K + 1), (chainForm m t n).Prime)).card : ℝ) := by
    have hnat : Q₁.card ≤ ∑ m ∈ V₁,
        ((Icc 1 ⌊y / ∏ i : Fin K, (m i : ℝ)⌋₊).filter
          (fun n => ∀ t ∈ range (K + 1), (chainForm m t n).Prime)).card := by
      calc Q₁.card
          ≤ (V₁.biUnion (fun m =>
              ((Icc 1 ⌊y / ∏ i : Fin K, (m i : ℝ)⌋₊).filter
                (fun n => ∀ t ∈ range (K + 1), (chainForm m t n).Prime)).image
                (fun n => chainForm m K n))).card := Finset.card_le_card hcover
        _ ≤ ∑ m ∈ V₁, (((Icc 1 ⌊y / ∏ i : Fin K, (m i : ℝ)⌋₊).filter
              (fun n => ∀ t ∈ range (K + 1), (chainForm m t n).Prime)).image
              (fun n => chainForm m K n)).card := Finset.card_biUnion_le
        _ ≤ ∑ m ∈ V₁, ((Icc 1 ⌊y / ∏ i : Fin K, (m i : ℝ)⌋₊).filter
              (fun n => ∀ t ∈ range (K + 1), (chainForm m t n).Prime)).card :=
            Finset.sum_le_sum fun _ _ => Finset.card_image_le
    exact_mod_cast hnat
  let S_max : ℝ :=
    (Real.exp (16 * Real.log (Real.log ((K + 1 : ℝ) ^ 3 * Real.log (2 * y) + 2) + 2) + 36)) ^ K
  have hterm_sieve : ∀ m ∈ V₁,
      (((Icc 1 ⌊y / ∏ i : Fin K, (m i : ℝ)⌋₊).filter
        (fun n => ∀ t ∈ range (K + 1), (chainForm m t n).Prime)).card : ℝ) ≤
        C_sieve * S_max * (y / (Real.log y) ^ (K + 1)) * ∏ i : Fin K, (1 / (m i : ℝ)) +
          2 * (y / ∏ i : Fin K, (m i : ℝ)) ^ ((4 : ℝ) / 5) := by
    intro m hm
    rw [Finset.mem_filter] at hm
    have hm1 : ∀ i : Fin K, 1 ≤ m i := fun i => by
      have := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hm.1 i); omega
    have hP_pos : 0 < ∏ i : Fin K, (m i : ℝ) :=
      Finset.prod_pos (fun i _ => by exact_mod_cast (hm1 i))
    let Xm : ℕ := ⌊y / ∏ i : Fin K, (m i : ℝ)⌋₊
    have hdiv_ge : yExp y j ≤ y / ∏ i : Fin K, (m i : ℝ) := by
      rw [le_div_iff₀ hP_pos]
      have h1 := (le_div_iff₀ (yExp_pos hy_pos j)).mp hm.2.1
      linarith only [h1]
    have hXm_ge : max X₀ 4 + 1 ≤ (Xm : ℝ) := by
      have h1 := Nat.lt_floor_add_one (y / ∏ i : Fin K, (m i : ℝ))
      linarith only [hyExp_ge, hdiv_ge, h1]
    have hXm_ge_X0 : X₀ ≤ (Xm : ℝ) := le_trans (le_max_left _ _) (by linarith only [hXm_ge])
    have hXm_le_div : (Xm : ℝ) ≤ y / ∏ i : Fin K, (m i : ℝ) :=
      Nat.floor_le (div_nonneg hy_pos.le hP_pos.le)
    have hXm_ge_half : (1 / 2) * yExp y j ≤ (Xm : ℝ) := by
      have h1 := Nat.lt_floor_add_one (y / ∏ i : Fin K, (m i : ℝ))
      linarith only [hyExp_ge3, hdiv_ge, h1]
    have hlogXm_ge : (1 / 2) * αj * Real.log y ≤ Real.log (Xm : ℝ) := by
      have h1 := Real.log_le_log (mul_pos (by norm_num) (yExp_pos hy_pos j)) hXm_ge_half
      rw [Real.log_mul (by norm_num) (yExp_pos hy_pos j).ne', log_yExp hy_pos j, one_div, Real.log_inv] at h1
      have h2 := Real.log_two_lt_d9
      have h3 : (4 : ℝ) ≤ αj * Real.log y := by
        have := (div_le_iff₀ hαj_pos).mp hlogy_ge4α; linarith only [this]
      linarith only [h1, h2, h3]
    have hS_le : singSeries m ≤ S_max := by
      have hprod_le_y : (∏ i : Fin K, (m i : ℝ)) ≤ y := by
        have hge1 : (1 : ℝ) ≤ yExp y j := by linarith only [hyExp_ge3]
        exact hm.2.1.trans (by rw [div_le_iff₀ (yExp_pos hy_pos j)]; nlinarith only [hy_pos, hge1])
      exact singSeries_upper m hm1 hy2 hprod_le_y
    have hs : (((Icc 1 Xm).filter (fun n => ∀ t ∈ range (K + 1), (chainForm m t n).Prime)).card : ℝ) ≤
        4 * (200 * (K + 1 : ℝ)) ^ (K + 1) * singSeries m * Xm / (Real.log Xm) ^ (K + 1) +
          2 * (Xm : ℝ) ^ ((4 : ℝ) / 5) := by
      convert hsieve Xm hXm_ge_X0 m hm1 using 2
    have herr_m : 2 * (Xm : ℝ) ^ ((4 : ℝ) / 5) ≤ 2 * (y / ∏ i : Fin K, (m i : ℝ)) ^ ((4 : ℝ) / 5) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hXm_le_div (by norm_num)) (by norm_num)
    have hmain_m : 4 * (200 * (K + 1 : ℝ)) ^ (K + 1) * singSeries m * Xm / (Real.log Xm) ^ (K + 1) ≤
        C_sieve * S_max * (y / (Real.log y) ^ (K + 1)) * ∏ i : Fin K, (1 / (m i : ℝ)) := by
      have hprod_inv : ∏ i : Fin K, (1 / (m i : ℝ)) = 1 / ∏ i : Fin K, (m i : ℝ) := by
        rw [Finset.prod_div_distrib, Finset.prod_const_one]
      have hαj_inv : αj⁻¹ = (j + 1 : ℝ) ^ etaFKL := by
        have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        simp only [αj, Real.rpow_neg (show (0 : ℝ) ≤ (j + 1 : ℝ) by linarith only [hj0]), inv_inv]
      have hCeq : 4 * (200 * (K + 1 : ℝ)) ^ (K + 1) / ((1 / 2 : ℝ) * αj) ^ (K + 1) = C_sieve := by
        simp only [C_sieve, ← hαj_inv]
        have h1 : (200 * (K + 1 : ℝ)) / (1 / 2 : ℝ) = 400 * (K + 1 : ℝ) := by ring
        rw [mul_pow (1 / 2 : ℝ) αj, ← div_div, mul_div_assoc, ← div_pow, h1, div_eq_mul_inv, ← inv_pow]
      have hnum : 4 * (200 * (K + 1 : ℝ)) ^ (K + 1) * singSeries m * Xm ≤
          4 * (200 * (K + 1 : ℝ)) ^ (K + 1) * S_max * (y / ∏ i : Fin K, (m i : ℝ)) := by
        have hS_nn : 0 ≤ singSeries m := singSeries_nonneg m
        have hXm_nn : (0 : ℝ) ≤ Xm := Nat.cast_nonneg _
        have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
        have hc_nn : (0 : ℝ) ≤ 4 * (200 * (K + 1 : ℝ)) ^ (K + 1) :=
          mul_nonneg (by norm_num) (pow_nonneg (mul_nonneg (by norm_num) (by linarith only [hK0])) _)
        have h1 : 4 * (200 * (K + 1 : ℝ)) ^ (K + 1) * singSeries m ≤
            4 * (200 * (K + 1 : ℝ)) ^ (K + 1) * S_max := mul_le_mul_of_nonneg_left hS_le hc_nn
        exact mul_le_mul h1 hXm_le_div hXm_nn (mul_nonneg hc_nn (hS_nn.trans hS_le))
      have hden_pos : 0 < ((1 / 2) * αj * Real.log y) ^ (K + 1) :=
        pow_pos (mul_pos (mul_pos (by norm_num) hαj_pos) hlogy_pos) (K + 1)
      have hden : ((1 / 2) * αj * Real.log y) ^ (K + 1) ≤ (Real.log Xm) ^ (K + 1) :=
        pow_le_pow_left₀ (mul_nonneg (mul_nonneg (by norm_num) hαj_pos.le) hlogy_pos.le) hlogXm_ge (K + 1)
      have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
      have hnum_nn : 0 ≤ 4 * (200 * (K + 1 : ℝ)) ^ (K + 1) * S_max * (y / ∏ i : Fin K, (m i : ℝ)) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
          (pow_nonneg (mul_nonneg (by norm_num) (by linarith only [hK0])) _))
          (pow_nonneg (Real.exp_pos _).le _)) (div_nonneg hy_pos.le hP_pos.le)
      calc 4 * (200 * (K + 1 : ℝ)) ^ (K + 1) * singSeries m * Xm / (Real.log Xm) ^ (K + 1)
          ≤ 4 * (200 * (K + 1 : ℝ)) ^ (K + 1) * S_max * (y / ∏ i : Fin K, (m i : ℝ)) /
              ((1 / 2) * αj * Real.log y) ^ (K + 1) :=
            div_le_div₀ hnum_nn hnum hden_pos hden
        _ = (4 * (200 * (K + 1 : ℝ)) ^ (K + 1) / ((1 / 2) * αj) ^ (K + 1)) *
              S_max * (y / (Real.log y) ^ (K + 1)) * (1 / ∏ i : Fin K, (m i : ℝ)) := by
            rw [mul_pow]; ring
        _ = C_sieve * S_max * (y / (Real.log y) ^ (K + 1)) * ∏ i : Fin K, (1 / (m i : ℝ)) := by
            rw [hCeq, hprod_inv]
    linarith only [hs, herr_m, hmain_m]
  have hsum_V1 : ∑ m ∈ V₁, ∏ i : Fin K, (1 / (m i : ℝ)) ≤
      (K : ℝ) * (AK K : ℝ) * (2 * Real.log y) ^ (K - 1) := by
    have hV1_sub : V₁ ⊆ (Finset.univ : Finset (Fin K)).biUnion
        (fun i₀ => BoxAll.filter (fun m => m i₀ ≤ AK K)) := by
      intro m hm
      rw [Finset.mem_filter] at hm
      obtain ⟨i₀, hi₀⟩ := hm.2.2
      exact Finset.mem_biUnion.mpr ⟨i₀, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hm.1, hi₀⟩⟩
    have h1coord : ∀ i₀ : Fin K,
        ∑ m ∈ BoxAll.filter (fun m => m i₀ ≤ AK K), ∏ i : Fin K, (1 / (m i : ℝ)) ≤
          (AK K : ℝ) * (2 * Real.log y) ^ (K - 1) := by
      intro i₀
      have hbox_eq : BoxAll.filter (fun m => m i₀ ≤ AK K) =
          Fintype.piFinset (fun i : Fin K => if i = i₀ then Icc 2 (min (AK K) ⌊y⌋₊) else Icc 2 ⌊y⌋₊) := by
        ext m
        simp only [BoxAll, Finset.mem_filter, Fintype.mem_piFinset]
        constructor
        · rintro ⟨hm, hle⟩ i
          split_ifs with hi
          · subst hi
            have hm' := Finset.mem_Icc.mp (hm i)
            exact Finset.mem_Icc.mpr ⟨hm'.1, le_min hle hm'.2⟩
          · exact hm i
        · intro h
          refine ⟨fun i => ?_, ?_⟩
          · have hi := h i; split_ifs at hi
            · have hi' := Finset.mem_Icc.mp hi
              exact Finset.mem_Icc.mpr ⟨hi'.1, le_trans hi'.2 (min_le_right _ _)⟩
            · exact hi
          · have hi := h i₀; simp only [↓reduceIte, Finset.mem_Icc] at hi
            exact le_trans hi.2 (min_le_left _ _)
      rw [hbox_eq, sum_piFinset_prod _ (fun _ a => (1 / (a : ℝ)))]
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
      simp only [↓reduceIte]
      have hsmall : ∑ a ∈ Icc 2 (min (AK K) ⌊y⌋₊), (1 / (a : ℝ)) ≤ (AK K : ℝ) := by
        calc ∑ a ∈ Icc 2 (min (AK K) ⌊y⌋₊), (1 / (a : ℝ))
            ≤ ∑ _a ∈ Icc 2 (min (AK K) ⌊y⌋₊), (1 : ℝ) := by
              refine Finset.sum_le_sum fun a ha => ?_
              rw [Finset.mem_Icc] at ha
              rw [div_le_one (by exact_mod_cast (show 0 < a by omega))]
              exact_mod_cast (show 1 ≤ a by omega)
          _ = ((Icc 2 (min (AK K) ⌊y⌋₊)).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          _ ≤ (AK K : ℝ) := by
              have hc : (Icc 2 (min (AK K) ⌊y⌋₊)).card ≤ AK K := by
                rw [Nat.card_Icc]; omega
              exact_mod_cast hc
      have hother : ∏ i ∈ (Finset.univ : Finset (Fin K)).erase i₀,
            ∑ a ∈ (if i = i₀ then Icc 2 (min (AK K) ⌊y⌋₊) else Icc 2 ⌊y⌋₊), (1 / (a : ℝ)) ≤
          (2 * Real.log y) ^ (K - 1) := by
        have hcongr : ∏ i ∈ (Finset.univ : Finset (Fin K)).erase i₀,
              ∑ a ∈ (if i = i₀ then Icc 2 (min (AK K) ⌊y⌋₊) else Icc 2 ⌊y⌋₊), (1 / (a : ℝ)) =
            ∏ _i ∈ (Finset.univ : Finset (Fin K)).erase i₀,
              ∑ a ∈ Icc 2 ⌊y⌋₊, (1 / (a : ℝ)) := by
          refine Finset.prod_congr rfl fun i hi => ?_
          rw [if_neg (Finset.ne_of_mem_erase hi)]
        rw [hcongr, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i₀),
          Finset.card_univ, Fintype.card_fin]
        refine pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => div_nonneg zero_le_one (Nat.cast_nonneg _))) ?_ (K - 1)
        have hsub : Icc 2 ⌊y⌋₊ ⊆ Icc 1 ⌊y⌋₊ := Finset.Icc_subset_Icc (by norm_num) le_rfl
        have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun a : ℕ => (1 / (a : ℝ)))
          (fun _ _ _ => div_nonneg zero_le_one (Nat.cast_nonneg _))
        have h2 := sum_inv_Icc_le_log_add_one_of_pos hfloor_pos
        have h3 : Real.log (⌊y⌋₊ : ℝ) ≤ Real.log y :=
          Real.log_le_log (by exact_mod_cast hfloor_pos) (Nat.floor_le hy_pos.le)
        linarith only [h1, h2, h3, hlogy_ge4]
      exact mul_le_mul hsmall hother
        (Finset.prod_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => div_nonneg zero_le_one (Nat.cast_nonneg _))))
        (Nat.cast_nonneg _)
    calc ∑ m ∈ V₁, ∏ i : Fin K, (1 / (m i : ℝ))
        ≤ ∑ m ∈ (Finset.univ : Finset (Fin K)).biUnion (fun i₀ => BoxAll.filter (fun m => m i₀ ≤ AK K)),
            ∏ i : Fin K, (1 / (m i : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hV1_sub (fun _ _ _ =>
            Finset.prod_nonneg (fun _ _ => div_nonneg zero_le_one (Nat.cast_nonneg _)))
      _ ≤ ∑ i₀ : Fin K, ∑ m ∈ BoxAll.filter (fun m => m i₀ ≤ AK K), ∏ i : Fin K, (1 / (m i : ℝ)) :=
          sum_biUnion_le_sum _ _ _ (fun _ =>
            Finset.prod_nonneg (fun _ _ => div_nonneg zero_le_one (Nat.cast_nonneg _)))
      _ ≤ ∑ _i₀ : Fin K, ((AK K : ℝ) * (2 * Real.log y) ^ (K - 1)) := Finset.sum_le_sum (fun i₀ _ => h1coord i₀)
      _ = (K : ℝ) * (AK K : ℝ) * (2 * Real.log y) ^ (K - 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hSmax_le : S_max ≤ (Real.exp 36) ^ K * C_ll ^ (16 * K) * (Real.log y) ^ ((1 : ℝ) / 2) := by
    let u : ℝ := (K + 1 : ℝ) ^ 3 * Real.log (2 * y) + 2
    have hu_pos : 0 < u := by
      have h1 : (0 : ℝ) < Real.log (2 * y) := Real.log_pos (by linarith only [hy2])
      positivity
    have hu_le : u ≤ (2 * (K + 1 : ℝ) ^ 3 + 2) * Real.log y := by
      have hlog2y : Real.log (2 * y) ≤ 2 * Real.log y := by
        rw [Real.log_mul (by norm_num) hy_pos.ne']
        have := Real.log_two_lt_d9; linarith only [this, hlogy_ge4]
      have hK3_nn : (0 : ℝ) ≤ (K + 1 : ℝ) ^ 3 := by positivity
      simp only [u]
      nlinarith only [hlog2y, hK3_nn, hlogy_ge4]
    have hlog_u_le : Real.log u + 2 ≤ C_ll * (Real.log y) ^ β_ll := by
      have h1 : Real.log u ≤ Real.log ((2 * (K + 1 : ℝ) ^ 3 + 2) * Real.log y) :=
        Real.log_le_log hu_pos hu_le
      have h2 : Real.log ((2 * (K + 1 : ℝ) ^ 3 + 2) * Real.log y) =
          Real.log (2 * (K + 1 : ℝ) ^ 3 + 2) + Real.log (Real.log y) :=
        Real.log_mul (by positivity) hlogy_pos.ne'
      have h3 : Real.log (2 * (K + 1 : ℝ) ^ 3 + 2) ≤ 2 * (K + 1 : ℝ) ^ 3 + 2 := by
        linarith only [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * (K + 1 : ℝ) ^ 3 + 2 by positivity)]
      have h4 : Real.log (Real.log y) ≤ (Real.log y) ^ β_ll / β_ll :=
        log_le_rpow_div_self hlogy_pos hβ_ll_pos
      have hrpow_ge1 : (1 : ℝ) ≤ (Real.log y) ^ β_ll :=
        Real.one_le_rpow (by linarith only [hlogy_ge4]) hβ_ll_pos.le
      have hβ_le1 : β_ll ≤ 1 := by
        simp only [β_ll]; rw [div_le_one (by positivity)]
        have : (4 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK4
        linarith only [this]
      have hinv_ge1 : (1 : ℝ) ≤ 1 / β_ll := by rw [one_le_div hβ_ll_pos]; exact hβ_le1
      have hdiv_ge : (2 * (K + 1 : ℝ) ^ 3 + 4) ≤ ((2 * (K + 1 : ℝ) ^ 3 + 5) / β_ll) * (Real.log y) ^ β_ll := by
        have hA : (2 * (K + 1 : ℝ) ^ 3 + 4) ≤ (2 * (K + 1 : ℝ) ^ 3 + 5) * (1 / β_ll) := by
          nlinarith only [hinv_ge1, show (0 : ℝ) ≤ (K + 1 : ℝ) ^ 3 by positivity]
        rw [mul_one_div] at hA
        have hB : 0 ≤ (2 * (K + 1 : ℝ) ^ 3 + 5) / β_ll := by positivity
        nlinarith only [hA, hrpow_ge1, hB]
      have hCll_eq : C_ll = (2 * (K + 1 : ℝ) ^ 3 + 5) / β_ll + 1 / β_ll := by
        simp only [C_ll]; ring
      rw [hCll_eq, add_mul, one_div_mul_eq_div]
      linarith only [h1, h2, h3, h4, hdiv_ge]
    have hpos_lu2 : 0 < Real.log u + 2 := by
      have hu1 : 1 ≤ u := by
        have h1 : (0 : ℝ) < Real.log (2 * y) := Real.log_pos (by linarith only [hy2])
        simp only [u]; nlinarith only [h1, show (0 : ℝ) ≤ (K + 1 : ℝ) ^ 3 by positivity]
      linarith only [Real.log_nonneg hu1]
    have hS_rew : S_max = (Real.exp 36) ^ K * (Real.log u + 2) ^ (16 * K) := by
      simp only [S_max, u]
      have h1 : Real.exp (16 * Real.log (Real.log u + 2) + 36) =
          Real.exp 36 * (Real.log u + 2) ^ (16 : ℕ) := by
        rw [Real.exp_add, mul_comm (Real.exp _), ← Real.rpow_natCast,
          Real.rpow_def_of_pos hpos_lu2]
        congr 2; push_cast; ring
      rw [h1, mul_pow, ← pow_mul]
    rw [hS_rew]
    calc (Real.exp 36) ^ K * (Real.log u + 2) ^ (16 * K)
        ≤ (Real.exp 36) ^ K * (C_ll * (Real.log y) ^ β_ll) ^ (16 * K) := by gcongr
      _ = (Real.exp 36) ^ K * C_ll ^ (16 * K) * ((Real.log y) ^ β_ll) ^ (16 * K) := by
          rw [mul_pow]; ring
      _ = (Real.exp 36) ^ K * C_ll ^ (16 * K) * (Real.log y) ^ ((1 : ℝ) / 2) := by
          rw [← Real.rpow_natCast ((Real.log y) ^ β_ll), ← Real.rpow_mul hlogy_pos.le]
          congr 2
          simp only [β_ll]
          have hKne : (K : ℝ) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
          push_cast; field_simp [hKne]; ring
  have hmain_bound : C_sieve * S_max * (y / (Real.log y) ^ (K + 1)) *
      ((K : ℝ) * (AK K : ℝ) * (2 * Real.log y) ^ (K - 1)) ≤
      (1 / 2 : ℝ) ^ K * (y / Real.log y) := by
    have hlog_ge_sq : (C_comb * C_ll ^ (16 * K)) ^ 2 ≤ Real.log y := by
      have h1 : Real.exp ((C_comb * C_ll ^ (16 * K)) ^ 2) ≤ y := le_trans (le_max_right _ _) hy_Ylog
      have h2 := Real.log_le_log (Real.exp_pos _) h1
      rwa [Real.log_exp] at h2
    have hsqrt_ge : C_comb * C_ll ^ (16 * K) ≤ (Real.log y) ^ ((1 : ℝ) / 2) := by
      have hbase_nn : 0 ≤ C_comb * C_ll ^ (16 * K) := mul_nonneg hC_comb_pos.le (pow_nonneg hC_ll_pos.le _)
      have h1 := Real.rpow_le_rpow (pow_nonneg hbase_nn 2) hlog_ge_sq (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      rw [← Real.rpow_natCast (C_comb * C_ll ^ (16 * K)), ← Real.rpow_mul hbase_nn] at h1
      norm_num at h1
      exact h1
    have hpow_cancel : (2 * Real.log y) ^ (K - 1) / (Real.log y) ^ (K + 1) =
        (2 : ℝ) ^ (K - 1) / (Real.log y) ^ 2 := by
      rw [mul_pow, show K + 1 = (K - 1) + 2 by omega, pow_add]
      have hne : (Real.log y) ^ (K - 1) ≠ 0 := pow_ne_zero _ hlogy_pos.ne'
      field_simp [hne]
    have h2K : (1 / 2 : ℝ) ^ K * (2 : ℝ) ^ K = 1 := by rw [← mul_pow]; norm_num
    have hrpow2 : (Real.log y) ^ ((1 : ℝ) / 2) * (Real.log y) ^ ((1 : ℝ) / 2) = Real.log y := by
      rw [← Real.rpow_add hlogy_pos]; norm_num
    have hCcomb_cancel : (1 / 2 : ℝ) ^ K * (C_comb * C_ll ^ (16 * K)) =
        C_sieve * (Real.exp 36) ^ K * (K : ℝ) * (AK K : ℝ) * (2 : ℝ) ^ (K - 1) * C_ll ^ (16 * K) := by
      simp only [C_comb]
      calc (1 / 2 : ℝ) ^ K * (C_sieve * Real.exp 36 ^ K * (K : ℝ) * (AK K : ℝ) * (2 : ℝ) ^ (K - 1) *
              (2 : ℝ) ^ K * C_ll ^ (16 * K))
          = ((1 / 2 : ℝ) ^ K * (2 : ℝ) ^ K) *
              (C_sieve * Real.exp 36 ^ K * (K : ℝ) * (AK K : ℝ) * (2 : ℝ) ^ (K - 1) * C_ll ^ (16 * K)) := by ring
        _ = _ := by rw [h2K, one_mul]
    calc C_sieve * S_max * (y / (Real.log y) ^ (K + 1)) *
            ((K : ℝ) * (AK K : ℝ) * (2 * Real.log y) ^ (K - 1))
        = C_sieve * S_max * ((K : ℝ) * (AK K : ℝ)) * y *
            ((2 * Real.log y) ^ (K - 1) / (Real.log y) ^ (K + 1)) := by ring
      _ = C_sieve * S_max * ((K : ℝ) * (AK K : ℝ)) * y *
            ((2 : ℝ) ^ (K - 1) / (Real.log y) ^ 2) := by rw [hpow_cancel]
      _ ≤ C_sieve * ((Real.exp 36) ^ K * C_ll ^ (16 * K) * (Real.log y) ^ ((1 : ℝ) / 2)) *
            ((K : ℝ) * (AK K : ℝ)) * y * ((2 : ℝ) ^ (K - 1) / (Real.log y) ^ 2) := by
          have hfac_nn : 0 ≤ (K : ℝ) * (AK K : ℝ) * y * ((2 : ℝ) ^ (K - 1) / (Real.log y) ^ 2) :=
            mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hAK_pos.le) hy_pos.le) (by positivity)
          have h1 := mul_le_mul_of_nonneg_left hSmax_le hC_sieve_pos.le
          have h2 := mul_le_mul_of_nonneg_right h1 hfac_nn
          linarith only [h2]
      _ = (1 / 2 : ℝ) ^ K * (C_comb * C_ll ^ (16 * K)) * (Real.log y) ^ ((1 : ℝ) / 2) *
            (y / (Real.log y) ^ 2) := by rw [hCcomb_cancel]; ring
      _ ≤ (1 / 2 : ℝ) ^ K * (Real.log y) ^ ((1 : ℝ) / 2) * (Real.log y) ^ ((1 : ℝ) / 2) *
            (y / (Real.log y) ^ 2) := by
          have h1 := mul_le_mul_of_nonneg_left hsqrt_ge (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) K)
          have h2 : (1 / 2 : ℝ) ^ K * (C_comb * C_ll ^ (16 * K)) * (Real.log y) ^ ((1 : ℝ) / 2) ≤
              (1 / 2 : ℝ) ^ K * (Real.log y) ^ ((1 : ℝ) / 2) * (Real.log y) ^ ((1 : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hlogy_pos.le _)
          exact mul_le_mul_of_nonneg_right h2 (div_nonneg hy_pos.le (sq_nonneg _))
      _ = (1 / 2 : ℝ) ^ K * (y / Real.log y) := by
          rw [mul_assoc ((1 / 2 : ℝ) ^ K), hrpow2]
          field_simp [hlogy_pos.ne']
  have herr_V1 : ∑ m ∈ V₁, 2 * (y / ∏ i : Fin K, (m i : ℝ)) ^ ((4 : ℝ) / 5) ≤
      (1 / 2 : ℝ) ^ K * (y / Real.log y) := by
    have hsub : V₁ ⊆ BoxAll.filter (fun m => (∏ i : Fin K, (m i : ℝ)) ≤ y / yExp y j) := by
      intro m hm; rw [Finset.mem_filter] at hm ⊢; exact ⟨hm.1, hm.2.1⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ =>
      mul_nonneg (by norm_num) (Real.rpow_nonneg
        (div_nonneg hy_pos.le (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))) _))).trans herr
  calc (Q₁.card : ℝ)
      ≤ ∑ m ∈ V₁, (((Icc 1 ⌊y / ∏ i : Fin K, (m i : ℝ)⌋₊).filter
          (fun n => ∀ t ∈ range (K + 1), (chainForm m t n).Prime)).card : ℝ) := hcard_le
    _ ≤ ∑ m ∈ V₁, (C_sieve * S_max * (y / (Real.log y) ^ (K + 1)) * ∏ i : Fin K, (1 / (m i : ℝ)) +
          2 * (y / ∏ i : Fin K, (m i : ℝ)) ^ ((4 : ℝ) / 5)) := Finset.sum_le_sum hterm_sieve
    _ = C_sieve * S_max * (y / (Real.log y) ^ (K + 1)) * (∑ m ∈ V₁, ∏ i : Fin K, (1 / (m i : ℝ))) +
          ∑ m ∈ V₁, 2 * (y / ∏ i : Fin K, (m i : ℝ)) ^ ((4 : ℝ) / 5) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ C_sieve * S_max * (y / (Real.log y) ^ (K + 1)) *
          ((K : ℝ) * (AK K : ℝ) * (2 * Real.log y) ^ (K - 1)) +
          (1 / 2 : ℝ) ^ K * (y / Real.log y) :=
        add_le_add (mul_le_mul_of_nonneg_left hsum_V1 (by positivity)) herr_V1
    _ ≤ (1 / 2 : ℝ) ^ K * (y / Real.log y) + (1 / 2 : ℝ) ^ K * (y / Real.log y) :=
        add_le_add hmain_bound le_rfl
    _ = 2 * (1 / 2 : ℝ) ^ K * (y / Real.log y) := by ring

/- Rankin box sum helper for `Q_{j,2}` -/

lemma rankin_box_sum_bound (j l : ℕ) (hj : 1 ≤ j) (hl : 4 ≤ l) {y : ℝ}
    (hlogy_pos : 0 < Real.log y) (hlogy_big : (l : ℝ) * Tweight (j - 1) ≤ Real.log y) :
    let K := j * l
    let V₂ := (Fintype.piFinset (fun _ : Fin K => range ⌊y⌋₊)).filter (fun t =>
      ∀ a ∈ range j,
        ∑ u ∈ range ((j - a) * l), (if hu : u < K then Real.log (Hgrid K (t ⟨u, hu⟩) : ℝ) else 0) ≤
          ((a + 1 : ℝ) ^ (-etaFKL) - (j + 1 : ℝ) ^ (-etaFKL)) * Real.log y)
    ∑ t ∈ V₂, ∏ u : Fin K, (Mgrid K (t u) : ℝ) / (Hgrid K (t u) : ℝ) ≤
      (4 * Real.exp 3 * etaFKL) ^ K * (Real.log y) ^ K /
        ((K : ℝ) ^ K * (j : ℝ) ^ (etaFKL * (K : ℝ))) := by
  intro K V₂
  have hK4 : 4 ≤ K := by show 4 ≤ j * l; nlinarith only [hj, hl]
  let wCoord : Fin K → ℝ := fun u => Tweight (j - 1 - (u : ℕ) / l)
  let σ : Fin K → ℝ := fun u => ((l : ℝ) / Real.log y) * wCoord u
  have hσ_pos : ∀ u : Fin K, 0 < σ u := fun u =>
    mul_pos (div_pos (by exact_mod_cast (show 0 < l by omega)) hlogy_pos) (Tweight_pos _)
  have hσ_le1 : ∀ u : Fin K, σ u ≤ 1 := fun u => by
    have hw_le : wCoord u ≤ Tweight (j - 1) :=
      Tweight_strictMono.monotone (Nat.sub_le _ _)
    simp only [σ]
    rw [div_mul_eq_mul_div, div_le_one hlogy_pos]
    have hl_nn : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    nlinarith only [hw_le, hlogy_big, hl_nn]
  have hrankin_pt : ∀ t ∈ V₂,
      (1 : ℝ) ≤ Real.exp (K : ℝ) * ∏ u : Fin K, (Hgrid K (t u) : ℝ) ^ (-σ u) := by
    intro t ht
    rw [Finset.mem_filter] at ht
    let xblock : ℕ → ℝ := fun b =>
      ∑ u ∈ Ico ((j - 1 - b) * l) ((j - b) * l),
        if hu : u < K then Real.log (Hgrid K (t ⟨u, hu⟩) : ℝ) else 0
    have hx_sum : ∀ a ∈ range j,
        ∑ b ∈ Ico a j, xblock b ≤ ((a + 1 : ℝ) ^ (-etaFKL) - (j + 1 : ℝ) ^ (-etaFKL)) * Real.log y := by
      intro a ha
      have ha_lt := Finset.mem_range.mp ha
      rw [← Finset.sum_biUnion (pairwiseDisjoint_Ico_blocks j l a),
        biUnion_Ico_eq_range_mul j l a (by omega) ha_lt.le]
      exact ht.2 a ha
    have htele := telescoping_Tweight j xblock y hx_sum
    have hsum_eq : ∑ u : Fin K, σ u * Real.log (Hgrid K (t u) : ℝ) =
        ((l : ℝ) / Real.log y) * ∑ b ∈ range j, Tweight b * xblock b := by
      have h1 : ∑ b ∈ range j, Tweight b * xblock b =
          ∑ u : Fin K, wCoord u * Real.log (Hgrid K (t u) : ℝ) := by
        have h2 : ∑ b ∈ range j, Tweight b * xblock b =
            ∑ b ∈ range j, ∑ u ∈ Ico ((j - 1 - b) * l) ((j - b) * l),
              Tweight b * (if hu : u < K then Real.log (Hgrid K (t ⟨u, hu⟩) : ℝ) else 0) :=
          Finset.sum_congr rfl fun b _ => Finset.mul_sum _ _ _
        rw [h2]
        have hrew : ∀ b ∈ range j,
            ∑ u ∈ Ico ((j - 1 - b) * l) ((j - b) * l),
              Tweight b * (if hu : u < K then Real.log (Hgrid K (t ⟨u, hu⟩) : ℝ) else 0) =
            ∑ u ∈ Ico ((j - 1 - b) * l) ((j - b) * l),
              if hu : u < K then wCoord ⟨u, hu⟩ * Real.log (Hgrid K (t ⟨u, hu⟩) : ℝ) else 0 := by
          intro b hb
          rw [Finset.mem_range] at hb
          refine Finset.sum_congr rfl fun u hu => ?_
          rw [Finset.mem_Ico] at hu
          split_ifs with huK
          · congr 1
            have hdiv : u / l = j - 1 - b := by
              have hlo : j - 1 - b ≤ u / l := (Nat.le_div_iff_mul_le (by omega)).mpr hu.1
              have hhi : u / l < j - b := (Nat.div_lt_iff_lt_mul (by omega)).mpr hu.2
              omega
            simp only [wCoord, hdiv]; congr 1; omega
          · ring
        have hr0 : range j = Ico 0 j := by ext; simp
        rw [Finset.sum_congr rfl hrew, hr0, ← Finset.sum_biUnion (pairwiseDisjoint_Ico_blocks j l 0),
          biUnion_Ico_eq_range_mul j l 0 (by omega) (Nat.zero_le j), Nat.sub_zero]
        have h3 := Fin.sum_univ_eq_sum_range
          (fun u => if hu : u < K then wCoord ⟨u, hu⟩ * Real.log (Hgrid K (t ⟨u, hu⟩) : ℝ) else 0) K
        rw [← h3]
        refine Finset.sum_congr rfl fun u _ => ?_
        simp [u.2]
      rw [h1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => by simp only [σ]; ring
    have hexp_le : ∑ u : Fin K, σ u * Real.log (Hgrid K (t u) : ℝ) ≤ (K : ℝ) := by
      rw [hsum_eq]
      calc ((l : ℝ) / Real.log y) * ∑ b ∈ range j, Tweight b * xblock b
          ≤ ((l : ℝ) / Real.log y) * ((j : ℝ) * Real.log y) :=
            mul_le_mul_of_nonneg_left htele (by positivity)
        _ = (K : ℝ) := by simp only [K, Nat.cast_mul]; field_simp [hlogy_pos.ne']
    have hprod_exp : ∏ u : Fin K, (Hgrid K (t u) : ℝ) ^ (-σ u) =
        Real.exp (-∑ u : Fin K, σ u * Real.log (Hgrid K (t u) : ℝ)) := by
      rw [← Finset.sum_neg_distrib, Real.exp_sum]
      refine Finset.prod_congr rfl fun u _ => ?_
      have hH_pos : (0 : ℝ) < (Hgrid K (t u) : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num) (Hgrid_ge_two K (t u)))
      rw [Real.rpow_def_of_pos hH_pos]; congr 1; ring
    rw [hprod_exp, ← Real.exp_add]
    exact Real.one_le_exp (by linarith only [hexp_le])
  have hprod_w : ((j : ℝ) / Real.exp 1) ^ ((1 + etaFKL) * (K : ℝ)) / etaFKL ^ K ≤
      ∏ u : Fin K, wCoord u := by
    have hgroup : ∏ u : Fin K, wCoord u = ∏ b ∈ range j, (Tweight b) ^ l := by
      have h1 : ∏ u : Fin K, wCoord u = ∏ u ∈ range K, Tweight (j - 1 - u / l) :=
        Fin.prod_univ_eq_prod_range (fun u => Tweight (j - 1 - u / l)) K
      rw [h1]
      have hr0 : range j = Ico 0 j := by ext; simp
      have hunion := biUnion_Ico_eq_range_mul j l 0 (by omega) (Nat.zero_le j)
      rw [Nat.sub_zero] at hunion
      rw [← hunion, Finset.prod_biUnion (pairwiseDisjoint_Ico_blocks j l 0), ← hr0]
      refine Finset.prod_congr rfl fun b hb => ?_
      rw [Finset.mem_range] at hb
      have hconst : ∀ u ∈ Ico ((j - 1 - b) * l) ((j - b) * l), Tweight (j - 1 - u / l) = Tweight b := by
        intro u hu
        rw [Finset.mem_Ico] at hu
        have hlo : j - 1 - b ≤ u / l := (Nat.le_div_iff_mul_le (by omega)).mpr hu.1
        have hhi : u / l < j - b := (Nat.div_lt_iff_lt_mul (by omega)).mpr hu.2
        congr 1; omega
      rw [Finset.prod_congr rfl hconst, Finset.prod_const, Nat.card_Ico]
      congr 1
      have : (j - b) * l - (j - 1 - b) * l = (j - b - (j - 1 - b)) * l := (Nat.sub_mul _ _ l).symm
      rw [this, show j - b - (j - 1 - b) = 1 by omega, one_mul]
    rw [hgroup]
    have hfac_eq : ∏ b ∈ range j, ((b + 1 : ℝ) ^ (1 + etaFKL)) =
        (j.factorial : ℝ) ^ (1 + etaFKL) := by
      rw [Real.finsetProd_rpow (range j) (fun b => (b + 1 : ℝ)) (fun b _ => by positivity)]
      congr 1
      have hgen : ∀ n : ℕ, ∏ b ∈ range n, ((b : ℝ) + 1) = (n.factorial : ℝ) := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          rw [Finset.prod_range_succ, ih, Nat.factorial_succ, Nat.cast_mul]
          push_cast; ring
      exact hgen j
    have hprod_lb : ((j.factorial : ℝ) ^ (1 + etaFKL) / etaFKL ^ j) ^ l ≤
        ∏ b ∈ range j, (Tweight b) ^ l := by
      rw [Finset.prod_pow]
      refine pow_le_pow_left₀ (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (pow_nonneg etaFKL_pos.le _)) ?_ l
      calc (j.factorial : ℝ) ^ (1 + etaFKL) / etaFKL ^ j
          = ∏ b ∈ range j, ((b + 1 : ℝ) ^ (1 + etaFKL) / etaFKL) := by
            rw [Finset.prod_div_distrib, hfac_eq, Finset.prod_const, Finset.card_range]
        _ ≤ ∏ b ∈ range j, Tweight b :=
            Finset.prod_le_prod (fun _ _ => div_nonneg (by positivity) etaFKL_pos.le)
              (fun b _ => Tweight_ge b)
    have hstirl : ((j : ℝ) / Real.exp 1) ^ ((1 + etaFKL) * (K : ℝ)) / etaFKL ^ K ≤
        ((j.factorial : ℝ) ^ (1 + etaFKL) / etaFKL ^ j) ^ l := by
      rw [div_pow, ← pow_mul]
      have hbase_nn : (0 : ℝ) ≤ (j : ℝ) / Real.exp 1 := by positivity
      have h1 : (((j : ℝ) / Real.exp 1) ^ j) ^ (1 + etaFKL) ≤ (j.factorial : ℝ) ^ (1 + etaFKL) :=
        Real.rpow_le_rpow (by positivity) (factorial_ge_div_e_pow j) (by linarith [etaFKL_pos])
      have h2 : ((((j : ℝ) / Real.exp 1) ^ j) ^ (1 + etaFKL)) ^ l ≤
          ((j.factorial : ℝ) ^ (1 + etaFKL)) ^ l :=
        pow_le_pow_left₀ (Real.rpow_nonneg (pow_nonneg hbase_nn j) _) h1 l
      have h3 : ((((j : ℝ) / Real.exp 1) ^ j) ^ (1 + etaFKL)) ^ l =
          ((j : ℝ) / Real.exp 1) ^ ((1 + etaFKL) * (K : ℝ)) := by
        rw [← Real.rpow_natCast ((((j : ℝ) / Real.exp 1) ^ j) ^ (1 + etaFKL)),
          ← Real.rpow_natCast ((j : ℝ) / Real.exp 1),
          ← Real.rpow_mul hbase_nn, ← Real.rpow_mul hbase_nn]
        congr 1; simp only [K, Nat.cast_mul]; ring
      rw [h3] at h2
      exact div_le_div_of_nonneg_right h2 (pow_nonneg etaFKL_pos.le _)
    exact hstirl.trans hprod_lb
  let BoxT := Fintype.piFinset (fun _ : Fin K => range ⌊y⌋₊)
  have hprod_w_pos : 0 < ∏ u : Fin K, wCoord u := Finset.prod_pos (fun u _ => Tweight_pos _)
  have heta_pos := etaFKL_pos
  have hj_pos : (0 : ℝ) < j := by exact_mod_cast hj
  have hl_pos : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have hlb_pos : 0 < ((j : ℝ) / Real.exp 1) ^ ((1 + etaFKL) * (K : ℝ)) / etaFKL ^ K :=
    div_pos (Real.rpow_pos_of_pos (div_pos hj_pos (Real.exp_pos 1)) _) (pow_pos heta_pos K)
  calc ∑ t ∈ V₂, ∏ u : Fin K, (Mgrid K (t u) : ℝ) / (Hgrid K (t u) : ℝ)
      ≤ ∑ t ∈ V₂, (Real.exp (K : ℝ) * ∏ u : Fin K, (Hgrid K (t u) : ℝ) ^ (-σ u)) *
          ∏ u : Fin K, (Mgrid K (t u) : ℝ) / (Hgrid K (t u) : ℝ) := by
        refine Finset.sum_le_sum fun t ht => ?_
        have hP_nn : 0 ≤ ∏ u : Fin K, (Mgrid K (t u) : ℝ) / (Hgrid K (t u) : ℝ) :=
          Finset.prod_nonneg (fun _ _ => by positivity)
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hrankin_pt t ht) hP_nn
    _ = Real.exp (K : ℝ) * ∑ t ∈ V₂,
          ∏ u : Fin K, ((Mgrid K (t u) : ℝ) / (Hgrid K (t u) : ℝ) * (Hgrid K (t u) : ℝ) ^ (-σ u)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [mul_assoc, ← Finset.prod_mul_distrib]
        congr 1; refine Finset.prod_congr rfl fun u _ => by ring
    _ ≤ Real.exp (K : ℝ) * ∑ t ∈ BoxT,
          ∏ u : Fin K, ((Mgrid K (t u) : ℝ) / (Hgrid K (t u) : ℝ) * (Hgrid K (t u) : ℝ) ^ (-σ u)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) (fun _ _ _ => Finset.prod_nonneg (fun _ _ => by positivity)))
          (Real.exp_pos _).le
    _ = Real.exp (K : ℝ) * ∏ u : Fin K,
          ∑ s ∈ range ⌊y⌋₊, ((Mgrid K s : ℝ) / (Hgrid K s : ℝ) * (Hgrid K s : ℝ) ^ (-σ u)) := by
        rw [sum_piFinset_prod (fun _ : Fin K => range ⌊y⌋₊)
          (fun u s => (Mgrid K s : ℝ) / (Hgrid K s : ℝ) * (Hgrid K s : ℝ) ^ (-σ u))]
    _ ≤ Real.exp (K : ℝ) * ∏ u : Fin K, (4 / σ u) := by
        refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod
          (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))
          (fun u _ => sum_Mgrid_mul_Hgrid_rpow_le (by omega) ⌊y⌋₊ (hσ_pos u) (hσ_le1 u)))
          (Real.exp_pos _).le
    _ = Real.exp (K : ℝ) * ((4 * Real.log y / (l : ℝ)) ^ K / ∏ u : Fin K, wCoord u) := by
        congr 1
        have hrew : ∀ u : Fin K, 4 / σ u = (4 * Real.log y / (l : ℝ)) / wCoord u := fun u => by
          simp only [σ]
          have h2 : wCoord u ≠ 0 := (Tweight_pos _).ne'
          field_simp [hl_pos.ne', h2, hlogy_pos.ne']
        simp_rw [hrew]
        rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ Real.exp (K : ℝ) * ((4 * Real.log y / (l : ℝ)) ^ K /
          (((j : ℝ) / Real.exp 1) ^ ((1 + etaFKL) * (K : ℝ)) / etaFKL ^ K)) := by
        refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) hlb_pos hprod_w)
          (Real.exp_pos _).le
    _ ≤ (4 * Real.exp 3 * etaFKL) ^ K * (Real.log y) ^ K /
          ((K : ℝ) ^ K * (j : ℝ) ^ (etaFKL * (K : ℝ))) := by
        have hdiv_rpow : ((j : ℝ) / Real.exp 1) ^ ((1 + etaFKL) * (K : ℝ)) =
            ((j : ℝ) ^ K * (j : ℝ) ^ (etaFKL * (K : ℝ))) / Real.exp ((1 + etaFKL) * (K : ℝ)) := by
          rw [Real.div_rpow hj_pos.le (Real.exp_pos 1).le,
            show (1 + etaFKL) * (K : ℝ) = (K : ℝ) + etaFKL * (K : ℝ) by ring,
            Real.rpow_add hj_pos, Real.rpow_natCast, ← Real.exp_mul]
          congr 2; ring
        have hK_eq : (l : ℝ) ^ K * (j : ℝ) ^ K = (K : ℝ) ^ K := by
          rw [← mul_pow]; congr 1; simp only [K, Nat.cast_mul]; ring
        have hexp_le : Real.exp (K : ℝ) * Real.exp ((1 + etaFKL) * (K : ℝ)) ≤ (Real.exp 3) ^ K := by
          rw [← Real.exp_add, ← Real.exp_nat_mul]
          apply Real.exp_le_exp.mpr
          have h1 := etaFKL_le_one
          nlinarith only [h1, show (0 : ℝ) ≤ (K : ℝ) by positivity]
        have hlhs_eq : Real.exp (K : ℝ) * ((4 * Real.log y / (l : ℝ)) ^ K /
              (((j : ℝ) / Real.exp 1) ^ ((1 + etaFKL) * (K : ℝ)) / etaFKL ^ K)) =
            ((4 : ℝ) ^ K * (Real.exp (K : ℝ) * Real.exp ((1 + etaFKL) * (K : ℝ))) * etaFKL ^ K *
              (Real.log y) ^ K) / ((K : ℝ) ^ K * (j : ℝ) ^ (etaFKL * (K : ℝ))) := by
          rw [hdiv_rpow, div_pow, mul_pow]
          have hne1 : (l : ℝ) ^ K ≠ 0 := pow_ne_zero K hl_pos.ne'
          have hne2 : (j : ℝ) ^ K ≠ 0 := pow_ne_zero K hj_pos.ne'
          have hne3 : (j : ℝ) ^ (etaFKL * (K : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hj_pos _).ne'
          have hne4 : Real.exp ((1 + etaFKL) * (K : ℝ)) ≠ 0 := (Real.exp_pos _).ne'
          have hne5 : etaFKL ^ K ≠ 0 := pow_ne_zero K heta_pos.ne'
          have hne6 : (K : ℝ) ^ K ≠ 0 := by rw [← hK_eq]; exact mul_ne_zero hne1 hne2
          rw [← hK_eq]
          field_simp [hne1, hne2, hne3, hne4, hne5]
        rw [hlhs_eq, show (4 * Real.exp 3 * etaFKL) ^ K * (Real.log y) ^ K =
            (4 : ℝ) ^ K * (Real.exp 3) ^ K * etaFKL ^ K * (Real.log y) ^ K by rw [mul_pow, mul_pow]]
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        have hfac_nn : 0 ≤ etaFKL ^ K * (Real.log y) ^ K :=
          mul_nonneg (pow_nonneg heta_pos.le K) (pow_nonneg hlogy_pos.le K)
        have h1 := mul_le_mul_of_nonneg_left hexp_le (show (0 : ℝ) ≤ (4 : ℝ) ^ K by positivity)
        have h2 := mul_le_mul_of_nonneg_right h1 hfac_nn
        linarith only [h2]

/- Bound on `Q_{j,2}`: chains with all multipliers `m_i > AK K` -/

open Classical in
lemma bound_Qj2 (j l : ℕ) (hj : 1 ≤ j) (hl : 4 ≤ l) :
    ∀ᶠ y : ℝ in atTop,
      (((Icc 1 ⌊y⌋₊).filter (fun p0 =>
        ∃ p : Fin (j * l + 1) → ℕ, IsPrimeChain (j * l) p ∧ p 0 = p0 ∧
          yExp y j ≤ (p (Fin.last (j * l)) : ℝ) ∧
          (∀ a ∈ Ico 1 j, ∀ ha : a * l < j * l + 1, (p ⟨a * l, ha⟩ : ℝ) < yExp y a) ∧
          (∀ i : Fin (j * l), AK (j * l) < chainMult p i))).card : ℝ) ≤
        (1600 * Real.exp 101 + 1) * (1 / 2 : ℝ) ^ (j * l) * (y / Real.log y) := by
  let K := j * l
  have hK4 : 4 ≤ K := by show 4 ≤ j * l; nlinarith only [hj, hl]
  obtain ⟨X₀, hX₀4, hsieve⟩ := sieve_upper_bound K
  let αj : ℝ := (j + 1 : ℝ) ^ (-etaFKL)
  have hαj_pos : 0 < αj := Real.rpow_pos_of_pos (by positivity) _
  let Y_sieve : ℝ := (max X₀ 4 + 2) ^ (1 / αj)
  let Y_min : ℝ := max (max (Real.exp 4) Y_sieve)
    (max (Real.exp (4 / αj)) (Real.exp ((l : ℝ) * Tweight (j - 1))))
  filter_upwards [sieve_error_sum_le K j (by omega), Filter.eventually_ge_atTop Y_min] with y herr hy
  have hy_exp4 : Real.exp 4 ≤ y := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hy)
  have hy_Ysieve : Y_sieve ≤ y := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hy)
  have hy_exp4α : Real.exp (4 / αj) ≤ y := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hy)
  have hy_Tw : Real.exp ((l : ℝ) * Tweight (j - 1)) ≤ y :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hy)
  have hy_pos : 0 < y := lt_of_lt_of_le (Real.exp_pos 4) hy_exp4
  have hlogy_ge4 : (4 : ℝ) ≤ Real.log y := by
    have := Real.log_le_log (Real.exp_pos 4) hy_exp4; rwa [Real.log_exp] at this
  have hlogy_pos : 0 < Real.log y := by linarith only [hlogy_ge4]
  have hlogy_ge4α : 4 / αj ≤ Real.log y := by
    have := Real.log_le_log (Real.exp_pos _) hy_exp4α; rwa [Real.log_exp] at this
  have hlogy_Tw : (l : ℝ) * Tweight (j - 1) ≤ Real.log y := by
    have := Real.log_le_log (Real.exp_pos _) hy_Tw; rwa [Real.log_exp] at this
  have hyExp_ge : max X₀ 4 + 2 ≤ yExp y j := by
    have h1 := Real.rpow_le_rpow (by positivity) hy_Ysieve hαj_pos.le
    rw [← Real.rpow_mul (by positivity)] at h1
    have hexp : (1 / αj) * αj = 1 := by field_simp [hαj_pos.ne']
    rw [hexp, Real.rpow_one] at h1
    exact h1
  have hyExp_ge3 : (3 : ℝ) ≤ yExp y j := by linarith only [hyExp_ge, le_max_right X₀ 4]
  let BoxT := Fintype.piFinset (fun _ : Fin K => range ⌊y⌋₊)
  let V₂ := BoxT.filter (fun t =>
    ∀ a ∈ range j,
      ∑ u ∈ range ((j - a) * l), (if hu : u < K then Real.log (Hgrid K (t ⟨u, hu⟩) : ℝ) else 0) ≤
        ((a + 1 : ℝ) ^ (-etaFKL) - (j + 1 : ℝ) ^ (-etaFKL)) * Real.log y)
  let BoxOf : (Fin K → ℕ) → Finset (Fin K → ℕ) := fun t =>
    Fintype.piFinset (fun i : Fin K => Ioc (Hgrid K (t i)) (Hgrid K (t i) + Mgrid K (t i)))
  let BoxValid : (Fin K → ℕ) → Finset (Fin K → ℕ) := fun t =>
    (BoxOf t).filter (fun m => (∏ i : Fin K, (m i : ℝ)) ≤ y / yExp y j)
  let Q₂ := (Icc 1 ⌊y⌋₊).filter (fun p0 =>
    ∃ p : Fin (K + 1) → ℕ, IsPrimeChain K p ∧ p 0 = p0 ∧
      yExp y j ≤ (p (Fin.last K) : ℝ) ∧
      (∀ a ∈ Ico 1 j, ∀ ha : a * l < K + 1, (p ⟨a * l, ha⟩ : ℝ) < yExp y a) ∧
      (∀ i : Fin K, AK K < chainMult p i))
  have hcover : Q₂ ⊆ V₂.biUnion (fun t => (BoxValid t).biUnion (fun m =>
      ((Icc 1 ⌊y / ∏ i : Fin K, (m i : ℝ)⌋₊).filter
        (fun n => ∀ s ∈ range (K + 1), (chainForm m s n).Prime)).image
        (fun n => chainForm m K n))) := by
    intro p0 hp0
    rw [Finset.mem_filter, Finset.mem_Icc] at hp0
    obtain ⟨⟨_, hp0_le⟩, p, hp_ch, hp0_eq, hlast_ge, hmid_lt, hm_gt_AK⟩ := hp0
    let m := chainMult p
    have hlast3 : 3 ≤ p (Fin.last K) := by
      have : (3 : ℝ) ≤ (p (Fin.last K) : ℝ) := le_trans hyExp_ge3 hlast_ge
      exact_mod_cast this
    have hm2 : ∀ i : Fin K, 2 ≤ m i := fun i => chainMult_ge_two hp_ch hlast3 i
    have hprod_mul : (∏ i : Fin K, (m i : ℝ)) * (p (Fin.last K) : ℝ) ≤ y := by
      have hcast : (∏ i : Fin K, (m i : ℝ)) * (p (Fin.last K) : ℝ) ≤ (p 0 : ℝ) := by
        exact_mod_cast chainMult_full_prod_le hp_ch
      have hp0_y : (p 0 : ℝ) ≤ y := by
        rw [hp0_eq]; exact le_trans (by exact_mod_cast hp0_le) (Nat.floor_le hy_pos.le)
      exact hcast.trans hp0_y
    have hprod_le : (∏ i : Fin K, (m i : ℝ)) ≤ y / yExp y j := by
      rw [le_div_iff₀ (yExp_pos hy_pos j)]
      exact (mul_le_mul_of_nonneg_left hlast_ge (Finset.prod_nonneg (fun _ _ => by positivity))).trans hprod_mul
    have hm_le_y : ∀ i : Fin K, m i ≤ ⌊y⌋₊ := fun i => by
      have h1 : m i ≤ ∏ u : Fin K, m u := by
        have hpos : ∀ u : Fin K, 1 ≤ m u := fun u => by have := hm2 u; omega
        calc m i = m i * 1 := (mul_one _).symm
          _ ≤ m i * ∏ u ∈ (Finset.univ : Finset (Fin K)).erase i, m u :=
              Nat.mul_le_mul_left _ (Finset.one_le_prod' fun u _ => hpos u)
          _ = ∏ u : Fin K, m u := Finset.mul_prod_erase _ _ (Finset.mem_univ i)
      have h2 : (m i : ℝ) ≤ y := by
        have hge1 : (1 : ℝ) ≤ yExp y j := by linarith only [hyExp_ge3]
        have h3 : (∏ u : Fin K, (m u : ℝ)) ≤ y :=
          hprod_le.trans (by rw [div_le_iff₀ (yExp_pos hy_pos j)]; nlinarith only [hy_pos, hge1])
        exact le_trans (by exact_mod_cast h1) h3
      exact Nat.le_floor h2
    have hex_t : ∀ i : Fin K, ∃ ti < ⌊y⌋₊, m i ∈ Ioc (Hgrid K ti) (Hgrid K ti + Mgrid K ti) := fun i => by
      obtain ⟨ti, hti_lt, hti_mem⟩ := exists_Hgrid_interval (hm_gt_AK i)
      exact ⟨ti, lt_of_lt_of_le hti_lt (hm_le_y i), hti_mem⟩
    let t : Fin K → ℕ := fun i => (hex_t i).choose
    have ht_lt : ∀ i : Fin K, t i < ⌊y⌋₊ := fun i => (hex_t i).choose_spec.1
    have ht_mem : ∀ i : Fin K, m i ∈ Ioc (Hgrid K (t i)) (Hgrid K (t i) + Mgrid K (t i)) :=
      fun i => (hex_t i).choose_spec.2
    have ht_in_V2 : t ∈ V₂ := by
      refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun i => Finset.mem_range.mpr (ht_lt i)), ?_⟩
      intro a ha
      rw [Finset.mem_range] at ha
      have hal_le_K : a * l ≤ K := Nat.mul_le_mul_right l ha.le
      have hal_lt : a * l < K + 1 := Nat.lt_succ_of_le hal_le_K
      have hpa_le : (p ⟨a * l, hal_lt⟩ : ℝ) ≤ yExp y a := by
        by_cases ha0 : a = 0
        · subst ha0
          rw [yExp_zero]
          have : (⟨0 * l, hal_lt⟩ : Fin (K + 1)) = 0 := by ext; simp
          rw [this, hp0_eq]
          exact le_trans (by exact_mod_cast hp0_le) (Nat.floor_le hy_pos.le)
        · exact (hmid_lt a (Finset.mem_Ico.mpr ⟨by omega, ha⟩) hal_lt).le
      have hblk := chainMult_block_prod_le hp_ch hal_le_K
      have hsub_eq : K - a * l = (j - a) * l := by simp only [K]; rw [Nat.sub_mul]
      rw [hsub_eq] at hblk
      let Hfn : ℕ → ℝ := fun u => if hu : u < K then (Hgrid K (t ⟨u, hu⟩) : ℝ) else 1
      have hHfn_pos : ∀ u ∈ range ((j - a) * l), 0 < Hfn u := fun u _ => by
        simp only [Hfn]; split_ifs
        · exact_mod_cast (lt_of_lt_of_le (by norm_num) (Hgrid_ge_two K _))
        · norm_num
      have hblk_r : (∏ u ∈ range ((j - a) * l), Hfn u) * yExp y j ≤ yExp y a := by
        have hprod_le_m : ∏ u ∈ range ((j - a) * l), Hfn u ≤
            ∏ u ∈ range ((j - a) * l), (if hlt : u < K then (m ⟨u, hlt⟩ : ℝ) else 1) := by
          refine Finset.prod_le_prod (fun u hu => (hHfn_pos u hu).le) (fun u _ => ?_)
          simp only [Hfn]; split_ifs with huK
          · exact_mod_cast (Finset.mem_Ioc.mp (ht_mem ⟨u, huK⟩)).1.le
          · exact le_rfl
        have hblk_cast : (∏ u ∈ range ((j - a) * l), (if hlt : u < K then (m ⟨u, hlt⟩ : ℝ) else 1)) *
            (p (Fin.last K) : ℝ) ≤ (p ⟨a * l, hal_lt⟩ : ℝ) := by
          have h1 : ((∏ u ∈ range ((j - a) * l), (if hlt : u < K then m ⟨u, hlt⟩ else 1) : ℕ) : ℝ) =
              ∏ u ∈ range ((j - a) * l), (if hlt : u < K then (m ⟨u, hlt⟩ : ℝ) else 1) := by
            rw [Nat.cast_prod]; refine Finset.prod_congr rfl fun u _ => by split_ifs <;> simp
          rw [← h1]; exact_mod_cast hblk
        calc (∏ u ∈ range ((j - a) * l), Hfn u) * yExp y j
            ≤ (∏ u ∈ range ((j - a) * l), (if hlt : u < K then (m ⟨u, hlt⟩ : ℝ) else 1)) *
                (p (Fin.last K) : ℝ) :=
              mul_le_mul hprod_le_m hlast_ge (yExp_pos hy_pos j).le
                (Finset.prod_nonneg (fun _ _ => by split_ifs <;> positivity))
          _ ≤ (p ⟨a * l, hal_lt⟩ : ℝ) := hblk_cast
          _ ≤ yExp y a := hpa_le
      have hlog_step := Real.log_le_log
        (mul_pos (Finset.prod_pos hHfn_pos) (yExp_pos hy_pos j)) hblk_r
      rw [Real.log_mul (Finset.prod_pos hHfn_pos).ne' (yExp_pos hy_pos j).ne',
        Real.log_prod (fun u hu => (hHfn_pos u hu).ne'),
        log_yExp hy_pos j, log_yExp hy_pos a] at hlog_step
      have hsum_congr : ∑ u ∈ range ((j - a) * l), Real.log (Hfn u) =
          ∑ u ∈ range ((j - a) * l),
            if hu : u < K then Real.log (Hgrid K (t ⟨u, hu⟩) : ℝ) else 0 := by
        refine Finset.sum_congr rfl fun u _ => ?_
        simp only [Hfn]; split_ifs <;> simp
      rw [hsum_congr] at hlog_step
      linarith only [hlog_step]
    rw [Finset.mem_biUnion]
    refine ⟨t, ht_in_V2, Finset.mem_biUnion.mpr ⟨m,
      Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ht_mem, hprod_le⟩, Finset.mem_image.mpr ?_⟩⟩
    refine ⟨p (Fin.last K), ?_, ?_⟩
    · simp only [Finset.mem_filter]
      refine ⟨Finset.mem_Icc.mpr ⟨by omega, ?_⟩, ?_⟩
      · apply Nat.le_floor
        have hP_pos : 0 < ∏ i : Fin K, (m i : ℝ) :=
          Finset.prod_pos (fun i _ => by exact_mod_cast (show 0 < m i by have := hm2 i; omega))
        rw [le_div_iff₀ hP_pos]; linarith only [hprod_mul]
      · intro s hs
        rw [Finset.mem_range] at hs
        rw [chainForm_chainMult hp_ch s (by omega)]
        exact hp_ch.1 _
    · rw [chainForm_chainMult hp_ch K le_rfl]
      have : (⟨K - K, by omega⟩ : Fin (K + 1)) = 0 := by ext; simp
      rw [this, hp0_eq]
  have hcard_le : (Q₂.card : ℝ) ≤
      ∑ t ∈ V₂, ∑ m ∈ BoxValid t,
        (((Icc 1 ⌊y / ∏ i : Fin K, (m i : ℝ)⌋₊).filter
          (fun n => ∀ s ∈ range (K + 1), (chainForm m s n).Prime)).card : ℝ) := by
    have hnat : Q₂.card ≤ ∑ t ∈ V₂, ∑ m ∈ BoxValid t,
        ((Icc 1 ⌊y / ∏ i : Fin K, (m i : ℝ)⌋₊).filter
          (fun n => ∀ s ∈ range (K + 1), (chainForm m s n).Prime)).card := by
      calc Q₂.card
          ≤ (V₂.biUnion (fun t => (BoxValid t).biUnion (fun m =>
              ((Icc 1 ⌊y / ∏ i : Fin K, (m i : ℝ)⌋₊).filter
                (fun n => ∀ s ∈ range (K + 1), (chainForm m s n).Prime)).image
                (fun n => chainForm m K n)))).card := Finset.card_le_card hcover
        _ ≤ ∑ t ∈ V₂, ((BoxValid t).biUnion (fun m =>
              ((Icc 1 ⌊y / ∏ i : Fin K, (m i : ℝ)⌋₊).filter
                (fun n => ∀ s ∈ range (K + 1), (chainForm m s n).Prime)).image
                (fun n => chainForm m K n))).card := Finset.card_biUnion_le
        _ ≤ ∑ t ∈ V₂, ∑ m ∈ BoxValid t,
              (((Icc 1 ⌊y / ∏ i : Fin K, (m i : ℝ)⌋₊).filter
                (fun n => ∀ s ∈ range (K + 1), (chainForm m s n).Prime)).image
                (fun n => chainForm m K n)).card := Finset.sum_le_sum (fun _ _ => Finset.card_biUnion_le)
        _ ≤ ∑ t ∈ V₂, ∑ m ∈ BoxValid t,
              ((Icc 1 ⌊y / ∏ i : Fin K, (m i : ℝ)⌋₊).filter
                (fun n => ∀ s ∈ range (K + 1), (chainForm m s n).Prime)).card :=
            Finset.sum_le_sum (fun _ _ => Finset.sum_le_sum (fun _ _ => Finset.card_image_le))
    exact_mod_cast hnat
  let C_sieve : ℝ := 4 * (400 * (K + 1 : ℝ)) ^ (K + 1) * ((j + 1 : ℝ) ^ etaFKL) ^ (K + 1)
  have hterm_sieve : ∀ t ∈ V₂, ∀ m ∈ BoxValid t,
      (((Icc 1 ⌊y / ∏ i : Fin K, (m i : ℝ)⌋₊).filter
        (fun n => ∀ s ∈ range (K + 1), (chainForm m s n).Prime)).card : ℝ) ≤
        C_sieve * (y / (Real.log y) ^ (K + 1)) * (singSeries m / ∏ i : Fin K, (Hgrid K (t i) : ℝ)) +
          2 * (y / ∏ i : Fin K, (m i : ℝ)) ^ ((4 : ℝ) / 5) := by
    intro t _ m hm
    rw [Finset.mem_filter] at hm
    have hm_gt_H : ∀ i : Fin K, Hgrid K (t i) < m i := fun i =>
      (Finset.mem_Ioc.mp (Fintype.mem_piFinset.mp hm.1 i)).1
    have hm1 : ∀ i : Fin K, 1 ≤ m i := fun i => by
      have := Hgrid_ge_two K (t i); have := hm_gt_H i; omega
    have hP_pos : 0 < ∏ i : Fin K, (m i : ℝ) :=
      Finset.prod_pos (fun i _ => by exact_mod_cast (hm1 i))
    have hH_pos : 0 < ∏ i : Fin K, (Hgrid K (t i) : ℝ) :=
      Finset.prod_pos (fun i _ => by exact_mod_cast (lt_of_lt_of_le (by norm_num) (Hgrid_ge_two K (t i))))
    have hH_le_P : ∏ i : Fin K, (Hgrid K (t i) : ℝ) ≤ ∏ i : Fin K, (m i : ℝ) :=
      Finset.prod_le_prod (fun _ _ => by positivity) (fun i _ => by exact_mod_cast (hm_gt_H i).le)
    let Xm : ℕ := ⌊y / ∏ i : Fin K, (m i : ℝ)⌋₊
    have hdiv_ge : yExp y j ≤ y / ∏ i : Fin K, (m i : ℝ) := by
      rw [le_div_iff₀ hP_pos]
      have h1 := (le_div_iff₀ (yExp_pos hy_pos j)).mp hm.2
      linarith only [h1]
    have hXm_ge_X0 : X₀ ≤ (Xm : ℝ) := by
      have h1 := Nat.lt_floor_add_one (y / ∏ i : Fin K, (m i : ℝ))
      linarith only [hyExp_ge, le_max_left X₀ 4, hdiv_ge, h1]
    have hXm_le_div : (Xm : ℝ) ≤ y / ∏ i : Fin K, (m i : ℝ) := Nat.floor_le (by positivity)
    have hXm_le_H : (Xm : ℝ) ≤ y / ∏ i : Fin K, (Hgrid K (t i) : ℝ) :=
      hXm_le_div.trans (div_le_div_of_nonneg_left hy_pos.le hH_pos hH_le_P)
    have hXm_ge_half : (1 / 2) * yExp y j ≤ (Xm : ℝ) := by
      have h1 := Nat.lt_floor_add_one (y / ∏ i : Fin K, (m i : ℝ))
      linarith only [hyExp_ge3, hdiv_ge, h1]
    have hlogXm_ge : (1 / 2) * αj * Real.log y ≤ Real.log (Xm : ℝ) := by
      have h1 := Real.log_le_log (by positivity) hXm_ge_half
      rw [Real.log_mul (by norm_num) (yExp_pos hy_pos j).ne', log_yExp hy_pos j, one_div, Real.log_inv] at h1
      have h2 := Real.log_two_lt_d9
      have h3 : (4 : ℝ) ≤ αj * Real.log y := by
        have := (div_le_iff₀ hαj_pos).mp hlogy_ge4α; linarith only [this]
      linarith only [h1, h2, h3]
    have hs : (((Icc 1 Xm).filter (fun n => ∀ s ∈ range (K + 1), (chainForm m s n).Prime)).card : ℝ) ≤
        4 * (200 * (K + 1 : ℝ)) ^ (K + 1) * singSeries m * Xm / (Real.log Xm) ^ (K + 1) +
          2 * (Xm : ℝ) ^ ((4 : ℝ) / 5) := by
      convert hsieve Xm hXm_ge_X0 m hm1 using 2
    have herr_m : 2 * (Xm : ℝ) ^ ((4 : ℝ) / 5) ≤ 2 * (y / ∏ i : Fin K, (m i : ℝ)) ^ ((4 : ℝ) / 5) := by
      gcongr
    have hmain_m : 4 * (200 * (K + 1 : ℝ)) ^ (K + 1) * singSeries m * Xm / (Real.log Xm) ^ (K + 1) ≤
        C_sieve * (y / (Real.log y) ^ (K + 1)) * (singSeries m / ∏ i : Fin K, (Hgrid K (t i) : ℝ)) := by
      have hαj_inv : αj⁻¹ = (j + 1 : ℝ) ^ etaFKL := by
        simp only [αj, Real.rpow_neg (show (0 : ℝ) ≤ (j + 1 : ℝ) by positivity), inv_inv]
      have hCeq : 4 * (200 * (K + 1 : ℝ)) ^ (K + 1) / ((1 / 2 : ℝ) * αj) ^ (K + 1) = C_sieve := by
        simp only [C_sieve, ← hαj_inv]
        have h1 : (200 * (K + 1 : ℝ)) / (1 / 2 : ℝ) = 400 * (K + 1 : ℝ) := by ring
        rw [mul_pow (1 / 2 : ℝ) αj, ← div_div, mul_div_assoc, ← div_pow, h1, div_eq_mul_inv, ← inv_pow]
      have hS_nn : 0 ≤ singSeries m := singSeries_nonneg m
      have hnum : 4 * (200 * (K + 1 : ℝ)) ^ (K + 1) * singSeries m * Xm ≤
          4 * (200 * (K + 1 : ℝ)) ^ (K + 1) * singSeries m * (y / ∏ i : Fin K, (Hgrid K (t i) : ℝ)) := by
        gcongr
      have hden : ((1 / 2) * αj * Real.log y) ^ (K + 1) ≤ (Real.log Xm) ^ (K + 1) :=
        pow_le_pow_left₀ (by positivity) hlogXm_ge (K + 1)
      calc 4 * (200 * (K + 1 : ℝ)) ^ (K + 1) * singSeries m * Xm / (Real.log Xm) ^ (K + 1)
          ≤ 4 * (200 * (K + 1 : ℝ)) ^ (K + 1) * singSeries m * (y / ∏ i : Fin K, (Hgrid K (t i) : ℝ)) /
              ((1 / 2) * αj * Real.log y) ^ (K + 1) :=
            div_le_div₀ (by positivity) hnum (by positivity) hden
        _ = (4 * (200 * (K + 1 : ℝ)) ^ (K + 1) / ((1 / 2) * αj) ^ (K + 1)) *
              (y / (Real.log y) ^ (K + 1)) * (singSeries m / ∏ i : Fin K, (Hgrid K (t i) : ℝ)) := by
            rw [mul_pow]; ring
        _ = C_sieve * (y / (Real.log y) ^ (K + 1)) * (singSeries m / ∏ i : Fin K, (Hgrid K (t i) : ℝ)) := by
            rw [hCeq]
    linarith only [hs, herr_m, hmain_m]
  have hbox_sing : ∀ t ∈ V₂,
      ∑ m ∈ BoxValid t, (singSeries m / ∏ i : Fin K, (Hgrid K (t i) : ℝ)) ≤
        Real.exp (100 * (K + 1 : ℝ)) * ∏ i : Fin K, (Mgrid K (t i) : ℝ) / (Hgrid K (t i) : ℝ) := by
    intro t _
    have hH_pos : 0 < ∏ i : Fin K, (Hgrid K (t i) : ℝ) :=
      Finset.prod_pos (fun i _ => by exact_mod_cast (lt_of_lt_of_le (by norm_num) (Hgrid_ge_two K (t i))))
    rw [← Finset.sum_div, Finset.prod_div_distrib, ← mul_div_assoc]
    refine div_le_div_of_nonneg_right ?_ hH_pos.le
    calc ∑ m ∈ BoxValid t, singSeries m
        ≤ ∑ m ∈ BoxOf t, singSeries m :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun m _ _ => singSeries_nonneg m)
      _ ≤ Real.exp (100 * (K + 1 : ℝ)) * ∏ i : Fin K, (Mgrid K (t i) : ℝ) :=
          singular_avg (by omega) (fun i => Hgrid K (t i)) (fun i => Mgrid K (t i))
            (fun i => Hgrid_ge_two K (t i)) (fun i => Hgrid_le_mul_Mgrid K (t i))
            (fun i => Mgrid_ge_big K (t i))
  have herr_V2 : ∑ t ∈ V₂, ∑ m ∈ BoxValid t, 2 * (y / ∏ i : Fin K, (m i : ℝ)) ^ ((4 : ℝ) / 5) ≤
      (1 / 2 : ℝ) ^ K * (y / Real.log y) := by
    have hdisj : Set.PairwiseDisjoint (V₂ : Set (Fin K → ℕ)) BoxValid := by
      intro t₁ _ t₂ _ hne
      simp only [Function.onFun]; rw [Finset.disjoint_left]
      intro m hm₁ hm₂
      apply hne; ext i
      have h1 := Finset.mem_Ioc.mp (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hm₁).1 i)
      have h2 := Finset.mem_Ioc.mp (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hm₂).1 i)
      have hadd1 : Hgrid K (t₁ i) + Mgrid K (t₁ i) = Hgrid K (t₁ i + 1) := by
        unfold Mgrid; exact Nat.add_sub_cancel' ((Hgrid_strictMono K).monotone (Nat.le_succ _))
      have hadd2 : Hgrid K (t₂ i) + Mgrid K (t₂ i) = Hgrid K (t₂ i + 1) := by
        unfold Mgrid; exact Nat.add_sub_cancel' ((Hgrid_strictMono K).monotone (Nat.le_succ _))
      rw [hadd1] at h1; rw [hadd2] at h2
      by_contra hne_i
      rcases lt_or_gt_of_ne hne_i with hlt | hgt
      · have := (Hgrid_strictMono K).monotone (show t₁ i + 1 ≤ t₂ i by omega); omega
      · have := (Hgrid_strictMono K).monotone (show t₂ i + 1 ≤ t₁ i by omega); omega
    have hsub : V₂.biUnion BoxValid ⊆
        (Fintype.piFinset (fun _ : Fin K => Icc 2 ⌊y⌋₊)).filter
          (fun m => (∏ i : Fin K, (m i : ℝ)) ≤ y / yExp y j) := by
      intro m hm
      rw [Finset.mem_biUnion] at hm
      obtain ⟨t, _, hm⟩ := hm
      rw [Finset.mem_filter] at hm ⊢
      refine ⟨Fintype.mem_piFinset.mpr (fun i => Finset.mem_Icc.mpr ⟨?_, ?_⟩), hm.2⟩
      · have h1 := (Finset.mem_Ioc.mp (Fintype.mem_piFinset.mp hm.1 i)).1
        have h2 := Hgrid_ge_two K (t i); omega
      · have hm2 : ∀ u : Fin K, 1 ≤ m u := fun u => by
          have := (Finset.mem_Ioc.mp (Fintype.mem_piFinset.mp hm.1 u)).1
          have := Hgrid_ge_two K (t u); omega
        have h1 : m i ≤ ∏ u : Fin K, m u := by
          calc m i = m i * 1 := (mul_one _).symm
            _ ≤ m i * ∏ u ∈ (Finset.univ : Finset (Fin K)).erase i, m u :=
                Nat.mul_le_mul_left _ (Finset.one_le_prod' fun u _ => hm2 u)
            _ = ∏ u : Fin K, m u := Finset.mul_prod_erase _ _ (Finset.mem_univ i)
        have hge1 : (1 : ℝ) ≤ yExp y j := by linarith only [hyExp_ge3]
        have h3 : (∏ u : Fin K, (m u : ℝ)) ≤ y :=
          hm.2.trans (by rw [div_le_iff₀ (yExp_pos hy_pos j)]; nlinarith only [hy_pos, hge1])
        exact Nat.le_floor (le_trans (by exact_mod_cast h1) h3)
    rw [← Finset.sum_biUnion hdisj]
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans herr
  have hrankin := rankin_box_sum_bound j l hj hl hlogy_pos hlogy_Tw
  have heta_pos := etaFKL_pos
  have hconst_prod :
      C_sieve * Real.exp (100 * (K + 1 : ℝ)) * (4 * Real.exp 3 * etaFKL) ^ K /
        ((K : ℝ) ^ K * (j : ℝ) ^ (etaFKL * (K : ℝ))) ≤
      (1600 * Real.exp 101) * (1 / 2 : ℝ) ^ K := by
    have hK_pos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
    have hj_pos : (0 : ℝ) < j := by exact_mod_cast hj
    have hKratio : ((K + 1 : ℝ) / (K : ℝ)) ^ K ≤ Real.exp 1 := by
      have h1 : (K + 1 : ℝ) / (K : ℝ) = 1 + 1 / (K : ℝ) := by field_simp [hK_pos.ne']
      rw [h1]
      calc (1 + 1 / (K : ℝ)) ^ K
          ≤ (Real.exp (1 / (K : ℝ))) ^ K :=
            pow_le_pow_left₀ (by positivity) (by linarith only [Real.add_one_le_exp (1 / (K : ℝ))]) K
        _ = Real.exp 1 := by rw [← Real.exp_nat_mul]; congr 1; field_simp [hK_pos.ne']
    have hK_exp : (K + 1 : ℝ) ≤ (Real.exp 1) ^ K := by
      calc (K + 1 : ℝ) ≤ Real.exp (K : ℝ) := by linarith only [Real.add_one_le_exp (K : ℝ)]
        _ = (Real.exp 1) ^ K := by rw [← Real.exp_nat_mul, mul_one]
    have hj_ratio : ((j + 1 : ℝ) / (j : ℝ)) ^ (etaFKL * (K : ℝ)) ≤ (2 : ℝ) ^ K := by
      have hle2 : (j + 1 : ℝ) / (j : ℝ) ≤ 2 := by
        rw [div_le_iff₀ hj_pos]; linarith only [show (1 : ℝ) ≤ j by exact_mod_cast hj]
      have hge1 : (1 : ℝ) ≤ (j + 1 : ℝ) / (j : ℝ) := by
        rw [one_le_div hj_pos]; linarith
      calc ((j + 1 : ℝ) / (j : ℝ)) ^ (etaFKL * (K : ℝ))
          ≤ ((j + 1 : ℝ) / (j : ℝ)) ^ (K : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hge1 (by nlinarith only [etaFKL_le_one, hK_pos])
        _ = ((j + 1 : ℝ) / (j : ℝ)) ^ K := Real.rpow_natCast _ K
        _ ≤ (2 : ℝ) ^ K := pow_le_pow_left₀ (by positivity) hle2 K
    have hj_extra : (j + 1 : ℝ) ^ etaFKL ≤ (Real.exp 1) ^ K := by
      have hj_le_K : (j + 1 : ℝ) ≤ (K + 1 : ℝ) := by
        have : j ≤ K := by show j ≤ j * l; nlinarith only [hl]
        exact_mod_cast (Nat.succ_le_succ this)
      calc (j + 1 : ℝ) ^ etaFKL
          ≤ (j + 1 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith only [hj_pos]) etaFKL_le_one
        _ = j + 1 := Real.rpow_one _
        _ ≤ K + 1 := hj_le_K
        _ ≤ (Real.exp 1) ^ K := hK_exp
    have hbase_le : 400 * Real.exp 100 * Real.exp 1 * Real.exp 1 * 2 * (4 * Real.exp 3 * etaFKL) ≤ 1 / 2 := by
      have h3200 : (3200 : ℝ) ≤ Real.exp 12 := by
        have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
        have hpow : (2 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) h2e 12
        rw [← Real.exp_nat_mul] at hpow
        norm_num at hpow
        linarith only [hpow]
      have hexp_eq : 400 * Real.exp 100 * Real.exp 1 * Real.exp 1 * 2 * (4 * Real.exp 3 * etaFKL) =
          3200 * (Real.exp 105 * etaFKL) := by
        have h105 : Real.exp 100 * Real.exp 1 * Real.exp 1 * Real.exp 3 = Real.exp 105 := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; norm_num
        calc 400 * Real.exp 100 * Real.exp 1 * Real.exp 1 * 2 * (4 * Real.exp 3 * etaFKL)
            = 3200 * ((Real.exp 100 * Real.exp 1 * Real.exp 1 * Real.exp 3) * etaFKL) := by ring
          _ = 3200 * (Real.exp 105 * etaFKL) := by rw [h105]
      rw [hexp_eq]
      calc 3200 * (Real.exp 105 * etaFKL)
          ≤ Real.exp 12 * (Real.exp 105 * etaFKL) :=
            mul_le_mul_of_nonneg_right h3200 (mul_nonneg (Real.exp_pos _).le heta_pos.le)
        _ = Real.exp (-3) := by
            simp only [etaFKL]
            rw [← Real.exp_add, ← Real.exp_add]; norm_num
        _ ≤ 1 / 2 := by
            have h1 : (2 : ℝ) ≤ Real.exp 3 := by linarith only [Real.add_one_le_exp (3 : ℝ)]
            rw [Real.exp_neg, inv_eq_one_div]
            exact one_div_le_one_div_of_le (by norm_num) h1
    have hsplit : C_sieve * Real.exp (100 * (K + 1 : ℝ)) * (4 * Real.exp 3 * etaFKL) ^ K /
          ((K : ℝ) ^ K * (j : ℝ) ^ (etaFKL * (K : ℝ))) =
        (4 * 400 * Real.exp 100) * ((K + 1 : ℝ) / (K : ℝ)) ^ K *
          ((K + 1 : ℝ) * (j + 1 : ℝ) ^ etaFKL * ((j + 1 : ℝ) / (j : ℝ)) ^ (etaFKL * (K : ℝ)) *
            (400 * Real.exp 100 * (4 * Real.exp 3 * etaFKL)) ^ K) := by
      simp only [C_sieve]
      have h1 : (400 * (K + 1 : ℝ)) ^ (K + 1) = 400 * (K + 1 : ℝ) * (400 : ℝ) ^ K * (K + 1 : ℝ) ^ K := by
        rw [pow_succ, mul_pow]; ring
      have h2 : ((j + 1 : ℝ) ^ etaFKL) ^ (K + 1) =
          (j + 1 : ℝ) ^ etaFKL * (j + 1 : ℝ) ^ (etaFKL * (K : ℝ)) := by
        rw [pow_succ, ← Real.rpow_natCast ((j + 1 : ℝ) ^ etaFKL), ← Real.rpow_mul (by positivity)]; ring
      have h3 : Real.exp (100 * (K + 1 : ℝ)) = Real.exp 100 * (Real.exp 100) ^ K := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
      have h4 : ((j + 1 : ℝ) / (j : ℝ)) ^ (etaFKL * (K : ℝ)) =
          (j + 1 : ℝ) ^ (etaFKL * (K : ℝ)) / (j : ℝ) ^ (etaFKL * (K : ℝ)) :=
        Real.div_rpow (by positivity) hj_pos.le _
      rw [h1, h2, h3, h4, div_pow, mul_pow, mul_pow]
      have hKne : (K : ℝ) ^ K ≠ 0 := pow_ne_zero K hK_pos.ne'
      have hjne : (j : ℝ) ^ (etaFKL * (K : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hj_pos _).ne'
      field_simp [hKne, hjne]
      simp only [mul_pow]; ring
    rw [hsplit]
    calc (4 * 400 * Real.exp 100) * ((K + 1 : ℝ) / (K : ℝ)) ^ K *
          ((K + 1 : ℝ) * (j + 1 : ℝ) ^ etaFKL * ((j + 1 : ℝ) / (j : ℝ)) ^ (etaFKL * (K : ℝ)) *
            (400 * Real.exp 100 * (4 * Real.exp 3 * etaFKL)) ^ K)
        ≤ (4 * 400 * Real.exp 100) * Real.exp 1 *
            ((Real.exp 1) ^ K * (Real.exp 1) ^ K * (2 : ℝ) ^ K *
              (400 * Real.exp 100 * (4 * Real.exp 3 * etaFKL)) ^ K) := by
          gcongr
      _ = (1600 * Real.exp 101) *
            (400 * Real.exp 100 * Real.exp 1 * Real.exp 1 * 2 * (4 * Real.exp 3 * etaFKL)) ^ K := by
          rw [show (4 * 400 * Real.exp 100) * Real.exp 1 = 1600 * Real.exp 101 by
            rw [mul_assoc, ← Real.exp_add]; norm_num]
          congr 1; simp only [mul_pow]; ring
      _ ≤ (1600 * Real.exp 101) * (1 / 2 : ℝ) ^ K := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase_le K) (by positivity)
  calc (Q₂.card : ℝ)
      ≤ ∑ t ∈ V₂, ∑ m ∈ BoxValid t,
          (((Icc 1 ⌊y / ∏ i : Fin K, (m i : ℝ)⌋₊).filter
            (fun n => ∀ s ∈ range (K + 1), (chainForm m s n).Prime)).card : ℝ) := hcard_le
    _ ≤ ∑ t ∈ V₂, ∑ m ∈ BoxValid t,
          (C_sieve * (y / (Real.log y) ^ (K + 1)) * (singSeries m / ∏ i : Fin K, (Hgrid K (t i) : ℝ)) +
            2 * (y / ∏ i : Fin K, (m i : ℝ)) ^ ((4 : ℝ) / 5)) :=
        Finset.sum_le_sum (fun t ht => Finset.sum_le_sum (fun m hm => hterm_sieve t ht m hm))
    _ = C_sieve * (y / (Real.log y) ^ (K + 1)) *
          (∑ t ∈ V₂, ∑ m ∈ BoxValid t, (singSeries m / ∏ i : Fin K, (Hgrid K (t i) : ℝ))) +
          ∑ t ∈ V₂, ∑ m ∈ BoxValid t, 2 * (y / ∏ i : Fin K, (m i : ℝ)) ^ ((4 : ℝ) / 5) := by
        simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ C_sieve * (y / (Real.log y) ^ (K + 1)) *
          (Real.exp (100 * (K + 1 : ℝ)) *
            ∑ t ∈ V₂, ∏ i : Fin K, (Mgrid K (t i) : ℝ) / (Hgrid K (t i) : ℝ)) +
          (1 / 2 : ℝ) ^ K * (y / Real.log y) := by
        refine add_le_add ?_ herr_V2
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum hbox_sing
    _ ≤ C_sieve * (y / (Real.log y) ^ (K + 1)) *
          (Real.exp (100 * (K + 1 : ℝ)) *
            ((4 * Real.exp 3 * etaFKL) ^ K * (Real.log y) ^ K /
              ((K : ℝ) ^ K * (j : ℝ) ^ (etaFKL * (K : ℝ))))) +
          (1 / 2 : ℝ) ^ K * (y / Real.log y) := by
        gcongr
    _ = (C_sieve * Real.exp (100 * (K + 1 : ℝ)) * (4 * Real.exp 3 * etaFKL) ^ K /
          ((K : ℝ) ^ K * (j : ℝ) ^ (etaFKL * (K : ℝ)))) * (y / Real.log y) +
          (1 / 2 : ℝ) ^ K * (y / Real.log y) := by
        rw [pow_succ]; field_simp [hlogy_pos.ne']
    _ ≤ (1600 * Real.exp 101) * (1 / 2 : ℝ) ^ K * (y / Real.log y) +
          (1 / 2 : ℝ) ^ K * (y / Real.log y) := by
        gcongr
    _ = (1600 * Real.exp 101 + 1) * (1 / 2 : ℝ) ^ K * (y / Real.log y) := by ring

/- Main theorem of this file: `condensed_chain_bound` (FKL10 Theorem `condensed_chain`) -/

open Classical in
theorem condensed_chain_bound (r l : ℕ) (hr : 1 ≤ r) (hl : 4 ≤ l) :
    ∀ᶠ y : ℝ in atTop,
      (((Icc 1 ⌊y⌋₊).filter (fun p0 => p0.Prime ∧ HasPrimeChain (r * l) p0 (yExp y r))).card : ℝ) ≤
        C_cond * (1 / 2 : ℝ) ^ l * (y / Real.log y) := by
  have hall1 : ∀ᶠ y : ℝ in atTop, ∀ j ∈ Icc 1 r,
      (((Icc 1 ⌊y⌋₊).filter (fun p0 =>
        ∃ p : Fin (j * l + 1) → ℕ, IsPrimeChain (j * l) p ∧ p 0 = p0 ∧
          yExp y j ≤ (p (Fin.last (j * l)) : ℝ) ∧
          ∃ i : Fin (j * l), chainMult p i ≤ AK (j * l))).card : ℝ) ≤
        2 * (1 / 2 : ℝ) ^ (j * l) * (y / Real.log y) := by
    rw [Filter.eventually_all_finset]
    intro j hj
    exact bound_Qj1 j l (Finset.mem_Icc.mp hj).1 hl
  have hall2 : ∀ᶠ y : ℝ in atTop, ∀ j ∈ Icc 1 r,
      (((Icc 1 ⌊y⌋₊).filter (fun p0 =>
        ∃ p : Fin (j * l + 1) → ℕ, IsPrimeChain (j * l) p ∧ p 0 = p0 ∧
          yExp y j ≤ (p (Fin.last (j * l)) : ℝ) ∧
          (∀ a ∈ Ico 1 j, ∀ ha : a * l < j * l + 1, (p ⟨a * l, ha⟩ : ℝ) < yExp y a) ∧
          (∀ i : Fin (j * l), AK (j * l) < chainMult p i))).card : ℝ) ≤
        (1600 * Real.exp 101 + 1) * (1 / 2 : ℝ) ^ (j * l) * (y / Real.log y) := by
    rw [Filter.eventually_all_finset]
    intro j hj
    exact bound_Qj2 j l (Finset.mem_Icc.mp hj).1 hl
  filter_upwards [hall1, hall2, Filter.eventually_ge_atTop (Real.exp 1)] with y h1 h2 hy
  have hy_pos : 0 < y := lt_of_lt_of_le (Real.exp_pos 1) hy
  have hlogy_pos : 0 < Real.log y := by
    have := Real.log_le_log (Real.exp_pos 1) hy; rw [Real.log_exp] at this; linarith
  let Q := (Icc 1 ⌊y⌋₊).filter (fun p0 => p0.Prime ∧ HasPrimeChain (r * l) p0 (yExp y r))
  let Qj1 : ℕ → Finset ℕ := fun j => (Icc 1 ⌊y⌋₊).filter (fun p0 =>
    ∃ p : Fin (j * l + 1) → ℕ, IsPrimeChain (j * l) p ∧ p 0 = p0 ∧
      yExp y j ≤ (p (Fin.last (j * l)) : ℝ) ∧
      ∃ i : Fin (j * l), chainMult p i ≤ AK (j * l))
  let Qj2 : ℕ → Finset ℕ := fun j => (Icc 1 ⌊y⌋₊).filter (fun p0 =>
    ∃ p : Fin (j * l + 1) → ℕ, IsPrimeChain (j * l) p ∧ p 0 = p0 ∧
      yExp y j ≤ (p (Fin.last (j * l)) : ℝ) ∧
      (∀ a ∈ Ico 1 j, ∀ ha : a * l < j * l + 1, (p ⟨a * l, ha⟩ : ℝ) < yExp y a) ∧
      (∀ i : Fin (j * l), AK (j * l) < chainMult p i))
  have hcover : Q ⊆ (Icc 1 r).biUnion (fun j => Qj1 j ∪ Qj2 j) := by
    intro p0 hp0
    rw [Finset.mem_filter] at hp0
    obtain ⟨hp0_Icc, _, p, hp_ch, hp0_eq, hlast_ge⟩ := hp0
    let S := (Icc 1 r).filter (fun j =>
      if hj : j * l < r * l + 1 then yExp y j ≤ (p ⟨j * l, hj⟩ : ℝ) else False)
    have hr_mem : r ∈ S := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hr, le_rfl⟩, ?_⟩
      rw [dif_pos (Nat.lt_succ_self _)]
      simpa [Fin.last] using hlast_ge
    let j := S.min' ⟨r, hr_mem⟩
    have hj_mem : j ∈ S := Finset.min'_mem S ⟨r, hr_mem⟩
    have hj_Icc : j ∈ Icc 1 r := (Finset.mem_filter.mp hj_mem).1
    have hj_le_r : j ≤ r := (Finset.mem_Icc.mp hj_Icc).2
    have hjl_lt : j * l < r * l + 1 := Nat.lt_succ_of_le (Nat.mul_le_mul_right l hj_le_r)
    have hj_ge : yExp y j ≤ (p ⟨j * l, hjl_lt⟩ : ℝ) := by
      have h := (Finset.mem_filter.mp hj_mem).2
      rwa [dif_pos hjl_lt] at h
    have hj_min : ∀ a (ha : a ∈ Ico 1 j),
        (p ⟨a * l, Nat.lt_succ_of_le (Nat.mul_le_mul_right l (le_trans (Finset.mem_Ico.mp ha).2.le hj_le_r))⟩ : ℝ) <
          yExp y a := by
      intro a ha
      by_contra hge; push Not at hge
      have ha_Icc : a ∈ Icc 1 r := Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp ha).1,
        le_trans (Finset.mem_Ico.mp ha).2.le hj_le_r⟩
      have ha_lt_rl : a * l < r * l + 1 := Nat.lt_succ_of_le (Nat.mul_le_mul_right l (Finset.mem_Icc.mp ha_Icc).2)
      have ha_S : a ∈ S := Finset.mem_filter.mpr ⟨ha_Icc, by rw [dif_pos ha_lt_rl]; exact hge⟩
      have hle := Finset.min'_le S a ha_S
      have hlt := (Finset.mem_Ico.mp ha).2
      omega
    let q : Fin (j * l + 1) → ℕ := fun i =>
      p ⟨(i : ℕ), lt_of_lt_of_le i.2 (Nat.succ_le_succ (Nat.mul_le_mul_right l hj_le_r))⟩
    have hq_ch : IsPrimeChain (j * l) q :=
      ⟨fun i => hp_ch.1 _, fun i => hp_ch.2 ⟨(i : ℕ), lt_of_lt_of_le i.2 (Nat.mul_le_mul_right l hj_le_r)⟩⟩
    have hq0 : q 0 = p0 := hp0_eq
    have hqlast : yExp y j ≤ (q (Fin.last (j * l)) : ℝ) := hj_ge
    rw [Finset.mem_biUnion]
    refine ⟨j, hj_Icc, ?_⟩
    by_cases hsmall : ∃ i : Fin (j * l), chainMult q i ≤ AK (j * l)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp0_Icc, q, hq_ch, hq0, hqlast, hsmall⟩)
    · push Not at hsmall
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp0_Icc, q, hq_ch, hq0, hqlast,
        fun a ha _ => hj_min a ha, hsmall⟩)
  have hcard_le : (Q.card : ℝ) ≤ ∑ j ∈ Icc 1 r, (((Qj1 j).card : ℝ) + ((Qj2 j).card : ℝ)) := by
    have hnat : Q.card ≤ ∑ j ∈ Icc 1 r, ((Qj1 j).card + (Qj2 j).card) := by
      calc Q.card
          ≤ ((Icc 1 r).biUnion (fun j => Qj1 j ∪ Qj2 j)).card := Finset.card_le_card hcover
        _ ≤ ∑ j ∈ Icc 1 r, (Qj1 j ∪ Qj2 j).card := Finset.card_biUnion_le
        _ ≤ ∑ j ∈ Icc 1 r, ((Qj1 j).card + (Qj2 j).card) :=
            Finset.sum_le_sum (fun _ _ => Finset.card_union_le _ _)
    exact_mod_cast hnat
  have hgeom : ∑ j ∈ Icc 1 r, (1 / 2 : ℝ) ^ (j * l) ≤ 2 * (1 / 2 : ℝ) ^ l := by
    let q : ℝ := (1 / 2 : ℝ) ^ l
    have hq_le : q ≤ 1 / 2 := by
      calc q = (1 / 2 : ℝ) ^ l := rfl
        _ ≤ (1 / 2 : ℝ) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        _ = 1 / 2 := pow_one _
    have hrew : ∀ j ∈ Icc 1 r, (1 / 2 : ℝ) ^ (j * l) = q ^ j := fun j _ => by
      simp only [q]; rw [mul_comm, pow_mul]
    rw [Finset.sum_congr rfl hrew]
    have hsum_geom : (1 - q) * ∑ j ∈ Icc 1 r, q ^ j = q - q ^ (r + 1) := by
      have hgen : ∀ N : ℕ, 1 ≤ N → (1 - q) * ∑ j ∈ Icc 1 N, q ^ j = q - q ^ (N + 1) := by
        intro N hN
        induction N, hN using Nat.le_induction with
        | base => simp; ring
        | succ n hn ih =>
          rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih, pow_succ]
          ring
      exact hgen r hr
    have h1q : (1 / 2 : ℝ) ≤ 1 - q := by linarith only [hq_le]
    have hsum_nn : 0 ≤ ∑ j ∈ Icc 1 r, q ^ j := Finset.sum_nonneg (fun _ _ => by positivity)
    have hqr_nn : 0 ≤ q ^ (r + 1) := by positivity
    nlinarith only [hsum_geom, h1q, hsum_nn, hqr_nn]
  calc (Q.card : ℝ)
      ≤ ∑ j ∈ Icc 1 r, (((Qj1 j).card : ℝ) + ((Qj2 j).card : ℝ)) := hcard_le
    _ ≤ ∑ j ∈ Icc 1 r, (2 * (1 / 2 : ℝ) ^ (j * l) * (y / Real.log y) +
          (1600 * Real.exp 101 + 1) * (1 / 2 : ℝ) ^ (j * l) * (y / Real.log y)) :=
        Finset.sum_le_sum (fun j hj => add_le_add (h1 j hj) (h2 j hj))
    _ = (1600 * Real.exp 101 + 3) * (y / Real.log y) * ∑ j ∈ Icc 1 r, (1 / 2 : ℝ) ^ (j * l) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
    _ ≤ (1600 * Real.exp 101 + 3) * (y / Real.log y) * (2 * (1 / 2 : ℝ) ^ l) :=
        mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = C_cond * (1 / 2 : ℝ) ^ l * (y / Real.log y) := by unfold C_cond; ring

end

/- ==================== Section 6: Main ==================== -/
section
open scoped BigOperators
open Filter Finset Nat

/- Iterated totient basics and prime/prime-square divisibility -/

lemma totient_iterate_le (k n : ℕ) : Nat.totient^[k] n ≤ n := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (Nat.totient_le _).trans ih

lemma totient_iterate_pos (k n : ℕ) (hn : 1 ≤ n) : 1 ≤ Nat.totient^[k] n := by
  induction k with
  | zero => exact hn
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact Nat.totient_pos.mpr (by omega)

lemma prime_dvd_totient_cases {q m : ℕ} (hq : q.Prime) (hm : 1 ≤ m) (hdvd : q ∣ Nat.totient m) :
    q ^ 2 ∣ m ∨ ∃ r ∈ m.primeFactors, q ∣ r - 1 := by
  rw [Nat.totient_eq_prod_factorization (by omega), Finsupp.prod] at hdvd
  obtain ⟨r, hr_supp, hqr⟩ := (hq.prime.dvd_finsetProd_iff _).mp hdvd
  have hr_pf : r ∈ m.primeFactors := by rwa [Nat.support_factorization] at hr_supp
  have hr_pr : r.Prime := Nat.prime_of_mem_primeFactors hr_pf
  rcases hq.dvd_mul.mp hqr with hpow | hsub
  · left
    have hqr_eq : q = r := (Nat.prime_dvd_prime_iff_eq hq hr_pr).mp (hq.dvd_of_dvd_pow hpow)
    subst hqr_eq
    have hexp_pos : 1 ≤ m.factorization q - 1 := by
      by_contra h0
      have : m.factorization q - 1 = 0 := by omega
      rw [this, pow_zero] at hpow
      exact hq.not_dvd_one hpow
    exact (hq.pow_dvd_iff_le_factorization (by omega)).mpr (by omega)
  · exact Or.inr ⟨r, hr_pf, hsub⟩

lemma prime_sq_dvd_totient_cases {q m : ℕ} (hq : q.Prime) (hm : 1 ≤ m)
    (hdvd : q ^ 2 ∣ Nat.totient m) (hnd : ¬ q ^ 2 ∣ m) :
    (∃ r ∈ m.primeFactors, q ^ 2 ∣ r - 1) ∨
    (∃ r₁ ∈ m.primeFactors, ∃ r₂ ∈ m.primeFactors, r₁ ≠ r₂ ∧ q ∣ r₁ - 1 ∧ q ∣ r₂ - 1) := by
  have hm0 : m ≠ 0 := by omega
  have hphi0 : Nat.totient m ≠ 0 := (Nat.totient_pos.mpr (by omega)).ne'
  have hfac_ge2 : 2 ≤ (Nat.totient m).factorization q :=
    (hq.pow_dvd_iff_le_factorization hphi0).mp hdvd
  have hprod_eq : (Nat.totient m).factorization q =
      ∑ r ∈ m.primeFactors, (r ^ (m.factorization r - 1) * (r - 1)).factorization q := by
    rw [Nat.totient_eq_prod_factorization hm0, Finsupp.prod, Nat.support_factorization]
    have hne : ∀ r ∈ m.primeFactors, r ^ (m.factorization r - 1) * (r - 1) ≠ 0 := by
      intro r hr
      have hr_pr := Nat.prime_of_mem_primeFactors hr
      exact mul_ne_zero (pow_ne_zero _ hr_pr.ne_zero) (by have := hr_pr.two_le; omega)
    rw [Nat.factorization_prod hne, Finsupp.finsetSum_apply]
  have hterm_eq : ∀ r ∈ m.primeFactors,
      (r ^ (m.factorization r - 1) * (r - 1)).factorization q = (r - 1).factorization q := by
    intro r hr
    have hr_pr := Nat.prime_of_mem_primeFactors hr
    have hr1 : r - 1 ≠ 0 := by have := hr_pr.two_le; omega
    rw [Nat.factorization_mul (pow_ne_zero _ hr_pr.ne_zero) hr1, Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hr_pr.factorization]
    by_cases hrq : r = q
    · subst hrq
      have hlt2 : m.factorization r < 2 := by
        by_contra hge; push Not at hge
        exact hnd ((hq.pow_dvd_iff_le_factorization hm0).mpr hge)
      have hsub0 : m.factorization r - 1 = 0 := by omega
      rw [hsub0, zero_mul, zero_add]
    · simp [hrq]
  rw [Finset.sum_congr rfl hterm_eq] at hprod_eq
  have hsum_ge2 : 2 ≤ ∑ r ∈ m.primeFactors, (r - 1).factorization q := by omega
  by_cases hex2 : ∃ r ∈ m.primeFactors, 2 ≤ (r - 1).factorization q
  · left
    obtain ⟨r, hr, h2⟩ := hex2
    have hr_pr := Nat.prime_of_mem_primeFactors hr
    exact ⟨r, hr, (hq.pow_dvd_iff_le_factorization (by have := hr_pr.two_le; omega)).mpr h2⟩
  · right
    push Not at hex2
    let S := m.primeFactors.filter (fun r => 1 ≤ (r - 1).factorization q)
    have hcard_ge2 : 2 ≤ S.card := by
      have hle_card : ∑ r ∈ m.primeFactors, (r - 1).factorization q ≤ S.card := by
        calc ∑ r ∈ m.primeFactors, (r - 1).factorization q
            = ∑ r ∈ S, (r - 1).factorization q := by
              symm; refine Finset.sum_subset (Finset.filter_subset _ _) fun r hr hnot => ?_
              simp only [S, Finset.mem_filter] at hnot
              have h0 : ¬ 1 ≤ (r - 1).factorization q := fun h1 => hnot ⟨hr, h1⟩
              omega
          _ ≤ ∑ _r ∈ S, 1 := Finset.sum_le_sum fun r hr => by
              have := hex2 r (Finset.mem_filter.mp hr).1; omega
          _ = S.card := by simp
      omega
    obtain ⟨r₁, hr₁, r₂, hr₂, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    rw [Finset.mem_filter] at hr₁ hr₂
    have hr₁_pr := Nat.prime_of_mem_primeFactors hr₁.1
    have hr₂_pr := Nat.prime_of_mem_primeFactors hr₂.1
    have hd1 : q ∣ r₁ - 1 := by
      simpa using (hq.pow_dvd_iff_le_factorization (by have := hr₁_pr.two_le; omega)).mpr hr₁.2
    have hd2 : q ∣ r₂ - 1 := by
      simpa using (hq.pow_dvd_iff_le_factorization (by have := hr₂_pr.two_le; omega)).mpr hr₂.2
    exact ⟨r₁, hr₁.1, r₂, hr₂.1, hne, hd1, hd2⟩

/- Tracing a large prime divisor back through `j` totient steps -/

lemma trace_prime_back :
    ∀ (j : ℕ) {n : ℕ}, 1 ≤ n → ∀ (L : ℝ) {p : ℕ}, p.Prime →
      L < (p : ℝ) → p ∣ Nat.totient^[j] n →
      (∃ i < j, ∃ q : ℕ, q.Prime ∧ L < (q : ℝ) ∧ q ^ 2 ∣ Nat.totient^[i] n) ∨
      (∃ c : Fin (j + 1) → ℕ, IsPrimeChain j c ∧ c (Fin.last j) = p ∧ c 0 ∣ n) := by
  intro j
  induction j with
  | zero =>
    intro n _ L p hp _ hdvd
    right
    refine ⟨fun _ => p, ⟨fun _ => hp, fun i => i.elim0⟩, rfl, hdvd⟩
  | succ j ih =>
    intro n hn L p hp hpL hdvd
    rw [Function.iterate_succ_apply'] at hdvd
    rcases prime_dvd_totient_cases hp (totient_iterate_pos j n hn) hdvd with hsq | ⟨r, hr_pf, hpr⟩
    · exact Or.inl ⟨j, Nat.lt_succ_self j, p, hp, hpL, hsq⟩
    · have hr_pr : r.Prime := Nat.prime_of_mem_primeFactors hr_pf
      have hr_dvd : r ∣ Nat.totient^[j] n := Nat.dvd_of_mem_primeFactors hr_pf
      have hp_lt_r : p < r := by
        have hle : p ≤ r - 1 := Nat.le_of_dvd (by have := hr_pr.two_le; omega) hpr
        have := hr_pr.two_le; omega
      have hrL : L < (r : ℝ) := lt_trans hpL (by exact_mod_cast hp_lt_r)
      rcases ih hn L hr_pr hrL hr_dvd with ⟨i, hi, q, hq, hqL, hqsq⟩ | ⟨c, hc_ch, hc_last, hc0⟩
      · exact Or.inl ⟨i, by omega, q, hq, hqL, hqsq⟩
      · right
        let c' : Fin (j + 2) → ℕ := Fin.snoc c p
        refine ⟨c', ⟨?_, ?_⟩, ?_, ?_⟩
        · intro i
          refine Fin.lastCases ?_ ?_ i
          · simp only [c', Fin.snoc_last]; exact hp
          · intro k; simp only [c', Fin.snoc_castSucc]; exact hc_ch.1 k
        · intro i
          refine Fin.lastCases ?_ ?_ i
          · have h1 : c' (Fin.last (j + 1)) = p := by simp [c']
            have h2 : c' (Fin.last j).castSucc = c (Fin.last j) := by simp [c']
            change c' (Fin.last j).succ ∣ c' (Fin.last j).castSucc - 1
            rw [Fin.succ_last, h1, h2, hc_last]
            exact hpr
          · intro k
            simp only [c', ← Fin.castSucc_succ, Fin.snoc_castSucc]
            exact hc_ch.2 k
        · simp [c']
        · have h0 : (0 : Fin (j + 2)) = (0 : Fin (j + 1)).castSucc := rfl
          simp only [c', h0, Fin.snoc_castSucc]
          exact hc0

/- Backward chain reciprocal sum lemma (handles ALL of Category (i)!) -/

def ValidChainFin (X d len : ℕ) : Finset (Fin len → ℕ) :=
  (Fintype.piFinset (fun _ : Fin len => Icc 2 X)).filter (fun c =>
    (∀ h : 0 < len, d ∣ c ⟨len - 1, by omega⟩ - 1) ∧
    ∀ i : Fin len, ∀ hi : (i : ℕ) + 1 < len, c ⟨(i : ℕ) + 1, hi⟩ ∣ c i - 1)

lemma validChainFin_ge_two {X d len : ℕ} {c : Fin len → ℕ}
    (hc : c ∈ ValidChainFin X d len) (i : Fin len) : 2 ≤ c i := by
  simp only [ValidChainFin, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc] at hc
  exact (hc.1 i).1

lemma sum_chain_inv_le (X : ℕ) (hX : 1 ≤ X) :
    ∀ (len d : ℕ), 1 ≤ d →
      ∑ c ∈ ValidChainFin X d len,
        (if h : 0 < len then (1 : ℝ) / (c ⟨0, h⟩ : ℝ) else 1 / (d : ℝ)) ≤
        (Real.log (X : ℝ) + 1) ^ len / (d : ℝ) := by
  intro len
  induction len with
  | zero =>
    intro d hd
    have hcard : ValidChainFin X d 0 = {Fin.elim0} := by
      ext c
      simp only [ValidChainFin, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_singleton]
      constructor
      · intro _; ext i; exact i.elim0
      · rintro rfl; exact ⟨fun i => i.elim0, fun h => by omega, fun i => i.elim0⟩
    rw [hcard, Finset.sum_singleton]
    simp
  | succ len ih =>
    intro d hd
    cases len with
    | zero =>
      -- `len + 1 = 1`: single coordinate `u ∈ Icc 2 X` with `d ∣ u - 1`
      let S := (Icc 1 X).filter (fun u => d ∣ u - 1 ∧ 1 < u)
      have hbij : ∑ c ∈ ValidChainFin X d 1,
            (if h : 0 < 1 then (1 : ℝ) / (c ⟨0, h⟩ : ℝ) else 1 / (d : ℝ)) =
          ∑ u ∈ S, (1 / (u : ℝ)) := by
        refine Finset.sum_bij (fun c _ => c 0) ?_ ?_ ?_ ?_
        · intro c hc
          simp only [ValidChainFin, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc] at hc
          simp only [S, Finset.mem_filter, Finset.mem_Icc]
          have h0 := hc.1 0
          exact ⟨⟨by omega, h0.2⟩, hc.2.1 (by norm_num), by omega⟩
        · intro c₁ _ c₂ _ heq
          ext i; fin_cases i; exact heq
        · intro u hu
          simp only [S, Finset.mem_filter, Finset.mem_Icc] at hu
          refine ⟨fun _ => u, ?_, rfl⟩
          simp only [ValidChainFin, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
          exact ⟨fun _ => ⟨by omega, hu.1.2⟩, fun _ => hu.2.1, fun i hi => by omega⟩
        · intro c _; simp
      rw [hbij, pow_one]
      have h1 := sum_inv_congr_one X d hd
      rwa [max_eq_left (by exact_mod_cast hX : (1 : ℝ) ≤ X)] at h1
    | succ len =>
      -- `len + 2`: split into `c' : Fin (len + 1) → ℕ` and `u = c 0` with `c' 0 ∣ u - 1`
      let S_u : (Fin (len + 1) → ℕ) → Finset ℕ := fun c' =>
        (Icc 1 X).filter (fun u => c' 0 ∣ u - 1 ∧ 1 < u)
      have hbij : ∑ c ∈ ValidChainFin X d (len + 2),
            (if h : 0 < len + 2 then (1 : ℝ) / (c ⟨0, h⟩ : ℝ) else 1 / (d : ℝ)) =
          ∑ c' ∈ ValidChainFin X d (len + 1), ∑ u ∈ S_u c', (1 / (u : ℝ)) := by
        rw [Finset.sum_sigma' (ValidChainFin X d (len + 1)) S_u (fun _ u => (1 : ℝ) / (u : ℝ))]
        refine Finset.sum_bij (fun c _ => ⟨fun i => c i.succ, c 0⟩) ?_ ?_ ?_ ?_
        · intro c hc
          simp only [ValidChainFin, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc] at hc
          rw [Finset.mem_sigma]
          refine ⟨?_, ?_⟩
          · simp only [ValidChainFin, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
            refine ⟨fun i => hc.1 i.succ, fun _ => hc.2.1 (by omega),
              fun i hi => hc.2.2 i.succ (by simp only [Fin.val_succ]; omega)⟩
          · simp only [S_u, Finset.mem_filter, Finset.mem_Icc]
            have h0 := hc.1 0
            exact ⟨⟨by omega, h0.2⟩, hc.2.2 0 (by simp), by omega⟩
        · intro c₁ _ c₂ _ heq
          have h1 : (fun i : Fin (len + 1) => c₁ i.succ) = (fun i : Fin (len + 1) => c₂ i.succ) :=
            congrArg Sigma.fst heq
          have h2 : c₁ 0 = c₂ 0 := by
            have := Sigma.mk.inj_iff.mp heq
            exact eq_of_heq this.2
          ext i
          refine Fin.cases h2 (fun k => congrFun h1 k) i
        · intro ⟨c', u⟩ hcu
          rw [Finset.mem_sigma] at hcu
          simp only [ValidChainFin, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc] at hcu
          simp only [S_u, Finset.mem_filter, Finset.mem_Icc] at hcu
          let c : Fin (len + 2) → ℕ := Fin.cons u c'
          refine ⟨c, ?_, ?_⟩
          · simp only [ValidChainFin, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
            refine ⟨fun i => Fin.cases (by simp only [c, Fin.cons_zero]; exact ⟨by omega, hcu.2.1.2⟩)
                (fun k => by simp only [c, Fin.cons_succ]; exact hcu.1.1 k) i,
              fun _ => by
                have heq : (⟨len + 2 - 1, by omega⟩ : Fin (len + 2)) = (⟨len + 1 - 1, by omega⟩ : Fin (len + 1)).succ := by
                  ext; simp
                rw [heq]; simp only [c, Fin.cons_succ]; exact hcu.1.2.1 (by omega),
              fun i => Fin.cases
                (fun _ => by
                  have h1 : (⟨(0 : Fin (len + 2)).val + 1, by omega⟩ : Fin (len + 2)) = (0 : Fin (len + 1)).succ := by
                    ext; simp
                  rw [h1]; simp only [c, Fin.cons_succ, Fin.cons_zero]; exact hcu.2.2.1)
                (fun k hk => by
                  have hk' : (k : ℕ) + 1 < len + 1 := by simp only [Fin.val_succ] at hk; omega
                  have h1 : (⟨k.succ.val + 1, hk⟩ : Fin (len + 2)) = (⟨(k : ℕ) + 1, hk'⟩ : Fin (len + 1)).succ := by
                    ext; simp
                  rw [h1]; simp only [c, Fin.cons_succ]; exact hcu.1.2.2 k hk') i⟩
          · refine Sigma.ext (funext fun k => by simp only [c, Fin.cons_succ])
              (heq_of_eq (show c 0 = u by simp only [c, Fin.cons_zero]))
        · intro c _; simp
      rw [hbij]
      have hinner : ∀ c' ∈ ValidChainFin X d (len + 1),
          ∑ u ∈ S_u c', (1 / (u : ℝ)) ≤ (Real.log (X : ℝ) + 1) * (1 / (c' 0 : ℝ)) := by
        intro c' hc'
        have hc'0 : 2 ≤ c' 0 := validChainFin_ge_two hc' 0
        have h1 := sum_inv_congr_one X (c' 0) (by omega)
        rw [max_eq_left (by exact_mod_cast hX : (1 : ℝ) ≤ X)] at h1
        simpa [div_eq_mul_inv] using h1
      have hlog_nn : 0 ≤ Real.log (X : ℝ) + 1 := by
        have : (1 : ℝ) ≤ X := by exact_mod_cast hX
        linarith [Real.log_nonneg this]
      calc ∑ c' ∈ ValidChainFin X d (len + 1), ∑ u ∈ S_u c', (1 / (u : ℝ))
          ≤ ∑ c' ∈ ValidChainFin X d (len + 1), (Real.log (X : ℝ) + 1) * (1 / (c' 0 : ℝ)) :=
            Finset.sum_le_sum hinner
        _ = (Real.log (X : ℝ) + 1) *
              ∑ c' ∈ ValidChainFin X d (len + 1),
                (if h : 0 < len + 1 then (1 : ℝ) / (c' ⟨0, h⟩ : ℝ) else 1 / (d : ℝ)) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun c' _ => by simp
        _ ≤ (Real.log (X : ℝ) + 1) * ((Real.log (X : ℝ) + 1) ^ (len + 1) / (d : ℝ)) :=
            mul_le_mul_of_nonneg_left (ih d hd) hlog_nn
        _ = (Real.log (X : ℝ) + 1) ^ (len + 2) / (d : ℝ) := by rw [_root_.pow_succ']; ring

/- Helper: count of multiples of `d` in `Icc 1 X` is `≤ X / d` -/

lemma card_Icc_dvd_le (X d : ℕ) (hd : 1 ≤ d) :
    (((Icc 1 X).filter (d ∣ ·)).card : ℝ) ≤ (X : ℝ) / (d : ℝ) := by
  have hnat : ((Icc 1 X).filter (d ∣ ·)).card ≤ X / d := by
    have hcard := Finset.card_le_card_of_injOn (fun n => n / d)
      (s := (Icc 1 X).filter (d ∣ ·)) (t := Icc 1 (X / d))
      (fun n hn => by
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
        obtain ⟨⟨hn1, hnX⟩, k, rfl⟩ := hn
        have hk1 : 1 ≤ k := by rcases eq_or_ne k 0 with rfl | _ <;> omega
        rw [Nat.mul_div_cancel_left k (by omega)]
        exact ⟨hk1, (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; exact hnX)⟩)
      (fun a ha b hb heq => by
        simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
        have := congrArg (d * ·) heq
        rwa [Nat.mul_div_cancel' ha.2, Nat.mul_div_cancel' hb.2] at this)
    simpa [Nat.card_Icc] using hcard
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast hd
  calc (((Icc 1 X).filter (d ∣ ·)).card : ℝ)
      ≤ ((X / d : ℕ) : ℝ) := by exact_mod_cast hnat
    _ ≤ (X : ℝ) / (d : ℝ) := by
        rw [le_div_iff₀ hd_pos]; exact_mod_cast Nat.div_mul_le_self X d

/- Category (i) bound: `q ^ 2 ∣ φ^[j](n)` for some `j < k` and `q > x ^ δ` -/

open Classical in
lemma category_i_bound_fixed_j (X L : ℕ) (hX : 1 ≤ X) (hL : 1 ≤ L) (j : ℕ) :
    let CatI_j := (Icc 1 X).filter (fun n =>
      (∃ q : ℕ, q.Prime ∧ L < q ∧ q ^ 2 ∣ Nat.totient^[j] n) ∧
      ∀ i < j, ¬ ∃ q : ℕ, q.Prime ∧ L < q ∧ q ^ 2 ∣ Nat.totient^[i] n)
    (CatI_j.card : ℝ) ≤ ((j + 2 : ℕ) : ℝ) * (X : ℝ) * (Real.log (X : ℝ) + 1) ^ (2 * j) / (L : ℝ) := by
  intro CatI_j
  have hlog_ge1 : (1 : ℝ) ≤ Real.log (X : ℝ) + 1 := by
    have : (1 : ℝ) ≤ X := by exact_mod_cast hX
    linarith [Real.log_nonneg this]
  cases j with
  | zero =>
    have hcover : CatI_j ⊆ (Icc (L + 1) X).biUnion (fun q => (Icc 1 X).filter (q ^ 2 ∣ ·)) := by
      intro n hn
      simp only [CatI_j, Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨hn1, hnX⟩, ⟨q, hq, hqL, hqsq⟩, _⟩ := hn
      simp only [Function.iterate_zero_apply] at hqsq
      have hq_le_X : q ≤ X := by
        have h1 : q ^ 2 ≤ n := Nat.le_of_dvd (by omega) hqsq
        have h2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
        omega
      exact Finset.mem_biUnion.mpr ⟨q, Finset.mem_Icc.mpr ⟨by omega, hq_le_X⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn1, hnX⟩, hqsq⟩⟩
    have hcard : (CatI_j.card : ℝ) ≤ ∑ q ∈ Icc (L + 1) X, (((Icc 1 X).filter (q ^ 2 ∣ ·)).card : ℝ) := by
      have hnat : CatI_j.card ≤ ∑ q ∈ Icc (L + 1) X, ((Icc 1 X).filter (q ^ 2 ∣ ·)).card :=
        (Finset.card_le_card hcover).trans Finset.card_biUnion_le
      exact_mod_cast hnat
    calc (CatI_j.card : ℝ)
        ≤ ∑ q ∈ Icc (L + 1) X, (((Icc 1 X).filter (q ^ 2 ∣ ·)).card : ℝ) := hcard
      _ ≤ ∑ q ∈ Icc (L + 1) X, (X : ℝ) / ((q ^ 2 : ℕ) : ℝ) :=
          Finset.sum_le_sum fun q hq => card_Icc_dvd_le X (q ^ 2)
            (Nat.one_le_pow 2 q (by have := (Finset.mem_Icc.mp hq).1; omega))
      _ = (X : ℝ) * ∑ q ∈ Icc (L + 1) X, (1 / (q : ℝ) ^ 2) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun q _ => by push_cast; ring
      _ ≤ (X : ℝ) * (1 / (L : ℝ)) := mul_le_mul_of_nonneg_left (sum_inv_sq_tail L X hL) (by positivity)
      _ ≤ ((0 + 2 : ℕ) : ℝ) * (X : ℝ) * (Real.log (X : ℝ) + 1) ^ (2 * 0) / (L : ℝ) := by
          simp only [Nat.zero_add, Nat.mul_zero, pow_zero, mul_one, Nat.cast_ofNat]
          rw [mul_one_div]
          have : (0 : ℝ) ≤ (X : ℝ) / (L : ℝ) := by positivity
          linarith only [this, show (2 : ℝ) * (X : ℝ) / (L : ℝ) = 2 * ((X : ℝ) / (L : ℝ)) by ring]
  | succ m =>
    -- Split `CatI_j` into subcase (a), subcase (b1), and subcase (b2, t) for `t : Fin m`!
    let SubA := (Icc (L + 1) X).biUnion (fun q =>
      (ValidChainFin X (q ^ 2) (m + 1)).biUnion (fun c =>
        (Icc 1 X).filter (c 0 ∣ ·)))
    let SubB1 := (Icc (L + 1) X).biUnion (fun q =>
      (ValidChainFin X q (m + 1)).biUnion (fun c₁ =>
        (ValidChainFin X q (m + 1)).biUnion (fun c₂ =>
          (Icc 1 X).filter (c₁ 0 * c₂ 0 ∣ ·))))
    let SubB2 : Fin m → Finset ℕ := fun t =>
      (Icc (L + 1) X).biUnion (fun q =>
        (ValidChainFin X q (m - (t : ℕ))).biUnion (fun c₁ =>
          (ValidChainFin X q (m - (t : ℕ))).biUnion (fun c₂ =>
            (ValidChainFin X (c₁ ⟨0, by omega⟩ * c₂ ⟨0, by omega⟩) ((t : ℕ) + 1)).biUnion (fun c₀ =>
              (Icc 1 X).filter (c₀ 0 ∣ ·)))))
    have hcover : CatI_j ⊆ SubA ∪ SubB1 ∪ (Finset.univ : Finset (Fin m)).biUnion SubB2 := by
      intro n hn
      simp only [CatI_j, Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨hn1, hnX⟩, ⟨q, hq, hqL, hqsq⟩, hmin⟩ := hn
      rw [Function.iterate_succ_apply'] at hqsq
      have hnd_m : ¬ q ^ 2 ∣ Nat.totient^[m] n := fun hd =>
        hmin m (Nat.lt_succ_self m) ⟨q, hq, hqL, hd⟩
      have hq_le_X : q ≤ X := by
        have h1 : q ^ 2 ≤ Nat.totient (Nat.totient^[m] n) :=
          Nat.le_of_dvd (Nat.totient_pos.mpr (totient_iterate_pos m n hn1)) hqsq
        have h2 : Nat.totient (Nat.totient^[m] n) ≤ n := by
          rw [← Function.iterate_succ_apply' Nat.totient]; exact totient_iterate_le (m + 1) n
        have h3 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
        omega
      have hq_mem : q ∈ Icc (L + 1) X := Finset.mem_Icc.mpr ⟨by omega, hq_le_X⟩
      have hno_prev : ∀ i < m, ¬ ∃ q' : ℕ, q'.Prime ∧ (L : ℝ) < (q' : ℝ) ∧ q' ^ 2 ∣ Nat.totient^[i] n := by
        intro i hi ⟨q', hq', hq'L, hq'sq⟩
        exact hmin i (by omega) ⟨q', hq', by exact_mod_cast hq'L, hq'sq⟩
      -- Helper: convert `c : Fin (m + 1) → ℕ` prime chain with `c 0 ∣ n` and `d ∣ c m - 1` into `ValidChainFin`
      have hchain_mem : ∀ (d : ℕ) (c : Fin (m + 1) → ℕ),
          IsPrimeChain m c → c 0 ∣ n → d ∣ c (Fin.last m) - 1 → c ∈ ValidChainFin X d (m + 1) := by
        intro d c hc_ch hc0 hd
        refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun i => Finset.mem_Icc.mpr ⟨(hc_ch.1 i).two_le, ?_⟩),
          fun _ => hd, fun i hi => hc_ch.2 ⟨(i : ℕ), by omega⟩⟩
        have hle0 : c i ≤ c 0 := by
          by_cases hi0 : i = 0
          · subst hi0; exact le_rfl
          · exact (isPrimeChain_strictAnti hc_ch (Fin.pos_of_ne_zero hi0)).le
        have h0n : c 0 ≤ n := Nat.le_of_dvd (by omega) hc0
        omega
      rcases prime_sq_dvd_totient_cases hq (totient_iterate_pos m n hn1) hqsq hnd_m with
        ⟨r, hr_pf, hq2r⟩ | ⟨r₁, hr₁_pf, r₂, hr₂_pf, hr_ne, hqr₁, hqr₂⟩
      · -- Subcase (a)
        have hr_pr : r.Prime := Nat.prime_of_mem_primeFactors hr_pf
        have hr_dvd : r ∣ Nat.totient^[m] n := Nat.dvd_of_mem_primeFactors hr_pf
        have hrL : (L : ℝ) < (r : ℝ) := by
          have h1 : q ^ 2 ≤ r - 1 := Nat.le_of_dvd (by have := hr_pr.two_le; omega) hq2r
          have h2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
          have := hr_pr.two_le
          exact_mod_cast (show L < r by omega)
        have htr := (trace_prime_back m hn1 (L : ℝ) hr_pr hrL hr_dvd).resolve_left (fun ⟨i, hi, ex⟩ => hno_prev i hi ex)
        obtain ⟨c, hc_ch, hc_last, hc0⟩ := htr
        rw [Finset.mem_union, Finset.mem_union]
        left; left
        refine Finset.mem_biUnion.mpr ⟨q, hq_mem, Finset.mem_biUnion.mpr
          ⟨c, hchain_mem (q ^ 2) c hc_ch hc0 (hc_last.symm ▸ hq2r),
            Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn1, hnX⟩, hc0⟩⟩⟩
      · -- Subcase (b): trace both `r₁` and `r₂`
        have hr₁_pr : r₁.Prime := Nat.prime_of_mem_primeFactors hr₁_pf
        have hr₂_pr : r₂.Prime := Nat.prime_of_mem_primeFactors hr₂_pf
        have hr₁L : (L : ℝ) < (r₁ : ℝ) := by
          have h1 : q ≤ r₁ - 1 := Nat.le_of_dvd (by have := hr₁_pr.two_le; omega) hqr₁
          have := hr₁_pr.two_le; exact_mod_cast (show L < r₁ by omega)
        have hr₂L : (L : ℝ) < (r₂ : ℝ) := by
          have h1 : q ≤ r₂ - 1 := Nat.le_of_dvd (by have := hr₂_pr.two_le; omega) hqr₂
          have := hr₂_pr.two_le; exact_mod_cast (show L < r₂ by omega)
        obtain ⟨c₁, hc₁_ch, hc₁_last, hc₁0⟩ :=
          (trace_prime_back m hn1 (L : ℝ) hr₁_pr hr₁L (Nat.dvd_of_mem_primeFactors hr₁_pf)).resolve_left
            (fun ⟨i, hi, ex⟩ => hno_prev i hi ex)
        obtain ⟨c₂, hc₂_ch, hc₂_last, hc₂0⟩ :=
          (trace_prime_back m hn1 (L : ℝ) hr₂_pr hr₂L (Nat.dvd_of_mem_primeFactors hr₂_pf)).resolve_left
            (fun ⟨i, hi, ex⟩ => hno_prev i hi ex)
        by_cases h0eq : c₁ 0 = c₂ 0
        · -- Subcase (b2): find largest `t < m` where `c₁ t = c₂ t`
          let S_eq := (Finset.univ : Finset (Fin (m + 1))).filter (fun i => c₁ i = c₂ i)
          have h0_mem : (0 : Fin (m + 1)) ∈ S_eq := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0eq⟩
          let t0 := S_eq.max' ⟨0, h0_mem⟩
          have ht0_mem : t0 ∈ S_eq := Finset.max'_mem S_eq ⟨0, h0_mem⟩
          have ht0_eq : c₁ t0 = c₂ t0 := (Finset.mem_filter.mp ht0_mem).2
          have ht0_lt : (t0 : ℕ) < m := by
            by_contra hge
            have heq_last : t0 = Fin.last m := Fin.ext (by simp only [Fin.val_last]; have := t0.2; omega)
            rw [heq_last, hc₁_last, hc₂_last] at ht0_eq
            exact hr_ne ht0_eq
          let t : Fin m := ⟨(t0 : ℕ), ht0_lt⟩
          have hsucc_ne : c₁ ⟨(t : ℕ) + 1, by omega⟩ ≠ c₂ ⟨(t : ℕ) + 1, by omega⟩ := by
            intro heq
            have hmem : (⟨(t : ℕ) + 1, by omega⟩ : Fin (m + 1)) ∈ S_eq :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩
            have hle := Finset.le_max' S_eq _ hmem
            have hval : (t : ℕ) = (t0 : ℕ) := rfl
            simp only [Fin.le_def] at hle
            omega
          have hcop : (c₁ ⟨(t : ℕ) + 1, by omega⟩).Coprime (c₂ ⟨(t : ℕ) + 1, by omega⟩) :=
            (Nat.coprime_primes (hc₁_ch.1 _) (hc₂_ch.1 _)).mpr hsucc_ne
          have hmul_dvd : c₁ ⟨(t : ℕ) + 1, by omega⟩ * c₂ ⟨(t : ℕ) + 1, by omega⟩ ∣
              c₁ ⟨(t : ℕ), by omega⟩ - 1 := by
            have hd1 : c₁ ⟨(t : ℕ) + 1, by omega⟩ ∣ c₁ ⟨(t : ℕ), by omega⟩ - 1 := hc₁_ch.2 t
            have hd2 : c₂ ⟨(t : ℕ) + 1, by omega⟩ ∣ c₁ ⟨(t : ℕ), by omega⟩ - 1 := by
              have hteq : (⟨(t : ℕ), by omega⟩ : Fin (m + 1)) = t0 := rfl
              rw [hteq, ht0_eq]; exact hc₂_ch.2 t
            exact hcop.mul_dvd_of_dvd_of_dvd hd1 hd2
          -- Build slices `c₁'`, `c₂' : Fin (m - t) → ℕ` and `c₀' : Fin (t + 1) → ℕ`
          let c₁' : Fin (m - (t : ℕ)) → ℕ := fun i => c₁ ⟨(t : ℕ) + 1 + (i : ℕ), by omega⟩
          let c₂' : Fin (m - (t : ℕ)) → ℕ := fun i => c₂ ⟨(t : ℕ) + 1 + (i : ℕ), by omega⟩
          let c₀' : Fin ((t : ℕ) + 1) → ℕ := fun i => c₁ ⟨(i : ℕ), by omega⟩
          have hc₁'_mem : c₁' ∈ ValidChainFin X q (m - (t : ℕ)) := by
            refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun i => Finset.mem_Icc.mpr
              ⟨(hc₁_ch.1 _).two_le, ?_⟩), fun _ => ?_, fun i hi => ?_⟩
            · have hle0 : c₁ ⟨(t : ℕ) + 1 + (i : ℕ), by omega⟩ ≤ c₁ 0 :=
                (isPrimeChain_strictAnti hc₁_ch (Fin.lt_def.mpr (by dsimp; omega))).le
              have h0n : c₁ 0 ≤ n := Nat.le_of_dvd (by omega) hc₁0
              exact hle0.trans (h0n.trans hnX)
            · have hlast_eq : (⟨(t : ℕ) + 1 + (m - (t : ℕ) - 1), by omega⟩ : Fin (m + 1)) = Fin.last m := by
                ext; simp [Fin.last]; omega
              simp only [c₁', hlast_eq, hc₁_last]; exact hqr₁
            · exact hc₁_ch.2 ⟨(t : ℕ) + 1 + (i : ℕ), by omega⟩
          have hc₂'_mem : c₂' ∈ ValidChainFin X q (m - (t : ℕ)) := by
            refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun i => Finset.mem_Icc.mpr
              ⟨(hc₂_ch.1 _).two_le, ?_⟩), fun _ => ?_, fun i hi => ?_⟩
            · have hle0 : c₂ ⟨(t : ℕ) + 1 + (i : ℕ), by omega⟩ ≤ c₂ 0 :=
                (isPrimeChain_strictAnti hc₂_ch (Fin.lt_def.mpr (by dsimp; omega))).le
              have h0n : c₂ 0 ≤ n := Nat.le_of_dvd (by omega) hc₂0
              exact hle0.trans (h0n.trans hnX)
            · have hlast_eq : (⟨(t : ℕ) + 1 + (m - (t : ℕ) - 1), by omega⟩ : Fin (m + 1)) = Fin.last m := by
                ext; simp [Fin.last]; omega
              simp only [c₂', hlast_eq, hc₂_last]; exact hqr₂
            · exact hc₂_ch.2 ⟨(t : ℕ) + 1 + (i : ℕ), by omega⟩
          have hc₀'_mem : c₀' ∈ ValidChainFin X (c₁' ⟨0, by omega⟩ * c₂' ⟨0, by omega⟩) ((t : ℕ) + 1) := by
            refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun i => Finset.mem_Icc.mpr
              ⟨(hc₁_ch.1 _).two_le, ?_⟩), fun _ => ?_, fun i hi => hc₁_ch.2 ⟨(i : ℕ), by omega⟩⟩
            · have hle0 : c₁ ⟨(i : ℕ), by omega⟩ ≤ c₁ 0 := by
                by_cases hi0 : (i : ℕ) = 0
                · have : (⟨(i : ℕ), by omega⟩ : Fin (m + 1)) = 0 := Fin.ext hi0; rw [this]
                · exact (isPrimeChain_strictAnti hc₁_ch (Fin.lt_def.mpr (by dsimp; omega))).le
              have h0n : c₁ 0 ≤ n := Nat.le_of_dvd (by omega) hc₁0
              exact hle0.trans (h0n.trans hnX)
            · simpa [c₁', c₂', c₀'] using hmul_dvd
          rw [Finset.mem_union]
          right
          refine Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨q, hq_mem,
            Finset.mem_biUnion.mpr ⟨c₁', hc₁'_mem, Finset.mem_biUnion.mpr ⟨c₂', hc₂'_mem,
              Finset.mem_biUnion.mpr ⟨c₀', hc₀'_mem, Finset.mem_filter.mpr
                ⟨Finset.mem_Icc.mpr ⟨hn1, hnX⟩, hc₁0⟩⟩⟩⟩⟩⟩
        · -- Subcase (b1): `c₁ 0 ≠ c₂ 0`, so `c₁ 0 * c₂ 0 ∣ n`
          have hcop : (c₁ 0).Coprime (c₂ 0) :=
            (Nat.coprime_primes (hc₁_ch.1 0) (hc₂_ch.1 0)).mpr h0eq
          have hmul_dvd : c₁ 0 * c₂ 0 ∣ n := hcop.mul_dvd_of_dvd_of_dvd hc₁0 hc₂0
          rw [Finset.mem_union, Finset.mem_union]
          left; right
          exact Finset.mem_biUnion.mpr ⟨q, hq_mem, Finset.mem_biUnion.mpr
            ⟨c₁, hchain_mem q c₁ hc₁_ch hc₁0 (hc₁_last.symm ▸ hqr₁),
              Finset.mem_biUnion.mpr ⟨c₂, hchain_mem q c₂ hc₂_ch hc₂0 (hc₂_last.symm ▸ hqr₂),
                Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn1, hnX⟩, hmul_dvd⟩⟩⟩⟩
    -- Bound each of `SubA`, `SubB1`, `SubB2 t` using `sum_chain_inv_le`!
    have hSubA : (SubA.card : ℝ) ≤ (X : ℝ) * (Real.log (X : ℝ) + 1) ^ (2 * (m + 1)) / (L : ℝ) := by
      have hcard : (SubA.card : ℝ) ≤ ∑ q ∈ Icc (L + 1) X, ∑ c ∈ ValidChainFin X (q ^ 2) (m + 1),
          (((Icc 1 X).filter (c 0 ∣ ·)).card : ℝ) := by
        have hnat : SubA.card ≤ ∑ q ∈ Icc (L + 1) X, ∑ c ∈ ValidChainFin X (q ^ 2) (m + 1),
            ((Icc 1 X).filter (c 0 ∣ ·)).card :=
          Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun _ _ => Finset.card_biUnion_le))
        exact_mod_cast hnat
      calc (SubA.card : ℝ)
          ≤ ∑ q ∈ Icc (L + 1) X, ∑ c ∈ ValidChainFin X (q ^ 2) (m + 1),
              (((Icc 1 X).filter (c 0 ∣ ·)).card : ℝ) := hcard
        _ ≤ ∑ q ∈ Icc (L + 1) X, ∑ c ∈ ValidChainFin X (q ^ 2) (m + 1),
              ((X : ℝ) * (if h : 0 < m + 1 then (1 : ℝ) / (c ⟨0, h⟩ : ℝ) else 1 / ((q ^ 2 : ℕ) : ℝ))) := by
            refine Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun c hc => ?_
            have hc0 : 1 ≤ c 0 := by have := validChainFin_ge_two hc 0; omega
            simp only [Nat.pos_of_ne_zero (Nat.succ_ne_zero m), ↓reduceDIte, mul_one_div]
            exact card_Icc_dvd_le X (c 0) hc0
        _ = (X : ℝ) * ∑ q ∈ Icc (L + 1) X, ∑ c ∈ ValidChainFin X (q ^ 2) (m + 1),
              (if h : 0 < m + 1 then (1 : ℝ) / (c ⟨0, h⟩ : ℝ) else 1 / ((q ^ 2 : ℕ) : ℝ)) := by
            simp_rw [← Finset.mul_sum]
        _ ≤ (X : ℝ) * ∑ q ∈ Icc (L + 1) X, ((Real.log (X : ℝ) + 1) ^ (m + 1) / ((q ^ 2 : ℕ) : ℝ)) := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun q hq => sum_chain_inv_le X hX (m + 1) (q ^ 2)
              (Nat.one_le_pow 2 q (by have := (Finset.mem_Icc.mp hq).1; omega))) (by positivity)
        _ = (X : ℝ) * (Real.log (X : ℝ) + 1) ^ (m + 1) * ∑ q ∈ Icc (L + 1) X, (1 / (q : ℝ) ^ 2) := by
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun q _ => by push_cast; ring
        _ ≤ (X : ℝ) * (Real.log (X : ℝ) + 1) ^ (m + 1) * (1 / (L : ℝ)) :=
            mul_le_mul_of_nonneg_left (sum_inv_sq_tail L X hL) (by positivity)
        _ ≤ (X : ℝ) * (Real.log (X : ℝ) + 1) ^ (2 * (m + 1)) / (L : ℝ) := by
            rw [mul_one_div]
            refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
              (pow_le_pow_right₀ hlog_ge1 (by omega)) (by positivity)) (by positivity)
    have hSubB1 : (SubB1.card : ℝ) ≤ (X : ℝ) * (Real.log (X : ℝ) + 1) ^ (2 * (m + 1)) / (L : ℝ) := by
      have hcard : (SubB1.card : ℝ) ≤ ∑ q ∈ Icc (L + 1) X,
          ∑ c₁ ∈ ValidChainFin X q (m + 1), ∑ c₂ ∈ ValidChainFin X q (m + 1),
            (((Icc 1 X).filter (c₁ 0 * c₂ 0 ∣ ·)).card : ℝ) := by
        have hnat : SubB1.card ≤ ∑ q ∈ Icc (L + 1) X,
            ∑ c₁ ∈ ValidChainFin X q (m + 1), ∑ c₂ ∈ ValidChainFin X q (m + 1),
              ((Icc 1 X).filter (c₁ 0 * c₂ 0 ∣ ·)).card :=
          Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ =>
            Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le))
        exact_mod_cast hnat
      calc (SubB1.card : ℝ)
          ≤ ∑ q ∈ Icc (L + 1) X, ∑ c₁ ∈ ValidChainFin X q (m + 1), ∑ c₂ ∈ ValidChainFin X q (m + 1),
              (((Icc 1 X).filter (c₁ 0 * c₂ 0 ∣ ·)).card : ℝ) := hcard
        _ ≤ ∑ q ∈ Icc (L + 1) X, ∑ c₁ ∈ ValidChainFin X q (m + 1), ∑ c₂ ∈ ValidChainFin X q (m + 1),
              ((X : ℝ) * ((if h : 0 < m + 1 then (1 : ℝ) / (c₁ ⟨0, h⟩ : ℝ) else 1 / (q : ℝ)) *
                (if h : 0 < m + 1 then (1 : ℝ) / (c₂ ⟨0, h⟩ : ℝ) else 1 / (q : ℝ)))) := by
            refine Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun c₁ hc₁ => Finset.sum_le_sum fun c₂ hc₂ => ?_
            have h1 : 1 ≤ c₁ 0 := by have := validChainFin_ge_two hc₁ 0; omega
            have h2 : 1 ≤ c₂ 0 := by have := validChainFin_ge_two hc₂ 0; omega
            have hd := card_Icc_dvd_le X (c₁ 0 * c₂ 0) (Nat.mul_pos h1 h2)
            simp only [Nat.pos_of_ne_zero (Nat.succ_ne_zero m), ↓reduceDIte]
            push_cast at hd
            calc (((Icc 1 X).filter (c₁ 0 * c₂ 0 ∣ ·)).card : ℝ)
                ≤ (X : ℝ) / ((c₁ 0 : ℝ) * (c₂ 0 : ℝ)) := hd
              _ = (X : ℝ) * ((1 / (c₁ 0 : ℝ)) * (1 / (c₂ 0 : ℝ))) := by ring
        _ = (X : ℝ) * ∑ q ∈ Icc (L + 1) X,
              (∑ c₁ ∈ ValidChainFin X q (m + 1), (if h : 0 < m + 1 then (1 : ℝ) / (c₁ ⟨0, h⟩ : ℝ) else 1 / (q : ℝ))) *
              (∑ c₂ ∈ ValidChainFin X q (m + 1), (if h : 0 < m + 1 then (1 : ℝ) / (c₂ ⟨0, h⟩ : ℝ) else 1 / (q : ℝ))) := by
            simp_rw [← Finset.mul_sum]; congr 1; refine Finset.sum_congr rfl fun q _ => ?_
            exact (Finset.sum_mul _ _ _).symm
        _ ≤ (X : ℝ) * ∑ q ∈ Icc (L + 1) X,
              ((Real.log (X : ℝ) + 1) ^ (m + 1) / (q : ℝ)) * ((Real.log (X : ℝ) + 1) ^ (m + 1) / (q : ℝ)) := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun q hq => ?_) (by positivity)
            have hq1 : 1 ≤ q := by have := (Finset.mem_Icc.mp hq).1; omega
            exact mul_le_mul (sum_chain_inv_le X hX (m + 1) q hq1) (sum_chain_inv_le X hX (m + 1) q hq1)
              (Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)) (by positivity)
        _ = (X : ℝ) * (Real.log (X : ℝ) + 1) ^ (2 * (m + 1)) * ∑ q ∈ Icc (L + 1) X, (1 / (q : ℝ) ^ 2) := by
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun q _ => ?_
            rw [show 2 * (m + 1) = (m + 1) + (m + 1) by ring, pow_add]; ring
        _ ≤ (X : ℝ) * (Real.log (X : ℝ) + 1) ^ (2 * (m + 1)) * (1 / (L : ℝ)) :=
            mul_le_mul_of_nonneg_left (sum_inv_sq_tail L X hL)
              (show (0 : ℝ) ≤ (X : ℝ) * (Real.log (X : ℝ) + 1) ^ (2 * (m + 1)) by positivity)
        _ = (X : ℝ) * (Real.log (X : ℝ) + 1) ^ (2 * (m + 1)) / (L : ℝ) := by ring
    have hSubB2 : ∀ t : Fin m,
        ((SubB2 t).card : ℝ) ≤ (X : ℝ) * (Real.log (X : ℝ) + 1) ^ (2 * (m + 1)) / (L : ℝ) := by
      intro t
      have ht_lt : (t : ℕ) < m := t.2
      have hcard : ((SubB2 t).card : ℝ) ≤ ∑ q ∈ Icc (L + 1) X,
          ∑ c₁ ∈ ValidChainFin X q (m - (t : ℕ)),
            ∑ c₂ ∈ ValidChainFin X q (m - (t : ℕ)),
              ∑ c₀ ∈ ValidChainFin X (c₁ ⟨0, by omega⟩ * c₂ ⟨0, by omega⟩) ((t : ℕ) + 1),
                (((Icc 1 X).filter (c₀ 0 ∣ ·)).card : ℝ) := by
        have hnat : (SubB2 t).card ≤ ∑ q ∈ Icc (L + 1) X,
            ∑ c₁ ∈ ValidChainFin X q (m - (t : ℕ)),
              ∑ c₂ ∈ ValidChainFin X q (m - (t : ℕ)),
                ∑ c₀ ∈ ValidChainFin X (c₁ ⟨0, by omega⟩ * c₂ ⟨0, by omega⟩) ((t : ℕ) + 1),
                  ((Icc 1 X).filter (c₀ 0 ∣ ·)).card :=
          Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ =>
            Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ =>
              Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le)))
        exact_mod_cast hnat
      have hinner_c0 : ∀ q ∈ Icc (L + 1) X,
          ∀ c₁ ∈ ValidChainFin X q (m - (t : ℕ)), ∀ c₂ ∈ ValidChainFin X q (m - (t : ℕ)),
            ∑ c₀ ∈ ValidChainFin X (c₁ ⟨0, by omega⟩ * c₂ ⟨0, by omega⟩) ((t : ℕ) + 1),
              (((Icc 1 X).filter (c₀ 0 ∣ ·)).card : ℝ) ≤
            (X : ℝ) * (Real.log (X : ℝ) + 1) ^ ((t : ℕ) + 1) *
              ((1 / (c₁ ⟨0, by omega⟩ : ℝ)) * (1 / (c₂ ⟨0, by omega⟩ : ℝ))) := by
        intro q _ c₁ hc₁ c₂ hc₂
        have hc1_pos : 1 ≤ c₁ ⟨0, by omega⟩ := by have := validChainFin_ge_two hc₁ ⟨0, by omega⟩; omega
        have hc2_pos : 1 ≤ c₂ ⟨0, by omega⟩ := by have := validChainFin_ge_two hc₂ ⟨0, by omega⟩; omega
        calc ∑ c₀ ∈ ValidChainFin X (c₁ ⟨0, by omega⟩ * c₂ ⟨0, by omega⟩) ((t : ℕ) + 1),
                (((Icc 1 X).filter (c₀ 0 ∣ ·)).card : ℝ)
            ≤ ∑ c₀ ∈ ValidChainFin X (c₁ ⟨0, by omega⟩ * c₂ ⟨0, by omega⟩) ((t : ℕ) + 1),
                ((X : ℝ) * (if h : 0 < (t : ℕ) + 1 then (1 : ℝ) / (c₀ ⟨0, h⟩ : ℝ) else
                  1 / ((c₁ ⟨0, by omega⟩ * c₂ ⟨0, by omega⟩ : ℕ) : ℝ))) := by
              refine Finset.sum_le_sum fun c₀ hc₀ => ?_
              have hc0_pos : 1 ≤ c₀ 0 := by have := validChainFin_ge_two hc₀ 0; omega
              simp only [Nat.pos_of_ne_zero (Nat.succ_ne_zero _), ↓reduceDIte, mul_one_div]
              exact card_Icc_dvd_le X (c₀ 0) hc0_pos
          _ = (X : ℝ) * ∑ c₀ ∈ ValidChainFin X (c₁ ⟨0, by omega⟩ * c₂ ⟨0, by omega⟩) ((t : ℕ) + 1),
                (if h : 0 < (t : ℕ) + 1 then (1 : ℝ) / (c₀ ⟨0, h⟩ : ℝ) else
                  1 / ((c₁ ⟨0, by omega⟩ * c₂ ⟨0, by omega⟩ : ℕ) : ℝ)) := (Finset.mul_sum _ _ _).symm
          _ ≤ (X : ℝ) * ((Real.log (X : ℝ) + 1) ^ ((t : ℕ) + 1) / ((c₁ ⟨0, by omega⟩ * c₂ ⟨0, by omega⟩ : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left (sum_chain_inv_le X hX ((t : ℕ) + 1) _ (Nat.mul_pos hc1_pos hc2_pos)) (by positivity)
          _ = (X : ℝ) * (Real.log (X : ℝ) + 1) ^ ((t : ℕ) + 1) *
                ((1 / (c₁ ⟨0, by omega⟩ : ℝ)) * (1 / (c₂ ⟨0, by omega⟩ : ℝ))) := by
              push_cast; ring
      calc ((SubB2 t).card : ℝ)
          ≤ ∑ q ∈ Icc (L + 1) X, ∑ c₁ ∈ ValidChainFin X q (m - (t : ℕ)),
              ∑ c₂ ∈ ValidChainFin X q (m - (t : ℕ)),
                ((X : ℝ) * (Real.log (X : ℝ) + 1) ^ ((t : ℕ) + 1) *
                  ((1 / (c₁ ⟨0, by omega⟩ : ℝ)) * (1 / (c₂ ⟨0, by omega⟩ : ℝ)))) :=
            hcard.trans (Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun c₁ hc₁ =>
              Finset.sum_le_sum fun c₂ hc₂ => hinner_c0 q hq c₁ hc₁ c₂ hc₂)
        _ = (X : ℝ) * (Real.log (X : ℝ) + 1) ^ ((t : ℕ) + 1) * ∑ q ∈ Icc (L + 1) X,
              (∑ c₁ ∈ ValidChainFin X q (m - (t : ℕ)),
                (if h : 0 < m - (t : ℕ) then (1 : ℝ) / (c₁ ⟨0, h⟩ : ℝ) else 1 / (q : ℝ))) *
              (∑ c₂ ∈ ValidChainFin X q (m - (t : ℕ)),
                (if h : 0 < m - (t : ℕ) then (1 : ℝ) / (c₂ ⟨0, h⟩ : ℝ) else 1 / (q : ℝ))) := by
            simp_rw [← Finset.mul_sum]; congr 1; refine Finset.sum_congr rfl fun q _ => ?_
            symm; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun c₁ _ => ?_
            simp only [show 0 < m - (t : ℕ) by omega, ↓reduceDIte]
        _ ≤ (X : ℝ) * (Real.log (X : ℝ) + 1) ^ ((t : ℕ) + 1) * ∑ q ∈ Icc (L + 1) X,
              ((Real.log (X : ℝ) + 1) ^ (m - (t : ℕ)) / (q : ℝ)) *
              ((Real.log (X : ℝ) + 1) ^ (m - (t : ℕ)) / (q : ℝ)) := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun q hq => ?_) (by positivity)
            have hq1 : 1 ≤ q := by have := (Finset.mem_Icc.mp hq).1; omega
            exact mul_le_mul (sum_chain_inv_le X hX (m - (t : ℕ)) q hq1)
              (sum_chain_inv_le X hX (m - (t : ℕ)) q hq1)
              (Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)) (by positivity)
        _ = (X : ℝ) * (Real.log (X : ℝ) + 1) ^ (((t : ℕ) + 1) + (m - (t : ℕ)) + (m - (t : ℕ))) *
              ∑ q ∈ Icc (L + 1) X, (1 / (q : ℝ) ^ 2) := by
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun q _ => ?_
            rw [pow_add, pow_add]; ring
        _ ≤ (X : ℝ) * (Real.log (X : ℝ) + 1) ^ (2 * (m + 1)) * (1 / (L : ℝ)) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left
              (pow_le_pow_right₀ hlog_ge1 (by omega)) (by positivity))
              (sum_inv_sq_tail L X hL) (Finset.sum_nonneg (fun _ _ => by positivity)) (by positivity)
        _ = (X : ℝ) * (Real.log (X : ℝ) + 1) ^ (2 * (m + 1)) / (L : ℝ) := by ring
    have hcard_total : (CatI_j.card : ℝ) ≤
        (SubA.card : ℝ) + (SubB1.card : ℝ) + ∑ t : Fin m, ((SubB2 t).card : ℝ) := by
      have hnat : CatI_j.card ≤ SubA.card + SubB1.card + ∑ t : Fin m, (SubB2 t).card := by
        calc CatI_j.card
            ≤ (SubA ∪ SubB1 ∪ (Finset.univ : Finset (Fin m)).biUnion SubB2).card :=
              Finset.card_le_card hcover
          _ ≤ (SubA ∪ SubB1).card + ((Finset.univ : Finset (Fin m)).biUnion SubB2).card :=
              Finset.card_union_le _ _
          _ ≤ (SubA.card + SubB1.card) + ∑ t : Fin m, (SubB2 t).card :=
              Nat.add_le_add (Finset.card_union_le _ _) Finset.card_biUnion_le
      exact_mod_cast hnat
    calc (CatI_j.card : ℝ)
        ≤ (SubA.card : ℝ) + (SubB1.card : ℝ) + ∑ t : Fin m, ((SubB2 t).card : ℝ) := hcard_total
      _ ≤ (X : ℝ) * (Real.log (X : ℝ) + 1) ^ (2 * (m + 1)) / (L : ℝ) +
            (X : ℝ) * (Real.log (X : ℝ) + 1) ^ (2 * (m + 1)) / (L : ℝ) +
            ∑ _t : Fin m, ((X : ℝ) * (Real.log (X : ℝ) + 1) ^ (2 * (m + 1)) / (L : ℝ)) :=
          add_le_add (add_le_add hSubA hSubB1) (Finset.sum_le_sum fun t _ => hSubB2 t)
      _ = ((m + 2 : ℕ) : ℝ) * ((X : ℝ) * (Real.log (X : ℝ) + 1) ^ (2 * (m + 1)) / (L : ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
      _ ≤ ((m + 1 + 2 : ℕ) : ℝ) * ((X : ℝ) * (Real.log (X : ℝ) + 1) ^ (2 * (m + 1)) / (L : ℝ)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast (show m + 2 ≤ m + 1 + 2 by omega)
      _ = ((m + 1 + 2 : ℕ) : ℝ) * (X : ℝ) * (Real.log (X : ℝ) + 1) ^ (2 * (m + 1)) / (L : ℝ) := by ring

open Classical in
lemma category_i_bound (k : ℕ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop,
      (((Icc 1 ⌊x⌋₊).filter (fun n =>
        ∃ j < k, ∃ q : ℕ, q.Prime ∧ x ^ δ < (q : ℝ) ∧ q ^ 2 ∣ Nat.totient^[j] n)).card : ℝ) ≤
        (ε / 4) * x := by
  let C_k : ℝ := 2 * (k : ℝ) * ((k + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * k)
  let β : ℝ := δ / (2 * ((2 * k + 1 : ℕ) : ℝ))
  have hβ_pos : 0 < β := div_pos hδ (by positivity)
  let C₁ : ℝ := 4 * (C_k + 1) / (ε * β ^ (2 * k))
  have hC₁_pos : 0 < C₁ := by positivity
  let X₀ : ℝ := max (max (Real.exp 2) ((4 : ℝ) ^ (1 / δ))) (C₁ ^ (2 / δ))
  filter_upwards [Filter.eventually_ge_atTop X₀] with x hx
  have hx_exp2 : Real.exp 2 ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hx)
  have hx_4 : (4 : ℝ) ^ (1 / δ) ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hx)
  have hx_C1 : C₁ ^ (2 / δ) ≤ x := le_trans (le_max_right _ _) hx
  have hx_pos : 0 < x := lt_of_lt_of_le (Real.exp_pos 2) hx_exp2
  have hx1 : 1 ≤ x := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hlogx_ge2 : (2 : ℝ) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 2) hx_exp2; rwa [Real.log_exp] at this
  have hX_pos : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx1)
  have hxd_ge4 : (4 : ℝ) ≤ x ^ δ := by
    have h1 := Real.rpow_le_rpow (by positivity) hx_4 hδ.le
    rw [← Real.rpow_mul (by norm_num)] at h1
    have : (1 / δ) * δ = 1 := by field_simp [hδ.ne']
    rwa [this, Real.rpow_one] at h1
  let L : ℕ := ⌊x ^ δ⌋₊
  have hL_ge2 : 2 ≤ L := by
    have : (2 : ℝ) ≤ (L : ℝ) := by linarith [Nat.lt_floor_add_one (x ^ δ), hxd_ge4]
    exact_mod_cast this
  have hL_ge_half : (1 / 2) * x ^ δ ≤ (L : ℝ) := by
    linarith [Nat.lt_floor_add_one (x ^ δ), hxd_ge4]
  let CatI := (Icc 1 ⌊x⌋₊).filter (fun n =>
    ∃ j < k, ∃ q : ℕ, q.Prime ∧ x ^ δ < (q : ℝ) ∧ q ^ 2 ∣ Nat.totient^[j] n)
  let CatI_j : ℕ → Finset ℕ := fun j => (Icc 1 ⌊x⌋₊).filter (fun n =>
    (∃ q : ℕ, q.Prime ∧ L < q ∧ q ^ 2 ∣ Nat.totient^[j] n) ∧
    ∀ i < j, ¬ ∃ q : ℕ, q.Prime ∧ L < q ∧ q ^ 2 ∣ Nat.totient^[i] n)
  have hcover : CatI ⊆ (range k).biUnion CatI_j := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hn_Icc, j0, hj0, q0, hq0, hq0x, hq0sq⟩ := hn
    have hex : ∃ j : ℕ, ∃ q, q.Prime ∧ L < q ∧ q ^ 2 ∣ Nat.totient^[j] n :=
      ⟨j0, q0, hq0, (Nat.floor_lt (by positivity)).mpr hq0x, hq0sq⟩
    let j := Nat.find hex
    have hj_spec := Nat.find_spec hex
    have hj_lt : j < k := lt_of_le_of_lt (Nat.find_min' hex ⟨q0, hq0, (Nat.floor_lt (by positivity)).mpr hq0x, hq0sq⟩) hj0
    have hj_min : ∀ i < j, ¬ ∃ q, q.Prime ∧ L < q ∧ q ^ 2 ∣ Nat.totient^[i] n :=
      fun i hi => Nat.find_min hex hi
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj_lt,
      Finset.mem_filter.mpr ⟨hn_Icc, hj_spec, hj_min⟩⟩
  have hcard_le : (CatI.card : ℝ) ≤ ∑ j ∈ range k, ((CatI_j j).card : ℝ) := by
    have hnat : CatI.card ≤ ∑ j ∈ range k, (CatI_j j).card :=
      (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    exact_mod_cast hnat
  have hlogX_le : Real.log (⌊x⌋₊ : ℝ) + 1 ≤ 2 * Real.log x := by
    have h1 : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x :=
      Real.log_le_log (by exact_mod_cast hX_pos) (Nat.floor_le hx_pos.le)
    linarith only [h1, hlogx_ge2]
  have hsum_le : (CatI.card : ℝ) ≤ C_k * x * (Real.log x) ^ (2 * k) / x ^ δ := by
    have hterm : ∀ j ∈ range k, ((CatI_j j).card : ℝ) ≤
        ((k + 2 : ℕ) : ℝ) * x * (2 * Real.log x) ^ (2 * k) / ((1 / 2) * x ^ δ) := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hb := category_i_bound_fixed_j ⌊x⌋₊ L hX_pos (by omega) j
      have hlog_ge1 : (1 : ℝ) ≤ Real.log (⌊x⌋₊ : ℝ) + 1 := by
        have : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hX_pos
        linarith [Real.log_nonneg this]
      have hlog_pow : (Real.log (⌊x⌋₊ : ℝ) + 1) ^ (2 * j) ≤ (2 * Real.log x) ^ (2 * k) :=
        (pow_le_pow_right₀ hlog_ge1 (by omega)).trans (pow_le_pow_left₀ (by positivity) hlogX_le (2 * k))
      have hX_le_x : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx_pos.le
      have hj2 : ((j + 2 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by exact_mod_cast (show j + 2 ≤ k + 2 by omega)
      calc ((CatI_j j).card : ℝ)
          ≤ ((j + 2 : ℕ) : ℝ) * (⌊x⌋₊ : ℝ) * (Real.log (⌊x⌋₊ : ℝ) + 1) ^ (2 * j) / (L : ℝ) := hb
        _ ≤ ((k + 2 : ℕ) : ℝ) * x * (2 * Real.log x) ^ (2 * k) / ((1 / 2) * x ^ δ) := by
            refine div_le_div₀ (by positivity) ?_ (by positivity) hL_ge_half
            gcongr
    calc (CatI.card : ℝ)
        ≤ ∑ j ∈ range k, ((CatI_j j).card : ℝ) := hcard_le
      _ ≤ ∑ _j ∈ range k, (((k + 2 : ℕ) : ℝ) * x * (2 * Real.log x) ^ (2 * k) / ((1 / 2) * x ^ δ)) :=
          Finset.sum_le_sum hterm
      _ = (k : ℝ) * (((k + 2 : ℕ) : ℝ) * x * (2 * Real.log x) ^ (2 * k) / ((1 / 2) * x ^ δ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = C_k * x * (Real.log x) ^ (2 * k) / x ^ δ := by
          simp only [C_k, mul_pow]; ring
  have hlog_rpow : (Real.log x) ^ (2 * k) ≤ (1 / β ^ (2 * k)) * x ^ (δ / 2) := by
    have h1 := log_le_rpow_div_self hx_pos hβ_pos
    calc (Real.log x) ^ (2 * k)
        ≤ (x ^ β / β) ^ (2 * k) := pow_le_pow_left₀ (by linarith only [hlogx_ge2]) h1 (2 * k)
      _ = (1 / β ^ (2 * k)) * (x ^ β) ^ (2 * k) := by rw [div_pow]; ring
      _ = (1 / β ^ (2 * k)) * x ^ (β * (2 * k : ℕ)) := by
          rw [← Real.rpow_natCast (x ^ β), ← Real.rpow_mul hx_pos.le]
      _ ≤ (1 / β ^ (2 * k)) * x ^ (δ / 2) := by
          refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 ?_) (by positivity)
          simp only [β]
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          have : ((2 * k : ℕ) : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ (2 * k)
          nlinarith only [this, hδ]
  have hx_delta2 : C₁ ≤ x ^ (δ / 2) := by
    have h1 := Real.rpow_le_rpow (by positivity) hx_C1 (show (0 : ℝ) ≤ δ / 2 by positivity)
    rw [← Real.rpow_mul hC₁_pos.le] at h1
    have : (2 / δ) * (δ / 2) = 1 := by field_simp [hδ.ne']
    rwa [this, Real.rpow_one] at h1
  have hxd_split : x ^ δ = x ^ (δ / 2) * x ^ (δ / 2) := by
    rw [← Real.rpow_add hx_pos]; congr 1; ring
  calc (CatI.card : ℝ)
      ≤ C_k * x * (Real.log x) ^ (2 * k) / x ^ δ := hsum_le
    _ ≤ (C_k + 1) * x * ((1 / β ^ (2 * k)) * x ^ (δ / 2)) / x ^ δ := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        have h1 : C_k * x ≤ (C_k + 1) * x := by nlinarith only [hx_pos]
        exact mul_le_mul h1 hlog_rpow (by positivity) (by positivity)
    _ = ((C_k + 1) / β ^ (2 * k)) * x / x ^ (δ / 2) := by
        rw [hxd_split]
        have hne : x ^ (δ / 2) ≠ 0 := (Real.rpow_pos_of_pos hx_pos _).ne'
        field_simp [hne]
    _ ≤ ((C_k + 1) / β ^ (2 * k)) * x / C₁ :=
        div_le_div_of_nonneg_left (by positivity) hC₁_pos hx_delta2
    _ = (ε / 4) * x := by
        simp only [C₁]
        have hne1 : C_k + 1 ≠ 0 := by positivity
        have hne2 : β ^ (2 * k) ≠ 0 := by positivity
        field_simp [hne1, hne2, hε.ne']

/- Category (ii) bound via dyadic splitting + `condensed_chain_bound` -/

open Classical in
lemma category_ii_bound {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ k : ℕ, ∀ᶠ x : ℝ in atTop,
      (((Icc 1 ⌊x⌋₊).filter (fun n =>
        ∃ p0, p0.Prime ∧ p0 ∣ n ∧ HasPrimeChain k p0 (x ^ δ))).card : ℝ) ≤ (ε / 4) * x := by
  let δ₀ : ℝ := min δ (1 / 2)
  have hδ₀_pos : 0 < δ₀ := lt_min hδ (by norm_num)
  have hδ₀_le_δ : δ₀ ≤ δ := min_le_left _ _
  have hδ₀_le_half : δ₀ ≤ 1 / 2 := min_le_right _ _
  let r : ℕ := max 1 ⌈(1 / δ₀) ^ (1 / etaFKL)⌉₊
  have hr1 : 1 ≤ r := le_max_left _ _
  have hr_exp : (r + 1 : ℝ) ^ (-etaFKL) ≤ δ₀ := by
    have h1 : (1 / δ₀) ^ (1 / etaFKL) ≤ (r + 1 : ℝ) := by
      have hceil : (1 / δ₀) ^ (1 / etaFKL) ≤ (⌈(1 / δ₀) ^ (1 / etaFKL)⌉₊ : ℝ) := Nat.le_ceil _
      have hle : (⌈(1 / δ₀) ^ (1 / etaFKL)⌉₊ : ℝ) ≤ (r : ℝ) := by exact_mod_cast le_max_right 1 _
      linarith only [hceil, hle]
    have h2 := Real.rpow_le_rpow (by positivity) h1 etaFKL_pos.le
    rw [← Real.rpow_mul (by positivity)] at h2
    have hexp : (1 / etaFKL) * etaFKL = 1 := by field_simp [etaFKL_pos.ne']
    rw [hexp, Real.rpow_one] at h2
    rw [Real.rpow_neg (by positivity), inv_eq_one_div]
    calc 1 / (r + 1 : ℝ) ^ etaFKL ≤ 1 / (1 / δ₀) := one_div_le_one_div_of_le (by positivity) h2
      _ = δ₀ := by field_simp [hδ₀_pos.ne']
  let l : ℕ := max 4 ⌈32 * C_cond / (ε * δ₀)⌉₊
  have hl4 : 4 ≤ l := le_max_left _ _
  have hC_cond_pos : 0 < C_cond := by unfold C_cond; positivity
  have hl_bound : (8 * C_cond / δ₀) * (1 / 2 : ℝ) ^ l ≤ ε / 4 := by
    have hl_ge : 32 * C_cond / (ε * δ₀) ≤ (l : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast le_max_right 4 _)
    have h2l : (l : ℝ) ≤ (2 : ℝ) ^ l := by exact_mod_cast (Nat.lt_two_pow_self (n := l)).le
    have h12l : (1 / 2 : ℝ) ^ l ≤ 1 / (l : ℝ) := by
      rw [one_div_pow]
      exact one_div_le_one_div_of_le (by exact_mod_cast (show 0 < l by omega)) h2l
    have hl_pos : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
    calc (8 * C_cond / δ₀) * (1 / 2 : ℝ) ^ l
        ≤ (8 * C_cond / δ₀) * (1 / (l : ℝ)) := mul_le_mul_of_nonneg_left h12l (by positivity)
      _ ≤ (8 * C_cond / δ₀) * (1 / (32 * C_cond / (ε * δ₀))) := by
          refine mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by positivity) hl_ge) (by positivity)
      _ = ε / 4 := by field_simp [hC_cond_pos.ne', hδ₀_pos.ne', hε.ne']; ring
  refine ⟨r * l, ?_⟩
  obtain ⟨Y_cond, hY_cond⟩ := Filter.eventually_atTop.mp (condensed_chain_bound r l hr1 hl4)
  let Y₁ : ℝ := max (max Y_cond 4) (Real.exp 4)
  let X_min : ℝ := max (max (Real.exp 4) ((2 * Y₁) ^ (1 / δ₀))) (Real.exp (2 * Real.log 2 / δ₀))
  filter_upwards [Filter.eventually_ge_atTop X_min] with x hx
  have hx_exp4 : Real.exp 4 ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hx)
  have hx_Y1 : (2 * Y₁) ^ (1 / δ₀) ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hx)
  have hx_log2 : Real.exp (2 * Real.log 2 / δ₀) ≤ x := le_trans (le_max_right _ _) hx
  have hx_pos : 0 < x := lt_of_lt_of_le (Real.exp_pos 4) hx_exp4
  have hx1 : 1 ≤ x := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hlogx_ge4 : (4 : ℝ) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 4) hx_exp4; rwa [Real.log_exp] at this
  have hlogx_pos : 0 < Real.log x := by linarith only [hlogx_ge4]
  have hxd0_ge : 2 * Y₁ ≤ x ^ δ₀ := by
    have hY1_pos : 0 < Y₁ := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right Y_cond 4) (le_max_left _ _))
    have h1 := Real.rpow_le_rpow (by positivity) hx_Y1 hδ₀_pos.le
    rw [← Real.rpow_mul (by positivity)] at h1
    have : (1 / δ₀) * δ₀ = 1 := by field_simp [hδ₀_pos.ne']
    rwa [this, Real.rpow_one] at h1
  let Pbad : Finset ℕ := (Icc 1 ⌊x⌋₊).filter (fun p0 : ℕ =>
    p0.Prime ∧ x ^ δ ≤ (p0 : ℝ) ∧ HasPrimeChain (r * l) p0 (x ^ δ))
  let CatII := (Icc 1 ⌊x⌋₊).filter (fun n => ∃ p0, p0.Prime ∧ p0 ∣ n ∧ HasPrimeChain (r * l) p0 (x ^ δ))
  have hcover_n : CatII ⊆ Pbad.biUnion (fun p0 => (Icc 1 ⌊x⌋₊).filter (p0 ∣ ·)) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnX⟩, p0, hp0_pr, hp0_dvd, hp0_ch⟩ := hn
    obtain ⟨p, hp_ch, hp0_eq, hlast_ge⟩ := hp0_ch
    have hp0_ge : x ^ δ ≤ (p0 : ℝ) := by
      have hle : p (Fin.last (r * l)) ≤ p 0 := isPrimeChain_ge_last hp_ch 0
      rw [hp0_eq] at hle
      exact hlast_ge.trans (by exact_mod_cast hle)
    have hp0_le : p0 ≤ ⌊x⌋₊ := le_trans (Nat.le_of_dvd (by omega) hp0_dvd) hnX
    exact Finset.mem_biUnion.mpr ⟨p0, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp0_pr.one_le, hp0_le⟩,
      hp0_pr, hp0_ge, ⟨p, hp_ch, hp0_eq, hlast_ge⟩⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn1, hnX⟩, hp0_dvd⟩⟩
  have hcard_catII : (CatII.card : ℝ) ≤ x * ∑ p0 ∈ Pbad, (1 / (p0 : ℝ)) := by
    have hnat : CatII.card ≤ ∑ p0 ∈ Pbad, ((Icc 1 ⌊x⌋₊).filter (p0 ∣ ·)).card :=
      (Finset.card_le_card hcover_n).trans Finset.card_biUnion_le
    calc (CatII.card : ℝ)
        ≤ ∑ p0 ∈ Pbad, (((Icc 1 ⌊x⌋₊).filter (p0 ∣ ·)).card : ℝ) := by exact_mod_cast hnat
      _ ≤ ∑ p0 ∈ Pbad, ((⌊x⌋₊ : ℝ) / (p0 : ℝ)) :=
          Finset.sum_le_sum fun p0 hp0 => card_Icc_dvd_le ⌊x⌋₊ p0 (Finset.mem_filter.mp hp0).2.1.one_le
      _ ≤ ∑ p0 ∈ Pbad, (x * (1 / (p0 : ℝ))) := by
          refine Finset.sum_le_sum fun p0 hp0 => ?_
          rw [mul_one_div]
          exact div_le_div_of_nonneg_right (Nat.floor_le hx_pos.le) (Nat.cast_nonneg _)
      _ = x * ∑ p0 ∈ Pbad, (1 / (p0 : ℝ)) := (Finset.mul_sum _ _ _).symm
  -- Dyadic cover of `Pbad`
  let T : ℕ := ⌊(1 - δ₀) * Real.log x / Real.log 2⌋₊ + 1
  let yt : ℕ → ℝ := fun t => x / (2 : ℝ) ^ t
  let Block : ℕ → Finset ℕ := fun t =>
    (Icc 1 ⌊yt t⌋₊).filter (fun p0 => p0.Prime ∧ yt t / 2 < (p0 : ℝ) ∧ HasPrimeChain (r * l) p0 (yExp (yt t) r))
  have hcover_P : Pbad ⊆ (range (T + 1)).biUnion Block := by
    intro p0 hp0
    rw [Finset.mem_filter, Finset.mem_Icc] at hp0
    obtain ⟨⟨_, hp0_le⟩, hp0_pr, hp0_ge, hp0_ch⟩ := hp0
    have hp0_pos : (0 : ℝ) < p0 := by exact_mod_cast hp0_pr.pos
    have hp0_le_x : (p0 : ℝ) ≤ x := le_trans (by exact_mod_cast hp0_le) (Nat.floor_le hx_pos.le)
    have hxd0_le_p0 : x ^ δ₀ ≤ (p0 : ℝ) :=
      (Real.rpow_le_rpow_of_exponent_le hx1 hδ₀_le_δ).trans hp0_ge
    let t : ℕ := ⌊Real.log (x / (p0 : ℝ)) / Real.log 2⌋₊
    have hlog_xp0_nn : 0 ≤ Real.log (x / (p0 : ℝ)) :=
      Real.log_nonneg ((one_le_div hp0_pos).mpr hp0_le_x)
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have ht_le : t ≤ T := by
      have hdiv_le : x / (p0 : ℝ) ≤ x ^ (1 - δ₀) := by
        rw [div_le_iff₀ hp0_pos]
        calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
          _ = x ^ (1 - δ₀) * x ^ δ₀ := by rw [← Real.rpow_add hx_pos]; congr 1; ring
          _ ≤ x ^ (1 - δ₀) * (p0 : ℝ) := mul_le_mul_of_nonneg_left hxd0_le_p0 (by positivity)
      have hlog_le : Real.log (x / (p0 : ℝ)) ≤ (1 - δ₀) * Real.log x := by
        calc Real.log (x / (p0 : ℝ)) ≤ Real.log (x ^ (1 - δ₀)) :=
              Real.log_le_log (div_pos hx_pos hp0_pos) hdiv_le
          _ = (1 - δ₀) * Real.log x := by rw [Real.log_rpow hx_pos]
      have hq_le : Real.log (x / (p0 : ℝ)) / Real.log 2 ≤ (1 - δ₀) * Real.log x / Real.log 2 :=
        div_le_div_of_nonneg_right hlog_le hlog2_pos.le
      have hfl := Nat.floor_mono hq_le
      omega
    have h2t_le : (2 : ℝ) ^ t ≤ x / (p0 : ℝ) := by
      have h1 : (t : ℝ) * Real.log 2 ≤ Real.log (x / (p0 : ℝ)) := by
        have := Nat.floor_le (div_nonneg hlog_xp0_nn hlog2_pos.le)
        exact (le_div_iff₀ hlog2_pos).mp this
      have h2 := Real.exp_le_exp.mpr h1
      rw [Real.exp_log (div_pos hx_pos hp0_pos), Real.exp_nat_mul, Real.exp_log (by norm_num)] at h2
      exact h2
    have hxp0_lt : x / (p0 : ℝ) < (2 : ℝ) ^ (t + 1) := by
      have h1 : Real.log (x / (p0 : ℝ)) < ((t + 1 : ℕ) : ℝ) * Real.log 2 := by
        have := Nat.lt_floor_add_one (Real.log (x / (p0 : ℝ)) / Real.log 2)
        have h2 : Real.log (x / (p0 : ℝ)) / Real.log 2 < ((t + 1 : ℕ) : ℝ) := by push_cast; exact this
        exact (div_lt_iff₀ hlog2_pos).mp h2
      have h2 := Real.exp_lt_exp.mpr h1
      rw [Real.exp_log (div_pos hx_pos hp0_pos), Real.exp_nat_mul, Real.exp_log (by norm_num)] at h2
      exact h2
    have hp0_le_yt : (p0 : ℝ) ≤ yt t := by
      simp only [yt]; rw [le_div_iff₀ (by positivity)]
      have := (le_div_iff₀ hp0_pos).mp h2t_le; linarith only [this]
    have hyt_half_lt : yt t / 2 < (p0 : ℝ) := by
      simp only [yt]; rw [div_div, ← pow_succ, div_lt_iff₀ (by positivity)]
      have := (div_lt_iff₀ hp0_pos).mp hxp0_lt; linarith only [this]
    have hyt_le_x : yt t ≤ x := by
      simp only [yt]; exact div_le_self hx_pos.le (one_le_pow₀ (by norm_num))
    have hyt_ge1 : (1 : ℝ) ≤ yt t := by
      have : (1 : ℝ) ≤ p0 := by exact_mod_cast hp0_pr.one_le
      linarith only [this, hp0_le_yt]
    have hyExp_le : yExp (yt t) r ≤ x ^ δ := by
      unfold yExp
      calc (yt t) ^ ((r + 1 : ℝ) ^ (-etaFKL))
          ≤ (yt t) ^ δ₀ := Real.rpow_le_rpow_of_exponent_le hyt_ge1 hr_exp
        _ ≤ x ^ δ₀ := Real.rpow_le_rpow (by positivity) hyt_le_x hδ₀_pos.le
        _ ≤ x ^ δ := Real.rpow_le_rpow_of_exponent_le hx1 hδ₀_le_δ
    rw [Finset.mem_biUnion]
    refine ⟨t, Finset.mem_range.mpr (by omega), Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hp0_pr.one_le, Nat.le_floor hp0_le_yt⟩, hp0_pr, hyt_half_lt, ?_⟩⟩
    obtain ⟨p, hp_ch, hp0_eq, hlast_ge⟩ := hp0_ch
    exact ⟨p, hp_ch, hp0_eq, hyExp_le.trans hlast_ge⟩
  -- Bound each dyadic block using `condensed_chain_bound`
  have hblock_le : ∀ t ∈ range (T + 1),
      ∑ p0 ∈ Block t, (1 / (p0 : ℝ)) ≤ (4 * C_cond / δ₀) * (1 / 2 : ℝ) ^ l / Real.log x := by
    intro t ht
    rw [Finset.mem_range] at ht
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h2t_le : (2 : ℝ) ^ t ≤ 2 * x ^ (1 - δ₀) := by
      have ht_le_r : (t : ℝ) ≤ (1 - δ₀) * Real.log x / Real.log 2 + 1 := by
        have htT : t ≤ T := by omega
        have hfl : (⌊(1 - δ₀) * Real.log x / Real.log 2⌋₊ : ℝ) ≤ (1 - δ₀) * Real.log x / Real.log 2 :=
          Nat.floor_le (div_nonneg (mul_nonneg (by linarith only [hδ₀_le_half]) hlogx_pos.le) hlog2_pos.le)
        have : (t : ℝ) ≤ (⌊(1 - δ₀) * Real.log x / Real.log 2⌋₊ : ℝ) + 1 := by exact_mod_cast htT
        linarith only [this, hfl]
      have hmul : (t : ℝ) * Real.log 2 ≤ Real.log 2 + (1 - δ₀) * Real.log x := by
        have h1 := mul_le_mul_of_nonneg_right ht_le_r hlog2_pos.le
        rw [add_mul, one_mul, div_mul_cancel₀ _ hlog2_pos.ne'] at h1
        linarith only [h1]
      have hexp := Real.exp_le_exp.mpr hmul
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num), Real.exp_add, Real.exp_log (by norm_num),
        mul_comm (1 - δ₀), ← Real.rpow_def_of_pos hx_pos] at hexp
      exact hexp
    have hyt_ge_half : (1 / 2) * x ^ δ₀ ≤ yt t := by
      simp only [yt]
      rw [le_div_iff₀ (by positivity)]
      calc (1 / 2) * x ^ δ₀ * (2 : ℝ) ^ t
          ≤ (1 / 2) * x ^ δ₀ * (2 * x ^ (1 - δ₀)) := mul_le_mul_of_nonneg_left h2t_le (by positivity)
        _ = x ^ δ₀ * x ^ (1 - δ₀) := by ring
        _ = x := by rw [← Real.rpow_add hx_pos]; simp
    have hyt_ge_Y1 : Y₁ ≤ yt t := by linarith only [hxd0_ge, hyt_ge_half]
    have hyt_ge_Ycond : Y_cond ≤ yt t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hyt_ge_Y1
    have hyt_pos : 0 < yt t := by simp only [yt]; positivity
    have hlog_yt_ge : (δ₀ / 2) * Real.log x ≤ Real.log (yt t) := by
      have h1 := Real.log_le_log (by positivity) hyt_ge_half
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx_pos, one_div, Real.log_inv] at h1
      have h2 : 2 * Real.log 2 / δ₀ ≤ Real.log x := by
        have := Real.log_le_log (Real.exp_pos _) hx_log2; rwa [Real.log_exp] at this
      have h3 : Real.log 2 ≤ (δ₀ / 2) * Real.log x := by
        have := (div_le_iff₀ hδ₀_pos).mp h2; linarith only [this]
      linarith only [h1, h3]
    have hlog_yt_pos : 0 < Real.log (yt t) := lt_of_lt_of_le (by positivity) hlog_yt_ge
    have hcard_B : ((Block t).card : ℝ) ≤ C_cond * (1 / 2 : ℝ) ^ l * (yt t / Real.log (yt t)) := by
      have hsub : Block t ⊆ (Icc 1 ⌊yt t⌋₊).filter (fun p0 => p0.Prime ∧ HasPrimeChain (r * l) p0 (yExp (yt t) r)) := by
        intro p0 hp0; rw [Finset.mem_filter] at hp0 ⊢; exact ⟨hp0.1, hp0.2.1, hp0.2.2.2⟩
      exact le_trans (by exact_mod_cast Finset.card_le_card hsub) (hY_cond (yt t) hyt_ge_Ycond)
    calc ∑ p0 ∈ Block t, (1 / (p0 : ℝ))
        ≤ ∑ _p0 ∈ Block t, (2 / yt t) := by
          refine Finset.sum_le_sum fun p0 hp0 => ?_
          have hlt := (Finset.mem_filter.mp hp0).2.2.1
          rw [div_le_div_iff₀ (by exact_mod_cast (Finset.mem_filter.mp hp0).2.1.pos) hyt_pos]
          linarith only [hlt]
      _ = (2 / yt t) * ((Block t).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ (2 / yt t) * (C_cond * (1 / 2 : ℝ) ^ l * (yt t / Real.log (yt t))) :=
          mul_le_mul_of_nonneg_left hcard_B (by positivity)
      _ = 2 * C_cond * (1 / 2 : ℝ) ^ l / Real.log (yt t) := by field_simp [hyt_pos.ne']
      _ ≤ 2 * C_cond * (1 / 2 : ℝ) ^ l / ((δ₀ / 2) * Real.log x) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hlog_yt_ge
      _ = (4 * C_cond / δ₀) * (1 / 2 : ℝ) ^ l / Real.log x := by field_simp [hδ₀_pos.ne', hlogx_pos.ne']; ring
  have hT1_le : ((T + 1 : ℕ) : ℝ) ≤ 2 * Real.log x := by
    have hlog2_gt : (2 / 3 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have hlog2_pos : 0 < Real.log 2 := by linarith only [hlog2_gt]
    have hfl : (⌊(1 - δ₀) * Real.log x / Real.log 2⌋₊ : ℝ) ≤ (1 - δ₀) * Real.log x / Real.log 2 :=
      Nat.floor_le (div_nonneg (mul_nonneg (by linarith only [hδ₀_le_half]) hlogx_pos.le) hlog2_pos.le)
    have hdiv_le : (1 - δ₀) * Real.log x / Real.log 2 ≤ (3 / 2) * Real.log x := by
      rw [div_le_iff₀ (by linarith only [hlog2_gt])]
      nlinarith only [hlog2_gt, hδ₀_pos, hlogx_pos]
    have hcast : ((T + 1 : ℕ) : ℝ) = (⌊(1 - δ₀) * Real.log x / Real.log 2⌋₊ : ℝ) + 2 := by
      simp only [T, Nat.cast_add, Nat.cast_one]; ring
    linarith only [hcast, hfl, hdiv_le, hlogx_ge4]
  calc (CatII.card : ℝ)
      ≤ x * ∑ p0 ∈ Pbad, (1 / (p0 : ℝ)) := hcard_catII
    _ ≤ x * ∑ p0 ∈ (range (T + 1)).biUnion Block, (1 / (p0 : ℝ)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hcover_P (fun _ _ _ => by positivity)) hx_pos.le
    _ ≤ x * ∑ t ∈ range (T + 1), ∑ p0 ∈ Block t, (1 / (p0 : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_biUnion_le_sum _ _ _ (fun _ => by positivity)) hx_pos.le
    _ ≤ x * ∑ _t ∈ range (T + 1), ((4 * C_cond / δ₀) * (1 / 2 : ℝ) ^ l / Real.log x) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hblock_le) hx_pos.le
    _ = x * (((T + 1 : ℕ) : ℝ) * ((4 * C_cond / δ₀) * (1 / 2 : ℝ) ^ l / Real.log x)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ x * ((2 * Real.log x) * ((4 * C_cond / δ₀) * (1 / 2 : ℝ) ^ l / Real.log x)) := by
        gcongr
    _ = ((8 * C_cond / δ₀) * (1 / 2 : ℝ) ^ l) * x := by
        field_simp [hlogx_pos.ne']; ring
    _ ≤ (ε / 4) * x := mul_le_mul_of_nonneg_right hl_bound hx_pos.le

/- Main proof of Ford–Konyagin–Luca (2010) Theorem 5 / Erdos 408 variant -/

open Classical in
theorem ford_konyagin_luca_main (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ k : ℕ, ∀ᶠ x : ℝ in atTop, (1 - ε) * x ≤
      ((Finset.Icc 1 ⌊x⌋₊).filter fun n ↦
        ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ).card := by
  obtain ⟨k, hcat2⟩ := category_ii_bound hε hδ
  have hcat1 := category_i_bound k hε hδ
  refine ⟨k, ?_⟩
  filter_upwards [hcat1, hcat2, Filter.eventually_ge_atTop (max 2 (2 / ε))] with x hc1 hc2 hx
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_left _ _) hx
  have hx_eps : 2 / ε ≤ x := le_trans (le_max_right _ _) hx
  have hx_pos : 0 < x := by linarith only [hx2]
  have hxd_gt1 : (1 : ℝ) < x ^ δ := Real.one_lt_rpow (by linarith only [hx2]) hδ
  let Good := (Icc 1 ⌊x⌋₊).filter (fun n => ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ)
  let Bad := (Icc 1 ⌊x⌋₊).filter (fun n => ¬ ((Nat.totient^[k] n).maxPrimeFac : ℝ) ≤ x ^ δ)
  let CatI := (Icc 1 ⌊x⌋₊).filter (fun n =>
    ∃ j < k, ∃ q : ℕ, q.Prime ∧ x ^ δ < (q : ℝ) ∧ q ^ 2 ∣ Nat.totient^[j] n)
  let CatII := (Icc 1 ⌊x⌋₊).filter (fun n =>
    ∃ p0, p0.Prime ∧ p0 ∣ n ∧ HasPrimeChain k p0 (x ^ δ))
  have hbad_sub : Bad ⊆ CatI ∪ CatII := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnX⟩, hgt⟩ := hn
    push Not at hgt
    let p := (Nat.totient^[k] n).maxPrimeFac
    have hp_gt1 : 1 < p := by
      have : (1 : ℝ) < (p : ℝ) := lt_trans hxd_gt1 hgt
      exact_mod_cast this
    have hphi_gt1 : 1 < Nat.totient^[k] n := by
      by_contra hle
      have hpos := totient_iterate_pos k n hn1
      have heq1 : Nat.totient^[k] n = 1 := by omega
      simp [p, heq1] at hp_gt1
    have hp_pr : p.Prime := Nat.prime_maxPrimeFac_of_one_lt (Nat.totient^[k] n) hphi_gt1
    have hp_dvd : p ∣ Nat.totient^[k] n := Nat.maxPrimeFac_dvd
    rcases trace_prime_back k hn1 (x ^ δ) hp_pr hgt hp_dvd with h1 | ⟨c, hc_ch, hc_last, hc0⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn1, hnX⟩, h1⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn1, hnX⟩,
        c 0, hc_ch.1 0, hc0, ⟨c, hc_ch, rfl, hc_last.symm ▸ hgt.le⟩⟩)
  have hbad_card : (Bad.card : ℝ) ≤ (ε / 2) * x := by
    have hnat : Bad.card ≤ CatI.card + CatII.card :=
      (Finset.card_le_card hbad_sub).trans (Finset.card_union_le _ _)
    have hcast : (Bad.card : ℝ) ≤ (CatI.card : ℝ) + (CatII.card : ℝ) := by exact_mod_cast hnat
    linarith only [hcast, hc1, hc2]
  have hpart : Good.card + Bad.card = (Icc 1 ⌊x⌋₊).card :=
    Finset.card_filter_add_card_filter_not (s := Icc 1 ⌊x⌋₊) _
  have hIcc_card : ((Icc 1 ⌊x⌋₊).card : ℝ) = (⌊x⌋₊ : ℝ) := by simp
  have hfloor_ge : x - 1 < (⌊x⌋₊ : ℝ) := by linarith [Nat.lt_floor_add_one x]
  have h1_le_eps : (1 : ℝ) ≤ (ε / 2) * x := by
    have := (div_le_iff₀ hε).mp hx_eps; linarith only [this]
  have hpart_r : (Good.card : ℝ) + (Bad.card : ℝ) = (⌊x⌋₊ : ℝ) := by
    rw [← hIcc_card, ← Nat.cast_add, hpart]
  linarith only [hpart_r, hbad_card, hfloor_ge, h1_le_eps]

end

end Erdos408FKL

theorem OMA.solution : type_of% @Erdos408.erdos_408.variants.ford_konyagin_luca :=
  Erdos408FKL.ford_konyagin_luca_main
