import FormalConjectures.Wikipedia.RiemannZetaValues
import Mathlib

/-! Proof of RiemannZetaValues.apery_central_binomial_series via Markov-Apery telescoping. -/

open Finset BigOperators Filter Topology
open scoped Nat

namespace OMA_AperySeries

private noncomputable def F (n k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * ((k ! : ℝ) ^ 2) / ((n : ℝ) ^ 3 * ∏ j ∈ Finset.Icc 1 k, ((n : ℝ) ^ 2 - (j : ℝ) ^ 2))

private noncomputable def H (n k : ℕ) : ℝ :=
  (-1 : ℝ) ^ (k - 1) * (((k - 1)! : ℝ) ^ 2) * ((n - k)! : ℝ) / (2 * (k : ℝ) * ((n + k)! : ℝ))

private lemma prod_sq_sub_eq_fact (n k : ℕ) (hk : k < n) :
    (n : ℝ) * ((n - k - 1)! : ℝ) * (∏ j ∈ Finset.Icc 1 k, ((n : ℝ) ^ 2 - (j : ℝ) ^ 2)) =
      ((n + k)! : ℝ) := by
  induction k with
  | zero =>
    simp only [Finset.Icc_eq_empty_of_lt (by norm_num : 0 < 1), Finset.prod_empty, mul_one,
      Nat.sub_zero, add_zero]
    have hn : n = (n - 1) + 1 := by omega
    conv_rhs => rw [hn, Nat.factorial_succ]
    push_cast
    rw [show ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) by exact_mod_cast hn.symm]
  | succ k ih =>
    have hlt : k < n := by omega
    have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.prod_insert (by simp)]
    have hfact_lo : ((n - k - 1)! : ℝ) = ((n - k - 1 : ℕ) : ℝ) * ((n - (k + 1) - 1)! : ℝ) := by
      have h1 : n - k - 1 = (n - (k + 1) - 1) + 1 := by omega
      conv_lhs => rw [h1, Nat.factorial_succ]
      push_cast
      rw [show ((n - (k + 1) - 1 : ℕ) : ℝ) + 1 = ((n - k - 1 : ℕ) : ℝ) by exact_mod_cast h1.symm]
    have hfact_hi : ((n + (k + 1))! : ℝ) = ((n + (k + 1) : ℕ) : ℝ) * ((n + k)! : ℝ) := by
      have h1 : n + (k + 1) = (n + k) + 1 := by omega
      rw [h1, Nat.factorial_succ]
      push_cast
      ring
    have hsub : ((n : ℝ) ^ 2 - ((k + 1 : ℕ) : ℝ) ^ 2) =
        ((n - k - 1 : ℕ) : ℝ) * ((n + (k + 1) : ℕ) : ℝ) := by
      have h1 : ((n - k - 1 : ℕ) : ℝ) = (n : ℝ) - ((k + 1 : ℕ) : ℝ) := by
        have : n - k - 1 + (k + 1) = n := by omega
        have hcast : ((n - k - 1 : ℕ) : ℝ) + ((k + 1 : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast this
        linarith
      rw [h1]; push_cast; ring
    rw [hfact_hi, ← ih hlt, hfact_lo, hsub]
    ring

private lemma prod_sq_sub_ne_zero (n k : ℕ) (hk : k < n) :
    (∏ j ∈ Finset.Icc 1 k, ((n : ℝ) ^ 2 - (j : ℝ) ^ 2)) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  simp only [Finset.mem_Icc] at hj
  have h1 : (j : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : j < n)
  have h2 : (j : ℝ) ^ 2 < (n : ℝ) ^ 2 := by nlinarith
  linarith

private lemma F_sub_eq_H_sub (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k < n) :
    F n (k - 1) - F n k = H (n - 1) k - H n k := by
  unfold F H
  have hIcc : Finset.Icc 1 k = insert k (Finset.Icc 1 (k - 1)) := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnotmem : k ∉ Finset.Icc 1 (k - 1) := by simp; omega
  have hprod_split :
      ∏ j ∈ Finset.Icc 1 k, ((n : ℝ) ^ 2 - (j : ℝ) ^ 2) =
        ((n : ℝ) ^ 2 - (k : ℝ) ^ 2) * ∏ j ∈ Finset.Icc 1 (k - 1), ((n : ℝ) ^ 2 - (j : ℝ) ^ 2) := by
    rw [hIcc, Finset.prod_insert hnotmem]
  have hP1 : (∏ j ∈ Finset.Icc 1 (k - 1), ((n : ℝ) ^ 2 - (j : ℝ) ^ 2)) ≠ 0 :=
    prod_sq_sub_ne_zero n (k - 1) (by omega)
  have hP2 : (∏ j ∈ Finset.Icc 1 k, ((n : ℝ) ^ 2 - (j : ℝ) ^ 2)) ≠ 0 :=
    prod_sq_sub_ne_zero n k hkn
  have hnk : ((n : ℝ) ^ 2 - (k : ℝ) ^ 2) ≠ 0 := by
    have : (k : ℝ) < (n : ℝ) := by exact_mod_cast hkn
    nlinarith
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hkfact : (k ! : ℝ) = (k : ℝ) * ((k - 1)! : ℝ) := by
    have h1 : k = (k - 1) + 1 := by omega
    conv_lhs => rw [h1, Nat.factorial_succ]
    push_cast
    rw [show ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) by exact_mod_cast h1.symm]
  have hpow : (-1 : ℝ) ^ k = -((-1 : ℝ) ^ (k - 1)) := by
    have h1 : k = (k - 1) + 1 := by omega
    conv_lhs => rw [h1, pow_succ]
    ring
  have hLHS :
      (-1 : ℝ) ^ (k - 1) * (((k - 1)! : ℝ) ^ 2) /
          ((n : ℝ) ^ 3 * ∏ j ∈ Finset.Icc 1 (k - 1), ((n : ℝ) ^ 2 - (j : ℝ) ^ 2)) -
      (-1 : ℝ) ^ k * ((k ! : ℝ) ^ 2) /
          ((n : ℝ) ^ 3 * ∏ j ∈ Finset.Icc 1 k, ((n : ℝ) ^ 2 - (j : ℝ) ^ 2)) =
      (-1 : ℝ) ^ (k - 1) * (((k - 1)! : ℝ) ^ 2) /
          ((n : ℝ) * ∏ j ∈ Finset.Icc 1 k, ((n : ℝ) ^ 2 - (j : ℝ) ^ 2)) := by
    rw [hprod_split, hkfact, hpow]
    field_simp [hn0, hP1, hnk]
    ring
  rw [hLHS]
  -- Now simplify RHS using prod_sq_sub_eq_fact
  have hfact_eq := prod_sq_sub_eq_fact n k hkn
  have hne_nk1 : ((n - 1 + k)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hne_nk2 : ((n + k)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hsub_eq : n - 1 - k = n - k - 1 := by omega
  have hnk_succ : ((n + k)! : ℝ) = ((n + k : ℕ) : ℝ) * ((n - 1 + k)! : ℝ) := by
    have h1 : n + k = (n - 1 + k) + 1 := by omega
    conv_lhs => rw [h1, Nat.factorial_succ]
    push_cast
    have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
      exact_mod_cast (show n - 1 + 1 = n by omega)
    linear_combination ((n - 1 + k)! : ℝ) * hcast
  have hsub_succ : ((n - k)! : ℝ) = ((n - k : ℕ) : ℝ) * ((n - k - 1)! : ℝ) := by
    have h1 : n - k = (n - k - 1) + 1 := by omega
    conv_lhs => rw [h1, Nat.factorial_succ]
    push_cast
    rw [show ((n - k - 1 : ℕ) : ℝ) + 1 = ((n - k : ℕ) : ℝ) by exact_mod_cast h1.symm]
  have hdiff_2k : ((n + k : ℕ) : ℝ) - ((n - k : ℕ) : ℝ) = 2 * (k : ℝ) := by
    have h1 : n - k + 2 * k = n + k := by omega
    have hcast : ((n - k : ℕ) : ℝ) + 2 * (k : ℝ) = ((n + k : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  rw [hsub_eq]
  have hRHS :
      (-1 : ℝ) ^ (k - 1) * (((k - 1)! : ℝ) ^ 2) * ((n - k - 1)! : ℝ) / (2 * (k : ℝ) * ((n - 1 + k)! : ℝ)) -
      (-1 : ℝ) ^ (k - 1) * (((k - 1)! : ℝ) ^ 2) * ((n - k)! : ℝ) / (2 * (k : ℝ) * ((n + k)! : ℝ)) =
      (-1 : ℝ) ^ (k - 1) * (((k - 1)! : ℝ) ^ 2) * ((n - k - 1)! : ℝ) / ((n + k)! : ℝ) := by
    have hne_add : ((n + k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [hnk_succ, hsub_succ]
    field_simp [hk0, hne_nk1, hne_add]
    have hnum : ((n + k : ℕ) : ℝ) = ((n - k : ℕ) : ℝ) + 2 * (k : ℝ) := by linarith
    rw [hnum]
    ring
  rw [hRHS, ← hfact_eq]
  have hfnz : ((n - k - 1)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp [hn0, hP2, hfnz]

private lemma F_zero (n : ℕ) : F n 0 = 1 / (n : ℝ) ^ 3 := by
  unfold F
  simp

private lemma F_last (n : ℕ) (hn : 1 ≤ n) :
    F n (n - 1) = 2 * (-1 : ℝ) ^ (n - 1) / ((n : ℝ) ^ 3 * (Nat.centralBinom n : ℝ)) := by
  unfold F
  have hfact := prod_sq_sub_eq_fact n (n - 1) (by omega)
  have h0 : n - (n - 1) - 1 = 0 := by omega
  have h2n1 : n + (n - 1) = 2 * n - 1 := by omega
  rw [h0, h2n1, Nat.factorial_zero, Nat.cast_one, mul_one] at hfact
  have hPne : (∏ j ∈ Finset.Icc 1 (n - 1), ((n : ℝ) ^ 2 - (j : ℝ) ^ 2)) ≠ 0 :=
    prod_sq_sub_ne_zero n (n - 1) (by omega)
  have hcb : (Nat.centralBinom n : ℝ) * ((n ! : ℝ) ^ 2) = ((2 * n)! : ℝ) := by
    have h1 := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    rw [show 2 * n - n = n by omega] at h1
    have h2 : Nat.centralBinom n * n ! ^ 2 = (2 * n)! := by
      unfold Nat.centralBinom; rw [sq]; linarith
    exact_mod_cast h2
  have h2n : ((2 * n)! : ℝ) = 2 * (n : ℝ) * ((2 * n - 1)! : ℝ) := by
    have h1 : 2 * n = (2 * n - 1) + 1 := by omega
    conv_lhs => rw [h1, Nat.factorial_succ]
    push_cast
    rw [show ((2 * n - 1 : ℕ) : ℝ) + 1 = 2 * (n : ℝ) by exact_mod_cast h1.symm]
  have hnfact : (n ! : ℝ) = (n : ℝ) * ((n - 1)! : ℝ) := by
    have h1 : n = (n - 1) + 1 := by omega
    conv_lhs => rw [h1, Nat.factorial_succ]
    push_cast
    rw [show ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) by exact_mod_cast h1.symm]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcb0 : (Nat.centralBinom n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.centralBinom_pos n).ne'
  rw [div_eq_div_iff (mul_ne_zero (pow_ne_zero 3 hn0) hPne) (mul_ne_zero (pow_ne_zero 3 hn0) hcb0)]
  have hkey : (n : ℝ) * (Nat.centralBinom n : ℝ) * (((n - 1)! : ℝ) ^ 2) =
      2 * ((2 * n - 1)! : ℝ) := by
    have : (Nat.centralBinom n : ℝ) * ((n : ℝ) * ((n - 1)! : ℝ)) ^ 2 = 2 * (n : ℝ) * ((2 * n - 1)! : ℝ) := by
      rw [← hnfact, hcb, h2n]
    apply mul_left_cancel₀ hn0
    linarith
  calc (-1 : ℝ) ^ (n - 1) * (((n - 1)! : ℝ) ^ 2) * ((n : ℝ) ^ 3 * (Nat.centralBinom n : ℝ))
      = (-1 : ℝ) ^ (n - 1) * (n : ℝ) ^ 2 * ((n : ℝ) * (Nat.centralBinom n : ℝ) * (((n - 1)! : ℝ) ^ 2)) := by ring
    _ = (-1 : ℝ) ^ (n - 1) * (n : ℝ) ^ 2 * (2 * ((2 * n - 1)! : ℝ)) := by rw [hkey]
    _ = (-1 : ℝ) ^ (n - 1) * (n : ℝ) ^ 2 * (2 * ((n : ℝ) * ∏ j ∈ Finset.Icc 1 (n - 1), ((n : ℝ) ^ 2 - (j : ℝ) ^ 2))) := by
        rw [← hfact]
    _ = 2 * (-1 : ℝ) ^ (n - 1) * ((n : ℝ) ^ 3 * ∏ j ∈ Finset.Icc 1 (n - 1), ((n : ℝ) ^ 2 - (j : ℝ) ^ 2)) := by ring

private lemma H_diag (k : ℕ) (hk : 1 ≤ k) :
    H k k = (-1 : ℝ) ^ (k - 1) / (2 * (k : ℝ) ^ 3 * (Nat.centralBinom k : ℝ)) := by
  unfold H
  rw [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, mul_one, ← two_mul]
  have hcb : (Nat.centralBinom k : ℝ) * ((k ! : ℝ) ^ 2) = ((2 * k)! : ℝ) := by
    have h1 := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
    rw [show 2 * k - k = k by omega] at h1
    have h2 : Nat.centralBinom k * k ! ^ 2 = (2 * k)! := by
      unfold Nat.centralBinom; rw [sq]; linarith
    exact_mod_cast h2
  have hkfact : (k ! : ℝ) = (k : ℝ) * ((k - 1)! : ℝ) := by
    have h1 : k = (k - 1) + 1 := by omega
    conv_lhs => rw [h1, Nat.factorial_succ]
    push_cast
    rw [show ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) by exact_mod_cast h1.symm]
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h2kf : ((2 * k)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hcb0 : (Nat.centralBinom k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.centralBinom_pos k).ne'
  rw [div_eq_div_iff (mul_ne_zero (mul_ne_zero two_ne_zero hk0) h2kf)
    (mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero 3 hk0)) hcb0)]
  rw [← hcb, hkfact]
  ring

private lemma partial_sum_identity (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) ^ 3) -
      (5 / 2 : ℝ) * (∑ n ∈ Finset.Icc 1 N, (-1 : ℝ) ^ (n - 1) / ((n : ℝ) ^ 3 * (Nat.centralBinom n : ℝ))) =
    -(∑ k ∈ Finset.Icc 1 N, H N k) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hIcc : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : N + 1 ∉ Finset.Icc 1 N := by simp
    rw [hIcc, Finset.sum_insert hnot, Finset.sum_insert hnot, Finset.sum_insert hnot]
    -- Telescope F (N+1) 0 - F (N+1) N = ∑ k ∈ Icc 1 N, (H N k - H (N+1) k)
    have htele : F (N + 1) 0 - F (N + 1) N =
        ∑ k ∈ Finset.Icc 1 N, (H N k - H (N + 1) k) := by
      have h1 : ∀ M m : ℕ, ∑ k ∈ Finset.Icc 1 m, (F M (k - 1) - F M k) = F M 0 - F M m := by
        intro M m
        induction m with
        | zero => simp
        | succ m ihm =>
          have hI : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
            ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hI, Finset.sum_insert (by simp)]
          simp only [Nat.add_sub_cancel]
          linarith
      rw [← h1 (N + 1) N]
      refine Finset.sum_congr rfl fun k hk => ?_
      simp only [Finset.mem_Icc] at hk
      exact F_sub_eq_H_sub (N + 1) k hk.1 (by omega)
    have hFlast := F_last (N + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hFlast
    rw [Finset.sum_sub_distrib, F_zero, hFlast] at htele
    have hHdiag := H_diag (N + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hHdiag ⊢
    have hH2 : H (N + 1) (N + 1) =
        (1 / 2 : ℝ) * ((-1 : ℝ) ^ N / (((N + 1 : ℕ) : ℝ) ^ 3 * (Nat.centralBinom (N + 1) : ℝ))) := by
      rw [hHdiag]; ring
    rw [hH2]
    linear_combination ih + htele

private lemma abs_H_le (N k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    |H N k| ≤ 1 / (2 * (N : ℝ) ^ 2) := by
  unfold H
  have h1 : |(-1 : ℝ) ^ (k - 1)| = 1 := by rw [abs_pow, abs_neg, abs_one, one_pow]
  have hnum_nn : 0 ≤ (((k - 1)! : ℝ) ^ 2) * ((N - k)! : ℝ) := by positivity
  have hden_pos : 0 < 2 * (k : ℝ) * ((N + k)! : ℝ) := by positivity
  rw [abs_div, abs_mul, abs_mul, h1, one_mul, abs_of_nonneg (sq_nonneg _),
    abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos hden_pos]
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  rw [div_le_div_iff₀ hden_pos (by positivity)]
  -- Need: ((k-1)!)^2 * (N-k)! * (2 * N^2) ≤ 1 * (2 * k * (N+k)!)
  -- Equivalently: ((k-1)!)^2 * (N-k)! * N^2 ≤ k * (N+k)!
  -- Note: (N-k)! * k! ≤ N! (since C(N, k) ≥ 1), and N! * (k-1)! * N ≤ (N+k)!
  -- Even simpler: (N-k)! * (k-1)! * N ≤ N! (wait: N! = C(N, k) * k! * (N-k)! ≥ k! * (N-k)! = k * (k-1)! * (N-k)!)
  -- And (N+k)! = (N+k) * ... * (N+1) * N! ≥ N * (k-1)! * N! ? Wait: for k=1: (N+1)! = (N+1) * N! ≥ N * 0! * N!.
  -- For general k ≥ 1: (N+k)! ≥ (N+1) * (k-1)! * N! ? Wait: (N+k)...(N+2) has k-1 factors all ≥ k-1 ≥ j!
  -- YES!! (N+k)! = N! * ∏_{j=1}^k (N + j) ≥ N! * (N + 1) * ∏_{j=2}^k (j - 1) = N! * (N + 1) * (k - 1)! !!
  -- Let's check for k = 1: (N+1)! = N! * (N+1) * 0! (exact!)
  -- For k = 2: (N+2)! = N! * (N+1) * (N+2) ≥ N! * (N+1) * 1!
  -- And N! ≥ k * (k-1)! * (N-k)! (from C(N, k) ≥ 1)!!
  --Wait: multiplying those two gives:
  --  (N+k)! ≥ (N+1) * (k-1)! * N! ≥ (N+1) * (k-1)! * k * (k-1)! * (N-k)! ≥ N * k * ((k-1)!)^2 * (N-k)!
  -- Almost! That has ONE factor of N, we want N^2!
  -- Wait: for k = 1: (N+1)! = (N+1) * N * (N-1)! ≥ N^2 * (N-1)! (here k=1 so k * (N+1)! ≥ N^2 * (N-1)!)
  -- For k ≥ 2: C(N, k) = N * (N-1)... / k! ≥ 1, wait: for k = N, (N-k)! = 0! = 1, and k * (2N)! vs N^2 * ((N-1)!)^2:
  --  (2N)! = C(2N, N) * (N!)^2 = C(2N, N) * N^2 * ((N-1)!)^2 ≥ 2 * N^2 * ((N-1)!)^2!
  -- SO IN GENERAL: (N+k)! = (N+k) * ... * (N-k+1) * (N-k)!
  -- Better: ∏_{j=1}^k (N + j) ≥ N * (k-1)! AND (N! / (N-k)!) = ∏_{j=0}^{k-1} (N - j) ≥ N * (k-1)! (since for k ≥ 2, N - j ≥ k - j)!
  -- CHECK THAT!!
  --   1) ∏_{j=0}^{k-1} (N - j) = N * ∏_{j=1}^{k-1} (N - j) ≥ N * ∏_{j=1}^{k-1} (k - j) = N * (k-1)! !!
  --   2) ∏_{j=1}^k (N + j) = (N + 1) * ∏_{j=2}^k (N + j) ≥ N * ∏_{j=2}^k j = N * k! / 1 ≥ N * (k-1)! !!
  -- MULTIPLY (1) AND (2):
  --   (N+k)! / (N-k)! = (∏_{j=1}^k (N+j)) * (∏_{j=0}^{k-1} (N-j)) ≥ (N * (k-1)!) * (N * (k-1)!) = N^2 * ((k-1)!)^2 !!
  -- AND WE EVEN HAVE AN EXTRA FACTOR OF k ON THE RHS!!
  have hA : N * (k - 1)! * (N - k)! ≤ N ! := by
    have h1 : k.choose 1 * (k - 1)! * (N - k)! ≤ N ! := by
      have hch := Nat.choose_mul_factorial_mul_factorial hkN
      have hpos : 1 ≤ N.choose k := Nat.choose_pos hkN
      have hkf : k ! = k * (k - 1)! := by
        conv_lhs => rw [← Nat.sub_add_cancel hk1]
        rw [Nat.factorial_succ, Nat.sub_add_cancel hk1]
      rw [Nat.choose_one_right, ← hkf]
      nlinarith
    -- Actually prove N * (k-1)! * (N-k)! ≤ N! directly via C(N-1, k-1) ≥ 1!
    have hch := Nat.choose_mul_factorial_mul_factorial (show k - 1 ≤ N - 1 by omega)
    have hpos : 1 ≤ (N - 1).choose (k - 1) := Nat.choose_pos (by omega)
    rw [show N - 1 - (k - 1) = N - k by omega] at hch
    have hNf : N ! = N * (N - 1)! := by
      conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ N by omega)]
      rw [Nat.factorial_succ, Nat.sub_add_cancel (show 1 ≤ N by omega)]
    rw [hNf]
    have hle : (k - 1)! * (N - k)! ≤ (N - 1)! := by nlinarith
    rw [mul_assoc]
    exact Nat.mul_le_mul_left N hle
  have hB : N * (k - 1)! * N ! ≤ (N + k)! := by
    have hch := Nat.choose_mul_factorial_mul_factorial (show k - 1 ≤ N + k - 1 by omega)
    have hpos : 1 ≤ (N + k - 1).choose (k - 1) := Nat.choose_pos (by omega)
    rw [show N + k - 1 - (k - 1) = N by omega] at hch
    have hle : (k - 1)! * N ! ≤ (N + k - 1)! := by nlinarith
    have hNk : (N + k)! = (N + k) * (N + k - 1)! := by
      conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ N + k by omega)]
      rw [Nat.factorial_succ, Nat.sub_add_cancel (show 1 ≤ N + k by omega)]
    rw [hNk]
    calc N * (k - 1)! * N ! = N * ((k - 1)! * N !) := by ring
      _ ≤ (N + k) * (N + k - 1)! := Nat.mul_le_mul (by omega) hle
  have hnat : (k - 1)! ^ 2 * (N - k)! * N ^ 2 ≤ k * (N + k)! := by
    have hNfnz : 0 < N ! := Nat.factorial_pos N
    have h1 : (k - 1)! ^ 2 * (N - k)! * N ^ 2 * N ! ≤ (N + k)! * N ! := by
      calc (k - 1)! ^ 2 * (N - k)! * N ^ 2 * N !
          = (N * (k - 1)! * (N - k)!) * (N * (k - 1)! * N !) := by ring
        _ ≤ N ! * (N + k)! := Nat.mul_le_mul hA hB
        _ = (N + k)! * N ! := by ring
    have h2 : (k - 1)! ^ 2 * (N - k)! * N ^ 2 ≤ (N + k)! :=
      Nat.le_of_mul_le_mul_right h1 hNfnz
    calc (k - 1)! ^ 2 * (N - k)! * N ^ 2 ≤ 1 * (N + k)! := by linarith
      _ ≤ k * (N + k)! := Nat.mul_le_mul_right _ hk1
  have hreal : (((k - 1)! : ℝ) ^ 2) * ((N - k)! : ℝ) * ((N : ℝ) ^ 2) ≤ (k : ℝ) * ((N + k)! : ℝ) := by
    exact_mod_cast hnat
  linarith

private lemma real_apery_identity :
    (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 3) =
      (5 / 2 : ℝ) * ∑' n : ℕ, (-1 : ℝ) ^ n / (((n : ℝ) + 1) ^ 3 * (Nat.centralBinom (n + 1) : ℝ)) := by
  let z (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1) ^ 3
  let a (n : ℕ) : ℝ := (-1) ^ n / (((n : ℝ) + 1) ^ 3 * (Nat.centralBinom (n + 1) : ℝ))
  change (∑' n, z n) = (5 / 2 : ℝ) * ∑' n, a n
  have hsum_zeta : Summable z := by
    have h1 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 3) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    simpa only [z, Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr h1
  have hsum_apery : Summable a := by
    refine Summable.of_norm_bounded (g := z) hsum_zeta fun n => ?_
    dsimp [z, a]
    have hcbpos : (0 : ℝ) < (Nat.centralBinom (n + 1) : ℝ) :=
      Nat.cast_pos.mpr (Nat.centralBinom_pos (n + 1))
    rw [abs_div, abs_pow, abs_neg, abs_one, one_pow,
      abs_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) + 1) ^ 3 * (Nat.centralBinom (n + 1) : ℝ))]
    have hcb1 : (1 : ℝ) ≤ (Nat.centralBinom (n + 1) : ℝ) := by
      exact_mod_cast Nat.centralBinom_pos (n + 1)
    exact div_le_div_of_nonneg_left zero_le_one (by positivity) (le_mul_of_one_le_right (by positivity) hcb1)
  have htend_diff := hsum_zeta.hasSum.tendsto_sum_nat.sub
    (hsum_apery.hasSum.tendsto_sum_nat.const_mul (5 / 2 : ℝ))
  have reindex (N : ℕ) (f : ℕ → ℝ) :
      (∑ n ∈ Finset.range N, f (n + 1)) = ∑ n ∈ Finset.Icc 1 N, f n := by
    refine Finset.sum_nbij (fun n => n + 1) ?_ ?_ ?_ ?_
    · intro n hn; simp only [Finset.mem_range] at hn; simp only [Finset.mem_Icc]; omega
    · intro a _ b _ h; dsimp only at h; omega
    · intro n hn; simp only [Finset.mem_coe, Finset.mem_Icc] at hn
      exact ⟨n - 1, by simp only [Finset.mem_coe, Finset.mem_range]; omega, by dsimp only; omega⟩
    · intro n _; rfl
  have htend_zero : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, z n) - (5 / 2 : ℝ) * ∑ n ∈ Finset.range N, a n)
      atTop (nhds 0) := by
    have hreindex : ∀ N : ℕ,
        (∑ n ∈ Finset.range N, z n) - (5 / 2 : ℝ) * ∑ n ∈ Finset.range N, a n =
        -(∑ k ∈ Finset.Icc 1 N, H N k) := by
      intro N
      rw [← partial_sum_identity N, ← reindex, ← reindex]
      simp only [z, a, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    simp_rw [hreindex]
    refine squeeze_zero_norm' (a := fun N : ℕ => (1 : ℝ) / (2 * (N : ℝ))) ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
      rw [Real.norm_eq_abs, abs_neg]
      calc |∑ k ∈ Finset.Icc 1 N, H N k|
          ≤ ∑ k ∈ Finset.Icc 1 N, |H N k| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k ∈ Finset.Icc 1 N, (1 : ℝ) / (2 * (N : ℝ) ^ 2) :=
            Finset.sum_le_sum fun k hk => abs_H_le N k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
        _ = (N : ℝ) * (1 / (2 * (N : ℝ) ^ 2)) := by
            rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        _ = 1 / (2 * (N : ℝ)) := by
            have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
            field_simp [hN0]
    · have hinv : Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ)) atTop (nhds 0) :=
        tendsto_one_div_atTop_nhds_zero_nat
      simpa [div_eq_mul_inv, mul_comm, mul_assoc] using hinv.const_mul (1 / 2 : ℝ)
  exact sub_eq_zero.mp (tendsto_nhds_unique htend_diff htend_zero)

end OMA_AperySeries

theorem OMA.solution : type_of% @RiemannZetaValues.apery_central_binomial_series := by
  have hzeta : riemannZeta (3 : ℂ) = ∑' n : ℕ, (1 : ℂ) / ((n : ℂ) + 1) ^ (3 : ℕ) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by norm_num : 1 < (3 : ℂ).re)]
    congr 1; ext n
    rw [show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
  rw [hzeta]
  have hcast := congrArg (Complex.ofReal) OMA_AperySeries.real_apery_identity
  rw [Complex.ofReal_tsum, Complex.ofReal_mul, Complex.ofReal_tsum] at hcast
  simpa only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_add,
    Complex.ofReal_one, Complex.ofReal_neg, Complex.ofReal_natCast, Complex.ofReal_ofNat] using hcast
