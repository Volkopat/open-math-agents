import FormalConjectures.ErdosProblems.«682»
import Mathlib

/-!
# Erdős Problem 682 (Exceptional Prime Gap Count)

This file provides a self-contained Lean 4 proof of the theorem of
Ayla Gafni and Terence Tao (arXiv:2508.06463, Theorem 1.1):
the number of exceptional prime gaps `(p_n, p_{n+1})` with `p_n ∈ [X, 2X]`
containing no integer `m ∈ (p_n, p_{n+1})` with `m.minFac ≥ p_{n+1} - p_n`
is `O(X / (log X)^2)`.

Following Gafni and Tao (2025) and the centered-moment framework of
Montgomery and Soundararajan (2004), the proof proceeds in five parts:
1. Elementary harmonic and dyadic Chebyshev--Mertens bounds;
2. A two-dimensional Selberg upper-bound sieve (built on Mathlib's
   `BoundingSieve`) for prime pairs in arithmetic progressions;
3. An elementary martingale-induction proof of the even centered moment bound
   for integers coprime to a finite prime set in short intervals;
4. Brun's pure sieve (truncated inclusion-exclusion) transferring the 6th
   centered moment to `[X, 2X]` and bounding empty windows of length `H`;
5. Four-regime assembly (boundary, huge, medium-long, and short gaps).
-/

namespace Erdos682Proof


section Mod1
open Finset Real Nat


lemma one_div_le_log_div_succ (k : ℕ) (hk : 1 ≤ k) :
    (1 : ℝ) / (k + 1 : ℕ) ≤ Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) := by
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1_pos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  rw [← Real.log_div hk1_pos.ne' hk_pos.ne']
  have h1 : (1 : ℝ) - (k : ℝ) / ((k + 1 : ℕ) : ℝ) ≤
      Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ)) := by
    have hinv := Real.one_sub_inv_le_log_of_pos (div_pos hk1_pos hk_pos)
    simpa [inv_div] using hinv
  have h2 : (1 : ℝ) - (k : ℝ) / ((k + 1 : ℕ) : ℝ) = (1 : ℝ) / ((k + 1 : ℕ) : ℝ) := by
    push_cast
    field_simp
    ring
  linarith

lemma log_div_succ_le_one_div (k : ℕ) (hk : 1 ≤ k) :
    Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) ≤ (1 : ℝ) / k := by
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1_pos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  rw [← Real.log_div hk1_pos.ne' hk_pos.ne']
  have h1 : Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ)) ≤
      ((k + 1 : ℕ) : ℝ) / (k : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hk1_pos hk_pos)
  have h2 : ((k + 1 : ℕ) : ℝ) / (k : ℝ) - 1 = (1 : ℝ) / k := by
    push_cast
    field_simp
    ring
  linarith

lemma sum_one_div_Icc_le_one_add_log (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k ≤ 1 + Real.log (max 1 n : ℕ) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rcases m with _ | m
    · simp
    · rw [Finset.sum_Icc_succ_top (by omega)]
      have hm1 : 1 ≤ m + 1 := by omega
      have hstep := one_div_le_log_div_succ (m + 1) hm1
      have hmax1 : max 1 (m + 1) = m + 1 := by omega
      have hmax2 : max 1 (m + 2) = m + 2 := by omega
      rw [hmax1] at ih
      rw [hmax2]
      have hcast : ((m + 1 + 1 : ℕ) : ℝ) = ((m + 2 : ℕ) : ℝ) := by norm_cast
      rw [hcast] at hstep
      linarith

lemma log_le_sum_one_div_Icc (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n + 1 : ℝ) ≤ ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases m with _ | m
    · simp only [zero_add, Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, div_one]
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      norm_num at h ⊢
      linarith
    · rw [Finset.sum_Icc_succ_top (by omega)]
      have hih := ih (by omega)
      have hstep := log_div_succ_le_one_div (m + 2) (by omega)
      have hcast1 : ((m + 1 : ℕ) : ℝ) + 1 = ((m + 2 : ℕ) : ℝ) := by push_cast; ring
      have hcast2 : ((m + 2 + 1 : ℕ) : ℝ) = ((m + 1 + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
      have hcast3 : ((m + 1 + 1 : ℕ) : ℝ) = ((m + 2 : ℕ) : ℝ) := by push_cast; ring
      rw [hcast1] at hih
      rw [hcast2] at hstep
      rw [hcast3]
      linarith

lemma sum_one_div_odd_ge (B : ℕ) (hB : 3 ≤ B) :
    (1 / 2 : ℝ) * Real.log ((B : ℝ) / 2) ≤
      ∑ k ∈ (Finset.Icc 1 B).filter Odd, (1 : ℝ) / k := by
  set m := (B + 1) / 2
  have hm_ge : 2 ≤ m := by omega
  have hlog : Real.log ((B : ℝ) / 2) ≤ Real.log (m + 1 : ℝ) := by
    apply Real.log_le_log (by positivity)
    have : B ≤ 2 * m := by omega
    have hcast : (B : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast this
    linarith
  have hharm : Real.log (m + 1 : ℝ) ≤ ∑ j ∈ Finset.Icc 1 m, (1 : ℝ) / j :=
    log_le_sum_one_div_Icc m (by omega)
  have hsub : (Finset.Icc 1 m).image (fun j => 2 * j - 1) ⊆ (Finset.Icc 1 B).filter Odd := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_Icc] at hx
    rcases hx with ⟨j, ⟨hj1, hjm⟩, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, by omega⟩, ⟨j - 1, by omega⟩⟩
  have hsum_le : ∑ j ∈ Finset.Icc 1 m, (1 : ℝ) / (2 * j) ≤
      ∑ k ∈ (Finset.Icc 1 B).filter Odd, (1 : ℝ) / k := by
    calc ∑ j ∈ Finset.Icc 1 m, (1 : ℝ) / (2 * j)
        ≤ ∑ j ∈ Finset.Icc 1 m, (1 : ℝ) / (2 * j - 1 : ℕ) := by
          apply Finset.sum_le_sum
          intro j hj
          simp only [Finset.mem_Icc] at hj
          have hpos : (0 : ℝ) < (2 * j - 1 : ℕ) := by exact_mod_cast (show 0 < 2 * j - 1 by omega)
          have hle : ((2 * j - 1 : ℕ) : ℝ) ≤ 2 * (j : ℝ) := by
            have : 2 * j - 1 ≤ 2 * j := by omega
            exact_mod_cast this
          exact one_div_le_one_div_of_le hpos hle
      _ = ∑ k ∈ (Finset.Icc 1 m).image (fun j : ℕ => (2 * j - 1 : ℕ)), (1 : ℝ) / (k : ℝ) := by
          rw [Finset.sum_image (f := fun k : ℕ => (1 : ℝ) / (k : ℝ))
              (g := fun j : ℕ => (2 * j - 1 : ℕ))]
          intro a ha b hb hab
          simp only [Finset.mem_coe, Finset.mem_Icc] at ha hb
          dsimp only at hab
          omega
      _ ≤ ∑ k ∈ (Finset.Icc 1 B).filter Odd, (1 : ℝ) / k := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro k _ _
          positivity
  have hhalf : ∑ j ∈ Finset.Icc 1 m, (1 : ℝ) / (2 * j) =
      (1 / 2 : ℝ) * ∑ j ∈ Finset.Icc 1 m, (1 : ℝ) / j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  linarith

lemma sum_inv_sq_Icc_le (N M : ℕ) (hN : 2 ≤ N) :
    ∑ k ∈ Finset.Icc N M, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 1 / ((N : ℝ) - 1) := by
  have hterm : ∀ k ∈ Finset.Icc N M,
      (1 : ℝ) / (k : ℝ) ^ 2 ≤ 1 / ((k : ℝ) - 1) - 1 / (k : ℝ) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (hN.trans hk.1)
    have h1 : (0 : ℝ) < k - 1 := by linarith
    have h2 : (0 : ℝ) < k := by linarith
    rw [div_sub_div _ _ h1.ne' h2.ne']
    have : 1 * (k : ℝ) - (k - 1) * 1 = 1 := by ring
    rw [this]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  calc ∑ k ∈ Finset.Icc N M, (1 : ℝ) / (k : ℝ) ^ 2
      ≤ ∑ k ∈ Finset.Icc N M, (1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) := Finset.sum_le_sum hterm
    _ ≤ 1 / ((N : ℝ) - 1) := by
        by_cases hNM : N ≤ M
        · clear hterm
          have htel : ∑ k ∈ Finset.Icc N M, (1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) =
              1 / ((N : ℝ) - 1) - 1 / (M : ℝ) := by
            induction M, hNM using Nat.le_induction with
            | base => simp
            | succ m hm ih =>
              rw [Finset.sum_Icc_succ_top (by omega), ih]
              push_cast
              ring
          rw [htel]
          have hMpos : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
          linarith
        · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
          have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by
            have : (2 : ℝ) ≤ N := by exact_mod_cast hN
            linarith
          positivity

lemma dyadic_prime_recip_sum (k : ℕ) (hk : 1 ≤ k) :
    ∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime, (1 : ℝ) / p ≤ 4 / k := by
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hstep : ∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime, (1 : ℝ) / p ≤
      (1 / ((2 : ℝ) ^ k * (k * Real.log 2))) *
        ∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime, Real.log p := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ico] at hp
    have hp_ge : (2 : ℝ) ^ k ≤ p := by exact_mod_cast hp.1.1
    have hp_pos : (0 : ℝ) < p := lt_of_lt_of_le h2k_pos hp_ge
    have hlogp : k * Real.log 2 ≤ Real.log p := by
      have h1 : Real.log ((2 : ℝ) ^ k) ≤ Real.log p := Real.log_le_log h2k_pos hp_ge
      rwa [Real.log_pow] at h1
    rw [one_div_mul_eq_div, div_le_div_iff₀ hp_pos (by positivity)]
    have hmul := mul_le_mul hp_ge hlogp (by positivity) (by positivity)
    linarith
  have htheta : ∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime, Real.log p ≤
      Chebyshev.theta ((2 ^ (k + 1) : ℕ) : ℝ) := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_Ico] at hp
      exact Nat.mem_primesLE.mpr ⟨le_of_lt hp.1.2, hp.2⟩
    · intro p _ _
      exact Real.log_natCast_nonneg p
  have hcheb : Chebyshev.theta ((2 ^ (k + 1) : ℕ) : ℝ) ≤ Real.log 4 * (2 ^ (k + 1) : ℕ) :=
    Chebyshev.theta_le_log4_mul_x (by positivity)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    ring
  calc ∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime, (1 : ℝ) / p
      ≤ (1 / ((2 : ℝ) ^ k * (k * Real.log 2))) * (Real.log 4 * (2 ^ (k + 1) : ℕ)) := by
        calc _ ≤ (1 / ((2 : ℝ) ^ k * (k * Real.log 2))) *
              ∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime, Real.log p := hstep
          _ ≤ (1 / ((2 : ℝ) ^ k * (k * Real.log 2))) *
              Chebyshev.theta ((2 ^ (k + 1) : ℕ) : ℝ) := by gcongr
          _ ≤ _ := by gcongr
    _ = 4 / k := by
        rw [hlog4]
        push_cast
        rw [pow_succ]
        field_simp
        ring

lemma sum_inv_primesBelow_le (n : ℕ) :
    ∑ p ∈ n.primesBelow, (1 : ℝ) / p ≤ 4 * Real.log (Real.log (n + 10 : ℕ)) + 10 := by
  have hlog10_gt2 : 2 < Real.log (n + 10 : ℕ) := by
    have h1 : Real.exp 2 < (n + 10 : ℕ) := by
      have hexp : Real.exp 2 < 8 := by
        have h1 := Real.exp_one_lt_d9
        have h0 := Real.exp_pos 1
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
        nlinarith
      have h10 : (10 : ℝ) ≤ (n + 10 : ℕ) := by exact_mod_cast (show 10 ≤ n + 10 by omega)
      linarith
    exact (Real.lt_log_iff_exp_lt (by positivity)).mpr h1
  have hloglog_pos : 0 < Real.log (Real.log (n + 10 : ℕ)) := Real.log_pos (by linarith)
  by_cases hn : n ≤ 2
  · have hemp : n.primesBelow = ∅ := by
      ext p
      simp only [Nat.mem_primesBelow, Finset.notMem_empty, iff_false, not_and]
      intro hlt hp
      have := hp.two_le
      omega
    rw [hemp, Finset.sum_empty]
    linarith
  · push Not at hn
    set K := Nat.log 2 n + 1
    have hK_ge : 2 ≤ K := by
      have : 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by omega)
      omega
    have hsub : n.primesBelow ⊆
        (Finset.Icc 1 K).biUnion (fun k => (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime) := by
      intro p hp
      rw [Nat.mem_primesBelow] at hp
      rw [Finset.mem_biUnion]
      refine ⟨Nat.log 2 p, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        refine ⟨Nat.le_log_of_pow_le (by norm_num) (by simpa using hp.2.two_le), ?_⟩
        exact (Nat.log_mono_right hp.1.le).trans (Nat.le_succ _)
      · rw [Finset.mem_filter, Finset.mem_Ico]
        exact ⟨⟨Nat.pow_log_le_self 2 hp.2.ne_zero, Nat.lt_pow_succ_log_self (by norm_num) p⟩, hp.2⟩
    have hpw : Set.PairwiseDisjoint (↑(Finset.Icc 1 K) : Set ℕ)
        (fun k => (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime) := by
      intro k1 _ k2 _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Finset.mem_filter, Finset.mem_Ico] at hp1 hp2
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hle : 2 ^ (k1 + 1) ≤ 2 ^ k2 := Nat.pow_le_pow_right (by norm_num) hlt
        omega
      · have hle : 2 ^ (k2 + 1) ≤ 2 ^ k1 := Nat.pow_le_pow_right (by norm_num) hgt
        omega
    have hsum1 : ∑ p ∈ n.primesBelow, (1 : ℝ) / p ≤
        ∑ k ∈ Finset.Icc 1 K,
          ∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime, (1 : ℝ) / p := by
      calc ∑ p ∈ n.primesBelow, (1 : ℝ) / p
          ≤ ∑ p ∈ (Finset.Icc 1 K).biUnion
              (fun k => (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime), (1 : ℝ) / p :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
        _ = ∑ k ∈ Finset.Icc 1 K,
              ∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime, (1 : ℝ) / p :=
            Finset.sum_biUnion hpw
    have hsum2 : ∑ k ∈ Finset.Icc 1 K,
        ∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime, (1 : ℝ) / p ≤
        4 * (1 + Real.log K) := by
      calc _ ≤ ∑ k ∈ Finset.Icc 1 K, (4 : ℝ) / k := by
              apply Finset.sum_le_sum
              intro k hk
              exact dyadic_prime_recip_sum k (Finset.mem_Icc.mp hk).1
        _ = 4 * ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / k := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              ring
        _ ≤ 4 * (1 + Real.log (max 1 K : ℕ)) := by
              gcongr
              exact sum_one_div_Icc_le_one_add_log K
        _ = 4 * (1 + Real.log K) := by
              rw [show max 1 K = K by omega]
    have hK_bound : (K : ℝ) ≤ 4 * Real.log (n + 10 : ℕ) := by
      have hpow : (2 : ℝ) ^ (Nat.log 2 n) ≤ (n : ℝ) := by
        exact_mod_cast Nat.pow_log_le_self 2 (by omega)
      have hlog_le : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log (n + 10 : ℕ) := by
        calc (Nat.log 2 n : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ (Nat.log 2 n)) := by
              rw [Real.log_pow]
          _ ≤ Real.log (n : ℝ) := Real.log_le_log (by positivity) hpow
          _ ≤ Real.log (n + 10 : ℕ) := by
              apply Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
              exact_mod_cast (show n ≤ n + 10 by omega)
      have hlog2_ge : (1 / 2 : ℝ) < Real.log 2 := by
        have h := Real.exp_one_lt_d9
        have h2 : Real.exp (1 / 2 : ℝ) < 2 := by
          have hsq : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp 1 := by
            rw [← Real.exp_nat_mul]; norm_num
          nlinarith [Real.exp_pos (1 / 2 : ℝ)]
        exact (Real.lt_log_iff_exp_lt (by norm_num)).mpr h2
      have hnatlog : (Nat.log 2 n : ℝ) ≤ 2 * Real.log (n + 10 : ℕ) := by nlinarith
      have hK_eq : (K : ℝ) = (Nat.log 2 n : ℝ) + 1 := by
        simp only [K, Nat.cast_add, Nat.cast_one]
      linarith
    have hlogK : Real.log K ≤ Real.log 4 + Real.log (Real.log (n + 10 : ℕ)) := by
      calc Real.log K ≤ Real.log (4 * Real.log (n + 10 : ℕ)) :=
            Real.log_le_log (by exact_mod_cast (show 0 < K by omega)) hK_bound
        _ = Real.log 4 + Real.log (Real.log (n + 10 : ℕ)) :=
            Real.log_mul (by norm_num) (by linarith)
    have hlog4_lt : Real.log 4 < 3 / 2 := by
      have h1 : (4 : ℝ) < Real.exp (3 / 2 : ℝ) := by
        have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
        have hsq : (Real.exp (3 / 2 : ℝ)) ^ 2 = (Real.exp 1) ^ 3 := by
          rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
        nlinarith [Real.exp_pos (3 / 2 : ℝ), sq_nonneg (Real.exp 1)]
      exact (Real.log_lt_iff_lt_exp (by norm_num)).mpr h1
    linarith

lemma neg_log_one_sub_le_two_mul {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    -Real.log (1 - t) ≤ 2 * t := by
  have h1 : 0 < 1 - t := by linarith
  have h2 : Real.exp (-2 * t) ≤ 1 - t := by
    have hconv : Real.exp (-2 * t) ≤ (1 - 2 * t) * Real.exp 0 + (2 * t) * Real.exp (-1) := by
      have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-1 : ℝ))
        (show 0 ≤ 1 - 2 * t by linarith) (show 0 ≤ 2 * t by linarith) (by ring)
      simpa [smul_eq_mul] using h
    have hexp1 : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
      linarith [Real.exp_one_gt_d9]
    rw [Real.exp_zero] at hconv
    nlinarith
  have h3 := Real.log_le_log (Real.exp_pos _) h2
  rw [Real.log_exp] at h3
  linarith

lemma prod_inv_one_sub_inv_primesBelow_le (n : ℕ) :
    ∏ p ∈ n.primesBelow, (1 - (1 : ℝ) / p)⁻¹ ≤ Real.exp 20 * (Real.log (n + 10 : ℕ)) ^ 8 := by
  have hpos : ∀ p ∈ n.primesBelow, 0 < 1 - (1 : ℝ) / p := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
    have : (1 : ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    linarith
  have hprod_pos : 0 < ∏ p ∈ n.primesBelow, (1 - (1 : ℝ) / p)⁻¹ :=
    Finset.prod_pos fun p hp => inv_pos.mpr (hpos p hp)
  have hlog10_pos : 0 < Real.log (n + 10 : ℕ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n + 10 by omega))
  rw [← Real.log_le_log_iff hprod_pos (by positivity)]
  rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp, Real.log_pow]
  rw [Real.log_prod (fun p hp => (inv_pos.mpr (hpos p hp)).ne')]
  have hstep : ∑ p ∈ n.primesBelow, Real.log ((1 - (1 : ℝ) / p)⁻¹) ≤
      2 * ∑ p ∈ n.primesBelow, (1 : ℝ) / p := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    rw [Real.log_inv]
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
    exact neg_log_one_sub_le_two_mul (by positivity) (one_div_le_one_div_of_le (by norm_num) hp2)
  linarith [sum_inv_primesBelow_le n]

lemma prod_one_sub_inv_primesBelow_pos (n : ℕ) :
    0 < ∏ p ∈ n.primesBelow, (1 - (1 : ℝ) / p) := by
  apply Finset.prod_pos
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
  have : (1 : ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
  linarith

lemma one_le_prod_real {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 1 ≤ f i) :
    1 ≤ ∏ i ∈ s, f i := by
  simpa using Finset.prod_le_prod (s := s) (f := fun _ => (1 : ℝ)) (g := f)
    (fun _ _ => zero_le_one) hf

lemma prod_inv_one_sub_two_div_primes_le (n : ℕ) :
    ∏ p ∈ n.primesBelow.filter (fun p => 3 ≤ p), (1 - (2 : ℝ) / p)⁻¹ ≤
      Real.exp 2 * (∏ p ∈ n.primesBelow, (1 - (1 : ℝ) / p)⁻¹) ^ 2 := by
  set S := n.primesBelow.filter (fun p => 3 ≤ p)
  have hS_sub : S ⊆ n.primesBelow := Finset.filter_subset _ _
  have hfactor : ∀ p ∈ S,
      (1 - (2 : ℝ) / p)⁻¹ = (1 - (1 : ℝ) / p)⁻¹ ^ 2 * (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2))) := by
    intro p hp
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2
    have hne1 : (p : ℝ) ≠ 0 := by linarith
    have hne2 : (p : ℝ) - 1 ≠ 0 := by linarith
    have hne3 : (p : ℝ) - 2 ≠ 0 := by linarith
    field_simp
    ring
  rw [Finset.prod_congr rfl hfactor, Finset.prod_mul_distrib, Finset.prod_pow]
  have hS_nonneg : 0 ≤ ∏ p ∈ S, (1 - (1 : ℝ) / p)⁻¹ := by
    apply Finset.prod_nonneg
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesBelow (hS_sub hp)).two_le
    have : (1 : ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    have hpos : 0 < 1 - (1 : ℝ) / p := by linarith
    positivity
  have h1 : (∏ p ∈ S, (1 - (1 : ℝ) / p)⁻¹) ^ 2 ≤
      (∏ p ∈ n.primesBelow, (1 - (1 : ℝ) / p)⁻¹) ^ 2 := by
    apply pow_le_pow_left₀ hS_nonneg
    rw [← Finset.prod_sdiff hS_sub]
    apply le_mul_of_one_le_left hS_nonneg
    apply one_le_prod_real
    intro p hp
    have hp_mem := (Finset.mem_sdiff.mp hp).1
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp_mem).two_le
    have hpos : 0 < 1 - (1 : ℝ) / p := by
      have : (1 : ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
      linarith
    exact (one_le_inv₀ hpos).mpr (by linarith [show (0 : ℝ) < 1 / p by positivity])
  have h2 : ∏ p ∈ S, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2))) ≤ Real.exp 2 := by
    calc ∏ p ∈ S, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2)))
        ≤ ∏ p ∈ S, Real.exp (1 / ((p : ℝ) * ((p : ℝ) - 2))) := by
          apply Finset.prod_le_prod
          · intro p hp
            have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2
            have hp2pos : (0 : ℝ) < (p : ℝ) - 2 := by linarith
            positivity
          · intro p _
            linarith [Real.add_one_le_exp (1 / ((p : ℝ) * ((p : ℝ) - 2)))]
      _ = Real.exp (∑ p ∈ S, 1 / ((p : ℝ) * ((p : ℝ) - 2))) := by rw [Real.exp_sum]
      _ ≤ Real.exp 2 := by
          apply Real.exp_le_exp.mpr
          have hsub2 : S ⊆ Finset.Icc 3 n := by
            intro p hp
            simp only [S, Finset.mem_filter, Nat.mem_primesBelow] at hp
            exact Finset.mem_Icc.mpr ⟨hp.2, hp.1.1.le⟩
          calc ∑ p ∈ S, 1 / ((p : ℝ) * ((p : ℝ) - 2))
              ≤ ∑ k ∈ Finset.Icc 3 n, 1 / ((k : ℝ) * ((k : ℝ) - 2)) := by
                apply Finset.sum_le_sum_of_subset_of_nonneg hsub2
                intro k hk _
                have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
                have hk2pos : (0 : ℝ) < (k : ℝ) - 2 := by linarith
                positivity
            _ ≤ ∑ k ∈ Finset.Icc 3 n, 2 / ((k - 1 : ℕ) : ℝ) ^ 2 := by
                apply Finset.sum_le_sum
                intro k hk
                have hk3 : 3 ≤ k := (Finset.mem_Icc.mp hk).1
                have hk3r : (3 : ℝ) ≤ k := by exact_mod_cast hk3
                have hk2pos : (0 : ℝ) < (k : ℝ) - 2 := by linarith
                have hk1pos : (0 : ℝ) < (k : ℝ) - 1 := by linarith
                have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
                  rw [Nat.cast_sub (by omega), Nat.cast_one]
                rw [hcast, div_le_div_iff₀ (by positivity) (by positivity)]
                nlinarith
            _ = 2 * ∑ k ∈ Finset.Icc 3 n, (1 : ℝ) / ((k - 1 : ℕ) : ℝ) ^ 2 := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro k _
                ring
            _ ≤ 2 * ∑ j ∈ Finset.Icc 2 n, (1 : ℝ) / (j : ℝ) ^ 2 := by
                gcongr
                have himg : ∑ k ∈ Finset.Icc 3 n, (1 : ℝ) / ((k - 1 : ℕ) : ℝ) ^ 2 =
                    ∑ j ∈ (Finset.Icc 3 n).image (fun k : ℕ => (k - 1 : ℕ)), (1 : ℝ) / (j : ℝ) ^ 2 := by
                  rw [Finset.sum_image (f := fun j : ℕ => (1 : ℝ) / (j : ℝ) ^ 2)
                      (g := fun k : ℕ => (k - 1 : ℕ))]
                  intro a ha b hb hab
                  simp only [Finset.mem_coe, Finset.mem_Icc] at ha hb
                  dsimp only at hab
                  omega
                rw [himg]
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro j hj
                  simp only [Finset.mem_image, Finset.mem_Icc] at hj ⊢
                  rcases hj with ⟨k, ⟨hk1, hk2⟩, rfl⟩
                  omega
                · intro _ _ _; positivity
            _ ≤ 2 * (1 / ((2 : ℝ) - 1)) := by
                gcongr
                exact sum_inv_sq_Icc_le 2 n le_rfl
            _ = 2 := by norm_num
  have hprod2_nonneg : 0 ≤ ∏ p ∈ S, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2))) := by
    apply Finset.prod_nonneg
    intro p hp
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2
    have hp2pos : (0 : ℝ) < (p : ℝ) - 2 := by linarith
    positivity
  calc (∏ p ∈ S, (1 - (1 : ℝ) / p)⁻¹) ^ 2 * ∏ p ∈ S, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2)))
      ≤ (∏ p ∈ n.primesBelow, (1 - (1 : ℝ) / p)⁻¹) ^ 2 * Real.exp 2 :=
        mul_le_mul h1 h2 hprod2_nonneg (sq_nonneg _)
    _ = Real.exp 2 * (∏ p ∈ n.primesBelow, (1 - (1 : ℝ) / p)⁻¹) ^ 2 := mul_comm _ _

lemma prod_primesBelow_eq_primorial (z : ℕ) (hz : 1 ≤ z) :
    ∏ p ∈ z.primesBelow, p = primorial (z - 1) := by
  rw [primorial_eq_prod_primesLE]
  apply Finset.prod_congr _ (fun _ _ => rfl)
  ext p
  simp only [Nat.mem_primesBelow, Nat.mem_primesLE]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩

lemma log_pow_le_const_mul_rpow {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → (Real.log (x + 10)) ^ a ≤ C * x ^ δ := by
  have hlim : Filter.Tendsto (fun x : ℝ => (Real.log (x + 10)) ^ a / x ^ δ)
      Filter.atTop (nhds 0) := by
    have h1 := isLittleO_log_rpow_rpow_atTop a hδ
    have hshift : Filter.Tendsto (fun x : ℝ => x + 10) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ 10 Filter.tendsto_id
    have hcomp := h1.tendsto_div_nhds_zero.comp hshift
    have hratio : Filter.Tendsto (fun x : ℝ => ((x + 10) / x) ^ δ) Filter.atTop (nhds 1) := by
      have hdiv : Filter.Tendsto (fun x : ℝ => (x + 10) / x) Filter.atTop (nhds 1) := by
        have h : ∀ᶠ x : ℝ in Filter.atTop, (x + 10) / x = 1 + 10 / x := by
          filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
          field_simp
        rw [Filter.tendsto_congr' h]
        have h10 : Filter.Tendsto (fun x : ℝ => (10 : ℝ) / x) Filter.atTop (nhds 0) :=
          tendsto_const_nhds.div_atTop Filter.tendsto_id
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).add h10
      have hc : ContinuousAt (fun t : ℝ => t ^ δ) 1 :=
        Real.continuousAt_rpow_const 1 δ (Or.inl one_ne_zero)
      have hcomp2 : Filter.Tendsto ((fun t : ℝ => t ^ δ) ∘ fun x : ℝ => (x + 10) / x)
          Filter.atTop (nhds ((1 : ℝ) ^ δ)) := hc.tendsto.comp hdiv
      simpa [Function.comp_def, Real.one_rpow] using hcomp2
    have hmul := hcomp.mul hratio
    simp only [zero_mul] at hmul
    refine hmul.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    simp only [Function.comp_apply]
    rw [Real.div_rpow (by linarith) hx.le]
    have hne : (x + 10) ^ δ ≠ 0 := (Real.rpow_pos_of_pos (by linarith) δ).ne'
    field_simp
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨M, hM⟩ := hlim 1 zero_lt_one
  set M' := max 1 M
  set C := max 1 ((Real.log (M' + 10)) ^ a)
  refine ⟨C, by positivity, fun x hx => ?_⟩
  by_cases hxM : x ≤ M'
  · have h1 : (Real.log (x + 10)) ^ a ≤ (Real.log (M' + 10)) ^ a := by
      apply Real.rpow_le_rpow (Real.log_nonneg (by linarith))
      · exact Real.log_le_log (by linarith) (by linarith)
      · exact ha
    have h2 : (1 : ℝ) ≤ x ^ δ := Real.one_le_rpow hx hδ.le
    calc (Real.log (x + 10)) ^ a ≤ (Real.log (M' + 10)) ^ a := h1
      _ ≤ C := le_max_right _ _
      _ ≤ C * x ^ δ := le_mul_of_one_le_right (by positivity) h2
  · push Not at hxM
    have hdist := hM x (le_trans (le_max_right 1 M) hxM.le)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by
      apply div_nonneg (Real.rpow_nonneg (Real.log_nonneg (by linarith)) a) (by positivity))] at hdist
    have hdiv : (Real.log (x + 10)) ^ a / x ^ δ ≤ C :=
      le_trans hdist.le (le_max_left _ _)
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (by linarith) δ)).mp hdiv


end Mod1


section Mod2
open Finset Real Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius


section SelbergOptimal

variable (s : BoundingSieve)

noncomputable def selbergSum (D : ℕ) : ℝ :=
  ∑ l ∈ s.prodPrimes.divisors.filter (· ≤ D), s.selbergTerms l

lemma one_le_selbergSum {D : ℕ} (hD : 1 ≤ D) : 1 ≤ selbergSum s D := by
  have h1mem : 1 ∈ s.prodPrimes.divisors.filter (· ≤ D) := by
    simp only [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨one_dvd _, s.prodPrimes_ne_zero⟩, hD⟩
  have h1eq : s.selbergTerms 1 = 1 := s.selbergTerms_isMultiplicative.map_one
  calc (1 : ℝ) = s.selbergTerms 1 := h1eq.symm
    _ ≤ selbergSum s D := by
        apply Finset.single_le_sum _ h1mem
        intro l hl
        exact (s.selbergTerms_pos (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hl).1)).le

lemma selbergSum_pos {D : ℕ} (hD : 1 ≤ D) : 0 < selbergSum s D :=
  lt_of_lt_of_le zero_lt_one (one_le_selbergSum s hD)

noncomputable def selbergWeights (D : ℕ) (d : ℕ) : ℝ :=
  if d ∣ s.prodPrimes ∧ d ≤ D then
    ((μ d : ℤ) : ℝ) / (selbergSum s D * s.nu d) *
      ∑ l ∈ s.prodPrimes.divisors.filter (fun l => l ≤ D ∧ d ∣ l), s.selbergTerms l
  else 0

lemma selbergWeights_one {D : ℕ} (hD : 1 ≤ D) : selbergWeights s D 1 = 1 := by
  unfold selbergWeights
  rw [if_pos ⟨one_dvd _, hD⟩]
  have hS : selbergSum s D ≠ 0 := (selbergSum_pos s hD).ne'
  have hnu : s.nu 1 = 1 := s.nu_mult.map_one
  have hmu : (μ 1 : ℤ) = 1 := by simp
  have hfilt : s.prodPrimes.divisors.filter (fun l => l ≤ D ∧ 1 ∣ l) =
      s.prodPrimes.divisors.filter (· ≤ D) := by
    ext l; simp
  rw [hnu, hmu, hfilt]
  simp only [Int.cast_one, mul_one, one_div]
  change (selbergSum s D)⁻¹ * selbergSum s D = 1
  exact inv_mul_cancel₀ hS

lemma selbergWeights_eq_zero_of_not {D d : ℕ} (h : ¬ (d ∣ s.prodPrimes ∧ d ≤ D)) :
    selbergWeights s D d = 0 := by
  unfold selbergWeights
  rw [if_neg h]

lemma sum_moebius_divisors_mul_eq {m l : ℕ} (hm : Squarefree m) (hlm : l ∣ m) :
    ∑ d ∈ m.divisors.filter (l ∣ ·), ((μ d : ℤ) : ℝ) =
      if m = l then ((μ l : ℤ) : ℝ) else 0 := by
  have hm0 : m ≠ 0 := hm.ne_zero
  have hl0 : l ≠ 0 := ne_zero_of_dvd_ne_zero hm0 hlm
  set q := m / l
  have hmq : l * q = m := Nat.mul_div_cancel' hlm
  have hq0 : q ≠ 0 := fun h => hm0 (by rw [← hmq, h, mul_zero])
  have hcop : l.Coprime q := (Nat.squarefree_mul_iff.mp (hmq ▸ hm)).1
  have hbij : ∑ d ∈ m.divisors.filter (l ∣ ·), ((μ d : ℤ) : ℝ) =
      ∑ e ∈ q.divisors, ((μ (l * e) : ℤ) : ℝ) := by
    refine Finset.sum_bij (fun d _ => d / l) ?_ ?_ ?_ ?_
    · intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors] at hd ⊢
      refine ⟨?_, hq0⟩
      have h1 : l * (d / l) ∣ l * q := by rw [Nat.mul_div_cancel' hd.2, hmq]; exact hd.1.1
      exact (mul_dvd_mul_iff_left hl0).mp h1
    · intro d1 hd1 d2 hd2 heq
      simp only [Finset.mem_filter] at hd1 hd2
      rw [← Nat.mul_div_cancel' hd1.2, ← Nat.mul_div_cancel' hd2.2, heq]
    · intro e he
      simp only [Nat.mem_divisors] at he
      refine ⟨l * e, ?_, Nat.mul_div_right e (Nat.pos_of_ne_zero hl0)⟩
      simp only [Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨hmq ▸ mul_dvd_mul_left l he.1, hm0⟩, dvd_mul_right l e⟩
    · intro d hd
      simp only [Finset.mem_filter] at hd
      rw [Nat.mul_div_cancel' hd.2]
  rw [hbij]
  have hmul : ∀ e ∈ q.divisors, ((μ (l * e) : ℤ) : ℝ) = ((μ l : ℤ) : ℝ) * ((μ e : ℤ) : ℝ) := by
    intro e he
    have heq : e ∣ q := Nat.dvd_of_mem_divisors he
    have hle : l.Coprime e := hcop.coprime_dvd_right heq
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hle]
    push_cast
    rfl
  rw [Finset.sum_congr rfl hmul, ← Finset.mul_sum]
  have hzeta : (∑ e ∈ q.divisors, (μ e : ℤ)) = if q = 1 then 1 else 0 := by
    have h := congrArg (fun f : ArithmeticFunction ℤ => f q) ArithmeticFunction.moebius_mul_coe_zeta
    rw [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply] at h
    have hsum : ∑ x ∈ q.divisorsAntidiagonal, (μ x.1 : ℤ) * ((ArithmeticFunction.zeta x.2 : ℕ) : ℤ) =
        ∑ e ∈ q.divisors, (μ e : ℤ) := by
      rw [Nat.sum_divisorsAntidiagonal (f := fun a b => (μ a : ℤ) * ((ArithmeticFunction.zeta b : ℕ) : ℤ))]
      apply Finset.sum_congr rfl; intro e he
      have he0 : e ≠ 0 := ne_zero_of_dvd_ne_zero hq0 (Nat.dvd_of_mem_divisors he)
      have hdiv0 : q / e ≠ 0 :=
        (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) (Nat.dvd_of_mem_divisors he))
          (Nat.pos_of_ne_zero he0)).ne'
      simp [ArithmeticFunction.zeta_apply, hdiv0]
    exact hsum.symm.trans h
  have hcast : (∑ e ∈ q.divisors, ((μ e : ℤ) : ℝ)) = if q = 1 then 1 else 0 := by
    rw [← Int.cast_sum, hzeta]
    split_ifs <;> simp
  rw [hcast]
  have hiff : q = 1 ↔ m = l := by
    constructor
    · intro h1; rw [← hmq, h1, mul_one]
    · intro h2; subst h2; exact Nat.div_self (Nat.pos_of_ne_zero hl0)
  by_cases hml : m = l
  · rw [if_pos (hiff.mpr hml), if_pos hml, mul_one]
  · rw [if_neg (mt hiff.mp hml), if_neg hml, mul_zero]

lemma selbergWeights_diag {D l : ℕ} (hD : 1 ≤ D) (hl : l ∈ s.prodPrimes.divisors) :
    (∑ d ∈ s.prodPrimes.divisors, if l ∣ d then s.nu d * selbergWeights s D d else 0) =
      if l ≤ D then ((μ l : ℤ) : ℝ) * s.selbergTerms l / selbergSum s D else 0 := by
  have hS : selbergSum s D ≠ 0 := (selbergSum_pos s hD).ne'
  by_cases hlD : l ≤ D
  · rw [if_pos hlD]
    have hstep1 : (∑ d ∈ s.prodPrimes.divisors,
        if l ∣ d then s.nu d * selbergWeights s D d else 0) =
      (selbergSum s D)⁻¹ * ∑ d ∈ s.prodPrimes.divisors.filter (fun d => d ≤ D ∧ l ∣ d),
        ((μ d : ℤ) : ℝ) *
          ∑ m ∈ s.prodPrimes.divisors.filter (fun m => m ≤ D ∧ d ∣ m), s.selbergTerms m := by
      rw [Finset.mul_sum, ← Finset.sum_filter]
      have hsub : s.prodPrimes.divisors.filter (fun d => d ≤ D ∧ l ∣ d) ⊆
          s.prodPrimes.divisors.filter (l ∣ ·) := by
        intro d hd; simp only [Finset.mem_filter] at hd ⊢; exact ⟨hd.1, hd.2.2⟩
      rw [← Finset.sum_subset hsub]
      · apply Finset.sum_congr rfl
        intro d hd
        simp only [Finset.mem_filter, Nat.mem_divisors] at hd
        unfold selbergWeights
        rw [if_pos ⟨hd.1.1, hd.2.1⟩]
        have hnu0 : s.nu d ≠ 0 := s.nu_ne_zero hd.1.1
        field_simp
      · intro d hd1 hd2
        simp only [Finset.mem_filter, Nat.mem_divisors] at hd1 hd2
        have hnot : ¬ (d ∣ s.prodPrimes ∧ d ≤ D) := by
          intro h; exact hd2 ⟨hd1.1, h.2, hd1.2⟩
        rw [selbergWeights_eq_zero_of_not s hnot, mul_zero]
    rw [hstep1]
    have hswap : ∑ d ∈ s.prodPrimes.divisors.filter (fun d => d ≤ D ∧ l ∣ d),
        ((μ d : ℤ) : ℝ) *
          ∑ m ∈ s.prodPrimes.divisors.filter (fun m => m ≤ D ∧ d ∣ m), s.selbergTerms m =
      ∑ m ∈ s.prodPrimes.divisors.filter (fun m => m ≤ D ∧ l ∣ m),
        s.selbergTerms m * ∑ d ∈ m.divisors.filter (l ∣ ·), ((μ d : ℤ) : ℝ) := by
      simp_rw [Finset.mul_sum]
      trans ∑ d ∈ s.prodPrimes.divisors.filter (fun d => d ≤ D ∧ l ∣ d),
          ∑ m ∈ s.prodPrimes.divisors.filter (fun m => m ≤ D ∧ l ∣ m),
            if d ∣ m then ((μ d : ℤ) : ℝ) * s.selbergTerms m else 0
      · apply Finset.sum_congr rfl
        intro d hd
        simp only [Finset.mem_filter] at hd
        rw [← Finset.sum_filter]
        apply Finset.sum_congr _ (fun _ _ => rfl)
        ext m
        simp only [Finset.mem_filter]
        exact ⟨fun h => ⟨⟨h.1, h.2.1, hd.2.2.trans h.2.2⟩, h.2.2⟩,
          fun h => ⟨h.1.1, h.1.2.1, h.2⟩⟩
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro m hm
        simp only [Finset.mem_filter, Nat.mem_divisors] at hm
        rw [← Finset.sum_filter]
        apply Finset.sum_congr _ (fun d _ => mul_comm _ _)
        ext d
        simp only [Finset.mem_filter, Nat.mem_divisors]
        constructor
        · rintro ⟨⟨⟨hdP, _⟩, hdD, hld⟩, hdm⟩
          exact ⟨⟨hdm, ne_zero_of_dvd_ne_zero hm.1.2 hm.1.1⟩, hld⟩
        · rintro ⟨⟨hdm, _⟩, hld⟩
          have hmpos : 0 < m := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hm.1.2 hm.1.1)
          exact ⟨⟨⟨hdm.trans hm.1.1, hm.1.2⟩, (Nat.le_of_dvd hmpos hdm).trans hm.2.1, hld⟩, hdm⟩
    rw [hswap]
    have hcollapse : ∑ m ∈ s.prodPrimes.divisors.filter (fun m => m ≤ D ∧ l ∣ m),
        s.selbergTerms m * ∑ d ∈ m.divisors.filter (l ∣ ·), ((μ d : ℤ) : ℝ) =
      s.selbergTerms l * ((μ l : ℤ) : ℝ) := by
      have hterm : ∀ m ∈ s.prodPrimes.divisors.filter (fun m => m ≤ D ∧ l ∣ m),
          s.selbergTerms m * ∑ d ∈ m.divisors.filter (l ∣ ·), ((μ d : ℤ) : ℝ) =
            if m = l then s.selbergTerms l * ((μ l : ℤ) : ℝ) else 0 := by
        intro m hm
        simp only [Finset.mem_filter] at hm
        rw [sum_moebius_divisors_mul_eq (s.squarefree_of_mem_divisors_prodPrimes hm.1) hm.2.2]
        split_ifs with hml
        · subst hml; rfl
        · ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
      rw [if_pos]
      simp only [Finset.mem_filter]
      exact ⟨hl, hlD, dvd_refl l⟩
    rw [hcollapse]
    ring
  · rw [if_neg hlD]
    apply Finset.sum_eq_zero
    intro d hd
    split_ifs with hld
    · have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero (Nat.mem_divisors.mp hd).2 (Nat.dvd_of_mem_divisors hd)
      have hle : l ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hld
      have hnot : ¬ (d ∣ s.prodPrimes ∧ d ≤ D) := by intro h; omega
      rw [selbergWeights_eq_zero_of_not s hnot, mul_zero]
    · rfl

lemma mainSum_lambdaSquared_selbergWeights {D : ℕ} (hD : 1 ≤ D) :
    s.mainSum (BoundingSieve.lambdaSquared (selbergWeights s D)) = (selbergSum s D)⁻¹ := by
  rw [s.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  have hS : selbergSum s D ≠ 0 := (selbergSum_pos s hD).ne'
  have hterm : ∀ l ∈ s.prodPrimes.divisors,
      (s.selbergTerms l)⁻¹ *
        (∑ d ∈ s.prodPrimes.divisors, if l ∣ d then s.nu d * selbergWeights s D d else 0) ^ 2 =
      if l ≤ D then s.selbergTerms l / (selbergSum s D) ^ 2 else 0 := by
    intro l hl
    rw [selbergWeights_diag s hD hl]
    split_ifs with hlD
    · have hsq : Squarefree l := s.squarefree_of_mem_divisors_prodPrimes hl
      have hmu_sq : (((μ l : ℤ) : ℝ)) ^ 2 = 1 := by
        rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]
        norm_cast
        rw [← pow_mul, mul_comm, pow_mul]
        simp
      have hgpos : s.selbergTerms l ≠ 0 :=
        (s.selbergTerms_pos (Nat.dvd_of_mem_divisors hl)).ne'
      calc (s.selbergTerms l)⁻¹ * (((μ l : ℤ) : ℝ) * s.selbergTerms l / selbergSum s D) ^ 2
          = (s.selbergTerms l)⁻¹ * ((((μ l : ℤ) : ℝ)) ^ 2 * (s.selbergTerms l) ^ 2 /
              (selbergSum s D) ^ 2) := by ring
        _ = (s.selbergTerms l)⁻¹ * (1 * (s.selbergTerms l) ^ 2 / (selbergSum s D) ^ 2) := by
              rw [hmu_sq]
        _ = s.selbergTerms l / (selbergSum s D) ^ 2 := by field_simp
    · simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, ← Finset.sum_div]
  change selbergSum s D / (selbergSum s D) ^ 2 = (selbergSum s D)⁻¹
  field_simp

lemma abs_selbergWeights_le {D d : ℕ} (hD : 1 ≤ D) :
    |selbergWeights s D d| ≤ if d ∣ s.prodPrimes ∧ d ≤ D then s.selbergTerms d / s.nu d else 0 := by
  by_cases hd : d ∣ s.prodPrimes ∧ d ≤ D
  · rw [if_pos hd]
    unfold selbergWeights
    rw [if_pos hd]
    have hSpos : 0 < selbergSum s D := selbergSum_pos s hD
    have hnupos : 0 < s.nu d := s.nu_pos_of_dvd_prodPrimes hd.1
    have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hd.1
    have hsum_le : ∑ l ∈ s.prodPrimes.divisors.filter (fun l => l ≤ D ∧ d ∣ l), s.selbergTerms l ≤
        s.selbergTerms d * selbergSum s D := by
      have hbij : ∑ l ∈ s.prodPrimes.divisors.filter (fun l => l ≤ D ∧ d ∣ l), s.selbergTerms l =
          ∑ m ∈ (s.prodPrimes.divisors.filter (fun l => l ≤ D ∧ d ∣ l)).image (· / d),
            s.selbergTerms d * s.selbergTerms m := by
        rw [Finset.sum_image]
        · apply Finset.sum_congr rfl
          intro l hl
          simp only [Finset.mem_filter, Nat.mem_divisors] at hl
          have hl_eq : d * (l / d) = l := Nat.mul_div_cancel' hl.2.2
          have hsq : Squarefree l := s.squarefree_of_dvd_prodPrimes hl.1.1
          have hsq_mul : Squarefree (d * (l / d)) := by rw [hl_eq]; exact hsq
          have hcop : d.Coprime (l / d) := (Nat.squarefree_mul_iff.mp hsq_mul).1
          rw [← s.selbergTerms_isMultiplicative.map_mul_of_coprime hcop, hl_eq]
        · intro l1 hl1 l2 hl2 heq
          simp only [Finset.mem_coe, Finset.mem_filter] at hl1 hl2
          dsimp only at heq
          rw [← Nat.mul_div_cancel' hl1.2.2, ← Nat.mul_div_cancel' hl2.2.2, heq]
      rw [hbij, ← Finset.mul_sum]
      have hsub : (s.prodPrimes.divisors.filter (fun l => l ≤ D ∧ d ∣ l)).image (· / d) ⊆
          s.prodPrimes.divisors.filter (· ≤ D) := by
        intro m hm
        simp only [Finset.mem_image, Finset.mem_filter, Nat.mem_divisors] at hm ⊢
        rcases hm with ⟨l, ⟨⟨hlP, hP0⟩, hlD, hdl⟩, rfl⟩
        exact ⟨⟨(Nat.div_dvd_of_dvd hdl).trans hlP, hP0⟩, (Nat.div_le_self l d).trans hlD⟩
      gcongr
      · exact (s.selbergTerms_pos hd.1).le
      · apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro m hm _
        exact (s.selbergTerms_pos (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hm).1)).le
    have hsum_nonneg : 0 ≤ ∑ l ∈ s.prodPrimes.divisors.filter (fun l => l ≤ D ∧ d ∣ l),
        s.selbergTerms l := by
      apply Finset.sum_nonneg
      intro l hl
      exact (s.selbergTerms_pos (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hl).1)).le
    have hmu_le : |((μ d : ℤ) : ℝ)| ≤ 1 := by
      have hsq : Squarefree d := s.squarefree_of_dvd_prodPrimes hd.1
      rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]
      simp
    rw [abs_mul, abs_div, abs_of_pos (mul_pos hSpos hnupos), abs_of_nonneg hsum_nonneg]
    calc |((μ d : ℤ) : ℝ)| / (selbergSum s D * s.nu d) *
          ∑ l ∈ s.prodPrimes.divisors.filter (fun l => l ≤ D ∧ d ∣ l), s.selbergTerms l
        ≤ 1 / (selbergSum s D * s.nu d) * (s.selbergTerms d * selbergSum s D) := by
          gcongr
      _ = s.selbergTerms d / s.nu d := by
          field_simp [hSpos.ne', hnupos.ne']
  · rw [if_neg hd, selbergWeights_eq_zero_of_not s hd, abs_zero]

lemma errSum_lambdaSquared_selbergWeights_le {D : ℕ} (hD : 1 ≤ D)
    (hw : ∀ d, d ∣ s.prodPrimes → d ≤ D → s.selbergTerms d / s.nu d ≤ (d : ℝ))
    (hrem : ∀ d, d ∣ s.prodPrimes → |s.rem d| ≤ (d : ℝ)) :
    s.errSum (BoundingSieve.lambdaSquared (selbergWeights s D)) ≤ (D : ℝ) ^ 6 := by
  set w := selbergWeights s D
  set A := s.prodPrimes.divisors.filter (· ≤ D)
  have hcard : A.card ≤ D := by
    have hsub : A ⊆ Finset.Icc 1 D := by
      intro d hd
      simp only [A, Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc] at hd ⊢
      exact ⟨Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hd.1.2 hd.1.1), hd.2⟩
    simpa using Finset.card_le_card hsub
  have hw_le : ∀ d ∈ A, |w d| ≤ (D : ℝ) := by
    intro d hd
    simp only [A, Finset.mem_filter, Nat.mem_divisors] at hd
    calc |w d| ≤ s.selbergTerms d / s.nu d := by
          have := abs_selbergWeights_le s hD (d := d)
          rwa [if_pos ⟨hd.1.1, hd.2⟩] at this
      _ ≤ (d : ℝ) := hw d hd.1.1 hd.2
      _ ≤ (D : ℝ) := by exact_mod_cast hd.2
  have hstep1 : s.errSum (BoundingSieve.lambdaSquared w) ≤
      ∑ d ∈ s.prodPrimes.divisors,
        ∑ d1 ∈ A, ∑ d2 ∈ A,
          if d = Nat.lcm d1 d2 then |w d1| * |w d2| * |s.rem d| else 0 := by
    unfold BoundingSieve.errSum
    apply Finset.sum_le_sum
    intro d hd
    unfold BoundingSieve.lambdaSquared
    calc |∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
            if d = Nat.lcm d1 d2 then w d1 * w d2 else 0| * |s.rem d|
        ≤ (∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
            if d = Nat.lcm d1 d2 then |w d1| * |w d2| else 0) * |s.rem d| := by
          gcongr
          calc |∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
                  if d = Nat.lcm d1 d2 then w d1 * w d2 else 0|
              ≤ ∑ d1 ∈ d.divisors, |∑ d2 ∈ d.divisors,
                  if d = Nat.lcm d1 d2 then w d1 * w d2 else 0| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
                  |if d = Nat.lcm d1 d2 then w d1 * w d2 else 0| := by
                apply Finset.sum_le_sum
                intro d1 _
                exact Finset.abs_sum_le_sum_abs _ _
            _ = ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
                  if d = Nat.lcm d1 d2 then |w d1| * |w d2| else 0 := by
                apply Finset.sum_congr rfl; intro d1 _
                apply Finset.sum_congr rfl; intro d2 _
                split_ifs <;> simp [abs_mul]
      _ = ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
            if d = Nat.lcm d1 d2 then |w d1| * |w d2| * |s.rem d| else 0 := by
          simp_rw [Finset.sum_mul, ite_mul, zero_mul]
      _ ≤ ∑ d1 ∈ A, ∑ d2 ∈ A,
            if d = Nat.lcm d1 d2 then |w d1| * |w d2| * |s.rem d| else 0 := by
          have h1 : ∀ d1 ∈ d.divisors,
              (∑ d2 ∈ d.divisors,
                if d = Nat.lcm d1 d2 then |w d1| * |w d2| * |s.rem d| else 0) ≤
              if d1 ∈ A then
                (∑ d2 ∈ A, if d = Nat.lcm d1 d2 then |w d1| * |w d2| * |s.rem d| else 0)
              else 0 := by
            intro d1 _
            by_cases hd1A : d1 ∈ A
            · rw [if_pos hd1A]
              calc (∑ d2 ∈ d.divisors,
                      (if d = Nat.lcm d1 d2 then |w d1| * |w d2| * |s.rem d| else (0 : ℝ)))
                  = ∑ d2 ∈ d.divisors.filter (· ∈ A),
                      (if d = Nat.lcm d1 d2 then |w d1| * |w d2| * |s.rem d| else (0 : ℝ)) := by
                    symm
                    apply Finset.sum_subset (Finset.filter_subset _ _)
                    intro d2 hd2 hd2not
                    have hnotA : d2 ∉ A := by
                      intro h; exact hd2not (Finset.mem_filter.mpr ⟨hd2, h⟩)
                    have hnot : ¬ (d2 ∣ s.prodPrimes ∧ d2 ≤ D) := by
                      intro h
                      exact hnotA (Finset.mem_filter.mpr
                        ⟨Nat.mem_divisors.mpr ⟨h.1, s.prodPrimes_ne_zero⟩, h.2⟩)
                    simp [w, selbergWeights_eq_zero_of_not s hnot]
                _ ≤ ∑ d2 ∈ A,
                      (if d = Nat.lcm d1 d2 then |w d1| * |w d2| * |s.rem d| else (0 : ℝ)) := by
                    apply Finset.sum_le_sum_of_subset_of_nonneg
                    · intro x hx; exact (Finset.mem_filter.mp hx).2
                    · intro x _ _; split_ifs <;> positivity
            · rw [if_neg hd1A]
              have hnot : ¬ (d1 ∣ s.prodPrimes ∧ d1 ≤ D) := by
                intro h
                exact hd1A (Finset.mem_filter.mpr
                  ⟨Nat.mem_divisors.mpr ⟨h.1, s.prodPrimes_ne_zero⟩, h.2⟩)
              apply le_of_eq
              apply Finset.sum_eq_zero
              intro d2 _
              simp [w, selbergWeights_eq_zero_of_not s hnot]
          calc (∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
                  (if d = Nat.lcm d1 d2 then |w d1| * |w d2| * |s.rem d| else (0 : ℝ)))
              ≤ ∑ d1 ∈ d.divisors, (if d1 ∈ A then
                  (∑ d2 ∈ A, (if d = Nat.lcm d1 d2 then |w d1| * |w d2| * |s.rem d| else (0 : ℝ)))
                else (0 : ℝ)) := Finset.sum_le_sum h1
            _ = ∑ d1 ∈ d.divisors.filter (· ∈ A),
                  ∑ d2 ∈ A, (if d = Nat.lcm d1 d2 then |w d1| * |w d2| * |s.rem d| else (0 : ℝ)) := by
                rw [Finset.sum_filter]
            _ ≤ ∑ d1 ∈ A,
                  ∑ d2 ∈ A, (if d = Nat.lcm d1 d2 then |w d1| * |w d2| * |s.rem d| else (0 : ℝ)) := by
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro x hx; exact (Finset.mem_filter.mp hx).2
                · intro x _ _
                  apply Finset.sum_nonneg
                  intro y _; split_ifs <;> positivity
  have hstep2 : (∑ d ∈ s.prodPrimes.divisors,
      ∑ d1 ∈ A, ∑ d2 ∈ A,
        if d = Nat.lcm d1 d2 then |w d1| * |w d2| * |s.rem d| else 0) =
      ∑ d1 ∈ A, ∑ d2 ∈ A, |w d1| * |w d2| * |s.rem (Nat.lcm d1 d2)| := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d1 hd1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d2 hd2
    have hlcm : Nat.lcm d1 d2 ∈ s.prodPrimes.divisors := by
      simp only [A, Finset.mem_filter, Nat.mem_divisors] at hd1 hd2 ⊢
      exact ⟨Nat.lcm_dvd hd1.1.1 hd2.1.1, s.prodPrimes_ne_zero⟩
    rw [Finset.sum_ite_eq' _ (Nat.lcm d1 d2), if_pos hlcm]
  calc s.errSum (BoundingSieve.lambdaSquared w)
      ≤ ∑ d1 ∈ A, ∑ d2 ∈ A, |w d1| * |w d2| * |s.rem (Nat.lcm d1 d2)| := hstep2 ▸ hstep1
    _ ≤ ∑ _d1 ∈ A, ∑ _d2 ∈ A, (D : ℝ) ^ 4 := by
        apply Finset.sum_le_sum; intro d1 hd1
        apply Finset.sum_le_sum; intro d2 hd2
        have h1 := hw_le d1 hd1
        have h2 := hw_le d2 hd2
        have hd1P := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd1).1
        have hd2P := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd2).1
        have hd1D : (d1 : ℝ) ≤ D := by exact_mod_cast (Finset.mem_filter.mp hd1).2
        have hd2D : (d2 : ℝ) ≤ D := by exact_mod_cast (Finset.mem_filter.mp hd2).2
        have h3 : |s.rem (Nat.lcm d1 d2)| ≤ (D : ℝ) ^ 2 := by
          calc |s.rem (Nat.lcm d1 d2)| ≤ (Nat.lcm d1 d2 : ℝ) :=
                hrem _ (Nat.lcm_dvd hd1P hd2P)
            _ ≤ ((d1 * d2 : ℕ) : ℝ) := by
                have hd10 : 0 < d1 := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hd1P)
                have hd20 : 0 < d2 := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hd2P)
                exact_mod_cast Nat.le_of_dvd (Nat.mul_pos hd10 hd20) (Nat.lcm_dvd_mul d1 d2)
            _ = (d1 : ℝ) * (d2 : ℝ) := by push_cast; rfl
            _ ≤ (D : ℝ) * (D : ℝ) := by gcongr
            _ = (D : ℝ) ^ 2 := by ring
        calc |w d1| * |w d2| * |s.rem (Nat.lcm d1 d2)|
            ≤ (D : ℝ) * (D : ℝ) * (D : ℝ) ^ 2 := by gcongr
          _ = (D : ℝ) ^ 4 := by ring
    _ = (A.card : ℝ) * (A.card : ℝ) * (D : ℝ) ^ 4 := by
        simp [mul_assoc]
    _ ≤ (D : ℝ) * (D : ℝ) * (D : ℝ) ^ 4 := by gcongr
    _ = (D : ℝ) ^ 6 := by ring

end SelbergOptimal

section SelbergDenominator

noncomputable def g2 (l : ℕ) : ℝ :=
  ∏ p ∈ l.primeFactors, (2 : ℝ) / ((p : ℝ) - 2)

lemma g2_nonneg (l : ℕ) (hl : ∀ p ∈ l.primeFactors, 3 ≤ p) : 0 ≤ g2 l := by
  unfold g2
  apply Finset.prod_nonneg
  intro p hp
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hl p hp
  have hp2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  positivity

lemma g2_mul_of_coprime {a b : ℕ} (h : a.Coprime b) : g2 (a * b) = g2 a * g2 b := by
  unfold g2
  rw [h.primeFactors_mul, Finset.prod_union h.disjoint_primeFactors]

lemma sum_e_add_one_div_pow_le {q : ℕ} (hq : 3 ≤ q) (E : ℕ) :
    ∑ e ∈ Finset.Icc 1 E, ((e + 1 : ℕ) : ℝ) / (q : ℝ) ^ e ≤ 2 / ((q : ℝ) - 2) := by
  set x : ℝ := (1 : ℝ) / q
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hxpos : 0 < x := by positivity
  have hxle : x ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hq3
  have hid : (1 - x) ^ 2 * ∑ e ∈ Finset.Icc 1 E, ((e + 1 : ℕ) : ℝ) * x ^ e =
      2 * x - x ^ 2 - ((E + 2 : ℕ) : ℝ) * x ^ (E + 1) + ((E + 1 : ℕ) : ℝ) * x ^ (E + 2) := by
    induction E with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
      push_cast
      ring
  have hrem_nonneg : 0 ≤ ((E + 2 : ℕ) : ℝ) * x ^ (E + 1) - ((E + 1 : ℕ) : ℝ) * x ^ (E + 2) := by
    have hfactor : ((E + 2 : ℕ) : ℝ) * x ^ (E + 1) - ((E + 1 : ℕ) : ℝ) * x ^ (E + 2) =
        x ^ (E + 1) * (((E + 2 : ℕ) : ℝ) - ((E + 1 : ℕ) : ℝ) * x) := by ring
    rw [hfactor]
    apply mul_nonneg (by positivity)
    push_cast
    nlinarith
  have hbound1 : (1 - x) ^ 2 * ∑ e ∈ Finset.Icc 1 E, ((e + 1 : ℕ) : ℝ) * x ^ e ≤
      2 * x - x ^ 2 := by linarith
  have hsum_eq : ∑ e ∈ Finset.Icc 1 E, ((e + 1 : ℕ) : ℝ) / (q : ℝ) ^ e =
      ∑ e ∈ Finset.Icc 1 E, ((e + 1 : ℕ) : ℝ) * x ^ e := by
    apply Finset.sum_congr rfl
    intro e _
    simp [x, div_eq_mul_inv, inv_pow]
  rw [hsum_eq]
  have h1mx : 0 < (1 - x) ^ 2 := by nlinarith
  have hbound2 : ∑ e ∈ Finset.Icc 1 E, ((e + 1 : ℕ) : ℝ) * x ^ e ≤
      (2 * x - x ^ 2) / (1 - x) ^ 2 := (le_div_iff₀' h1mx).mpr hbound1
  have hbound3 : (2 * x - x ^ 2) / (1 - x) ^ 2 ≤ 2 / ((q : ℝ) - 2) := by
    have hq0 : (q : ℝ) ≠ 0 := by linarith
    have hq1 : (q : ℝ) - 1 ≠ 0 := by linarith
    have hq2 : (q : ℝ) - 2 ≠ 0 := by linarith
    have heq : (2 * x - x ^ 2) / (1 - x) ^ 2 = (2 * (q : ℝ) - 1) / ((q : ℝ) - 1) ^ 2 := by
      simp only [x]
      field_simp
    rw [heq, div_le_div_iff₀ (by positivity) (by linarith)]
    nlinarith
  exact hbound2.trans hbound3

def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

lemma rad_dvd (n : ℕ) : rad n ∣ n := Nat.prod_primeFactors_dvd n

lemma rad_primeFactors (n : ℕ) : (rad n).primeFactors = n.primeFactors := by
  unfold rad
  exact Nat.primeFactors_prod fun p hp => Nat.prime_of_mem_primeFactors hp

lemma sum_divisors_div_self_of_rad_eq (D l : ℕ)
    (hl_odd : ∀ p ∈ l.primeFactors, 3 ≤ p) :
    ∑ n ∈ (Finset.Icc 1 D).filter (fun n => rad n = l), ((n.divisors.card : ℝ) / n) ≤ g2 l := by
  set S := (Finset.Icc 1 D).filter (fun n => rad n = l)
  set P := l.primeFactors
  set box := Fintype.piFinset (fun _ : P => Finset.Icc 1 D)
  let facFn : ℕ → (P → ℕ) := fun n p => n.factorization p.1
  have hmaps : ∀ n ∈ S, facFn n ∈ box := by
    intro n hn
    simp only [S, Finset.mem_filter, Finset.mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    have hpf : n.primeFactors = P := by
      rw [← rad_primeFactors n, hn.2]
    rw [Fintype.mem_piFinset]
    intro p
    rw [Finset.mem_Icc]
    have hp_mem : p.1 ∈ n.primeFactors := by rw [hpf]; exact p.2
    have hpos : 0 < n.factorization p.1 :=
      Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp_mem) hn0
        (Nat.dvd_of_mem_primeFactors hp_mem)
    have hle : n.factorization p.1 ≤ D := by
      have hp2 : 2 ≤ p.1 := (Nat.prime_of_mem_primeFactors hp_mem).two_le
      have hpow : p.1 ^ (n.factorization p.1) ≤ n :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.ordProj_dvd n p.1)
      have hlin : n.factorization p.1 ≤ 2 ^ (n.factorization p.1) := Nat.lt_two_pow_self.le
      have hpow2 : 2 ^ (n.factorization p.1) ≤ p.1 ^ (n.factorization p.1) :=
        Nat.pow_le_pow_left hp2 _
      omega
    exact ⟨hpos, hle⟩
  have hinj : Set.InjOn facFn (↑S : Set ℕ) := by
    intro n1 hn1 n2 hn2 heq
    simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn1 hn2
    have hn10 : n1 ≠ 0 := by omega
    have hn20 : n2 ≠ 0 := by omega
    have hpf1 : n1.primeFactors = P := by rw [← rad_primeFactors n1, hn1.2]
    have hpf2 : n2.primeFactors = P := by rw [← rad_primeFactors n2, hn2.2]
    rw [← Nat.prod_factorization_pow_eq_self hn10, ← Nat.prod_factorization_pow_eq_self hn20]
    simp only [Finsupp.prod, Nat.support_factorization, hpf1, hpf2]
    apply Finset.prod_congr rfl
    intro p hp
    have := congrFun heq ⟨p, hp⟩
    simp only [facFn] at this
    rw [this]
  have hval : ∀ n ∈ S, ((n.divisors.card : ℝ) / n) =
      ∏ p : P, ((facFn n p + 1 : ℕ) : ℝ) / (p.1 : ℝ) ^ (facFn n p) := by
    intro n hn
    simp only [S, Finset.mem_filter, Finset.mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    have hpf : n.primeFactors = P := by rw [← rad_primeFactors n, hn.2]
    have hcard : n.divisors.card = ∏ p ∈ P, (n.factorization p + 1) := by
      rw [Nat.card_divisors hn0, hpf]
    have hn_eq : n = ∏ p ∈ P, p ^ (n.factorization p) := by
      conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
      simp only [Finsupp.prod, Nat.support_factorization, hpf]
    calc ((n.divisors.card : ℝ) / (n : ℝ))
        = (((∏ p ∈ P, (n.factorization p + 1)) : ℕ) : ℝ) /
            (((∏ p ∈ P, p ^ (n.factorization p)) : ℕ) : ℝ) :=
          congrArg₂ (· / ·) (by exact_mod_cast hcard) (by exact_mod_cast hn_eq)
      _ = ∏ p ∈ P, ((n.factorization p + 1 : ℕ) : ℝ) / (p : ℝ) ^ (n.factorization p) := by
          push_cast; rw [← Finset.prod_div_distrib]
      _ = ∏ p : P, ((facFn n p + 1 : ℕ) : ℝ) / (p.1 : ℝ) ^ (facFn n p) := by
          rw [← Finset.prod_coe_sort P]
  calc ∑ n ∈ S, ((n.divisors.card : ℝ) / n)
      = ∑ n ∈ S, ∏ p : P, ((facFn n p + 1 : ℕ) : ℝ) / (p.1 : ℝ) ^ (facFn n p) :=
        Finset.sum_congr rfl hval
    _ = ∑ f ∈ S.image facFn, ∏ p : P, ((f p + 1 : ℕ) : ℝ) / (p.1 : ℝ) ^ (f p) :=
        (Finset.sum_image (f := fun f : P → ℕ =>
          ∏ p : P, ((f p + 1 : ℕ) : ℝ) / (p.1 : ℝ) ^ (f p)) hinj).symm
    _ ≤ ∑ f ∈ box, ∏ p : P, ((f p + 1 : ℕ) : ℝ) / (p.1 : ℝ) ^ (f p) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro f hf
          rcases Finset.mem_image.mp hf with ⟨n, hn, rfl⟩
          exact hmaps n hn
        · intro f _ _
          apply Finset.prod_nonneg
          intro p _; positivity
    _ = ∏ p : P, ∑ e ∈ Finset.Icc 1 D, ((e + 1 : ℕ) : ℝ) / (p.1 : ℝ) ^ e :=
        Finset.sum_prod_piFinset (Finset.Icc 1 D) (fun (p : P) (e : ℕ) =>
          ((e + 1 : ℕ) : ℝ) / (p.1 : ℝ) ^ e)
    _ ≤ ∏ p : P, (2 : ℝ) / ((p.1 : ℝ) - 2) := by
        apply Finset.prod_le_prod
        · intro p _
          apply Finset.sum_nonneg; intro e _; positivity
        · intro p _
          exact sum_e_add_one_div_pow_le (hl_odd p.1 p.2) D
    _ = g2 l := by
        unfold g2
        exact Finset.prod_coe_sort P (fun p => (2 : ℝ) / ((p : ℝ) - 2))

lemma selberg_denom_full_ge (D : ℕ) (hD : 100 ≤ D) :
    (1 / 64 : ℝ) * (Real.log D) ^ 2 ≤
      ∑ l ∈ (∏ p ∈ (Finset.Icc 3 D).filter Nat.Prime, p).divisors.filter (· ≤ D), g2 l := by
  set P_odd := ∏ p ∈ (Finset.Icc 3 D).filter Nat.Prime, p
  have hP_pos : 0 < P_odd := Finset.prod_pos fun p hp => (Finset.mem_filter.mp hp).2.pos
  have hP_pf : P_odd.primeFactors = (Finset.Icc 3 D).filter Nat.Prime :=
    Nat.primeFactors_prod fun p hp => (Finset.mem_filter.mp hp).2
  set Lset := P_odd.divisors.filter (· ≤ D)
  have hsum_ge_odd : ∑ n ∈ (Finset.Icc 1 D).filter Odd, ((n.divisors.card : ℝ) / n) ≤
      ∑ l ∈ Lset, g2 l := by
    have hmaps : ∀ n ∈ (Finset.Icc 1 D).filter Odd, rad n ∈ Lset := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      simp only [Lset, Finset.mem_filter, Nat.mem_divisors]
      refine ⟨⟨?_, hP_pos.ne'⟩, (Nat.le_of_dvd (by omega) (rad_dvd n)).trans hn.1.2⟩
      unfold rad
      apply Finset.prod_dvd_prod_of_subset
      intro p hp
      have hp_prime := Nat.prime_of_mem_primeFactors hp
      have hp_dvd := Nat.dvd_of_mem_primeFactors hp
      have hp_ne2 : p ≠ 2 := by
        intro h2; subst h2
        rcases hn.2 with ⟨k, hk⟩
        omega
      have hp3 : 3 ≤ p := by have := hp_prime.two_le; omega
      have hpD : p ≤ D := (Nat.le_of_dvd (by omega) hp_dvd).trans hn.1.2
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp3, hpD⟩, hp_prime⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    apply Finset.sum_le_sum
    intro l hl
    have hlP : l ∣ P_odd := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hl).1
    have hl_odd : ∀ p ∈ l.primeFactors, 3 ≤ p := by
      intro p hp
      have hpP : p ∈ P_odd.primeFactors :=
        Nat.primeFactors_mono hlP hP_pos.ne' hp
      rw [hP_pf] at hpP
      exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hpP).1).1
    calc ∑ n ∈ ((Finset.Icc 1 D).filter Odd).filter (fun n => rad n = l),
            ((n.divisors.card : ℝ) / n)
        ≤ ∑ n ∈ (Finset.Icc 1 D).filter (fun n => rad n = l),
            ((n.divisors.card : ℝ) / n) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            simp only [Finset.mem_filter] at hn ⊢
            exact ⟨hn.1.1, hn.2⟩
          · intro n _ _; positivity
      _ ≤ g2 l := sum_divisors_div_self_of_rad_eq D l hl_odd
  set B := Nat.sqrt D
  have hB_ge : 10 ≤ B := by
    rw [Nat.le_sqrt]
    omega
  set O := (Finset.Icc 1 B).filter Odd
  have hsq_le : (∑ a ∈ O, (1 : ℝ) / a) ^ 2 ≤
      ∑ n ∈ (Finset.Icc 1 D).filter Odd, ((n.divisors.card : ℝ) / n) := by
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
    have hmaps : ∀ ab ∈ O ×ˢ O, ab.1 * ab.2 ∈ (Finset.Icc 1 D).filter Odd := by
      intro ab hab
      simp only [Finset.mem_product, O, Finset.mem_filter, Finset.mem_Icc] at hab ⊢
      refine ⟨⟨Nat.mul_pos (by omega) (by omega), ?_⟩, hab.1.2.mul hab.2.2⟩
      exact (Nat.mul_le_mul hab.1.1.2 hab.2.1.2).trans (Nat.sqrt_le D)
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    apply Finset.sum_le_sum
    intro n hn
    have hterm_eq : ∀ ab ∈ (O ×ˢ O).filter (fun ab => ab.1 * ab.2 = n),
        (1 : ℝ) / ab.1 * ((1 : ℝ) / ab.2) = (1 : ℝ) / n := by
      intro ab hab
      have heq := (Finset.mem_filter.mp hab).2
      rw [← heq]
      push_cast
      ring
    rw [Finset.sum_congr rfl hterm_eq, Finset.sum_const, nsmul_eq_mul, mul_one_div]
    gcongr
    have hsub : ((O ×ˢ O).filter (fun ab => ab.1 * ab.2 = n)).image Prod.fst ⊆ n.divisors := by
      intro a ha
      simp only [Finset.mem_image, Finset.mem_filter] at ha
      rcases ha with ⟨⟨a, b⟩, ⟨_, hab⟩, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      exact Nat.mem_divisors.mpr ⟨⟨b, hab.symm⟩, by omega⟩
    have hinj : Set.InjOn Prod.fst (↑((O ×ˢ O).filter (fun ab => ab.1 * ab.2 = n)) : Set (ℕ × ℕ)) := by
      intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, O, Finset.mem_Icc] at hx hy
      have hx1 : 0 < x.1 := by omega
      ext
      · exact hxy
      · have : x.1 * x.2 = x.1 * y.2 := by rw [hx.2, ← hy.2, hxy]
        exact Nat.eq_of_mul_eq_mul_left hx1 this
    rw [← Finset.card_image_of_injOn hinj]
    exact_mod_cast Finset.card_le_card hsub
  have hodd_ge : (1 / 2 : ℝ) * Real.log ((B : ℝ) / 2) ≤ ∑ a ∈ O, (1 : ℝ) / a :=
    sum_one_div_odd_ge B (by omega)
  have hlog_ge : (1 / 4 : ℝ) * Real.log D ≤ Real.log ((B : ℝ) / 2) := by
    have hD_pos : (0 : ℝ) < D := by positivity
    have hB_pos : (0 : ℝ) < (B : ℝ) / 2 := by
      have : (10 : ℝ) ≤ B := by exact_mod_cast hB_ge
      linarith
    have hB_lower : (D : ℝ) ^ (1 / 4 : ℝ) ≤ (B : ℝ) / 2 := by
      have hD_le : (D : ℝ) ≤ ((B + 1 : ℕ) : ℝ) ^ 2 := by
        have h1 : D < (B + 1) ^ 2 := by
          simpa [sq] using Nat.lt_succ_sqrt D
        exact_mod_cast h1.le
      have hB1 : ((B + 1 : ℕ) : ℝ) ≤ (11 / 10 : ℝ) * B := by
        have hB10 : (10 : ℝ) ≤ B := by exact_mod_cast hB_ge
        push_cast
        linarith
      have hpow4 : (D : ℝ) ≤ ((B : ℝ) / 2) ^ 4 := by
        have hB10 : (10 : ℝ) ≤ B := by exact_mod_cast hB_ge
        calc (D : ℝ) ≤ ((B + 1 : ℕ) : ℝ) ^ 2 := hD_le
          _ ≤ ((11 / 10 : ℝ) * B) ^ 2 := by gcongr
          _ ≤ ((B : ℝ) / 2) ^ 4 := by nlinarith [sq_nonneg ((B : ℝ) - 10)]
      have := Real.rpow_le_rpow hD_pos.le hpow4 (show (0 : ℝ) ≤ 1 / 4 by norm_num)
      rw [← Real.rpow_natCast ((B : ℝ) / 2) 4, ← Real.rpow_mul hB_pos.le] at this
      norm_num at this
      exact this
    have hlog := Real.log_le_log (Real.rpow_pos_of_pos hD_pos _) hB_lower
    rwa [Real.log_rpow hD_pos] at hlog
  have hD_log_nonneg : 0 ≤ Real.log D := Real.log_nonneg (by exact_mod_cast (show 1 ≤ D by omega))
  have hsq_final : (1 / 64 : ℝ) * (Real.log D) ^ 2 ≤ (∑ a ∈ O, (1 : ℝ) / a) ^ 2 := by
    have hlin : (1 / 8 : ℝ) * Real.log D ≤ ∑ a ∈ O, (1 : ℝ) / a := by linarith
    nlinarith
  exact hsq_final.trans (hsq_le.trans hsum_ge_odd)

lemma selberg_denom_factor_ge (h D : ℕ) (hh : 4 ≤ h) (hD : 100 ≤ D) :
    (1 / 64 : ℝ) * (Real.log D) ^ 2 ≤
      (∏ p ∈ h.primesBelow.filter (fun p => 3 ≤ p), (1 - (2 : ℝ) / p)⁻¹) *
        ∑ l ∈ (∏ p ∈ (Finset.Icc h D).filter Nat.Prime, p).divisors.filter (· ≤ D), g2 l := by
  set P_all := ∏ p ∈ (Finset.Icc 3 D).filter Nat.Prime, p
  set P_lo := ∏ p ∈ (Finset.Icc 3 (min (h - 1) D)).filter Nat.Prime, p
  set P_hi := ∏ p ∈ (Finset.Icc h D).filter Nat.Prime, p
  have hdisj : Disjoint ((Finset.Icc 3 (min (h - 1) D)).filter Nat.Prime)
      ((Finset.Icc h D).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp1 hp2
    omega
  have hunion : (Finset.Icc 3 D).filter Nat.Prime =
      (Finset.Icc 3 (min (h - 1) D)).filter Nat.Prime ∪ (Finset.Icc h D).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union]
    constructor
    · rintro ⟨⟨h3, hD'⟩, hp⟩
      by_cases hph : p < h
      · left; exact ⟨⟨h3, by omega⟩, hp⟩
      · right; exact ⟨⟨by omega, hD'⟩, hp⟩
    · rintro (⟨⟨h3, hle⟩, hp⟩ | ⟨⟨hge, hD'⟩, hp⟩)
      · exact ⟨⟨h3, by omega⟩, hp⟩
      · exact ⟨⟨by omega, hD'⟩, hp⟩
  have hP_eq : P_all = P_lo * P_hi := by
    simp only [P_all, P_lo, P_hi, hunion, Finset.prod_union hdisj]
  have hcop : P_lo.Coprime P_hi := by
    apply Nat.coprime_prod_left_iff.mpr; intro p hp
    apply Nat.coprime_prod_right_iff.mpr; intro q hq
    have hpq : p ≠ q := fun heq => Finset.disjoint_left.mp hdisj hp (heq ▸ hq)
    exact (Nat.coprime_primes (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2).mpr hpq
  have hP_lo_sq : Squarefree P_lo := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hp q hq hpq
      exact Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2).mpr hpq)
    · intro p hp; exact (Finset.mem_filter.mp hp).2.squarefree
  have hP_lo_pf : P_lo.primeFactors = (Finset.Icc 3 (min (h - 1) D)).filter Nat.Prime :=
    Nat.primeFactors_prod fun p hp => (Finset.mem_filter.mp hp).2
  have hsum_lo : ∑ l1 ∈ P_lo.divisors, g2 l1 =
      ∏ p ∈ (Finset.Icc 3 (min (h - 1) D)).filter Nat.Prime, (1 - (2 : ℝ) / p)⁻¹ := by
    let f : ArithmeticFunction ℝ := ArithmeticFunction.prodPrimeFactors (fun p => (2 : ℝ) / ((p : ℝ) - 2))
    have hf_mult : f.IsMultiplicative := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
    have hf_eq : ∀ d ∈ P_lo.divisors, g2 d = f d := by
      intro d hd
      have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hP_lo_sq.ne_zero (Nat.dvd_of_mem_divisors hd)
      simp [g2, f, ArithmeticFunction.prodPrimeFactors_apply hd0]
    rw [Finset.sum_congr rfl hf_eq]
    have hprod := hf_mult.prodPrimeFactors_one_add_of_squarefree hP_lo_sq
    rw [← hprod, hP_lo_pf]
    apply Finset.prod_congr rfl
    intro p hp
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    have hp0 : p ≠ 0 := by have := (Finset.mem_filter.mp hp).2.pos; omega
    have hne : (p : ℝ) - 2 ≠ 0 := by linarith
    have hfp : f p = (2 : ℝ) / ((p : ℝ) - 2) := by
      rw [show f p = ∏ q ∈ p.primeFactors, (2 : ℝ) / ((q : ℝ) - 2) from
        ArithmeticFunction.prodPrimeFactors_apply hp0]
      rw [(Finset.mem_filter.mp hp).2.primeFactors, Finset.prod_singleton]
    rw [hfp]
    field_simp
    ring
  have hlo_le : ∏ p ∈ (Finset.Icc 3 (min (h - 1) D)).filter Nat.Prime, (1 - (2 : ℝ) / p)⁻¹ ≤
      ∏ p ∈ h.primesBelow.filter (fun p => 3 ≤ p), (1 - (2 : ℝ) / p)⁻¹ := by
    have hsub : (Finset.Icc 3 (min (h - 1) D)).filter Nat.Prime ⊆
        h.primesBelow.filter (fun p => 3 ≤ p) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesBelow] at hp ⊢
      exact ⟨⟨by omega, hp.2⟩, hp.1.1⟩
    rw [← Finset.prod_sdiff hsub]
    apply le_mul_of_one_le_left
    · apply Finset.prod_nonneg
      intro p hp
      have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
      have hpos : 0 < 1 - (2 : ℝ) / p := by
        have : (2 : ℝ) / p ≤ 2 / 3 := by
          rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
        linarith
      positivity
    · apply one_le_prod_real
      intro p hp
      have hp_mem := (Finset.mem_sdiff.mp hp).1
      have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp_mem).2
      have hpos : 0 < 1 - (2 : ℝ) / p := by
        have : (2 : ℝ) / p ≤ 2 / 3 := by
          rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
        linarith
      exact (one_le_inv₀ hpos).mpr (by linarith [show (0 : ℝ) < 2 / p by positivity])
  have hsplit : ∑ l ∈ P_all.divisors.filter (· ≤ D), g2 l ≤
      (∑ l1 ∈ P_lo.divisors, g2 l1) * ∑ l2 ∈ P_hi.divisors.filter (· ≤ D), g2 l2 := by
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    have hmap : ∀ l ∈ P_all.divisors.filter (· ≤ D),
        (l.gcd P_lo, l.gcd P_hi) ∈ P_lo.divisors ×ˢ P_hi.divisors.filter (· ≤ D) := by
      intro l hl
      simp only [Finset.mem_filter, Nat.mem_divisors] at hl
      simp only [Finset.mem_product, Finset.mem_filter, Nat.mem_divisors]
      have hl0 : 0 < l := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hl.1.2 hl.1.1)
      have hP_lo0 : P_lo ≠ 0 := hP_lo_sq.ne_zero
      have hP_hi0 : P_hi ≠ 0 := (Finset.prod_pos fun p hp => (Finset.mem_filter.mp hp).2.pos).ne'
      exact ⟨⟨Nat.gcd_dvd_right l P_lo, hP_lo0⟩,
        ⟨⟨Nat.gcd_dvd_right l P_hi, hP_hi0⟩, (Nat.le_of_dvd hl0 (Nat.gcd_dvd_left l P_hi)).trans hl.2⟩⟩
    have hP_all_sq : Squarefree P_all := by
      apply Finset.squarefree_prod_of_pairwise_isCoprime
      · intro p hp q hq hpq
        exact Nat.coprime_iff_isRelPrime.mp
          ((Nat.coprime_primes (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2).mpr hpq)
      · intro p hp; exact (Finset.mem_filter.mp hp).2.squarefree
    have hl_factor : ∀ l ∈ P_all.divisors.filter (· ≤ D),
        l.gcd P_lo * l.gcd P_hi = l := by
      intro l hl
      have hlP : l ∣ P_lo * P_hi := hP_eq ▸ Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hl).1
      have hlsq : Squarefree l := hP_all_sq.squarefree_of_dvd (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hl).1)
      have hcop_g : (l.gcd P_lo).Coprime (l.gcd P_hi) :=
        hcop.coprime_dvd_left (Nat.gcd_dvd_right l P_lo) |>.coprime_dvd_right (Nat.gcd_dvd_right l P_hi)
      have hdvd1 : l.gcd P_lo * l.gcd P_hi ∣ l :=
        hcop_g.mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_left l P_lo) (Nat.gcd_dvd_left l P_hi)
      have hdvd2 : l ∣ l.gcd P_lo * l.gcd P_hi := by
        have hpart : l.primeFactors =
            l.primeFactors.filter (· ∣ P_lo) ∪ l.primeFactors.filter (fun p => ¬ p ∣ P_lo) := by
          ext p; simp only [Finset.mem_union, Finset.mem_filter]; tauto
        have hdj : Disjoint (l.primeFactors.filter (· ∣ P_lo))
            (l.primeFactors.filter (fun p => ¬ p ∣ P_lo)) := by
          rw [Finset.disjoint_left]; intro p h1 h2
          exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
        conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hlsq, hpart, Finset.prod_union hdj]
        apply mul_dvd_mul
        · have h1 : ∏ p ∈ l.primeFactors.filter (· ∣ P_lo), p ∣ l := by
            conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree hlsq]
            exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
          have h2 : ∏ p ∈ l.primeFactors.filter (· ∣ P_lo), p ∣ P_lo := by
            have hP_lo_pf' : l.primeFactors.filter (· ∣ P_lo) ⊆ P_lo.primeFactors := by
              intro p hp
              have hp1 := (Finset.mem_filter.mp hp).1
              have hp2 := (Finset.mem_filter.mp hp).2
              exact (Nat.prime_of_mem_primeFactors hp1).mem_primeFactors hp2 hP_lo_sq.ne_zero
            conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree hP_lo_sq]
            exact Finset.prod_dvd_prod_of_subset _ _ _ hP_lo_pf'
          exact Nat.dvd_gcd h1 h2
        · have hP_hi_sq : Squarefree P_hi := by
            apply Finset.squarefree_prod_of_pairwise_isCoprime
            · intro p hp q hq hpq
              exact Nat.coprime_iff_isRelPrime.mp
                ((Nat.coprime_primes (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2).mpr hpq)
            · intro p hp; exact (Finset.mem_filter.mp hp).2.squarefree
          have h1 : ∏ p ∈ l.primeFactors.filter (fun p => ¬ p ∣ P_lo), p ∣ l := by
            conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree hlsq]
            exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
          have h2 : ∏ p ∈ l.primeFactors.filter (fun p => ¬ p ∣ P_lo), p ∣ P_hi := by
            have hsub : l.primeFactors.filter (fun p => ¬ p ∣ P_lo) ⊆ P_hi.primeFactors := by
              intro p hp
              have hp1 := (Finset.mem_filter.mp hp).1
              have hp_not := (Finset.mem_filter.mp hp).2
              have hp_prime := Nat.prime_of_mem_primeFactors hp1
              have hp_dvd_mul : p ∣ P_lo * P_hi := (Nat.dvd_of_mem_primeFactors hp1).trans hlP
              rcases hp_prime.dvd_mul.mp hp_dvd_mul with hlo | hhi
              · exact absurd hlo hp_not
              · exact hp_prime.mem_primeFactors hhi hP_hi_sq.ne_zero
            conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree hP_hi_sq]
            exact Finset.prod_dvd_prod_of_subset _ _ _ hsub
          exact Nat.dvd_gcd h1 h2
      exact Nat.dvd_antisymm hdvd1 hdvd2
    have hinj : Set.InjOn (fun l : ℕ => (l.gcd P_lo, l.gcd P_hi))
        (↑(P_all.divisors.filter (· ≤ D)) : Set ℕ) := by
      intro l1 hl1 l2 hl2 heq
      dsimp only at heq
      rcases Prod.mk.inj heq with ⟨h1, h2⟩
      rw [← hl_factor l1 (Finset.mem_coe.mp hl1), ← hl_factor l2 (Finset.mem_coe.mp hl2), h1, h2]
    have hval : ∀ l ∈ P_all.divisors.filter (· ≤ D),
        g2 l = g2 (l.gcd P_lo) * g2 (l.gcd P_hi) := by
      intro l hl
      have hcop_g : (l.gcd P_lo).Coprime (l.gcd P_hi) :=
        hcop.coprime_dvd_left (Nat.gcd_dvd_right l P_lo) |>.coprime_dvd_right (Nat.gcd_dvd_right l P_hi)
      rw [← g2_mul_of_coprime hcop_g, hl_factor l hl]
    calc ∑ l ∈ P_all.divisors.filter (· ≤ D), g2 l
        = ∑ l ∈ P_all.divisors.filter (· ≤ D), g2 (l.gcd P_lo) * g2 (l.gcd P_hi) :=
          Finset.sum_congr rfl hval
      _ = ∑ ab ∈ (P_all.divisors.filter (· ≤ D)).image (fun l : ℕ => (l.gcd P_lo, l.gcd P_hi)),
            g2 ab.1 * g2 ab.2 := (Finset.sum_image (f := fun ab : ℕ × ℕ => g2 ab.1 * g2 ab.2) hinj).symm
      _ ≤ ∑ ab ∈ P_lo.divisors ×ˢ P_hi.divisors.filter (· ≤ D), g2 ab.1 * g2 ab.2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro ab hab
            rcases Finset.mem_image.mp hab with ⟨l, hl, rfl⟩
            exact hmap l hl
          · intro ab hab _
            simp only [Finset.mem_product, Finset.mem_filter, Nat.mem_divisors] at hab
            apply mul_nonneg
            · apply g2_nonneg
              intro p hp
              have hpP : p ∈ P_lo.primeFactors :=
                Nat.primeFactors_mono hab.1.1 hab.1.2 hp
              rw [hP_lo_pf] at hpP
              exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hpP).1).1
            · apply g2_nonneg
              intro p hp
              have hP_hi_pf : P_hi.primeFactors = (Finset.Icc h D).filter Nat.Prime :=
                Nat.primeFactors_prod fun q hq => (Finset.mem_filter.mp hq).2
              have hpP : p ∈ P_hi.primeFactors :=
                Nat.primeFactors_mono hab.2.1.1 hab.2.1.2 hp
              rw [hP_hi_pf] at hpP
              have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hpP).1).1
              omega
  have hhi_nonneg : 0 ≤ ∑ l2 ∈ P_hi.divisors.filter (· ≤ D), g2 l2 := by
    apply Finset.sum_nonneg
    intro l2 hl2
    have hP_hi_pf : P_hi.primeFactors = (Finset.Icc h D).filter Nat.Prime :=
      Nat.primeFactors_prod fun q hq => (Finset.mem_filter.mp hq).2
    apply g2_nonneg
    intro p hp
    have hl2_div := Nat.mem_divisors.mp (Finset.mem_filter.mp hl2).1
    have hpP : p ∈ P_hi.primeFactors := Nat.primeFactors_mono hl2_div.1 hl2_div.2 hp
    rw [hP_hi_pf] at hpP
    have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hpP).1).1
    omega
  calc (1 / 64 : ℝ) * (Real.log D) ^ 2
      ≤ ∑ l ∈ P_all.divisors.filter (· ≤ D), g2 l := selberg_denom_full_ge D hD
    _ ≤ (∑ l1 ∈ P_lo.divisors, g2 l1) * ∑ l2 ∈ P_hi.divisors.filter (· ≤ D), g2 l2 := hsplit
    _ = (∏ p ∈ (Finset.Icc 3 (min (h - 1) D)).filter Nat.Prime, (1 - (2 : ℝ) / p)⁻¹) *
          ∑ l2 ∈ P_hi.divisors.filter (· ≤ D), g2 l2 := by rw [hsum_lo]
    _ ≤ (∏ p ∈ h.primesBelow.filter (fun p => 3 ≤ p), (1 - (2 : ℝ) / p)⁻¹) *
          ∑ l2 ∈ P_hi.divisors.filter (· ≤ D), g2 l2 := by gcongr

end SelbergDenominator

section PairSieve

lemma count_Ico_mod_eq (K N d : ℕ) (hd : 0 < d) (r : ZMod d) :
    |(((Finset.Ico K (K + N)).filter (fun k : ℕ => (k : ZMod d) = r)).card : ℝ) - (N : ℝ) / d| ≤ 1 := by
  have : NeZero d := ⟨hd.ne'⟩
  set q := N / d
  set rem := N % d
  have hN : N = q * d + rem := by rw [mul_comm]; exact (Nat.div_add_mod N d).symm
  have hrem : rem < d := Nat.mod_lt N hd
  have hblock : ∀ m : ℕ, ((Finset.Ico m (m + d)).filter (fun k : ℕ => (k : ZMod d) = r)).card = 1 := by
    intro m
    let f : ℕ → ZMod d := fun k => (k : ZMod d)
    have hbij : Finset.image f (Finset.Ico m (m + d)) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_image_of_injOn]
      · simp [ZMod.card]
      · intro a ha b hb hab
        simp only [Finset.mem_coe, Finset.mem_Ico] at ha hb
        have hmod : a ≡ b [MOD d] := by
          have := congrArg ZMod.val hab
          simpa [f, Nat.ModEq, ZMod.val_natCast] using this
        rcases le_total a b with hle | hle
        · have hsub : d ∣ b - a := (Nat.modEq_iff_dvd' hle).mp hmod
          rcases eq_or_ne (b - a) 0 with h0 | hne
          · omega
          · exact absurd (Nat.le_of_dvd (by omega) hsub) (by omega)
        · have hsub : d ∣ a - b := (Nat.modEq_iff_dvd' hle).mp hmod.symm
          rcases eq_or_ne (a - b) 0 with h0 | hne
          · omega
          · exact absurd (Nat.le_of_dvd (by omega) hsub) (by omega)
    have hex : ∃ k ∈ Finset.Ico m (m + d), (k : ZMod d) = r := by
      have : r ∈ Finset.image f (Finset.Ico m (m + d)) := hbij ▸ Finset.mem_univ r
      simpa [f] using this
    rcases hex with ⟨k0, hk0, hr0⟩
    have hsing : (Finset.Ico m (m + d)).filter (fun k : ℕ => (k : ZMod d) = r) = {k0} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro ⟨hk, hkr⟩
        simp only [Finset.mem_Ico] at hk hk0
        have hmod : k ≡ k0 [MOD d] := by
          have := congrArg ZMod.val (hkr.trans hr0.symm)
          simpa [Nat.ModEq, ZMod.val_natCast] using this
        rcases le_total k k0 with hle | hle
        · have hsub : d ∣ k0 - k := (Nat.modEq_iff_dvd' hle).mp hmod
          rcases eq_or_ne (k0 - k) 0 with h0 | hne
          · omega
          · exact absurd (Nat.le_of_dvd (by omega) hsub) (by omega)
        · have hsub : d ∣ k - k0 := (Nat.modEq_iff_dvd' hle).mp hmod.symm
          rcases eq_or_ne (k - k0) 0 with h0 | hne
          · omega
          · exact absurd (Nat.le_of_dvd (by omega) hsub) (by omega)
      · rintro rfl; exact ⟨hk0, hr0⟩
    rw [hsing, Finset.card_singleton]
  have hblocks : ∀ t : ℕ,
      ((Finset.Ico K (K + t * d)).filter (fun k : ℕ => (k : ZMod d) = r)).card = t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have hsplit : Finset.Ico K (K + (t + 1) * d) =
          Finset.Ico K (K + t * d) ∪ Finset.Ico (K + t * d) (K + t * d + d) := by
        rw [show K + (t + 1) * d = K + t * d + d by ring]
        exact (Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)).symm
      rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint]
      · rw [ih, hblock]
      · exact Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)
  have hfull_split : Finset.Ico K (K + N) =
      Finset.Ico K (K + q * d) ∪ Finset.Ico (K + q * d) (K + q * d + rem) := by
    rw [show K + N = K + q * d + rem by omega]
    exact (Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)).symm
  have hrem_le : ((Finset.Ico (K + q * d) (K + q * d + rem)).filter
      (fun k : ℕ => (k : ZMod d) = r)).card ≤ 1 := by
    calc _ ≤ ((Finset.Ico (K + q * d) (K + q * d + d)).filter
            (fun k : ℕ => (k : ZMod d) = r)).card := by
          apply Finset.card_le_card
          apply Finset.filter_subset_filter
          exact Finset.Ico_subset_Ico_right (by omega)
      _ = 1 := hblock (K + q * d)
  have hcard_eq : ((Finset.Ico K (K + N)).filter (fun k : ℕ => (k : ZMod d) = r)).card =
      q + ((Finset.Ico (K + q * d) (K + q * d + rem)).filter (fun k : ℕ => (k : ZMod d) = r)).card := by
    rw [hfull_split, Finset.filter_union, Finset.card_union_of_disjoint, hblocks]
    exact Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)
  set c := ((Finset.Ico (K + q * d) (K + q * d + rem)).filter (fun k : ℕ => (k : ZMod d) = r)).card
  have hc_le : (c : ℝ) ≤ 1 := by exact_mod_cast hrem_le
  have hrem_div : (rem : ℝ) / d < 1 := (div_lt_one (by exact_mod_cast hd)).mpr (by exact_mod_cast hrem)
  have hNd : (N : ℝ) / d = (q : ℝ) + (rem : ℝ) / d := by
    have : (N : ℝ) = (q : ℝ) * d + rem := by exact_mod_cast hN
    rw [this]
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp
  rw [hcard_eq, Nat.cast_add, hNd]
  rw [show (q : ℝ) + c - ((q : ℝ) + (rem : ℝ) / d) = (c : ℝ) - (rem : ℝ) / d by ring]
  rw [abs_le]
  have hc_nn : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
  have hrem_nn : (0 : ℝ) ≤ (rem : ℝ) / d := div_nonneg (Nat.cast_nonneg rem) (Nat.cast_nonneg d)
  constructor <;> linarith

lemma card_roots_pair_mod_sqfree (W b h d : ℕ) [NeZero d] (hd_sq : Squarefree d)
    (hcopW : d.Coprime W) (hcoph : d.Coprime h) :
    (Finset.univ.filter (fun r : ZMod d =>
      ((W : ZMod d) * r + b) * ((W : ZMod d) * r + b + h) = 0)).card =
      2 ^ d.primeFactors.card := by
  suffices ∀ m : ℕ, ∀ [NeZero m], Squarefree m → m.Coprime W → m.Coprime h →
      (Finset.univ.filter (fun r : ZMod m =>
        ((W : ZMod m) * r + b) * ((W : ZMod m) * r + b + h) = 0)).card =
        2 ^ m.primeFactors.card from this d hd_sq hcopW hcoph
  intro d
  induction d using Nat.strong_induction_on with | h d ih =>
  intro _ hd_sq hcopW hcoph
  by_cases hd1 : d = 1
  · subst hd1
    have h1 : Finset.univ.filter (fun r : ZMod 1 =>
        ((W : ZMod 1) * r + (b : ZMod 1)) * ((W : ZMod 1) * r + (b : ZMod 1) + (h : ZMod 1)) = 0) =
        Finset.univ := by
      ext r; simp [Subsingleton.elim _ (0 : ZMod 1)]
    rw [h1]
    simp
  · have hd_pos : 0 < d := Nat.pos_of_ne_zero hd_sq.ne_zero
    obtain ⟨q, hq_prime, hqd⟩ := Nat.exists_prime_and_dvd hd1
    set d' := d / q
    have hd_eq : q * d' = d := Nat.mul_div_cancel' hqd
    have hcop_qd' : q.Coprime d' := (Nat.squarefree_mul_iff.mp (hd_eq ▸ hd_sq)).1
    have hd'_sq : Squarefree d' := (Nat.squarefree_mul_iff.mp (hd_eq ▸ hd_sq)).2.2
    have hd'_lt : d' < d := Nat.div_lt_self hd_pos hq_prime.one_lt
    have hcopW_q : q.Coprime W := hcopW.coprime_dvd_left hqd
    have hcopW_d' : d'.Coprime W := hcopW.coprime_dvd_left (Nat.div_dvd_of_dvd hqd)
    have hcoph_q : q.Coprime h := hcoph.coprime_dvd_left hqd
    have hcoph_d' : d'.Coprime h := hcoph.coprime_dvd_left (Nat.div_dvd_of_dvd hqd)
    have : NeZero q := ⟨hq_prime.ne_zero⟩
    have : NeZero d' := ⟨hd'_sq.ne_zero⟩
    have hcard_q : (Finset.univ.filter (fun r : ZMod q =>
        ((W : ZMod q) * r + (b : ZMod q)) * ((W : ZMod q) * r + (b : ZMod q) + (h : ZMod q)) = 0)).card = 2 := by
      have : Fact q.Prime := ⟨hq_prime⟩
      have hW0 : (W : ZMod q) ≠ 0 := by
        intro h0
        have hdvd : q ∣ W := (ZMod.natCast_eq_zero_iff W q).mp h0
        have := Nat.dvd_gcd (dvd_refl q) hdvd
        rw [hcopW_q.gcd_eq_one] at this
        exact hq_prime.not_dvd_one this
      have hh0 : (h : ZMod q) ≠ 0 := by
        intro h0
        have hdvd : q ∣ h := (ZMod.natCast_eq_zero_iff h q).mp h0
        have := Nat.dvd_gcd (dvd_refl q) hdvd
        rw [hcoph_q.gcd_eq_one] at this
        exact hq_prime.not_dvd_one this
      set r1 : ZMod q := -(W : ZMod q)⁻¹ * (b : ZMod q)
      set r2 : ZMod q := -(W : ZMod q)⁻¹ * ((b : ZMod q) + (h : ZMod q))
      have hr12 : r1 ≠ r2 := by
        intro heq
        have hdiff : (W : ZMod q) * (r1 - r2) = 0 := by rw [heq, sub_self, mul_zero]
        have hcalc : (W : ZMod q) * (r1 - r2) = (h : ZMod q) := by
          simp only [r1, r2]
          have : (W : ZMod q) * (W : ZMod q)⁻¹ = 1 := mul_inv_cancel₀ hW0
          linear_combination ((h : ZMod q)) * this
        exact hh0 (hcalc.symm.trans hdiff)
      have hset : Finset.univ.filter (fun r : ZMod q =>
          ((W : ZMod q) * r + (b : ZMod q)) * ((W : ZMod q) * r + (b : ZMod q) + (h : ZMod q)) = 0) =
          {r1, r2} := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, _root_.mul_eq_zero]
        constructor
        · rintro (h1 | h2)
          · left
            have : (W : ZMod q) * r = -(b : ZMod q) := eq_neg_of_add_eq_zero_left h1
            calc r = (W : ZMod q)⁻¹ * ((W : ZMod q) * r) := by rw [inv_mul_cancel_left₀ hW0]
              _ = r1 := by rw [this]; simp [r1]
          · right
            have : (W : ZMod q) * r = -((b : ZMod q) + (h : ZMod q)) := by
              linear_combination h2
            calc r = (W : ZMod q)⁻¹ * ((W : ZMod q) * r) := by rw [inv_mul_cancel_left₀ hW0]
              _ = r2 := by rw [this]; simp only [r2]; ring
        · rintro (rfl | rfl)
          · left; simp [r1, mul_neg, mul_inv_cancel_left₀ hW0]
          · right; simp [r2, mul_neg, mul_inv_cancel_left₀ hW0]
      rw [hset, Finset.card_pair hr12]
    have hcard_d' := ih d' hd'_lt hd'_sq hcopW_d' hcoph_d'
    have hpf : d.primeFactors.card = 1 + d'.primeFactors.card := by
      rw [← hd_eq, hcop_qd'.primeFactors_mul, Finset.card_union_of_disjoint hcop_qd'.disjoint_primeFactors,
        hq_prime.primeFactors, Finset.card_singleton]
    rw [hpf, pow_add, pow_one, ← hcard_d', ← hcard_q]
    let eEq : ZMod d ≃+* ZMod (q * d') := hd_eq.symm ▸ RingEquiv.refl (ZMod d)
    let eRing : ZMod d ≃+* ZMod q × ZMod d' := eEq.trans (ZMod.chineseRemainder hcop_qd')
    set Sq := Finset.univ.filter (fun r : ZMod q =>
        ((W : ZMod q) * r + (b : ZMod q)) * ((W : ZMod q) * r + (b : ZMod q) + (h : ZMod q)) = 0)
    set Sd' := Finset.univ.filter (fun r : ZMod d' =>
        ((W : ZMod d') * r + (b : ZMod d')) * ((W : ZMod d') * r + (b : ZMod d') + (h : ZMod d')) = 0)
    set S := Finset.univ.filter (fun r : ZMod d =>
        ((W : ZMod d) * r + (b : ZMod d)) *
          ((W : ZMod d) * r + (b : ZMod d) + (h : ZMod d)) = 0)
    rw [← Finset.card_product]
    apply Finset.card_bij (fun r _ => eRing r)
    · intro r hr
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hr
      simp only [Finset.mem_product, Sq, Sd', Finset.mem_filter, Finset.mem_univ, true_and]
      have h0 := congrArg eRing hr
      simp only [map_mul, map_add, map_natCast, _root_.map_zero, Prod.ext_iff, Prod.fst_mul,
        Prod.fst_add, Prod.snd_mul, Prod.snd_add, Prod.fst_zero, Prod.snd_zero,
        Prod.fst_natCast, Prod.snd_natCast] at h0
      exact h0
    · intro r1 _ r2 _ heq; exact eRing.injective heq
    · intro p hp
      refine ⟨eRing.symm p, ?_, eRing.apply_symm_apply p⟩
      simp only [Finset.mem_product, Sq, Sd', Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      apply eRing.injective
      simp only [map_mul, map_add, map_natCast, _root_.map_zero, eRing.apply_symm_apply,
        Prod.ext_iff, Prod.fst_mul, Prod.fst_add, Prod.snd_mul, Prod.snd_add,
        Prod.fst_zero, Prod.snd_zero, Prod.fst_natCast, Prod.snd_natCast]
      exact hp

noncomputable def primePairs (X h : ℕ) (b : ZMod (primorial (h - 1))) : Finset ℕ :=
  (Finset.Icc X (2 * X)).filter (fun m : ℕ =>
    m.Prime ∧ (m + h).Prime ∧ (m : ZMod (primorial (h - 1))) = b)

lemma primePairs_card_le_selberg (X h D : ℕ) (hh : 4 ≤ h) (heven : Even h)
    (hD : 100 ≤ D) (hDX : D < X) (hW_le : primorial (h - 1) ≤ X)
    (b : ZMod (primorial (h - 1))) :
    ((primePairs X h b).card : ℝ) ≤
      (2 * (X : ℝ) / (primorial (h - 1) : ℝ)) *
        (64 * Real.exp 2 * (∏ p ∈ h.primesBelow, (1 - (1 : ℝ) / p)⁻¹) ^ 2 / (Real.log D) ^ 2) +
      (D : ℝ) ^ 6 := by
  let W := primorial (h - 1)
  have hW_pos : 0 < W := primorial_pos (h - 1)
  have : NeZero W := ⟨hW_pos.ne'⟩
  set P := ∏ p ∈ (Finset.Icc h D).filter Nat.Prime, p
  have hP_sq : Squarefree P := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hp q hq hpq
      exact Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2).mpr hpq)
    · intro p hp; exact (Finset.mem_filter.mp hp).2.squarefree
  have hP_pos : 0 < P := Finset.prod_pos fun p hp => (Finset.mem_filter.mp hp).2.pos
  have hP_pf : P.primeFactors = (Finset.Icc h D).filter Nat.Prime :=
    Nat.primeFactors_prod fun p hp => (Finset.mem_filter.mp hp).2
  set K0 := X / W
  set N := (2 * X) / W - X / W + 1
  have hN_le : (N : ℝ) ≤ 2 * (X : ℝ) / (W : ℝ) := by
    have hN_nat : N * W ≤ 2 * X := by
      have h1 : (2 * X) / W * W ≤ 2 * X := Nat.div_mul_le_self (2 * X) W
      have hpos_div : 1 ≤ X / W := Nat.div_pos hW_le hW_pos
      have hmono : X / W ≤ (2 * X) / W := Nat.div_le_div_right (by omega)
      have hsub : (2 * X) / W - X / W + 1 ≤ (2 * X) / W := by omega
      exact (Nat.mul_le_mul_right W hsub).trans h1
    rw [le_div_iff₀ (by exact_mod_cast hW_pos)]
    exact_mod_cast hN_nat
  let val : ℕ → ℕ := fun k => (W * k + b.val) * (W * k + b.val + h)
  have hval_inj : Function.Injective val := by
    intro k1 k2 heq
    have hmono : StrictMono val := by
      intro a c hac
      have h1 : W * a + b.val < W * c + b.val := by nlinarith
      have h2 : W * a + b.val + h < W * c + b.val + h := by omega
      exact Nat.mul_lt_mul'' h1 h2
    exact hmono.injective heq
  let nu : ArithmeticFunction ℝ :=
    ArithmeticFunction.prodPrimeFactors (fun p => if p ∈ P.primeFactors then (2 : ℝ) / p else 0)
  have hnu_mult : nu.IsMultiplicative := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  have hnu_prime : ∀ p : ℕ, p.Prime → p ∣ P → nu p = (2 : ℝ) / p := by
    intro p hp hpP
    have hmem : p ∈ P.primeFactors := hp.mem_primeFactors hpP hP_pos.ne'
    change ArithmeticFunction.prodPrimeFactors
      (fun q => if q ∈ P.primeFactors then (2 : ℝ) / q else 0) p = (2 : ℝ) / p
    rw [ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors,
      Finset.prod_singleton, if_pos hmem]
  have hprime_ge5 : ∀ p : ℕ, p.Prime → p ∣ P → 5 ≤ p := by
    intro p hp hpP
    have hmem : p ∈ P.primeFactors := hp.mem_primeFactors hpP hP_pos.ne'
    rw [hP_pf, Finset.mem_filter, Finset.mem_Icc] at hmem
    have hp_ne4 : p ≠ 4 := by intro h4; subst h4; exact absurd hp (by decide)
    omega
  let s : BoundingSieve := {
    support := (Finset.Ico K0 (K0 + N)).image val
    prodPrimes := P
    prodPrimes_squarefree := hP_sq
    weights := fun _ => 1
    weights_nonneg := fun _ => zero_le_one
    totalMass := (N : ℝ)
    nu := nu
    nu_mult := hnu_mult
    nu_pos_of_prime := fun p hp hpP => by
      rw [hnu_prime p hp hpP]
      have := hp.pos
      positivity
    nu_lt_one_of_prime := fun p hp hpP => by
      rw [hnu_prime p hp hpP]
      have hp5 : (5 : ℝ) ≤ p := by exact_mod_cast hprime_ge5 p hp hpP
      rw [div_lt_one (by linarith)]
      linarith
  }
  have hcards_le : ((primePairs X h b).card : ℝ) ≤ s.siftedSum := by
    have hsub : (primePairs X h b).image (fun m => m * (m + h)) ⊆
        s.support.filter (Nat.Coprime P) := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨m, hm, rfl⟩
      simp only [primePairs, Finset.mem_filter, Finset.mem_Icc] at hm
      simp only [Finset.mem_filter, s, Finset.mem_image, Finset.mem_Ico]
      refine ⟨⟨m / W, ⟨?_, ?_⟩, ?_⟩, ?_⟩
      · exact Nat.div_le_div_right hm.1.1
      · have hle : m / W ≤ (2 * X) / W := Nat.div_le_div_right hm.1.2
        have hK0le : K0 ≤ (2 * X) / W := Nat.div_le_div_right (by omega)
        omega
      · have hmod : m % W = b.val := by
          have := congrArg ZMod.val hm.2.2.2
          simpa [W, ZMod.val_natCast] using this
        have hm_eq : W * (m / W) + b.val = m := by rw [← hmod]; exact Nat.div_add_mod m W
        simp [val, hm_eq]
      · apply Nat.coprime_prod_left_iff.mpr
        intro q hq
        simp only [Finset.mem_filter, Finset.mem_Icc] at hq
        rw [hq.2.coprime_iff_not_dvd]
        intro hdvd
        rcases hq.2.dvd_mul.mp hdvd with hqm | hqmh
        · have := (Nat.prime_dvd_prime_iff_eq hq.2 hm.2.1).mp hqm
          omega
        · have := (Nat.prime_dvd_prime_iff_eq hq.2 hm.2.2.1).mp hqmh
          omega
    have hinj : Set.InjOn (fun m => m * (m + h)) (↑(primePairs X h b) : Set ℕ) := by
      intro m1 _ m2 _ heq
      have hmono : StrictMono (fun m : ℕ => m * (m + h)) := by
        intro a c hac; exact Nat.mul_lt_mul'' hac (by omega)
      exact hmono.injective heq
    have hsifted : s.siftedSum = ((s.support.filter (Nat.Coprime P)).card : ℝ) := by
      simp [BoundingSieve.siftedSum, s]
    rw [hsifted, ← Finset.card_image_of_injOn hinj]
    exact_mod_cast Finset.card_le_card hsub
  have hselberg_eq : ∀ d, d ∣ P → s.selbergTerms d = g2 d := by
    intro d hd
    rw [s.selbergTerms_apply, ← s.prod_primeFactors_nu hd]
    rw [← Finset.prod_mul_distrib]
    unfold g2
    apply Finset.prod_congr rfl
    intro p hp
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have hpP : p ∣ P := (Nat.dvd_of_mem_primeFactors hp).trans hd
    rw [show s.nu p = (2 : ℝ) / p from hnu_prime p hp_prime hpP]
    have hp5 : (5 : ℝ) ≤ p := by exact_mod_cast hprime_ge5 p hp_prime hpP
    have hne : (p : ℝ) - 2 ≠ 0 := by linarith
    field_simp
  have hS_eq : selbergSum s D = ∑ l ∈ P.divisors.filter (· ≤ D), g2 l := by
    unfold selbergSum
    apply Finset.sum_congr rfl
    intro l hl
    exact hselberg_eq l (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hl).1)
  have hrem_bound : ∀ d, d ∣ P → |s.rem d| ≤ (d : ℝ) := by
    intro d hd
    have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hP_pos.ne' hd
    have hd_pos : 0 < d := Nat.pos_of_ne_zero hd0
    have hd_sq : Squarefree d := hP_sq.squarefree_of_dvd hd
    have : NeZero d := ⟨hd0⟩
    have hcopW : d.Coprime W := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨q, hq_prime, hqg⟩ := Nat.exists_prime_and_dvd hne
      have hqd : q ∣ d := hqg.trans (Nat.gcd_dvd_left d W)
      have hqW : q ∣ W := hqg.trans (Nat.gcd_dvd_right d W)
      have hqP : q ∈ P.primeFactors := hq_prime.mem_primeFactors (hqd.trans hd) hP_pos.ne'
      rw [hP_pf, Finset.mem_filter, Finset.mem_Icc] at hqP
      have hqle : q ≤ h - 1 := hq_prime.dvd_primorial_iff.mp hqW
      omega
    have hcoph : d.Coprime h := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨q, hq_prime, hqg⟩ := Nat.exists_prime_and_dvd hne
      have hqd : q ∣ d := hqg.trans (Nat.gcd_dvd_left d h)
      have hqh : q ∣ h := hqg.trans (Nat.gcd_dvd_right d h)
      have hqP : q ∈ P.primeFactors := hq_prime.mem_primeFactors (hqd.trans hd) hP_pos.ne'
      rw [hP_pf, Finset.mem_filter, Finset.mem_Icc] at hqP
      have hqle : q ≤ h := Nat.le_of_dvd (by omega) hqh
      have hqeq : q = h := by omega
      subst hqeq
      rcases heven with ⟨k, hk⟩
      have h2dvd : 2 ∣ q := ⟨k, by omega⟩
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq_prime).mp h2dvd
      omega
    set Rd := Finset.univ.filter (fun r : ZMod d =>
      ((W : ZMod d) * r + (b.val : ZMod d)) * ((W : ZMod d) * r + (b.val : ZMod d) + (h : ZMod d)) = 0)
    have hRd_card : Rd.card = 2 ^ d.primeFactors.card :=
      card_roots_pair_mod_sqfree W b.val h d hd_sq hcopW hcoph
    have hnu_d : s.nu d = (Rd.card : ℝ) / d := by
      rw [← s.prod_primeFactors_nu hd, hRd_card]
      have hprod_eq : ∏ p ∈ d.primeFactors, s.nu p = ∏ p ∈ d.primeFactors, ((2 : ℝ) / p) := by
        apply Finset.prod_congr rfl
        intro p hp
        exact hnu_prime p (Nat.prime_of_mem_primeFactors hp)
          ((Nat.dvd_of_mem_primeFactors hp).trans hd)
      rw [hprod_eq, Finset.prod_div_distrib, Finset.prod_const, ← Nat.cast_prod,
        Nat.prod_primeFactors_of_squarefree hd_sq]
      push_cast
      rfl
    have hmult_eq : s.multSum d =
        ∑ r ∈ Rd, (((Finset.Ico K0 (K0 + N)).filter (fun k : ℕ => (k : ZMod d) = r)).card : ℝ) := by
      simp only [BoundingSieve.multSum, s, Finset.sum_image (fun a _ c _ h => hval_inj h),
        Finset.sum_boole]
      norm_cast
      have hfilt_eq : (Finset.Ico K0 (K0 + N)).filter (fun k : ℕ => d ∣ val k) =
          Rd.biUnion (fun r => (Finset.Ico K0 (K0 + N)).filter (fun k : ℕ => (k : ZMod d) = r)) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_biUnion, Rd, Finset.mem_univ, true_and]
        constructor
        · intro ⟨hk, hdvd⟩
          refine ⟨(k : ZMod d), ?_, hk, rfl⟩
          have h0 : (val k : ZMod d) = 0 := (ZMod.natCast_eq_zero_iff (val k) d).mpr hdvd
          simpa [val] using h0
        · rintro ⟨r, hr, hk, rfl⟩
          refine ⟨hk, (ZMod.natCast_eq_zero_iff (val k) d).mp ?_⟩
          simpa [val] using hr
      rw [hfilt_eq, Finset.card_biUnion]
      intro r1 _ r2 _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro k hk1 hk2
      exact hne ((Finset.mem_filter.mp hk1).2.symm.trans (Finset.mem_filter.mp hk2).2)
    have hrem_eq : s.rem d =
        ∑ r ∈ Rd, ((((Finset.Ico K0 (K0 + N)).filter (fun k : ℕ => (k : ZMod d) = r)).card : ℝ) -
          (N : ℝ) / d) := by
      simp only [BoundingSieve.rem, hmult_eq, hnu_d, s, Finset.sum_sub_distrib, Finset.sum_const,
        nsmul_eq_mul]
      ring
    rw [hrem_eq]
    calc |∑ r ∈ Rd, ((((Finset.Ico K0 (K0 + N)).filter (fun k : ℕ => (k : ZMod d) = r)).card : ℝ) -
            (N : ℝ) / d)|
        ≤ ∑ r ∈ Rd, |(((Finset.Ico K0 (K0 + N)).filter (fun k : ℕ => (k : ZMod d) = r)).card : ℝ) -
            (N : ℝ) / d| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r ∈ Rd, (1 : ℝ) := Finset.sum_le_sum fun r _ => count_Ico_mod_eq K0 N d hd_pos r
      _ = (Rd.card : ℝ) := by simp
      _ ≤ (d : ℝ) := by
          rw [hRd_card]
          have hle : 2 ^ d.primeFactors.card ≤ d := by
            conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree hd_sq]
            rw [← Finset.prod_const]
            exact Finset.prod_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
          exact_mod_cast hle
  have hw_bound : ∀ d, d ∣ P → d ≤ D → s.selbergTerms d / s.nu d ≤ (d : ℝ) := by
    intro d hd _
    have hd_sq : Squarefree d := hP_sq.squarefree_of_dvd hd
    rw [s.selbergTerms_apply, mul_div_cancel_left₀ _ (s.nu_ne_zero hd)]
    have hprod_le : ∏ p ∈ d.primeFactors, (1 - s.nu p)⁻¹ ≤ ∏ p ∈ d.primeFactors, (p : ℝ) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hp_prime := Nat.prime_of_mem_primeFactors hp
        have hpP := (Nat.dvd_of_mem_primeFactors hp).trans hd
        have := s.nu_lt_one_of_prime p hp_prime hpP
        positivity
      · intro p hp
        have hp_prime := Nat.prime_of_mem_primeFactors hp
        have hpP := (Nat.dvd_of_mem_primeFactors hp).trans hd
        rw [show s.nu p = (2 : ℝ) / p from hnu_prime p hp_prime hpP]
        have hp5 : (5 : ℝ) ≤ p := by exact_mod_cast hprime_ge5 p hp_prime hpP
        have hpos : 0 < 1 - (2 : ℝ) / p := by
          have : (2 : ℝ) / p < 1 := (div_lt_one (by linarith)).mpr (by linarith)
          linarith
        rw [inv_le_iff_one_le_mul₀ hpos]
        have hcalc : (p : ℝ) * (1 - (2 : ℝ) / p) = p - 2 := by field_simp
        rw [hcalc]
        linarith
    calc ∏ p ∈ d.primeFactors, (1 - s.nu p)⁻¹ ≤ ∏ p ∈ d.primeFactors, (p : ℝ) := hprod_le
      _ = (d : ℝ) := by rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd_sq]
  have hsieve := s.siftedSum_le_mainSum_errSum_of_upperMoebius
    (BoundingSieve.lambdaSquared (selbergWeights s D))
    (BoundingSieve.upperMoebius_lambdaSquared _ (selbergWeights_one s (by omega)))
  rw [mainSum_lambdaSquared_selbergWeights s (by omega)] at hsieve
  have herr := errSum_lambdaSquared_selbergWeights_le s (by omega) hw_bound hrem_bound
  have hlogD_pos : 0 < Real.log D := Real.log_pos (by exact_mod_cast (show 1 < D by omega))
  have hS_pos : 0 < selbergSum s D := selbergSum_pos s (by omega)
  have hS_lower : (1 / 64 : ℝ) * (Real.log D) ^ 2 ≤
      (Real.exp 2 * (∏ p ∈ h.primesBelow, (1 - (1 : ℝ) / p)⁻¹) ^ 2) * selbergSum s D := by
    rw [hS_eq]
    have h1 := selberg_denom_factor_ge h D hh hD
    have h2 := prod_inv_one_sub_two_div_primes_le h
    have h3 : 0 ≤ ∑ l ∈ P.divisors.filter (· ≤ D), g2 l := hS_eq ▸ hS_pos.le
    exact h1.trans (mul_le_mul_of_nonneg_right h2 h3)
  have hinvS : (selbergSum s D)⁻¹ ≤
      64 * Real.exp 2 * (∏ p ∈ h.primesBelow, (1 - (1 : ℝ) / p)⁻¹) ^ 2 / (Real.log D) ^ 2 := by
    rw [inv_le_iff_one_le_mul₀ hS_pos]
    have : 64 * Real.exp 2 * (∏ p ∈ h.primesBelow, (1 - (1 : ℝ) / p)⁻¹) ^ 2 / (Real.log D) ^ 2 *
        selbergSum s D =
      (64 / (Real.log D) ^ 2) *
        ((Real.exp 2 * (∏ p ∈ h.primesBelow, (1 - (1 : ℝ) / p)⁻¹) ^ 2) * selbergSum s D) := by ring
    rw [this]
    have hmul := mul_le_mul_of_nonneg_left hS_lower (show 0 ≤ 64 / (Real.log D) ^ 2 by positivity)
    have hleft : 64 / (Real.log D) ^ 2 * ((1 / 64 : ℝ) * (Real.log D) ^ 2) = 1 := by
      field_simp [hlogD_pos.ne']
    linarith
  have hmain_le : s.totalMass * (selbergSum s D)⁻¹ ≤
      (2 * (X : ℝ) / (W : ℝ)) *
        (64 * Real.exp 2 * (∏ p ∈ h.primesBelow, (1 - (1 : ℝ) / p)⁻¹) ^ 2 / (Real.log D) ^ 2) := by
    change (N : ℝ) * (selbergSum s D)⁻¹ ≤ _
    exact mul_le_mul hN_le hinvS (inv_nonneg.mpr hS_pos.le) (by positivity)
  linarith

end PairSieve


end Mod2


section Mod3
open Finset Real Nat
open scoped Classical


section BasicHelpers

lemma sum_range_zmod {n : ℕ} [NeZero n] (f : ZMod n → ℝ) :
    ∑ b ∈ Finset.range n, f (b : ZMod n) = ∑ b : ZMod n, f b := by
  refine Finset.sum_bij (fun b _ => (b : ZMod n)) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · intro a ha b hb hab
    have h := congrArg ZMod.val hab
    rw [ZMod.val_natCast, ZMod.val_natCast,
      Nat.mod_eq_of_lt (Finset.mem_range.mp ha), Nat.mod_eq_of_lt (Finset.mem_range.mp hb)] at h
    exact h
  · intro b _
    exact ⟨b.val, Finset.mem_range.mpr (ZMod.val_lt b), ZMod.natCast_zmod_val b⟩

lemma rpow_add_le_add_rpow_of_le_one {x y t : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (x + y) ^ t ≤ x ^ t + y ^ t := by
  by_cases hxy : x + y = 0
  · have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    subst hx0; subst hy0
    simp [Real.zero_rpow ht0.ne']
  · have hpos : 0 < x + y := lt_of_le_of_ne (by linarith) (Ne.symm hxy)
    have hpow_pos : 0 < (x + y) ^ t := Real.rpow_pos_of_pos hpos t
    have hx_le : x / (x + y) ≤ 1 := (div_le_one hpos).mpr (by linarith)
    have hy_le : y / (x + y) ≤ 1 := (div_le_one hpos).mpr (by linarith)
    have hx_pow : x / (x + y) ≤ (x / (x + y)) ^ t := by
      by_cases hx0 : x = 0
      · subst hx0; simp [Real.zero_rpow ht0.ne']
      · have hxp : 0 < x / (x + y) := div_pos (lt_of_le_of_ne hx (Ne.symm hx0)) hpos
        conv_lhs => rw [← Real.rpow_one (x / (x + y))]
        exact Real.rpow_le_rpow_of_exponent_ge hxp hx_le ht1
    have hy_pow : y / (x + y) ≤ (y / (x + y)) ^ t := by
      by_cases hy0 : y = 0
      · subst hy0; simp [Real.zero_rpow ht0.ne']
      · have hyp : 0 < y / (x + y) := div_pos (lt_of_le_of_ne hy (Ne.symm hy0)) hpos
        conv_lhs => rw [← Real.rpow_one (y / (x + y))]
        exact Real.rpow_le_rpow_of_exponent_ge hyp hy_le ht1
    have hsum1 : (1 : ℝ) ≤ (x / (x + y)) ^ t + (y / (x + y)) ^ t := by
      have : x / (x + y) + y / (x + y) = 1 := by field_simp
      linarith
    rw [Real.div_rpow hx hpos.le, Real.div_rpow hy hpos.le] at hsum1
    have hmul := mul_le_mul_of_nonneg_right hsum1 hpow_pos.le
    rw [one_mul, add_mul, div_mul_cancel₀ _ hpow_pos.ne', div_mul_cancel₀ _ hpow_pos.ne'] at hmul
    exact hmul

lemma avg_mul_pow_le_holder {α : Type*} [Fintype α] [Nonempty α]
    (x y : α → ℝ) (hx : ∀ a, 0 ≤ x a) (hy : ∀ a, 0 ≤ y a)
    {K j : ℕ} (hK : 0 < K) (hj1 : 0 < j) (hj2 : j ≤ K) :
    (1 / (Fintype.card α : ℝ)) * ∑ a, x a ^ (K - j) * y a ^ j ≤
      ((1 / (Fintype.card α : ℝ)) * ∑ a, x a ^ K) ^ (((K : ℝ) - j) / K) *
      ((1 / (Fintype.card α : ℝ)) * ∑ a, y a ^ K) ^ ((j : ℝ) / K) := by
  have hcard_pos : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos (α := α)
  have hK_pos : (0 : ℝ) < K := by exact_mod_cast hK
  by_cases hjK : j = K
  · subst hjK
    simp [div_self hK_pos.ne']
  · have hj_lt : j < K := lt_of_le_of_ne hj2 hjK
    set A := (1 / (Fintype.card α : ℝ)) * ∑ a, x a ^ K
    set B := (1 / (Fintype.card α : ℝ)) * ∑ a, y a ^ K
    have hA_nonneg : 0 ≤ A := mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => pow_nonneg (hx a) _)
    have hB_nonneg : 0 ≤ B := mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => pow_nonneg (hy a) _)
    by_cases hA0 : A = 0
    · have hx0 : ∀ a, x a = 0 := by
        intro a
        have hsum0 : ∑ b : α, x b ^ K = 0 := by
          rcases mul_eq_zero.mp hA0 with h1 | h2
          · exact absurd h1 (by positivity)
          · exact h2
        have hterm0 : x a ^ K = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => pow_nonneg (hx b) _)).mp hsum0 a (Finset.mem_univ a)
        exact eq_zero_of_pow_eq_zero hterm0
      have hlhs0 : (1 / (Fintype.card α : ℝ)) * ∑ a, x a ^ (K - j) * y a ^ j = 0 := by
        have : ∀ a, x a ^ (K - j) * y a ^ j = 0 := fun a => by
          rw [hx0 a, zero_pow (by omega), zero_mul]
        simp [this]
      rw [hlhs0]
      exact mul_nonneg (Real.rpow_nonneg hA_nonneg _) (Real.rpow_nonneg hB_nonneg _)
    · by_cases hB0 : B = 0
      · have hy0 : ∀ a, y a = 0 := by
          intro a
          have hsum0 : ∑ b : α, y b ^ K = 0 := by
            rcases mul_eq_zero.mp hB0 with h1 | h2
            · exact absurd h1 (by positivity)
            · exact h2
          have hterm0 : y a ^ K = 0 :=
            (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => pow_nonneg (hy b) _)).mp hsum0 a (Finset.mem_univ a)
          exact eq_zero_of_pow_eq_zero hterm0
        have hlhs0 : (1 / (Fintype.card α : ℝ)) * ∑ a, x a ^ (K - j) * y a ^ j = 0 := by
          have : ∀ a, x a ^ (K - j) * y a ^ j = 0 := fun a => by
            rw [hy0 a, zero_pow (by omega), mul_zero]
          simp [this]
        rw [hlhs0]
        exact mul_nonneg (Real.rpow_nonneg hA_nonneg _) (Real.rpow_nonneg hB_nonneg _)
      · have hA_pos : 0 < A := lt_of_le_of_ne hA_nonneg (Ne.symm hA0)
        have hB_pos : 0 < B := lt_of_le_of_ne hB_nonneg (Ne.symm hB0)
        set w1 : ℝ := ((K - j : ℕ) : ℝ) / K
        set w2 : ℝ := (j : ℝ) / K
        have hw1_eq : w1 = ((K : ℝ) - j) / K := by
          simp only [w1, Nat.cast_sub hj2]
        have hw_sum : w1 + w2 = 1 := by
          rw [hw1_eq]; simp only [w2]; field_simp [hK_pos.ne']; ring
        have hpt : ∀ a : α,
            x a ^ (K - j) * y a ^ j / (A ^ w1 * B ^ w2) ≤
              w1 * (x a ^ K / A) + w2 * (y a ^ K / B) := by
          intro a
          have hgm := Real.geom_mean_le_arith_mean2_weighted (show 0 ≤ w1 by positivity)
            (show 0 ≤ w2 by positivity) (div_nonneg (pow_nonneg (hx a) K) hA_pos.le)
            (div_nonneg (pow_nonneg (hy a) K) hB_pos.le) hw_sum
          have hlhs_eq : (x a ^ K / A) ^ w1 * (y a ^ K / B) ^ w2 =
              x a ^ (K - j) * y a ^ j / (A ^ w1 * B ^ w2) := by
            rw [Real.div_rpow (pow_nonneg (hx a) K) hA_pos.le,
                Real.div_rpow (pow_nonneg (hy a) K) hB_pos.le]
            have hx_pow : (x a ^ K) ^ w1 = x a ^ (K - j) := by
              rw [← Real.rpow_natCast (x a) K, ← Real.rpow_mul (hx a)]
              have hexp : (K : ℝ) * w1 = ((K - j : ℕ) : ℝ) := by
                simp only [w1]; field_simp [hK_pos.ne']
              rw [hexp, Real.rpow_natCast]
            have hy_pow : (y a ^ K) ^ w2 = y a ^ j := by
              rw [← Real.rpow_natCast (y a) K, ← Real.rpow_mul (hy a)]
              have hexp : (K : ℝ) * w2 = (j : ℝ) := by
                simp only [w2]; field_simp [hK_pos.ne']
              rw [hexp, Real.rpow_natCast]
            rw [hx_pow, hy_pow]
            ring
          rwa [hlhs_eq] at hgm
        have havg : (1 / (Fintype.card α : ℝ)) * ∑ a, x a ^ (K - j) * y a ^ j / (A ^ w1 * B ^ w2) ≤ 1 := by
          calc (1 / (Fintype.card α : ℝ)) * ∑ a, x a ^ (K - j) * y a ^ j / (A ^ w1 * B ^ w2)
              ≤ (1 / (Fintype.card α : ℝ)) * ∑ a, (w1 * (x a ^ K / A) + w2 * (y a ^ K / B)) := by
                gcongr with a
                exact hpt a
            _ = w1 * (A / A) + w2 * (B / B) := by
                rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
                    ← Finset.sum_div, ← Finset.sum_div]
                simp only [A, B]
                ring
            _ = 1 := by
                rw [div_self hA_pos.ne', div_self hB_pos.ne']
                linarith
        have hdenom_pos : 0 < A ^ w1 * B ^ w2 :=
          mul_pos (Real.rpow_pos_of_pos hA_pos w1) (Real.rpow_pos_of_pos hB_pos w2)
        have hpull : (1 / (Fintype.card α : ℝ)) * ∑ a, x a ^ (K - j) * y a ^ j / (A ^ w1 * B ^ w2) =
            ((1 / (Fintype.card α : ℝ)) * ∑ a, x a ^ (K - j) * y a ^ j) / (A ^ w1 * B ^ w2) := by
          rw [← Finset.sum_div]; ring
        rw [hpull, div_le_one hdenom_pos] at havg
        rwa [← hw1_eq]

lemma sum_pow_le_card_pow {ι : Type*} (s : Finset ι) (f : ι → ℝ) (K : ℕ) (hK : 1 ≤ K) :
    |∑ i ∈ s, f i| ^ K ≤ (s.card : ℝ) ^ (K - 1) * ∑ i ∈ s, |f i| ^ K := by
  by_cases hs : s = ∅
  · subst hs; simp [zero_pow (by omega : K ≠ 0)]
  · have hcard_pos : (0 : ℝ) < s.card := by
      exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
    have h1 : |∑ i ∈ s, f i| ≤ ∑ i ∈ s, |f i| := Finset.abs_sum_le_sum_abs _ _
    have hconv : ((1 / (s.card : ℝ)) * ∑ i ∈ s, |f i|) ^ K ≤
        (1 / (s.card : ℝ)) * ∑ i ∈ s, |f i| ^ K := by
      have hj := (convexOn_pow K).map_sum_le (t := s) (w := fun _ => (1 : ℝ) / s.card)
        (p := fun i => |f i|) (fun _ _ => by positivity)
        (by simp [hcard_pos.ne']) (fun i _ => Set.mem_Ici.mpr (abs_nonneg _))
      simpa [smul_eq_mul, ← Finset.mul_sum] using hj
    have h2 : (∑ i ∈ s, |f i|) ^ K ≤ (s.card : ℝ) ^ (K - 1) * ∑ i ∈ s, |f i| ^ K := by
      rw [mul_pow, one_div_pow] at hconv
      have hmul := mul_le_mul_of_nonneg_left hconv (pow_nonneg hcard_pos.le K)
      have hlhs : (s.card : ℝ) ^ K * ((1 : ℝ) / (s.card : ℝ) ^ K * (∑ i ∈ s, |f i|) ^ K) =
          (∑ i ∈ s, |f i|) ^ K := by
        field_simp [hcard_pos.ne']
      have hrhs : (s.card : ℝ) ^ K * (1 / (s.card : ℝ) * ∑ i ∈ s, |f i| ^ K) =
          (s.card : ℝ) ^ (K - 1) * ∑ i ∈ s, |f i| ^ K := by
        have hpow : (s.card : ℝ) ^ K = (s.card : ℝ) ^ (K - 1) * (s.card : ℝ) := by
          rw [← pow_succ, Nat.sub_add_cancel hK]
        rw [hpow]
        field_simp [hcard_pos.ne']
      linarith
    exact (pow_le_pow_left₀ (abs_nonneg _) h1 K).trans h2

lemma abs_three_add_pow_le (a b c : ℝ) (K : ℕ) (hK : 1 ≤ K) :
    |a + b + c| ^ K ≤ 3 ^ K * (|a| ^ K + |b| ^ K + |c| ^ K) := by
  have h := sum_pow_le_card_pow (Finset.univ : Finset (Fin 3)) ![a, b, c] K hK
  simp only [Finset.card_univ, Fintype.card_fin, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two] at h
  have h3 : (3 : ℝ) ^ (K - 1) ≤ (3 : ℝ) ^ K :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le K 1)
  have hnonneg : 0 ≤ |a| ^ K + |b| ^ K + |c| ^ K := by positivity
  calc |a + b + c| ^ K ≤ (3 : ℝ) ^ (K - 1) * (|a| ^ K + |b| ^ K + |c| ^ K) := by
        simpa [add_assoc] using h
    _ ≤ (3 : ℝ) ^ K * (|a| ^ K + |b| ^ K + |c| ^ K) := mul_le_mul_of_nonneg_right h3 hnonneg

lemma abs_two_add_pow_le (a b : ℝ) (K : ℕ) (hK : 1 ≤ K) :
    |a + b| ^ K ≤ 2 ^ K * (|a| ^ K + |b| ^ K) := by
  have h := sum_pow_le_card_pow (Finset.univ : Finset (Fin 2)) ![a, b] K hK
  simp only [Finset.card_univ, Fintype.card_fin, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h
  have h2 : (2 : ℝ) ^ (K - 1) ≤ (2 : ℝ) ^ K :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le K 1)
  have hnonneg : 0 ≤ |a| ^ K + |b| ^ K := by positivity
  exact h.trans (mul_le_mul_of_nonneg_right h2 hnonneg)

lemma add_pow_split_two (Z Δ : ℝ) (K : ℕ) (hK : 2 ≤ K) :
    (Z + Δ) ^ K =
      Z ^ K + (K : ℝ) * Z ^ (K - 1) * Δ +
      ∑ j ∈ Finset.Icc 2 K, (Nat.choose K j : ℝ) * Z ^ (K - j) * Δ ^ j := by
  rw [add_comm Z Δ, add_pow]
  have hrange : Finset.range (K + 1) = insert 0 (insert 1 (Finset.Icc 2 K)) := by
    ext j; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [hrange, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, Nat.sub_zero,
    Nat.choose_one_right, pow_one, one_mul]
  have hcomm : ∑ x ∈ Finset.Icc 2 K, Δ ^ x * Z ^ (K - x) * (Nat.choose K x : ℝ) =
      ∑ j ∈ Finset.Icc 2 K, (Nat.choose K j : ℝ) * Z ^ (K - j) * Δ ^ j := by
    apply Finset.sum_congr rfl; intro j _; ring
  rw [hcomm]; ring

end BasicHelpers

section PrimeSetModel

def prodQ (Q : Finset ℕ) : ℕ := ∏ q ∈ Q, q

noncomputable def densQ (Q : Finset ℕ) : ℝ := ∏ q ∈ Q, (1 - (1 : ℝ) / q)

noncomputable def countSub (Q A : Finset ℕ) (b : ZMod (prodQ Q)) : ℝ :=
  ∑ i ∈ A, if IsUnit (b + (i : ZMod (prodQ Q))) then (1 : ℝ) else 0

noncomputable def countQ (Q : Finset ℕ) (L : ℕ) (b : ZMod (prodQ Q)) : ℝ :=
  countSub Q (Finset.Icc 1 L) b

noncomputable def centMom (K : ℕ) (Q : Finset ℕ) (L : ℕ) : ℝ :=
  (1 / (prodQ Q : ℝ)) *
    ∑ b ∈ Finset.range (prodQ Q), (countQ Q L (b : ZMod (prodQ Q)) - (L : ℝ) * densQ Q) ^ K

lemma prodQ_pos {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) : 0 < prodQ Q :=
  Finset.prod_pos fun q hq => (hQ q hq).pos

lemma prodQ_ne_zero {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) : prodQ Q ≠ 0 :=
  (prodQ_pos hQ).ne'

lemma centMom_eq_sum_zmod (K : ℕ) (Q : Finset ℕ) (L : ℕ) [NeZero (prodQ Q)] :
    centMom K Q L =
      (1 / (prodQ Q : ℝ)) * ∑ b : ZMod (prodQ Q), (countQ Q L b - (L : ℝ) * densQ Q) ^ K := by
  unfold centMom
  rw [sum_range_zmod (fun b : ZMod (prodQ Q) => (countQ Q L b - (L : ℝ) * densQ Q) ^ K)]

lemma prodQ_coprime_of_disjoint {Q1 Q2 : Finset ℕ}
    (hQ1 : ∀ q ∈ Q1, q.Prime) (hQ2 : ∀ q ∈ Q2, q.Prime) (hdisj : Disjoint Q1 Q2) :
    (prodQ Q1).Coprime (prodQ Q2) := by
  unfold prodQ
  apply Nat.coprime_prod_left_iff.mpr; intro p hp
  apply Nat.coprime_prod_right_iff.mpr; intro q hq
  have hpq : p ≠ q := fun heq => Finset.disjoint_left.mp hdisj hp (heq ▸ hq)
  exact (Nat.coprime_primes (hQ1 p hp) (hQ2 q hq)).mpr hpq

lemma densQ_pos {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) : 0 < densQ Q := by
  unfold densQ
  apply Finset.prod_pos
  intro q hq
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (hQ q hq).two_le
  have : (1 : ℝ) / q ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hq2
  linarith

lemma densQ_le_one {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) : densQ Q ≤ 1 := by
  unfold densQ
  apply Finset.prod_le_one
  · intro q hq
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (hQ q hq).two_le
    have : (1 : ℝ) / q ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hq2
    linarith
  · intro q hq
    have : (0 : ℝ) < 1 / q := by have := (hQ q hq).pos; positivity
    linarith

lemma densQ_empty : densQ ∅ = 1 := by simp [densQ]

lemma densQ_insert {Q : Finset ℕ} {q : ℕ} (hq : q ∉ Q) :
    densQ (insert q Q) = (1 - (1 : ℝ) / q) * densQ Q :=
  Finset.prod_insert hq

lemma densQ_union {Q1 Q2 : Finset ℕ} (hdisj : Disjoint Q1 Q2) :
    densQ (Q1 ∪ Q2) = densQ Q1 * densQ Q2 :=
  Finset.prod_union hdisj

lemma prodQ_union {Q1 Q2 : Finset ℕ} (hdisj : Disjoint Q1 Q2) :
    prodQ (Q1 ∪ Q2) = prodQ Q1 * prodQ Q2 :=
  Finset.prod_union hdisj

lemma centMom_empty (K L : ℕ) (hK : 1 ≤ K) : centMom K ∅ L = 0 := by
  unfold centMom
  have hP1 : prodQ ∅ = 1 := rfl
  have hsum0 : ∑ b ∈ Finset.range (prodQ ∅),
      (countQ ∅ L (b : ZMod (prodQ ∅)) - (L : ℝ) * densQ ∅) ^ K = 0 := by
    apply Finset.sum_eq_zero; intro b _
    have hcnt : countQ ∅ L (b : ZMod (prodQ ∅)) = (L : ℝ) := by
      unfold countQ countSub
      have h1 : ∀ i ∈ Finset.Icc 1 L, IsUnit ((b : ZMod (prodQ ∅)) + (i : ZMod (prodQ ∅))) := by
        intro i _
        change IsUnit ((b : ZMod 1) + (i : ZMod 1))
        rw [Subsingleton.elim ((b : ZMod 1) + (i : ZMod 1)) 1]
        exact isUnit_one
      rw [Finset.sum_congr rfl (fun i hi => if_pos (h1 i hi)), Finset.sum_const, nsmul_eq_mul, mul_one]
      simp [Nat.card_Icc]
    rw [hcnt, densQ_empty, mul_one, sub_self, zero_pow (by omega)]
  rw [hsum0, mul_zero]

def zmodRingEquivOfEq {a b : ℕ} (h : a = b) : ZMod a ≃+* ZMod b :=
  h ▸ RingEquiv.refl (ZMod a)

def crtUnion {Q1 Q2 : Finset ℕ} (hQ1 : ∀ q ∈ Q1, q.Prime) (hQ2 : ∀ q ∈ Q2, q.Prime)
    (hdisj : Disjoint Q1 Q2) :
    ZMod (prodQ (Q1 ∪ Q2)) ≃+* ZMod (prodQ Q1) × ZMod (prodQ Q2) :=
  (zmodRingEquivOfEq (prodQ_union hdisj)).trans
    (ZMod.chineseRemainder (prodQ_coprime_of_disjoint hQ1 hQ2 hdisj))

def crtInsert {Q : Finset ℕ} {q : ℕ} (hq : q.Prime) (hQ : ∀ p ∈ Q, p.Prime) (hqnot : q ∉ Q) :
    ZMod (prodQ (insert q Q)) ≃+* ZMod q × ZMod (prodQ Q) :=
  (zmodRingEquivOfEq (Finset.prod_insert hqnot)).trans
    (ZMod.chineseRemainder (by
      apply Nat.coprime_prod_right_iff.mpr; intro p hp
      exact (Nat.coprime_primes hq (hQ p hp)).mpr (fun heq => hqnot (heq ▸ hp))))

lemma isUnit_crt_iff {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (e : R ≃+* S × T) (x : R) :
    IsUnit x ↔ IsUnit (e x).1 ∧ IsUnit (e x).2 := by
  rw [← Prod.isUnit_iff]
  exact ⟨fun h => h.map e.toMonoidHom, fun h => by simpa using h.map e.symm.toMonoidHom⟩

lemma countSub_crtInsert {Q A : Finset ℕ} {q : ℕ} (hq : q.Prime) (hQ : ∀ p ∈ Q, p.Prime)
    (hqnot : q ∉ Q) (r : ZMod q) (b : ZMod (prodQ Q)) :
    countSub (insert q Q) A ((crtInsert hq hQ hqnot).symm (r, b)) =
      countSub Q A b -
        countSub Q (A.filter (fun i : ℕ => r + (i : ZMod q) = 0)) b := by
  have : Fact q.Prime := ⟨hq⟩
  let e := crtInsert hq hQ hqnot
  unfold countSub
  rw [Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hunit : IsUnit ((crtInsert hq hQ hqnot).symm (r, b) + (i : ZMod (prodQ (insert q Q)))) ↔
      IsUnit (r + (i : ZMod q)) ∧ IsUnit (b + (i : ZMod (prodQ Q))) := by
    rw [isUnit_crt_iff e]
    simp [e, map_add, map_natCast, RingEquiv.apply_symm_apply]
  have hq_unit : IsUnit (r + (i : ZMod q)) ↔ r + (i : ZMod q) ≠ 0 := isUnit_iff_ne_zero
  simp only [hunit, hq_unit]
  by_cases h1 : r + (i : ZMod q) = 0 <;> by_cases h2 : IsUnit (b + (i : ZMod (prodQ Q))) <;>
    simp [h1, h2]

lemma avg_countSub_filter_zero {Q A : Finset ℕ} {q : ℕ} [NeZero q]
    (b : ZMod (prodQ Q)) :
    (1 / (q : ℝ)) * ∑ r : ZMod q, countSub Q (A.filter (fun i : ℕ => r + (i : ZMod q) = 0)) b =
      countSub Q A b / q := by
  unfold countSub
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  have hinner : ∀ i ∈ A,
      (∑ r : ZMod q, if r + (i : ZMod q) = 0 then
          if IsUnit (b + (i : ZMod (prodQ Q))) then (1 : ℝ) else 0
        else 0) =
      if IsUnit (b + (i : ZMod (prodQ Q))) then (1 : ℝ) else 0 := by
    intro i _
    have hiff : ∀ r : ZMod q, (r + (i : ZMod q) = 0) ↔ r = -(i : ZMod q) := fun r => by
      constructor
      · intro h; exact eq_neg_of_add_eq_zero_left h
      · intro h; rw [h, neg_add_cancel]
    simp_rw [hiff]
    simp
  rw [Finset.sum_congr rfl hinner]
  ring

lemma sum_delta_insert_eq_zero {Q A : Finset ℕ} {q : ℕ} [NeZero q]
    (hq : q.Prime) (hQ : ∀ p ∈ Q, p.Prime)
    (hqnot : q ∉ Q) (b : ZMod (prodQ Q)) :
    ∑ r : ZMod q,
      (countSub (insert q Q) A ((crtInsert hq hQ hqnot).symm (r, b)) -
        (1 - (1 : ℝ) / q) * countSub Q A b) = 0 := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
  simp_rw [countSub_crtInsert hq hQ hqnot]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have havg := avg_countSub_filter_zero b (Q := Q) (A := A) (q := q)
  have hsum : ∑ r : ZMod q, countSub Q (A.filter (fun i : ℕ => r + (i : ZMod q) = 0)) b =
      countSub Q A b := by
    have := congrArg ((q : ℝ) * ·) havg
    field_simp [hq0] at this
    exact this
  rw [hsum]
  field_simp [hq0]
  ring

lemma avg_zmod_insert {Q : Finset ℕ} {q : ℕ} [NeZero q] [NeZero (prodQ Q)]
    [NeZero (prodQ (insert q Q))]
    (hq : q.Prime) (hQ : ∀ p ∈ Q, p.Prime) (hqnot : q ∉ Q)
    (f : ZMod (prodQ (insert q Q)) → ℝ) :
    (1 / (prodQ (insert q Q) : ℝ)) * ∑ b : ZMod (prodQ (insert q Q)), f b =
      (1 / (prodQ Q : ℝ)) * ∑ b : ZMod (prodQ Q),
        (1 / (q : ℝ)) * ∑ r : ZMod q, f ((crtInsert hq hQ hqnot).symm (r, b)) := by
  have hprod : (prodQ (insert q Q) : ℝ) = (q : ℝ) * (prodQ Q : ℝ) := by
    unfold prodQ; rw [Finset.prod_insert hqnot]; push_cast; rfl
  let e := crtInsert hq hQ hqnot
  have hsum : ∑ b : ZMod (prodQ (insert q Q)), f b =
      ∑ p : ZMod q × ZMod (prodQ Q), f (e.symm p) :=
    (Fintype.sum_equiv e.symm (fun p => f (e.symm p)) f (fun _ => rfl)).symm
  rw [hsum, Fintype.sum_prod_type_right, hprod]
  simp_rw [← Finset.mul_sum]
  ring

lemma avg_zmod_union {Q1 Q2 : Finset ℕ} [NeZero (prodQ Q1)] [NeZero (prodQ Q2)]
    [NeZero (prodQ (Q1 ∪ Q2))]
    (hQ1 : ∀ p ∈ Q1, p.Prime) (hQ2 : ∀ p ∈ Q2, p.Prime) (hdisj : Disjoint Q1 Q2)
    (f : ZMod (prodQ (Q1 ∪ Q2)) → ℝ) :
    (1 / (prodQ (Q1 ∪ Q2) : ℝ)) * ∑ b : ZMod (prodQ (Q1 ∪ Q2)), f b =
      (1 / (prodQ Q1 : ℝ)) * ∑ b1 : ZMod (prodQ Q1),
        (1 / (prodQ Q2 : ℝ)) * ∑ b2 : ZMod (prodQ Q2),
          f ((crtUnion hQ1 hQ2 hdisj).symm (b1, b2)) := by
  have hprod : (prodQ (Q1 ∪ Q2) : ℝ) = (prodQ Q1 : ℝ) * (prodQ Q2 : ℝ) := by
    rw [prodQ_union hdisj]; push_cast; rfl
  let e := crtUnion hQ1 hQ2 hdisj
  have hsum : ∑ b : ZMod (prodQ (Q1 ∪ Q2)), f b =
      ∑ p : ZMod (prodQ Q1) × ZMod (prodQ Q2), f (e.symm p) :=
    (Fintype.sum_equiv e.symm (fun p => f (e.symm p)) f (fun _ => rfl)).symm
  rw [hsum, Fintype.sum_prod_type, hprod]
  simp_rw [← Finset.mul_sum]
  ring

end PrimeSetModel

section LargePrimesMartingale

def largeMartConst : ℕ → ℝ
  | 0 => 1
  | k + 1 => (2 : ℝ) ^ (2 * (k + 1)) * (1 + largeMartConst k)

lemma largeMartConst_pos (k : ℕ) : 0 < largeMartConst k := by
  induction k with
  | zero => simp [largeMartConst]
  | succ k ih => simp only [largeMartConst]; positivity

private lemma large_primes_inner_step (k L q : ℕ) (A S : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 L) (hS_prime : ∀ p ∈ S, p.Prime)
    (hq_prime : q.Prime) (hq_gt : L < q) (hqnot : q ∉ S)
    (V : ℝ) (hV1 : 1 ≤ V) [NeZero q] (b : ZMod (prodQ S)) :
    (1 / (q : ℝ)) * ∑ r : ZMod q,
      (countSub (insert q S) A ((crtInsert hq_prime hS_prime hqnot).symm (r, b)) -
        (A.card : ℝ) * densQ (insert q S)) ^ (2 * (k + 1)) ≤
    (countSub S A b - (A.card : ℝ) * densQ S) ^ (2 * (k + 1)) +
    ((2 : ℝ) ^ (2 * (k + 1)) * ((L : ℝ) / q)) *
      (V ^ k + (countSub S A b - (A.card : ℝ) * densQ S) ^ (2 * k)) := by
  set K := 2 * (k + 1)
  have hq_pos : (0 : ℝ) < q := by exact_mod_cast hq_prime.pos
  set Z := (1 - (1 : ℝ) / q) * (countSub S A b - (A.card : ℝ) * densQ S)
  set Δ : ZMod q → ℝ := fun r =>
    countSub (insert q S) A ((crtInsert hq_prime hS_prime hqnot).symm (r, b)) -
      (1 - (1 : ℝ) / q) * countSub S A b
  have hsplit : ∀ r : ZMod q,
      countSub (insert q S) A ((crtInsert hq_prime hS_prime hqnot).symm (r, b)) -
        (A.card : ℝ) * densQ (insert q S) = Z + Δ r := by
    intro r
    simp only [Z, Δ, densQ_insert hqnot]
    ring
  simp_rw [hsplit, add_pow_split_two Z _ K (by omega)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h1 : (1 / (q : ℝ)) * ∑ _r : ZMod q, Z ^ K = Z ^ K := by
    simp [ZMod.card, hq_pos.ne']
  have h2 : ∑ r : ZMod q, (K : ℝ) * Z ^ (K - 1) * Δ r = 0 := by
    rw [← Finset.mul_sum, sum_delta_insert_eq_zero hq_prime hS_prime hqnot b, mul_zero]
  have hZ_le : Z ^ K ≤ (countSub S A b - (A.card : ℝ) * densQ S) ^ K := by
    have hfac_nonneg : 0 ≤ 1 - (1 : ℝ) / q := by
      have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq_prime.two_le
      have : (1 : ℝ) / q ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hq2
      linarith
    have hfac_le : (1 - (1 : ℝ) / q) ^ K ≤ 1 :=
      pow_le_one₀ hfac_nonneg (by linarith [show (0 : ℝ) < 1 / q by positivity])
    have hpow_nonneg : 0 ≤ (countSub S A b - (A.card : ℝ) * densQ S) ^ K :=
      Even.pow_nonneg ⟨k + 1, by dsimp only [K]; omega⟩ _
    simp only [Z, mul_pow]
    exact mul_le_of_le_one_left hpow_nonneg hfac_le
  have hN_le_one : ∀ r : ZMod q,
      countSub S (A.filter (fun i : ℕ => r + (i : ZMod q) = 0)) b ≤ 1 := by
    intro r
    have hcard_le : (A.filter (fun i : ℕ => r + (i : ZMod q) = 0)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro i hi j hj
      simp only [Finset.mem_filter] at hi hj
      have hiL := Finset.mem_Icc.mp (hA hi.1)
      have hjL := Finset.mem_Icc.mp (hA hj.1)
      have hmod : (i : ZMod q) = (j : ZMod q) := by
        have h1' : (i : ZMod q) = -r := eq_neg_of_add_eq_zero_right hi.2
        have h2' : (j : ZMod q) = -r := eq_neg_of_add_eq_zero_right hj.2
        exact h1'.trans h2'.symm
      have hval := congrArg ZMod.val hmod
      rw [ZMod.val_natCast, ZMod.val_natCast,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hval
      exact hval
    unfold countSub
    calc ∑ i ∈ A.filter (fun i : ℕ => r + (i : ZMod q) = 0),
            (if IsUnit (b + (i : ZMod (prodQ S))) then (1 : ℝ) else 0)
        ≤ ∑ _i ∈ A.filter (fun i : ℕ => r + (i : ZMod q) = 0), (1 : ℝ) := by
          apply Finset.sum_le_sum; intro i _; split_ifs <;> norm_num
      _ = ((A.filter (fun i : ℕ => r + (i : ZMod q) = 0)).card : ℝ) := by simp
      _ ≤ 1 := by exact_mod_cast hcard_le
  have hcnt_le_L : countSub S A b ≤ (L : ℝ) := by
    unfold countSub
    calc ∑ i ∈ A, (if IsUnit (b + (i : ZMod (prodQ S))) then (1 : ℝ) else 0)
        ≤ ∑ _i ∈ A, (1 : ℝ) := Finset.sum_le_sum fun _ _ => by split_ifs <;> norm_num
      _ = (A.card : ℝ) := by simp
      _ ≤ ((Finset.Icc 1 L).card : ℝ) := by exact_mod_cast Finset.card_le_card hA
      _ = (L : ℝ) := by simp
  have hcnt_nonneg : 0 ≤ countSub S A b := by
    unfold countSub; apply Finset.sum_nonneg; intro _ _; split_ifs <;> norm_num
  have hΔ_eq : ∀ r : ZMod q, Δ r = countSub S A b / q -
      countSub S (A.filter (fun i : ℕ => r + (i : ZMod q) = 0)) b := fun r => by
    simp only [Δ]
    rw [countSub_crtInsert hq_prime hS_prime hqnot]
    ring
  have hΔ_abs_le : ∀ r : ZMod q, |Δ r| ≤ 1 := by
    intro r
    rw [hΔ_eq r, abs_le]
    have h1' : 0 ≤ countSub S A b / q := div_nonneg hcnt_nonneg hq_pos.le
    have h2' : countSub S A b / q ≤ 1 := by
      rw [div_le_one hq_pos]
      exact hcnt_le_L.trans (by exact_mod_cast hq_gt.le)
    have h3' : 0 ≤ countSub S (A.filter (fun i : ℕ => r + (i : ZMod q) = 0)) b := by
      unfold countSub; apply Finset.sum_nonneg; intro _ _; split_ifs <;> norm_num
    have h4' := hN_le_one r
    constructor <;> linarith
  have hΔ_sq_avg : (1 / (q : ℝ)) * ∑ r : ZMod q, (Δ r) ^ 2 ≤ (L : ℝ) / q := by
    have hsq : ∀ r : ZMod q, (Δ r) ^ 2 =
        (countSub S (A.filter (fun i : ℕ => r + (i : ZMod q) = 0)) b) ^ 2 -
        2 * (countSub S A b / q) * countSub S (A.filter (fun i : ℕ => r + (i : ZMod q) = 0)) b +
        (countSub S A b / q) ^ 2 := fun r => by rw [hΔ_eq r]; ring
    simp_rw [hsq]
    have hle1 : ∀ r : ZMod q,
        (countSub S (A.filter (fun i : ℕ => r + (i : ZMod q) = 0)) b) ^ 2 ≤
        countSub S (A.filter (fun i : ℕ => r + (i : ZMod q) = 0)) b := by
      intro r
      have h0 : 0 ≤ countSub S (A.filter (fun i : ℕ => r + (i : ZMod q) = 0)) b := by
        unfold countSub; apply Finset.sum_nonneg; intro _ _; split_ifs <;> norm_num
      have h1' := hN_le_one r
      nlinarith
    have hsum_avg := avg_countSub_filter_zero b (Q := S) (A := A) (q := q)
    calc (1 / (q : ℝ)) * ∑ r : ZMod q,
            ((countSub S (A.filter (fun i : ℕ => r + (i : ZMod q) = 0)) b) ^ 2 -
            2 * (countSub S A b / q) *
              countSub S (A.filter (fun i : ℕ => r + (i : ZMod q) = 0)) b +
            (countSub S A b / q) ^ 2)
        ≤ (1 / (q : ℝ)) * ∑ r : ZMod q,
            (countSub S (A.filter (fun i : ℕ => r + (i : ZMod q) = 0)) b -
            2 * (countSub S A b / q) *
              countSub S (A.filter (fun i : ℕ => r + (i : ZMod q) = 0)) b +
            (countSub S A b / q) ^ 2) := by
          gcongr with r
          exact hle1 r
      _ = countSub S A b / q - (countSub S A b / q) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
          simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
          have hsum_eq : ∑ r : ZMod q,
              countSub S (A.filter (fun i : ℕ => r + (i : ZMod q) = 0)) b = countSub S A b := by
            have := congrArg ((q : ℝ) * ·) hsum_avg
            rw [← mul_assoc, mul_one_div_cancel hq_pos.ne', one_mul, mul_div_cancel₀ _ hq_pos.ne'] at this
            exact this
          rw [hsum_eq]
          field_simp [hq_pos.ne']
          ring
      _ ≤ countSub S A b / q := by linarith [sq_nonneg (countSub S A b / q)]
      _ ≤ (L : ℝ) / q := by gcongr
  have htail : (1 / (q : ℝ)) * ∑ r : ZMod q,
      ∑ j ∈ Finset.Icc 2 K, (Nat.choose K j : ℝ) * Z ^ (K - j) * (Δ r) ^ j ≤
      ((2 : ℝ) ^ K * ((L : ℝ) / q)) *
        (V ^ k + (countSub S A b - (A.card : ℝ) * densQ S) ^ (2 * k)) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    have hZ_pow : ∀ j ∈ Finset.Icc 2 K,
        |Z| ^ (K - j) ≤ V ^ k + (countSub S A b - (A.card : ℝ) * densQ S) ^ (2 * k) := by
      intro j hj
      simp only [Finset.mem_Icc] at hj
      set u := |countSub S A b - (A.card : ℝ) * densQ S|
      have hZu : |Z| ≤ u := by
        simp only [Z, u, abs_mul]
        have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq_prime.two_le
        have hfac : |1 - (1 : ℝ) / q| ≤ 1 := by
          rw [abs_of_nonneg]
          · linarith [show (0 : ℝ) < 1 / q by positivity]
          · have : (1 : ℝ) / q ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hq2
            linarith
        exact mul_le_of_le_one_left (abs_nonneg _) hfac
      have hu_pow : u ^ (K - j) ≤ V ^ k + u ^ (2 * k) := by
        by_cases hu : u ≤ Real.sqrt V
        · have hle : u ^ (K - j) ≤ (Real.sqrt V) ^ (K - j) :=
            pow_le_pow_left₀ (abs_nonneg _) hu _
          have hrt : (Real.sqrt V) ^ (K - j) ≤ (Real.sqrt V) ^ (2 * k) :=
            pow_le_pow_right₀ (Real.one_le_sqrt.mpr hV1) (by omega)
          have hsq : (Real.sqrt V) ^ (2 * k) = V ^ k := by
            rw [pow_mul, Real.sq_sqrt (by linarith)]
          linarith [pow_nonneg (abs_nonneg (countSub S A b - (A.card : ℝ) * densQ S)) (2 * k)]
        · push Not at hu
          have hu1 : 1 ≤ u := (Real.one_le_sqrt.mpr hV1).trans hu.le
          have hle : u ^ (K - j) ≤ u ^ (2 * k) := pow_le_pow_right₀ hu1 (by omega)
          linarith [pow_nonneg (by linarith : (0 : ℝ) ≤ V) k]
      have h2k_eq : u ^ (2 * k) = (countSub S A b - (A.card : ℝ) * densQ S) ^ (2 * k) := by
        simp only [u, pow_mul, sq_abs]
      rw [← h2k_eq]
      exact (pow_le_pow_left₀ (abs_nonneg _) hZu _).trans hu_pow
    calc ∑ j ∈ Finset.Icc 2 K,
            (1 / (q : ℝ)) * ∑ r : ZMod q, (Nat.choose K j : ℝ) * Z ^ (K - j) * (Δ r) ^ j
        ≤ ∑ j ∈ Finset.Icc 2 K,
            (Nat.choose K j : ℝ) *
              (V ^ k + (countSub S A b - (A.card : ℝ) * densQ S) ^ (2 * k)) *
              ((L : ℝ) / q) := by
          apply Finset.sum_le_sum
          intro j hj
          have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
          have hΔj : ∀ r : ZMod q, |(Δ r) ^ j| ≤ (Δ r) ^ 2 := by
            intro r
            rw [abs_pow]
            have hsub : j = 2 + (j - 2) := by omega
            rw [hsub, pow_add]
            have hpow1 : |Δ r| ^ (j - 2) ≤ 1 := pow_le_one₀ (abs_nonneg _) (hΔ_abs_le r)
            rw [sq_abs]
            exact mul_le_of_le_one_right (sq_nonneg _) hpow1
          calc (1 / (q : ℝ)) * ∑ r : ZMod q,
                  (Nat.choose K j : ℝ) * Z ^ (K - j) * (Δ r) ^ j
              ≤ (1 / (q : ℝ)) * ∑ r : ZMod q,
                  (Nat.choose K j : ℝ) * |Z| ^ (K - j) * (Δ r) ^ 2 := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                apply Finset.sum_le_sum; intro r _
                calc (Nat.choose K j : ℝ) * Z ^ (K - j) * (Δ r) ^ j
                    ≤ |(Nat.choose K j : ℝ) * Z ^ (K - j) * (Δ r) ^ j| := le_abs_self _
                  _ = (Nat.choose K j : ℝ) * |Z| ^ (K - j) * |(Δ r) ^ j| := by
                      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_pow]
                  _ ≤ (Nat.choose K j : ℝ) * |Z| ^ (K - j) * (Δ r) ^ 2 := by
                      gcongr; exact hΔj r
            _ = (Nat.choose K j : ℝ) * |Z| ^ (K - j) *
                  ((1 / (q : ℝ)) * ∑ r : ZMod q, (Δ r) ^ 2) := by
                rw [← Finset.mul_sum]; ring
            _ ≤ (Nat.choose K j : ℝ) *
                  (V ^ k + (countSub S A b - (A.card : ℝ) * densQ S) ^ (2 * k)) *
                  ((L : ℝ) / q) := by
                have hpos1 : 0 ≤ (1 / (q : ℝ)) * ∑ r : ZMod q, (Δ r) ^ 2 := by
                  apply mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
                have hpos2 : 0 ≤ V ^ k + (countSub S A b - (A.card : ℝ) * densQ S) ^ (2 * k) := by
                  have : 0 ≤ (countSub S A b - (A.card : ℝ) * densQ S) ^ (2 * k) :=
                    Even.pow_nonneg ⟨k, by omega⟩ _
                  positivity
                exact mul_le_mul
                  (mul_le_mul_of_nonneg_left (hZ_pow j hj) (Nat.cast_nonneg _))
                  hΔ_sq_avg hpos1 (mul_nonneg (Nat.cast_nonneg _) hpos2)
      _ = (∑ j ∈ Finset.Icc 2 K, (Nat.choose K j : ℝ)) *
            (V ^ k + (countSub S A b - (A.card : ℝ) * densQ S) ^ (2 * k)) *
            ((L : ℝ) / q) := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
      _ ≤ (2 : ℝ) ^ K *
            (V ^ k + (countSub S A b - (A.card : ℝ) * densQ S) ^ (2 * k)) *
            ((L : ℝ) / q) := by
          have hch : ∑ j ∈ Finset.Icc 2 K, (Nat.choose K j : ℝ) ≤ (2 : ℝ) ^ K := by
            calc ∑ j ∈ Finset.Icc 2 K, (Nat.choose K j : ℝ)
                ≤ ∑ j ∈ Finset.range (K + 1), (Nat.choose K j : ℝ) := by
                  apply Finset.sum_le_sum_of_subset_of_nonneg
                  · intro j hj; simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢; omega
                  · intro _ _ _; positivity
              _ = (2 : ℝ) ^ K := by
                  rw [← Nat.cast_sum, Nat.sum_range_choose]; norm_cast
          have hpos2 : 0 ≤ V ^ k + (countSub S A b - (A.card : ℝ) * densQ S) ^ (2 * k) := by
            have : 0 ≤ (countSub S A b - (A.card : ℝ) * densQ S) ^ (2 * k) :=
              Even.pow_nonneg ⟨k, by omega⟩ _
            positivity
          gcongr
      _ = ((2 : ℝ) ^ K * ((L : ℝ) / q)) *
            (V ^ k + (countSub S A b - (A.card : ℝ) * densQ S) ^ (2 * k)) := by ring
  rw [mul_add, mul_add, h1, h2, mul_zero, add_zero]
  linarith

lemma large_primes_sub_moment (k : ℕ) :
    ∀ (L : ℕ) (A : Finset ℕ), A ⊆ Finset.Icc 1 L →
    ∀ (Q : Finset ℕ), (∀ q ∈ Q, q.Prime ∧ L < q) →
    ∀ (V : ℝ), 1 + (L : ℝ) * ∑ q ∈ Q, (1 : ℝ) / q ≤ V →
      (1 / (prodQ Q : ℝ)) *
        ∑ b ∈ Finset.range (prodQ Q),
          (countSub Q A (b : ZMod (prodQ Q)) - (A.card : ℝ) * densQ Q) ^ (2 * k) ≤
        largeMartConst k * V ^ k := by
  induction k with
  | zero =>
    intro L A _ Q hQ V _
    have hP0 : (prodQ Q : ℝ) ≠ 0 := by exact_mod_cast prodQ_ne_zero fun q hq => (hQ q hq).1
    simp [largeMartConst, hP0]
  | succ k ih_k =>
    intro L A hA Q hQ V hV
    have hV1 : 1 ≤ V := by
      have : 0 ≤ (L : ℝ) * ∑ q ∈ Q, (1 : ℝ) / q := by
        apply mul_nonneg (Nat.cast_nonneg _)
        apply Finset.sum_nonneg; intro q _; positivity
      linarith
    have hmain : ∀ S : Finset ℕ, S ⊆ Q →
        (1 / (prodQ S : ℝ)) *
          ∑ b ∈ Finset.range (prodQ S),
            (countSub S A (b : ZMod (prodQ S)) - (A.card : ℝ) * densQ S) ^ (2 * (k + 1)) ≤
          largeMartConst (k + 1) * V ^ k * ((L : ℝ) * ∑ q ∈ S, (1 : ℝ) / q) := by
      intro S
      induction S using Finset.induction_on with
      | empty =>
        intro _
        have hsum0 : ∑ b ∈ Finset.range (prodQ ∅),
            (countSub ∅ A (b : ZMod (prodQ ∅)) - (A.card : ℝ) * densQ ∅) ^ (2 * (k + 1)) = 0 := by
          apply Finset.sum_eq_zero; intro b _
          have hcnt : countSub ∅ A (b : ZMod (prodQ ∅)) = (A.card : ℝ) := by
            unfold countSub
            have h1 : ∀ i ∈ A, IsUnit ((b : ZMod (prodQ ∅)) + (i : ZMod (prodQ ∅))) := fun i _ => by
              change IsUnit ((b : ZMod 1) + (i : ZMod 1))
              rw [Subsingleton.elim ((b : ZMod 1) + (i : ZMod 1)) 1]
              exact isUnit_one
            rw [Finset.sum_congr rfl (fun i hi => if_pos (h1 i hi)), Finset.sum_const, nsmul_eq_mul, mul_one]
          rw [hcnt, densQ_empty, mul_one, sub_self, zero_pow (by omega)]
        rw [hsum0, mul_zero]
        simp
      | @insert q S hqnot ihS =>
        intro hSQ
        have hQ_S : ∀ p ∈ S, p.Prime ∧ L < p := fun p hp => hQ p (hSQ (Finset.mem_insert_of_mem hp))
        have hS_prime : ∀ p ∈ S, p.Prime := fun p hp => (hQ_S p hp).1
        have hq_pair := hQ q (hSQ (Finset.mem_insert_self q S))
        have hq_prime : q.Prime := hq_pair.1
        have hq_gt : L < q := hq_pair.2
        have hS_sub : S ⊆ Q := (Finset.subset_insert q S).trans hSQ
        have hihS := ihS hS_sub
        have : NeZero q := ⟨hq_prime.ne_zero⟩
        have : NeZero (prodQ S) := ⟨prodQ_ne_zero hS_prime⟩
        have : NeZero (prodQ (insert q S)) := ⟨prodQ_ne_zero (fun p hp => (hQ p (hSQ hp)).1)⟩
        rw [sum_range_zmod (fun b : ZMod (prodQ S) =>
          (countSub S A b - (A.card : ℝ) * densQ S) ^ (2 * (k + 1)))] at hihS
        rw [sum_range_zmod (fun b : ZMod (prodQ (insert q S)) =>
          (countSub (insert q S) A b - (A.card : ℝ) * densQ (insert q S)) ^ (2 * (k + 1)))]
        rw [avg_zmod_insert hq_prime hS_prime hqnot]
        set K := 2 * (k + 1)
        have hP_pos : (0 : ℝ) < prodQ S := by exact_mod_cast prodQ_pos hS_prime
        have hV_S : 1 + (L : ℝ) * ∑ p ∈ S, (1 : ℝ) / p ≤ V := by
          have hsub_sum : ∑ p ∈ S, (1 : ℝ) / p ≤ ∑ p ∈ Q, (1 : ℝ) / p :=
            Finset.sum_le_sum_of_subset_of_nonneg hS_sub (fun _ _ _ => by positivity)
          linarith [mul_le_mul_of_nonneg_left hsub_sum (Nat.cast_nonneg L)]
        have hih_k_S := ih_k L A hA S hQ_S V hV_S
        rw [sum_range_zmod (fun b : ZMod (prodQ S) =>
          (countSub S A b - (A.card : ℝ) * densQ S) ^ (2 * k))] at hih_k_S
        calc (1 / (prodQ S : ℝ)) * ∑ b : ZMod (prodQ S),
                (1 / (q : ℝ)) * ∑ r : ZMod q,
                  (countSub (insert q S) A ((crtInsert hq_prime hS_prime hqnot).symm (r, b)) -
                    (A.card : ℝ) * densQ (insert q S)) ^ K
            ≤ (1 / (prodQ S : ℝ)) * ∑ b : ZMod (prodQ S),
                ((countSub S A b - (A.card : ℝ) * densQ S) ^ K +
                ((2 : ℝ) ^ K * ((L : ℝ) / q)) *
                  (V ^ k + (countSub S A b - (A.card : ℝ) * densQ S) ^ (2 * k))) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact Finset.sum_le_sum fun b _ =>
                large_primes_inner_step k L q A S hA hS_prime hq_prime hq_gt hqnot V hV1 b
          _ = (1 / (prodQ S : ℝ)) * ∑ b : ZMod (prodQ S),
                (countSub S A b - (A.card : ℝ) * densQ S) ^ K +
              ((2 : ℝ) ^ K * ((L : ℝ) / q)) *
                (V ^ k + (1 / (prodQ S : ℝ)) * ∑ b : ZMod (prodQ S),
                  (countSub S A b - (A.card : ℝ) * densQ S) ^ (2 * k)) := by
              rw [Finset.sum_add_distrib, mul_add]
              congr 1
              rw [← Finset.mul_sum, Finset.sum_add_distrib]
              simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
              rw [mul_add, mul_add]
              have hcancel : (1 / (prodQ S : ℝ)) * (((2 : ℝ) ^ K * ((L : ℝ) / q)) *
                  ((prodQ S : ℝ) * V ^ k)) = ((2 : ℝ) ^ K * ((L : ℝ) / q)) * V ^ k := by
                field_simp [hP_pos.ne']
              rw [hcancel]
              ring
          _ ≤ largeMartConst (k + 1) * V ^ k * ((L : ℝ) * ∑ p ∈ S, (1 : ℝ) / p) +
              ((2 : ℝ) ^ K * ((L : ℝ) / q)) * (V ^ k + largeMartConst k * V ^ k) := by
              gcongr
          _ = largeMartConst (k + 1) * V ^ k * ((L : ℝ) * ∑ p ∈ insert q S, (1 : ℝ) / p) := by
              rw [Finset.sum_insert hqnot]
              simp only [largeMartConst, K]
              ring
    have hfull := hmain Q (Finset.Subset.refl Q)
    have hmul_le : (L : ℝ) * ∑ q ∈ Q, (1 : ℝ) / q ≤ V := by linarith
    calc _ ≤ largeMartConst (k + 1) * V ^ k * ((L : ℝ) * ∑ q ∈ Q, (1 : ℝ) / q) := hfull
      _ ≤ largeMartConst (k + 1) * V ^ k * V :=
          mul_le_mul_of_nonneg_left hmul_le
            (mul_nonneg (largeMartConst_pos (k + 1)).le (pow_nonneg (by linarith) _))
      _ = largeMartConst (k + 1) * V ^ (k + 1) := by rw [pow_succ]; ring

lemma centMom_split_large (k : ℕ) (hk : 1 ≤ k) (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime) (L : ℕ) :
    centMom (2 * k) Q L ≤
      (2 : ℝ) ^ (2 * k) * largeMartConst k *
        (1 + (L : ℝ) * ∑ q ∈ Q.filter (fun q => L < q), (1 : ℝ) / q) ^ k +
      (2 : ℝ) ^ (2 * k) * centMom (2 * k) (Q.filter (fun q => q ≤ L)) L := by
  set Q1 := Q.filter (fun q => q ≤ L)
  set Q2 := Q.filter (fun q => L < q)
  have hQ1 : ∀ q ∈ Q1, q.Prime := fun q hq => hQ q (Finset.mem_filter.mp hq).1
  have hQ2 : ∀ q ∈ Q2, q.Prime := fun q hq => hQ q (Finset.mem_filter.mp hq).1
  have hdisj : Disjoint Q1 Q2 := by
    rw [Finset.disjoint_left]; intro q h1 h2
    have := (Finset.mem_filter.mp h1).2
    have := (Finset.mem_filter.mp h2).2
    omega
  have hunion : Q = Q1 ∪ Q2 := by
    ext q; simp only [Q1, Q2, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hq
      by_cases h : q ≤ L
      · exact Or.inl ⟨hq, h⟩
      · exact Or.inr ⟨hq, by omega⟩
    · rintro (⟨hq, _⟩ | ⟨hq, _⟩) <;> exact hq
  set K := 2 * k
  have hK_even : Even K := ⟨k, by dsimp only [K]; omega⟩
  have hK1 : 1 ≤ K := by omega
  have : NeZero (prodQ Q1) := ⟨prodQ_ne_zero hQ1⟩
  have : NeZero (prodQ Q2) := ⟨prodQ_ne_zero hQ2⟩
  have : NeZero (prodQ (Q1 ∪ Q2)) := ⟨prodQ_ne_zero (hunion ▸ hQ)⟩
  let e := crtUnion hQ1 hQ2 hdisj
  have havg_eq : centMom K Q L =
      (1 / (prodQ Q1 : ℝ)) * ∑ b1 : ZMod (prodQ Q1),
        (1 / (prodQ Q2 : ℝ)) * ∑ b2 : ZMod (prodQ Q2),
          (countQ (Q1 ∪ Q2) L (e.symm (b1, b2)) - (L : ℝ) * (densQ Q1 * densQ Q2)) ^ K := by
    have h1 : centMom K Q L = centMom K (Q1 ∪ Q2) L := by rw [← hunion]
    rw [h1, centMom_eq_sum_zmod, densQ_union hdisj, avg_zmod_union hQ1 hQ2 hdisj]
  rw [havg_eq]
  have hinner : ∀ b1 : ZMod (prodQ Q1),
      (1 / (prodQ Q2 : ℝ)) * ∑ b2 : ZMod (prodQ Q2),
        (countQ (Q1 ∪ Q2) L (e.symm (b1, b2)) - (L : ℝ) * (densQ Q1 * densQ Q2)) ^ K ≤
      (2 : ℝ) ^ K * largeMartConst k *
        (1 + (L : ℝ) * ∑ q ∈ Q2, (1 : ℝ) / q) ^ k +
      (2 : ℝ) ^ K * (countQ Q1 L b1 - (L : ℝ) * densQ Q1) ^ K := by
    intro b1
    set A := (Finset.Icc 1 L).filter (fun i : ℕ => IsUnit (b1 + (i : ZMod (prodQ Q1))))
    have hA_sub : A ⊆ Finset.Icc 1 L := Finset.filter_subset _ _
    have hA_card : (A.card : ℝ) = countQ Q1 L b1 := by
      have h1 : (A.card : ℝ) = ∑ _i ∈ A, (1 : ℝ) := by simp
      have h2 : ∑ _i ∈ A, (1 : ℝ) =
          ∑ i ∈ Finset.Icc 1 L, if IsUnit (b1 + (i : ZMod (prodQ Q1))) then (1 : ℝ) else 0 :=
        Finset.sum_filter (s := Finset.Icc 1 L)
          (p := fun i : ℕ => IsUnit (b1 + (i : ZMod (prodQ Q1)))) (f := fun _ => (1 : ℝ))
      rw [h1, h2]
      unfold countQ countSub
      apply Finset.sum_congr rfl; intro i _
      by_cases h : IsUnit (b1 + (i : ZMod (prodQ Q1))) <;> simp [h]
    have hcnt_eq : ∀ b2 : ZMod (prodQ Q2),
        countQ (Q1 ∪ Q2) L (e.symm (b1, b2)) = countSub Q2 A b2 := by
      intro b2
      unfold countQ countSub
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      have hu : IsUnit (e.symm (b1, b2) + (i : ZMod (prodQ (Q1 ∪ Q2)))) ↔
          IsUnit (b1 + (i : ZMod (prodQ Q1))) ∧ IsUnit (b2 + (i : ZMod (prodQ Q2))) := by
        rw [isUnit_crt_iff e]
        simp [map_add, map_natCast, e.apply_symm_apply]
      simp only [hu]
      by_cases h1 : IsUnit (b1 + (i : ZMod (prodQ Q1))) <;>
        by_cases h2 : IsUnit (b2 + (i : ZMod (prodQ Q2))) <;> simp [h1, h2]
    have hpt : ∀ b2 : ZMod (prodQ Q2),
        (countQ (Q1 ∪ Q2) L (e.symm (b1, b2)) - (L : ℝ) * (densQ Q1 * densQ Q2)) ^ K ≤
        (2 : ℝ) ^ K * (countSub Q2 A b2 - (A.card : ℝ) * densQ Q2) ^ K +
        (2 : ℝ) ^ K * (countQ Q1 L b1 - (L : ℝ) * densQ Q1) ^ K := by
      intro b2
      rw [hcnt_eq b2]
      have hdecomp : countSub Q2 A b2 - (L : ℝ) * (densQ Q1 * densQ Q2) =
          (countSub Q2 A b2 - (A.card : ℝ) * densQ Q2) +
          densQ Q2 * (countQ Q1 L b1 - (L : ℝ) * densQ Q1) := by
        rw [hA_card]; ring
      rw [hdecomp]
      have hpow := abs_two_add_pow_le (countSub Q2 A b2 - (A.card : ℝ) * densQ Q2)
        (densQ Q2 * (countQ Q1 L b1 - (L : ℝ) * densQ Q1)) K hK1
      have hev : ∀ x : ℝ, |x| ^ K = x ^ K := fun x => by
        simp only [K, pow_mul, sq_abs]
      rw [hev, hev, hev] at hpow
      have hdens2 : (densQ Q2 * (countQ Q1 L b1 - (L : ℝ) * densQ Q1)) ^ K ≤
          (countQ Q1 L b1 - (L : ℝ) * densQ Q1) ^ K := by
        rw [mul_pow]
        exact mul_le_of_le_one_left (hK_even.pow_nonneg _)
          (pow_le_one₀ (densQ_pos hQ2).le (densQ_le_one hQ2))
      nlinarith [pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) K]
    have hP2_pos : (0 : ℝ) < prodQ Q2 := by exact_mod_cast prodQ_pos hQ2
    have hmart := large_primes_sub_moment k L A hA_sub Q2
      (fun q hq => ⟨hQ2 q hq, (Finset.mem_filter.mp hq).2⟩)
      (1 + (L : ℝ) * ∑ q ∈ Q2, (1 : ℝ) / q) le_rfl
    rw [sum_range_zmod (fun b : ZMod (prodQ Q2) =>
      (countSub Q2 A b - (A.card : ℝ) * densQ Q2) ^ (2 * k))] at hmart
    calc (1 / (prodQ Q2 : ℝ)) * ∑ b2 : ZMod (prodQ Q2),
            (countQ (Q1 ∪ Q2) L (e.symm (b1, b2)) - (L : ℝ) * (densQ Q1 * densQ Q2)) ^ K
        ≤ (1 / (prodQ Q2 : ℝ)) * ∑ b2 : ZMod (prodQ Q2),
            ((2 : ℝ) ^ K * (countSub Q2 A b2 - (A.card : ℝ) * densQ Q2) ^ K +
            (2 : ℝ) ^ K * (countQ Q1 L b1 - (L : ℝ) * densQ Q1) ^ K) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum fun b2 _ => hpt b2
      _ = (2 : ℝ) ^ K * ((1 / (prodQ Q2 : ℝ)) * ∑ b2 : ZMod (prodQ Q2),
            (countSub Q2 A b2 - (A.card : ℝ) * densQ Q2) ^ K) +
          (2 : ℝ) ^ K * (countQ Q1 L b1 - (L : ℝ) * densQ Q1) ^ K := by
          rw [Finset.sum_add_distrib, mul_add]
          congr 1
          · rw [← Finset.mul_sum]; ring
          · simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
            field_simp [hP2_pos.ne']
      _ ≤ (2 : ℝ) ^ K * (largeMartConst k * (1 + (L : ℝ) * ∑ q ∈ Q2, (1 : ℝ) / q) ^ k) +
          (2 : ℝ) ^ K * (countQ Q1 L b1 - (L : ℝ) * densQ Q1) ^ K := by
          gcongr
      _ = _ := by ring
  have hP1_pos : (0 : ℝ) < prodQ Q1 := by exact_mod_cast prodQ_pos hQ1
  calc _ ≤ (1 / (prodQ Q1 : ℝ)) * ∑ b1 : ZMod (prodQ Q1),
            ((2 : ℝ) ^ K * largeMartConst k * (1 + (L : ℝ) * ∑ q ∈ Q2, (1 : ℝ) / q) ^ k +
            (2 : ℝ) ^ K * (countQ Q1 L b1 - (L : ℝ) * densQ Q1) ^ K) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum fun b1 _ => hinner b1
    _ = (2 : ℝ) ^ K * largeMartConst k * (1 + (L : ℝ) * ∑ q ∈ Q2, (1 : ℝ) / q) ^ k +
        (2 : ℝ) ^ K * centMom K Q1 L := by
        rw [centMom_eq_sum_zmod, Finset.sum_add_distrib, mul_add]
        congr 1
        · simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
          field_simp [hP1_pos.ne']
        · rw [← Finset.mul_sum]; ring

end LargePrimesMartingale

section ProgressionInvariance

lemma filter_residue_progression (q L : ℕ) (hq : 0 < q) (r : ZMod q) :
    let S := (Finset.Icc 1 L).filter (fun i : ℕ => r + (i : ZMod q) = 0)
    ∃ a0 : ℕ, 1 ≤ a0 ∧ a0 ≤ q ∧
      S = (Finset.Icc 1 S.card).image (fun j : ℕ => a0 + (j - 1) * q) ∧
      |(L : ℝ) / q - (S.card : ℝ)| ≤ 1 ∧
      (q ≤ L → (S.card : ℝ) ≤ 2 * (L : ℝ) / q) ∧
      (3 ≤ q → q ≤ L → S.card < L) := by
  have : NeZero q := ⟨hq.ne'⟩
  set S := (Finset.Icc 1 L).filter (fun i : ℕ => r + (i : ZMod q) = 0)
  set a0 := q - r.val
  have hrlt : r.val < q := ZMod.val_lt r
  have ha0_1 : 1 ≤ a0 := by omega
  have ha0_q : a0 ≤ q := by omega
  have ha0_zero : r + (a0 : ZMod q) = 0 := by
    have hsum : r.val + a0 = q := by omega
    have hcast : ((r.val + a0 : ℕ) : ZMod q) = 0 := by rw [hsum]; simp
    simpa [Nat.cast_add, ZMod.natCast_zmod_val] using hcast
  have hmem_iff : ∀ i : ℕ, (1 ≤ i ∧ i ≤ L ∧ r + (i : ZMod q) = 0) ↔
      ∃ t : ℕ, i = a0 + t * q ∧ a0 + t * q ≤ L := by
    intro i
    constructor
    · rintro ⟨hi1, hiL, hri⟩
      have hdiff : ((r.val + i : ℕ) : ZMod q) = 0 := by
        simpa [Nat.cast_add, ZMod.natCast_zmod_val] using hri
      have hdvd : q ∣ (r.val + i) := (ZMod.natCast_eq_zero_iff _ q).mp hdiff
      rcases hdvd with ⟨m, hm⟩
      cases m with
      | zero => omega
      | succ m' =>
        have hqm : q * (m' + 1) = q + m' * q := by ring
        refine ⟨m', by omega, by omega⟩
    · rintro ⟨t, rfl, hle⟩
      refine ⟨by omega, hle, ?_⟩
      have : r + ((a0 + t * q : ℕ) : ZMod q) = r + (a0 : ZMod q) + (t : ZMod q) * (q : ZMod q) := by
        push_cast; ring
      rw [this, ha0_zero, ZMod.natCast_self, mul_zero, add_zero]
  set m := if L < a0 then 0 else (L - a0) / q + 1
  have hS_eq : S = (Finset.Icc 1 m).image (fun j : ℕ => a0 + (j - 1) * q) := by
    ext i
    simp only [S, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    rw [and_assoc, hmem_iff]
    constructor
    · rintro ⟨t, rfl, hle⟩
      have hLa : ¬ L < a0 := by omega
      refine ⟨t + 1, ⟨by omega, ?_⟩, by simp⟩
      simp only [m, if_neg hLa]
      have ht : t * q ≤ L - a0 := by omega
      have := (Nat.le_div_iff_mul_le hq).mpr ht
      omega
    · rintro ⟨j, ⟨hj1, hjm⟩, rfl⟩
      by_cases hLa : L < a0
      · simp [m, if_pos hLa] at hjm; omega
      · simp only [m, if_neg hLa] at hjm
        refine ⟨j - 1, rfl, ?_⟩
        have h1 : (j - 1) * q ≤ (L - a0) / q * q := Nat.mul_le_mul_right q (by omega)
        have h2 : (L - a0) / q * q ≤ L - a0 := Nat.div_mul_le_self (L - a0) q
        omega
  have hinj : Set.InjOn (fun j : ℕ => a0 + (j - 1) * q) (↑(Finset.Icc 1 m) : Set ℕ) := by
    intro j1 hj1 j2 hj2 heq
    simp only [Finset.mem_coe, Finset.mem_Icc] at hj1 hj2
    dsimp only at heq
    have hmul : (j1 - 1) * q = (j2 - 1) * q := by omega
    have := Nat.eq_of_mul_eq_mul_right hq hmul
    omega
  have hcard : S.card = m := by
    rw [hS_eq, Finset.card_image_of_injOn hinj, Nat.card_Icc]
    omega
  refine ⟨a0, ha0_1, ha0_q, hcard ▸ hS_eq, ?_, ?_, ?_⟩
  · rw [hcard]
    have hq_pos : (0 : ℝ) < q := by exact_mod_cast hq
    by_cases hLa : L < a0
    · simp only [m, if_pos hLa, Nat.cast_zero, sub_zero]
      rw [abs_of_nonneg (by positivity), div_le_one hq_pos]
      exact_mod_cast (show L ≤ q by omega)
    · simp only [m, if_neg hLa]
      set t := (L - a0) / q
      have hdiv_le : t * q ≤ L - a0 := Nat.div_mul_le_self (L - a0) q
      have hdiv_lt : L - a0 < (t + 1) * q := by
        have h1 : L - a0 < t * q + q := Nat.lt_div_mul_add (a := L - a0) hq
        have h2 : (t + 1) * q = t * q + q := by ring
        omega
      have hlow : (t : ℝ) * q ≤ (L : ℝ) := by exact_mod_cast (show t * q ≤ L by omega)
      have hhigh : (L : ℝ) ≤ ((t + 2 : ℕ) : ℝ) * q := by
        have h2 : (t + 2) * q = (t + 1) * q + q := by ring
        have : L ≤ (t + 2) * q := by omega
        exact_mod_cast this
      rw [abs_le]
      push_cast
      have h1 : (t : ℝ) ≤ (L : ℝ) / q := (le_div_iff₀ hq_pos).mpr hlow
      have h2 : (L : ℝ) / q ≤ (t : ℝ) + 2 := (div_le_iff₀ hq_pos).mpr (by push_cast at hhigh; linarith)
      constructor <;> linarith
  · intro hqL
    have hq_pos : (0 : ℝ) < q := by exact_mod_cast hq
    rw [hcard]
    by_cases hLa : L < a0
    · simp only [m, if_pos hLa, Nat.cast_zero]; positivity
    · simp only [m, if_neg hLa]
      have h1 : ((L - a0) / q + 1) * q ≤ 2 * L := by
        have hle := Nat.div_mul_le_self (L - a0) q
        have hmul : ((L - a0) / q + 1) * q = (L - a0) / q * q + q := by ring
        omega
      rw [le_div_iff₀ hq_pos]
      exact_mod_cast h1
  · intro hq3 hqL
    rw [hcard]
    by_cases hLa : L < a0
    · simp only [m, if_pos hLa]; omega
    · simp only [m, if_neg hLa]
      have h1 : (L - a0) / q * q ≤ L - a0 := Nat.div_mul_le_self (L - a0) q
      have h2 : (L - a0) / q * 3 ≤ (L - a0) / q * q := Nat.mul_le_mul_left _ hq3
      omega

lemma avg_countSub_progression_eq_centMom (K q L : ℕ) (Q : Finset ℕ) [NeZero (prodQ Q)]
    (hq : q.Prime) (hQ : ∀ p ∈ Q, p.Prime) (hqnot : q ∉ Q) (r : ZMod q) :
    let S := (Finset.Icc 1 L).filter (fun i : ℕ => r + (i : ZMod q) = 0)
    (1 / (prodQ Q : ℝ)) *
      ∑ b : ZMod (prodQ Q), (countSub Q S b - (S.card : ℝ) * densQ Q) ^ K =
      centMom K Q S.card := by
  have hcop : q.Coprime (prodQ Q) := by
    apply Nat.coprime_prod_right_iff.mpr; intro p hp
    exact (Nat.coprime_primes hq (hQ p hp)).mpr (fun heq => hqnot (heq ▸ hp))
  obtain ⟨a0, ha0_1, _, hS_eq, _, _, _⟩ := filter_residue_progression q L hq.pos r
  set S := (Finset.Icc 1 L).filter (fun i : ℕ => r + (i : ZMod q) = 0)
  have hu : IsUnit (q : ZMod (prodQ Q)) := (ZMod.isUnit_iff_coprime q (prodQ Q)).mpr hcop
  rcases hu with ⟨u, hu_eq⟩
  let shiftEquiv : ZMod (prodQ Q) ≃ ZMod (prodQ Q) := {
    toFun := fun b => (u⁻¹ : (ZMod (prodQ Q))ˣ) * (b + (a0 : ZMod (prodQ Q)) - (q : ZMod (prodQ Q)))
    invFun := fun c => (u : ZMod (prodQ Q)) * c + (q : ZMod (prodQ Q)) - (a0 : ZMod (prodQ Q))
    left_inv := fun b => by
      dsimp only
      rw [← mul_assoc, Units.mul_inv, one_mul]
      ring
    right_inv := fun c => by
      dsimp only
      have : (u : ZMod (prodQ Q)) * c + (q : ZMod (prodQ Q)) - (a0 : ZMod (prodQ Q)) +
          (a0 : ZMod (prodQ Q)) - (q : ZMod (prodQ Q)) = (u : ZMod (prodQ Q)) * c := by ring
      rw [this, ← mul_assoc, Units.inv_mul, one_mul]
  }
  have hcnt : ∀ b : ZMod (prodQ Q), countSub Q S b = countQ Q S.card (shiftEquiv b) := by
    intro b
    unfold countQ countSub
    nth_rw 1 [hS_eq]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have hcast_eq : b + ((a0 + (j - 1) * q : ℕ) : ZMod (prodQ Q)) =
          (u : ZMod (prodQ Q)) * (shiftEquiv b + (j : ZMod (prodQ Q))) := by
        simp only [shiftEquiv, Equiv.coe_fn_mk, mul_add]
        rw [← mul_assoc, Units.mul_inv, one_mul, hu_eq]
        have hcast : (((j - 1 : ℕ) : ZMod (prodQ Q)) + 1) = (j : ZMod (prodQ Q)) := by
          conv_rhs => rw [← Nat.sub_add_cancel hj1]
          push_cast; rfl
        push_cast
        rw [← hcast]
        ring
      have hu_mul : IsUnit ((u : ZMod (prodQ Q)) * (shiftEquiv b + (j : ZMod (prodQ Q)))) ↔
          IsUnit (shiftEquiv b + (j : ZMod (prodQ Q))) :=
        ⟨fun h => by simpa [← mul_assoc] using u⁻¹.isUnit.mul h, fun h => u.isUnit.mul h⟩
      simp only [hcast_eq, hu_mul]
      by_cases h : IsUnit (shiftEquiv b + (j : ZMod (prodQ Q))) <;> simp [h]
    · intro j1 hj1 j2 hj2 heq
      simp only [Finset.mem_coe, Finset.mem_Icc] at hj1 hj2
      dsimp only at heq
      have hmul : (j1 - 1) * q = (j2 - 1) * q := by omega
      have := Nat.eq_of_mul_eq_mul_right hq.pos hmul
      omega
  dsimp only
  rw [centMom_eq_sum_zmod]
  congr 1
  simp_rw [hcnt]
  exact Fintype.sum_equiv shiftEquiv _ _ (fun _ => rfl)

end ProgressionInvariance

section MediumAndFullMoment

lemma tail_rpow_sum_tendsto_zero {α : ℝ} (hα : 1 < α) :
    ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, 3 ≤ N ∧
      ∀ S : Finset ℕ, (∀ n ∈ S, N ≤ n) → ∑ n ∈ S, (1 : ℝ) / (n : ℝ) ^ α ≤ δ := by
  intro δ hδ
  have hsum : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ α) := by
    have h := Real.summable_nat_rpow_inv.mpr hα
    simpa [one_div] using h
  have htend := hsum.hasSum.tendsto_sum_nat
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N0, hN0⟩ := htend δ hδ
  refine ⟨max 3 N0, le_max_left 3 N0, fun S hS => ?_⟩
  set M := max (max 3 N0) (S.sup id + 1)
  have hsub : S ⊆ Finset.Ico (max 3 N0) M := by
    intro n hn
    simp only [Finset.mem_Ico]
    refine ⟨hS n hn, ?_⟩
    have hle : n ≤ S.sup id := Finset.le_sup (f := id) hn
    omega
  have hS_le : ∑ n ∈ S, (1 : ℝ) / (n : ℝ) ^ α ≤
      ∑ n ∈ Finset.Ico (max 3 N0) M, (1 : ℝ) / (n : ℝ) ^ α :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have hsplit : ∑ n ∈ Finset.range (max 3 N0), (1 : ℝ) / (n : ℝ) ^ α +
      ∑ n ∈ Finset.Ico (max 3 N0) M, (1 : ℝ) / (n : ℝ) ^ α =
      ∑ n ∈ Finset.range M, (1 : ℝ) / (n : ℝ) ^ α := by
    rw [← Finset.sum_union]
    · congr 1
      ext n; simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]; omega
    · rw [Finset.disjoint_left]; intro n h1 h2
      simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2; omega
  have hle_tsum : ∑ n ∈ Finset.range M, (1 : ℝ) / (n : ℝ) ^ α ≤
      ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ α :=
    hsum.sum_le_tsum (Finset.range M) (fun _ _ => by positivity)
  have hdist := hN0 (max 3 N0) (le_max_right 3 N0)
  rw [Real.dist_eq, abs_lt] at hdist
  linarith

-- Helper 1: Bound the K-th moment of the martingale difference Δ for one prime q ∈ [q0, L]
private lemma medium_step_delta_moment (k q0 L q : ℕ) (hk : 1 ≤ k) {ε C : ℝ} (hε : 0 < ε)
    (hC1 : 1 ≤ C) (hq0_3 : 3 ≤ q0) (hq_prime : q.Prime) (hq_ge : q0 ≤ q) (hq_leL : q ≤ L)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ q0 ≤ p ∧ p ≤ L) (hqnot : q ∉ S)
    (hS_bound_U : centMom (2 * k) S L ≤ C * (L : ℝ) ^ ((k : ℝ) + ε))
    (ihL : ∀ m < L, ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ q0 ≤ p ∧ p ≤ m) →
      centMom (2 * k) Q m ≤ C * ((max 1 m : ℕ) : ℝ) ^ ((k : ℝ) + ε)) :
    let hS_prime : ∀ p ∈ S, p.Prime := fun p hp => (hS p hp).1
    have : NeZero q := ⟨hq_prime.ne_zero⟩
    have : NeZero (prodQ S) := ⟨prodQ_ne_zero hS_prime⟩
    let e := crtInsert hq_prime hS_prime hqnot
    let Δfn : ZMod (prodQ S) × ZMod q → ℝ :=
      fun p => countQ (insert q S) L (e.symm (p.2, p.1)) - (1 - (1 : ℝ) / q) * countQ S L p.1
    (1 / (Fintype.card (ZMod (prodQ S) × ZMod q) : ℝ)) *
      ∑ p : ZMod (prodQ S) × ZMod q, |Δfn p| ^ (2 * k) ≤
      (3 : ℝ) ^ (2 * k) * (C * (L : ℝ) ^ ((k : ℝ) + ε)) / (q : ℝ) ^ (2 * k) +
      (3 : ℝ) ^ (2 * k) * (2 : ℝ) ^ (2 * k) * C * (2 * (L : ℝ) / q) ^ ((k : ℝ) + ε) +
      ((3 : ℝ) ^ (2 * k) * (2 : ℝ) ^ (2 * k) * largeMartConst k * (2 : ℝ) ^ k) *
        ((L : ℝ) / q) ^ k * (2 + Real.log (L : ℝ)) ^ k +
      (3 : ℝ) ^ (2 * k) := by
  have hS_prime : ∀ p ∈ S, p.Prime := fun p hp => (hS p hp).1
  have : NeZero q := ⟨hq_prime.ne_zero⟩
  have : NeZero (prodQ S) := ⟨prodQ_ne_zero hS_prime⟩
  dsimp only
  set K := 2 * k
  set U : ℝ := C * (L : ℝ) ^ ((k : ℝ) + ε)
  set Λ : ℝ := 2 + Real.log (L : ℝ)
  set c3 : ℝ := (3 : ℝ) ^ K * (2 : ℝ) ^ K * largeMartConst k * (2 : ℝ) ^ k
  set A1 : ℝ := (3 : ℝ) ^ K * U / (q : ℝ) ^ K
  set A2 : ℝ := (3 : ℝ) ^ K * (2 : ℝ) ^ K * C * (2 * (L : ℝ) / q) ^ ((k : ℝ) + ε)
  set A3 : ℝ := c3 * ((L : ℝ) / q) ^ k * Λ ^ k
  set A4 : ℝ := (3 : ℝ) ^ K
  have hK1 : 1 ≤ K := by omega
  have hL1 : 1 ≤ L := by omega
  have hL_ge1 : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hmaxL : max 1 L = L := by omega
  have hq_ge3 : 3 ≤ q := le_trans hq0_3 hq_ge
  have hq_pos : (0 : ℝ) < q := by exact_mod_cast hq_prime.pos
  let e := crtInsert hq_prime hS_prime hqnot
  let Δfn : ZMod (prodQ S) × ZMod q → ℝ :=
    fun p => countQ (insert q S) L (e.symm (p.2, p.1)) - (1 - (1 : ℝ) / q) * countQ S L p.1
  have hcard_eq : (Fintype.card (ZMod (prodQ S) × ZMod q) : ℝ) = (prodQ S : ℝ) * (q : ℝ) := by
    simp [Fintype.card_prod, ZMod.card]
  rw [hcard_eq, Fintype.sum_prod_type_right]
  have hfor_r : ∀ r : ZMod q,
      (1 / (prodQ S : ℝ)) * ∑ b : ZMod (prodQ S), |Δfn (b, r)| ^ K ≤ A1 + A2 + A3 + A4 := by
    intro r
    set Sr := (Finset.Icc 1 L).filter (fun i : ℕ => r + (i : ZMod q) = 0)
    obtain ⟨_, _, _, _, hLr_diff, hLr_2L, hLr_lt⟩ := filter_residue_progression q L hq_prime.pos r
    have hΔ_decomp : ∀ b : ZMod (prodQ S),
        Δfn (b, r) =
        (countQ S L b - (L : ℝ) * densQ S) / q +
        (-(countSub S Sr b - (Sr.card : ℝ) * densQ S)) +
        ((L : ℝ) / q - (Sr.card : ℝ)) * densQ S := by
      intro b
      simp only [Δfn, countQ, Sr, e]
      rw [countSub_crtInsert hq_prime hS_prime hqnot]
      ring
    have hpt_r : ∀ b : ZMod (prodQ S),
        |Δfn (b, r)| ^ K ≤
        (3 : ℝ) ^ K *
          ((countQ S L b - (L : ℝ) * densQ S) ^ K / (q : ℝ) ^ K +
          (countSub S Sr b - (Sr.card : ℝ) * densQ S) ^ K + 1) := by
      intro b
      rw [hΔ_decomp b]
      have h3 := abs_three_add_pow_le
        ((countQ S L b - (L : ℝ) * densQ S) / q)
        (-(countSub S Sr b - (Sr.card : ℝ) * densQ S))
        (((L : ℝ) / q - (Sr.card : ℝ)) * densQ S) K hK1
      have hev : ∀ x : ℝ, |x| ^ K = x ^ K := fun x => by simp only [K, pow_mul, sq_abs]
      rw [abs_div, abs_of_pos hq_pos, div_pow, hev, abs_neg, hev] at h3
      have h3rd : |((L : ℝ) / q - (Sr.card : ℝ)) * densQ S| ^ K ≤ 1 := by
        apply pow_le_one₀ (abs_nonneg _)
        rw [abs_mul, abs_of_pos (densQ_pos hS_prime)]
        exact mul_le_one₀ hLr_diff (densQ_pos hS_prime).le (densQ_le_one hS_prime)
      have h3pos : (0 : ℝ) ≤ 3 ^ K := by positivity
      calc |((countQ S L b - (L : ℝ) * densQ S) / q) +
            (-(countSub S Sr b - (Sr.card : ℝ) * densQ S)) +
            ((L : ℝ) / q - (Sr.card : ℝ)) * densQ S| ^ K
          ≤ 3 ^ K * ((countQ S L b - (L : ℝ) * densQ S) ^ K / (q : ℝ) ^ K +
              (countSub S Sr b - (Sr.card : ℝ) * densQ S) ^ K +
              |((L : ℝ) / q - (Sr.card : ℝ)) * densQ S| ^ K) := by
            simpa [hev] using h3
        _ ≤ 3 ^ K * ((countQ S L b - (L : ℝ) * densQ S) ^ K / (q : ℝ) ^ K +
              (countSub S Sr b - (Sr.card : ℝ) * densQ S) ^ K + 1) := by gcongr
    have hPS_pos : (0 : ℝ) < prodQ S := by exact_mod_cast prodQ_pos hS_prime
    have hprog_eq := avg_countSub_progression_eq_centMom K q L S hq_prime hS_prime hqnot r
    have hSr_mom : centMom K S Sr.card ≤
        (2 : ℝ) ^ K * largeMartConst k * (2 * (L : ℝ) / q * Λ) ^ k +
        (2 : ℝ) ^ K * C * (2 * (L : ℝ) / q) ^ ((k : ℝ) + ε) := by
      have hsp := centMom_split_large k hk S hS_prime Sr.card
      have hS_lo_bound : centMom K (S.filter (fun p => p ≤ Sr.card)) Sr.card ≤
          C * (2 * (L : ℝ) / q) ^ ((k : ℝ) + ε) := by
        by_cases hSr0 : Sr.card = 0
        · rw [hSr0]
          have h0 : centMom K (S.filter (fun p => p ≤ 0)) 0 = 0 := by
            unfold centMom countQ countSub; simp [zero_pow (by omega : K ≠ 0)]
          rw [h0]; positivity
        · have hSr_lt : Sr.card < L := hLr_lt hq_ge3 hq_leL
          have hih_Sr := ihL Sr.card hSr_lt (S.filter (fun p => p ≤ Sr.card))
            (fun p hp => by
              have h1 := (Finset.mem_filter.mp hp).1
              have h2 := (Finset.mem_filter.mp hp).2
              exact ⟨(hS p h1).1, (hS p h1).2.1, h2⟩)
          have hmaxSr : max 1 Sr.card = Sr.card := by omega
          rw [hmaxSr] at hih_Sr
          calc centMom K (S.filter (fun p => p ≤ Sr.card)) Sr.card
              ≤ C * (Sr.card : ℝ) ^ ((k : ℝ) + ε) := hih_Sr
            _ ≤ C * (2 * (L : ℝ) / q) ^ ((k : ℝ) + ε) :=
                mul_le_mul_of_nonneg_left
                  (Real.rpow_le_rpow (Nat.cast_nonneg _) (hLr_2L hq_leL) (by positivity))
                  (by linarith)
      have hS_hi_bound : 1 + (Sr.card : ℝ) *
          ∑ p ∈ S.filter (fun p => Sr.card < p), (1 : ℝ) / p ≤ 2 * (L : ℝ) / q * Λ := by
        have hsum_hi : ∑ p ∈ S.filter (fun p => Sr.card < p), (1 : ℝ) / p ≤ 1 + Real.log (L : ℝ) := by
          have hsub : S.filter (fun p => Sr.card < p) ⊆ Finset.Icc 1 L := fun p hp =>
            Finset.mem_Icc.mpr ⟨(hS p (Finset.mem_filter.mp hp).1).1.one_le,
              (hS p (Finset.mem_filter.mp hp).1).2.2⟩
          calc ∑ p ∈ S.filter (fun p => Sr.card < p), (1 : ℝ) / p
              ≤ ∑ n ∈ Finset.Icc 1 L, (1 : ℝ) / n :=
                Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
            _ ≤ 1 + Real.log (max 1 L : ℕ) := sum_one_div_Icc_le_one_add_log L
            _ = 1 + Real.log (L : ℝ) := by rw [hmaxL]
        have h1_le : (1 : ℝ) ≤ (L : ℝ) / q := (one_le_div hq_pos).mpr (by exact_mod_cast hq_leL)
        have h2_le : (2 : ℝ) ≤ 2 * (L : ℝ) / q := by rw [mul_div_assoc]; linarith
        have hSr_le := hLr_2L hq_leL
        have hmul1 : (Sr.card : ℝ) * ∑ p ∈ S.filter (fun p => Sr.card < p), (1 : ℝ) / p ≤
            (2 * (L : ℝ) / q) * (1 + Real.log (L : ℝ)) :=
          mul_le_mul hSr_le hsum_hi (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
        have hlogL : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg hL_ge1
        simp only [Λ]
        nlinarith
      have hsp1 : (1 + (Sr.card : ℝ) *
          ∑ p ∈ S.filter (fun p => Sr.card < p), (1 : ℝ) / p) ^ k ≤ (2 * (L : ℝ) / q * Λ) ^ k :=
        pow_le_pow_left₀
          (add_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _)
            (Finset.sum_nonneg fun _ _ => by positivity)))
          hS_hi_bound k
      have hsp2 := mul_le_mul_of_nonneg_left hsp1
        (show (0 : ℝ) ≤ (2 : ℝ) ^ K * largeMartConst k by have := largeMartConst_pos k; positivity)
      have hsp3 := mul_le_mul_of_nonneg_left hS_lo_bound (show (0 : ℝ) ≤ (2 : ℝ) ^ K by positivity)
      have hsp' : centMom K S Sr.card ≤
          (2 : ℝ) ^ K * largeMartConst k *
            (1 + (Sr.card : ℝ) * ∑ p ∈ S.filter (fun p => Sr.card < p), (1 : ℝ) / p) ^ k +
          (2 : ℝ) ^ K * centMom K (S.filter (fun p => p ≤ Sr.card)) Sr.card := hsp
      linarith
    have h3A3 : (3 : ℝ) ^ K * ((2 : ℝ) ^ K * largeMartConst k * (2 * (L : ℝ) / q * Λ) ^ k) = A3 := by
      simp only [A3, c3]
      rw [show 2 * (L : ℝ) / q * Λ = 2 * ((L : ℝ) / q) * Λ by ring, mul_pow, mul_pow]
      ring
    calc (1 / (prodQ S : ℝ)) * ∑ b : ZMod (prodQ S), |Δfn (b, r)| ^ K
        ≤ (1 / (prodQ S : ℝ)) * ∑ b : ZMod (prodQ S),
            (3 : ℝ) ^ K * ((countQ S L b - (L : ℝ) * densQ S) ^ K / (q : ℝ) ^ K +
              (countSub S Sr b - (Sr.card : ℝ) * densQ S) ^ K + 1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum fun b _ => hpt_r b
      _ = (3 : ℝ) ^ K * (centMom K S L / (q : ℝ) ^ K + centMom K S Sr.card + 1) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_div]
          simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
          have hsum1 : ∑ b : ZMod (prodQ S), (countQ S L b - (L : ℝ) * densQ S) ^ K =
              (prodQ S : ℝ) * centMom K S L := by
            have h := congrArg ((prodQ S : ℝ) * ·) (centMom_eq_sum_zmod K S L).symm
            rwa [← mul_assoc, mul_one_div_cancel hPS_pos.ne', one_mul] at h
          have hsum2 : ∑ b : ZMod (prodQ S), (countSub S Sr b - (Sr.card : ℝ) * densQ S) ^ K =
              (prodQ S : ℝ) * centMom K S Sr.card := by
            have h := congrArg ((prodQ S : ℝ) * ·) hprog_eq
            rwa [← mul_assoc, mul_one_div_cancel hPS_pos.ne', one_mul] at h
          rw [hsum1, hsum2]
          field_simp [hPS_pos.ne']
      _ ≤ (3 : ℝ) ^ K * (U / (q : ℝ) ^ K +
            ((2 : ℝ) ^ K * largeMartConst k * (2 * (L : ℝ) / q * Λ) ^ k +
              (2 : ℝ) ^ K * C * (2 * (L : ℝ) / q) ^ ((k : ℝ) + ε)) + 1) := by
          gcongr
      _ = A1 + A2 + A3 + A4 := by
          rw [← h3A3]; simp only [A1, A2, A4]; ring
  calc (1 / ((prodQ S : ℝ) * (q : ℝ))) *
        ∑ r : ZMod q, ∑ b : ZMod (prodQ S), |Δfn (b, r)| ^ K
      = (1 / (q : ℝ)) * ∑ r : ZMod q,
          ((1 / (prodQ S : ℝ)) * ∑ b : ZMod (prodQ S), |Δfn (b, r)| ^ K) := by
        rw [Finset.mul_sum, Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _; ring
    _ ≤ (1 / (q : ℝ)) * ∑ _r : ZMod q, (A1 + A2 + A3 + A4) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum fun r _ => hfor_r r
    _ = A1 + A2 + A3 + A4 := by
        simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
        field_simp [hq_pos.ne']

-- Helper 2: Bound each Holder term U^(1 - j/K) * (A1 + A2 + A3 + A4)^(j/K) for 2 ≤ j ≤ K
private lemma medium_holder_four_terms (k L q j : ℕ) (hk : 1 ≤ k) (hL1 : 1 ≤ L) (hq1 : 1 ≤ q)
    (hj2 : 2 ≤ j) (hjK : j ≤ 2 * k) {ε C : ℝ} (hε : 0 < ε) (hC1 : 1 ≤ C) :
    let K := 2 * k
    let U : ℝ := C * (L : ℝ) ^ ((k : ℝ) + ε)
    let Λ : ℝ := 2 + Real.log (L : ℝ)
    let c2 : ℝ := 3 * (2 : ℝ) ^ ((3 : ℝ) / 2 + ε / K)
    let c3 : ℝ := (3 : ℝ) ^ K * (2 : ℝ) ^ K * largeMartConst k * (2 : ℝ) ^ k
    let A1 : ℝ := (3 : ℝ) ^ K * U / (q : ℝ) ^ K
    let A2 : ℝ := (3 : ℝ) ^ K * (2 : ℝ) ^ K * C * (2 * (L : ℝ) / q) ^ ((k : ℝ) + ε)
    let A3 : ℝ := c3 * ((L : ℝ) / q) ^ k * Λ ^ k
    let A4 : ℝ := (3 : ℝ) ^ K
    U ^ (1 - (j : ℝ) / K) * (A1 + A2 + A3 + A4) ^ ((j : ℝ) / K) ≤
      (3 : ℝ) ^ K * U / (q : ℝ) ^ 2 +
      c2 ^ K * U / (q : ℝ) ^ ((1 : ℝ) + ε / k) +
      (max 1 c3) * C ^ (1 - (1 : ℝ) / k) * (L : ℝ) ^ ((k : ℝ) + ε - ε / k) * Λ ^ k / (q : ℝ) +
      (3 : ℝ) ^ K * C ^ (1 - (1 : ℝ) / k) * (L : ℝ) ^ ((k : ℝ) + ε - 1) := by
  dsimp only
  set K := 2 * k
  set U : ℝ := C * (L : ℝ) ^ ((k : ℝ) + ε)
  set Λ : ℝ := 2 + Real.log (L : ℝ)
  set c2 : ℝ := 3 * (2 : ℝ) ^ ((3 : ℝ) / 2 + ε / K)
  set c3 : ℝ := (3 : ℝ) ^ K * (2 : ℝ) ^ K * largeMartConst k * (2 : ℝ) ^ k
  set A1 : ℝ := (3 : ℝ) ^ K * U / (q : ℝ) ^ K
  set A2 : ℝ := (3 : ℝ) ^ K * (2 : ℝ) ^ K * C * (2 * (L : ℝ) / q) ^ ((k : ℝ) + ε)
  set A3 : ℝ := c3 * ((L : ℝ) / q) ^ k * Λ ^ k
  set A4 : ℝ := (3 : ℝ) ^ K
  have hK_pos : 0 < K := by omega
  have hK_real : (K : ℝ) = 2 * (k : ℝ) := by simp [K]
  have hL_pos : (0 : ℝ) < L := by exact_mod_cast hL1
  have hL_ge1 : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hq_pos : (0 : ℝ) < q := by exact_mod_cast hq1
  have hq_ge1 : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hU_pos : 0 < U := by positivity
  have hΛ1 : 1 ≤ Λ := by have := Real.log_nonneg hL_ge1; linarith
  have hc2_pos : 0 < c2 := by positivity
  have hc3_pos : 0 < c3 := by have := largeMartConst_pos k; positivity
  have ht0 : 0 < (j : ℝ) / K := div_pos (by exact_mod_cast (show 0 < j by omega)) (by exact_mod_cast hK_pos)
  have ht1 : (j : ℝ) / K ≤ 1 := (div_le_one (by exact_mod_cast hK_pos)).mpr (by exact_mod_cast hjK)
  have hj_ge2 : (2 : ℝ) ≤ j := by exact_mod_cast hj2
  have hjk_ge : (1 : ℝ) / k ≤ (j : ℝ) / K := by
    rw [hK_real, div_le_div_iff₀ (by exact_mod_cast hk) (by positivity)]
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hsubadd : (A1 + A2 + A3 + A4) ^ ((j : ℝ) / K) ≤
      A1 ^ ((j : ℝ) / K) + A2 ^ ((j : ℝ) / K) + A3 ^ ((j : ℝ) / K) + A4 ^ ((j : ℝ) / K) := by
    have hA1_nn : 0 ≤ A1 := by simp only [A1]; positivity
    have hA2_nn : 0 ≤ A2 := by simp only [A2]; positivity
    have hA3_nn : 0 ≤ A3 := by simp only [A3]; positivity
    have hA4_nn : 0 ≤ A4 := by simp only [A4]; positivity
    have h1 := rpow_add_le_add_rpow_of_le_one (show 0 ≤ A1 + A2 + A3 by linarith) hA4_nn ht0 ht1
    have h2 := rpow_add_le_add_rpow_of_le_one (show 0 ≤ A1 + A2 by linarith) hA3_nn ht0 ht1
    have h3 := rpow_add_le_add_rpow_of_le_one hA1_nn hA2_nn ht0 ht1
    linarith
  have hU_split : U ^ (1 - (j : ℝ) / K) * U ^ ((j : ℝ) / K) = U := by
    rw [← Real.rpow_add hU_pos, sub_add_cancel, Real.rpow_one]
  have hb1 : U ^ (1 - (j : ℝ) / K) * A1 ^ ((j : ℝ) / K) ≤ (3 : ℝ) ^ K * U / (q : ℝ) ^ 2 := by
    have hA1_eq : A1 ^ ((j : ℝ) / K) = (3 : ℝ) ^ j * U ^ ((j : ℝ) / K) / (q : ℝ) ^ j := by
      simp only [A1]
      rw [Real.div_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) hU_pos.le]
      have h3p : ((3 : ℝ) ^ K) ^ ((j : ℝ) / K) = (3 : ℝ) ^ j := by
        rw [← Real.rpow_natCast (3 : ℝ) K, ← Real.rpow_mul (by norm_num)]
        rw [mul_div_cancel₀ _ (by exact_mod_cast hK_pos.ne'), Real.rpow_natCast]
      have hqp : ((q : ℝ) ^ K) ^ ((j : ℝ) / K) = (q : ℝ) ^ j := by
        rw [← Real.rpow_natCast (q : ℝ) K, ← Real.rpow_mul hq_pos.le]
        rw [mul_div_cancel₀ _ (by exact_mod_cast hK_pos.ne'), Real.rpow_natCast]
      rw [h3p, hqp]
    rw [hA1_eq]
    have hmul : U ^ (1 - (j : ℝ) / K) * ((3 : ℝ) ^ j * U ^ ((j : ℝ) / K) / (q : ℝ) ^ j) =
        (3 : ℝ) ^ j * U / (q : ℝ) ^ j := by
      calc _ = (3 : ℝ) ^ j * (U ^ (1 - (j : ℝ) / K) * U ^ ((j : ℝ) / K)) / (q : ℝ) ^ j := by ring
        _ = _ := by rw [hU_split]
    rw [hmul]
    exact div_le_div₀ (by positivity)
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hjK) hU_pos.le)
      (by positivity) (pow_le_pow_right₀ hq_ge1 hj2)
  have hb2 : U ^ (1 - (j : ℝ) / K) * A2 ^ ((j : ℝ) / K) ≤
      c2 ^ K * U / (q : ℝ) ^ ((1 : ℝ) + ε / k) := by
    have hA2_eq : A2 = c2 ^ K * U / (q : ℝ) ^ ((k : ℝ) + ε) := by
      have hexp : ((3 : ℝ) / 2 + ε / K) * (K : ℝ) = (K : ℝ) + ((k : ℝ) + ε) := by
        have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast hK_pos.ne'
        rw [add_mul, div_mul_cancel₀ _ hK0, hK_real]; ring
      have h2pow : ((2 : ℝ) ^ ((3 : ℝ) / 2 + ε / K)) ^ K =
          (2 : ℝ) ^ K * (2 : ℝ) ^ ((k : ℝ) + ε) := by
        rw [← Real.rpow_natCast _ K, ← Real.rpow_mul (by norm_num), hexp,
            Real.rpow_add (by norm_num), Real.rpow_natCast]
      simp only [A2, c2, U]
      rw [mul_pow, h2pow, Real.div_rpow (by positivity) hq_pos.le,
          Real.mul_rpow (by norm_num) hL_pos.le]
      ring
    rw [hA2_eq, Real.div_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) hU_pos.le]
    have hc2p : (c2 ^ K) ^ ((j : ℝ) / K) = c2 ^ j := by
      rw [← Real.rpow_natCast c2 K, ← Real.rpow_mul hc2_pos.le]
      rw [mul_div_cancel₀ _ (by exact_mod_cast hK_pos.ne'), Real.rpow_natCast]
    have hqp : ((q : ℝ) ^ ((k : ℝ) + ε)) ^ ((j : ℝ) / K) =
        (q : ℝ) ^ (((k : ℝ) + ε) * ((j : ℝ) / K)) := (Real.rpow_mul hq_pos.le _ _).symm
    rw [hc2p, hqp]
    have hmul : U ^ (1 - (j : ℝ) / K) *
        (c2 ^ j * U ^ ((j : ℝ) / K) / (q : ℝ) ^ (((k : ℝ) + ε) * ((j : ℝ) / K))) =
        c2 ^ j * U / (q : ℝ) ^ (((k : ℝ) + ε) * ((j : ℝ) / K)) := by
      calc _ = c2 ^ j * (U ^ (1 - (j : ℝ) / K) * U ^ ((j : ℝ) / K)) /
            (q : ℝ) ^ (((k : ℝ) + ε) * ((j : ℝ) / K)) := by ring
        _ = _ := by rw [hU_split]
    rw [hmul]
    have hc2_ge1 : 1 ≤ c2 := by
      have : (1 : ℝ) ≤ (2 : ℝ) ^ ((3 : ℝ) / 2 + ε / K) := Real.one_le_rpow (by norm_num) (by positivity)
      simp only [c2]; linarith
    have hexp_ge : (1 : ℝ) + ε / k ≤ ((k : ℝ) + ε) * ((j : ℝ) / K) := by
      have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
      have h1 : ((k : ℝ) + ε) * ((1 : ℝ) / k) = (1 : ℝ) + ε / k := by field_simp
      rw [← h1]; exact mul_le_mul_of_nonneg_left hjk_ge (by positivity)
    exact div_le_div₀ (by positivity)
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc2_ge1 hjK) hU_pos.le)
      (by positivity) (Real.rpow_le_rpow_of_exponent_le hq_ge1 hexp_ge)
  have hb3 : U ^ (1 - (j : ℝ) / K) * A3 ^ ((j : ℝ) / K) ≤
      (max 1 c3) * C ^ (1 - (1 : ℝ) / k) * (L : ℝ) ^ ((k : ℝ) + ε - ε / k) * Λ ^ k / (q : ℝ) := by
    have hA3_rpow : A3 ^ ((j : ℝ) / K) =
        c3 ^ ((j : ℝ) / K) * ((L : ℝ) / q) ^ ((j : ℝ) / 2) * Λ ^ ((j : ℝ) / 2) := by
      simp only [A3]
      rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hc3_pos.le (by positivity)]
      have hk_mul : (k : ℝ) * ((j : ℝ) / K) = (j : ℝ) / 2 := by
        rw [hK_real]; field_simp [show (k : ℝ) ≠ 0 by exact_mod_cast (show k ≠ 0 by omega)]
      rw [← Real.rpow_natCast ((L : ℝ) / q) k, ← Real.rpow_mul (by positivity), hk_mul]
      rw [← Real.rpow_natCast Λ k, ← Real.rpow_mul (by positivity), hk_mul]
    rw [hA3_rpow, Real.div_rpow hL_pos.le hq_pos.le]
    have hU_rpow : U ^ (1 - (j : ℝ) / K) =
        C ^ (1 - (j : ℝ) / K) * (L : ℝ) ^ (((k : ℝ) + ε) * (1 - (j : ℝ) / K)) := by
      simp only [U]
      rw [Real.mul_rpow hC_pos.le (by positivity), ← Real.rpow_mul hL_pos.le]
    rw [hU_rpow]
    have hL_comb : (L : ℝ) ^ (((k : ℝ) + ε) * (1 - (j : ℝ) / K)) * (L : ℝ) ^ ((j : ℝ) / 2) =
        (L : ℝ) ^ ((k : ℝ) + ε - ε * ((j : ℝ) / K)) := by
      rw [← Real.rpow_add hL_pos]
      congr 1
      have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
      rw [hK_real]; field_simp; ring
    have hrewrite : C ^ (1 - (j : ℝ) / K) * (L : ℝ) ^ (((k : ℝ) + ε) * (1 - (j : ℝ) / K)) *
        (c3 ^ ((j : ℝ) / K) * ((L : ℝ) ^ ((j : ℝ) / 2) / (q : ℝ) ^ ((j : ℝ) / 2)) *
          Λ ^ ((j : ℝ) / 2)) =
        c3 ^ ((j : ℝ) / K) * C ^ (1 - (j : ℝ) / K) *
          ((L : ℝ) ^ (((k : ℝ) + ε) * (1 - (j : ℝ) / K)) * (L : ℝ) ^ ((j : ℝ) / 2)) *
          Λ ^ ((j : ℝ) / 2) / (q : ℝ) ^ ((j : ℝ) / 2) := by ring
    rw [hrewrite, hL_comb]
    have hc3_le : c3 ^ ((j : ℝ) / K) ≤ max 1 c3 := by
      calc c3 ^ ((j : ℝ) / K) ≤ (max 1 c3) ^ ((j : ℝ) / K) :=
            Real.rpow_le_rpow hc3_pos.le (le_max_right 1 c3) ht0.le
        _ ≤ (max 1 c3) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (le_max_left 1 c3) ht1
        _ = max 1 c3 := Real.rpow_one _
    have hC_le : C ^ (1 - (j : ℝ) / K) ≤ C ^ (1 - (1 : ℝ) / k) :=
      Real.rpow_le_rpow_of_exponent_le hC1 (by linarith)
    have hL_le : (L : ℝ) ^ ((k : ℝ) + ε - ε * ((j : ℝ) / K)) ≤ (L : ℝ) ^ ((k : ℝ) + ε - ε / k) := by
      apply Real.rpow_le_rpow_of_exponent_le hL_ge1
      have : ε / k ≤ ε * ((j : ℝ) / K) := by
        rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hjk_ge hε.le
      linarith
    have hLam_le : Λ ^ ((j : ℝ) / 2) ≤ Λ ^ k := by
      rw [← Real.rpow_natCast Λ k]
      apply Real.rpow_le_rpow_of_exponent_le hΛ1
      have : (j : ℝ) ≤ 2 * (k : ℝ) := by rw [← hK_real]; exact_mod_cast hjK
      linarith
    have hq_ge : (q : ℝ) ≤ (q : ℝ) ^ ((j : ℝ) / 2) := by
      conv_lhs => rw [← Real.rpow_one (q : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le hq_ge1 (by linarith)
    exact div_le_div₀ (by positivity) (by gcongr) hq_pos hq_ge
  have hb4 : U ^ (1 - (j : ℝ) / K) * A4 ^ ((j : ℝ) / K) ≤
      (3 : ℝ) ^ K * C ^ (1 - (1 : ℝ) / k) * (L : ℝ) ^ ((k : ℝ) + ε - 1) := by
    have hA4_eq : A4 ^ ((j : ℝ) / K) = (3 : ℝ) ^ j := by
      simp only [A4]
      rw [← Real.rpow_natCast (3 : ℝ) K, ← Real.rpow_mul (by norm_num)]
      rw [mul_div_cancel₀ _ (by exact_mod_cast hK_pos.ne'), Real.rpow_natCast]
    have hU_rpow : U ^ (1 - (j : ℝ) / K) =
        C ^ (1 - (j : ℝ) / K) * (L : ℝ) ^ (((k : ℝ) + ε) * (1 - (j : ℝ) / K)) := by
      simp only [U]
      rw [Real.mul_rpow hC_pos.le (by positivity), ← Real.rpow_mul hL_pos.le]
    rw [hA4_eq, hU_rpow]
    have h3_le : (3 : ℝ) ^ j ≤ (3 : ℝ) ^ K := pow_le_pow_right₀ (by norm_num) hjK
    have hC_le : C ^ (1 - (j : ℝ) / K) ≤ C ^ (1 - (1 : ℝ) / k) :=
      Real.rpow_le_rpow_of_exponent_le hC1 (by linarith)
    have hL_le : (L : ℝ) ^ (((k : ℝ) + ε) * (1 - (j : ℝ) / K)) ≤ (L : ℝ) ^ ((k : ℝ) + ε - 1) := by
      apply Real.rpow_le_rpow_of_exponent_le hL_ge1
      have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
      have h1 : ((k : ℝ) + ε) * ((1 : ℝ) / k) = 1 + ε / k := by field_simp
      have h2 : ((k : ℝ) + ε) * ((1 : ℝ) / k) ≤ ((k : ℝ) + ε) * ((j : ℝ) / K) :=
        mul_le_mul_of_nonneg_left hjk_ge (by positivity)
      have h3 : (0 : ℝ) < ε / k := div_pos hε (by exact_mod_cast hk)
      nlinarith
    calc C ^ (1 - (j : ℝ) / K) * (L : ℝ) ^ (((k : ℝ) + ε) * (1 - (j : ℝ) / K)) * (3 : ℝ) ^ j
        = (3 : ℝ) ^ j * C ^ (1 - (j : ℝ) / K) * (L : ℝ) ^ (((k : ℝ) + ε) * (1 - (j : ℝ) / K)) := by ring
      _ ≤ (3 : ℝ) ^ K * C ^ (1 - (1 : ℝ) / k) * (L : ℝ) ^ ((k : ℝ) + ε - 1) := by gcongr
  have hmul_sub := mul_le_mul_of_nonneg_left hsubadd (Real.rpow_nonneg hU_pos.le (1 - (j : ℝ) / K))
  change U ^ (1 - (j : ℝ) / K) * (A1 + A2 + A3 + A4) ^ ((j : ℝ) / K) ≤
      (3 : ℝ) ^ K * U / (q : ℝ) ^ 2 +
      c2 ^ K * U / (q : ℝ) ^ ((1 : ℝ) + ε / k) +
      (max 1 c3) * C ^ (1 - (1 : ℝ) / k) * (L : ℝ) ^ ((k : ℝ) + ε - ε / k) * Λ ^ k / (q : ℝ) +
      (3 : ℝ) ^ K * C ^ (1 - (1 : ℝ) / k) * (L : ℝ) ^ ((k : ℝ) + ε - 1)
  linarith

-- Helper 3: Single prime insertion step for centMom
private lemma medium_insert_step (k q0 L q : ℕ) (hk : 1 ≤ k) {ε C : ℝ} (hε : 0 < ε)
    (hC1 : 1 ≤ C) (hq0_3 : 3 ≤ q0) (hq_prime : q.Prime) (hq_ge : q0 ≤ q) (hq_leL : q ≤ L)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ q0 ≤ p ∧ p ≤ L) (hqnot : q ∉ S)
    (hS_bound_U : centMom (2 * k) S L ≤ C * (L : ℝ) ^ ((k : ℝ) + ε))
    (ihL : ∀ m < L, ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ q0 ≤ p ∧ p ≤ m) →
      centMom (2 * k) Q m ≤ C * ((max 1 m : ℕ) : ℝ) ^ ((k : ℝ) + ε)) :
    let K := 2 * k
    let U : ℝ := C * (L : ℝ) ^ ((k : ℝ) + ε)
    let Λ : ℝ := 2 + Real.log (L : ℝ)
    let c2 : ℝ := 3 * (2 : ℝ) ^ ((3 : ℝ) / 2 + ε / K)
    let c3 : ℝ := (3 : ℝ) ^ K * (2 : ℝ) ^ K * largeMartConst k * (2 : ℝ) ^ k
    centMom K (insert q S) L ≤ centMom K S L +
      ((2 : ℝ) ^ K * (3 : ℝ) ^ K * U / (q : ℝ) ^ 2 +
      (2 : ℝ) ^ K * c2 ^ K * U / (q : ℝ) ^ ((1 : ℝ) + ε / k) +
      (2 : ℝ) ^ K * (max 1 c3) * C ^ (1 - (1 : ℝ) / k) *
        (L : ℝ) ^ ((k : ℝ) + ε - ε / k) * Λ ^ k / (q : ℝ) +
      (2 : ℝ) ^ K * (3 : ℝ) ^ K * C ^ (1 - (1 : ℝ) / k) * (L : ℝ) ^ ((k : ℝ) + ε - 1)) := by
  dsimp only
  set K := 2 * k
  set U : ℝ := C * (L : ℝ) ^ ((k : ℝ) + ε)
  set Λ : ℝ := 2 + Real.log (L : ℝ)
  set c2 : ℝ := 3 * (2 : ℝ) ^ ((3 : ℝ) / 2 + ε / K)
  set c3 : ℝ := (3 : ℝ) ^ K * (2 : ℝ) ^ K * largeMartConst k * (2 : ℝ) ^ k
  set A1 : ℝ := (3 : ℝ) ^ K * U / (q : ℝ) ^ K
  set A2 : ℝ := (3 : ℝ) ^ K * (2 : ℝ) ^ K * C * (2 * (L : ℝ) / q) ^ ((k : ℝ) + ε)
  set A3 : ℝ := c3 * ((L : ℝ) / q) ^ k * Λ ^ k
  set A4 : ℝ := (3 : ℝ) ^ K
  have hK_pos : 0 < K := by omega
  have hK_even : Even K := ⟨k, by dsimp only [K]; omega⟩
  have hL1 : 1 ≤ L := by omega
  have hq_pos : (0 : ℝ) < q := by exact_mod_cast hq_prime.pos
  have hS_prime : ∀ p ∈ S, p.Prime := fun p hp => (hS p hp).1
  have hIS_prime : ∀ p ∈ insert q S, p.Prime := fun p hp => by
    rcases Finset.mem_insert.mp hp with rfl | hp'
    · exact hq_prime
    · exact hS_prime p hp'
  have : NeZero q := ⟨hq_prime.ne_zero⟩
  have : NeZero (prodQ S) := ⟨prodQ_ne_zero hS_prime⟩
  have : NeZero (prodQ (insert q S)) := ⟨prodQ_ne_zero hIS_prime⟩
  let e := crtInsert hq_prime hS_prime hqnot
  let Zfn : ZMod (prodQ S) × ZMod q → ℝ :=
    fun p => (1 - (1 : ℝ) / q) * (countQ S L p.1 - (L : ℝ) * densQ S)
  let Δfn : ZMod (prodQ S) × ZMod q → ℝ :=
    fun p => countQ (insert q S) L (e.symm (p.2, p.1)) - (1 - (1 : ℝ) / q) * countQ S L p.1
  have hΔ_mom := medium_step_delta_moment k q0 L q hk hε hC1 hq0_3 hq_prime hq_ge hq_leL S hS
    hqnot hS_bound_U ihL
  have hZ_mom : (1 / (Fintype.card (ZMod (prodQ S) × ZMod q) : ℝ)) *
      ∑ p : ZMod (prodQ S) × ZMod q, |Zfn p| ^ K ≤ U := by
    have hcard_eq : (Fintype.card (ZMod (prodQ S) × ZMod q) : ℝ) = (prodQ S : ℝ) * (q : ℝ) := by
      simp [Fintype.card_prod, ZMod.card]
    rw [hcard_eq, Fintype.sum_prod_type]
    have hfac : ∀ b : ZMod (prodQ S), ∑ r : ZMod q, |Zfn (b, r)| ^ K =
        (q : ℝ) * (1 - (1 : ℝ) / q) ^ K * (countQ S L b - (L : ℝ) * densQ S) ^ K := by
      intro b
      have hconst : ∀ r : ZMod q, |Zfn (b, r)| ^ K =
          (1 - (1 : ℝ) / q) ^ K * (countQ S L b - (L : ℝ) * densQ S) ^ K := by
        intro r
        simp only [Zfn, abs_mul, mul_pow]
        have h1 : 0 ≤ 1 - (1 : ℝ) / q := by
          have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq_prime.two_le
          have : (1 : ℝ) / q ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hq2
          linarith
        rw [abs_of_nonneg h1]
        simp only [K, pow_mul, sq_abs]
      simp_rw [hconst]
      simp [ZMod.card, mul_assoc]
    simp_rw [hfac, ← Finset.mul_sum]
    have hsimp : 1 / ((prodQ S : ℝ) * (q : ℝ)) *
        ((q : ℝ) * (1 - (1 : ℝ) / q) ^ K *
          ∑ b : ZMod (prodQ S), (countQ S L b - (L : ℝ) * densQ S) ^ K) =
        (1 - (1 : ℝ) / q) ^ K * centMom K S L := by
      rw [centMom_eq_sum_zmod]; field_simp [hq_pos.ne']
    rw [hsimp]
    have h1 : (1 - (1 : ℝ) / q) ^ K ≤ 1 := by
      apply pow_le_one₀
      · have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq_prime.two_le
        have : (1 : ℝ) / q ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hq2
        linarith
      · linarith [show (0 : ℝ) < 1 / q by positivity]
    have hcm_nn : 0 ≤ centMom K S L := by
      rw [centMom_eq_sum_zmod]
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => hK_even.pow_nonneg _)
    exact (mul_le_of_le_one_left hcm_nn h1).trans hS_bound_U
  have hstep_expand : centMom K (insert q S) L =
      (1 - (1 : ℝ) / q) ^ K * centMom K S L +
      ∑ j ∈ Finset.Icc 2 K, (Nat.choose K j : ℝ) *
        ((1 / (Fintype.card (ZMod (prodQ S) × ZMod q) : ℝ)) *
          ∑ p : ZMod (prodQ S) × ZMod q, Zfn p ^ (K - j) * Δfn p ^ j) := by
    rw [centMom_eq_sum_zmod, avg_zmod_insert hq_prime hS_prime hqnot]
    have hcard_eq : (Fintype.card (ZMod (prodQ S) × ZMod q) : ℝ) = (prodQ S : ℝ) * (q : ℝ) := by
      simp [Fintype.card_prod, ZMod.card]
    have hsplit : ∀ (b : ZMod (prodQ S)) (r : ZMod q),
        (countQ (insert q S) L ((crtInsert hq_prime hS_prime hqnot).symm (r, b)) -
          (L : ℝ) * densQ (insert q S)) ^ K =
        Zfn (b, r) ^ K + (K : ℝ) * Zfn (b, r) ^ (K - 1) * Δfn (b, r) +
          ∑ j ∈ Finset.Icc 2 K, (Nat.choose K j : ℝ) * Zfn (b, r) ^ (K - j) * Δfn (b, r) ^ j := by
      intro b r
      have hadd : countQ (insert q S) L ((crtInsert hq_prime hS_prime hqnot).symm (r, b)) -
            (L : ℝ) * densQ (insert q S) =
          Zfn (b, r) + Δfn (b, r) := by
        simp only [Zfn, Δfn, e, densQ_insert hqnot]; ring
      rw [hadd]
      exact add_pow_split_two (Zfn (b, r)) (Δfn (b, r)) K (by omega)
    simp_rw [hsplit, Finset.sum_add_distrib]
    have hzero : ∀ b : ZMod (prodQ S),
        ∑ r : ZMod q, (K : ℝ) * Zfn (b, r) ^ (K - 1) * Δfn (b, r) = 0 := by
      intro b
      have hconst : ∀ r : ZMod q, Zfn (b, r) = Zfn (b, 0) := fun _ => rfl
      simp_rw [hconst, ← Finset.mul_sum]
      have := sum_delta_insert_eq_zero hq_prime hS_prime hqnot b (A := Finset.Icc 1 L)
      change (K : ℝ) * Zfn (b, 0) ^ (K - 1) * ∑ r : ZMod q, Δfn (b, r) = 0
      rw [show ∑ r : ZMod q, Δfn (b, r) = 0 from this, mul_zero]
    simp_rw [hzero, add_zero]
    simp_rw [mul_add, Finset.sum_add_distrib, mul_add]
    congr 1
    · have hZsum : ∀ b : ZMod (prodQ S),
          (1 / (q : ℝ)) * ∑ r : ZMod q, Zfn (b, r) ^ K =
          (1 - (1 : ℝ) / q) ^ K * (countQ S L b - (L : ℝ) * densQ S) ^ K := by
        intro b
        simp only [Zfn, mul_pow, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
        rw [← mul_assoc, mul_comm (1 / (q : ℝ)), ← mul_assoc, mul_one_div_cancel hq_pos.ne', one_mul]
      simp_rw [hZsum, ← Finset.mul_sum]
      rw [centMom_eq_sum_zmod]; ring
    · simp_rw [hcard_eq, Fintype.sum_prod_type]
      rw [Finset.mul_sum]
      have hswap : ∀ b : ZMod (prodQ S),
          (1 / (prodQ S : ℝ)) * ((1 / (q : ℝ)) *
            ∑ r : ZMod q, ∑ j ∈ Finset.Icc 2 K,
              (Nat.choose K j : ℝ) * Zfn (b, r) ^ (K - j) * Δfn (b, r) ^ j) =
          ∑ j ∈ Finset.Icc 2 K, (Nat.choose K j : ℝ) *
            ((1 / ((prodQ S : ℝ) * (q : ℝ))) *
              ∑ r : ZMod q, Zfn (b, r) ^ (K - j) * Δfn (b, r) ^ j) := by
        intro b
        rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro r _; ring
      simp_rw [hswap]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro j _
      rw [← Finset.mul_sum, ← Finset.mul_sum]
  set Bq : ℝ := (3 : ℝ) ^ K * U / (q : ℝ) ^ 2 +
      c2 ^ K * U / (q : ℝ) ^ ((1 : ℝ) + ε / k) +
      (max 1 c3) * C ^ (1 - (1 : ℝ) / k) * (L : ℝ) ^ ((k : ℝ) + ε - ε / k) * Λ ^ k / (q : ℝ) +
      (3 : ℝ) ^ K * C ^ (1 - (1 : ℝ) / k) * (L : ℝ) ^ ((k : ℝ) + ε - 1)
  have hBq_nn : 0 ≤ Bq := by
    have : 0 ≤ U := by positivity
    have : 0 ≤ c2 := by positivity
    have : 0 ≤ Λ := by have := Real.log_nonneg (show (1 : ℝ) ≤ L by exact_mod_cast hL1); linarith
    positivity
  have hj_bound : ∀ j ∈ Finset.Icc 2 K,
      (1 / (Fintype.card (ZMod (prodQ S) × ZMod q) : ℝ)) *
        ∑ p : ZMod (prodQ S) × ZMod q, Zfn p ^ (K - j) * Δfn p ^ j ≤ Bq := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have h1mt : ((K : ℝ) - j) / K = 1 - (j : ℝ) / K := by
      have : (K : ℝ) ≠ 0 := by exact_mod_cast hK_pos.ne'
      field_simp
    have hj_leR : (j : ℝ) ≤ K := by exact_mod_cast hj.2
    have hhold : (1 / (Fintype.card (ZMod (prodQ S) × ZMod q) : ℝ)) *
        ∑ p : ZMod (prodQ S) × ZMod q, Zfn p ^ (K - j) * Δfn p ^ j ≤
        U ^ (1 - (j : ℝ) / K) * (A1 + A2 + A3 + A4) ^ ((j : ℝ) / K) := by
      calc (1 / (Fintype.card (ZMod (prodQ S) × ZMod q) : ℝ)) *
            ∑ p : ZMod (prodQ S) × ZMod q, Zfn p ^ (K - j) * Δfn p ^ j
          ≤ (1 / (Fintype.card (ZMod (prodQ S) × ZMod q) : ℝ)) *
            ∑ p : ZMod (prodQ S) × ZMod q, |Zfn p| ^ (K - j) * |Δfn p| ^ j := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply Finset.sum_le_sum; intro p _
            calc Zfn p ^ (K - j) * Δfn p ^ j ≤ |Zfn p ^ (K - j) * Δfn p ^ j| := le_abs_self _
              _ = |Zfn p| ^ (K - j) * |Δfn p| ^ j := by rw [abs_mul, abs_pow, abs_pow]
        _ ≤ ((1 / (Fintype.card (ZMod (prodQ S) × ZMod q) : ℝ)) *
              ∑ p : ZMod (prodQ S) × ZMod q, |Zfn p| ^ K) ^ (((K : ℝ) - j) / K) *
            ((1 / (Fintype.card (ZMod (prodQ S) × ZMod q) : ℝ)) *
              ∑ p : ZMod (prodQ S) × ZMod q, |Δfn p| ^ K) ^ ((j : ℝ) / K) :=
            avg_mul_pow_le_holder (fun p => |Zfn p|) (fun p => |Δfn p|)
              (fun _ => abs_nonneg _) (fun _ => abs_nonneg _) hK_pos (by omega) hj.2
        _ ≤ U ^ (((K : ℝ) - j) / K) * (A1 + A2 + A3 + A4) ^ ((j : ℝ) / K) := by
            apply mul_le_mul
            · exact Real.rpow_le_rpow
                (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => pow_nonneg (abs_nonneg _) _))
                hZ_mom (div_nonneg (by linarith) (by positivity))
            · exact Real.rpow_le_rpow
                (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => pow_nonneg (abs_nonneg _) _))
                hΔ_mom (by positivity)
            · exact Real.rpow_nonneg
                (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => pow_nonneg (abs_nonneg _) _)) _
            · exact Real.rpow_nonneg (by positivity) _
        _ = U ^ (1 - (j : ℝ) / K) * (A1 + A2 + A3 + A4) ^ ((j : ℝ) / K) := by rw [h1mt]
    exact hhold.trans (medium_holder_four_terms k L q j hk hL1 hq_prime.one_le hj.1 hj.2 hε hC1)
  rw [hstep_expand]
  have h1_le : (1 - (1 : ℝ) / q) ^ K * centMom K S L ≤ centMom K S L := by
    have hfac : (1 - (1 : ℝ) / q) ^ K ≤ 1 := by
      apply pow_le_one₀
      · have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq_prime.two_le
        have : (1 : ℝ) / q ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hq2
        linarith
      · linarith [show (0 : ℝ) < 1 / q by positivity]
    have hcm_nn : 0 ≤ centMom K S L := by
      rw [centMom_eq_sum_zmod]
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => hK_even.pow_nonneg _)
    exact mul_le_of_le_one_left hcm_nn hfac
  have hsum_j : ∑ j ∈ Finset.Icc 2 K, (Nat.choose K j : ℝ) *
      ((1 / (Fintype.card (ZMod (prodQ S) × ZMod q) : ℝ)) *
        ∑ p : ZMod (prodQ S) × ZMod q, Zfn p ^ (K - j) * Δfn p ^ j) ≤ (2 : ℝ) ^ K * Bq := by
    calc _ ≤ ∑ j ∈ Finset.Icc 2 K, (Nat.choose K j : ℝ) * Bq := by
          apply Finset.sum_le_sum; intro j hj
          exact mul_le_mul_of_nonneg_left (hj_bound j hj) (Nat.cast_nonneg _)
      _ = (∑ j ∈ Finset.Icc 2 K, (Nat.choose K j : ℝ)) * Bq := (Finset.sum_mul _ _ _).symm
      _ ≤ (2 : ℝ) ^ K * Bq := by
          apply mul_le_mul_of_nonneg_right _ hBq_nn
          calc ∑ j ∈ Finset.Icc 2 K, (Nat.choose K j : ℝ)
              ≤ ∑ j ∈ Finset.range (K + 1), (Nat.choose K j : ℝ) := by
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro j hj; simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢; omega
                · intro _ _ _; positivity
            _ = (2 : ℝ) ^ K := by rw [← Nat.cast_sum, Nat.sum_range_choose]; norm_cast
  have hBq_eq : (2 : ℝ) ^ K * Bq =
      (2 : ℝ) ^ K * (3 : ℝ) ^ K * U / (q : ℝ) ^ 2 +
      (2 : ℝ) ^ K * c2 ^ K * U / (q : ℝ) ^ ((1 : ℝ) + ε / k) +
      (2 : ℝ) ^ K * (max 1 c3) * C ^ (1 - (1 : ℝ) / k) *
        (L : ℝ) ^ ((k : ℝ) + ε - ε / k) * Λ ^ k / (q : ℝ) +
      (2 : ℝ) ^ K * (3 : ℝ) ^ K * C ^ (1 - (1 : ℝ) / k) * (L : ℝ) ^ ((k : ℝ) + ε - 1) := by
    simp only [Bq]; ring
  linarith

lemma medium_primes_moment_bound (k : ℕ) (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ q0 : ℕ, 3 ≤ q0 ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ (L : ℕ) (Q : Finset ℕ), (∀ q ∈ Q, q.Prime ∧ q0 ≤ q ∧ q ≤ L) →
        centMom (2 * k) Q L ≤ C * ((max 1 L : ℕ) : ℝ) ^ ((k : ℝ) + ε) := by
  set K := 2 * k
  have hK_pos : 0 < K := by omega
  have hK1 : 1 ≤ K := by omega
  have hα2 : 1 < (1 : ℝ) + ε / k := by
    have : (0 : ℝ) < ε / k := div_pos hε (by exact_mod_cast hk)
    linarith
  obtain ⟨N1, hN1_3, hN1⟩ := tail_rpow_sum_tendsto_zero (α := (2 : ℝ)) (by norm_num)
    (1 / (4 * (2 : ℝ) ^ K * (3 : ℝ) ^ K)) (by positivity)
  set c2 : ℝ := 3 * (2 : ℝ) ^ ((3 : ℝ) / 2 + ε / K)
  have hc2_pos : 0 < c2 := by positivity
  obtain ⟨N2, hN2_3, hN2⟩ := tail_rpow_sum_tendsto_zero (α := (1 : ℝ) + ε / k) hα2
    (1 / (4 * (2 : ℝ) ^ K * c2 ^ K)) (by positivity)
  set q0 := max N1 N2
  have hq0_3 : 3 ≤ q0 := le_trans hN1_3 (le_max_left _ _)
  obtain ⟨D_log, hD_log_pos, hD_log⟩ := log_pow_le_const_mul_rpow (a := (k + 1 : ℝ))
    (δ := ε / k) (by positivity) (div_pos hε (by exact_mod_cast hk))
  have hLam_bound : ∀ L : ℕ, 1 ≤ L →
      (2 + Real.log (L : ℝ)) ^ (k + 1) ≤ 3 ^ (k + 1) * D_log * (L : ℝ) ^ (ε / k) := by
    intro L hL
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
    have h2le : 2 + Real.log (L : ℝ) ≤ 3 * Real.log ((L : ℝ) + 10) := by
      have hlog11 : 1 ≤ Real.log ((L : ℝ) + 10) := by
        have h1 : Real.exp 1 ≤ (L : ℝ) + 10 := by linarith [Real.exp_one_lt_d9]
        exact (Real.le_log_iff_exp_le (by linarith)).mpr h1
      have hlog_mono : Real.log (L : ℝ) ≤ Real.log ((L : ℝ) + 10) :=
        Real.log_le_log (by linarith) (by linarith)
      linarith
    have hnonneg : 0 ≤ 2 + Real.log (L : ℝ) := by have := Real.log_nonneg hL1; linarith
    calc (2 + Real.log (L : ℝ)) ^ (k + 1)
        ≤ (3 * Real.log ((L : ℝ) + 10)) ^ (k + 1) := pow_le_pow_left₀ hnonneg h2le _
      _ = 3 ^ (k + 1) * (Real.log ((L : ℝ) + 10)) ^ (k + 1) := mul_pow _ _ _
      _ = 3 ^ (k + 1) * (Real.log ((L : ℝ) + 10)) ^ ((k + 1 : ℕ) : ℝ) := by rw [Real.rpow_natCast]
      _ ≤ 3 ^ (k + 1) * (D_log * (L : ℝ) ^ (ε / k)) := by gcongr; simpa using hD_log (L : ℝ) hL1
      _ = 3 ^ (k + 1) * D_log * (L : ℝ) ^ (ε / k) := by ring
  set c3 : ℝ := (3 : ℝ) ^ K * (2 : ℝ) ^ K * largeMartConst k * (2 : ℝ) ^ k
  have hc3_pos : 0 < c3 := by have := largeMartConst_pos k; positivity
  set M3 : ℝ := 4 * (2 : ℝ) ^ K * (max 1 c3) * (3 ^ (k + 1) * D_log)
  set M4 : ℝ := 4 * (2 : ℝ) ^ K * (3 : ℝ) ^ K
  set C : ℝ := max 1 ((max M3 M4) ^ k)
  have hC1 : 1 ≤ C := le_max_left _ _
  have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hC_A3 : (2 : ℝ) ^ K * (max 1 c3) * (3 ^ (k + 1) * D_log) * C ^ (-((1 : ℝ) / k)) ≤ 1 / 4 := by
    have hM3_le : M3 ≤ C ^ ((1 : ℝ) / k) := by
      have h1 : M3 ≤ max M3 M4 := le_max_left _ _
      have h2 : (max M3 M4) ^ k ≤ C := le_max_right _ _
      have hM_nn : 0 ≤ max M3 M4 := le_trans (by positivity) (le_max_left M3 M4)
      have h3 := Real.rpow_le_rpow (pow_nonneg hM_nn k) h2 (show (0 : ℝ) ≤ 1 / k by positivity)
      rw [← Real.rpow_natCast (max M3 M4) k, ← Real.rpow_mul hM_nn,
          mul_one_div_cancel (by exact_mod_cast (show k ≠ 0 by omega)), Real.rpow_one] at h3
      exact h1.trans h3
    rw [Real.rpow_neg hC_pos.le, ← div_eq_mul_inv, div_le_iff₀ (Real.rpow_pos_of_pos hC_pos _)]
    simp only [M3] at hM3_le; linarith
  have hC_A4 : (2 : ℝ) ^ K * (3 : ℝ) ^ K * C ^ (-((1 : ℝ) / k)) ≤ 1 / 4 := by
    have hM4_le : M4 ≤ C ^ ((1 : ℝ) / k) := by
      have h1 : M4 ≤ max M3 M4 := le_max_right _ _
      have h2 : (max M3 M4) ^ k ≤ C := le_max_right _ _
      have hM_nn : 0 ≤ max M3 M4 := le_trans (by positivity) (le_max_right M3 M4)
      have h3 := Real.rpow_le_rpow (pow_nonneg hM_nn k) h2 (show (0 : ℝ) ≤ 1 / k by positivity)
      rw [← Real.rpow_natCast (max M3 M4) k, ← Real.rpow_mul hM_nn,
          mul_one_div_cancel (by exact_mod_cast (show k ≠ 0 by omega)), Real.rpow_one] at h3
      exact h1.trans h3
    rw [Real.rpow_neg hC_pos.le, ← div_eq_mul_inv, div_le_iff₀ (Real.rpow_pos_of_pos hC_pos _)]
    simp only [M4] at hM4_le; linarith
  refine ⟨q0, hq0_3, C, hC1, ?_⟩
  intro L
  induction L using Nat.strong_induction_on with | h L ihL =>
  intro Q hQ
  by_cases hL0 : L < q0
  · have hQ_emp : Q = ∅ := by
      ext q; simp only [Finset.notMem_empty, iff_false]
      intro hq; have := hQ q hq; omega
    subst hQ_emp
    rw [centMom_empty K L hK1]
    positivity
  · push Not at hL0
    have hL1 : 1 ≤ L := by omega
    have hmaxL : max 1 L = L := by omega
    rw [hmaxL]
    set U : ℝ := C * (L : ℝ) ^ ((k : ℝ) + ε)
    have hL_pos : (0 : ℝ) < L := by exact_mod_cast hL1
    have hL_ge1 : (1 : ℝ) ≤ L := by exact_mod_cast hL1
    have hU_pos : 0 < U := by positivity
    set Λ : ℝ := 2 + Real.log (L : ℝ)
    have hΛ1 : 1 ≤ Λ := by have := Real.log_nonneg hL_ge1; linarith
    let W : ℕ → ℝ := fun q =>
      (2 : ℝ) ^ K * (3 : ℝ) ^ K * U / (q : ℝ) ^ 2 +
      (2 : ℝ) ^ K * c2 ^ K * U / (q : ℝ) ^ ((1 : ℝ) + ε / k) +
      (2 : ℝ) ^ K * (max 1 c3) * C ^ (1 - (1 : ℝ) / k) *
        (L : ℝ) ^ ((k : ℝ) + ε - ε / k) * Λ ^ k / (q : ℝ) +
      (2 : ℝ) ^ K * (3 : ℝ) ^ K * C ^ (1 - (1 : ℝ) / k) * (L : ℝ) ^ ((k : ℝ) + ε - 1)
    have hW_sum_le : ∀ S : Finset ℕ, S ⊆ Q → ∑ q ∈ S, W q ≤ U := by
      intro S hSQ
      have hS_ge_N1 : ∀ q ∈ S, N1 ≤ q := fun q hq =>
        le_trans (le_max_left N1 N2) (hQ q (hSQ hq)).2.1
      have hS_ge_N2 : ∀ q ∈ S, N2 ≤ q := fun q hq =>
        le_trans (le_max_right N1 N2) (hQ q (hSQ hq)).2.1
      have hS_card : S.card ≤ L := by
        have hsub : S ⊆ Finset.Icc 1 L := fun q hq =>
          Finset.mem_Icc.mpr ⟨(hQ q (hSQ hq)).1.one_le, (hQ q (hSQ hq)).2.2⟩
        simpa using Finset.card_le_card hsub
      have hS_harm : ∑ q ∈ S, (1 : ℝ) / q ≤ Λ := by
        have hsub : S ⊆ Finset.Icc 1 L := fun q hq =>
          Finset.mem_Icc.mpr ⟨(hQ q (hSQ hq)).1.one_le, (hQ q (hSQ hq)).2.2⟩
        calc ∑ q ∈ S, (1 : ℝ) / q ≤ ∑ n ∈ Finset.Icc 1 L, (1 : ℝ) / n :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
          _ ≤ 1 + Real.log (max 1 L : ℕ) := sum_one_div_Icc_le_one_add_log L
          _ ≤ Λ := by rw [hmaxL]; linarith
      simp only [W, Finset.sum_add_distrib]
      have hT1 : ∑ q ∈ S, (2 : ℝ) ^ K * (3 : ℝ) ^ K * U / (q : ℝ) ^ 2 ≤ U / 4 := by
        have hfac : ∑ q ∈ S, (2 : ℝ) ^ K * (3 : ℝ) ^ K * U / (q : ℝ) ^ 2 =
            ((2 : ℝ) ^ K * (3 : ℝ) ^ K * U) * ∑ q ∈ S, (1 : ℝ) / (q : ℝ) ^ (2 : ℝ) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _
          rw [Real.rpow_two]; ring
        rw [hfac]
        calc ((2 : ℝ) ^ K * (3 : ℝ) ^ K * U) * ∑ q ∈ S, (1 : ℝ) / (q : ℝ) ^ (2 : ℝ)
            ≤ ((2 : ℝ) ^ K * (3 : ℝ) ^ K * U) * (1 / (4 * (2 : ℝ) ^ K * (3 : ℝ) ^ K)) := by
              gcongr; exact hN1 S hS_ge_N1
          _ = U / 4 := by field_simp
      have hT2 : ∑ q ∈ S, (2 : ℝ) ^ K * c2 ^ K * U / (q : ℝ) ^ ((1 : ℝ) + ε / k) ≤ U / 4 := by
        have hfac : ∑ q ∈ S, (2 : ℝ) ^ K * c2 ^ K * U / (q : ℝ) ^ ((1 : ℝ) + ε / k) =
            ((2 : ℝ) ^ K * c2 ^ K * U) * ∑ q ∈ S, (1 : ℝ) / (q : ℝ) ^ ((1 : ℝ) + ε / k) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring
        rw [hfac]
        calc ((2 : ℝ) ^ K * c2 ^ K * U) * ∑ q ∈ S, (1 : ℝ) / (q : ℝ) ^ ((1 : ℝ) + ε / k)
            ≤ ((2 : ℝ) ^ K * c2 ^ K * U) * (1 / (4 * (2 : ℝ) ^ K * c2 ^ K)) := by
              gcongr; exact hN2 S hS_ge_N2
          _ = U / 4 := by field_simp
      have hT3 : ∑ q ∈ S, (2 : ℝ) ^ K * (max 1 c3) * C ^ (1 - (1 : ℝ) / k) *
          (L : ℝ) ^ ((k : ℝ) + ε - ε / k) * Λ ^ k / (q : ℝ) ≤ U / 4 := by
        have hfac : ∑ q ∈ S, (2 : ℝ) ^ K * (max 1 c3) * C ^ (1 - (1 : ℝ) / k) *
            (L : ℝ) ^ ((k : ℝ) + ε - ε / k) * Λ ^ k / (q : ℝ) =
            ((2 : ℝ) ^ K * (max 1 c3) * C ^ (1 - (1 : ℝ) / k) *
              (L : ℝ) ^ ((k : ℝ) + ε - ε / k) * Λ ^ k) * ∑ q ∈ S, (1 : ℝ) / q := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring
        rw [hfac]
        have hC_split : C ^ (1 - (1 : ℝ) / k) = C * C ^ (-((1 : ℝ) / k)) := by
          rw [sub_eq_add_neg, Real.rpow_add hC_pos, Real.rpow_one]
        have hL_split : (L : ℝ) ^ ((k : ℝ) + ε - ε / k) * (L : ℝ) ^ (ε / k) =
            (L : ℝ) ^ ((k : ℝ) + ε) := by
          rw [← Real.rpow_add hL_pos]; congr 1; ring
        have hLam_step : Λ ^ k * Λ ≤ 3 ^ (k + 1) * D_log * (L : ℝ) ^ (ε / k) := by
          rw [← pow_succ]; exact hLam_bound L hL1
        calc ((2 : ℝ) ^ K * (max 1 c3) * C ^ (1 - (1 : ℝ) / k) *
              (L : ℝ) ^ ((k : ℝ) + ε - ε / k) * Λ ^ k) * ∑ q ∈ S, (1 : ℝ) / q
            ≤ ((2 : ℝ) ^ K * (max 1 c3) * C ^ (1 - (1 : ℝ) / k) *
              (L : ℝ) ^ ((k : ℝ) + ε - ε / k) * Λ ^ k) * Λ := by gcongr
          _ = (2 : ℝ) ^ K * (max 1 c3) * C ^ (1 - (1 : ℝ) / k) *
              (L : ℝ) ^ ((k : ℝ) + ε - ε / k) * (Λ ^ k * Λ) := by ring
          _ ≤ (2 : ℝ) ^ K * (max 1 c3) * C ^ (1 - (1 : ℝ) / k) *
              (L : ℝ) ^ ((k : ℝ) + ε - ε / k) * (3 ^ (k + 1) * D_log * (L : ℝ) ^ (ε / k)) := by
              gcongr
          _ = ((2 : ℝ) ^ K * (max 1 c3) * (3 ^ (k + 1) * D_log) * C ^ (-((1 : ℝ) / k))) * U := by
              rw [hC_split]
              calc (2 : ℝ) ^ K * max 1 c3 * (C * C ^ (-(1 / (k : ℝ)))) *
                    (L : ℝ) ^ ((k : ℝ) + ε - ε / k) * (3 ^ (k + 1) * D_log * (L : ℝ) ^ (ε / k))
                  = ((2 : ℝ) ^ K * max 1 c3 * (3 ^ (k + 1) * D_log) * C ^ (-(1 / (k : ℝ)))) *
                    (C * ((L : ℝ) ^ ((k : ℝ) + ε - ε / k) * (L : ℝ) ^ (ε / k))) := by ring
                _ = _ := by rw [hL_split]
          _ ≤ (1 / 4 : ℝ) * U := mul_le_mul_of_nonneg_right hC_A3 hU_pos.le
          _ = U / 4 := by ring
      have hT4 : ∑ _q ∈ S, (2 : ℝ) ^ K * (3 : ℝ) ^ K * C ^ (1 - (1 : ℝ) / k) *
          (L : ℝ) ^ ((k : ℝ) + ε - 1) ≤ U / 4 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have hC_split : C ^ (1 - (1 : ℝ) / k) = C * C ^ (-((1 : ℝ) / k)) := by
          rw [sub_eq_add_neg, Real.rpow_add hC_pos, Real.rpow_one]
        have hL_split : (L : ℝ) * (L : ℝ) ^ ((k : ℝ) + ε - 1) = (L : ℝ) ^ ((k : ℝ) + ε) := by
          nth_rw 1 [← Real.rpow_one (L : ℝ)]
          rw [← Real.rpow_add hL_pos]; congr 1; ring
        calc (S.card : ℝ) * ((2 : ℝ) ^ K * (3 : ℝ) ^ K * C ^ (1 - (1 : ℝ) / k) *
              (L : ℝ) ^ ((k : ℝ) + ε - 1))
            ≤ (L : ℝ) * ((2 : ℝ) ^ K * (3 : ℝ) ^ K * C ^ (1 - (1 : ℝ) / k) *
              (L : ℝ) ^ ((k : ℝ) + ε - 1)) := by
              apply mul_le_mul_of_nonneg_right (by exact_mod_cast hS_card) (by positivity)
          _ = ((2 : ℝ) ^ K * (3 : ℝ) ^ K * C ^ (-((1 : ℝ) / k))) * U := by
              rw [hC_split]
              calc (L : ℝ) * ((2 : ℝ) ^ K * (3 : ℝ) ^ K * (C * C ^ (-(1 / (k : ℝ)))) *
                    (L : ℝ) ^ ((k : ℝ) + ε - 1))
                  = ((2 : ℝ) ^ K * (3 : ℝ) ^ K * C ^ (-(1 / (k : ℝ)))) *
                    (C * ((L : ℝ) * (L : ℝ) ^ ((k : ℝ) + ε - 1))) := by ring
                _ = _ := by rw [hL_split]
          _ ≤ (1 / 4 : ℝ) * U := mul_le_mul_of_nonneg_right hC_A4 hU_pos.le
          _ = U / 4 := by ring
      linarith
    have hindS : ∀ S : Finset ℕ, S ⊆ Q → centMom K S L ≤ ∑ q ∈ S, W q := by
      intro S
      induction S using Finset.induction_on with
      | empty =>
        intro _; rw [centMom_empty K L hK1]; simp
      | @insert q S hqnot ihS =>
        intro hSQ
        have hS_sub : S ⊆ Q := (Finset.subset_insert q S).trans hSQ
        have hihS := ihS hS_sub
        have hS_bound_U : centMom K S L ≤ U := hihS.trans (hW_sum_le S hS_sub)
        have hq_prop := hQ q (hSQ (Finset.mem_insert_self q S))
        have hstep := medium_insert_step k q0 L q hk hε hC1 hq0_3 hq_prop.1 hq_prop.2.1 hq_prop.2.2
          S (fun p hp => hQ p (hS_sub hp)) hqnot hS_bound_U ihL
        rw [Finset.sum_insert hqnot]
        dsimp only [W]
        linarith
    exact (hindS Q (Finset.Subset.refl Q)).trans (hW_sum_le Q (Finset.Subset.refl Q))

lemma peel_small_primes (k q0 : ℕ) (hk : 1 ≤ k) (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime) (L : ℕ) :
    centMom (2 * k) Q L ≤
      (2 : ℝ) ^ (2 * k) * ((4 ^ q0 : ℕ) : ℝ) ^ (2 * k) *
        (1 + (Finset.Icc 0 L).sup' (Finset.nonempty_Icc.mpr (Nat.zero_le L))
          (fun L' => centMom (2 * k) (Q.filter (fun q => q0 ≤ q)) L')) := by
  set K := 2 * k
  have hK1 : 1 ≤ K := by omega
  have hK_even : Even K := ⟨k, by dsimp only [K]; omega⟩
  set Q1 := Q.filter (fun q => q < q0)
  set Q2 := Q.filter (fun q => q0 ≤ q)
  have hQ1 : ∀ q ∈ Q1, q.Prime := fun q hq => hQ q (Finset.mem_filter.mp hq).1
  have hQ2 : ∀ q ∈ Q2, q.Prime := fun q hq => hQ q (Finset.mem_filter.mp hq).1
  have hdisj : Disjoint Q1 Q2 := by
    rw [Finset.disjoint_left]; intro q h1 h2
    have := (Finset.mem_filter.mp h1).2
    have := (Finset.mem_filter.mp h2).2
    omega
  have hunion : Q = Q1 ∪ Q2 := by
    ext q; simp only [Q1, Q2, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hq
      by_cases h : q < q0
      · exact Or.inl ⟨hq, h⟩
      · exact Or.inr ⟨hq, by omega⟩
    · rintro (⟨hq, _⟩ | ⟨hq, _⟩) <;> exact hq
  set P1 := prodQ Q1
  have hP1_pos : 0 < P1 := prodQ_pos hQ1
  have hP1_le : P1 ≤ 4 ^ q0 := by
    have hsub : Q1 ⊆ Nat.primesLE q0 := by
      intro q hq
      simp only [Q1, Finset.mem_filter] at hq
      exact Nat.mem_primesLE.mpr ⟨hq.2.le, hQ q hq.1⟩
    have hdvd : P1 ∣ primorial q0 := by
      rw [primorial_eq_prod_primesLE]
      exact Finset.prod_dvd_prod_of_subset _ _ _ hsub
    exact (Nat.le_of_dvd (primorial_pos q0) hdvd).trans (primorial_le_four_pow q0)
  have : NeZero P1 := ⟨hP1_pos.ne'⟩
  have : NeZero (prodQ Q2) := ⟨prodQ_ne_zero hQ2⟩
  have : NeZero (prodQ (Q1 ∪ Q2)) := ⟨prodQ_ne_zero (hunion ▸ hQ)⟩
  set Msup := (Finset.Icc 0 L).sup' (Finset.nonempty_Icc.mpr (Nat.zero_le L)) (fun L' => centMom K Q2 L')
  have hMsup_nn : 0 ≤ Msup := by
    have h0 : 0 ≤ centMom K Q2 0 := by
      rw [centMom_eq_sum_zmod]; exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => hK_even.pow_nonneg _)
    exact h0.trans (Finset.le_sup' (f := fun L' => centMom K Q2 L') (show 0 ∈ Finset.Icc 0 L by simp))
  let e := crtUnion hQ1 hQ2 hdisj
  have havg_eq : centMom K Q L =
      (1 / (P1 : ℝ)) * ∑ b1 : ZMod P1,
        (1 / (prodQ Q2 : ℝ)) * ∑ b2 : ZMod (prodQ Q2),
          (countQ (Q1 ∪ Q2) L (e.symm (b1, b2)) - (L : ℝ) * (densQ Q1 * densQ Q2)) ^ K := by
    have h1 : centMom K Q L = centMom K (Q1 ∪ Q2) L := by rw [← hunion]
    rw [h1, centMom_eq_sum_zmod, densQ_union hdisj, avg_zmod_union hQ1 hQ2 hdisj]
  rw [havg_eq]
  have hcop : P1.Coprime (prodQ Q2) := prodQ_coprime_of_disjoint hQ1 hQ2 hdisj
  have hu : IsUnit (P1 : ZMod (prodQ Q2)) := (ZMod.isUnit_iff_coprime P1 (prodQ Q2)).mpr hcop
  rcases hu with ⟨u, hu_eq⟩
  have hfor_b1 : ∀ b1 : ZMod P1,
      (1 / (prodQ Q2 : ℝ)) * ∑ b2 : ZMod (prodQ Q2),
        (countQ (Q1 ∪ Q2) L (e.symm (b1, b2)) - (L : ℝ) * (densQ Q1 * densQ Q2)) ^ K ≤
      (2 : ℝ) ^ K * (P1 : ℝ) ^ K * (1 + Msup) := by
    intro b1
    set U1 : Finset (ZMod P1) := Finset.univ.filter (fun r : ZMod P1 => IsUnit (b1 + r))
    have hU1_card : (U1.card : ℝ) = (P1 : ℝ) * densQ Q1 := by
      have hbij : U1.card = (Finset.univ.filter (fun x : ZMod P1 => IsUnit x)).card := by
        apply Finset.card_bij (fun r _ => b1 + r)
        · intro r hr; simp only [U1, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢; exact hr
        · intro r1 _ r2 _ heq; exact add_left_cancel heq
        · intro x hx
          refine ⟨x - b1, ?_, by ring⟩
          simp only [U1, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          simpa using hx
      have htot : (Finset.univ.filter (fun x : ZMod P1 => IsUnit x)).card = Nat.totient P1 := by
        rw [← ZMod.card_units_eq_totient P1]
        apply Finset.card_bij (fun x hx => (Finset.mem_filter.mp hx).2.unit)
        · intro _ _; exact Finset.mem_univ _
        · intro x hx y hy heq
          have := congrArg Units.val heq
          simpa using this
        · intro v _
          exact ⟨v.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, v.isUnit⟩, by ext; rfl⟩
      rw [hbij, htot]
      have hP1_pf : P1.primeFactors = Q1 := Nat.primeFactors_prod hQ1
      have htot_eq : (Nat.totient P1 : ℝ) = (P1 : ℝ) * ∏ p ∈ P1.primeFactors, (1 - (1 : ℝ) / p) := by
        have := Nat.totient_eq_mul_prod_factors P1
        have hrat := congrArg (fun q : ℚ => (q : ℝ)) this
        push_cast at hrat
        simp_rw [← one_div] at hrat
        exact hrat
      rw [htot_eq, hP1_pf]
      rfl
    let Sr : ZMod P1 → Finset ℕ := fun r =>
      (Finset.Icc 1 L).filter (fun i : ℕ => (-r) + (i : ZMod P1) = 0)
    have hcnt_decomp : ∀ b2 : ZMod (prodQ Q2),
        countQ (Q1 ∪ Q2) L (e.symm (b1, b2)) = ∑ r ∈ U1, countSub Q2 (Sr r) b2 := by
      intro b2
      have hpart : (Finset.Icc 1 L).filter (fun i : ℕ => IsUnit (b1 + (i : ZMod P1))) =
          U1.biUnion Sr := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_biUnion, U1, Sr, Finset.mem_univ, true_and]
        constructor
        · intro ⟨hi, hu1⟩
          refine ⟨(i : ZMod P1), hu1, hi, neg_add_cancel _⟩
        · rintro ⟨r, hr, hi, hri⟩
          have hr_eq : r = (i : ZMod P1) := by
            have := eq_neg_of_add_eq_zero_left hri
            simpa using congrArg Neg.neg this
          exact ⟨hi, hr_eq ▸ hr⟩
      have hpw : Set.PairwiseDisjoint (↑U1 : Set (ZMod P1)) Sr := by
        intro r1 _ r2 _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro i h1 h2
        simp only [Sr, Finset.mem_filter] at h1 h2
        have h1' : r1 = (i : ZMod P1) := by
          simpa using congrArg Neg.neg (eq_neg_of_add_eq_zero_left h1.2)
        have h2' : r2 = (i : ZMod P1) := by
          simpa using congrArg Neg.neg (eq_neg_of_add_eq_zero_left h2.2)
        exact hne (h1'.trans h2'.symm)
      have hlhs : countQ (Q1 ∪ Q2) L (e.symm (b1, b2)) =
          countSub Q2 ((Finset.Icc 1 L).filter (fun i : ℕ => IsUnit (b1 + (i : ZMod P1)))) b2 := by
        unfold countQ countSub
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl; intro i _
        have hunit : IsUnit (e.symm (b1, b2) + (i : ZMod (prodQ (Q1 ∪ Q2)))) ↔
            IsUnit (b1 + (i : ZMod P1)) ∧ IsUnit (b2 + (i : ZMod (prodQ Q2))) := by
          rw [isUnit_crt_iff e]
          simp [map_add, map_natCast, e.apply_symm_apply]
        simp only [hunit]
        by_cases h1 : IsUnit (b1 + (i : ZMod P1)) <;>
          by_cases h2 : IsUnit (b2 + (i : ZMod (prodQ Q2))) <;> simp [h1, h2]
      rw [hlhs, hpart]
      unfold countSub
      exact Finset.sum_biUnion hpw
    have herr_le : |∑ r ∈ U1, (((Sr r).card : ℝ) - (L : ℝ) / P1) * densQ Q2| ≤ (P1 : ℝ) := by
      calc |∑ r ∈ U1, (((Sr r).card : ℝ) - (L : ℝ) / P1) * densQ Q2|
          ≤ ∑ r ∈ U1, |(((Sr r).card : ℝ) - (L : ℝ) / P1) * densQ Q2| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _r ∈ U1, (1 : ℝ) := by
            apply Finset.sum_le_sum; intro r _
            rw [abs_mul, abs_of_pos (densQ_pos hQ2)]
            obtain ⟨_, _, _, _, hdiff, _, _⟩ := filter_residue_progression P1 L hP1_pos (-r)
            rw [abs_sub_comm] at hdiff
            exact mul_le_one₀ hdiff (densQ_pos hQ2).le (densQ_le_one hQ2)
        _ = (U1.card : ℝ) := by simp
        _ ≤ (P1 : ℝ) := by
            have hle : U1.card ≤ P1 := by
              calc U1.card ≤ (Finset.univ : Finset (ZMod P1)).card := Finset.card_le_univ _
                _ = P1 := ZMod.card P1
            exact_mod_cast hle
    have havg_r : ∀ r ∈ U1,
        (1 / (prodQ Q2 : ℝ)) * ∑ b2 : ZMod (prodQ Q2),
          (countSub Q2 (Sr r) b2 - ((Sr r).card : ℝ) * densQ Q2) ^ K ≤ Msup := by
      intro r _
      obtain ⟨a0, ha0_1, _, hSr_eq, _, _, _⟩ := filter_residue_progression P1 L hP1_pos (-r)
      let shiftEquiv : ZMod (prodQ Q2) ≃ ZMod (prodQ Q2) := {
        toFun := fun b => (u⁻¹ : (ZMod (prodQ Q2))ˣ) * (b + (a0 : ZMod (prodQ Q2)) - (P1 : ZMod (prodQ Q2)))
        invFun := fun c => (u : ZMod (prodQ Q2)) * c + (P1 : ZMod (prodQ Q2)) - (a0 : ZMod (prodQ Q2))
        left_inv := fun b => by dsimp only; rw [← mul_assoc, Units.mul_inv, one_mul]; ring
        right_inv := fun c => by
          dsimp only
          have : (u : ZMod (prodQ Q2)) * c + (P1 : ZMod (prodQ Q2)) - (a0 : ZMod (prodQ Q2)) +
              (a0 : ZMod (prodQ Q2)) - (P1 : ZMod (prodQ Q2)) = (u : ZMod (prodQ Q2)) * c := by ring
          rw [this, ← mul_assoc, Units.inv_mul, one_mul]
      }
      have hcnt : ∀ b2 : ZMod (prodQ Q2), countSub Q2 (Sr r) b2 = countQ Q2 (Sr r).card (shiftEquiv b2) := by
        intro b2
        unfold countQ countSub
        nth_rw 1 [show Sr r = (Finset.Icc 1 (Sr r).card).image (fun j : ℕ => a0 + (j - 1) * P1) from hSr_eq]
        rw [Finset.sum_image]
        · apply Finset.sum_congr rfl; intro j hj
          have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
          have hcast_eq : b2 + ((a0 + (j - 1) * P1 : ℕ) : ZMod (prodQ Q2)) =
              (u : ZMod (prodQ Q2)) * (shiftEquiv b2 + (j : ZMod (prodQ Q2))) := by
            simp only [shiftEquiv, Equiv.coe_fn_mk, mul_add]
            rw [← mul_assoc, Units.mul_inv, one_mul, hu_eq]
            have hcast : (((j - 1 : ℕ) : ZMod (prodQ Q2)) + 1) = (j : ZMod (prodQ Q2)) := by
              conv_rhs => rw [← Nat.sub_add_cancel hj1]
              push_cast; rfl
            push_cast; rw [← hcast]; ring
          have hu_mul : IsUnit ((u : ZMod (prodQ Q2)) * (shiftEquiv b2 + (j : ZMod (prodQ Q2)))) ↔
              IsUnit (shiftEquiv b2 + (j : ZMod (prodQ Q2))) :=
            ⟨fun h => by simpa [← mul_assoc] using u⁻¹.isUnit.mul h, fun h => u.isUnit.mul h⟩
          simp only [hcast_eq, hu_mul]
          by_cases h : IsUnit (shiftEquiv b2 + (j : ZMod (prodQ Q2))) <;> simp [h]
        · intro j1 hj1 j2 hj2 heq
          simp only [Finset.mem_coe, Finset.mem_Icc] at hj1 hj2
          dsimp only at heq
          have hmul : (j1 - 1) * P1 = (j2 - 1) * P1 := by omega
          have := Nat.eq_of_mul_eq_mul_right hP1_pos hmul
          omega
      have heq : (1 / (prodQ Q2 : ℝ)) * ∑ b2 : ZMod (prodQ Q2),
          (countSub Q2 (Sr r) b2 - ((Sr r).card : ℝ) * densQ Q2) ^ K = centMom K Q2 (Sr r).card := by
        rw [centMom_eq_sum_zmod]; congr 1; simp_rw [hcnt]; exact Fintype.sum_equiv shiftEquiv _ _ (fun _ => rfl)
      rw [heq]
      have hcard_le : (Sr r).card ≤ L := by
        calc (Sr r).card ≤ (Finset.Icc 1 L).card := Finset.card_le_card (Finset.filter_subset _ _)
          _ = L := by simp
      exact Finset.le_sup' (f := fun L' => centMom K Q2 L') (Finset.mem_Icc.mpr ⟨Nat.zero_le _, hcard_le⟩)
    have hpt : ∀ b2 : ZMod (prodQ Q2),
        (countQ (Q1 ∪ Q2) L (e.symm (b1, b2)) - (L : ℝ) * (densQ Q1 * densQ Q2)) ^ K ≤
        (2 : ℝ) ^ K * ((P1 : ℝ) ^ (K - 1) *
          ∑ r ∈ U1, (countSub Q2 (Sr r) b2 - ((Sr r).card : ℝ) * densQ Q2) ^ K) +
        (2 : ℝ) ^ K * (P1 : ℝ) ^ K := by
      intro b2
      rw [hcnt_decomp b2]
      have hdecomp : ∑ r ∈ U1, countSub Q2 (Sr r) b2 - (L : ℝ) * (densQ Q1 * densQ Q2) =
          (∑ r ∈ U1, (countSub Q2 (Sr r) b2 - ((Sr r).card : ℝ) * densQ Q2)) +
          (∑ r ∈ U1, (((Sr r).card : ℝ) - (L : ℝ) / P1) * densQ Q2) := by
        simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hU1_card]
        have hP10 : (P1 : ℝ) ≠ 0 := by exact_mod_cast hP1_pos.ne'
        field_simp [hP10]
        ring
      rw [hdecomp]
      have h2 := abs_two_add_pow_le
        (∑ r ∈ U1, (countSub Q2 (Sr r) b2 - ((Sr r).card : ℝ) * densQ Q2))
        (∑ r ∈ U1, (((Sr r).card : ℝ) - (L : ℝ) / P1) * densQ Q2) K hK1
      have hev : ∀ x : ℝ, |x| ^ K = x ^ K := fun x => by simp only [K, pow_mul, sq_abs]
      rw [hev] at h2
      have hsum_bd := sum_pow_le_card_pow U1
        (fun r => countSub Q2 (Sr r) b2 - ((Sr r).card : ℝ) * densQ Q2) K hK1
      have hU1_le_P1 : (U1.card : ℝ) ≤ P1 := by
        have : U1.card ≤ P1 := (Finset.card_le_univ U1).trans (ZMod.card P1).le
        exact_mod_cast this
      have hsum_bd2 : |∑ r ∈ U1, (countSub Q2 (Sr r) b2 - ((Sr r).card : ℝ) * densQ Q2)| ^ K ≤
          (P1 : ℝ) ^ (K - 1) * ∑ r ∈ U1, (countSub Q2 (Sr r) b2 - ((Sr r).card : ℝ) * densQ Q2) ^ K := by
        have hsum_bd' : |∑ r ∈ U1, (countSub Q2 (Sr r) b2 - ((Sr r).card : ℝ) * densQ Q2)| ^ K ≤
            (U1.card : ℝ) ^ (K - 1) * ∑ r ∈ U1, (countSub Q2 (Sr r) b2 - ((Sr r).card : ℝ) * densQ Q2) ^ K := by
          simpa [hev] using hsum_bd
        refine hsum_bd'.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hU1_le_P1 _) ?_)
        exact Finset.sum_nonneg fun _ _ => hK_even.pow_nonneg _
      have herr_pow : |∑ r ∈ U1, (((Sr r).card : ℝ) - (L : ℝ) / P1) * densQ Q2| ^ K ≤ (P1 : ℝ) ^ K :=
        pow_le_pow_left₀ (abs_nonneg _) herr_le K
      nlinarith [pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) K]
    have hP2_pos : (0 : ℝ) < prodQ Q2 := by exact_mod_cast prodQ_pos hQ2
    calc (1 / (prodQ Q2 : ℝ)) * ∑ b2 : ZMod (prodQ Q2),
            (countQ (Q1 ∪ Q2) L (e.symm (b1, b2)) - (L : ℝ) * (densQ Q1 * densQ Q2)) ^ K
        ≤ (1 / (prodQ Q2 : ℝ)) * ∑ b2 : ZMod (prodQ Q2),
            ((2 : ℝ) ^ K * ((P1 : ℝ) ^ (K - 1) *
              ∑ r ∈ U1, (countSub Q2 (Sr r) b2 - ((Sr r).card : ℝ) * densQ Q2) ^ K) +
            (2 : ℝ) ^ K * (P1 : ℝ) ^ K) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum fun b2 _ => hpt b2
      _ = (2 : ℝ) ^ K * (P1 : ℝ) ^ (K - 1) *
            ∑ r ∈ U1, ((1 / (prodQ Q2 : ℝ)) * ∑ b2 : ZMod (prodQ Q2),
              (countSub Q2 (Sr r) b2 - ((Sr r).card : ℝ) * densQ Q2) ^ K) +
          (2 : ℝ) ^ K * (P1 : ℝ) ^ K := by
          rw [Finset.sum_add_distrib, mul_add]
          congr 1
          · rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
            simp_rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro r _
            apply Finset.sum_congr rfl; intro b2 _; ring
          · simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
            field_simp [hP2_pos.ne']
      _ ≤ (2 : ℝ) ^ K * (P1 : ℝ) ^ (K - 1) * ∑ _r ∈ U1, Msup +
          (2 : ℝ) ^ K * (P1 : ℝ) ^ K := by
          gcongr with r hr; exact havg_r r hr
      _ = (2 : ℝ) ^ K * (P1 : ℝ) ^ (K - 1) * (U1.card : ℝ) * Msup +
          (2 : ℝ) ^ K * (P1 : ℝ) ^ K := by simp [mul_assoc]
      _ ≤ (2 : ℝ) ^ K * (P1 : ℝ) ^ (K - 1) * (P1 : ℝ) * Msup +
          (2 : ℝ) ^ K * (P1 : ℝ) ^ K := by
          have hU1_le_P1 : (U1.card : ℝ) ≤ P1 := by
            have : U1.card ≤ P1 := (Finset.card_le_univ U1).trans (ZMod.card P1).le
            exact_mod_cast this
          gcongr
      _ = (2 : ℝ) ^ K * (P1 : ℝ) ^ K * (1 + Msup) := by
          have hpow : (P1 : ℝ) ^ (K - 1) * (P1 : ℝ) = (P1 : ℝ) ^ K := by
            rw [← pow_succ, Nat.sub_add_cancel hK1]
          calc (2 : ℝ) ^ K * (P1 : ℝ) ^ (K - 1) * (P1 : ℝ) * Msup + (2 : ℝ) ^ K * (P1 : ℝ) ^ K
              = (2 : ℝ) ^ K * ((P1 : ℝ) ^ (K - 1) * (P1 : ℝ)) * Msup + (2 : ℝ) ^ K * (P1 : ℝ) ^ K := by ring
            _ = _ := by rw [hpow]; ring
  calc (1 / (P1 : ℝ)) * ∑ b1 : ZMod P1,
          (1 / (prodQ Q2 : ℝ)) * ∑ b2 : ZMod (prodQ Q2),
            (countQ (Q1 ∪ Q2) L (e.symm (b1, b2)) - (L : ℝ) * (densQ Q1 * densQ Q2)) ^ K
      ≤ (1 / (P1 : ℝ)) * ∑ _b1 : ZMod P1, ((2 : ℝ) ^ K * (P1 : ℝ) ^ K * (1 + Msup)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum fun b1 _ => hfor_b1 b1
    _ = (2 : ℝ) ^ K * (P1 : ℝ) ^ K * (1 + Msup) := by
        simp [ZMod.card, (by exact_mod_cast hP1_pos.ne' : (P1 : ℝ) ≠ 0)]
    _ ≤ (2 : ℝ) ^ K * ((4 ^ q0 : ℕ) : ℝ) ^ K * (1 + Msup) := by gcongr

theorem unified_centered_moment_bound (k : ℕ) (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (Q : Finset ℕ), 1 ≤ L → (∀ q ∈ Q, q.Prime) →
        centMom (2 * k) Q L ≤
          C * (L : ℝ) ^ ((k : ℝ) + ε) *
            (1 + ∑ q ∈ Q.filter (fun q => L < q), (1 : ℝ) / q) ^ k := by
  obtain ⟨q0, _, Cmed, hCmed1, hmed⟩ := medium_primes_moment_bound k hk hε
  obtain ⟨Dlog, hDlog_pos, hDlog⟩ := log_pow_le_const_mul_rpow (a := (k : ℝ)) (δ := ε)
    (by positivity) hε
  set K := 2 * k
  set Cmid : ℝ := (2 : ℝ) ^ K * largeMartConst k * (3 ^ k * Dlog) + (2 : ℝ) ^ K * Cmed
  set C1 : ℝ := (2 : ℝ) ^ K * largeMartConst k
  set C2 : ℝ := (2 : ℝ) ^ K * ((2 : ℝ) ^ K * ((4 ^ q0 : ℕ) : ℝ) ^ K * (1 + Cmid))
  refine ⟨C1 + C2, by have := largeMartConst_pos k; positivity, fun L Q hL hQ => ?_⟩
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL_pos : (0 : ℝ) < L := by exact_mod_cast hL
  have hmaxL : max 1 L = L := by omega
  have hsp := centMom_split_large k hk Q hQ L
  set Qlo := Q.filter (fun q => q ≤ L)
  have hQlo : ∀ q ∈ Qlo, q.Prime := fun q hq => hQ q (Finset.mem_filter.mp hq).1
  have hpeel := peel_small_primes k q0 hk Qlo hQlo L
  have hsup_le : (Finset.Icc 0 L).sup' (Finset.nonempty_Icc.mpr (Nat.zero_le L))
      (fun L' => centMom K (Qlo.filter (fun q => q0 ≤ q)) L') ≤
      Cmid * (L : ℝ) ^ ((k : ℝ) + ε) := by
    rw [Finset.sup'_le_iff]
    intro L' hL'
    have hL'_le : L' ≤ L := (Finset.mem_Icc.mp hL').2
    set Qmid := Qlo.filter (fun q => q0 ≤ q)
    have hQmid : ∀ q ∈ Qmid, q.Prime := fun q hq => hQlo q (Finset.mem_filter.mp hq).1
    have hsp' := centMom_split_large k hk Qmid hQmid L'
    have hmed_L' : centMom K (Qmid.filter (fun q => q ≤ L')) L' ≤ Cmed * (L : ℝ) ^ ((k : ℝ) + ε) := by
      have h1 := hmed L' (Qmid.filter (fun q => q ≤ L')) (fun q hq => by
        have hq1 := (Finset.mem_filter.mp hq).1
        have hq2 := (Finset.mem_filter.mp hq).2
        have hq_ge := (Finset.mem_filter.mp hq1).2
        exact ⟨hQmid q hq1, hq_ge, hq2⟩)
      have hmax_le : ((max 1 L' : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast (show max 1 L' ≤ L by omega)
      calc centMom K (Qmid.filter (fun q => q ≤ L')) L'
          ≤ Cmed * ((max 1 L' : ℕ) : ℝ) ^ ((k : ℝ) + ε) := h1
        _ ≤ Cmed * (L : ℝ) ^ ((k : ℝ) + ε) := by gcongr
    have hhi_L' : (1 + (L' : ℝ) * ∑ q ∈ Qmid.filter (fun q => L' < q), (1 : ℝ) / q) ^ k ≤
        3 ^ k * Dlog * (L : ℝ) ^ ((k : ℝ) + ε) := by
      have hsum_le : ∑ q ∈ Qmid.filter (fun q => L' < q), (1 : ℝ) / q ≤ 1 + Real.log (L : ℝ) := by
        have hsub : Qmid.filter (fun q => L' < q) ⊆ Finset.Icc 1 L := by
          intro q hq
          have hq1 := (Finset.mem_filter.mp hq).1
          have hqlo := (Finset.mem_filter.mp hq1).1
          exact Finset.mem_Icc.mpr ⟨(hQmid q hq1).one_le, (Finset.mem_filter.mp hqlo).2⟩
        calc ∑ q ∈ Qmid.filter (fun q => L' < q), (1 : ℝ) / q
            ≤ ∑ n ∈ Finset.Icc 1 L, (1 : ℝ) / n :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
          _ ≤ 1 + Real.log (max 1 L : ℕ) := sum_one_div_Icc_le_one_add_log L
          _ = 1 + Real.log (L : ℝ) := by rw [hmaxL]
      have hbase : 1 + (L' : ℝ) * ∑ q ∈ Qmid.filter (fun q => L' < q), (1 : ℝ) / q ≤
          (L : ℝ) * (3 * Real.log ((L : ℝ) + 10)) := by
        have hlog11 : 1 ≤ Real.log ((L : ℝ) + 10) := by
          have h1 : Real.exp 1 ≤ (L : ℝ) + 10 := by linarith [Real.exp_one_lt_d9]
          exact (Real.le_log_iff_exp_le (by linarith)).mpr h1
        have hlog_mono : Real.log (L : ℝ) ≤ Real.log ((L : ℝ) + 10) :=
          Real.log_le_log hL_pos (by linarith)
        have hL'_leR : (L' : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL'_le
        have hmul : (L' : ℝ) * ∑ q ∈ Qmid.filter (fun q => L' < q), (1 : ℝ) / q ≤
            (L : ℝ) * (1 + Real.log (L : ℝ)) :=
          mul_le_mul hL'_leR hsum_le (Finset.sum_nonneg fun _ _ => by positivity) hL_pos.le
        nlinarith
      calc (1 + (L' : ℝ) * ∑ q ∈ Qmid.filter (fun q => L' < q), (1 : ℝ) / q) ^ k
          ≤ ((L : ℝ) * (3 * Real.log ((L : ℝ) + 10))) ^ k :=
            pow_le_pow_left₀ (by
              have : 0 ≤ (L' : ℝ) * ∑ q ∈ Qmid.filter (fun q => L' < q), (1 : ℝ) / q :=
                mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ => by positivity)
              linarith) hbase k
        _ = (L : ℝ) ^ k * (3 ^ k * (Real.log ((L : ℝ) + 10)) ^ k) := by rw [mul_pow, mul_pow]
        _ = (L : ℝ) ^ k * (3 ^ k * (Real.log ((L : ℝ) + 10)) ^ (k : ℝ)) := by rw [Real.rpow_natCast]
        _ ≤ (L : ℝ) ^ k * (3 ^ k * (Dlog * (L : ℝ) ^ ε)) := by gcongr; exact hDlog (L : ℝ) hL1
        _ = 3 ^ k * Dlog * ((L : ℝ) ^ (k : ℝ) * (L : ℝ) ^ ε) := by rw [Real.rpow_natCast]; ring
        _ = 3 ^ k * Dlog * (L : ℝ) ^ ((k : ℝ) + ε) := by rw [← Real.rpow_add hL_pos]
    have hsp'1 := mul_le_mul_of_nonneg_left hhi_L'
      (mul_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ K) (largeMartConst_pos k).le)
    have hsp'2 := mul_le_mul_of_nonneg_left hmed_L' (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ K)
    calc centMom K Qmid L'
        ≤ (2 : ℝ) ^ K * largeMartConst k *
            (1 + (L' : ℝ) * ∑ q ∈ Qmid.filter (fun q => L' < q), (1 : ℝ) / q) ^ k +
          (2 : ℝ) ^ K * centMom K (Qmid.filter (fun q => q ≤ L')) L' := hsp'
      _ ≤ (2 : ℝ) ^ K * largeMartConst k * (3 ^ k * Dlog * (L : ℝ) ^ ((k : ℝ) + ε)) +
          (2 : ℝ) ^ K * (Cmed * (L : ℝ) ^ ((k : ℝ) + ε)) := add_le_add hsp'1 hsp'2
      _ = Cmid * (L : ℝ) ^ ((k : ℝ) + ε) := by simp only [Cmid]; ring
  set S_hi : ℝ := ∑ q ∈ Q.filter (fun q => L < q), (1 : ℝ) / q
  have hShi_nn : 0 ≤ S_hi := Finset.sum_nonneg fun _ _ => by positivity
  have h1Shi_ge1 : (1 : ℝ) ≤ (1 + S_hi) ^ k := one_le_pow₀ (by linarith)
  have hL_pow_ge1 : (1 : ℝ) ≤ (L : ℝ) ^ ((k : ℝ) + ε) := Real.one_le_rpow hL1 (by positivity)
  have hpart1 : C1 * (1 + (L : ℝ) * S_hi) ^ k ≤
      C1 * (L : ℝ) ^ ((k : ℝ) + ε) * (1 + S_hi) ^ k := by
    have h1 : 1 + (L : ℝ) * S_hi ≤ (L : ℝ) * (1 + S_hi) := by nlinarith
    have h2 : (1 + (L : ℝ) * S_hi) ^ k ≤ (L : ℝ) ^ k * (1 + S_hi) ^ k := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) h1 k
    have h3 : (L : ℝ) ^ k ≤ (L : ℝ) ^ ((k : ℝ) + ε) := by
      rw [← Real.rpow_natCast (L : ℝ) k]
      exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    have hC1_nn : 0 ≤ C1 := by have := largeMartConst_pos k; positivity
    calc C1 * (1 + (L : ℝ) * S_hi) ^ k
        ≤ C1 * ((L : ℝ) ^ k * (1 + S_hi) ^ k) := mul_le_mul_of_nonneg_left h2 hC1_nn
      _ ≤ C1 * ((L : ℝ) ^ ((k : ℝ) + ε) * (1 + S_hi) ^ k) := by gcongr
      _ = C1 * (L : ℝ) ^ ((k : ℝ) + ε) * (1 + S_hi) ^ k := by ring
  have hpart2 : (2 : ℝ) ^ K * centMom K Qlo L ≤
      C2 * (L : ℝ) ^ ((k : ℝ) + ε) * (1 + S_hi) ^ k := by
    have hpeel2 : centMom K Qlo L ≤
        (2 : ℝ) ^ K * ((4 ^ q0 : ℕ) : ℝ) ^ K * (1 + Cmid) * (L : ℝ) ^ ((k : ℝ) + ε) := by
      calc centMom K Qlo L
          ≤ (2 : ℝ) ^ K * ((4 ^ q0 : ℕ) : ℝ) ^ K *
              (1 + (Finset.Icc 0 L).sup' (Finset.nonempty_Icc.mpr (Nat.zero_le L))
                (fun L' => centMom K (Qlo.filter (fun q => q0 ≤ q)) L')) := hpeel
        _ ≤ (2 : ℝ) ^ K * ((4 ^ q0 : ℕ) : ℝ) ^ K * (1 + Cmid * (L : ℝ) ^ ((k : ℝ) + ε)) := by
            gcongr
        _ ≤ (2 : ℝ) ^ K * ((4 ^ q0 : ℕ) : ℝ) ^ K * ((1 + Cmid) * (L : ℝ) ^ ((k : ℝ) + ε)) := by
            gcongr; nlinarith
        _ = _ := by ring
    have hC2_eq : (2 : ℝ) ^ K * ((2 : ℝ) ^ K * ((4 ^ q0 : ℕ) : ℝ) ^ K * (1 + Cmid) *
        (L : ℝ) ^ ((k : ℝ) + ε)) = C2 * (L : ℝ) ^ ((k : ℝ) + ε) := by simp only [C2]; ring
    calc (2 : ℝ) ^ K * centMom K Qlo L
        ≤ (2 : ℝ) ^ K * ((2 : ℝ) ^ K * ((4 ^ q0 : ℕ) : ℝ) ^ K * (1 + Cmid) *
            (L : ℝ) ^ ((k : ℝ) + ε)) := by gcongr
      _ = C2 * (L : ℝ) ^ ((k : ℝ) + ε) := hC2_eq
      _ ≤ C2 * (L : ℝ) ^ ((k : ℝ) + ε) * (1 + S_hi) ^ k :=
          le_mul_of_one_le_right (by have := largeMartConst_pos k; positivity) h1Shi_ge1
  calc centMom K Q L
      ≤ C1 * (1 + (L : ℝ) * S_hi) ^ k + (2 : ℝ) ^ K * centMom K Qlo L := hsp
    _ ≤ C1 * (L : ℝ) ^ ((k : ℝ) + ε) * (1 + S_hi) ^ k +
        C2 * (L : ℝ) ^ ((k : ℝ) + ε) * (1 + S_hi) ^ k := add_le_add hpart1 hpart2
    _ = (C1 + C2) * (L : ℝ) ^ ((k : ℝ) + ε) * (1 + S_hi) ^ k := by ring

end MediumAndFullMoment


end Mod3


section Mod4
open Finset Real Nat
open scoped Classical


section CombinatorialBonferroni

lemma alt_sum_choose_eq {n : ℕ} (hn : 1 ≤ n) (M : ℕ) :
    ∑ j ∈ Finset.range (M + 1), (-1 : ℝ) ^ j * (Nat.choose n j : ℝ) =
      (-1 : ℝ) ^ M * (Nat.choose (n - 1) M : ℝ) := by
  induction M with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have hpas : Nat.choose n (m + 1) = Nat.choose (n - 1) m + Nat.choose (n - 1) (m + 1) := by
      have hn_eq : n = (n - 1) + 1 := (Nat.sub_add_cancel hn).symm
      conv_lhs => rw [hn_eq]
      rw [Nat.choose_succ_succ]
    rw [hpas]
    push_cast
    rw [pow_succ]
    ring

lemma sum_powerset_card_le_eq (S : Finset ℕ) (M : ℕ) :
    ∑ T ∈ S.powerset.filter (fun T => T.card ≤ M), (-1 : ℝ) ^ T.card =
      ∑ j ∈ Finset.range (M + 1), (-1 : ℝ) ^ j * (Nat.choose S.card j : ℝ) := by
  have hmaps : ∀ T ∈ S.powerset.filter (fun T => T.card ≤ M), T.card ∈ Finset.range (M + 1) := by
    intro T hT
    rw [Finset.mem_range]
    have := (Finset.mem_filter.mp hT).2
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro j hj
  have hjM : j ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hfilt : (S.powerset.filter (fun T => T.card ≤ M)).filter (fun T => T.card = j) =
      S.powersetCard j := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hTS, _⟩, hcard⟩; exact ⟨hTS, hcard⟩
    · rintro ⟨hTS, hcard⟩; exact ⟨⟨hTS, hcard ▸ hjM⟩, hcard⟩
  rw [hfilt]
  have hconst : ∀ T ∈ S.powersetCard j, (-1 : ℝ) ^ T.card = (-1 : ℝ) ^ j := by
    intro T hT; rw [(Finset.mem_powersetCard.mp hT).2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul, mul_comm]

lemma bonferroni_upper (S : Finset ℕ) (r : ℕ) :
    (if S = ∅ then (1 : ℝ) else 0) ≤
      ∑ T ∈ S.powerset.filter (fun T => T.card ≤ 2 * r), (-1 : ℝ) ^ T.card := by
  rw [sum_powerset_card_le_eq]
  by_cases hS : S = ∅
  · subst hS
    rw [if_pos rfl]
    rw [Finset.card_empty, Finset.sum_range_succ']
    have h0 : ∑ k ∈ Finset.range (2 * r), (-1 : ℝ) ^ (k + 1) * (Nat.choose 0 (k + 1) : ℝ) = 0 := by
      apply Finset.sum_eq_zero; intro k _; simp
    rw [h0]; simp
  · rw [if_neg hS]
    have hpos : 1 ≤ S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
    rw [alt_sum_choose_eq hpos (2 * r)]
    have heven : (-1 : ℝ) ^ (2 * r) = 1 := by rw [pow_mul]; norm_num
    rw [heven, one_mul]
    exact Nat.cast_nonneg _

lemma bonferroni_lower (S : Finset ℕ) (r : ℕ) :
    ∑ T ∈ S.powerset.filter (fun T => T.card ≤ 2 * r + 1), (-1 : ℝ) ^ T.card ≤
      (if S = ∅ then (1 : ℝ) else 0) := by
  rw [sum_powerset_card_le_eq]
  by_cases hS : S = ∅
  · subst hS
    rw [if_pos rfl]
    rw [Finset.card_empty, Finset.sum_range_succ']
    have h0 : ∑ k ∈ Finset.range (2 * r + 1), (-1 : ℝ) ^ (k + 1) * (Nat.choose 0 (k + 1) : ℝ) = 0 := by
      apply Finset.sum_eq_zero; intro k _; simp
    rw [h0]; simp
  · rw [if_neg hS]
    have hpos : 1 ≤ S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
    rw [alt_sum_choose_eq hpos (2 * r + 1)]
    have hodd : (-1 : ℝ) ^ (2 * r + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    rw [hodd, neg_one_mul]
    linarith [Nat.cast_nonneg (α := ℝ) (Nat.choose (S.card - 1) (2 * r + 1))]

lemma factorial_mul_sum_powersetCard_prod_le (Q : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ q ∈ Q, 0 ≤ f q) (j : ℕ) :
    (j.factorial : ℝ) * ∑ T ∈ Q.powersetCard j, ∏ q ∈ T, f q ≤ (∑ q ∈ Q, f q) ^ j := by
  induction j with
  | zero => simp
  | succ m ih =>
    have hstep : ((m + 1 : ℕ) : ℝ) * ∑ T ∈ Q.powersetCard (m + 1), ∏ q ∈ T, f q ≤
        (∑ q ∈ Q, f q) * ∑ T' ∈ Q.powersetCard m, ∏ q ∈ T', f q := by
      have hlhs : ((m + 1 : ℕ) : ℝ) * ∑ T ∈ Q.powersetCard (m + 1), ∏ q ∈ T, f q =
          ∑ T ∈ Q.powersetCard (m + 1), ∑ q ∈ T, f q * ∏ p ∈ T.erase q, f p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro T hT
        have hcard : T.card = m + 1 := (Finset.mem_powersetCard.mp hT).2
        have hterm : ∀ q ∈ T, f q * ∏ p ∈ T.erase q, f p = ∏ p ∈ T, f p :=
          fun q hq => Finset.mul_prod_erase T f hq
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, hcard, nsmul_eq_mul]
      rw [hlhs]
      have hswap : ∑ T ∈ Q.powersetCard (m + 1), ∑ q ∈ T, f q * ∏ p ∈ T.erase q, f p =
          ∑ q ∈ Q, f q * ∑ T' ∈ (Q.erase q).powersetCard m, ∏ p ∈ T', f p := by
        trans ∑ T ∈ Q.powersetCard (m + 1), ∑ q ∈ Q,
            if q ∈ T then f q * ∏ p ∈ T.erase q, f p else 0
        · apply Finset.sum_congr rfl; intro T hT
          rw [← Finset.sum_filter]
          apply Finset.sum_congr _ (fun _ _ => rfl)
          ext q; simp only [Finset.mem_filter]
          exact ⟨fun hq => ⟨(Finset.mem_powersetCard.mp hT).1 hq, hq⟩, fun h => h.2⟩
        · rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro q hq
          rw [← Finset.sum_filter, Finset.mul_sum]
          refine Finset.sum_bij (fun T _ => T.erase q) ?_ ?_ ?_ ?_
          · intro T hT
            simp only [Finset.mem_filter, Finset.mem_powersetCard] at hT ⊢
            refine ⟨Finset.erase_subset_erase q hT.1.1, ?_⟩
            rw [Finset.card_erase_of_mem hT.2, hT.1.2]; omega
          · intro T1 hT1 T2 hT2 heq
            simp only [Finset.mem_filter] at hT1 hT2
            rw [← Finset.insert_erase hT1.2, ← Finset.insert_erase hT2.2, heq]
          · intro T' hT'
            simp only [Finset.mem_powersetCard] at hT'
            have hqnot : q ∉ T' := fun h => (Finset.mem_erase.mp (hT'.1 h)).1 rfl
            refine ⟨insert q T', ?_, Finset.erase_insert hqnot⟩
            simp only [Finset.mem_filter, Finset.mem_powersetCard]
            refine ⟨⟨Finset.insert_subset hq (hT'.1.trans (Finset.erase_subset q Q)), ?_⟩,
              Finset.mem_insert_self q T'⟩
            rw [Finset.card_insert_of_notMem hqnot, hT'.2]
          · intro T _; rfl
      rw [hswap, Finset.sum_mul]
      apply Finset.sum_le_sum; intro q hq
      apply mul_le_mul_of_nonneg_left _ (hf q hq)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.powersetCard_mono (Finset.erase_subset q Q)
      · intro T' hT' _
        exact Finset.prod_nonneg fun p hp => hf p ((Finset.mem_powersetCard.mp hT').1 hp)
    rw [Nat.factorial_succ, Nat.cast_mul, pow_succ, mul_comm ((∑ q ∈ Q, f q) ^ m)]
    calc ((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ) * ∑ T ∈ Q.powersetCard (m + 1), ∏ q ∈ T, f q
        = (m.factorial : ℝ) * (((m + 1 : ℕ) : ℝ) * ∑ T ∈ Q.powersetCard (m + 1), ∏ q ∈ T, f q) := by ring
      _ ≤ (m.factorial : ℝ) * ((∑ q ∈ Q, f q) * ∑ T' ∈ Q.powersetCard m, ∏ q ∈ T', f q) :=
          mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg _)
      _ = (∑ q ∈ Q, f q) * ((m.factorial : ℝ) * ∑ T' ∈ Q.powersetCard m, ∏ q ∈ T', f q) := by ring
      _ ≤ (∑ q ∈ Q, f q) * (∑ q ∈ Q, f q) ^ m :=
          mul_le_mul_of_nonneg_left ih (Finset.sum_nonneg hf)

lemma pow_div_factorial_le_exp_pow (U : ℝ) (hU : 0 ≤ U) (j : ℕ) (hj : 1 ≤ j) :
    U ^ j / (j.factorial : ℝ) ≤ (Real.exp 1 * U / j) ^ j := by
  have hj_pos : (0 : ℝ) < j := by exact_mod_cast hj
  have hexp : (j : ℝ) ^ j / (j.factorial : ℝ) ≤ Real.exp (j : ℝ) := by
    have hsum := Real.sum_le_exp_of_nonneg hj_pos.le (j + 1)
    have hmem : j ∈ Finset.range (j + 1) := Finset.mem_range.mpr (Nat.lt_succ_self j)
    have hsingle := Finset.single_le_sum (f := fun k => (j : ℝ) ^ k / (k.factorial : ℝ))
      (fun k _ => by positivity) hmem
    exact hsingle.trans hsum
  have hexp_eq : Real.exp (j : ℝ) = (Real.exp 1) ^ j := by
    rw [← Real.exp_nat_mul, mul_one]
  rw [hexp_eq] at hexp
  have h1 : U ^ j / (j.factorial : ℝ) = (U / j) ^ j * ((j : ℝ) ^ j / (j.factorial : ℝ)) := by
    rw [div_pow]; field_simp [hj_pos.ne']
  rw [h1]
  calc (U / j) ^ j * ((j : ℝ) ^ j / (j.factorial : ℝ))
      ≤ (U / j) ^ j * (Real.exp 1) ^ j := mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = (Real.exp 1 * U / j) ^ j := by rw [← mul_pow]; congr 1; ring

lemma sum_half_pow_tail (M N : ℕ) :
    ∑ j ∈ Finset.Icc (M + 1) N, ((1 : ℝ) / 2) ^ j ≤ ((1 : ℝ) / 2) ^ M := by
  by_cases hMN : M + 1 ≤ N
  · have hgeom : ∀ t : ℕ, ∑ k ∈ Finset.range t, ((1 : ℝ) / 2) ^ k ≤ 2 := by
      intro t
      induction t with
      | zero => norm_num
      | succ t ih =>
        rw [Finset.sum_range_succ']
        have h1 : ∑ k ∈ Finset.range t, ((1 : ℝ) / 2) ^ (k + 1) =
            (1 / 2 : ℝ) * ∑ k ∈ Finset.range t, ((1 : ℝ) / 2) ^ k := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; rw [pow_succ, mul_comm]
        rw [h1]
        linarith
    have hshift : ∑ j ∈ Finset.Icc (M + 1) N, ((1 : ℝ) / 2) ^ j =
        ((1 : ℝ) / 2) ^ (M + 1) * ∑ k ∈ Finset.range (N - M), ((1 : ℝ) / 2) ^ k := by
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun j _ => j - (M + 1)) ?_ ?_ ?_ ?_
      · intro j hj; simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢; omega
      · intro j1 hj1 j2 hj2 heq; simp only [Finset.mem_Icc] at hj1 hj2; omega
      · intro k hk
        simp only [Finset.mem_range] at hk
        refine ⟨M + 1 + k, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        rw [← pow_add, show M + 1 + (j - (M + 1)) = j by omega]
    rw [hshift]
    calc ((1 : ℝ) / 2) ^ (M + 1) * ∑ k ∈ Finset.range (N - M), ((1 : ℝ) / 2) ^ k
        ≤ ((1 : ℝ) / 2) ^ (M + 1) * 2 := by gcongr; exact hgeom (N - M)
      _ = ((1 : ℝ) / 2) ^ M := by rw [pow_succ]; ring
  · rw [Finset.Icc_eq_empty hMN, Finset.sum_empty]
    positivity

end CombinatorialBonferroni

section BrunPureSieve

def localCount (D : Finset ℕ) (q : ℕ) : ℕ :=
  (D.image (fun d : ℕ => -(d : ZMod q))).card

lemma localCount_le_card (D : Finset ℕ) (q : ℕ) : localCount D q ≤ D.card :=
  Finset.card_image_le

lemma localCount_le_q (D : Finset ℕ) (q : ℕ) (hq : 0 < q) : localCount D q ≤ q := by
  have : NeZero q := ⟨hq.ne'⟩
  calc localCount D q ≤ (Finset.univ : Finset (ZMod q)).card := Finset.card_le_univ _
    _ = q := ZMod.card q

lemma card_bad_residues_prodQ (D T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime) [NeZero (prodQ T)] :
    (Finset.univ.filter (fun r : ZMod (prodQ T) =>
      ∀ q ∈ T, ∃ d ∈ D, (r.val + d : ℕ) % q = 0)).card =
      ∏ q ∈ T, localCount D q := by
  suffices ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime) → ∀ [NeZero (prodQ S)],
      (Finset.univ.filter (fun r : ZMod (prodQ S) =>
        ∀ q ∈ S, ∃ d ∈ D, (r.val + d : ℕ) % q = 0)).card =
        ∏ q ∈ S, localCount D q from this T hT
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _ _
    have h1 : Finset.univ.filter (fun r : ZMod (prodQ ∅) =>
        ∀ q ∈ (∅ : Finset ℕ), ∃ d ∈ D, (r.val + d : ℕ) % q = 0) = Finset.univ := by
      ext r; simp
    rw [h1, Finset.prod_empty, Finset.card_univ, ZMod.card]
    rfl
  | @insert q T hqnot ih =>
    intro hT _
    have hq : q.Prime := hT q (Finset.mem_insert_self q T)
    have hT' : ∀ p ∈ T, p.Prime := fun p hp => hT p (Finset.mem_insert_of_mem hp)
    have : NeZero q := ⟨hq.ne_zero⟩
    have : NeZero (prodQ T) := ⟨prodQ_ne_zero hT'⟩
    let e := crtInsert hq hT' hqnot
    rw [Finset.prod_insert hqnot, ← ih hT']
    set Sq := D.image (fun d : ℕ => -(d : ZMod q))
    set ST := Finset.univ.filter (fun r : ZMod (prodQ T) =>
        ∀ p ∈ T, ∃ d ∈ D, (r.val + d : ℕ) % p = 0)
    set Sfull := Finset.univ.filter (fun r : ZMod (prodQ (insert q T)) =>
        ∀ p ∈ insert q T, ∃ d ∈ D, (r.val + d : ℕ) % p = 0)
    have hmod_eq_q : ∀ r : ZMod (prodQ (insert q T)),
        ((r.val : ZMod q)) = (e r).1 := by
      intro r
      have h1 := congrArg Prod.fst (map_natCast e r.val)
      simp only [Prod.fst_natCast, ZMod.natCast_zmod_val] at h1
      exact h1.symm
    have hmod_eq_T : ∀ r : ZMod (prodQ (insert q T)), ∀ p ∈ T,
        ((r.val : ZMod p)) = (((e r).2).val : ZMod p) := by
      intro r p hp
      have hp_dvd : p ∣ prodQ T := Finset.dvd_prod_of_mem id hp
      have h2 := congrArg Prod.snd (map_natCast e r.val)
      simp only [Prod.snd_natCast, ZMod.natCast_zmod_val] at h2
      have hcast : ZMod.castHom hp_dvd (ZMod p) (e r).2 = (r.val : ZMod p) := by
        rw [h2]; exact map_natCast _ _
      have hcast2 : ZMod.castHom hp_dvd (ZMod p) (e r).2 = (((e r).2).val : ZMod p) := by
        conv_lhs => rw [← ZMod.natCast_zmod_val (e r).2]
        exact map_natCast _ _
      exact hcast.symm.trans hcast2
    have hcond_iff : ∀ r : ZMod (prodQ (insert q T)),
        r ∈ Sfull ↔ (e r).1 ∈ Sq ∧ (e r).2 ∈ ST := by
      intro r
      simp only [Sfull, Sq, ST, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_insert]
      constructor
      · intro hr
        constructor
        · obtain ⟨d, hd, hmod⟩ := hr q (Or.inl rfl)
          refine ⟨d, hd, ?_⟩
          have h0 : ((r.val + d : ℕ) : ZMod q) = 0 :=
            (ZMod.natCast_eq_zero_iff _ q).mpr (Nat.dvd_of_mod_eq_zero hmod)
          rw [Nat.cast_add, hmod_eq_q] at h0
          exact (eq_neg_of_add_eq_zero_left h0).symm
        · intro p hp
          obtain ⟨d, hd, hmod⟩ := hr p (Or.inr hp)
          refine ⟨d, hd, ?_⟩
          have h0 : ((r.val + d : ℕ) : ZMod p) = 0 :=
            (ZMod.natCast_eq_zero_iff _ p).mpr (Nat.dvd_of_mod_eq_zero hmod)
          rw [Nat.cast_add, hmod_eq_T r p hp, ← Nat.cast_add] at h0
          exact Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ p).mp h0)
      · rintro ⟨⟨dq, hdq, hqeq⟩, hTcond⟩ p (hpq | hp)
        · rw [hpq]
          refine ⟨dq, hdq, ?_⟩
          have h0 : ((r.val + dq : ℕ) : ZMod q) = 0 := by
            rw [Nat.cast_add, hmod_eq_q, ← hqeq, neg_add_cancel]
          exact Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ q).mp h0)
        · obtain ⟨dp, hdp, hmod⟩ := hTcond p hp
          refine ⟨dp, hdp, ?_⟩
          have h0 : ((((e r).2).val + dp : ℕ) : ZMod p) = 0 :=
            (ZMod.natCast_eq_zero_iff _ p).mpr (Nat.dvd_of_mod_eq_zero hmod)
          rw [Nat.cast_add, ← hmod_eq_T r p hp, ← Nat.cast_add] at h0
          exact Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ p).mp h0)
    change Sfull.card = Sq.card * ST.card
    rw [← Finset.card_product]
    apply Finset.card_bij (fun r _ => e r)
    · intro r hr; exact Finset.mem_product.mpr ((hcond_iff r).mp hr)
    · intro r1 _ r2 _ heq; exact e.injective heq
    · intro p hp
      refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
      rw [hcond_iff, e.apply_symm_apply]
      exact Finset.mem_product.mp hp

lemma avg_zmod_tuple_coprime_eq_prod (D Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime) [NeZero (prodQ Q)] :
    (1 / (prodQ Q : ℝ)) *
      ∑ b : ZMod (prodQ Q), (if ∀ d ∈ D, IsUnit (b + (d : ZMod (prodQ Q))) then (1 : ℝ) else 0) =
      ∏ q ∈ Q, (1 - (localCount D q : ℝ) / q) := by
  suffices ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime) → ∀ [NeZero (prodQ S)],
      (1 / (prodQ S : ℝ)) *
        ∑ b : ZMod (prodQ S), (if ∀ d ∈ D, IsUnit (b + (d : ZMod (prodQ S))) then (1 : ℝ) else 0) =
        ∏ q ∈ S, (1 - (localCount D q : ℝ) / q) from this Q hQ
  intro Q
  induction Q using Finset.induction_on with
  | empty =>
    intro _ _
    have h1 : ∀ b : ZMod (prodQ ∅), ∀ d ∈ D, IsUnit (b + (d : ZMod (prodQ ∅))) := fun b d _ => by
      have : Subsingleton (ZMod (prodQ ∅)) := show Subsingleton (ZMod 1) from inferInstance
      rw [Subsingleton.elim (b + (d : ZMod (prodQ ∅))) 1]; exact isUnit_one
    have hsum : ∑ b : ZMod (prodQ ∅),
        (if ∀ d ∈ D, IsUnit (b + (d : ZMod (prodQ ∅))) then (1 : ℝ) else 0) = 1 := by
      rw [Finset.sum_congr rfl (fun b _ => if_pos (h1 b)), Finset.sum_const, Finset.card_univ, ZMod.card]
      simp [prodQ]
    rw [hsum]; simp [prodQ]
  | @insert q Q hqnot ih =>
    intro hQ _
    have hq : q.Prime := hQ q (Finset.mem_insert_self q Q)
    have hQ' : ∀ p ∈ Q, p.Prime := fun p hp => hQ p (Finset.mem_insert_of_mem hp)
    have : Fact q.Prime := ⟨hq⟩
    have : NeZero q := ⟨hq.ne_zero⟩
    have : NeZero (prodQ Q) := ⟨prodQ_ne_zero hQ'⟩
    let e := crtInsert hq hQ' hqnot
    rw [avg_zmod_insert hq hQ' hqnot, Finset.prod_insert hqnot, ← ih hQ']
    have hinner : ∀ b : ZMod (prodQ Q),
        (1 / (q : ℝ)) * ∑ r : ZMod q,
          (if ∀ d ∈ D, IsUnit ((crtInsert hq hQ' hqnot).symm (r, b) + (d : ZMod (prodQ (insert q Q)))) then (1 : ℝ) else 0) =
        (1 - (localCount D q : ℝ) / q) *
          (if ∀ d ∈ D, IsUnit (b + (d : ZMod (prodQ Q))) then (1 : ℝ) else 0) := by
      intro b
      have hcond : ∀ r : ZMod q,
          (∀ d ∈ D, IsUnit ((crtInsert hq hQ' hqnot).symm (r, b) + (d : ZMod (prodQ (insert q Q))))) ↔
          (r ∉ D.image (fun d : ℕ => -(d : ZMod q))) ∧ (∀ d ∈ D, IsUnit (b + (d : ZMod (prodQ Q)))) := by
        intro r
        have h1 : ∀ d ∈ D, IsUnit ((crtInsert hq hQ' hqnot).symm (r, b) + (d : ZMod (prodQ (insert q Q)))) ↔
            r ≠ -(d : ZMod q) ∧ IsUnit (b + (d : ZMod (prodQ Q))) := by
          intro d _
          rw [isUnit_crt_iff e]
          simp only [e, map_add, map_natCast, RingEquiv.apply_symm_apply, Prod.fst_add, Prod.snd_add,
            Prod.fst_natCast, Prod.snd_natCast, isUnit_iff_ne_zero]
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨fun h => h1 (by rw [h, neg_add_cancel]), h2⟩
          · rintro ⟨h1, h2⟩; exact ⟨fun h => h1 (eq_neg_of_add_eq_zero_left h), h2⟩
        simp only [Finset.mem_image, not_exists, not_and]
        constructor
        · intro hall
          exact ⟨fun d hd heq => (h1 d hd).mp (hall d hd) |>.1 heq.symm,
            fun d hd => ((h1 d hd).mp (hall d hd)).2⟩
        · rintro ⟨hnot, hb⟩ d hd
          exact (h1 d hd).mpr ⟨fun heq => hnot d hd heq.symm, hb d hd⟩
      have hsum_eq : ∑ r : ZMod q,
          (if ∀ d ∈ D, IsUnit ((crtInsert hq hQ' hqnot).symm (r, b) + (d : ZMod (prodQ (insert q Q)))) then (1 : ℝ) else 0) =
          ∑ r : ZMod q,
            (if (r ∉ D.image (fun d : ℕ => -(d : ZMod q))) ∧ (∀ d ∈ D, IsUnit (b + (d : ZMod (prodQ Q)))) then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl; intro r _
        by_cases hc : (r ∉ D.image (fun d : ℕ => -(d : ZMod q))) ∧ (∀ d ∈ D, IsUnit (b + (d : ZMod (prodQ Q))))
        · rw [if_pos ((hcond r).mpr hc), if_pos hc]
        · rw [if_neg (fun h => hc ((hcond r).mp h)), if_neg hc]
      rw [hsum_eq]
      by_cases hb : ∀ d ∈ D, IsUnit (b + (d : ZMod (prodQ Q)))
      · have hsum2 : ∑ r : ZMod q,
            (if (r ∉ D.image (fun d : ℕ => -(d : ZMod q))) ∧
                (∀ d ∈ D, IsUnit (b + (d : ZMod (prodQ Q)))) then (1 : ℝ) else 0) =
            ∑ r : ZMod q,
              (if r ∉ D.image (fun d : ℕ => -(d : ZMod q)) then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl; intro r _
          by_cases h : r ∉ D.image (fun d : ℕ => -(d : ZMod q))
          · rw [if_pos ⟨h, hb⟩, if_pos h]
          · rw [if_neg (fun h' => h h'.1), if_neg h]
        rw [hsum2, if_pos hb, mul_one, Finset.sum_boole]
        have hcard : (Finset.univ.filter (fun r : ZMod q => r ∉ D.image (fun d : ℕ => -(d : ZMod q)))).card =
            q - localCount D q := by
          have hcompl : Finset.univ.filter (fun r : ZMod q => r ∉ D.image (fun d : ℕ => -(d : ZMod q))) =
              Finset.univ \ D.image (fun d : ℕ => -(d : ZMod q)) := by
            ext r; simp
          rw [hcompl, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, ZMod.card]
          rfl
        rw [hcard, Nat.cast_sub (localCount_le_q D q hq.pos)]
        have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
        field_simp [hq0]
      · have hsum0 : ∑ r : ZMod q,
            (if (r ∉ D.image (fun d : ℕ => -(d : ZMod q))) ∧
                (∀ d ∈ D, IsUnit (b + (d : ZMod (prodQ Q)))) then (1 : ℝ) else 0) = 0 := by
          apply Finset.sum_eq_zero; intro r _
          rw [if_neg (fun h => hb h.2)]
        rw [hsum0, if_neg hb, mul_zero, mul_zero]
    simp_rw [hinner, ← Finset.mul_sum]
    ring

lemma brun_tuple_count_close (X r : ℕ) (hX : 1 ≤ X) (D Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime)
    [NeZero (prodQ Q)]
    (hUr : 6 * ((D.card : ℝ) * ∑ q ∈ Q, (1 : ℝ) / q) ≤ (2 * r + 1 : ℕ)) :
    |(1 / (X : ℝ)) *
        ∑ a ∈ Finset.Ico X (2 * X),
          (if ∀ d ∈ D, (a + d).Coprime (prodQ Q) then (1 : ℝ) else 0) -
      (1 / (prodQ Q : ℝ)) *
        ∑ b : ZMod (prodQ Q),
          (if ∀ d ∈ D, IsUnit (b + (d : ZMod (prodQ Q))) then (1 : ℝ) else 0)| ≤
      ((1 : ℝ) / 2) ^ (2 * r) +
        ((2 * r + 2 : ℕ) : ℝ) * ((max 1 (D.card * Q.card) : ℕ) : ℝ) ^ (2 * r + 1) / (X : ℝ) := by
  have hX_pos : (0 : ℝ) < X := by exact_mod_cast hX
  rw [avg_zmod_tuple_coprime_eq_prod D Q hQ]
  let f : ℕ → ℝ := fun q => (localCount D q : ℝ) / q
  have hf_nn : ∀ q ∈ Q, 0 ≤ f q := fun q _ => by simp only [f]; positivity
  -- Expand ∏_{q ∈ Q} (1 - f q) = ∑_{T ⊆ Q} (-1)^|T| ∏_{q ∈ T} f q
  have hprod_expand : ∏ q ∈ Q, (1 - f q) =
      ∑ T ∈ Q.powerset, (-1 : ℝ) ^ T.card * ∏ q ∈ T, f q := by
    have h := Finset.prod_add (s := Q) (f := fun q => -f q) (g := fun _ => (1 : ℝ))
    simp only [Finset.prod_const_one, mul_one, Finset.prod_neg] at h
    simpa [sub_eq_add_neg, add_comm] using h
  -- For any M, compare ∑_{a ∈ Ico X (2X)} ∑_{T ⊆ S(a), |T| ≤ M} (-1)^|T| with X * ∑_{T ⊆ Q, |T| ≤ M} (-1)^|T| ∏ f
  let S : ℕ → Finset ℕ := fun a => Q.filter (fun q => ∃ d ∈ D, q ∣ (a + d))
  have hcop_iff : ∀ a : ℕ, (∀ d ∈ D, (a + d).Coprime (prodQ Q)) ↔ S a = ∅ := by
    intro a
    rw [Finset.eq_empty_iff_forall_notMem]
    simp only [S, Finset.mem_filter, not_and, not_exists]
    constructor
    · intro h q hq d hd hdvd
      have hc := (Nat.coprime_prod_right_iff.mp (h d hd)) q hq
      exact (hQ q hq).coprime_iff_not_dvd.mp hc.symm hdvd
    · intro h d hd
      apply Nat.coprime_prod_right_iff.mpr; intro q hq
      exact ((hQ q hq).coprime_iff_not_dvd.mpr (h q hq d hd)).symm
  have htrunc_err : ∀ M : ℕ,
      |(1 / (X : ℝ)) *
          ∑ a ∈ Finset.Ico X (2 * X),
            ∑ T ∈ (S a).powerset.filter (fun T => T.card ≤ M), (-1 : ℝ) ^ T.card -
        ∑ T ∈ Q.powerset.filter (fun T => T.card ≤ M), (-1 : ℝ) ^ T.card * ∏ q ∈ T, f q| ≤
        (1 / (X : ℝ)) * ∑ T ∈ Q.powerset.filter (fun T => T.card ≤ M), ((D.card : ℝ) ^ T.card) := by
    intro M
    have hswap : ∑ a ∈ Finset.Ico X (2 * X),
        ∑ T ∈ (S a).powerset.filter (fun T => T.card ≤ M), (-1 : ℝ) ^ T.card =
        ∑ T ∈ Q.powerset.filter (fun T => T.card ≤ M),
          (-1 : ℝ) ^ T.card *
            (((Finset.Ico X (2 * X)).filter (fun a => T ⊆ S a)).card : ℝ) := by
      trans ∑ a ∈ Finset.Ico X (2 * X), ∑ T ∈ Q.powerset.filter (fun T => T.card ≤ M),
          if T ⊆ S a then (-1 : ℝ) ^ T.card else 0
      · apply Finset.sum_congr rfl; intro a _
        rw [← Finset.sum_filter]
        apply Finset.sum_congr _ (fun _ _ => rfl)
        ext T
        simp only [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨fun ⟨hTS, hle⟩ => ⟨⟨hTS.trans (Finset.filter_subset _ _), hle⟩, hTS⟩,
          fun ⟨⟨_, hle⟩, hTS⟩ => ⟨hTS, hle⟩⟩
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro T _
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    rw [hswap, Finset.mul_sum, ← Finset.sum_sub_distrib]
    calc |∑ T ∈ Q.powerset.filter (fun T => T.card ≤ M),
            (1 / (X : ℝ) * ((-1 : ℝ) ^ T.card *
              (((Finset.Ico X (2 * X)).filter (fun a => T ⊆ S a)).card : ℝ)) -
              (-1 : ℝ) ^ T.card * ∏ q ∈ T, f q)|
        ≤ ∑ T ∈ Q.powerset.filter (fun T => T.card ≤ M),
            |1 / (X : ℝ) * ((-1 : ℝ) ^ T.card *
              (((Finset.Ico X (2 * X)).filter (fun a => T ⊆ S a)).card : ℝ)) -
              (-1 : ℝ) ^ T.card * ∏ q ∈ T, f q| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ T ∈ Q.powerset.filter (fun T => T.card ≤ M), (1 / (X : ℝ)) * (D.card : ℝ) ^ T.card := by
          apply Finset.sum_le_sum
          intro T hT
          have hTQ : T ⊆ Q := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
          have hT_prime : ∀ q ∈ T, q.Prime := fun q hq => hQ q (hTQ hq)
          have hPT_pos : 0 < prodQ T := prodQ_pos hT_prime
          have : NeZero (prodQ T) := ⟨hPT_pos.ne'⟩
          set BadT := Finset.univ.filter (fun r : ZMod (prodQ T) =>
              ∀ q ∈ T, ∃ d ∈ D, (r.val + d : ℕ) % q = 0)
          have hBad_card : BadT.card = ∏ q ∈ T, localCount D q :=
            card_bad_residues_prodQ D T hT_prime
          have hfilt_T : (Finset.Ico X (2 * X)).filter (fun a => T ⊆ S a) =
              BadT.biUnion (fun r => (Finset.Ico X (X + X)).filter (fun a : ℕ => (a : ZMod (prodQ T)) = r)) := by
            ext a
            rw [show 2 * X = X + X by ring]
            simp only [Finset.mem_filter, Finset.mem_biUnion, BadT, Finset.mem_univ, true_and]
            constructor
            · intro ⟨ha, hTS⟩
              refine ⟨(a : ZMod (prodQ T)), ?_, ha, rfl⟩
              intro q hq
              have hqS := hTS hq
              simp only [S, Finset.mem_filter] at hqS
              obtain ⟨d, hd, hdvd⟩ := hqS.2
              refine ⟨d, hd, ?_⟩
              have hq_dvd_P : q ∣ prodQ T := Finset.dvd_prod_of_mem id hq
              have hmod_eq : (a : ZMod (prodQ T)).val % q = a % q := by
                rw [ZMod.val_natCast, Nat.mod_mod_of_dvd a hq_dvd_P]
              have : ((a : ZMod (prodQ T)).val + d) % q = (a + d) % q := by
                rw [Nat.add_mod, hmod_eq, ← Nat.add_mod]
              rw [this]
              exact Nat.mod_eq_zero_of_dvd hdvd
            · rintro ⟨r, hr, ha, rfl⟩
              refine ⟨ha, fun q hq => ?_⟩
              simp only [S, Finset.mem_filter]
              refine ⟨hTQ hq, ?_⟩
              obtain ⟨d, hd, hmod⟩ := hr q hq
              refine ⟨d, hd, ?_⟩
              have hq_dvd_P : q ∣ prodQ T := Finset.dvd_prod_of_mem id hq
              have hmod_eq : (a : ZMod (prodQ T)).val % q = a % q := by
                rw [ZMod.val_natCast, Nat.mod_mod_of_dvd a hq_dvd_P]
              have : (a + d) % q = ((a : ZMod (prodQ T)).val + d) % q := by
                rw [Nat.add_mod, ← hmod_eq, ← Nat.add_mod]
              exact Nat.dvd_of_mod_eq_zero (this.trans hmod)
          have hcard_T : (((Finset.Ico X (2 * X)).filter (fun a => T ⊆ S a)).card : ℝ) =
              ∑ r ∈ BadT, (((Finset.Ico X (X + X)).filter (fun a : ℕ => (a : ZMod (prodQ T)) = r)).card : ℝ) := by
            rw [hfilt_T, Finset.card_biUnion]
            · push_cast; rfl
            · intro r1 _ r2 _ hne
              rw [Function.onFun, Finset.disjoint_left]; intro a h1 h2
              exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
          have hprod_f : ∏ q ∈ T, f q = (BadT.card : ℝ) / (prodQ T : ℝ) := by
            have hnum : (BadT.card : ℝ) = ∏ q ∈ T, (localCount D q : ℝ) := by
              rw [hBad_card]; push_cast; rfl
            have hden : (prodQ T : ℝ) = ∏ q ∈ T, (q : ℝ) := by
              unfold prodQ; push_cast; rfl
            rw [hnum, hden, ← Finset.prod_div_distrib]
          have hdiff_eq : 1 / (X : ℝ) * ((-1 : ℝ) ^ T.card *
                (((Finset.Ico X (2 * X)).filter (fun a => T ⊆ S a)).card : ℝ)) -
              (-1 : ℝ) ^ T.card * ∏ q ∈ T, f q =
              ((-1 : ℝ) ^ T.card / (X : ℝ)) *
                ∑ r ∈ BadT, ((((Finset.Ico X (X + X)).filter
                  (fun a : ℕ => (a : ZMod (prodQ T)) = r)).card : ℝ) - (X : ℝ) / (prodQ T : ℝ)) := by
            rw [hcard_T, hprod_f, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
            field_simp [hX_pos.ne']
          rw [hdiff_eq, abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos hX_pos]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc |∑ r ∈ BadT, ((((Finset.Ico X (X + X)).filter
                  (fun a : ℕ => (a : ZMod (prodQ T)) = r)).card : ℝ) - (X : ℝ) / (prodQ T : ℝ))|
              ≤ ∑ r ∈ BadT, |(((Finset.Ico X (X + X)).filter
                  (fun a : ℕ => (a : ZMod (prodQ T)) = r)).card : ℝ) - (X : ℝ) / (prodQ T : ℝ)| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _r ∈ BadT, (1 : ℝ) :=
                Finset.sum_le_sum fun r _ => count_Ico_mod_eq X X (prodQ T) hPT_pos r
            _ = (BadT.card : ℝ) := by simp
            _ ≤ (D.card : ℝ) ^ T.card := by
                rw [hBad_card]
                push_cast
                rw [← Finset.prod_const]
                apply Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
                intro q _; exact_mod_cast localCount_le_card D q
      _ = (1 / (X : ℝ)) * ∑ T ∈ Q.powerset.filter (fun T => T.card ≤ M), (D.card : ℝ) ^ T.card := by
          rw [← Finset.mul_sum]
  -- Tail bound for ∑_{T ⊆ Q, M < |T|} ∏ f q
  have htail_bound : ∀ M : ℕ, 2 * r ≤ M →
      |∑ T ∈ Q.powerset.filter (fun T => T.card ≤ M), (-1 : ℝ) ^ T.card * ∏ q ∈ T, f q -
        ∏ q ∈ Q, (1 - f q)| ≤ ((1 : ℝ) / 2) ^ (2 * r) := by
    intro M hMr
    rw [hprod_expand]
    have hsplit : ∑ T ∈ Q.powerset, (-1 : ℝ) ^ T.card * ∏ q ∈ T, f q =
        ∑ T ∈ Q.powerset.filter (fun T => T.card ≤ M), (-1 : ℝ) ^ T.card * ∏ q ∈ T, f q +
        ∑ T ∈ Q.powerset.filter (fun T => M < T.card), (-1 : ℝ) ^ T.card * ∏ q ∈ T, f q := by
      rw [← Finset.sum_union]
      · congr 1; ext T; simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · intro h
          by_cases hle : T.card ≤ M
          · exact Or.inl ⟨h, hle⟩
          · exact Or.inr ⟨h, by omega⟩
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · rw [Finset.disjoint_left]; intro T h1 h2
        simp only [Finset.mem_filter] at h1 h2; omega
    rw [hsplit, sub_add_cancel_left, abs_neg]
    have hmaps : ∀ T ∈ Q.powerset.filter (fun T => M < T.card),
        T.card ∈ Finset.Icc (M + 1) Q.card := by
      intro T hT
      simp only [Finset.mem_filter, Finset.mem_powerset] at hT
      exact Finset.mem_Icc.mpr ⟨by omega, Finset.card_le_card hT.1⟩
    set U := ∑ q ∈ Q, f q
    have hU_le : U ≤ (D.card : ℝ) * ∑ q ∈ Q, (1 : ℝ) / q := by
      simp only [U, f, Finset.mul_sum]
      apply Finset.sum_le_sum; intro q _
      rw [mul_one_div]
      gcongr
      exact_mod_cast localCount_le_card D q
    have hU_nn : 0 ≤ U := Finset.sum_nonneg hf_nn
    calc |∑ T ∈ Q.powerset.filter (fun T => M < T.card), (-1 : ℝ) ^ T.card * ∏ q ∈ T, f q|
        ≤ ∑ T ∈ Q.powerset.filter (fun T => M < T.card), |(-1 : ℝ) ^ T.card * ∏ q ∈ T, f q| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ T ∈ Q.powerset.filter (fun T => M < T.card), ∏ q ∈ T, f q := by
          apply Finset.sum_congr rfl; intro T hT
          rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg]
          exact Finset.prod_nonneg fun q hq => hf_nn q (Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1 hq)
      _ = ∑ j ∈ Finset.Icc (M + 1) Q.card, ∑ T ∈ Q.powersetCard j, ∏ q ∈ T, f q := by
          rw [← Finset.sum_fiberwise_of_maps_to hmaps]
          apply Finset.sum_congr rfl; intro j hj
          have hjM : M < j := by have := (Finset.mem_Icc.mp hj).1; omega
          congr 1; ext T
          simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
          exact ⟨fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨h1, h2 ▸ hjM⟩, h2⟩⟩
      _ ≤ ∑ j ∈ Finset.Icc (M + 1) Q.card, ((1 : ℝ) / 2) ^ j := by
          apply Finset.sum_le_sum; intro j hj
          have hj1 : 1 ≤ j := by have := (Finset.mem_Icc.mp hj).1; omega
          have hj_ge : (2 * r + 1 : ℕ) ≤ j := by have := (Finset.mem_Icc.mp hj).1; omega
          have hfac := factorial_mul_sum_powersetCard_prod_le Q f hf_nn j
          have hdiv : ∑ T ∈ Q.powersetCard j, ∏ q ∈ T, f q ≤ U ^ j / (j.factorial : ℝ) :=
            (le_div_iff₀' (by exact_mod_cast Nat.factorial_pos j)).mpr hfac
          have hexp := pow_div_factorial_le_exp_pow U hU_nn j hj1
          have hbase : Real.exp 1 * U / j ≤ 1 / 2 := by
            have he3 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
            have h6U : 6 * U ≤ (j : ℝ) := by
              have : ((2 * r + 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast hj_ge
              linarith
            rw [div_le_div_iff₀ (by exact_mod_cast hj1) (by norm_num)]
            nlinarith
          exact hdiv.trans (hexp.trans (pow_le_pow_left₀ (by positivity) hbase j))
      _ ≤ ((1 : ℝ) / 2) ^ M := sum_half_pow_tail M Q.card
      _ ≤ ((1 : ℝ) / 2) ^ (2 * r) := pow_le_pow_of_le_one (by norm_num) (by norm_num) hMr
  -- Remainder sum bound for M ≤ 2*r + 1
  have hrem_sum_bound : ∀ M : ℕ, M ≤ 2 * r + 1 →
      ∑ T ∈ Q.powerset.filter (fun T => T.card ≤ M), (D.card : ℝ) ^ T.card ≤
        ((2 * r + 2 : ℕ) : ℝ) * ((max 1 (D.card * Q.card) : ℕ) : ℝ) ^ (2 * r + 1) := by
    intro M hM
    have hmaps : ∀ T ∈ Q.powerset.filter (fun T => T.card ≤ M), T.card ∈ Finset.range (M + 1) := by
      intro T hT; rw [Finset.mem_range]; have := (Finset.mem_filter.mp hT).2; omega
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    calc ∑ j ∈ Finset.range (M + 1),
            ∑ T ∈ (Q.powerset.filter (fun T => T.card ≤ M)).filter (fun T => T.card = j),
              (D.card : ℝ) ^ T.card
        ≤ ∑ j ∈ Finset.range (M + 1), ((max 1 (D.card * Q.card) : ℕ) : ℝ) ^ (2 * r + 1) := by
          apply Finset.sum_le_sum; intro j hj
          have hjM : j ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          have hfilt : (Q.powerset.filter (fun T => T.card ≤ M)).filter (fun T => T.card = j) =
              Q.powersetCard j := by
            ext T; simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
            exact ⟨fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨h1, h2 ▸ hjM⟩, h2⟩⟩
          rw [hfilt]
          have hconst : ∀ T ∈ Q.powersetCard j, (D.card : ℝ) ^ T.card = (D.card : ℝ) ^ j := by
            intro T hT; rw [(Finset.mem_powersetCard.mp hT).2]
          rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
          have hch : (Nat.choose Q.card j : ℝ) ≤ (Q.card : ℝ) ^ j :=
            (Nat.choose_le_pow_div j Q.card).trans
              (div_le_self (by positivity) (by exact_mod_cast Nat.factorial_pos j))
          have h1 : (Nat.choose Q.card j : ℝ) * (D.card : ℝ) ^ j ≤ ((D.card * Q.card : ℕ) : ℝ) ^ j := by
            push_cast; rw [mul_pow, mul_comm ((D.card : ℝ) ^ j)]
            gcongr
          have h2 : ((D.card * Q.card : ℕ) : ℝ) ^ j ≤ ((max 1 (D.card * Q.card) : ℕ) : ℝ) ^ j := by
            gcongr; exact_mod_cast le_max_right 1 (D.card * Q.card)
          have h3 : ((max 1 (D.card * Q.card) : ℕ) : ℝ) ^ j ≤
              ((max 1 (D.card * Q.card) : ℕ) : ℝ) ^ (2 * r + 1) :=
            pow_le_pow_right₀ (by exact_mod_cast le_max_left 1 (D.card * Q.card)) (by omega)
          exact h1.trans (h2.trans h3)
      _ = ((M + 1 : ℕ) : ℝ) * ((max 1 (D.card * Q.card) : ℕ) : ℝ) ^ (2 * r + 1) := by
          simp [Finset.sum_const]
      _ ≤ ((2 * r + 2 : ℕ) : ℝ) * ((max 1 (D.card * Q.card) : ℕ) : ℝ) ^ (2 * r + 1) :=
          mul_le_mul_of_nonneg_right
            (by exact_mod_cast (show M + 1 ≤ 2 * r + 2 by omega)) (by positivity)
  -- Combine upper (M = 2r) and lower (M = 2r + 1) bounds!
  have hup_ind : (1 / (X : ℝ)) *
      ∑ a ∈ Finset.Ico X (2 * X), (if ∀ d ∈ D, (a + d).Coprime (prodQ Q) then (1 : ℝ) else 0) ≤
      (1 / (X : ℝ)) * ∑ a ∈ Finset.Ico X (2 * X),
        ∑ T ∈ (S a).powerset.filter (fun T => T.card ≤ 2 * r), (-1 : ℝ) ^ T.card := by
    gcongr with a
    simp_rw [hcop_iff]
    exact bonferroni_upper (S a) r
  have hlo_ind : (1 / (X : ℝ)) * ∑ a ∈ Finset.Ico X (2 * X),
        ∑ T ∈ (S a).powerset.filter (fun T => T.card ≤ 2 * r + 1), (-1 : ℝ) ^ T.card ≤
      (1 / (X : ℝ)) *
        ∑ a ∈ Finset.Ico X (2 * X), (if ∀ d ∈ D, (a + d).Coprime (prodQ Q) then (1 : ℝ) else 0) := by
    gcongr with a
    simp_rw [hcop_iff]
    exact bonferroni_lower (S a) r
  have he1 := htrunc_err (2 * r)
  have ht1 := htail_bound (2 * r) le_rfl
  have hr1 := hrem_sum_bound (2 * r) (by omega)
  have he2 := htrunc_err (2 * r + 1)
  have ht2 := htail_bound (2 * r + 1) (by omega)
  have hr2 := hrem_sum_bound (2 * r + 1) le_rfl
  rw [abs_le] at he1 ht1 he2 ht2 ⊢
  have h1x : (1 / (X : ℝ)) * ∑ T ∈ Q.powerset.filter (fun T => T.card ≤ 2 * r), (D.card : ℝ) ^ T.card ≤
      ((2 * r + 2 : ℕ) : ℝ) * ((max 1 (D.card * Q.card) : ℕ) : ℝ) ^ (2 * r + 1) / (X : ℝ) := by
    rw [one_div_mul_eq_div]; exact div_le_div_of_nonneg_right hr1 hX_pos.le
  have h2x : (1 / (X : ℝ)) * ∑ T ∈ Q.powerset.filter (fun T => T.card ≤ 2 * r + 1), (D.card : ℝ) ^ T.card ≤
      ((2 * r + 2 : ℕ) : ℝ) * ((max 1 (D.card * Q.card) : ℕ) : ℝ) ^ (2 * r + 1) / (X : ℝ) := by
    rw [one_div_mul_eq_div]; exact div_le_div_of_nonneg_right hr2 hX_pos.le
  constructor <;> linarith

end BrunPureSieve

section EmptyWindows

noncomputable def H_param (X : ℕ) : ℕ := max 1 ⌊Real.log (X : ℝ) / 40⌋₊

noncomputable def Z_param (X : ℕ) : ℕ := ⌈(Real.log (X : ℝ)) ^ 2⌉₊ + 1

noncomputable def intervalCount (Q : Finset ℕ) (H a : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 H, if (a + i).Coprime (prodQ Q) then (1 : ℝ) else 0

def emptyWindows (X H Z : ℕ) : Finset ℕ :=
  (Finset.Ico X (2 * X)).filter (fun a =>
    ∀ i ∈ Finset.Icc 1 H, ¬ (a + i).Coprime (prodQ Z.primesBelow))

lemma interval_moment_sub_centMom_le (K X H r : ℕ) (hX : 1 ≤ X) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime)
    (hUr : 6 * ((K : ℝ) * ∑ q ∈ Q, (1 : ℝ) / q) ≤ (2 * r + 1 : ℕ)) :
    |(1 / (X : ℝ)) *
        ∑ a ∈ Finset.Ico X (2 * X), (intervalCount Q H a - (H : ℝ) * densQ Q) ^ K -
      centMom K Q H| ≤
      (2 * (H : ℝ)) ^ K *
        (((1 : ℝ) / 2) ^ (2 * r) +
          ((2 * r + 2 : ℕ) : ℝ) * ((max 1 (K * Q.card) : ℕ) : ℝ) ^ (2 * r + 1) / (X : ℝ)) := by
  set p := densQ Q
  have : NeZero (prodQ Q) := ⟨prodQ_ne_zero hQ⟩
  have hp_pos : 0 < p := densQ_pos hQ
  have hp_le1 : p ≤ 1 := densQ_le_one hQ
  set I := Finset.Icc 1 H
  set tuples := Fintype.piFinset (fun _ : Fin K => I)
  have htuples_card : tuples.card = H ^ K := by
    simp [tuples, I]
  -- Expand (∑ i ∈ I, (ind i - p))^K for any indicator function ind : ℕ → Prop with arbitrary Decidable instances
  have hexpand : ∀ (ind : ℕ → Prop) (d1 : ∀ i, Decidable (ind i))
      (d2 : ∀ T : Finset ℕ, Decidable (∀ d ∈ T, ind d)),
      ((∑ i ∈ I, @ite ℝ (ind i) (d1 i) 1 0) - (H : ℝ) * p) ^ K =
      ∑ g ∈ tuples, ∑ S ∈ (Finset.univ : Finset (Fin K)).powerset,
        (-p) ^ (K - S.card) * (@ite ℝ (∀ d ∈ S.image g, ind d) (d2 (S.image g)) 1 0) := by
    intro ind d1 d2
    have hsub : (∑ i ∈ I, @ite ℝ (ind i) (d1 i) 1 0) - (H : ℝ) * p =
        ∑ i ∈ I, (@ite ℝ (ind i) (d1 i) 1 0 - p) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, show I.card = H by simp [I], nsmul_eq_mul]
    rw [hsub]
    have hpow : (∑ i ∈ I, (@ite ℝ (ind i) (d1 i) 1 0 - p)) ^ K =
        ∑ g ∈ tuples, ∏ j : Fin K, (@ite ℝ (ind (g j)) (d1 (g j)) 1 0 - p) := by
      rw [Finset.sum_prod_piFinset I (fun (_ : Fin K) (i : ℕ) =>
        @ite ℝ (ind i) (d1 i) 1 0 - p)]
      simp [Finset.prod_const]
    rw [hpow]
    apply Finset.sum_congr rfl; intro g _
    have hprod := Finset.prod_add (s := (Finset.univ : Finset (Fin K)))
      (f := fun j => @ite ℝ (ind (g j)) (d1 (g j)) 1 0) (g := fun _ => -p)
    simp only [sub_eq_add_neg] at hprod ⊢
    rw [hprod]
    apply Finset.sum_congr rfl; intro S _
    have hcard_sdiff : (Finset.univ \ S).card = K - S.card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    rw [Finset.prod_const, hcard_sdiff, mul_comm]
    congr 1
    by_cases hall : ∀ d ∈ S.image g, ind d
    · rw [if_pos hall]
      apply Finset.prod_eq_one; intro j hj
      rw [if_pos (hall (g j) (Finset.mem_image_of_mem g hj))]
    · rw [if_neg hall]
      push Not at hall
      rcases hall with ⟨d, hd, hnd⟩
      rcases Finset.mem_image.mp hd with ⟨j, hj, rfl⟩
      apply Finset.prod_eq_zero hj
      rw [if_neg hnd]
  have hlhs_exp : (1 / (X : ℝ)) *
      ∑ a ∈ Finset.Ico X (2 * X), (intervalCount Q H a - (H : ℝ) * p) ^ K =
      ∑ g ∈ tuples, ∑ S ∈ (Finset.univ : Finset (Fin K)).powerset,
        (-p) ^ (K - S.card) *
          ((1 / (X : ℝ)) * ∑ a ∈ Finset.Ico X (2 * X),
            if ∀ d ∈ S.image g, (a + d).Coprime (prodQ Q) then (1 : ℝ) else 0) := by
    have hpt : ∀ a ∈ Finset.Ico X (2 * X),
        (intervalCount Q H a - (H : ℝ) * p) ^ K =
        ∑ g ∈ tuples, ∑ S ∈ (Finset.univ : Finset (Fin K)).powerset,
          (-p) ^ (K - S.card) * (if ∀ d ∈ S.image g, (a + d).Coprime (prodQ Q) then (1 : ℝ) else 0) := by
      intro a _
      exact hexpand (fun d => (a + d).Coprime (prodQ Q)) _ _
    rw [Finset.sum_congr rfl hpt, Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro g _
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro S _
    rw [← Finset.mul_sum, ← mul_assoc, mul_comm (1 / (X : ℝ)), mul_assoc]
  have hrhs_exp : centMom K Q H =
      ∑ g ∈ tuples, ∑ S ∈ (Finset.univ : Finset (Fin K)).powerset,
        (-p) ^ (K - S.card) *
          ((1 / (prodQ Q : ℝ)) * ∑ b : ZMod (prodQ Q),
            if ∀ d ∈ S.image g, IsUnit (b + (d : ZMod (prodQ Q))) then (1 : ℝ) else 0) := by
    rw [centMom_eq_sum_zmod]
    have hpt : ∀ b : ZMod (prodQ Q),
        (countQ Q H b - (H : ℝ) * densQ Q) ^ K =
        ∑ g ∈ tuples, ∑ S ∈ (Finset.univ : Finset (Fin K)).powerset,
          (-p) ^ (K - S.card) *
            (if ∀ d ∈ S.image g, IsUnit (b + (d : ZMod (prodQ Q))) then (1 : ℝ) else 0) := by
      intro b
      exact hexpand (fun d => IsUnit (b + (d : ZMod (prodQ Q)))) _ _
    rw [Finset.sum_congr rfl (fun b _ => hpt b)]
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro g _
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro S _
    rw [← Finset.mul_sum, ← mul_assoc, mul_comm (1 / (prodQ Q : ℝ)), mul_assoc]
  rw [hlhs_exp, hrhs_exp, ← Finset.sum_sub_distrib]
  set E : ℝ := ((1 : ℝ) / 2) ^ (2 * r) +
    ((2 * r + 2 : ℕ) : ℝ) * ((max 1 (K * Q.card) : ℕ) : ℝ) ^ (2 * r + 1) / (X : ℝ)
  calc |∑ g ∈ tuples, (∑ S ∈ (Finset.univ : Finset (Fin K)).powerset,
            (-p) ^ (K - S.card) * ((1 / (X : ℝ)) * ∑ a ∈ Finset.Ico X (2 * X),
              if ∀ d ∈ S.image g, (a + d).Coprime (prodQ Q) then (1 : ℝ) else 0) -
          ∑ S ∈ (Finset.univ : Finset (Fin K)).powerset,
            (-p) ^ (K - S.card) * ((1 / (prodQ Q : ℝ)) * ∑ b : ZMod (prodQ Q),
              if ∀ d ∈ S.image g, IsUnit (b + (d : ZMod (prodQ Q))) then (1 : ℝ) else 0))|
      ≤ ∑ g ∈ tuples, |∑ S ∈ (Finset.univ : Finset (Fin K)).powerset,
            (-p) ^ (K - S.card) *
              (((1 / (X : ℝ)) * ∑ a ∈ Finset.Ico X (2 * X),
                if ∀ d ∈ S.image g, (a + d).Coprime (prodQ Q) then (1 : ℝ) else 0) -
               ((1 / (prodQ Q : ℝ)) * ∑ b : ZMod (prodQ Q),
                if ∀ d ∈ S.image g, IsUnit (b + (d : ZMod (prodQ Q))) then (1 : ℝ) else 0))| := by
        calc _ ≤ ∑ g ∈ tuples, |_| := Finset.abs_sum_le_sum_abs _ _
          _ = _ := by
              apply Finset.sum_congr rfl; intro g _
              rw [← Finset.sum_sub_distrib]
              congr 1; apply Finset.sum_congr rfl; intro S _; ring
    _ ≤ ∑ _g ∈ tuples, ((2 : ℝ) ^ K * E) := by
        apply Finset.sum_le_sum; intro g _
        calc |∑ S ∈ (Finset.univ : Finset (Fin K)).powerset, _|
            ≤ ∑ S ∈ (Finset.univ : Finset (Fin K)).powerset,
                |(-p) ^ (K - S.card) * _| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _S ∈ (Finset.univ : Finset (Fin K)).powerset, E := by
              apply Finset.sum_le_sum; intro S _
              rw [abs_mul, abs_pow, abs_neg, abs_of_pos hp_pos]
              have hp_pow : p ^ (K - S.card) ≤ 1 := pow_le_one₀ hp_pos.le hp_le1
              have hcardD : (S.image g).card ≤ K := by
                calc (S.image g).card ≤ S.card := Finset.card_image_le
                  _ ≤ (Finset.univ : Finset (Fin K)).card := Finset.card_le_univ S
                  _ = K := Fintype.card_fin K
              have hUrD : 6 * (((S.image g).card : ℝ) * ∑ q ∈ Q, (1 : ℝ) / q) ≤ (2 * r + 1 : ℕ) := by
                have hsum_nn : 0 ≤ ∑ q ∈ Q, (1 : ℝ) / q := Finset.sum_nonneg fun _ _ => by positivity
                have hle : ((S.image g).card : ℝ) ≤ K := by exact_mod_cast hcardD
                nlinarith
              have hbrun := brun_tuple_count_close X r hX (S.image g) Q hQ hUrD
              have hE_le : ((1 : ℝ) / 2) ^ (2 * r) +
                  ((2 * r + 2 : ℕ) : ℝ) * ((max 1 ((S.image g).card * Q.card) : ℕ) : ℝ) ^ (2 * r + 1) / (X : ℝ) ≤ E := by
                simp only [E]
                gcongr
              have hdiff_le : |_ - _| ≤ E := hbrun.trans hE_le
              exact mul_le_of_le_one_left (abs_nonneg _) hp_pow |>.trans hdiff_le
          _ = (2 : ℝ) ^ K * E := by simp [Finset.sum_const]
    _ = (2 * (H : ℝ)) ^ K * E := by
        simp only [Finset.sum_const, htuples_card, nsmul_eq_mul, Nat.cast_pow, mul_pow]
        ring

private lemma empty_windows_brun_err_le1 (X H Z r Qcard : ℕ) (L LL : ℝ)
    (hL_eq : L = Real.log (X : ℝ)) (hLL_eq : LL = Real.log L)
    (hX_pos : (0 : ℝ) < X) (hlog : 1000 ≤ L) (hloglog : 10 ≤ LL)
    (hH_le : (H : ℝ) ≤ L / 40) (hZ_le : (Z : ℝ) ≤ 2 * L ^ 2)
    (hr_ge : 100 * LL ≤ (r : ℝ)) (hr_le : (r : ℝ) ≤ 101 * LL)
    (hQcard_le : Qcard ≤ Z) (hr2 : LL ^ 2 / L ≤ 1 / 10000) :
    (2 * (H : ℝ)) ^ 6 *
      (((1 : ℝ) / 2) ^ (2 * r) +
        ((2 * r + 2 : ℕ) : ℝ) * ((max 1 (6 * Qcard) : ℕ) : ℝ) ^ (2 * r + 1) / (X : ℝ)) ≤ 1 := by
  have hL_pos : 0 < L := by linarith
  have h2H6 : (2 * (H : ℝ)) ^ 6 ≤ L ^ 6 := by
    have : 2 * (H : ℝ) ≤ L := by linarith
    exact pow_le_pow_left₀ (by positivity) this 6
  have hpart1 : L ^ 6 * ((1 : ℝ) / 2) ^ (2 * r) ≤ 1 / 2 := by
    have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
      have hsq : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp 1 := by
        rw [← Real.exp_nat_mul]; norm_num
      have hexp : Real.exp (1 / 2 : ℝ) < 2 := by nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 / 2 : ℝ)]
      exact (Real.lt_log_iff_exp_lt (by norm_num)).mpr hexp
    have h2r_ge : 200 * LL ≤ ((2 * r : ℕ) : ℝ) := by push_cast; linarith
    have hexp_bound : L ^ 6 * ((1 : ℝ) / 2) ^ (2 * r) ≤ Real.exp (-50 * LL) := by
      rw [← Real.log_le_log_iff (by positivity) (Real.exp_pos _)]
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
          Real.log_div one_ne_zero two_ne_zero, Real.log_one, zero_sub, Real.log_exp]
      rw [← hLL_eq]
      norm_num
      nlinarith
    have hexp_half : Real.exp (-50 * LL) ≤ 1 / 2 := by
      rw [show (1 / 2 : ℝ) = Real.exp (-Real.log 2) by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num]
      apply Real.exp_le_exp.mpr
      have hlog2_le : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
      linarith
    exact hexp_bound.trans hexp_half
  have hpart2 : L ^ 6 * (((2 * r + 2 : ℕ) : ℝ) *
      ((max 1 (6 * Qcard) : ℕ) : ℝ) ^ (2 * r + 1) / (X : ℝ)) ≤ 1 / 2 := by
    have hbase_le : ((max 1 (6 * Qcard) : ℕ) : ℝ) ≤ L ^ 3 := by
      have h1 : (max 1 (6 * Qcard) : ℕ) ≤ 6 * Z + 1 := by omega
      have h2 : ((max 1 (6 * Qcard) : ℕ) : ℝ) ≤ 6 * (Z : ℝ) + 1 := by exact_mod_cast h1
      nlinarith
    have h2r2_le : ((2 * r + 2 : ℕ) : ℝ) ≤ L ^ 2 := by
      have hLL_le_L : LL ≤ L := by
        rw [hLL_eq]; have := Real.log_le_sub_one_of_pos hL_pos; linarith
      push_cast; nlinarith
    have hnum_le : L ^ 6 * (((2 * r + 2 : ℕ) : ℝ) *
        ((max 1 (6 * Qcard) : ℕ) : ℝ) ^ (2 * r + 1)) ≤ L ^ (6 * r + 11) := by
      have h1 : ((max 1 (6 * Qcard) : ℕ) : ℝ) ^ (2 * r + 1) ≤ (L ^ 3) ^ (2 * r + 1) :=
        pow_le_pow_left₀ (by positivity) hbase_le _
      have h2 : L ^ 6 * (((2 * r + 2 : ℕ) : ℝ) * ((max 1 (6 * Qcard) : ℕ) : ℝ) ^ (2 * r + 1)) ≤
          L ^ 6 * (L ^ 2 * (L ^ 3) ^ (2 * r + 1)) := by gcongr
      have h3 : L ^ 6 * (L ^ 2 * (L ^ 3) ^ (2 * r + 1)) = L ^ (6 * r + 11) := by
        rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; omega
      exact h2.trans_eq h3
    have hlog_bound : Real.log (L ^ (6 * r + 11) / (X : ℝ)) ≤ -1 := by
      rw [Real.log_div (by positivity) hX_pos.ne', Real.log_pow, ← hLL_eq, ← hL_eq]
      have h6r : ((6 * r + 11 : ℕ) : ℝ) * LL ≤ 700 * LL ^ 2 := by
        push_cast; nlinarith
      have hLL2 : LL ^ 2 ≤ L / 10000 := by
        have := (div_le_iff₀ hL_pos).mp hr2
        linarith
      linarith
    have hexp_bound : L ^ (6 * r + 11) / (X : ℝ) ≤ Real.exp (-1) := by
      rw [← Real.log_le_log_iff (by positivity) (Real.exp_pos _), Real.log_exp]
      exact hlog_bound
    have hexp1 : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
      linarith [Real.exp_one_gt_d9]
    calc L ^ 6 * (((2 * r + 2 : ℕ) : ℝ) *
          ((max 1 (6 * Qcard) : ℕ) : ℝ) ^ (2 * r + 1) / (X : ℝ))
        = (L ^ 6 * (((2 * r + 2 : ℕ) : ℝ) *
            ((max 1 (6 * Qcard) : ℕ) : ℝ) ^ (2 * r + 1))) / (X : ℝ) := by ring
      _ ≤ L ^ (6 * r + 11) / (X : ℝ) := div_le_div_of_nonneg_right hnum_le hX_pos.le
      _ ≤ Real.exp (-1) := hexp_bound
      _ ≤ 1 / 2 := hexp1
  have hmul := mul_le_mul_of_nonneg_right h2H6 (show (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ (2 * r) +
      ((2 * r + 2 : ℕ) : ℝ) * ((max 1 (6 * Qcard) : ℕ) : ℝ) ^ (2 * r + 1) / (X : ℝ) by positivity)
  linarith [mul_add (L ^ 6) (((1 : ℝ) / 2) ^ (2 * r))
    (((2 * r + 2 : ℕ) : ℝ) * ((max 1 (6 * Qcard) : ℕ) : ℝ) ^ (2 * r + 1) / (X : ℝ))]

private lemma empty_windows_final_ratio (Cmom L LL dens : ℝ) (H : ℕ)
    (hCmom : 0 < Cmom) (hL : 1000 ≤ L) (hLL : 10 ≤ LL)
    (hH_ge1 : 1 ≤ H) (hH_ge : L / 50 ≤ (H : ℝ))
    (hdens_pos : 0 < dens) (hdens_inv : dens⁻¹ ≤ Real.exp 20 * (3 * LL) ^ 8)
    (hr1 : LL ^ 60 / L ^ ((1 : ℝ) / 2) ≤ 1 / (10 ^ 35 * (Cmom + 1) * Real.exp 120)) :
    ((Cmom + 1) * (H : ℝ) ^ ((3 : ℝ) + 1 / 10) * (5 * LL) ^ 3) /
      ((H : ℝ) * dens) ^ 6 ≤ (H : ℝ) / L ^ 2 := by
  have hL_pos : 0 < L := by linarith
  have hH_pos : (0 : ℝ) < H := by exact_mod_cast hH_ge1
  have hrhs_rewrite : ((Cmom + 1) * (H : ℝ) ^ ((3 : ℝ) + 1 / 10) * (5 * LL) ^ 3) /
      ((H : ℝ) * dens) ^ 6 =
      (Cmom + 1) * (5 * LL) ^ 3 * (dens⁻¹) ^ 6 * (H : ℝ) ^ ((3 : ℝ) + 1 / 10) / (H : ℝ) ^ 6 := by
    rw [mul_pow, inv_pow]; field_simp [hdens_pos.ne', hH_pos.ne']
  rw [hrhs_rewrite]
  have hinv6 : (dens⁻¹) ^ 6 ≤ (Real.exp 20 * (3 * LL) ^ 8) ^ 6 :=
    pow_le_pow_left₀ (inv_nonneg.mpr hdens_pos.le) hdens_inv 6
  have hexp120 : (Real.exp 20 * (3 * LL) ^ 8) ^ 6 = Real.exp 120 * 3 ^ 48 * LL ^ 48 := by
    rw [mul_pow, ← Real.exp_nat_mul, ← pow_mul, mul_pow]
    norm_num; ring
  rw [hexp120] at hinv6
  have hH_pow_eq : (H : ℝ) ^ ((3 : ℝ) + 1 / 10) / (H : ℝ) ^ 6 =
      (H : ℝ) / (H : ℝ) ^ ((3 : ℝ) + 9 / 10) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    rw [← Real.rpow_natCast (H : ℝ) 6, ← Real.rpow_add hH_pos]
    conv_rhs => arg 1; rw [← Real.rpow_one (H : ℝ)]
    rw [← Real.rpow_add hH_pos]
    congr 1; norm_num
  have hH39_ge : (L / 50) ^ ((3 : ℝ) + 9 / 10) ≤ (H : ℝ) ^ ((3 : ℝ) + 9 / 10) :=
    Real.rpow_le_rpow (by positivity) hH_ge (by norm_num)
  have hH_L : L ^ ((5 : ℝ) / 2) / 50 ^ 4 ≤ (L / 50) ^ ((3 : ℝ) + 9 / 10) := by
    rw [Real.div_rpow hL_pos.le (by norm_num)]
    have h50 : (50 : ℝ) ^ ((3 : ℝ) + 9 / 10) ≤ 50 ^ 4 := by
      rw [← Real.rpow_natCast (50 : ℝ) 4]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have hLpow : L ^ ((5 : ℝ) / 2) ≤ L ^ ((3 : ℝ) + 9 / 10) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    exact div_le_div₀ (by positivity) hLpow (by positivity) h50
  have hL52 : L ^ ((5 : ℝ) / 2) = L ^ 2 * L ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_natCast L 2, ← Real.rpow_add hL_pos]; congr 1; norm_num
  have hLL51 : LL ^ 51 ≤ LL ^ 60 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hnum_const : (5 : ℝ) ^ 3 * 3 ^ 48 * 50 ^ 4 ≤ 10 ^ 35 := by norm_num
  calc (Cmom + 1) * (5 * LL) ^ 3 * (dens⁻¹) ^ 6 * (H : ℝ) ^ ((3 : ℝ) + 1 / 10) / (H : ℝ) ^ 6
      = (Cmom + 1) * (5 * LL) ^ 3 * (dens⁻¹) ^ 6 *
          ((H : ℝ) ^ ((3 : ℝ) + 1 / 10) / (H : ℝ) ^ 6) := by ring
    _ = (Cmom + 1) * (5 * LL) ^ 3 * (dens⁻¹) ^ 6 *
          ((H : ℝ) / (H : ℝ) ^ ((3 : ℝ) + 9 / 10)) := by rw [hH_pow_eq]
    _ ≤ (Cmom + 1) * (5 * LL) ^ 3 * (Real.exp 120 * 3 ^ 48 * LL ^ 48) *
          ((H : ℝ) / (L ^ ((5 : ℝ) / 2) / 50 ^ 4)) := by
        gcongr
        exact hH_L.trans hH39_ge
    _ = ((5 ^ 3 * 3 ^ 48 * 50 ^ 4) * (Cmom + 1) * Real.exp 120) *
          (LL ^ 51 / L ^ ((1 : ℝ) / 2)) * ((H : ℝ) / L ^ 2) := by
        rw [hL52, mul_pow]
        field_simp [hL_pos.ne', (Real.rpow_pos_of_pos hL_pos _).ne']
    _ ≤ (10 ^ 35 * (Cmom + 1) * Real.exp 120) *
          (LL ^ 60 / L ^ ((1 : ℝ) / 2)) * ((H : ℝ) / L ^ 2) := by
        gcongr
    _ ≤ (10 ^ 35 * (Cmom + 1) * Real.exp 120) *
          (1 / (10 ^ 35 * (Cmom + 1) * Real.exp 120)) * ((H : ℝ) / L ^ 2) := by
        gcongr
    _ = (H : ℝ) / L ^ 2 := by
        have hne : (10 ^ 35 * (Cmom + 1) * Real.exp 120 : ℝ) ≠ 0 := by positivity
        field_simp [hne]

lemma empty_windows_bound :
    ∀ᶠ X : ℕ in Filter.atTop,
      ((emptyWindows X (H_param X) (Z_param X)).card : ℝ) ≤
        (H_param X : ℝ) * ((X : ℝ) / (Real.log (X : ℝ)) ^ 2) := by
  obtain ⟨Cmom, hCmom_pos, hmom⟩ := unified_centered_moment_bound 3 (by norm_num) (ε := (1 : ℝ) / 10) (by norm_num)
  -- Growth lemmas as X → ∞
  have hlog_top : Filter.Tendsto (fun X : ℕ => Real.log (X : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog_top : Filter.Tendsto (fun X : ℕ => Real.log (Real.log (X : ℝ))) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp hlog_top
  -- (log log X)^60 / (log X)^(1/2) → 0
  have hratio1 : Filter.Tendsto
      (fun X : ℕ => (Real.log (Real.log (X : ℝ))) ^ 60 / (Real.log (X : ℝ)) ^ ((1 : ℝ) / 2))
      Filter.atTop (nhds 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (60 : ℝ) (show (0 : ℝ) < 1 / 2 by norm_num)).tendsto_div_nhds_zero
    have hcomp := h.comp hlog_top
    simpa [Function.comp_def, Real.rpow_natCast] using hcomp
  -- (log log X)^2 / log X → 0
  have hratio2 : Filter.Tendsto
      (fun X : ℕ => (Real.log (Real.log (X : ℝ))) ^ 2 / Real.log (X : ℝ))
      Filter.atTop (nhds 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (show (0 : ℝ) < 1 by norm_num)).tendsto_div_nhds_zero
    have hcomp := h.comp hlog_top
    simpa [Function.comp_def, Real.rpow_natCast, Real.rpow_one] using hcomp
  -- Thresholds
  have hev_log : ∀ᶠ X : ℕ in Filter.atTop, (1000 : ℝ) ≤ Real.log (X : ℝ) :=
    hlog_top.eventually (Filter.eventually_ge_atTop 1000)
  have hev_loglog : ∀ᶠ X : ℕ in Filter.atTop, (10 : ℝ) ≤ Real.log (Real.log (X : ℝ)) :=
    hloglog_top.eventually (Filter.eventually_ge_atTop 10)
  have hev_r1 : ∀ᶠ X : ℕ in Filter.atTop,
      (Real.log (Real.log (X : ℝ))) ^ 60 / (Real.log (X : ℝ)) ^ ((1 : ℝ) / 2) ≤
        1 / (10 ^ 35 * (Cmom + 1) * Real.exp 120) := by
    have hpos : (0 : ℝ) < 1 / (10 ^ 35 * (Cmom + 1) * Real.exp 120) := by positivity
    filter_upwards [hratio1.eventually (gt_mem_nhds hpos)] with X hX using hX.le
  have hev_r2 : ∀ᶠ X : ℕ in Filter.atTop,
      (Real.log (Real.log (X : ℝ))) ^ 2 / Real.log (X : ℝ) ≤ 1 / 10000 := by
    filter_upwards [hratio2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 10000))] with X hX using hX.le
  filter_upwards [hev_log, hev_loglog, hev_r1, hev_r2] with X hlog hloglog hr1 hr2
  set L := Real.log (X : ℝ)
  set LL := Real.log L
  have hL_pos : 0 < L := by linarith
  have hLL_pos : 0 < LL := by linarith
  have hX_ge1 : 1 ≤ X := by
    by_contra hlt; push Not at hlt
    have hX0 : X = 0 := by omega
    simp [L, hX0] at hlog
    linarith
  have hX_pos : (0 : ℝ) < X := by exact_mod_cast hX_ge1
  set H := H_param X
  set Z := Z_param X
  set Q := Z.primesBelow
  have hQ_prime : ∀ q ∈ Q, q.Prime := fun q hq => Nat.prime_of_mem_primesBelow hq
  -- Bounds on H and Z
  have hH_ge : L / 50 ≤ (H : ℝ) := by
    have hfl : L / 40 - 1 ≤ (⌊L / 40⌋₊ : ℝ) := (Nat.sub_one_lt_floor _).le
    have hle : (⌊L / 40⌋₊ : ℝ) ≤ (H : ℝ) := by exact_mod_cast le_max_right 1 ⌊L / 40⌋₊
    linarith
  have hH_le : (H : ℝ) ≤ L / 40 := by
    have h1 : 1 ≤ ⌊L / 40⌋₊ := Nat.le_floor (by norm_cast; linarith)
    have hmax : H = ⌊L / 40⌋₊ := max_eq_right h1
    rw [hmax]
    exact Nat.floor_le (by linarith)
  have hH_ge1 : 1 ≤ H := le_max_left _ _
  have hZ_le : (Z : ℝ) ≤ 2 * L ^ 2 := by
    have h1 : (⌈L ^ 2⌉₊ : ℝ) < L ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
    have hZeq : (Z : ℝ) = (⌈L ^ 2⌉₊ : ℝ) + 1 := by simp [Z, Z_param, L]
    nlinarith
  have hZ_ge : L ^ 2 ≤ (Z : ℝ) := by
    have h1 : L ^ 2 ≤ (⌈L ^ 2⌉₊ : ℝ) := Nat.le_ceil _
    have hZeq : (Z : ℝ) = (⌈L ^ 2⌉₊ : ℝ) + 1 := by simp [Z, Z_param, L]
    linarith
  have hlogZ10 : Real.log ((Z + 10 : ℕ) : ℝ) ≤ 3 * LL := by
    have hZ10 : ((Z + 10 : ℕ) : ℝ) ≤ L ^ 3 := by
      push_cast; nlinarith
    have hlog_le : Real.log ((Z + 10 : ℕ) : ℝ) ≤ Real.log (L ^ 3) :=
      Real.log_le_log (by positivity) hZ10
    rw [Real.log_pow] at hlog_le
    simpa [LL] using hlog_le
  -- Set Brun sieve parameter r = ⌈100 * LL⌉₊
  set r := ⌈100 * LL⌉₊
  have hr_ge : 100 * LL ≤ (r : ℝ) := Nat.le_ceil _
  have hr_le : (r : ℝ) ≤ 101 * LL := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 100 * LL by positivity)
    linarith
  -- Verify Brun sieve condition 6 * (6 * ∑_{q ∈ Q} 1/q) ≤ 2*r + 1
  have hharmQ : ∑ q ∈ Q, (1 : ℝ) / q ≤ 4 * LL := by
    have hsub : Q ⊆ Finset.Icc 1 Z := fun q hq => by
      have hp := Nat.mem_primesBelow.mp hq
      exact Finset.mem_Icc.mpr ⟨hp.2.one_le, hp.1.le⟩
    calc ∑ q ∈ Q, (1 : ℝ) / q ≤ ∑ n ∈ Finset.Icc 1 Z, (1 : ℝ) / n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ 1 + Real.log (max 1 Z : ℕ) := sum_one_div_Icc_le_one_add_log Z
      _ ≤ 1 + Real.log ((Z + 10 : ℕ) : ℝ) := by
          gcongr; omega
      _ ≤ 4 * LL := by linarith
  have hUr : 6 * ((6 : ℝ) * ∑ q ∈ Q, (1 : ℝ) / q) ≤ (2 * r + 1 : ℕ) := by
    push_cast; linarith
  -- Apply Brun moment transfer (K = 6)
  have htransfer := interval_moment_sub_centMom_le 6 X H r hX_ge1 Q hQ_prime hUr
  -- Bound the Brun error term by 1
  have hQcard_le : Q.card ≤ Z := by
    have hsub : Q ⊆ Finset.range Z := fun q hq => Finset.mem_range.mpr (Nat.mem_primesBelow.mp hq).1
    simpa using Finset.card_le_card hsub
  have hbrun_err_le1 :=
    empty_windows_brun_err_le1 X H Z r Q.card L LL rfl rfl hX_pos hlog hloglog hH_le hZ_le
      hr_ge hr_le hQcard_le hr2
  have hinterval_mom : (1 / (X : ℝ)) *
      ∑ a ∈ Finset.Ico X (2 * X), (intervalCount Q H a - (H : ℝ) * densQ Q) ^ 6 ≤
      centMom 6 Q H + 1 := by
    have h1 := (abs_le.mp htransfer).2
    linarith
  -- Apply unified_centered_moment_bound (k = 3, ε = 1/10)
  have hmom_Z := hmom H Q hH_ge1 hQ_prime
  have hhi_sum : 1 + ∑ q ∈ Q.filter (fun q => H < q), (1 : ℝ) / q ≤ 5 * LL := by
    have hsub : Q.filter (fun q => H < q) ⊆ Q := Finset.filter_subset _ _
    have hle : ∑ q ∈ Q.filter (fun q => H < q), (1 : ℝ) / q ≤ ∑ q ∈ Q, (1 : ℝ) / q :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    linarith
  have hmom_bound : centMom 6 Q H + 1 ≤ (Cmom + 1) * (H : ℝ) ^ ((3 : ℝ) + 1 / 10) * (5 * LL) ^ 3 := by
    have h1 : centMom 6 Q H ≤ Cmom * (H : ℝ) ^ ((3 : ℝ) + 1 / 10) * (5 * LL) ^ 3 := by
      calc centMom 6 Q H
          ≤ Cmom * (H : ℝ) ^ ((3 : ℝ) + 1 / 10) *
              (1 + ∑ q ∈ Q.filter (fun q => H < q), (1 : ℝ) / q) ^ 3 := hmom_Z
        _ ≤ Cmom * (H : ℝ) ^ ((3 : ℝ) + 1 / 10) * (5 * LL) ^ 3 := by
            gcongr
    have hH_pow_ge1 : (1 : ℝ) ≤ (H : ℝ) ^ ((3 : ℝ) + 1 / 10) :=
      Real.one_le_rpow (by exact_mod_cast hH_ge1) (by norm_num)
    have h5LL_ge1 : (1 : ℝ) ≤ (5 * LL) ^ 3 := one_le_pow₀ (by linarith)
    have h1_le : (1 : ℝ) ≤ (H : ℝ) ^ ((3 : ℝ) + 1 / 10) * (5 * LL) ^ 3 :=
      one_le_mul_of_one_le_of_one_le hH_pow_ge1 h5LL_ge1
    linarith
  -- Markov on emptyWindows
  have hmarkov : ((emptyWindows X H Z).card : ℝ) * ((H : ℝ) * densQ Q) ^ 6 ≤
      ∑ a ∈ Finset.Ico X (2 * X), (intervalCount Q H a - (H : ℝ) * densQ Q) ^ 6 := by
    have hsub : emptyWindows X H Z ⊆ Finset.Ico X (2 * X) := Finset.filter_subset _ _
    calc ((emptyWindows X H Z).card : ℝ) * ((H : ℝ) * densQ Q) ^ 6
        = ∑ a ∈ emptyWindows X H Z, (intervalCount Q H a - (H : ℝ) * densQ Q) ^ 6 := by
          rw [← nsmul_eq_mul, ← Finset.sum_const]
          apply Finset.sum_congr rfl; intro a ha
          have hemp := (Finset.mem_filter.mp ha).2
          have hcnt0 : intervalCount Q H a = 0 := by
            unfold intervalCount
            apply Finset.sum_eq_zero; intro i hi
            rw [if_neg (hemp i hi)]
          rw [hcnt0, zero_sub, Even.neg_pow ⟨3, by norm_num⟩]
      _ ≤ ∑ a ∈ Finset.Ico X (2 * X), (intervalCount Q H a - (H : ℝ) * densQ Q) ^ 6 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Even.pow_nonneg ⟨3, by norm_num⟩ _)
  -- Lower bound on densQ Q using Mertens bound from Mod1
  have hdens_inv : (densQ Q)⁻¹ ≤ Real.exp 20 * (3 * LL) ^ 8 := by
    have h1 : (densQ Q)⁻¹ = ∏ p ∈ Z.primesBelow, (1 - (1 : ℝ) / p)⁻¹ := by
      unfold densQ; rw [Finset.prod_inv_distrib]
    rw [h1]
    have h2 := prod_inv_one_sub_inv_primesBelow_le Z
    have h3 : (Real.log ((Z + 10 : ℕ) : ℝ)) ^ 8 ≤ (3 * LL) ^ 8 :=
      pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (show 1 ≤ Z + 10 by omega))) hlogZ10 8
    exact h2.trans (mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le)
  have hdens_pos : 0 < densQ Q := densQ_pos hQ_prime
  have hcard_le : ((emptyWindows X H Z).card : ℝ) ≤
      (X : ℝ) * ((Cmom + 1) * (H : ℝ) ^ ((3 : ℝ) + 1 / 10) * (5 * LL) ^ 3) /
        ((H : ℝ) * densQ Q) ^ 6 := by
    have hmul : ∑ a ∈ Finset.Ico X (2 * X), (intervalCount Q H a - (H : ℝ) * densQ Q) ^ 6 ≤
        (X : ℝ) * ((Cmom + 1) * (H : ℝ) ^ ((3 : ℝ) + 1 / 10) * (5 * LL) ^ 3) := by
      have h := mul_le_mul_of_nonneg_left (hinterval_mom.trans hmom_bound) hX_pos.le
      rw [← mul_assoc, mul_one_div_cancel hX_pos.ne', one_mul] at h
      exact h
    exact (le_div_iff₀ (by positivity)).mpr (hmarkov.trans hmul)
  have hfinal_ratio :=
    empty_windows_final_ratio Cmom L LL (densQ Q) H hCmom_pos hlog hloglog hH_ge1 hH_ge
      hdens_pos hdens_inv hr1
  calc ((emptyWindows X H Z).card : ℝ)
      ≤ (X : ℝ) * (((Cmom + 1) * (H : ℝ) ^ ((3 : ℝ) + 1 / 10) * (5 * LL) ^ 3) /
          ((H : ℝ) * densQ Q) ^ 6) := by rw [← mul_div_assoc]; exact hcard_le
    _ ≤ (X : ℝ) * ((H : ℝ) / L ^ 2) := mul_le_mul_of_nonneg_left hfinal_ratio hX_pos.le
    _ = (H : ℝ) * ((X : ℝ) / L ^ 2) := by ring

end EmptyWindows


end Mod4


section Mod5
open Finset Real Nat Filter Asymptotics
open scoped Classical


lemma bad_residues_short_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℕ, 4 ≤ h →
      let Q := h.primesBelow
      let Bad := (Finset.range (prodQ Q)).filter (fun b : ℕ =>
        countQ Q (h - 1) (b : ZMod (prodQ Q)) = 0)
      ((Bad.card : ℝ) / (prodQ Q : ℝ)) * (∏ p ∈ Q, (1 - (1 : ℝ) / p)⁻¹) ^ 2 ≤
        C / ((h - 1 : ℕ) : ℝ) ^ 2 := by
  obtain ⟨Cmom, hCmom_pos, hmom⟩ :=
    unified_centered_moment_bound 3 (by norm_num) (ε := (1 : ℝ) / 10) (by norm_num)
  obtain ⟨Clog, hClog_pos, hlog⟩ :=
    log_pow_le_const_mul_rpow (a := (64 : ℝ)) (δ := (9 : ℝ) / 10) (by norm_num) (by norm_num)
  refine ⟨Cmom * Real.exp 160 * (2 ^ 64 * Clog), by positivity, fun h hh => ?_⟩
  set Q := h.primesBelow
  have hQ : ∀ q ∈ Q, q.Prime := fun q hq => Nat.prime_of_mem_primesBelow hq
  set Bad := (Finset.range (prodQ Q)).filter (fun b : ℕ =>
    countQ Q (h - 1) (b : ZMod (prodQ Q)) = 0)
  have hP_pos : (0 : ℝ) < prodQ Q := by exact_mod_cast prodQ_pos hQ
  have hdens_pos : 0 < densQ Q := densQ_pos hQ
  have hh1 : 1 ≤ h - 1 := by omega
  have hh1_pos : (0 : ℝ) < (h - 1 : ℕ) := by exact_mod_cast hh1
  have hh1_ge1 : (1 : ℝ) ≤ (h - 1 : ℕ) := by exact_mod_cast hh1
  -- Markov on Bad
  have hmarkov : ((Bad.card : ℝ) / (prodQ Q : ℝ)) * (((h - 1 : ℕ) : ℝ) * densQ Q) ^ 6 ≤
      centMom 6 Q (h - 1) := by
    unfold centMom
    have hsum : (Bad.card : ℝ) * (((h - 1 : ℕ) : ℝ) * densQ Q) ^ 6 ≤
        ∑ b ∈ Finset.range (prodQ Q),
          (countQ Q (h - 1) (b : ZMod (prodQ Q)) - ((h - 1 : ℕ) : ℝ) * densQ Q) ^ 6 := by
      calc (Bad.card : ℝ) * (((h - 1 : ℕ) : ℝ) * densQ Q) ^ 6
          = ∑ b ∈ Bad, (countQ Q (h - 1) (b : ZMod (prodQ Q)) - ((h - 1 : ℕ) : ℝ) * densQ Q) ^ 6 := by
            rw [← nsmul_eq_mul, ← Finset.sum_const]
            apply Finset.sum_congr rfl; intro b hb
            have h0 := (Finset.mem_filter.mp hb).2
            rw [h0, zero_sub, Even.neg_pow ⟨3, by norm_num⟩]
        _ ≤ ∑ b ∈ Finset.range (prodQ Q),
              (countQ Q (h - 1) (b : ZMod (prodQ Q)) - ((h - 1 : ℕ) : ℝ) * densQ Q) ^ 6 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun _ _ _ => Even.pow_nonneg ⟨3, by norm_num⟩ _)
    calc ((Bad.card : ℝ) / (prodQ Q : ℝ)) * (((h - 1 : ℕ) : ℝ) * densQ Q) ^ 6
        = (1 / (prodQ Q : ℝ)) * ((Bad.card : ℝ) * (((h - 1 : ℕ) : ℝ) * densQ Q) ^ 6) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)
  -- No prime in Q = h.primesBelow exceeds h - 1!
  have hhi_empty : Q.filter (fun q => h - 1 < q) = ∅ := by
    ext q; simp only [Q, Finset.mem_filter, Nat.mem_primesBelow, Finset.notMem_empty, iff_false]
    intro ⟨⟨hq_lt, _⟩, hq_gt⟩; omega
  have hmom_h : centMom 6 Q (h - 1) ≤ Cmom * ((h - 1 : ℕ) : ℝ) ^ ((3 : ℝ) + 1 / 10) := by
    have h1 := hmom (h - 1) Q hh1 hQ
    rw [hhi_empty, Finset.sum_empty, add_zero, one_pow, mul_one] at h1
    exact h1
  -- Density inverse bound
  have hdens_inv_eq : (densQ Q)⁻¹ = ∏ p ∈ Q, (1 - (1 : ℝ) / p)⁻¹ := by
    unfold densQ; rw [Finset.prod_inv_distrib]
  have hinv_le : (densQ Q)⁻¹ ≤ Real.exp 20 * (Real.log ((h + 10 : ℕ) : ℝ)) ^ 8 := by
    rw [hdens_inv_eq]; exact prod_inv_one_sub_inv_primesBelow_le h
  have hlog_shift : Real.log ((h + 10 : ℕ) : ℝ) ≤ 2 * Real.log (((h - 1 : ℕ) : ℝ) + 10) := by
    have h1 : ((h + 10 : ℕ) : ℝ) ≤ (((h - 1 : ℕ) : ℝ) + 10) ^ 2 := by
      have hcast : ((h - 1 : ℕ) : ℝ) = (h : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
      rw [hcast]; push_cast
      have hh4 : (4 : ℝ) ≤ h := by exact_mod_cast hh
      nlinarith
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at h2
    exact h2
  have hinv8 : ((densQ Q)⁻¹) ^ 8 ≤
      Real.exp 160 * (2 ^ 64 * Clog) * ((h - 1 : ℕ) : ℝ) ^ ((9 : ℝ) / 10) := by
    have h1 : ((densQ Q)⁻¹) ^ 8 ≤ (Real.exp 20 * (Real.log ((h + 10 : ℕ) : ℝ)) ^ 8) ^ 8 :=
      pow_le_pow_left₀ (inv_nonneg.mpr hdens_pos.le) hinv_le 8
    have h2 : (Real.exp 20 * (Real.log ((h + 10 : ℕ) : ℝ)) ^ 8) ^ 8 =
        Real.exp 160 * (Real.log ((h + 10 : ℕ) : ℝ)) ^ 64 := by
      rw [mul_pow, ← Real.exp_nat_mul, ← pow_mul]; norm_num
    have h3 : (Real.log ((h + 10 : ℕ) : ℝ)) ^ 64 ≤
        2 ^ 64 * (Real.log (((h - 1 : ℕ) : ℝ) + 10)) ^ 64 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (show 1 ≤ h + 10 by omega)))
        hlog_shift 64
    have h4 : (Real.log (((h - 1 : ℕ) : ℝ) + 10)) ^ 64 ≤
        Clog * ((h - 1 : ℕ) : ℝ) ^ ((9 : ℝ) / 10) := by
      have h' := hlog ((h - 1 : ℕ) : ℝ) hh1_ge1
      rw [show (64 : ℝ) = ((64 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h'
      exact h'
    rw [h2] at h1
    calc ((densQ Q)⁻¹) ^ 8
        ≤ Real.exp 160 * (Real.log ((h + 10 : ℕ) : ℝ)) ^ 64 := h1
      _ ≤ Real.exp 160 * (2 ^ 64 * (Real.log (((h - 1 : ℕ) : ℝ) + 10)) ^ 64) := by gcongr
      _ ≤ Real.exp 160 * (2 ^ 64 * (Clog * ((h - 1 : ℕ) : ℝ) ^ ((9 : ℝ) / 10))) := by gcongr
      _ = Real.exp 160 * (2 ^ 64 * Clog) * ((h - 1 : ℕ) : ℝ) ^ ((9 : ℝ) / 10) := by ring
  -- Combine Markov + moment + density
  have hbad_div : (Bad.card : ℝ) / (prodQ Q : ℝ) ≤
      Cmom * ((h - 1 : ℕ) : ℝ) ^ ((3 : ℝ) + 1 / 10) / (((h - 1 : ℕ) : ℝ) * densQ Q) ^ 6 :=
    (le_div_iff₀ (by positivity)).mpr (hmarkov.trans hmom_h)
  dsimp only
  rw [← hdens_inv_eq]
  have hcomb_pow : ((h - 1 : ℕ) : ℝ) ^ ((3 : ℝ) + 1 / 10) * ((h - 1 : ℕ) : ℝ) ^ ((9 : ℝ) / 10) /
      ((h - 1 : ℕ) : ℝ) ^ 6 = 1 / ((h - 1 : ℕ) : ℝ) ^ 2 := by
    rw [← Real.rpow_add hh1_pos]
    have h4 : (3 : ℝ) + 1 / 10 + 9 / 10 = (4 : ℝ) := by norm_num
    rw [h4, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp [hh1_pos.ne']
  calc ((Bad.card : ℝ) / (prodQ Q : ℝ)) * ((densQ Q)⁻¹) ^ 2
      ≤ (Cmom * ((h - 1 : ℕ) : ℝ) ^ ((3 : ℝ) + 1 / 10) /
          (((h - 1 : ℕ) : ℝ) * densQ Q) ^ 6) * ((densQ Q)⁻¹) ^ 2 := by gcongr
    _ = Cmom * ((densQ Q)⁻¹) ^ 8 * (((h - 1 : ℕ) : ℝ) ^ ((3 : ℝ) + 1 / 10) /
          ((h - 1 : ℕ) : ℝ) ^ 6) := by
        rw [mul_pow, inv_pow]; field_simp [hdens_pos.ne', hh1_pos.ne']
    _ ≤ Cmom * (Real.exp 160 * (2 ^ 64 * Clog) * ((h - 1 : ℕ) : ℝ) ^ ((9 : ℝ) / 10)) *
          (((h - 1 : ℕ) : ℝ) ^ ((3 : ℝ) + 1 / 10) / ((h - 1 : ℕ) : ℝ) ^ 6) := by gcongr
    _ = (Cmom * Real.exp 160 * (2 ^ 64 * Clog)) *
          (((h - 1 : ℕ) : ℝ) ^ ((3 : ℝ) + 1 / 10) * ((h - 1 : ℕ) : ℝ) ^ ((9 : ℝ) / 10) /
            ((h - 1 : ℕ) : ℝ) ^ 6) := by ring
    _ = (Cmom * Real.exp 160 * (2 ^ 64 * Clog)) * (1 / ((h - 1 : ℕ) : ℝ) ^ 2) := by rw [hcomb_pow]
    _ = (Cmom * Real.exp 160 * (2 ^ 64 * Clog)) / ((h - 1 : ℕ) : ℝ) ^ 2 := by ring

lemma short_gaps_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in Filter.atTop,
      (((Finset.range (2 * X + 1)).filter (fun n =>
        X ≤ Erdos682.p n ∧ Erdos682.p n ≤ 2 * X ∧
        Erdos682.p (n + 1) - Erdos682.p n ≤ 2 * H_param X ∧
        ∀ m ∈ Set.Ioo (Erdos682.p n) (Erdos682.p (n + 1)),
          m.minFac < Erdos682.p (n + 1) - Erdos682.p n)).card : ℝ) ≤
        C * ((X : ℝ) / (Real.log (X : ℝ)) ^ 2) := by
  obtain ⟨Cbad, hCbad_pos, hbad⟩ := bad_residues_short_bound
  set Csieve : ℝ := 2 * (64 * Real.exp 2 * 400) + 1
  refine ⟨Csieve * Cbad, by positivity, ?_⟩
  have hlog_top : Filter.Tendsto (fun X : ℕ => Real.log (X : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow_log : Filter.Tendsto (fun X : ℕ => (Real.log (X : ℝ)) ^ 2 / (X : ℝ) ^ ((3 : ℝ) / 10))
      Filter.atTop (nhds 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (show (0 : ℝ) < 3 / 10 by norm_num)).tendsto_div_nhds_zero
    have hcomp := h.comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def, Real.rpow_natCast] using hcomp
  have hev_log : ∀ᶠ X : ℕ in Filter.atTop, (1000 : ℝ) ≤ Real.log (X : ℝ) :=
    hlog_top.eventually (Filter.eventually_ge_atTop 1000)
  have hev_rpow : ∀ᶠ X : ℕ in Filter.atTop,
      (Real.log (X : ℝ)) ^ 2 / (X : ℝ) ^ ((3 : ℝ) / 10) ≤ 1 := by
    filter_upwards [hpow_log.eventually (gt_mem_nhds zero_lt_one)] with X hX using hX.le
  filter_upwards [hev_log, hev_rpow] with X hlog hrpow
  set L := Real.log (X : ℝ)
  have hL_pos : 0 < L := by linarith
  have hX_ge100 : 100 ≤ X := by
    by_contra hlt; push Not at hlt
    have hle : (X : ℝ) ≤ 100 := by exact_mod_cast (show X ≤ 100 by omega)
    have h1 : Real.log (X : ℝ) ≤ Real.log 100 := by
      rcases eq_or_ne X 0 with rfl | hne
      · simp; positivity
      · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hne) hle
    have h100 : Real.log 100 < 100 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 100 by norm_num); linarith
    linarith
  have hX_pos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  set D := ⌊(X : ℝ) ^ ((1 : ℝ) / 10)⌋₊
  have hX10_ge : (200 : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 10) := by
    have h1 : Real.log 200 ≤ L / 10 := by
      have he6 : (200 : ℝ) < Real.exp 6 := by
        have he : (5 / 2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        have h6 : Real.exp 6 = (Real.exp 1) ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
        have hpow : (5 / 2 : ℝ) ^ 6 < (Real.exp 1) ^ 6 :=
          pow_lt_pow_left₀ he (by norm_num) (by norm_num)
        rw [h6]; norm_num at hpow; linarith
      have hlog200 : Real.log 200 < 6 := (Real.log_lt_iff_lt_exp (by norm_num)).mpr he6
      linarith
    rw [← Real.log_le_log_iff (by norm_num) (Real.rpow_pos_of_pos hX_pos _), Real.log_rpow hX_pos]
    linarith
  have hD_ge100 : 100 ≤ D := by
    have hfl : (X : ℝ) ^ ((1 : ℝ) / 10) - 1 ≤ (D : ℝ) := (Nat.sub_one_lt_floor _).le
    have : (100 : ℝ) ≤ (D : ℝ) := by linarith
    exact_mod_cast this
  have hD_le_rpow : (D : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 10) := Nat.floor_le (by positivity)
  have hD_lt_X : D < X := by
    have hlt : (X : ℝ) ^ ((1 : ℝ) / 10) < (X : ℝ) := by
      conv_rhs => rw [← Real.rpow_one (X : ℝ)]
      exact Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast (show 1 < X by omega)) (by norm_num)
    exact_mod_cast lt_of_le_of_lt hD_le_rpow hlt
  have hlogD_ge : L / 20 ≤ Real.log (D : ℝ) := by
    have hD_ge_half : (1 / 2 : ℝ) * (X : ℝ) ^ ((1 : ℝ) / 10) ≤ (D : ℝ) := by
      have hfl : (X : ℝ) ^ ((1 : ℝ) / 10) - 1 ≤ (D : ℝ) := (Nat.sub_one_lt_floor _).le
      linarith
    have hlog := Real.log_le_log (by positivity) hD_ge_half
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hX_pos _).ne',
        Real.log_rpow hX_pos, Real.log_div one_ne_zero two_ne_zero, Real.log_one, zero_sub] at hlog
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    linarith
  have hH_le : (H_param X : ℝ) ≤ L / 40 := by
    have h1 : 1 ≤ ⌊L / 40⌋₊ := Nat.le_floor (by norm_cast; linarith)
    have hmax : H_param X = ⌊L / 40⌋₊ := max_eq_right h1
    rw [hmax]; exact Nat.floor_le (by linarith)
  set Eshort := (Finset.range (2 * X + 1)).filter (fun n =>
    X ≤ Erdos682.p n ∧ Erdos682.p n ≤ 2 * X ∧
    Erdos682.p (n + 1) - Erdos682.p n ≤ 2 * H_param X ∧
    ∀ m ∈ Set.Ioo (Erdos682.p n) (Erdos682.p (n + 1)),
      m.minFac < Erdos682.p (n + 1) - Erdos682.p n)
  set Hset := (Finset.Icc 4 (2 * H_param X)).filter Even
  have hmaps : ∀ n ∈ Eshort, Erdos682.p (n + 1) - Erdos682.p n ∈ Hset := by
    intro n hn
    simp only [Eshort, Finset.mem_filter] at hn
    have hpn_prime : (Erdos682.p n).Prime := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime n
    have hpn1_prime : (Erdos682.p (n + 1)).Prime := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (n + 1)
    have hlt : Erdos682.p n < Erdos682.p (n + 1) :=
      Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self n)
    have hodd1 : Odd (Erdos682.p n) := hpn_prime.odd_of_ne_two (by omega)
    have hodd2 : Odd (Erdos682.p (n + 1)) := hpn1_prime.odd_of_ne_two (by omega)
    have heven : Even (Erdos682.p (n + 1) - Erdos682.p n) := by
      rcases hodd1 with ⟨a, ha⟩; rcases hodd2 with ⟨b, hb⟩
      exact ⟨b - a, by omega⟩
    have hne2 : Erdos682.p (n + 1) - Erdos682.p n ≠ 2 := by
      intro h2
      have hmem : Erdos682.p n + 1 ∈ Set.Ioo (Erdos682.p n) (Erdos682.p (n + 1)) := by
        simp only [Set.mem_Ioo]; omega
      have hmin := hn.2.2.2.2 (Erdos682.p n + 1) hmem
      have hge2 : 2 ≤ (Erdos682.p n + 1).minFac := (Nat.minFac_prime (by omega)).two_le
      omega
    have hge4 : 4 ≤ Erdos682.p (n + 1) - Erdos682.p n := by
      rcases heven with ⟨k, hk⟩; omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hge4, hn.2.2.2.1⟩, heven⟩
  have hcard_split : (Eshort.card : ℝ) =
      ∑ h ∈ Hset, ((Eshort.filter (fun n => Erdos682.p (n + 1) - Erdos682.p n = h)).card : ℝ) := by
    rw [← Nat.cast_sum, Finset.card_eq_sum_card_fiberwise hmaps]
  rw [hcard_split]
  -- Bound each h ∈ Hset
  have hfor_h : ∀ h ∈ Hset,
      ((Eshort.filter (fun n => Erdos682.p (n + 1) - Erdos682.p n = h)).card : ℝ) ≤
        Csieve * Cbad * ((X : ℝ) / L ^ 2) / ((h - 1 : ℕ) : ℝ) ^ 2 := by
    intro h hh_mem
    simp only [Hset, Finset.mem_filter, Finset.mem_Icc] at hh_mem
    have hh4 : 4 ≤ h := hh_mem.1.1
    have hh_le : h ≤ 2 * H_param X := hh_mem.1.2
    have heven : Even h := hh_mem.2
    set Q := h.primesBelow
    have hQ : ∀ q ∈ Q, q.Prime := fun q hq => Nat.prime_of_mem_primesBelow hq
    set W := primorial (h - 1)
    have hW_eq : prodQ Q = W := prod_primesBelow_eq_primorial h (by omega)
    have hW_pos : 0 < W := primorial_pos (h - 1)
    have hW_le_rpow : (W : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 10) := by
      have hW4 : (W : ℝ) ≤ (4 : ℝ) ^ h := by
        have h1 : W ≤ 4 ^ (h - 1) := primorial_le_four_pow (h - 1)
        have h2 : 4 ^ (h - 1) ≤ 4 ^ h := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le h 1)
        exact_mod_cast h1.trans h2
      have hlog4 : Real.log 4 < 2 := by
        have : (4 : ℝ) < Real.exp 2 := by
          have he := Real.exp_one_gt_d9
          rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]; nlinarith
        exact (Real.log_lt_iff_lt_exp (by norm_num)).mpr this
      have hW4_le : (4 : ℝ) ^ h ≤ (X : ℝ) ^ ((1 : ℝ) / 10) := by
        rw [← Real.log_le_log_iff (by positivity) (Real.rpow_pos_of_pos hX_pos _),
            Real.log_pow, Real.log_rpow hX_pos]
        have hhR : (h : ℝ) ≤ L / 20 := by
          have : (h : ℝ) ≤ 2 * (H_param X : ℝ) := by exact_mod_cast hh_le
          linarith
        nlinarith [Real.log_pos (show (1 : ℝ) < 4 by norm_num)]
      exact hW4.trans hW4_le
    have hW_le_X : W ≤ X := by
      have hlt : (X : ℝ) ^ ((1 : ℝ) / 10) ≤ (X : ℝ) := by
        conv_rhs => rw [← Real.rpow_one (X : ℝ)]
        exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ X by omega)) (by norm_num)
      exact_mod_cast hW_le_rpow.trans hlt
    -- Set of bad residues in ZMod W
    have : NeZero W := ⟨hW_pos.ne'⟩
    set BadQ := (Finset.range (prodQ Q)).filter (fun b : ℕ =>
      countQ Q (h - 1) (b : ZMod (prodQ Q)) = 0)
    set BadW := BadQ.image (fun b : ℕ => (b : ZMod W))
    have hBad_card : BadW.card = BadQ.card := by
      apply Finset.card_image_of_injOn
      intro a ha b hb hab
      have ha' : a < W := hW_eq ▸ Finset.mem_range.mp (Finset.mem_filter.mp ha).1
      have hb' : b < W := hW_eq ▸ Finset.mem_range.mp (Finset.mem_filter.mp hb).1
      have hval := congrArg ZMod.val hab
      rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at hval
      exact hval
    -- Map Eshort_h into BadW.biUnion (primePairs X h) via n ↦ p n
    set Eh := Eshort.filter (fun n => Erdos682.p (n + 1) - Erdos682.p n = h)
    have hinj : Set.InjOn Erdos682.p Eh := fun n1 _ n2 _ heq =>
      (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective heq
    have hsub : Eh.image Erdos682.p ⊆ BadW.biUnion (fun b => primePairs X h b) := by
      intro m hm
      rcases Finset.mem_image.mp hm with ⟨n, hn, rfl⟩
      simp only [Eh, Eshort, Finset.mem_filter] at hn
      rw [Finset.mem_biUnion]
      refine ⟨(Erdos682.p n : ZMod W), ?_, ?_⟩
      · simp only [BadW, BadQ, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
        refine ⟨Erdos682.p n % W, ⟨hW_eq.symm ▸ Nat.mod_lt _ hW_pos, ?_⟩, ?_⟩
        · have hmod_cast : ((Erdos682.p n % W : ℕ) : ZMod (prodQ Q)) =
              (Erdos682.p n : ZMod (prodQ Q)) := by
            rw [← hW_eq, ZMod.natCast_mod]
          rw [hmod_cast]
          unfold countQ countSub
          apply Finset.sum_eq_zero; intro i hi
          simp only [Finset.mem_Icc] at hi
          rw [if_neg]
          intro hu
          have hcop : (Erdos682.p n + i).Coprime (prodQ Q) := by
            have : ((Erdos682.p n + i : ℕ) : ZMod (prodQ Q)) =
                (Erdos682.p n : ZMod (prodQ Q)) + (i : ZMod (prodQ Q)) := by push_cast; rfl
            exact (ZMod.isUnit_iff_coprime _ _).mp (this ▸ hu)
          have hlt : Erdos682.p n < Erdos682.p (n + 1) :=
            Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self n)
          have hmem_oo : Erdos682.p n + i ∈ Set.Ioo (Erdos682.p n) (Erdos682.p (n + 1)) := by
            simp only [Set.mem_Ioo]; omega
          have hmin_lt : (Erdos682.p n + i).minFac < h := by
            rw [← hn.2]; exact hn.1.2.2.2.2 _ hmem_oo
          have hmin_prime : (Erdos682.p n + i).minFac.Prime := Nat.minFac_prime (by omega)
          have hmin_mem : (Erdos682.p n + i).minFac ∈ Q := Nat.mem_primesBelow.mpr ⟨hmin_lt, hmin_prime⟩
          have hmin_dvd_P : (Erdos682.p n + i).minFac ∣ prodQ Q := Finset.dvd_prod_of_mem id hmin_mem
          have hmin_dvd_m : (Erdos682.p n + i).minFac ∣ (Erdos682.p n + i) := Nat.minFac_dvd _
          have h1 : (Erdos682.p n + i).minFac ∣ Nat.gcd (Erdos682.p n + i) (prodQ Q) :=
            Nat.dvd_gcd hmin_dvd_m hmin_dvd_P
          rw [hcop.gcd_eq_one] at h1
          exact hmin_prime.not_dvd_one h1
        · exact ZMod.natCast_mod _ _
      · simp only [primePairs, Finset.mem_filter, Finset.mem_Icc]
        have hlt : Erdos682.p n < Erdos682.p (n + 1) :=
          Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self n)
        have hadd : Erdos682.p n + h = Erdos682.p (n + 1) := by omega
        exact ⟨⟨hn.1.2.1, hn.1.2.2.1⟩, Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime n,
          hadd ▸ Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (n + 1), trivial⟩
    have hEh_le : (Eh.card : ℝ) ≤ ∑ b ∈ BadW, ((primePairs X h b).card : ℝ) := by
      have hnat : Eh.card ≤ ∑ b ∈ BadW, (primePairs X h b).card := by
        rw [← Finset.card_image_of_injOn hinj]
        exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      exact_mod_cast hnat
    -- Bound each primePairs X h b via Selberg sieve!
    have hpair_bd : ∀ b ∈ BadW, ((primePairs X h b).card : ℝ) ≤
        Csieve * (∏ p ∈ Q, (1 - (1 : ℝ) / p)⁻¹) ^ 2 * ((X : ℝ) / L ^ 2) / (W : ℝ) := by
      intro b _
      have hsel := primePairs_card_le_selberg X h D hh4 heven hD_ge100 hD_lt_X hW_le_X b
      have hlogD_pos : 0 < Real.log (D : ℝ) := by linarith
      have hinv_logD : 1 / (Real.log (D : ℝ)) ^ 2 ≤ 400 / L ^ 2 := by
        have hsq : (L / 20) ^ 2 ≤ (Real.log (D : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hlogD_ge 2
        have h1 : (L / 20) ^ 2 = L ^ 2 / 400 := by ring
        rw [h1] at hsq
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have hD6_le : (D : ℝ) ^ 6 ≤ ((X : ℝ) / L ^ 2) / (W : ℝ) := by
        have hD6 : (D : ℝ) ^ 6 ≤ (X : ℝ) ^ ((6 : ℝ) / 10) := by
          calc (D : ℝ) ^ 6 ≤ ((X : ℝ) ^ ((1 : ℝ) / 10)) ^ 6 :=
                pow_le_pow_left₀ (Nat.cast_nonneg D) hD_le_rpow 6
            _ = (X : ℝ) ^ ((6 : ℝ) / 10) := by
                rw [← Real.rpow_natCast _ 6, ← Real.rpow_mul hX_pos.le]; norm_num
        have hL2 : L ^ 2 ≤ (X : ℝ) ^ ((3 : ℝ) / 10) :=
          (div_le_one (Real.rpow_pos_of_pos hX_pos _)).mp hrpow
        have hprod : (D : ℝ) ^ 6 * (W : ℝ) * L ^ 2 ≤ (X : ℝ) := by
          calc (D : ℝ) ^ 6 * (W : ℝ) * L ^ 2
              ≤ (X : ℝ) ^ ((6 : ℝ) / 10) * (X : ℝ) ^ ((1 : ℝ) / 10) * (X : ℝ) ^ ((3 : ℝ) / 10) := by
                gcongr
            _ = (X : ℝ) := by
                rw [← Real.rpow_add hX_pos, ← Real.rpow_add hX_pos]
                norm_num
        rw [le_div_iff₀ (by exact_mod_cast hW_pos), le_div_iff₀ (by positivity)]
        linarith
      have hprod_ge1 : (1 : ℝ) ≤ (∏ p ∈ Q, (1 - (1 : ℝ) / p)⁻¹) ^ 2 := by
        have h1 : (1 : ℝ) ≤ ∏ p ∈ Q, (1 - (1 : ℝ) / p)⁻¹ := by
          apply one_le_prod_real; intro p hp
          have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hQ p hp).two_le
          have hpos : 0 < 1 - (1 : ℝ) / p := by
            have : (1 : ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
            linarith
          exact (one_le_inv₀ hpos).mpr (by linarith [show (0 : ℝ) < 1 / p by positivity])
        nlinarith
      have hmain : (2 * (X : ℝ) / (W : ℝ)) *
          (64 * Real.exp 2 * (∏ p ∈ Q, (1 - (1 : ℝ) / p)⁻¹) ^ 2 / (Real.log (D : ℝ)) ^ 2) ≤
          2 * (64 * Real.exp 2 * 400) * (∏ p ∈ Q, (1 - (1 : ℝ) / p)⁻¹) ^ 2 *
            ((X : ℝ) / L ^ 2) / (W : ℝ) := by
        have h1 : (2 * (X : ℝ) / (W : ℝ)) *
            (64 * Real.exp 2 * (∏ p ∈ Q, (1 - (1 : ℝ) / p)⁻¹) ^ 2 / (Real.log (D : ℝ)) ^ 2) =
            (2 * 64 * Real.exp 2 * (∏ p ∈ Q, (1 - (1 : ℝ) / p)⁻¹) ^ 2 * (X : ℝ) / (W : ℝ)) *
              (1 / (Real.log (D : ℝ)) ^ 2) := by ring
        rw [h1]
        calc _ ≤ (2 * 64 * Real.exp 2 * (∏ p ∈ Q, (1 - (1 : ℝ) / p)⁻¹) ^ 2 * (X : ℝ) / (W : ℝ)) *
              (400 / L ^ 2) := by gcongr
          _ = _ := by ring
      have herr : (D : ℝ) ^ 6 ≤ 1 * (∏ p ∈ Q, (1 - (1 : ℝ) / p)⁻¹) ^ 2 * ((X : ℝ) / L ^ 2) / (W : ℝ) := by
        calc (D : ℝ) ^ 6 ≤ ((X : ℝ) / L ^ 2) / (W : ℝ) := hD6_le
          _ ≤ (∏ p ∈ Q, (1 - (1 : ℝ) / p)⁻¹) ^ 2 * (((X : ℝ) / L ^ 2) / (W : ℝ)) :=
              le_mul_of_one_le_left (by positivity) hprod_ge1
          _ = _ := by ring
      have hsel' : ((primePairs X h b).card : ℝ) ≤
          (2 * (X : ℝ) / (W : ℝ)) *
            (64 * Real.exp 2 * (∏ p ∈ Q, (1 - (1 : ℝ) / p)⁻¹) ^ 2 / (Real.log (D : ℝ)) ^ 2) +
          (D : ℝ) ^ 6 := hsel
      exact hsel'.trans ((add_le_add hmain herr).trans_eq (by simp only [Csieve]; ring))
    have hbad_h := hbad h hh4
    calc (Eh.card : ℝ)
        ≤ ∑ b ∈ BadW, ((primePairs X h b).card : ℝ) := hEh_le
      _ ≤ ∑ _b ∈ BadW, (Csieve * (∏ p ∈ Q, (1 - (1 : ℝ) / p)⁻¹) ^ 2 * ((X : ℝ) / L ^ 2) / (W : ℝ)) :=
          Finset.sum_le_sum hpair_bd
      _ = Csieve * ((X : ℝ) / L ^ 2) *
            (((BadQ.card : ℝ) / (prodQ Q : ℝ)) * (∏ p ∈ Q, (1 - (1 : ℝ) / p)⁻¹) ^ 2) := by
          rw [Finset.sum_const, hBad_card, hW_eq, nsmul_eq_mul]; ring
      _ ≤ Csieve * ((X : ℝ) / L ^ 2) * (Cbad / ((h - 1 : ℕ) : ℝ) ^ 2) := by gcongr
      _ = Csieve * Cbad * ((X : ℝ) / L ^ 2) / ((h - 1 : ℕ) : ℝ) ^ 2 := by ring
  -- Sum 1/(h - 1)^2 over h ∈ Hset
  have hsum_inv : ∑ h ∈ Hset, (1 : ℝ) / ((h - 1 : ℕ) : ℝ) ^ 2 ≤ 1 := by
    have hsub1 : Hset ⊆ Finset.Icc 4 (2 * H_param X) := Finset.filter_subset _ _
    calc ∑ h ∈ Hset, (1 : ℝ) / ((h - 1 : ℕ) : ℝ) ^ 2
        ≤ ∑ h ∈ Finset.Icc 4 (2 * H_param X), (1 : ℝ) / ((h - 1 : ℕ) : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub1 (fun _ _ _ => by positivity)
      _ = ∑ j ∈ (Finset.Icc 4 (2 * H_param X)).image (fun h : ℕ => (h - 1 : ℕ)),
            (1 : ℝ) / (j : ℝ) ^ 2 := by
          rw [Finset.sum_image (f := fun j : ℕ => (1 : ℝ) / (j : ℝ) ^ 2)
              (g := fun h : ℕ => (h - 1 : ℕ))]
          intro a ha b hb hab
          simp only [Finset.mem_coe, Finset.mem_Icc] at ha hb
          dsimp only at hab
          omega
      _ ≤ ∑ j ∈ Finset.Icc 3 (2 * H_param X), (1 : ℝ) / (j : ℝ) ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro j hj
            simp only [Finset.mem_image, Finset.mem_Icc] at hj ⊢
            rcases hj with ⟨h, ⟨h4, hle⟩, rfl⟩
            omega
          · intro _ _ _; positivity
      _ ≤ 1 / ((3 : ℝ) - 1) := sum_inv_sq_Icc_le 3 (2 * H_param X) (by norm_num)
      _ ≤ 1 := by norm_num
  calc ∑ h ∈ Hset, ((Eshort.filter (fun n => Erdos682.p (n + 1) - Erdos682.p n = h)).card : ℝ)
      ≤ ∑ h ∈ Hset, (Csieve * Cbad * ((X : ℝ) / L ^ 2) / ((h - 1 : ℕ) : ℝ) ^ 2) :=
        Finset.sum_le_sum hfor_h
    _ = Csieve * Cbad * ((X : ℝ) / L ^ 2) * ∑ h ∈ Hset, (1 : ℝ) / ((h - 1 : ℕ) : ℝ) ^ 2 := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro h _; ring
    _ ≤ Csieve * Cbad * ((X : ℝ) / L ^ 2) * 1 := by gcongr
    _ = Csieve * Cbad * ((X : ℝ) / L ^ 2) := by ring

lemma main_exceptional_count :
    (fun X : ℕ => ({n | Erdos682.p n ∈ Set.Icc X (2 * X) ∧
        ∀ m ∈ Set.Ioo (Erdos682.p n) (Erdos682.p (n + 1)),
          m.minFac < Erdos682.p (n + 1) - Erdos682.p n}.ncard : ℝ)) =O[Filter.atTop]
      fun X : ℕ => (X : ℝ) / Real.log (X : ℝ) ^ 2 := by
  obtain ⟨Cshort, hCshort_pos, hshort⟩ := short_gaps_bound
  have hemp := empty_windows_bound
  have hlog_top : Filter.Tendsto (fun X : ℕ => Real.log (X : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog2_div : Filter.Tendsto (fun X : ℕ => (Real.log (X : ℝ)) ^ 2 / (X : ℝ))
      Filter.atTop (nhds 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) zero_lt_one).tendsto_div_nhds_zero
    have hcomp := h.comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def, Real.rpow_natCast, Real.rpow_one] using hcomp
  have hev_log : ∀ᶠ X : ℕ in Filter.atTop, (1000 : ℝ) ≤ Real.log (X : ℝ) :=
    hlog_top.eventually (Filter.eventually_ge_atTop 1000)
  have hev_1 : ∀ᶠ X : ℕ in Filter.atTop, (Real.log (X : ℝ)) ^ 2 / (X : ℝ) ≤ 1 := by
    filter_upwards [hlog2_div.eventually (gt_mem_nhds zero_lt_one)] with X hX using hX.le
  rw [Asymptotics.isBigO_iff]
  refine ⟨Cshort + 3, ?_⟩
  filter_upwards [hshort, hemp, hev_log, hev_1] with X hXshort hXemp hlog hX1
  set L := Real.log (X : ℝ)
  have hL_pos : 0 < L := by linarith
  have hX_ge100 : 100 ≤ X := by
    by_contra hlt; push Not at hlt
    have hle : (X : ℝ) ≤ 100 := by exact_mod_cast (show X ≤ 100 by omega)
    have h1 : Real.log (X : ℝ) ≤ Real.log 100 := by
      rcases eq_or_ne X 0 with rfl | hne
      · simp; positivity
      · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hne) hle
    have h100 : Real.log 100 < 100 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 100 by norm_num); linarith
    linarith
  have hX_pos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hscale_ge1 : 1 ≤ (X : ℝ) / L ^ 2 := by
    have h1 : L ^ 2 ≤ (X : ℝ) := (div_le_one hX_pos).mp hX1
    exact (one_le_div (by positivity)).mpr h1
  set E := (Finset.range (2 * X + 1)).filter (fun n =>
    X ≤ Erdos682.p n ∧ Erdos682.p n ≤ 2 * X ∧
    ∀ m ∈ Set.Ioo (Erdos682.p n) (Erdos682.p (n + 1)),
      m.minFac < Erdos682.p (n + 1) - Erdos682.p n)
  have hset_eq : {n | Erdos682.p n ∈ Set.Icc X (2 * X) ∧
      ∀ m ∈ Set.Ioo (Erdos682.p n) (Erdos682.p (n + 1)),
        m.minFac < Erdos682.p (n + 1) - Erdos682.p n} = (E : Set ℕ) := by
    ext n
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, Finset.mem_coe, E, Finset.mem_filter,
      Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have hle : n ≤ Erdos682.p n := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).id_le n
      exact ⟨by omega, h1, h2, h3⟩
    · rintro ⟨_, h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, h3⟩
  rw [hset_eq, Set.ncard_coe_finset]
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity)]
  -- Partition E into 4 regimes
  set Ebdry := E.filter (fun n => 2 * X < Erdos682.p (n + 1))
  set Ehuge := E.filter (fun n => Erdos682.p (n + 1) ≤ 2 * X ∧
    Z_param X ≤ Erdos682.p (n + 1) - Erdos682.p n)
  set Emed := E.filter (fun n => Erdos682.p (n + 1) ≤ 2 * X ∧
    2 * H_param X < Erdos682.p (n + 1) - Erdos682.p n ∧
    Erdos682.p (n + 1) - Erdos682.p n < Z_param X)
  set Eshort := (Finset.range (2 * X + 1)).filter (fun n =>
    X ≤ Erdos682.p n ∧ Erdos682.p n ≤ 2 * X ∧
    Erdos682.p (n + 1) - Erdos682.p n ≤ 2 * H_param X ∧
    ∀ m ∈ Set.Ioo (Erdos682.p n) (Erdos682.p (n + 1)),
      m.minFac < Erdos682.p (n + 1) - Erdos682.p n)
  have hcover : E ⊆ Ebdry ∪ Ehuge ∪ Emed ∪ Eshort := by
    intro n hn
    simp only [Finset.mem_union]
    by_cases h1 : Erdos682.p (n + 1) - Erdos682.p n ≤ 2 * H_param X
    · right
      simp only [E, Finset.mem_filter] at hn
      simp only [Eshort, Finset.mem_filter]
      exact ⟨hn.1, hn.2.1, hn.2.2.1, h1, hn.2.2.2⟩
    · left
      by_cases h2 : 2 * X < Erdos682.p (n + 1)
      · left; left; exact Finset.mem_filter.mpr ⟨hn, h2⟩
      · by_cases h3 : Z_param X ≤ Erdos682.p (n + 1) - Erdos682.p n
        · left; right; exact Finset.mem_filter.mpr ⟨hn, by omega, h3⟩
        · right; exact Finset.mem_filter.mpr ⟨hn, by omega, by omega, by omega⟩
  have hcard_sum : (E.card : ℝ) ≤
      (Ebdry.card : ℝ) + (Ehuge.card : ℝ) + (Emed.card : ℝ) + (Eshort.card : ℝ) := by
    have hnat : E.card ≤ Ebdry.card + Ehuge.card + Emed.card + Eshort.card := by
      calc E.card ≤ (Ebdry ∪ Ehuge ∪ Emed ∪ Eshort).card := Finset.card_le_card hcover
        _ ≤ (Ebdry ∪ Ehuge ∪ Emed).card + Eshort.card := Finset.card_union_le _ _
        _ ≤ (Ebdry ∪ Ehuge).card + Emed.card + Eshort.card := by
            have := Finset.card_union_le (Ebdry ∪ Ehuge) Emed; omega
        _ ≤ Ebdry.card + Ehuge.card + Emed.card + Eshort.card := by
            have := Finset.card_union_le Ebdry Ehuge; omega
    exact_mod_cast hnat
  -- 1. Boundary gap: ≤ 1 ≤ X / L^2
  have hbdry : (Ebdry.card : ℝ) ≤ (X : ℝ) / L ^ 2 := by
    have hle1 : Ebdry.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro n1 hn1 n2 hn2
      simp only [Ebdry, E, Finset.mem_filter] at hn1 hn2
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hle : Erdos682.p (n1 + 1) ≤ Erdos682.p n2 :=
          (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone (Nat.succ_le_of_lt hlt)
        omega
      · have hle : Erdos682.p (n2 + 1) ≤ Erdos682.p n1 :=
          (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone (Nat.succ_le_of_lt hgt)
        omega
    exact (by exact_mod_cast hle1 : (Ebdry.card : ℝ) ≤ 1).trans hscale_ge1
  -- 2. Huge gaps: ≤ X / L^2
  have hhuge : (Ehuge.card : ℝ) ≤ (X : ℝ) / L ^ 2 := by
    have hpw : Set.PairwiseDisjoint (↑Ehuge : Set ℕ)
        (fun n => Finset.Ioc (Erdos682.p n) (Erdos682.p (n + 1))) := by
      intro n1 _ n2 _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_Ioc] at hx1 hx2
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hle : Erdos682.p (n1 + 1) ≤ Erdos682.p n2 :=
          (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone (Nat.succ_le_of_lt hlt)
        omega
      · have hle : Erdos682.p (n2 + 1) ≤ Erdos682.p n1 :=
          (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone (Nat.succ_le_of_lt hgt)
        omega
    have hsub_Ioc : Ehuge.biUnion (fun n => Finset.Ioc (Erdos682.p n) (Erdos682.p (n + 1))) ⊆
        Finset.Ioc X (2 * X) := by
      intro x hx
      rcases Finset.mem_biUnion.mp hx with ⟨n, hn, hxn⟩
      simp only [Ehuge, E, Finset.mem_filter] at hn
      simp only [Finset.mem_Ioc] at hxn ⊢
      omega
    have hnat : Ehuge.card * Z_param X ≤ X := by
      calc Ehuge.card * Z_param X
          = ∑ _n ∈ Ehuge, Z_param X := by simp
        _ ≤ ∑ n ∈ Ehuge, (Finset.Ioc (Erdos682.p n) (Erdos682.p (n + 1))).card := by
            apply Finset.sum_le_sum; intro n hn
            simp only [Nat.card_Ioc]
            exact (Finset.mem_filter.mp hn).2.2
        _ = (Ehuge.biUnion (fun n => Finset.Ioc (Erdos682.p n) (Erdos682.p (n + 1)))).card :=
            (Finset.card_biUnion hpw).symm
        _ ≤ (Finset.Ioc X (2 * X)).card := Finset.card_le_card hsub_Ioc
        _ = X := by simp [Nat.card_Ioc]; omega
    have hZ_ge : L ^ 2 ≤ (Z_param X : ℝ) := by
      have h1 : L ^ 2 ≤ (⌈L ^ 2⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : (Z_param X : ℝ) = (⌈L ^ 2⌉₊ : ℝ) + 1 := by simp [Z_param, L]
      linarith
    have hreal : (Ehuge.card : ℝ) * L ^ 2 ≤ (X : ℝ) := by
      calc (Ehuge.card : ℝ) * L ^ 2 ≤ (Ehuge.card : ℝ) * (Z_param X : ℝ) := by gcongr
        _ ≤ (X : ℝ) := by exact_mod_cast hnat
    exact (le_div_iff₀ (by positivity)).mpr hreal
  -- 3. Medium-long gaps: ≤ X / L^2
  have hmed : (Emed.card : ℝ) ≤ (X : ℝ) / L ^ 2 := by
    have hpw : Set.PairwiseDisjoint (↑Emed : Set ℕ)
        (fun n => Finset.Ico (Erdos682.p n) (Erdos682.p n + H_param X)) := by
      intro n1 hn1 n2 hn2 hne
      rw [Function.onFun, Finset.disjoint_left]
      intro a ha1 ha2
      simp only [Finset.mem_coe, Emed, Finset.mem_filter] at hn1 hn2
      simp only [Finset.mem_Ico] at ha1 ha2
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hle : Erdos682.p (n1 + 1) ≤ Erdos682.p n2 :=
          (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone (Nat.succ_le_of_lt hlt)
        omega
      · have hle : Erdos682.p (n2 + 1) ≤ Erdos682.p n1 :=
          (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone (Nat.succ_le_of_lt hgt)
        omega
    have hsub_emp : Emed.biUnion (fun n => Finset.Ico (Erdos682.p n) (Erdos682.p n + H_param X)) ⊆
        emptyWindows X (H_param X) (Z_param X) := by
      intro a ha
      rcases Finset.mem_biUnion.mp ha with ⟨n, hn, han⟩
      simp only [Emed, E, Finset.mem_filter] at hn
      simp only [Finset.mem_Ico] at han
      simp only [emptyWindows, Finset.mem_filter, Finset.mem_Ico]
      refine ⟨⟨by omega, by omega⟩, fun i hi => ?_⟩
      simp only [Finset.mem_Icc] at hi
      intro hcop
      have hmem_oo : a + i ∈ Set.Ioo (Erdos682.p n) (Erdos682.p (n + 1)) := by
        simp only [Set.mem_Ioo]; omega
      have hmin_lt : (a + i).minFac < Z_param X :=
        lt_trans (hn.1.2.2.2 _ hmem_oo) hn.2.2.2
      have hmin_prime : (a + i).minFac.Prime := Nat.minFac_prime (by omega)
      have hmin_mem : (a + i).minFac ∈ (Z_param X).primesBelow :=
        Nat.mem_primesBelow.mpr ⟨hmin_lt, hmin_prime⟩
      have hmin_dvd_P : (a + i).minFac ∣ prodQ (Z_param X).primesBelow :=
        Finset.dvd_prod_of_mem id hmin_mem
      have h1 : (a + i).minFac ∣ Nat.gcd (a + i) (prodQ (Z_param X).primesBelow) :=
        Nat.dvd_gcd (Nat.minFac_dvd _) hmin_dvd_P
      rw [hcop.gcd_eq_one] at h1
      exact hmin_prime.not_dvd_one h1
    have hnat : Emed.card * H_param X ≤ (emptyWindows X (H_param X) (Z_param X)).card := by
      calc Emed.card * H_param X
          = ∑ _n ∈ Emed, H_param X := by simp
        _ = ∑ n ∈ Emed, (Finset.Ico (Erdos682.p n) (Erdos682.p n + H_param X)).card := by
            apply Finset.sum_congr rfl; intro n _; simp [Nat.card_Ico]
        _ = (Emed.biUnion (fun n => Finset.Ico (Erdos682.p n) (Erdos682.p n + H_param X))).card :=
            (Finset.card_biUnion hpw).symm
        _ ≤ (emptyWindows X (H_param X) (Z_param X)).card := Finset.card_le_card hsub_emp
    have hH_pos : (0 : ℝ) < H_param X := by exact_mod_cast (show 0 < H_param X by simp [H_param])
    have hnatR : (Emed.card : ℝ) * (H_param X : ℝ) ≤
        ((emptyWindows X (H_param X) (Z_param X)).card : ℝ) := by exact_mod_cast hnat
    have hreal : (Emed.card : ℝ) * (H_param X : ℝ) ≤ (H_param X : ℝ) * ((X : ℝ) / L ^ 2) :=
      hnatR.trans hXemp
    nlinarith
  linarith


end Mod5


end Erdos682Proof

theorem OMA.solution : type_of% @Erdos682.erdos_682.variants.exceptional_count :=
  Erdos682Proof.main_exceptional_count
