import OMAStatements.S_oeis_a347205
import Mathlib

namespace OMA.P_oeis_a347205

open OMA.S_oeis_a347205

private lemma wt_two_mul (n : ℕ) : wt (2 * n) = wt n := by
  cases n with
  | zero => rfl
  | succ n =>
    have h : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    rw [h, wt]
    have hmod : (2 * n + 1 + 1) % 2 = 0 := by omega
    have hdiv : (2 * n + 1 + 1) / 2 = n + 1 := by omega
    rw [hmod, hdiv, zero_add]

private lemma wt_two_mul_add_one (n : ℕ) : wt (2 * n + 1) = wt n + 1 := by
  rw [wt]
  have hmod : (2 * n + 1) % 2 = 1 := by omega
  have hdiv : (2 * n + 1) / 2 = n := by omega
  rw [hmod, hdiv, add_comm]

private lemma wt_pos_of_pos (n : ℕ) (hn : 1 ≤ n) : 1 ≤ wt n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · have hm1 : 1 ≤ m := by omega
      rw [show n = 2 * m by omega, wt_two_mul]
      exact ih m (by omega) hm1
    · rw [hm, wt_two_mul_add_one]; omega

private lemma wt_sub_two_pow_v2 (n : ℕ) (hn : 1 ≤ n) :
    wt (n - 2 ^ padicValNat 2 n) + 1 = wt n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · have hm1 : 1 ≤ m := by omega
      have hn_eq : n = 2 * m := by omega
      have hval : padicValNat 2 n = padicValNat 2 m + 1 := by
        rw [hn_eq, padicValNat.mul (by omega) (by omega), padicValNat.self (by omega)]
        omega
      have hsub : n - 2 ^ padicValNat 2 n = 2 * (m - 2 ^ padicValNat 2 m) := by
        rw [hval, hn_eq, pow_succ', Nat.mul_sub_left_distrib]
      rw [hsub, wt_two_mul, hn_eq, wt_two_mul]
      exact ih m (by omega) hm1
    · have hval : padicValNat 2 n = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
      rw [hval, pow_zero, hm, Nat.add_sub_cancel, wt_two_mul, wt_two_mul_add_one]

private lemma T_two_mul (n k : ℕ) (hn : 1 ≤ n) :
    T347205 (2 * n) k = ∑ i ∈ Finset.Icc 1 k, T347205 n i := by
  obtain ⟨m, hm⟩ : ∃ m, 2 * n = m + 1 := ⟨2 * n - 1, by omega⟩
  rw [hm, T347205]
  have hmod : ¬((m + 1) % 2 = 1) := by omega
  have hdiv : (m + 1) / 2 = n := by omega
  simp only [hmod, ↓reduceIte, hdiv]

private lemma T_two_mul_add_one (n k : ℕ) :
    T347205 (2 * n + 1) k = if k = wt n + 2 then T347205 n (wt n + 1) else T347205 n k := by
  rw [T347205]
  have hmod : (2 * n + 1) % 2 = 1 := by omega
  have hdiv : (2 * n + 1) / 2 = n := by omega
  simp only [hmod, ↓reduceIte, hdiv]

-- Core 5-line lemma: T(2n, k) = T(n - 2^v2(n), k) for all n >= 1 and 1 <= k <= wt(n)!
private lemma T_two_mul_eq_sub (n : ℕ) (hn : 1 ≤ n) :
    ∀ k : ℕ, 1 ≤ k → k ≤ wt n → T347205 (2 * n) k = T347205 (n - 2 ^ padicValNat 2 n) k := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro k hk1 hkw
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- n = 2 * m (m >= 1)
      have hm1 : 1 ≤ m := by omega
      have hn_eq : n = 2 * m := by omega
      have hval : padicValNat 2 n = padicValNat 2 m + 1 := by
        rw [hn_eq, padicValNat.mul (by omega) (by omega), padicValNat.self (by omega)]
        omega
      have hsub : n - 2 ^ padicValNat 2 n = 2 * (m - 2 ^ padicValNat 2 m) := by
        rw [hval, hn_eq, pow_succ', Nat.mul_sub_left_distrib]
      have hwm : wt n = wt m := by rw [hn_eq, wt_two_mul]
      rw [T_two_mul n k hn, hsub]
      by_cases hsub0 : m - 2 ^ padicValNat 2 m = 0
      · -- m = 2^r => wt m = 1, k = 1!
        have hk1_eq : k = 1 := by
          have : wt (m - 2 ^ padicValNat 2 m) + 1 = wt m := wt_sub_two_pow_v2 m hm1
          rw [hsub0, wt] at this
          omega
        subst hk1_eq
        rw [hsub0, mul_zero, T347205, if_pos rfl, Finset.Icc_self, Finset.sum_singleton]
        rw [hn_eq, ih m (by omega) hm1 1 (le_refl 1) (by omega), hsub0, T347205, if_pos rfl]
      · rw [T_two_mul (m - 2 ^ padicValNat 2 m) k (by omega)]
        refine Finset.sum_congr rfl fun i hi => ?_
        simp only [Finset.mem_Icc] at hi
        rw [hn_eq]
        exact ih m (by omega) hm1 i hi.1 (by omega)
    · -- n = 2 * m + 1 (odd): v2(n) = 0, n - 1 = 2 * m!
      have hval : padicValNat 2 n = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
      rw [hval, pow_zero, hm, Nat.add_sub_cancel]
      rw [T_two_mul (2 * m + 1) k (by omega)]
      have hterm : ∀ i ∈ Finset.Icc 1 k, T347205 (2 * m + 1) i = T347205 m i := by
        intro i hi
        simp only [Finset.mem_Icc] at hi
        rw [T_two_mul_add_one, if_neg]
        rw [hm, wt_two_mul_add_one] at hkw
        omega
      rw [Finset.sum_congr rfl hterm]
      cases m with
      | zero =>
        rw [hm, wt_two_mul_add_one] at hkw
        have hk1_eq : k = 1 := by simp [wt] at hkw; omega
        subst hk1_eq
        simp [T347205]
      | succ m =>
        rw [T_two_mul (m + 1) k (Nat.succ_pos m)]

private lemma a347205_eq_T (n : ℕ) : a347205 n = T347205 n (wt n + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [a347205, T347205, wt]
    | succ n =>
      rcases Nat.even_or_odd (n + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
      · -- n + 1 = 2 * m (m >= 1)
        have hm1 : 1 ≤ m := by omega
        have hn_eq : n + 1 = 2 * m := by omega
        rw [a347205]
        have hmod : ¬((n + 1) % 2 = 1) := by omega
        have hdiv : (n + 1) / 2 = m := by omega
        simp only [hmod, ↓reduceIte, hdiv]
        have hsub_lt : m - 2 ^ padicValNat 2 m < n + 1 := by
          have := Nat.sub_le m (2 ^ padicValNat 2 m); omega
        rw [ih m (by omega), ih (m - 2 ^ padicValNat 2 m) hsub_lt]
        rw [hn_eq, wt_two_mul, T_two_mul m (wt m + 1) hm1]
        have hIcc : Finset.Icc 1 (wt m + 1) = insert (wt m + 1) (Finset.Icc 1 (wt m)) := by
          ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hIcc, Finset.sum_insert (by simp)]
        have hsum_eq : ∑ i ∈ Finset.Icc 1 (wt m), T347205 m i = T347205 (2 * m) (wt m) :=
          (T_two_mul m (wt m) hm1).symm
        rw [hsum_eq, T_two_mul_eq_sub m hm1 (wt m) (wt_pos_of_pos m hm1) (le_refl _),
          wt_sub_two_pow_v2 m hm1]
      · -- n + 1 = 2 * m + 1
        rw [a347205]
        have hmod : (n + 1) % 2 = 1 := by omega
        have hdiv : (n + 1) / 2 = m := by omega
        simp only [hmod, ↓reduceIte, hdiv]
        rw [ih m (by omega), hm, wt_two_mul_add_one, T_two_mul_add_one, if_pos rfl]

private theorem main_proved :
    ∀ n : ℕ,
      a347205 n = T347205 n (wt n + 1) ∧
      a347205 (2 * n) = ∑ k ∈ Finset.Icc 1 (wt n + 1), T347205 n k := by
  intro n
  refine ⟨a347205_eq_T n, ?_⟩
  cases n with
  | zero => simp [a347205, T347205, wt]
  | succ n =>
    rw [a347205_eq_T (2 * (n + 1)), wt_two_mul, T_two_mul (n + 1) (wt (n + 1) + 1) (Nat.succ_pos n)]

end OMA.P_oeis_a347205

theorem OMA.solution : type_of% @OMA.S_oeis_a347205.main :=
  OMA.P_oeis_a347205.main_proved
