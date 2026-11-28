import OMAStatements.S_oeis_a246695
import Mathlib

namespace A246695Aux

open OMA.S_oeis_a246695 in
lemma T_step (n k : ℕ) : T (n + 2) (k + 2) = T (n + 2) k + 1 := by
  rw [T]

open OMA.S_oeis_a246695 in
lemma T_col (N : ℕ) (hN : 2 ≤ N) (k : ℕ) : T N k = T N (k % 2) + ((k / 2 : ℕ) : ℤ) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | _ | k
    · simp
    · simp
    · rw [T_step, ih k (by omega), show (k + 2) % 2 = k % 2 from by omega,
        show (k + 2) / 2 = k / 2 + 1 from by omega]
      push_cast
      ring

open OMA.S_oeis_a246695 in
lemma T0_even (N : ℕ) (hN : 2 ≤ N) (hp : N % 2 = 0) : T N 0 = T (N - 1) (N - 1) + 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  rw [T, if_neg (by omega)]
  rfl

open OMA.S_oeis_a246695 in
lemma T1_even (N : ℕ) (hN : 2 ≤ N) (hp : N % 2 = 0) : T N 1 = T (N - 1) (N - 2) + 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  rw [T, if_neg (by omega)]
  rfl

open OMA.S_oeis_a246695 in
lemma T0_odd (N : ℕ) (hN : 2 ≤ N) (hp : N % 2 = 1) : T N 0 = T (N - 1) (N - 2) + 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  rw [T, if_pos (by omega)]
  rfl

open OMA.S_oeis_a246695 in
lemma T1_odd (N : ℕ) (hN : 2 ≤ N) (hp : N % 2 = 1) : T N 1 = T (N - 1) (N - 1) + 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  rw [T, if_pos (by omega)]
  rfl

open OMA.S_oeis_a246695 in
lemma closed (m : ℕ) :
    T (2 * m + 2) 0 = ((m : ℤ) + 1) ^ 2 + (m + 1) + 1 ∧ T (2 * m + 2) 1 = ((m : ℤ) + 1) ^ 2 + 1 ∧
    T (2 * m + 3) 0 = ((m : ℤ) + 1) ^ 2 + (m + 1) + 1 ∧ T (2 * m + 3) 1 = ((m : ℤ) + 2) ^ 2 + 1 := by
  induction m with
  | zero =>
    have e20 : T 2 0 = 3 := by
      rw [T0_even 2 (by omega) (by omega)]
      simp [T]
    have e21 : T 2 1 = 2 := by
      rw [T1_even 2 (by omega) (by omega)]
      simp [T]
    have e22 : T 2 2 = 4 := by
      rw [T_col 2 (by omega) 2]
      simp [e20]
    have e30 : T 3 0 = 3 := by
      rw [T0_odd 3 (by omega) (by omega)]
      simp [e21]
    have e31 : T 3 1 = 5 := by
      rw [T1_odd 3 (by omega) (by omega)]
      simp [e22]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using e20
    · simpa using e21
    · simpa using e30
    · simpa using e31
  | succ m ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    have c1 := T_col (2 * m + 3) (by omega) (2 * m + 3)
    have c2 := T_col (2 * m + 3) (by omega) (2 * m + 2)
    rw [show (2 * m + 3) % 2 = 1 from by omega, show (2 * m + 3) / 2 = m + 1 from by omega] at c1
    rw [show (2 * m + 2) % 2 = 0 from by omega, show (2 * m + 2) / 2 = m + 1 from by omega] at c2
    have a1 : T (2 * m + 4) 0 = ((m : ℤ) + 2) ^ 2 + (m + 2) + 1 := by
      rw [T0_even (2 * m + 4) (by omega) (by omega), show 2 * m + 4 - 1 = 2 * m + 3 from by omega,
        c1, h4]
      push_cast
      ring
    have a2 : T (2 * m + 4) 1 = ((m : ℤ) + 2) ^ 2 + 1 := by
      rw [T1_even (2 * m + 4) (by omega) (by omega), show 2 * m + 4 - 1 = 2 * m + 3 from by omega,
        show 2 * m + 4 - 2 = 2 * m + 2 from by omega, c2, h3]
      push_cast
      ring
    have c3 := T_col (2 * m + 4) (by omega) (2 * m + 3)
    have c4 := T_col (2 * m + 4) (by omega) (2 * m + 4)
    rw [show (2 * m + 3) % 2 = 1 from by omega, show (2 * m + 3) / 2 = m + 1 from by omega] at c3
    rw [show (2 * m + 4) % 2 = 0 from by omega, show (2 * m + 4) / 2 = m + 2 from by omega] at c4
    have a3 : T (2 * m + 5) 0 = ((m : ℤ) + 2) ^ 2 + (m + 2) + 1 := by
      rw [T0_odd (2 * m + 5) (by omega) (by omega), show 2 * m + 5 - 1 = 2 * m + 4 from by omega,
        show 2 * m + 5 - 2 = 2 * m + 3 from by omega, c3, a2]
      push_cast
      ring
    have a4 : T (2 * m + 5) 1 = ((m : ℤ) + 3) ^ 2 + 1 := by
      rw [T1_odd (2 * m + 5) (by omega) (by omega), show 2 * m + 5 - 1 = 2 * m + 4 from by omega,
        c4, a1]
      push_cast
      ring
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [show 2 * (m + 1) + 2 = 2 * m + 4 from by ring, a1]
      push_cast
      ring
    · rw [show 2 * (m + 1) + 2 = 2 * m + 4 from by ring, a2]
      push_cast
      ring
    · rw [show 2 * (m + 1) + 3 = 2 * m + 5 from by ring, a3]
      push_cast
      ring
    · rw [show 2 * (m + 1) + 3 = 2 * m + 5 from by ring, a4]
      push_cast
      ring

open OMA.S_oeis_a246695 in
lemma sum_pairs (N : ℕ) (hN : 2 ≤ N) (j : ℕ) :
    ∑ k ∈ Finset.range (2 * j), T N k = (j : ℤ) * (T N 0 + T N 1) + (j : ℤ) * ((j : ℤ) - 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 from by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, T_col N hN (2 * j), T_col N hN (2 * j + 1),
      show (2 * j) % 2 = 0 from by omega, show (2 * j) / 2 = j from by omega,
      show (2 * j + 1) % 2 = 1 from by omega, show (2 * j + 1) / 2 = j from by omega]
    push_cast
    ring

open OMA.S_oeis_a246695 in
lemma a_even (m : ℕ) : a (2 * m + 2) = (2 * (m : ℤ) + 3) * ((m : ℤ) ^ 2 + 3 * m + 3) := by
  unfold a
  have h := sum_pairs (2 * m + 2) (by omega) (m + 1)
  have c := T_col (2 * m + 2) (by omega) (2 * (m + 1))
  rw [show (2 * (m + 1)) % 2 = 0 from by omega, show (2 * (m + 1)) / 2 = m + 1 from by omega] at c
  obtain ⟨h1, h2, -, -⟩ := closed m
  rw [show 2 * m + 2 + 1 = 2 * (m + 1) + 1 from by ring, Finset.sum_range_succ, h, c, h1, h2]
  push_cast
  ring

open OMA.S_oeis_a246695 in
lemma a_odd (m : ℕ) : a (2 * m + 3) = ((m : ℤ) + 2) * (2 * (m : ℤ) ^ 2 + 8 * m + 9) := by
  unfold a
  have h := sum_pairs (2 * m + 3) (by omega) (m + 2)
  obtain ⟨-, -, h3, h4⟩ := closed m
  rw [show 2 * m + 3 + 1 = 2 * (m + 2) from by ring, h, h3, h4]
  push_cast
  ring

open OMA.S_oeis_a246695 in
lemma acl (n : ℕ) :
    8 * a n = ((n : ℤ) + 1) * ((-1) ^ n + 2 * (n : ℤ) ^ 2 + 4 * n + 7) := by
  rcases n with _ | _ | n
  · simp [a, T]
  · simp [a, T, Finset.sum_range_succ]
  · obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · rw [a_even, Even.neg_one_pow ⟨m + 1, by ring⟩]
      push_cast
      ring
    · rw [show 2 * m + 1 + 2 = 2 * m + 3 from by ring, a_odd, Odd.neg_one_pow ⟨m + 1, by ring⟩]
      push_cast
      ring

open OMA.S_oeis_a246695 in
lemma arec (j : ℕ) : a (j + 6) = 2 * a (j + 5) + a (j + 4) - 4 * a (j + 3) + a (j + 2)
    + 2 * a (j + 1) - a j := by
  have h0 := acl j
  have h1 := acl (j + 1)
  have h2 := acl (j + 2)
  have h3 := acl (j + 3)
  have h4 := acl (j + 4)
  have h5 := acl (j + 5)
  have h6 := acl (j + 6)
  simp only [pow_add] at h1 h2 h3 h4 h5 h6
  push_cast at h1 h2 h3 h4 h5 h6
  have key : 8 * a (j + 6) = 8 * (2 * a (j + 5) + a (j + 4) - 4 * a (j + 3) + a (j + 2)
      + 2 * a (j + 1) - a j) := by
    linear_combination h6 - 2 * h5 - h4 + 4 * h3 - h2 - 2 * h1 + h0
  linarith

open PowerSeries in
lemma coeff_term (f : ℕ → ℤ) (c : ℤ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A246695Aux

open OMA.S_oeis_a246695 A246695Aux PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a246695.main := by
  have v0 : a 0 = 1 := by have h := acl 0; norm_num at h; omega
  have v1 : a 1 = 3 := by have h := acl 1; norm_num at h; omega
  have v2 : a 2 = 9 := by have h := acl 2; norm_num at h; omega
  have v3 : a 3 = 18 := by have h := acl 3; norm_num at h; omega
  have v4 : a 4 = 35 := by have h := acl 4; norm_num at h; omega
  have v5 : a 5 = 57 := by have h := acl 5; norm_num at h; omega
  have v6 : a 6 = 91 := by have h := acl 6; norm_num at h; omega
  refine ⟨⟨v0, v1, v2, v3, v4, v5, v6, ?_⟩, ?_, acl⟩
  · intro n hn
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 6 := ⟨n - 6, by omega⟩
    rw [show j + 6 - 1 = j + 5 from by omega, show j + 6 - 2 = j + 4 from by omega,
      show j + 6 - 3 = j + 3 from by omega, show j + 6 - 4 = j + 2 from by omega,
      show j + 6 - 5 = j + 1 from by omega, show j + 6 - 6 = j from by omega]
    exact arec j
  · have hD : ((X - 1) ^ 4 * (X + 1) ^ 2 : PowerSeries ℤ) =
        C (1 : ℤ) * X ^ 0 + C (-2 : ℤ) * X ^ 1 + C (-1 : ℤ) * X ^ 2 + C (4 : ℤ) * X ^ 3 +
        C (-1 : ℤ) * X ^ 4 + C (-2 : ℤ) * X ^ 5 + C (1 : ℤ) * X ^ 6 := by
      simp only [map_one, map_ofNat, map_neg]
      ring
    have hN : (1 + X + 2 * X ^ 2 + X ^ 3 + X ^ 4 : PowerSeries ℤ) =
        C (1 : ℤ) * X ^ 0 + C (1 : ℤ) * X ^ 1 + C (2 : ℤ) * X ^ 2 + C (1 : ℤ) * X ^ 3 +
        C (1 : ℤ) * X ^ 4 := by
      simp only [map_one, map_ofNat]
      ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases Nat.lt_or_ge n 6 with hs | hs
    · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
      rw [if_pos (show 0 ≤ m + 6 by omega), if_pos (show 1 ≤ m + 6 by omega),
        if_pos (show 2 ≤ m + 6 by omega), if_pos (show 3 ≤ m + 6 by omega),
        if_pos (show 4 ≤ m + 6 by omega), if_pos (show 5 ≤ m + 6 by omega),
        if_pos (show 6 ≤ m + 6 by omega),
        if_neg (show ¬ (m + 6 = 0) by omega), if_neg (show ¬ (m + 6 = 1) by omega),
        if_neg (show ¬ (m + 6 = 2) by omega), if_neg (show ¬ (m + 6 = 3) by omega),
        if_neg (show ¬ (m + 6 = 4) by omega)]
      rw [show m + 6 - 1 = m + 5 from by omega, show m + 6 - 2 = m + 4 from by omega,
        show m + 6 - 3 = m + 3 from by omega, show m + 6 - 4 = m + 2 from by omega,
        show m + 6 - 5 = m + 1 from by omega, show m + 6 - 6 = m from by omega,
        show m + 6 - 0 = m + 6 from by omega]
      have hrec := arec m
      linarith
