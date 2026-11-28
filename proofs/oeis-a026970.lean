import OMAStatements.S_oeis_a026970
import Mathlib

-- Proof of Colin Barker's conjectures in OEIS A026970 (statement by @ivillar).
-- Idea: the triangle is symmetric, so Sum k*T(n,k) = (n/2)*S(n) with S(n) the row sum, and
-- a(n) = (n+2)*S(n)/2; the row sums satisfy S(n) = 2S(n-1) + 2(f(n) - f(n-1)) - 2 with
-- f(n) = floor((3n-1)/2), giving 3*S(n) = 2^(n+2) - 3 - (-1)^n; the recurrence and the g.f.
-- follow from the closed form.

namespace OMAA026970Helpers

open OMA.S_oeis_a026970

theorem T_zero (n : ℕ) : T n 0 = 1 := by cases n <;> simp [T]

theorem T_self (n : ℕ) : T n n = 1 := by cases n <;> simp [T]

theorem T_one (n : ℕ) (h : 2 ≤ n) : T n 1 = (3 * n - 1) / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [T, if_neg (by omega), if_neg (by omega), if_pos (by omega)]

theorem T_pred (n : ℕ) (h : 2 ≤ n) : T n (n - 1) = (3 * n - 1) / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [T, if_neg (by omega), if_neg (by omega), if_pos (by omega)]

theorem T_mid (n k : ℕ) (h1 : 2 ≤ k) (h2 : k + 2 ≤ n) : T n k = T (n - 1) (k - 1) + T (n - 1) k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [T, if_neg (by omega), if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel]

theorem T_gt : ∀ n k : ℕ, n < k → T n k = 0
  | 0, k, h => by simp [T]; omega
  | n + 1, k, h => by rw [T, if_neg (by omega), if_pos h]

theorem T_sym : ∀ n k : ℕ, k ≤ n → T n (n - k) = T n k
  | 0, k, h => by simp at h; subst h; rfl
  | n + 1, k, h => by
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k
      · simp [T_zero, T_self]
      · rcases Nat.lt_or_ge n 1 with hn | hn
        · interval_cases n; rfl
        · rw [T_one (n + 1) (by omega), show n + 1 - 1 = n by omega]
          have := T_pred (n + 1) (by omega)
          rw [show n + 1 - 1 = n by omega] at this
          exact this
    · rcases Nat.lt_or_ge (n + 1) (k + 2) with hk2 | hk2
      · -- k = n or k = n + 1
        rcases Nat.eq_or_lt_of_le h with h' | h'
        · rw [h', Nat.sub_self, T_zero, T_self]
        · have hkn : k = n := by omega
          subst hkn
          rw [show k + 1 - k = 1 by omega, T_one (k + 1) (by omega)]
          have := T_pred (k + 1) (by omega)
          rw [show k + 1 - 1 = k by omega] at this
          exact this.symm
      · rw [T_mid (n + 1) k hk hk2, T_mid (n + 1) (n + 1 - k) (by omega) (by omega)]
        simp only [Nat.add_sub_cancel]
        have e1 := T_sym n (k - 1) (by omega)
        have e2 := T_sym n k (by omega)
        rw [show n + 1 - k - 1 = n - k by omega, show n + 1 - k = n - (k - 1) by omega, e1, e2]
        ring

def S (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), T n k

theorem S_rec (m : ℕ) : S (m + 4) + 2 + 2 * ((3 * (m + 3) - 1) / 2) =
    2 * ((3 * (m + 4) - 1) / 2) + 2 * S (m + 3) := by
  have hmid : ∀ j ∈ Finset.range (m + 1), T (m + 4) (j + 2) = T (m + 3) (j + 1) + T (m + 3) (j + 2) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [T_mid (m + 4) (j + 2) (by omega) (by omega)]
    rfl
  have h4 : S (m + 4) = T (m + 4) 0 + T (m + 4) 1 + ∑ j ∈ Finset.range (m + 1), T (m + 4) (j + 2) +
      T (m + 4) (m + 3) + T (m + 4) (m + 4) := by
    unfold S
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ', Finset.sum_range_succ']
    ring
  have h3a : S (m + 3) = T (m + 3) 0 + ∑ j ∈ Finset.range (m + 1), T (m + 3) (j + 1) +
      T (m + 3) (m + 2) + T (m + 3) (m + 3) := by
    unfold S
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ']
    ring
  have h3b : S (m + 3) = T (m + 3) 0 + T (m + 3) 1 + ∑ j ∈ Finset.range (m + 1), T (m + 3) (j + 2) +
      T (m + 3) (m + 3) := by
    unfold S
    rw [Finset.sum_range_succ, Finset.sum_range_succ', Finset.sum_range_succ']
    ring
  rw [Finset.sum_congr rfl hmid, Finset.sum_add_distrib] at h4
  have t1 := T_one (m + 4) (by omega)
  have t2 := T_pred (m + 4) (by omega)
  have t3 := T_one (m + 3) (by omega)
  have t4 := T_pred (m + 3) (by omega)
  simp only [show m + 4 - 1 = m + 3 by omega, show m + 3 - 1 = m + 2 by omega] at t2 t4
  rw [T_zero, T_self] at h4 h3a h3b
  omega

theorem S_closed : ∀ n : ℕ, 1 ≤ n → 3 * (S n : ℤ) = 2 ^ (n + 2) - 3 - (-1) ^ n
  | 0, h => by omega
  | 1, _ => by decide
  | 2, _ => by decide
  | 3, _ => by decide
  | m + 4, _ => by
    have ih := S_closed (m + 3) (by omega)
    have hr := S_rec m
    have hf : (3 * (m + 4) - 1) / 2 = (3 * (m + 3) - 1) / 2 + (if m % 2 = 0 then 1 else 2) := by
      split_ifs with h <;> omega
    rw [hf] at hr
    have hr' : (S (m + 4) : ℤ) = 2 * S (m + 3) + 2 * (if m % 2 = 0 then 1 else 2) - 2 := by
      have := congrArg (fun x : ℕ => (x : ℤ)) hr
      push_cast at this
      split_ifs at this ⊢ <;> linarith
    rw [hr']
    rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
    · subst hj
      rw [if_pos (by omega)]
      have : ((-1 : ℤ) ^ (j + j + 4)) = 1 := by rw [show j + j + 4 = 2 * (j + 2) by ring, pow_mul]; norm_num
      have h2 : ((-1 : ℤ) ^ (j + j + 3)) = -1 := by
        rw [show j + j + 3 = 2 * (j + 1) + 1 by ring, pow_succ, pow_mul]; norm_num
      rw [this]; rw [h2] at ih
      rw [show j + j + 4 + 2 = (j + j + 3 + 2) + 1 by ring, pow_succ]
      linarith
    · subst hj
      rw [if_neg (by omega)]
      have : ((-1 : ℤ) ^ (2 * j + 1 + 4)) = -1 := by
        rw [show 2 * j + 1 + 4 = 2 * (j + 2) + 1 by ring, pow_succ, pow_mul]; norm_num
      have h2 : ((-1 : ℤ) ^ (2 * j + 1 + 3)) = 1 := by
        rw [show 2 * j + 1 + 3 = 2 * (j + 2) by ring, pow_mul]; norm_num
      rw [this]; rw [h2] at ih
      rw [show 2 * j + 1 + 4 + 2 = (2 * j + 1 + 3 + 2) + 1 by ring, pow_succ]
      linarith

theorem two_a (n : ℕ) : 2 * a n = (n + 2) * S n := by
  have hW : 2 * ∑ k ∈ Finset.range (n + 1), k * T n k = n * S n := by
    have hr := Finset.sum_range_reflect (fun k => k * T n k) (n + 1)
    simp only [Nat.add_sub_cancel] at hr
    have hr2 : ∑ j ∈ Finset.range (n + 1), (n - j) * T n (n - j) =
        ∑ j ∈ Finset.range (n + 1), (n - j) * T n j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_range] at hj
      rw [T_sym n j (by omega)]
    rw [hr2] at hr
    unfold S
    rw [two_mul]
    nth_rewrite 2 [← hr]
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [← add_mul, show j + (n - j) = n by omega]
  unfold a
  have : ∑ k ∈ Finset.range (n + 1), (k + 1) * T n k =
      ∑ k ∈ Finset.range (n + 1), k * T n k + S n := by
    unfold S
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [this]
  linarith

theorem a_closed (n : ℕ) (hn : 0 < n) :
    (a n : ℚ) = -((-1) ^ n - 2 ^ (n + 2) + 3) * (n + 2) / 6 := by
  have h2 := two_a n
  have h3 := S_closed n hn
  have h2' : ((2 * a n : ℕ) : ℚ) = (((n + 2) * S n : ℕ) : ℚ) := by rw [h2]
  have h3' : ((3 * (S n : ℤ) : ℤ) : ℚ) = ((2 ^ (n + 2) - 3 - (-1) ^ n : ℤ) : ℚ) := by rw [h3]
  push_cast at h2' h3'
  linear_combination (1 / 2 : ℚ) * h2' + (((n : ℚ) + 2) / 6) * h3'

theorem a_rec (j : ℕ) : (a (j + 7) : ℚ) = 4 * a (j + 6) - 2 * a (j + 5) - 8 * a (j + 4) +
    7 * a (j + 3) + 4 * a (j + 2) - 4 * a (j + 1) := by
  rw [a_closed (j + 7) (by omega), a_closed (j + 6) (by omega), a_closed (j + 5) (by omega),
    a_closed (j + 4) (by omega), a_closed (j + 3) (by omega), a_closed (j + 2) (by omega),
    a_closed (j + 1) (by omega)]
  push_cast
  ring

theorem a0 : (a 0 : ℚ) = 1 := by simp [a, T]

theorem key : PowerSeries.mk (fun n => (a n : ℚ)) *
    ((1 - PowerSeries.X) ^ 2 * (1 + PowerSeries.X) ^ 2 * (1 - 2 * PowerSeries.X) ^ 2) =
    1 - PowerSeries.X - 2 * PowerSeries.X ^ 2 + 7 * PowerSeries.X ^ 3 - 7 * PowerSeries.X ^ 4 -
      4 * PowerSeries.X ^ 5 + 4 * PowerSeries.X ^ 6 := by
  set F := PowerSeries.mk (fun n => (a n : ℚ))
  have e1 : F * ((1 - PowerSeries.X) ^ 2 * (1 + PowerSeries.X) ^ 2 * (1 - 2 * PowerSeries.X) ^ 2) =
      F - PowerSeries.C (4 : ℚ) * (PowerSeries.X ^ 1 * F) + PowerSeries.C (2 : ℚ) * (PowerSeries.X ^ 2 * F) +
        PowerSeries.C (8 : ℚ) * (PowerSeries.X ^ 3 * F) - PowerSeries.C (7 : ℚ) * (PowerSeries.X ^ 4 * F) -
        PowerSeries.C (4 : ℚ) * (PowerSeries.X ^ 5 * F) + PowerSeries.C (4 : ℚ) * (PowerSeries.X ^ 6 * F) := by
    simp only [map_ofNat]
    ring
  have e2 : (1 - PowerSeries.X - 2 * PowerSeries.X ^ 2 + 7 * PowerSeries.X ^ 3 - 7 * PowerSeries.X ^ 4 -
      4 * PowerSeries.X ^ 5 + 4 * PowerSeries.X ^ 6 : PowerSeries ℚ) =
      PowerSeries.X ^ 0 - PowerSeries.X ^ 1 - PowerSeries.C (2 : ℚ) * PowerSeries.X ^ 2 +
        PowerSeries.C (7 : ℚ) * PowerSeries.X ^ 3 - PowerSeries.C (7 : ℚ) * PowerSeries.X ^ 4 -
        PowerSeries.C (4 : ℚ) * PowerSeries.X ^ 5 + PowerSeries.C (4 : ℚ) * PowerSeries.X ^ 6 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  have v1 : (a 1 : ℚ) = 3 := by rw [a_closed 1 (by norm_num)]; norm_num
  have v2 : (a 2 : ℚ) = 8 := by rw [a_closed 2 (by norm_num)]; norm_num
  have v3 : (a 3 : ℚ) = 25 := by rw [a_closed 3 (by norm_num)]; norm_num
  have v4 : (a 4 : ℚ) = 60 := by rw [a_closed 4 (by norm_num)]; norm_num
  have v5 : (a 5 : ℚ) = 147 := by rw [a_closed 5 (by norm_num)]; norm_num
  have v6 : (a 6 : ℚ) = 336 := by rw [a_closed 6 (by norm_num)]; norm_num
  ext n
  simp only [F, map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
  by_cases hn : n ≤ 6
  · interval_cases n <;> simp [a0, v1, v2, v3, v4, v5, v6] <;> norm_num
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 7 := ⟨n - 7, by omega⟩
    have h := a_rec j
    simp
    linear_combination h

end OMAA026970Helpers

open OMA.S_oeis_a026970 OMAA026970Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a026970.main := by
  refine ⟨a_closed, fun n hn => ?_, ?_⟩
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 7 := ⟨n - 7, by omega⟩
    rw [show j + 7 - 1 = j + 6 by omega, show j + 7 - 2 = j + 5 by omega, show j + 7 - 3 = j + 4 by omega,
      show j + 7 - 4 = j + 3 by omega, show j + 7 - 5 = j + 2 by omega, show j + 7 - 6 = j + 1 by omega]
    exact_mod_cast a_rec j
  · rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp), key]
