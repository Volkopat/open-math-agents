import OMAStatements.S_oeis_a105752
import Mathlib

/-! A105752. `∑ₖ c(n,k) xᵏ = x (x+1) ⋯ (x+n-1)` for the unsigned Stirling numbers `c`; evaluate
at `x = 1` and `x = -1` and keep the even part. -/

open Finset Nat

def OMA.c (n k : ℕ) : ℤ := stirlingFirst n k

open OMA in
theorem OMA.p (n : ℕ) (x : ℤ) :
    ∑ k ∈ range (n + 1), c n k * x ^ k = ∏ i ∈ range n, (x + i) := by
  induction n with
  | zero => simp [c]
  | succ n ih =>
    have h1 : ∑ k ∈ range (n + 1), c n (k + 1) * x ^ (k + 1)
        = ∑ k ∈ range (n + 1), c n k * x ^ k - c n 0 := by
      rw [sum_range_succ (fun k => c n (k + 1) * x ^ (k + 1)),
        sum_range_succ' (fun k => c n k * x ^ k)]
      simp [c, stirlingFirst_eq_zero_of_lt]
    have h0 : n * c n 0 = 0 := by cases n <;> simp [c]
    calc _ = ∑ k ∈ range (n + 1), c (n + 1) (k + 1) * x ^ (k + 1) := by
          rw [sum_range_succ' _ (n + 1)]
          simp [c]
      _ = n * ∑ k ∈ range (n + 1), c n (k + 1) * x ^ (k + 1)
          + x * ∑ k ∈ range (n + 1), c n k * x ^ k := by
          rw [mul_sum, mul_sum, ← sum_add_distrib]
          exact sum_congr rfl fun k _ => by push_cast [c, stirlingFirst_succ_succ]; ring
      _ = _ := by
          rw [h1, prod_range_succ, ← ih]
          linear_combination -h0

theorem OMA.e (f : ℕ → ℤ) (m : ℕ) :
    ∑ j ∈ range (2 * m), f j * (1 + (-1) ^ j) = 2 * ∑ k ∈ range m, f (2 * k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e1 : (-1 : ℤ) ^ (2 * m) = 1 := by simp [pow_mul]
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_range_succ _ (2 * m + 1),
      sum_range_succ _ (2 * m), ih, sum_range_succ _ m, pow_succ, e1]
    ring

open OMA.S_oeis_a105752 OMA in
theorem OMA.solution : type_of% @OMA.S_oeis_a105752.main := by
  intro n
  have ht : ∑ k ∈ range (n + 1), stirling1 n (2 * k)
      = (-1) ^ n * ∑ k ∈ range (n + 1), c n (2 * k) := by
    rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rcases le_or_gt (2 * k) n with h | h
    · have : (-1 : ℤ) ^ n = (-1) ^ (n - 2 * k) := by
        conv_lhs => rw [← Nat.sub_add_cancel h]
        simp [pow_add, pow_mul]
      simp only [stirling1, c, this]
    · simp [stirling1, c, stirlingFirst_eq_zero_of_lt h]
  have hv : ∑ j ∈ range (2 * (n + 1)), c n j * (1 + (-1) ^ j)
      = ∑ j ∈ range (n + 1), c n j * (1 + (-1) ^ j) := by
    refine (sum_subset (range_mono (by omega)) fun j _ h => ?_).symm
    simp only [mem_range, not_lt] at h
    rw [c, stirlingFirst_eq_zero_of_lt (by omega)]
    simp
  have hf : (n.factorial : ℤ) = ∑ k ∈ range (n + 1), c n k * 1 ^ k := by
    rw [p, ← prod_range_add_one_eq_factorial]
    push_cast
    exact prod_congr rfl fun i _ => add_comm _ _
  have key : 2 * ∑ k ∈ range (n + 1), stirling1 n (2 * k)
      = (-1) ^ n * (n.factorial + ∏ i ∈ range n, ((-1 : ℤ) + i)) := by
    rw [ht, mul_left_comm, ← e (c n), hv, hf, ← p n (-1), ← sum_add_distrib]
    congr 1
    exact sum_congr rfl fun j _ => by ring
  have hm : (n.factorial : ℤ) * ((if n ≤ 1 then 1 else 0) + (-1) ^ n)
      = 2 * ∑ k ∈ range (n + 1), stirling1 n (2 * k) := by
    rw [key]
    rcases n with _ | _ | n
    · simp
    · simp
    · rw [prod_eq_zero (i := 1) (mem_range.mpr (by omega)) (by norm_num)]
      split_ifs <;> first | omega | ring
  simp only [a]
  rw [hm]
  omega
