import OMAStatements.S_oeis_a159856
import Mathlib

-- Proof of R. J. Mathar's conjecture in OEIS A159856 (statement by @ivillar).
-- Idea: (-1)^k*T(n,k) ≥ 0 by induction, so the sum of |T(n,k)| is S(n) = Σ (-1)^k T(n,k);
-- the recurrence gives S(n+1) = 3*S(n) - n, whence 4*S(n) = 3^(n+1) + 2n + 1.

namespace OMAA159856Helpers

open OMA.S_oeis_a159856

theorem T_zero_of_lt : ∀ n k : ℕ, n < k → T n k = 0
  | 0, k + 1, _ => by simp [T]
  | n + 1, k + 1, h => by
    rw [T, T_zero_of_lt n (k + 1) (by omega), T_zero_of_lt n k (by omega)]
    ring

theorem sign : ∀ n k : ℕ, 0 ≤ (-1 : ℤ) ^ k * T n k
  | n, 0 => by simp [T]; omega
  | 0, k + 1 => by simp [T]
  | n + 1, k + 1 => by
    have h1 := sign n (k + 1)
    have h2 := sign n k
    rw [T]
    have e : (-1 : ℤ) ^ (k + 1) * (2 * T n (k + 1) - T n k) =
        2 * ((-1 : ℤ) ^ (k + 1) * T n (k + 1)) + (-1) ^ k * T n k := by ring
    rw [e]
    positivity

theorem abs_T (n k : ℕ) : |T n k| = (-1 : ℤ) ^ k * T n k := by
  have h := sign n k
  rcases neg_one_pow_eq_or ℤ k with hk | hk
  · rw [hk, one_mul] at h ⊢; exact abs_of_nonneg h
  · rw [hk, neg_one_mul] at h ⊢; exact abs_of_nonpos (by linarith)

def S (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * T n k

theorem S_succ (n : ℕ) : S (n + 1) = 3 * S n - n := by
  unfold S
  rw [Finset.sum_range_succ']
  have h1 : ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (k + 1) * T (n + 1) (k + 1) =
      -2 * ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * T n (k + 1) +
        ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * T n k := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [T]
    ring
  have h2 : ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * T n (k + 1) =
      -(∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * T n k - T n 0) := by
    have := Finset.sum_range_succ' (fun j => (-1 : ℤ) ^ j * T n j) (n + 1)
    rw [Finset.sum_range_succ, T_zero_of_lt n (n + 1) (by omega), mul_zero, add_zero] at this
    rw [this]
    simp only [pow_zero, one_mul, add_sub_cancel_right]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [h1, h2]
  simp only [T, pow_zero, one_mul]
  push_cast
  ring

theorem S_closed (n : ℕ) : 4 * S n = 3 ^ (n + 1) + 2 * n + 1 := by
  induction n with
  | zero => simp [S, T]
  | succ n ih =>
    rw [S_succ]
    push_cast
    linear_combination 3 * ih

end OMAA159856Helpers

open OMA.S_oeis_a159856 OMAA159856Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a159856.main := by
  intro n
  have h : (∑ k ∈ Finset.range (n + 1), |T n k| : ℤ) = S n := by
    unfold S
    exact Finset.sum_congr rfl (fun k _ => abs_T n k)
  rw [h]
  have := S_closed n
  rw [eq_div_iff (by norm_num)]
  have h' : ((4 * S n : ℤ) : ℚ) = ((3 ^ (n + 1) + 2 * n + 1 : ℤ) : ℚ) := by rw [this]
  push_cast at h'
  linarith

