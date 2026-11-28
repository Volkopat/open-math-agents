import OMAStatements.S_oeis_a127628
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Proof sketch: the summand is 5^k times the ballot number B(n,k) = C(2n,n+k) − C(2n,n+k+1),
-- which vanishes for k > n. Pascal's rule applied twice gives
-- B(n+1,k+1) = B(n,k+2) + 2·B(n,k+1) + B(n,k) and B(n+1,0) = B(n,0) + B(n,1), so the sums satisfy
-- 5·a(n+1) = 36·a(n) − 6·B(n,0). Since B(n,0) is the Catalan number, (n+2)·B(n+1,0) =
-- 2(2n+1)·B(n,0), and eliminating B(n,0) from two consecutive instances gives the recurrence.

namespace OMAProofA127628

def B (n k : ℕ) : ℚ := ((2 * n).choose (n + k) : ℚ) - ((2 * n).choose (n + k + 1) : ℚ)

def S (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), B n k * 5 ^ k

theorem term_eq (n k : ℕ) (hk : k ≤ n) :
    ((Nat.choose (2 * n) (n - k) : ℚ) * (2 * k + 1) * 5 ^ k) / ((n : ℚ) + k + 1)
      = B n k * 5 ^ k := by
  have hs : (2 * n).choose (n - k) = (2 * n).choose (n + k) :=
    Nat.choose_symm_of_eq_add (by omega)
  have h := Nat.choose_succ_right_eq (2 * n) (n + k)
  have h' : 2 * n - (n + k) = n - k := by omega
  rw [h'] at h
  have hq : ((2 * n).choose (n + k + 1) : ℚ) * ((n : ℚ) + k + 1)
      = ((2 * n).choose (n + k) : ℚ) * ((n : ℚ) - k) := by
    have := congrArg (Nat.cast : ℕ → ℚ) h
    push_cast [Nat.cast_sub hk] at this
    linarith
  have hpos : ((n : ℚ) + k + 1) ≠ 0 := by positivity
  unfold B
  rw [hs, div_eq_iff hpos]
  linear_combination (5 : ℚ) ^ k * hq

theorem B_zero (n k : ℕ) (hk : n < k) : B n k = 0 := by
  unfold B
  rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]
  simp

theorem a_eq (n : ℕ) : OMA.S_oeis_a127628.a n = S n := by
  unfold OMA.S_oeis_a127628.a S
  apply Finset.sum_congr rfl
  intro k hk
  exact term_eq n k (by have := Finset.mem_range.mp hk; omega)

theorem pas (N j : ℕ) :
    ((N + 2).choose (j + 2) : ℚ) = N.choose (j + 2) + 2 * N.choose (j + 1) + N.choose j := by
  have e1 : (N + 2).choose (j + 2) = (N + 1).choose (j + 1) + (N + 1).choose (j + 2) :=
    Nat.choose_succ_succ' (N + 1) (j + 1)
  have e2 : (N + 1).choose (j + 1) = N.choose j + N.choose (j + 1) := Nat.choose_succ_succ' N j
  have e3 : (N + 1).choose (j + 2) = N.choose (j + 1) + N.choose (j + 2) :=
    Nat.choose_succ_succ' N (j + 1)
  rw [e1, e2, e3]
  push_cast
  ring

theorem B_step (n k : ℕ) : B (n + 1) (k + 1) = B n (k + 2) + 2 * B n (k + 1) + B n k := by
  have h1 := pas (2 * n) (n + k)
  have h2 := pas (2 * n) (n + k + 1)
  unfold B
  ring_nf at h1 h2 ⊢
  linarith

theorem B0 (n : ℕ) : B (n + 1) 0 = B n 0 + B n 1 := by
  have h2 := pas (2 * n) n
  have e1 : (2 * n + 2).choose (n + 1) = (2 * n + 1).choose n + (2 * n + 1).choose (n + 1) :=
    Nat.choose_succ_succ' (2 * n + 1) n
  have e2 : (2 * n + 1).choose n = (2 * n + 1).choose (n + 1) :=
    Nat.choose_symm_of_eq_add (by omega)
  have e3 : (2 * n + 1).choose (n + 1) = (2 * n).choose n + (2 * n).choose (n + 1) :=
    Nat.choose_succ_succ' (2 * n) n
  have h1 : ((2 * n + 2).choose (n + 1) : ℚ)
      = 2 * (((2 * n).choose n : ℚ) + ((2 * n).choose (n + 1) : ℚ)) := by
    rw [e1, e2, e3]
    push_cast
    ring
  unfold B
  ring_nf at h1 h2 ⊢
  linarith

theorem step (n : ℕ) : 5 * S (n + 1) = 36 * S n - 6 * B n 0 := by
  have z1 : B n (n + 1) = 0 := B_zero n (n + 1) (by omega)
  have z2 : B n (n + 2) = 0 := B_zero n (n + 2) (by omega)
  have hA : ∑ k ∈ Finset.range (n + 2), B n k * (5 : ℚ) ^ k
      = ∑ k ∈ Finset.range (n + 1), B n (k + 1) * (5 : ℚ) ^ (k + 1) + B n 0 * (5 : ℚ) ^ 0 :=
    Finset.sum_range_succ' _ _
  have hB : ∑ k ∈ Finset.range (n + 2), B n k * (5 : ℚ) ^ k
      = ∑ k ∈ Finset.range (n + 1), B n k * (5 : ℚ) ^ k + B n (n + 1) * (5 : ℚ) ^ (n + 1) :=
    Finset.sum_range_succ _ _
  have hC : ∑ k ∈ Finset.range (n + 3), B n k * (5 : ℚ) ^ k
      = ∑ k ∈ Finset.range (n + 2), B n (k + 1) * (5 : ℚ) ^ (k + 1) + B n 0 * (5 : ℚ) ^ 0 :=
    Finset.sum_range_succ' _ _
  have hD : ∑ k ∈ Finset.range (n + 2), B n (k + 1) * (5 : ℚ) ^ (k + 1)
      = ∑ k ∈ Finset.range (n + 1), B n (k + 2) * (5 : ℚ) ^ (k + 2) + B n 1 * (5 : ℚ) ^ 1 :=
    Finset.sum_range_succ' _ _
  have hE : ∑ k ∈ Finset.range (n + 3), B n k * (5 : ℚ) ^ k
      = ∑ k ∈ Finset.range (n + 2), B n k * (5 : ℚ) ^ k + B n (n + 2) * (5 : ℚ) ^ (n + 2) :=
    Finset.sum_range_succ _ _
  have hS : ∑ k ∈ Finset.range (n + 2), B (n + 1) k * (5 : ℚ) ^ k
      = ∑ k ∈ Finset.range (n + 1), B (n + 1) (k + 1) * (5 : ℚ) ^ (k + 1)
        + B (n + 1) 0 * (5 : ℚ) ^ 0 :=
    Finset.sum_range_succ' _ _
  have hT : ∑ k ∈ Finset.range (n + 1), B (n + 1) (k + 1) * (5 : ℚ) ^ (k + 1)
      = (1 / 5) * ∑ k ∈ Finset.range (n + 1), B n (k + 2) * (5 : ℚ) ^ (k + 2)
        + 2 * ∑ k ∈ Finset.range (n + 1), B n (k + 1) * (5 : ℚ) ^ (k + 1)
        + 5 * ∑ k ∈ Finset.range (n + 1), B n k * (5 : ℚ) ^ k := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [B_step]
    ring
  have hZ := B0 n
  rw [z1] at hB
  rw [z2] at hE
  simp only [pow_zero, pow_one, mul_one, zero_mul, add_zero] at hA hB hC hD hE hS
  have key : 5 * ∑ k ∈ Finset.range (n + 2), B (n + 1) k * (5 : ℚ) ^ k
      = 36 * ∑ k ∈ Finset.range (n + 1), B n k * (5 : ℚ) ^ k - 6 * B n 0 := by
    linarith
  exact key

theorem D_eq (n : ℕ) : B n 0 * ((n : ℚ) + 1) = ((2 * n).choose n : ℚ) := by
  have h := Nat.choose_succ_right_eq (2 * n) n
  have h' : 2 * n - n = n := by omega
  rw [h'] at h
  have hq : ((2 * n).choose (n + 1) : ℚ) * ((n : ℚ) + 1) = ((2 * n).choose n : ℚ) * n := by
    exact_mod_cast h
  unfold B
  simp only [add_zero]
  linear_combination (-1 : ℚ) * hq

theorem D_rec (n : ℕ) : ((n : ℚ) + 2) * B (n + 1) 0 = 2 * (2 * (n : ℚ) + 1) * B n 0 := by
  have d0 := D_eq n
  have d1 := D_eq (n + 1)
  have cb := Nat.succ_mul_centralBinom_succ n
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at cb
  have cq : ((n : ℚ) + 1) * ((2 * (n + 1)).choose (n + 1) : ℚ)
      = 2 * (2 * (n : ℚ) + 1) * ((2 * n).choose n : ℚ) := by
    exact_mod_cast cb
  push_cast at d1
  have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
  apply mul_left_cancel₀ hn
  linear_combination ((n : ℚ) + 1) * d1 + cq - 2 * (2 * (n : ℚ) + 1) * d0

end OMAProofA127628

open OMAProofA127628 in
theorem OMA.solution : type_of% @OMA.S_oeis_a127628.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h1 : m + 2 - 1 = m + 1 := by omega
  have h2 : m + 2 - 2 = m := by omega
  rw [h1, h2, a_eq, a_eq, a_eq]
  have E1 : 5 * S (m + 2) = 36 * S (m + 1) - 6 * B (m + 1) 0 := step (m + 1)
  have E0 : 5 * S (m + 1) = 36 * S m - 6 * B m 0 := step m
  have ED : ((m : ℚ) + 2) * B (m + 1) 0 = 2 * (2 * (m : ℚ) + 1) * B m 0 := D_rec m
  push_cast
  linear_combination ((m : ℚ) + 2) * E1 - 6 * ED - 2 * (2 * (m : ℚ) + 1) * E0
