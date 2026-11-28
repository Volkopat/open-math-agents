import OMAStatements.S_oeis_a001792
import Mathlib

-- Problem: A001792, preceding(n) + A098156(n+1) = 2 a(n), where a(n) = (n+2) 2^(n-1) for n >= 1.
-- Upstream: formal-conjectures statements/oeis-a001792.lean (declaration OMA.S_oeis_a001792.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the stated identity holds).
-- Proof: 4 interleaved(k) = 3k + 2 + (-1)^k (2 - k), so 4 A098156(N) is a combination of the sums
-- of C(N,k), k C(N,k), (-1)^k C(N,k) and k (-1)^k C(N,k), which are 2^N, N 2^(N-1), 0 and
-- -N [N = 1] for N >= 1. This gives A098156(n+1) in closed form, and the identity follows.

namespace OMA.P_oeis_a001792

open OMA.S_oeis_a001792

theorem w4 (k : ℕ) : 4 * (interleaved k : ℤ) = 3 * k + 2 + (-1) ^ k * (2 - k) := by
  unfold interleaved
  rcases Nat.even_or_odd' k with ⟨s, rfl | rfl⟩
  · rw [if_pos (by omega), show 2 * s / 2 = s by omega]
    have h : ((-1 : ℤ)) ^ (2 * s) = 1 := by rw [pow_mul]; norm_num
    rw [h]
    push_cast
    ring
  · rw [if_neg (by omega)]
    have h : ((-1 : ℤ)) ^ (2 * s + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    rw [h]
    push_cast
    ring

theorem S4 (M : ℕ) : ∑ k ∈ Finset.range (M + 1 + 1), (k : ℤ) * (-1) ^ k * ((M + 1).choose k : ℤ)
    = -((M : ℤ) + 1) * (if M = 0 then 1 else 0) := by
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero]
  have h : ∀ j ∈ Finset.range (M + 1), ((j + 1 : ℕ) : ℤ) * (-1) ^ (j + 1) * ((M + 1).choose (j + 1) : ℤ)
      = -((M : ℤ) + 1) * ((-1) ^ j * (M.choose j : ℤ)) := by
    intro j _
    have e' : ((M : ℤ) + 1) * (M.choose j : ℤ) = ((M + 1).choose (j + 1) : ℤ) * ((j : ℤ) + 1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq M j
    push_cast
    rw [pow_succ]
    linear_combination ((-1 : ℤ) ^ j) * e'
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, Int.alternating_sum_range_choose]

theorem b4 (M : ℕ) : 4 * (a098156 (M + 1) : ℤ) = 3 * ((M : ℤ) + 1) * 2 ^ M + 2 * 2 ^ (M + 1)
    + ((M : ℤ) + 1) * (if M = 0 then 1 else 0) := by
  unfold a098156
  push_cast
  rw [Finset.mul_sum]
  have h : ∀ k ∈ Finset.range (M + 1 + 1), 4 * (((M + 1).choose k : ℤ) * (interleaved k : ℤ))
      = 3 * ((k : ℤ) * ((M + 1).choose k : ℤ)) + 2 * ((M + 1).choose k : ℤ)
        + 2 * ((-1) ^ k * ((M + 1).choose k : ℤ)) - (k : ℤ) * (-1) ^ k * ((M + 1).choose k : ℤ) := by
    intro k _
    linear_combination ((M + 1).choose k : ℤ) * w4 k
  rw [Finset.sum_congr rfl h]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum]
  have s1 : ∑ k ∈ Finset.range (M + 1 + 1), ((M + 1).choose k : ℤ) = 2 ^ (M + 1) := by
    exact_mod_cast Nat.sum_range_choose (M + 1)
  have s2 : ∑ k ∈ Finset.range (M + 1 + 1), (k : ℤ) * ((M + 1).choose k : ℤ) = ((M : ℤ) + 1) * 2 ^ M := by
    have := Nat.sum_range_mul_choose (M + 1)
    rw [Nat.add_sub_cancel] at this
    exact_mod_cast this
  have s3 : ∑ k ∈ Finset.range (M + 1 + 1), ((-1) ^ k * ((M + 1).choose k : ℤ)) = 0 :=
    Int.alternating_sum_range_choose_of_ne (by omega)
  rw [s1, s2, s3, S4 M]
  ring

theorem main' : ∀ n : ℕ, preceding n + a098156 (n + 1) = 2 * a n := by
  intro n
  have hb := b4 n
  suffices h : (preceding n : ℤ) + (a098156 (n + 1) : ℤ) = 2 * (a n : ℤ) by exact_mod_cast h
  rcases n with _ | _ | k
  · simp [preceding, a] at hb ⊢
    linarith
  · simp [preceding, a] at hb ⊢
    linarith
  · have e : (if k + 1 + 1 = 0 then (1 : ℤ) else 0) = 0 := if_neg (by omega)
    rw [e] at hb
    simp only [preceding, a]
    push_cast at hb ⊢
    apply mul_left_cancel₀ (show (4 : ℤ) ≠ 0 by norm_num)
    rw [mul_add, hb]
    ring

end OMA.P_oeis_a001792

theorem OMA.solution : type_of% @OMA.S_oeis_a001792.main := OMA.P_oeis_a001792.main'
