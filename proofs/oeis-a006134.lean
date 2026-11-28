import OMAStatements.S_oeis_a006134
import Mathlib

open OMA.S_oeis_a006134
open Polynomial

namespace P006134

theorem P_closed : ∀ m : ℕ, P m = ∑ i ∈ Finset.range (m / 2 + 1), X ^ i * (1 + X) ^ (m - 2 * i) := by
  intro m
  induction m with
  | zero => simp [P]
  | succ m ih =>
    show (1 + X) * P m + (if (m + 1) % 2 = 0 then X ^ ((m + 1) / 2) else 0) = _
    rw [ih, Finset.mul_sum]
    have hterm : ∀ i ∈ Finset.range (m / 2 + 1),
        ((1 + X : ℕ[X]) * (X ^ i * (1 + X) ^ (m - 2 * i))) = X ^ i * (1 + X) ^ (m + 1 - 2 * i) := by
      intro i hi
      simp only [Finset.mem_range] at hi
      rw [show m + 1 - 2 * i = (m - 2 * i) + 1 by omega, pow_succ]
      ring
    rw [Finset.sum_congr rfl hterm]
    split_ifs with h
    · rw [show (m + 1) / 2 = m / 2 + 1 by omega, Finset.sum_range_succ _ (m / 2 + 1),
        show m + 1 - 2 * (m / 2 + 1) = 0 by omega, pow_zero, mul_one]
    · rw [show (m + 1) / 2 = m / 2 by omega, add_zero]

theorem part1 (n : ℕ) : a n = T013580 (2 * n + 1) (n + 1) := by
  unfold T013580 a
  rw [show 2 * n + 1 - 1 = 2 * n by omega, show n + 1 - 1 = n by omega, P_closed,
    show 2 * n / 2 = n by omega, finset_sum_coeff]
  have : ∀ i ∈ Finset.range (n + 1), (X ^ i * (1 + X) ^ (2 * n - 2 * i) : ℕ[X]).coeff n =
      Nat.choose (2 * (n - i)) (n - i) := by
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [coeff_X_pow_mul', if_pos (by omega), coeff_one_add_X_pow,
      show 2 * n - 2 * i = 2 * (n - i) by omega]
    simp
  rw [Finset.sum_congr rfl this]
  rw [← Finset.sum_range_reflect (fun k => Nat.choose (2 * k) k) (n + 1)]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  rw [show n + 1 - 1 - i = n - i by omega]

theorem evsum : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), Nat.choose (2 * k) k =
    ∑ x ∈ Finset.range (2 * n + 1), (if 2 ∣ x then Nat.choose x (x / 2) else 0) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ _ (n + 1), ih, show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by ring,
      Finset.sum_range_succ _ ((2 * n + 1) + 1), Finset.sum_range_succ _ (2 * n + 1)]
    rw [if_neg (by omega), if_pos (by omega), show (2 * n + 1 + 1) / 2 = n + 1 by omega,
      show 2 * n + 1 + 1 = 2 * (n + 1) by ring]
    simp

theorem part2 (n : ℕ) : a n = T231147 (2 * n + 1) (n + 1) := by
  unfold T231147 R a
  rw [show n + 1 - 1 = n by omega, finset_sum_coeff]
  have hexp : ∀ j : ℕ, ((1 + X ^ 2) ^ j : ℕ[X]) = expand ℕ 2 ((1 + X) ^ j) := by
    intro j; simp [map_pow, map_add]
  have : ∀ j ∈ Finset.range (2 * n + 1), (X ^ (2 * n + 1 - 1 - j) * (1 + X ^ 2) ^ j : ℕ[X]).coeff (2 * n) =
      if 2 ∣ j then Nat.choose j (j / 2) else 0 := by
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [coeff_X_pow_mul', if_pos (by omega), hexp, coeff_expand (by norm_num), coeff_one_add_X_pow,
      show 2 * n - (2 * n + 1 - 1 - j) = j by omega]
    simp
  rw [Finset.sum_congr rfl this]
  exact evsum n


end P006134

theorem OMA.solution : type_of% @OMA.S_oeis_a006134.main :=
  ⟨P006134.part1, P006134.part2⟩
