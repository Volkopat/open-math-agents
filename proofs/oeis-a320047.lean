import OMAStatements.S_oeis_a320047
import Mathlib

namespace OMA.S_oeis_a320047
open Polynomial

lemma P_eq (l : ℕ) : P l = C ((l:ℚ) - l*(l+1)*(2*l+1)) + C (3*(l:ℚ)*(l+1)) * X := by
  induction l with
  | zero => simp [P]
  | succ l ih =>
    have : P (l+1) = P l + ∑ j ∈ Finset.range 2, C (R j) * C ((l+1:ℕ) : ℚ) ^ j * (X - C ((l+1:ℕ) : ℚ)) ^ j := by
      unfold P
      rw [Finset.sum_Icc_succ_top (by omega)]
    rw [this, ih]
    simp [Finset.sum_range_succ, R]
    push_cast
    simp only [map_add, map_mul, map_sub, map_one, map_ofNat, map_pow, map_neg]
    ring_nf

lemma c0 (l : ℕ) : (P l).coeff 0 = (l:ℚ) - l*(l+1)*(2*l+1) := by
  rw [P_eq]; simp only [coeff_add, coeff_C_zero, coeff_C_mul, coeff_X_zero, mul_zero, add_zero]

lemma c1 (l : ℕ) : (P l).coeff 1 = 3*(l:ℚ)*(l+1) := by
  rw [P_eq]; simp only [coeff_add, coeff_C_mul, coeff_X_one, coeff_C, if_neg one_ne_zero, mul_one, zero_add]

lemma a_odd (k : ℕ) : a (2*k+1) = ((k:ℚ)+1)*((k:ℚ)+2)*(2*k+3) - ((k:ℚ)+1) := by
  have h : (2*k+1) % 2 = 1 := by omega
  have h2 : (2*k+1+1)/2 = k+1 := by omega
  simp only [a, h, h2, if_true, U, c0]
  push_cast
  ring

lemma a_even (k : ℕ) : a (2*k) = 3*(k:ℚ)*(k+1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [a, U, c1]
  have h : (2*k) % 2 = 0 := by omega
  have h2 : (2*k)/2 = k := by omega
  simp only [a, h, h2, U, c1]
  simp

end OMA.S_oeis_a320047

theorem OMA.solution : type_of% @OMA.S_oeis_a320047.main := by
  open OMA.S_oeis_a320047 in
  have cf : ∀ n : ℕ, 0 < n → a n = (4 - 4 * (-1) ^ n - 3 * (-5 + (-1) ^ n) * (n : ℚ) -
      3 * (-3 + (-1) ^ n) * (n : ℚ) ^ 2 + (1 + (-1) ^ (1 + n)) * (n : ℚ) ^ 3) / 8 := by
    intro n hn
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · have s1 : ((-1:ℚ))^(2*k) = 1 := by rw [pow_mul]; simp
      have s2 : ((-1:ℚ))^(1+2*k) = -1 := by rw [pow_add, pow_mul]; simp
      rw [a_even, s1, s2]
      push_cast; ring
    · have s1 : ((-1:ℚ))^(2*k+1) = -1 := by rw [pow_succ, pow_mul]; simp
      have s2 : ((-1:ℚ))^(1+(2*k+1)) = 1 := by rw [show 1+(2*k+1) = 2*(k+1) by ring, pow_mul]; simp
      rw [a_odd, s1, s2]
      push_cast; ring
  refine ⟨cf, ?_⟩
  intro n hn
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k-4, by omega⟩
    have e1 : 2*(j+4) - 2 = 2*(j+3) := by omega
    have e2 : 2*(j+4) - 4 = 2*(j+2) := by omega
    have e3 : 2*(j+4) - 6 = 2*(j+1) := by omega
    have e4 : 2*(j+4) - 8 = 2*j := by omega
    rw [e1, e2, e3, e4, a_even, a_even, a_even, a_even, a_even]
    push_cast; ring
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k-4, by omega⟩
    have e1 : 2*(j+4)+1 - 2 = 2*(j+3)+1 := by omega
    have e2 : 2*(j+4)+1 - 4 = 2*(j+2)+1 := by omega
    have e3 : 2*(j+4)+1 - 6 = 2*(j+1)+1 := by omega
    have e4 : 2*(j+4)+1 - 8 = 2*j+1 := by omega
    rw [e1, e2, e3, e4, a_odd, a_odd, a_odd, a_odd, a_odd]
    push_cast; ring

