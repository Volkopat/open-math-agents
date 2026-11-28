import OMAStatements.S_oeis_a026021
import Mathlib

/-!
The argument follows the accepted proof of the template entry A026008: split by parity, write
every term as a rational multiple of one central binomial coefficient, then clear denominators.
The factor k(k-1)(k-2) vanishes for k < 3, matching the convention binomial(n, k-3) = 0.
-/

open OMA.S_oeis_a026021

namespace A026021Proof

lemma c_succ (k : ℕ) :
    ((2*(k+1)).choose (k+1) : ℚ) = ((2*k).choose k : ℚ) * (2*(2*k+1)) / (k+1) := by
  have h := Nat.succ_mul_centralBinom_succ k
  simp only [Nat.centralBinom_eq_two_mul_choose] at h
  have h' : ((k:ℚ)+1) * ((2*(k+1)).choose (k+1) : ℚ) = 2*(2*k+1) * ((2*k).choose k : ℚ) := by
    exact_mod_cast h
  field_simp
  linear_combination h'

lemma odd_c (k : ℕ) : ((2*k+1).choose k : ℚ) = ((2*k).choose k : ℚ) * (2*k+1) / (k+1) := by
  have h1 : ((2*k+1).choose k : ℚ) = (2*k+1).factorial / (k.factorial * (k+1).factorial) := by
    rw [Nat.cast_choose ℚ (by omega : k ≤ 2*k+1), show 2*k+1-k = k+1 by omega]
  have h2 : ((2*k).choose k : ℚ) = (2*k).factorial / (k.factorial * k.factorial) := by
    rw [Nat.cast_choose ℚ (by omega : k ≤ 2*k), show 2*k-k = k by omega]
  rw [h1, h2]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  field_simp

lemma even_a (k : ℕ) : a (2*k) = ((2*k).choose k : ℚ) *
    (1 - (k:ℚ)*((k:ℚ)-1)*((k:ℚ)-2)/(((k:ℚ)+1)*((k:ℚ)+2)*((k:ℚ)+3))) := by
  rw [a, show 2*k/2 = k by omega, T]
  rcases (show k < 3 ∨ 3 ≤ k by omega) with hk | hk
  · rw [if_neg (by omega)]
    interval_cases k <;> norm_num
  · rw [if_pos hk]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k-3, by omega⟩
    rw [show j + 3 - 3 = j by omega,
      Nat.cast_choose ℚ (by omega : j ≤ 2*(j+3)), Nat.cast_choose ℚ (by omega : j+3 ≤ 2*(j+3)),
      show 2*(j+3) - j = j + 6 by omega, show 2*(j+3) - (j+3) = j+3 by omega]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    field_simp
    ring

lemma odd_a (k : ℕ) : a (2*k+1) = ((2*k).choose k : ℚ) * (2*k+1) / (k+1) *
    (1 - (k:ℚ)*((k:ℚ)-1)*((k:ℚ)-2)/(((k:ℚ)+2)*((k:ℚ)+3)*((k:ℚ)+4))) := by
  rw [a, show (2*k+1)/2 = k by omega, T, ← odd_c]
  rcases (show k < 3 ∨ 3 ≤ k by omega) with hk | hk
  · rw [if_neg (by omega)]
    interval_cases k <;> norm_num
  · rw [if_pos hk]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k-3, by omega⟩
    rw [show j + 3 - 3 = j by omega,
      Nat.cast_choose ℚ (by omega : j ≤ 2*(j+3)+1),
      Nat.cast_choose ℚ (by omega : j+3 ≤ 2*(j+3)+1),
      show 2*(j+3) + 1 - j = j + 7 by omega, show 2*(j+3) + 1 - (j+3) = j+4 by omega]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    field_simp
    ring

end A026021Proof

open A026021Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a026021.main := by
  intro n hn
  obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2*k+4 ∨ n = 2*k+5 := ⟨(n-4)/2, by omega⟩
  · rw [show 2*k+4-1 = 2*(k+1)+1 by omega, show 2*k+4-2 = 2*(k+1) by omega,
      show 2*k+4-3 = 2*k+1 by omega, show 2*k+4-4 = 2*k by omega,
      show 2*k+4 = 2*(k+2) by omega, even_a, even_a, even_a, odd_a, odd_a,
      c_succ (k+1), c_succ k]
    push_cast
    field_simp
    ring
  · rw [show 2*k+5-1 = 2*(k+2) by omega, show 2*k+5-2 = 2*(k+1)+1 by omega,
      show 2*k+5-3 = 2*(k+1) by omega, show 2*k+5-4 = 2*k+1 by omega,
      show 2*k+5 = 2*(k+2)+1 by omega, even_a, even_a, odd_a, odd_a, odd_a,
      c_succ (k+1), c_succ k]
    push_cast
    field_simp
    ring
