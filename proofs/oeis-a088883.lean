import OMAStatements.S_oeis_a088883
import Mathlib

open OMA.S_oeis_a088883

lemma OMA.rev3 (p : ℕ) : rev p % 3 = p % 3 := by
  have h1 : rev p ≡ Nat.ofDigits (10 % 3) (Nat.digits 10 p).reverse [MOD 3] := Nat.ofDigits_modEq 10 3 _
  have h2 : p ≡ (Nat.digits 10 p).sum [MOD 3] := Nat.modEq_three_digits_sum p
  rw [show 10 % 3 = 1 by norm_num, Nat.ofDigits_one, List.sum_reverse] at h1
  exact h1.trans h2.symm

theorem OMA.solution : type_of% @OMA.S_oeis_a088883.main := by
  intro p hp hN
  rcases hp.eq_two_or_odd with rfl | h
  · revert hN; decide
  obtain rfl | h' := eq_or_ne p 3
  · revert hN; decide
  have := OMA.rev3 p
  have := hp.two_le
  have := Nat.le_mul_of_pos_right p (by positivity : 0 < 10 ^ (Nat.digits 10 p).length)
  have : p * 10 ^ (Nat.digits 10 p).length % 3 = p % 3 := by simp [Nat.mul_mod, Nat.pow_mod]
  generalize p * 10 ^ _ = t at *
  have : ¬ 3 ∣ p := fun d => by have := hp.eq_one_or_self_of_dvd 3 d; omega
  have : ¬ 3 ∣ t + rev p + 2 := fun d => by have := hN.eq_one_or_self_of_dvd 3 d; omega
  have : p % 3 = 1 := by omega
  omega
