import OMAStatements.S_oeis_a195986
import Mathlib

/-! Proof for OEIS A195986: for even `n`, the lifting-the-exponent lemma gives
`v₂(5^n - 3^n) = v₂(n) + 3` and `v₂(3^n - 1) = v₂(n) + 2 ≥ 3`; for odd `n`, both `5^n - 3^n` and
`3^n - 1` are `2 (mod 4)`, so both valuations are `1`.
Credit: Sudharsan Rajendiran -/

namespace OMA.P195986
open OMA.S_oeis_a195986

lemma val_of_mod4 (m : ℕ) (h : m % 4 = 2) : padicValNat 2 m = 1 := by
  obtain ⟨q, rfl⟩ : ∃ q, m = 2 * (2 * q + 1) := ⟨m / 4, by omega⟩
  rw [padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num),
    padicValNat.eq_zero_of_not_dvd (by omega)]

lemma odd_case (n : ℕ) (hn : Odd n) : a n = 1 ∧ b n = 1 := by
  obtain ⟨m, rfl⟩ := hn
  have h5 : 5 ^ (2 * m + 1) % 4 = 1 := by rw [Nat.pow_mod]; norm_num
  have h3 : 3 ^ (2 * m + 1) % 4 = 3 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num
  have hlt : 3 ^ (2 * m + 1) < 5 ^ (2 * m + 1) := Nat.pow_lt_pow_left (by norm_num) (by omega)
  have h1 : 1 ≤ 3 ^ (2 * m + 1) := Nat.one_le_pow _ _ (by norm_num)
  unfold a b
  generalize 5 ^ (2 * m + 1) = A at *
  generalize 3 ^ (2 * m + 1) = B at *
  exact ⟨val_of_mod4 _ (by omega), val_of_mod4 _ (by omega)⟩

lemma even_case (n : ℕ) (hn0 : n ≠ 0) (hn : Even n) :
    a n = padicValNat 2 n + 3 ∧ b n = padicValNat 2 n + 2 := by
  have hA := padicValNat.pow_two_sub_pow (x := 5) (y := 3) (by norm_num) (by norm_num)
    (by norm_num) hn0 hn
  have hB := padicValNat.pow_two_sub_pow (x := 3) (y := 1) (by norm_num) (by norm_num)
    (by norm_num) hn0 hn
  have h8 : padicValNat 2 (5 + 3) = 3 := by
    rw [show (5 + 3 : ℕ) = 2 ^ 3 by norm_num, padicValNat.prime_pow]
  have h2 : padicValNat 2 (5 - 3) = 1 := by norm_num
  have h4 : padicValNat 2 (3 + 1) = 2 := by
    rw [show (3 + 1 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
  have h2' : padicValNat 2 (3 - 1) = 1 := by norm_num
  rw [h8, h2] at hA
  rw [h4, h2', one_pow] at hB
  unfold a b
  omega

end OMA.P195986

theorem OMA.solution : type_of% @OMA.S_oeis_a195986.main := by
  intro n hn
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨ha, hb⟩ := OMA.P195986.even_case n (by omega) he
    have hv : 1 ≤ padicValNat 2 n := one_le_padicValNat_of_dvd (by omega) (even_iff_two_dvd.mp he)
    rw [ha, hb, if_neg (by omega)]
  · obtain ⟨ha, hb⟩ := OMA.P195986.odd_case n ho
    rw [ha, hb, if_pos rfl]

