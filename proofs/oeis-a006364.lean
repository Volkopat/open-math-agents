import OMAStatements.S_oeis_a006364

-- Problem: Velin Yanev's formula for OEIS A006364.
-- Source: https://oeis.org/A006364
-- Credit: @yiklin21

namespace A006364Proof
open OMA.S_oeis_a006364

instance : DecidablePred Qualifies := fun m => inferInstanceAs (Decidable (bitCount (m / 2) % 2 = 0))

lemma bitCount_bit (b r : ℕ) (hr : r < 2) :
    bitCount (2 * b + r) = bitCount b + r := by
  by_cases h : 2 * b + r = 0
  · have hb : b = 0 := by omega
    have hz : r = 0 := by omega
    simp [hb, hz]
  · unfold bitCount
    rw [Nat.digits_eq_cons_digits_div (by decide : 1 < 2) h, List.sum_cons,
      show (2 * b + r) % 2 = r by omega, show (2 * b + r) / 2 = b by omega, Nat.add_comm]

-- The first pair qualifies exactly when the binary weight of b is even.
lemma qualifies_iff (b i : ℕ) (hi : i < 4) :
    Qualifies (4 * b + i) ↔ i / 2 = bitCount b % 2 := by
  unfold Qualifies
  rw [show (4 * b + i) / 2 = 2 * b + i / 2 by omega, bitCount_bit b (i / 2) (by omega)]
  omega

lemma count_block (b i : ℕ) (hi : i ≤ 4) :
    Nat.count Qualifies (4 * b + i) =
      Nat.count Qualifies (4 * b) + min 2 (i - 2 * (bitCount b % 2)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Nat.add_succ, Nat.count_succ, ih (by omega)]
    simp only [qualifies_iff b i (by omega)]
    split <;> omega

lemma count_blocks (b : ℕ) : Nat.count Qualifies (4 * b) = 2 * b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.mul_succ, count_block b 4 (by decide), ih]
    omega

lemma nth_pair (b r : ℕ) (hr : r < 2) :
    Nat.nth Qualifies (2 * b + r) = 4 * b + (2 * (bitCount b % 2) + r) := by
  let i := 2 * (bitCount b % 2) + r
  have hi : i < 4 := by dsimp [i]; omega
  have hq : Qualifies (4 * b + i) := (qualifies_iff b i hi).2 (by dsimp [i]; omega)
  have hc := count_block b i (by omega)
  rw [count_blocks] at hc
  have hindex : Nat.count Qualifies (4 * b + i) = 2 * b + r := by dsimp [i] at hc ⊢; omega
  rw [← hindex]
  exact Nat.nth_count hq

lemma sign_pow (e : ℕ) : (-1 : ℤ) ^ e = if e % 2 = 0 then 1 else -1 := by
  induction e with
  | zero => decide
  | succ e ih => rw [pow_succ, ih]; split <;> split <;> omega

end A006364Proof

open OMA.S_oeis_a006364 A006364Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a006364.main := by
  intro n hn
  obtain ⟨b, r, hr, rfl⟩ : ∃ b r : ℕ, r < 2 ∧ n = 2 * b + r + 1 :=
    ⟨(n - 1) / 2, (n - 1) % 2, by omega, by omega⟩
  simp only [a, Nat.add_sub_cancel, nth_pair b r hr, bitCount_bit b r hr]
  rw [sign_pow, sign_pow]
  have h : bitCount b ≤ b := Nat.digit_sum_le 2 b
  split <;> split <;> omega
