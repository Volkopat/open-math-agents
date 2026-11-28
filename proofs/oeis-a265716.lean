import OMAStatements.S_oeis_a265716
import Mathlib

open Nat

/-!
# A265716: McEachen's formula for n IMPL 2n

With L the binary length of n ≥ 1, the binary length of 2n is L + 1, and
2^(L+1) − 1 − n = 2^L + (2^L − 1 − n) with 2^L − 1 − n < 2^L. Comparing bits: below position L both
sides read the bits of 2^L − 1 − n or 2n; at position L both are set, because 2n has its top bit
there; above L both vanish.
-/

namespace A265716Proof

theorem top_bit (x L : ℕ) (h1 : 2 ^ L ≤ x) (h2 : x < 2 ^ (L + 1)) : x.testBit L = true := by
  have e : x = 2 ^ L + (x - 2 ^ L) := by omega
  rw [e, testBit_two_pow_add_eq, testBit_lt_two_pow (by rw [pow_succ] at h2; omega)]
  rfl

end A265716Proof

open OMA.S_oeis_a265716 in
theorem OMA.solution : type_of% @OMA.S_oeis_a265716.main := by
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [a, impl, A003817]
  unfold a impl A003817
  rw [if_neg hn.ne']
  have hs : size (2 * n) = size n + 1 := by
    rw [show 2 * n = n <<< 1 by rw [shiftLeft_eq]; ring]
    exact size_shiftLeft hn.ne' 1
  rw [hs]
  have hL : 0 < size n := size_pos.mpr hn
  have hnL : n < 2 ^ size n := lt_size_self n
  have hLn : 2 ^ (size n - 1) ≤ n := lt_size.mp (by omega)
  generalize size n = L at hL hnL hLn
  have hpow : 2 ^ L = 2 * 2 ^ (L - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hm : 2 ^ (L + 1) - 1 - n = 2 ^ L + (2 ^ L - 1 - n) := by
    rw [pow_succ]; omega
  rw [hm]
  have h2n : (2 * n).testBit L = true :=
    A265716Proof.top_bit _ _ (by omega) (by rw [pow_succ]; omega)
  apply eq_of_testBit_eq
  intro i
  rw [testBit_lor, testBit_lor]
  rcases lt_trichotomy i L with h | rfl | h
  · rw [testBit_two_pow_add_gt h]
  · rw [testBit_two_pow_add_eq, testBit_lt_two_pow (show 2 ^ i - 1 - n < 2 ^ i by omega), h2n]
    rfl
  · have hi : 2 ^ (L + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) h
    rw [testBit_lt_two_pow (show 2 ^ L + (2 ^ L - 1 - n) < 2 ^ i by rw [pow_succ] at hi; omega),
      testBit_lt_two_pow (show 2 ^ L - 1 - n < 2 ^ i by rw [pow_succ] at hi; omega)]
