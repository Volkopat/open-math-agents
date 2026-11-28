import Mathlib

/-!
# A298607: Powers of 2 with the digit '0' in their decimal expansion.

Source: https://oeis.org/A298607
Credit: @darealpandaboi

Conjecture: the complement A238938 (powers of 2 without the digit 0) is finite.

Translation notes.
* The complement of this sequence within the powers of 2 is the set of powers 2^k (k >= 0) whose
  decimal digits do not include 0; the statement says that set is finite.
* Khovanova's belief that 2^86 is the largest power of 2 not in this sequence is reported as a
  belief, not as a conjecture of the entry, so it is not stated. Among k < 10000 the zeroless
  powers are 2^k for k = 0, ..., 9, 13, 14, 15, 16, 18, 19, 24, 25, 27, 28, 31, ..., 37, 39, 49,
  51, 67, 72, 76, 77, 81, 86 (checked by computer).
-/

namespace OMA.S_oeis_a298607

theorem main : {m : ℕ | (∃ k : ℕ, m = 2 ^ k) ∧ 0 ∉ Nat.digits 10 m}.Finite := by
  sorry

end OMA.S_oeis_a298607
