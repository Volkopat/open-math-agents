import Mathlib

/-!
# A113318: Numbers whose biquadrates (fourth powers) are exclusionary.

Source: https://oeis.org/A113318
Credit: @darealpandaboi

Conjecture: the sequence is complete.

Translation notes.
* A positive integer m with no repeated decimal digits has an exclusionary fourth power when no
  decimal digit of m^4 appears in m.
* Complete is stated as: the set of such m is exactly the set of the 26 listed terms
  2, 3, 4, 7, 8, 9, 24, ..., 843, 2673.
* m has distinct digits, so m < 10^10 and the statement is a finite check: an exhaustive computer
  search over all positive integers with distinct digits finds exactly the listed terms.
-/

namespace OMA.S_oeis_a113318

theorem main :
    {m : ℕ | 0 < m ∧ (Nat.digits 10 m).Nodup ∧
      ∀ d ∈ Nat.digits 10 (m ^ 4), d ∉ Nat.digits 10 m} =
      {2, 3, 4, 7, 8, 9, 24, 27, 28, 32, 42, 52, 53, 58, 59, 67, 89, 93, 203, 258, 284, 324,
        329, 832, 843, 2673} := by
  sorry

end OMA.S_oeis_a113318
