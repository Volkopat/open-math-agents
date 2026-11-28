import Mathlib

/-!
# OEIS A030701: the decimal expansion of 4^n contains no zeros

Source: https://oeis.org/A030701 (OEIS Foundation, CC BY-SA 4.0)
Credit: @sntntHb

A030701 lists the `n` such that `4^n` has no digit 0 in base 10:
0, 1, 2, 3, 4, 7, 8, 9, 12, 14, 16, 17, 18, 36, 38, 43. The entry states:

  Integers in A007377 / 2. Conjectured to be finite, and probably complete.

We formalize the strongest form, which contains both parts (finiteness and completeness):
the set of `n` such that `0` is not a decimal digit of `4^n` is exactly the listed set.
(A direct computation confirms that no further `n < 3000` qualifies.)
-/

namespace OMA.S_oeis_a030701

/-- The exponents `n` for which `4^n` has no zero digit in base 10. -/
def zeroless : Set ℕ := {n | 0 ∉ Nat.digits 10 (4 ^ n)}

/-- Conjecture of A030701: the list of terms is finite and complete. -/
theorem main : zeroless = {0, 1, 2, 3, 4, 7, 8, 9, 12, 14, 16, 17, 18, 36, 38, 43} := by
  sorry

end OMA.S_oeis_a030701
