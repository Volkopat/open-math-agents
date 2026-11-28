import Mathlib

/-!
# A060035: Least m >= 0 such that 2^m has n 2's in its base-3 expansion.

Source: https://oeis.org/A060035
Credit: @azmiozgen

Conjecture quoted in the entry: "Paul Erdős conjectured that for n > 8, 2^n is not a sum of
distinct powers of 3. In terms of digits, this states that powers of 2 for n > 8 must always
contain a '2' in their base 3 expansion."

Formalization notes:
* The digit form is stated: for every n > 8, the digit 2 occurs among the base-3 digits of 2^n
  (`Nat.digits 3`, least significant first; the order does not matter here). A natural number is a
  sum of distinct powers of 3 exactly when its base-3 digits are all 0 or 1.
* In terms of this sequence, the conjecture says that 0, 2 and 8 are the only m for which 2^m
  has no digit 2 in base 3; the statement does not need the sequence itself.
* Controls: for n < 60, the powers 2^n without a digit 2 in base 3 are exactly n = 0, 2, 8
  (1, 11, 100111 in base 3).
-/

namespace OMA.S_oeis_a060035

/-- Erdős's ternary conjecture: for `n > 8`, `2 ^ n` has a digit `2` in base 3. -/
theorem main : ∀ n : ℕ, 8 < n → 2 ∈ Nat.digits 3 (2 ^ n) := by
  sorry

end OMA.S_oeis_a060035
