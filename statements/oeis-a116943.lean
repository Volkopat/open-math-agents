import Mathlib

/-!
# A116943: Number of 4s digits plus non-final 3s digits 3 base 5 expansion of 2^n.

Source: https://oeis.org/A116943
Credit: @gblacher2

Conjecture (comment section of A116943):
"In his comment on A038003 Frank Adams-Watters conjectures "that 2^n contains such a base 5
digit for n>=9. This is almost certainly true." That is equivalent to a(n) > 0 for n>=9, which
is also equivalent to A094389(n) = 5 where A094389 is last decimal digit of the odd Catalan
number A038003(n)."

The statement below is the form a(n) > 0 for n >= 9.

The sequence has offset 0: 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 3, 2, ...

Modelling choices:
* `Nat.digits 5 m` lists the base-5 digits of `m` from the least significant (rightmost)
  one, so its head is the final digit and its tail lists the other digits.
* `a n` counts every digit 4 of `2 ^ n` in base 5, plus every digit 3 other than the final
  (rightmost) one. This matches the examples of the entry: 2^7 = 1003 in base 5 gives
  a(7) = 0 ("it has a digit 3, but that digit is final, meaning rightmost"), and
  2^10 = 13044 in base 5 gives a(10) = 2 + 1 = 3.
-/

namespace OMA.S_oeis_a116943

/-- A116943(n): the number of digits 4 plus the number of non-final digits 3 in the base-5
expansion of `2 ^ n`. -/
def a (n : ℕ) : ℕ :=
  (Nat.digits 5 (2 ^ n)).count 4 + (Nat.digits 5 (2 ^ n)).tail.count 3

/-- The conjecture: a(n) > 0 for n ≥ 9. -/
theorem main : ∀ n : ℕ, 9 ≤ n → 0 < a n := by
  sorry

end OMA.S_oeis_a116943
