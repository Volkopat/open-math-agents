import Mathlib

/-!
# A358982: In base 10, for all numbers with n digits, a(n) is the number where the sum of digits of a(n) minus the sum of the last n digits of a(n)^3 reaches a record maximum.

Source: https://oeis.org/A358982
Credit: @agchua

Example line of A358982 (the entry is by Martin Raab, Dec 08 2022), verbatim:
  Heuristically it can be conjectured that there are infinitely many numbers x for which the
  digit sum of x^3 is smaller than the digit sum of x.

Formalisation. The digit sum is the sum of the decimal digits (`Nat.digits 10`). The claim is
that the set of natural numbers x for which the digit sum of x^3 is smaller than the digit sum
of x is infinite.
-/

namespace OMA.S_oeis_a358982

/-- The sum of the decimal digits of `x`. -/
def digitSum (x : ℕ) : ℕ := (Nat.digits 10 x).sum

/-- There are infinitely many `x` whose cube has a smaller digit sum than `x`. -/
theorem main : Set.Infinite {x : ℕ | digitSum (x ^ 3) < digitSum x} := by
  sorry

end OMA.S_oeis_a358982
