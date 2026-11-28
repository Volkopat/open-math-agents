import Mathlib

/-!
# A104896: a(0) = 0; a(n) = 7*a(n-1) + 7.

Source: https://oeis.org/A104896
Credit: @rickmanelius

Conjecture: this is also the number of integers from 0 to 10^n - 1 that lack 0, 1 and 2 as a
digit.

Formalization notes:
* The sequence is defined by the recurrence in the name of the entry: a(0) = 0 and
  a(n) = 7*a(n-1) + 7 for n ≥ 1, written a (n + 1) = 7 * a n + 7. The offset is 0.
* The integers from 0 to 10^n - 1 are the natural numbers m < 10^n, that is Finset.range (10 ^ n).
* A number lacks 0, 1 and 2 as a digit when none of its decimal digits is 0, 1 or 2. The decimal
  digits of m are Nat.digits 10 m (least significant first, no leading zero when m > 0).
* The number 0 is written with the single digit 0, so it does not lack the digit 0 and is not
  counted. Since Nat.digits 10 0 is the empty list, 0 is excluded explicitly by the condition
  0 < m. This reading matches the data: a(1) = 7 counts 3, 4, ..., 9 among 0, ..., 9.
* The conjecture is stated for every n ≥ 0, the offset of the entry (for n = 0 both sides are 0).
-/

namespace OMA.S_oeis_a104896

/-- A104896: a(0) = 0 and a(n) = 7*a(n-1) + 7 for n ≥ 1. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => 7 * a n + 7

/-- The conjecture: a(n) is the number of integers m with 0 ≤ m ≤ 10^n - 1 none of whose decimal
digits is 0, 1 or 2. -/
theorem main :
    ∀ n : ℕ, a n = ((Finset.range (10 ^ n)).filter
      (fun m => 0 < m ∧ ∀ d ∈ Nat.digits 10 m, d ≠ 0 ∧ d ≠ 1 ∧ d ≠ 2)).card := by
  sorry

end OMA.S_oeis_a104896
