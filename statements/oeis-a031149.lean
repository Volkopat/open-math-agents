import Mathlib

/-!
# A031149: Numbers whose square with its last digit deleted is also a square.

Source: https://oeis.org/A031149
Credit: @SPatel2133

Conjecture (Colin Barker, Dec 31 2017): a(n) = 38*a(n-7) - a(n-14) for n > 15.
Empirical g.f. (Colin Barker, Jan 17 2014):
x^2*(1 + 2*x + 3*x^2 + 4*x^3 + 7*x^4 + 13*x^5 + 16*x^6 - 19*x^7 - 38*x^8 - 57*x^9 - 16*x^10
  - 13*x^11 - 7*x^12 - 4*x^13) / (1 - 38*x^7 + x^14).

Deleting the last decimal digit of x^2 gives floor(x^2/10); for a one-digit square the result
is 0, as the OEIS entry says. So the sequence lists, in increasing order and with offset one,
the numbers x such that floor(x^2/10) is a square: 0, 1, 2, 3, 4, 7, 13, 16, 19, 38, 57, ...
Here it is `Nat.nth` of that predicate, shifted to offset one, and padded with `a 0 = 0`, the
constant coefficient of the generating function. The values are cast to `ℤ` so that the
subtraction is exact. The generating function is stated with its denominator cleared.
-/

namespace OMA.S_oeis_a031149

open PowerSeries

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.nth (fun x => IsSquare (x ^ 2 / 10)) (n - 1)

theorem main :
    (∀ n : ℕ, 15 < n → (a n : ℤ) = 38 * a (n - 7) - a (n - 14)) ∧
    ((1 - 38 * X ^ 7 + X ^ 14) * PowerSeries.mk (fun n => (a n : ℤ)) =
      (X ^ 2 * (1 + 2 * X + 3 * X ^ 2 + 4 * X ^ 3 + 7 * X ^ 4 + 13 * X ^ 5 + 16 * X ^ 6
        - 19 * X ^ 7 - 38 * X ^ 8 - 57 * X ^ 9 - 16 * X ^ 10 - 13 * X ^ 11 - 7 * X ^ 12
        - 4 * X ^ 13) : PowerSeries ℤ)) := by
  sorry

end OMA.S_oeis_a031149
