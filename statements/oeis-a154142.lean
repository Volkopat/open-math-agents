import Mathlib

/-!
# A154142: Indices k such that 9 plus the k-th triangular number is a perfect square.

Source: https://oeis.org/A154142
Credit: @SPatel2133

Conjectures from the OEIS entry:
a(n) = a(n-1) + 6*a(n-2) - 6*a(n-3) - a(n-4) + a(n-5).
G.f.: x^2*(10 + 3*x - 10*x^2 - x^3)/((1-x) * (x^2-2*x-1) * (x^2+2*x-1)).

The sequence lists, in increasing order and with offset one, the numbers k such that
9 + k*(k+1)/2 is a square: 0, 10, 13, 63, 80, 370, 469, ... Here it is `Nat.nth` of that
predicate, shifted to offset one, and padded with `a 0 = 0`, the constant coefficient of the
generating function. The recurrence is stated for n > 5, where it only reads terms of the
sequence; with the padding it fails at n = 5. The values are cast to `ℤ` so that the
subtraction is exact. The generating function is stated with its denominator cleared. The
second form of the generating function in the entry is the partial fraction expansion of the
first.
-/

namespace OMA.S_oeis_a154142

open PowerSeries

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.nth (fun k => IsSquare (9 + k * (k + 1) / 2)) (n - 1)

theorem main :
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = a (n - 1) + 6 * a (n - 2) - 6 * a (n - 3) - a (n - 4) + a (n - 5)) ∧
    ((1 - X) * (X ^ 2 - 2 * X - 1) * (X ^ 2 + 2 * X - 1) * PowerSeries.mk (fun n => (a n : ℤ)) =
      (X ^ 2 * (10 + 3 * X - 10 * X ^ 2 - X ^ 3) : PowerSeries ℤ)) := by
  sorry

end OMA.S_oeis_a154142
