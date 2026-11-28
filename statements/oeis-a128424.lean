import Mathlib

/-!
# A128424: a(n) = floor(sqrt(a(n-1)^2 + a(n-2)^2 + a(n-1)*a(n-2))), a(1)=1, a(2)=3.

Source: https://oeis.org/A128424
Credit: @SPatel2133

Conjectures from Colin Barker, Nov 03 2018 (OEIS formula section):
G.f.: x*(1 + x - 2*x^2 + x^3 - 2*x^4 + x^5 - x^6) / ((1 - x)*(1 - x - x^3)).
a(n) = 2*a(n-1) - a(n-2) + a(n-3) - a(n-4) for n>7.

The sequence has offset one. It is padded with `a 0 = 0`, the constant coefficient of the
conjectured generating function; the recurrence for `a (n + 3)` never reads `a 0`.
`Nat.sqrt` is the floor of the real square root. The values are cast to `ℤ` so that the
subtractions are exact. The generating function is stated with its denominator cleared.
-/

namespace OMA.S_oeis_a128424

open PowerSeries

def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | n + 3 => Nat.sqrt (a (n + 2) ^ 2 + a (n + 1) ^ 2 + a (n + 2) * a (n + 1))

theorem main :
    (∀ n : ℕ, 7 < n →
      (a n : ℤ) = 2 * a (n - 1) - a (n - 2) + a (n - 3) - a (n - 4)) ∧
    ((1 - X) * (1 - X - X ^ 3) * PowerSeries.mk (fun n => (a n : ℤ)) =
      (X * (1 + X - 2 * X ^ 2 + X ^ 3 - 2 * X ^ 4 + X ^ 5 - X ^ 6) : PowerSeries ℤ)) := by
  sorry

end OMA.S_oeis_a128424
