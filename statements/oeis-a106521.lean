import Mathlib

/-!
# A106521: Numbers m such that Sum_{k=0..10} (m+k)^2 is a square.

Source: https://oeis.org/A106521
Credit: @SPatel2133

G.f. (Vladeta Jovovic, May 31 2005; adapted to the offset by Bruno Berselli):
2*x*(9+10*x+29*x^2-x^3-2*x^4)/(1-x)/(1-20*x^2+x^4).
M. F. Hasler's comment in the entry (Jan 27 2008) calls this the conjectured g.f.

The sequence lists, in increasing order and with offset one, the natural numbers m such that
m^2 + (m+1)^2 + ... + (m+10)^2 is a square: 18, 38, 456, 854, 9192, ... Here it is `Nat.nth`
of that predicate, shifted to offset one, and padded with `a 0 = 0`, the constant coefficient
of the generating function. The values are cast to `ℤ` so that the subtraction is exact. The
generating function is stated with its denominator cleared.
-/

namespace OMA.S_oeis_a106521

open PowerSeries

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else Nat.nth (fun m => IsSquare (∑ k ∈ Finset.range 11, (m + k) ^ 2)) (n - 1)

theorem main :
    (1 - X) * (1 - 20 * X ^ 2 + X ^ 4) * PowerSeries.mk (fun n => (a n : ℤ)) =
      (2 * X * (9 + 10 * X + 29 * X ^ 2 - X ^ 3 - 2 * X ^ 4) : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a106521
