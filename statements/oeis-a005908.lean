import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# A005908: a(n) = floor(phi*a(n-1)) + floor(phi*a(n-2)), where phi is the golden ratio

Source: https://oeis.org/A005908
Credit: @SPatel2133

Conjectures of Chai Wah Wu, 13 June 2020:
a(n) = 2*a(n-1) + a(n-2) - a(n-4) - a(n-5) for n > 4, and
G.f.: x*(-x^3 - x^2 - x + 1)/(x^5 + x^4 - x^2 - 2*x + 1).

The sequence has offset zero, with a(0) = 0 and a(1) = 1. The generating function is stated
with its denominator cleared.
-/

namespace OMA.S_oeis_a005908

open PowerSeries

noncomputable def a : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => ⌊Real.goldenRatio * (a (n + 1) : ℝ)⌋ + ⌊Real.goldenRatio * (a n : ℝ)⌋

theorem main :
    (∀ n : ℕ, 4 < n → a n = 2 * a (n - 1) + a (n - 2) - a (n - 4) - a (n - 5)) ∧
    ((X ^ 5 + X ^ 4 - X ^ 2 - 2 * X + 1) * PowerSeries.mk a =
      (X * (-X ^ 3 - X ^ 2 - X + 1) : PowerSeries ℤ)) := by
  sorry

end OMA.S_oeis_a005908
