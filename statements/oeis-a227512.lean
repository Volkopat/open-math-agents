import Mathlib

/-!
# A227512: Floor(-1/n + 1/log((2n+1)/(2n-1)))

Data (offset 1): 10, 92, 318, 760, 1490, 2581, 4103, 6129, 8731, 11981, ...

a(n) = 12*n^3 - floor(9*n/5) - 1. (conjectured, based on computations by Peter J. C. Moses, Jul 14 2013)
a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) + a(n-5) - 3*a(n-6) + 3*a(n-7) - a(n-8) (conjectured; verified up to n = 100000).
G.f.: (10 + 62 x + 72 x^2 + 72 x^3 + 72 x^4 + 63 x^5 + 8 x^6 + x^7)/((-1 + x)^4 (1 + x + x^2 + x^3 + x^4)) (conjectured).

Conventions: a n is the floor of 1 / (log((2n+1)/(2n-1)) - 1/n), computed in the reals, for n at
least 1. The OEIS name writes -1/n + 1/log((2n+1)/(2n-1)), but its comment, example and data all
use the reciprocal of log((2n+1)/(2n-1)) - 1/n (for n = 4: -1/4 + log(9/7) = 0.0013144...,
1/0.0013144... = 760.78...), and that is what is stated here. The closed form is stated for
n at least 1, the recurrence for n at least 9 (it reaches back to a(n-8)), and the g.f.
as printed has no factor x, so its coefficient at x^k is a(k+1).
-/

namespace OMA.S_oeis_a227512

noncomputable def a (n : ℕ) : ℤ :=
  ⌊1 / (Real.log ((2 * n + 1) / (2 * n - 1)) - 1 / n)⌋

open PowerSeries in
theorem main :
    (∀ n : ℕ, 1 ≤ n → a n = 12 * n ^ 3 - ⌊(9 * n / 5 : ℚ)⌋ - 1) ∧
      (∀ n : ℕ, 9 ≤ n → a n = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) + a (n - 5)
        - 3 * a (n - 6) + 3 * a (n - 7) - a (n - 8)) ∧
      PowerSeries.mk (fun k => a (k + 1)) * ((-1 + X) ^ 4 * (1 + X + X ^ 2 + X ^ 3 + X ^ 4) : ℤ⟦X⟧) =
        10 + 62 * X + 72 * X ^ 2 + 72 * X ^ 3 + 72 * X ^ 4 + 63 * X ^ 5 + 8 * X ^ 6 + X ^ 7 := by
  sorry

end OMA.S_oeis_a227512
