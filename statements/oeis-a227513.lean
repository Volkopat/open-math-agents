import Mathlib

/-!
# A227513: Round(-1/n + 1/log((2n+1)/(2n-1)))

Data (offset 1): 10, 92, 319, 761, 1491, 2581, 4103, 6130, 8732, 11982, ...

a(n) = 12*n^3 - round(9*n/5) (conjectured, based on computations by Peter J. C. Moses, Jul 14 2013).
a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) + a(n-5) - 3*a(n-6) + 3*a(n-7) - a(n-8) (conjectured; verified up to n = 100000).
G.f.: x*(10 + 62*x + 73*x^2 + 70*x^3 + 73*x^4 + 62*x^5 + 10*x^6)/((-1 + x)^4*(1 + x + x^2 + x^3 + x^4)) (conjectured).

Conventions: a n is the round (Mathlib round, half up) of 1 / (log((2n+1)/(2n-1)) - 1/n), computed in the reals, for n at
least 1. The OEIS name writes -1/n + 1/log((2n+1)/(2n-1)), but its comment, example and data all
use the reciprocal of log((2n+1)/(2n-1)) - 1/n (for n = 4: -1/4 + log(9/7) = 0.0013144...,
1/0.0013144... = 760.78...), and that is what is stated here. The closed form is stated for
n at least 1, the recurrence for n at least 9 (it reaches back to a(n-8)), and the g.f.
starts at x^1 (offset 1), so its coefficient at x^0 is 0.
-/

namespace OMA.S_oeis_a227513

noncomputable def a (n : ℕ) : ℤ :=
  round (1 / (Real.log ((2 * n + 1) / (2 * n - 1)) - 1 / n))

open PowerSeries in
theorem main :
    (∀ n : ℕ, 1 ≤ n → a n = 12 * n ^ 3 - round (9 * n / 5 : ℚ)) ∧
      (∀ n : ℕ, 9 ≤ n → a n = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) + a (n - 5)
        - 3 * a (n - 6) + 3 * a (n - 7) - a (n - 8)) ∧
      PowerSeries.mk (fun n => if n = 0 then 0 else a n) *
          ((-1 + X) ^ 4 * (1 + X + X ^ 2 + X ^ 3 + X ^ 4) : ℤ⟦X⟧) =
        X * (10 + 62 * X + 73 * X ^ 2 + 70 * X ^ 3 + 73 * X ^ 4 + 62 * X ^ 5 + 10 * X ^ 6) := by
  sorry

end OMA.S_oeis_a227513
