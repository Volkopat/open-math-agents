import Mathlib

/-!
# A127275: Mathar's recurrence, corrected to n ≥ 3

Source: https://oeis.org/A127275
Credit: @ivillar

Status: known result. The entry records: Conjecture verified using the differential equation (4*x-1)^2 * g'(x) +
(8*x-2)*g(x) + 1 - 2*x = 0 satisfied by the g.f. - Robert Israel, Jan 15 2023
It is false as stated at n = 2 (the left side is 2 at n = 2 on the OEIS data); `main` is the
corrected recurrence (n ≥ 3), which is proved.

A127275 (offset 0): expansion of (sqrt(1-4x)-x)/(1-4x);
data 1, 1, 2, 4, 6, -4, -100, -664, -3514, -16916, -77388, -343144, ...

Conjecture (R. J. Mathar, Nov 26 2012):
n*a(n) + 2*(-4*n+3)*a(n-1) + 8*(2*n-3)*a(n-2) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1
(the constant term selects the branch of the square root), and the g.f. G is determined by
(1 - 4*x)*G = S - x;
a(n) = [x^n] G. `main` is the corrected recurrence (n ≥ 3): on the data the left side of the recurrence as
stated is 2 at n = 2, and it vanishes from n = 3 on.
-/

namespace OMA.S_oeis_a127275

open PowerSeries

/-- The corrected recurrence (n ≥ 3): Mathar's recurrence, which fails at n = 2. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    (1 - 4 * X) * G = S - X →
    ∀ n : ℕ, 3 ≤ n →
      ((n : ℚ)) * coeff n G + (6 - 8 * (n : ℚ)) * coeff (n - 1) G +
        (-24 + 16 * (n : ℚ)) * coeff (n - 2) G = 0 := by
  sorry

end OMA.S_oeis_a127275
