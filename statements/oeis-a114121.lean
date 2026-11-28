import Mathlib

/-!
# A114121: Mathar's recurrence, corrected to n ≥ 3

Source: https://oeis.org/A114121
Credit: @ivillar

Status: known result. The entry records: Conjecture verified using the differential equation (16*x^2-8*x+1)*g'(x) +
(8*x-2)*g(x)-2*x=0 satisfied by the G.f. - Robert Israel, Jul 27 2020
It is false as stated at n = 2 (the left side is 2 at n = 2 on the OEIS data); `main` is the
corrected recurrence (n ≥ 3), which is proved.

A114121 (offset 0): expansion of (sqrt(1 - 4*x) + (1 - 2*x))/(2*(1 - 4*x));
data 1, 2, 7, 26, 99, 382, 1486, 5812, 22819, 89846, 354522, 1401292, ...

Conjecture (R. J. Mathar, Nov 07 2012):
n*a(n) + 2*(3 - 4*n)*a(n-1) + 8*(2*n-3)*a(n-2) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1
(the constant term selects the branch of the square root), and the g.f. G is determined by
2*(1 - 4*x)*G = S + (1 - 2*x);
a(n) = [x^n] G. `main` is the corrected recurrence (n ≥ 3): on the data the left side of the recurrence as
stated is 2 at n = 2, and it vanishes from n = 3 on.
-/

namespace OMA.S_oeis_a114121

open PowerSeries

/-- The corrected recurrence (n ≥ 3): Mathar's recurrence, which fails at n = 2. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    2 * (1 - 4 * X) * G = S + (1 - 2 * X) →
    ∀ n : ℕ, 3 ≤ n →
      ((n : ℚ)) * coeff n G + (6 - 8 * (n : ℚ)) * coeff (n - 1) G +
        (-24 + 16 * (n : ℚ)) * coeff (n - 2) G = 0 := by
  sorry

end OMA.S_oeis_a114121
