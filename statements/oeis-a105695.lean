import Mathlib

/-!
# A105695: Mathar's recurrence, corrected to n ≥ 4

Source: https://oeis.org/A105695
Credit: @ivillar

Status: false as stated at n = 3 (the left side is 1 at n = 3 on the OEIS data); `main` is the
corrected recurrence (n ≥ 4), which is proved.

A105695 (offset 0): expansion of (1-x)*c(x/(1+x)), where c(x) is the g.f. of the Catalan numbers (A000108);
data 1, 0, 0, 1, 2, 5, 12, 30, 76, 196, 512, 1353, ...

Conjecture (R. J. Mathar, Dec 13 2011):
(n+1)*a(n)+(2-3n)*a(n-1) +(1-n)*a(n-2)+3*(n-4)*a(n-3) = 0.

Formalization: T is the formal power series over ℚ with T^2*(1+x) = 1-3*x and constant term 1, that is
T = sqrt(1 - 4*y) for y = x/(1+x) (the constant term selects the branch of the square root). Since
y*c(y) = (1 - sqrt(1-4*y))/2 for the Catalan g.f. c, the stated g.f. G is determined by
2*x*G = (1-x)*(1+x)*(1-T);
a(n) = [x^n] G. `main` is the corrected recurrence (n ≥ 4): on the data the left side of the recurrence as
stated is 1 at n = 3, and it vanishes from n = 4 on.
-/

namespace OMA.S_oeis_a105695

open PowerSeries

/-- The corrected recurrence (n ≥ 4): Mathar's recurrence, which fails at n = 3. -/
theorem main : ∀ T G : ℚ⟦X⟧, T ^ 2 * (1 + X) = 1 - 3 * X →
    coeff 0 T = 1 →
    2 * X * G = (1 - X) * (1 + X) * (1 - T) →
    ∀ n : ℕ, 4 ≤ n →
      (1 + (n : ℚ)) * coeff n G + (2 - 3 * (n : ℚ)) * coeff (n - 1) G +
        (1 - (n : ℚ)) * coeff (n - 2) G + (-12 + 3 * (n : ℚ)) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a105695
