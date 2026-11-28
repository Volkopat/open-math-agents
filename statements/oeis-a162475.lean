import Mathlib

/-!
# A162475: Mathar's recurrence, corrected to n ≥ 6

Source: https://oeis.org/A162475
Credit: @ivillar

Status: false as stated at n = 5 (the left side is 3 at n = 5 on the OEIS data); `main` is the
corrected recurrence (n ≥ 6), which is proved.

A162475 (offset 0): expansion of c(x/(1-x)^4), c(x) the g.f. of A000108;
data 1, 1, 6, 31, 166, 931, 5412, 32334, 197378, 1225871, 7722282, 49224175, ...

Conjecture (R. J. Mathar, Nov 17 2011):
(n+1)*a(n) +3*(2-3n)*a(n-1) +2*(7n-20)*a(n-2) +2*(22-5n)*a(n-3) +(5n-31)*a(n-4) +(8-n)*a(n-5) = 0.

Formalization: T is the formal power series over ℚ with T^2*(1-x)^4 = (1-x)^4 - 4*x and constant term 1, that is
T = sqrt(1 - 4*y) for y = x/(1-x)^4 (the constant term selects the branch of the square root). Since
y*c(y) = (1 - sqrt(1-4*y))/2 for the Catalan g.f. c, the stated g.f. G is determined by
2*x*G = (1-x)^4*(1-T);
a(n) = [x^n] G. `main` is the corrected recurrence (n ≥ 6): on the data the left side of the recurrence as
stated is 3 at n = 5, and it vanishes from n = 6 on.
-/

namespace OMA.S_oeis_a162475

open PowerSeries

/-- The corrected recurrence (n ≥ 6): Mathar's recurrence, which fails at n = 5. -/
theorem main : ∀ T G : ℚ⟦X⟧, T ^ 2 * (1 - X) ^ 4 = (1 - X) ^ 4 - 4 * X →
    coeff 0 T = 1 →
    2 * X * G = (1 - X) ^ 4 * (1 - T) →
    ∀ n : ℕ, 6 ≤ n →
      (1 + (n : ℚ)) * coeff n G + (6 - 9 * (n : ℚ)) * coeff (n - 1) G +
        (-40 + 14 * (n : ℚ)) * coeff (n - 2) G + (44 - 10 * (n : ℚ)) * coeff (n - 3) G +
        (-31 + 5 * (n : ℚ)) * coeff (n - 4) G + (8 - (n : ℚ)) * coeff (n - 5) G = 0 := by
  sorry

end OMA.S_oeis_a162475
