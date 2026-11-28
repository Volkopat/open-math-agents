import Mathlib

/-!
# A113956: Mathar's recurrence

Source: https://oeis.org/A113956
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A113956 (offset 0): expansion of (1/((1-4x)c(x)))/(1-x^2c(x)/sqrt(1-4x)), c(x) the g.f. of A000108;
data 1, 3, 12, 48, 194, 787, 3199, 13017, 52997, 215831, 879076, 3580511, ...

Conjecture (R. J. Mathar, Jan 24 2020): D-finite with recurrence
n*a(n) + 2*(-5*n+4)*a(n-1) + (27*n-46)*a(n-2) + (5*n-2)*a(n-3) + (-57*n+188)*a(n-4)
+ 2*(-21*n+83)*a(n-5) + 4*(-2*n+9)*a(n-6) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1, that is
S = sqrt(1-4x) (the constant term selects the branch of the square root); c is the Catalan g.f.,
determined by 2*x*c = 1 - S; and the g.f. G is determined by G*(1-4*x)*c*(S - x^2*c) = S, which is
the stated expression with numerator and denominator multiplied by S;
a(n) = [x^n] G. The recurrence involves a(n-6), so it is stated for n ≥ 6; it is checked by the data, for
example at n = 6: (6)*(3199) + (-52)*(787) + (116)*(194) + (28)*(48) + (-154)*(12) + (-86)*(3) + (-12)*(1) = 0.
-/

namespace OMA.S_oeis_a113956

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A113956, for n ≥ 6. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    2 * X * c = 1 - S →
    G * ((1 - 4 * X) * c * (S - X ^ 2 * c)) = S →
    ∀ n : ℕ, 6 ≤ n →
      ((n : ℚ)) * coeff n G + (8 - 10 * (n : ℚ)) * coeff (n - 1) G +
        (-46 + 27 * (n : ℚ)) * coeff (n - 2) G + (-2 + 5 * (n : ℚ)) * coeff (n - 3) G +
        (188 - 57 * (n : ℚ)) * coeff (n - 4) G + (166 - 42 * (n : ℚ)) * coeff (n - 5) G +
        (36 - 8 * (n : ℚ)) * coeff (n - 6) G = 0 := by
  sorry

end OMA.S_oeis_a113956
