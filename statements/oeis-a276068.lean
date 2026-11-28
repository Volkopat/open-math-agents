import Mathlib

/-!
# A276068: Sum of the lengths of the first descents in all bargraphs having semiperimeter n (n>=2).

Source: https://oeis.org/A276068
Credit: @vivanpoddar

The sequence (offset 2) begins 1, 3, 9, 26, 74, 210, 598, 1715, 4963, 14504, 42808, 127553, ...
The entry gives the generating function
  g(z) = (1-z)(1-2z-z^2-Q)/(2z(1-2z)), where Q = sqrt((1-z)(1-3z-z^2-z^3)),
and its expansion z^2 + 3 z^3 + 9 z^4 + 26 z^5 + ... reproduces the data. This generating function is used
here as the definition of the sequence: a(n) is the coefficient of z^n in g(z).

The conjecture (R. J. Mathar, Jul 22 2022) reads
  Conjecture D-finite with recurrence (n+1)*a(n) +(-6*n+1)*a(n-1) +(10*n-13)*a(n-2) +(-4*n+13)*a(n-3)
  +(n-4)*a(n-4) +2*(-n+6)*a(n-5)=0.
It involves a(n-5) and the offset is 2, so it is stated for n >= 7.

Formalization. S is the formal power series over the rationals with S^2 = (1 - X)*(1 - 3*X - X^2 - X^3)
and constant term 1, that is S = Q (the constant term selects the branch). The generating function G = g is
characterized by the relation obtained by clearing the denominator,
2*X*(1 - 2*X)*G = (1 - X)*(1 - 2*X - X^2 - S); the factor 2*X*(1 - 2*X) is a nonzero power series, so G is
determined by this relation. a(n) is the coefficient of X^n in G.
-/

namespace OMA.S_oeis_a276068

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A276068, for n ≥ 7. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = (1 - X) * (1 - 3 * X - X ^ 2 - X ^ 3) →
    coeff 0 S = 1 →
    2 * X * (1 - 2 * X) * G = (1 - X) * (1 - 2 * X - X ^ 2 - S) →
    ∀ n : ℕ, 7 ≤ n →
      ((n : ℚ) + 1) * coeff n G + (-6 * (n : ℚ) + 1) * coeff (n - 1) G
        + (10 * (n : ℚ) - 13) * coeff (n - 2) G + (-4 * (n : ℚ) + 13) * coeff (n - 3) G
        + ((n : ℚ) - 4) * coeff (n - 4) G + 2 * (-(n : ℚ) + 6) * coeff (n - 5) G = 0 := by
  sorry

end OMA.S_oeis_a276068
