import Mathlib

/-!
# A141771: Expansion of (1-sqrt(1-4*x))/(2*x) + 8*x^3/((sqrt(1-4*x))*(1+sqrt(1-4*x))^3).

Source: https://oeis.org/A141771
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 2, 6, 19, 63, 216, 759, 2717, 9867, 36244, 134368, ...

The conjecture (R. J. Mathar, Apr 30 2016) reads
  Conjecture: (n+1)*(n^2+5*n-12)*(n^3-5*n^2+38*n-250)*a(n)
  -2*(2*n-3)*(n^2+7*n-6)*(n^3-5*n^2+38*n-250)*a(n-1)=0.
As printed it fails at n = 1 and at n = 2 (the left-hand side equals 1728 and 2232 for the terms of the
entry); it holds for the terms of the entry from n = 3 on, and it is stated here for n >= 3.

Formalization. S is the formal power series over the rationals with S^2 = 1 - 4*X and constant term 1,
that is S = sqrt(1 - 4x) (the constant term selects the branch). The generating function
G = (1 - S)/(2x) + 8x^3/(S*(1 + S)^3) is characterized by the relation obtained by clearing the
denominators, 2*X*S*(1 + S)^3*G = (1 - S)*S*(1 + S)^3 + 16*X^4; the factor 2*X*S*(1 + S)^3 is a nonzero
power series, so G is determined by this relation. a(n) is the coefficient of X^n in G.
-/

namespace OMA.S_oeis_a141771

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A141771, for n ≥ 3. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    2 * X * S * (1 + S) ^ 3 * G = (1 - S) * S * (1 + S) ^ 3 + 16 * X ^ 4 →
    ∀ n : ℕ, 3 ≤ n →
      ((n : ℚ) + 1) * ((n : ℚ) ^ 2 + 5 * (n : ℚ) - 12) * ((n : ℚ) ^ 3 - 5 * (n : ℚ) ^ 2 + 38 * (n : ℚ) - 250) * coeff n G
        - 2 * (2 * (n : ℚ) - 3) * ((n : ℚ) ^ 2 + 7 * (n : ℚ) - 6) * ((n : ℚ) ^ 3 - 5 * (n : ℚ) ^ 2 + 38 * (n : ℚ) - 250) * coeff (n - 1) G = 0 := by
  sorry

end OMA.S_oeis_a141771
