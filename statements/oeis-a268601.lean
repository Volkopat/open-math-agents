import Mathlib

/-!
# A268601: Expansion of 1/(2*f(x)) - 1/(4 - 2*g(x)), where f(x) = sqrt(1 - 4*x) and g(x) = sqrt(1 + 4*x).

Source: https://oeis.org/A268601
Credit: @vivanpoddar

The sequence (offset 0) begins 0, 0, 2, 8, 34, 120, 468, 1680, 6530, 23960, 93532, 348656, ...

The conjecture (R. J. Mathar, Jan 25 2020) reads
  Conjecture D-finite with recurrence: 3*n*(n-1)*a(n) -8*(n-1)*(5*n-12)*a(n-1) +4*(28*n-73)*a(n-2)
  +160*(2*n-5)*(2*n-7)*a(n-3) -192*(2*n-5)*(2*n-7)*a(n-4)=0.
It involves a(n-4) and the offset is 0, so it is stated for n >= 4 (it holds for the terms of the entry
from n = 4 on).

Formalization. F and K are the formal power series over the rationals with F^2 = 1 - 4*X, K^2 = 1 + 4*X
and constant terms 1, that is F = sqrt(1 - 4x) and K = sqrt(1 + 4x) (the constant terms select the
branches). The generating function G = 1/(2*F) - 1/(4 - 2*K) is characterized by the relation obtained by
clearing the denominators, 2*F*(4 - 2*K)*G = (4 - 2*K) - 2*F; the factor 2*F*(4 - 2*K) has constant
term 4, so G is determined by this relation. a(n) is the coefficient of X^n in G.
-/

namespace OMA.S_oeis_a268601

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A268601, for n ≥ 4. -/
theorem main : ∀ F K G : ℚ⟦X⟧, F ^ 2 = 1 - 4 * X →
    coeff 0 F = 1 →
    K ^ 2 = 1 + 4 * X →
    coeff 0 K = 1 →
    2 * F * (4 - 2 * K) * G = 4 - 2 * K - 2 * F →
    ∀ n : ℕ, 4 ≤ n →
      3 * (n : ℚ) * ((n : ℚ) - 1) * coeff n G - 8 * ((n : ℚ) - 1) * (5 * (n : ℚ) - 12) * coeff (n - 1) G
        + 4 * (28 * (n : ℚ) - 73) * coeff (n - 2) G
        + 160 * (2 * (n : ℚ) - 5) * (2 * (n : ℚ) - 7) * coeff (n - 3) G
        - 192 * (2 * (n : ℚ) - 5) * (2 * (n : ℚ) - 7) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a268601
