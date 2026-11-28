import Mathlib

/-!
# A182122: Mathar's recurrence

Source: https://oeis.org/A182122
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A182122 (offset 0): expansion of exp( arcsinh( 2*x ) );
data 1, 2, 2, 0, -2, 0, 4, 0, -10, 0, 28, 0, ...

Conjecture (R. J. Mathar, Jul 24 2012):
n*(n+1)*a(n) + (n+2)*(n-1)*a(n-1) +4*(n+1)*(n-3)*a(n-2) +4*(n+2)*(n-4)*a(n-3) = 0.

Formalization: exp(arcsinh(y)) = y + sqrt(1 + y^2), and the entry records the g.f. as 2*x + sqrt(1 + 4*x^2). So S is
the formal power series over ℚ with S^2 = 1+4*x^2 and constant term 1 (the constant term selects the
branch of the square root), and the g.f. is G = 2*x + S;
a(n) = [x^n] G. The recurrence involves a(n-3), so it is stated for n ≥ 3; it is checked by the data, for
example at n = 3: (12)*(0) + (10)*(2) + (0)*(2) + (-20)*(1) = 0.
-/

namespace OMA.S_oeis_a182122

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A182122, for n ≥ 3. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 + 4 * X ^ 2 →
    coeff 0 S = 1 →
    G = 2 * X + S →
    ∀ n : ℕ, 3 ≤ n →
      ((n : ℚ) + (n : ℚ) ^ 2) * coeff n G + (-2 + (n : ℚ) + (n : ℚ) ^ 2) * coeff (n - 1) G +
        (-12 - 8 * (n : ℚ) + 4 * (n : ℚ) ^ 2) * coeff (n - 2) G + (-32 - 8 * (n : ℚ) + 4 * (n : ℚ) ^ 2) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a182122
