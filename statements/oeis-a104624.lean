import Mathlib

/-!
# A104624: Mathar's recurrence

Source: https://oeis.org/A104624
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A104624 (offset 0): expansion of exp( arcsinh( -2*x ) ) in powers of x;
data 1, -2, 2, 0, -2, 0, 4, 0, -10, 0, 28, 0, ...

Conjecture (R. J. Mathar, Nov 15 2012):
n*a(n) + (n-1)*a(n-1) + 4*(n-3)*a(n-2) + 4*(n-4)*a(n-3) = 0.

Formalization: exp(arcsinh(y)) = y + sqrt(1 + y^2), and the entry records the g.f. as sqrt(1 + 4*x^2) - 2*x. So S is
the formal power series over ℚ with S^2 = 1+4*x^2 and constant term 1 (the constant term selects the
branch of the square root), and the g.f. is G = S - 2*x;
a(n) = [x^n] G. The recurrence involves a(n-3), so it is stated for n ≥ 3; it is checked by the data, for
example at n = 3: (3)*(0) + (2)*(2) + (0)*(-2) + (-4)*(1) = 0.
-/

namespace OMA.S_oeis_a104624

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A104624, for n ≥ 3. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 + 4 * X ^ 2 →
    coeff 0 S = 1 →
    G = S - 2 * X →
    ∀ n : ℕ, 3 ≤ n →
      ((n : ℚ)) * coeff n G + (-1 + (n : ℚ)) * coeff (n - 1) G +
        (-12 + 4 * (n : ℚ)) * coeff (n - 2) G + (-16 + 4 * (n : ℚ)) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a104624
