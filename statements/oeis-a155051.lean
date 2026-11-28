import Mathlib

/-!
# A155051: Mathar's recurrence

Source: https://oeis.org/A155051
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A155051 (offset 0): expansion of c(x^2)*(1+x)/(1-x), c(x) the g.f. of A000108;
data 1, 2, 3, 4, 6, 8, 13, 18, 32, 46, 88, 130, ...

Conjecture (R. J. Mathar, Feb 05 2015):
-(n+2)*(n-3)*a(n) +(n^2-n-10)*a(n-1) +4*(n^2-4*n+5)*a(n-2) -4*(n-2)^2*a(n-3) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x^2 and constant term 1 (the constant term
selects the branch of the square root), so that c(x^2) = (1-S)/(2*x^2) for the Catalan g.f. c, and
the g.f. G = c(x^2)*(1+x)/(1-x) is determined by 2*x^2*(1-x)*G = (1+x)*(1-S);
a(n) = [x^n] G. The recurrence involves a(n-3), so it is stated for n ≥ 3; it is checked by the data, for
example at n = 3: (0)*(4) + (-4)*(3) + (8)*(2) + (-4)*(1) = 0.
-/

namespace OMA.S_oeis_a155051

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A155051, for n ≥ 3. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X ^ 2 →
    coeff 0 S = 1 →
    2 * X ^ 2 * (1 - X) * G = (1 + X) * (1 - S) →
    ∀ n : ℕ, 3 ≤ n →
      (6 + (n : ℚ) - (n : ℚ) ^ 2) * coeff n G + (-10 - (n : ℚ) + (n : ℚ) ^ 2) * coeff (n - 1) G +
        (20 - 16 * (n : ℚ) + 4 * (n : ℚ) ^ 2) * coeff (n - 2) G + (-16 + 16 * (n : ℚ) - 4 * (n : ℚ) ^ 2) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a155051
