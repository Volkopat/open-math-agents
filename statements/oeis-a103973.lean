import Mathlib

/-!
# A103973: Mathar's recurrence

Source: https://oeis.org/A103973
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A103973 (offset 0): expansion of (sqrt(1-8*x^2)+8*x^2+2*x-1)/(2*x*sqrt(1-8*x^2));
data 1, 2, 4, 4, 24, 16, 160, 80, 1120, 448, 8064, 2688, ...

Conjecture (R. J. Mathar, Nov 09 2012): D-finite with recurrence
11*n*(n+1)*a(n) + 4*n*(4*n+1)*a(n-1) + 8*(27-11*n^2)*a(n-2) - 32*(4*n+9)*(n-3)*a(n-3) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-8*x^2 and constant term 1
(the constant term selects the branch of the square root), and the g.f. G is determined by
G*(2*x*S) = S + 8*x^2 + 2*x - 1;
a(n) = [x^n] G. The recurrence involves a(n-3), so it is stated for n ≥ 3; it is checked by the data, for
example at n = 3: (132)*(4) + (156)*(4) + (-576)*(2) + (0)*(1) = 0.
-/

namespace OMA.S_oeis_a103973

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A103973, for n ≥ 3. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 8 * X ^ 2 →
    coeff 0 S = 1 →
    G * (2 * X * S) = S + 8 * X ^ 2 + 2 * X - 1 →
    ∀ n : ℕ, 3 ≤ n →
      (11 * (n : ℚ) + 11 * (n : ℚ) ^ 2) * coeff n G + (4 * (n : ℚ) + 16 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (216 - 88 * (n : ℚ) ^ 2) * coeff (n - 2) G + (864 + 96 * (n : ℚ) - 128 * (n : ℚ) ^ 2) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a103973
