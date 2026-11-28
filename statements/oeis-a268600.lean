import Mathlib

/-!
# A268600: Mathar's recurrence

Source: https://oeis.org/A268600
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A268600 (offset 0): expansion of 1/(2*f(x)) + 1/(4 - 2*g(x)), where f(x) = sqrt(1 - 4*x) and g(x) = sqrt(1 + 4*x);
data 1, 2, 4, 12, 36, 132, 456, 1752, 6340, 24660, 91224, 356776, ...

Conjecture (R. J. Mathar, Jan 25 2020): D-finite with recurrence
-3*n*(n-1)*a(n) +8*(n-1)*(5*n-12)*a(n-1) +4*(-28*n+73)*a(n-2) -160*(2*n-5)*(2*n-7)*a(n-3)
+192*(2*n-5)*(2*n-7)*a(n-4) = 0.

Formalization: T and W are the formal power series over ℚ with T^2 = 1-4*x, W^2 = 1+4*x and constant terms 1, that
is T = f(x) = sqrt(1-4x) and W = g(x) = sqrt(1+4x) (the constant terms select the branches of the square
roots); and G is determined by G*(2*T*(4 - 2*W)) = (4 - 2*W) + 2*T, which is the stated
expression multiplied by 2*T*(4 - 2*W) (its constant term is recorded as a hypothesis);
a(n) = [x^n] G. The recurrence involves a(n-4), so it is stated for n ≥ 4; it is checked by the data, for
example at n = 4: (-36)*(36) + (192)*(12) + (-156)*(4) + (-480)*(2) + (576)*(1) = 0.
-/

namespace OMA.S_oeis_a268600

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A268600, for n ≥ 4. -/
theorem main : ∀ T W G : ℚ⟦X⟧, T ^ 2 = 1 - 4 * X →
    coeff 0 T = 1 →
    W ^ 2 = 1 + 4 * X →
    coeff 0 W = 1 →
    G * (2 * T * (4 - 2 * W)) = (4 - 2 * W) + 2 * T →
    coeff 0 G = 1 →
    ∀ n : ℕ, 4 ≤ n →
      (3 * (n : ℚ) - 3 * (n : ℚ) ^ 2) * coeff n G + (96 - 136 * (n : ℚ) + 40 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (292 - 112 * (n : ℚ)) * coeff (n - 2) G + (-5600 + 3840 * (n : ℚ) - 640 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (6720 - 4608 * (n : ℚ) + 768 * (n : ℚ) ^ 2) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a268600
