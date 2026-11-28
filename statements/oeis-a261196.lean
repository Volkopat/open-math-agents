import Mathlib

/-!
# A261196: Mathar's recurrence

Source: https://oeis.org/A261196
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A261196 (offset 0): expansion of sqrt(8*x + sqrt(1 + 64*x^2));
data 1, 4, 8, -32, -160, 896, 5376, -33792, -219648, 1464320, 9957376, -68796416, ...

Conjecture (R. J. Mathar, Jun 07 2016): D-finite with recurrence
n*(n-1)*a(n) +(n-1)*(n-2)*a(n-1) +16*(2*n-3)*(2*n-5)*a(n-2) +16*(2*n-5)*(2*n-7)*a(n-3) = 0.

Formalization: T is the formal power series over ℚ with T^2 = 1+64*x^2 and constant term 1, and G is the formal
power series with G^2 = 8*x + T and constant term 1, that is G = sqrt(8x + sqrt(1+64x^2)) (the
constant terms select the branches of the square roots);
a(n) = [x^n] G. The recurrence involves a(n-3), so it is stated for n ≥ 3; it is checked by the data, for
example at n = 3: (6)*(-32) + (2)*(8) + (48)*(4) + (-16)*(1) = 0.
-/

namespace OMA.S_oeis_a261196

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A261196, for n ≥ 3. -/
theorem main : ∀ T G : ℚ⟦X⟧, T ^ 2 = 1 + 64 * X ^ 2 →
    coeff 0 T = 1 →
    G ^ 2 = 8 * X + T →
    coeff 0 G = 1 →
    ∀ n : ℕ, 3 ≤ n →
      (-(n : ℚ) + (n : ℚ) ^ 2) * coeff n G + (2 - 3 * (n : ℚ) + (n : ℚ) ^ 2) * coeff (n - 1) G +
        (240 - 256 * (n : ℚ) + 64 * (n : ℚ) ^ 2) * coeff (n - 2) G + (560 - 384 * (n : ℚ) + 64 * (n : ℚ) ^ 2) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a261196
