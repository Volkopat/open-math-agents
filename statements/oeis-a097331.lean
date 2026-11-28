import Mathlib

/-!
# A097331: Mathar's recurrence

Source: https://oeis.org/A097331
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A097331 (offset 0): expansion of 1 + 2x/(1 + sqrt(1 - 4x^2));
data 1, 1, 0, 1, 0, 2, 0, 5, 0, 14, 0, 42, ...

Conjecture (R. J. Mathar, Dec 02 2012):
(n+1)*a(n) + n*a(n-1) + 4*(-n+2)*a(n-2) + 4*(-n+3)*a(n-3) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x^2 and constant term 1
(the constant term selects the branch of the square root), and the g.f. G is determined by
(G - 1)*(1 + S) = 2*x;
a(n) = [x^n] G. The recurrence involves a(n-3), so it is stated for n ≥ 3; it is checked by the data, for
example at n = 3: (4)*(1) + (3)*(0) + (-4)*(1) + (0)*(1) = 0.
-/

namespace OMA.S_oeis_a097331

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A097331, for n ≥ 3. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X ^ 2 →
    coeff 0 S = 1 →
    (G - 1) * (1 + S) = 2 * X →
    ∀ n : ℕ, 3 ≤ n →
      (1 + (n : ℚ)) * coeff n G + ((n : ℚ)) * coeff (n - 1) G +
        (8 - 4 * (n : ℚ)) * coeff (n - 2) G + (12 - 4 * (n : ℚ)) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a097331
