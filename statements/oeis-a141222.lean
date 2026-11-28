import Mathlib

/-!
# A141222: Mathar's recurrence

Source: https://oeis.org/A141222
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A141222 (offset 0): expansion of -1/(2*x) + (2*x-1)^2/(2*x*(1-4x)^(3/2));
data 1, 5, 22, 95, 406, 1722, 7260, 30459, 127270, 529958, 2200276, 9111830, ...

Conjecture (R. J. Mathar, Nov 24 2012):
(n+1)*a(n) + 2*(-3*n-1)*a(n-1) + 4*(2*n-3)*a(n-2) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1 (the constant term
selects the branch of the square root), so that (1-4x)^(3/2) = (1-4*x)*S, and the g.f. G is determined
by G*(2*x*(1-4*x)*S) = (2*x-1)^2 - (1-4*x)*S, which is the stated expression multiplied by
2*x*(1-4*x)*S;
a(n) = [x^n] G. The recurrence involves a(n-2), so it is stated for n ≥ 2; it is checked by the data, for
example at n = 2: (3)*(22) + (-14)*(5) + (4)*(1) = 0.
-/

namespace OMA.S_oeis_a141222

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A141222, for n ≥ 2. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    G * (2 * X * ((1 - 4 * X) * S)) = (2 * X - 1) ^ 2 - (1 - 4 * X) * S →
    ∀ n : ℕ, 2 ≤ n →
      (1 + (n : ℚ)) * coeff n G + (-2 - 6 * (n : ℚ)) * coeff (n - 1) G +
        (-12 + 8 * (n : ℚ)) * coeff (n - 2) G = 0 := by
  sorry

end OMA.S_oeis_a141222
