import Mathlib

/-!
# A115967: Mathar's recurrence

Source: https://oeis.org/A115967
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A115967 (offset 0): expansion of 1/(2*sqrt(1-2*x-3*x^2) - 1);
data 1, 2, 8, 28, 104, 384, 1428, 5316, 19820, 73948, 276044, 1030796, ...

Conjecture (R. J. Mathar, Nov 15 2012): D-finite with recurrence
3*n*a(n) + (-14*n + 9)*a(n - 1) + (-5*n + 3)*a(n - 2) + 12*(4*n - 9)* a(n - 3) + 36*(n - 3)*a(n -
4) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-2*x-3*x^2 and constant term 1
(the constant term selects the branch of the square root), and the g.f. G is determined by
G*(2*S - 1) = 1;
a(n) = [x^n] G. The recurrence involves a(n-4), so it is stated for n ≥ 4; it is checked by the data, for
example at n = 4: (12)*(104) + (-47)*(28) + (-17)*(8) + (84)*(2) + (36)*(1) = 0.
-/

namespace OMA.S_oeis_a115967

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A115967, for n ≥ 4. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 2 * X - 3 * X ^ 2 →
    coeff 0 S = 1 →
    G * (2 * S - 1) = 1 →
    ∀ n : ℕ, 4 ≤ n →
      (3 * (n : ℚ)) * coeff n G + (9 - 14 * (n : ℚ)) * coeff (n - 1) G +
        (3 - 5 * (n : ℚ)) * coeff (n - 2) G + (-108 + 48 * (n : ℚ)) * coeff (n - 3) G +
        (-108 + 36 * (n : ℚ)) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a115967
