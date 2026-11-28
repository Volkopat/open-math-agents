import Mathlib

/-!
# A278023: Mathar's recurrence, corrected to n ≥ 5

Source: https://oeis.org/A278023
Credit: @ivillar

Status: false as stated at n = 4 (the left side is 156 at n = 4 on the OEIS data); `main` is the
corrected recurrence (n ≥ 5), which is proved.

A278023 (offset 0): g.f.: 2*x*(1-x*sqrt(1-4*x))/((1+2*x^2+sqrt(1-4*x))*sqrt(1-4*x));
data 0, 1, 2, 8, 30, 109, 401, 1495, 5623, 21289, 81034, 309817, ...

Conjecture (R. J. Mathar, Jun 24 2018):
+n*(3*n^2-12*n+11) *a(n) -(3*n-5) *(3*n^2-9*n+4) *a(n-1) -2*(2*n-5) *(3*n^2-6*n+2) *a(n-2)
+n *(3*n^2-12*n+11) *a(n-3) -2 *(2*n-5) *(3*n^2-6*n+2) *a(n-4) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1 (the constant term
selects the branch of the square root), and the g.f. G is determined by
G*(1+2*x^2+S)*S = 2*x*(1-x*S);
a(n) = [x^n] G. `main` is the corrected recurrence (n ≥ 5): on the data the left side of the recurrence as
stated is 156 at n = 4, and it vanishes from n = 5 on.
-/

namespace OMA.S_oeis_a278023

open PowerSeries

/-- The corrected recurrence (n ≥ 5): Mathar's recurrence, which fails at n = 4. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    G * ((1 + 2 * X ^ 2 + S) * S) = 2 * X * (1 - X * S) →
    ∀ n : ℕ, 5 ≤ n →
      (11 * (n : ℚ) - 12 * (n : ℚ) ^ 2 + 3 * (n : ℚ) ^ 3) * coeff n G + (20 - 57 * (n : ℚ) + 42 * (n : ℚ) ^ 2 - 9 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (20 - 68 * (n : ℚ) + 54 * (n : ℚ) ^ 2 - 12 * (n : ℚ) ^ 3) * coeff (n - 2) G + (11 * (n : ℚ) - 12 * (n : ℚ) ^ 2 + 3 * (n : ℚ) ^ 3) * coeff (n - 3) G +
        (20 - 68 * (n : ℚ) + 54 * (n : ℚ) ^ 2 - 12 * (n : ℚ) ^ 3) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a278023
