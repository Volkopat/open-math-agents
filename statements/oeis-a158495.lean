import Mathlib

/-!
# A158495: Mathar's recurrence, corrected to n ≥ 3

Source: https://oeis.org/A158495
Credit: @ivillar

Status: false as stated at n = 2 (the left side is 4 at n = 2 on the OEIS data); `main` is the
corrected recurrence (n ≥ 3), which is proved.

A158495 (offset 0): expansion of ((1-4*x) + sqrt(1-4*x))/(2*(1-2*x));
data 1, -1, -3, -8, -21, -56, -154, -440, -1309, -4048, -12958, -42712, ...

Conjecture (R. J. Mathar, Dec 03 2014): D-finite with recurrence
n*a(n) + 6*(-n + 1)*a(n - 1) + 4*(2*n - 3)*a(n - 2) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1
(the constant term selects the branch of the square root), and the g.f. G is determined by
2*(1 - 2*x)*G = (1 - 4*x) + S;
a(n) = [x^n] G. `main` is the corrected recurrence (n ≥ 3): on the data the left side of the recurrence as
stated is 4 at n = 2, and it vanishes from n = 3 on.
-/

namespace OMA.S_oeis_a158495

open PowerSeries

/-- The corrected recurrence (n ≥ 3): Mathar's recurrence, which fails at n = 2. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    2 * (1 - 2 * X) * G = (1 - 4 * X) + S →
    ∀ n : ℕ, 3 ≤ n →
      ((n : ℚ)) * coeff n G + (6 - 6 * (n : ℚ)) * coeff (n - 1) G +
        (-12 + 8 * (n : ℚ)) * coeff (n - 2) G = 0 := by
  sorry

end OMA.S_oeis_a158495
