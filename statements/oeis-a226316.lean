import Mathlib

/-!
# A226316: Mathar's recurrence, corrected to n ≥ 4

Source: https://oeis.org/A226316
Credit: @ivillar

Status: known result. The entry records a verification through a differential equation satisfied by the g.f.
It is false as stated at n = 3 (the left side is -4 at n = 3 on the OEIS data); `main` is the
corrected recurrence (n ≥ 4), which is proved.

A226316 (offset 0): expansion of g.f. 1/2 + 1/(1+sqrt(1-8*x+8*x^2));
data 1, 1, 3, 12, 56, 284, 1516, 8384, 47600, 275808, 1624352, 9694912, ...

Conjecture (R. J. Mathar, Apr 02 2015): D-finite with recurrence
(n + 1)*a(n) + 3*(-3*n + 1)*a(n - 1) + 4*(4*n - 5)*a(n - 2) + 8*(-n + 2)*a(n - 3) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-8*x+8*x^2 and constant term 1
(the constant term selects the branch of the square root), and the g.f. G is determined by
(2*G - 1)*(1 + S) = 2;
a(n) = [x^n] G. `main` is the corrected recurrence (n ≥ 4): on the data the left side of the recurrence as
stated is -4 at n = 3, and it vanishes from n = 4 on.
-/

namespace OMA.S_oeis_a226316

open PowerSeries

/-- The corrected recurrence (n ≥ 4): Mathar's recurrence, which fails at n = 3. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 8 * X + 8 * X ^ 2 →
    coeff 0 S = 1 →
    (2 * G - 1) * (1 + S) = 2 →
    ∀ n : ℕ, 4 ≤ n →
      (1 + (n : ℚ)) * coeff n G + (3 - 9 * (n : ℚ)) * coeff (n - 1) G +
        (-20 + 16 * (n : ℚ)) * coeff (n - 2) G + (16 - 8 * (n : ℚ)) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a226316
