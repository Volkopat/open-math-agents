import Mathlib

/-!
# A217214: Mathar's recurrence, corrected to n ≥ 5

Source: https://oeis.org/A217214
Credit: @ivillar

Status: false as stated at n = 3 and n = 4 (the left side is 3592 at n = 3, 33072 at n = 4 on the OEIS data); `main` is the
corrected recurrence (n ≥ 5), which is proved.

A217214 (offset 0): g.f. (P-Q*sqrt(1-4*x))/(x*(1-4*x)^3), where P = (1-4*x)^3*(1-x-x^2) and
Q = 1-11*x+39*x^2-40*x^3-22*x^4;
data 0, 0, 0, 2, 38, 322, 2112, 12210, 65494, 334334, 1647776, 7910916, ...

Conjecture (R. J. Mathar, Jan 25 2020): D-finite with recurrence
-(n+1)*(423*n-1718)*a(n) + (-423*n^2+4779*n+1718)*a(n-1) + (17801*n^2-84527*n+75390)*a(n-2)
- 2*(9341*n-20828)*(2*n-7)*a(n-3) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1
(the constant term selects the branch of the square root), and the g.f. G is determined by
x*(1-4*x)^3*G = (1-4*x)^3*(1-x-x^2) - (1-11*x+39*x^2-40*x^3-22*x^4)*S;
a(n) = [x^n] G. `main` is the corrected recurrence (n ≥ 5): on the data the left side of the recurrence as
stated is 3592 at n = 3, 33072 at n = 4, and it vanishes from n = 5 on.
-/

namespace OMA.S_oeis_a217214

open PowerSeries

/-- The corrected recurrence (n ≥ 5): Mathar's recurrence, which fails at n = 3 and n = 4. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    X * (1 - 4 * X) ^ 3 * G =
      (1 - 4 * X) ^ 3 * (1 - X - X ^ 2) - (1 - 11 * X + 39 * X ^ 2 - 40 * X ^ 3 - 22 * X ^ 4) * S →
    ∀ n : ℕ, 5 ≤ n →
      (1718 + 1295 * (n : ℚ) - 423 * (n : ℚ) ^ 2) * coeff n G + (1718 + 4779 * (n : ℚ) - 423 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (75390 - 84527 * (n : ℚ) + 17801 * (n : ℚ) ^ 2) * coeff (n - 2) G + (-291592 + 214086 * (n : ℚ) - 37364 * (n : ℚ) ^ 2) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a217214
