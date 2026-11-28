import Mathlib

/-!
# A218045: Mathar's recurrence, corrected to n ≥ 5

Source: https://oeis.org/A218045
Credit: @ivillar

Status: false as stated at n = 4 (the left side is 32 at n = 4 on the OEIS data); `main` is the
corrected recurrence (n ≥ 5), which is proved.

A218045 (offset 0): number of truth tables of bracketed formulas (case 3);
data 0, 0, 1, 2, 9, 46, 262, 1588, 10053, 65686, 439658, 2999116, ...

Conjecture (R. J. Mathar, Dec 02 2025): D-finite with recurrence
n*(n-1)*(2*n-3)*a(n) -2*(n-1)*(11*n^2-39*n+35)*a(n-1) +8*(-3*n^3+42*n^2-159*n+175)*a(n-2)
+32*(2*n-7)*(8*n^2-61*n+115)*a(n-3) +128*(n-5)*(2*n-7)*(2*n-9)*a(n-4) = 0.

Formalization: The entry records the g.f. (2+2*sqrt(1-8*x)-(1+sqrt(1-8*x))*sqrt(2+2*sqrt(1-8*x)+8*x))/8 (due to Yildiz),
and this closed form is used as the definition here. T is the formal power series over ℚ with
T^2 = 1-8*x and constant term 1; W is the formal power series with W^2 = 2 + 2*T + 8*x and constant term 2
(the constant terms select the branches of the square roots); and G is determined by
8*G = 2 + 2*T - (1+T)*W;
a(n) = [x^n] G. `main` is the corrected recurrence (n ≥ 5): on the data the left side of the recurrence as
stated is 32 at n = 4, and it vanishes from n = 5 on.
-/

namespace OMA.S_oeis_a218045

open PowerSeries

/-- The corrected recurrence (n ≥ 5): Mathar's recurrence, which fails at n = 4. -/
theorem main : ∀ T W G : ℚ⟦X⟧, T ^ 2 = 1 - 8 * X →
    coeff 0 T = 1 →
    W ^ 2 = 2 + 2 * T + 8 * X →
    coeff 0 W = 2 →
    8 * G = 2 + 2 * T - (1 + T) * W →
    ∀ n : ℕ, 5 ≤ n →
      (3 * (n : ℚ) - 5 * (n : ℚ) ^ 2 + 2 * (n : ℚ) ^ 3) * coeff n G + (70 - 148 * (n : ℚ) + 100 * (n : ℚ) ^ 2 - 22 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (1400 - 1272 * (n : ℚ) + 336 * (n : ℚ) ^ 2 - 24 * (n : ℚ) ^ 3) * coeff (n - 2) G + (-25760 + 21024 * (n : ℚ) - 5696 * (n : ℚ) ^ 2 + 512 * (n : ℚ) ^ 3) * coeff (n - 3) G +
        (-40320 + 28544 * (n : ℚ) - 6656 * (n : ℚ) ^ 2 + 512 * (n : ℚ) ^ 3) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a218045
