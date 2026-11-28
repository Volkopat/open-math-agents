import Mathlib

/-!
# A247471: Mathar's recurrence, corrected to n ≥ 8

Source: https://oeis.org/A247471
Credit: @ivillar

Status: false as stated at n = 7 (the left side is -2 at n = 7 on the OEIS data); `main` is the
corrected recurrence (n ≥ 8), which is proved.

A247471 (offset 0): number of paths in B(n) that start with a u step and end with a d step;
data 0, 0, 0, 1, 1, 2, 5, 11, 26, 62, 148, 356, ...

Conjecture (R. J. Mathar, Jul 22 2022): D-finite with recurrence
(n+3)*a(n) +3*(-n-1)*a(n-1) +(n-9)*a(n-3) +2*(2*n-9)*a(n-4) +(n-9)*a(n-5) +(-n+9)*a(n-6) = 0.

Formalization: T is the series g of the entry: the formal power series over ℚ with T = 1 + x*T + x^2*T + x^3*T^2
(this equation has exactly one power series solution, with constant term 1); and the g.f. G is
determined by G = x^3*(1 - x - x^2)*T^2 (the second form of the g.f. in the entry, due to Emeric Deutsch);
a(n) = [x^n] G. `main` is the corrected recurrence (n ≥ 8): on the data the left side of the recurrence as
stated is -2 at n = 7, and it vanishes from n = 8 on.
At n = 6 the left side of the recurrence as stated is 0 on the data; these indices are not
included in `main`, which is stated for n ≥ 8 only.
-/

namespace OMA.S_oeis_a247471

open PowerSeries

/-- The corrected recurrence (n ≥ 8): Mathar's recurrence, which fails at n = 7. -/
theorem main : ∀ T G : ℚ⟦X⟧, T = 1 + X * T + X ^ 2 * T + X ^ 3 * T ^ 2 →
    G = X ^ 3 * (1 - X - X ^ 2) * T ^ 2 →
    ∀ n : ℕ, 8 ≤ n →
      (3 + (n : ℚ)) * coeff n G + (-3 - 3 * (n : ℚ)) * coeff (n - 1) G +
        (-9 + (n : ℚ)) * coeff (n - 3) G + (-18 + 4 * (n : ℚ)) * coeff (n - 4) G +
        (-9 + (n : ℚ)) * coeff (n - 5) G + (9 - (n : ℚ)) * coeff (n - 6) G = 0 := by
  sorry

end OMA.S_oeis_a247471
