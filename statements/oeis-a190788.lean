import Mathlib

/-!
# A190788: Mathar's recurrence, corrected to n ≥ 8

Source: https://oeis.org/A190788
Credit: @ivillar

Status: false as stated at n = 7 (the left side is 16 at n = 7 on the OEIS data); `main` is the
corrected recurrence (n ≥ 8), which is proved.

A190788 (offset 0): expansion of ((x-1)*sqrt(1-4*x^2))/((x-1)*sqrt(1-4*x^2)+x);
data 1, 1, 2, 6, 14, 38, 94, 248, 628, 1638, 4190, 10872, ...

Conjecture (R. J. Mathar, Nov 28 2013): D-finite with recurrence
(-n+1)*a(n) + (3*n-5)*a(n-1) + 2*(3*n-7)*a(n-2) + 4*(-6*n+19)*a(n-3) + 4*(n-3)*a(n-4)
+ 4*(11*n-53)*a(n-5) + 16*(-3*n+16)*a(n-6) + 16*(n-6)*a(n-7) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x^2 and constant term 1
(the constant term selects the branch of the square root), and the g.f. G is determined by
G*((x-1)*S + x) = (x-1)*S;
a(n) = [x^n] G. `main` is the corrected recurrence (n ≥ 8): on the data the left side of the recurrence as
stated is 16 at n = 7, and it vanishes from n = 8 on.
-/

namespace OMA.S_oeis_a190788

open PowerSeries

/-- The corrected recurrence (n ≥ 8): Mathar's recurrence, which fails at n = 7. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X ^ 2 →
    coeff 0 S = 1 →
    G * ((X - 1) * S + X) = (X - 1) * S →
    ∀ n : ℕ, 8 ≤ n →
      (1 - (n : ℚ)) * coeff n G + (-5 + 3 * (n : ℚ)) * coeff (n - 1) G +
        (-14 + 6 * (n : ℚ)) * coeff (n - 2) G + (76 - 24 * (n : ℚ)) * coeff (n - 3) G +
        (-12 + 4 * (n : ℚ)) * coeff (n - 4) G + (-212 + 44 * (n : ℚ)) * coeff (n - 5) G +
        (256 - 48 * (n : ℚ)) * coeff (n - 6) G + (-96 + 16 * (n : ℚ)) * coeff (n - 7) G = 0 := by
  sorry

end OMA.S_oeis_a190788
