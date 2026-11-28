import Mathlib

/-!
# A239425: Mathar's recurrence, corrected to n ≥ 5

Source: https://oeis.org/A239425
Credit: @ivillar

Status: false as stated at n = 4 (the left side is -3240 at n = 4 on the OEIS data); `main` is the
corrected recurrence (n ≥ 5), which is proved.

A239425 (offset 0): expansion of -16/(sqrt(12*x+2*sqrt(1-4*x)+2)-sqrt(1-4*x)-1)^2+1/x^2-1;
data 1, 2, 7, 16, 53, 156, 522, 1702, 5833, 19990, 70079, 247160, ...

Conjecture (R. J. Mathar, Apr 02 2014):
2*(2*n+1)*(n+2)*(n+1)*a(n) +(n+1)*(n^2-27*n+2)*a(n-1) +2*(-73*n^3+204*n^2-167*n+6)*a(n-2)
+12*(n-3)*(2*n-3)*(4*n-7)*a(n-3) +216*(2*n-5)*(n-3)*(2*n-3)*a(n-4) = 0.

Formalization: T is the formal power series over ℚ with T^2 = 1-4*x and constant term 1; W is the formal power
series with W^2 = 12*x + 2*T + 2 and constant term 2, that is W = sqrt(12x + 2*sqrt(1-4x) + 2) (the
constant terms select the branches of the square roots); and G is determined by
G*x^2*(W-T-1)^2 = -16*x^2 + (1-x^2)*(W-T-1)^2, which is the stated expression multiplied by
x^2*(W-T-1)^2 (its constant term is recorded as a hypothesis);
a(n) = [x^n] G. `main` is the corrected recurrence (n ≥ 5): on the data the left side of the recurrence as
stated is -3240 at n = 4, and it vanishes from n = 5 on.
-/

namespace OMA.S_oeis_a239425

open PowerSeries

/-- The corrected recurrence (n ≥ 5): Mathar's recurrence, which fails at n = 4. -/
theorem main : ∀ T W G : ℚ⟦X⟧, T ^ 2 = 1 - 4 * X →
    coeff 0 T = 1 →
    W ^ 2 = 12 * X + 2 * T + 2 →
    coeff 0 W = 2 →
    G * (X ^ 2 * (W - T - 1) ^ 2) = -(16 * X ^ 2) + (1 - X ^ 2) * (W - T - 1) ^ 2 →
    coeff 0 G = 1 →
    ∀ n : ℕ, 5 ≤ n →
      (4 + 14 * (n : ℚ) + 14 * (n : ℚ) ^ 2 + 4 * (n : ℚ) ^ 3) * coeff n G + (2 - 25 * (n : ℚ) - 26 * (n : ℚ) ^ 2 + (n : ℚ) ^ 3) * coeff (n - 1) G +
        (12 - 334 * (n : ℚ) + 408 * (n : ℚ) ^ 2 - 146 * (n : ℚ) ^ 3) * coeff (n - 2) G + (-756 + 1188 * (n : ℚ) - 600 * (n : ℚ) ^ 2 + 96 * (n : ℚ) ^ 3) * coeff (n - 3) G +
        (-9720 + 13608 * (n : ℚ) - 6048 * (n : ℚ) ^ 2 + 864 * (n : ℚ) ^ 3) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a239425
