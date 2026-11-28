import Mathlib

/-!
# A101478: Mathar's recurrence, corrected to n ≥ 4

Source: https://oeis.org/A101478
Credit: @ivillar

Status: false as stated at n = 3 (the left side is 48 at n = 3 on the OEIS data); `main` is the
corrected recurrence (n ≥ 4), which is proved.

A101478 (offset 0): g.f. satisfies A(x) = x*(1+A(x))^4/(1+A(x)^2);
data 0, 1, 4, 21, 124, 782, 5144, 34845, 241196, 1697498, 12104872, 87246770, ...

Conjecture (R. J. Mathar, Nov 10 2013):
n*(n-1)*(n+1)*a(n) -12*n*(n-1)*(2*n-3)*a(n-1) +12*(n-1)*(16*n^2-64*n+65)*a(n-2)
-16*(2*n-5)*(4*n-9)*(4*n-11)*a(n-3) = 0.

Formalization: G is the formal power series over ℚ with zero constant term and G*(1+G^2) = x*(1+G)^4, which is
the stated equation A = x*(1+A)^4/(1+A^2) multiplied by 1+A^2;
a(n) = [x^n] G. `main` is the corrected recurrence (n ≥ 4): on the data the left side of the recurrence as
stated is 48 at n = 3, and it vanishes from n = 4 on.
-/

namespace OMA.S_oeis_a101478

open PowerSeries

/-- The corrected recurrence (n ≥ 4): Mathar's recurrence, which fails at n = 3. -/
theorem main : ∀ G : ℚ⟦X⟧, coeff 0 G = 0 →
    G * (1 + G ^ 2) = X * (1 + G) ^ 4 →
    ∀ n : ℕ, 4 ≤ n →
      (-(n : ℚ) + (n : ℚ) ^ 3) * coeff n G + (-36 * (n : ℚ) + 60 * (n : ℚ) ^ 2 - 24 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (-780 + 1548 * (n : ℚ) - 960 * (n : ℚ) ^ 2 + 192 * (n : ℚ) ^ 3) * coeff (n - 2) G + (7920 - 9568 * (n : ℚ) + 3840 * (n : ℚ) ^ 2 - 512 * (n : ℚ) ^ 3) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a101478
