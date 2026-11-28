import Mathlib

/-!
# A102880: A Chebyshev transform of the first kind of the Catalan numbers.

Source: https://oeis.org/A102880 (conjecture by R. J. Mathar, Nov 09 2012)

`a(n)` (offset 0) is the coefficient of `x^n` in `((1-x^2)/(1+x^2)) c(x/(1+x^2))`, where `c(x)` is the
g.f. of the Catalan numbers A000108: the Chebyshev transform of the first kind maps a g.f. `g(x)` to
`((1-x^2)/(1+x^2)) g(x/(1+x^2))` (see the comments of the entry). Over `ℚ`, `c` is Mathlib's
`catalanSeries` mapped to `ℚ`, `1/(1+x^2)` is the power-series inverse `(1 + X^2)⁻¹` (its constant
term is `1`), and `c(x/(1+x^2))` is `PowerSeries.subst` (the inner series has zero constant term).

The conjecture, stated for `n >= 5`. The entry gives no range; at `n = 4`, the first index
where every term is defined, the left side is `5*8 - 14*2 + 2*0 - 6*1 - 3*1 = 3`, not `0` (data
`1, 1, 0, 2, 8`), so the identity is stated from `n = 5` on, the range on which such recurrences
from the g.f. are meant:
Conjecture: (n+1)*(n-3)*a(n) -2*(2*n-1)*(n-3)*a(n-1) +2*(1-4*n+n^2)*a(n-2) -2*(n-1)*(2*n-7)*a(n-3) +(n-1)*(n-5)*a(n-4)=0.
-/

namespace OMA.S_oeis_a102880

open PowerSeries

/-- The generating function `c(x)` of the Catalan numbers A000108 (over `ℚ`). -/
noncomputable def c : PowerSeries ℚ := PowerSeries.map (Nat.castRingHom ℚ) catalanSeries

/-- The generating function of the sequence, ((1-x^2)/(1+x^2)) c(x/(1+x^2)). -/
noncomputable def A : PowerSeries ℚ := (1 - X ^ 2) * (1 + X ^ 2)⁻¹ * c.subst (X * (1 + X ^ 2)⁻¹)

theorem main : ∀ n : ℕ, 5 ≤ n →
      (((n : ℚ)+1)*((n : ℚ)-3)) * coeff n A +
        (-2*(2*(n : ℚ)-1)*((n : ℚ)-3)) * coeff (n - 1) A +
        (2*(1-4*(n : ℚ)+(n : ℚ)^2)) * coeff (n - 2) A +
        (-2*((n : ℚ)-1)*(2*(n : ℚ)-7)) * coeff (n - 3) A +
        (((n : ℚ)-1)*((n : ℚ)-5)) * coeff (n - 4) A = 0 := by
  sorry

end OMA.S_oeis_a102880
