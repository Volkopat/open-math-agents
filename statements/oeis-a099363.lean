import Mathlib

/-!
# A099363: An inverse Chebyshev transform of 1-x.

Source: https://oeis.org/A099363 (conjecture by R. J. Mathar, Nov 26 2012)

`a(n)` (offset 0) is the coefficient of `x^n` in the generating function
`(1-(1-x)c(x^2))/x` given in the entry, where `c(x)` is the generating function of the
Catalan numbers A000108. Here `c(x^2)` is Mathlib's `catalanSeries` (cast to `ℚ`) with
`X ^ 2` substituted for `X`, and dividing by `x` is expressed by taking the coefficient of
`x^(n+1)` in `1 - (1 - x) * c(x^2)` (whose constant term is `0`). The terms are integers;
they are computed in `ℚ`.

The conjecture, stated for `n >= 3` (the first `n` where every index is defined):
Conjecture: (n+3)*a(n) +(-n-1)*a(n-1) -4*n*a(n-2) +4*(n-2)*a(n-3)=0.
-/

namespace OMA.S_oeis_a099363

open PowerSeries

/-- `c(x^2)`, the Catalan generating function evaluated at `x^2`. -/
noncomputable def c2 : PowerSeries ℚ :=
  (catalanSeries.map (Nat.castRingHom ℚ)).subst ((X : PowerSeries ℚ) ^ 2)

/-- `a(n) = [x^n] (1 - (1 - x) c(x^2)) / x`. -/
noncomputable def a (n : ℕ) : ℚ := coeff (n + 1) (1 - (1 - X) * c2)

theorem main : ∀ n : ℕ, 3 ≤ n →
      ((n : ℚ) + 3) * a n + (-(n : ℚ) - 1) * a (n - 1) + (-4 * (n : ℚ)) * a (n - 2) +
        (4 * ((n : ℚ) - 2)) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a099363
