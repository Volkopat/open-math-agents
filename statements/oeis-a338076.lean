import Mathlib

/-!
# A338076: diagonal terms in the expansion of 1/(1-x-2*y-3*z)

Source: https://oeis.org/A338076 (conjectures by Robert Israel, Oct 25 2020)

Entry (offset 0): expand the rational function 1/(1-x-2*y-3*z) as
Sum_i Sum_j Sum_k c(i,j,k)*x^i*y^j*z^k; then a(n) = c(n,n,n).
Formula section, Conjectures from Robert Israel, Oct 25 2020:
a(n+1) = 18*(3*n+1)*(3*n+2)*a(n)/(n+1)^2.
G.f.: hypergeom([1/3, 2/3], [1], 162*x).

Formalization notes:
* The expansion is taken in the multivariate formal power series ring in the variables
  `X 0 = x`, `X 1 = y`, `X 2 = z` over `ℚ`, where `1 - x - 2*y - 3*z` (constant term 1) is
  invertible; `c(i,j,k)` is the coefficient of the monomial `x^i*y^j*z^k`, i.e. of the exponent
  vector `single 0 i + single 1 j + single 2 k`.
* The first conjecture is stated for all `n >= 0`, in `ℚ`.
* `hypergeom([1/3, 2/3], [1], 162*x)` is the Gauss hypergeometric series
  `Sum_(n >= 0) (1/3)_n (2/3)_n / ((1)_n n!) * (162*x)^n`, with `(c)_n` the rising factorial
  (`ascPochhammer`); the g.f. identity is stated as an equality of formal power series in `x`.
* Controls from the entry: a(0..3) = 1, 36, 3240, 362880.
-/

namespace OMA.S_oeis_a338076

/-- The power series expansion of 1/(1-x-2*y-3*z), with `x, y, z = X 0, X 1, X 2`. -/
noncomputable def G : MvPowerSeries (Fin 3) ℚ :=
  (1 - MvPowerSeries.X 0 - 2 * MvPowerSeries.X 1 - 3 * MvPowerSeries.X 2)⁻¹

/-- `c(i,j,k)`: the coefficient of `x^i*y^j*z^k` in the expansion. -/
noncomputable def c (i j k : ℕ) : ℚ :=
  MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 j + Finsupp.single 2 k) G

/-- A338076(n) = c(n,n,n). -/
noncomputable def a (n : ℕ) : ℚ := c n n n

/-- The rising factorial `(x)_n`. -/
noncomputable def rf (x : ℚ) (n : ℕ) : ℚ := (ascPochhammer ℚ n).eval x

/-- Israel's ratio recurrence and hypergeometric generating function. -/
theorem main :
    (∀ n : ℕ, a (n + 1) = 18 * (3 * (n : ℚ) + 1) * (3 * (n : ℚ) + 2) * a n / ((n : ℚ) + 1) ^ 2) ∧
    PowerSeries.mk a =
      PowerSeries.mk fun n => rf (1 / 3) n * rf (2 / 3) n / (rf 1 n * (n.factorial : ℚ)) * 162 ^ n := by
  sorry

end OMA.S_oeis_a338076
