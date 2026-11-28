import Mathlib

/-!
# A110322: Row sums of A110321, a number triangle related to the Jacobsthal numbers.

Source: https://oeis.org/A110322
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 2, 9, 52, 425, 4206, 50737, 708464, 11350257, ...
The entry gives the exponential generating function
  exp(x)/(1-x-2*x^2)
(see the entry). It is used here as the definition: a(n) is n! times the coefficient of x^n of that series,
where exp(u) is the exponential power series evaluated at the power series u (which has no constant
term). In normalised form the series is
  ((1)*exp((x)/(1)) + (0)) / (-2*x^2 - x + 1),
which is the expression used below. Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 11 2014) reads
  Conjecture: a(n) +(-n-1)*a(n-1) -(2*n-1)*(n-1)*a(n-2) +2*(n-1)*(n-2)*a(n-3)=0
It involves a(n-3) and the offset is 0, so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a110322

open PowerSeries

/-- The exponent, a power series without constant term. -/
noncomputable def U : PowerSeries ℚ := X

/-- exp(U): the exponential series evaluated at U. -/
noncomputable def W : PowerSeries ℚ := (PowerSeries.exp ℚ).subst U

/-- A110322: n! times the coefficient of x^n in the exponential generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  (n.factorial : ℚ) * coeff n
    (((1) * W + (0)) * (1 - X - 2 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A110322. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (1) * a n + (-(n : ℚ) - 1) * a (n - 1) + (-2 * (n : ℚ) ^ 2 + 3 * (n : ℚ) - 1) * a (n - 2)
      + (2 * (n : ℚ) ^ 2 - 6 * (n : ℚ) + 4) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a110322
