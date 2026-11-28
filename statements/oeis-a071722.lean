import Mathlib

/-!
# A071722: Expansion of (1+x^2*C^2)*C^3, where C is the g.f. for Catalan numbers

Source: https://oeis.org/A071722
Credit: @jagong-cmu

Here C = (1-(1-4*x)^(1/2))/(2*x) is the g.f. for the Catalan numbers A000108.
The sequence (offset 0) starts 1, 3, 10, 33, 110, 372, 1276, ...

Conjecture (R. J. Mathar, 2013):
2*(n+3)*a(n) + 4*(-3*n-4)*a(n-1) + (17*n-9)*a(n-2) + 2*(-2*n+5)*a(n-3) = 0.

Conventions:
* `catGF` is the power series C = `Sum_{n ≥ 0} catalan(n) x^n` in `PowerSeries ℤ`; this is
  the series expansion of `(1-(1-4x)^(1/2))/(2x)`. `a n` is the coefficient of `x^n` in
  `(1 + x^2 C^2) C^3` with `C = catGF`.
* The recurrence is stated in `ℤ` for `n ≥ 3`, where `a(n)`, ..., `a(n-3)` are all terms of the
  sequence (offset 0), so the truncated subtractions are exact. (With the convention that terms
  of negative index are 0, the recurrence fails at n = 0, 1, 2, so n ≥ 3 is the intended range.)
-/

namespace OMA.S_oeis_a071722

/-- The g.f. `catGF(x) = Sum_{n ≥ 0} catalan(n) x^n` of A000108. -/
def catGF : PowerSeries ℤ := PowerSeries.mk fun n => (catalan n : ℤ)

/-- A071722: the coefficient of `x^n` in `(1 + x^2 catGF^2) catGF^3`. -/
noncomputable def a (n : ℕ) : ℤ :=
  PowerSeries.coeff n ((1 + PowerSeries.X ^ 2 * catGF ^ 2) * catGF ^ 3)

/-- Mathar's conjectured recurrence, for `n ≥ 3`. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    2 * ((n : ℤ) + 3) * a n + 4 * (-3 * (n : ℤ) - 4) * a (n - 1) +
      (17 * (n : ℤ) - 9) * a (n - 2) + 2 * (-2 * (n : ℤ) + 5) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a071722
