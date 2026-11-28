import Mathlib

/-!
# A192753: Coefficient of x in the reduction by x^2->x+1 of the polynomial p(n,x) defined below in Comments.

Source: https://oeis.org/A192753
Credit: @JeremyDevs

Formalizes the generating function conjectured in OEIS A192753 (R. J. Mathar, May 04 2014):
G.f.: x*(-1-5*x+2*x^2) / ( (x^2+x-1)*(x-1)^2 ).

Conventions:
* The titular polynomial is defined recursively (COMMENTS section of the entry) by
  p(n,x) = x*p(n-1,x) + 4*n+3 for n > 0, where p(0,x) = 1; it is `p n` below, in `ℤ[X]`,
  with the recursion written with `n + 1` in place of `n`.
* The reduction of a polynomial by x^2 -> x+1 (see A192232) replaces x^2 by x+1 repeatedly until
  a polynomial of degree at most 1 is left; this is the remainder of the polynomial modulo
  x^2 - x - 1, here `p n %ₘ (X ^ 2 - X - 1)`. Its coefficient of x is its coefficient of index 1.
* The sequence has offset 0 and a(n) is the coefficient of x in the reduction of p(n,x)
  (data 0, 1, 8, 20, 43, 82, ...; for instance p(1,x) = x + 7 -> 7 + x, p(2,x) = x^2 + 7x + 11 -> 12 + 8x).
* The ordinary generating function is the formal power series `∑ a(n) x^n`, here
  `PowerSeries.mk a` in `PowerSeries ℤ`. "G.f. = N(x)/D(x)" is stated without division, as
  `G.f. * D(x) = N(x)` with D(x) = (x^2+x-1)*(x-1)^2, which is the same assertion (D has constant
  term -1, so it is invertible as a power series). The remark "with first differences in A192752" of the same comment is not stated.
-/

namespace OMA.S_oeis_a192753

open Polynomial

/-- p(0,x) = 1, p(n,x) = x*p(n-1,x) + 4*n+3. -/
noncomputable def p : ℕ → ℤ[X]
  | 0 => 1
  | n + 1 => X * p n + C (4 * ((n : ℤ) + 1) + 3)

/-- A192753 (offset 0): the coefficient of x in the reduction of p(n,x) by x^2 -> x+1. -/
noncomputable def a (n : ℕ) : ℤ := (p n %ₘ (X ^ 2 - X - 1)).coeff 1

/-- The generating function of A192753 is x*(-1-5*x+2*x^2) / ( (x^2+x-1)*(x-1)^2 ). -/
theorem main :
    PowerSeries.mk a * ((PowerSeries.X ^ 2 + PowerSeries.X - 1) * (PowerSeries.X - 1) ^ 2)
      = (PowerSeries.X : PowerSeries ℤ) * (-1 - 5 * PowerSeries.X + 2 * PowerSeries.X ^ 2) := by
  sorry

end OMA.S_oeis_a192753
