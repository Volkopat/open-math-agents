import Mathlib

/-!
# A192755: Coefficient of x in the reduction by x^2->x+1 of the polynomial p(n,x) defined below in Comments.

Source: https://oeis.org/A192755
Credit: @JeremyDevs

Formalizes the generating function conjectured in OEIS A192755 (R. J. Mathar, May 04 2014):
G.f.: -x*(1+4*x) / ( (x^2+x-1)*(x-1)^2 ).

Conventions:
* The titular polynomial is defined recursively (COMMENTS section of the entry) by
  p(n,x) = x*p(n-1,x) + 5*n+1 for n > 0, where p(0,x) = 1; it is `p n` below, in `ℤ[X]`,
  with the recursion written with `n + 1` in place of `n`.
* The reduction of a polynomial by x^2 -> x+1 (see A192232) replaces x^2 by x+1 repeatedly until
  a polynomial of degree at most 1 is left; this is the remainder of the polynomial modulo
  x^2 - x - 1, here `p n %ₘ (X ^ 2 - X - 1)`. Its coefficient of x is its coefficient of index 1.
* The sequence has offset 0 and a(n) is the coefficient of x in the reduction of p(n,x)
  (data 0, 1, 7, 19, 42, 82, ...; for instance p(1,x) = x + 6 -> 6 + x, p(2,x) = x^2 + 6x + 11 -> 12 + 7x).
* The ordinary generating function is the formal power series `∑ a(n) x^n`, here
  `PowerSeries.mk a` in `PowerSeries ℤ`. "G.f. = N(x)/D(x)" is stated without division, as
  `G.f. * D(x) = N(x)` with D(x) = (x^2+x-1)*(x-1)^2, which is the same assertion (D has constant
  term -1, so it is invertible as a power series).
-/

namespace OMA.S_oeis_a192755

open Polynomial

/-- p(0,x) = 1, p(n,x) = x*p(n-1,x) + 5*n+1. -/
noncomputable def p : ℕ → ℤ[X]
  | 0 => 1
  | n + 1 => X * p n + C (5 * ((n : ℤ) + 1) + 1)

/-- A192755 (offset 0): the coefficient of x in the reduction of p(n,x) by x^2 -> x+1. -/
noncomputable def a (n : ℕ) : ℤ := (p n %ₘ (X ^ 2 - X - 1)).coeff 1

/-- The generating function of A192755 is -x*(1+4*x) / ( (x^2+x-1)*(x-1)^2 ). -/
theorem main :
    PowerSeries.mk a * ((PowerSeries.X ^ 2 + PowerSeries.X - 1) * (PowerSeries.X - 1) ^ 2)
      = -(PowerSeries.X : PowerSeries ℤ) * (1 + 4 * PowerSeries.X) := by
  sorry

end OMA.S_oeis_a192755
