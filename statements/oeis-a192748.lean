import Mathlib

/-!
# A192748: Constant term of the reduction by x^2->x+1 of the polynomial p(n,x) defined below in Comments.

Source: https://oeis.org/A192748
Credit: @agchua

R. J. Mathar (May 04 2014), in the formula section of A192748:
  Conjecture: G.f.: -x^2*(1+x+x^2) / ( (x^2+x-1)*(x-1)^2 ), so the first differences are in A154691.
The comment of the entry defines p(0,x) = 1 and p(n,x) = x*p(n-1,x) + 3n for n > 0; the reduction by
x^2 -> x+1 (A192232, A192744) is the remainder on division by the monic polynomial x^2 - x - 1, here
Polynomial.modByMonic. Offset 1.
Which coefficient: the listed terms 0, 1, 4, 11, 24, 47, ... and the entry's Mathematica program (its
list u2, the coefficient of x^1 in the reduction of p(n-1,x) for n = 1, 2, 3, ...) give a(n) = the
coefficient of x in the reduction of p(n-1,x); the constant terms 1, 3, 7, 13, 23, ... are A154691, as
the program's own comment says. Mathar's conjecture is about the listed terms, so the definition below
follows the terms and the program: a(n) = coefficient of x^1 in p(n-1,x) mod (x^2 - x - 1), n ≥ 1.
Both parts are stated as identities of formal power series over ℚ: the g.f. of (a(n))_{n ≥ 1}, written
X * ∑ a(n+1) X^n, times (X^2+X-1)(X-1)^2 equals -X^2(1+X+X^2); and the first differences
a(n+2) - a(n+1), n ≥ 0, have the g.f. (1+x+x^2)/((1-x)(1-x-x^2)), which defines A154691 (offset 0).
-/

namespace OMA.S_oeis_a192748

open Polynomial

/-- The polynomials of the comment: p(0,x) = 1, p(n,x) = x*p(n-1,x) + 3n for n > 0. -/
noncomputable def p : ℕ → Polynomial ℤ
  | 0 => 1
  | (n + 1) => X * p n + C (3 * ((n : ℤ) + 1))

/-- A192748(n), n ≥ 1: the coefficient of x in the reduction of p(n-1,x) by x^2 -> x+1. -/
noncomputable def a (n : ℕ) : ℤ := (p (n - 1) %ₘ (X ^ 2 - X - 1)).coeff 1

/-- Mathar's conjecture: the g.f. -x^2(1+x+x^2)/((x^2+x-1)(x-1)^2), and the first differences have
the g.f. (1+x+x^2)/((1-x)(1-x-x^2)) of A154691. -/
theorem main :
    PowerSeries.X * PowerSeries.mk (fun n => (a (n + 1) : ℚ)) *
        ((PowerSeries.X ^ 2 + PowerSeries.X - 1) * (PowerSeries.X - 1) ^ 2) =
      -(PowerSeries.X ^ 2 * (1 + PowerSeries.X + PowerSeries.X ^ 2)) ∧
    PowerSeries.mk (fun n => (a (n + 2) : ℚ) - (a (n + 1) : ℚ)) *
        ((1 - PowerSeries.X) * (1 - PowerSeries.X - PowerSeries.X ^ 2)) =
      1 + PowerSeries.X + PowerSeries.X ^ 2 := by
  sorry

end OMA.S_oeis_a192748
