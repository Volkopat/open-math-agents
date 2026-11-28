import Mathlib

/-!
# A192747: Coefficient of x in the reduction by x^2->x+1 of the polynomial p(n,x) defined below in Comments.

Source: https://oeis.org/A192747
Credit: @agchua

R. J. Mathar (May 04 2014), in the formula section of A192747:
  Conjecture: G.f.: x^2*(-1-3*x+x^2) / ( (x^2+x-1)*(x-1)^2 ), so the first differences are in A192746.
The polynomials. The comment of the entry reads p(n,x)=x*(n-1,x)+3n+1 for n>0, where p(0,x)=1. The
Mathematica program that computes this entry (in A192746, by Clark Kimberling, Jul 09 2011, list u2)
uses p(n,x) = x*p(n-1,x) + 3n + 2 with p(0,x) = 1, and the listed terms 0, 1, 6, 15, 32, 61, ... of
this entry and 1, 5, 9, 17, 29, ... of A192746 are those of the program (with 3n+1 the terms would be
0, 1, 5, 13, 28, ...). Mathar's conjecture is about the listed terms, so the definition below follows
the terms and the program: p(0,x) = 1, p(n,x) = x*p(n-1,x) + 3n + 2.
The reduction by x^2 -> x+1 (A192232, A192744) is the remainder on division by the monic polynomial
x^2 - x - 1, here Polynomial.modByMonic. The program lists the coefficient of x in the reduction of
p(n-1,x) as the term n = 1, 2, 3, ... (offset 1), so a(n) = coefficient of x^1 in p(n-1,x) mod
(x^2 - x - 1), n ≥ 1; and A192746(n), offset 0, is the constant term of the reduction of p(n,x).
Both parts are stated: the g.f. of (a(n))_{n ≥ 1}, written X * ∑ a(n+1) X^n, times (X^2+X-1)(X-1)^2
equals X^2(-1-3X+X^2), as an identity of formal power series over ℚ; and the first differences
a(n+2) - a(n+1), n ≥ 0, are the terms A192746(n), the constant terms of the reductions.
-/

namespace OMA.S_oeis_a192747

open Polynomial

/-- The polynomials of the program: p(0,x) = 1, p(n,x) = x*p(n-1,x) + 3n + 2 for n > 0. -/
noncomputable def p : ℕ → Polynomial ℤ
  | 0 => 1
  | (n + 1) => X * p n + C (3 * ((n : ℤ) + 1) + 2)

/-- A192747(n), n ≥ 1: the coefficient of x in the reduction of p(n-1,x) by x^2 -> x+1. -/
noncomputable def a (n : ℕ) : ℤ := (p (n - 1) %ₘ (X ^ 2 - X - 1)).coeff 1

/-- Mathar's conjecture: the g.f. x^2(-1-3x+x^2)/((x^2+x-1)(x-1)^2), and the first differences are
the terms of A192746, the constant terms of the reductions of p(n,x). -/
theorem main :
    PowerSeries.X * PowerSeries.mk (fun n => (a (n + 1) : ℚ)) *
        ((PowerSeries.X ^ 2 + PowerSeries.X - 1) * (PowerSeries.X - 1) ^ 2) =
      PowerSeries.X ^ 2 * (-1 - 3 * PowerSeries.X + PowerSeries.X ^ 2) ∧
    ∀ n : ℕ, a (n + 2) - a (n + 1) = (p n %ₘ (X ^ 2 - X - 1)).coeff 0 := by
  sorry

end OMA.S_oeis_a192747
