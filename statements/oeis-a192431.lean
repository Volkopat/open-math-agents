import Mathlib

/-!
# A192431: Coefficient of x in the reduction by x^2->x+1 of the polynomial p(n,x) defined below in Comments.

Source: https://oeis.org/A192431
Credit: @JeremyDevs

Formalizes the recurrence conjectured by Colin Barker (Jun 07 2019) in OEIS A192431:
a(n) = 2*a(n-1) + 6*a(n-2) - 2*a(n-3) - a(n-4) for n>3.

Conventions:
* The polynomials are p(n,x) = (u^n + v^n)/2 + (u^n - v^n)/(2d), where u = x+d, v = x-d and
  d = sqrt(x+2). This is the definition used by the Mathematica program of the entry (given at
  A192430, to which the entry refers) and it is the one that reproduces the polynomials of the
  EXAMPLE section (p(0,x) = 1, p(1,x) = 1+x, p(2,x) = 2+3x+x^2, p(3,x) = 2+7x+6x^2+x^3, ...) and
  the data. The COMMENTS line prints the same formula with typos (a stray exponent and
  d=sqrt(x^2+2)); with x^2+2 the examples and the data would not be obtained.
* Since d^2 = x+2, one has (x+d)^n = P_n(x) + Q_n(x)*d and (x-d)^n = P_n(x) - Q_n(x)*d for
  polynomials P_n, Q_n with integer coefficients, determined by P_0 = 1, Q_0 = 0 and
  (P + Q*d)*(x + d) = (x*P + (x+2)*Q) + (P + x*Q)*d, so that p(n,x) = P_n(x) + Q_n(x). The pair
  (P_n, Q_n) is `pq n` below and p(n,x) is `p n`, in `ℤ[X]`.
* The reduction of a polynomial by x^2 -> x+1 (see A192232) replaces x^2 by x+1 repeatedly until
  a polynomial of degree at most 1 is left; this is the remainder of the polynomial modulo
  x^2 - x - 1, here `p n %ₘ (X ^ 2 - X - 1)`. Its coefficient of x is its coefficient of index 1.
* The sequence has offset 0 (data 0, 1, 4, 15, 52, 185, 648, ...): a(n) is the coefficient of x
  in the reduction of p(n,x). The terms are integers.
* The range `n > 3` is the one stated in the source; there all the indices `n - 1, ..., n - 4`
  are at least the offset 0.
* Barker's generating function x*(1 + x)^2 / (1 - 2*x - 6*x^2 + 2*x^3 + x^4) is not stated
  separately: given the first four terms it is the same assertion as the recurrence.
-/

namespace OMA.S_oeis_a192431

open Polynomial

/-- `(x + d)^n = P_n + Q_n * d` with `d^2 = x + 2`: the pair `(P_n, Q_n)`. -/
noncomputable def pq : ℕ → ℤ[X] × ℤ[X]
  | 0 => (1, 0)
  | n + 1 => (X * (pq n).1 + (X + 2) * (pq n).2, (pq n).1 + X * (pq n).2)

/-- p(n,x) = ((x+d)^n + (x-d)^n)/2 + ((x+d)^n - (x-d)^n)/(2d) with d = sqrt(x+2). -/
noncomputable def p (n : ℕ) : ℤ[X] := (pq n).1 + (pq n).2

/-- A192431 (offset 0): the coefficient of x in the reduction of p(n,x) by x^2 -> x+1. -/
noncomputable def a (n : ℕ) : ℤ := (p n %ₘ (X ^ 2 - X - 1)).coeff 1

/-- For every `n > 3`, a(n) = 2*a(n-1) + 6*a(n-2) - 2*a(n-3) - a(n-4). -/
theorem main : ∀ n : ℕ, 3 < n →
    a n = 2 * a (n - 1) + 6 * a (n - 2) - 2 * a (n - 3) - a (n - 4) := by
  sorry

end OMA.S_oeis_a192431
