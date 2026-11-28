import Mathlib

/-!
# A192758: Coefficient of x in the reduction by x^2->x+1 of the polynomial p(n,x) defined below in Comments.

Source: https://oeis.org/A192758
Credit: @JeremyDevs

Formalizes the generating function conjectured in OEIS A192758 (R. J. Mathar, May 04 2014):
G.f.: -x^2 / ( (1+x)*(x^2+1)*(x^2+x-1)*(x-1)^2 ).

Conventions:
* The titular polynomial is defined recursively (COMMENTS section of the entry) by
  p(n,x) = x*p(n-1,x) + floor((n+4)/4) for n > 0, where p(0,x) = 1; it is `p n` below, in `ℤ[X]`,
  with the recursion written with `n + 1` in place of `n`; floor((n+4)/4) is the natural-number
  quotient `(n + 4) / 4`.
* The reduction of a polynomial by x^2 -> x+1 (see A192232) replaces x^2 by x+1 repeatedly until
  a polynomial of degree at most 1 is left; this is the remainder of the polynomial modulo
  x^2 - x - 1, here `p n %ₘ (X ^ 2 - X - 1)`. Its coefficient of x is its coefficient of index 1.
* The sequence has offset 1 and its first term comes from p(0,x) = 1 (data 0, 1, 2, 4, 7, 13, 22,
  37, ...: p(0,x) = 1 -> 1, p(1,x) = x + 1 -> 1 + x, p(2,x) = x^2 + x + 1 -> 2 + 2x), so a(n) is
  the coefficient of x in the reduction of p(n-1,x). The function `b` below is this coefficient
  for p(m,x), i.e. a(n) = b(n-1) for `n ≥ 1`.
* The ordinary generating function of an offset-1 sequence is the formal power series
  `∑_{n ≥ 1} a(n) x^n = x * ∑_{m ≥ 0} b(m) x^m`, here `PowerSeries.X * PowerSeries.mk b` in
  `PowerSeries ℤ`. "G.f. = N(x)/D(x)" is stated without division, as `G.f. * D(x) = N(x)` with
  D(x) = (1+x)*(x^2+1)*(x^2+x-1)*(x-1)^2, which is the same assertion (D has constant term -1, so
  it is invertible as a power series).
* The same comment also records "partial sums of A080239. a(n)-a(n-2) = A097083(n-1)"; these are
  not stated separately.
-/

namespace OMA.S_oeis_a192758

open Polynomial

/-- p(0,x) = 1, p(n,x) = x*p(n-1,x) + floor((n+4)/4). -/
noncomputable def p : ℕ → ℤ[X]
  | 0 => 1
  | n + 1 => X * p n + C ((((n + 1 + 4) / 4 : ℕ) : ℤ))

/-- The coefficient of x in the reduction of p(m,x) by x^2 -> x+1; A192758(n) = b(n-1). -/
noncomputable def b (m : ℕ) : ℤ := (p m %ₘ (X ^ 2 - X - 1)).coeff 1

/-- The generating function of A192758 is -x^2 / ( (1+x)*(x^2+1)*(x^2+x-1)*(x-1)^2 ). -/
theorem main :
    (PowerSeries.X * PowerSeries.mk b)
        * ((1 + PowerSeries.X) * (PowerSeries.X ^ 2 + 1) * (PowerSeries.X ^ 2 + PowerSeries.X - 1)
          * (PowerSeries.X - 1) ^ 2)
      = -(PowerSeries.X : PowerSeries ℤ) ^ 2 := by
  sorry

end OMA.S_oeis_a192758
