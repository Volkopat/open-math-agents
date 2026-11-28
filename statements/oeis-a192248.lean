import Mathlib

/-!
# A192248: 0-sequence of reduction of binomial coefficient sequence B(n,4)=A000332 by x^2 -> x+1

Source: https://oeis.org/A192248
Credit: @ivillar

Clark Kimberling's sequence (offset 1, data 1, 1, 16, 51, 191, 569, 1619, ...). Following the entry's
program: c(n) = n(n+1)(n+2)(n+3)/24 (the binomial coefficients, so c(k+1) = binomial(k+4,4)), and
p(0,x) = 1, p(n,x) = p(n-1,x) + x^n*c(n+1), i.e. p(n,x) = Sum_{k=0..n} c(k+1)*x^k. Reducing by
x^2 -> x+1 means replacing x^2 by x + 1 repeatedly until the degree is at most 1 (see A192232); the
result is the remainder modulo the monic polynomial x^2 - x - 1. The program lists the constant
terms of the reductions of p(0,x), p(1,x), ..., so a(n) is the constant term of the reduction of
p(n-1,x). We work in ℚ[x].

Conjecture (R. J. Mathar, May 04 2014):
G.f.: -x*(-1+5*x-20*x^2+30*x^3-25*x^4+8*x^5) / ( (x-1)*(x^2+x-1)^5 ).
It is the g.f. of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ.
-/

namespace OMA.S_oeis_a192248

open Polynomial

/-- c(n) = n(n+1)(n+2)(n+3)/24. -/
noncomputable def c (n : ℕ) : ℚ := (n : ℚ) * (n + 1) * (n + 2) * (n + 3) / 24

/-- p(0,x) = 1 and p(n,x) = p(n-1,x) + x^n*c(n+1). -/
noncomputable def p : ℕ → ℚ[X]
  | 0 => 1
  | n + 1 => p n + X ^ (n + 1) * C (c (n + 2))

/-- The reduction by x^2 -> x+1: the remainder modulo x^2 - x - 1. -/
noncomputable def reduce (f : ℚ[X]) : ℚ[X] := f %ₘ (X ^ 2 - X - 1)

/-- a(n) (offset 1): the constant term of the reduction of p(n-1,x). -/
noncomputable def a (n : ℕ) : ℚ := (reduce (p (n - 1))).coeff 0

/-- The conjectured g.f. -x*(-1+5*x-20*x^2+30*x^3-25*x^4+8*x^5) / ((x-1)*(x^2+x-1)^5). -/
noncomputable def G : PowerSeries ℚ :=
  (-PowerSeries.X * (-1 + 5 * PowerSeries.X - 20 * PowerSeries.X ^ 2 + 30 * PowerSeries.X ^ 3 -
      25 * PowerSeries.X ^ 4 + 8 * PowerSeries.X ^ 5)) *
    ((PowerSeries.X - 1) * (PowerSeries.X ^ 2 + PowerSeries.X - 1) ^ 5)⁻¹

/-- Mathar's conjectured generating function. -/
theorem main : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n) = G := by
  sorry

end OMA.S_oeis_a192248
