import Mathlib

/-!
# A192249: 1-sequence of reduction of binomial coefficient sequence B(n,4)=A000332 by x^2 -> x+1.

Source: https://oeis.org/A192249
Credit: @agchua

R. J. Mathar (May 04 2014), in the formula section of A192249:
  Conjecture: G.f.: 5*x^2*(1-2*x+4*x^2-3*x^3+x^4) / ( (x-1)*(x^2+x-1)^5 ).
Definition, as in A192232 (the k-sequences of the reduction of a sequence) and in the Mathematica
program of A192248, which computes A192248 and A192249: c(n) = n(n+1)(n+2)(n+3)/24 = B(n+3,4),
p(0,x) = 1 and p(n,x) = p(n-1,x) + c(n+1) x^n, so p(n,x) = Sum_{k=0..n} B(k+4,4) x^k (the terms
1, 5, 15, 35, ... of A000332 from its first nonzero term). The reduction by x^2 -> x+1 (replace x^2 by
x+1 until the degree is below 2) is the remainder on division by the monic polynomial x^2 - x - 1,
here Polynomial.modByMonic, and the 1-sequence is its coefficient of x. The program lists it for
p(0,x), p(1,x), ... as the terms n = 1, 2, ... (offset 1), so a(n) = coefficient of x in
p(n-1,x) mod (x^2 - x - 1) for n ≥ 1; this gives the listed terms 0, 5, 20, 90, 300, 930, ...
The g.f. of (a(n))_{n ≥ 1}, written X * Sum_{n ≥ 0} a(n+1) X^n, is stated as an identity of formal
power series over ℚ: it times (X-1)(X^2+X-1)^5 equals 5X^2(1-2X+4X^2-3X^3+X^4).
-/

namespace OMA.S_oeis_a192249

open Polynomial

/-- p(n,x) = Sum_{k=0..n} B(k+4,4) x^k, the polynomials of the program in A192248. -/
noncomputable def p (n : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range (n + 1), C ((Nat.choose (k + 4) 4 : ℕ) : ℤ) * X ^ k

/-- A192249(n), n ≥ 1: the coefficient of x in the reduction of p(n-1,x) by x^2 -> x+1. -/
noncomputable def a (n : ℕ) : ℤ := (p (n - 1) %ₘ (X ^ 2 - X - 1)).coeff 1

/-- Mathar's conjecture: the g.f. 5x^2(1-2x+4x^2-3x^3+x^4)/((x-1)(x^2+x-1)^5). -/
theorem main :
    PowerSeries.X * PowerSeries.mk (fun n => (a (n + 1) : ℚ)) *
        ((PowerSeries.X - 1) * (PowerSeries.X ^ 2 + PowerSeries.X - 1) ^ 5) =
      5 * PowerSeries.X ^ 2 * (1 - 2 * PowerSeries.X + 4 * PowerSeries.X ^ 2 -
        3 * PowerSeries.X ^ 3 + PowerSeries.X ^ 4) := by
  sorry

end OMA.S_oeis_a192249
