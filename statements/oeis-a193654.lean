import Mathlib

/-!
# A193654: Q-residue of the triangle p(n,k)=floor((n+1)/(n+k+2)/2), 0<=k<=n, where Q is the triangular array (t(i,j)) given by t(i,j)=1.  (See Comments.)

Source: https://oeis.org/A193654
Credit: @agchua

R. J. Mathar (Feb 19 2015), in the formula section of A193654:
  Conjecture: G.f.: ( -1-2*x+4*x^2+4*x^3-8*x^5 ) / ( (1+x)*(2*x+1)*(x-1)^2*(2*x-1)^3 ).
This file states the g.f. as an identity of formal power series over ℚ (offset 0, so the
series starts with a(0) X^0):
(∑ a(n) X^n) * ((1+X)(2X+1)(X-1)^2(2X-1)^3) = -1 - 2X + 4X^2 + 4X^3 - 8X^5.

Definition, as in the entry's Mathematica program (Clark Kimberling): r(0) = 1,
r(k) = Sum_{i=0..k-1} q(k-1,i) r(k-1-i) with q = 1, p(n,k) = floor((n+1)(n+k+2)/2) and
a(n) = Sum_{k=0..n} p(n,k) r(n-k). This is the Q-residue of A193649: the Q-downstep is linear
and the Q-residue of x^m is r(m). With q = 1 the recursion reads r(k) = r(0) + ... + r(k-1), so
r = 1, 1, 2, 4, 8, ..., that is r(0) = 1 and r(k) = 2^(k-1) for k ≥ 1; r is defined by this
formula below. The name line prints the triangle as floor((n+1)/(n+k+2)/2), which is 0 for all
n and k; the program and the listed data 1, 7, 28, 94, 275, ... use floor((n+1)(n+k+2)/2),
which is the natural-number quotient (n+1)(n+k+2) div 2 used below.
-/

namespace OMA.S_oeis_a193654

/-- The Q-residue of x^k for the all-ones array Q: r(0) = 1 and r(k) = 2^(k-1) for k ≥ 1. -/
def r (k : ℕ) : ℕ := if k = 0 then 1 else 2 ^ (k - 1)

/-- The triangle p(n,k) = floor((n+1)(n+k+2)/2), 0 ≤ k ≤ n. -/
def p (n k : ℕ) : ℕ := (n + 1) * (n + k + 2) / 2

/-- A193654: a(n) = Sum_{k=0..n} p(n,k) r(n-k). -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), p n k * r (n - k)

/-- Mathar's conjectured g.f. ( -1-2x+4x^2+4x^3-8x^5 ) / ( (1+x)(2x+1)(x-1)^2(2x-1)^3 ). -/
theorem main : PowerSeries.mk (fun n => (a n : ℚ)) *
    ((1 + PowerSeries.X) * (2 * PowerSeries.X + 1) * (PowerSeries.X - 1) ^ 2 *
      (2 * PowerSeries.X - 1) ^ 3) =
    -1 - 2 * PowerSeries.X + 4 * PowerSeries.X ^ 2 + 4 * PowerSeries.X ^ 3 -
      8 * PowerSeries.X ^ 5 := by
  sorry

end OMA.S_oeis_a193654
