import Mathlib

/-!
# A049638: a(n) = T(n,4), array T as in A049627.

Source: https://oeis.org/A049638
Credit: @agchua

R. J. Mathar (Oct 26 2015), in the formula section of A049638:
  Conjectured g.f.: 2 -x*(-7-9*x-5*x^2+2*x^3+3*x^4) / ( (1+x)*(1+x+x^2)*(x-1)^2 ).
Definition. A049627 is the array T(i,j) = (i+1)*(j+1) - H(i,j), where H is the array of A049615,
the number of lattice points (x,y), 0 <= x <= i, 0 <= y <= j, hidden from (i,j) (some lattice point
lies strictly between them), that is gcd(i-x, j-y) > 1. The PARI program of A049638 and of A049627
(Michel Marcus, Aug 06 2021) is T(n,k) = (n+1)*(k+1) - sum(i=0, n, sum(j=0, k, gcd(i,j)>1)) and
a(n) = T(n, 4); it is used verbatim below (with Nat.gcd, where gcd(0,0) = 0). It gives the listed
terms 2, 7, 9, 12, 14, 18, 19, 23, ... Offset 0.
The g.f. is stated as an identity of formal power series over ℚ: the g.f. of (a(n))_{n ≥ 0} times
D = (1+x)(1+x+x^2)(x-1)^2 equals 2*D - x*(-7-9x-5x^2+2x^3+3x^4).
-/

namespace OMA.S_oeis_a049638

/-- The array T of A049627, by the PARI program of the entry:
T(n,k) = (n+1)(k+1) - #{(i,j) : 0 ≤ i ≤ n, 0 ≤ j ≤ k, gcd(i,j) > 1}. -/
def T (n k : ℕ) : ℤ :=
  ((n : ℤ) + 1) * ((k : ℤ) + 1) -
    ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (k + 1),
      if 1 < Nat.gcd i j then (1 : ℤ) else 0

/-- A049638(n) = T(n,4), n ≥ 0. -/
def a (n : ℕ) : ℤ := T n 4

/-- Mathar's conjecture: the g.f. is 2 - x(-7-9x-5x^2+2x^3+3x^4)/((1+x)(1+x+x^2)(x-1)^2). -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) *
        ((1 + PowerSeries.X) * (1 + PowerSeries.X + PowerSeries.X ^ 2) * (PowerSeries.X - 1) ^ 2) =
      2 * ((1 + PowerSeries.X) * (1 + PowerSeries.X + PowerSeries.X ^ 2) * (PowerSeries.X - 1) ^ 2) -
        PowerSeries.X * (-7 - 9 * PowerSeries.X - 5 * PowerSeries.X ^ 2 + 2 * PowerSeries.X ^ 3 +
          3 * PowerSeries.X ^ 4) := by
  sorry

end OMA.S_oeis_a049638
