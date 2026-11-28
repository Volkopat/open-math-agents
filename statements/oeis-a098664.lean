import Mathlib

/-!
# A098664: Expansion of e.g.f. BesselI(0,4*x)+BesselI(1,4*x)/2.

Source: https://oeis.org/A098664
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A098664 (R. J. Mathar, Dec 08 2011):
(n+1)*a(n) + 8*(n-1)*a(n-1) - 16*n*a(n-2) + 128*(2-n)*a(n-3) = 0.

Conventions:
* The sequence has offset 0 (data 1, 1, 8, 12, 96, 160, 1280, ...) and a(n) is n! times the
  coefficient of x^n in the exponential generating function BesselI(0,4*x) + BesselI(1,4*x)/2.
* BesselI(v,z) is the modified Bessel function of the first kind, with the power series
  BesselI(v,z) = Sum_{k>=0} (z/2)^(2k+v) / (k! * (k+v)!). Hence
  BesselI(0,4*x) = Sum_{k>=0} 2^(2k) * x^(2k) / (k!)^2 and
  BesselI(1,4*x) = Sum_{k>=0} 2^(2k+1) * x^(2k+1) / (k! * (k+1)!).
  `i0 n` and `i1 n` below are the coefficients of x^n in these two series: `i0 n` is
  2^n / ((n/2)!)^2 for even n and 0 for odd n, and `i1 n` is 2^n / (((n-1)/2)! * ((n+1)/2)!)
  for odd n and 0 for even n.
* a(n) is defined as a rational number (it is an integer, binomial(n, floor(n/2))*4^floor(n/2)).
* The source gives no range for n. The recurrence is asserted for every `n ≥ 3`, which is
  exactly the range in which all the indices n, n-1, n-2, n-3 are at least the offset 0.
* The identity is stated in `ℚ`, with the natural number `n` cast to `ℚ`, so the subtractions
  in the polynomial coefficients (n-1, 2-n) are exact.
-/

namespace OMA.S_oeis_a098664

/-- The coefficient of x^n in BesselI(0,4*x) = Sum_{k>=0} 2^(2k) * x^(2k) / (k!)^2. -/
def i0 (n : ℕ) : ℚ := if Even n then (2 : ℚ) ^ n / (((n / 2).factorial : ℚ) ^ 2) else 0

/-- The coefficient of x^n in BesselI(1,4*x) = Sum_{k>=0} 2^(2k+1) * x^(2k+1) / (k!*(k+1)!). -/
def i1 (n : ℕ) : ℚ :=
  if Odd n then (2 : ℚ) ^ n / ((((n - 1) / 2).factorial : ℚ) * (((n + 1) / 2).factorial : ℚ))
  else 0

/-- A098664 (offset 0): n! times the coefficient of x^n in BesselI(0,4*x) + BesselI(1,4*x)/2. -/
def a (n : ℕ) : ℚ := (n.factorial : ℚ) * (i0 n + i1 n / 2)

/-- For every `n ≥ 3`, (n+1)*a(n) + 8*(n-1)*a(n-1) - 16*n*a(n-2) + 128*(2-n)*a(n-3) = 0. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    ((n : ℚ) + 1) * a n + 8 * ((n : ℚ) - 1) * a (n - 1) - 16 * (n : ℚ) * a (n - 2)
      + 128 * (2 - (n : ℚ)) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a098664
