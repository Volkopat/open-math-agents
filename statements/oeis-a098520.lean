import Mathlib

/-!
# A098520: E.g.f. exp(x)*BesselI(1,4*x)/2.

Source: https://oeis.org/A098520
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A098520 (R. J. Mathar, Dec 11 2011):
(n-1)*(n+1)*a(n) - n*(2n-1)*a(n-1) - 15*n*(n-1)*a(n-2) = 0.

Conventions:
* The sequence has offset 0 (data 0, 1, 2, 15, 52, 285, 1206, 6027, ...) and a(n) is n! times
  the coefficient of x^n in the exponential generating function exp(x)*BesselI(1,4*x)/2.
* BesselI(v,z) is the modified Bessel function of the first kind, with the power series
  BesselI(v,z) = Sum_{k>=0} (z/2)^(2k+v) / (k! * (k+v)!). Hence
  BesselI(1,4*x)/2 = Sum_{k>=0} 4^k * x^(2k+1) / (k! * (k+1)!).
  `b n` below is the coefficient of x^n in this series: 4^((n-1)/2) / (((n-1)/2)! * ((n+1)/2)!)
  for odd n and 0 for even n.
* exp(x) is the formal power series `PowerSeries.exp ℚ` and the product is the product of
  formal power series over `ℚ`.
* a(n) is defined as a rational number (it is an integer).
* The source gives no range for n. The recurrence is asserted for every `n ≥ 2`, which is
  exactly the range in which all the indices n, n-1, n-2 are at least the offset 0.
* The identity is stated in `ℚ`, with the natural number `n` cast to `ℚ`, so the subtractions
  in the polynomial coefficients are exact.
-/

namespace OMA.S_oeis_a098520

/-- The coefficient of x^n in BesselI(1,4*x)/2 = Sum_{k>=0} 4^k * x^(2k+1) / (k!*(k+1)!). -/
def b (n : ℕ) : ℚ :=
  if Odd n then
    (4 : ℚ) ^ ((n - 1) / 2) / ((((n - 1) / 2).factorial : ℚ) * (((n + 1) / 2).factorial : ℚ))
  else 0

/-- A098520 (offset 0): n! times the coefficient of x^n in exp(x)*BesselI(1,4*x)/2. -/
noncomputable def a (n : ℕ) : ℚ :=
  (n.factorial : ℚ) * PowerSeries.coeff n (PowerSeries.exp ℚ * PowerSeries.mk b)

/-- For every `n ≥ 2`, (n-1)*(n+1)*a(n) - n*(2n-1)*a(n-1) - 15*n*(n-1)*a(n-2) = 0. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    ((n : ℚ) - 1) * ((n : ℚ) + 1) * a n - (n : ℚ) * (2 * (n : ℚ) - 1) * a (n - 1)
      - 15 * (n : ℚ) * ((n : ℚ) - 1) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a098520
