import Mathlib

/-!
# A119975: E.g.f. exp(x)*(Bessel_I(0,2*sqrt(2)x) + Bessel_I(1,2*sqrt(2)x)/sqrt(2)).

Source: https://oeis.org/A119975
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A119975 (R. J. Mathar, Dec 10 2011):
(n+1)*a(n) +(n-4)*a(n-1) +(9-13*n)*a(n-2) +21*(2-n)*a(n-3) =0.

Conventions:
* The sequence has offset 0 (data 1, 2, 7, 22, 77, 266, 947, 3382, ...) and a(n) is n! times
  the coefficient of x^n in the exponential generating function
  exp(x)*(Bessel_I(0,2*sqrt(2)x) + Bessel_I(1,2*sqrt(2)x)/sqrt(2)).
* Bessel_I(v,z) is the modified Bessel function of the first kind, with the power series
  Bessel_I(v,z) = Sum_{k>=0} (z/2)^(2k+v) / (k! * (k+v)!). Hence
  Bessel_I(0,2*sqrt(2)x) = Sum_{k>=0} 2^k * x^(2k) / (k!)^2 and
  Bessel_I(1,2*sqrt(2)x)/sqrt(2) = Sum_{k>=0} 2^k * x^(2k+1) / (k! * (k+1)!), two series with
  rational coefficients. `b0 n` and `b1 n` below are the coefficients of x^n in these two
  series: `b0 n` is 2^(n/2) / ((n/2)!)^2 for even n and 0 for odd n, and `b1 n` is
  2^((n-1)/2) / (((n-1)/2)! * ((n+1)/2)!) for odd n and 0 for even n.
* exp(x) is the formal power series `PowerSeries.exp ℚ` and the product is the product of
  formal power series over `ℚ`.
* a(n) is defined as a rational number (it is an integer).
* The source gives no range for n. The recurrence is asserted for every `n ≥ 3`, which is
  exactly the range in which all the indices n, n-1, n-2, n-3 are at least the offset 0.
* The identity is stated in `ℚ`, with the natural number `n` cast to `ℚ`, so the subtractions
  in the polynomial coefficients are exact.
-/

namespace OMA.S_oeis_a119975

/-- The coefficient of x^n in Bessel_I(0,2*sqrt(2)x) = Sum_{k>=0} 2^k * x^(2k) / (k!)^2. -/
def b0 (n : ℕ) : ℚ := if Even n then (2 : ℚ) ^ (n / 2) / (((n / 2).factorial : ℚ) ^ 2) else 0

/-- The coefficient of x^n in
Bessel_I(1,2*sqrt(2)x)/sqrt(2) = Sum_{k>=0} 2^k * x^(2k+1) / (k!*(k+1)!). -/
def b1 (n : ℕ) : ℚ :=
  if Odd n then
    (2 : ℚ) ^ ((n - 1) / 2) / ((((n - 1) / 2).factorial : ℚ) * (((n + 1) / 2).factorial : ℚ))
  else 0

/-- A119975 (offset 0): n! times the coefficient of x^n in
exp(x)*(Bessel_I(0,2*sqrt(2)x) + Bessel_I(1,2*sqrt(2)x)/sqrt(2)). -/
noncomputable def a (n : ℕ) : ℚ :=
  (n.factorial : ℚ)
    * PowerSeries.coeff n (PowerSeries.exp ℚ * (PowerSeries.mk b0 + PowerSeries.mk b1))

/-- For every `n ≥ 3`, (n+1)*a(n) + (n-4)*a(n-1) + (9-13*n)*a(n-2) + 21*(2-n)*a(n-3) = 0. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    ((n : ℚ) + 1) * a n + ((n : ℚ) - 4) * a (n - 1) + (9 - 13 * (n : ℚ)) * a (n - 2)
      + 21 * (2 - (n : ℚ)) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a119975
