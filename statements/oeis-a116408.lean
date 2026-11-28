import Mathlib

/-!
# A116408: E.g.f. exp(x)*(Bessel_I(2,2*x) - Bessel_I(3,2*x) + Bessel_I(4,2*x)).

Source: https://oeis.org/A116408
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A116408 (R. J. Mathar, Dec 10 2011):
2*(n+4)*(n-23)*a(n) + 2*(n^2+64n+79)*a(n-1) +(-59n^2+232n+740)*a(n-2) +(64n^2-585n+1019)*a(n-3)
+3(n-3)*(41n-124)*a(n-4)=0.

Conventions:
* The sequence has offset 0 (data 0, 0, 1, 2, 7, 20, 61, 182, 546, 1632, ...) and a(n) is n!
  times the coefficient of x^n in the exponential generating function
  exp(x)*(Bessel_I(2,2*x) - Bessel_I(3,2*x) + Bessel_I(4,2*x)).
* Bessel_I(v,z) is the modified Bessel function of the first kind, with the power series
  Bessel_I(v,z) = Sum_{k>=0} (z/2)^(2k+v) / (k! * (k+v)!). Hence
  Bessel_I(v,2*x) = Sum_{k>=0} x^(2k+v) / (k! * (k+v)!), a series with rational coefficients.
  `bes v n` below is the coefficient of x^n in this series: it is
  1 / (((n-v)/2)! * ((n+v)/2)!) when n >= v and n - v is even (then k = (n-v)/2 and
  k + v = (n+v)/2), and 0 otherwise.
* `b n` is the coefficient of x^n in Bessel_I(2,2*x) - Bessel_I(3,2*x) + Bessel_I(4,2*x).
* exp(x) is the formal power series `PowerSeries.exp ℚ` and the product is the product of
  formal power series over `ℚ`.
* a(n) is defined as a rational number (it is an integer).
* The source gives no range for n. The recurrence is asserted for every `n ≥ 4`, which is
  exactly the range in which all the indices n, n-1, n-2, n-3, n-4 are at least the offset 0.
* The identity is stated in `ℚ`, with the natural number `n` cast to `ℚ`, so the subtractions
  in the polynomial coefficients are exact.
-/

namespace OMA.S_oeis_a116408

/-- The coefficient of x^n in Bessel_I(v,2*x) = Sum_{k>=0} x^(2k+v) / (k! * (k+v)!). -/
def bes (v n : ℕ) : ℚ :=
  if v ≤ n ∧ (n - v) % 2 = 0 then
    1 / ((((n - v) / 2).factorial : ℚ) * (((n + v) / 2).factorial : ℚ))
  else 0

/-- The coefficient of x^n in Bessel_I(2,2*x) - Bessel_I(3,2*x) + Bessel_I(4,2*x). -/
def b (n : ℕ) : ℚ := bes 2 n - bes 3 n + bes 4 n

/-- A116408 (offset 0): n! times the coefficient of x^n in
exp(x)*(Bessel_I(2,2*x) - Bessel_I(3,2*x) + Bessel_I(4,2*x)). -/
noncomputable def a (n : ℕ) : ℚ :=
  (n.factorial : ℚ) * PowerSeries.coeff n (PowerSeries.exp ℚ * PowerSeries.mk b)

/-- For every `n ≥ 4`, 2*(n+4)*(n-23)*a(n) + 2*(n^2+64n+79)*a(n-1) + (-59n^2+232n+740)*a(n-2)
+ (64n^2-585n+1019)*a(n-3) + 3(n-3)*(41n-124)*a(n-4) = 0. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    2 * ((n : ℚ) + 4) * ((n : ℚ) - 23) * a n
      + 2 * ((n : ℚ) ^ 2 + 64 * (n : ℚ) + 79) * a (n - 1)
      + (-59 * (n : ℚ) ^ 2 + 232 * (n : ℚ) + 740) * a (n - 2)
      + (64 * (n : ℚ) ^ 2 - 585 * (n : ℚ) + 1019) * a (n - 3)
      + 3 * ((n : ℚ) - 3) * (41 * (n : ℚ) - 124) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a116408
