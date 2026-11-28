import Mathlib

/-!
# A065919: Bessel polynomial y_n(4).

Source: https://oeis.org/A065919
Credit: @agchua

Formula line of A065919 (Peter Bala, Dec 09 2025):
  Conjecture: ( Sum_{n >= 0} a(n)*x^n/n! )/( 1 + Sum_{n >= 0} a(n)*x^(n+1)/(n+1)! ) =
  Sum_{n >= 0} A059304(n)*x^n/n!.
Offset of A065919: 0 (data 1, 5, 61, 1225, 34361, ...).
A059304 (offset 0): a(n) = 2^n * (2*n)! / (n!)^2, its name line (data 1, 4, 24, 160, ...).

Formalisation. a(n) = y_n(4) is computed from the entry's formula
y_n(x) = Sum_{k=0..n} (n+k)!*(x/2)^k/((n-k)!*k!) with x = 4; each quotient (n+k)!/((n-k)!*k!)
is an integer, so the natural-number division is exact. The three series are power series
over the rationals; the series in the denominator has constant term 1, so it is invertible, and
the quotient P/Q is written P * Q⁻¹. The series Sum a(n)*x^(n+1)/(n+1)! is
X * Sum a(n)*x^n/(n+1)!.
-/

namespace OMA.S_oeis_a065919

/-- a(n) = y_n(4) = Sum_{k=0..n} (n+k)!/((n-k)!*k!) * 2^k. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), (n + k).factorial / ((n - k).factorial * k.factorial) * 2 ^ k

/-- A059304(n) = 2^n * (2*n)! / (n!)^2. -/
def A059304 (n : ℕ) : ℕ := 2 ^ n * (2 * n).factorial / (n.factorial ^ 2)

/-- The conjecture, as printed: the quotient of the two exponential generating functions is
the exponential generating function of A059304. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ) / (n.factorial : ℚ)) *
        (1 + PowerSeries.X * PowerSeries.mk (fun n => (a n : ℚ) / ((n + 1).factorial : ℚ)))⁻¹ =
      PowerSeries.mk (fun n => (A059304 n : ℚ) / (n.factorial : ℚ)) := by
  sorry

end OMA.S_oeis_a065919
