import Mathlib

/-!
# A329421: a(n) = gcd(A330050(n), A330051(n)).

Source: https://oeis.org/A329421
Credit: @agchua

Colin Barker, in the formula section of A329421:
  Conjectures from _Colin Barker_, Dec 02 2019: (Start)
  G.f.: x*(1 + x)*(3 - x + 8*x^2 + 17*x^3 - 8*x^4 + 18*x^5 - 24*x^6 + 9*x^7 - x^9 + 8*x^10 + 2*x^11 + x^12) / ((1 + 4*x^2 - x^4)*(1 + x^2 - x^4)*(1 - x^2 - x^4)*(1 - 4*x^2 - x^4)).
  a(n) = 21*a(n-4) - 56*a(n-8) + 21*a(n-12) - a(n-16) for n>15.
  (End)
This file states both parts: the g.f. as an identity of formal power series over ℚ (the series of
a times the denominator equals the numerator), and the recurrence for n ≥ 16. Offset 0.

Definitions, from the name lines of A330050 and A330051 (both offset 0), with F = A000045
extended to negative indices by F(-k) = (-1)^(k+1) F(k) (this is needed for F(n-2) at n = 0, 1):
  A330050(n) = 2*((-1)^n - 1)*(F(n) - 1) - (3*(-1)^n + 7)/2 * F(n+1) + 5*F(n+1)^2,
  A330051(n) = 1 + F(2*n+1) - (F(n+4) - (-1)^n*F(n-2))/2.
Both quotients by 2 are exact ((3*(-1)^n + 7)/2 is 5 or 2, and F(n+4) - (-1)^n*F(n-2) is
4*F(n+1) for even n and 2*(F(n) + F(n+2)) for odd n), so the integer division of ℤ gives the
exact values. a(n) is Int.gcd of the two values, a natural number; gcd(0, 0) = 0 gives the listed
a(0) = 0.
-/

namespace OMA.S_oeis_a329421

/-- The Fibonacci numbers A000045 on ℤ: F(n) = Nat.fib n for n ≥ 0, and F(-(k+1)) =
(-1)^k F(k+1), that is F(-m) = (-1)^(m+1) F(m). -/
def F : ℤ → ℤ
  | Int.ofNat n => (Nat.fib n : ℤ)
  | Int.negSucc k => (-1) ^ k * (Nat.fib (k + 1) : ℤ)

/-- A330050(n) = 2*((-1)^n - 1)*(F(n) - 1) - (3*(-1)^n + 7)/2 * F(n+1) + 5*F(n+1)^2. -/
def A330050 (n : ℕ) : ℤ :=
  2 * ((-1) ^ n - 1) * (F (n : ℤ) - 1) - (3 * (-1) ^ n + 7) / 2 * F ((n : ℤ) + 1) +
    5 * F ((n : ℤ) + 1) ^ 2

/-- A330051(n) = 1 + F(2*n+1) - (F(n+4) - (-1)^n*F(n-2))/2. -/
def A330051 (n : ℕ) : ℤ :=
  1 + F (2 * (n : ℤ) + 1) - (F ((n : ℤ) + 4) - (-1) ^ n * F ((n : ℤ) - 2)) / 2

/-- A329421(n) = gcd(A330050(n), A330051(n)). -/
def a (n : ℕ) : ℕ := Int.gcd (A330050 n) (A330051 n)

/-- Barker's conjectures: the g.f. x*(1 + x)*(3 - x + 8*x^2 + 17*x^3 - 8*x^4 + 18*x^5 - 24*x^6 +
9*x^7 - x^9 + 8*x^10 + 2*x^11 + x^12) / ((1 + 4*x^2 - x^4)*(1 + x^2 - x^4)*(1 - x^2 - x^4)*
(1 - 4*x^2 - x^4)), and a(n) = 21*a(n-4) - 56*a(n-8) + 21*a(n-12) - a(n-16) for n > 15. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) *
        ((1 + 4 * PowerSeries.X ^ 2 - PowerSeries.X ^ 4) * (1 + PowerSeries.X ^ 2 - PowerSeries.X ^ 4) *
          (1 - PowerSeries.X ^ 2 - PowerSeries.X ^ 4) * (1 - 4 * PowerSeries.X ^ 2 - PowerSeries.X ^ 4)) =
      PowerSeries.X * (1 + PowerSeries.X) *
        (3 - PowerSeries.X + 8 * PowerSeries.X ^ 2 + 17 * PowerSeries.X ^ 3 - 8 * PowerSeries.X ^ 4 +
          18 * PowerSeries.X ^ 5 - 24 * PowerSeries.X ^ 6 + 9 * PowerSeries.X ^ 7 - PowerSeries.X ^ 9 +
          8 * PowerSeries.X ^ 10 + 2 * PowerSeries.X ^ 11 + PowerSeries.X ^ 12) ∧
    ∀ n : ℕ, 16 ≤ n →
      (a n : ℤ) = 21 * (a (n - 4) : ℤ) - 56 * (a (n - 8) : ℤ) + 21 * (a (n - 12) : ℤ) -
        (a (n - 16) : ℤ) := by
  sorry

end OMA.S_oeis_a329421