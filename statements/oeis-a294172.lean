import Mathlib

/-!
# A294172: maximum of the cyclic convolution of 1..n with itself (OEIS A294172)

Source: https://oeis.org/A294172 (OEIS Foundation, CC BY-SA 4.0).
Formalization: @thomasfredrickson.

The entry defines (formula section, offset 1)
  a(n) = Max { Sum_{i=1..n} (n-i+1) * (1 + (i+k) mod n) : k = 1..n },
which is `a` below (`conv n k` is the inner sum; a(1..5) = 1, 5, 13, 28, 50).
With this definition `a 0 = 0` (an empty maximum), which is the value used for
the coefficient of x^0 in the generating function.

`main` conjoins the conjectures listed in the entry (reported true by
Sela Fried, Aug 13 2024):
  * a(n) = n*(13 + 3*(-1)^n + 24*n + 14*n^2)/48 for n >= 1;
  * lim_{n -> infinity} a(n)/n^3 = 7/24;
  * (Colin Barker) G.f.: x*(1 + 3*x + 2*x^2 + x^3) / ((1 - x)^4*(1 + x)^2),
    stated as: the power series Sum a(n) x^n times the denominator equals
    the numerator;
  * (Colin Barker) a(n) = 2*a(n-1) + a(n-2) - 4*a(n-3) + a(n-4) + 2*a(n-5)
    - a(n-6) for n > 6.
-/

namespace OMA.S_oeis_a294172

open Finset

/-- The k-th cyclic convolution sum: Sum_{i=1..n} (n-i+1) * (1 + (i+k) mod n). -/
def conv (n k : ℕ) : ℕ := ∑ i ∈ Icc 1 n, (n - i + 1) * (1 + (i + k) % n)

/-- a(n) = Max over k = 1..n of the convolution sums (a(0) = 0, the empty maximum). -/
def a (n : ℕ) : ℕ := (Icc 1 n).sup (conv n)

theorem main :
    (∀ n : ℕ, 1 ≤ n →
      (a n : ℚ) = ((n : ℚ) * (13 + 3 * (-1) ^ n + 24 * n + 14 * (n : ℚ) ^ 2)) / 48) ∧
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) / (n : ℝ) ^ 3) Filter.atTop (nhds (7 / 24)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) *
        ((1 - PowerSeries.X) ^ 4 * (1 + PowerSeries.X) ^ 2) =
      PowerSeries.X * (1 + 3 * PowerSeries.X + 2 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3)) ∧
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 2 * a (n - 1) + a (n - 2) - 4 * a (n - 3) + a (n - 4)
      + 2 * a (n - 5) - a (n - 6)) := by
  sorry

end OMA.S_oeis_a294172
