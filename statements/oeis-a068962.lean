import Mathlib

/-!
# A068962: Number of successive terms of A028356 that add to n; or length of n-th term of A028355.

Source: https://oeis.org/A068962
Credit: @agchua

Chai Wah Wu (Apr 18 2024), in the formula section of A068962:
  Conjectures from Chai Wah Wu, Apr 18 2024: (Start)
  a(n) = a(n-1) + a(n-15) - a(n-16) for n > 16.
  G.f.: x*(x^14 + x^10 + x^9 - x^8 + 2*x^7 - x^6 + x^5 + x^4 + 1)/(x^16 - x^15 - x + 1). (End)
This file states both parts: the recurrence for n > 16 (offset 1, so all indices are terms), and
the g.f. as an identity of formal power series over ℚ,
(∑ a(n) X^n) * (X^16 - X^15 - X + 1) = X * (X^14 + X^10 + X^9 - X^8 + 2X^7 - X^6 + X^5 + X^4 + 1);
its coefficient of X^0 is a(0), which the definition below makes 0 (no terms add to 0), in
accordance with the factor x of the g.f. (offset 1).
Definition: A028356 (offset 0) is the periodic sequence 1, 2, 3, 4, 3, 2, 1, 2, 3, 4, 3, 2, ...
with period 6, written c(i) below. Let S(m) be the sum of its first m terms. A028356 splits into
consecutive blocks with sums 1, 2, 3, ... (the clock property: every triangular number is some
S(m)), and the n-th block consists of the terms after which the partial sum S(m) lies in
((n-1)n/2, n(n+1)/2]. So a(n) is the number of m with (n-1)n/2 < S(m) ≤ n(n+1)/2; since
S(m) ≥ m, all such m lie in 0 .. n(n+1)/2.
-/

namespace OMA.S_oeis_a068962

/-- A028356 (offset 0): 1, 2, 3, 4, 3, 2, repeated with period 6. -/
def c (i : ℕ) : ℕ := [1, 2, 3, 4, 3, 2].getD (i % 6) 0

/-- The sum of the first m terms of A028356. -/
def S (m : ℕ) : ℕ := ∑ i ∈ Finset.range m, c i

/-- A068962: the number of m with (n-1)n/2 < S(m) ≤ n(n+1)/2, i.e. the number of terms in the
n-th block of A028356 (the block whose terms add to n). -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n * (n + 1) / 2 + 1)).filter
    (fun m => (n - 1) * n / 2 < S m ∧ S m ≤ n * (n + 1) / 2)).card

/-- Chai Wah Wu's conjectures: a(n) = a(n-1) + a(n-15) - a(n-16) for n > 16, and the g.f.
x(x^14 + x^10 + x^9 - x^8 + 2x^7 - x^6 + x^5 + x^4 + 1)/(x^16 - x^15 - x + 1). -/
theorem main : (∀ n : ℕ, 17 ≤ n → (a n : ℤ) = a (n - 1) + a (n - 15) - a (n - 16)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) *
        (PowerSeries.X ^ 16 - PowerSeries.X ^ 15 - PowerSeries.X + 1) =
      PowerSeries.X * (PowerSeries.X ^ 14 + PowerSeries.X ^ 10 + PowerSeries.X ^ 9 -
        PowerSeries.X ^ 8 + 2 * PowerSeries.X ^ 7 - PowerSeries.X ^ 6 + PowerSeries.X ^ 5 +
        PowerSeries.X ^ 4 + 1) := by
  sorry

end OMA.S_oeis_a068962
