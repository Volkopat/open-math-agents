import Mathlib

/-!
# A295292: Barker's recurrence

Source: https://oeis.org/A295292
Credit: @ivillar

Wesley Ivan Hurt's sequence: the sum of the products of the smaller and larger parts of the partitions of n into two parts with the larger part odd,
a(n) = Sum_{i=1..floor(n/2)} i * (n - i) * ((n-i) mod 2) (offset 1; data 0, 1, 0, 3, 6, 14, 10, 22, 34, 55, ...).
Colin Barker conjectured (Nov 20 2017)
a(n) = a(n-1) + 3*a(n-4) - 3*a(n-5) - 3*a(n-8) + 3*a(n-9) + a(n-12) - a(n-13) for n > 13.

Formalization notes:
* The recurrence is stated over ℤ.
* Barker's generating function x^2*(1 - x + 3*x^2 + 3*x^3 + 5*x^4 - x^5 + 3*x^6 + 3*x^7) / ((1 - x)^4*(1 + x)^3*(1 + x^2)^3) is the rational function determined by this
  recurrence and the initial terms; it is not restated.
-/

namespace OMA.S_oeis_a295292

/-- A295292: `a(n) = Sum_{i=1..floor(n/2)} i * (n - i) * ((n-i) mod 2)`. -/
def a (n : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 (n / 2), i * (n - i) * ((n - i) % 2)

/-- Barker's conjectured recurrence for A295292, for every `n > 13`. -/
theorem main : ∀ n : ℕ, 13 < n →
    (a n : ℤ) = a (n - 1) + 3 * a (n - 4) - 3 * a (n - 5) - 3 * a (n - 8) + 3 * a (n - 9) +
      a (n - 12) - a (n - 13) := by
  sorry

end OMA.S_oeis_a295292
