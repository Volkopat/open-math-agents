import Mathlib

/-!
# A295293: Barker's recurrence

Source: https://oeis.org/A295293
Credit: @ivillar

Wesley Ivan Hurt's sequence: the sum of the products of the smaller and larger parts of the partitions of n into two parts with the larger part even,
a(n) = Sum_{i=1..floor(n/2)} i * (n - i) * ((n-i+1) mod 2) (offset 1; data 0, 0, 2, 4, 4, 8, 18, 28, 26, 40, ...).
Colin Barker conjectured (Nov 20 2017)
a(n) = a(n-1) + 3*a(n-4) - 3*a(n-5) - 3*a(n-8) + 3*a(n-9) + a(n-12) - a(n-13) for n > 13.

Status: known result ('Conjectures verified by Robert Israel, Dec 05 2017' in the entry).

Formalization notes:
* The recurrence is stated over ℤ.
* Barker's generating function 2*x^3*(1 + x + 2*x^3 + 2*x^4 + 2*x^5 - x^6 + x^7) / ((1 - x)^4*(1 + x)^3*(1 + x^2)^3) is the rational function determined by this
  recurrence and the initial terms; it is not restated.
-/

namespace OMA.S_oeis_a295293

/-- A295293: `a(n) = Sum_{i=1..floor(n/2)} i * (n - i) * ((n-i+1) mod 2)`. -/
def a (n : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 (n / 2), i * (n - i) * ((n - i + 1) % 2)

/-- Barker's conjectured recurrence for A295293, for every `n > 13`. -/
theorem main : ∀ n : ℕ, 13 < n →
    (a n : ℤ) = a (n - 1) + 3 * a (n - 4) - 3 * a (n - 5) - 3 * a (n - 8) + 3 * a (n - 9) +
      a (n - 12) - a (n - 13) := by
  sorry

end OMA.S_oeis_a295293
