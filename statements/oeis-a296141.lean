import Mathlib

/-!
# A296141: Barker's recurrence

Source: https://oeis.org/A296141
Credit: @ivillar

Wesley Ivan Hurt's sequence: the sum of the smaller parts of the partitions of n into two distinct parts with the larger part even,
a(n) = Sum_{i=1..floor((n-1)/2)} i * ((n-i+1) mod 2) (offset 1; data 0, 0, 1, 0, 1, 2, 4, 2, 4, 6, ...).
Colin Barker conjectured (Dec 06 2017) a(n) = a(n-1) + 2*a(n-4) - 2*a(n-5) - a(n-8) + a(n-9)
for n > 9.

Formalization notes:
* The recurrence is stated over ℤ.
* Barker's generating function x^3*(1 - x + x^2 + x^3) / ((1 - x)^3*(1 + x)^2*(1 + x^2)^2) is the rational function determined by this
  recurrence and the initial terms; it is not restated.
-/

namespace OMA.S_oeis_a296141

/-- A296141: `a(n) = Sum_{i=1..floor((n-1)/2)} i * ((n-i+1) mod 2)`. -/
def a (n : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 ((n - 1) / 2), i * ((n - i + 1) % 2)

/-- Barker's conjectured recurrence for A296141, for every `n > 9`. -/
theorem main : ∀ n : ℕ, 9 < n →
    (a n : ℤ) = a (n - 1) + 2 * a (n - 4) - 2 * a (n - 5) - a (n - 8) + a (n - 9) := by
  sorry

end OMA.S_oeis_a296141
