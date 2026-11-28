import Mathlib

/-!
# A139262: Mathar's recurrence for the number of two-element antichains in ordered trees

Source: https://oeis.org/A139262
Credit: @ivillar

A139262 (offset 0) is the total number of two-element antichains over all ordered trees on n
edges; data 0, 0, 1, 8, 47, 244, 1186, 5536, ... The entry gives the closed formula
2*a(n) = (n+1)*A000984(n) - 4^n (J. M. Bergot, Feb 02 2013), where A000984(n) = binomial(2n, n)
is the central binomial coefficient.

Conjecture (R. J. Mathar, Feb 03 2013):
n*(n-2)*a(n) + 2*(-4*n^2+9*n-3)*a(n-1) + 8*(n-1)*(2*n-3)*a(n-2) = 0.
Robert Israel (Feb 02 2016) notes in the entry that it follows from Bergot's formula.

Formalization: a(n) is defined by Bergot's formula as an integer; the division by 2 is exact
((n+1)*binomial(2n, n) - 4^n is even). The recurrence is stated for every n ≥ 2, the range in
which a(n-2) is defined.
-/

namespace OMA.S_oeis_a139262

/-- a(n) = ((n+1)·binomial(2n, n) − 4^n)/2, Bergot's formula for A139262. -/
def a (n : ℕ) : ℤ := (((n : ℤ) + 1) * (Nat.centralBinom n : ℤ) - 4 ^ n) / 2

/-- Mathar's conjectured recurrence. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    (n : ℤ) * ((n : ℤ) - 2) * a n + 2 * (-4 * (n : ℤ) ^ 2 + 9 * (n : ℤ) - 3) * a (n - 1) +
      8 * ((n : ℤ) - 1) * (2 * (n : ℤ) - 3) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a139262
