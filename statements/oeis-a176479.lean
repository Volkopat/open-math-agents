import Mathlib.Combinatorics.Enumerative.Schroder

/-!
# A176479: a(n) = (n+1)*A001003(n).

Source: https://oeis.org/A176479
Credit: @vivanpoddar

The sequence (offset 0) is 1, 2, 9, 44, 225, 1182, 6321, ..., where A001003 = 1, 1, 3, 11, 45, 197, ...
are the little Schroeder numbers.

Conventions:
* Mathlib's `Nat.smallSchroder` is 1, 1, 1, 3, 11, 45, 197, ... (it starts one index earlier),
  so A001003(n) = `Nat.smallSchroder (n + 1)`.
* The conjecture (R. J. Mathar, Dec 03 2014) reads
  n*(n-1)*a(n) - 3*(2*n-1)*(n-1)*a(n-1) + n*(n-2)*a(n-2) = 0.
  It involves a(n-2), so it is stated for n >= 2, over the integers.
-/

namespace OMA.S_oeis_a176479

/-- A176479 (offset 0): a(n) = (n+1)*A001003(n). -/
def a (n : ℕ) : ℤ :=
  ((n : ℤ) + 1) * (Nat.smallSchroder (n + 1) : ℤ)

/-- Mathar's conjectured recurrence for A176479. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    (n : ℤ) * ((n : ℤ) - 1) * a n - 3 * (2 * (n : ℤ) - 1) * ((n : ℤ) - 1) * a (n - 1)
      + (n : ℤ) * ((n : ℤ) - 2) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a176479
