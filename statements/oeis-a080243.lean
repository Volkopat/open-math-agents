import Mathlib.Combinatorics.Enumerative.Schroder

/-!
# A080243: Signed super-Catalan or little Schroeder numbers.

Source: https://oeis.org/A080243
Credit: @vivanpoddar

The sequence (offset 0) is 1, -1, 3, -11, 45, -197, 903, -4279, ...: the little Schroeder
numbers A001003 = 1, 1, 3, 11, 45, 197, ... with alternating signs, a(n) = (-1)^n * A001003(n).

Conventions:
* Mathlib's `Nat.smallSchroder` is 1, 1, 1, 3, 11, 45, 197, ... (it starts one index earlier),
  so A001003(n) = `Nat.smallSchroder (n + 1)`.
* The conjecture (R. J. Mathar, Nov 26 2012) reads
  (n+1)*a(n) + 3*(2*n-1)*a(n-1) + (n-2)*a(n-2) = 0.
  It involves a(n-2), so it is stated for n >= 2, over the integers.
-/

namespace OMA.S_oeis_a080243

/-- A080243 (offset 0): the little Schroeder numbers with alternating signs. -/
def a (n : ℕ) : ℤ :=
  (-1) ^ n * (Nat.smallSchroder (n + 1) : ℤ)

/-- Mathar's conjectured recurrence for A080243. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    ((n : ℤ) + 1) * a n + 3 * (2 * (n : ℤ) - 1) * a (n - 1) + ((n : ℤ) - 2) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a080243
