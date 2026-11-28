import Mathlib

/-!
# A099976: Bisection of A000984.

Source: https://oeis.org/A099976

Offset 0, with a(n) = binomial(4n+2, 2n+1) (formula of Emeric Deutsch; data 2, 20, 252, 3432, ...).
Formalizes the D-finite recurrence stated by R. J. Mathar (Jul 11 2024):
n (2n+1) a(n) - 2 (4n-1) (4n+1) a(n-1) = 0, for n >= 1. The identity is taken in ℤ.
-/

namespace OMA.S_oeis_a099976

/-- A099976: `a n = binomial(4n+2, 2n+1)`, the odd-indexed central binomial coefficients. -/
def a (n : ℕ) : ℕ := Nat.choose (4 * n + 2) (2 * n + 1)

/-- Mathar's D-finite recurrence for A099976. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (n : ℤ) * (2 * n + 1) * a n - 2 * (4 * (n : ℤ) - 1) * (4 * n + 1) * a (n - 1) = 0 := by
  sorry

end OMA.S_oeis_a099976
