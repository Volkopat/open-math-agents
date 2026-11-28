import Mathlib

/-!
# A006231: Mathar's recurrence

Source: https://oeis.org/A006231 (OEIS Foundation, CC BY-SA 4.0).

a(n) = Sum_{k=2..n} n(n-1)...(n-k+1)/k, with offset 1. R. J. Mathar (Aug 06 2013)
conjectured that
a(n) + (-n-2)*a(n-1) + (3n-2)*a(n-2) + 3*(-n+2)*a(n-3) + (n-3)*a(n-4) = 0.
The recurrence involves a(n-4), so it is stated for n >= 5, where every index
is at least the offset 1.

The falling factorial n(n-1)...(n-k+1) is `Nat.descFactorial n k`. It equals
k! * binomial(n, k), so k divides it and the natural-number division is exact.
-/

namespace OMA.S_oeis_a006231

/-- `a n = Sum_{k=2..n} n(n-1)...(n-k+1)/k`. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 2 n, n.descFactorial k / k

theorem main : ∀ n : ℕ, 5 ≤ n →
    (a n : ℤ) + (-(n : ℤ) - 2) * a (n - 1) + (3 * (n : ℤ) - 2) * a (n - 2)
      + 3 * (-(n : ℤ) + 2) * a (n - 3) + ((n : ℤ) - 3) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a006231
