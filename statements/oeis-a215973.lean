import Mathlib

/-!
# A215973: a(0) = 1, for n > 0: a(n) = Sum_{k=0..n-1} a(k) * (1 + a(n-1-k)).

Source: https://oeis.org/A215973
Credit: @vivanpoddar

The sequence (offset 0) is 1, 2, 7, 28, 122, 565, 2735, 13682, 70188, ..., defined by the recursion of
the title.

The conjecture (R. J. Mathar, Jun 14 2016) reads
(n+1)*a(n) + 3*(-3*n+1)*a(n-1) + 4*(5*n-7)*a(n-2) + 2*(-8*n+19)*a(n-3) + 2*(2*n-7)*a(n-4) = 0.
It involves a(n-4), so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a215973

/-- A215973 (offset 0): a(0) = 1 and a(n+1) = Sum_{k=0..n} a(k) * (1 + a(n-k)). -/
def a : ℕ → ℤ
  | 0 => 1
  | (n + 1) => ∑ k : Fin (n + 1), a k * (1 + a (n - k))

/-- Mathar's conjectured recurrence for A215973. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℤ) + 1) * a n + 3 * (-3 * (n : ℤ) + 1) * a (n - 1) + 4 * (5 * (n : ℤ) - 7) * a (n - 2)
      + 2 * (-8 * (n : ℤ) + 19) * a (n - 3) + 2 * (2 * (n : ℤ) - 7) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a215973
