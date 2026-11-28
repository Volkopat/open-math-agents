import Mathlib

/-!
# A141353: Mathar's recurrence for Catalan(n) + 2^n - 0^n

Source: https://oeis.org/A141353
Credit: @ivillar

A141353 (offset 0) is a(n) = Catalan(n) + 2^n - 0^n, with data 1, 3, 6, 13, 30, 74, 196, ...;
its g.f. is c(x) + 2x/(1-2x), where c(x) is the g.f. of A000108.
Conjecture (R. J. Mathar, Nov 15 2012):
(n+1)*a(n) + 2*(-4*n+1)*a(n-1) + 4*(5*n-7)*a(n-2) + 8*(-2*n+5)*a(n-3) = 0.

Formalization notes.
* `catalan n` is Mathlib's n-th Catalan number (A000108), and `0 ^ 0 = 1`, so a(0) = 1 and
  a(n) = Catalan(n) + 2^n for n ≥ 1. The terms are computed in ℤ.
* The source gives no range. At the first index where all four terms exist, n = 3, the left
  side equals 4*13 - 22*6 + 32*3 - 8*1 = 8 (the 0^n correction at a(0) breaks it), so the
  recurrence is stated for every n ≥ 4, from which point on it is claimed to hold.
-/

namespace OMA.S_oeis_a141353

/-- A141353: a(n) = Catalan(n) + 2^n - 0^n. -/
def a (n : ℕ) : ℤ := (catalan n : ℤ) + 2 ^ n - 0 ^ n

/-- Mathar's recurrence, for every n ≥ 4. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℤ) + 1) * a n + 2 * (-4 * (n : ℤ) + 1) * a (n - 1) + 4 * (5 * (n : ℤ) - 7) * a (n - 2) +
      8 * (-2 * (n : ℤ) + 5) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a141353
