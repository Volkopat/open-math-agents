import Mathlib

/-!
# A141351: Mathar's recurrence for Catalan(n) + 1 - 0^n

Source: https://oeis.org/A141351
Credit: @ivillar

A141351 (offset 0) is a(n) = C(n) + 1 - 0^n, where C(n) = A000108(n) is the n-th Catalan number,
with data 1, 2, 3, 6, 15, 43, 133, 430, ...; its g.f. is c(x) + x/(1-x).
Conjecture (R. J. Mathar, Oct 15 2014):
(n+1)*a(n) + 2*(-3*n+1)*a(n-1) + (9*n-13)*a(n-2) + 2*(-2*n+5)*a(n-3) = 0.

Formalization notes.
* `catalan n` is Mathlib's n-th Catalan number (A000108), and `0 ^ 0 = 1`, so a(0) = 1 and
  a(n) = C(n) + 1 for n ≥ 1. The terms are computed in ℤ.
* The source gives no range. At the first index where all four terms exist, n = 3, the left
  side equals 4*6 - 16*3 + 14*2 - 2*1 = 2 (the 0^n correction at a(0) breaks it), so the
  recurrence is stated for every n ≥ 4, from which point on it is claimed to hold.
-/

namespace OMA.S_oeis_a141351

/-- A141351: a(n) = C(n) + 1 - 0^n. -/
def a (n : ℕ) : ℤ := (catalan n : ℤ) + 1 - 0 ^ n

/-- Mathar's recurrence, for every n ≥ 4. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℤ) + 1) * a n + 2 * (-3 * (n : ℤ) + 1) * a (n - 1) + (9 * (n : ℤ) - 13) * a (n - 2) +
      2 * (-2 * (n : ℤ) + 5) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a141351
