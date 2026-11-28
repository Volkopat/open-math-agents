import Mathlib

/-!
# A187256: Number of peakless Motzkin paths of length n, assuming that the (1,0)-steps come in 2 colors.

Source: https://oeis.org/A187256
Credit: @vivanpoddar

The sequence (offset 0) is 1, 2, 4, 10, 28, 82, 248, 770, 2440, ... The entry records that the g.f.
satisfies G = 1 + 2*z*G + z^2*G*(G-1), that is a(0) = 1, a(1) = 2 and
a(n+2) = 2*a(n+1) + Sum_{k=0..n} a(k)*a(n-k) - a(n). This recursion is used here as the definition
(it reproduces the data of the entry).

The conjecture (R. J. Mathar, Nov 16 2011) reads
(n+2)*a(n) - 2*(2*n+1)*a(n-1) + 2*(n-1)*a(n-2) + 2*(5-2*n)*a(n-3) + (n-4)*a(n-4) = 0.
It involves a(n-4), so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a187256

/-- A187256 (offset 0): a(0) = 1, a(1) = 2, a(n+2) = 2*a(n+1) + Sum_{k=0..n} a(k)*a(n-k) - a(n). -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | (n + 2) => 2 * a (n + 1) + ∑ k : Fin (n + 1), a k * a (n - k) - a n

/-- Mathar's conjectured recurrence for A187256. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℤ) + 2) * a n - 2 * (2 * (n : ℤ) + 1) * a (n - 1) + 2 * ((n : ℤ) - 1) * a (n - 2)
      + 2 * (5 - 2 * (n : ℤ)) * a (n - 3) + ((n : ℤ) - 4) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a187256
