import Mathlib

/-!
# A192480: a(n) = n + A000108(n-1) for n > 1; a(0) = 0, a(1) = 1

Source: https://oeis.org/A192480
Credit: @sntntHb

Formalizes R. J. Mathar's conjectured recurrence (OEIS A192480, Jun 14 2016):
`n*(3*n^2-16*n+19)*a(n) + (-15*n^3+95*n^2-188*n+120)*a(n-1)
  + 2*(2*n-5)*(3*n^2-10*n+6)*a(n-2) = 0`.
With the stated initial terms the identity fails at `n = 2` and `n = 3`
(it involves the exceptional values `a(0)`, `a(1)`), so it is stated for every `n >= 4`.
-/

namespace OMA.S_oeis_a192480

/-- A192480: `a(0) = 0`, `a(1) = 1` and `a(n) = n + catalan (n - 1)` for `n > 1`. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => (n + 2) + catalan (n + 1)

/-- Mathar's conjectured second-order recurrence, for every `n >= 4`. -/
theorem main :
    ∀ n : ℕ, 4 ≤ n →
      (n : ℤ) * (3 * (n : ℤ) ^ 2 - 16 * (n : ℤ) + 19) * (a n : ℤ) +
        (-15 * (n : ℤ) ^ 3 + 95 * (n : ℤ) ^ 2 - 188 * (n : ℤ) + 120) * (a (n - 1) : ℤ) +
        2 * (2 * (n : ℤ) - 5) * (3 * (n : ℤ) ^ 2 - 10 * (n : ℤ) + 6) * (a (n - 2) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a192480
