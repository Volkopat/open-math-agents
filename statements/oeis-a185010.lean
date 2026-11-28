import Mathlib

/-!
# A185010: a(n) = A000108(n) * A015518(n+1)

Source: https://oeis.org/A185010
Credit: @sntntHb

A185010 is the product of the Catalan number `A000108(n)` and `A015518(n+1)`, where
`A015518(0) = 0`, `A015518(1) = 1` and `A015518(n) = 2*A015518(n-1) + 3*A015518(n-2)`.

Formalizes R. J. Mathar's conjectured recurrence (OEIS A185010, Oct 08 2016):
`n*(n+1)*a(n) - 4*n*(2*n-1)*a(n-1) - 12*(2*n-1)*(2*n-3)*a(n-2) = 0`,
stated for every `n >= 2` (offset 0).
-/

namespace OMA.S_oeis_a185010

/-- A015518: `0, 1, 2, 7, 20, ...` with `b(n) = 2*b(n-1) + 3*b(n-2)`. -/
def b : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * b (n + 1) + 3 * b n

/-- A185010: `a(n) = catalan n * b (n + 1)`. -/
def a (n : ℕ) : ℕ := catalan n * b (n + 1)

/-- Mathar's conjectured second-order recurrence, for every `n >= 2`. -/
theorem main :
    ∀ n : ℕ, 2 ≤ n →
      (n : ℤ) * ((n : ℤ) + 1) * (a n : ℤ) -
        4 * (n : ℤ) * (2 * (n : ℤ) - 1) * (a (n - 1) : ℤ) -
        12 * (2 * (n : ℤ) - 1) * (2 * (n : ℤ) - 3) * (a (n - 2) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a185010
