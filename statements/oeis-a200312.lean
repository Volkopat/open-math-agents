import Mathlib

/-!
# A200312: a(n) = A000108(n) * A006130(n)

Source: https://oeis.org/A200312
Credit: @sntntHb

A200312 is the product of the Catalan number `A000108(n)` and `A006130(n)`, where
`A006130(0) = A006130(1) = 1` and `A006130(n) = A006130(n-1) + 3*A006130(n-2)`.

Formalizes R. J. Mathar's conjectured recurrence (OEIS A200312, Nov 17 2011):
`n*(n+1)*a(n) - 2*n*(2*n-1)*a(n-1) - 12*(2*n-1)*(2*n-3)*a(n-2) = 0`,
stated for every `n >= 2` (offset 0).
-/

namespace OMA.S_oeis_a200312

/-- A006130: `1, 1, 4, 7, 19, ...` with `b(n) = b(n-1) + 3*b(n-2)`. -/
def b : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => b (n + 1) + 3 * b n

/-- A200312: `a(n) = catalan n * b n`. -/
def a (n : ℕ) : ℕ := catalan n * b n

/-- Mathar's conjectured second-order recurrence, for every `n >= 2`. -/
theorem main :
    ∀ n : ℕ, 2 ≤ n →
      (n : ℤ) * ((n : ℤ) + 1) * (a n : ℤ) -
        2 * (n : ℤ) * (2 * (n : ℤ) - 1) * (a (n - 1) : ℤ) -
        12 * (2 * (n : ℤ) - 1) * (2 * (n : ℤ) - 3) * (a (n - 2) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a200312
