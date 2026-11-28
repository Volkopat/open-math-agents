import Mathlib

/-!
# OEIS A079291: squares of Pell numbers in Pythagorean triples `(X, Y, Y + 1)`

Source: https://oeis.org/A079291
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (OEIS entry): for a primitive Pythagorean triple `(X, Y, Z = Y + 1)` with
`X = A001333(n)`, `n > 1`, if `n` is even then `Y` is a square Pell number, and if `n` is odd then
`Z` is a square Pell number. (E.g. `(3, 4, 5)`, `(7, 24, 25)`, `(17, 144, 145)`.)

Conventions:
* A001333: `1, 1, 3, 7, 17, 41, …` (`A(0) = A(1) = 1`, `A(n) = 2A(n-1) + A(n-2)`); Pell numbers:
  `P(0) = 0, P(1) = 1`, `P(n) = 2P(n-1) + P(n-2)`.
* `X = A(n)` is odd, so the triple is `(X, (X² - 1)/2, (X² + 1)/2)`, which is primitive.
  "`Y` (resp. `Z`) is a square Pell number" means it equals `P(m)²` for some `m`.
-/

namespace OMA.S_oeis_a079291

/-- A001333. -/
def A : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * A (n + 1) + A n

/-- Pell numbers. -/
def P : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * P (n + 1) + P n

/-- The parity rule for square Pell numbers. -/
theorem main : ∀ n : ℕ, 1 < n →
    (Even n → ∃ m, (A n ^ 2 - 1) / 2 = P m ^ 2) ∧ (Odd n → ∃ m, (A n ^ 2 + 1) / 2 = P m ^ 2) := by
  sorry

end OMA.S_oeis_a079291
