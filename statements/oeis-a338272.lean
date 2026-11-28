import Mathlib

/-!
# Zhi-Wei Sun's conjecture on restricted sums of four squares (OEIS A338272)

Source: https://oeis.org/A338272
Credit: @yuka30240

The sequence counts representations for the coefficient pair (1, 32).
Sun's conjecture asserts existence for each of the sixteen pairs below.
-/

namespace OMA.S_oeis_a338272

/-- The ordered coefficient pairs in Sun's conjecture. -/
def coefficientPairs : Finset (ℤ × ℤ) :=
  {(1, -2), (1, 2), (1, 10), (1, 32), (2, -1), (2, 10), (2, 14), (2, 16),
   (2, 36), (3, 4), (4, -2), (4, 18), (6, 18), (8, 9), (9, 10), (16, -2)}

theorem main : ∀ n : ℕ, 0 < n → n ≡ 1 [MOD 4] →
    ∀ a b : ℤ, (a, b) ∈ coefficientPairs →
      ∃ x y z w : ℕ, n = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 ∧
        IsSquare (a * x * y + b * z * w) := by
  sorry

end OMA.S_oeis_a338272
