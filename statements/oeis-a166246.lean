import Mathlib

/-!
# A166246: Primes representable as the sum of two rational cubes

Source: https://oeis.org/A166246

Conjecture (J. J. Sylvester; implied by the Birch and Swinnerton-Dyer conjecture):
Every prime number `p` congruent to `4`, `7`, or `8` modulo `9` can be written as
the sum of two rational cubes, `p = x ^ 3 + y ^ 3` with `x, y ∈ ℚ`.

Conventions:
- First terms of A166246: `2, 7, 13, 17, 19, 31, 37, 43, 53, 61, ...`.
- Examples: `7 = 2^3 + (-1)^3`, `13 = (7/3)^3 + (2/3)^3`, `17 = (18/7)^3 + (-1/7)^3`.
-/

namespace OMA.S_oeis_a166246

/-- Conjecture (Sylvester / BSD): every prime `p ≡ 4, 7, or 8 (mod 9)` is the sum of
two rational cubes. -/
theorem main :
    ∀ p : ℕ, Nat.Prime p →
      (p % 9 = 4 ∨ p % 9 = 7 ∨ p % 9 = 8) →
      ∃ x y : ℚ, x ^ 3 + y ^ 3 = (p : ℚ) := by
  sorry

end OMA.S_oeis_a166246
