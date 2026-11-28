import Mathlib

/-!
# A282863: Number of ways to write n as x^2 + y^2 + z^2 + w^2 with x,y,z,w nonnegative integers such that 72*x^3 + (y-z)^3 is an even square.

Source: https://oeis.org/A282863
Credit: @keiichisince1986-bot

A282863 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 for any nonnegative integer n. [The further claims of the entry are not
formalized here.]

Conventions:
- All variables are natural numbers (nonnegative integers) unless stated otherwise; `(…).IsSquare` is
  Mathlib's `IsSquare`. The representation is ordered, which does not matter for existence.
- The expression is computed in `ℤ` (`y - z` may be negative). An even square is the square of an even
  integer `2m`.
-/

namespace OMA.S_oeis_a282863

theorem main :
    ∀ n : ℕ, ∃ x y z w : ℕ, n = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 ∧
      ∃ m : ℤ, (72 * x ^ 3 + (y - z) ^ 3 : ℤ) = (2 * m) ^ 2 := by
  sorry

end OMA.S_oeis_a282863
