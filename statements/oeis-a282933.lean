import Mathlib

/-!
# A282933: Number of ways to write n as x^4 + y^2 + z^2 + w^2 with x,y,z nonnegative integers and w a positive integer such that 8*y^2 - 8*y*z + 9*z^2 is a square.

Source: https://oeis.org/A282933
Credit: @keiichisince1986-bot

A282933 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 for all n > 0. [Only the claim a(n) > 0 is formalized here; the list of n with a(n) = 1 and the other parts are
not.]

Conventions:
- All variables are natural numbers (nonnegative integers) unless stated otherwise; `IsSquare` is
  Mathlib's. The representation is ordered, which does not matter for existence.
- Expressions with a subtraction are computed in `ℤ`; a negative integer is never a square.
-/

namespace OMA.S_oeis_a282933

theorem main :
    ∀ n : ℕ, 0 < n → ∃ x y z w : ℕ, 0 < w ∧ n = x ^ 4 + y ^ 2 + z ^ 2 + w ^ 2 ∧
      IsSquare (8 * y ^ 2 - 8 * y * z + 9 * z ^ 2 : ℤ) := by
  sorry

end OMA.S_oeis_a282933
