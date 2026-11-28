import Mathlib

/-!
# A271778: Number of ordered ways to write n as x^2 + y^2 + z^2 + w^2 with x,y,z,w nonnegative integers and x^2 + 3*y^2 + 5*z^2 - 8*w^2 a square.

Source: https://oeis.org/A271778
Credit: @keiichisince1986-bot

A271778 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 for all n = 0,1,2,... [Only the first claim of part (i), a(n) > 0, is formalized here; the list of n with a(n) = 1
and the other parts are not.]

Conventions:
- All variables are natural numbers (nonnegative integers) unless stated otherwise; `(…).IsSquare` is
  Mathlib's `IsSquare`. The representation is ordered, which does not matter for existence.
- The expression may be negative, so it is computed in `ℤ`; a negative integer is never a square.
-/

namespace OMA.S_oeis_a271778

theorem main :
    ∀ n : ℕ, ∃ x y z w : ℕ, n = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 ∧
      IsSquare (x ^ 2 + 3 * y ^ 2 + 5 * z ^ 2 - 8 * w ^ 2 : ℤ) := by
  sorry

end OMA.S_oeis_a271778
