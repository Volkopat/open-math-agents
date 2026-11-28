import Mathlib

/-!
# A282562: Number of ways to write n as x^2 + y^2 + z^2 + w^2 with x,y,z,w nonnegative integers such that both 2*x - y and 9*z^2 + 666*z*w + w^2 are squares.

Source: https://oeis.org/A282562
Credit: @keiichisince1986-bot

A282562 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n = 0,1,2,.... [Only the claim a(n) > 0 is formalized here; the list of n with a(n) = 1 and the other parts are
not.]

Conventions:
- All variables are natural numbers (nonnegative integers) unless stated otherwise; `IsSquare` is
  Mathlib's. The representation is ordered, which does not matter for existence.
- Expressions with a subtraction are computed in `ℤ`; a negative integer is never a square.
-/

namespace OMA.S_oeis_a282562

theorem main :
    ∀ n : ℕ, ∃ x y z w : ℕ, n = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 ∧ IsSquare (2 * x - y : ℤ) ∧
      IsSquare (9 * z ^ 2 + 666 * z * w + w ^ 2) := by
  sorry

end OMA.S_oeis_a282562
