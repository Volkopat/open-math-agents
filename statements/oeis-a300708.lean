import Mathlib

/-!
# A300708: Number of ways to write n as x^2 + y^2 + z^2 + w^2 with x,y,z,w nonnegative integers and z <= w such that x or y is a square and x - y is also a square.

Source: https://oeis.org/A300708
Credit: @keiichisince1986-bot

A300708 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n >= 0. [Only the claim a(n) > 0 is formalized here; the list of n with a(n) = 1 and the other parts are
not.]

Conventions:
- All variables are natural numbers (nonnegative integers) unless stated otherwise; `IsSquare` is
  Mathlib's. The representation is ordered, which does not matter for existence.
- Expressions with a subtraction are computed in `ℤ`; a negative integer is never a square.
-/

namespace OMA.S_oeis_a300708

theorem main :
    ∀ n : ℕ, ∃ x y z w : ℕ, z ≤ w ∧ n = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 ∧ (IsSquare x ∨ IsSquare y) ∧
      IsSquare (x - y : ℤ) := by
  sorry

end OMA.S_oeis_a300708
