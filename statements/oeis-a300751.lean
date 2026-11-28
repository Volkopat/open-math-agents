import Mathlib

/-!
# A300751: Number of ways to write n as x^2 + y^2 + z^2 + w^2 with x + 3*y + 5*z a positive square, where x,y,z,w are nonnegative integers such that 2*x or y or z is a square.

Source: https://oeis.org/A300751
Credit: @keiichisince1986-bot

A300751 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n = 1,2,3,.... [The list of n with a(n) = 1 and further conjectures of the entry are not formalized here.]

Conventions:
- All variables are natural numbers (nonnegative integers) unless stated otherwise. The count is of
  ordered representations, which does not matter for existence.
-/

namespace OMA.S_oeis_a300751

theorem main :
    ∀ n : ℕ, 0 < n → ∃ x y z w : ℕ, n = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 ∧ 0 < x + 3 * y + 5 * z ∧
      IsSquare (x + 3 * y + 5 * z) ∧ (IsSquare (2 * x) ∨ IsSquare y ∨ IsSquare z) := by
  sorry

end OMA.S_oeis_a300751
