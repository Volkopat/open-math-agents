import Mathlib

/-!
# A273278: Number of ordered ways to write n as x^2 + y^2 + z^2 + w^2 with x,y,z,w nonnegative integers such that x^2*y^2 + 3*y^2*z^2 + 2*z^2*w^2 is a square.

Source: https://oeis.org/A273278
Credit: @keiichisince1986-bot

A273278 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n = 0,1,2,... [The list of n with a(n) = 1 is not formalized here.]

Conventions:
- All variables are natural numbers (nonnegative integers) unless stated otherwise; `(…).IsSquare` is
  Mathlib's `IsSquare`. The representation is ordered, which does not matter for existence.
-/

namespace OMA.S_oeis_a273278

theorem main :
    ∀ n : ℕ, ∃ x y z w : ℕ, n = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 ∧
      IsSquare (x ^ 2 * y ^ 2 + 3 * y ^ 2 * z ^ 2 + 2 * z ^ 2 * w ^ 2) := by
  sorry

end OMA.S_oeis_a273278
