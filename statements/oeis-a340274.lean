import Mathlib

/-!
# A340274: Number of ways to write n as x + y + z with x, y, z positive integers such that 3*x^2*y^2 + 5*y^2*z^2 + 8*z^2*x^2 is a square.

Source: https://oeis.org/A340274
Credit: @keiichisince1986-bot

A340274 is the sequence `a(n)` named in the title. The entry states:
Conjecture 1: a(n) > 0 for all n > 2. [Further conjectures of the entry are not formalized here.]

Conventions:
- `(x, y, z)` is an ordered triple of positive integers; a square is `IsSquare`.
-/

namespace OMA.S_oeis_a340274

theorem main :
    ∀ n : ℕ, 2 < n → ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = n ∧
      IsSquare (3 * x ^ 2 * y ^ 2 + 5 * y ^ 2 * z ^ 2 + 8 * z ^ 2 * x ^ 2) := by
  sorry

end OMA.S_oeis_a340274
