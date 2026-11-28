import Mathlib

/-!
# A338019: Number of ways to write n as x^2 + y^2 + z^2 + w^2 with 3*x + 10*y + 36*z a positive square, where x, y, z, w are nonnegative integers.

Source: https://oeis.org/A338019
Credit: @keiichisince1986-bot

A338019 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 if n is not divisible by 8. [The second claim, describing exactly when a(n) = 0, is
not formalized here.]

Conventions:
- All variables are natural numbers (nonnegative integers) unless stated otherwise; `(…).IsSquare` is
  Mathlib's `IsSquare`. The representation is ordered, which does not matter for existence.
-/

namespace OMA.S_oeis_a338019

theorem main :
    ∀ n : ℕ, ¬ 8 ∣ n → ∃ x y z w : ℕ, n = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 ∧
      0 < 3 * x + 10 * y + 36 * z ∧ IsSquare (3 * x + 10 * y + 36 * z) := by
  sorry

end OMA.S_oeis_a338019
