import Mathlib

/-!
# A338139: Number of ways to write n as x^2 + y^2 + z^2 + w^2 with x^2 + 26*y^2 - 11*x*y a power of two (including 2^0 = 1), where x, y, z, w are nonnegative integers with z <= w.

Source: https://oeis.org/A338139
Credit: @keiichisince1986-bot

A338139 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 0. [The further claim for n congruent to 1 or 2 modulo 4 is not
formalized here.]

Conventions:
- All variables are natural numbers (nonnegative integers) unless stated otherwise; `IsSquare` is
  Mathlib's. The representation is ordered, which does not matter for existence.
- Expressions with a subtraction are computed in `ℤ`; a power of two is positive.
-/

namespace OMA.S_oeis_a338139

theorem main :
    ∀ n : ℕ, 0 < n → ∃ x y z w k : ℕ, z ≤ w ∧ n = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 ∧
      (x ^ 2 + 26 * y ^ 2 - 11 * x * y : ℤ) = 2 ^ k := by
  sorry

end OMA.S_oeis_a338139
