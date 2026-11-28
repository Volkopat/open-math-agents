import Mathlib

/-!
# A338094: Number of ways to write 2*n + 1 as x^2 + y^2 + z^2 + w^2 with x + y a positive power of two, where x, y, z, w are nonnegative integers with x <= y and z <= w.

Source: https://oeis.org/A338094
Credit: @keiichisince1986-bot

A338094 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 0. [The further claim with powers of 4 is not formalized here.]

Conventions:
- All variables are natural numbers (nonnegative integers) unless stated otherwise. The count is of
  ordered representations, which does not matter for existence.
- A positive power of two is `2^k` with `k ≥ 1`.
-/

namespace OMA.S_oeis_a338094

theorem main :
    ∀ n : ℕ, 0 < n → ∃ x y z w k : ℕ, x ≤ y ∧ z ≤ w ∧ 1 ≤ k ∧ x + y = 2 ^ k ∧
      2 * n + 1 = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 := by
  sorry

end OMA.S_oeis_a338094
