import Mathlib

/-!
# A337082: Number of ways to write n as x^2 + y^2 + z^2 + w^2 with 2*x^2 + 4*y^2 - 7*x*y a power of two (including 2^0 = 1), where x, y, z, w are nonnegative integers with z <= w.

Source: https://oeis.org/A337082
Credit: @keiichisince1986-bot

A337082 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 0. [The further claim for n congruent to 1 or 2 modulo 4 is not
formalized here.]

Conventions:
- All variables are natural numbers (nonnegative integers) unless stated otherwise. The count is of
  ordered representations, which does not matter for existence.
- `2x^2 + 4y^2 - 7xy` is computed in `ℤ`; a power of two is `2^k` with `k ≥ 0`.
-/

namespace OMA.S_oeis_a337082

theorem main :
    ∀ n : ℕ, 0 < n → ∃ x y z w k : ℕ, z ≤ w ∧ n = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 ∧
      (2 * x ^ 2 + 4 * y ^ 2 - 7 * x * y : ℤ) = 2 ^ k := by
  sorry

end OMA.S_oeis_a337082
