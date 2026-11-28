import Mathlib

/-!
# A301891: Number of ways to write 2*n^2 as x^2 + y^2 + z^2 + w^2 with x,y,z,w nonnegative integers such that x + 3*y + 5*z + 15*w is a power of 4.

Source: https://oeis.org/A301891
Credit: @keiichisince1986-bot

A301891 is the sequence `a(n)` named in the title. The entry states:
Conjecture 1: a(n) > 0 for all n > 0. [The list of n with a(n) = 1 and further conjectures of the entry are not formalized here.]

Conventions:
- All variables are natural numbers (nonnegative integers) unless stated otherwise. The count is of
  ordered representations, which does not matter for existence.
- A power of `4` is `4^k` with `k ≥ 0`.
-/

namespace OMA.S_oeis_a301891

theorem main :
    ∀ n : ℕ, 0 < n → ∃ x y z w k : ℕ, 2 * n ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 ∧
      x + 3 * y + 5 * z + 15 * w = 4 ^ k := by
  sorry

end OMA.S_oeis_a301891
