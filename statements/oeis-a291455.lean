import Mathlib

/-!
# A291455: Number of ways to write 2*n+1 as x^2 + y^2 + z^2 + w^2 with x,y,z,w nonnegative integers such that x + 3*y + 5*z + 7*w, x^3 + 3*y^3 + 5*z^3 + 7*w^3 and x^7 + 3*y^7 + 5*z^7 + 7*w^7 are all prime.

Source: https://oeis.org/A291455
Credit: @keiichisince1986-bot

A291455 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 for all n = 0,1,2,.... [The list of n with a(n) = 1 and further conjectures of the entry are not formalized here.]

Conventions:
- All variables are natural numbers (nonnegative integers) unless stated otherwise. The count is of
  ordered representations, which does not matter for existence.
-/

namespace OMA.S_oeis_a291455

theorem main :
    ∀ n : ℕ, ∃ x y z w : ℕ, 2 * n + 1 = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 ∧
      (x + 3 * y + 5 * z + 7 * w).Prime ∧ (x ^ 3 + 3 * y ^ 3 + 5 * z ^ 3 + 7 * w ^ 3).Prime ∧
      (x ^ 7 + 3 * y ^ 7 + 5 * z ^ 7 + 7 * w ^ 7).Prime := by
  sorry

end OMA.S_oeis_a291455
