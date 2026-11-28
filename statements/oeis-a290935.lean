import Mathlib

/-!
# A290935: Number of ways to write 2*n+1 as x^2 + y^2 + z^2 + w^2 with x,y,z,w nonnegative integers such that p = x^2 + 3*y^2 + 5*z^2 + 7*w^2 and p - 2 are twin prime.

Source: https://oeis.org/A290935
Credit: @keiichisince1986-bot

A290935 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n = 0,1,2,... [The list of n with a(n) = 1 is not formalized here.]

Conventions:
- All variables are natural numbers (nonnegative integers) unless stated otherwise; `(…).IsSquare` is
  Mathlib's `IsSquare`. The representation is ordered, which does not matter for existence.
- `p` and `p - 2` twin prime means both are prime; `p ≥ 2`, so `p - 2` is exact when it matters (a truncated
  `0` is not prime).
-/

namespace OMA.S_oeis_a290935

theorem main :
    ∀ n : ℕ, ∃ x y z w : ℕ, 2 * n + 1 = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 ∧
      (x ^ 2 + 3 * y ^ 2 + 5 * z ^ 2 + 7 * w ^ 2).Prime ∧ (x ^ 2 + 3 * y ^ 2 + 5 * z ^ 2 + 7 * w ^ 2 - 2).Prime := by
  sorry

end OMA.S_oeis_a290935
