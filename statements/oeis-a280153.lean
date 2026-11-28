import Mathlib

/-!
# A280153: Number of ways to write n as x^3 + 2*y^3 + z^2 + 4^k, where x is a positive integer and y,z,k are nonnegative integers.

Source: https://oeis.org/A280153
Credit: @keiichisince1986-bot

A280153 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 for all n > 1. [Only the claim a(n) > 0 is formalized here; the list of n with a(n) = 1 and the other parts are
not.]

Conventions:
- All variables are natural numbers (nonnegative integers) unless stated otherwise; `IsSquare` is
  Mathlib's. The representation is ordered, which does not matter for existence.
-/

namespace OMA.S_oeis_a280153

theorem main :
    ∀ n : ℕ, 1 < n → ∃ x y z k : ℕ, 0 < x ∧ n = x ^ 3 + 2 * y ^ 3 + z ^ 2 + 4 ^ k := by
  sorry

end OMA.S_oeis_a280153
