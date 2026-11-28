import Mathlib

/-!
# A272084: Number of ordered ways to write n as x^2 + y^2 + z^2 + w^2 with 4*x^2 + 5*y^2 + 20*z*w a square, where x,y,z,w are nonnegative integers with z < w.

Source: https://oeis.org/A272084
Credit: @keiichisince1986-bot

A272084 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 for all n > 0. [Only the first claim of part (i), a(n) > 0, is formalized here; the list of n with a(n) = 1
and the other parts are not.]

Conventions:
- All variables are natural numbers (nonnegative integers) unless stated otherwise; `(…).IsSquare` is
  Mathlib's `IsSquare`. The representation is ordered, which does not matter for existence.
-/

namespace OMA.S_oeis_a272084

theorem main :
    ∀ n : ℕ, 0 < n → ∃ x y z w : ℕ, z < w ∧ n = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 ∧
      IsSquare (4 * x ^ 2 + 5 * y ^ 2 + 20 * z * w) := by
  sorry

end OMA.S_oeis_a272084
