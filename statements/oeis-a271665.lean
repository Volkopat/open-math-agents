import Mathlib

/-!
# A271665: Number of ordered ways to write n as w^2 + x^2 + y^2 + z^2 such that w^2 + 4*x*y + 8*y*z + 32*z*x is a square, where w is a positive integer and x,y,z are nonnegative integers.

Source: https://oeis.org/A271665
Credit: @keiichisince1986-bot

A271665 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 for all n > 0. [Only the first claim of part (i), a(n) > 0, is formalized here; the list of n with a(n) = 1
and the other parts are not.]

Conventions:
- All variables are natural numbers (nonnegative integers) unless stated otherwise; `(…).IsSquare` is
  Mathlib's `IsSquare`. The representation is ordered, which does not matter for existence.
-/

namespace OMA.S_oeis_a271665

theorem main :
    ∀ n : ℕ, 0 < n → ∃ w x y z : ℕ, 0 < w ∧ n = w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 ∧
      IsSquare (w ^ 2 + 4 * x * y + 8 * y * z + 32 * z * x) := by
  sorry

end OMA.S_oeis_a271665
