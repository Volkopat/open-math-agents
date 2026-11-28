import Mathlib

/-!
# A271714: Number of ordered ways to write n as w^2 + x^2 + y^2 + z^2 such that (10*w+5*x)^2 + (12*y+36*z)^2 is a square, where w is a positive integer and x,y,z are nonnegative integers.

Source: https://oeis.org/A271714
Credit: @keiichisince1986-bot

A271714 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 for all n > 0. [Only the first claim of part (i), a(n) > 0, is formalized here; the list of n with a(n) = 1
and the other parts are not.]

Conventions:
- All variables are natural numbers (nonnegative integers) unless stated otherwise; `(…).IsSquare` is
  Mathlib's `IsSquare`. The representation is ordered, which does not matter for existence.
-/

namespace OMA.S_oeis_a271714

theorem main :
    ∀ n : ℕ, 0 < n → ∃ w x y z : ℕ, 0 < w ∧ n = w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 ∧
      IsSquare ((10 * w + 5 * x) ^ 2 + (12 * y + 36 * z) ^ 2) := by
  sorry

end OMA.S_oeis_a271714
