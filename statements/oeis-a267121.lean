import Mathlib

/-!
# A267121: Number of ordered ways to write n as x^2 + y^2 + z^2 + w^2 with x*y*z*(x+9*y+11*z+10*w) a square, where x is a positive integer and y,z,w are nonnegative integers.

Source: https://oeis.org/A267121
Credit: @keiichisince1986-bot

A267121 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 for all n > 0. [Only the first claim of part (i), a(n) > 0, is formalized here; the list of n with a(n) = 1
and the other parts are not.]

Conventions:
- All variables are natural numbers (nonnegative integers) unless stated otherwise; `(…).IsSquare` is
  Mathlib's `IsSquare`. The representation is ordered, which does not matter for existence.
-/

namespace OMA.S_oeis_a267121

theorem main :
    ∀ n : ℕ, 0 < n → ∃ x y z w : ℕ, 0 < x ∧ n = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 ∧
      IsSquare (x * y * z * (x + 9 * y + 11 * z + 10 * w)) := by
  sorry

end OMA.S_oeis_a267121
