import Mathlib

/-!
# A273021: Number of ordered ways to write n as x^2 + y^2 + z^2 + w^2 with 2*x*y + y*z - z*w - w*x a square, where w is a positive integer and x,y,z are nonnegative integers with x <= y.

Source: https://oeis.org/A273021
Credit: @keiichisince1986-bot

A273021 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 for all n > 0. [Only the first claim of part (i), a(n) > 0, is formalized here; the list of n with a(n) = 1
and the other parts are not.]

Conventions:
- All variables are natural numbers (nonnegative integers) unless stated otherwise; `(…).IsSquare` is
  Mathlib's `IsSquare`. The representation is ordered, which does not matter for existence.
- The expression may be negative, so it is computed in `ℤ`; a negative integer is never a square.
-/

namespace OMA.S_oeis_a273021

theorem main :
    ∀ n : ℕ, 0 < n → ∃ x y z w : ℕ, 0 < w ∧ x ≤ y ∧ n = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 ∧
      IsSquare (2 * x * y + y * z - z * w - w * x : ℤ) := by
  sorry

end OMA.S_oeis_a273021
