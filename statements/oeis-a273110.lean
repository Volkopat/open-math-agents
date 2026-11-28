import Mathlib

/-!
# A273110: Number of ordered ways to write n as x^2 + y^2 + z^2 + w^2 with (x+4*y+4*z)^2 + (9*x+3*y+3*z)^2 a square, where x,y,z,w are nonnegative integers with y > 0 and y >= z <= w.

Source: https://oeis.org/A273110
Credit: @keiichisince1986-bot

A273110 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 for all n > 0. [Only the first claim of part (i), a(n) > 0, is formalized here; the list of n with a(n) = 1
and the other parts are not.]

Conventions:
- All variables are natural numbers (nonnegative integers) unless stated otherwise; `(…).IsSquare` is
  Mathlib's `IsSquare`. The representation is ordered, which does not matter for existence.
- `y >= z <= w` means `z ≤ y` and `z ≤ w`.
-/

namespace OMA.S_oeis_a273110

theorem main :
    ∀ n : ℕ, 0 < n → ∃ x y z w : ℕ, 0 < y ∧ z ≤ y ∧ z ≤ w ∧ n = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 ∧
      IsSquare ((x + 4 * y + 4 * z) ^ 2 + (9 * x + 3 * y + 3 * z) ^ 2) := by
  sorry

end OMA.S_oeis_a273110
