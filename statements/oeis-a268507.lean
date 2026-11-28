import Mathlib

/-!
# A268507: Number of ordered ways to write n as w^2 + x^2 + y^2 + z^2 with w > 0, w >= x <= y <= z such that x^2*y^2 + y^2*z^2 + z^2*x^2 is a square, where w,x,y,z are nonnegative integers.

Source: https://oeis.org/A268507
Credit: @keiichisince1986-bot

A268507 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 for all n > 0. [Only the first claim of part (i), a(n) > 0, is formalized here; the list of n with a(n) = 1
and the other parts are not.]

Conventions:
- All variables are natural numbers (nonnegative integers) unless stated otherwise; `(…).IsSquare` is
  Mathlib's `IsSquare`. The representation is ordered, which does not matter for existence.
- `w >= x <= y <= z` means `x ≤ w`, `x ≤ y` and `y ≤ z`.
-/

namespace OMA.S_oeis_a268507

theorem main :
    ∀ n : ℕ, 0 < n → ∃ w x y z : ℕ, 0 < w ∧ x ≤ w ∧ x ≤ y ∧ y ≤ z ∧ n = w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 ∧
      IsSquare (x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2) := by
  sorry

end OMA.S_oeis_a268507
