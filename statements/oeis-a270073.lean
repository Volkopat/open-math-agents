import Mathlib

/-!
# A270073: Number of ordered ways to write n as x^2 + y^2 + z^2 + w^2 with x*y + 2*z*w a square, where x,y,z are nonnegative integers and w is an integer with x <= y and z >= |w|.

Source: https://oeis.org/A270073
Credit: @keiichisince1986-bot

A270073 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 for all n = 0,1,2,... [Only the first claim of part (i), a(n) > 0, is formalized here; the list of n with a(n) = 1
and the other parts are not.]

Conventions:
- All variables are natural numbers (nonnegative integers) unless stated otherwise; `(…).IsSquare` is
  Mathlib's `IsSquare`. The representation is ordered, which does not matter for existence.
- Here `w` is an integer (it may be negative) and the identity is stated in `ℤ`.
-/

namespace OMA.S_oeis_a270073

theorem main :
    ∀ n : ℕ, ∃ x y z : ℕ, ∃ w : ℤ, x ≤ y ∧ |w| ≤ z ∧ (n : ℤ) = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 ∧
      IsSquare ((x * y : ℤ) + 2 * z * w) := by
  sorry

end OMA.S_oeis_a270073
