import Mathlib

/-!
# A351902: Number of ways to write n as w^2 + x^2 + y^2 + z^2 + 3*x*y*z, where w is a positive integer, and x,y,z are nonnegative integers with x <= y <= z.

Source: https://oeis.org/A351902
Credit: @keiichisince1986-bot

A351902 is the sequence `a(n)` named in the title. The entry states:
Conjecture: We have a(n) > 0 except for n = 23. In other words, any positive integer n not equal to
23 can be written as w^2 + x^2 + y^2 + z^2 + 3*x*y*z with w > 0 and x, y, z >= 0.

Conventions:
- `a(23) = 0` in the data, so the conjecture says that the set of positive `n` with no such representation
  is exactly `{23}`.
-/

namespace OMA.S_oeis_a351902

theorem main :
    {n : ℕ | 0 < n ∧ ¬ ∃ w x y z : ℕ, 0 < w ∧ x ≤ y ∧ y ≤ z ∧
        n = w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 + 3 * x * y * z} = {23} := by
  sorry

end OMA.S_oeis_a351902
