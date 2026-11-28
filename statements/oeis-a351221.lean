import Mathlib

/-!
# A351221: Least positive integer m such that m^6*n = x^6 + y^3 + z^2 for some nonnegative integers x,y,z.

Source: https://oeis.org/A351221
Credit: @keiichisince1986-bot

A351221 is the sequence `a(n)` named in the title. The entry states:
6-3-2 Conjecture: a(n) exists for any nonnegative integer n. Equivalently, each nonnegative rational
number can be written as x^6 + y^3 + z^2 with x,y,z nonnegative rational numbers. (We formalize that
a(n) exists for every n.)

Conventions:
- All variables are natural numbers.
-/

namespace OMA.S_oeis_a351221

theorem main :
    ∀ n : ℕ, ∃ m x y z : ℕ, 0 < m ∧ m ^ 6 * n = x ^ 6 + y ^ 3 + z ^ 2 := by
  sorry

end OMA.S_oeis_a351221
