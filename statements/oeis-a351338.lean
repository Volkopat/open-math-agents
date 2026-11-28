import Mathlib

/-!
# A351338: Least nonnegative integer m such that n = x^3 + y^3 - (z^3 + m^3) for some nonnegative integers x,y,z with z <= m.

Source: https://oeis.org/A351338
Credit: @keiichisince1986-bot

A351338 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) exists for any n >= 0. Equivalently, each integer can be written as x^3 + y^3 -
(z^3 + w^3) with x,y,z,w nonnegative integers. (We formalize that a(n) exists for every n >= 0.)

Conventions:
- All variables are natural numbers; the identity is stated in `ℤ`.
-/

namespace OMA.S_oeis_a351338

theorem main :
    ∀ n : ℕ, ∃ m x y z : ℕ, z ≤ m ∧ (n : ℤ) = x ^ 3 + y ^ 3 - (z ^ 3 + m ^ 3) := by
  sorry

end OMA.S_oeis_a351338
