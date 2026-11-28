import Mathlib

/-!
# A343950: Number of ways to write n as x + y + z with x^2 + 4*y^2 + 5*z^2 a square, where x,y,z are positive integers with y or z a positive power of two.

Source: https://oeis.org/A343950
Credit: @keiichisince1986-bot

A343950 is the sequence `a(n)` named in the title. The entry states:
Conjecture 1: a(n) > 0 for all n > 7. [The list of n with a(n) = 1 and further conjectures of the entry are not formalized here.]

Conventions:
- All variables are natural numbers (nonnegative integers) unless stated otherwise. The count is of
  ordered representations, which does not matter for existence.
- A positive power of two is `2^k` with `k ≥ 1`.
-/

namespace OMA.S_oeis_a343950

theorem main :
    ∀ n : ℕ, 7 < n → ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = n ∧
      (∃ k : ℕ, 1 ≤ k ∧ (y = 2 ^ k ∨ z = 2 ^ k)) ∧ IsSquare (x ^ 2 + 4 * y ^ 2 + 5 * z ^ 2) := by
  sorry

end OMA.S_oeis_a343950
