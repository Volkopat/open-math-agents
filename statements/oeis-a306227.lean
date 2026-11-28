import Mathlib

/-!
# A306227: Number of ways to write n as w + x^4 + y*(y+1)/2 + z*(z+1)/2, where w is 0 or 1, and x, y, z are nonnegative integers with x >= w and y < z.

Source: https://oeis.org/A306227
Credit: @keiichisince1986-bot

A306227 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 0. In other words, any positive integer can be written as the sum of
two fourth powers one of which is 0 or 1, and two distinct triangular numbers.

Conventions:
- `w ∈ {0, 1}` is written `w ≤ 1`; the triangular numbers `y(y+1)/2` are exact natural-number divisions.
-/

namespace OMA.S_oeis_a306227

theorem main :
    ∀ n : ℕ, 0 < n → ∃ w x y z : ℕ, w ≤ 1 ∧ w ≤ x ∧ y < z ∧
      n = w + x ^ 4 + y * (y + 1) / 2 + z * (z + 1) / 2 := by
  sorry

end OMA.S_oeis_a306227
