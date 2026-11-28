import Mathlib

/-!
# Does `x^4 + y^4 + 1 = z^2` have a non-trivial solution?

Source: https://math.stackexchange.com/questions/16887/does-the-equation-x4y41-z2-have-a-non-trivial-solution
Credit: @shc261392

Question. Does the equation `x^4 + y^4 + 1 = z^2` (equivalently `x^4 + y^4 = z^2 - 1`) have a
solution in positive integers? Searches found none with `0 < x < y < 7.9 · 10^7`.

Reading used here: the affirmative answer, a solution with `x, y > 0` (if `x = 0` or `y = 0`,
the equation forces the other to be `0` too, which is the trivial solution).
-/

namespace OMA.S_mse_16887

theorem main : ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ x ^ 4 + y ^ 4 + 1 = z ^ 2 := by
  sorry

end OMA.S_mse_16887
