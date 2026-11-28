import Mathlib

/-!
# Diophantine equations and the numbers 4, 7, 8

Source: https://mathoverflow.net/questions/201980
Asked by MathOverflow user user70097.

The question considers the Diophantine equation `x^n + y^n + z^n = k * x * y * z` in
positive integers `n, x, y, z`, for `k` in `{4, 7, 8}`. For `n = 1, 2, 3` it is known
that there is no solution. The question asks: is this equation solvable for `n ≥ 4`
and `k = 4`? And the same question for `k = 7` and `k = 8`.

Translation choices.
* All quantities are natural numbers; positivity of `x, y, z` is an explicit hypothesis,
  and `n ≥ 4` is the range asked about.
* `main` is the affirmative answer in its weakest form: for at least one `k` in
  `{4, 7, 8}` and at least one exponent `n ≥ 4` the equation has a solution in
  positive integers.
-/

namespace OMA.S_mo_201980

theorem main :
    ∃ k ∈ ({4, 7, 8} : Finset ℕ), ∃ n : ℕ, 4 ≤ n ∧
      ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x ^ n + y ^ n + z ^ n = k * x * y * z := by
  sorry

end OMA.S_mo_201980
