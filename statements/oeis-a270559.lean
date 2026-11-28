import Mathlib

/-!
# OEIS A270559: n = x^4 + x^3 + y^2 + z(z+1)/2

Source: https://oeis.org/A270559
Conjecture: Zhi-Wei Sun.
Credit: @biondadave

A270559(n) is the number of ordered ways to write `n` as `x^4 + x^3 + y^2 + z(z+1)/2`, where
`x, y` and `z` are integers with `x` nonzero, `y` nonnegative and `z` positive.

Conjecture (i): `a(n) > 0` for all `n > 0`. In other words, for each `n = 1, 2, 3, ...` there are
integers `x` and `y` such that `n - (x^4 + x^3 + y^2)` is a positive triangular number.

Formalization notes:
* Stated with the conditions of the definition (`x ≠ 0`, `y ≥ 0`, `z > 0`). This agrees with the
  "in other words" form, because `x = -1` gives `x^4 + x^3 = 0`, the same value as `x = 0`, and
  `y^2` only depends on `|y|`.
-/

namespace OMA.S_oeis_a270559

/-- Every positive integer is `x^4 + x^3 + y^2 + z(z+1)/2` with `x ≠ 0`, `y ≥ 0`, `z > 0`. -/
theorem main :
    ∀ n : ℕ, 0 < n → ∃ x : ℤ, x ≠ 0 ∧ ∃ y z : ℕ, 0 < z ∧
      (n : ℤ) = x ^ 4 + x ^ 3 + (y : ℤ) ^ 2 + (z * (z + 1) / 2 : ℕ) := by
  sorry

end OMA.S_oeis_a270559
