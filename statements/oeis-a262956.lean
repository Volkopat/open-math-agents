import Mathlib

/-!
# OEIS A262956: n or n + 1 is a fourth power plus a square plus a positive triangular number

Source: https://oeis.org/A262956
Conjecture: Zhi-Wei Sun.
Credit: @biondadave

A262956(n) is the number of ordered pairs `(x, y)` with `x ≥ 0` and `y > 0` such that
`n - x⁴ - y(y+1)/2` is a square or a square minus 1.

Conjecture: `a(n) > 0` for all `n > 0`. In other words, for any positive integer `n`, either `n`
or `n + 1` can be written as the sum of a fourth power, a square and a positive triangular
number.

Formalization notes:
* `n - x⁴ - y(y+1)/2 = w²` gives `n = x⁴ + w² + T`, and `= w² - 1` gives `n + 1 = x⁴ + w² + T`,
  with `T = y(y+1)/2` a positive triangular number (`y > 0`); fourth powers and squares of
  natural numbers (including `0`).
-/

namespace OMA.S_oeis_a262956

/-- For every positive `n`, `n` or `n + 1` is `x⁴ + w² + y(y+1)/2` with `y > 0`. -/
theorem main :
    ∀ n : ℕ, 0 < n → ∃ x w y : ℕ, 0 < y ∧
      (n = x ^ 4 + w ^ 2 + y * (y + 1) / 2 ∨ n + 1 = x ^ 4 + w ^ 2 + y * (y + 1) / 2) := by
  sorry

end OMA.S_oeis_a262956
