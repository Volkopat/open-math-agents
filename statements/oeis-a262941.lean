import Mathlib

/-!
# OEIS A262941: n = x^4 + 2^k y^2 + z(z+1)/2 with k in {1, 2}

Source: https://oeis.org/A262941
Conjecture: Zhi-Wei Sun.
Credit: @biondadave

A262941(n) is the number of ordered pairs `(x, y)` with `x ≥ 0` and `y > 0` such that
`n - x⁴ - y(y+1)/2` is an even square or twice a square.

Conjecture: `a(n) > 0` for all `n > 0`. In other words, any positive integer `n` can be written as
`x⁴ + 2ᵏ y² + z(z+1)/2`, where `k` is 1 or 2, and `x, y, z` are integers with `z > 0`.

Formalization notes:
* An even square is `(2w)² = 2² w²` and twice a square is `2¹ w²`, so the two readings agree;
  the second is stated. Since only `x⁴` and `y²` occur, taking `x, y` natural numbers loses
  nothing; `z > 0` is a positive integer.
-/

namespace OMA.S_oeis_a262941

/-- Every positive integer is `x⁴ + 2ᵏ y² + z(z+1)/2` with `k ∈ {1, 2}`, `x, y ≥ 0`, `z > 0`. -/
theorem main :
    ∀ n : ℕ, 0 < n → ∃ k x y z : ℕ, (k = 1 ∨ k = 2) ∧ 0 < z ∧
      n = x ^ 4 + 2 ^ k * y ^ 2 + z * (z + 1) / 2 := by
  sorry

end OMA.S_oeis_a262941
