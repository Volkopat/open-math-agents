import Mathlib

/-!
# OEIS A055217: partial row sums of trinomial coefficients, a recurrence

Source: https://oeis.org/A055217
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the sum of the first `n` coefficients of `(1 + x + x²)ⁿ` (`n ≥ 1`): `1, 3, 10, 31, 96, …`.
Conjecture (OEIS entry): `(n+1) a(n) - (5n+1) a(n-1) + 3(n-1) a(n-2) + 9(n-1) a(n-3) = 0`.

Conventions:
* As usual for these recurrences, `n` counts from `0` along the listed terms: with
  `b(n) = a(n+1)` (`b(0) = 1, b(1) = 3, b(2) = 10, b(3) = 31, b(4) = 96`) the identity reads
  `(n+1) b(n) - (5n+1) b(n-1) + 3(n-1) b(n-2) + 9(n-1) b(n-3) = 0`, which holds at `n = 3, 4`;
  `main` states it for `n ≥ 3`.
-/

namespace OMA.S_oeis_a055217

/-- `a(n)`: sum of the coefficients of `x⁰, …, x^(n-1)` in `(1 + x + x²)ⁿ`. -/
noncomputable def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range n, ((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ) ^ n).coeff k

/-- `b(n) = a(n+1)`. -/
noncomputable def b (n : ℕ) : ℤ := a (n + 1)

/-- The recurrence for `n ≥ 3`. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    let m : ℤ := n
    (m + 1) * b n - (5 * m + 1) * b (n - 1) + 3 * (m - 1) * b (n - 2) + 9 * (m - 1) * b (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a055217
