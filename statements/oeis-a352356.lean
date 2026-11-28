import Mathlib

/-!
# A352356: Number of ways to write 12*n + 5 as 2*x^2 + 5*y^2 + 9*z^2 + x*y*z, where x, y and z are nonnegative integers.

Source: https://oeis.org/A352356
Credit: @ceejcake

Conjecture (Zhi-Wei Sun, OEIS A352356): for each `n = 0, 1, 2, ...` we can write `12 * n + 5`
as `2 * x ^ 2 + 5 * y ^ 2 + 9 * z ^ 2 + x * y * z` with `x, y, z` nonnegative integers,
i.e. `a(n) > 0` for every `n ≥ 0`.

Formalization notes:
* The sequence has offset `0` (`n : ℕ`).
* `a n` counts ordered triples `(x, y, z)` of natural numbers with
  `2 * x ^ 2 + 5 * y ^ 2 + 9 * z ^ 2 + x * y * z = 12 * n + 5`.
* Writing `m = 12 * n + 5`, every term is nonnegative, so any solution satisfies the lossless bounds
  - `2 * x ^ 2 ≤ m`, hence `x ^ 2 ≤ m / 2` and `x ≤ (m / 2).sqrt`;
  - `5 * y ^ 2 ≤ m`, hence `y ≤ (m / 5).sqrt`;
  - `9 * z ^ 2 ≤ m`, hence `z ≤ (m / 9).sqrt`.
* Initial values for `n = 0, 1, ..., 15`:
  `a(n) = 1, 2, 1, 3, 3, 1, 2, 4, 3, 3, 2, 5, 1, 3, 4, 3, ...`.
-/

namespace OMA.S_oeis_a352356

/-- `a n` is the number of ordered triples `(x, y, z)` of nonnegative integers such that
`2 * x ^ 2 + 5 * y ^ 2 + 9 * z ^ 2 + x * y * z = 12 * n + 5`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (((12 * n + 5) / 2).sqrt + 1) ×ˢ Finset.range (((12 * n + 5) / 5).sqrt + 1) ×ˢ
      Finset.range (((12 * n + 5) / 9).sqrt + 1)).filter
    fun ⟨x, y, z⟩ => 2 * x ^ 2 + 5 * y ^ 2 + 9 * z ^ 2 + x * y * z = 12 * n + 5).card

/-- OEIS A352356 conjecture: `a n > 0` for every `n ≥ 0`. -/
theorem main : ∀ n : ℕ, 0 < a n := by
  sorry

end OMA.S_oeis_a352356
