import Mathlib

/-!
# A343391: Number of ways to write n as x^2 + [y^2/4] + [z^4/6] with x,y,z positive integers, where [.] is the floor function.

Source: https://oeis.org/A343391
Credit: @ceejcake

Conjecture (Zhi-Wei Sun, 2021, OEIS A343391): `a(n) > 0` for all `n > 0`.

Formalization notes:
* The sequence has offset `1`; the conjecture is stated for every `n : ℕ` with `0 < n`.
* `a n` counts ordered triples `(x, y, z)` of positive integers with
  `x ^ 2 + y ^ 2 / 4 + z ^ 4 / 6 = n`, where `/` is natural-number division, i.e. the floor.
* Because every term is nonnegative, any solution satisfies the lossless bounds:
  - `x ^ 2 ≤ n`, hence `x ≤ n.sqrt`;
  - `y ^ 2 / 4 ≤ n`, i.e. `y ^ 2 ≤ 4 * n + 3`, hence `y ≤ (4 * n + 3).sqrt`;
  - `z ^ 4 / 6 ≤ n`, i.e. `(z ^ 2) ^ 2 ≤ 6 * n + 5`, hence `z ≤ (6 * n + 5).sqrt.sqrt`.
  Positivity of `x, y, z` is imposed by ranging over `Finset.Icc 1 _`.
* Initial values for `n = 1, ..., 16`:
  `a(n) = 1, 1, 2, 2, 3, 2, 3, 2, 2, 4, 2, 3, 4, 1, 5, 3, ...`.
-/

namespace OMA.S_oeis_a343391

/-- `a n` is the number of ordered triples `(x, y, z)` of positive integers such that
`x ^ 2 + ⌊y ^ 2 / 4⌋ + ⌊z ^ 4 / 6⌋ = n`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n.sqrt ×ˢ Finset.Icc 1 (4 * n + 3).sqrt ×ˢ
      Finset.Icc 1 (6 * n + 5).sqrt.sqrt).filter
    fun ⟨x, y, z⟩ => x ^ 2 + y ^ 2 / 4 + z ^ 4 / 6 = n).card

/-- OEIS A343391 conjecture (Zhi-Wei Sun): `a n > 0` for every `n > 0`. -/
theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a343391
