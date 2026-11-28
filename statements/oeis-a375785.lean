import Mathlib

/-!
# A375785: a(n) is the number of distinct integer-sided cuboids having the same surface as a cube with edge length n.

Source: https://oeis.org/A375785
Credit: @ceejcake

Conjecture (OEIS A375785): All terms are odd.

Formalization notes:
* The sequence has offset `1` (`n ≥ 1`).
* Distinct integer-sided cuboids with side lengths `x, y, z ≥ 1` are represented canonically by
  ordered triples `1 ≤ x ≤ y ≤ z` (unordered solutions up to permutation of sides).
* Having the same surface area as a cube of edge length `n` means
  `2 * (x * y + y * z + x * z) = 6 * n ^ 2`, equivalently `x * y + y * z + x * z = 3 * n ^ 2`.
* Every positive integer solution with `1 ≤ x ≤ y ≤ z` satisfies the lossless bounds:
  - `3 * x ^ 2 ≤ x * y + y * z + x * z = 3 * n ^ 2`, hence `x ≤ n`;
  - `y ^ 2 ≤ y * z ≤ 3 * n ^ 2 ≤ (2 * n) ^ 2`, hence `y ≤ 2 * n`;
  - `z ≤ y * z ≤ 3 * n ^ 2`, hence `z ≤ 3 * n ^ 2`.
* Initial values for `n = 1, 2, 3, 4, 5, 6, 7, 8, ...`:
  `a(n) = 1, 1, 3, 3, 5, 5, 5, 7, 9, 9, 9, 13, ...`.
-/

namespace OMA.S_oeis_a375785

/-- `a n` is the number of distinct integer-sided cuboids `(x, y, z)` (`1 ≤ x ≤ y ≤ z`) having
the same surface area as a cube of edge length `n`, i.e., `x * y + y * z + x * z = 3 * n ^ 2`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n ×ˢ Finset.Icc 1 (2 * n) ×ˢ Finset.Icc 1 (3 * n ^ 2)).filter
    fun ⟨x, y, z⟩ => x ≤ y ∧ y ≤ z ∧ x * y + y * z + x * z = 3 * n ^ 2).card

/-- OEIS A375785 conjecture: `a n` is odd for every `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → Odd (a n) := by
  sorry

end OMA.S_oeis_a375785
