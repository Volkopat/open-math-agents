import Mathlib

/-!
# A338696: Number of ways to write n as x^3 + y^2 + z*(3*z+2), where x and y are nonnegative integers, and z is an integer.

Source: https://oeis.org/A338696
Credit: @ceejcake

Conjecture (Zhi-Wei Sun, 2021, OEIS A338696): `a(n) > 0` except for `n = 19`.

Formalization notes:
* The sequence has offset `1`; the conjecture is stated for every `n : ℕ` with `0 < n`
  (it says that among `n = 1, 2, 3, ...` exactly `n = 19` has `a(n) = 0`).
* `a n` counts ordered triples `(x, y, z)` with `x, y : ℕ`, `z : ℤ` (any integer, possibly
  negative) and `x ^ 3 + y ^ 2 + z * (3 * z + 2) = n`, computed in `ℤ`.
* Lossless bounds. For every integer `z`, `z * (3 * z + 2) - z ^ 2 = 2 * z * (z + 1) ≥ 0`, so
  `z * (3 * z + 2) ≥ z ^ 2 ≥ 0`. Hence all three terms are nonnegative and any solution has
  - `x ^ 2 ≤ x ^ 3 ≤ n` (or `x = 0`), hence `x ≤ n.sqrt`;
  - `y ^ 2 ≤ n`, hence `y ≤ n.sqrt`;
  - `z ^ 2 ≤ n`, hence `|z| ≤ n.sqrt`.
  The integer range `-n.sqrt ≤ z ≤ n.sqrt` is written as the image of `k ↦ k - n.sqrt` over
  `k < 2 * n.sqrt + 1` (it is exactly that interval) so that the definition is computable.
* Initial values for `n = 1, ..., 20`:
  `a(n) = 3, 3, 1, 1, 3, 3, 1, 2, 6, 5, 1, 2, 3, 2, 1, 3, 8, 4, 0, 2`.
-/

namespace OMA.S_oeis_a338696

/-- `a n` is the number of triples `(x, y, z)` with `x, y` nonnegative integers and `z` an
integer such that `x ^ 3 + y ^ 2 + z * (3 * z + 2) = n`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n.sqrt + 1) ×ˢ Finset.range (n.sqrt + 1) ×ˢ
      (Finset.range (2 * n.sqrt + 1)).image (fun k : ℕ => (k : ℤ) - n.sqrt)).filter
    fun ⟨x, y, z⟩ => (x : ℤ) ^ 3 + (y : ℤ) ^ 2 + z * (3 * z + 2) = (n : ℤ)).card

/-- OEIS A338696 conjecture (Zhi-Wei Sun): for `n > 0`, `a n > 0` if and only if `n ≠ 19`. -/
theorem main : ∀ n : ℕ, 0 < n → (0 < a n ↔ n ≠ 19) := by
  sorry

end OMA.S_oeis_a338696
