import Mathlib

/-!
# A306250: Number of ways to write n as x*(3x+1) + y*(3y-1) + z*(3z+2) + w*(3w-2), where x,y,z,w are nonnegative integers with x*y*z = 0.

Source: https://oeis.org/A306250
Credit: @ceejcake

Conjecture (Zhi-Wei Sun, 2019, OEIS A306250): `a(n) > 0` for any nonnegative integer `n`.

Formalization notes:
* The sequence has offset `0`; the conjecture is stated for every `n : ℕ`.
* `a n` counts ordered 4-tuples `(x, y, z, w)` of nonnegative integers with `x * y * z = 0` and
  `x * (3 * x + 1) + y * (3 * y - 1) + z * (3 * z + 2) + w * (3 * w - 2) = n`.
  The equation is evaluated in `ℤ` (after casting `x, y, z, w`), so `3 * y - 1` and `3 * w - 2`
  are genuine integer subtractions and no truncated natural-number subtraction occurs.
* Lossless bounds. For nonnegative integers, each of the four terms is at least the square of its
  variable: `x * (3 * x + 1) - x ^ 2 = 2 * x ^ 2 + x ≥ 0`, `y * (3 * y - 1) - y ^ 2 = y * (2 * y - 1) ≥ 0`,
  `z * (3 * z + 2) - z ^ 2 = 2 * z ^ 2 + 2 * z ≥ 0`, `w * (3 * w - 2) - w ^ 2 = 2 * w * (w - 1) ≥ 0`.
  So all four terms are nonnegative, each is at most `n`, and every variable is at most `n.sqrt`.
* Initial values for `n = 0, ..., 15`:
  `a(n) = 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 1, 3, 4, ...`.
-/

namespace OMA.S_oeis_a306250

/-- `a n` is the number of ordered 4-tuples `(x, y, z, w)` of nonnegative integers with
`x * y * z = 0` and `x * (3 * x + 1) + y * (3 * y - 1) + z * (3 * z + 2) + w * (3 * w - 2) = n`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n.sqrt + 1) ×ˢ Finset.range (n.sqrt + 1) ×ˢ
      Finset.range (n.sqrt + 1) ×ˢ Finset.range (n.sqrt + 1)).filter
    fun ⟨x, y, z, w⟩ => x * y * z = 0 ∧
      (x : ℤ) * (3 * x + 1) + (y : ℤ) * (3 * y - 1) + (z : ℤ) * (3 * z + 2) +
        (w : ℤ) * (3 * w - 2) = (n : ℤ)).card

/-- OEIS A306250 conjecture (Zhi-Wei Sun): `a n > 0` for every nonnegative integer `n`. -/
theorem main : ∀ n : ℕ, 0 < a n := by
  sorry

end OMA.S_oeis_a306250
