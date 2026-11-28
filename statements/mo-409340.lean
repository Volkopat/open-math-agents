import Mathlib.Data.Rat.Defs

/-!
# Rational points on the magic-hourglass curve

Source: https://mathoverflow.net/q/409340
Credit: @Gh0stBlock

Thomas asks whether the displayed curve has an affine rational point with
abscissa outside the three already known values.
-/

namespace OMA.S_mo_409340

/-- The polynomial in Thomas's equation. -/
def polynomial (x : ℚ) : ℚ :=
  49 * x ^ 12 - 128 * x ^ 11 - 298 * x ^ 10 + 320 * x ^ 9 +
  1071 * x ^ 8 - 1856 * x ^ 7 + 1140 * x ^ 6 - 64 * x ^ 5 -
  321 * x ^ 4 + 192 * x ^ 3 - 42 * x ^ 2 + 1

theorem main :
    ∃ x y : ℚ, x ≠ 0 ∧ x ≠ 1 ∧ x ≠ -1 ∧ y ^ 2 = polynomial x := by
  sorry

end OMA.S_mo_409340
