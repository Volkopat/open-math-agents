import Mathlib

/-!
# A282828: Decimal representation of the x-axis, from the left edge to the origin, of the n-th stage of growth of the two-dimensional cellular automaton defined by Rule 521, based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A282828 (OEIS Foundation, CC BY-SA 4.0).
Conjectures: Colin Barker, Feb 22 2017.
Formalization: @longling12 (drafted with AI assistance)

Stage zero has one ON cell at the origin. The rule updates the whole integer plane
using bit c + 2s, with s the sum of the four orthogonal neighbors and c the center.
The x-axis is read in base 2 with the outer endpoint most significant.
The sequence starts at index 0. The ordinary generating function is cross-multiplied in ℤ⟦X⟧.
-/

namespace OMA.S_oeis_a282828

open PowerSeries

def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | n + 1, x, y => Nat.testBit 521 ((state n x y).toNat + 2 *
      ((state n (x - 1) y).toNat + (state n (x + 1) y).toNat +
       (state n x (y - 1)).toNat + (state n x (y + 1)).toNat))

def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n + 1), ((state n ((j : ℤ) - n) 0).toNat : ℤ) * 2 ^ (n - j)

theorem main :
    (∀ n : ℕ, 15 < n → a n = a (n - 2) + 256 * a (n - 8) - 256 * a (n - 10)) ∧
    (PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 + 4 * X ^ 2) * (1 + 16 * X ^ 4)) =
      (1 + 6 * X ^ 4 + 7 * X ^ 5 + 14 * X ^ 6 - 7 * X ^ 7 - 152 * X ^ 8 + 124 * X ^ 9
       + 216 * X ^ 10 - 124 * X ^ 11 + 152 * X ^ 12 + 172 * X ^ 13 - 96 * X ^ 14 + 256 * X ^ 15
       - 32 * X ^ 17 : PowerSeries ℤ)) := by
  sorry

end OMA.S_oeis_a282828
