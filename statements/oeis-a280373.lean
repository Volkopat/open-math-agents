import Mathlib

/-!
# A280373: Decimal representation of the x-axis, from the left edge to the origin, of the n-th stage of growth of the two-dimensional cellular automaton defined by Rule 260, based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A280373 (OEIS Foundation, CC BY-SA 4.0).
Conjectures: Colin Barker, Jan 02 2017.
Formalization: @longling12 (drafted with AI assistance)

Stage zero has one ON cell at the origin. The rule updates the whole integer plane
using bit c + 2s, with s the sum of the four orthogonal neighbors and c the center.
The x-axis is read in base 2 with the outer endpoint most significant.
The sequence starts at index 0. The ordinary generating function is cross-multiplied in ℤ⟦X⟧.
-/

namespace OMA.S_oeis_a280373

open PowerSeries

def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | n + 1, x, y => Nat.testBit 260 ((state n x y).toNat + 2 *
      ((state n (x - 1) y).toNat + (state n (x + 1) y).toNat +
       (state n x (y - 1)).toNat + (state n x (y + 1)).toNat))

def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n + 1), ((state n ((j : ℤ) - n) 0).toNat : ℤ) * 2 ^ (n - j)

theorem main :
    (∀ n : ℕ, 3 < n → a n = 16 * a (n - 4)) ∧
    (PowerSeries.mk a * ((1 - 2 * X) * (1 + 2 * X) * (1 + 4 * X ^ 2)) =
      (1 + 2 * X + 5 * X ^ 2 + 8 * X ^ 3 + 8 * X ^ 5 + 4 * X ^ 6 + 2 * X ^ 7 + X ^ 8 - 16 * X ^ 12 : PowerSeries ℤ)) := by
  sorry

end OMA.S_oeis_a280373
