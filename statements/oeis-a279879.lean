import Mathlib

/-!
# A279879: Decimal representation of the x-axis, from the left edge to the origin, of the n-th stage of growth of the two-dimensional cellular automaton defined by Rule 213, based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A279879 (OEIS Foundation, CC BY-SA 4.0).
Conjectures: Colin Barker, Dec 22 2016.
Formalization: @longling12 (drafted with AI assistance)

Stage zero has one ON cell at the origin. The rule updates the whole integer plane
using bit c + 2s, with s the sum of the four orthogonal neighbors and c the center.
The x-axis is read in base 2 with the outer endpoint most significant.
The sequence starts at index 0. The ordinary generating function is cross-multiplied in ℤ⟦X⟧.
-/

namespace OMA.S_oeis_a279879

open PowerSeries

def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | n + 1, x, y => Nat.testBit 213 ((state n x y).toNat + 2 *
      ((state n (x - 1) y).toNat + (state n (x + 1) y).toNat +
       (state n x (y - 1)).toNat + (state n x (y + 1)).toNat))

def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n + 1), ((state n ((j : ℤ) - n) 0).toNat : ℤ) * 2 ^ (n - j)

theorem main :
    (∀ n : ℕ, 6 < n → a n = 7 * a (n - 2) - 14 * a (n - 4) + 8 * a (n - 6)) ∧
    (PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 - 2 * X ^ 2)) =
      (1 + 2 * X - 5 * X ^ 2 - 2 * X ^ 3 + 7 * X ^ 4 - 14 * X ^ 6 + 8 * X ^ 8 : PowerSeries ℤ)) := by
  sorry

end OMA.S_oeis_a279879
