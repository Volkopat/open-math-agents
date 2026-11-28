import Mathlib

/-!
# A279499: Binary representation of the x-axis, from the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular automaton defined by Rule 161, based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A279499 (OEIS Foundation, CC BY-SA 4.0).
Conjectures: Colin Barker, Dec 14 2016.
Formalization: @longling12 (drafted with AI assistance)

Stage zero has one ON cell at the origin. The rule updates the whole integer plane
using bit c + 2s, with s the sum of the four orthogonal neighbors and c the center.
The x-axis is read in base 10 with the origin most significant.
The sequence starts at index 0. The ordinary generating function is cross-multiplied in ℤ⟦X⟧.
-/

namespace OMA.S_oeis_a279499

open PowerSeries

def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | n + 1, x, y => Nat.testBit 161 ((state n x y).toNat + 2 *
      ((state n (x - 1) y).toNat + (state n (x + 1) y).toNat +
       (state n x (y - 1)).toNat + (state n x (y + 1)).toNat))

def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n + 1), ((state n (j : ℤ) 0).toNat : ℤ) * 10 ^ (n - j)

theorem main :
    (∀ n : ℕ, 6 < n → a n = 100 * a (n - 2) + a (n - 4) - 100 * a (n - 6)) ∧
    (PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 + X ^ 2)) =
      (1 + X ^ 2 + 1000 * X ^ 4 - 99000 * X ^ 6 - 10000000 * X ^ 10 : PowerSeries ℤ)) := by
  sorry

end OMA.S_oeis_a279499
