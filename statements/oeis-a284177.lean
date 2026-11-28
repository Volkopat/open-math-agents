import Mathlib

/-!
# A284177: Decimal representation of the x-axis, from the left edge to the origin, of the n-th stage of growth of the two-dimensional cellular automaton defined by Rule 809, based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A284177 (OEIS Foundation, CC BY-SA 4.0).
Conjectures: Colin Barker, Mar 22 2017.
Formalization: @longling12 (drafted with AI assistance)

Stage zero has one ON cell at the origin. The rule updates the whole integer plane
using bit c + 2s, with s the sum of the four orthogonal neighbors and c the center.
The x-axis is read in base 2 with the outer endpoint most significant.
The sequence starts at index 0. The ordinary generating function is cross-multiplied in ℤ⟦X⟧.
-/

namespace OMA.S_oeis_a284177

open PowerSeries

def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | n + 1, x, y => Nat.testBit 809 ((state n x y).toNat + 2 *
      ((state n (x - 1) y).toNat + (state n (x + 1) y).toNat +
       (state n x (y - 1)).toNat + (state n x (y + 1)).toNat))

def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n + 1), ((state n ((j : ℤ) - n) 0).toNat : ℤ) * 2 ^ (n - j)

theorem main :
    (PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 + 4 * X ^ 2) * (1 + 16 * X ^ 4)) =
      (1 + 4 * X ^ 4 + 16 * X ^ 6 + 8 * X ^ 7 - 204 * X ^ 8 + 256 * X ^ 10 + 128 * X ^ 11
       - 192 * X ^ 12 + 32 * X ^ 13 + 32 * X ^ 14 + 512 * X ^ 17 : PowerSeries ℤ)) ∧
    (∀ n : ℕ, 14 < n → a n = a (n - 2) + 256 * a (n - 8) - 256 * a (n - 10)) := by
  sorry

end OMA.S_oeis_a284177
