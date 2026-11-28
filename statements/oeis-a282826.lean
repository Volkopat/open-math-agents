import Mathlib

/-!
# A282826: Binary representation of the x-axis, from the left edge to the origin, of the n-th stage of growth of the two-dimensional cellular automaton defined by Rule 521, based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A282826 (OEIS Foundation, CC BY-SA 4.0).
Conjectures: Colin Barker, Feb 22 2017.
Formalization: @longling12 (drafted with AI assistance)

Stage zero has one ON cell at the origin. The rule updates the whole integer plane
using bit c + 2s, with s the sum of the four orthogonal neighbors and c the center.
The x-axis is read in base 10 with the outer endpoint most significant.
The sequence starts at index 0. The ordinary generating function is cross-multiplied in ℤ⟦X⟧.
-/

namespace OMA.S_oeis_a282826

open PowerSeries

def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | n + 1, x, y => Nat.testBit 521 ((state n x y).toNat + 2 *
      ((state n (x - 1) y).toNat + (state n (x + 1) y).toNat +
       (state n x (y - 1)).toNat + (state n x (y + 1)).toNat))

def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n + 1), ((state n ((j : ℤ) - n) 0).toNat : ℤ) * 10 ^ (n - j)

theorem main :
    (∀ n : ℕ, 15 < n → a n = a (n - 2) + 100000000 * a (n - 8) - 100000000 * a (n - 10)) ∧
    (PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 + 100 * X ^ 2) * (1 + 10000 * X ^ 4)) =
      (1 + 110 * X ^ 4 + 111 * X ^ 5 + 9990 * X ^ 6 - 111 * X ^ 7 - 98899000 * X ^ 8
       + 1111100 * X ^ 9 + 99899000 * X ^ 10 - 1111100 * X ^ 11 + 10091000 * X ^ 12
       + 10101100 * X ^ 13 - 1100000 * X ^ 14 + 100000000 * X ^ 15 - 100000 * X ^ 17 : PowerSeries ℤ)) := by
  sorry

end OMA.S_oeis_a282826
