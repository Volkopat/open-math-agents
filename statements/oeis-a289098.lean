import Mathlib

/-!
# A289098: Decimal representation of the diagonal from the corner to the origin of the n-th stage of growth of the two-dimensional cellular automaton defined by Rule 545, based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A289098 (OEIS Foundation, CC BY-SA 4.0).
Conjectures: Chai Wah Wu, Jun 13 2025; Stefano Spezia, Jun 14 2025.
Formalization: @longling12 (drafted with AI assistance)

Stage zero has one ON cell at the origin. The rule updates the whole integer plane
using bit c + 2s, with s the sum of the four orthogonal neighbors and c the center.
The last line of the OEIS %t program extracts the center row, which disagrees with the published terms.
This definition follows the diagonal specified by %N and confirmed by the data.
The diagonal is read in base 2 with the outer endpoint most significant.
The sequence starts at index 0. The ordinary generating function is cross-multiplied in ℤ⟦X⟧.
-/

namespace OMA.S_oeis_a289098

open PowerSeries

def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | n + 1, x, y => Nat.testBit 545 ((state n x y).toNat + 2 *
      ((state n (x - 1) y).toNat + (state n (x + 1) y).toNat +
       (state n x (y - 1)).toNat + (state n x (y + 1)).toNat))

def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n + 1), ((state n ((j : ℤ) - n) ((j : ℤ) - n)).toNat : ℤ) * 2 ^ (n - j)

theorem main :
    (∀ n : ℕ, 5 < n → a n = 2 * a (n - 1) + a (n - 2) - 2 * a (n - 3)) ∧
    (PowerSeries.mk a * ((X - 1) * (X + 1) * (2 * X - 1)) =
      (4 * X ^ 5 - 2 * X ^ 4 + 2 * X ^ 2 + 1 : PowerSeries ℤ)) ∧
    (let ch (r : ℚ) := PowerSeries.mk (fun n => if Even n then r ^ n / n.factorial else 0)
      let sh (r : ℚ) := PowerSeries.mk (fun n => if Odd n then r ^ n / n.factorial else 0)
      PowerSeries.mk (fun n => (a n : ℚ) / n.factorial) =
        2 + X ^ 2 - 3 * ch 1 + 2 * ch 2 - 2 * sh 1 + 2 * sh 2) := by
  sorry

end OMA.S_oeis_a289098
