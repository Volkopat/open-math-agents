import Mathlib

/-!
# A290195: Decimal representation of the diagonal from the origin to the corner of the n-th stage of growth of the two-dimensional cellular automaton defined by Rule 705, based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A290195 (OEIS Foundation, CC BY-SA 4.0).
Conjectures: David A. Corneth, Jul 23 2017; Chai Wah Wu, Nov 01 2018.
Formalization: @longling12 (drafted with AI assistance)

Stage zero has one ON cell at the origin. The rule updates the whole integer plane
using bit c + 2s, with s the sum of the four orthogonal neighbors and c the center.
The last line of the OEIS %t program extracts the center row, which disagrees with the published terms.
This definition follows the diagonal specified by %N and confirmed by the data.
The diagonal is read in base 2 with the origin most significant.
The sequence starts at index 0. The ordinary generating function is cross-multiplied in ℤ⟦X⟧.
-/

namespace OMA.S_oeis_a290195

open PowerSeries

def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | n + 1, x, y => Nat.testBit 705 ((state n x y).toNat + 2 *
      ((state n (x - 1) y).toNat + (state n (x + 1) y).toNat +
       (state n x (y - 1)).toNat + (state n x (y + 1)).toNat))

def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n + 1), ((state n (j : ℤ) (j : ℤ)).toNat : ℤ) * 2 ^ (n - j)

theorem main :
    (∀ n : ℕ, 3 < n → n % 2 = 1 → a n = 2 ^ (n - 1) - 1) ∧
    (∀ n : ℕ, 3 < n → n % 2 = 0 → a n = 3 * 2 ^ (n - 1) - 1) ∧
    (∀ n : ℕ, 5 < n → a n = a (n - 1) + 4 * a (n - 2) - 4 * a (n - 3)) ∧
    (PowerSeries.mk a * ((X - 1) * (2 * X - 1) * (2 * X + 1)) =
      (16 * X ^ 5 - 20 * X ^ 4 + 6 * X ^ 3 + 1 : PowerSeries ℤ)) := by
  sorry

end OMA.S_oeis_a290195
