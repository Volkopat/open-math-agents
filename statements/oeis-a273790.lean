import Mathlib

/-!
# A273790: Partial sums of the number of active (ON, black) cells in n-th stage of growth of two-dimensional cellular automaton defined by Rule 931, based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A273790 (OEIS Foundation, CC BY-SA 4.0).
Conjectures: Colin Barker, May 31 2016; Stefano Spezia, Dec 30 2024.
Formalization: @longling12 (drafted with AI assistance)

Stage zero has one ON cell at the origin. The rule updates the whole integer plane
using bit c + 2s, with s the sum of the four orthogonal neighbors and c the center.
The count uses the square [-n,n] by [-n,n] at each stage. Partial sums include stages 0 through n.
The sequence starts at index 0. The ordinary generating function is cross-multiplied in ℤ⟦X⟧.
-/

namespace OMA.S_oeis_a273790

open PowerSeries

def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | n + 1, x, y => Nat.testBit 931 ((state n x y).toNat + 2 *
      ((state n (x - 1) y).toNat + (state n (x + 1) y).toNat +
       (state n x (y - 1)).toNat + (state n x (y + 1)).toNat))

def onCount (n : ℕ) : ℤ :=
  (((Finset.range (2 * n + 1) ×ˢ Finset.range (2 * n + 1)).filter fun p : ℕ × ℕ =>
    state n ((p.1 : ℤ) - n) ((p.2 : ℤ) - n)).card : ℤ)

def a (n : ℕ) : ℤ := ∑ j ∈ Finset.range (n + 1), onCount j

theorem main :
    (∀ n : ℕ, 0 < n → (a n : ℚ) = (4 * (n : ℚ) ^ 3 + 12 * (n : ℚ) ^ 2 + 11 * (n : ℚ) - 9) / 3) ∧
    (∀ n : ℕ, 4 < n → a n = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4)) ∧
    (PowerSeries.mk a * ((1 - X) ^ 4) =
      (1 + 2 * X + 13 * X ^ 2 - 12 * X ^ 3 + 4 * X ^ 4 : PowerSeries ℤ)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ) / n.factorial) =
      4 + PowerSeries.exp ℚ * (PowerSeries.C (4 / 3 : ℚ) * X ^ 3 + 8 * X ^ 2 + 9 * X - 3)) := by
  sorry

end OMA.S_oeis_a273790
