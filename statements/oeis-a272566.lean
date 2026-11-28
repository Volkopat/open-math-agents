import Mathlib

/-!
# A272566: Partial sums of the number of active (ON, black) cells in n-th stage of growth of two-dimensional cellular automaton defined by Rule 501, based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A272566 (OEIS Foundation, CC BY-SA 4.0).
Conjectures: Colin Barker, May 03 2016.
Formalization: @longling12 (drafted with AI assistance)

Stage zero has one ON cell at the origin. The rule updates the whole integer plane
using bit c + 2s, with s the sum of the four orthogonal neighbors and c the center.
The count uses the square [-n,n] by [-n,n] at each stage. Partial sums include stages 0 through n.
The sequence starts at index 0. The ordinary generating function is cross-multiplied in ℤ⟦X⟧.
-/

namespace OMA.S_oeis_a272566

open PowerSeries

def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | n + 1, x, y => Nat.testBit 501 ((state n x y).toNat + 2 *
      ((state n (x - 1) y).toNat + (state n (x + 1) y).toNat +
       (state n x (y - 1)).toNat + (state n x (y + 1)).toNat))

def onCount (n : ℕ) : ℤ :=
  (((Finset.range (2 * n + 1) ×ˢ Finset.range (2 * n + 1)).filter fun p : ℕ × ℕ =>
    state n ((p.1 : ℤ) - n) ((p.2 : ℤ) - n)).card : ℤ)

def a (n : ℕ) : ℤ := ∑ j ∈ Finset.range (n + 1), onCount j

theorem main :
    (∀ n : ℕ, 4 < n → (a n : ℚ) = 1 / 4 * (75 - 7 * (-1) ^ n) - 25 * (n : ℚ) / 6 - ((-3) + (-1) ^ n) * (n : ℚ) ^ 2 + 2 * (n : ℚ) ^ 3 / 3) ∧
    (∀ n : ℕ, 4 < n → n % 2 = 0 → (a n : ℚ) = (4 * (n : ℚ) ^ 3 + 12 * (n : ℚ) ^ 2 - 25 * (n : ℚ) + 102) / 6) ∧
    (∀ n : ℕ, 4 < n → n % 2 = 1 → (a n : ℚ) = (4 * (n : ℚ) ^ 3 + 24 * (n : ℚ) ^ 2 - 25 * (n : ℚ) + 123) / 6) ∧
    (∀ n : ℕ, 9 < n → a n = a (n - 1) + 3 * a (n - 2) - 3 * a (n - 3) - 3 * a (n - 4) + 3 * a (n - 5) + a (n - 6) - a (n - 7)) ∧
    (PowerSeries.mk a * ((1 - X) ^ 4 * (1 + X) ^ 3) =
      (1 + 8 * X + 2 * X ^ 2 + 20 * X ^ 3 + X ^ 4 + 4 * X ^ 5 - 4 * X ^ 7 - 4 * X ^ 8 + 8 * X ^ 9
       - 4 * X ^ 11 : PowerSeries ℤ)) := by
  sorry

end OMA.S_oeis_a272566
