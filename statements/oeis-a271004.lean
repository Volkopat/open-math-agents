import Mathlib

/-!
# A271004: Number of active (ON, black) cells in n-th stage of growth of two-dimensional cellular automaton defined by Rule 245, based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A271004 (OEIS Foundation, CC BY-SA 4.0).
Conjectures: Colin Barker, Mar 28 2016.
Formalization: @longling12 (drafted with AI assistance)

Stage zero has one ON cell at the origin. The rule updates the whole integer plane
using bit c + 2s, with s the sum of the four orthogonal neighbors and c the center.
The count uses the square [-n,n] by [-n,n] at each stage.
The sequence starts at index 0. The ordinary generating function is cross-multiplied in ℤ⟦X⟧.
-/

namespace OMA.S_oeis_a271004

open PowerSeries

def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | n + 1, x, y => Nat.testBit 245 ((state n x y).toNat + 2 *
      ((state n (x - 1) y).toNat + (state n (x + 1) y).toNat +
       (state n x (y - 1)).toNat + (state n x (y + 1)).toNat))

def a (n : ℕ) : ℤ :=
  (((Finset.range (2 * n + 1) ×ˢ Finset.range (2 * n + 1)).filter fun p : ℕ × ℕ =>
    state n ((p.1 : ℤ) - n) ((p.2 : ℤ) - n)).card : ℤ)

theorem main :
    (∀ n : ℕ, 5 < n → (a n : ℚ) = ((-13) - 9 * (-1) ^ n + 4 * (2 + (-1) ^ n) * (n : ℚ) - 4 * ((-1) + (-1) ^ n) * (n : ℚ) ^ 2) / 2) ∧
    (∀ n : ℕ, 3 < n → n % 2 = 0 → a n = 6 * (n : ℤ) - 11) ∧
    (∀ n : ℕ, 5 < n → n % 2 = 1 → a n = 4 * (n : ℤ) ^ 2 + 2 * (n : ℤ) - 2) ∧
    (∀ n : ℕ, 9 < n → a n = 3 * a (n - 2) - 3 * a (n - 4) + a (n - 6)) ∧
    (PowerSeries.mk a * ((1 - X) ^ 3 * (1 + X) ^ 3) =
      (1 + 8 * X + X ^ 2 + 20 * X ^ 3 + 4 * X ^ 4 + 4 * X ^ 5 - 3 * X ^ 6 - 4 * X ^ 7 - 3 * X ^ 8
       + 8 * X ^ 9 - 4 * X ^ 11 : PowerSeries ℤ)) := by
  sorry

end OMA.S_oeis_a271004
