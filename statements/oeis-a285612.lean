import Mathlib

/-!
# A285612: Binary representation of the diagonal from the corner to the origin of the n-th stage of growth of the two-dimensional cellular automaton defined by Rule 62, based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A285612 (OEIS Foundation, CC BY-SA 4.0).
Conjectures: Colin Barker, Apr 23 2017.
Formalization: @longling12 (drafted with AI assistance)

Stage zero has one ON cell at the origin. The rule updates the whole integer plane
using bit c + 2s, with s the sum of the four orthogonal neighbors and c the center.
The last line of the OEIS %t program extracts the center row, which disagrees with the published terms.
This definition follows the diagonal specified by %N and confirmed by the data.
The diagonal is read in base 10 with the outer endpoint most significant.
The sequence starts at index 0. The ordinary generating function is cross-multiplied in ℤ⟦X⟧.
-/

namespace OMA.S_oeis_a285612

open PowerSeries

def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | n + 1, x, y => Nat.testBit 62 ((state n x y).toNat + 2 *
      ((state n (x - 1) y).toNat + (state n (x + 1) y).toNat +
       (state n x (y - 1)).toNat + (state n x (y + 1)).toNat))

def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n + 1), ((state n ((j : ℤ) - n) ((j : ℤ) - n)).toNat : ℤ) * 10 ^ (n - j)

theorem main :
    (PowerSeries.mk a * ((1 - X) * (1 - 10 * X ^ 2)) =
      (1 - X ^ 2 + 10 * X ^ 4 : PowerSeries ℤ)) ∧
    (∀ n : ℕ, 1 < n → n % 2 = 0 → (a n : ℚ) = 10 * (10 ^ (n / 2) - 1) / 9) ∧
    (∀ n : ℕ, 1 < n → n % 2 = 1 → (a n : ℚ) = (10 ^ ((n + 1) / 2) - 10) / 9) ∧
    (∀ n : ℕ, 2 < n → a n = a (n - 1) + 10 * a (n - 2) - 10 * a (n - 3)) := by
  sorry

end OMA.S_oeis_a285612
