import Mathlib

/-!
# OEIS A285645

Decimal representation of the diagonal from the corner to the origin of the n-th stage of growth
of the two-dimensional cellular automaton defined by Rule 65, based on the 5-celled von Neumann
neighborhood.

Source: https://oeis.org/A285645
Conjectures: Colin Barker, Apr 24 2017.
Formalization: @longling12 (drafted with AI assistance)

Initially only the origin is ON. On the whole integer plane, bit c+2s of the rule gives the
next state, where c is the central bit and s counts the four orthogonal ON neighbors.
The diagonal runs from corner to origin inclusive. Its first cell is the most significant digit
in base 2.
The last line of %t extracts the central row and disagrees with the published terms.
The definition follows the diagonal in %N and the published data.
The sequence starts at n = 0. Generating functions are ordinary formal power series.
-/

namespace OMA.S_oeis_a285645

open PowerSeries

/-- Synchronous evolution on the integer plane from one ON cell. -/
def state (r : ℕ) : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t+1, x, y =>
    let s := state r t
    r.testBit ((s x y).toNat + 2 * ((s (x-1) y).toNat + (s (x+1) y).toNat +
      (s x (y-1)).toNat + (s x (y+1)).toNat))

/-- Read the diagonal from corner to origin, most significant digit first. -/
def digits (r n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n+1), ((state r n ((i : ℤ) - n) ((i : ℤ) - n)).toNat : ℤ) * 2 ^ (n-i)

def a (n : ℕ) : ℤ := digits 65 n

theorem main :
    (PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X)) =
      1 + 2 * X - 4 * X ^ 2 + 2 * X ^ 3 + 8 * X ^ 5 + 2 * X ^ 6 - 8 * X ^ 8) ∧
    (∀ n : ℕ, 4 < n → n % 2 = 0 → a n = 3) ∧
    (∀ n : ℕ, 4 < n → n % 2 = 1 → a n = 2 * (2 ^ n - 2)) ∧
    (∀ n : ℕ, 3 < n → a n = 5 * a (n - 2) - 4 * a (n - 4)) := by
  sorry

end OMA.S_oeis_a285645
