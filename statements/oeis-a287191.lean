import Mathlib

/-!
# OEIS A287191

Binary representation of the diagonal from the origin to the corner of the n-th stage of growth
of the two-dimensional cellular automaton defined by Rule 253, based on the 5-celled von Neumann
neighborhood.

Source: https://oeis.org/A287191
Conjectures: Colin Barker, Nov 22 2017.
Formalization: @longling12 (drafted with AI assistance)

Initially only the origin is ON. On the whole integer plane, bit c+2s of the rule gives the
next state, where c is the central bit and s counts the four orthogonal ON neighbors.
The diagonal runs from origin to corner inclusive. Its first cell is the most significant digit
in base 10.
The last line of %t extracts the central row and disagrees with the published terms.
The definition follows the diagonal in %N and the published data.
The sequence starts at n = 0. Generating functions are ordinary formal power series.
-/

namespace OMA.S_oeis_a287191

open PowerSeries

/-- Synchronous evolution on the integer plane from one ON cell. -/
def state (r : ℕ) : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t+1, x, y =>
    let s := state r t
    r.testBit ((s x y).toNat + 2 * ((s (x-1) y).toNat + (s (x+1) y).toNat +
      (s x (y-1)).toNat + (s x (y+1)).toNat))

/-- Read the diagonal from origin to corner, most significant digit first. -/
def digits (r n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n+1), ((state r n (i : ℤ) (i : ℤ)).toNat : ℤ) * 10 ^ (n-i)

def a (n : ℕ) : ℤ := digits 253 n

theorem main :
    (PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X)) =
      1 + X - 101 * X ^ 2 + 10 * X ^ 3 + 11100 * X ^ 4 - 11000 * X ^ 6) ∧
    (∀ n : ℕ, 2 < n → (a n : ℚ) = 1 / 180 * (-10 + 89 * (-10) ^ n + 10 * (-1) ^ n + 109 * 10 ^ n)) ∧
    (∀ n : ℕ, 4 < n → a n = 101 * a (n - 2) - 100 * a (n - 4)) := by
  sorry

end OMA.S_oeis_a287191
