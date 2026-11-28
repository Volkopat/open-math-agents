import Mathlib

/-!
# OEIS A283644

Binary representation of the x-axis, from the left edge to the origin, of the n-th stage of
growth of the two-dimensional cellular automaton defined by Rule 694, based on the 5-celled von
Neumann neighborhood.

Source: https://oeis.org/A283644
Conjectures: Colin Barker, Mar 14 2017.
Formalization: @longling12 (drafted with AI assistance)

Initially only the origin is ON. On the whole integer plane, bit c+2s of the rule gives the
next state, where c is the central bit and s counts the four orthogonal ON neighbors.
The central row runs from left edge to origin inclusive. Its first cell is the most significant
digit in base 10.
The sequence starts at n = 0. Generating functions are ordinary formal power series.
-/

namespace OMA.S_oeis_a283644

open PowerSeries

/-- Synchronous evolution on the integer plane from one ON cell. -/
def state (r : ℕ) : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t+1, x, y =>
    let s := state r t
    r.testBit ((s x y).toNat + 2 * ((s (x-1) y).toNat + (s (x+1) y).toNat +
      (s x (y-1)).toNat + (s x (y+1)).toNat))

/-- Read the central row from left edge to origin, most significant digit first. -/
def digits (r n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n+1), ((state r n ((i : ℤ) - n) 0).toNat : ℤ) * 10 ^ (n-i)

def a (n : ℕ) : ℤ := digits 694 n

theorem main :
    (PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + X ^ 2) * (1 + X ^ 4)) =
      1 + X + X ^ 2 - 99 * X ^ 3 + X ^ 4 - 99 * X ^ 5 - 9999 * X ^ 6 + 1009901 * X ^ 7 - 100 * X ^ 9 -
      10000 * X ^ 10 + 1010000 * X ^ 11 - 100000000 * X ^ 12) ∧
    (∀ n : ℕ, 11 < n → a n = 10 * a (n - 1) + a (n - 8) - 10 * a (n - 9)) := by
  sorry

end OMA.S_oeis_a283644
