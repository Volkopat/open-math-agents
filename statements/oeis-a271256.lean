import Mathlib

/-!
# OEIS A271256

First differences of number of active (ON, black) cells in n-th stage of growth of two-
dimensional cellular automaton defined by Rule 323, based on the 5-celled von Neumann
neighborhood.

Source: https://oeis.org/A271256
Conjectures: Colin Barker, Apr 03 2016.
Formalization: @longling12 (drafted with AI assistance)

Initially only the origin is ON. On the whole integer plane, bit c+2s of the rule gives the
next state, where c is the central bit and s counts the four orthogonal ON neighbors.
At stage t the count is restricted to the square [-t,t]². Take the count at stage n+1 minus the
count at n.
The sequence starts at n = 0. Generating functions are ordinary formal power series.
-/

namespace OMA.S_oeis_a271256

open PowerSeries

/-- Synchronous evolution on the integer plane from one ON cell. -/
def state (r : ℕ) : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t+1, x, y =>
    let s := state r t
    r.testBit ((s x y).toNat + 2 * ((s (x-1) y).toNat + (s (x+1) y).toNat +
      (s x (y-1)).toNat + (s x (y+1)).toNat))

/-- Number of ON cells in the central square at time t. -/
def countOn (r t : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (2*t+1), ∑ j ∈ Finset.range (2*t+1),
    ((state r t ((i : ℤ) - t) ((j : ℤ) - t)).toNat : ℤ)

def a (n : ℕ) : ℤ := countOn 323 (n+1) - countOn 323 n

theorem main :
    (∀ n : ℕ, 4 < n → a n = 2 + (-1) ^ n + 4 * (n : ℤ) + 4 * (-1) ^ n * (n : ℤ) ^ 2) ∧
    (∀ n : ℕ, 4 < n → n % 2 = 0 → a n = 4 * (n : ℤ) ^ 2 + 4 * (n : ℤ) + 3) ∧
    (∀ n : ℕ, 4 < n → n % 2 = 1 → a n = -4 * (n : ℤ) ^ 2 + 4 * (n : ℤ) + 1) ∧
    (∀ n : ℕ, 7 < n → a n = -a (n - 1) + 2 * a (n - 2) + 2 * a (n - 3) - a (n - 4) - a (n - 5)) ∧
    (PowerSeries.mk a * ((1 - X) ^ 2 * (1 + X) ^ 3) =
      4 + 4 * X + 23 * X ^ 2 - 4 * X ^ 3 + 2 * X ^ 4 + 4 * X ^ 5 + 3 * X ^ 6 - 8 * X ^ 7 + 4 * X ^ 9) := by
  sorry

end OMA.S_oeis_a271256
