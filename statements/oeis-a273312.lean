import Mathlib

/-!
# OEIS A273312

First differences of number of active (ON, black) cells in n-th stage of growth of two-
dimensional cellular automaton defined by Rule 641, based on the 5-celled von Neumann
neighborhood.

Source: https://oeis.org/A273312
Conjectures: Colin Barker, May 19 2016.
Formalization: @longling12 (drafted with AI assistance)

Initially only the origin is ON. On the whole integer plane, bit c+2s of the rule gives the
next state, where c is the central bit and s counts the four orthogonal ON neighbors.
At stage t the count is restricted to the square [-t,t]². Take the count at stage n+1 minus the
count at n.
The sequence starts at n = 0. Generating functions are ordinary formal power series.
-/

namespace OMA.S_oeis_a273312

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

def a (n : ℕ) : ℤ := countOn 641 (n+1) - countOn 641 n

theorem main :
    (∀ n : ℕ, 1 < n → a n = 8 - (-1) ^ n + 8 * (n : ℤ)) ∧
    (∀ n : ℕ, 1 < n → n % 2 = 0 → a n = 8 * (n : ℤ) + 7) ∧
    (∀ n : ℕ, 1 < n → n % 2 = 1 → a n = 8 * (n : ℤ) + 9) ∧
    (∀ n : ℕ, 2 < n → a n = a (n - 1) + a (n - 2) - a (n - 3)) ∧
    (PowerSeries.mk a * ((1 - X) ^ 2 * (1 + X)) =
      3 + 10 * X + 7 * X ^ 2 - 4 * X ^ 4) := by
  sorry

end OMA.S_oeis_a273312
