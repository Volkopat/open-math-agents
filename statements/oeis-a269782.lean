import Mathlib

/-!
# OEIS A269782

Number of active (ON, black) cells in n-th stage of growth of two-dimensional cellular automaton
defined by Rule 65, based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A269782
Conjectures: Colin Barker, Apr 03 2016.
Formalization: @longling12 (drafted with AI assistance)

Initially only the origin is ON. On the whole integer plane, bit c+2s of the rule gives the
next state, where c is the central bit and s counts the four orthogonal ON neighbors.
At stage t the count is restricted to the square [-t,t]². Use the count at stage n.
The sequence starts at n = 0. Generating functions are ordinary formal power series.
-/

namespace OMA.S_oeis_a269782

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

def a (n : ℕ) : ℤ := countOn 65 n

theorem main :
    (∀ n : ℕ, 4 < n → (a n : ℚ) = (11 - (-1) ^ n + 4 * (-1) ^ n * (n : ℚ) - 4 * (-1 + (-1) ^ n) * (n : ℚ) ^
      2) / 2) ∧
    (∀ n : ℕ, 4 < n → n % 2 = 0 → a n = 2 * (n : ℤ) + 5) ∧
    (∀ n : ℕ, 4 < n → n % 2 = 1 → a n = 4 * (n : ℤ) ^ 2 - 2 * (n : ℤ) + 6) ∧
    (∀ n : ℕ, 8 < n → a n = 3 * a (n - 2) - 3 * a (n - 4) + a (n - 6)) ∧
    (PowerSeries.mk a * ((1 - X) ^ 3 * (1 + X) ^ 3) =
      1 + 4 * X + 2 * X ^ 2 + 24 * X ^ 3 - 3 * X ^ 4 + 4 * X ^ 6 + 4 * X ^ 7 - 8 * X ^ 8 + 4 * X ^ 10) := by
  sorry

end OMA.S_oeis_a269782
