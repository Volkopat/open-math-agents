import Mathlib

/-!
# OEIS A270008

Partial sums of the number of active (ON, black) cells in n-th stage of growth of two-
dimensional cellular automaton defined by Rule 5, based on the 5-celled von Neumann
neighborhood.

Source: https://oeis.org/A270008
Conjectures: Colin Barker, Mar 09 2016.
Formalization: @longling12 (drafted with AI assistance)

Initially only the origin is ON. On the whole integer plane, bit c+2s of the rule gives the
next state, where c is the central bit and s counts the four orthogonal ON neighbors.
At stage t the count is restricted to the square [-t,t]². Sum the counts from stage zero through
n inclusive. The recurrence uses n ≥ 7, the domain where all seven preceding terms exist.
The sequence starts at n = 0. Generating functions are ordinary formal power series.
-/

namespace OMA.S_oeis_a270008

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

def a (n : ℕ) : ℤ := ∑ j ∈ Finset.range (n+1), countOn 5 j

theorem main :
    (∀ n : ℕ, 0 < n → (a n : ℚ) = (9 - 9 * (-1) ^ n + (22 - 24 * (-1) ^ n) * (n : ℚ) - 12 * (-2 + (-1) ^ n)
      * (n : ℚ) ^ 2 + 8 * (n : ℚ) ^ 3) / 12) ∧
    (∀ n : ℕ, 0 < n → n % 2 = 0 → (a n : ℚ) = (4 * (n : ℚ) ^ 3 + 6 * (n : ℚ) ^ 2 - (n : ℚ)) / 6) ∧
    (∀ n : ℕ, 0 < n → n % 2 = 1 → (a n : ℚ) = (4 * (n : ℚ) ^ 3 + 18 * (n : ℚ) ^ 2 + 23 * (n : ℚ) + 9) / 6) ∧
    (∀ n : ℕ, 6 < n → a n = a (n - 1) + 3 * a (n - 2) - 3 * a (n - 3) - 3 * a (n - 4) + 3 * a (n - 5) + a (n
      - 6) - a (n - 7)) ∧
    (PowerSeries.mk a * ((1 - X) ^ 4 * (1 + X) ^ 3) =
      1 + 8 * X - 3 * X ^ 2 + 25 * X ^ 3 + 3 * X ^ 4 - 2 * X ^ 5 - X ^ 6 + X ^ 7) := by
  sorry

end OMA.S_oeis_a270008
