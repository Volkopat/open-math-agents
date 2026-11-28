import Mathlib

/-!
# OEIS A283356

Binary representation of the x-axis, from the origin to the right edge, of the n-th stage of
growth of the two-dimensional cellular automaton defined by Rule 621, based on the 5-celled von
Neumann neighborhood.

Source: https://oeis.org/A283356
Conjectures: Colin Barker, Mar 06 2017.
Formalization: @longling12 (drafted with AI assistance)

Initially only the origin is ON. On the whole integer plane, bit c+2s of the rule gives the
next state, where c is the central bit and s counts the four orthogonal ON neighbors.
The central row runs from origin to right edge inclusive. Its first cell is the most significant
digit in base 10.
The sequence starts at n = 0. Generating functions are ordinary formal power series.
-/

namespace OMA.S_oeis_a283356

open PowerSeries

/-- Synchronous evolution on the integer plane from one ON cell. -/
def state (r : ℕ) : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t+1, x, y =>
    let s := state r t
    r.testBit ((s x y).toNat + 2 * ((s (x-1) y).toNat + (s (x+1) y).toNat +
      (s x (y-1)).toNat + (s x (y+1)).toNat))

/-- Read the central row from origin to right edge, most significant digit first. -/
def digits (r n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n+1), ((state r n (i : ℤ) 0).toNat : ℤ) * 10 ^ (n-i)

def a (n : ℕ) : ℤ := digits 621 n

theorem main :
    (PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 10 * X)) =
      1 - 9 * X - 10 * X ^ 2 + 1100 * X ^ 3 - 1000 * X ^ 4 - 90000 * X ^ 5 + 100000 * X ^ 7) ∧
    (∀ n : ℕ, 4 < n → n % 2 = 0 → (a n : ℚ) = (10 ^ n - 9991) / 9) ∧
    (∀ n : ℕ, 4 < n → n % 2 = 1 → (a n : ℚ) = (10 ^ n - 91) / 9) ∧
    (∀ n : ℕ, 5 < n → a n = 10 * a (n - 1) + a (n - 2) - 10 * a (n - 3)) := by
  sorry

end OMA.S_oeis_a283356
