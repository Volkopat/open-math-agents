import Mathlib

/-!
# OEIS A282295

Binary representation of the x-axis, from the left edge to the origin, of the n-th stage of
growth of the two-dimensional cellular automaton defined by Rule 451, based on the 5-celled
von Neumann neighborhood.

Source: https://oeis.org/A282295
Referenced sequence: https://oeis.org/A279720
Conjectures: R. J. Mathar, Jun 21 2025.
Formalization: @longling12 (drafted with AI assistance)

Stage zero has a single ON cell at the origin. Each cell of the integer plane updates using
rule bit c+2s, where c is its current state and s counts its four orthogonal ON neighbors.
The central row runs from left edge to origin inclusive. Its first cell is the most
significant digit in base 10.
-/

namespace OMA.S_oeis_a282295

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

def a (n : ℕ) : ℤ := digits 451 n

/-- A279720 uses the same axial readout with Rule 193, starting from a single ON cell. -/
def A279720 (n : ℕ) : ℤ := digits 193 n

theorem main :
    ∀ n : ℕ, 2 ≤ n → a n = A279720 n := by
  sorry

end OMA.S_oeis_a282295
