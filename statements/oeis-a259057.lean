import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Rat.Cast.Defs

/-!
# OEIS A259057

Source: https://oeis.org/A259057
Credit: @AShahver

The defining matrix is from https://oeis.org/A259056. On the upper wedge
its zero-based entry at i,j is i*n-i²+j+1. The minimum distance to the four
edges extends this entry by transpose and central reflection.
-/

namespace OMA.S_oeis_a259057

/-- Distance in layers from the outer edge of an n by n matrix. -/
def radius (n i j : ℤ) : ℤ := min (min i j) (min (n - 1 - i) (n - 1 - j))

/-- Unified zero-based formula for the matrix in OEIS A259056. -/
def entry (n i j : ℤ) : ℤ :=
  let r := radius n i j
  r * (n + 1 - r) + |i - j| + 1

def B (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j => entry n i.val j.val

def normalizedDet (m : ℕ) : ℚ := ((B (2 * m)).det : ℚ) / 3

/-- Every term of OEIS A259057 is an integer. -/

theorem main : ∀ m : ℕ, 0 < m → ∃ z : ℤ, normalizedDet m = (z : ℚ) := by
  sorry

end OMA.S_oeis_a259057
