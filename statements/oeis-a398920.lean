import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Asymptotic count of the Diophantine inequality in A398920

Write i = b and j = b+d in ab+bc+cd. Then 1 ≤ i < j, and for every
positive a there are exactly (N-i*a)/j positive choices of c, using
natural-number division and truncated subtraction. The indices in count
are shifted by one to enumerate positive sizes.

Source: https://oeis.org/A398920
Credit: @CubeJerry
-/

namespace OMA.S_oeis_a398920

open Finset Filter Asymptotics

def triangle (N i j : ℕ) : ℕ :=
  ∑ u ∈ range (N/i), (N-i*(u+1))/j

def count (N : ℕ) : ℕ :=
  ∑ j ∈ range N, ∑ i ∈ range j, triangle N (i+1) (j+1)

theorem main :
    (fun N : ℕ => (count N : ℝ) - (N:ℝ)^2 * (Real.log N)^2 / 4)
      =O[atTop] (fun N : ℕ => (N:ℝ)^2 * Real.log N) := by
  sorry

end OMA.S_oeis_a398920
