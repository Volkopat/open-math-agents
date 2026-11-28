import FormalConjectures.ErdosProblems.«80»
import Mathlib

-- Reduction Erdos80.erdos_80.parts.ii.R1
-- Credit: @marcusbuffett

/-!
# Erdős 80 (ii): the dense range `c > 1/4`

A classical case: for `1/4 < c < 1/2` every graph on `n` vertices with at least `cn²` edges has
an edge in at least `(4c - 1) n` triangles. For an edge `uv` the common neighbourhood has at
least `deg u + deg v - n` vertices; summing over the edges and using Cauchy-Schwarz,
`Σ deg² ≥ 4e²/n`, gives a book of size `4e/n - n`. So `f_c(n) ≥ (4c-1)n`, which is far more than
`log n`. This is `H1`. The open core `H2` is the range `0 < c ≤ 1/4`, where Fox and Loh showed
that `f_c(n) ≤ n^{O(1/log log n)}` for `c < 1/4`.
-/

namespace OMA.R_Erdos80_erdos_80_parts_ii_R1
open Erdos80

/-- The dense range `1/4 < c < 1/2`, where a book of linear size is forced. -/
def H1 : Prop :=
  ∀ c : ℝ, 1 / 4 < c → c < 1 / 2 →
    (fun n : ℕ ↦ (f c n : ℝ)) ≫ (fun n : ℕ ↦ Real.log n)

/-- The open core: the sparse range `0 < c ≤ 1/4`. -/
def H2 : Prop :=
  ∀ c : ℝ, 0 < c → c ≤ 1 / 4 →
    (fun n : ℕ ↦ (f c n : ℝ)) ≫ (fun n : ℕ ↦ Real.log n)

theorem main : H1 → H2 → type_of% @Erdos80.erdos_80.parts.ii := by
  intro h1 h2 c hc hc2
  rcases le_or_gt c (1 / 4) with h | h
  · exact h2 c hc h
  · exact h1 c h hc2

end OMA.R_Erdos80_erdos_80_parts_ii_R1
