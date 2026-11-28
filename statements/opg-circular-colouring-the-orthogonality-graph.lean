import Mathlib

/-!
# Circular colouring the orthogonality graph

Source: https://www.openproblemgarden.org/op/circular_colouring_the_orthogonality_graph
(M. DeVos, M. Ghebleh, L. Goddyn, B. Mohar, R. Naserasr)
Credit: @ishaanzee

Let `𝒪` denote the graph with vertex set consisting of all lines through the origin in `ℝ³` and two
vertices adjacent in `𝒪` if they are perpendicular.

**Problem.** Is `χ_c(𝒪) = 4`?

Here `χ_c` is the circular chromatic number: the infimum of `p / q` over all `(p, q)`-colorings,
where a `(p, q)`-coloring assigns to each vertex an element of `ℤ_p` so that adjacent vertices get
colors `a`, `b` with `q ≤ |a - b|_p` (distance in the cycle `ℤ_p`), i.e. `q ≤ (a - b) mod p ≤ p - q`.
We state the affirmative answer.

Formalization:
* Instead of lines we use their unit direction vectors: the graph on the unit sphere of
  `EuclideanSpace ℝ (Fin 3)` with `u ~ v` iff `⟪u, v⟫ = 0`. Each line contains two antipodal unit
  vectors, which are not adjacent, and adjacency depends only on the lines, so this graph and `𝒪`
  map homomorphically to each other and have the same circular chromatic number.
* A `(p, q)`-coloring is `c : vertices → Fin p` with `q ≤ (c u - c v) mod p ≤ p - q` for adjacent
  `u`, `v`; `χ_c` is the `sInf` of the set of ratios `p / q` (`p, q ≥ 1`) admitting such a coloring.
-/

namespace OMA.S_opg_circular_colouring_the_orthogonality_graph

/-- The orthogonality graph on unit vectors of `ℝ³`. -/
noncomputable def orthoGraph :
    SimpleGraph (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  SimpleGraph.fromRel fun u v => inner ℝ (u : EuclideanSpace ℝ (Fin 3)) (v : EuclideanSpace ℝ (Fin 3)) = 0

/-- `c` is a `(p, q)`-coloring of `G`. -/
def IsCircularColoring {V : Type*} (G : SimpleGraph V) (p q : ℕ) (c : V → Fin p) : Prop :=
  ∀ u v, G.Adj u v → (q : ℤ) ≤ ((c u : ℤ) - c v) % p ∧ ((c u : ℤ) - c v) % p ≤ p - q

/-- The circular chromatic number of `G`. -/
noncomputable def circularChromaticNumber {V : Type*} (G : SimpleGraph V) : ℝ :=
  sInf {r : ℝ | ∃ p q : ℕ, 1 ≤ q ∧ 1 ≤ p ∧ r = (p : ℝ) / q ∧
    ∃ c : V → Fin p, IsCircularColoring G p q c}

/-- **Question** (DeVos–Ghebleh–Goddyn–Mohar–Naserasr), affirmative form: `χ_c(𝒪) = 4`. -/
theorem main : circularChromaticNumber orthoGraph = 4 := by
  sorry

end OMA.S_opg_circular_colouring_the_orthogonality_graph
