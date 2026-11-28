import Mathlib

/-!
# Circular coloring triangle-free subcubic planar graphs

Source: https://www.openproblemgarden.org/op/circular_chromatic_number_of_triangle_free_planar_graphs

Problem (Ghebleh, Zhu): does every triangle-free planar graph of maximum degree three have
circular chromatic number at most `20/7`? (The dodecahedron lies in this class and has
circular chromatic number exactly `20/7`.)

Conventions:
- Graphs are finite simple graphs, given as a `SimpleGraph` on a finite vertex type `V`.
- For integers `k ≥ d ≥ 1`, a `(k, d)`-colouring of `G` is a map `c : V → {0, …, k - 1}` with
  `d ≤ |c u - c v| ≤ k - d` whenever `u` and `v` are adjacent. The circular chromatic number
  `χ_c(G)` is the infimum of `k / d` over all `(k, d)`-colourings of `G` (for finite graphs
  this infimum is attained).
- Planarity is the plane-drawing definition used in `statements/wp-apex-graph.lean`, copied
  verbatim.
- Maximum degree three: every vertex has degree at most `3`; triangle-free: no `3`-clique.
- The source asks a yes/no question; `main` states the answer yes, and a disproof would
  answer no.
-/

namespace OMA.S_opg_circular_chromatic_number_of_triangle_free_planar_graphs

open SimpleGraph

/-- `G` has a plane drawing: vertices at distinct points, edges as arcs joining their endpoints,
with arc interiors avoiding all vertices and the interiors of all other arcs. -/
def IsPlanar {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ (pos : V → ℝ × ℝ) (arc : G.edgeSet → C(unitInterval, ℝ × ℝ)),
    Function.Injective pos ∧
    (∀ e, Function.Injective (arc e)) ∧
    (∀ e, Sym2.map pos e.1 = s(arc e 0, arc e 1)) ∧
    (∀ e (t : unitInterval), (t : ℝ) ∈ Set.Ioo 0 1 → ∀ v, arc e t ≠ pos v) ∧
    (∀ e f, e ≠ f → ∀ s t : unitInterval, (s : ℝ) ∈ Set.Ioo 0 1 → (t : ℝ) ∈ Set.Ioo 0 1 →
      arc e s ≠ arc f t)

/-- `c` is a `(k, d)`-colouring of `G`: colours in `{0, …, k - 1}`, and adjacent vertices get
colours at circular distance at least `d` modulo `k`. -/
def IsCircularColoring {V : Type} (G : SimpleGraph V) (k d : ℕ) (c : V → ℕ) : Prop :=
  (∀ v, c v < k) ∧
    ∀ u v, G.Adj u v → (d : ℤ) ≤ |(c u : ℤ) - c v| ∧ |(c u : ℤ) - c v| ≤ k - d

/-- The circular chromatic number: the infimum of `k / d` over all `(k, d)`-colourings with
`1 ≤ d ≤ k`. -/
noncomputable def circularChromaticNumber {V : Type} (G : SimpleGraph V) : ℝ :=
  sInf {r : ℝ | ∃ k d : ℕ, 1 ≤ d ∧ d ≤ k ∧ (∃ c, IsCircularColoring G k d c) ∧ r = k / d}

/-- Every finite triangle-free planar graph of maximum degree at most three has circular
chromatic number at most `20/7`. -/
theorem main :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      IsPlanar G → G.CliqueFree 3 → (∀ v, G.degree v ≤ 3) →
        circularChromaticNumber G ≤ 20 / 7 := by
  sorry

end OMA.S_opg_circular_chromatic_number_of_triangle_free_planar_graphs
