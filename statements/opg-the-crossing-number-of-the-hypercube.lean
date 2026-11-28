import Mathlib

/-!
# The Crossing Number of the Hypercube

Source: https://www.openproblemgarden.org/op/the_crossing_number_of_the_hypercube
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Erdős–Guy): `lim_{d → ∞} cr(Q_d) / 4^d = 5/32`.

Conventions:
* `Q_d` is the `d`-dimensional hypercube: vertices `Fin d → Bool`, adjacent iff they differ in
  exactly one coordinate.
* A drawing places the vertices at distinct points of the plane and each edge as an arc (an
  injective path) between its endpoints whose interior avoids all vertices. Only drawings in which
  any two distinct edges meet in finitely many interior points are allowed, and `cr` minimises the
  number of (unordered pair of distinct edges, common interior point) incidences. This is the
  standard crossing number.
-/

namespace OMA.S_opg_the_crossing_number_of_the_hypercube

open Set Filter Topology

/-- The plane. -/
abbrev P := EuclideanSpace ℝ (Fin 2)

/-- A drawing of `G` in the plane, with an arc for each dart. -/
structure Drawing {V : Type} (G : SimpleGraph V) where
  pos : V → P
  pos_inj : Function.Injective pos
  arc : (d : G.Dart) → Path (pos d.fst) (pos d.snd)
  arc_inj : ∀ d, Function.Injective (arc d)
  arc_symm : ∀ d, arc d.symm = (arc d).symm
  arc_avoids : ∀ d (t : unitInterval), (t : ℝ) ∈ Ioo (0 : ℝ) 1 → arc d t ∉ range pos

variable {V : Type} {G : SimpleGraph V}

/-- The interior of the arc of an edge `e`. -/
def Drawing.inner (D : Drawing G) (e : Sym2 V) : Set P :=
  ⋃ (d : G.Dart) (_ : d.edge = e), (D.arc d) '' {t | (t : ℝ) ∈ Ioo (0 : ℝ) 1}

/-- Triples (edge, edge, point) of two distinct edges and a common interior point. -/
def Drawing.crossings (D : Drawing G) : Set (Sym2 V × Sym2 V × P) :=
  {p | p.1 ∈ G.edgeSet ∧ p.2.1 ∈ G.edgeSet ∧ p.1 ≠ p.2.1 ∧ p.2.2 ∈ D.inner p.1 ∩ D.inner p.2.1}

/-- Admissible drawings: every two distinct edges meet in finitely many interior points. -/
def Drawing.Good (D : Drawing G) : Prop := D.crossings.Finite

/-- The crossing number (each crossing is counted once for each order of its two edges,
hence the division by `2`). -/
noncomputable def cr (G : SimpleGraph V) : ℕ :=
  sInf {n | ∃ D : Drawing G, D.Good ∧ n = D.crossings.ncard / 2}

/-- The `d`-dimensional hypercube graph. -/
def hypercube (d : ℕ) : SimpleGraph (Fin d → Bool) :=
  SimpleGraph.fromRel fun x y => (Finset.univ.filter fun i => x i ≠ y i).card = 1

/-- `cr(Q_d) / 4^d → 5/32`. -/
theorem main :
    Tendsto (fun d : ℕ => (cr (hypercube d) : ℝ) / 4 ^ d) atTop (𝓝 (5 / 32)) := by
  sorry

end OMA.S_opg_the_crossing_number_of_the_hypercube
