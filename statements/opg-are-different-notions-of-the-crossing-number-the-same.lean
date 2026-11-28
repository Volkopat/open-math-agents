import Mathlib

/-!
# Are different notions of the crossing number the same?

Source: https://www.openproblemgarden.org/op/are_different_notions_of_the_crossing_number_the_same
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Problem (Pach–Tóth): does `cr(G) = pcr(G)` hold for every graph `G`?

Conventions:
* Graphs are finite simple graphs. A drawing places the vertices at distinct points of the plane
  and each edge as an arc (an injective path) between its endpoints whose interior avoids all
  vertices. Both orientations of an edge carry the same arc.
* Following the usual convention (Pach–Tóth, "Which crossing number is it anyway?"), only
  drawings in which any two distinct edges meet in finitely many interior points are allowed.
  `cr` minimises the total number of common interior points over pairs of distinct edges;
  `pcr` minimises the number of pairs of distinct edges that meet. Touching points and points
  shared by three or more edges are counted like crossings (pairwise); a local redrawing removes
  them without increasing either count, so the two minima agree with the usual definitions.
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer
  no.
-/

namespace OMA.S_opg_are_different_notions_of_the_crossing_number_the_same

open Set

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

/-- Ordered pairs of distinct edges whose arcs meet in an interior point. -/
def Drawing.crossingPairs (D : Drawing G) : Set (Sym2 V × Sym2 V) :=
  {p | p.1 ∈ G.edgeSet ∧ p.2 ∈ G.edgeSet ∧ p.1 ≠ p.2 ∧ (D.inner p.1 ∩ D.inner p.2).Nonempty}

/-- Admissible drawings: every two distinct edges meet in finitely many interior points. -/
def Drawing.Good (D : Drawing G) : Prop := D.crossings.Finite

/-- The crossing number. -/
noncomputable def cr (G : SimpleGraph V) : ℕ :=
  sInf {n | ∃ D : Drawing G, D.Good ∧ n = D.crossings.ncard / 2}

/-- The pair-crossing number. -/
noncomputable def pcr (G : SimpleGraph V) : ℕ :=
  sInf {n | ∃ D : Drawing G, D.Good ∧ n = D.crossingPairs.ncard / 2}

theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V), cr G = pcr G := by
  sorry

end OMA.S_opg_are_different_notions_of_the_crossing_number_the_same
