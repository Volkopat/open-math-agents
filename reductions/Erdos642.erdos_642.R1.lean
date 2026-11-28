import FormalConjectures.ErdosProblems.«642»

-- Credit: @PetrouilFan

/-!
Reduction of Erdos642.erdos_642 (Erdos problem 642: is the maximal edge count
f(n) of a graph on n vertices in which every cycle has more vertices than chords
linearly bounded?).

H1 is the genuinely open combinatorial core: a uniform constant C bounding the
edge count of every admissible finite graph linearly in its vertex count.

H2 is the upstream-proved transfer lemma `Erdos642.isBigO_iff_uniform_edge_bound`
(backward direction, category API, full proof in the FormalConjectures module):
a uniform linear edge bound implies the asymptotic statement f(n) = O(n).

The main theorem applies the proved transfer direction to the open core. Neither
hypothesis mentions the target, main, or each other.
-/

open Filter Asymptotics

namespace OMA.R_Erdos642_erdos_642_R1

/-- Genuinely open core: a uniform linear bound on admissible finite graphs. -/
def H1 : Prop :=
  ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    Erdos642.CyclesHaveMoreVerticesThanChords G → (G.edgeSet.ncard : ℝ) ≤ C * n

/-- Upstream-proved transfer direction of isBigO_iff_uniform_edge_bound. -/
def H2 : Prop :=
  ∀ C : ℝ,
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      Erdos642.CyclesHaveMoreVerticesThanChords G → (G.edgeSet.ncard : ℝ) ≤ C * n) →
    ((fun n : ℕ => (Erdos642.maxEdges n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)))

theorem main : H1 → H2 → type_of% @Erdos642.erdos_642 := by
  intro h1 h2
  obtain ⟨C, hC⟩ := h1
  exact h2 C hC

end OMA.R_Erdos642_erdos_642_R1
