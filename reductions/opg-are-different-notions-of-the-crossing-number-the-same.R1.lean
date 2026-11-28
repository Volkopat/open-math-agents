import OMAStatements.S_opg_are_different_notions_of_the_crossing_number_the_same

-- Reduction opg-are-different-notions-of-the-crossing-number-the-same.R1 of
-- Are different notions of the crossing number the same?
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- H1 is the classical easy half (Pach-Toth 2000): every drawing has at least as many crossing
-- points as crossing pairs of edges, so pcr G <= cr G, and the planar case pcr G = 0 forces
-- cr G = 0. H2 is the open part: cr G <= pcr G for every non-planar graph.

namespace OMA.R_opg_are_different_notions_of_the_crossing_number_the_same_R1

open OMA.S_opg_are_different_notions_of_the_crossing_number_the_same

/-- Pach-Toth: `pcr G ≤ cr G` for every graph, with equality (both zero) in the planar case
`pcr G = 0`. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), pcr G ≤ cr G ∧ (pcr G = 0 → cr G = 0)

/-- The open core: `cr G ≤ pcr G` for every graph with positive pair-crossing number. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), 0 < pcr G → cr G ≤ pcr G

theorem main : H1 → H2 → type_of% @OMA.S_opg_are_different_notions_of_the_crossing_number_the_same.main := by
  intro h1 h2 V _ G
  obtain ⟨hle, h0⟩ := h1 V G
  rcases Nat.eq_zero_or_pos (pcr G) with h | h
  · rw [h0 h, h]
  · exact le_antisymm (h2 V G h) hle

end OMA.R_opg_are_different_notions_of_the_crossing_number_the_same_R1
