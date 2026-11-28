import OMAStatements.S_opg_intersecting_two_perfect_matchings

/-!
Reduction opg-intersecting-two-perfect-matchings.R1 of The intersection of two perfect matchings.

The target asks, for every bridgeless cubic graph, for two perfect matchings whose common
edges contain no odd edge-cut. The two stages are independent:

* H1 is Petersens 1891 theorem in this encoding: every bridgeless cubic graph admits at
  least one perfect matching.
* H2 is the relative second-matching step: given one perfect matching of such a graph, a
  second perfect matching can be chosen so that the two matchings share no edge cut of odd
  size. The main proof only assembles the two witnesses.
-/

namespace OMA.R_opg_intersecting_two_perfect_matchings_R1

open SimpleGraph OMA.S_opg_intersecting_two_perfect_matchings

/-- Petersens theorem: every bridgeless cubic graph has a perfect matching. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsRegularOfDegree 3 → (∀ e ∈ G.edgeSet, ¬ G.IsBridge e) →
      ∃ M₁ : G.Subgraph, M₁.IsPerfectMatching

/-- Given a perfect matching of a bridgeless cubic graph, a second perfect matching can be
chosen so that their intersection contains no odd edge-cut. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsRegularOfDegree 3 → (∀ e ∈ G.edgeSet, ¬ G.IsBridge e) →
      ∀ M₁ : G.Subgraph, M₁.IsPerfectMatching →
        ∃ M₂ : G.Subgraph, M₂.IsPerfectMatching ∧
          ¬ ContainsOddEdgeCut G (M₁.edgeSet ∩ M₂.edgeSet)

theorem main : H1 → H2 → type_of% @OMA.S_opg_intersecting_two_perfect_matchings.main := by
  intro h1 h2 V _ G _ hreg hbridge
  obtain ⟨M₁, hM₁⟩ := h1 V G hreg hbridge
  obtain ⟨M₂, hM₂, hNoCut⟩ := h2 V G hreg hbridge M₁ hM₁
  exact ⟨M₁, M₂, hM₁, hM₂, hNoCut⟩

end OMA.R_opg_intersecting_two_perfect_matchings_R1
