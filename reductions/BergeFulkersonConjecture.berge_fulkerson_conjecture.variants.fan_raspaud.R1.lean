import FormalConjectures.Wikipedia.BergeFulkersonConjecture

-- Reduction BergeFulkersonConjecture.berge_fulkerson_conjecture.variants.fan_raspaud.R1
-- of the Fan-Raspaud conjecture
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The Fan-Raspaud conjecture, split by oddness

A perfect matching `M` of a cubic graph `G` leaves a 2-factor `G - M`, a disjoint union of
circuits. The oddness of `G` is the least number of odd circuits in such a 2-factor. Here the
odd circuits of `G - M` are counted as the connected components of `G.deleteEdges M.edgeSet`
with an odd number of vertices.

* `H1` (known): the Fan-Raspaud conjecture for bridgeless cubic graphs of oddness at most 2.
  Oddness 0 is the 3-edge-colourable case, where the three colour classes are pairwise disjoint
  perfect matchings. Oddness 2 is the theorem of E. Macajova and M. Skoviera, *Sparsely
  intersecting perfect matchings in cubic graphs*, Combinatorica 34 (2014), 61-94.
* `H2` (open): the Fan-Raspaud conjecture for bridgeless cubic graphs of oddness greater than 2,
  that is, every 2-factor that is the complement of a perfect matching has more than two odd
  circuits. This is the target restricted to a subclass of graphs, so it is no stronger than
  the target.

`main` is the case distinction on whether some perfect matching leaves at most two odd circuits.
-/

namespace OMA.R_BergeFulkersonConjecture_berge_fulkerson_conjecture_variants_fan_raspaud_R1

open SimpleGraph BergeFulkersonConjecture

/-- Fan-Raspaud for oddness at most 2 (Macajova and Skoviera 2014; oddness 0 is the
3-edge-colourable case). -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    IsCubic G → G.IsBridgeless →
    (∃ N : G.Subgraph, N.IsPerfectMatching ∧
      {c : (G.deleteEdges N.edgeSet).ConnectedComponent | Odd c.supp.ncard}.ncard ≤ 2) →
    ∃ M : Fin 3 → G.Subgraph, (∀ i, (M i).IsPerfectMatching) ∧
      ∀ e, ¬ (e ∈ (M 0).edgeSet ∧ e ∈ (M 1).edgeSet ∧ e ∈ (M 2).edgeSet)

/-- Fan-Raspaud for oddness greater than 2: the open part. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    IsCubic G → G.IsBridgeless →
    (∀ N : G.Subgraph, N.IsPerfectMatching →
      2 < {c : (G.deleteEdges N.edgeSet).ConnectedComponent | Odd c.supp.ncard}.ncard) →
    ∃ M : Fin 3 → G.Subgraph, (∀ i, (M i).IsPerfectMatching) ∧
      ∀ e, ¬ (e ∈ (M 0).edgeSet ∧ e ∈ (M 1).edgeSet ∧ e ∈ (M 2).edgeSet)

theorem main : H1 → H2 →
    type_of% @BergeFulkersonConjecture.berge_fulkerson_conjecture.variants.fan_raspaud := by
  intro h1 h2 V _ _ G _ hcubic hbr
  by_cases h : ∃ N : G.Subgraph, N.IsPerfectMatching ∧
      {c : (G.deleteEdges N.edgeSet).ConnectedComponent | Odd c.supp.ncard}.ncard ≤ 2
  · exact h1 G hcubic hbr h
  · refine h2 G hcubic hbr fun N hN => ?_
    by_contra hlt
    exact h ⟨N, hN, not_lt.mp hlt⟩

end OMA.R_BergeFulkersonConjecture_berge_fulkerson_conjecture_variants_fan_raspaud_R1
