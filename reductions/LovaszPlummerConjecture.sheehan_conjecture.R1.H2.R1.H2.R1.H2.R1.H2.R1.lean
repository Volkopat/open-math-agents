import OMAReductions.R_LovaszPlummerConjecture_sheehan_conjecture_R1_H2_R1_H2_R1_H2_R1
import Mathlib

/-! A complete three-by-three bipartite subgraph can be detected from the marked cycle in every quartic host. -/
namespace OMA.R_LovaszPlummerConjecture_sheehan_conjecture_R1_H2_R1_H2_R1_H2_R1_H2_R1
open SimpleGraph Finset LovaszPlummerConjecture

private lemma rim_degree {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {v : V} {c : G.Walk v v} (hc : IsHamiltonianCycle G c) (x : V) :
    letI := Classical.decRel c.toSubgraph.spanningCoe.Adj
    c.toSubgraph.spanningCoe.degree x = 2 := by
  classical
  let R := c.toSubgraph.spanningCoe
  have card : (R.neighborSet x).ncard = R.degree x := by
    rw [Set.ncard_eq_toFinset_card']
    exact R.card_neighborFinset_eq_degree x
  exact card.symm.trans (hc.1.ncard_neighborSet_toSubgraph_eq_two (hc.2 x))

private theorem no_three {V : Type} [Fintype V] [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj] {z r s t : V}
    (bound : K.degree z≤2) (rs : r≠s) (rt : r≠t) (st : s≠t)
    (hr : K.Adj z r) (hs : K.Adj z s) (ht : K.Adj z t) : False := by
  have sub : ({r,s,t} : Finset V)⊆K.neighborFinset z := by
    intro v hv
    simp only [mem_insert,mem_singleton] at hv
    rcases hv with rfl|rfl|rfl <;> apply (K.mem_neighborFinset _ _).mpr <;> assumption
  have card := card_le_card sub
  have count : ({r,s,t} : Finset V).card=3 := by simp [rs,rt,st]
  rw [count,card_neighborFinset_eq_degree] at card
  omega

private theorem touches {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {v : V} (c : G.Walk v v)
    (hc : IsHamiltonianCycle G c) (l r : Fin 3 ↪ V) (all : ∀ i j,G.Adj (l i) (r j))
    (bound : ∀ i,G.degree (l i)≤4) (i : Fin 3) : ∃ j,s(l i,r j)∈c.edges := by
  classical
  by_contra! misses
  let R := c.toSubgraph.spanningCoe
  let F := G\R
  have sub : R.neighborFinset (l i) ⊆ G.neighborFinset (l i) := fun x hx =>
    (G.mem_neighborFinset ..).mpr (c.toSubgraph.spanningCoe_le ((R.mem_neighborFinset ..).mp hx))
  have two : R.degree (l i)=2 := rim_degree hc _
  have small : F.degree (l i)≤2 := by
    change (G\R).degree (l i)≤2
    rw [←card_neighborFinset_eq_degree,neighborFinset_sdiff,card_sdiff_of_subset sub,
      card_neighborFinset_eq_degree,card_neighborFinset_eq_degree,two]
    have := bound i
    omega
  have adjacent (j) : F.Adj (l i) (r j) :=
    ⟨all i j,fun h => misses j (Walk.adj_toSubgraph_iff_mem_edges.mp h)⟩
  exact no_three F small (r.injective.ne (by decide : (0:Fin 3)≠1))
    (r.injective.ne (by decide : (0:Fin 3)≠2)) (r.injective.ne (by decide : (1:Fin 3)≠2))
    (adjacent 0) (adjacent 1) (adjacent 2)

/-- Local exchanges on three pairs in an arbitrary finite simple graph.
All adjacencies on a vertex outside the six displayed ones are preserved. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (c : G.Walk v v),IsHamiltonianCycle G c →
    ∀ l r : Fin 3 ↪ V,(∀ i j,G.Adj (l i) (r j)) → (∀ i,∃ j,s(l i,r j)∈c.edges) →
    ∃ (w : V) (d : G.Walk w w),IsHamiltonianCycle G d ∧ d.edges.toFinset≠c.edges.toFinset ∧
      ∀ x y,((∀ i,x≠l i ∧ x≠r i) ∨ (∀ j,y≠l j ∧ y≠r j)) →
        (s(x,y)∈d.edges ↔ s(x,y)∈c.edges)

open scoped Classical in
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (_four : ∀ u, G.degree u=4) (v : V) (c : G.Walk v v), IsHamiltonianCycle G c →
    (¬ ∃ (M : SimpleGraph V) (e : Sym2 V), M ≤ G ∧ e ∈ c.edges ∧
      (∀ u, M.degree u ≤ 1) ∧ (∀ u, M.degree u = 0 → u ∈ e) ∧
      (∀ f ∈ c.edges, f ∉ M.edgeSet)) →
    (¬ ∃ I : Finset V, I.Nonempty ∧
      (∀ x ∈ I, ∀ y ∈ I, s(x,y) ∉ c.edges) ∧
      (∀ u : V, u ∉ I → (∃ x ∈ I, s(u,x) ∈ c.edges) →
        ∃ w ∈ I, G.Adj u w ∧ s(u,w) ∉ c.edges)) →
    ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ (e : Fin n ≃ V),
    (∀ x y, s(x,y) ∈ c.edges ↔ ∃ i : Fin n, s(x,y)=s(e i,e (i+1))) →
    ∀ i j : Fin n, G.Adj (e i) (e j) → ¬G.Adj (e (i+2)) (e (j+2)) →
    (∀ (q : (G\c.toSubgraph.spanningCoe).ConnectedComponent) (lo hi : Fin n),lo≤hi →
      ¬∀ s : Fin n,e s∈q.supp ↔ lo ≤ s ∧ s≤hi) →
    (∃ a b u w : Fin n,a<b ∧ b<u ∧ u<w ∧
      (G\c.toSubgraph.spanningCoe).Reachable (e a) (e u) ∧
      (G\c.toSubgraph.spanningCoe).Reachable (e b) (e w) ∧
      ¬(G\c.toSubgraph.spanningCoe).Reachable (e a) (e b)) →
    (¬∃ l r : Fin 3 ↪ V,∀ i j,G.Adj (l i) (r j)) →
    ∃ (w : V) (d : G.Walk w w), IsHamiltonianCycle G d ∧ d.edges.toFinset ≠ c.edges.toFinset

theorem main : H1 → H2 → OMA.R_LovaszPlummerConjecture_sheehan_conjecture_R1_H2_R1_H2_R1_H2_R1.H2 := by
  classical
  intro reroute remaining V _ _ G _ four v c hc unmatched undominated n _ hn e rim i j chord absent unbroken interlaced
  by_cases present : ∃ l r : Fin 3 ↪ V,∀ i j,G.Adj (l i) (r j)
  · obtain ⟨l,r,edges⟩ := present
    have marks := touches G c hc l r edges (fun a => (four _).le)
    obtain ⟨w,d,ham,diff,_⟩ := reroute G v c hc l r edges marks
    exact ⟨w,d,ham,diff⟩
  · exact remaining G four v c hc unmatched undominated n hn e rim i j chord absent unbroken interlaced present

end OMA.R_LovaszPlummerConjecture_sheehan_conjecture_R1_H2_R1_H2_R1_H2_R1_H2_R1
