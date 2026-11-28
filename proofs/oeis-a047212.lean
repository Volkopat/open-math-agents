import OMAStatements.S_oeis_a047212

/-!
# The arboricity of the square queen graph

We prove Eric Weisstein's arboricity conjecture in OEIS A047212.
For a set of s squares, route the s(n²-s) ordered pairs leaving the set
first along a row and then along a column. Each directed edge leaving the
set carries at most n of these routes. Subtracting this boundary from
the degree sum, bounded both directly and from the complementary set,
gives the Nash-Williams inequalities. The whole board forces the answer.
Credit for the queen-graph argument: @asher-lanzone (opencode, gpt-6.2-astra).

The general forest-cover criterion below is Nash-Williams' 1964 theorem,
formalized by Juan Pablo Traverso Gianini (LeanPool, Apache-2.0).
The following block is adapted from Auxiliary.lean and Theorems.lean in
https://github.com/LeanPool/lean-pool/tree/432e18b03cfb58eca4e6ee9b3244d6bd6657140e/LeanPool/NashWilliamsTutte .
Unused tree-packing helpers are omitted, and the section parameters are explicit.
-/


/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/


open Finset Fintype SimpleGraph Function

namespace NashWilliamsTutte

variable {V : Type*}

/-- Reachability transfers along a map that sends adjacent vertices to reachable ones. -/
theorem reachable_map_of_adj {W : Type*} {A : SimpleGraph V} {B : SimpleGraph W} (g : V → W)
    (h : ∀ a b, A.Adj a b → B.Reachable (g a) (g b)) {a b : V} (hab : A.Reachable a b) :
    B.Reachable (g a) (g b) := by
  obtain ⟨p⟩ := hab
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (h _ _ hadj).trans ih

/-- Disjointness of simple graphs in terms of adjacency. -/
theorem disjoint_iff_adj {A B : SimpleGraph V} :
    Disjoint A B ↔ ∀ a b, A.Adj a b → ¬ B.Adj a b := by
  rw [← disjoint_edgeSet, Set.disjoint_left]
  constructor
  · intro h a b ha hb
    exact h (show s(a, b) ∈ A.edgeSet from ha) hb
  · intro h e
    induction e using Sym2.ind with
    | _ a b => exact fun ha hb ↦ h a b ha hb

/-- The sum of the sizes of pairwise disjoint subsets of a finite set is at most its size. -/
theorem sum_ncard_le_of_pairwise_disjoint {ι α : Type*} [Fintype ι] [Finite α] (A : ι → Set α)
    (B : Set α) (hAB : ∀ i, A i ⊆ B) (hd : Pairwise (Disjoint on A)) :
    ∑ i, (A i).ncard ≤ B.ncard := by
  have h := Set.ncard_iUnion_of_finite (s := A) (fun i ↦ Set.toFinite _) hd
  rw [finsum_eq_sum_of_fintype] at h
  rw [← h]
  exact Set.ncard_le_ncard (Set.iUnion_subset hAB)

/-- A forest on a finite nonempty vertex type has at most `|V| - 1` edges, and exactly `|V| - 1`
only if it is a tree. -/
theorem IsAcyclic.ncard_edgeSet_add_one_le [Finite V] [Nonempty V] {F : SimpleGraph V}
    (hF : F.IsAcyclic) :
    F.edgeSet.ncard + 1 ≤ Nat.card V ∧ (Nat.card V ≤ F.edgeSet.ncard + 1 → F.IsTree) := by
  obtain ⟨T, hFT, hT⟩ := exists_maximal_isAcyclic_of_le_isAcyclic (le_top : F ≤ ⊤) hF
  have hT' : T.IsTree := by
    rw [← maximal_isAcyclic_iff_isTree]
    exact ⟨hT.1.2, fun H hH hle ↦ hT.2 ⟨le_top, hH⟩ hle⟩
  have hcard := (isTree_iff_connected_and_card.1 hT').2
  rw [Nat.card_coe_set_eq] at hcard
  have hsub : F.edgeSet ⊆ T.edgeSet := edgeSet_mono hFT
  have hle : F.edgeSet.ncard ≤ T.edgeSet.ncard := Set.ncard_le_ncard hsub
  refine ⟨by omega, fun h ↦ ?_⟩
  have heq : F.edgeSet = T.edgeSet := Set.eq_of_subset_of_ncard_le hsub (by omega)
  rwa [edgeSet_inj.1 heq]

/-- Deleting an edge of the unique path between `u` and `v` in a forest disconnects `u` from
`v`. -/
theorem not_reachable_deleteEdges_of_mem_edges {F : SimpleGraph V} (hF : F.IsAcyclic) {u v x y : V}
    (p : F.Walk u v) (hp : p.IsPath) (he : s(x, y) ∈ p.edges) :
    ¬ (F.deleteEdges {s(x, y)}).Reachable u v := by
  classical
  rintro ⟨q⟩
  have hq : (q.bypass.mapLe (deleteEdges_le _)).IsPath := (Walk.isPath_mapLe _).2 q.bypass_isPath
  have := (hF.subsingleton_path u v).elim ⟨p, hp⟩ ⟨_, hq⟩
  simp only [Subtype.mk.injEq] at this
  rw [this, Walk.edges_mapLe_eq_edges] at he
  have := q.bypass.edges_subset_edgeSet he
  simp [edgeSet_deleteEdges] at this

section Exchange

variable (G : SimpleGraph V) {k : ℕ}

/-- `k` pairwise edge-disjoint forests in `G`. -/
def ValidForests (F : Fin k → SimpleGraph V) : Prop :=
  (∀ i, F i ≤ G ∧ (F i).IsAcyclic) ∧ Pairwise fun i j ↦ Disjoint (F i) (F j)

/-- The total number of edges of a family of graphs. -/
noncomputable def totalEdges (F : Fin k → SimpleGraph V) : ℕ := ∑ i, (F i).edgeSet.ncard

/-- `uv` is an edge of `G` not covered by the family `F`. -/
def Uncovered (F : Fin k → SimpleGraph V) (u v : V) : Prop := G.Adj u v ∧ ∀ j, ¬ (F j).Adj u v

/-- One exchange step: an uncovered edge `uv` replaces an edge `xy` of some `F i`, keeping it
acyclic. -/
def ExchangeStep (F F' : Fin k → SimpleGraph V) : Prop :=
  ∃ i u v x y, Uncovered G F u v ∧ (F i).Adj x y ∧
    ((F i).deleteEdges {s(x, y)} ⊔ edge u v).IsAcyclic ∧
    F' = update F i ((F i).deleteEdges {s(x, y)} ⊔ edge u v)

variable {G}

theorem total_update (F : Fin k → SimpleGraph V) (i : Fin k) (X : SimpleGraph V) :
    totalEdges (update F i X) + (F i).edgeSet.ncard = totalEdges F + X.edgeSet.ncard := by
  simp only [totalEdges]
  rw [show (fun j ↦ (update F i X j).edgeSet.ncard) =
      update (fun j ↦ (F j).edgeSet.ncard) i X.edgeSet.ncard from
    funext fun j ↦ apply_update (fun _ (H : SimpleGraph V) ↦ H.edgeSet.ncard) F i X j]
  rw [Finset.sum_update_of_mem (mem_univ i), Finset.sdiff_singleton_eq_erase]
  have := Finset.add_sum_erase univ (fun j ↦ (F j).edgeSet.ncard) (mem_univ i)
  omega

theorem Uncovered.adj_iff {F : Fin k → SimpleGraph V} {u v : V} (h : Uncovered G F u v) {j : Fin k}
    {a b : V} (hab : s(a, b) = s(u, v)) : ¬ (F j).Adj a b := by
  rcases Sym2.eq_iff.1 hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h.2 j
  · exact fun h' ↦ h.2 j h'.symm

theorem adj_new {F : SimpleGraph V} {x y u v a b : V}
    (h : (F.deleteEdges {s(x, y)} ⊔ edge u v).Adj a b) :
    (F.Adj a b ∧ s(a, b) ≠ s(x, y)) ∨ s(a, b) = s(u, v) := by
  rcases h with h | h
  · rw [deleteEdges_adj] at h
    exact Or.inl ⟨h.1, h.2⟩
  · rw [edge_adj] at h
    right
    rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact Sym2.eq_swap

/-- Replacing `F i` by a graph `X ≤ G` whose edges are edges of `F i` or uncovered edges keeps
the family valid, provided `X` is acyclic. -/
theorem ValidForests.update {F : Fin k → SimpleGraph V} (hF : ValidForests G F)
    (i : Fin k) {X : SimpleGraph V}
    (hXG : X ≤ G) (hX : X.IsAcyclic)
    (hXadj : ∀ a b, X.Adj a b → (F i).Adj a b ∨ ∀ j, ¬ (F j).Adj a b) :
    ValidForests G (update F i X) := by
  refine ⟨fun j ↦ ?_, fun j₁ j₂ hj ↦ ?_⟩
  · by_cases hj : j = i
    · subst hj; simpa using ⟨hXG, hX⟩
    · simpa [hj] using hF.1 j
  · have key : ∀ j, j ≠ i → Disjoint X (F j) := by
      intro j hji
      rw [disjoint_iff_adj]
      intro a b hab
      rcases hXadj a b hab with h | h
      · exact (disjoint_iff_adj.1 (hF.2 (Ne.symm hji))) a b h
      · exact h j
    by_cases h₁ : j₁ = i
    · subst h₁
      simpa [Ne.symm hj] using key j₂ (Ne.symm hj)
    · by_cases h₂ : j₂ = i
      · subst h₂
        simpa [h₁] using (key j₁ h₁).symm
      · simpa [h₁, h₂] using hF.2 hj

theorem ExchangeStep.valid {F F' : Fin k → SimpleGraph V} (hF : ValidForests G F)
    (h : ExchangeStep G F F') :
    ValidForests G F' := by
  obtain ⟨i, u, v, x, y, huv, hxy, hac, rfl⟩ := h
  refine hF.update i (sup_le ((deleteEdges_le _).trans (hF.1 i).1)
    ((edge_le_iff _).2 (Or.inr huv.1))) hac fun a b hab ↦ ?_
  rcases adj_new hab with h | h
  · exact Or.inl h.1
  · exact Or.inr fun j ↦ huv.adj_iff h

theorem ExchangeStep.total_eq [Finite V] {F F' : Fin k → SimpleGraph V} (h : ExchangeStep G F F') :
    totalEdges F' = totalEdges F := by
  obtain ⟨i, u, v, x, y, huv, hxy, hac, rfl⟩ := h
  have h1 := total_update F i ((F i).deleteEdges {s(x, y)} ⊔ edge u v)
  have hne : u ≠ v := huv.1.ne
  have h2 : ((F i).deleteEdges {s(x, y)} ⊔ edge u v).edgeSet.ncard = (F i).edgeSet.ncard := by
    rw [edgeSet_sup, edgeSet_deleteEdges, edgeSet_edge_of_ne hne,
      Set.ncard_union_eq (s := (F i).edgeSet \ {s(x, y)})
        (Set.disjoint_singleton_right.2 fun h ↦ huv.2 i h.1) (Set.toFinite _)
        (Set.toFinite _), Set.ncard_singleton]
    exact Set.ncard_sdiff_singleton_add_one (show s(x, y) ∈ (F i).edgeSet from hxy)
      (Set.toFinite _)
  omega

/-- In a family with the maximum total number of edges, the endpoints of an uncovered edge are
joined in every forest. -/
theorem reachable_of_uncovered [Finite V] {F : Fin k → SimpleGraph V} (hF : ValidForests G F)
    (hmax : ∀ F' : Fin k → SimpleGraph V, ValidForests G F' → totalEdges F' ≤ totalEdges F)
    {u v : V}
    (huv : Uncovered G F u v) (i : Fin k) :
    (F i).Reachable u v := by
  by_contra h
  have hval : ValidForests G (update F i (F i ⊔ edge u v)) := by
    refine hF.update i (sup_le (hF.1 i).1 ((edge_le_iff _).2 (Or.inr huv.1)))
      ((hF.1 i).2.sup_edge_of_not_reachable h) fun a b hab ↦ ?_
    rcases hab with hab | hab
    · exact Or.inl hab
    · right
      intro j
      apply huv.adj_iff
      rw [edge_adj] at hab
      rcases hab.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact Sym2.eq_swap
  have h1 := total_update F i (F i ⊔ edge u v)
  have h2 : (F i ⊔ edge u v).edgeSet.ncard = (F i).edgeSet.ncard + 1 := by
    rw [edgeSet_sup, edgeSet_edge_of_ne huv.1.ne,
      Set.ncard_union_eq
        (Set.disjoint_singleton_right.2 (show s(u, v) ∉ (F i).edgeSet from huv.2 i))
        (Set.toFinite _)
        (Set.toFinite _), Set.ncard_singleton]
  have h3 := hmax _ hval
  omega

theorem ExchangeStep.uncovered {F : Fin k → SimpleGraph V} (hF : ValidForests G F)
    {i : Fin k} {u v x y : V}
    (huv : Uncovered G F u v) (hxy : (F i).Adj x y) :
    Uncovered G (update F i ((F i).deleteEdges {s(x, y)} ⊔ edge u v)) x y := by
  refine ⟨(hF.1 i).1 hxy, fun j ↦ ?_⟩
  by_cases hj : j = i
  · subst hj
    simp only [update_self]
    intro h
    rcases adj_new h with h | h
    · exact h.2 rfl
    · exact huv.adj_iff h hxy
  · simp only [update_of_ne hj]
    exact disjoint_iff_adj.1 (hF.2 (Ne.symm hj)) x y hxy

end Exchange

section Core

variable {G : SimpleGraph V} {k : ℕ}

/-- The graph of all edges of `G` that are uncovered in some family obtained from `F₀` by a
sequence of exchange steps. -/
def exchangeGraph (G : SimpleGraph V) (F₀ : Fin k → SimpleGraph V) : SimpleGraph V where
  Adj a b := ∃ F, Relation.ReflTransGen (ExchangeStep G) F₀ F ∧ Uncovered G F a b
  symm := ⟨fun _ _ ⟨F, h, hu⟩ ↦ ⟨F, h, hu.1.symm, fun j h' ↦ hu.2 j h'.symm⟩⟩
  loopless := ⟨fun _ ⟨_, _, hu⟩ ↦ hu.1.ne rfl⟩

theorem exchangeGraph_adj {F₀ : Fin k → SimpleGraph V} {a b : V} :
    (exchangeGraph G F₀).Adj a b ↔
      ∃ F, Relation.ReflTransGen (ExchangeStep G) F₀ F ∧ Uncovered G F a b :=
  Iff.rfl

variable [Finite V] {F₀ : Fin k → SimpleGraph V}

theorem reach_valid (hF₀ : ValidForests G F₀) {F : Fin k → SimpleGraph V} (hF : Relation.ReflTransGen (ExchangeStep G) F₀ F) :
    ValidForests G F ∧ totalEdges F = totalEdges F₀ := by
  induction hF with
  | refl => exact ⟨hF₀, rfl⟩
  | tail _ hstep ih => exact ⟨hstep.valid ih.1, hstep.total_eq.trans ih.2⟩

theorem reach_uncovered_reachable (hF₀ : ValidForests G F₀)
    (hmax : ∀ F : Fin k → SimpleGraph V, ValidForests G F → totalEdges F ≤ totalEdges F₀) {F : Fin k → SimpleGraph V}
    (hF : Relation.ReflTransGen (ExchangeStep G) F₀ F) {u v : V}
    (huv : Uncovered G F u v) (i : Fin k) :
    (F i ⊓ exchangeGraph G F₀).Reachable u v := by
  classical
  obtain ⟨hval, htot⟩ := reach_valid hF₀ hF
  have hr := reachable_of_uncovered hval (fun F' hF' ↦ htot ▸ hmax F' hF') huv i
  obtain ⟨w⟩ := hr
  set p := w.bypass
  have hp : p.IsPath := w.bypass_isPath
  refine ⟨p.transfer _ fun e he ↦ ?_⟩
  induction e using Sym2.ind with
  | _ x y =>
    have hxy : (F i).Adj x y := p.edges_subset_edgeSet he
    refine ⟨hxy, exchangeGraph_adj.2
      ⟨update F i ((F i).deleteEdges {s(x, y)} ⊔ edge u v), ?_,
        ExchangeStep.uncovered hval huv hxy⟩⟩
    refine hF.tail ⟨i, u, v, x, y, huv, hxy, ?_, rfl⟩
    exact ((hval.1 i).2.anti (deleteEdges_le _)).sup_edge_of_not_reachable
      (not_reachable_deleteEdges_of_mem_edges (hval.1 i).2 p hp he)

theorem step_reachable_iff (hF₀ : ValidForests G F₀)
    (hmax : ∀ F : Fin k → SimpleGraph V, ValidForests G F → totalEdges F ≤ totalEdges F₀) {F F' : Fin k → SimpleGraph V}
    (hF : Relation.ReflTransGen (ExchangeStep G) F₀ F) (hstep : ExchangeStep G F F')
    (j : Fin k) (a b : V) :
    (F j ⊓ exchangeGraph G F₀).Reachable a b ↔ (F' j ⊓ exchangeGraph G F₀).Reachable a b := by
  classical
  have hF' : Relation.ReflTransGen (ExchangeStep G) F₀ F' := hF.tail hstep
  have hval := (reach_valid hF₀ hF).1
  obtain ⟨i, u, v, x, y, huv, hxy, hac, rfl⟩ := hstep
  by_cases hj : j = i
  swap
  · simp only [update_of_ne hj]
  subst hj
  simp only [update_self]
  constructor
  · refine reachable_map_of_adj id fun c d hcd ↦ ?_
    by_cases hc : s(c, d) = s(x, y)
    · have h := reach_uncovered_reachable hF₀ hmax hF' (ExchangeStep.uncovered hval huv hxy) j
      simp only [update_self] at h
      rcases Sym2.eq_iff.1 hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h
      · exact h.symm
    · exact Adj.reachable
        ⟨Or.inl (deleteEdges_adj.2 ⟨hcd.1, fun h ↦ hc (Set.mem_singleton_iff.1 h)⟩), hcd.2⟩
  · refine reachable_map_of_adj id fun c d hcd ↦ ?_
    rcases adj_new hcd.1 with h | h
    · exact Adj.reachable ⟨h.1, hcd.2⟩
    · have h' := reach_uncovered_reachable hF₀ hmax hF huv j
      rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h'
      · exact h'.symm

theorem reach_reachable_iff (hF₀ : ValidForests G F₀)
    (hmax : ∀ F : Fin k → SimpleGraph V, ValidForests G F → totalEdges F ≤ totalEdges F₀) {F : Fin k → SimpleGraph V}
    (hF : Relation.ReflTransGen (ExchangeStep G) F₀ F) (j : Fin k) (a b : V) :
    (F j ⊓ exchangeGraph G F₀).Reachable a b ↔ (F₀ j ⊓ exchangeGraph G F₀).Reachable a b := by
  induction hF with
  | refl => rfl
  | tail h hstep ih => exact (step_reachable_iff hF₀ hmax h hstep j a b).symm.trans ih

end Core

/-- **Core exchange lemma.** For every finite graph `G` there are `k` pairwise edge-disjoint
forests `F i ≤ G` and a subgraph `H ≤ G` such that each `F i ⊓ H` has the same connected
components as `H`, and every edge of `G` outside `H` belongs to some `F i`. -/
theorem exists_forests_core [Finite V] (G : SimpleGraph V) (k : ℕ) :
    ∃ (F : Fin k → SimpleGraph V) (H : SimpleGraph V), (∀ i, F i ≤ G ∧ (F i).IsAcyclic) ∧
      (Pairwise fun i j ↦ Disjoint (F i) (F j)) ∧ H ≤ G ∧
      (∀ i a b, H.Reachable a b → (F i ⊓ H).Reachable a b) ∧
      (∀ a b, G.Adj a b → ¬ H.Adj a b → ∃ i, (F i).Adj a b) := by
  have : Finite (SimpleGraph V) := Finite.of_injective _ fun _ _ h ↦ SimpleGraph.ext h
  have hval0 : ValidForests G (fun _ : Fin k ↦ (⊥ : SimpleGraph V)) :=
    ⟨fun _ ↦ ⟨bot_le, isAcyclic_bot⟩, fun _ _ _ ↦ disjoint_bot_left⟩
  obtain ⟨F₀, hF₀, hmax⟩ := Set.exists_max_image
    {F : Fin k → SimpleGraph V | ValidForests G F} totalEdges (Set.toFinite _) ⟨_, hval0⟩
  refine ⟨F₀, exchangeGraph G F₀, hF₀.1, hF₀.2, fun a b h ↦ ?_, fun i a b hab ↦ ?_,
    fun a b hab hH ↦ ?_⟩
  · obtain ⟨_, _, hu⟩ := exchangeGraph_adj.1 h
    exact hu.1
  · refine reachable_map_of_adj id (fun c d h ↦ ?_) hab
    obtain ⟨F, hF, hu⟩ := exchangeGraph_adj.1 h
    exact (reach_reachable_iff hF₀ hmax hF i c d).1 (reach_uncovered_reachable hF₀ hmax hF hu i)
  · by_contra h
    exact hH (exchangeGraph_adj.2 ⟨F₀, .refl, hab, fun j hj ↦ h ⟨j, hj⟩⟩)

end NashWilliamsTutte

open Finset Fintype SimpleGraph
namespace NashWilliamsTutte
/-- **Nash-Williams' arboricity theorem.** The edges of a finite graph can be covered by `k`
forests if and only if every nonempty set `S` of vertices spans at most `k (#S - 1)` edges. -/
theorem arboricity {V : Type*} [Finite V] (G : SimpleGraph V) (k : ℕ) :
    (∃ F : Fin k → SimpleGraph V, (∀ i, F i ≤ G ∧ (F i).IsAcyclic) ∧ G = ⨆ i, F i) ↔
      ∀ S : Finset V, S.Nonempty → (G.induce (S : Set V)).edgeSet.ncard ≤ k * (#S - 1) := by
  constructor
  · rintro ⟨F, hF, hG⟩ S hS
    have : Nonempty (S : Set V) := ⟨⟨hS.choose, hS.choose_spec⟩⟩
    have hcardS : Nat.card (S : Set V) = #S := by
      rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
    have hsub : (G.induce (S : Set V)).edgeSet ⊆ ⋃ i, ((F i).induce (S : Set V)).edgeSet := by
      intro e he
      induction e using Sym2.ind with
      | _ a b =>
        have hab : G.Adj a b := he
        rw [hG, iSup_adj] at hab
        obtain ⟨i, hi⟩ := hab
        exact Set.mem_iUnion.2 ⟨i, hi⟩
    calc (G.induce (S : Set V)).edgeSet.ncard
        ≤ ∑ i, ((F i).induce (S : Set V)).edgeSet.ncard :=
          (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_iUnion_le_of_fintype _)
      _ ≤ ∑ _i : Fin k, (#S - 1) := sum_le_sum fun i _ ↦ by
          have := (IsAcyclic.ncard_edgeSet_add_one_le ((hF i).2.induce (S : Set V))).1
          omega
      _ = k * (#S - 1) := by simp
  · intro hcond
    have := Fintype.ofFinite V
    classical
    obtain ⟨F, H, hF, hdisj, -, hreach, hcov⟩ := exists_forests_core G k
    refine ⟨F, hF, le_antisymm (fun u v huv ↦ ?_) (iSup_le fun i ↦ (hF i).1)⟩
    rw [iSup_adj]
    by_contra hnot
    have hH : H.Adj u v := by
      by_contra h
      exact hnot (hcov u v huv h)
    let S : Finset V := univ.filter fun w ↦ H.Reachable u w
    have hu : u ∈ S := by simp [S]
    have hv : v ∈ S := by simpa [S] using hH.reachable
    have hcardS : Nat.card (S : Set V) = #S := by
      rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
    have hconn : ∀ i, ((F i ⊓ H).induce (S : Set V)).Connected := by
      intro i
      have hS : (S : Set V) = ((F i ⊓ H).connectedComponentMk u).supp := by
        ext w
        simp only [S, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq,
          ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
        exact ⟨fun h ↦ (hreach i u w h).symm, fun h ↦ (h.mono inf_le_right).symm⟩
      rw [hS]
      exact ((F i ⊓ H).connectedComponentMk u).connected_toSimpleGraph
    let e : Sym2 (S : Set V) := s(⟨u, hu⟩, ⟨v, hv⟩)
    have he : e ∈ (G.induce (S : Set V)).edgeSet := huv
    have h1 := sum_ncard_le_of_pairwise_disjoint
      (fun i ↦ ((F i ⊓ H).induce (S : Set V)).edgeSet) ((G.induce (S : Set V)).edgeSet \ {e})
      (fun i x hx ↦ by
        induction x using Sym2.ind with
        | _ a b =>
          have hab : (F i ⊓ H).Adj a b := hx
          refine ⟨(hF i).1 hab.1, fun h ↦ ?_⟩
          rcases Sym2.eq_iff.1 (Set.mem_singleton_iff.1 h) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hnot ⟨i, hab.1⟩
          · exact hnot ⟨i, hab.1.symm⟩)
      (fun i j hij ↦ by
        rw [Function.onFun, disjoint_edgeSet, disjoint_iff_adj]
        intro a b hi hj
        exact disjoint_iff_adj.1 (hdisj hij) a b hi.1 hj.1)
    have h2 := Set.ncard_sdiff_singleton_add_one he (Set.toFinite _)
    have h3 := hcond S ⟨u, hu⟩
    have h4 : ∑ _i : Fin k, (#S - 1) ≤ ∑ i, ((F i ⊓ H).induce (S : Set V)).edgeSet.ncard :=
      sum_le_sum fun i _ ↦ by
        have := (hconn i).card_vert_le_card_edgeSet_add_one
        rw [Nat.card_coe_set_eq (((F i ⊓ H).induce (S : Set V)).edgeSet), hcardS] at this
        omega
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h4
    omega


end NashWilliamsTutte


namespace QueenDensity

private lemma numericLarge (n s e k : ℚ) (hn : 12 ≤ n) (hs : 2 ≤ s)
    (hsN : s ≤ n*n) (hk₁ : 5*n-5 ≤ 3*k) (hk₂ : 3*k ≤ 5*n)
    (hc : 2*e ≤ s*(s-1))
    (hmax : 2*n*e + s*(n*n-s) ≤ n*4*(n-1)*s)
    (hmin : 3*(2*n*e + s*(n*n-s) + 3*n*(n-1)*(n*n-s)) ≤ 2*n*n*(n-1)*(5*n-1)) :
    e ≤ k*(s-1) := by
  have hn' : 0 < n := by linarith
  by_cases hsmall : s ≤ 2*k
  · nlinarith [mul_nonneg (sub_nonneg.mpr hsmall) (show 0 ≤ s-1 by linarith)]
  let j := n*(n-2)/3
  have hj : 2*k ≤ j := by
    dsimp [j]
    nlinarith [mul_nonneg hn'.le (show 0 ≤ n-12 by linarith)]
  have hbound (u : ℚ) (hu : 2*k ≤ u) (huj : u ≤ j) :
      n*4*(n-1)*u - u*(n*n-u) ≤ 2*n*k*(u-1) := by
    have hu' : 0 ≤ u := by linarith
    have hcoef : 3*(4*n*(n-1) - n*n + u) ≤ n*(10*n-14) := by
      dsimp [j] at huj
      linarith
    nlinarith [mul_le_mul_of_nonneg_right hcoef hu',
      mul_nonneg (mul_nonneg hn'.le hu') (show 0 ≤ 6*k-(10*n-10) by linarith),
      mul_nonneg hn'.le (show 0 ≤ 4*u-6*k by linarith)]
  by_cases hsplit : s ≤ j
  · exact (mul_le_mul_iff_right₀ (show 0 < 2*n by positivity)).mp
      (by nlinarith [hbound s (by linarith) hsplit])
  let f := fun u : ℚ =>
    2*n*n*(n-1)*(5*n-1) - 3*u*(n*n-u) - 9*n*(n-1)*(n*n-u) - 6*n*k*(u-1)
  have hfj : f j ≤ 0 := by
    have h := hbound j hj le_rfl
    dsimp [f, j] at *
    linarith
  have hfN : f (n*n) ≤ 0 := by
    dsimp [f]
    nlinarith [mul_nonneg (mul_nonneg hn'.le (show 0 ≤ n*n-1 by nlinarith))
      (show 0 ≤ 3*k-(5*n-5) by linarith),
      mul_nonneg (mul_nonneg hn'.le (show 0 ≤ n-1 by linarith))
      (show 0 ≤ n-5 by linarith)]
  let b := 6*n*n - 9*n - 6*n*k
  have diff (u v : ℚ) : f u - f v = (u-v)*(3*(u+v)+b) := by
    dsimp [f,b]
    ring
  have hfs : f s ≤ 0 := by
    by_cases hm : 3*(s+j)+b ≤ 0
    · have := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ s-j by linarith) hm
      linarith [diff s j]
    · have := mul_nonneg (show 0 ≤ n*n-s by linarith)
          (show 0 ≤ 3*(n*n+s)+b by linarith)
      linarith [diff (n*n) s]
  exact (mul_le_mul_iff_right₀ (show 0 < 6*n by positivity)).mp
    (by dsimp [f] at hfs; linarith)

private lemma numericSmall : ∀ n : Fin 12, ∀ s : Fin 122,
    let n := n.val
    let s := s.val
    let k := (5*n-3)/3
    let w := k*(s-1)+1
    2 ≤ n → n ≠ 4 → 2 ≤ s → s ≤ n*n →
      ¬ (2*w ≤ s*(s-1) ∧
         2*n*w+s*(n*n-s) ≤ n*(4*(n-1)*s) ∧
         3*(2*n*w+s*(n*n-s)+n*(3*(n-1)*(n*n-s))) ≤ 2*n*n*(n-1)*(5*n-1)) := by
  decide

theorem edge_bound_numeric (n s e : ℕ) (hn : 2 ≤ n) (h4 : n ≠ 4)
    (hs : 2 ≤ s) (hN : s ≤ n*n) (hc : 2*e ≤ s*(s-1))
    (hmax : 2*n*e+s*(n*n-s) ≤ n*(4*(n-1)*s))
    (hmin : 3*(2*n*e+s*(n*n-s)+n*(3*(n-1)*(n*n-s))) ≤ 2*n*n*(n-1)*(5*n-1)) :
    e ≤ ((5*n-3)/3)*(s-1) := by
  by_cases hsmall : n < 12
  · by_contra! h
    have hs' : s < 122 := by nlinarith [Nat.mul_self_le_mul_self (show n ≤ 11 by omega)]
    apply numericSmall ⟨n,hsmall⟩ ⟨s,hs'⟩ hn h4 hs hN
    dsimp only
    have hw : (5*n-3)/3*(s-1)+1 ≤ e := h
    exact ⟨le_trans (by gcongr) hc, le_trans (by gcongr) hmax, le_trans (by gcongr) hmin⟩
  let k := (5*n-3)/3
  change e ≤ k*(s-1)
  have hk₁ : 5*n ≤ 3*k+5 := by dsimp [k]; omega
  have hk₂ : 3*k ≤ 5*n := by dsimp [k]; omega
  have hn1 : 1 ≤ n := by omega
  have h5n : 1 ≤ 5*n := by omega
  have hs1 : 1 ≤ s := by omega
  have hn12 : 12 ≤ n := by omega
  qify [Nat.cast_sub hs1, Nat.cast_sub hn1, Nat.cast_sub hN, Nat.cast_sub h5n] at hc hmax hmin hn12 hs hN hk₁ hk₂ ⊢
  apply numericLarge n s e k hn12 hs hN (by linarith) hk₂ hc <;> linarith

end QueenDensity

namespace QueenDensity
open OMA.S_oeis_a047212 Finset

abbrev Pos (n : ℕ) := Fin n × Fin n

private lemma queen_rook {n : ℕ} {u v : Pos n} (h : u ≠ v)
    (hr : u.1 = v.1 ∨ u.2 = v.2) : (queenGraph n).Adj u v := by
  rw [queenGraph, SimpleGraph.fromRel_adj]
  exact ⟨h, Or.inl (hr.imp_right Or.inl)⟩

abbrev Cross {n : ℕ} (S : Finset (Pos n)) :=
  {p : S × (Sᶜ : Finset (Pos n)) // (queenGraph n).Adj p.1.val p.2.val}

private noncomputable def encode {n : ℕ} (S : Finset (Pos n))
    (p : S × (Sᶜ : Finset (Pos n))) : Cross S × Fin n := by
  classical
  let x := p.1.val
  let y := p.2.val
  let m : Pos n := (x.1, y.2)
  have hx : x ∈ S := p.1.property
  have hy : y ∉ S := Finset.mem_compl.mp p.2.property
  if hm : m ∈ S then
    have hne : m ≠ y := fun h => hy (h ▸ hm)
    exact (⟨(⟨m,hm⟩,p.2), queen_rook hne (Or.inr rfl)⟩, x.2)
  else
    have hne : x ≠ m := fun h => hm (h ▸ hx)
    exact (⟨(p.1,⟨m,Finset.mem_compl.mpr hm⟩), queen_rook hne (Or.inl rfl)⟩, y.1)

private def decode {n : ℕ} {S : Finset (Pos n)} (z : Cross S × Fin n) : Pos n × Pos n :=
  let a := z.1.val.1.val
  let b := z.1.val.2.val
  if a.1 = b.1 then (a,(z.2,b.2)) else ((a.1,z.2),b)

private lemma decode_encode {n : ℕ} (S : Finset (Pos n)) (p : S × (Sᶜ : Finset (Pos n))) :
    decode (encode S p) = (p.1.val,p.2.val) := by
  classical
  obtain ⟨⟨⟨i,j⟩,hx⟩,⟨⟨r,c⟩,hy⟩⟩ := p
  by_cases hm : (i,c) ∈ S
  · have h : i ≠ r := by rintro rfl; exact Finset.mem_compl.mp hy hm
    simp [decode,encode,hm,h]
  · simp [decode,encode,hm]

theorem rook_cut {n : ℕ} (S : Finset (Pos n)) :
    S.card*(n*n-S.card) ≤ n * Nat.card (Cross S) := by
  classical
  have hi : Function.Injective (encode S) := by
    intro p q he
    have h := congrArg decode he
    rw [decode_encode,decode_encode] at h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  have := Nat.card_le_card_of_injective _ hi
  simpa [Nat.card_prod, Nat.card_eq_fintype_card, Finset.card_compl, Nat.mul_comm] using this

private noncomputable def splitDarts {n : ℕ} (S : Finset (Pos n)) :
    ((x : S) × (queenGraph n).neighborSet x.val) ≃
      ((queenGraph n).induce (S : Set (Pos n))).Dart ⊕ Cross S := by
  classical
  exact
    { toFun := fun ⟨x,y⟩ => if h : y.val ∈ S then Sum.inl ⟨(x,⟨y,h⟩),y.property⟩
            else Sum.inr ⟨(x,⟨y,Finset.mem_compl.mpr h⟩),y.property⟩
      invFun := fun z => match z with
        | Sum.inl d => ⟨d.fst,⟨d.snd.val,d.adj⟩⟩
        | Sum.inr d => ⟨d.val.1,⟨d.val.2.val,d.property⟩⟩
      left_inv := by rintro ⟨x,y⟩; by_cases h : y.val ∈ S <;> simp [h]
      right_inv := by
        rintro (⟨⟨x,y⟩,h⟩|⟨⟨x,y⟩,h⟩)
        · simp [y.property]
        · simp [Finset.mem_compl.mp y.property] }

theorem split_degree_sum {n : ℕ} (S : Finset (Pos n)) :
    ∑ x ∈ S, Nat.card ((queenGraph n).neighborSet x) =
      2*((queenGraph n).induce (S : Set (Pos n))).edgeSet.ncard + Nat.card (Cross S) := by
  classical
  let H := (queenGraph n).induce (S : Set (Pos n))
  have hd : Nat.card H.Dart = 2*H.edgeSet.ncard := by
    rw [Nat.card_eq_fintype_card,H.dart_card_eq_twice_card_edges,H.edgeFinset_card,
      ← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  have h := Nat.card_congr (splitDarts S)
  rw [Nat.card_sum, hd] at h
  rw [← Finset.sum_attach]
  simpa [H,Nat.card_eq_fintype_card,Fintype.card_sigma,Finset.sum_coe_sort] using h

theorem seq_closed (n : ℕ) (hn : 1 ≤ n) : a n = (5*n-3)/3 := by
  let p := fun m : ℕ => m % 5 = 0 ∨ m % 5 = 2 ∨ m % 5 = 4
  let f := fun i : ℕ => (5*i+2)/3
  have hInf : (Set.ofPred p).Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro b
    exact ⟨5*(b+1),by change _ % 5 = 0 ∨ _; omega,by omega⟩
  have hall (i : ℕ) : ∀ h : (Set.ofPred p).Finite, i < h.toFinset.card :=
    fun h => False.elim (hInf h)
  have h := Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn (p := p) f
    (by intro y hy; change y % 5 = 0 ∨ y % 5 = 2 ∨ y % 5 = 4 at hy
        use 3 * (y/5) + (y%5)/2, hall _
        dsimp [f]; omega)
    (by intro i _; change _ % 5 = 0 ∨ _ % 5 = 2 ∨ _ % 5 = 4
        dsimp [f]; omega)
    (by intro i _ j _ hij; dsimp [f]; omega)
    (hall (n-1))
  change Nat.nth p (n-1) = _
  rw [← h]
  dsimp [f]
  omega

end QueenDensity

namespace QueenDensity
open OMA.S_oeis_a047212 Finset

private abbrev Square (n : ℕ) := Fin n × Fin n

private lemma queenAdj {n : ℕ} {a b : Square n} : (queenGraph n).Adj a b ↔
    (a.1.val ≠ b.1.val ∨ a.2.val ≠ b.2.val) ∧
    (a.1.val = b.1.val ∨ a.2.val = b.2.val ∨
     a.1.val+a.2.val = b.1.val+b.2.val ∨ a.1.val+b.2.val = b.1.val+a.2.val) := by
  obtain ⟨a,c⟩ := a
  obtain ⟨b,d⟩ := b
  simp only [queenGraph, SimpleGraph.fromRel_adj, ne_eq, Prod.mk.injEq, Fin.ext_iff,
    Int.natAbs_eq_natAbs_iff]
  omega

private def spans (n i j : ℕ) : Fin 8 → ℕ :=
  ![i, n-1-i, j, n-1-j,
    min i j, min i (n-1-j), min (n-1-i) j, min (n-1-i) (n-1-j)]

private def ray (i j : ℕ) (d : Fin 8) (t : ℕ) : ℕ × ℕ :=
  (![ (i-(t+1),j), (i+t+1,j), (i,j-(t+1)), (i,j+t+1),
      (i-(t+1),j-(t+1)), (i-(t+1),j+t+1), (i+t+1,j-(t+1)), (i+t+1,j+t+1)] :
      Fin 8 → ℕ × ℕ) d

private lemma ray_ok {n : ℕ} (a : Square n) (d : Fin 8) (t : Fin (spans n a.1 a.2 d)) :
    (ray a.1 a.2 d t).1 < n ∧ (ray a.1 a.2 d t).2 < n ∧
    ∀ (b : Square n), (b.1.val,b.2.val) = ray a.1 a.2 d t → (queenGraph n).Adj a b := by
  have ha := a.1.isLt
  have hb := a.2.isLt
  have h := t.isLt
  fin_cases d <;> simp [spans,ray,queenAdj] at * <;> grind

private def rayVertex {n : ℕ} (a : Square n) (x : (d : Fin 8) × Fin (spans n a.1 a.2 d)) :
    (queenGraph n).neighborSet a :=
  let p := ray a.1 a.2 x.1 x.2
  let h := ray_ok a x.1 x.2
  ⟨(⟨p.1,h.1⟩,⟨p.2,h.2.1⟩),h.2.2 _ rfl⟩

set_option maxHeartbeats 3000000 in
private lemma ray_inj {n : ℕ} (a : Square n) : Function.Injective (rayVertex a) := by
  rintro ⟨d,t⟩ ⟨e,s⟩ he
  have hv := congrArg (fun z : (queenGraph n).neighborSet a => (z.val.1.val,z.val.2.val)) he
  change ray a.1 a.2 d t = ray a.1 a.2 e s at hv
  have ht := t.isLt
  have hs := s.isLt
  fin_cases d <;> fin_cases e <;> simp [ray,spans] at hv ht hs <;>
    first | omega | congr 1; apply Fin.ext; omega

private lemma ray_surj {n : ℕ} (a : Square n) : Function.Surjective (rayVertex a) := by
  rintro ⟨b,hb⟩
  have hh := queenAdj.mp hb
  have hi := a.1.isLt
  have hj := a.2.isLt
  have hx := b.1.isLt
  have hy := b.2.isLt
  have make (d : Fin 8) (t : ℕ) (ht : t < spans n a.1 a.2 d)
      (hp : ray a.1 a.2 d t = (b.1.val,b.2.val)) :
      ∃ z, rayVertex a z = ⟨b,hb⟩ := by
    use ⟨d, ⟨t,ht⟩⟩
    exact Subtype.ext (Prod.ext (Fin.ext (congrArg Prod.fst hp)) (Fin.ext (congrArg Prod.snd hp)))
  rcases lt_trichotomy a.1.val b.1.val with h | h | h <;>
    rcases lt_trichotomy a.2.val b.2.val with k | k | k
  · apply make 7 (b.1-a.1-1 : ℕ) <;> simp [ray,spans] <;> omega
  · apply make 1 (b.1-a.1-1 : ℕ) <;> simp [ray,spans] <;> omega
  · apply make 6 (b.1-a.1-1 : ℕ) <;> simp [ray,spans] <;> omega
  · apply make 3 (b.2-a.2-1 : ℕ) <;> simp [ray,spans] <;> omega
  · omega
  · apply make 2 (a.2-b.2-1 : ℕ) <;> simp [ray,spans] <;> omega
  · apply make 5 (a.1-b.1-1 : ℕ) <;> simp [ray,spans] <;> omega
  · apply make 0 (a.1-b.1-1 : ℕ) <;> simp [ray,spans] <;> omega
  · apply make 4 (a.1-b.1-1 : ℕ) <;> simp [ray,spans] <;> omega

theorem queenDegree {n : ℕ} (a : Square n) :
    Nat.card ((queenGraph n).neighborSet a) = ∑ d : Fin 8, spans n a.1 a.2 d := by
  classical
  rw [← Nat.card_congr (Equiv.ofBijective (rayVertex a) ⟨ray_inj a,ray_surj a⟩)]
  simp [Nat.card_eq_fintype_card, Fintype.card_sigma]

private lemma degree_formula {n : ℕ} (a : Square n) :
    Nat.card ((queenGraph n).neighborSet a) = 2*(n-1) +
      min a.1.val a.2.val + min a.1.val a.2.rev.val +
      min a.1.rev.val a.2.val + min a.1.rev.val a.2.rev.val := by
  rw [queenDegree, Fin.sum_univ_eight]
  simp [spans,Fin.val_rev]
  omega

theorem degree_bounds {n : ℕ} (a : Square n) :
    3*(n-1) ≤ Nat.card ((queenGraph n).neighborSet a) ∧
    Nat.card ((queenGraph n).neighborSet a) ≤ 4*(n-1) := by
  rw [degree_formula]
  simp only [Fin.val_rev]
  have := a.1.isLt
  have := a.2.isLt
  omega

private lemma minSum (n : ℕ) :
    6*(∑ i : Fin n, ∑ j : Fin n, min i.val j.val) = n*(n-1)*(2*n-1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsum : (∑ i : Fin n, i.val)*2 = n*(n-1) := by
      rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i)]
      exact Finset.sum_range_id_mul_two n
    have hmin (i : Fin n) : min n i.val = i.val := min_eq_right i.isLt.le
    have hmin' (i : Fin n) : min i.val n = i.val := min_eq_left i.isLt.le
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    simp_rw [Fin.sum_univ_castSucc (fun j : Fin (n+1) => min _ j.val),
      Fin.val_castSucc,Fin.val_last]
    simp only [hmin,hmin',min_self,Finset.sum_add_distrib]
    cases n with
    | zero => simp
    | succ m =>
      have h₁ : 2*(m+1)-1 = 2*m+1 := by omega
      have h₂ : 2*(m+1+1)-1 = 2*m+3 := by omega
      simp only [Nat.add_sub_cancel, h₁, h₂] at ih hsum ⊢
      nlinarith

theorem degree_total (n : ℕ) :
    3*(∑ a : Square n, Nat.card ((queenGraph n).neighborSet a)) = 2*n*(n-1)*(5*n-1) := by
  have hr (f : Fin n → ℕ) : (∑ i : Fin n, f i.rev) = ∑ i : Fin n, f i :=
    Equiv.sum_comp Fin.revPerm f
  simp_rw [degree_formula]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    smul_eq_mul]
  have hr' (t : ℕ) : (∑ j : Fin n, min t j.rev.val) = ∑ j : Fin n, min t j.val :=
    hr (fun j => min t j.val)
  simp only [hr']
  simp only [hr (fun i => ∑ j : Fin n, min i.val j.val)]
  have hm := minSum n
  cases n with
  | zero => simp
  | succ m =>
    have h₁ : 2*(m+1)-1 = 2*m+1 := by omega
    have h₂ : 5*(m+1)-1 = 5*m+4 := by omega
    simp only [Nat.add_sub_cancel,h₁,h₂] at hm ⊢
    nlinarith

end QueenDensity

namespace QueenDensity
open OMA.S_oeis_a047212 Finset

private def HasCover {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ F : Fin k → SimpleGraph V, (∀ i, (F i).IsAcyclic) ∧
    ∀ u v, G.Adj u v → ∃ i, (F i).Adj u v

private lemma cover_iff {V : Type*} [Finite V] (G : SimpleGraph V) (k : ℕ) :
    HasCover G k ↔ ∀ S : Finset V, S.Nonempty →
      (G.induce (S : Set V)).edgeSet.ncard ≤ k*(S.card-1) := by
  rw [← NashWilliamsTutte.arboricity]
  constructor
  · rintro ⟨F,hF,h⟩
    refine ⟨fun i => G ⊓ F i,fun i => ⟨inf_le_left,(hF i).anti inf_le_right⟩,
      le_antisymm ?_ (iSup_le fun _ => inf_le_left)⟩
    intro a b hab
    obtain ⟨i,hi⟩ := h a b hab
    exact SimpleGraph.iSup_adj.mpr ⟨i,hab,hi⟩
  · rintro ⟨F,hF,h⟩
    exact ⟨F,fun i => (hF i).2,fun u v huv => SimpleGraph.iSup_adj.mp (h ▸ huv)⟩

theorem queen_solve (n : ℕ) (hn : 2 ≤ n) (h4 : n ≠ 4)
    (hb : ∀ a : Pos n, 3*(n-1) ≤ Nat.card ((queenGraph n).neighborSet a) ∧
      Nat.card ((queenGraph n).neighborSet a) ≤ 4*(n-1))
    (ht : 3*(∑ a : Pos n, Nat.card ((queenGraph n).neighborSet a)) = 2*n*(n-1)*(5*n-1)) :
    arboricity (queenGraph n) = a n := by
  classical
  rw [seq_closed n (by omega)]
  let G := queenGraph n
  let k := (5*n-3)/3
  let d := fun x : Pos n => Nat.card (G.neighborSet x)
  change sInf {k | HasCover G k} = k
  have upper : HasCover G k := by
    apply (cover_iff _ _).mpr
    intro S _
    let H := G.induce (S : Set (Pos n))
    let e := H.edgeSet.ncard
    change e ≤ k*(S.card-1)
    have hc : 2*e ≤ S.card*(S.card-1) := by
      have h := H.card_edgeFinset_le_card_choose_two
      rw [H.edgeFinset_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
        Nat.choose_two_right] at h
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,Set.ncard_coe_finset] at h
      change e ≤ S.card*(S.card-1)/2 at h
      omega
    by_cases hs : 2 ≤ S.card
    · have hN : S.card ≤ n*n := by simpa using S.card_le_univ
      have cut := rook_cut S
      have split : ∑ x ∈ S, d x = 2*e + Nat.card (Cross S) := split_degree_sum S
      have maxsum : ∑ x ∈ S, d x ≤ 4*(n-1)*S.card := by
        simpa [Nat.mul_comm,d,G] using Finset.sum_le_sum (s := S) (fun x _ => (hb x).2)
      have minsum : 3*(n-1)*(n*n-S.card) ≤ ∑ x ∈ Sᶜ, d x := by
        simpa [Nat.mul_comm,Finset.card_compl,d,G] using Finset.sum_le_sum (s := Sᶜ)
          (fun x _ => (hb x).1)
      have tot : 3*((∑ x ∈ S, d x) + ∑ x ∈ Sᶜ, d x) = 2*n*(n-1)*(5*n-1) := by
        rwa [Finset.sum_add_sum_compl]
      have hsub : 3*((∑ x ∈ S, d x)+3*(n-1)*(n*n-S.card)) ≤ 2*n*(n-1)*(5*n-1) := by omega
      rw [split] at maxsum hsub
      apply edge_bound_numeric n S.card e hn h4 hs hN hc
      · nlinarith only [Nat.mul_le_mul_left n maxsum,cut]
      · nlinarith only [Nat.mul_le_mul_left n hsub,cut]
    · have hsmall : S.card ≤ 1 := by omega
      have : S.card-1 = 0 := by omega
      simp_all
  apply le_antisymm (Nat.sInf_le (show k ∈ {j | HasCover G j} from upper))
  apply le_csInf ⟨k,upper⟩
  intro m hm
  haveI : NeZero n := ⟨by omega⟩
  have hlo := (cover_iff G m).mp hm (Finset.univ : Finset (Pos n)) Finset.univ_nonempty
  have spl := split_degree_sum (Finset.univ : Finset (Pos n))
  have hz : IsEmpty (Cross (Finset.univ : Finset (Pos n))) :=
    ⟨fun z => Finset.mem_compl.mp z.val.2.property (Finset.mem_univ _)⟩
  have hzero : Nat.card (Cross (Finset.univ : Finset (Pos n))) = 0 := by simp
  rw [hzero] at spl
  simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin] at hlo
  rw [spl] at ht
  simp only [add_zero] at ht
  change _ ≤ m*(n*n-1) at hlo
  by_contra! hbad
  have hmk : 3*m+6 ≤ 5*n := by dsimp [k] at hbad; omega
  have hn1 : 1 ≤ n := by omega
  have hnn : 1 ≤ n*n := by nlinarith
  have h5 : 1 ≤ 5*n := by omega
  zify [Nat.cast_sub hn1, Nat.cast_sub hnn, Nat.cast_sub h5] at hlo ht hmk hn hnn
  nlinarith [mul_nonneg (show 0 ≤ (n:ℤ)*n-1 by linarith)
    (show 0 ≤ 5*(n:ℤ)-(3*m+6) by linarith)]

end QueenDensity

theorem OMA.solution : type_of% @OMA.S_oeis_a047212.main := by
  intro n hn h1 h4
  apply QueenDensity.queen_solve n (by omega) h4
  · exact QueenDensity.degree_bounds
  · exact QueenDensity.degree_total n
