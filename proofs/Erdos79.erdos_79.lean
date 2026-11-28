import FormalConjectures.ErdosProblems.«79»

-- Problem: Erdős Problem 79
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/79.lean:47 (declaration Erdos79.erdos_79)
-- Credit: @OrangeHeadz (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-
Attribution. Everything in this file before the namespace OMA79 is adapted from the Lean
formalization of Erdős Problem 79 in the public plby/lean-proofs repository
(https://github.com/plby/lean-proofs, commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e, files
src/latest/ErdosProblems/Erdos79.lean, src/latest/ErdosProblems/Erdos79/*.lean and
src/latest/Util/Ramsey.lean).  Those source files carry no licence statement and the repository
has no licence file; the material is reproduced here with attribution only, and all rights in it
remain with its authors.
Informal proof: Wigderson, as credited in the source file.  Formal authors as credited in the
source file: Codex, GPT-5.6 Sol.
Changes made here: the modules are flattened into one file in dependency order, the namespace
Erdos79 is renamed E79P, imports, linter options, axiom printouts and the refl, symm and trans
attributes are removed.  This ported part is not original work of the submitter.
The bridge from the ported theorem to the formal-conjectures statement (namespace OMA79 and the
final theorem) is new.
-/

/- ===== from Util.Ramsey ===== -/
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-
# Finite Ramsey theory utilities

This file contains the finite two-color Ramsey definitions and elementary bounds shared by
multiple developments.
-/

open Finset

noncomputable section

namespace SimpleGraph

theorem IndepSetFree.comap {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β} {n : ℕ}
    (f : H ↪g G) : G.IndepSetFree n → H.IndepSetFree n := by
  intro h
  rw [← cliqueFree_compl] at h ⊢
  exact CliqueFree.comap
    (((Embedding.complEquiv (G := H) (H := G)).toFun f).isContained) h

end SimpleGraph

namespace Ramsey

/--
The Ramsey property on `n` vertices: every finite simple graph on `n` vertices contains
either a `k`-clique or an independent set of size `l`.
-/
def RamseyProperty (k l n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬ (G.CliqueFree k ∧ G.IndepSetFree l)

lemma ramseyProperty_of_card {k l n : ℕ} {α : Type*} [Fintype α]
    (hcard : Fintype.card α = n) (hprop : RamseyProperty k l n) :
    ∀ G : SimpleGraph α, ¬ (G.CliqueFree k ∧ G.IndepSetFree l) := by
  intro G hbad
  let H : SimpleGraph (Fin n) := G.overFin hcard
  let e : G ≃g H := SimpleGraph.overFinIso (G := G) hcard
  have hcf : H.CliqueFree k := hbad.1.comap e.symm.toEmbedding.isContained
  have hcfCompl : Hᶜ.CliqueFree l := by
    have hGCompl : Gᶜ.CliqueFree l := by
      simpa [SimpleGraph.cliqueFree_compl] using hbad.2
    exact hGCompl.comap
      (((SimpleGraph.Embedding.complEquiv (G := H) (H := G)).toFun e.symm.toEmbedding).isContained)
  have hif : H.IndepSetFree l := by
    simpa [SimpleGraph.cliqueFree_compl] using hcfCompl
  exact hprop H ⟨hcf, hif⟩

lemma ramseyProperty_mono {k l n m : ℕ} (hnm : n ≤ m) :
    RamseyProperty k l n → RamseyProperty k l m := by
  intro h G hbad
  let f : Fin n ↪ Fin m := Fin.castLEEmb hnm
  have hcf : (G.comap f).CliqueFree k :=
    hbad.1.comap (SimpleGraph.Embedding.comap f G).isContained
  have hif : (G.comap f).IndepSetFree l :=
    SimpleGraph.IndepSetFree.comap (SimpleGraph.Embedding.comap f G) hbad.2
  exact h (G.comap f) ⟨hcf, hif⟩

/-- Finite Ramsey's theorem, packaged as the existence of a size satisfying `RamseyProperty`. -/
theorem ramseyProperty_exists (k l : ℕ) : ∃ n, RamseyProperty k l n := by
  revert l
  induction k with
  | zero =>
      intro l
      refine ⟨0, ?_⟩
      intro G hbad
      simpa using hbad.1
  | succ k ih =>
      intro l
      induction l with
      | zero =>
          refine ⟨0, ?_⟩
          intro G hbad
          exact hbad.2 ∅ (by simp [SimpleGraph.isNIndepSet_iff])
      | succ l ihl =>
          rcases ih (l + 1) with ⟨m, hm⟩
          rcases ihl with ⟨n, hn⟩
          refine ⟨m + n + 1, ?_⟩
          intro G hbad
          classical
          let v : Fin (m + n + 1) := 0
          by_cases hdeg : m ≤ G.degree v
          · let H : SimpleGraph (G.neighborSet v) := G.induce (G.neighborSet v)
            have hprop : RamseyProperty k (l + 1) (G.degree v) := ramseyProperty_mono hdeg hm
            have hcf : H.CliqueFree k := by
              intro t ht
              let t' : Finset (Fin (m + n + 1)) :=
                Finset.map ⟨Subtype.val, Subtype.val_injective⟩ t
              have htInd :
                  (((⊤ : SimpleGraph.Subgraph G).induce (G.neighborSet v)).coe).IsNClique k t := by
                rw [← SimpleGraph.induce_eq_coe_induce_top]
                exact ht
              have ht' : G.IsNClique k t' := by
                simpa [H, t'] using
                  (SimpleGraph.IsNClique.of_induce
                    (S := (⊤ : SimpleGraph.Subgraph G)) (F := G.neighborSet v) (cc := htInd))
              have hvt : ∀ b ∈ t', G.Adj v b := by
                intro b hb
                rcases Finset.mem_map.mp hb with ⟨x, hx, rfl⟩
                exact x.property
              exact hbad.1 _ (ht'.insert hvt)
            have hif : H.IndepSetFree (l + 1) := by
              exact SimpleGraph.IndepSetFree.comap
                (SimpleGraph.Embedding.induce (G := G) (s := G.neighborSet v)) hbad.2
            exact ramseyProperty_of_card (G.card_neighborSet_eq_degree v) hprop H ⟨hcf, hif⟩
          · let H : SimpleGraph (Gᶜ.neighborSet v) := G.induce (Gᶜ.neighborSet v)
            have hcompdeg : n ≤ Gᶜ.degree v := by
              rw [G.degree_compl (v := v), Fintype.card_fin]
              omega
            have hprop : RamseyProperty (k + 1) l (Gᶜ.degree v) :=
              ramseyProperty_mono hcompdeg hn
            have hcf : H.CliqueFree (k + 1) := by
              exact hbad.1.comap
                (SimpleGraph.Embedding.induce (G := G) (s := Gᶜ.neighborSet v)).isContained
            have hif : H.IndepSetFree l := by
              intro t ht
              let t' : Finset (Fin (m + n + 1)) :=
                Finset.map ⟨Subtype.val, Subtype.val_injective⟩ t
              have htInd :
                  (((⊤ : SimpleGraph.Subgraph G).induce
                    (Gᶜ.neighborSet v)).coe).IsNIndepSet l t := by
                rw [← SimpleGraph.induce_eq_coe_induce_top]
                exact ht
              have ht' : G.IsNIndepSet l t' := by
                simpa [H, t'] using
                  (SimpleGraph.isNIndepSet_induce
                    (G := G) (F := Gᶜ.neighborSet v) (s := t) (n := l)).1 htInd
              have ht'compl : Gᶜ.IsNClique l t' := by
                simpa using ht'
              have hvt : ∀ b ∈ t', Gᶜ.Adj v b := by
                intro b hb
                rcases Finset.mem_map.mp hb with ⟨x, hx, rfl⟩
                exact x.property
              have ht'' : G.IsNIndepSet (l + 1) (insert v t') := by
                simpa using ht'compl.insert hvt
              exact hbad.2 _ ht''
            exact ramseyProperty_of_card (Gᶜ.card_neighborSet_eq_degree v) hprop H ⟨hcf, hif⟩

end Ramsey

/- ===== from ErdosProblems.Erdos79.Core ===== -/
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-
# Finite-graph and Ramsey foundations for Erdős Problem 79

The problem concerns ordinary (not necessarily induced) subgraphs.  To quantify over finite
graphs without carrying a vertex type and a `Fintype` instance everywhere, we use canonical
codes: a graph with `n` vertices is represented by a simple graph on `Fin n`.

`RamseyAt F H N` says that every red/blue colouring of the edges of `K_N` has a red copy of
`F` or a blue copy of `H`.  A colouring is represented by its red graph `C`; its blue graph is
then `Cᶜ`.  Thus the definition is the usual (non-induced) graph Ramsey property.
-/

open scoped SimpleGraph

noncomputable section

namespace E79P
/-- A canonical code for a finite simple graph: the first component is the number of vertices
and the second is a graph on `Fin` of that number. -/
abbrev GraphCode := Σ n : ℕ, SimpleGraph (Fin n)

namespace GraphCode

/-- The number of vertices of a coded graph. -/
abbrev vertexCount (G : GraphCode) : ℕ := G.1

/-- The simple graph carried by a code. -/
abbrev graph (G : GraphCode) : SimpleGraph (Fin G.vertexCount) := G.2

/-- The number of (unordered) edges of a coded graph. -/
noncomputable def edgeCount (G : GraphCode) : ℕ :=
  Nat.card G.graph.edgeSet

@[simp] theorem vertexCount_mk (n : ℕ) (G : SimpleGraph (Fin n)) :
    GraphCode.vertexCount (⟨n, G⟩ : GraphCode) = n := rfl

@[simp] theorem graph_mk (n : ℕ) (G : SimpleGraph (Fin n)) :
    GraphCode.graph (⟨n, G⟩ : GraphCode) = G := rfl

@[simp] theorem edgeCount_mk (n : ℕ) (G : SimpleGraph (Fin n)) :
    GraphCode.edgeCount (⟨n, G⟩ : GraphCode) = Nat.card G.edgeSet := rfl

/-- On choosing a decidable adjacency relation, `edgeCount` is the cardinality of Mathlib's
finite edge set. -/
theorem edgeCount_eq_card_edgeFinset (G : GraphCode) [DecidableRel G.graph.Adj] :
    G.edgeCount = G.graph.edgeFinset.card := by
  rw [edgeCount, Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]

end GraphCode

/-- Ordinary, non-induced containment of coded finite graphs.  `IsContained F G` means that
`G` has a (not necessarily induced) subgraph isomorphic to `F`. -/
abbrev IsContained (F G : GraphCode) : Prop := F.graph ⊑ G.graph

/-- Isomorphism of coded finite graphs. -/
abbrev Isomorphic (F G : GraphCode) : Prop := Nonempty (F.graph ≃g G.graph)

namespace IsContained

theorem refl (G : GraphCode) : IsContained G G :=
  SimpleGraph.IsContained.refl G.graph

theorem rfl {G : GraphCode} : IsContained G G := refl G

theorem trans {F G H : GraphCode} (hFG : IsContained F G)
    (hGH : IsContained G H) : IsContained F H :=
  SimpleGraph.IsContained.trans hFG hGH

/-- Containment cannot decrease the number of available vertices. -/
theorem vertexCount_le {F G : GraphCode} (h : IsContained F G) :
    F.vertexCount ≤ G.vertexCount := by
  rcases h with ⟨f⟩
  simpa using Fintype.card_le_of_embedding f.toEmbedding

/-- Containment cannot decrease the number of edges. -/
theorem edgeCount_le {F G : GraphCode} (h : IsContained F G) :
    F.edgeCount ≤ G.edgeCount := by
  rcases h with ⟨f⟩
  exact Finite.card_le_of_embedding f.mapEdgeSet

end IsContained

namespace Isomorphic

theorem refl (G : GraphCode) : Isomorphic G G :=
  ⟨SimpleGraph.Iso.refl⟩

theorem rfl {G : GraphCode} : Isomorphic G G := refl G

theorem symm {F G : GraphCode} (h : Isomorphic F G) : Isomorphic G F := by
  rcases h with ⟨e⟩
  exact ⟨e.symm⟩

theorem trans {F G H : GraphCode} (hFG : Isomorphic F G)
    (hGH : Isomorphic G H) : Isomorphic F H := by
  rcases hFG with ⟨eFG⟩
  rcases hGH with ⟨eGH⟩
  exact ⟨eGH.comp eFG⟩

theorem isContained {F G : GraphCode} (h : Isomorphic F G) : IsContained F G := by
  rcases h with ⟨e⟩
  exact e.isContained

theorem isContained' {F G : GraphCode} (h : Isomorphic F G) : IsContained G F :=
  h.symm.isContained

end Isomorphic

/-- The usual graph Ramsey property at the *exact* ambient order `N`.

Every graph `C` on `Fin N` is viewed as the red graph of a two-colouring of `K_N`; `Cᶜ` is
the blue graph.  Copies are ordinary, non-induced copies. -/
def RamseyAt (F H : GraphCode) (N : ℕ) : Prop :=
  ∀ C : SimpleGraph (Fin N), F.graph ⊑ C ∨ H.graph ⊑ Cᶜ

namespace RamseyAt

/-- Making the first forbidden graph smaller preserves a Ramsey assertion. -/
theorem mono_left {F F' H : GraphCode} {N : ℕ} (hFF' : IsContained F' F)
    (h : RamseyAt F H N) : RamseyAt F' H N := by
  intro C
  exact (h C).imp (fun hFC ↦ SimpleGraph.IsContained.trans hFF' hFC) id

/-- Making the second forbidden graph smaller preserves a Ramsey assertion. -/
theorem mono_right {F H H' : GraphCode} {N : ℕ} (hHH' : IsContained H' H)
    (h : RamseyAt F H N) : RamseyAt F H' N := by
  intro C
  exact (h C).imp id (fun hHC ↦ SimpleGraph.IsContained.trans hHH' hHC)

/-- Simultaneous antitonicity in the two forbidden graphs. -/
theorem mono {F F' H H' : GraphCode} {N : ℕ} (hFF' : IsContained F' F)
    (hHH' : IsContained H' H) (h : RamseyAt F H N) : RamseyAt F' H' N :=
  (h.mono_left hFF').mono_right hHH'

/-- Replacing the first forbidden graph by an isomorphic graph changes nothing. -/
theorem congr_left {F F' H : GraphCode} {N : ℕ} (hFF' : Isomorphic F F') :
    RamseyAt F H N ↔ RamseyAt F' H N := by
  constructor
  · exact mono_left hFF'.isContained'
  · exact mono_left hFF'.isContained

/-- Replacing the second forbidden graph by an isomorphic graph changes nothing. -/
theorem congr_right {F H H' : GraphCode} {N : ℕ} (hHH' : Isomorphic H H') :
    RamseyAt F H N ↔ RamseyAt F H' N := by
  constructor
  · exact mono_right hHH'.isContained'
  · exact mono_right hHH'.isContained

/-- Isomorphism invariance in both forbidden graphs. -/
theorem congr {F F' H H' : GraphCode} {N : ℕ} (hFF' : Isomorphic F F')
    (hHH' : Isomorphic H H') : RamseyAt F H N ↔ RamseyAt F' H' N := by
  rw [congr_left hFF', congr_right hHH']

/-- Once the Ramsey property holds, it continues to hold after adding ambient vertices. -/
theorem mono_vertices {F H : GraphCode} {N M : ℕ} (hNM : N ≤ M)
    (h : RamseyAt F H N) : RamseyAt F H M := by
  intro C
  let f : Fin N ↪ Fin M := Fin.castLEEmb hNM
  rcases h (C.comap f) with hF | hH
  · left
    exact hF.trans (SimpleGraph.Embedding.comap f C).isContained
  · right
    have hcomp : (C.comap f)ᶜ = Cᶜ.comap f := by
      ext u v
      simp only [SimpleGraph.compl_adj, SimpleGraph.comap_adj]
      rw [f.injective.ne_iff]
    have hHC : H.graph ⊑ Cᶜ.comap f := by
      simpa only [hcomp] using hH
    exact hHC.trans (SimpleGraph.Embedding.comap f Cᶜ).isContained

end RamseyAt

/-- Every pair of coded finite graphs has a finite Ramsey bound. -/
theorem ramseyAt_exists (F H : GraphCode) : ∃ N, RamseyAt F H N := by
  obtain ⟨N, hN⟩ := Ramsey.ramseyProperty_exists F.vertexCount H.vertexCount
  refine ⟨N, ?_⟩
  intro C
  have hor : ¬ C.CliqueFree F.vertexCount ∨ ¬ C.IndepSetFree H.vertexCount :=
    not_and_or.mp (hN C)
  rcases hor with hred | hblue
  · left
    have htop : (⊤ : SimpleGraph (Fin F.vertexCount)) ⊑ C := by
      simpa only [SimpleGraph.completeGraph_eq_top] using
        (SimpleGraph.not_cliqueFree_iff_top_isContained F.vertexCount).mp hred
    exact (SimpleGraph.IsContained.of_le le_top).trans htop
  · right
    have hblue' : ¬ Cᶜ.CliqueFree H.vertexCount := by
      simpa only [SimpleGraph.cliqueFree_compl] using hblue
    have htop : (⊤ : SimpleGraph (Fin H.vertexCount)) ⊑ Cᶜ := by
      simpa only [SimpleGraph.completeGraph_eq_top] using
        (SimpleGraph.not_cliqueFree_iff_top_isContained H.vertexCount).mp hblue'
    exact (SimpleGraph.IsContained.of_le le_top).trans htop

/-- The least ambient order at which the graph Ramsey property holds. -/
noncomputable def graphRamseyNumber (F H : GraphCode) : ℕ :=
  by
    classical
    exact Nat.find (ramseyAt_exists F H)

theorem graphRamseyNumber_spec (F H : GraphCode) :
    RamseyAt F H (graphRamseyNumber F H) := by
  classical
  simpa only [graphRamseyNumber] using Nat.find_spec (ramseyAt_exists F H)

theorem graphRamseyNumber_le_of_ramseyAt {F H : GraphCode} {N : ℕ}
    (h : RamseyAt F H N) : graphRamseyNumber F H ≤ N := by
  classical
  simpa only [graphRamseyNumber] using Nat.find_min' (ramseyAt_exists F H) h

theorem ramseyAt_of_graphRamseyNumber_le {F H : GraphCode} {N : ℕ}
    (h : graphRamseyNumber F H ≤ N) : RamseyAt F H N :=
  (graphRamseyNumber_spec F H).mono_vertices h

theorem ramseyAt_iff_graphRamseyNumber_le {F H : GraphCode} {N : ℕ} :
    RamseyAt F H N ↔ graphRamseyNumber F H ≤ N :=
  ⟨graphRamseyNumber_le_of_ramseyAt, ramseyAt_of_graphRamseyNumber_le⟩

/-- The canonical code of a complete graph. -/
def completeCode (n : ℕ) : GraphCode := ⟨n, ⊤⟩

/-- A coded graph has no isolated vertices.  The empty graph satisfies this predicate
vacuously, as is standard. -/
def NoIsolated (G : GraphCode) : Prop :=
  ∀ v, ¬ G.graph.IsIsolated v

namespace NoIsolated

/-- Absence of isolated vertices is invariant under graph isomorphism. -/
theorem congr {F G : GraphCode} (hFG : Isomorphic F G) : NoIsolated F ↔ NoIsolated G := by
  rcases hFG with ⟨e⟩
  constructor
  · intro h w
    let v := e.symm w
    obtain ⟨u, hvu⟩ := F.graph.exists_adj_iff_not_isIsolated.mpr (h v)
    apply G.graph.exists_adj_iff_not_isIsolated.mp
    exact ⟨e u, by simpa [v] using e.map_rel_iff.mpr hvu⟩
  · intro h v
    let w := e v
    obtain ⟨u, hwu⟩ := G.graph.exists_adj_iff_not_isIsolated.mpr (h w)
    apply F.graph.exists_adj_iff_not_isIsolated.mp
    exact ⟨e.symm u, by simpa [w] using e.symm.map_rel_iff.mpr hwu⟩

/-- A finite graph without isolated vertices has at most twice as many vertices as edges. -/
theorem vertexCount_le_twice_edgeCount {G : GraphCode} (hG : NoIsolated G) :
    G.vertexCount ≤ 2 * G.edgeCount := by
  classical
  calc
    G.vertexCount = ∑ _v : Fin G.vertexCount, 1 := by simp
    _ ≤ ∑ v : Fin G.vertexCount, G.graph.degree v := by
      apply Finset.sum_le_sum
      intro v _hv
      exact (G.graph.degree_pos v).mpr (hG v)
    _ = 2 * G.graph.edgeFinset.card := G.graph.sum_degrees_eq_twice_card_edges
    _ = 2 * G.edgeCount := by rw [G.edgeCount_eq_card_edgeFinset]

end NoIsolated

/-- `F` is Ramsey size linear if one natural constant works uniformly for every coded graph
`H` without isolated vertices, with the Ramsey assertion holding already at the exact order
`C * e(H)`. -/
def RamseySizeLinear (F : GraphCode) : Prop :=
  ∃ C : ℕ, ∀ H : GraphCode, NoIsolated H → RamseyAt F H (C * H.edgeCount)

namespace RamseySizeLinear

/-- An equivalent least-Ramsey-number formulation of Ramsey size linearity. -/
theorem iff_graphRamseyNumber_le {F : GraphCode} :
    RamseySizeLinear F ↔
      ∃ C : ℕ, ∀ H : GraphCode, NoIsolated H →
        graphRamseyNumber F H ≤ C * H.edgeCount := by
  simp only [RamseySizeLinear, ramseyAt_iff_graphRamseyNumber_le]

/-- If `F'` is contained in a Ramsey-size-linear graph `F`, then `F'` is Ramsey size linear. -/
theorem mono {F F' : GraphCode} (hF'F : IsContained F' F) (hF : RamseySizeLinear F) :
    RamseySizeLinear F' := by
  rcases hF with ⟨C, hC⟩
  exact ⟨C, fun H hH ↦ (hC H hH).mono_left hF'F⟩

/-- Ramsey size linearity is invariant under graph isomorphism. -/
theorem congr {F F' : GraphCode} (hFF' : Isomorphic F F') :
    RamseySizeLinear F ↔ RamseySizeLinear F' := by
  constructor
  · exact mono hFF'.isContained'
  · exact mono hFF'.isContained

end RamseySizeLinear

end E79P

/- ===== from ErdosProblems.Erdos79.Forest ===== -/
namespace E79P
open Finset
open scoped SimpleGraph

namespace SimpleGraph

variable {U V : Type} {T : _root_.SimpleGraph U} {G : _root_.SimpleGraph V}

/-- A finite tree embeds in every nonempty finite graph whose minimum degree is at least
one less than the number of vertices of the tree. -/
theorem isContained_of_isTree_of_card_sub_one_le_minDegree
    [Fintype U] [Fintype V] [Nonempty V]
    [DecidableRel G.Adj]
    (hT : T.IsTree) (hdeg : Fintype.card U - 1 ≤ G.minDegree) : T ⊑ G := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∀ (U : Type) [Fintype U] (T : _root_.SimpleGraph U),
      Fintype.card U = n → T.IsTree →
        Fintype.card U - 1 ≤ G.minDegree → T ⊑ G
  suffices hP : P (Fintype.card U) by
    exact hP U T rfl hT hdeg
  apply Nat.strong_induction_on (p := P) (Fintype.card U)
  intro n ih U _ T hn hT hdeg
  by_cases hU : Nontrivial U
  · let : Nontrivial U := hU
    obtain ⟨v, hv⟩ := hT.exists_vert_degree_one_of_nontrivial
    let U' := ({v}ᶜ : Set U)
    let T' : _root_.SimpleGraph U' := T.induce ({v}ᶜ : Set U)
    have hT' : T'.IsTree := ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hv,
      hT.isAcyclic.induce _⟩
    have hcardU' : Fintype.card U' = n - 1 := by
      change Fintype.card ↑({v}ᶜ : Set U) = n - 1
      rw [Fintype.card_compl_set]
      simp [hn]
    have hlt : Fintype.card U' < n := by
      rw [hcardU']
      have hnpos : 0 < n := by
        simpa [← hn] using Fintype.card_pos_iff.mpr (inferInstance : Nonempty U)
      omega
    have hdeg' : Fintype.card U' - 1 ≤ G.minDegree := by
      rw [hcardU']
      omega
    obtain ⟨e⟩ := ih (Fintype.card U') hlt U' T' rfl hT' hdeg'
    obtain ⟨p, hvp, hp_unique⟩ := (T.degree_eq_one_iff_existsUnique_adj).mp hv
    have hp_ne_v : p ≠ v := hvp.ne'
    let p' : U' := ⟨p, by
      change p ∈ ({v}ᶜ : Set U)
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact hp_ne_v⟩
    let used : Finset V := Finset.univ.image e
    have hused_card : used.card = Fintype.card U' := by
      simpa [used] using
        Finset.card_image_of_injective (Finset.univ : Finset U') e.injective
    have hused_le_neighbor : used.card ≤ (G.neighborFinset (e p')).card := by
      rw [hused_card, G.card_neighborFinset_eq_degree, hcardU']
      have hdeg_n : n - 1 ≤ G.minDegree := by
        rw [← hn]
        exact hdeg
      exact hdeg_n.trans (G.minDegree_le_degree (e p'))
    have hnot_subset : ¬ G.neighborFinset (e p') ⊆ used := by
      intro hsub
      have heq : G.neighborFinset (e p') = used :=
        Finset.eq_of_subset_of_card_le hsub hused_le_neighbor
      have hp_mem_used : e p' ∈ used := by simp [used]
      have hp_not_neighbor : e p' ∉ G.neighborFinset (e p') := G.notMem_neighborFinset_self _
      exact hp_not_neighbor (heq.symm ▸ hp_mem_used)
    obtain ⟨w, hw_neighbor, hw_unused⟩ := Finset.not_subset.mp hnot_subset
    have hw_adj : G.Adj (e p') w := (G.mem_neighborFinset _ _).mp hw_neighbor
    let f : U → V := fun x ↦ if hx : x = v then w else e ⟨x, by simpa [hx]⟩
    have hf_v : f v = w := by simp [f]
    have hf_ne (x : U) (hx : x ≠ v) : f x = e ⟨x, by simpa [hx]⟩ := by simp [f, hx]
    have hf_inj : Function.Injective f := by
      intro x y hxy
      by_cases hx : x = v
      · subst x
        by_cases hy : y = v
        · exact hy.symm
        exfalso
        have hwy : w = e ⟨y, by simpa [hy]⟩ := by
          simpa [hf_v, hf_ne y hy] using hxy
        apply hw_unused
        apply Finset.mem_image.mpr
        exact ⟨⟨y, by simp [U', hy]⟩, Finset.mem_univ _, hwy.symm⟩
      · by_cases hy : y = v
        · subst y
          exfalso
          have : e ⟨x, by simpa [hx]⟩ = w := by simpa [hf_v, hf_ne x hx] using hxy
          apply hw_unused
          apply Finset.mem_image.mpr
          exact ⟨⟨x, by simp [U', hx]⟩, Finset.mem_univ _, this⟩
        · have heq : e ⟨x, by simpa [hx]⟩ = e ⟨y, by simpa [hy]⟩ := by
            simpa [hf_ne x hx, hf_ne y hy] using hxy
          exact congrArg Subtype.val (e.injective heq)
    refine ⟨⟨⟨f, ?_⟩, hf_inj⟩⟩
    intro x y hxy
    by_cases hx : x = v
    · subst x
      have hy : y = p := hp_unique y hxy
      subst y
      simpa [hf_v, hf_ne p hp_ne_v, p'] using hw_adj.symm
    · by_cases hy : y = v
      · subst y
        have hx_p : x = p := hp_unique x hxy.symm
        subst x
        simpa [hf_v, hf_ne p hp_ne_v, p'] using hw_adj
      · have hT'xy : T'.Adj ⟨x, by simpa [hx]⟩ ⟨y, by simpa [hy]⟩ := hxy
        simpa [hf_ne x hx, hf_ne y hy] using e.toHom.map_adj hT'xy
  · let : Subsingleton U := not_nontrivial_iff_subsingleton.mp hU
    exact ⟨{
      toHom := {
        toFun := fun _ ↦ Classical.choice (inferInstance : Nonempty V)
        map_rel' := fun {a b} hab ↦
          (T.loopless.irrefl a (Subsingleton.elim b a ▸ hab)).elim }
      injective' := fun _ _ _ ↦ Subsingleton.elim _ _ }⟩

/-- Adjoining a vertex adjacent to an embedded clique produces a clique one vertex larger. -/
theorem top_succ_isContained_of_copy_of_adj
    {k : ℕ}
    (v : V) (q : (⊤ : _root_.SimpleGraph (Fin k)).Copy G)
    (hq : ∀ i, G.Adj v (q i)) :
    (⊤ : _root_.SimpleGraph (Fin (k + 1))) ⊑ G := by
  classical
  let f : Fin (k + 1) → V := Fin.cases v q
  have hf_inj : Function.Injective f := by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
        cases j using Fin.cases with
        | zero => rfl
        | succ j =>
            exfalso
            exact (hq j).ne hij
    | succ i =>
        cases j using Fin.cases with
        | zero =>
            exfalso
            exact (hq i).ne' hij
        | succ j =>
            exact congrArg Fin.succ (q.injective hij)
  refine ⟨⟨⟨f, ?_⟩, hf_inj⟩⟩
  intro i j hij
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero => simp at hij
      | succ j => exact hq j
  | succ i =>
      cases j using Fin.cases with
      | zero => exact (hq i).symm
      | succ j =>
          apply q.toHom.map_adj
          simpa using hij

end SimpleGraph

/-- Chvátal's tree-versus-clique bound
`R(T, K_s) ≤ (|T| - 1)(s - 1) + 1`. -/
theorem ramseyAt_tree_completeCode (F : GraphCode) (hF : F.graph.IsTree) (s : ℕ) :
    RamseyAt F (completeCode s) ((F.vertexCount - 1) * (s - 1) + 1) := by
  classical
  induction s using Nat.twoStepInduction with
  | zero =>
      simp only [Nat.zero_sub, Nat.mul_zero, Nat.zero_add]
      intro C
      right
      change (⊤ : _root_.SimpleGraph (Fin 0)) ⊑ Cᶜ
      exact _root_.SimpleGraph.IsContained.of_isEmpty
  | one =>
      simp only [Nat.sub_self, Nat.mul_zero, Nat.zero_add]
      intro C
      right
      change (⊤ : _root_.SimpleGraph (Fin 1)) ⊑ Cᶜ
      apply _root_.SimpleGraph.IsContained.of_le
      intro i j hij
      have hij' : i = j := Subsingleton.elim i j
      subst j
      exact ((⊤ : _root_.SimpleGraph (Fin 1)).loopless.irrefl i hij).elim
  | more k hk hk1 =>
      rw [show k + 2 - 1 = k + 1 by omega]
      let N := (F.vertexCount - 1) * (k + 1) + 1
      change RamseyAt F (completeCode (k + 2)) N
      intro C
      by_cases hred : F.graph ⊑ C
      · exact Or.inl hred
      right
      have hNpos : 0 < N := by simp [N]
      let : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hNpos
      have hmindeg : ¬ F.vertexCount - 1 ≤ C.minDegree := by
        intro h
        apply hred
        apply SimpleGraph.isContained_of_isTree_of_card_sub_one_le_minDegree hF
        simpa using h
      obtain ⟨v, hv⟩ := C.exists_minimal_degree_vertex
      have hvlt : C.degree v < F.vertexCount - 1 := by
        rw [← hv]
        exact Nat.lt_of_not_ge hmindeg
      let M := (F.vertexCount - 1) * k + 1
      have hblue_degree : M ≤ Cᶜ.degree v := by
        rw [C.degree_compl]
        simp only [Fintype.card_fin]
        dsimp [N, M]
        calc
          (F.vertexCount - 1) * k + 1 ≤
              (F.vertexCount - 1) * k + (F.vertexCount - 1) - C.degree v := by omega
          _ = (F.vertexCount - 1) * (k + 1) - C.degree v :=
            congrArg (fun z ↦ z - C.degree v) (Nat.mul_succ _ _).symm
      let S := Cᶜ.neighborSet v
      have hMcard : M ≤ Fintype.card S := by
        change M ≤ Fintype.card (Cᶜ.neighborSet v)
        rw [Cᶜ.card_neighborSet_eq_degree]
        exact hblue_degree
      let j : Fin M ↪ S :=
        (Function.Embedding.nonempty_of_card_le (by simpa using hMcard)).some
      let f : Fin M ↪ Fin N := j.trans (Function.Embedding.subtype _)
      have hrec : RamseyAt F (completeCode (k + 1)) M := by
        simpa [M] using hk1
      rcases hrec (C.comap f) with hsmallred | hsmallblue
      · exact (hred (hsmallred.trans (SimpleGraph.Embedding.comap f C).isContained)).elim
      · have hsmallblue' :
            (⊤ : _root_.SimpleGraph (Fin (k + 1))) ⊑ Cᶜ.comap f := by
          have hcompl : (C.comap f)ᶜ = Cᶜ.comap f := by
            ext x y
            simp [f.injective.eq_iff]
          rw [← hcompl]
          exact hsmallblue
        let q : (⊤ : _root_.SimpleGraph (Fin (k + 1))).Copy Cᶜ :=
          (SimpleGraph.Embedding.comap f Cᶜ).toCopy.comp hsmallblue'.some
        have hq (i : Fin (k + 1)) : Cᶜ.Adj v (q i) := by
          have hj := (j (hsmallblue'.some i)).property
          change Cᶜ.Adj v (j (hsmallblue'.some i)).val at hj
          change Cᶜ.Adj v (f (hsmallblue'.some i))
          exact hj
        exact SimpleGraph.top_succ_isContained_of_copy_of_adj v q hq

/-- Every finite forest is Ramsey size linear. -/
theorem ramseySizeLinear_of_isAcyclic (F : GraphCode) (hF : F.graph.IsAcyclic) :
    RamseySizeLinear F := by
  classical
  by_cases hF0 : F.vertexCount = 0
  · refine ⟨0, fun H hH C ↦ ?_⟩
    left
    have : IsEmpty (Fin F.vertexCount) := by rw [hF0]; infer_instance
    exact SimpleGraph.IsContained.of_isEmpty
  · have hFpos : 0 < F.vertexCount := Nat.pos_of_ne_zero hF0
    let : Nonempty (Fin F.vertexCount) := Fin.pos_iff_nonempty.mp hFpos
    have htop : (⊤ : _root_.SimpleGraph (Fin F.vertexCount)).Connected :=
      _root_.SimpleGraph.connected_top
    obtain ⟨T, hFT, _hTtop, hT⟩ := htop.exists_isTree_le_of_le_of_isAcyclic le_top hF
    let FT : GraphCode := ⟨F.vertexCount, T⟩
    refine ⟨2 * F.vertexCount + 1, fun H hH ↦ ?_⟩
    by_cases hm : H.edgeCount = 0
    · rw [hm, Nat.mul_zero]
      have hH0 : H.vertexCount = 0 := by
        have := hH.vertexCount_le_twice_edgeCount
        omega
      intro C
      right
      have : IsEmpty (Fin H.vertexCount) := by rw [hH0]; infer_instance
      exact SimpleGraph.IsContained.of_isEmpty
    · have hmpos : 0 < H.edgeCount := Nat.pos_of_ne_zero hm
      have hHK : IsContained H (completeCode H.vertexCount) := by
        change H.graph ⊑ (⊤ : _root_.SimpleGraph (Fin H.vertexCount))
        exact _root_.SimpleGraph.IsContained.of_le le_top
      have hramsey :
          RamseyAt FT H ((F.vertexCount - 1) * (H.vertexCount - 1) + 1) :=
        (ramseyAt_tree_completeCode FT hT H.vertexCount).mono_right hHK
      have hbound :
          (F.vertexCount - 1) * (H.vertexCount - 1) + 1 ≤
            (2 * F.vertexCount + 1) * H.edgeCount := by
        calc
          (F.vertexCount - 1) * (H.vertexCount - 1) + 1 ≤
              F.vertexCount * H.vertexCount + 1 :=
            Nat.add_le_add_right
              (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)) 1
          _ ≤ F.vertexCount * (2 * H.edgeCount) + 1 :=
            Nat.add_le_add_right
              (Nat.mul_le_mul_left F.vertexCount hH.vertexCount_le_twice_edgeCount) 1
          _ ≤ (2 * F.vertexCount + 1) * H.edgeCount := by
            simpa [Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
              Nat.add_le_add_left hmpos (2 * F.vertexCount * H.edgeCount)
      have hFFT : IsContained F FT := by
        change F.graph ⊑ T
        exact _root_.SimpleGraph.IsContained.of_le hFT
      exact (hramsey.mono_left hFFT).mono_vertices hbound

end E79P

/- ===== from ErdosProblems.Erdos79.Uniform ===== -/
/-
# Exact counting in a finite uniform product space

This file supplies the elementary finite probability space used in the
probabilistic part of the proof of Erdős Problem 79.  An outcome assigns one
of `q` labels to every coordinate.  We work with cardinalities rather than a
measure: dividing all displayed cardinalities by `q ^ Fintype.card ι` gives
the corresponding uniform probabilities.

The main exact calculation is `card_cylinder`.  It says that requiring the
labels on a set `s` of coordinates to lie in a fixed allowed set `A` leaves
`A.card` choices on each coordinate of `s` and `q` choices everywhere else.
The final lemmas are finite union-bound / first-moment existence principles.
-/

open scoped BigOperators

namespace E79P.Uniform

noncomputable section

/-- The finite product space of `q`-valued labels on `ι`. -/
abbrev Outcome (ι : Type*) (q : ℕ) := ι → Fin q

/-- Outcomes whose labels on every coordinate of `s` belong to `A`. -/
def cylinder {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ℕ)
    (s : Finset ι) (A : Finset (Fin q)) : Finset (Outcome ι q) :=
  Finset.univ.filter fun ω ↦ ∀ i ∈ s, ω i ∈ A

@[simp]
theorem mem_cylinder {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}
    {s : Finset ι} {A : Finset (Fin q)} {ω : Outcome ι q} :
    ω ∈ cylinder q s A ↔ ∀ i ∈ s, ω i ∈ A := by
  simp [cylinder]

/-- There are exactly `q ^ |ι|` outcomes. -/
@[simp]
theorem card_outcome (ι : Type*) [Fintype ι] [DecidableEq ι] (q : ℕ) :
    Fintype.card (Outcome ι q) = q ^ Fintype.card ι := by
  simp [Outcome]

/-- Split a constrained labeling into its restrictions to `s` and to the
complement of `s`. -/
private def cylinderEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ℕ)
    (s : Finset ι) (A : Finset (Fin q)) :
    ↑(cylinder q s A) ≃ ((i : ↑s) → ↑A) × ((i : ↑sᶜ) → Fin q) where
  toFun ω :=
    (⟨fun i ↦ ⟨ω.1 i.1, (mem_cylinder.mp ω.2) i.1 i.2⟩,
      fun i ↦ ω.1 i.1⟩)
  invFun x :=
    ⟨fun i ↦ if hi : i ∈ s then (x.1 ⟨i, hi⟩).1
      else x.2 ⟨i, by simpa using hi⟩,
    mem_cylinder.mpr (by
      intro i hi
      simp [hi, (x.1 ⟨i, hi⟩).2])⟩
  left_inv ω := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ s
    · simp [hi]
    · simp [hi]
  right_inv x := by
    rcases x with ⟨a, b⟩
    apply Prod.ext
    · funext i
      apply Subtype.ext
      simp [i.2]
    · funext i
      have hi : (i.1 : ι) ∉ s := Finset.mem_compl.mp i.2
      simp [hi]

/-- Exact cardinality of a finite uniform-product cylinder. -/
theorem card_cylinder {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ℕ)
    (s : Finset ι) (A : Finset (Fin q)) :
    (cylinder q s A).card =
      A.card ^ s.card * q ^ (Fintype.card ι - s.card) := by
  calc
    (cylinder q s A).card = Fintype.card ↑(cylinder q s A) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card (((i : ↑s) → ↑A) × ((i : ↑sᶜ) → Fin q)) :=
      Fintype.card_congr (cylinderEquiv q s A)
    _ = A.card ^ s.card * q ^ (Fintype.card ι - s.card) := by
      simp

/-- The first `r` labels in `Fin q`. -/
def below (q r : ℕ) : Finset (Fin q) :=
  Finset.univ.filter fun x ↦ (x : ℕ) < r

@[simp]
theorem mem_below {q r : ℕ} {x : Fin q} :
    x ∈ below q r ↔ (x : ℕ) < r := by
  simp [below]

/-- If `r ≤ q`, exactly `r` members of `Fin q` are below `r`. -/
@[simp]
theorem card_below {q r : ℕ} (hrq : r ≤ q) : (below q r).card = r := by
  let e : Fin r ≃ ↑(below q r) :=
    { toFun := fun x ↦
        ⟨⟨x.1, lt_of_lt_of_le x.2 hrq⟩, by simp⟩
      invFun := fun x ↦ ⟨x.1.1, mem_below.mp x.2⟩
      left_inv := fun x ↦ by apply Fin.ext; rfl
      right_inv := fun x ↦ by apply Subtype.ext; apply Fin.ext; rfl }
  calc
    (below q r).card = Fintype.card ↑(below q r) := (Fintype.card_coe _).symm
    _ = Fintype.card (Fin r) := (Fintype.card_congr e).symm
    _ = r := Fintype.card_fin r

/-- Outcomes with label `< r` at every coordinate of `s`. -/
def thresholdCylinder {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q r : ℕ) (s : Finset ι) : Finset (Outcome ι q) :=
  cylinder q s (below q r)

@[simp]
theorem mem_thresholdCylinder {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q r : ℕ} {s : Finset ι} {ω : Outcome ι q} :
    ω ∈ thresholdCylinder q r s ↔ ∀ i ∈ s, (ω i : ℕ) < r := by
  simp [thresholdCylinder]

/-- Exact cardinality of a threshold cylinder. -/
theorem card_thresholdCylinder {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q r : ℕ} (hrq : r ≤ q) (s : Finset ι) :
    (thresholdCylinder q r s).card =
      r ^ s.card * q ^ (Fintype.card ι - s.card) := by
  simp [thresholdCylinder, card_cylinder, card_below hrq]

/-- The labels other than a specified label. -/
def exceptLabel {q : ℕ} (a : Fin q) : Finset (Fin q) :=
  Finset.univ.erase a

@[simp]
theorem mem_exceptLabel {q : ℕ} {a x : Fin q} :
    x ∈ exceptLabel a ↔ x ≠ a := by
  simp [exceptLabel]

@[simp]
theorem card_exceptLabel {q : ℕ} (a : Fin q) :
    (exceptLabel a).card = q - 1 := by
  simp [exceptLabel]

/-- A cylinder requiring every coordinate in `s` to avoid one specified
label.  This is the form used to count a completely blue vertex set when one
label is interpreted as red. -/
def avoidingLabelCylinder {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ℕ} (a : Fin q) (s : Finset ι) : Finset (Outcome ι q) :=
  cylinder q s (exceptLabel a)

@[simp]
theorem mem_avoidingLabelCylinder {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ℕ} {a : Fin q} {s : Finset ι} {ω : Outcome ι q} :
    ω ∈ avoidingLabelCylinder a s ↔ ∀ i ∈ s, ω i ≠ a := by
  simp [avoidingLabelCylinder]

/-- Double-counting identity underlying finite first-moment calculations:
sum event sizes by event, or sum the number of events containing each
outcome. -/
theorem sum_card_eq_sum_memberships {J Ω : Type*}
    [Fintype J] [Fintype Ω] [DecidableEq Ω] (B : J → Finset Ω) :
    ∑ j, (B j).card =
      ∑ ω, ((Finset.univ.filter fun j ↦ ω ∈ B j).card) := by
  classical
  calc
    ∑ j ∈ (Finset.univ : Finset J), (B j).card =
        ∑ j ∈ (Finset.univ : Finset J),
          ∑ ω ∈ (Finset.univ : Finset Ω), if ω ∈ B j then 1 else 0 := by
      simp
    _ = ∑ ω ∈ (Finset.univ : Finset Ω),
        ∑ j ∈ (Finset.univ : Finset J), if ω ∈ B j then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ ω ∈ (Finset.univ : Finset Ω),
        ((Finset.univ.filter fun j ↦ ω ∈ B j).card) := by
      simp

section ExponentialBounds

end ExponentialBounds

end

end E79P.Uniform

/- ===== from ErdosProblems.Erdos79.HighGirth ===== -/
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/







/-
# Dense finite graphs of arbitrarily large girth

This file proves the elementary finite first-moment construction used in the proof of
Erdős Problem 79.  Edges of the complete graph on `Fin L` receive independent uniform labels
in `Fin L`, and precisely the labels below `24` are retained.  A finite averaging argument gives
an outcome with more retained edges than short cycles plus `6 * L`.  We then remove one edge from
every surviving short cycle, using `SimpleGraph.killCopies`.
-/

open scoped SimpleGraph
open Finset Function

noncomputable section

namespace E79P
private theorem card_cycleGraph_edges {l : ℕ} (hl : 3 ≤ l) :
    #(SimpleGraph.cycleGraph l).edgeFinset = l := by
  have hdeg : ∀ v : Fin l, (SimpleGraph.cycleGraph l).degree v = 2 := by
    obtain ⟨n, hn⟩ : ∃ n, l = n + 3 := ⟨l - 3, by omega⟩
    subst l
    exact fun v ↦ SimpleGraph.cycleGraph_degree_three_le (n := n) (v := v)
  have hsum := (SimpleGraph.cycleGraph l).sum_degrees_eq_twice_card_edges
  simp_rw [hdeg] at hsum
  have : 2 * l = 2 * #(SimpleGraph.cycleGraph l).edgeFinset := by
    simpa [mul_comm] using hsum
  omega

private abbrev CompleteEdge (L : ℕ) := (⊤ : SimpleGraph (Fin L)).edgeSet

private abbrev EdgeOutcome (L : ℕ) := Uniform.Outcome (CompleteEdge L) L

/-- Retain precisely the complete-graph edges whose uniform label is below `24`. -/
private def sampledGraph {L : ℕ} (w : EdgeOutcome L) : SimpleGraph (Fin L) :=
  SimpleGraph.fromEdgeSet
    {e | ∃ he : e ∈ (⊤ : SimpleGraph (Fin L)).edgeSet, (w ⟨e, he⟩ : ℕ) < 24}

private theorem mem_sampledGraph_edgeSet {L : ℕ} {w : EdgeOutcome L} {e : Sym2 (Fin L)} :
    e ∈ (sampledGraph w).edgeSet ↔
      ∃ he : e ∈ (⊤ : SimpleGraph (Fin L)).edgeSet, (w ⟨e, he⟩ : ℕ) < 24 := by
  rw [sampledGraph, SimpleGraph.edgeSet_fromEdgeSet]
  constructor
  · exact fun he ↦ he.1
  · intro h
    exact ⟨h, by simpa using h.choose⟩

private noncomputable instance sampledGraph.edgeSetFintype {L : ℕ} (w : EdgeOutcome L) :
    Fintype (sampledGraph w).edgeSet := Fintype.ofFinite _

private theorem sampledGraph_edgeCard {L : ℕ} (w : EdgeOutcome L) :
    #(sampledGraph w).edgeFinset =
      #((Finset.univ : Finset (CompleteEdge L)).filter fun e ↦ (w e : ℕ) < 24) := by
  classical
  rw [SimpleGraph.edgeFinset_card]
  let f : (sampledGraph w).edgeSet →
      {e : CompleteEdge L // (w e : ℕ) < 24} := fun e ↦ by
    have he := mem_sampledGraph_edgeSet.mp e.2
    exact ⟨⟨e.1, he.choose⟩, he.choose_spec⟩
  have hf : Injective f := by
    intro e e' h
    apply Subtype.ext
    exact congrArg (fun x ↦ x.1.1) h
  have hsurj : Surjective f := by
    rintro ⟨⟨e, he⟩, hw⟩
    refine ⟨⟨e, mem_sampledGraph_edgeSet.mpr ⟨he, hw⟩⟩, ?_⟩
    rfl
  calc
    Fintype.card (sampledGraph w).edgeSet =
        Fintype.card {e : CompleteEdge L // (w e : ℕ) < 24} :=
      Fintype.card_congr (Equiv.ofBijective f ⟨hf, hsurj⟩)
    _ = Fintype.card
        ↑((Finset.univ : Finset (CompleteEdge L)).filter fun e ↦ (w e : ℕ) < 24) := by
      apply Fintype.card_congr
      exact
        { toFun := fun e ↦ ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2⟩⟩
          invFun := fun e ↦ ⟨e.1, (Finset.mem_filter.mp e.2).2⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
    _ = #((Finset.univ : Finset (CompleteEdge L)).filter fun e ↦ (w e : ℕ) < 24) :=
      Fintype.card_coe _

private def completeCycleCopy {l L : ℕ} (f : Fin l ↪ Fin L) :
    SimpleGraph.Copy (SimpleGraph.cycleGraph l) (⊤ : SimpleGraph (Fin L)) where
  toHom :=
    { toFun := f
      map_rel' := fun hab ↦ by simpa using f.injective.ne hab.ne }
  injective' := f.injective

/-- The complete-graph edges which must be retained in order for `f` to give a labelled copy of
the `l`-cycle. -/
private def cycleSupport {l L : ℕ} (f : Fin l ↪ Fin L) : Finset (CompleteEdge L) :=
  Finset.univ.map (completeCycleCopy f).mapEdgeSet

private theorem card_cycleSupport {l L : ℕ} (hl : 3 ≤ l) (f : Fin l ↪ Fin L) :
    #(cycleSupport f) = l := by
  classical
  rw [cycleSupport, Finset.card_map, Finset.card_univ,
    SimpleGraph.card_edgeSet, card_cycleGraph_edges hl]

/-- Number of injective labelled `l`-cycles whose required edges all survive in the outcome. -/
private abbrev CycleCandidates {L : ℕ} (w : EdgeOutcome L) (l : ℕ) :=
  {f : Fin l ↪ Fin L // f ∈
    (Finset.univ.filter fun f ↦
      w ∈ Uniform.thresholdCylinder L 24 (cycleSupport f))}

private def cycleCandidateCount {L : ℕ} (w : EdgeOutcome L) (l : ℕ) : ℕ :=
  Nat.card (CycleCandidates w l)

private theorem copyEmbedding_mem_candidates {L l : ℕ} (w : EdgeOutcome L)
    (c : SimpleGraph.Copy (SimpleGraph.cycleGraph l) (sampledGraph w)) :
    c.toEmbedding ∈ (Finset.univ.filter fun f : Fin l ↪ Fin L ↦
      w ∈ Uniform.thresholdCylinder L 24 (cycleSupport f)) := by
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, Uniform.mem_thresholdCylinder.mpr ?_⟩
  intro e he
  rw [cycleSupport, Finset.mem_map] at he
  obtain ⟨e', -, rfl⟩ := he
  have hmem := c.toHom.map_mem_edgeSet e'.2
  have hlow := (mem_sampledGraph_edgeSet.mp hmem).choose_spec
  simpa [completeCycleCopy, SimpleGraph.Copy.mapEdgeSet,
    SimpleGraph.Hom.mapEdgeSet, SimpleGraph.Copy.toEmbedding] using hlow

private def copyToCandidate {L l : ℕ} (w : EdgeOutcome L) :
    SimpleGraph.Copy (SimpleGraph.cycleGraph l) (sampledGraph w) →
      CycleCandidates w l :=
  fun c ↦ ⟨c.toEmbedding, copyEmbedding_mem_candidates w c⟩

private theorem copyToCandidate_injective {L l : ℕ} (w : EdgeOutcome L) :
    Injective (copyToCandidate (l := l) w) := by
  intro c c' h
  apply SimpleGraph.Copy.ext
  intro x
  exact congrArg (fun z ↦ z.1.1 x) h

private theorem labelledCopyCount_eq_natCard {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    G.labelledCopyCount H = Nat.card (SimpleGraph.Copy H G) := by
  classical
  unfold SimpleGraph.labelledCopyCount
  exact Nat.card_eq_fintype_card.symm

private theorem labelledCopyCount_cycle_le_candidateCount {L l : ℕ} (w : EdgeOutcome L) :
    (sampledGraph w).labelledCopyCount (SimpleGraph.cycleGraph l) ≤
      cycleCandidateCount w l := by
  rw [labelledCopyCount_eq_natCard]
  exact Nat.card_le_card_of_injective (copyToCandidate (l := l) w)
    (copyToCandidate_injective w)

private theorem edgeFinset_card_eq_natCard {V : Type*} (G : SimpleGraph V)
    [Fintype G.edgeSet] : #G.edgeFinset = Nat.card G.edgeSet := by
  rw [SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card]

private theorem card_completeEdge (L : ℕ) :
    Fintype.card (CompleteEdge L) = L.choose 2 := by
  rw [← SimpleGraph.edgeFinset_card,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  simp

private theorem sum_sampledGraph_edgeCard {L : ℕ} (hL : 24 ≤ L) :
    (∑ w : EdgeOutcome L, #(sampledGraph w).edgeFinset) =
      Fintype.card (CompleteEdge L) *
        (24 * L ^ (Fintype.card (CompleteEdge L) - 1)) := by
  classical
  let B : CompleteEdge L → Finset (EdgeOutcome L) := fun e ↦
    Uniform.thresholdCylinder L 24 {e}
  have hdouble := Uniform.sum_card_eq_sum_memberships B
  calc
    (∑ w : EdgeOutcome L, #(sampledGraph w).edgeFinset) =
        ∑ w : EdgeOutcome L,
          #((Finset.univ : Finset (CompleteEdge L)).filter fun e ↦ (w e : ℕ) < 24) := by
      apply Finset.sum_congr rfl
      intro w _
      exact sampledGraph_edgeCard w
    _ = ∑ w : EdgeOutcome L,
          #((Finset.univ : Finset (CompleteEdge L)).filter fun e ↦ w ∈ B e) := by
      apply Finset.sum_congr rfl
      intro w _
      apply congrArg Finset.card
      ext e
      simp [B, Uniform.mem_thresholdCylinder]
    _ = ∑ e : CompleteEdge L, #(B e) := hdouble.symm
    _ = Fintype.card (CompleteEdge L) *
        (24 * L ^ (Fintype.card (CompleteEdge L) - 1)) := by
      simp [B, Uniform.card_thresholdCylinder hL]

private theorem card_embedding_le_functions (l L : ℕ) :
    Fintype.card (Fin l ↪ Fin L) ≤ L ^ l := by
  classical
  have h := Fintype.card_le_of_injective
    (fun f : Fin l ↪ Fin L ↦ (f : Fin l → Fin L))
    (fun _ _ hff' ↦ DFunLike.coe_injective hff')
  simpa [Fintype.card_fun] using h

private theorem sum_cycleCandidateCount_le {L l : ℕ} (hL : 24 ≤ L) (hl : 3 ≤ l) :
    (∑ w : EdgeOutcome L, cycleCandidateCount w l) ≤
      24 ^ l * L ^ Fintype.card (CompleteEdge L) := by
  classical
  cases isEmpty_or_nonempty (Fin l ↪ Fin L) with
  | inl hempty => simp [cycleCandidateCount, CycleCandidates]
  | inr hnempty =>
      let B : (Fin l ↪ Fin L) → Finset (EdgeOutcome L) := fun f ↦
        Uniform.thresholdCylinder L 24 (cycleSupport f)
      have hdouble := Uniform.sum_card_eq_sum_memberships B
      let f₀ : Fin l ↪ Fin L := Classical.choice hnempty
      have hlM : l ≤ Fintype.card (CompleteEdge L) := by
        rw [← card_cycleSupport hl f₀]
        exact Finset.card_le_univ _
      calc
        (∑ w : EdgeOutcome L, cycleCandidateCount w l) =
            ∑ w : EdgeOutcome L,
              #((Finset.univ : Finset (Fin l ↪ Fin L)).filter fun f ↦ w ∈ B f) := by
          apply Finset.sum_congr rfl
          intro w _
          change Nat.card
              ↑((Finset.univ : Finset (Fin l ↪ Fin L)).filter fun f ↦ w ∈ B f) =
            #((Finset.univ : Finset (Fin l ↪ Fin L)).filter fun f ↦ w ∈ B f)
          rw [Nat.card_eq_fintype_card, Fintype.card_coe]
        _ = ∑ f : Fin l ↪ Fin L, #(B f) := hdouble.symm
        _ = Fintype.card (Fin l ↪ Fin L) *
            (24 ^ l * L ^ (Fintype.card (CompleteEdge L) - l)) := by
          simp [B, Uniform.card_thresholdCylinder hL, card_cycleSupport hl]
        _ ≤ L ^ l * (24 ^ l * L ^ (Fintype.card (CompleteEdge L) - l)) :=
          Nat.mul_le_mul_right _ (card_embedding_le_functions l L)
        _ = 24 ^ l * L ^ Fintype.card (CompleteEdge L) := by
          calc
            L ^ l * (24 ^ l * L ^ (Fintype.card (CompleteEdge L) - l)) =
                24 ^ l * (L ^ l * L ^ (Fintype.card (CompleteEdge L) - l)) := by
              ac_rfl
            _ = 24 ^ l * L ^ Fintype.card (CompleteEdge L) := by
              rw [← pow_add, Nat.add_sub_of_le hlM]

private def shortCycleBudget (g : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (g - 3), 24 ^ (i + 3)

private def shortCycleCount {L : ℕ} (w : EdgeOutcome L) (g : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (g - 3), cycleCandidateCount w (i + 3)

private theorem sum_shortCycleCount_le {L g : ℕ} (hL : 24 ≤ L) :
    (∑ w : EdgeOutcome L, shortCycleCount w g) ≤
      shortCycleBudget g * L ^ Fintype.card (CompleteEdge L) := by
  classical
  calc
    (∑ w : EdgeOutcome L, shortCycleCount w g) =
        ∑ i ∈ Finset.range (g - 3), ∑ w : EdgeOutcome L, cycleCandidateCount w (i + 3) := by
      simp only [shortCycleCount]
      rw [Finset.sum_comm]
    _ ≤ ∑ i ∈ Finset.range (g - 3),
        24 ^ (i + 3) * L ^ Fintype.card (CompleteEdge L) := by
      apply Finset.sum_le_sum
      intro i _
      exact sum_cycleCandidateCount_le hL (by omega)
    _ = shortCycleBudget g * L ^ Fintype.card (CompleteEdge L) := by
      simp [shortCycleBudget, Finset.sum_mul]

private theorem exists_goodSample (g : ℕ) :
    let B := shortCycleBudget g
    let L := B + 25
    ∃ w : EdgeOutcome L,
      shortCycleCount w g + 6 * L < #(sampledGraph w).edgeFinset := by
  classical
  dsimp only
  let B := shortCycleBudget g
  let L := B + 25
  let M := Fintype.card (CompleteEdge L)
  have hL : L = B + 25 := rfl
  have hL24 : 24 ≤ L := by omega
  have hMcard : M = L.choose 2 := card_completeEdge L
  have htwoM : 2 * M = L * (L - 1) := by
    rw [mul_comm, hMcard, Nat.choose_two_right,
      Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self L)]
  have hMpos : 0 < M := by
    have hLpos : 0 < L * (L - 1) := Nat.mul_pos (by omega) (by omega)
    omega
  have hpow : L ^ M = L ^ (M - 1) * L := by
    conv_lhs => rw [show M = (M - 1) + 1 by omega]
    exact pow_succ _ _
  have hcoef : B + 6 * L < 12 * (L - 1) := by
    omega
  have hfactor : 0 < L ^ (M - 1) * L :=
    Nat.mul_pos (pow_pos (by omega) (M - 1)) (by omega)
  have hmul := Nat.mul_lt_mul_of_pos_right hcoef hfactor
  have harith :
      B * L ^ M + (6 * L) * L ^ M < M * (24 * L ^ (M - 1)) := by
    calc
      B * L ^ M + (6 * L) * L ^ M =
          (B + 6 * L) * (L ^ (M - 1) * L) := by rw [hpow]; ring
      _ < 12 * (L - 1) * (L ^ (M - 1) * L) := hmul
      _ = 12 * (L * (L - 1)) * L ^ (M - 1) := by ring
      _ = 12 * (2 * M) * L ^ (M - 1) := by rw [← htwoM]
      _ = M * (24 * L ^ (M - 1)) := by ring
  have hedge := sum_sampledGraph_edgeCard hL24
  have hcycle := sum_shortCycleCount_le (g := g) hL24
  have hstrict :
      (∑ w : EdgeOutcome L, shortCycleCount w g) +
          ∑ _w : EdgeOutcome L, 6 * L <
        ∑ w : EdgeOutcome L, #(sampledGraph w).edgeFinset := by
    calc
      (∑ w : EdgeOutcome L, shortCycleCount w g) +
            ∑ _w : EdgeOutcome L, 6 * L ≤
          B * L ^ M + (6 * L) * L ^ M := by
        apply Nat.add_le_add hcycle
        simp [M, mul_comm, mul_assoc]
      _ < M * (24 * L ^ (M - 1)) := harith
      _ = ∑ w : EdgeOutcome L, #(sampledGraph w).edgeFinset := by
        simpa [M] using hedge.symm
  by_contra hnone
  push Not at hnone
  have hle :
      (∑ w : EdgeOutcome L, #(sampledGraph w).edgeFinset) ≤
        ∑ w : EdgeOutcome L, (shortCycleCount w g + 6 * L) :=
    Finset.sum_le_sum fun w _ ↦ hnone w
  rw [Finset.sum_add_distrib] at hle
  omega

private theorem labelledCopyCount_mono {V W : Type*} [Fintype V] [Fintype W]
    {G G' : SimpleGraph V} (h : G' ≤ G) (H : SimpleGraph W) :
    G'.labelledCopyCount H ≤ G.labelledCopyCount H := by
  classical
  unfold SimpleGraph.labelledCopyCount
  apply Fintype.card_le_of_injective
    (fun f : SimpleGraph.Copy H G' =>
      (SimpleGraph.Copy.ofLE G' G h).comp f)
  intro f f' hff'
  apply SimpleGraph.Copy.ext
  intro x
  have := DFunLike.congr_fun hff' x
  simpa using this

/-- Starting with `G`, successively remove one edge from every copy of the cycle graphs of
lengths `3, 4, ..., n + 2`. -/
private noncomputable def killShortCycles {V : Type*} (G : SimpleGraph V) :
    ℕ → SimpleGraph V
  | 0 => G
  | n + 1 => (killShortCycles G n).killCopies (SimpleGraph.cycleGraph (n + 3))

private theorem killShortCycles_le {V : Type*} (G : SimpleGraph V) (n : ℕ) :
    killShortCycles G n ≤ G := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact SimpleGraph.killCopies_le_left.trans ih

private noncomputable instance killShortCycles.edgeSetFintype {V : Type*}
    [Finite V] (G : SimpleGraph V) (n : ℕ) :
    Fintype (killShortCycles G n).edgeSet := Fintype.ofFinite _

private theorem free_mono_right {V W : Type*} {H : SimpleGraph W} {G G' : SimpleGraph V}
    (hfree : H.Free G) (hle : G' ≤ G) : H.Free G' := by
  intro hcopy
  exact hfree (hcopy.trans (SimpleGraph.IsContained.of_le hle))

private theorem killShortCycles_free {V : Type*} (G : SimpleGraph V) {i n : ℕ}
    (hi : i < n) :
    (SimpleGraph.cycleGraph (i + 3)).Free (killShortCycles G n) := by
  induction n with
  | zero => simp at hi
  | succ n ih =>
      by_cases hin : i = n
      · subst i
        exact SimpleGraph.free_killCopies (by
          intro hbot
          have hadj : (SimpleGraph.cycleGraph (n + 3)).Adj
              ⟨0, by omega⟩ ⟨1, by omega⟩ := by
            simp [SimpleGraph.cycleGraph_adj']
          have : ¬ (SimpleGraph.cycleGraph (n + 3)).Adj
              ⟨0, by omega⟩ ⟨1, by omega⟩ := by simp [hbot]
          exact this hadj)
      · have hil : i < n := by omega
        exact free_mono_right (ih hil) SimpleGraph.killCopies_le_left

private theorem edgeCard_le_killShortCycles_add {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (n : ℕ) :
    #G.edgeFinset ≤ #(killShortCycles G n).edgeFinset +
      ∑ i ∈ Finset.range n, G.labelledCopyCount (SimpleGraph.cycleGraph (i + 3)) := by
  classical
  induction n with
  | zero =>
      rw [show Finset.range 0 = ∅ by rfl, Finset.sum_empty, add_zero]
      apply Nat.le_of_eq
      apply congrArg Finset.card
      ext e
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeFinset]
      rfl
  | succ n ih =>
      let P := killShortCycles G n
      let C := SimpleGraph.cycleGraph (n + 3)
      have hkill : #P.edgeFinset ≤ #(P.killCopies C).edgeFinset + P.copyCount C :=
        SimpleGraph.le_card_edgeFinset_killCopies_add_copyCount
      have hcopy : P.copyCount C ≤ G.labelledCopyCount C :=
        (SimpleGraph.copyCount_le_labelledCopyCount).trans
          (labelledCopyCount_mono (killShortCycles_le G n) C)
      dsimp [P, C] at hkill hcopy
      have hsucc : #(killShortCycles G (n + 1)).edgeFinset =
          #((killShortCycles G n).killCopies
            (SimpleGraph.cycleGraph (n + 3))).edgeFinset := by
        apply congrArg Finset.card
        ext e
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeFinset]
        rfl
      rw [hsucc, Finset.sum_range_succ]
      calc
        #G.edgeFinset ≤ #(killShortCycles G n).edgeFinset +
            ∑ i ∈ Finset.range n,
              G.labelledCopyCount (SimpleGraph.cycleGraph (i + 3)) := ih
        _ ≤ (#((killShortCycles G n).killCopies
              (SimpleGraph.cycleGraph (n + 3))).edgeFinset +
              (killShortCycles G n).copyCount (SimpleGraph.cycleGraph (n + 3))) +
            ∑ i ∈ Finset.range n,
              G.labelledCopyCount (SimpleGraph.cycleGraph (i + 3)) :=
          Nat.add_le_add_right hkill _
        _ ≤ (#((killShortCycles G n).killCopies
              (SimpleGraph.cycleGraph (n + 3))).edgeFinset +
              G.labelledCopyCount (SimpleGraph.cycleGraph (n + 3))) +
            ∑ i ∈ Finset.range n,
              G.labelledCopyCount (SimpleGraph.cycleGraph (i + 3)) := by omega
        _ = _ := by omega

private theorem egirth_killShortCycles {V : Type*} (G : SimpleGraph V) (g : ℕ) :
    (g : ℕ∞) ≤ (killShortCycles G (g - 3)).egirth := by
  rw [SimpleGraph.le_egirth]
  intro a w hw
  by_contra hnot
  have hwlt : w.length < g := by
    exact_mod_cast (not_le.mp hnot)
  have hthree : 3 ≤ w.length := hw.three_le_length
  have hi : w.length - 3 < g - 3 := by omega
  have hfree := killShortCycles_free G hi
  have hlen : w.length - 3 + 3 = w.length := by omega
  rw [hlen] at hfree
  apply hfree
  rw [SimpleGraph.cycleGraph_isContained_iff hthree]
  exact ⟨a, w, hw, rfl⟩

/-- For every prescribed lower bound on the girth, there is a finite graph with more than six
edges per vertex.  This is the dense high-girth input used in the resolution of Erdős Problem 79. -/
theorem exists_dense_highGirth (g : ℕ) :
    ∃ G : GraphCode,
      (g : ℕ∞) ≤ G.graph.egirth ∧ 6 * G.vertexCount < G.edgeCount := by
  classical
  let B := shortCycleBudget g
  let L := B + 25
  obtain ⟨w, hw⟩ := exists_goodSample g
  let Y := sampledGraph w
  let X := killShortCycles Y (g - 3)
  have hedge := edgeCard_le_killShortCycles_add Y (g - 3)
  have hcopies :
      (∑ i ∈ Finset.range (g - 3),
          Y.labelledCopyCount (SimpleGraph.cycleGraph (i + 3))) ≤
        shortCycleCount w g := by
    apply Finset.sum_le_sum
    intro i _
    exact labelledCopyCount_cycle_le_candidateCount w
  have hdense : 6 * L < #X.edgeFinset := by
    have hbound : #Y.edgeFinset ≤ #X.edgeFinset + shortCycleCount w g :=
      hedge.trans (Nat.add_le_add_left hcopies _)
    dsimp [Y] at hw hbound
    omega
  refine ⟨⟨L, X⟩, ?_, ?_⟩
  · exact egirth_killShortCycles Y g
  · have hnat : 6 * L < Nat.card X.edgeSet := by
      exact lt_of_lt_of_eq hdense (edgeFinset_card_eq_natCard X)
    change 6 * L < Nat.card X.edgeSet
    exact hnat

end E79P

/- ===== from ErdosProblems.Erdos79.Minimal ===== -/
/-
# Minimal obstructions and the infinitude assembly for Erdős Problem 79

This file contains the finite order-theoretic part of Wigderson's argument.  It is deliberately
separated from the two quantitative inputs (forests are Ramsey size linear, and dense graphs of
arbitrarily large girth exist): those inputs plug into the assembly theorem near the end.
-/

open scoped SimpleGraph

noncomputable section

namespace E79P
/-- The size used to well-found ordinary containment of finite graphs. -/
def GraphCode.size (G : GraphCode) : ℕ := G.vertexCount + G.edgeCount

/-- Ordinary proper subgraph containment, taken up to graph isomorphism. -/
def ProperSubgraph (F G : GraphCode) : Prop :=
  IsContained F G ∧ ¬ Isomorphic F G

/-- A graph which is not Ramsey size linear although every proper subgraph is. -/
def MinimallyNonRamseySizeLinear (G : GraphCode) : Prop :=
  ¬ RamseySizeLinear G ∧
    ∀ F : GraphCode, ProperSubgraph F G → RamseySizeLinear F

namespace IsContained

/-- A containment between finite graphs with the same numbers of vertices and edges is an
isomorphism.  Surjectivity on vertices follows from the vertex count; equality of the finite
edge sets upgrades the edge-preserving copy to an adjacency-reflecting equivalence. -/
theorem isomorphic_of_vertexCount_eq_of_edgeCount_eq {F G : GraphCode}
    (h : IsContained F G) (hv : F.vertexCount = G.vertexCount)
    (he : F.edgeCount = G.edgeCount) : Isomorphic F G := by
  classical
  rcases h with ⟨f⟩
  have hf_surj : Function.Surjective f.toEmbedding := by
    exact ((Fintype.bijective_iff_injective_and_card f.toEmbedding).mpr
      ⟨f.injective, by simpa using hv⟩).surjective
  let e : Fin F.vertexCount ≃ Fin G.vertexCount :=
    f.toEmbedding.equivOfSurjective hf_surj
  have hedge_card : Fintype.card F.graph.edgeSet = Fintype.card G.graph.edgeSet := by
    simpa only [GraphCode.edgeCount, Nat.card_eq_fintype_card] using he
  have hedge_surj : Function.Surjective f.mapEdgeSet :=
    ((Fintype.bijective_iff_injective_and_card f.mapEdgeSet).mpr
      ⟨f.mapEdgeSet.injective, hedge_card⟩).surjective
  refine ⟨{ e with map_rel_iff' := ?_ }⟩
  intro u v
  change G.graph.Adj (f u) (f v) ↔ F.graph.Adj u v
  constructor
  · intro huv
    let eg : G.graph.edgeSet := ⟨s(f u, f v), huv⟩
    obtain ⟨ef, hef⟩ := hedge_surj eg
    have hedge : (ef : Sym2 (Fin F.vertexCount)) = s(u, v) := by
      apply Sym2.map.injective f.injective
      have hval := congrArg Subtype.val hef
      simpa [eg, SimpleGraph.Copy.mapEdgeSet, SimpleGraph.Hom.mapEdgeSet] using hval
    rw [← SimpleGraph.mem_edgeSet]
    simpa [hedge] using ef.property
  · exact f.toHom.map_adj

/-- Equal total size under containment forces isomorphism. -/
theorem isomorphic_of_size_eq {F G : GraphCode} (h : IsContained F G)
    (hs : F.size = G.size) : Isomorphic F G := by
  have hv := h.vertexCount_le
  have he := h.edgeCount_le
  simp only [GraphCode.size] at hs
  apply h.isomorphic_of_vertexCount_eq_of_edgeCount_eq
  · omega
  · omega

end IsContained

/-- Proper containment strictly decreases `vertexCount + edgeCount`. -/
theorem ProperSubgraph.size_lt {F G : GraphCode} (h : ProperSubgraph F G) :
    F.size < G.size := by
  rcases h with ⟨hFG, hniso⟩
  have hv := hFG.vertexCount_le
  have he := hFG.edgeCount_le
  have hle : F.size ≤ G.size := Nat.add_le_add hv he
  exact hle.lt_of_ne fun hs ↦ hniso (hFG.isomorphic_of_size_eq hs)

namespace MinimallyNonRamseySizeLinear

/-- Minimal-obstruction status is invariant under graph isomorphism. -/
theorem congr {F G : GraphCode} (hFG : Isomorphic F G) :
    MinimallyNonRamseySizeLinear F ↔ MinimallyNonRamseySizeLinear G := by
  have forward : ∀ {A B : GraphCode}, Isomorphic A B →
      MinimallyNonRamseySizeLinear A → MinimallyNonRamseySizeLinear B := by
    intro A B hAB
    rintro ⟨hbad, hproper⟩
    refine ⟨?_, ?_⟩
    · exact fun hB ↦ hbad ((RamseySizeLinear.congr hAB).mpr hB)
    · intro H hHB
      apply hproper H
      refine ⟨hHB.1.trans hAB.isContained', ?_⟩
      intro hHA
      exact hHB.2 (hHA.trans hAB)
  exact ⟨forward hFG, forward hFG.symm⟩

end MinimallyNonRamseySizeLinear

/- ## Finite minimality -/

/-- The natural-number sizes attained by non-Ramsey-size-linear subgraphs of `X`. -/
def badSubgraphSizes (X : GraphCode) : Set ℕ :=
  {n | ∃ F : GraphCode, IsContained F X ∧ ¬ RamseySizeLinear F ∧ F.size = n}

theorem badSubgraphSizes_nonempty {X : GraphCode} (hX : ¬ RamseySizeLinear X) :
    (badSubgraphSizes X).Nonempty := by
  exact ⟨X.size, X, IsContained.rfl, hX, rfl⟩

/-- A finite non-Ramsey-size-linear graph contains a containment-minimal obstruction. -/
theorem exists_minimallyNonRamseySizeLinear_subgraph {X : GraphCode}
    (hX : ¬ RamseySizeLinear X) :
    ∃ G : GraphCode, IsContained G X ∧ MinimallyNonRamseySizeLinear G := by
  let n := sInf (badSubgraphSizes X)
  have hn_mem : n ∈ badSubgraphSizes X :=
    Nat.sInf_mem (badSubgraphSizes_nonempty hX)
  obtain ⟨G, hGX, hbadG, hsizeG⟩ := hn_mem
  refine ⟨G, hGX, hbadG, ?_⟩
  intro F hFG
  by_contra hbadF
  have hFmem : F.size ∈ badSubgraphSizes X :=
    ⟨F, hFG.1.trans hGX, hbadF, rfl⟩
  have hmin : n ≤ F.size := Nat.sInf_le hFmem
  rw [← hsizeG] at hmin
  exact (not_lt_of_ge hmin) hFG.size_lt

/- ## Cycles and finite-family girth avoidance -/

/-- If all finite forests are Ramsey size linear, every minimal obstruction is cyclic. -/
theorem MinimallyNonRamseySizeLinear.not_isAcyclic
    (forest_ramseySizeLinear : ∀ F : GraphCode,
      F.graph.IsAcyclic → RamseySizeLinear F)
    {G : GraphCode} (hG : MinimallyNonRamseySizeLinear G) :
    ¬ G.graph.IsAcyclic := by
  intro hacyc
  exact hG.1 (forest_ramseySizeLinear G hacyc)

/-- A natural girth threshold strictly exceeding the girth of every graph in `s`.
The extra `max 3` makes it a valid graph-girth request even for the empty family. -/
def familyGirthBound (s : Finset GraphCode) : ℕ :=
  max 3 (s.sup fun G ↦ G.graph.girth + 1)

theorem three_le_familyGirthBound (s : Finset GraphCode) :
    3 ≤ familyGirthBound s := le_max_left _ _

theorem girth_lt_familyGirthBound {s : Finset GraphCode} {G : GraphCode}
    (hGs : G ∈ s) : G.graph.girth < familyGirthBound s := by
  have hsup : G.graph.girth + 1 ≤ s.sup (fun H ↦ H.graph.girth + 1) :=
    Finset.le_sup (f := fun H : GraphCode ↦ H.graph.girth + 1) hGs
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hsup.trans (le_max_right _ _))

/-- A graph whose extended girth reaches `familyGirthBound s` contains no cyclic member of `s`.
Using extended girth here lets the high-girth construction return an acyclic graph as a harmless
degenerate possibility, although the dense graphs used in the final application are cyclic. -/
theorem not_isContained_of_familyGirthBound_le_egirth
    {s : Finset GraphCode} {X : GraphCode}
    (hcyclic : ∀ G ∈ s, ¬ G.graph.IsAcyclic)
    (hgirth : (familyGirthBound s : ℕ∞) ≤ X.graph.egirth) :
    ∀ G ∈ s, ¬ IsContained G X := by
  intro G hGs hGX
  have hle : X.graph.egirth ≤ G.graph.egirth := hGX.egirth_le
  have hfinite : (G.graph.girth : ℕ∞) = G.graph.egirth := by
    exact ENat.natCast_toNat (SimpleGraph.egirth_eq_top.not.mpr (hcyclic G hGs))
  have hbound : (familyGirthBound s : ℕ∞) ≤ (G.graph.girth : ℕ∞) := by
    rw [hfinite]
    exact hgirth.trans hle
  exact (not_le_of_gt (girth_lt_familyGirthBound hGs))
    (ENat.natCast_le_natCast.mp hbound)

/- ## Assembly from the two quantitative inputs -/

/-- The two mathematical inputs needed by the purely order-theoretic infinitude argument. -/
structure InfinitudeInputs : Prop where
  forest_ramseySizeLinear : ∀ F : GraphCode,
    F.graph.IsAcyclic → RamseySizeLinear F
  nonRamseySizeLinear_largeGirth : ∀ g : ℕ, 3 ≤ g →
    ∃ X : GraphCode, ¬ RamseySizeLinear X ∧ (g : ℕ∞) ≤ X.graph.egirth

/-- Package the exact interfaces supplied by the forest, density-obstruction, and dense
high-girth modules.  The high-girth construction gives the stronger inequality `6v < e`, while
the first-moment obstruction only needs `5v < e`. -/
theorem infinitudeInputs_of_dense_highGirth
    (forest_ramseySizeLinear : ∀ F : GraphCode,
      F.graph.IsAcyclic → RamseySizeLinear F)
    (dense_not_ramseySizeLinear : ∀ F : GraphCode,
      5 * F.vertexCount < F.edgeCount → ¬ RamseySizeLinear F)
    (dense_highGirth : ∀ g : ℕ, ∃ X : GraphCode,
      (g : ℕ∞) ≤ X.graph.egirth ∧ 6 * X.vertexCount < X.edgeCount) :
    InfinitudeInputs := by
  refine ⟨forest_ramseySizeLinear, ?_⟩
  intro g _hg
  obtain ⟨X, hgirth, hdense⟩ := dense_highGirth g
  refine ⟨X, dense_not_ramseySizeLinear X ?_, hgirth⟩
  omega

/-- Given the forest theorem and non-linear graphs of arbitrary girth, every finite family of
minimal obstructions can be avoided up to isomorphism. -/
theorem exists_minimal_avoiding_finset (inputs : InfinitudeInputs)
    (s : Finset GraphCode)
    (hs : ∀ G ∈ s, MinimallyNonRamseySizeLinear G) :
    ∃ G : GraphCode, MinimallyNonRamseySizeLinear G ∧
      ∀ H ∈ s, ¬ Isomorphic G H := by
  obtain ⟨X, hbadX, hgirthX⟩ :=
    inputs.nonRamseySizeLinear_largeGirth (familyGirthBound s)
      (three_le_familyGirthBound s)
  have hcyclic : ∀ H ∈ s, ¬ H.graph.IsAcyclic := by
    intro H hHs
    exact (hs H hHs).not_isAcyclic inputs.forest_ramseySizeLinear
  have havoids : ∀ H ∈ s, ¬ IsContained H X :=
    not_isContained_of_familyGirthBound_le_egirth hcyclic hgirthX
  obtain ⟨G, hGX, hminG⟩ := exists_minimallyNonRamseySizeLinear_subgraph hbadX
  refine ⟨G, hminG, ?_⟩
  intro H hHs hGH
  exact havoids H hHs (hGH.isContained'.trans hGX)

/- ## Turning finite-family avoidance into a sequence -/

/-- The representation-independent finite-family avoidance principle. -/
abbrev FiniteFamilyAvoidance : Prop :=
  ∀ s : Finset GraphCode,
  (∀ G ∈ s, MinimallyNonRamseySizeLinear G) →
    ∃ G : GraphCode, MinimallyNonRamseySizeLinear G ∧
      ∀ H ∈ s, ¬ Isomorphic G H

variable (avoid : FiniteFamilyAvoidance)

/-- A deterministic choice of a new obstruction outside a finite family.  The fallback branch is
never reached in the recursive construction below. -/
noncomputable def freshObstruction (s : Finset GraphCode) : GraphCode :=
  by
    classical
    exact if hs : ∀ G ∈ s, MinimallyNonRamseySizeLinear G then
      Classical.choose (avoid s hs)
    else completeCode 0

theorem freshObstruction_minimal {s : Finset GraphCode}
    (hs : ∀ G ∈ s, MinimallyNonRamseySizeLinear G) :
    MinimallyNonRamseySizeLinear (freshObstruction avoid s) := by
  classical
  simp only [freshObstruction, dif_pos hs]
  exact (Classical.choose_spec (avoid s hs)).1

theorem freshObstruction_not_isomorphic {s : Finset GraphCode}
    (hs : ∀ G ∈ s, MinimallyNonRamseySizeLinear G)
    {H : GraphCode} (hHs : H ∈ s) :
    ¬ Isomorphic (freshObstruction avoid s) H := by
  classical
  simp only [freshObstruction, dif_pos hs]
  exact (Classical.choose_spec (avoid s hs)).2 H hHs

/-- The finite set of obstructions selected during the first `n` stages. -/
noncomputable def obstructionSets : ℕ → Finset GraphCode
  | 0 => ∅
  | n + 1 => by
      classical
      exact insert (freshObstruction avoid (obstructionSets n)) (obstructionSets n)

theorem obstructionSets_mono : Monotone (obstructionSets avoid) := by
  classical
  apply monotone_nat_of_le_succ
  intro n
  simp only [obstructionSets]
  exact Finset.subset_insert _ _

theorem obstructionSets_all_minimal (n : ℕ) :
    ∀ G ∈ obstructionSets avoid n, MinimallyNonRamseySizeLinear G := by
  classical
  induction n with
  | zero => simp [obstructionSets]
  | succ n ih =>
      intro G hG
      rw [obstructionSets] at hG
      rcases Finset.mem_insert.mp hG with rfl | hG
      · exact freshObstruction_minimal avoid ih
      · exact ih G hG

/-- The recursively selected sequence of minimal obstructions. -/
noncomputable def obstructionSequence (n : ℕ) : GraphCode :=
  freshObstruction avoid (obstructionSets avoid n)

theorem obstructionSequence_minimal (n : ℕ) :
    MinimallyNonRamseySizeLinear (obstructionSequence avoid n) :=
  freshObstruction_minimal avoid (obstructionSets_all_minimal avoid n)

theorem obstructionSequence_mem_obstructionSets_succ (n : ℕ) :
    obstructionSequence avoid n ∈ obstructionSets avoid (n + 1) := by
  classical
  simp [obstructionSequence, obstructionSets]

theorem obstructionSequence_mem_obstructionSets {i j : ℕ} (hij : i < j) :
    obstructionSequence avoid i ∈ obstructionSets avoid j := by
  exact obstructionSets_mono avoid (Nat.succ_le_iff.mpr hij)
    (obstructionSequence_mem_obstructionSets_succ avoid i)

theorem obstructionSequence_not_isomorphic_of_lt {i j : ℕ} (hij : i < j) :
    ¬ Isomorphic (obstructionSequence avoid i) (obstructionSequence avoid j) := by
  intro hijIso
  have hnew := freshObstruction_not_isomorphic avoid
    (obstructionSets_all_minimal avoid j)
    (obstructionSequence_mem_obstructionSets avoid hij)
  exact hnew hijIso.symm

/-- Finite-family avoidance yields a natural-number-indexed pairwise non-isomorphic sequence of
minimal non-Ramsey-size-linear finite graphs. -/
theorem exists_pairwise_nonisomorphic_sequence_of_avoidance
    (avoid : FiniteFamilyAvoidance) :
    ∃ f : ℕ → GraphCode,
      (∀ n, MinimallyNonRamseySizeLinear (f n)) ∧
      Pairwise fun i j ↦ ¬ Isomorphic (f i) (f j) := by
  refine ⟨obstructionSequence avoid, obstructionSequence_minimal avoid, ?_⟩
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact obstructionSequence_not_isomorphic_of_lt avoid hij
  · intro h
    exact obstructionSequence_not_isomorphic_of_lt avoid hji h.symm

/-- The quantitative inputs imply a pairwise non-isomorphic sequence of minimal obstructions. -/
theorem exists_pairwise_nonisomorphic_sequence (inputs : InfinitudeInputs) :
    ∃ f : ℕ → GraphCode,
      (∀ n, MinimallyNonRamseySizeLinear (f n)) ∧
      Pairwise fun i j ↦ ¬ Isomorphic (f i) (f j) := by
  exact exists_pairwise_nonisomorphic_sequence_of_avoidance
    (fun s hs ↦ exists_minimal_avoiding_finset inputs s hs)

end E79P

/- ===== from ErdosProblems.Erdos79.Nonlinear ===== -/
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/




/-
# A first-moment obstruction to Ramsey size linearity

This file proves the elementary density criterion used in the formalization of Erdős
Problem 79.  If a finite graph has more than five times as many edges as vertices, then it
is not Ramsey size linear.  The proof is the finite first-moment argument with red edge
probability `1 / k`, ambient order `k ^ 5`, and blue target `K_(k ^ 2)`.
-/

open Finset MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal SimpleGraph

noncomputable section

namespace E79P
namespace Nonlinear

/-- The required host edges for a fixed injective labelling of a graph. -/
noncomputable def requiredEdges {a N : ℕ} (A : SimpleGraph (Fin a)) (f : Fin a ↪ Fin N) :
    Finset (Sym2 (Fin N)) := by
  classical
  exact A.edgeSet.toFinite.toFinset.map f.sym2Map

@[simp] theorem card_requiredEdges {a N : ℕ} (A : SimpleGraph (Fin a))
    (f : Fin a ↪ Fin N) :
    (requiredEdges A f).card = Nat.card A.edgeSet := by
  classical
  calc
    (requiredEdges A f).card = A.edgeSet.toFinite.toFinset.card := by
      simp [requiredEdges]
    _ = Fintype.card A.edgeSet := Set.Finite.card_toFinset A.edgeSet.toFinite
    _ = Nat.card A.edgeSet := by rw [Nat.card_eq_fintype_card]

theorem requiredEdges_subset_diagCompl {a N : ℕ} (A : SimpleGraph (Fin a))
    (f : Fin a ↪ Fin N) :
    (↑(requiredEdges A f) : Set (Sym2 (Fin N))) ⊆ Sym2.diagSetᶜ := by
  classical
  intro e he
  rcases Finset.mem_map.mp he with ⟨e', he', rfl⟩
  have heA : e' ∈ A.edgeSet := by
    exact A.edgeSet.toFinite.mem_toFinset.mp he'
  exact fun hdiag ↦
    A.not_isDiag_of_mem_edgeSet heA ((Sym2.isDiag_map f.injective).mp hdiag)

/-- Under the Bernoulli edge measure, all edges in a fixed finite set are red with the
expected product probability. -/
theorem setBernoulli_superset_finset {ι : Type*} [Finite ι]
    (u : Set ι) (p : I) (t : Finset ι) (ht : (↑t : Set ι) ⊆ u) :
    setBer(u, p) {s : Set ι | (↑t : Set ι) ⊆ s} = toNNReal p ^ t.card := by
  classical
  let := Fintype.ofFinite ι
  rw [setBernoulli_apply', Measure.infinitePi_eq_pi]
  have hpre :
      ((fun q : ι → Prop ↦ {i | q i}) ⁻¹' {s : Set ι | (↑t : Set ι) ⊆ s}) =
        ((↑t : Set ι).pi fun _ ↦ ({True} : Set Prop)) := by
    ext q
    simp [Set.subset_def]
  rw [hpre, Measure.pi_pi_finset, Finset.prod_eq_pow_card]
  intro i hi
  have hiu : i ∈ u := ht hi
  simp only [hiu, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply,
    Set.mem_singleton_iff, Set.indicator_of_mem, Pi.one_apply]
  rw [Set.indicator_of_notMem]
  · simp
  · simp

/-- Under the Bernoulli edge measure, all edges in a fixed finite set are blue with the
expected product probability. -/
theorem setBernoulli_disjoint_finset {ι : Type*} [Finite ι]
    (u : Set ι) (p : I) (t : Finset ι) (ht : (↑t : Set ι) ⊆ u) :
    setBer(u, p) {s : Set ι | Disjoint (↑t : Set ι) s} =
      toNNReal (σ p) ^ t.card := by
  classical
  let := Fintype.ofFinite ι
  rw [setBernoulli_apply', Measure.infinitePi_eq_pi]
  have hpre :
      ((fun q : ι → Prop ↦ {i | q i}) ⁻¹'
        {s : Set ι | Disjoint (↑t : Set ι) s}) =
        ((↑t : Set ι).pi fun _ ↦ ({False} : Set Prop)) := by
    ext q
    simp [Set.disjoint_left]
  rw [hpre, Measure.pi_pi_finset, Finset.prod_eq_pow_card]
  intro i hi
  have hiu : i ∈ u := ht hi
  simp only [hiu, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply,
    Set.mem_singleton_iff, Set.indicator_of_mem, Pi.one_apply]
  rw [Set.indicator_of_notMem]
  · simp
  · simp

/-- Red-copy bad event for one injective vertex labelling. -/
def redEvent {a N : ℕ} (A : SimpleGraph (Fin a)) (f : Fin a ↪ Fin N) :
    Set (Set (Sym2 (Fin N))) :=
  { ω | (↑(requiredEdges A f) : Set (Sym2 (Fin N))) ⊆ ω }

/-- Blue-copy bad event for one injective vertex labelling. -/
def blueEvent {a N : ℕ} (A : SimpleGraph (Fin a)) (f : Fin a ↪ Fin N) :
    Set (Set (Sym2 (Fin N))) :=
  { ω | Disjoint (↑(requiredEdges A f) : Set (Sym2 (Fin N))) ω }

theorem measure_redEvent {a N : ℕ} (A : SimpleGraph (Fin a)) (f : Fin a ↪ Fin N)
    (p : I) :
    setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p) (redEvent A f) =
      toNNReal p ^ Nat.card A.edgeSet := by
  rw [redEvent, setBernoulli_superset_finset _ _ _ (requiredEdges_subset_diagCompl A f),
    card_requiredEdges]

theorem measure_blueEvent {a N : ℕ} (A : SimpleGraph (Fin a)) (f : Fin a ↪ Fin N)
    (p : I) :
    setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p) (blueEvent A f) =
      toNNReal (σ p) ^ Nat.card A.edgeSet := by
  rw [blueEvent, setBernoulli_disjoint_finset _ _ _ (requiredEdges_subset_diagCompl A f),
    card_requiredEdges]

/-- The union of all injectively labelled red copies. -/
def badRed {a N : ℕ} (A : SimpleGraph (Fin a)) : Set (Set (Sym2 (Fin N))) :=
  ⋃ f : Fin a ↪ Fin N, redEvent A f

/-- The union of all injectively labelled blue copies. -/
def badBlue {a N : ℕ} (A : SimpleGraph (Fin a)) : Set (Set (Sym2 (Fin N))) :=
  ⋃ f : Fin a ↪ Fin N, blueEvent A f

theorem measure_badRed_le {a N : ℕ} (A : SimpleGraph (Fin a)) (p : I) :
    setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p) (badRed (N := N) A) ≤
      (N : ℝ≥0∞) ^ a * (toNNReal p : ℝ≥0∞) ^ Nat.card A.edgeSet := by
  classical
  let μ : Measure (Set (Sym2 (Fin N))) :=
    setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p)
  calc
    μ (badRed (N := N) A) ≤ ∑ f : Fin a ↪ Fin N, μ (redEvent A f) := by
      simpa [badRed] using measure_iUnion_fintype_le μ (fun f : Fin a ↪ Fin N ↦ redEvent A f)
    _ = (Fintype.card (Fin a ↪ Fin N) : ℝ≥0∞) *
        (toNNReal p : ℝ≥0∞) ^ Nat.card A.edgeSet := by
      simp [μ, measure_redEvent]
    _ ≤ (N : ℝ≥0∞) ^ a *
        (toNNReal p : ℝ≥0∞) ^ Nat.card A.edgeSet := by
      gcongr
      norm_cast
      calc
        Fintype.card (Fin a ↪ Fin N) ≤ Fintype.card (Fin a → Fin N) :=
          Fintype.card_le_of_injective (fun f ↦ f.toFun)
            (fun _ _ h ↦ DFunLike.coe_injective h)
        _ = N ^ a := by simp

theorem measure_badBlue_le {a N : ℕ} (A : SimpleGraph (Fin a)) (p : I) :
    setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p) (badBlue (N := N) A) ≤
      (N : ℝ≥0∞) ^ a * (toNNReal (σ p) : ℝ≥0∞) ^ Nat.card A.edgeSet := by
  classical
  let μ : Measure (Set (Sym2 (Fin N))) :=
    setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p)
  calc
    μ (badBlue (N := N) A) ≤ ∑ f : Fin a ↪ Fin N, μ (blueEvent A f) := by
      simpa [badBlue] using measure_iUnion_fintype_le μ (fun f : Fin a ↪ Fin N ↦ blueEvent A f)
    _ = (Fintype.card (Fin a ↪ Fin N) : ℝ≥0∞) *
        (toNNReal (σ p) : ℝ≥0∞) ^ Nat.card A.edgeSet := by
      simp [μ, measure_blueEvent]
    _ ≤ (N : ℝ≥0∞) ^ a *
        (toNNReal (σ p) : ℝ≥0∞) ^ Nat.card A.edgeSet := by
      gcongr
      norm_cast
      calc
        Fintype.card (Fin a ↪ Fin N) ≤ Fintype.card (Fin a → Fin N) :=
          Fintype.card_le_of_injective (fun f ↦ f.toFun)
            (fun _ _ h ↦ DFunLike.coe_injective h)
        _ = N ^ a := by simp

/-- Every actual red copy belongs to one of the labelled red-copy events. -/
theorem mem_badRed_of_isContained {a N : ℕ} (A : SimpleGraph (Fin a))
    (ω : Set (Sym2 (Fin N))) (h : A ⊑ SimpleGraph.fromEdgeSet ω) :
    ω ∈ badRed (N := N) A := by
  classical
  rcases h with ⟨c⟩
  refine Set.mem_iUnion.2 ⟨c.toEmbedding, ?_⟩
  intro e he
  rcases Finset.mem_map.mp he with ⟨e', heA, rfl⟩
  have heA' : e' ∈ A.edgeSet := by
    exact A.edgeSet.toFinite.mem_toFinset.mp heA
  have hmap : A.map c.toEmbedding ≤ SimpleGraph.fromEdgeSet ω := by
    rw [SimpleGraph.map_le_iff_le_comap]
    exact c.toHom.le_comap
  have he' : e'.map c.toEmbedding ∈ (SimpleGraph.fromEdgeSet ω).edgeSet :=
    SimpleGraph.edgeSet_mono hmap (by
      rw [SimpleGraph.edgeSet_map]
      exact ⟨e', heA', rfl⟩)
  rw [SimpleGraph.edgeSet_fromEdgeSet] at he'
  exact he'.1

/-- Every actual blue copy belongs to one of the labelled blue-copy events. -/
theorem mem_badBlue_of_isContained {a N : ℕ} (A : SimpleGraph (Fin a))
    (ω : Set (Sym2 (Fin N))) (h : A ⊑ (SimpleGraph.fromEdgeSet ω)ᶜ) :
    ω ∈ badBlue (N := N) A := by
  classical
  rcases h with ⟨c⟩
  refine Set.mem_iUnion.2 ⟨c.toEmbedding, ?_⟩
  change Disjoint (↑(requiredEdges A c.toEmbedding) : Set (Sym2 (Fin N))) ω
  rw [Set.disjoint_left]
  intro e he hω
  rcases Finset.mem_map.mp he with ⟨e', heA, rfl⟩
  have heA' : e' ∈ A.edgeSet := by
    exact A.edgeSet.toFinite.mem_toFinset.mp heA
  have hmap : A.map c.toEmbedding ≤ (SimpleGraph.fromEdgeSet ω)ᶜ := by
    rw [SimpleGraph.map_le_iff_le_comap]
    exact c.toHom.le_comap
  have heBlue : e'.map c.toEmbedding ∈ (SimpleGraph.fromEdgeSet ω)ᶜ.edgeSet :=
    SimpleGraph.edgeSet_mono hmap (by
      rw [SimpleGraph.edgeSet_map]
      exact ⟨e', heA', rfl⟩)
  have hndiag : ¬ (e'.map c.toEmbedding).IsDiag := by
    exact fun hdiag ↦
      A.not_isDiag_of_mem_edgeSet heA' ((Sym2.isDiag_map c.injective).mp hdiag)
  have heRed : e'.map c.toEmbedding ∈ (SimpleGraph.fromEdgeSet ω).edgeSet := by
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    exact ⟨hω, by simpa using hndiag⟩
  revert heBlue heRed
  refine Sym2.inductionOn (e'.map c.toEmbedding) ?_
  intro u v hblue hred
  have hnot : ¬ (SimpleGraph.fromEdgeSet ω).Adj u v := by
    simpa [SimpleGraph.mem_edgeSet] using hblue.2
  exact hnot (by simpa [SimpleGraph.mem_edgeSet] using hred)

theorem thirtyTwo_mul_le_two_pow {t : ℕ} (ht : 8 ≤ t) : 32 * t ≤ 2 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih =>
      rw [pow_succ]
      have hthirtyTwo : 32 ≤ 2 ^ t := (by omega : 32 ≤ 32 * t).trans ih
      omega

theorem natCard_edgeSet_top (n : ℕ) :
    Nat.card (⊤ : SimpleGraph (Fin n)).edgeSet = Nat.choose n 2 := by
  classical
  rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  simp

/-- Numerical core of the first-moment estimate.  Choosing `k` to be a sufficiently large
power of two lets us bound the blue-copy term by grouping the required edges into blocks of
`k`, avoiding any appeal to an unformalized asymptotic estimate. -/
theorem firstMoment_parameters (C a b : ℕ) (hab : 5 * a < b) :
    ∃ t d k s N r : ℕ, ∃ p : I,
      t = C + 8 ∧ d = 2 ^ (C + 7) ∧ k = 2 * d ∧ s = k ^ 2 ∧ N = k ^ 5 ∧
      r = d * (s - 1) ∧
      C * Nat.choose s 2 < N ∧ Nat.choose s 2 = k * r ∧
      (N : ℝ≥0∞) ^ a * (toNNReal p : ℝ≥0∞) ^ b ≤ 1 / 4 ∧
      (N : ℝ≥0∞) ^ s * (toNNReal (σ p) : ℝ≥0∞) ^ Nat.choose s 2 ≤ 1 / 4 := by
  let t : ℕ := C + 8
  let d : ℕ := 2 ^ (C + 7)
  let k : ℕ := 2 * d
  let s : ℕ := k ^ 2
  let N : ℕ := k ^ 5
  let r : ℕ := d * (s - 1)
  have ht : 8 ≤ t := by simp [t]
  have hkpow : k = 2 ^ t := by
    simp only [k, d, t]
    rw [show C + 8 = (C + 7) + 1 by omega, pow_succ]
    ring
  have h32 : 32 * t ≤ k := by simpa [hkpow] using thirtyTwo_mul_le_two_pow ht
  have h16 : 16 * t ≤ d := by
    dsimp [k] at h32
    omega
  have hkfour : 4 ≤ k := by
    have : 32 * 8 ≤ k := (Nat.mul_le_mul_left 32 ht).trans h32
    omega
  have hCk : C < k := by
    dsimp [t] at h32
    omega
  have hsfour : 4 ≤ s := by
    dsimp [s]
    nlinarith
  have hchoose : Nat.choose s 2 = k * r := by
    rw [Nat.choose_two_right]
    have hnum : s * (s - 1) = 2 * (k * r) := by
      calc
        s * (s - 1) = (k * k) * (s - 1) := by simp [s, pow_two]
        _ = 2 * (k * r) := by simp only [k, r]; ring
    rw [hnum]
    simp
  have hambient : C * Nat.choose s 2 < N := by
    calc
      C * Nat.choose s 2 ≤ C * s ^ 2 :=
        Nat.mul_le_mul_left C (Nat.choose_le_pow s 2)
      _ < k * s ^ 2 := Nat.mul_lt_mul_of_pos_right hCk (pow_pos (by omega) _)
      _ = N := by simp [N, s, pow_succ]; ring
  have hgap : 5 * t * s + 2 ≤ r := by
    have hten : 10 * t + 1 ≤ d := by omega
    have hmul := Nat.mul_le_mul_right s hten
    simp only [add_mul, one_mul] at hmul
    have hleft : 10 * t * s + 4 ≤ d * s := by omega
    have hright : d * s ≤ 2 * r := by
      have hs : s ≤ 2 * (s - 1) := by omega
      simpa [r, mul_assoc, mul_left_comm, mul_comm] using Nat.mul_le_mul_left d hs
    have : 2 * (5 * t * s + 2) ≤ 2 * r := by
      calc
        2 * (5 * t * s + 2) = 10 * t * s + 4 := by ring
        _ ≤ d * s := hleft
        _ ≤ 2 * r := hright
    omega
  let q : ℝ := 1 / (k : ℝ)
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := by
    dsimp [q]
    apply (one_div_le (by positivity) zero_lt_one).2
    norm_num
    exact_mod_cast (show 1 ≤ k by omega)
  let p : I := ⟨q, hq0, hq1⟩
  have hp_real : ((toNNReal p : NNReal) : ℝ) = q := by simp [p]
  have hp_blue_real : ((toNNReal (σ p) : NNReal) : ℝ) = 1 - q := by
    simp [p]
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hred_real : (N : ℝ) ^ a * q ^ b ≤ 1 / 4 := by
    have hba : 5 * a + 1 ≤ b := by omega
    have hpow : (k : ℝ) ^ (5 * a + 1) ≤ (k : ℝ) ^ b := by
      exact pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ k by omega)) hba
    have hratio :
        (N : ℝ) ^ a * q ^ b =
          ((k : ℝ) ^ (5 * a + 1) / (k : ℝ) ^ b) * (1 / (k : ℝ)) := by
      simp only [N, q, Nat.cast_pow, div_pow]
      field_simp
      rw [show 5 * a + 1 = 5 * a + 1 by rfl, pow_succ]
      ring
    rw [hratio]
    calc
      ((k : ℝ) ^ (5 * a + 1) / (k : ℝ) ^ b) * (1 / (k : ℝ))
          ≤ 1 * (1 / (k : ℝ)) := by
            gcongr
            exact (div_le_one (pow_pos hkreal b)).2 hpow
      _ ≤ 1 / 4 := by
        simpa using
          (one_div_le hkreal (by norm_num : (0 : ℝ) < 1 / 4)).2 (by
            norm_num
            exact_mod_cast hkfour)
  have hblue_block : (1 - q) ^ k ≤ (1 / 2 : ℝ) := by
    calc
      (1 - q) ^ k = (1 - (1 : ℝ) / k) ^ k := by rfl
      _ ≤ Real.exp (-1) := Real.one_sub_div_pow_le_exp_neg (by exact_mod_cast (show 1 ≤ k by omega))
      _ ≤ 1 / 2 := Real.exp_neg_one_lt_half.le
  have hblue_nonneg : 0 ≤ 1 - q := sub_nonneg.mpr hq1
  have hblue_pow : (1 - q) ^ Nat.choose s 2 ≤ (1 / 2 : ℝ) ^ r := by
    rw [hchoose, pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg hblue_nonneg k) hblue_block r
  have hNpow : (N : ℝ) ^ s = (2 : ℝ) ^ (5 * t * s) := by
    calc
      (N : ℝ) ^ s = ((k : ℝ) ^ 5) ^ s := by simp [N]
      _ = (k : ℝ) ^ (5 * s) := by rw [← pow_mul]
      _ = (((2 : ℝ) ^ t) ^ (5 * s)) := by rw [hkpow]; norm_cast
      _ = (2 : ℝ) ^ (t * (5 * s)) := by rw [← pow_mul]
      _ = (2 : ℝ) ^ (5 * t * s) := by
        congr 1
        ring
  have hpowers : (2 : ℝ) ^ (5 * t * s + 2) ≤ (2 : ℝ) ^ r := by
    exact pow_le_pow_right₀ (by norm_num) hgap
  have hblue_real : (N : ℝ) ^ s * (1 - q) ^ Nat.choose s 2 ≤ 1 / 4 := by
    calc
      (N : ℝ) ^ s * (1 - q) ^ Nat.choose s 2
          ≤ (N : ℝ) ^ s * (1 / 2 : ℝ) ^ r := by gcongr
      _ = (2 : ℝ) ^ (5 * t * s) / (2 : ℝ) ^ r := by rw [hNpow, div_pow]; ring
      _ ≤ 1 / 4 := by
        rw [div_le_iff₀ (pow_pos (by norm_num) r)]
        have hfour : 4 * (2 : ℝ) ^ (5 * t * s) ≤ (2 : ℝ) ^ r := by
          rw [pow_add] at hpowers
          norm_num at hpowers
          nlinarith
        nlinarith
  have hred_enn :
      (N : ℝ≥0∞) ^ a * (toNNReal p : ℝ≥0∞) ^ b ≤ 1 / 4 := by
    apply (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) (ENNReal.pow_ne_top (by simp)))
      (by simp)).mp
    simpa [ENNReal.toReal_mul, ENNReal.toReal_pow, hp_real] using hred_real
  have hblue_enn :
      (N : ℝ≥0∞) ^ s * (toNNReal (σ p) : ℝ≥0∞) ^ Nat.choose s 2 ≤ 1 / 4 := by
    apply (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) (ENNReal.pow_ne_top (by simp)))
      (by simp)).mp
    simpa [ENNReal.toReal_mul, ENNReal.toReal_pow, hp_blue_real] using hblue_real
  exact ⟨t, d, k, s, N, r, p, rfl, rfl, rfl, rfl, rfl, rfl,
    hambient, hchoose, hred_enn, hblue_enn⟩

/-- A graph with more than five edges per vertex is not Ramsey size linear.

The witness against a proposed constant `C` is the complete graph on `k ^ 2` vertices,
where `k` is a sufficiently large power of two.  A finite Bernoulli count on graphs with
`k ^ 5` vertices gives a colouring with neither a red copy of `G` nor a blue `K_(k^2)`.
-/
theorem not_ramseySizeLinear_of_five_mul_vertexCount_lt_edgeCount (G : GraphCode)
    (hG : 5 * G.vertexCount < G.edgeCount) : ¬ RamseySizeLinear G := by
  intro hlinear
  rcases hlinear with ⟨C, hC⟩
  obtain ⟨t, d, k, s, N, r, p, ht, hd, hk, hs, hN, hr, hambient, hchoose,
      hredBound, hblueBound⟩ :=
    firstMoment_parameters C G.vertexCount G.edgeCount hG
  let H : GraphCode := completeCode s
  have hsfour : 4 ≤ s := by
    have hdpos : 0 < d := by rw [hd]; positivity
    have hk2 : 2 ≤ k := by rw [hk]; omega
    rw [hs]
    nlinarith
  have hHNoIsolated : NoIsolated H := by
    have : Nontrivial (Fin s) := Fin.nontrivial_iff_two_le.mpr (by omega)
    change ∀ v : Fin s, ¬ (⊤ : SimpleGraph (Fin s)).IsIsolated v
    intro v
    apply ((⊤ : SimpleGraph (Fin s)).exists_adj_iff_not_isIsolated).mp
    obtain ⟨w, hw⟩ := exists_ne v
    exact ⟨w, by simpa using hw.symm⟩
  let μ : Measure (Set (Sym2 (Fin N))) :=
    setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p)
  have hredMeasure : μ (badRed (N := N) G.graph) ≤ 1 / 4 := by
    calc
      μ (badRed (N := N) G.graph) ≤
          (N : ℝ≥0∞) ^ G.vertexCount *
            (toNNReal p : ℝ≥0∞) ^ Nat.card G.graph.edgeSet := by
              simpa [μ] using measure_badRed_le (N := N) G.graph p
      _ ≤ 1 / 4 := by simpa [GraphCode.edgeCount] using hredBound
  have hblueMeasure : μ (badBlue (N := N) (⊤ : SimpleGraph (Fin s))) ≤ 1 / 4 := by
    calc
      μ (badBlue (N := N) (⊤ : SimpleGraph (Fin s))) ≤
          (N : ℝ≥0∞) ^ s *
            (toNNReal (σ p) : ℝ≥0∞) ^ Nat.card (⊤ : SimpleGraph (Fin s)).edgeSet := by
              simpa [μ] using measure_badBlue_le (N := N) (⊤ : SimpleGraph (Fin s)) p
      _ ≤ 1 / 4 := by
        rw [natCard_edgeSet_top]
        exact hblueBound
  have hbadMeasure :
      μ (badRed (N := N) G.graph ∪ badBlue (N := N) (⊤ : SimpleGraph (Fin s))) < 1 := by
    calc
      μ (badRed (N := N) G.graph ∪ badBlue (N := N) (⊤ : SimpleGraph (Fin s))) ≤
          μ (badRed (N := N) G.graph) +
            μ (badBlue (N := N) (⊤ : SimpleGraph (Fin s))) := measure_union_le _ _
      _ ≤ 1 / 4 + 1 / 4 := add_le_add hredMeasure hblueMeasure
      _ < 1 := by
        have htr :
            (((1 / 4 : ℝ≥0∞) + 1 / 4).toReal) < (1 : ℝ≥0∞).toReal := by
          norm_num [ENNReal.toReal_add]
        exact (ENNReal.toReal_lt_toReal (by simp) (by simp)).1 htr
  have hbadNeUniv :
      badRed (N := N) G.graph ∪ badBlue (N := N) (⊤ : SimpleGraph (Fin s)) ≠ Set.univ := by
    intro hall
    rw [hall] at hbadMeasure
    simp [μ] at hbadMeasure
  obtain ⟨ω, hω⟩ := (Set.ne_univ_iff_exists_notMem _).mp hbadNeUniv
  let X : SimpleGraph (Fin N) := SimpleGraph.fromEdgeSet ω
  have hredFree : ¬ G.graph ⊑ X := by
    intro hcopy
    apply hω
    exact Or.inl (mem_badRed_of_isContained G.graph ω hcopy)
  have hblueFree : ¬ (⊤ : SimpleGraph (Fin s)) ⊑ Xᶜ := by
    intro hcopy
    apply hω
    exact Or.inr (mem_badBlue_of_isContained (⊤ : SimpleGraph (Fin s)) ω hcopy)
  have hnotRamsey : ¬ RamseyAt G H N := by
    intro hramsey
    rcases hramsey X with hred | hblue
    · exact hredFree hred
    · exact hblueFree (by simpa [H, completeCode] using hblue)
  apply hnotRamsey
  have hHedges : H.edgeCount = Nat.choose s 2 := by
    change Nat.card (⊤ : SimpleGraph (Fin s)).edgeSet = Nat.choose s 2
    exact natCard_edgeSet_top s
  have hramsey := hC H hHNoIsolated
  rw [hHedges] at hramsey
  exact hramsey.mono_vertices hambient.le

end Nonlinear

/-- Namespace-level form of the elementary first-moment obstruction. -/
theorem not_ramseySizeLinear_of_five_mul_vertexCount_lt_edgeCount (G : GraphCode)
    (hG : 5 * G.vertexCount < G.edgeCount) : ¬ RamseySizeLinear G :=
  Nonlinear.not_ramseySizeLinear_of_five_mul_vertexCount_lt_edgeCount G hG

end E79P

/- ===== from ErdosProblems.Erdos79 ===== -/
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 79.
https://www.erdosproblems.com/forum/thread/79

Informal authors:
- Yufei Wigderson

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/E79P.md
-/




/-
# Erdős Problem 79

This file formalizes Wigderson's resolution of Erdős Problem 79: there are infinitely many,
up to isomorphism, finite graphs which are not Ramsey size linear although every proper
ordinary subgraph is Ramsey size linear.

The two quantitative ingredients used here are proved in the imported modules.  Every finite
forest is Ramsey size linear.  On the other hand, a finite first-moment argument shows that a
graph with more than five edges per vertex is not Ramsey size linear, and a second finite
first-moment argument followed by deletion produces such graphs with arbitrarily large girth.
-/

open scoped SimpleGraph

noncomputable section

namespace E79P
/-- The closed pair of inputs used by the representation-independent infinitude assembly. -/
theorem infinitudeInputs : InfinitudeInputs :=
  infinitudeInputs_of_dense_highGirth
    ramseySizeLinear_of_isAcyclic
    not_ramseySizeLinear_of_five_mul_vertexCount_lt_edgeCount
    exists_dense_highGirth

/-- **Resolution of Erdős Problem 79.**

There is a natural-number-indexed sequence of pairwise non-isomorphic finite graphs, every one
of which is not Ramsey size linear while each of its proper ordinary subgraphs is Ramsey size
linear.  `GraphCode` represents a finite graph on `Fin n`; `Isomorphic` is ordinary graph
isomorphism, so pairwise non-isomorphism states infinitude of isomorphism classes rather than
mere infinitude of labelled presentations. -/
theorem erdos_79 :
    ∃ f : ℕ → GraphCode,
      (∀ n, MinimallyNonRamseySizeLinear (f n)) ∧
      Pairwise fun i j ↦ ¬ Isomorphic (f i) (f j) :=
  exists_pairwise_nonisomorphic_sequence infinitudeInputs



end E79P

/- ===== New material: bridge to the formal-conjectures statement ===== -/

namespace OMA79

/-- The Ramsey number of formal-conjectures agrees with the ported least Ramsey order. -/
theorem graphRamsey_eq {α : Type*} {inst : Fintype α} {n m : ℕ} (G : SimpleGraph α)
    (G' : SimpleGraph (Fin n)) (e : G ≃g G') (H : SimpleGraph (Fin m)) :
    SimpleGraph.graphRamsey G H = E79P.graphRamseyNumber ⟨n, G'⟩ ⟨m, H⟩ := by
  have hset : {N : ℕ | ∀ C : SimpleGraph (Fin N), G.IsContained C ∨ H.IsContained Cᶜ}
      = {N | E79P.RamseyAt ⟨n, G'⟩ ⟨m, H⟩ N} := by
    ext N
    simp only [Set.mem_ofPred_eq, E79P.RamseyAt]
    refine forall_congr' fun C => or_congr ?_ Iff.rfl
    exact ⟨fun h => (e.symm.isContained).trans h, fun h => (e.isContained).trans h⟩
  unfold SimpleGraph.graphRamsey
  rw [hset]
  have hmem : E79P.graphRamseyNumber ⟨n, G'⟩ ⟨m, H⟩ ∈
      {N | E79P.RamseyAt ⟨n, G'⟩ ⟨m, H⟩ N} := E79P.graphRamseyNumber_spec _ _
  apply le_antisymm
  · exact Nat.sInf_le hmem
  · apply E79P.graphRamseyNumber_le_of_ramseyAt
    exact Nat.sInf_mem ⟨_, hmem⟩

theorem edgeCount_cast {m : ℕ} (H : SimpleGraph (Fin m)) :
    (H.edgeSet.ncard : ℝ) = (E79P.GraphCode.edgeCount ⟨m, H⟩ : ℝ) := by
  rw [E79P.GraphCode.edgeCount_mk, Nat.card_coe_set_eq]

/-- Ramsey size linearity in the sense of formal-conjectures agrees with the ported notion. -/
theorem linear_iff {α : Type*} {inst : Fintype α} {n : ℕ} (G : SimpleGraph α)
    (G' : SimpleGraph (Fin n)) (e : G ≃g G') :
    G.IsRamseySizeLinear ↔ E79P.RamseySizeLinear ⟨n, G'⟩ := by
  rw [E79P.RamseySizeLinear.iff_graphRamseyNumber_le]
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨⌈c⌉₊, ?_⟩
    rintro ⟨m, H⟩ hH
    classical
    have h1 := h m H (fun v => (H.degree_pos v).mpr (hH v))
    rw [graphRamsey_eq G G' e H, edgeCount_cast] at h1
    have h3 : (c : ℝ) ≤ ⌈c⌉₊ := Nat.le_ceil c
    have h4 : ((E79P.graphRamseyNumber ⟨n, G'⟩ ⟨m, H⟩ : ℕ) : ℝ) ≤
        ((⌈c⌉₊ * E79P.GraphCode.edgeCount ⟨m, H⟩ : ℕ) : ℝ) := by
      push_cast
      exact h1.trans (mul_le_mul_of_nonneg_right h3 (Nat.cast_nonneg _))
    exact_mod_cast h4
  · rintro ⟨C, h⟩
    refine ⟨(C : ℝ) + 1, by positivity, ?_⟩
    intro m H inst' hdeg
    have hH : E79P.NoIsolated ⟨m, H⟩ := fun v => (H.degree_pos v).mp (hdeg v)
    have h1 := h ⟨m, H⟩ hH
    rw [graphRamsey_eq G G' e H, edgeCount_cast]
    have h4 : ((E79P.graphRamseyNumber ⟨n, G'⟩ ⟨m, H⟩ : ℕ) : ℝ) ≤
        ((C * E79P.GraphCode.edgeCount ⟨m, H⟩ : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h4
    nlinarith [Nat.cast_nonneg (α := ℝ) (E79P.GraphCode.edgeCount ⟨m, H⟩)]

/-- A proper subgraph is not isomorphic to the whole graph. -/
theorem not_iso_of_lt_top {n : ℕ} (G : SimpleGraph (Fin n)) (H : G.Subgraph) (hH : H < ⊤)
    (e : H.coe ≃g G) : False := by
  have hsurjV : Function.Surjective (Subtype.val : H.verts → Fin n) :=
    (Finite.injective_iff_surjective_of_equiv e.toEquiv).mp Subtype.val_injective
  have hverts : H.verts = Set.univ := by
    apply Set.eq_univ_iff_forall.2
    intro x
    obtain ⟨⟨y, hy⟩, rfl⟩ := hsurjV x
    exact hy
  have hsurjE : Function.Surjective (SimpleGraph.Hom.mapEdgeSet H.hom) :=
    (Finite.injective_iff_surjective_of_equiv e.mapEdgeSet).mp
      (SimpleGraph.Hom.mapEdgeSet.injective H.hom H.hom_injective)
  have hadj : ∀ u v, G.Adj u v → H.Adj u v := by
    intro u v huv
    obtain ⟨⟨x, hx⟩, hxe⟩ := hsurjE ⟨s(u, v), huv⟩
    revert hx hxe
    refine Sym2.ind (fun a b => ?_) x
    intro hx hxe
    have hab : H.Adj a.1 b.1 := by simpa using hx
    have h2 : s(a.1, b.1) = s(u, v) := by
      simpa [SimpleGraph.Hom.mapEdgeSet] using congrArg Subtype.val hxe
    rcases Sym2.eq_iff.mp h2 with ⟨h1, h3⟩ | ⟨h1, h3⟩
    · rw [← h1, ← h3]; exact hab
    · rw [← h1, ← h3]; exact hab.symm
  have htop : H = ⊤ := by
    apply SimpleGraph.Subgraph.ext
    · simpa using hverts
    · funext u v
      exact propext ⟨fun h => h.adj_sub, hadj u v⟩
  exact hH.ne htop

/-- A pairwise non-isomorphic sequence of coded graphs has members of arbitrarily large order. -/
theorem exists_large (f : ℕ → E79P.GraphCode)
    (hf : Pairwise fun i j => ¬ E79P.Isomorphic (f i) (f j)) (N : ℕ) : ∃ i, N ≤ (f i).1 := by
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  let g : ℕ → Σ k : Fin N, SimpleGraph (Fin k) := fun i => ⟨⟨(f i).1, hcon i⟩, (f i).2⟩
  have hg : Function.Injective g := by
    intro i j hij
    by_contra hne
    apply hf hne
    have h1 : f i = f j := by
      have := congrArg (fun x : Σ k : Fin N, SimpleGraph (Fin k) =>
        (⟨x.1.1, x.2⟩ : E79P.GraphCode)) hij
      simpa [g] using this
    rw [h1]
    exact E79P.Isomorphic.refl _
  exact not_injective_infinite_finite g hg

end OMA79

theorem OMA.solution : type_of% @Erdos79.erdos_79 := by
  intro N
  obtain ⟨f, hmin, hpair⟩ := E79P.erdos_79
  obtain ⟨i, hi⟩ := OMA79.exists_large f hpair N
  refine ⟨(f i).1, hi, (f i).2, ?_, ?_⟩
  · intro hlin
    exact (hmin i).1 ((OMA79.linear_iff (f i).2 (f i).2 SimpleGraph.Iso.refl).mp hlin)
  · intro H hH
    have hc : Nat.card H.verts = Nat.card H.verts := rfl
    obtain ⟨k, G', ⟨e⟩⟩ : ∃ (k : ℕ) (G' : SimpleGraph (Fin k)), Nonempty (H.coe ≃g G') := by
      classical
      exact ⟨Fintype.card H.verts, H.coe.overFin rfl, ⟨SimpleGraph.overFinIso (G := H.coe) rfl⟩⟩
    refine (OMA79.linear_iff H.coe G' e).mpr ?_
    apply (hmin i).2 ⟨k, G'⟩
    refine ⟨?_, ?_⟩
    · exact (e.symm.isContained).trans ⟨⟨H.hom, H.hom_injective⟩⟩
    · rintro ⟨e'⟩
      exact OMA79.not_iso_of_lt_top (f i).2 H hH (e'.comp e)
