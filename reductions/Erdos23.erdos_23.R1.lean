import FormalConjectures.ErdosProblems.«23»
import Mathlib

/-!
Reduction of Erdős Problem 23 to two independent partition statements.

`H1` is the dense maximal case: a maximal triangle-free graph on `5n` vertices
with at least `2*n^2` edges has a vertex partition with at most `n^2`
same-side edges.  `H2` is the elementary max-cut bound, valid for every finite
graph.  The proof below handles the sparse case with `H2`, extends any dense
triangle-free graph to a maximal one with Mathlib's finite maximal principle,
applies `H1`, and restricts the partition back.  Turning a partition into the
required bipartite subgraph is also proved here.  Neither hypothesis is the
full theorem: one is restricted to maximal graphs and the dense range, the
other asks only for a half-cut of an arbitrary graph.
-/

namespace OMA.R_Erdos23_erdos_23_R1

open SimpleGraph Finset
open scoped Classical

/-- Dense maximal case: a maximal triangle-free graph on 5n vertices with at
least 2*n^2 edges has a vertex partition with at most n^2 same-side edges. -/
def H1 : Prop :=
  ∀ (n : ℕ) (V : Type) [Fintype V], Fintype.card V = 5 * n →
    ∀ (K : SimpleGraph V), K.CliqueFree 3 →
      (∀ L : SimpleGraph V, K ≤ L → L.CliqueFree 3 → L = K) →
      2 * n ^ 2 ≤ K.edgeFinset.card →
      ∃ S : Finset V,
        (K.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card ≤ n ^ 2

/-- Elementary max-cut bound: every finite graph has a vertex partition with
at most half of its edges on one side. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    ∃ S : Finset V,
      (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card ≤
        G.edgeFinset.card / 2

section
variable {V : Type*} [Fintype V] [DecidableEq V]

-- Both ends of an edge lie on the same side of `S` iff its two endpoints do.
omit [Fintype V] in
lemma same_mk (S : Finset V) (u v : V) :
    (∀ x ∈ s(u, v), ∀ y ∈ s(u, v), (x ∈ S ↔ y ∈ S)) ↔ (u ∈ S ↔ v ∈ S) := by
  simp only [Sym2.mem_iff]
  constructor
  · intro h
    exact h u (Or.inl rfl) v (Or.inr rfl)
  · rintro h x (rfl | rfl) y (rfl | rfl) <;> tauto

-- Deleting the same-side edges of a partition leaves a bipartite subgraph.
lemma cut_graph (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.IsBipartite ∧
      (G.edgeFinset \ H.edgeFinset).card =
        (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card := by
  let H : SimpleGraph V :=
    { Adj := fun u v => G.Adj u v ∧ ¬ (u ∈ S ↔ v ∈ S)
      symm := ⟨fun u v h => ⟨h.1.symm, fun h' => h.2 h'.symm⟩⟩
      loopless := ⟨fun u h => h.2 Iff.rfl⟩ }
  have hH : ∀ u v, H.Adj u v ↔ (G.Adj u v ∧ ¬ (u ∈ S ↔ v ∈ S)) := fun _ _ => Iff.rfl
  refine ⟨H, fun u v h => ((hH u v).1 h).1, ?_, ?_⟩
  · refine ⟨Coloring.mk (fun v => if v ∈ S then (0 : Fin 2) else 1) ?_⟩
    intro u v h
    have h2 := ((hH u v).1 h).2
    clear h hH
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp_all
  · congr 1
    ext e
    induction e using Sym2.ind with
    | h x y =>
      simp only [Finset.mem_sdiff, mem_edgeFinset, mem_edgeSet, Finset.mem_filter, same_mk, hH]
      tauto

end

theorem main : H1 → H2 → type_of% @Erdos23.erdos_23 := by
  intro h1 h2 n V instV hcard G hG
  classical
  by_cases hd : G.edgeFinset.card ≤ 2 * n ^ 2
  · obtain ⟨S, hS⟩ := h2 V G
    obtain ⟨H, hle, hbip, hdiff⟩ := cut_graph G S
    refine ⟨H, hle, hbip, ?_⟩
    rw [hdiff]
    exact hS.trans (Nat.div_le_of_le_mul hd)
  · obtain ⟨K, hGK, hKmax⟩ :=
      Finite.exists_le_maximal (p := fun L : SimpleGraph V => L.CliqueFree 3) hG
    have hKcf : K.CliqueFree 3 := hKmax.1
    have hmax : ∀ L : SimpleGraph V, K ≤ L → L.CliqueFree 3 → L = K :=
      fun L hKL hLcf => le_antisymm (hKmax.2 hLcf hKL) hKL
    have hKdense : 2 * n ^ 2 ≤ K.edgeFinset.card := by
      exact (by omega : 2 * n ^ 2 ≤ G.edgeFinset.card).trans
        (Finset.card_le_card (edgeFinset_mono hGK))
    obtain ⟨S, hS⟩ := h1 n V hcard K hKcf hmax hKdense
    obtain ⟨H, hle, hbip, hdiff⟩ := cut_graph G S
    refine ⟨H, hle, hbip, ?_⟩
    rw [hdiff]
    exact (Finset.card_le_card (Finset.filter_subset_filter _ (edgeFinset_mono hGK))).trans hS

end OMA.R_Erdos23_erdos_23_R1
