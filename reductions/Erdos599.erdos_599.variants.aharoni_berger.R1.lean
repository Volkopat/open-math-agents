import FormalConjectures.ErdosProblems.«599»
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Tactic

/-!
# Reduction of `Erdos599.erdos_599.variants.aharoni_berger`

Following R. Aharoni and E. Berger (*Menger's theorem for infinite graphs*, Invent. Math. 176
(2009), 1–62; see also R. Diestel, *Graph Theory*, 5th ed., §8.4, Lemma 8.4.3 and Theorem 8.4.6),
we reduce Menger's theorem for arbitrary (possibly infinite) graphs to its two canonical pillars
in the theory of waves and loose/wave-free webs:
1. `H1`: **Existence of a maximal wave** (Aharoni–Berger Lemma 3.5 / Diestel Lemma 8.4.3):
   in every graph `(G, A, B)` on `V : Type`, there exists a wave — a family `(p i : G.Walk (a i) (x i))`
   of pairwise vertex-disjoint paths from `A` to a terminal set `X = Set.range x` separating `A`
   from `B` — such that the after-wave induced subgraph `G' = G.induce V'` on
   `V' = {v | v ∈ X ∨ ∀ i, v ∉ (p i).support}` is **wave-free** between `X' = {v : V' | v.1 ∈ X}`
   and `B' = {v : V' | v.1 ∈ B}` (every wave in `(G', X', B')` has terminal set equal to `X'`).
2. `H2`: **Linkability of wave-free webs** (Aharoni–Berger Main Theorem / Diestel Theorem 8.4.6):
   every wave-free web `(G', X', B')` admits a linkage covering all of `X'`, i.e., a family of
   pairwise vertex-disjoint paths `(q x : G'.Walk x (b' x))` indexed by `x : X'` with `b' x ∈ B'`.

Inside `main`, we prove from scratch:
- Lifting each linkage path `q (x i)` from `G.induce V'` back to `G` via `SimpleGraph.Embedding.induce`,
  preserving `IsPath` and vertex support.
- Vertex-disjointness of `(p i).support` from `(q_lift i).support.tail` (using `V'` and pairwise
  disjointness of `p`), yielding `((p i).append (q_lift i)).IsPath` via `Walk.support_append` and
  `List.nodup_append`.
- Pairwise vertex-disjointness of the concatenated `A`–`B` paths `r i = (p i).append (q_lift i)`.
- Exact one-vertex-per-path orthogonality for the separator `S := Set.range x`: `S` lies in the
  union of the supports of `r`, meets each `r i` in the unique vertex `x i`, and separates `A` from
  `B` in `G`.

Thanks to @MechaNuggan for the infinite-graph walk induction and Aharoni–Berger wave/loose-web
analysis.
Credit: @tkaiman
-/

namespace OMA.R_Erdos599_erdos_599_variants_aharoni_berger_R1

open SimpleGraph

private lemma mem_support_map_induce {V : Type} {G : SimpleGraph V} {s : Set V}
    {u v : s} (q : (G.induce s).Walk u v) (w : V) :
    w ∈ (q.map (SimpleGraph.Embedding.induce s).toHom).support ↔
      ∃ z : s, z.1 = w ∧ z ∈ q.support := by
  rw [Walk.support_map, List.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, rfl, hz⟩
  · rintro ⟨z, rfl, hz⟩
    exact ⟨z, hz, rfl⟩

private lemma isPath_append_of_disjoint_tail {V : Type} {G : SimpleGraph V}
    {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (hp : p.IsPath) (hq : q.IsPath)
    (hdisj : ∀ z, z ∈ p.support → z ∈ q.support.tail → False) :
    (p.append q).IsPath := by
  rw [Walk.isPath_def, Walk.support_append, List.nodup_append]
  refine ⟨hp.support_nodup, ?_, ?_⟩
  · have hnodup : (v :: q.support.tail).Nodup := by
      rw [Walk.cons_tail_support q]
      exact hq.support_nodup
    exact (List.nodup_cons.mp hnodup).2
  · intro x hx y hy hxy
    subst hxy
    exact hdisj x hx hy

private lemma mem_support_append_iff_local {V : Type} {G : SimpleGraph V}
    {u v w : V} {p : G.Walk u v} {q : G.Walk v w} {z : V} :
    z ∈ (p.append q).support ↔ z ∈ p.support ∨ z ∈ q.support := by
  rw [Walk.support_append, List.mem_append]
  constructor
  · rintro (hp | hq)
    · exact Or.inl hp
    · exact Or.inr (List.mem_of_mem_tail hq)
  · rintro (hp | hq)
    · exact Or.inl hp
    · rw [← Walk.cons_tail_support q, List.mem_cons] at hq
      rcases hq with rfl | hqt
      · exact Or.inl (Walk.end_mem_support p)
      · exact Or.inr hqt

/-- **Existence of a maximal wave** (Aharoni–Berger 2009 / Diestel Lemma 8.4.3):
for every graph `G` on `V` and arbitrary vertex sets `A, B ⊆ V`, there exists a wave
`(ι, a, x, p)` of pairwise vertex-disjoint paths `p i : G.Walk (a i) (x i)` from `A` to
`X = Set.range x` separating `A` from `B`, such that the after-wave induced subgraph
`G' = G.induce V'` on `V' = {v | v ∈ X ∨ ∀ i, v ∉ (p i).support}` is wave-free between
`X' = {v : V' | v.1 ∈ X}` and `B' = {v : V' | v.1 ∈ B}` (every wave in `(G', X', B')` has
terminal set equal to `X'`). -/
def H1 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) (A B : Set V),
    ∃ (ι : Type) (a x : ι → V) (p : ∀ i, G.Walk (a i) (x i)),
      (∀ i, a i ∈ A) ∧ (∀ i, (p i).IsPath) ∧
      (Pairwise fun i j => Disjoint {v | v ∈ (p i).support} {v | v ∈ (p j).support}) ∧
      (∀ a' ∈ A, ∀ b' ∈ B, ∀ q : G.Walk a' b', q.IsPath → ∃ v ∈ q.support, v ∈ Set.range x) ∧
      let V' : Set V := {v | v ∈ Set.range x ∨ ∀ i, v ∉ (p i).support}
      let G' : SimpleGraph V' := G.induce V'
      let X' : Set V' := {v : V' | v.1 ∈ Set.range x}
      let B' : Set V' := {v : V' | v.1 ∈ B}
      ∀ (κ : Type) (s t : κ → V') (r : ∀ k, G'.Walk (s k) (t k)),
        (∀ k, s k ∈ X') → (∀ k, (r k).IsPath) →
        (Pairwise fun k₁ k₂ => Disjoint {v | v ∈ (r k₁).support} {v | v ∈ (r k₂).support}) →
        (∀ x' ∈ X', ∀ b' ∈ B', ∀ q : G'.Walk x' b', q.IsPath →
          ∃ v ∈ q.support, v ∈ Set.range t) →
        Set.range t = X'

/-- **Linkability of wave-free webs** (Aharoni–Berger 2009 Main Theorem / Diestel Theorem 8.4.6):
for every graph `G'` on `V'` and vertex sets `X', B' ⊆ V'`, if every wave in `(G', X', B')` has
terminal set equal to `X'`, then `X'` is linkable to `B'` in `G'`: there exists a family of
pairwise vertex-disjoint paths `(q x : G'.Walk x.1 (b' x))` starting at every `x : X'` and
ending in `B'`. -/
def H2 : Prop :=
  ∀ (V' : Type) (G' : SimpleGraph V') (X' B' : Set V'),
    (∀ (κ : Type) (s t : κ → V') (r : ∀ k, G'.Walk (s k) (t k)),
      (∀ k, s k ∈ X') → (∀ k, (r k).IsPath) →
      (Pairwise fun k₁ k₂ => Disjoint {v | v ∈ (r k₁).support} {v | v ∈ (r k₂).support}) →
      (∀ x' ∈ X', ∀ b' ∈ B', ∀ q : G'.Walk x' b', q.IsPath →
        ∃ v ∈ q.support, v ∈ Set.range t) →
      Set.range t = X') →
    ∃ (b' : X' → V') (q : ∀ x : X', G'.Walk x.1 (b' x)),
      (∀ x : X', b' x ∈ B') ∧ (∀ x : X', (q x).IsPath) ∧
      (Pairwise fun x₁ x₂ : X' => Disjoint {v | v ∈ (q x₁).support} {v | v ∈ (q x₂).support})

theorem main : H1 → H2 → type_of% @Erdos599.erdos_599.variants.aharoni_berger := by
  intro h1 h2 V G A B
  obtain ⟨ι, a, x, p, haA, hp_path, hp_disj, hsep, hwavefree⟩ := h1 V G A B
  let V' : Set V := {v | v ∈ Set.range x ∨ ∀ i, v ∉ (p i).support}
  let G' : SimpleGraph V' := G.induce V'
  let X' : Set V' := {v : V' | v.1 ∈ Set.range x}
  let B' : Set V' := {v : V' | v.1 ∈ B}
  obtain ⟨b', q, hb'B, hq_path, hq_disj⟩ := h2 V' G' X' B' hwavefree
  -- Embed each terminal vertex `x i` into `X'`
  let xi' : ι → X' := fun i => ⟨⟨x i, Or.inl ⟨i, rfl⟩⟩, ⟨i, rfl⟩⟩
  have hxi_inj : Function.Injective xi' := by
    intro i j hij
    have hval : x i = x j := congrArg (fun z : X' => z.1.1) hij
    by_contra hne
    have hdis := Set.disjoint_left.mp (hp_disj hne)
    have hi : x i ∈ (p i).support := Walk.end_mem_support (p i)
    have hj : x i ∈ (p j).support := by rw [hval]; exact Walk.end_mem_support (p j)
    exact hdis hi hj
  -- Lift each linkage path `q (xi' i)` from `G'` back to `G`
  let emb : G' ↪g G := SimpleGraph.Embedding.induce V'
  let qG : ∀ i : ι, G.Walk (x i) (b' (xi' i)).1 := fun i => (q (xi' i)).map emb.toHom
  have hqG_path : ∀ i : ι, (qG i).IsPath := fun i => by
    have hsup : (qG i).support = (q (xi' i)).support.map emb.toHom :=
      Walk.support_map emb.toHom (q (xi' i))
    rw [Walk.isPath_def, hsup]
    exact (hq_path (xi' i)).support_nodup.map emb.injective
  -- Any vertex shared by `p i` and `qG j` must equal `x i` (hence `i = j` too)
  have hp_qG_inter : ∀ i j : ι, ∀ v : V,
      v ∈ (p i).support → v ∈ (qG j).support → v = x i ∧ i = j := by
    intro i j v hvp hvq
    obtain ⟨z, rfl, hzq⟩ := (mem_support_map_induce (q (xi' j)) v).mp hvq
    rcases z.2 with ⟨k, hk⟩ | hout
    · have hki : k = i := by
        by_contra hne
        have hdis := Set.disjoint_left.mp (hp_disj hne)
        exact hdis (hk ▸ Walk.end_mem_support (p k)) hvp
      subst hki
      have hkj : k = j := by
        by_contra hne
        have hdis := Set.disjoint_left.mp (hq_disj (fun heq => hne (hxi_inj heq)))
        have hz_eq : z = (xi' k).1 := Subtype.ext hk.symm
        have hstart : z ∈ (q (xi' k)).support := hz_eq ▸ Walk.start_mem_support (q (xi' k))
        exact hdis hstart hzq
      exact ⟨hk.symm, hkj⟩
    · exact absurd hvp (hout i)
  -- Concatenate `p i` and `qG i`
  let r : ∀ i : ι, G.Walk (a i) (b' (xi' i)).1 := fun i => (p i).append (qG i)
  refine ⟨ι, a, fun i => (b' (xi' i)).1, r, Set.range x, haA, fun i => hb'B (xi' i), ?_, ?_, ?_, ?_, hsep⟩
  · -- Each concatenated walk `r i` is a path
    intro i
    refine isPath_append_of_disjoint_tail (hp_path i) (hqG_path i) ?_
    intro z hzp hzqt
    have hzq : z ∈ (qG i).support := List.mem_of_mem_tail hzqt
    have hzx : z = x i := (hp_qG_inter i i z hzp hzq).1
    have hnodup : (x i :: (qG i).support.tail).Nodup := by
      rw [Walk.cons_tail_support (qG i)]
      exact (hqG_path i).support_nodup
    exact (List.nodup_cons.mp hnodup).1 (hzx ▸ hzqt)
  · -- The concatenated paths `r i` are pairwise vertex-disjoint
    intro i j hij
    rw [Set.disjoint_left]
    intro v hvi hvj
    have hvi' : v ∈ (p i).support ∨ v ∈ (qG i).support :=
      mem_support_append_iff_local.mp hvi
    have hvj' : v ∈ (p j).support ∨ v ∈ (qG j).support :=
      mem_support_append_iff_local.mp hvj
    rcases hvi' with hpi | hqi <;> rcases hvj' with hpj | hqj
    · exact Set.disjoint_left.mp (hp_disj hij) hpi hpj
    · exact hij (hp_qG_inter i j v hpi hqj).2
    · exact hij.symm (hp_qG_inter j i v hpj hqi).2
    · obtain ⟨z₁, rfl, hz₁⟩ := (mem_support_map_induce (q (xi' i)) v).mp hqi
      obtain ⟨z₂, hz₂_eq, hz₂⟩ := (mem_support_map_induce (q (xi' j)) z₁.1).mp hqj
      have hz_eq : z₁ = z₂ := Subtype.ext hz₂_eq.symm
      exact Set.disjoint_left.mp (hq_disj (fun heq => hij (hxi_inj heq))) hz₁ (hz_eq ▸ hz₂)
  · -- `S = Set.range x ⊆ ⋃ i, (r i).support`
    rintro v ⟨i, rfl⟩
    exact ⟨i, mem_support_append_iff_local.mpr (Or.inl (Walk.end_mem_support (p i)))⟩
  · -- Each `r i` meets `S = Set.range x` in the unique vertex `x i`
    intro i
    refine ⟨x i, ⟨⟨i, rfl⟩, mem_support_append_iff_local.mpr (Or.inl (Walk.end_mem_support (p i)))⟩, ?_⟩
    rintro v ⟨⟨j, rfl⟩, hvr⟩
    rcases mem_support_append_iff_local.mp hvr with hpi | hqi
    · have hji : j = i := by
        by_contra hne
        exact Set.disjoint_left.mp (hp_disj hne) (Walk.end_mem_support (p j)) hpi
      rw [hji]
    · have hji : j = i := (hp_qG_inter j i (x j) (Walk.end_mem_support (p j)) hqi).2
      rw [hji]

end OMA.R_Erdos599_erdos_599_variants_aharoni_berger_R1
