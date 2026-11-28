import FormalConjectures.WrittenOnTheWallII.GraphConjecture40

/-!
# Second reduction of Written on the Wall II - Conjecture 40

Sharpens the reduction `R1` (2-connected bipartite / 2-connected non-bipartite residual classes,
both above the scattering bound) by the deletion conditions satisfied by a counterexample that is
minimal in (number of vertices, number of edges):

- vertex condition (A): deleting any vertex does not change the largest induced forest size;
- vertex condition (B): deleting any vertex strictly decreases `p + b` (in the bipartite class
  this reads: deleting a vertex never increases the path cover number);
- vertex condition (C): every vertex-deleted subgraph satisfies the conjectured inequality
  against the forest number of the whole graph (so the graph misses the bound by at most one);
- edge criticality (E): deleting any edge strictly increases the largest induced forest size
  (2-connected graphs on at least three vertices have no bridge, which is proved here);
- strict slack minimality (D): every connected induced subgraph on at least two and fewer than
  all vertices has strictly larger slack `2 f - p - b` than the graph itself.

The first lemma section below reproduces the lemmas of the merged reduction `R1`, because a
reduction of the problem itself may only import the problem module.
-/

namespace OMA.R_WrittenOnTheWallII_GraphConjecture40_conjecture40_R2

open SimpleGraph

/-- 2-connected bipartite graphs above the scattering bound such that: no vertex deletion changes
the forest number; every vertex-deleted subgraph satisfies the conjectured inequality against the
forest number of the whole graph; no vertex deletion increases the path cover number; every
edge deletion increases the forest number; and every connected proper induced subgraph on at
least two vertices has strictly larger slack `2 f - p - b`. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    4 ≤ Fintype.card V →
    G.Connected →
    (∀ v : V, (G.induce ({v}ᶜ : Set V)).Connected) →
    G.IsBipartite →
    (∀ S : Finset V,
      Nat.card (G.induce (S : Set V)ᶜ).ConnectedComponent < G.pathCoverNumber + S.card) →
    (∀ v : V, (G.induce ((({v} : Finset V)ᶜ : Finset V) : Set V)).largestInducedForestSize =
      G.largestInducedForestSize) →
    (∀ v : V, (G.induce ((({v} : Finset V)ᶜ : Finset V) : Set V)).pathCoverNumber +
        (G.induce ((({v} : Finset V)ᶜ : Finset V) : Set V)).largestInducedBipartiteSubgraphSize
          + 1 ≤ 2 * G.largestInducedForestSize) →
    (∀ v : V, (G.induce ((({v} : Finset V)ᶜ : Finset V) : Set V)).pathCoverNumber ≤
      G.pathCoverNumber) →
    (∀ a b : V, G.Adj a b →
      G.largestInducedForestSize < (G.deleteEdges {s(a, b)}).largestInducedForestSize) →
    (∀ R : Finset V, 2 ≤ R.card → R.card < Fintype.card V → (G.induce (R : Set V)).Connected →
      (G.induce (R : Set V)).pathCoverNumber + R.card + 2 * G.largestInducedForestSize <
        G.pathCoverNumber + Fintype.card V +
          2 * (G.induce (R : Set V)).largestInducedForestSize) →
    G.pathCoverNumber + Fintype.card V + 1 ≤ 2 * G.largestInducedForestSize

/-- 2-connected non-bipartite graphs above the scattering bound and above the path cover number
of every maximum induced bipartite subgraph such that: no vertex deletion changes the forest
number; every vertex-deleted subgraph satisfies the conjectured inequality against the forest
number of the whole graph; every vertex deletion strictly decreases `p + b`; every edge
deletion increases the forest number; and every connected proper induced subgraph on at least two
vertices has strictly larger slack `2 f - p - b`. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    3 ≤ Fintype.card V →
    G.Connected →
    (∀ v : V, (G.induce ({v}ᶜ : Set V)).Connected) →
    ¬ G.IsBipartite →
    (∀ S : Finset V,
      Nat.card (G.induce (S : Set V)ᶜ).ConnectedComponent < G.pathCoverNumber + S.card) →
    (∀ B : Finset V,
      (G.induce (B : Set V)).IsBipartite →
      B.card = G.largestInducedBipartiteSubgraphSize →
      (G.induce (B : Set V)).pathCoverNumber < G.pathCoverNumber) →
    (∀ v : V, (G.induce ((({v} : Finset V)ᶜ : Finset V) : Set V)).largestInducedForestSize =
      G.largestInducedForestSize) →
    (∀ v : V, (G.induce ((({v} : Finset V)ᶜ : Finset V) : Set V)).pathCoverNumber +
        (G.induce ((({v} : Finset V)ᶜ : Finset V) : Set V)).largestInducedBipartiteSubgraphSize
          + 1 ≤ 2 * G.largestInducedForestSize) →
    (∀ v : V, (G.induce ((({v} : Finset V)ᶜ : Finset V) : Set V)).pathCoverNumber +
        (G.induce ((({v} : Finset V)ᶜ : Finset V) : Set V)).largestInducedBipartiteSubgraphSize <
      G.pathCoverNumber + G.largestInducedBipartiteSubgraphSize) →
    (∀ a b : V, G.Adj a b →
      G.largestInducedForestSize < (G.deleteEdges {s(a, b)}).largestInducedForestSize) →
    (∀ R : Finset V, 2 ≤ R.card → R.card < Fintype.card V → (G.induce (R : Set V)).Connected →
      (G.induce (R : Set V)).pathCoverNumber +
          (G.induce (R : Set V)).largestInducedBipartiteSubgraphSize +
          2 * G.largestInducedForestSize <
        G.pathCoverNumber + G.largestInducedBipartiteSubgraphSize +
          2 * (G.induce (R : Set V)).largestInducedForestSize) →
    G.pathCoverNumber + G.largestInducedBipartiteSubgraphSize + 1 ≤ 2 * G.largestInducedForestSize

section

private lemma conjecture40_iff_nat {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α) :
    ⌈(((G.pathCoverNumber : ℝ) + G.b + 1) / 2)⌉ ≤ (G.largestInducedForestSize : ℤ) ↔
      G.pathCoverNumber + G.largestInducedBipartiteSubgraphSize + 1 ≤
        2 * G.largestInducedForestSize := by
  rw [Int.ceil_le, SimpleGraph.b, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  push_cast
  constructor
  · intro h
    have h' : ((G.pathCoverNumber + G.largestInducedBipartiteSubgraphSize + 1 : ℕ) : ℝ) ≤
        ((2 * G.largestInducedForestSize : ℕ) : ℝ) := by
      push_cast
      linarith
    exact Nat.cast_le.mp h'
  · intro h
    have h' : ((G.pathCoverNumber + G.largestInducedBipartiteSubgraphSize + 1 : ℕ) : ℝ) ≤
        ((2 * G.largestInducedForestSize : ℕ) : ℝ) := Nat.cast_le.mpr h
    push_cast at h'
    linarith

private lemma bipartite_size_eq_card {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hbip : G.IsBipartite) :
    G.largestInducedBipartiteSubgraphSize = Fintype.card V := by
  unfold SimpleGraph.largestInducedBipartiteSubgraphSize
  apply le_antisymm
  · apply csSup_le
    · refine ⟨0, ∅, ?_, rfl⟩
      rw [SimpleGraph.induce_isBipartite_iff_exists_coloring]
      exact ⟨fun _ => 0, by simp⟩
    · rintro n ⟨s, _, rfl⟩
      exact s.card_le_univ
  · apply le_csSup
    · exact ⟨Fintype.card V, fun n ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
    · refine ⟨Finset.univ, ?_, Finset.card_univ⟩
      rcases hbip with ⟨c⟩
      rw [SimpleGraph.induce_isBipartite_iff_exists_coloring]
      exact ⟨c, fun u _ v _ huv => c.valid huv⟩

private lemma two_connected_bipartite_card_ge_four {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hn : 3 ≤ Fintype.card V)
    (h2conn : ∀ v : V, (G.induce ({v}ᶜ : Set V)).Connected)
    (hbip : G.IsBipartite) :
    4 ≤ Fintype.card V := by
  by_contra hlt
  have hcard : Fintype.card V = 3 := by omega
  rcases hbip with ⟨c⟩
  have hnotinj : ¬ Function.Injective c := by
    intro hinj
    have hle := Fintype.card_le_of_injective c hinj
    simp [hcard] at hle
  rw [Function.Injective] at hnotinj
  push Not at hnotinj
  rcases hnotinj with ⟨x, y, hxy, hne⟩
  have hne_pair : ({x, y} : Finset V).card < Fintype.card V := by
    rw [Finset.card_pair hne, hcard]
    omega
  obtain ⟨z, hz⟩ : ∃ z : V, z ∉ ({x, y} : Finset V) := by
    by_contra hall
    push Not at hall
    have hsub : Finset.univ ⊆ ({x, y} : Finset V) := fun w _ => hall w
    have hle : Fintype.card V ≤ ({x, y} : Finset V).card := by
      simpa [Finset.card_univ] using Finset.card_le_card hsub
    omega
  have hzx : x ≠ z := fun h => hz (by simp [h])
  have hzy : y ≠ z := fun h => hz (by simp [h])
  have hxmem : x ∈ ({z}ᶜ : Set V) := by simpa using hzx
  have hymem : y ∈ ({z}ᶜ : Set V) := by simpa using hzy
  have hreach := (h2conn z).preconnected ⟨x, hxmem⟩ ⟨y, hymem⟩
  obtain ⟨p⟩ := hreach
  have hne_sub : (⟨x, hxmem⟩ : ({z}ᶜ : Set V)) ≠ ⟨y, hymem⟩ := by
    intro h
    exact hne (congrArg Subtype.val h)
  cases p with
  | nil => exact hne_sub rfl
  | @cons _ w _ hadj _ =>
    have hw_ne_x : w.val ≠ x := (G.ne_of_adj hadj).symm
    have hw_ne_z : w.val ≠ z := Set.mem_compl_singleton_iff.mp w.prop
    have hw_eq_y : w.val = y := by
      by_contra hwy
      have hsub : ({x, y, z, w.val} : Finset V).card ≤ Fintype.card V := Finset.card_le_univ _
      have h4 : ({x, y, z, w.val} : Finset V).card = 4 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp [hw_ne_z.symm]
        · simp [hzy, Ne.symm hwy]
        · simp [hne, hzx, hw_ne_x.symm]
      omega
    have hadj_xy : G.Adj x y := hw_eq_y ▸ hadj
    exact c.valid hadj_xy hxy

private lemma card_two_bound {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hconn : G.Connected) (hcard : Fintype.card V = 2) :
    G.pathCoverNumber + G.largestInducedBipartiteSubgraphSize + 1 ≤
      2 * G.largestInducedForestSize := by
  have hb : G.largestInducedBipartiteSubgraphSize ≤ 2 := by
    unfold SimpleGraph.largestInducedBipartiteSubgraphSize
    apply csSup_le
    · refine ⟨0, ∅, ?_, rfl⟩
      rw [SimpleGraph.induce_isBipartite_iff_exists_coloring]
      exact ⟨fun _ => 0, by simp⟩
    · rintro n ⟨s, _, rfl⟩
      exact hcard ▸ s.card_le_univ
  have hf : 2 ≤ G.largestInducedForestSize := by
    unfold SimpleGraph.largestInducedForestSize
    apply le_csSup
    · exact ⟨Fintype.card V, fun n ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
    · refine ⟨Finset.univ, ?_, by rw [Finset.card_univ, hcard]⟩
      intro u c hc
      have hlen := hc.three_le_length
      have hnodup := hc.support_nodup
      have hle := hnodup.length_le_card
      have hcard_u : Fintype.card (↑(Finset.univ : Finset V) : Set V) = 2 := by
        simp [hcard]
      have hlen_tail : c.support.tail.length = c.length := by
        simp [SimpleGraph.Walk.length_support]
      omega
  have hp : G.pathCoverNumber ≤ 1 := by
    obtain ⟨u, v, huv_ne, huv_univ⟩ : ∃ u v : V, u ≠ v ∧ ({u, v} : Finset V) = Finset.univ := by
      have h1 : ∃ u : V, True := by
        have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
        exact ⟨Classical.arbitrary V, trivial⟩
      rcases h1 with ⟨u, _⟩
      have hne_u : ({u} : Finset V).card < Fintype.card V := by simp [hcard]
      obtain ⟨v, hv⟩ : ∃ v : V, v ∉ ({u} : Finset V) := by
        by_contra hall
        push Not at hall
        have hle : (Finset.univ : Finset V).card ≤ ({u} : Finset V).card :=
          Finset.card_le_card (fun w _ => hall w)
        rw [Finset.card_univ] at hle
        omega
      have huv : u ≠ v := fun h => hv (by simp [h])
      refine ⟨u, v, huv, ?_⟩
      apply Finset.eq_univ_of_card
      rw [Finset.card_pair huv, hcard]
    obtain ⟨w⟩ := hconn.preconnected u v
    cases w with
    | nil => exact (huv_ne rfl).elim
    | @cons _ x _ hux _ =>
      have hx : x = v := by
        have hmem : x ∈ ({u, v} : Finset V) := huv_univ ▸ Finset.mem_univ x
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with rfl | rfl
        · exact (G.ne_of_adj hux rfl).elim
        · rfl
      have huv_adj : G.Adj u v := hx ▸ hux
      unfold SimpleGraph.pathCoverNumber
      apply Nat.sInf_le
      refine ⟨{{u, v}}, Finset.card_singleton _, ?_, ?_, ?_⟩
      · intro s1 hs1 s2 hs2 hne
        simp only [Finset.mem_singleton] at hs1 hs2
        exact (hne (hs1.trans hs2.symm)).elim
      · intro w _
        simp [huv_univ]
      · intro s hs
        simp only [Finset.mem_singleton] at hs
        subst hs
        refine ⟨u, v, Walk.cons huv_adj Walk.nil, ?_, ?_⟩
        · rw [Walk.cons_isPath_iff]
          exact ⟨Walk.IsPath.nil, by simp [huv_ne]⟩
        · ext w
          simp
  omega

private lemma isPathCover_map {α : Type*} {β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {G : SimpleGraph α} {K : SimpleGraph β} (e : G ≃g K)
    {P : Finset (Finset α)} (hP : G.IsPathCover P) :
    K.IsPathCover (P.image fun s => s.map e.toEquiv.toEmbedding) := by
  rcases hP with ⟨hdisj, hcov, hpaths⟩
  refine ⟨?_, ?_, ?_⟩
  · intro t1 ht1 t2 ht2 hne
    rcases Finset.mem_image.mp ht1 with ⟨s1, hs1, rfl⟩
    rcases Finset.mem_image.mp ht2 with ⟨s2, hs2, rfl⟩
    have hsne : s1 ≠ s2 := fun h => hne (by rw [h])
    refine Finset.disjoint_left.mpr fun b hb1 hb2 => ?_
    rcases Finset.mem_map.mp hb1 with ⟨a1, ha1, rfl⟩
    rcases Finset.mem_map.mp hb2 with ⟨a2, ha2, hEq⟩
    rw [e.toEquiv.toEmbedding.injective hEq] at ha2
    exact Finset.disjoint_left.mp (hdisj s1 hs1 s2 hs2 hsne) ha1 ha2
  · intro b _
    have ha : e.symm b ∈ P.biUnion id := hcov (Finset.mem_univ (e.symm b))
    rcases Finset.mem_biUnion.mp ha with ⟨s, hsP, has⟩
    refine Finset.mem_biUnion.mpr ⟨s.map e.toEquiv.toEmbedding, Finset.mem_image_of_mem _ hsP, ?_⟩
    exact Finset.mem_map.mpr ⟨e.symm b, has, e.apply_symm_apply b⟩
  · intro t ht
    rcases Finset.mem_image.mp ht with ⟨s, hsP, rfl⟩
    rcases hpaths s hsP with ⟨u, v, p, hp, hs⟩
    refine ⟨e u, e v, p.map e.toHom, (Walk.isPath_map_iff_of_injective e.injective).mpr hp, ?_⟩
    ext b
    simp only [hs, Finset.mem_map, List.mem_toFinset, Walk.support_map, List.mem_map,
      RelIso.coe_fn_toEquiv, Function.Embedding.coeFn_mk]
    rfl

private lemma induce_isBipartite_map {α : Type*} {β : Type*} [DecidableEq α] [DecidableEq β]
    {G : SimpleGraph α} {K : SimpleGraph β} (e : G ≃g K) {s : Finset α}
    (hs : (G.induce (s : Set α)).IsBipartite) :
    (K.induce ((s.map e.toEquiv.toEmbedding : Finset β) : Set β)).IsBipartite := by
  rw [SimpleGraph.induce_isBipartite_iff_exists_coloring] at hs ⊢
  rcases hs with ⟨c, hc⟩
  refine ⟨fun b => c (e.symm b), ?_⟩
  intro u hu v hv huv
  rcases Finset.mem_map.mp hu with ⟨a, ha, rfl⟩
  rcases Finset.mem_map.mp hv with ⟨b, hb, rfl⟩
  simp only [RelIso.coe_fn_toEquiv, Equiv.coe_toEmbedding, RelIso.symm_apply_apply]
  exact hc a ha b hb (e.map_rel_iff.mp huv)

private lemma induce_isAcyclic_map {α : Type*} {β : Type*} [DecidableEq α] [DecidableEq β]
    {G : SimpleGraph α} {K : SimpleGraph β} (e : G ≃g K) {s : Finset α}
    (hs : (G.induce (s : Set α)).IsAcyclic) :
    (K.induce ((s.map e.toEquiv.toEmbedding : Finset β) : Set β)).IsAcyclic := by
  intro v c hc
  let φ : K.induce ((s.map e.toEquiv.toEmbedding : Finset β) : Set β) →g G.induce (s : Set α) :=
    { toFun := fun x =>
        ⟨e.symm x.val, by
          rcases Finset.mem_map.mp x.prop with ⟨a, ha, hax⟩
          have : e.symm x.val = a := by
            rw [← hax]
            exact e.symm_apply_apply a
          simpa [this] using ha⟩
      map_rel' := fun {x y} hxy => e.symm.map_rel_iff.mpr hxy }
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    exact e.symm.injective (congrArg Subtype.val hxy)
  exact hs (c.map φ) (hc.map hφ_inj)

private lemma iso_invariance {α : Type*} {β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {G : SimpleGraph α} {K : SimpleGraph β} (e : G ≃g K) :
    G.pathCoverNumber = K.pathCoverNumber ∧
      G.largestInducedBipartiteSubgraphSize = K.largestInducedBipartiteSubgraphSize ∧
      G.largestInducedForestSize = K.largestInducedForestSize := by
  refine ⟨?_, ?_, ?_⟩
  · unfold SimpleGraph.pathCoverNumber
    congr 1
    ext k
    constructor
    · rintro ⟨P, rfl, hP⟩
      refine ⟨P.image fun s => s.map e.toEquiv.toEmbedding, ?_, isPathCover_map e hP⟩
      exact Finset.card_image_of_injective P (Finset.map_injective e.toEquiv.toEmbedding)
    · rintro ⟨Q, rfl, hQ⟩
      refine ⟨Q.image fun s => s.map e.symm.toEquiv.toEmbedding, ?_, isPathCover_map e.symm hQ⟩
      exact Finset.card_image_of_injective Q (Finset.map_injective e.symm.toEquiv.toEmbedding)
  · unfold SimpleGraph.largestInducedBipartiteSubgraphSize
    congr 1
    ext n
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s.map e.toEquiv.toEmbedding, induce_isBipartite_map e hs, Finset.card_map _⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t.map e.symm.toEquiv.toEmbedding, induce_isBipartite_map e.symm ht, Finset.card_map _⟩
  · unfold SimpleGraph.largestInducedForestSize
    congr 1
    ext n
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s.map e.toEquiv.toEmbedding, induce_isAcyclic_map e hs, Finset.card_map _⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t.map e.symm.toEquiv.toEmbedding, induce_isAcyclic_map e.symm ht, Finset.card_map _⟩

private lemma isAcyclic_of_all_adj_eq {W : Type*} (H : SimpleGraph W) (r : W)
    (hstar : ∀ a b : W, H.Adj a b → a = r ∨ b = r) : H.IsAcyclic := by
  intro u c hc
  have hlen := hc.three_le_length
  cases c with
  | nil => simp at hlen
  | @cons _ x _ h1 c1 =>
    cases c1 with
    | nil => simp at hlen
    | @cons _ y _ h2 c2 =>
      cases c2 with
      | nil => simp at hlen
      | @cons _ z _ h3 c3 =>
        have hnd : (x :: y :: c3.support).Nodup := hc.support_nodup
        rw [List.nodup_cons] at hnd
        have hx_not : x ∉ y :: c3.support := hnd.1
        have hy_nd : (y :: c3.support).Nodup := hnd.2
        rw [List.nodup_cons] at hy_nd
        have hy_not : y ∉ c3.support := hy_nd.1
        have hz_mem : z ∈ c3.support := c3.start_mem_support
        have hu_mem : u ∈ c3.support := c3.end_mem_support
        rcases hstar u x h1 with rfl | rfl
        · rcases hstar x y h2 with hxr | rfl
          · exact H.ne_of_adj h1 hxr.symm
          · exact hy_not hu_mem
        · rcases hstar y z h3 with hyx | rfl
          · exact H.ne_of_adj h2 hyx.symm
          · exact hx_not (List.mem_cons_of_mem _ hz_mem)

private lemma indep_add_one_le_forest {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (hconn : H.Connected) (hn : 1 < Fintype.card W)
    (I : Finset W) (hind : ∀ x ∈ I, ∀ y ∈ I, ¬ H.Adj x y) :
    I.card + 1 ≤ H.largestInducedForestSize := by
  obtain ⟨w, hw⟩ : ∃ w : W, w ∉ I := by
    by_contra hall
    push Not at hall
    obtain ⟨x, y, hxy⟩ := Fintype.one_lt_card_iff.mp hn
    obtain ⟨p⟩ := hconn.preconnected x y
    cases p with
    | nil => exact hxy rfl
    | @cons _ z _ hxz _ => exact hind x (hall x) z (hall z) hxz
  let T : Finset W := insert w I
  have hTcard : T.card = I.card + 1 := Finset.card_insert_of_notMem hw
  have hTacyc : (H.induce (T : Set W)).IsAcyclic := by
    apply isAcyclic_of_all_adj_eq (H.induce (T : Set W)) ⟨w, Finset.mem_insert_self w I⟩
    intro a b hadj
    have ha : a.val = w ∨ a.val ∈ I := Finset.mem_insert.mp a.prop
    have hb : b.val = w ∨ b.val ∈ I := Finset.mem_insert.mp b.prop
    rcases ha with haw | haI
    · exact Or.inl (Subtype.ext haw)
    · rcases hb with hbw | hbI
      · exact Or.inr (Subtype.ext hbw)
      · exact (hind a.val haI b.val hbI hadj).elim
  unfold SimpleGraph.largestInducedForestSize
  apply le_csSup
  · exact ⟨Fintype.card W, fun n ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
  · exact ⟨T, hTacyc, hTcard⟩

private lemma bip_add_two_le_two_forest {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (hconn : H.Connected) (hn : 1 < Fintype.card W) :
    H.largestInducedBipartiteSubgraphSize + 2 ≤ 2 * H.largestInducedForestSize := by
  have hne : ({ n | ∃ s : Finset W, (H.induce (s : Set W)).IsBipartite ∧ s.card = n }).Nonempty := by
    refine ⟨0, ∅, ?_, rfl⟩
    rw [SimpleGraph.induce_isBipartite_iff_exists_coloring]
    exact ⟨fun _ => 0, by simp⟩
  have hbdd : BddAbove { n | ∃ s : Finset W, (H.induce (s : Set W)).IsBipartite ∧ s.card = n } :=
    ⟨Fintype.card W, fun n ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
  obtain ⟨B, hBbip, hBcard⟩ := Nat.sSup_mem hne hbdd
  obtain ⟨c, hc⟩ := (SimpleGraph.induce_isBipartite_iff_exists_coloring H B).mp hBbip
  let X : Finset W := B.filter (fun v => c v = 0)
  let Y : Finset W := B.filter (fun v => c v = 1)
  have hXind : ∀ x ∈ X, ∀ y ∈ X, ¬ H.Adj x y := by
    intro x hx y hy hadj
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    exact hc x hx'.1 y hy'.1 hadj (hx'.2.trans hy'.2.symm)
  have hYind : ∀ x ∈ Y, ∀ y ∈ Y, ¬ H.Adj x y := by
    intro x hx y hy hadj
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    exact hc x hx'.1 y hy'.1 hadj (hx'.2.trans hy'.2.symm)
  have hXYdisj : Disjoint X Y := by
    rw [Finset.disjoint_left]
    intro v hvX hvY
    have h0 := (Finset.mem_filter.mp hvX).2
    have h1 := (Finset.mem_filter.mp hvY).2
    have : (0 : Fin 2) = 1 := h0.symm.trans h1
    omega
  have hXYunion : X ∪ Y = B := by
    ext v
    simp only [X, Y, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
    · intro hv
      have h01 : c v = 0 ∨ c v = 1 := by
        rcases c v with ⟨k, hk⟩
        have hkz : k = 0 ∨ k = 1 := by omega
        rcases hkz with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      rcases h01 with h0 | h1
      · exact Or.inl ⟨hv, h0⟩
      · exact Or.inr ⟨hv, h1⟩
  have hcard : X.card + Y.card = B.card := by
    rw [← Finset.card_union_of_disjoint hXYdisj, hXYunion]
  have hX := indep_add_one_le_forest H hconn hn X hXind
  have hY := indep_add_one_le_forest H hconn hn Y hYind
  change B.card = H.largestInducedBipartiteSubgraphSize at hBcard
  omega

private lemma scattering_bound {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hconn : G.Connected) (hn : 1 < Fintype.card V) (S : Finset V) :
    Nat.card (G.induce (S : Set V)ᶜ).ConnectedComponent +
        G.largestInducedBipartiteSubgraphSize + 1 ≤
      2 * G.largestInducedForestSize + S.card := by
  classical
  set H := G.induce (S : Set V)ᶜ
  rw [Nat.card_eq_fintype_card]
  let D : H.ConnectedComponent → Finset V := fun C =>
    Finset.univ.filter (fun v => ∃ hv : v ∈ (S : Set V)ᶜ, H.connectedComponentMk ⟨v, hv⟩ = C)
  have hD_mem : ∀ C v, v ∈ D C ↔ ∃ hv : v ∈ (S : Set V)ᶜ, H.connectedComponentMk ⟨v, hv⟩ = C := by
    intro C v
    simp [D]
  have hD_disj : ∀ C₁ C₂, C₁ ≠ C₂ → Disjoint (D C₁) (D C₂) := by
    intro C₁ C₂ hne
    rw [Finset.disjoint_left]
    intro v hv₁ hv₂
    rcases (hD_mem C₁ v).mp hv₁ with ⟨hv, hC₁⟩
    rcases (hD_mem C₂ v).mp hv₂ with ⟨_, hC₂⟩
    exact hne (hC₁.symm.trans hC₂)
  have hD_biUnion : Finset.univ.biUnion D = Sᶜ := by
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, hD_mem, Finset.mem_compl]
    constructor
    · rintro ⟨_, hv, _⟩
      exact hv
    · intro hv
      exact ⟨H.connectedComponentMk ⟨v, hv⟩, hv, rfl⟩
  have hD_sum_card : ∑ C : H.ConnectedComponent, (D C).card = Sᶜ.card := by
    rw [← hD_biUnion, Finset.card_biUnion]
    intro C₁ _ C₂ _ hne
    exact hD_disj C₁ C₂ hne
  have hD_nonempty : ∀ C : H.ConnectedComponent, 1 ≤ (D C).card := by
    intro C
    obtain ⟨⟨v, hv⟩, hC⟩ := Quot.exists_rep C
    have hvmem : v ∈ D C := (hD_mem C v).mpr ⟨hv, hC⟩
    exact Finset.card_pos.mpr ⟨v, hvmem⟩
  have hD_no_cross : ∀ C₁ C₂ x y, x ∈ D C₁ → y ∈ D C₂ → G.Adj x y → C₁ = C₂ := by
    intro C₁ C₂ x y hx hy hadj
    rcases (hD_mem C₁ x).mp hx with ⟨hx', hC₁⟩
    rcases (hD_mem C₂ y).mp hy with ⟨hy', hC₂⟩
    have hadjH : H.Adj ⟨x, hx'⟩ ⟨y, hy'⟩ := hadj
    have heq : H.connectedComponentMk ⟨x, hx'⟩ = H.connectedComponentMk ⟨y, hy'⟩ :=
      ConnectedComponent.eq.mpr hadjH.reachable
    exact hC₁.symm.trans (heq.trans hC₂)
  by_cases hsmall : ∀ C : H.ConnectedComponent, (D C).card ≤ 1
  · have hcomp_card : Fintype.card H.ConnectedComponent = Sᶜ.card := by
      have h1 : ∀ C : H.ConnectedComponent, (D C).card = 1 := fun C =>
        le_antisymm (hsmall C) (hD_nonempty C)
      rw [← hD_sum_card]
      simp [h1]
    have hSc_ind : ∀ x ∈ Sᶜ, ∀ y ∈ Sᶜ, ¬ G.Adj x y := by
      intro x hx y hy hadj
      have hx' : x ∈ (S : Set V)ᶜ := by simpa using hx
      have hy' : y ∈ (S : Set V)ᶜ := by simpa using hy
      let C := H.connectedComponentMk ⟨x, hx'⟩
      have hxD : x ∈ D C := (hD_mem C x).mpr ⟨hx', rfl⟩
      have hadjH : H.Adj ⟨x, hx'⟩ ⟨y, hy'⟩ := hadj
      have hyD : y ∈ D C := (hD_mem C y).mpr ⟨hy', (ConnectedComponent.eq.mpr hadjH.reachable).symm⟩
      have hne : x ≠ y := G.ne_of_adj hadj
      have hpair : ({x, y} : Finset V) ⊆ D C := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption
      have hle := Finset.card_le_card hpair
      rw [Finset.card_pair hne] at hle
      have := hsmall C
      omega
    have hf : Sᶜ.card + 1 ≤ G.largestInducedForestSize :=
      indep_add_one_le_forest G hconn hn Sᶜ hSc_ind
    have hb : G.largestInducedBipartiteSubgraphSize ≤ Fintype.card V := by
      unfold SimpleGraph.largestInducedBipartiteSubgraphSize
      apply csSup_le
      · refine ⟨0, ∅, ?_, rfl⟩
        rw [SimpleGraph.induce_isBipartite_iff_exists_coloring]
        exact ⟨fun _ => 0, by simp⟩
      · rintro n ⟨s, _, rfl⟩
        exact s.card_le_univ
    have hcard_split : Sᶜ.card + S.card = Fintype.card V := Finset.card_compl_add_card S
    omega
  · push Not at hsmall
    rcases hsmall with ⟨C₀, hC₀⟩
    have hD_conn : ∀ C : H.ConnectedComponent, (G.induce (D C : Set V)).Connected := by
      intro C
      have hneDC : Nonempty (D C : Set V) := by
        obtain ⟨v, hv⟩ := Finset.card_pos.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one (hD_nonempty C))
        exact ⟨⟨v, hv⟩⟩
      refine ⟨fun a b => ?_⟩
      rcases (hD_mem C a.val).mp a.prop with ⟨ha, hCa⟩
      rcases (hD_mem C b.val).mp b.prop with ⟨hb, hCb⟩
      have hreach : H.Reachable ⟨a.val, ha⟩ ⟨b.val, hb⟩ :=
        ConnectedComponent.exact (hCa.trans hCb.symm)
      obtain ⟨p⟩ := hreach
      let p' : (G.induce (S : Set V)ᶜ).Walk ⟨a.val, ha⟩ ⟨b.val, hb⟩ := p
      let pG : G.Walk a.val b.val := p'.map (Embedding.induce (G := G) (S : Set V)ᶜ).toHom
      have hsub : ∀ v ∈ pG.support, v ∈ (D C : Set V) := by
        intro v hv
        have hv' : v ∈ List.map (Embedding.induce (G := G) (S : Set V)ᶜ).toHom p'.support :=
          (Walk.support_map (Embedding.induce (G := G) (S : Set V)ᶜ).toHom p') ▸ hv
        rcases List.mem_map.mp hv' with ⟨z, hz, rfl⟩
        have hz_reach : H.Reachable ⟨a.val, ha⟩ z := (p'.takeUntil z hz).reachable
        have hz_eq : H.connectedComponentMk z = C :=
          (ConnectedComponent.eq.mpr hz_reach).symm.trans hCa
        exact (hD_mem C z.val).mpr ⟨z.prop, hz_eq⟩
      exact ⟨pG.induce (D C : Set V) hsub⟩
    have hF_exists : ∀ C : H.ConnectedComponent,
        ∃ F : Finset (D C : Set V),
          ((G.induce (D C : Set V)).induce (F : Set (D C : Set V))).IsAcyclic ∧
          F.card = (G.induce (D C : Set V)).largestInducedForestSize := by
      intro C
      have hne : ({ n | ∃ s : Finset (D C : Set V),
          ((G.induce (D C : Set V)).induce (s : Set (D C : Set V))).IsAcyclic ∧ s.card = n }).Nonempty := by
        refine ⟨0, ∅, ?_, rfl⟩
        intro u c hc
        exact False.elim (Finset.notMem_empty u.val u.prop)
      have hbdd : BddAbove { n | ∃ s : Finset (D C : Set V),
          ((G.induce (D C : Set V)).induce (s : Set (D C : Set V))).IsAcyclic ∧ s.card = n } :=
        ⟨Fintype.card (D C : Set V), fun n ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
      exact Nat.sSup_mem hne hbdd
    choose F hF_acyc hF_card using hF_exists
    let F' : H.ConnectedComponent → Finset V := fun C => (F C).image Subtype.val
    have hF'_sub : ∀ C, F' C ⊆ D C := by
      intro C x hx
      rcases Finset.mem_image.mp hx with ⟨a, _, rfl⟩
      exact a.prop
    have hF'_card : ∀ C, (F' C).card = (G.induce (D C : Set V)).largestInducedForestSize := by
      intro C
      rw [Finset.card_image_of_injective _ Subtype.val_injective, hF_card C]
    have hF'_disj : ∀ C₁ C₂, C₁ ≠ C₂ → Disjoint (F' C₁) (F' C₂) := fun C₁ C₂ hne =>
      Disjoint.mono (hF'_sub C₁) (hF'_sub C₂) (hD_disj C₁ C₂ hne)
    let U : Finset V := Finset.univ.biUnion F'
    have hU_card : U.card = ∑ C : H.ConnectedComponent, (G.induce (D C : Set V)).largestInducedForestSize := by
      rw [Finset.card_biUnion]
      · simp [hF'_card]
      · intro C₁ _ C₂ _ hne
        exact hF'_disj C₁ C₂ hne
    have hU_acyc : (G.induce (U : Set V)).IsAcyclic := by
      intro u c hc
      have huU : u.val ∈ U := u.prop
      rcases Finset.mem_biUnion.mp huU with ⟨C, _, huF'⟩
      have huD : u.val ∈ D C := hF'_sub C huF'
      have hwalk_stay : ∀ {a b : (U : Set V)} (p : (G.induce (U : Set V)).Walk a b),
          a.val ∈ D C → ∀ w ∈ p.support, w.val ∈ D C := by
        intro a b p
        induction p with
        | nil =>
          intro ha w hw
          simp only [Walk.support_nil, List.mem_singleton] at hw
          subst hw
          exact ha
        | @cons a x b hadj q ih =>
          intro ha w hw
          have hxU : x.val ∈ U := x.prop
          rcases Finset.mem_biUnion.mp hxU with ⟨C', _, hxF'⟩
          have hxD' : x.val ∈ D C' := hF'_sub C' hxF'
          have hCC' : C = C' := hD_no_cross C C' a.val x.val ha hxD' hadj
          have hxD : x.val ∈ D C := hCC' ▸ hxD'
          simp only [Walk.support_cons, List.mem_cons] at hw
          rcases hw with rfl | hw'
          · exact ha
          · exact ih hxD w hw'
      let cG : G.Walk u.val u.val := c.map (Embedding.induce (G := G) (U : Set V)).toHom
      have hcG : cG.IsCycle :=
        (Walk.isCycle_map_iff_of_injective (Embedding.induce (G := G) (U : Set V)).injective).mpr hc
      have hsubD : ∀ x ∈ cG.support, x ∈ (D C : Set V) := by
        intro x hx
        have hx' : x ∈ List.map (Embedding.induce (G := G) (U : Set V)).toHom c.support :=
          (Walk.support_map (Embedding.induce (G := G) (U : Set V)).toHom c) ▸ hx
        rcases List.mem_map.mp hx' with ⟨w, hw, rfl⟩
        exact hwalk_stay c huD w hw
      let cD : (G.induce (D C : Set V)).Walk ⟨u.val, huD⟩ ⟨u.val, huD⟩ :=
        cG.induce (D C : Set V) hsubD
      have hcD : cD.IsCycle :=
        (Walk.isCycle_map_iff_of_injective
          (f := (Embedding.induce (G := G) (D C : Set V)).toHom)
          (Embedding.induce (G := G) (D C : Set V)).injective).mp
          ((Walk.map_induce cG hsubD).symm ▸ hcG)
      have hsubF : ∀ y ∈ cD.support, y ∈ (F C : Set (D C : Set V)) := by
        intro y hy
        have hsupp : List.map (Embedding.induce (G := G) (D C : Set V)).toHom cD.support = cG.support := by
          rw [← Walk.support_map]
          exact congrArg Walk.support (Walk.map_induce cG hsubD)
        have hyG : y.val ∈ cG.support := by
          rw [← hsupp]
          exact List.mem_map_of_mem hy
        have hyG' : y.val ∈ List.map (Embedding.induce (G := G) (U : Set V)).toHom c.support :=
          (Walk.support_map (Embedding.induce (G := G) (U : Set V)).toHom c) ▸ hyG
        rcases List.mem_map.mp hyG' with ⟨w, _, hwy⟩
        have hwU : y.val ∈ U := hwy ▸ w.prop
        rcases Finset.mem_biUnion.mp hwU with ⟨C', _, hyF'⟩
        have hyD' : y.val ∈ D C' := hF'_sub C' hyF'
        have hCC' : C' = C := by
          by_contra hne
          exact Finset.disjoint_left.mp (hD_disj C' C hne) hyD' y.prop
        have hyF : y.val ∈ F' C := hCC' ▸ hyF'
        rcases Finset.mem_image.mp hyF with ⟨a, haF, hay⟩
        have : a = y := Subtype.ext hay
        exact this ▸ haF
      let cF := cD.induce (F C : Set (D C : Set V)) hsubF
      have hcF : cF.IsCycle :=
        (Walk.isCycle_map_iff_of_injective
          (f := (Embedding.induce (G := G.induce (D C : Set V)) (F C : Set (D C : Set V))).toHom)
          (Embedding.induce (G := G.induce (D C : Set V)) (F C : Set (D C : Set V))).injective).mp
          ((Walk.map_induce cD hsubF).symm ▸ hcD)
      exact hF_acyc C cF hcF
    have hforest_sum :
        ∑ C : H.ConnectedComponent, (G.induce (D C : Set V)).largestInducedForestSize ≤
          G.largestInducedForestSize := by
      rw [← hU_card]
      unfold SimpleGraph.largestInducedForestSize
      apply le_csSup
      · exact ⟨Fintype.card V, fun n ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
      · exact ⟨U, hU_acyc, rfl⟩
    have hB_ne : ({ n | ∃ s : Finset V, (G.induce (s : Set V)).IsBipartite ∧ s.card = n }).Nonempty := by
      refine ⟨0, ∅, ?_, rfl⟩
      rw [SimpleGraph.induce_isBipartite_iff_exists_coloring]
      exact ⟨fun _ => 0, by simp⟩
    have hB_bdd : BddAbove { n | ∃ s : Finset V, (G.induce (s : Set V)).IsBipartite ∧ s.card = n } :=
      ⟨Fintype.card V, fun n ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
    obtain ⟨B, hBbip, hBcard⟩ := Nat.sSup_mem hB_ne hB_bdd
    change B.card = G.largestInducedBipartiteSubgraphSize at hBcard
    obtain ⟨col, hcol⟩ := (SimpleGraph.induce_isBipartite_iff_exists_coloring G B).mp hBbip
    have hB_comp : ∀ C : H.ConnectedComponent,
        (B ∩ D C).card ≤ (G.induce (D C : Set V)).largestInducedBipartiteSubgraphSize := by
      intro C
      let BC : Finset (D C : Set V) := Finset.univ.filter (fun x : (D C : Set V) => x.val ∈ B)
      have hBC_img : BC.image Subtype.val = B ∩ D C := by
        ext v
        simp only [BC, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_inter]
        constructor
        · rintro ⟨a, haB, rfl⟩
          exact ⟨haB, a.prop⟩
        · rintro ⟨hvB, hvD⟩
          exact ⟨⟨v, hvD⟩, hvB, rfl⟩
      have hBC_card : BC.card = (B ∩ D C).card := by
        rw [← hBC_img, Finset.card_image_of_injective _ Subtype.val_injective]
      have hBC_bip : ((G.induce (D C : Set V)).induce (BC : Set (D C : Set V))).IsBipartite := by
        rw [SimpleGraph.induce_isBipartite_iff_exists_coloring]
        refine ⟨fun x => col x.val, ?_⟩
        intro u hu v hv hadj
        have huB : u.val ∈ B := (Finset.mem_filter.mp hu).2
        have hvB : v.val ∈ B := (Finset.mem_filter.mp hv).2
        exact hcol u.val huB v.val hvB hadj
      rw [← hBC_card]
      unfold SimpleGraph.largestInducedBipartiteSubgraphSize
      apply le_csSup
      · exact ⟨Fintype.card (D C : Set V), fun n ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
      · exact ⟨BC, hBC_bip, rfl⟩
    have hB_split : B.card ≤ S.card + ∑ C : H.ConnectedComponent, (B ∩ D C).card := by
      have hsub : B ⊆ S ∪ Finset.univ.biUnion (fun C => B ∩ D C) := by
        intro v hv
        by_cases hvS : v ∈ S
        · exact Finset.mem_union_left _ hvS
        · apply Finset.mem_union_right
          have hvSc : v ∈ Sᶜ := Finset.mem_compl.mpr hvS
          rw [← hD_biUnion, Finset.mem_biUnion] at hvSc
          rcases hvSc with ⟨C, _, hvD⟩
          exact Finset.mem_biUnion.mpr ⟨C, Finset.mem_univ C, Finset.mem_inter.mpr ⟨hv, hvD⟩⟩
      calc B.card
          ≤ (S ∪ Finset.univ.biUnion (fun C => B ∩ D C)).card := Finset.card_le_card hsub
        _ ≤ S.card + (Finset.univ.biUnion (fun C => B ∩ D C)).card := Finset.card_union_le _ _
        _ ≤ S.card + ∑ C : H.ConnectedComponent, (B ∩ D C).card := by
            gcongr
            exact Finset.card_biUnion_le
    have hB_sum :
        G.largestInducedBipartiteSubgraphSize ≤
          S.card + ∑ C : H.ConnectedComponent,
            (G.induce (D C : Set V)).largestInducedBipartiteSubgraphSize := by
      rw [← hBcard]
      exact le_trans hB_split (Nat.add_le_add_left (Finset.sum_le_sum fun C _ => hB_comp C) _)
    have hD_fintype_card : ∀ C : H.ConnectedComponent, Fintype.card (D C : Set V) = (D C).card := by
      intro C
      simp
    have hcomp_bound : ∀ C : H.ConnectedComponent,
        (G.induce (D C : Set V)).largestInducedBipartiteSubgraphSize + 1 ≤
          2 * (G.induce (D C : Set V)).largestInducedForestSize := by
      intro C
      by_cases h2 : 2 ≤ (D C).card
      · have hgt1 : 1 < Fintype.card (D C : Set V) := by
          rw [hD_fintype_card C]
          omega
        have := bip_add_two_le_two_forest (G.induce (D C : Set V)) (hD_conn C) hgt1
        omega
      · have h1 : (D C).card = 1 := by
          have := hD_nonempty C
          omega
        have hcard1 : Fintype.card (D C : Set V) = 1 := by
          rw [hD_fintype_card C, h1]
        have hb1 : (G.induce (D C : Set V)).largestInducedBipartiteSubgraphSize ≤ 1 := by
          unfold SimpleGraph.largestInducedBipartiteSubgraphSize
          apply csSup_le
          · refine ⟨0, ∅, ?_, rfl⟩
            rw [SimpleGraph.induce_isBipartite_iff_exists_coloring]
            exact ⟨fun _ => 0, by simp⟩
          · rintro n ⟨s, _, rfl⟩
            exact hcard1 ▸ s.card_le_univ
        have hf1 : 1 ≤ (G.induce (D C : Set V)).largestInducedForestSize := by
          unfold SimpleGraph.largestInducedForestSize
          apply le_csSup
          · exact ⟨Fintype.card (D C : Set V), fun n ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
          · refine ⟨Finset.univ, ?_, by rw [Finset.card_univ, hcard1]⟩
            intro u c hc
            have hlen := hc.three_le_length
            have hnodup := hc.support_nodup
            have hle := hnodup.length_le_card
            have hcard_u : Fintype.card (↑(Finset.univ : Finset (D C : Set V)) : Set (D C : Set V)) = 1 := by
              simp [h1]
            have hlen_tail : c.support.tail.length = c.length := by
              rw [List.length_tail, SimpleGraph.Walk.length_support]
              omega
            omega
        omega
    have hC₀_bound :
        (G.induce (D C₀ : Set V)).largestInducedBipartiteSubgraphSize + 2 ≤
          2 * (G.induce (D C₀ : Set V)).largestInducedForestSize := by
      have hgt1 : 1 < Fintype.card (D C₀ : Set V) := by
        rw [hD_fintype_card C₀]
        omega
      exact bip_add_two_le_two_forest (G.induce (D C₀ : Set V)) (hD_conn C₀) hgt1
    have hsum_erase :
        ∑ C ∈ Finset.univ.erase C₀,
            ((G.induce (D C : Set V)).largestInducedBipartiteSubgraphSize + 1) ≤
          ∑ C ∈ Finset.univ.erase C₀,
            (2 * (G.induce (D C : Set V)).largestInducedForestSize) :=
      Finset.sum_le_sum fun C _ => hcomp_bound C
    have hsum_all :
        (∑ C : H.ConnectedComponent,
            ((G.induce (D C : Set V)).largestInducedBipartiteSubgraphSize + 1)) + 1 ≤
          ∑ C : H.ConnectedComponent,
            (2 * (G.induce (D C : Set V)).largestInducedForestSize) := by
      have hL := Finset.sum_erase_add Finset.univ
        (fun C : H.ConnectedComponent =>
          (G.induce (D C : Set V)).largestInducedBipartiteSubgraphSize + 1)
        (Finset.mem_univ C₀)
      have hR := Finset.sum_erase_add Finset.univ
        (fun C : H.ConnectedComponent =>
          2 * (G.induce (D C : Set V)).largestInducedForestSize)
        (Finset.mem_univ C₀)
      omega
    have hsum_L :
        ∑ C : H.ConnectedComponent,
            ((G.induce (D C : Set V)).largestInducedBipartiteSubgraphSize + 1) =
          (∑ C : H.ConnectedComponent,
            (G.induce (D C : Set V)).largestInducedBipartiteSubgraphSize) +
            Fintype.card H.ConnectedComponent := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
    have hsum_R :
        ∑ C : H.ConnectedComponent,
            (2 * (G.induce (D C : Set V)).largestInducedForestSize) =
          2 * ∑ C : H.ConnectedComponent,
            (G.induce (D C : Set V)).largestInducedForestSize := by
      rw [← Finset.mul_sum]
    omega

private lemma leaf_reduction {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hconn : G.Connected) (hn : 3 ≤ Fintype.card V) (u v : V) (huv : u ≠ v)
    (hdeg : ∀ w : V, G.Adj u w → w = v)
    (ih : ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W),
      Fintype.card W < Fintype.card V → 1 < Fintype.card W → H.Connected →
      H.pathCoverNumber + H.largestInducedBipartiteSubgraphSize + 1 ≤
        2 * H.largestInducedForestSize) :
    G.pathCoverNumber + G.largestInducedBipartiteSubgraphSize + 1 ≤
      2 * G.largestInducedForestSize := by
  let W : Type := ({u}ᶜ : Set V)
  let H : SimpleGraph W := G.induce ({u}ᶜ : Set V)
  have hcardW : Fintype.card W = Fintype.card V - 1 := by
    have hfilt : Finset.univ.filter (fun x : V => x ≠ u) = Finset.univ.erase u := by
      ext x
      simp [Finset.mem_erase]
    have hcard1 : Fintype.card W = (Finset.univ.filter (fun x : V => x ≠ u)).card := by
      simp [W]
    rw [hcard1, hfilt, Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ]
  have hW_lt : Fintype.card W < Fintype.card V := by omega
  have hW_gt : 1 < Fintype.card W := by omega
  have huv_adj : G.Adj u v := by
    obtain ⟨p⟩ := hconn.preconnected u v
    cases p with
    | nil => exact (huv rfl).elim
    | @cons _ w _ huw _ =>
      have hw : w = v := hdeg w huw
      exact hw ▸ huw
  have hHconn : H.Connected := by
    classical
    have hdeg1 : G.degree u = 1 :=
      G.degree_eq_one_iff_existsUnique_adj.mpr ⟨v, huv_adj, hdeg⟩
    exact hconn.induce_compl_singleton_of_degree_eq_one hdeg1
  let emb : W ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  have hpath : G.pathCoverNumber ≤ H.pathCoverNumber + 1 := by
    have hne : { k | ∃ P : Finset (Finset W), P.card = k ∧ H.IsPathCover P }.Nonempty := by
      let P0 : Finset (Finset W) := Finset.univ.image (fun w : W => ({w} : Finset W))
      refine ⟨P0.card, P0, rfl, ?_, ?_, ?_⟩
      · intro s1 hs1 s2 hs2 hne12
        rcases Finset.mem_image.mp hs1 with ⟨w1, _, rfl⟩
        rcases Finset.mem_image.mp hs2 with ⟨w2, _, rfl⟩
        have hwne : w1 ≠ w2 := fun h => hne12 (by rw [h])
        exact Finset.disjoint_singleton.mpr hwne
      · intro w _
        refine Finset.mem_biUnion.mpr ⟨{w}, ?_, Finset.mem_singleton_self w⟩
        exact Finset.mem_image.mpr ⟨w, Finset.mem_univ w, rfl⟩
      · intro s hs
        rcases Finset.mem_image.mp hs with ⟨w, _, rfl⟩
        exact ⟨w, w, Walk.nil, Walk.IsPath.nil, by simp⟩
    obtain ⟨P, hPcard, hPdisj, hPcov, hPpaths⟩ := Nat.sInf_mem hne
    change P.card = H.pathCoverNumber at hPcard
    let P' : Finset (Finset V) := insert ({u} : Finset V) (P.image (Finset.map emb))
    have hu_notMem_map : ∀ s : Finset W, u ∉ s.map emb := by
      intro s hs
      rcases Finset.mem_map.mp hs with ⟨w, _, hw⟩
      exact w.prop hw
    have hP'cov : G.IsPathCover P' := by
      refine ⟨?_, ?_, ?_⟩
      · intro s1 hs1 s2 hs2 hne12
        rcases Finset.mem_insert.mp hs1 with rfl | hs1'
        · rcases Finset.mem_insert.mp hs2 with rfl | hs2'
          · exact (hne12 rfl).elim
          · rcases Finset.mem_image.mp hs2' with ⟨t2, _, rfl⟩
            exact Finset.disjoint_singleton_left.mpr (hu_notMem_map t2)
        · rcases Finset.mem_image.mp hs1' with ⟨t1, ht1, rfl⟩
          rcases Finset.mem_insert.mp hs2 with rfl | hs2'
          · exact Finset.disjoint_singleton_right.mpr (hu_notMem_map t1)
          · rcases Finset.mem_image.mp hs2' with ⟨t2, ht2, rfl⟩
            have htne : t1 ≠ t2 := fun h => hne12 (by rw [h])
            rw [Finset.disjoint_left]
            intro x hx1 hx2
            rcases Finset.mem_map.mp hx1 with ⟨w1, hw1, rfl⟩
            rcases Finset.mem_map.mp hx2 with ⟨w2, hw2, heq⟩
            have hweq : w2 = w1 := Subtype.val_injective heq
            exact Finset.disjoint_left.mp (hPdisj t1 ht1 t2 ht2 htne) hw1 (hweq ▸ hw2)
      · intro x _
        by_cases hxu : x = u
        · subst hxu
          exact Finset.mem_biUnion.mpr ⟨{x}, Finset.mem_insert_self _ _, Finset.mem_singleton_self x⟩
        · let xw : W := ⟨x, hxu⟩
          have hmem := hPcov (Finset.mem_univ xw)
          rcases Finset.mem_biUnion.mp hmem with ⟨t, ht, hxt⟩
          refine Finset.mem_biUnion.mpr ⟨t.map emb, ?_, ?_⟩
          · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨t, ht, rfl⟩)
          · exact Finset.mem_map.mpr ⟨xw, hxt, rfl⟩
      · intro s hs
        rcases Finset.mem_insert.mp hs with rfl | hs'
        · exact ⟨u, u, Walk.nil, Walk.IsPath.nil, by simp⟩
        · rcases Finset.mem_image.mp hs' with ⟨t, ht, rfl⟩
          rcases hPpaths t ht with ⟨a, b, p, hp, hteq⟩
          refine ⟨_, _, p.map (Embedding.induce ({u}ᶜ : Set V)).toHom, ?_, ?_⟩
          · exact (Walk.isPath_map_iff_of_injective Subtype.val_injective).mpr hp
          · ext x
            rw [Finset.mem_map, List.mem_toFinset, Walk.support_map, List.mem_map]
            simp only [hteq, List.mem_toFinset, emb, Function.Embedding.coeFn_mk]
            constructor
            · rintro ⟨w, hw, rfl⟩
              exact ⟨w, hw, rfl⟩
            · rintro ⟨w, hw, rfl⟩
              exact ⟨w, hw, rfl⟩
    have hle1 : G.pathCoverNumber ≤ P'.card := Nat.sInf_le ⟨P', rfl, hP'cov⟩
    have hle2 : P'.card ≤ (P.image (Finset.map emb)).card + 1 := Finset.card_insert_le _ _
    have hle3 : (P.image (Finset.map emb)).card ≤ P.card := Finset.card_image_le
    omega
  have hbip : G.largestInducedBipartiteSubgraphSize ≤ H.largestInducedBipartiteSubgraphSize + 1 := by
    change sSup { n | ∃ s : Finset V, (G.induce (s : Set V)).IsBipartite ∧ s.card = n } ≤
      H.largestInducedBipartiteSubgraphSize + 1
    apply csSup_le
    · refine ⟨0, ∅, ?_, rfl⟩
      rw [SimpleGraph.induce_isBipartite_iff_exists_coloring]
      exact ⟨fun _ => 0, by simp⟩
    · rintro n ⟨B, hBbip, rfl⟩
      let B' : Finset W := Finset.univ.filter (fun w : W => w.val ∈ B)
      have hB'map : B'.map emb = B.erase u := by
        ext x
        simp only [B', Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_erase, emb, Function.Embedding.coeFn_mk]
        constructor
        · rintro ⟨w, hw, rfl⟩
          exact ⟨w.prop, hw⟩
        · rintro ⟨hxu, hxB⟩
          exact ⟨⟨x, hxu⟩, hxB, rfl⟩
      have hB'card : B.card ≤ B'.card + 1 := by
        have h1 : B'.card = (B.erase u).card := by
          rw [← Finset.card_map emb, hB'map]
        rw [h1]
        by_cases huB : u ∈ B
        · rw [Finset.card_erase_add_one huB]
        · rw [Finset.erase_eq_of_notMem huB]
          omega
      have hB'bip : (H.induce (B' : Set W)).IsBipartite := by
        rw [SimpleGraph.induce_isBipartite_iff_exists_coloring] at hBbip ⊢
        rcases hBbip with ⟨c, hc⟩
        refine ⟨fun w => c w.val, ?_⟩
        intro x hx y hy hxy
        have hxB : x.val ∈ B := (Finset.mem_filter.mp hx).2
        have hyB : y.val ∈ B := (Finset.mem_filter.mp hy).2
        exact hc x.val hxB y.val hyB hxy
      have hB'le : B'.card ≤ H.largestInducedBipartiteSubgraphSize := by
        unfold SimpleGraph.largestInducedBipartiteSubgraphSize
        apply le_csSup
        · exact ⟨Fintype.card W, fun m ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
        · exact ⟨B', hB'bip, rfl⟩
      omega
  have hfor : H.largestInducedForestSize + 1 ≤ G.largestInducedForestSize := by
    have hneF : { n | ∃ s : Finset W, (H.induce (s : Set W)).IsAcyclic ∧ s.card = n }.Nonempty := by
      refine ⟨0, ∅, ?_, rfl⟩
      intro a _ _
      exact (Finset.notMem_empty a.val a.prop).elim
    have hbddF : BddAbove { n | ∃ s : Finset W, (H.induce (s : Set W)).IsAcyclic ∧ s.card = n } :=
      ⟨Fintype.card W, fun m ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
    obtain ⟨F', hF'acyc, hF'card⟩ := Nat.sSup_mem hneF hbddF
    change F'.card = H.largestInducedForestSize at hF'card
    let F : Finset V := insert u (F'.map emb)
    have hu_notMem_F' : u ∉ F'.map emb := by
      intro h
      rcases Finset.mem_map.mp h with ⟨w, _, hw⟩
      exact w.prop hw
    have hFcard : F.card = H.largestInducedForestSize + 1 := by
      rw [Finset.card_insert_of_notMem hu_notMem_F', Finset.card_map, hF'card]
    have hFacyc : (G.induce (F : Set V)).IsAcyclic := by
      intro a c hc
      let uF : (F : Set V) := ⟨u, Finset.mem_insert_self u _⟩
      by_cases hu_supp : uF ∈ c.support
      · let c' := c.rotate uF hu_supp
        have hc' : c'.IsCycle := (Walk.isCycle_rotate hu_supp).mpr hc
        have hlen3 : 3 ≤ c'.length := hc'.three_le_length
        have h0_lt : 0 < c'.length := by omega
        have hlast_lt : c'.length - 1 < c'.length := by omega
        have hadj1 : (G.induce (F : Set V)).Adj (c'.getVert 0) (c'.getVert 1) :=
          c'.adj_getVert_succ h0_lt
        have hadj2 : (G.induce (F : Set V)).Adj (c'.getVert (c'.length - 1))
            (c'.getVert (c'.length - 1 + 1)) := c'.adj_getVert_succ hlast_lt
        have h0_eq : c'.getVert 0 = uF := c'.getVert_zero
        have hlast_eq : c'.getVert (c'.length - 1 + 1) = uF := by
          have heq : c'.length - 1 + 1 = c'.length := by omega
          rw [heq, c'.getVert_length]
        have h1_val : (c'.getVert 1).val = v := by
          rw [h0_eq] at hadj1
          exact hdeg _ hadj1
        have h2_val : (c'.getVert (c'.length - 1)).val = v := by
          rw [hlast_eq] at hadj2
          exact hdeg _ hadj2.symm
        have heq_vert : c'.getVert 1 = c'.getVert (c'.length - 1) :=
          Subtype.ext (h1_val.trans h2_val.symm)
        have hnodup : c'.support.tail.Nodup := hc'.support_nodup
        have htail_len : c'.support.tail.length = c'.length := by
          simp [Walk.length_support]
        have hi0 : 0 < c'.support.tail.length := by omega
        have hi2 : c'.length - 2 < c'.support.tail.length := by omega
        have hget0 : c'.support.tail[0]'hi0 = c'.getVert 1 := by
          rw [List.getElem_tail, Walk.getVert_eq_support_getElem c' (by omega)]
        have hget2 : c'.support.tail[c'.length - 2]'hi2 = c'.getVert (c'.length - 1) := by
          rw [List.getElem_tail, Walk.getVert_eq_support_getElem c' (by omega)]
          congr 1
          omega
        have hidx : 0 = c'.length - 2 :=
          (List.Nodup.getElem_inj_iff hnodup).mp (by rw [hget0, hget2, heq_vert])
        omega
      · let cG := c.map (Embedding.induce (F : Set V)).toHom
        have hcG : cG.IsCycle :=
          (Walk.isCycle_map_iff_of_injective Subtype.val_injective).mpr hc
        have hsupp_ne_u : ∀ z ∈ cG.support, z ∈ ({u}ᶜ : Set V) := by
          intro z hz
          dsimp only [cG] at hz
          rw [Walk.support_map, List.mem_map] at hz
          rcases hz with ⟨x, hx, rfl⟩
          intro hxu
          apply hu_supp
          have hxeq : x = uF := Subtype.ext hxu
          exact hxeq ▸ hx
        let cW := cG.induce ({u}ᶜ : Set V) hsupp_ne_u
        have hcW : cW.IsCycle := by
          rw [← Walk.isCycle_map_iff_of_injective (f := (Embedding.induce ({u}ᶜ : Set V)).toHom)
            Subtype.val_injective, Walk.map_induce]
          exact hcG
        have hsupp_F' : ∀ w ∈ cW.support, w ∈ (F' : Set W) := by
          intro w hw
          have hw_val_mem : w.val ∈ cG.support := by
            have hmem : w.val ∈ (cW.map (Embedding.induce ({u}ᶜ : Set V)).toHom).support := by
              rw [Walk.support_map, List.mem_map]
              exact ⟨w, hw, rfl⟩
            have hmap : (cW.map (Embedding.induce ({u}ᶜ : Set V)).toHom).support = cG.support :=
              congrArg Walk.support (Walk.map_induce cG hsupp_ne_u)
            exact hmap ▸ hmem
          dsimp only [cG] at hw_val_mem
          rw [Walk.support_map, List.mem_map] at hw_val_mem
          rcases hw_val_mem with ⟨x, _, hxw⟩
          have hxF : x.val ∈ F := x.prop
          change x.val = w.val at hxw
          rw [hxw] at hxF
          rcases Finset.mem_insert.mp hxF with hwu | hwmap
          · exact (w.prop hwu).elim
          · rcases Finset.mem_map.mp hwmap with ⟨w', hw', hww'⟩
            have hweq : w' = w := Subtype.ext hww'
            exact hweq ▸ hw'
        let cF' := cW.induce (F' : Set W) hsupp_F'
        have hcF' : cF'.IsCycle := by
          rw [← Walk.isCycle_map_iff_of_injective (f := (Embedding.induce (F' : Set W)).toHom)
            Subtype.val_injective, Walk.map_induce]
          exact hcW
        exact hF'acyc cF' hcF'
    have hFle : F.card ≤ G.largestInducedForestSize := by
      unfold SimpleGraph.largestInducedForestSize
      apply le_csSup
      · exact ⟨Fintype.card V, fun m ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
      · exact ⟨F, hFacyc, rfl⟩
    omega
  have hIH := ih W H hW_lt hW_gt hHconn
  omega

private lemma ncvr_exists_pathCover_card_eq {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) :
    ∃ P : Finset (Finset α), P.card = G.pathCoverNumber ∧ G.IsPathCover P := by
  have hne : { k | ∃ P : Finset (Finset α), P.card = k ∧ G.IsPathCover P }.Nonempty := by
    refine ⟨(Finset.univ.image (fun x : α => ({x} : Finset α))).card,
      Finset.univ.image (fun x : α => ({x} : Finset α)), rfl, ?_, ?_, ?_⟩
    · intro s1 hs1 s2 hs2 hne_s
      rcases Finset.mem_image.mp hs1 with ⟨x1, _, rfl⟩
      rcases Finset.mem_image.mp hs2 with ⟨x2, _, rfl⟩
      rw [Finset.disjoint_singleton]
      intro hx
      exact hne_s (by rw [hx])
    · intro x _
      rw [Finset.mem_biUnion]
      exact ⟨{x}, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩, Finset.mem_singleton_self x⟩
    · intro s hs
      rcases Finset.mem_image.mp hs with ⟨x, _, rfl⟩
      exact ⟨x, x, Walk.nil, Walk.IsPath.nil, by simp⟩
  exact Nat.sInf_mem hne

private lemma ncvr_exists_bipartite_card_eq {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) :
    ∃ B : Finset α, (G.induce (B : Set α)).IsBipartite ∧
      B.card = G.largestInducedBipartiteSubgraphSize := by
  have hne : { n | ∃ s : Finset α, (G.induce (s : Set α)).IsBipartite ∧ s.card = n }.Nonempty := by
    refine ⟨0, ∅, ?_, rfl⟩
    rw [SimpleGraph.induce_isBipartite_iff_exists_coloring]
    exact ⟨fun _ => 0, by simp⟩
  have hbdd : BddAbove { n | ∃ s : Finset α, (G.induce (s : Set α)).IsBipartite ∧ s.card = n } :=
    ⟨Fintype.card α, fun _ ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
  exact Nat.sSup_mem hne hbdd

private lemma ncvr_exists_acyclic_card_eq {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) :
    ∃ F : Finset α, (G.induce (F : Set α)).IsAcyclic ∧
      F.card = G.largestInducedForestSize := by
  have hne : { n | ∃ s : Finset α, (G.induce (s : Set α)).IsAcyclic ∧ s.card = n }.Nonempty := by
    refine ⟨0, ∅, ?_, rfl⟩
    intro u
    exact False.elim (Finset.notMem_empty u.1 u.2)
  have hbdd : BddAbove { n | ∃ s : Finset α, (G.induce (s : Set α)).IsAcyclic ∧ s.card = n } :=
    ⟨Fintype.card α, fun _ ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
  exact Nat.sSup_mem hne hbdd

private lemma ncvr_card_le_largestInducedForestSize {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (F : Finset α) (hF : (G.induce (F : Set α)).IsAcyclic) :
    F.card ≤ G.largestInducedForestSize := by
  unfold SimpleGraph.largestInducedForestSize
  apply le_csSup
  · exact ⟨Fintype.card α, fun _ ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
  · exact ⟨F, hF, rfl⟩

private lemma ncvr_induce_isBipartite_mono {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {A B : Finset V} (hAB : A ⊆ B) (hB : (G.induce (B : Set V)).IsBipartite) :
    (G.induce (A : Set V)).IsBipartite := by
  rw [SimpleGraph.induce_isBipartite_iff_exists_coloring] at hB ⊢
  rcases hB with ⟨c, hc⟩
  exact ⟨c, fun u hu v hv huv => hc u (hAB hu) v (hAB hv) huv⟩

private lemma ncvr_card_le_induce_bipartite {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S T : Finset V) (hTS : T ⊆ S)
    (hT : (G.induce (T : Set V)).IsBipartite) :
    T.card ≤ (G.induce (S : Set V)).largestInducedBipartiteSubgraphSize := by
  let T' : Finset (S : Set V) := Finset.univ.filter (fun x : (S : Set V) => x.1 ∈ T)
  have hcard : T'.card = T.card := by
    have himg : T'.image Subtype.val = T := by
      ext x
      simp only [T', Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨y, _⟩, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, hTS hx⟩, hx, rfl⟩
    rw [← himg, Finset.card_image_of_injective _ Subtype.val_injective]
  rw [← hcard]
  unfold SimpleGraph.largestInducedBipartiteSubgraphSize
  apply le_csSup
  · exact ⟨Fintype.card (S : Set V), fun _ ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
  · refine ⟨T', ?_, rfl⟩
    rw [SimpleGraph.induce_isBipartite_iff_exists_coloring] at hT ⊢
    rcases hT with ⟨c, hc⟩
    refine ⟨fun x => c x.1, ?_⟩
    intro u hu v hv huv
    have hu' : u.1 ∈ T := (Finset.mem_filter.mp hu).2
    have hv' : v.1 ∈ T := (Finset.mem_filter.mp hv).2
    exact hc u.1 hu' v.1 hv' huv

private lemma ncvr_card_le_induce_forest {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S F : Finset V) (hFS : F ⊆ S)
    (hF : (G.induce (F : Set V)).IsAcyclic) :
    F.card ≤ (G.induce (S : Set V)).largestInducedForestSize := by
  let F' : Finset (S : Set V) := Finset.univ.filter (fun x : (S : Set V) => x.1 ∈ F)
  have hcard : F'.card = F.card := by
    have himg : F'.image Subtype.val = F := by
      ext x
      simp only [F', Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨y, _⟩, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, hFS hx⟩, hx, rfl⟩
    rw [← himg, Finset.card_image_of_injective _ Subtype.val_injective]
  rw [← hcard]
  apply ncvr_card_le_largestInducedForestSize
  intro u c hc
  let f : ((G.induce (S : Set V)).induce (F' : Set (S : Set V))) →g G.induce (F : Set V) :=
    { toFun := fun x => ⟨x.1.1, (Finset.mem_filter.mp x.2).2⟩
      map_rel' := fun hadj => hadj }
  have hfinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z => z.1) hab
  exact hF (c.map f) (hc.map hfinj)

private lemma ncvr_exists_acyclic_subset_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) :
    ∃ F : Finset V, F ⊆ S ∧ (G.induce (F : Set V)).IsAcyclic ∧
      F.card = (G.induce (S : Set V)).largestInducedForestSize := by
  obtain ⟨F', hF'ac, hF'card⟩ := ncvr_exists_acyclic_card_eq (G.induce (S : Set V))
  let F : Finset V := F'.image Subtype.val
  have hFS : F ⊆ S := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨⟨y, hy⟩, _, rfl⟩
    exact hy
  have hcard : F.card = F'.card := Finset.card_image_of_injective F' Subtype.val_injective
  refine ⟨F, hFS, ?_, hcard.trans hF'card⟩
  intro u c hc
  have hmemF' : ∀ x : (F : Set V), (⟨x.1, hFS x.2⟩ : (S : Set V)) ∈ F' := by
    intro x
    rcases Finset.mem_image.mp x.2 with ⟨⟨y, hy⟩, hyF', hyx⟩
    have heq : (⟨x.1, hFS x.2⟩ : (S : Set V)) = ⟨y, hy⟩ := Subtype.ext hyx.symm
    exact heq ▸ hyF'
  let f : G.induce (F : Set V) →g (G.induce (S : Set V)).induce (F' : Set (S : Set V)) :=
    { toFun := fun x => ⟨⟨x.1, hFS x.2⟩, hmemF' x⟩
      map_rel' := fun hadj => hadj }
  have hfinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z => z.1.1) hab
  exact hF'ac (c.map f) (hc.map hfinj)

private lemma ncvr_pathCoverNumber_le_sum_partition {V ι : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] [DecidableEq ι] (G : SimpleGraph V) (A : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (hcov : ∀ x : V, ∃ i : ι, x ∈ A i) :
    G.pathCoverNumber ≤ ∑ i : ι, (G.induce (A i : Set V)).pathCoverNumber := by
  choose P' hP'card hP'cov using fun i => ncvr_exists_pathCover_card_eq (G.induce (A i : Set V))
  let lift : ι → Finset (Finset V) := fun i => (P' i).image (fun s => s.image Subtype.val)
  let P : Finset (Finset V) := Finset.univ.biUnion lift
  have hPcov : G.IsPathCover P := by
    refine ⟨?_, ?_, ?_⟩
    · intro s1 hs1 s2 hs2 hne
      rcases Finset.mem_biUnion.mp hs1 with ⟨i, _, hi⟩
      rcases Finset.mem_biUnion.mp hs2 with ⟨j, _, hj⟩
      rcases Finset.mem_image.mp hi with ⟨s1', hs1', rfl⟩
      rcases Finset.mem_image.mp hj with ⟨s2', hs2', rfl⟩
      by_cases hij : i = j
      · subst hij
        have hne' : s1' ≠ s2' := fun h => hne (by rw [h])
        have hd := (hP'cov i).1 s1' hs1' s2' hs2' hne'
        rw [Finset.disjoint_left] at hd ⊢
        intro x hx1 hx2
        rcases Finset.mem_image.mp hx1 with ⟨a, ha, rfl⟩
        rcases Finset.mem_image.mp hx2 with ⟨b, hb, hab⟩
        have hba : a = b := Subtype.ext hab.symm
        exact hd ha (hba ▸ hb)
      · have hd := hdisj i j hij
        rw [Finset.disjoint_left] at hd ⊢
        intro x hx1 hx2
        rcases Finset.mem_image.mp hx1 with ⟨a, _, rfl⟩
        rcases Finset.mem_image.mp hx2 with ⟨b, _, hab⟩
        exact hd a.2 (hab ▸ b.2)
    · intro x _
      rcases hcov x with ⟨i, hxi⟩
      have hxmem : (⟨x, hxi⟩ : (A i : Set V)) ∈ (P' i).biUnion id :=
        (hP'cov i).2.1 (Finset.mem_univ _)
      rcases Finset.mem_biUnion.mp hxmem with ⟨s', hs', hxs'⟩
      rw [Finset.mem_biUnion]
      refine ⟨s'.image Subtype.val, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
        Finset.mem_image.mpr ⟨s', hs', rfl⟩⟩, ?_⟩
      exact Finset.mem_image.mpr ⟨⟨x, hxi⟩, hxs', rfl⟩
    · intro s hs
      rcases Finset.mem_biUnion.mp hs with ⟨i, _, hi⟩
      rcases Finset.mem_image.mp hi with ⟨s', hs', rfl⟩
      rcases (hP'cov i).2.2 s' hs' with ⟨u, v, p, hp, rfl⟩
      refine ⟨_, _, p.map (Embedding.induce (A i : Set V)).toHom,
        hp.map Subtype.val_injective, ?_⟩
      ext x
      simp only [Finset.mem_image, List.mem_toFinset, Walk.support_map, List.mem_map]
      rfl
  have hle : G.pathCoverNumber ≤ P.card := by
    unfold SimpleGraph.pathCoverNumber
    exact Nat.sInf_le ⟨P, rfl, hPcov⟩
  calc
    G.pathCoverNumber ≤ P.card := hle
    _ ≤ ∑ i : ι, (lift i).card := Finset.card_biUnion_le
    _ ≤ ∑ i : ι, (P' i).card := Finset.sum_le_sum (fun i _ => Finset.card_image_le)
    _ = ∑ i : ι, (G.induce (A i : Set V)).pathCoverNumber := by
      refine Finset.sum_congr rfl (fun i _ => hP'card i)

private lemma ncvr_pathCoverNumber_singleton_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) :
    (G.induce (({v} : Finset V) : Set V)).pathCoverNumber ≤ 1 := by
  unfold SimpleGraph.pathCoverNumber
  apply Nat.sInf_le
  refine ⟨{Finset.univ}, Finset.card_singleton _, ?_, ?_, ?_⟩
  · intro s1 hs1 s2 hs2 hne
    simp only [Finset.mem_singleton] at hs1 hs2
    exact (hne (hs1.trans hs2.symm)).elim
  · intro x _
    exact Finset.mem_biUnion.mpr ⟨Finset.univ, Finset.mem_singleton_self _, Finset.mem_univ x⟩
  · intro s hs
    simp only [Finset.mem_singleton] at hs
    subst hs
    let v0 : (({v} : Finset V) : Set V) := ⟨v, Finset.mem_singleton_self v⟩
    refine ⟨v0, v0, Walk.nil, Walk.IsPath.nil, ?_⟩
    ext x
    simp only [Finset.mem_univ, Walk.support_nil, List.toFinset_cons, List.toFinset_nil,
      insert_empty_eq, Finset.mem_singleton, true_iff]
    apply Subtype.ext
    exact Finset.mem_singleton.mp x.2

private lemma ncvr_walk_hits_cut_of_diff_comp {V : Type*} (G : SimpleGraph V) (v : V)
    {a b : V} (w : G.Walk a b) (ha : a ≠ v) (hb : b ≠ v)
    (hdiff : (G.induce ({v}ᶜ : Set V)).connectedComponentMk ⟨a, ha⟩ ≠
      (G.induce ({v}ᶜ : Set V)).connectedComponentMk ⟨b, hb⟩) :
    v ∈ w.support := by
  induction w with
  | nil => exact (hdiff rfl).elim
  | @cons x y z hxy w' ih =>
    by_cases hy : y = v
    · subst hy
      exact List.mem_cons_of_mem _ w'.start_mem_support
    · have hcomp : (G.induce ({v}ᶜ : Set V)).connectedComponentMk ⟨x, ha⟩ =
          (G.induce ({v}ᶜ : Set V)).connectedComponentMk ⟨y, hy⟩ :=
        ConnectedComponent.sound (Adj.reachable (G := G.induce ({v}ᶜ : Set V)) hxy)
      exact List.mem_cons_of_mem _ (ih hy hb (hcomp ▸ hdiff))

private lemma ncvr_exists_adj_cut_in_comp {V : Type*} (G : SimpleGraph V) (v : V)
    {a b : V} (w : G.Walk a b) (ha : a ≠ v) (hb : b = v) :
    ∃ (u : V) (hu : u ≠ v),
      (G.induce ({v}ᶜ : Set V)).connectedComponentMk ⟨u, hu⟩ =
        (G.induce ({v}ᶜ : Set V)).connectedComponentMk ⟨a, ha⟩ ∧
      G.Adj u v := by
  induction w with
  | nil => exact (ha hb).elim
  | @cons x y z hxy w' ih =>
    by_cases hy : y = v
    · subst hy
      exact ⟨x, ha, rfl, hxy⟩
    · have hcomp : (G.induce ({v}ᶜ : Set V)).connectedComponentMk ⟨x, ha⟩ =
          (G.induce ({v}ᶜ : Set V)).connectedComponentMk ⟨y, hy⟩ :=
        ConnectedComponent.sound (Adj.reachable (G := G.induce ({v}ᶜ : Set V)) hxy)
      obtain ⟨u, hu, hucomp, huv⟩ := ih hy hb
      exact ⟨u, hu, hucomp.trans hcomp.symm, huv⟩

private lemma nontrivial_cut_vertex_reduction {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected) (hn : 3 ≤ Fintype.card V) (v : V)
    (hcut : ¬ (G.induce ({v}ᶜ : Set V)).Connected)
    (hnoleaf : ∀ u : V, u ≠ v → ∃ w : V, w ≠ v ∧ G.Adj u w)
    (ih : ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W),
      Fintype.card W < Fintype.card V → 1 < Fintype.card W → H.Connected →
      H.pathCoverNumber + H.largestInducedBipartiteSubgraphSize + 1 ≤
        2 * H.largestInducedForestSize) :
    G.pathCoverNumber + G.largestInducedBipartiteSubgraphSize + 1 ≤
      2 * G.largestInducedForestSize := by
  classical
  let H := G.induce ({v}ᶜ : Set V)
  have hHnonempty : Nonempty ({v}ᶜ : Set V) := by
    have hlt : ({v} : Finset V).card < Fintype.card V := by simp; omega
    obtain ⟨u, hu⟩ : ∃ u : V, u ∉ ({v} : Finset V) := by
      by_contra hall
      push Not at hall
      have hle : (Finset.univ : Finset V).card ≤ ({v} : Finset V).card :=
        Finset.card_le_card (fun x _ => hall x)
      rw [Finset.card_univ] at hle
      omega
    exact ⟨⟨u, by simpa using hu⟩⟩
  have hcomp_ge2 : 2 ≤ Fintype.card H.ConnectedComponent := by
    by_contra hlt
    have hle1 : Fintype.card H.ConnectedComponent ≤ 1 := by omega
    have hsub : Subsingleton H.ConnectedComponent := Fintype.card_le_one_iff_subsingleton.mp hle1
    apply hcut
    have := hHnonempty
    exact ⟨fun x y => ConnectedComponent.exact (Subsingleton.elim _ _)⟩
  let D : H.ConnectedComponent → Finset V := fun C =>
    Finset.univ.filter (fun u => ∃ hu : u ≠ v, H.connectedComponentMk ⟨u, hu⟩ = C)
  let E : H.ConnectedComponent → Finset V := fun C => insert v (D C)
  have hv_notMem_D : ∀ C, v ∉ D C := by
    intro C hv
    rcases (Finset.mem_filter.mp hv).2 with ⟨hvv, _⟩
    exact hvv rfl
  have hD_disj : ∀ C₁ C₂, C₁ ≠ C₂ → Disjoint (D C₁) (D C₂) := by
    intro C₁ C₂ hne
    rw [Finset.disjoint_left]
    intro u hu1 hu2
    rcases (Finset.mem_filter.mp hu1).2 with ⟨hu, h1⟩
    rcases (Finset.mem_filter.mp hu2).2 with ⟨_, h2⟩
    exact hne (h1.symm.trans h2)
  have hD_mem_of_ne : ∀ u : V, (hu : u ≠ v) → u ∈ D (H.connectedComponentMk ⟨u, hu⟩) := by
    intro u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu, rfl⟩
  have hD_card_ge2 : ∀ C, 2 ≤ (D C).card := by
    intro C
    obtain ⟨⟨u, hu⟩, hCu⟩ := C.exists_rep
    have hu' : u ≠ v := Set.mem_compl_singleton_iff.mp hu
    obtain ⟨w, hw, huw⟩ := hnoleaf u hu'
    have hwu : w ≠ u := (G.ne_of_adj huw).symm
    have hCu' : H.connectedComponentMk ⟨u, hu'⟩ = C := hCu
    have hCw : H.connectedComponentMk ⟨w, hw⟩ = C := by
      have hadjH : H.Adj ⟨u, hu'⟩ ⟨w, hw⟩ := huw
      exact (ConnectedComponent.sound (Adj.reachable hadjH)).symm.trans hCu'
    have hsub : ({u, w} : Finset V) ⊆ D C := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu', hCu'⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw, hCw⟩
    calc
      2 = ({u, w} : Finset V).card := (Finset.card_pair hwu.symm).symm
      _ ≤ (D C).card := Finset.card_le_card hsub
  have hD_card_lt : ∀ C, (D C).card < Fintype.card V := by
    intro C
    have hlt : (D C).card < (insert v (D C)).card := by
      rw [Finset.card_insert_of_notMem (hv_notMem_D C)]
      omega
    exact lt_of_lt_of_le hlt (Finset.card_le_univ _)
  have hD_conn : ∀ C, (G.induce (D C : Set V)).Connected := by
    intro C
    obtain ⟨⟨u0, hu0⟩, hCu0⟩ := C.exists_rep
    have hu0' : u0 ≠ v := Set.mem_compl_singleton_iff.mp hu0
    have hne : Nonempty (D C : Set V) :=
      ⟨⟨u0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu0', hCu0⟩⟩⟩
    have := hne
    refine ⟨fun x y => ?_⟩
    rcases (Finset.mem_filter.mp x.2).2 with ⟨hx, hCx⟩
    rcases (Finset.mem_filter.mp y.2).2 with ⟨hy, hCy⟩
    have hreach : H.Reachable ⟨x.1, hx⟩ ⟨y.1, hy⟩ :=
      ConnectedComponent.exact (hCx.trans hCy.symm)
    obtain ⟨p⟩ := hreach
    have hp_mem : ∀ z ∈ p.support, z.1 ∈ D C := by
      intro z hz
      have hxz : H.Reachable ⟨x.1, hx⟩ z := ⟨p.takeUntil z hz⟩
      have hCz : H.connectedComponentMk z = C :=
        (ConnectedComponent.sound hxz).symm.trans hCx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Set.mem_compl_singleton_iff.mp z.2, hCz⟩
    let pG := p.map (Embedding.induce ({v}ᶜ : Set V)).toHom
    have hpG_mem : ∀ w ∈ pG.support, w ∈ (D C : Set V) := by
      intro w hw
      dsimp only [pG] at hw
      rw [Walk.support_map, List.mem_map] at hw
      rcases hw with ⟨z, hz, hzw⟩
      exact hzw ▸ hp_mem z hz
    exact ⟨pG.induce (D C : Set V) hpG_mem⟩
  have hE_conn : ∀ C, (G.induce (E C : Set V)).Connected := by
    intro C
    have hvE : v ∈ E C := Finset.mem_insert_self v (D C)
    obtain ⟨⟨u0, hu0⟩, hCu0⟩ := C.exists_rep
    have hu0' : u0 ≠ v := Set.mem_compl_singleton_iff.mp hu0
    obtain ⟨w0⟩ := hconn.preconnected u0 v
    obtain ⟨u, hu, hCu, huv⟩ := ncvr_exists_adj_cut_in_comp G v w0 hu0' rfl
    have huD : u ∈ D C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu, hCu.trans hCu0⟩
    have huE : u ∈ E C := Finset.mem_insert_of_mem huD
    have hreach_v : ∀ x : (E C : Set V), (G.induce (E C : Set V)).Reachable x ⟨v, hvE⟩ := by
      intro x
      by_cases hxv : x.1 = v
      · have hx_eq : x = ⟨v, hvE⟩ := Subtype.ext hxv
        exact hx_eq ▸ Reachable.refl _
      · have hxD : x.1 ∈ D C := by
          rcases Finset.mem_insert.mp x.2 with hxv' | hxD
          · exact (hxv hxv').elim
          · exact hxD
        obtain ⟨px⟩ := (hD_conn C).preconnected ⟨x.1, hxD⟩ ⟨u, huD⟩
        let f : G.induce (D C : Set V) →g G.induce (E C : Set V) :=
          { toFun := fun z => ⟨z.1, Finset.mem_insert_of_mem z.2⟩
            map_rel' := fun hadj => hadj }
        have hxu : (G.induce (E C : Set V)).Reachable x ⟨u, huE⟩ := ⟨px.map f⟩
        have huvE : (G.induce (E C : Set V)).Adj ⟨u, huE⟩ ⟨v, hvE⟩ := huv
        exact hxu.trans (Adj.reachable huvE)
    have : Nonempty (E C : Set V) := ⟨⟨v, hvE⟩⟩
    exact ⟨fun x y => (hreach_v x).trans (hreach_v y).symm⟩
  have hE_card_ge3 : ∀ C, 3 ≤ (E C).card := by
    intro C
    rw [Finset.card_insert_of_notMem (hv_notMem_D C)]
    have := hD_card_ge2 C
    omega
  have hE_card_lt : ∀ C, (E C).card < Fintype.card V := by
    intro C
    have hex : ∃ C' : H.ConnectedComponent, C' ≠ C := by
      by_contra hall
      push Not at hall
      have hsub : Subsingleton H.ConnectedComponent := ⟨fun a b => (hall a).trans (hall b).symm⟩
      have hle1 : Fintype.card H.ConnectedComponent ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr hsub
      omega
    rcases hex with ⟨C', hC'⟩
    have hdisj : Disjoint (E C) (D C') := by
      rw [Finset.disjoint_insert_left]
      exact ⟨hv_notMem_D C', hD_disj C C' hC'.symm⟩
    have hle : (E C).card + (D C').card ≤ Fintype.card V := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_univ _
    have h2 := hD_card_ge2 C'
    omega
  have hIH_D : ∀ C, (G.induce (D C : Set V)).pathCoverNumber +
      (G.induce (D C : Set V)).largestInducedBipartiteSubgraphSize + 1 ≤
      2 * (G.induce (D C : Set V)).largestInducedForestSize := by
    intro C
    have hcard : Fintype.card (D C : Set V) = (D C).card := Fintype.card_coe (D C)
    exact ih (D C : Set V) (G.induce (D C : Set V))
      (hcard ▸ hD_card_lt C) (by have := hD_card_ge2 C; omega) (hD_conn C)
  have hIH_E : ∀ C, (G.induce (E C : Set V)).pathCoverNumber +
      (G.induce (E C : Set V)).largestInducedBipartiteSubgraphSize + 1 ≤
      2 * (G.induce (E C : Set V)).largestInducedForestSize := by
    intro C
    have hcard : Fintype.card (E C : Set V) = (E C).card := Fintype.card_coe (E C)
    exact ih (E C : Set V) (G.induce (E C : Set V))
      (hcard ▸ hE_card_lt C) (by have := hE_card_ge3 C; omega) (hE_conn C)
  have hp_all : G.pathCoverNumber ≤
      1 + ∑ C : H.ConnectedComponent, (G.induce (D C : Set V)).pathCoverNumber := by
    let A : Option H.ConnectedComponent → Finset V
      | none => {v}
      | some C => D C
    have hdisjA : ∀ i j, i ≠ j → Disjoint (A i) (A j) := by
      intro i j hij
      cases i with
      | none =>
        cases j with
        | none => exact (hij rfl).elim
        | some C => exact Finset.disjoint_singleton_left.mpr (hv_notMem_D C)
      | some C₁ =>
        cases j with
        | none => exact Finset.disjoint_singleton_right.mpr (hv_notMem_D C₁)
        | some C₂ => exact hD_disj C₁ C₂ (fun h => hij (congrArg some h))
    have hcovA : ∀ x : V, ∃ i : Option H.ConnectedComponent, x ∈ A i := by
      intro x
      by_cases hx : x = v
      · exact ⟨none, by simp [A, hx]⟩
      · exact ⟨some (H.connectedComponentMk ⟨x, hx⟩), hD_mem_of_ne x hx⟩
    have hsum := ncvr_pathCoverNumber_le_sum_partition G A hdisjA hcovA
    rw [Fintype.sum_option] at hsum
    dsimp only [A] at hsum
    have hsing := ncvr_pathCoverNumber_singleton_le G v
    omega
  have hp_merge : ∀ C₀ : H.ConnectedComponent, G.pathCoverNumber ≤
      (G.induce (E C₀ : Set V)).pathCoverNumber +
        ∑ C ∈ Finset.univ.erase C₀, (G.induce (D C : Set V)).pathCoverNumber := by
    intro C₀
    let A : H.ConnectedComponent → Finset V := fun C => if C = C₀ then E C₀ else D C
    have hdisjA : ∀ C₁ C₂, C₁ ≠ C₂ → Disjoint (A C₁) (A C₂) := by
      intro C₁ C₂ hne
      simp only [A]
      split_ifs with h1 h2 h2
      · exact (hne (h1.trans h2.symm)).elim
      · subst h1
        rw [Finset.disjoint_insert_left]
        exact ⟨hv_notMem_D C₂, hD_disj C₁ C₂ hne⟩
      · subst h2
        rw [Finset.disjoint_insert_right]
        exact ⟨hv_notMem_D C₁, hD_disj C₁ C₂ hne⟩
      · exact hD_disj C₁ C₂ hne
    have hcovA : ∀ x : V, ∃ C : H.ConnectedComponent, x ∈ A C := by
      intro x
      by_cases hx : x = v
      · refine ⟨C₀, ?_⟩
        simp [A, E, hx]
      · refine ⟨H.connectedComponentMk ⟨x, hx⟩, ?_⟩
        simp only [A]
        split_ifs with hC
        · rw [← hC]
          exact Finset.mem_insert_of_mem (hD_mem_of_ne x hx)
        · exact hD_mem_of_ne x hx
    have hsum := ncvr_pathCoverNumber_le_sum_partition G A hdisjA hcovA
    have hcongr : ∀ S T : Finset V, S = T →
        (G.induce (S : Set V)).pathCoverNumber = (G.induce (T : Set V)).pathCoverNumber := by
      intro S T hST
      subst hST
      rfl
    have hsplit : ∑ C : H.ConnectedComponent, (G.induce (A C : Set V)).pathCoverNumber =
        (G.induce (E C₀ : Set V)).pathCoverNumber +
          ∑ C ∈ Finset.univ.erase C₀, (G.induce (D C : Set V)).pathCoverNumber := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ C₀)]
      congr 1
      · apply hcongr
        simp [A]
      · refine Finset.sum_congr rfl (fun C hC => ?_)
        have hne : C ≠ C₀ := (Finset.mem_erase.mp hC).1
        apply hcongr
        simp [A, hne]
    omega
  have hb_all : G.largestInducedBipartiteSubgraphSize ≤
      1 + ∑ C : H.ConnectedComponent,
        (G.induce (D C : Set V)).largestInducedBipartiteSubgraphSize := by
    obtain ⟨B, hBbip, hBcard⟩ := ncvr_exists_bipartite_card_eq G
    have hBsub : B ⊆ insert v (Finset.univ.biUnion (fun C : H.ConnectedComponent => B ∩ D C)) := by
      intro x hx
      by_cases hxv : x = v
      · subst hxv
        exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        rw [Finset.mem_biUnion]
        exact ⟨H.connectedComponentMk ⟨x, hxv⟩, Finset.mem_univ _,
          Finset.mem_inter.mpr ⟨hx, hD_mem_of_ne x hxv⟩⟩
    have hle1 : B.card ≤ 1 + (Finset.univ.biUnion (fun C => B ∩ D C)).card := by
      have h1 := Finset.card_le_card hBsub
      have h2 := Finset.card_insert_le v (Finset.univ.biUnion (fun C => B ∩ D C))
      omega
    have hle2 : (Finset.univ.biUnion (fun C => B ∩ D C)).card ≤
        ∑ C : H.ConnectedComponent, (B ∩ D C).card := Finset.card_biUnion_le
    have hle3 : ∑ C : H.ConnectedComponent, (B ∩ D C).card ≤
        ∑ C : H.ConnectedComponent,
          (G.induce (D C : Set V)).largestInducedBipartiteSubgraphSize := by
      refine Finset.sum_le_sum (fun C _ => ?_)
      exact ncvr_card_le_induce_bipartite G (D C) (B ∩ D C) Finset.inter_subset_right
        (ncvr_induce_isBipartite_mono Finset.inter_subset_left hBbip)
    omega
  have hf_all : ∑ C : H.ConnectedComponent,
      (G.induce (D C : Set V)).largestInducedForestSize ≤ G.largestInducedForestSize := by
    choose F hFD hFac hFcard using fun C => ncvr_exists_acyclic_subset_eq G (D C)
    let U : Finset V := Finset.univ.biUnion F
    have hFdisj : ∀ C₁ C₂, C₁ ≠ C₂ → Disjoint (F C₁) (F C₂) := fun C₁ C₂ hne =>
      Disjoint.mono (hFD C₁) (hFD C₂) (hD_disj C₁ C₂ hne)
    have hUcard : U.card = ∑ C : H.ConnectedComponent, (F C).card :=
      Finset.card_biUnion (fun C₁ _ C₂ _ hne => hFdisj C₁ C₂ hne)
    have hUac : (G.induce (U : Set V)).IsAcyclic := by
      intro u c hc
      rcases Finset.mem_biUnion.mp u.2 with ⟨C, _, huC⟩
      have hstay : ∀ {a b : (U : Set V)} (w : (G.induce (U : Set V)).Walk a b),
          a.1 ∈ F C → ∀ z ∈ w.support, z.1 ∈ F C := by
        intro a b w
        induction w with
        | nil =>
          intro ha z hz
          simp only [Walk.support_nil, List.mem_singleton] at hz
          exact hz ▸ ha
        | @cons x y _ hxy w' ihw =>
          intro hx z hz
          have hyC : y.1 ∈ F C := by
            rcases Finset.mem_biUnion.mp y.2 with ⟨C', _, hyC'⟩
            by_cases hCC' : C' = C
            · exact hCC' ▸ hyC'
            · have hxD : x.1 ∈ D C := hFD C hx
              have hyD : y.1 ∈ D C' := hFD C' hyC'
              rcases (Finset.mem_filter.mp hxD).2 with ⟨hxne, hCx⟩
              rcases (Finset.mem_filter.mp hyD).2 with ⟨hyne, hCy⟩
              have heq : H.connectedComponentMk ⟨x.1, hxne⟩ =
                  H.connectedComponentMk ⟨y.1, hyne⟩ :=
                ConnectedComponent.sound (Adj.reachable (G := H) hxy)
              exact (hCC' (hCy.symm.trans (heq.symm.trans hCx))).elim
          rcases List.mem_cons.mp hz with rfl | hz'
          · exact hx
          · exact ihw hyC z hz'
      let cG := c.map (Embedding.induce (U : Set V)).toHom
      have hcG_cyc : cG.IsCycle := hc.map Subtype.val_injective
      have hcG_mem : ∀ x ∈ cG.support, x ∈ (F C : Set V) := by
        intro x hx
        dsimp only [cG] at hx
        rw [Walk.support_map, List.mem_map] at hx
        rcases hx with ⟨z, hz, hzx⟩
        exact hzx ▸ hstay c huC z hz
      let cF := cG.induce (F C : Set V) hcG_mem
      have hcF_cyc : cF.IsCycle := by
        apply Walk.IsCycle.of_map (f := (Embedding.induce (F C : Set V)).toHom)
        rw [Walk.map_induce]
        exact hcG_cyc
      exact hFac C cF hcF_cyc
    have hle := ncvr_card_le_largestInducedForestSize G U hUac
    have hsum_eq : ∑ C : H.ConnectedComponent, (F C).card =
        ∑ C : H.ConnectedComponent, (G.induce (D C : Set V)).largestInducedForestSize :=
      Finset.sum_congr rfl (fun C _ => hFcard C)
    omega
  by_cases hcomp3 : 3 ≤ Fintype.card H.ConnectedComponent
  · have hsum_ih : ∑ C : H.ConnectedComponent,
        ((G.induce (D C : Set V)).pathCoverNumber +
          (G.induce (D C : Set V)).largestInducedBipartiteSubgraphSize + 1) ≤
        ∑ C : H.ConnectedComponent,
          2 * (G.induce (D C : Set V)).largestInducedForestSize :=
      Finset.sum_le_sum (fun C _ => hIH_D C)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
      ← Finset.mul_sum] at hsum_ih
    omega
  · have hcomp2 : Fintype.card H.ConnectedComponent = 2 := by omega
    obtain ⟨C₁, C₂, hne12, huniv⟩ : ∃ C₁ C₂ : H.ConnectedComponent,
        C₁ ≠ C₂ ∧ (Finset.univ : Finset H.ConnectedComponent) = {C₁, C₂} := by
      obtain ⟨C₁, C₂, hne⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card H.ConnectedComponent)
      refine ⟨C₁, C₂, hne, ?_⟩
      apply Eq.symm
      apply Finset.eq_univ_of_card
      rw [Finset.card_pair hne, hcomp2]
    have hsum_pair : ∀ f : H.ConnectedComponent → ℕ,
        ∑ C : H.ConnectedComponent, f C = f C₁ + f C₂ := by
      intro f
      rw [show (∑ C : H.ConnectedComponent, f C) = ∑ C ∈ Finset.univ, f C from rfl,
        huniv, Finset.sum_pair hne12]
    have hD1 := hIH_D C₁
    have hD2 := hIH_D C₂
    have hE1 := hIH_E C₁
    have hE2 := hIH_E C₂
    have hf12 : (G.induce (D C₁ : Set V)).largestInducedForestSize +
        (G.induce (D C₂ : Set V)).largestInducedForestSize ≤ G.largestInducedForestSize := by
      rwa [hsum_pair] at hf_all
    have hp_all2 : G.pathCoverNumber ≤
        1 + ((G.induce (D C₁ : Set V)).pathCoverNumber +
          (G.induce (D C₂ : Set V)).pathCoverNumber) := by
      rwa [hsum_pair] at hp_all
    have hb_all2 : G.largestInducedBipartiteSubgraphSize ≤
        1 + ((G.induce (D C₁ : Set V)).largestInducedBipartiteSubgraphSize +
          (G.induce (D C₂ : Set V)).largestInducedBipartiteSubgraphSize) := by
      rwa [hsum_pair] at hb_all
    by_cases hp_small : G.pathCoverNumber ≤
        (G.induce (D C₁ : Set V)).pathCoverNumber + (G.induce (D C₂ : Set V)).pathCoverNumber
    · omega
    by_cases hb_small : G.largestInducedBipartiteSubgraphSize ≤
        (G.induce (D C₁ : Set V)).largestInducedBipartiteSubgraphSize +
          (G.induce (D C₂ : Set V)).largestInducedBipartiteSubgraphSize
    · omega
    have herase1 : (Finset.univ : Finset H.ConnectedComponent).erase C₁ = {C₂} := by
      rw [huniv, Finset.erase_insert (by simp [hne12])]
    have herase2 : (Finset.univ : Finset H.ConnectedComponent).erase C₂ = {C₁} := by
      rw [huniv, Finset.pair_comm, Finset.erase_insert (by simp [hne12.symm])]
    have hpE1 : (G.induce (D C₁ : Set V)).pathCoverNumber + 1 ≤
        (G.induce (E C₁ : Set V)).pathCoverNumber := by
      have hm := hp_merge C₁
      rw [herase1, Finset.sum_singleton] at hm
      omega
    have hpE2 : (G.induce (D C₂ : Set V)).pathCoverNumber + 1 ≤
        (G.induce (E C₂ : Set V)).pathCoverNumber := by
      have hm := hp_merge C₂
      rw [herase2, Finset.sum_singleton] at hm
      omega
    have hbE : (G.induce (D C₁ : Set V)).largestInducedBipartiteSubgraphSize + 1 ≤
          (G.induce (E C₁ : Set V)).largestInducedBipartiteSubgraphSize ∧
        (G.induce (D C₂ : Set V)).largestInducedBipartiteSubgraphSize + 1 ≤
          (G.induce (E C₂ : Set V)).largestInducedBipartiteSubgraphSize := by
      obtain ⟨B, hBbip, hBcard⟩ := ncvr_exists_bipartite_card_eq G
      have hB1_le : (B ∩ D C₁).card ≤
          (G.induce (D C₁ : Set V)).largestInducedBipartiteSubgraphSize :=
        ncvr_card_le_induce_bipartite G (D C₁) (B ∩ D C₁) Finset.inter_subset_right
          (ncvr_induce_isBipartite_mono Finset.inter_subset_left hBbip)
      have hB2_le : (B ∩ D C₂).card ≤
          (G.induce (D C₂ : Set V)).largestInducedBipartiteSubgraphSize :=
        ncvr_card_le_induce_bipartite G (D C₂) (B ∩ D C₂) Finset.inter_subset_right
          (ncvr_induce_isBipartite_mono Finset.inter_subset_left hBbip)
      have hBsub : B ⊆ (B ∩ {v}) ∪ ((B ∩ D C₁) ∪ (B ∩ D C₂)) := by
        intro x hx
        by_cases hxv : x = v
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, by simp [hxv]⟩)
        · apply Finset.mem_union_right
          have hCmem : H.connectedComponentMk ⟨x, hxv⟩ ∈ ({C₁, C₂} : Finset H.ConnectedComponent) :=
            huniv ▸ Finset.mem_univ _
          simp only [Finset.mem_insert, Finset.mem_singleton] at hCmem
          rcases hCmem with h1 | h2
          · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, h1 ▸ hD_mem_of_ne x hxv⟩)
          · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hx, h2 ▸ hD_mem_of_ne x hxv⟩)
      have hB_le_sum : B.card ≤ (B ∩ {v}).card + (B ∩ D C₁).card + (B ∩ D C₂).card := by
        have h1 := Finset.card_le_card hBsub
        have h2 := Finset.card_union_le (B ∩ {v}) ((B ∩ D C₁) ∪ (B ∩ D C₂))
        have h3 := Finset.card_union_le (B ∩ D C₁) (B ∩ D C₂)
        omega
      have hv_card_le : (B ∩ {v}).card ≤ 1 := by
        have := Finset.card_le_card (Finset.inter_subset_right (s₁ := B) (s₂ := {v}))
        simpa using this
      have hvB : v ∈ B := by
        by_contra hnv
        have h0 : (B ∩ {v}).card = 0 := by
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro x hx
          rcases Finset.mem_inter.mp hx with ⟨hxB, hxv⟩
          exact hnv (Finset.mem_singleton.mp hxv ▸ hxB)
        omega
      have hB1_eq : (B ∩ D C₁).card =
          (G.induce (D C₁ : Set V)).largestInducedBipartiteSubgraphSize := by omega
      have hB2_eq : (B ∩ D C₂).card =
          (G.induce (D C₂ : Set V)).largestInducedBipartiteSubgraphSize := by omega
      have hBE1 : B ∩ E C₁ = insert v (B ∩ D C₁) := by
        ext x
        simp only [E, Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨hxB, rfl | hxD⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hxB, hxD⟩
        · rintro (rfl | ⟨hxB, hxD⟩)
          · exact ⟨hvB, Or.inl rfl⟩
          · exact ⟨hxB, Or.inr hxD⟩
      have hBE2 : B ∩ E C₂ = insert v (B ∩ D C₂) := by
        ext x
        simp only [E, Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨hxB, rfl | hxD⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hxB, hxD⟩
        · rintro (rfl | ⟨hxB, hxD⟩)
          · exact ⟨hvB, Or.inl rfl⟩
          · exact ⟨hxB, Or.inr hxD⟩
      have hv_not_BD1 : v ∉ B ∩ D C₁ := fun h => hv_notMem_D C₁ (Finset.mem_inter.mp h).2
      have hv_not_BD2 : v ∉ B ∩ D C₂ := fun h => hv_notMem_D C₂ (Finset.mem_inter.mp h).2
      constructor
      · have hle := ncvr_card_le_induce_bipartite G (E C₁) (B ∩ E C₁) Finset.inter_subset_right
          (ncvr_induce_isBipartite_mono Finset.inter_subset_left hBbip)
        rw [hBE1, Finset.card_insert_of_notMem hv_not_BD1, hB1_eq] at hle
        exact hle
      · have hle := ncvr_card_le_induce_bipartite G (E C₂) (B ∩ E C₂) Finset.inter_subset_right
          (ncvr_induce_isBipartite_mono Finset.inter_subset_left hBbip)
        rw [hBE2, Finset.card_insert_of_notMem hv_not_BD2, hB2_eq] at hle
        exact hle
    rcases hbE with ⟨hbE1, hbE2⟩
    by_cases hfE1 : (G.induce (E C₁ : Set V)).largestInducedForestSize ≤
        (G.induce (D C₁ : Set V)).largestInducedForestSize
    · omega
    by_cases hfE2 : (G.induce (E C₂ : Set V)).largestInducedForestSize ≤
        (G.induce (D C₂ : Set V)).largestInducedForestSize
    · omega
    obtain ⟨F₁, hF₁E, hF₁ac, hF₁card⟩ := ncvr_exists_acyclic_subset_eq G (E C₁)
    obtain ⟨F₂, hF₂E, hF₂ac, hF₂card⟩ := ncvr_exists_acyclic_subset_eq G (E C₂)
    have hvF₁ : v ∈ F₁ := by
      by_contra hnv
      have hF₁D : F₁ ⊆ D C₁ := by
        intro x hx
        rcases Finset.mem_insert.mp (hF₁E hx) with rfl | hxD
        · exact (hnv hx).elim
        · exact hxD
      have hle := ncvr_card_le_induce_forest G (D C₁) F₁ hF₁D hF₁ac
      omega
    have hvF₂ : v ∈ F₂ := by
      by_contra hnv
      have hF₂D : F₂ ⊆ D C₂ := by
        intro x hx
        rcases Finset.mem_insert.mp (hF₂E hx) with rfl | hxD
        · exact (hnv hx).elim
        · exact hxD
      have hle := ncvr_card_le_induce_forest G (D C₂) F₂ hF₂D hF₂ac
      omega
    have hFinter : F₁ ∩ F₂ = {v} := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_singleton]
      constructor
      · rintro ⟨hx1, hx2⟩
        rcases Finset.mem_insert.mp (hF₁E hx1) with rfl | hxD1
        · rfl
        · rcases Finset.mem_insert.mp (hF₂E hx2) with rfl | hxD2
          · rfl
          · exact (Finset.disjoint_left.mp (hD_disj C₁ C₂ hne12) hxD1 hxD2).elim
      · rintro rfl
        exact ⟨hvF₁, hvF₂⟩
    have hFunion_card : (F₁ ∪ F₂).card + 1 = F₁.card + F₂.card := by
      have h := Finset.card_union_add_card_inter F₁ F₂
      rw [hFinter, Finset.card_singleton] at h
      exact h
    have hFunion_ac : (G.induce ((F₁ ∪ F₂ : Finset V) : Set V)).IsAcyclic := by
      intro u c hc
      by_cases hall1 : ∀ z ∈ c.support, z.1 ∈ F₁
      · let cG := c.map (Embedding.induce ((F₁ ∪ F₂ : Finset V) : Set V)).toHom
        have hcG_cyc : cG.IsCycle := hc.map Subtype.val_injective
        have hcG_mem : ∀ x ∈ cG.support, x ∈ (F₁ : Set V) := by
          intro x hx
          dsimp only [cG] at hx
          rw [Walk.support_map, List.mem_map] at hx
          rcases hx with ⟨z, hz, hzx⟩
          exact hzx ▸ hall1 z hz
        let c1 := cG.induce (F₁ : Set V) hcG_mem
        have hc1_cyc : c1.IsCycle := by
          apply Walk.IsCycle.of_map (f := (Embedding.induce (F₁ : Set V)).toHom)
          rw [Walk.map_induce]
          exact hcG_cyc
        exact hF₁ac c1 hc1_cyc
      by_cases hall2 : ∀ z ∈ c.support, z.1 ∈ F₂
      · let cG := c.map (Embedding.induce ((F₁ ∪ F₂ : Finset V) : Set V)).toHom
        have hcG_cyc : cG.IsCycle := hc.map Subtype.val_injective
        have hcG_mem : ∀ x ∈ cG.support, x ∈ (F₂ : Set V) := by
          intro x hx
          dsimp only [cG] at hx
          rw [Walk.support_map, List.mem_map] at hx
          rcases hx with ⟨z, hz, hzx⟩
          exact hzx ▸ hall2 z hz
        let c2 := cG.induce (F₂ : Set V) hcG_mem
        have hc2_cyc : c2.IsCycle := by
          apply Walk.IsCycle.of_map (f := (Embedding.induce (F₂ : Set V)).toHom)
          rw [Walk.map_induce]
          exact hcG_cyc
        exact hF₂ac c2 hc2_cyc
      push Not at hall1 hall2
      rcases hall2 with ⟨x, hx_supp, hx_not2⟩
      rcases hall1 with ⟨y, hy_supp, hy_not1⟩
      have hx1 : x.1 ∈ F₁ := (Finset.mem_union.mp x.2).resolve_right hx_not2
      have hy2 : y.1 ∈ F₂ := (Finset.mem_union.mp y.2).resolve_left hy_not1
      have hxv : x.1 ≠ v := fun h => hx_not2 (h ▸ hvF₂)
      have hyv : y.1 ≠ v := fun h => hy_not1 (h ▸ hvF₁)
      have hxD1 : x.1 ∈ D C₁ := (Finset.mem_insert.mp (hF₁E hx1)).resolve_left hxv
      have hyD2 : y.1 ∈ D C₂ := (Finset.mem_insert.mp (hF₂E hy2)).resolve_left hyv
      have hCx : H.connectedComponentMk ⟨x.1, hxv⟩ = C₁ := by
        rcases (Finset.mem_filter.mp hxD1).2 with ⟨_, h⟩
        exact h
      have hCy : H.connectedComponentMk ⟨y.1, hyv⟩ = C₂ := by
        rcases (Finset.mem_filter.mp hyD2).2 with ⟨_, h⟩
        exact h
      let c' := c.rotate x hx_supp
      have hc'_cyc : c'.IsCycle := (Walk.isCycle_rotate hx_supp).mpr hc
      have hy_supp' : y ∈ c'.support := (Walk.mem_support_rotate_iff c x hx_supp).mpr hy_supp
      let p := c'.takeUntil y hy_supp'
      let q := c'.dropUntil y hy_supp'
      have hpq : p.append q = c' := Walk.take_spec c' hy_supp'
      let emb := (Embedding.induce (G := G) ((F₁ ∪ F₂ : Finset V) : Set V)).toHom
      have hv_in_pG : v ∈ (p.map emb).support :=
        ncvr_walk_hits_cut_of_diff_comp G v (p.map emb) hxv hyv (by
          change H.connectedComponentMk ⟨x.1, hxv⟩ ≠ H.connectedComponentMk ⟨y.1, hyv⟩
          rw [hCx, hCy]
          exact hne12)
      have hv_in_qG : v ∈ (q.map emb).support :=
        ncvr_walk_hits_cut_of_diff_comp G v (q.map emb) hyv hxv (by
          change H.connectedComponentMk ⟨y.1, hyv⟩ ≠ H.connectedComponentMk ⟨x.1, hxv⟩
          rw [hCx, hCy]
          exact hne12.symm)
      let v' : ((F₁ ∪ F₂ : Finset V) : Set V) := ⟨v, Finset.mem_union_left _ hvF₁⟩
      have hv_in_p : v' ∈ p.support := by
        rw [Walk.support_map, List.mem_map] at hv_in_pG
        rcases hv_in_pG with ⟨z, hz, hzv⟩
        have : z = v' := Subtype.ext hzv
        exact this ▸ hz
      have hv_in_q : v' ∈ q.support := by
        rw [Walk.support_map, List.mem_map] at hv_in_qG
        rcases hv_in_qG with ⟨z, hz, hzv⟩
        have : z = v' := Subtype.ext hzv
        exact this ▸ hz
      have hv_tail_p : v' ∈ p.support.tail := by
        rw [← Walk.cons_tail_support] at hv_in_p
        rcases List.mem_cons.mp hv_in_p with h | h
        · exact (hxv (congrArg Subtype.val h).symm).elim
        · exact h
      have hv_tail_q : v' ∈ q.support.tail := by
        rw [← Walk.cons_tail_support] at hv_in_q
        rcases List.mem_cons.mp hv_in_q with h | h
        · exact (hyv (congrArg Subtype.val h).symm).elim
        · exact h
      have hnodup : (p.support.tail ++ q.support.tail).Nodup := by
        rw [← Walk.tail_support_append, hpq]
        exact hc'_cyc.support_nodup
      exact (List.nodup_append.mp hnodup).2.2 v' hv_tail_p v' hv_tail_q rfl
    have hle := ncvr_card_le_largestInducedForestSize G (F₁ ∪ F₂) hFunion_ac
    omega

private lemma nonbip_sub_walk_induce_lift {α : Type*} {G : SimpleGraph α} {S : Set α}
    {u v : α} (p : G.Walk u v) (hmem : ∀ z ∈ p.support, z ∈ S)
    (hu : u ∈ S) (hv : v ∈ S) :
    ∃ q : (G.induce S).Walk ⟨u, hu⟩ ⟨v, hv⟩,
      q.map (SimpleGraph.Embedding.induce S).toHom = p := by
  induction p with
  | nil =>
    exact ⟨Walk.nil, rfl⟩
  | @cons a b c hadj p' ih =>
    have hb : b ∈ S := hmem b (by simp)
    have hmem' : ∀ z ∈ p'.support, z ∈ S := fun z hz => hmem z (by simp [hz])
    obtain ⟨q', hq'⟩ := ih hmem' hb hv
    have hadj' : (G.induce S).Adj ⟨a, hu⟩ ⟨b, hb⟩ := hadj
    exact ⟨Walk.cons hadj' q', by simp [hq']⟩

private lemma nonbip_sub_singleton_pathCover {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) :
    IsPathCover H (Finset.univ.image fun x : W => ({x} : Finset W)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s1 hs1 s2 hs2 hne
    rcases Finset.mem_image.mp hs1 with ⟨x, _, rfl⟩
    rcases Finset.mem_image.mp hs2 with ⟨y, _, rfl⟩
    have hxy : x ≠ y := fun h => hne (by rw [h])
    simp [hxy]
  · intro x _
    rw [Finset.mem_biUnion]
    exact ⟨{x}, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩, Finset.mem_singleton_self x⟩
  · intro s hs
    rcases Finset.mem_image.mp hs with ⟨x, _, rfl⟩
    refine ⟨x, x, Walk.nil, Walk.IsPath.nil, ?_⟩
    ext y
    simp

private lemma nonbip_sub_pathCover_le_card {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) :
    H.pathCoverNumber ≤ Fintype.card W := by
  unfold SimpleGraph.pathCoverNumber
  apply Nat.sInf_le
  refine ⟨Finset.univ.image fun x : W => ({x} : Finset W), ?_, nonbip_sub_singleton_pathCover H⟩
  rw [Finset.card_image_of_injective _ Finset.singleton_injective, Finset.card_univ]

private lemma nonbip_sub_pathCover_reduction {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected) (hn : 1 < Fintype.card V)
    (hnb : ¬ G.IsBipartite) (B : Finset V)
    (hBbip : (G.induce (B : Set V)).IsBipartite)
    (hBcard : B.card = G.largestInducedBipartiteSubgraphSize)
    (hBp : G.pathCoverNumber ≤ (G.induce (B : Set V)).pathCoverNumber)
    (ih : ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W),
      Fintype.card W < Fintype.card V → 1 < Fintype.card W → H.Connected →
      H.pathCoverNumber + H.largestInducedBipartiteSubgraphSize + 1 ≤
        2 * H.largestInducedForestSize) :
    G.pathCoverNumber + G.largestInducedBipartiteSubgraphSize + 1 ≤
      2 * G.largestInducedForestSize := by
  classical
  let GB : SimpleGraph (B : Set V) := G.induce (B : Set V)
  have hB_lt : B.card < Fintype.card V := by
    by_contra hge
    have hBeq : B.card = Fintype.card V := le_antisymm B.card_le_univ (by omega)
    have hBuniv : B = Finset.univ := Finset.eq_univ_of_card B hBeq
    obtain ⟨c, hc⟩ := (SimpleGraph.induce_isBipartite_iff_exists_coloring G B).mp hBbip
    apply hnb
    refine ⟨SimpleGraph.Coloring.mk c ?_⟩
    intro u v huv
    exact hc u (hBuniv ▸ Finset.mem_univ u) v (hBuniv ▸ Finset.mem_univ v) huv
  let D : GB.ConnectedComponent → Finset V :=
    fun C => B.filter fun v => ∃ hv : v ∈ B, GB.connectedComponentMk ⟨v, hv⟩ = C
  have hD_sub : ∀ C, D C ⊆ B := fun C => Finset.filter_subset _ _
  have hD_mem : ∀ C v, v ∈ D C ↔ ∃ hv : v ∈ B, GB.connectedComponentMk ⟨v, hv⟩ = C := by
    intro C v
    simp only [D, Finset.mem_filter]
    exact ⟨fun h => h.2, fun ⟨hv, hC⟩ => ⟨hv, hv, hC⟩⟩
  have hD_disj : Pairwise fun C₁ C₂ => Disjoint (D C₁) (D C₂) := by
    intro C₁ C₂ hne
    rw [Finset.disjoint_left]
    intro v hv₁ hv₂
    obtain ⟨_, hC₁⟩ := (hD_mem C₁ v).mp hv₁
    obtain ⟨_, hC₂⟩ := (hD_mem C₂ v).mp hv₂
    exact hne (hC₁.symm.trans hC₂)
  have hD_biUnion : Finset.univ.biUnion D = B := by
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, hD_mem]
    constructor
    · rintro ⟨_, hv, _⟩
      exact hv
    · intro hv
      exact ⟨GB.connectedComponentMk ⟨v, hv⟩, hv, rfl⟩
  have hD_sum : ∑ C : GB.ConnectedComponent, (D C).card = B.card := by
    calc
      ∑ C : GB.ConnectedComponent, (D C).card = (Finset.univ.biUnion D).card :=
        (Finset.card_biUnion fun C₁ _ C₂ _ hne => hD_disj hne).symm
      _ = B.card := congrArg Finset.card hD_biUnion
  have hD_pos : ∀ C : GB.ConnectedComponent, 1 ≤ (D C).card := by
    intro C
    obtain ⟨x, hx⟩ := C.nonempty_supp
    have hxD : x.val ∈ D C := (hD_mem C x.val).mpr ⟨x.prop, hx⟩
    exact Finset.card_pos.mpr ⟨x.val, hxD⟩
  have hC₀_ex : ∃ C₀ : GB.ConnectedComponent, 2 ≤ (D C₀).card := by
    by_contra hall
    push Not at hall
    have hno_edge : ∀ u ∈ B, ∀ v ∈ B, ¬ G.Adj u v := by
      intro u hu v hv huv
      let C := GB.connectedComponentMk ⟨u, hu⟩
      have hCu : u ∈ D C := (hD_mem C u).mpr ⟨hu, rfl⟩
      have hreach : GB.Reachable ⟨u, hu⟩ ⟨v, hv⟩ := SimpleGraph.Adj.reachable huv
      have hCv : v ∈ D C := (hD_mem C v).mpr ⟨hv, (SimpleGraph.ConnectedComponent.eq.mpr hreach).symm⟩
      have hne : u ≠ v := G.ne_of_adj huv
      have hpair : ({u, v} : Finset V) ⊆ D C := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl <;> assumption
      have h2 : 2 ≤ (D C).card := by
        calc
          2 = ({u, v} : Finset V).card := (Finset.card_pair hne).symm
          _ ≤ (D C).card := Finset.card_le_card hpair
      have hlt := hall C
      omega
    obtain ⟨w, hw⟩ : ∃ w : V, w ∉ B := by
      by_contra h
      push Not at h
      have hle : (Finset.univ : Finset V).card ≤ B.card := Finset.card_le_card fun x _ => h x
      rw [Finset.card_univ] at hle
      omega
    have hB'_bip : (G.induce (insert w B : Finset V)).IsBipartite := by
      rw [SimpleGraph.induce_isBipartite_iff_exists_coloring]
      refine ⟨fun x => if x = w then 0 else 1, ?_⟩
      intro u hu v hv huv
      simp only [Finset.mem_insert] at hu hv
      rcases hu with rfl | huB <;> rcases hv with rfl | hvB
      · exact (G.ne_of_adj huv rfl).elim
      · have hvu : v ≠ u := fun h => hw (h ▸ hvB)
        simp [hvu]
      · have huv' : u ≠ v := fun h => hw (h ▸ huB)
        simp [huv']
      · exact (hno_edge u huB v hvB huv).elim
    have hle : (insert w B).card ≤ G.largestInducedBipartiteSubgraphSize := by
      unfold SimpleGraph.largestInducedBipartiteSubgraphSize
      apply le_csSup
      · exact ⟨Fintype.card V, fun n ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
      · exact ⟨insert w B, hB'_bip, rfl⟩
    rw [Finset.card_insert_of_notMem hw] at hle
    omega
  have hPC_sum :
      GB.pathCoverNumber ≤ ∑ C : GB.ConnectedComponent, (G.induce (D C : Set V)).pathCoverNumber := by
    have hexP : ∀ C : GB.ConnectedComponent,
        ∃ P : Finset (Finset (D C : Set V)),
          P.card = (G.induce (D C : Set V)).pathCoverNumber ∧
          IsPathCover (G.induce (D C : Set V)) P := by
      intro C
      have hne : { k | ∃ P : Finset (Finset (D C : Set V)),
          P.card = k ∧ IsPathCover (G.induce (D C : Set V)) P }.Nonempty :=
        ⟨_, Finset.univ.image fun x => ({x} : Finset (D C : Set V)), rfl,
          nonbip_sub_singleton_pathCover (G.induce (D C : Set V))⟩
      exact Nat.sInf_mem hne
    choose P hPcard hPcov using hexP
    let ι : ∀ C : GB.ConnectedComponent, (D C : Set V) ↪ (B : Set V) :=
      fun C => ⟨fun x => ⟨x.val, hD_sub C x.prop⟩, fun _ _ h => Subtype.ext (Subtype.mk.inj h)⟩
    let Q : Finset (Finset (B : Set V)) :=
      Finset.univ.biUnion fun C => (P C).image fun s => s.map (ι C)
    have hQcov : IsPathCover GB Q := by
      refine ⟨?_, ?_, ?_⟩
      · intro s1 hs1 s2 hs2 hne
        simp only [Q, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at hs1 hs2
        rcases hs1 with ⟨C₁, t₁, ht₁, rfl⟩
        rcases hs2 with ⟨C₂, t₂, ht₂, rfl⟩
        by_cases hC : C₁ = C₂
        · subst hC
          have htne : t₁ ≠ t₂ := fun h => hne (by rw [h])
          have htd : Disjoint t₁ t₂ := (hPcov C₁).1 t₁ ht₁ t₂ ht₂ htne
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          rcases Finset.mem_map.mp hx1 with ⟨a₁, ha₁, hxa₁⟩
          rcases Finset.mem_map.mp hx2 with ⟨a₂, ha₂, hxa₂⟩
          have haeq : a₁ = a₂ := (ι C₁).injective (hxa₁.trans hxa₂.symm)
          exact Finset.disjoint_left.mp htd ha₁ (haeq ▸ ha₂)
        · rw [Finset.disjoint_left]
          intro x hx1 hx2
          rcases Finset.mem_map.mp hx1 with ⟨a₁, _, hxa₁⟩
          rcases Finset.mem_map.mp hx2 with ⟨a₂, _, hxa₂⟩
          have hx1D : x.val ∈ D C₁ := by rw [← hxa₁]; exact a₁.prop
          have hx2D : x.val ∈ D C₂ := by rw [← hxa₂]; exact a₂.prop
          exact Finset.disjoint_left.mp (hD_disj hC) hx1D hx2D
      · intro x _
        let C := GB.connectedComponentMk x
        have hxDC : x.val ∈ D C := (hD_mem C x.val).mpr ⟨x.prop, rfl⟩
        have hmem := (hPcov C).2.1 (Finset.mem_univ (⟨x.val, hxDC⟩ : (D C : Set V)))
        rw [Finset.mem_biUnion] at hmem
        rcases hmem with ⟨t, ht, hxt⟩
        rw [Finset.mem_biUnion]
        refine ⟨t.map (ι C), ?_, ?_⟩
        · simp only [Q, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
          exact ⟨C, t, ht, rfl⟩
        · exact Finset.mem_map.mpr ⟨⟨x.val, hxDC⟩, hxt, rfl⟩
      · intro s hs
        simp only [Q, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at hs
        rcases hs with ⟨C, t, ht, rfl⟩
        obtain ⟨u, v, p, hp, rfl⟩ := (hPcov C).2.2 t ht
        let f : (G.induce (D C : Set V)) →g GB :=
          ⟨ι C, fun huv => huv⟩
        refine ⟨ι C u, ι C v, p.map f, hp.map (ι C).injective, ?_⟩
        ext x
        simp only [Finset.mem_map, List.mem_toFinset, Walk.support_map, List.mem_map]
        rfl
    have hQle : GB.pathCoverNumber ≤ Q.card := by
      unfold SimpleGraph.pathCoverNumber
      exact Nat.sInf_le ⟨Q, rfl, hQcov⟩
    calc
      GB.pathCoverNumber ≤ Q.card := hQle
      _ ≤ ∑ C : GB.ConnectedComponent, ((P C).image fun s => s.map (ι C)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ C : GB.ConnectedComponent, (P C).card :=
        Finset.sum_le_sum fun C _ => Finset.card_image_le
      _ = ∑ C : GB.ConnectedComponent, (G.induce (D C : Set V)).pathCoverNumber := by
        simp_rw [hPcard]
  have hF_sum :
      ∑ C : GB.ConnectedComponent, (G.induce (D C : Set V)).largestInducedForestSize ≤
        G.largestInducedForestSize := by
    have hexF : ∀ C : GB.ConnectedComponent,
        ∃ F : Finset (D C : Set V),
          ((G.induce (D C : Set V)).induce (F : Set (D C : Set V))).IsAcyclic ∧
          F.card = (G.induce (D C : Set V)).largestInducedForestSize := by
      intro C
      let S : Set ℕ :=
        { n | ∃ s : Finset (D C : Set V),
          ((G.induce (D C : Set V)).induce (s : Set (D C : Set V))).IsAcyclic ∧ s.card = n }
      have hne : S.Nonempty := by
        refine ⟨0, ∅, ?_, rfl⟩
        intro u
        exact (Finset.notMem_empty u.val u.prop).elim
      have hbdd : BddAbove S :=
        ⟨Fintype.card (D C : Set V), fun n ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
      exact Nat.sSup_mem hne hbdd
    choose FC hFC_acyc hFC_card using hexF
    let F' : GB.ConnectedComponent → Finset V :=
      fun C => (FC C).map ⟨Subtype.val, Subtype.val_injective⟩
    have hF'_sub : ∀ C, F' C ⊆ D C := by
      intro C v hv
      rcases Finset.mem_map.mp hv with ⟨x, _, rfl⟩
      exact x.prop
    have hF'_card : ∀ C, (F' C).card = (FC C).card := fun C => Finset.card_map _
    have hF'_disj : Pairwise fun C₁ C₂ => Disjoint (F' C₁) (F' C₂) := by
      intro C₁ C₂ hne
      exact Disjoint.mono (hF'_sub C₁) (hF'_sub C₂) (hD_disj hne)
    let F : Finset V := Finset.univ.biUnion F'
    have hF_card : F.card =
        ∑ C : GB.ConnectedComponent, (G.induce (D C : Set V)).largestInducedForestSize := by
      rw [Finset.card_biUnion (fun C₁ _ C₂ _ hne => hF'_disj hne)]
      simp_rw [hF'_card, hFC_card]
    have hF_acyc : (G.induce (F : Set V)).IsAcyclic := by
      intro u c hc
      have huF : u.val ∈ F := u.prop
      simp only [F, Finset.mem_biUnion, Finset.mem_univ, true_and] at huF
      rcases huF with ⟨C, huFC⟩
      let S : Set (F : Set V) := { x | x.val ∈ F' C }
      have hadj_stay : ∀ {x y : (F : Set V)},
          (G.induce (F : Set V)).Adj x y → x ∈ S → y ∈ S := by
        intro x y hxy hxS
        have hyF : y.val ∈ F := y.prop
        simp only [F, Finset.mem_biUnion, Finset.mem_univ, true_and] at hyF
        rcases hyF with ⟨C', hyFC'⟩
        have hxDC : x.val ∈ D C := hF'_sub C hxS
        have hyDC' : y.val ∈ D C' := hF'_sub C' hyFC'
        obtain ⟨hxB, hCx⟩ := (hD_mem C x.val).mp hxDC
        obtain ⟨hyB, hCy⟩ := (hD_mem C' y.val).mp hyDC'
        have hreach : GB.Reachable ⟨x.val, hxB⟩ ⟨y.val, hyB⟩ := SimpleGraph.Adj.reachable hxy
        have hCeq : C = C' := hCx.symm.trans ((SimpleGraph.ConnectedComponent.eq.mpr hreach).trans hCy)
        show y.val ∈ F' C
        exact hCeq ▸ hyFC'
      have hwalk_stay : ∀ {a b : (F : Set V)} (p : (G.induce (F : Set V)).Walk a b),
          a ∈ S → ∀ z ∈ p.support, z ∈ S := by
        intro a b p
        induction p with
        | nil =>
          intro ha z hz
          simp only [Walk.support_nil, List.mem_singleton] at hz
          exact hz ▸ ha
        | @cons a b d hab p' ih =>
          intro ha z hz
          simp only [Walk.support_cons, List.mem_cons] at hz
          rcases hz with rfl | hz'
          · exact ha
          · exact ih (hadj_stay hab ha) z hz'
      have hmem_c : ∀ z ∈ c.support, z ∈ S := hwalk_stay c huFC
      obtain ⟨q, hq⟩ := nonbip_sub_walk_induce_lift c hmem_c huFC huFC
      have hq_cyc : q.IsCycle := by
        rw [← hq] at hc
        exact hc.of_map
      let g : ((G.induce (F : Set V)).induce S) →g
          ((G.induce (D C : Set V)).induce (FC C : Set (D C : Set V))) :=
        ⟨fun x =>
          ⟨⟨x.val.val, hF'_sub C x.prop⟩, by
            rcases Finset.mem_map.mp x.prop with ⟨y, hy, hyval⟩
            have hy_eq : y = ⟨x.val.val, hF'_sub C x.prop⟩ := Subtype.ext hyval
            exact hy_eq ▸ hy⟩,
          fun huv => huv⟩
      have hg_inj : Function.Injective g := by
        intro x y hxy
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z => z.val.val) hxy
      exact hFC_acyc C (q.map g) (hq_cyc.map hg_inj)
    rw [← hF_card]
    unfold SimpleGraph.largestInducedForestSize
    apply le_csSup
    · exact ⟨Fintype.card V, fun n ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
    · exact ⟨F, hF_acyc, rfl⟩
  have hcomp_bound : ∀ C : GB.ConnectedComponent,
      (G.induce (D C : Set V)).pathCoverNumber + (D C).card +
          (if 2 ≤ (D C).card then 1 else 0) ≤
        2 * (G.induce (D C : Set V)).largestInducedForestSize := by
    intro C
    let HC : SimpleGraph (D C : Set V) := G.induce (D C : Set V)
    have hcard_DC : Fintype.card (D C : Set V) = (D C).card := Fintype.card_coe (D C)
    by_cases h2 : 2 ≤ (D C).card
    · rw [if_pos h2]
      have hHC_bip : HC.IsBipartite := by
        obtain ⟨c, hc⟩ := (SimpleGraph.induce_isBipartite_iff_exists_coloring G B).mp hBbip
        exact ⟨SimpleGraph.Coloring.mk (fun x => c x.val) fun {u v} huv =>
          hc u.val (hD_sub C u.prop) v.val (hD_sub C v.prop) huv⟩
      have hHC_bsize : HC.largestInducedBipartiteSubgraphSize = (D C).card := by
        rw [← hcard_DC]
        unfold SimpleGraph.largestInducedBipartiteSubgraphSize
        apply le_antisymm
        · apply csSup_le
          · refine ⟨0, ∅, ?_, rfl⟩
            rw [SimpleGraph.induce_isBipartite_iff_exists_coloring]
            exact ⟨fun _ => 0, by simp⟩
          · rintro n ⟨s, _, rfl⟩
            exact s.card_le_univ
        · apply le_csSup
          · exact ⟨Fintype.card (D C : Set V), fun n ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
          · refine ⟨Finset.univ, ?_, Finset.card_univ⟩
            rcases hHC_bip with ⟨c⟩
            rw [SimpleGraph.induce_isBipartite_iff_exists_coloring]
            exact ⟨c, fun u _ v _ huv => c.valid huv⟩
      have hHC_conn : HC.Connected := by
        have : Nonempty (D C : Set V) := by
          obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < (D C).card)
          exact ⟨⟨v, hv⟩⟩
        refine ⟨fun x y => ?_⟩
        obtain ⟨hxB, hCx⟩ := (hD_mem C x.val).mp x.prop
        obtain ⟨hyB, hCy⟩ := (hD_mem C y.val).mp y.prop
        have hreach : GB.Reachable ⟨x.val, hxB⟩ ⟨y.val, hyB⟩ :=
          SimpleGraph.ConnectedComponent.eq.mp (hCx.trans hCy.symm)
        obtain ⟨w⟩ := hreach
        let SC : Set (B : Set V) := { z | z.val ∈ D C }
        have hmem_w : ∀ z ∈ w.support, z ∈ SC := by
          intro z hz
          have hrz : GB.Reachable ⟨x.val, hxB⟩ z :=
            ⟨w.takeUntil z hz⟩
          exact (hD_mem C z.val).mpr
            ⟨z.prop, (SimpleGraph.ConnectedComponent.eq.mpr hrz).symm.trans hCx⟩
        obtain ⟨q, _⟩ := nonbip_sub_walk_induce_lift w hmem_w x.prop y.prop
        let g : (GB.induce SC) →g HC := ⟨fun z => ⟨z.val.val, z.prop⟩, fun huv => huv⟩
        exact ⟨q.map g⟩
      have hlt_card : Fintype.card (D C : Set V) < Fintype.card V := by
        rw [hcard_DC]
        exact lt_of_le_of_lt (Finset.card_le_card (hD_sub C)) hB_lt
      have hgt1_card : 1 < Fintype.card (D C : Set V) := by omega
      have hih := ih (D C : Set V) HC hlt_card hgt1_card hHC_conn
      rw [hHC_bsize] at hih
      exact hih
    · rw [if_neg h2]
      have h1 : (D C).card = 1 := by
        have hp := hD_pos C
        omega
      have hp_le : HC.pathCoverNumber ≤ 1 := by
        have := nonbip_sub_pathCover_le_card HC
        omega
      have hf_ge : 1 ≤ HC.largestInducedForestSize := by
        unfold SimpleGraph.largestInducedForestSize
        apply le_csSup
        · exact ⟨Fintype.card (D C : Set V), fun n ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
        · refine ⟨Finset.univ, ?_, by rw [Finset.card_univ, hcard_DC, h1]⟩
          intro u c hc
          have hlen := hc.three_le_length
          have hnodup := hc.support_nodup
          have hle := hnodup.length_le_card
          have hcard_u : Fintype.card (↑(Finset.univ : Finset (D C : Set V)) : Set (D C : Set V)) = 1 := by
            simp [h1]
          have hlen_tail : c.support.tail.length = c.length := by
            rw [List.length_tail, c.length_support]
            omega
          omega
      change HC.pathCoverNumber + (D C).card + 0 ≤ 2 * HC.largestInducedForestSize
      omega
  obtain ⟨C₀, hC₀⟩ := hC₀_ex
  have hsum_ineq :
      (∑ C : GB.ConnectedComponent, (G.induce (D C : Set V)).pathCoverNumber) +
          (∑ C : GB.ConnectedComponent, (D C).card) +
          (∑ C : GB.ConnectedComponent, if 2 ≤ (D C).card then 1 else 0) ≤
        2 * ∑ C : GB.ConnectedComponent, (G.induce (D C : Set V)).largestInducedForestSize := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun C _ => hcomp_bound C
  have hbonus : 1 ≤ ∑ C : GB.ConnectedComponent, if 2 ≤ (D C).card then 1 else 0 := by
    calc
      1 = (if 2 ≤ (D C₀).card then 1 else 0) := by rw [if_pos hC₀]
      _ ≤ ∑ C : GB.ConnectedComponent, if 2 ≤ (D C).card then 1 else 0 :=
        Finset.single_le_sum (f := fun C => if 2 ≤ (D C).card then 1 else 0)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ C₀)
  have hBp' : G.pathCoverNumber ≤ GB.pathCoverNumber := hBp
  omega

end

section

private lemma r2_forest_induce_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) :
    (G.induce (S : Set V)).largestInducedForestSize ≤ G.largestInducedForestSize := by
  obtain ⟨F, _, hFac, hFcard⟩ := ncvr_exists_acyclic_subset_eq G S
  rw [← hFcard]
  exact ncvr_card_le_largestInducedForestSize G F hFac

private lemma r2_bip_le_induce_compl_add_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) :
    G.largestInducedBipartiteSubgraphSize ≤
      (G.induce ((({v} : Finset V)ᶜ : Finset V) : Set V)).largestInducedBipartiteSubgraphSize
        + 1 := by
  obtain ⟨B, hBbip, hBcard⟩ := ncvr_exists_bipartite_card_eq G
  have hsub : B.erase v ⊆ (({v} : Finset V)ᶜ : Finset V) := by
    intro x hx
    rw [Finset.mem_compl, Finset.mem_singleton]
    exact Finset.ne_of_mem_erase hx
  have hbip : (G.induce ((B.erase v : Finset V) : Set V)).IsBipartite :=
    ncvr_induce_isBipartite_mono (Finset.erase_subset v B) hBbip
  have h1 := ncvr_card_le_induce_bipartite G _ _ hsub hbip
  have h2 : B.card - 1 ≤ (B.erase v).card := Finset.pred_card_le_card_erase
  omega

private lemma r2_pathCover_le_induce_compl_add_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) :
    G.pathCoverNumber ≤
      (G.induce ((({v} : Finset V)ᶜ : Finset V) : Set V)).pathCoverNumber + 1 := by
  have h := ncvr_pathCoverNumber_le_sum_partition G
    (fun i : Bool => if i then (({v} : Finset V)ᶜ : Finset V) else ({v} : Finset V))
    (by
      intro i j hij
      cases i <;> cases j
      · exact (hij rfl).elim
      · simpa using disjoint_compl_right
      · simpa using disjoint_compl_left
      · exact (hij rfl).elim)
    (by
      intro x
      by_cases hx : x = v
      · exact ⟨false, by simp [hx]⟩
      · exact ⟨true, by simp [hx]⟩)
  rw [Fintype.sum_bool] at h
  have h' : G.pathCoverNumber ≤
      (G.induce ((({v} : Finset V)ᶜ : Finset V) : Set V)).pathCoverNumber +
        (G.induce (({v} : Finset V) : Set V)).pathCoverNumber := h
  have h1 := ncvr_pathCoverNumber_singleton_le G v
  omega

/-- Vertex deletion: if `G - v` is connected and satisfies the conjecture, then `G` satisfies it
as soon as the forest number drops or `p + b` does not drop. -/
private lemma r2_vertex_reduction {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (v : V)
    (hK : (G.induce ((({v} : Finset V)ᶜ : Finset V) : Set V)).pathCoverNumber +
        (G.induce ((({v} : Finset V)ᶜ : Finset V) : Set V)).largestInducedBipartiteSubgraphSize
          + 1 ≤
      2 * (G.induce ((({v} : Finset V)ᶜ : Finset V) : Set V)).largestInducedForestSize)
    (hfail :
      (G.induce ((({v} : Finset V)ᶜ : Finset V) : Set V)).largestInducedForestSize <
        G.largestInducedForestSize ∨
      G.pathCoverNumber + G.largestInducedBipartiteSubgraphSize ≤
        (G.induce ((({v} : Finset V)ᶜ : Finset V) : Set V)).pathCoverNumber +
        (G.induce ((({v} : Finset V)ᶜ : Finset V) : Set V)).largestInducedBipartiteSubgraphSize) :
    G.pathCoverNumber + G.largestInducedBipartiteSubgraphSize + 1 ≤
      2 * G.largestInducedForestSize := by
  have hf := r2_forest_induce_le G (({v} : Finset V)ᶜ : Finset V)
  have hb := r2_bip_le_induce_compl_add_one G v
  have hp := r2_pathCover_le_induce_compl_add_one G v
  rcases hfail with h | h <;> omega

private lemma r2_isPathCover_mono {V : Type*} [Fintype V] [DecidableEq V]
    {G K : SimpleGraph V} (hle : K ≤ G) {P : Finset (Finset V)} (hP : K.IsPathCover P) :
    G.IsPathCover P := by
  rcases hP with ⟨hdisj, hcov, hpaths⟩
  refine ⟨hdisj, hcov, ?_⟩
  intro s hs
  rcases hpaths s hs with ⟨u, w, p, hp, rfl⟩
  refine ⟨u, w, p.mapLe hle, hp.mapLe hle, ?_⟩
  rw [Walk.support_mapLe_eq_support]

/-- Edge deletion: if `G - e` satisfies the conjecture and has no larger induced forest, then
`G` satisfies the conjecture. -/
private lemma r2_edge_reduction {V : Type} [Fintype V] [DecidableEq V] (G K : SimpleGraph V)
    (hle : K ≤ G)
    (hK : K.pathCoverNumber + K.largestInducedBipartiteSubgraphSize + 1 ≤
      2 * K.largestInducedForestSize)
    (hf : K.largestInducedForestSize ≤ G.largestInducedForestSize) :
    G.pathCoverNumber + G.largestInducedBipartiteSubgraphSize + 1 ≤
      2 * G.largestInducedForestSize := by
  have hp : G.pathCoverNumber ≤ K.pathCoverNumber := by
    obtain ⟨P, hPcard, hP⟩ := ncvr_exists_pathCover_card_eq K
    rw [← hPcard]
    unfold SimpleGraph.pathCoverNumber
    exact Nat.sInf_le ⟨P, rfl, r2_isPathCover_mono hle hP⟩
  have hb : G.largestInducedBipartiteSubgraphSize ≤ K.largestInducedBipartiteSubgraphSize := by
    obtain ⟨B, hBbip, hBcard⟩ := ncvr_exists_bipartite_card_eq G
    rw [← hBcard]
    unfold SimpleGraph.largestInducedBipartiteSubgraphSize
    apply le_csSup
    · exact ⟨Fintype.card V, fun _ ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
    · refine ⟨B, ?_, rfl⟩
      rw [SimpleGraph.induce_isBipartite_iff_exists_coloring] at hBbip ⊢
      rcases hBbip with ⟨c, hc⟩
      exact ⟨c, fun u hu w hw huw => hc u hu w hw (hle huw)⟩
  omega

private lemma r2_deleteEdges_ncard_lt {V : Type*} [Fintype V] (G : SimpleGraph V) (a b : V)
    (hab : G.Adj a b) :
    (G.deleteEdges {s(a, b)}).edgeSet.ncard < G.edgeSet.ncard := by
  apply Set.ncard_lt_ncard _ (Set.toFinite _)
  rw [SimpleGraph.edgeSet_deleteEdges]
  refine ⟨Set.diff_subset, fun h => ?_⟩
  have hmem : s(a, b) ∈ G.edgeSet := hab
  exact (h hmem).2 rfl

/-- A graph on at least three vertices all of whose vertex-deleted subgraphs are connected has
no bridge. -/
private lemma r2_deleteEdges_connected {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hn3 : 3 ≤ Fintype.card V)
    (h2c : ∀ v : V, (G.induce ({v}ᶜ : Set V)).Connected) (a b : V) (hab : a ≠ b) :
    (G.deleteEdges {s(a, b)}).Connected := by
  have key : ∀ u : V, (u = a ∨ u = b) → ∀ x y : V, x ≠ u → y ≠ u →
      (G.deleteEdges {s(a, b)}).Reachable x y := by
    intro u hu x y hx hy
    let f : G.induce ({u}ᶜ : Set V) →g G.deleteEdges {s(a, b)} :=
      { toFun := Subtype.val
        map_rel' := by
          intro p q hpq
          rw [SimpleGraph.deleteEdges_adj]
          refine ⟨hpq, ?_⟩
          intro hmem
          have hp : p.1 ≠ u := p.2
          have hq : q.1 ≠ u := q.2
          rw [Set.mem_singleton_iff, Sym2.eq_iff] at hmem
          rcases hu with rfl | rfl <;> rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact hp h1
          · exact hq h2
          · exact hq h2
          · exact hp h1 }
    exact ((h2c u).preconnected ⟨x, hx⟩ ⟨y, hy⟩).map f
  have hc : ∃ c : V, c ≠ a ∧ c ≠ b := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset V) ⊆ {a, b} := by
      intro x _
      by_cases hx : x = a
      · simp [hx]
      · simp [h x hx]
    have h1 := Finset.card_le_card hsub
    have h2 : ({a, b} : Finset V).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ] at h1
    omega
  rcases hc with ⟨c, hca, hcb⟩
  have hreach : ∀ x : V, (G.deleteEdges {s(a, b)}).Reachable x c := by
    intro x
    by_cases hx : x = a
    · subst hx
      exact key b (Or.inr rfl) x c hab hcb
    · exact key a (Or.inl rfl) x c hx hca
  exact { preconnected := fun x y => (hreach x).trans (hreach y).symm, nonempty := ⟨a⟩ }

end

theorem main : H1 → H2 → type_of% @WrittenOnTheWallII.GraphConjecture40.conjecture40 := by
  intro h1 h2 α _ _ _ G hconn hn
  rw [conjecture40_iff_nat]
  have hmain : ∀ (n m : ℕ) (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V),
      Fintype.card V = n → H.edgeSet.ncard = m → 1 < Fintype.card V → H.Connected →
      H.pathCoverNumber + H.largestInducedBipartiteSubgraphSize + 1 ≤
        2 * H.largestInducedForestSize := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih_n =>
      intro m
      induction m using Nat.strong_induction_on with
      | h m ih_m =>
      intro V _ _ H hcard hedges hgt1 hHconn
      have ih : ∀ (W : Type) [Fintype W] [DecidableEq W] (K : SimpleGraph W),
          Fintype.card W < Fintype.card V → 1 < Fintype.card W → K.Connected →
          K.pathCoverNumber + K.largestInducedBipartiteSubgraphSize + 1 ≤
            2 * K.largestInducedForestSize := by
        intro W _ _ K hlt
        exact ih_n (Fintype.card W) (hcard ▸ hlt) K.edgeSet.ncard W K rfl rfl
      have ihe : ∀ K : SimpleGraph V, K.edgeSet.ncard < H.edgeSet.ncard → K.Connected →
          K.pathCoverNumber + K.largestInducedBipartiteSubgraphSize + 1 ≤
            2 * K.largestInducedForestSize := by
        intro K hlt hKconn
        exact ih_m K.edgeSet.ncard (hedges ▸ hlt) V K hcard rfl hgt1 hKconn
      by_cases hn2 : Fintype.card V = 2
      · exact card_two_bound H hHconn hn2
      · have hn3 : 3 ≤ Fintype.card V := by omega
        by_cases hsc : ∃ S : Finset V,
            H.pathCoverNumber + S.card ≤
              Nat.card (H.induce (S : Set V)ᶜ).ConnectedComponent
        · rcases hsc with ⟨S, hS⟩
          have hsb := scattering_bound H hHconn hgt1 S
          omega
        · push Not at hsc
          by_cases h2c : ∀ v : V, (H.induce ({v}ᶜ : Set V)).Connected
          · have hdel : ∀ v : V,
                (H.induce ((({v} : Finset V)ᶜ : Finset V) : Set V)).pathCoverNumber +
                  (H.induce ((({v} : Finset V)ᶜ : Finset V) :
                    Set V)).largestInducedBipartiteSubgraphSize + 1 ≤
                2 * (H.induce ((({v} : Finset V)ᶜ : Finset V) :
                    Set V)).largestInducedForestSize := by
              intro v
              have hset : ((({v} : Finset V)ᶜ : Finset V) : Set V) = ({v}ᶜ : Set V) := by
                ext x
                simp
              have hKconn : (H.induce ((({v} : Finset V)ᶜ : Finset V) : Set V)).Connected := by
                rw [hset]
                exact h2c v
              have hKcard : Fintype.card ((({v} : Finset V)ᶜ : Finset V) : Set V) =
                  Fintype.card V - 1 := by
                simp only [Finset.coe_sort_coe, Fintype.card_coe, Finset.card_compl,
                  Finset.card_singleton]
              exact ih _ _ (by omega) (by omega) hKconn
            by_cases hD : ∀ R : Finset V, 2 ≤ R.card → R.card < Fintype.card V →
                (H.induce (R : Set V)).Connected →
                (H.induce (R : Set V)).pathCoverNumber +
                    (H.induce (R : Set V)).largestInducedBipartiteSubgraphSize +
                    2 * H.largestInducedForestSize <
                  H.pathCoverNumber + H.largestInducedBipartiteSubgraphSize +
                    2 * (H.induce (R : Set V)).largestInducedForestSize
            swap
            · push Not at hD
              rcases hD with ⟨R, hR2, hRlt, hRconn, hRge⟩
              have hRcard : Fintype.card (R : Set V) = R.card := by
                simp only [Finset.coe_sort_coe, Fintype.card_coe]
              have hRih := ih _ (H.induce (R : Set V)) (by omega) (by omega) hRconn
              omega
            by_cases hfv : ∀ v : V,
                (H.induce ((({v} : Finset V)ᶜ : Finset V) : Set V)).largestInducedForestSize =
                  H.largestInducedForestSize
            · by_cases hpb : ∀ v : V,
                  (H.induce ((({v} : Finset V)ᶜ : Finset V) : Set V)).pathCoverNumber +
                    (H.induce ((({v} : Finset V)ᶜ : Finset V) :
                      Set V)).largestInducedBipartiteSubgraphSize <
                  H.pathCoverNumber + H.largestInducedBipartiteSubgraphSize
              · have hC : ∀ v : V,
                    (H.induce ((({v} : Finset V)ᶜ : Finset V) : Set V)).pathCoverNumber +
                      (H.induce ((({v} : Finset V)ᶜ : Finset V) :
                        Set V)).largestInducedBipartiteSubgraphSize + 1 ≤
                    2 * H.largestInducedForestSize := by
                  intro v
                  have h1' := hdel v
                  have h2' := hfv v
                  omega
                by_cases hfe : ∀ a b : V, H.Adj a b →
                    H.largestInducedForestSize <
                      (H.deleteEdges {s(a, b)}).largestInducedForestSize
                · by_cases hbip : H.IsBipartite
                  · have hn4 := two_connected_bipartite_card_ge_four H hn3 h2c hbip
                    have hb := bipartite_size_eq_card H hbip
                    have hpv : ∀ v : V,
                        (H.induce ((({v} : Finset V)ᶜ : Finset V) : Set V)).pathCoverNumber ≤
                          H.pathCoverNumber := by
                      intro v
                      have h1' := hpb v
                      have h2' := r2_bip_le_induce_compl_add_one H v
                      omega
                    have hD1 : ∀ R : Finset V, 2 ≤ R.card → R.card < Fintype.card V →
                        (H.induce (R : Set V)).Connected →
                        (H.induce (R : Set V)).pathCoverNumber + R.card +
                            2 * H.largestInducedForestSize <
                          H.pathCoverNumber + Fintype.card V +
                            2 * (H.induce (R : Set V)).largestInducedForestSize := by
                      intro R hR2 hRlt hRconn
                      have hRbip : (H.induce (R : Set V)).IsBipartite := by
                        rcases hbip with ⟨c⟩
                        exact ⟨c.comp (SimpleGraph.Embedding.induce (R : Set V)).toHom⟩
                      have hbR := bipartite_size_eq_card (H.induce (R : Set V)) hRbip
                      have hRcard : Fintype.card (R : Set V) = R.card := by
                        simp only [Finset.coe_sort_coe, Fintype.card_coe]
                      have h0 := hD R hR2 hRlt hRconn
                      omega
                    rw [hb]
                    exact h1 V H hn4 hHconn h2c hbip hsc hfv hC hpv hfe hD1
                  · by_cases hsub : ∃ B : Finset V,
                      (H.induce (B : Set V)).IsBipartite ∧
                      B.card = H.largestInducedBipartiteSubgraphSize ∧
                      H.pathCoverNumber ≤ (H.induce (B : Set V)).pathCoverNumber
                    · rcases hsub with ⟨B, hBbip, hBcard, hBp⟩
                      exact nonbip_sub_pathCover_reduction H hHconn hgt1 hbip B hBbip hBcard hBp ih
                    · push Not at hsub
                      exact h2 V H hn3 hHconn h2c hbip hsc hsub hfv hC hpb hfe hD
                · push Not at hfe
                  rcases hfe with ⟨a, b, hab, hle⟩
                  exact r2_edge_reduction H _ (SimpleGraph.deleteEdges_le _)
                    (ihe _ (r2_deleteEdges_ncard_lt H a b hab)
                      (r2_deleteEdges_connected H hn3 h2c a b hab.ne)) hle
              · push Not at hpb
                rcases hpb with ⟨v, hv⟩
                exact r2_vertex_reduction H v (hdel v) (Or.inr hv)
            · push Not at hfv
              rcases hfv with ⟨v, hv⟩
              have hle := r2_forest_induce_le H (({v} : Finset V)ᶜ : Finset V)
              exact r2_vertex_reduction H v (hdel v) (Or.inl (by omega))
          · push Not at h2c
            rcases h2c with ⟨v, hv⟩
            by_cases hleaf : ∃ u : V, u ≠ v ∧ ∀ w : V, H.Adj u w → w = v
            · rcases hleaf with ⟨u, huv, hdeg⟩
              exact leaf_reduction H hHconn hn3 u v huv hdeg ih
            · push Not at hleaf
              have hnoleaf : ∀ u : V, u ≠ v → ∃ w : V, w ≠ v ∧ H.Adj u w := by
                intro u huv
                rcases hleaf u huv with ⟨w, hadj, hw⟩
                exact ⟨w, hw, hadj⟩
              exact nontrivial_cut_vertex_reduction H hHconn hn3 v hv hnoleaf ih
  let e := Fintype.equivFin α
  let K := G.map e.toEmbedding
  have eK : G ≃g K := SimpleGraph.Iso.map e G
  have hKconn : K.Connected := eK.connected_iff.mp hconn
  have hKcard : Fintype.card (Fin (Fintype.card α)) = Fintype.card α := Fintype.card_fin _
  obtain ⟨hp, hb, hf⟩ := iso_invariance eK
  rw [hp, hb, hf]
  exact hmain (Fintype.card α) K.edgeSet.ncard (Fin (Fintype.card α)) K hKcard rfl
    (hKcard.symm ▸ hn) hKconn

end OMA.R_WrittenOnTheWallII_GraphConjecture40_conjecture40_R2
