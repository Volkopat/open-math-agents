import OMAReductions.R_Arxiv_2607_06396_alon_tarsi_short_cycle_cover_R1_H2_R1

-- Reduction Arxiv.2607.06396.alon_tarsi_short_cycle_cover.R1.H2.R1.H2.R1 of step Arxiv.2607.06396.alon_tarsi_short_cycle_cover.R1.H2.R1.H2
-- Credit: @sovrana

/-!
# Alon-Tarsi, degree at least four: split vertices down to the subcubic case

The step `R1.H2.R1.H2` asks for a short cycle cover of every bridgeless graph with an odd vertex and a
vertex of degree at least four whose edges are not the union of two even sets. Proved below:

* covers pull back along vertex splitting at no cost (`cover_transfer`): moving two edges `vu`, `vw`
  of `G` to a new vertex gives a graph `G'` on `Option V` with the same number of edges, and the map
  `Option V → V` that sends the new vertex to `v` is a homomorphism which is a bijection on edges, so
  each cycle of `G'` becomes a closed trail of `G`, which Veblen's theorem (proved again here) splits
  into edge-disjoint cycles of the same total length;
* splitting keeps an odd vertex (the degree of `v` drops by two), creates a vertex of degree two and
  lowers `∑ (deg - 3)`, so by induction (`all_cases`), with the `4/3` bound of Bermond, Jackson and
  Jaeger for graphs that are a union of two even sets (`cover_of_two_even`), everything reduces to
  the two hypotheses:
* graphs close to a 4-flow are also proved (`cover_of_near_two_even`): two even sets `S`, `T`
  plus cycles `D` through the remaining edges give a cover of length at most
  `4/3 |S ∪ T| + len D`, which is at most `7/5 |E|` when `len D ≤ |E|/15`;
* `H1`: the subcubic case with a vertex of degree two and no such near-4-flow structure (a special
  case of the sibling step `R1.H2.R1.H1`), still open;
* `H2`: Fleischner's splitting lemma (1990): at a vertex of degree at least four of a bridgeless
  graph, some two edges can be split off to a new vertex without creating a bridge. This is a
  classical theorem; a kernel-checked proof is ready for it.
-/

open Finset SimpleGraph

namespace OMA.R_Arxiv_2607_06396_alon_tarsi_short_cycle_cover_R1_H2_R1_H2_R1

/-- A graph with an edge in which every degree is even contains a cycle: the last vertex of a
longest path has a second neighbour, which must lie on the path. -/
lemma exists_cycle {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hev : ∀ v, Even (G.degree v)) {a b : V} (hab : G.Adj a b) :
    ∃ (u : V) (c : G.Walk u u), c.IsCycle := by
  classical
  by_contra hno
  push_neg at hno
  have hac : G.IsAcyclic := fun u c hc => hno u c hc
  let P : ℕ → Prop := fun n => ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ p.length = n
  have hbound : ∀ n, P n → n ≤ Fintype.card V := by
    rintro n ⟨u, v, p, hp, rfl⟩
    exact hp.length_lt.le
  have h1 : P 1 := ⟨a, b, Walk.cons hab Walk.nil, by simp [hab.ne], by simp⟩
  have hN : P (Nat.findGreatest P (Fintype.card V)) := Nat.findGreatest_spec (hbound 1 h1) h1
  have hN1 : 1 ≤ Nat.findGreatest P (Fintype.card V) := Nat.le_findGreatest (hbound 1 h1) h1
  obtain ⟨u, v, p, hp, hlen⟩ := hN
  have hnil : ¬ p.Nil := by
    intro h
    rw [Walk.nil_iff_length_eq] at h
    omega
  have hpen : G.Adj p.penultimate v := p.adj_penultimate hnil
  have hmem : p.penultimate ∈ G.neighborFinset v := by
    rw [mem_neighborFinset]; exact hpen.symm
  have hpos : 0 < G.degree v := by
    rw [← card_neighborFinset_eq_degree]; exact card_pos.mpr ⟨_, hmem⟩
  have h2 : 1 < (G.neighborFinset v).card := by
    rw [card_neighborFinset_eq_degree]
    obtain ⟨k, hk⟩ := hev v
    omega
  obtain ⟨w, hw, hwne⟩ := exists_mem_ne h2 p.penultimate
  rw [mem_neighborFinset] at hw
  by_cases hws : w ∈ p.support
  · exact hwne (hac.eq_penultimate_of_adj_end hp hw hws)
  · have hp' : (p.concat hw).IsPath := hp.concat hws hw
    have hP : P (p.length + 1) := ⟨u, w, p.concat hw, hp', by simp⟩
    have hle := hbound _ hP
    exact Nat.findGreatest_is_greatest (by omega) hle hP

/-- Deleting the edges of a closed trail keeps every degree even. -/
lemma even_degree_delete {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hev : ∀ v, Even (G.degree v)) {u : V} (c : G.Walk u u)
    (hc : c.IsTrail) [DecidableRel (G.deleteEdges (c.edges.toFinset : Set (Sym2 V))).Adj] (x : V) :
    Even ((G.deleteEdges (c.edges.toFinset : Set (Sym2 V))).degree x) := by
  set S : Finset (Sym2 V) := c.edges.toFinset with hS
  have hsub : S ⊆ G.edgeFinset := by
    intro e he
    rw [hS, List.mem_toFinset] at he
    exact mem_edgeFinset.mpr (c.edges_subset_edgeSet he)
  have hcnt : Even (c.edges.countP fun e => decide (x ∈ e)) :=
    (hc.even_countP_edges_iff x).mpr (fun h => absurd rfl h)
  have hcnt' : (c.edges.countP fun e => decide (x ∈ e)) = (S.filter (x ∈ ·)).card := by
    rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hc.edges_nodup.filter _),
      hS, List.toFinset_filter]
    simp
  rw [← card_incidenceFinset_eq_degree, incidenceFinset_eq_filter, edgeFinset_deleteEdges]
  have hfs : (G.edgeFinset \ S).filter (x ∈ ·) = (G.edgeFinset.filter (x ∈ ·)) \ (S.filter (x ∈ ·)) := by
    ext e; simp only [mem_filter, mem_sdiff]; tauto
  have hfsub : S.filter (x ∈ ·) ⊆ G.edgeFinset.filter (x ∈ ·) := filter_subset_filter _ hsub
  rw [hfs, card_sdiff_of_subset hfsub, ← hcnt']
  have hA : Even (G.edgeFinset.filter (x ∈ ·)).card := by
    rw [← incidenceFinset_eq_filter, card_incidenceFinset_eq_degree]; exact hev x
  have hle : (c.edges.countP fun e => decide (x ∈ e)) ≤ (G.edgeFinset.filter (x ∈ ·)).card := by
    rw [hcnt']; exact card_le_card hfsub
  exact (Nat.even_sub hle).mpr (iff_of_true hA hcnt)

/-- Veblen's theorem, as a cycle cover: induction on the number of edges. -/
theorem veblen {V : Type} [Fintype V] [DecidableEq V] : ∀ (n : ℕ) (G : SimpleGraph V)
    [DecidableRel G.Adj], #G.edgeFinset = n → (∀ v, Even (G.degree v)) →
      ∃ C : Multiset (Cycle G), Arxiv.«2607.06396».IsCycleCover G C ∧
        Arxiv.«2607.06396».totalLength C ≤ #G.edgeFinset := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ hn hev
  classical
  by_cases hE : G.edgeFinset = ∅
  · exact ⟨0, (Arxiv.«2607.06396».isCycleCover_zero_iff G).mpr hE, by simp⟩
  obtain ⟨e, he⟩ := nonempty_iff_ne_empty.mpr hE
  induction e using Sym2.ind with
  | _ a b =>
  have hab : G.Adj a b := mem_edgeFinset.mp he
  obtain ⟨u, c, hc⟩ := exists_cycle G hev hab
  set S : Finset (Sym2 V) := c.edges.toFinset with hS
  set G' := G.deleteEdges (S : Set (Sym2 V)) with hG'
  have hsub : S ⊆ G.edgeFinset := by
    intro e he
    rw [hS, List.mem_toFinset] at he
    exact mem_edgeFinset.mpr (c.edges_subset_edgeSet he)
  have hScard : #S = c.length := by
    rw [hS, List.toFinset_card_of_nodup hc.edges_nodup, Walk.length_edges]
  have h3 : 3 ≤ c.length := hc.three_le_length
  have hE' : G'.edgeFinset = G.edgeFinset \ S := by
    convert edgeFinset_deleteEdges (G := G) S
  have hcard' : #G'.edgeFinset + c.length = #G.edgeFinset := by
    rw [hE', card_sdiff_of_subset hsub, hScard]
    have := card_le_card hsub
    omega
  have hev' : ∀ v, Even (G'.degree v) := fun v => even_degree_delete G hev c hc.isTrail v
  obtain ⟨C', hC', hlen'⟩ := ih #G'.edgeFinset (by omega) G' rfl hev'
  have hle : G' ≤ G := deleteEdges_le _
  let f : Cycle G' → Cycle G := fun d => ⟨d.base, d.walk.mapLe hle, (Walk.isCycle_mapLe hle).mpr d.isCycle⟩
  refine ⟨⟨u, c, hc⟩ ::ₘ C'.map f, ?_, ?_⟩
  · intro e he
    by_cases heS : e ∈ S
    · refine ⟨⟨u, c, hc⟩, Multiset.mem_cons_self _ _, ?_⟩
      rw [hS, List.mem_toFinset] at heS
      exact heS
    · have he' : e ∈ G'.edgeFinset := by rw [hE']; exact mem_sdiff.mpr ⟨he, heS⟩
      obtain ⟨d, hd, hed⟩ := hC' e he'
      refine ⟨f d, Multiset.mem_cons_of_mem (Multiset.mem_map_of_mem f hd), ?_⟩
      show e ∈ (d.walk.mapLe hle).edges
      rw [Walk.edges_mapLe_eq_edges]; exact hed
  · have hmap : Arxiv.«2607.06396».totalLength (C'.map f) = Arxiv.«2607.06396».totalLength C' := by
      simp only [Arxiv.«2607.06396».totalLength, Multiset.map_map]
      congr 1
      apply Multiset.map_congr rfl
      intro d _
      exact Walk.length_mapLe hle d.walk
    have hcons : Arxiv.«2607.06396».totalLength (⟨u, c, hc⟩ ::ₘ C'.map f) =
        c.length + Arxiv.«2607.06396».totalLength (C'.map f) := by
      simp only [Arxiv.«2607.06396».totalLength, Multiset.map_cons, Multiset.sum_cons]
      rfl
    rw [hcons, hmap]
    omega

/-- An edge set of `G` in which every vertex meets an even number of edges is covered by cycles of
`G` of total length at most its size (Veblen applied to the spanning subgraph it forms). -/
lemma even_set_cover {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset (Sym2 V)) (hS : S ⊆ G.edgeFinset)
    (hev : ∀ v, Even (S.filter (v ∈ ·)).card) :
    ∃ C : Multiset (Cycle G), (∀ e ∈ S, ∃ c ∈ C, e ∈ c.edges) ∧
      Arxiv.«2607.06396».totalLength C ≤ #S := by
  classical
  obtain ⟨H, hle, hHset⟩ : ∃ H : SimpleGraph V, H ≤ G ∧ H.edgeSet = (S : Set (Sym2 V)) := by
    refine ⟨SimpleGraph.fromEdgeSet (S : Set (Sym2 V)), ?_, ?_⟩
    · intro a b hab
      rw [fromEdgeSet_adj] at hab
      exact mem_edgeFinset.mp (hS hab.1)
    · ext e
      rw [edgeSet_fromEdgeSet]
      constructor
      · intro h; exact h.1
      · intro h
        refine ⟨h, ?_⟩
        exact G.not_isDiag_of_mem_edgeSet (mem_edgeFinset.mp (hS h))
  have hHE : H.edgeFinset = S := by
    ext e; rw [mem_edgeFinset, hHset]; simp
  have hdeg : ∀ v, Even (H.degree v) := by
    intro v
    rw [← card_incidenceFinset_eq_degree, incidenceFinset_eq_filter, hHE]
    exact hev v
  obtain ⟨C, hC, hlen⟩ := veblen _ H rfl hdeg
  let f : Cycle H → Cycle G := fun d =>
    ⟨d.base, d.walk.mapLe hle, (Walk.isCycle_mapLe hle).mpr d.isCycle⟩
  refine ⟨C.map f, ?_, ?_⟩
  · intro e he
    obtain ⟨d, hd, hed⟩ := hC e (mem_edgeFinset.mpr (by rw [hHset]; exact he))
    refine ⟨f d, Multiset.mem_map_of_mem f hd, ?_⟩
    show e ∈ (d.walk.mapLe hle).edges
    rw [Walk.edges_mapLe_eq_edges]; exact hed
  · have hmap : Arxiv.«2607.06396».totalLength (C.map f) = Arxiv.«2607.06396».totalLength C := by
      simp only [Arxiv.«2607.06396».totalLength, Multiset.map_map]
      congr 1
      apply Multiset.map_congr rfl
      intro d _
      exact Walk.length_mapLe hle d.walk
    rw [hmap]
    calc _ ≤ _ := hlen
      _ = #S := by congr 1

/-- Two even edge sets whose union is all of `E(G)` give a cycle cover of total length at most
`4/3 |E|`: with `X = S`, `Y = T`, `Z = S ∆ T` (also even), every edge lies in exactly two of them,
so the two smallest have total size at most `4/3 |E|`, and any two of them cover `E(G)`. -/
lemma cover_of_two_even {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S T : Finset (Sym2 V)) (hS : S ⊆ G.edgeFinset) (hT : T ⊆ G.edgeFinset)
    (hU : S ∪ T = G.edgeFinset)
    (hSe : ∀ v, Even (S.filter (v ∈ ·)).card) (hTe : ∀ v, Even (T.filter (v ∈ ·)).card) :
    ∃ C : Multiset (Cycle G), Arxiv.«2607.06396».IsCycleCover G C ∧
      3 * Arxiv.«2607.06396».totalLength C ≤ 4 * #G.edgeFinset := by
  classical
  set Z := (S \ T) ∪ (T \ S) with hZdef
  have hZ : Z ⊆ G.edgeFinset := by
    intro e he
    rcases mem_union.mp he with h | h
    · exact hS (mem_sdiff.mp h).1
    · exact hT (mem_sdiff.mp h).1
  have hZe : ∀ v, Even (Z.filter (v ∈ ·)).card := by
    intro v
    have h1 : (Z.filter (v ∈ ·)).card + 2 * ((S ∩ T).filter (v ∈ ·)).card =
        (S.filter (v ∈ ·)).card + (T.filter (v ∈ ·)).card := by
      have a1 : (S.filter (v ∈ ·)).card = ((S \ T).filter (v ∈ ·)).card + ((S ∩ T).filter (v ∈ ·)).card := by
        rw [← card_union_of_disjoint]
        · congr 1; ext e; simp only [mem_filter, mem_union, mem_sdiff, mem_inter]; tauto
        · rw [Finset.disjoint_left]; intro e h1 h2
          simp only [mem_filter, mem_sdiff, mem_inter] at h1 h2; tauto
      have a2 : (T.filter (v ∈ ·)).card = ((T \ S).filter (v ∈ ·)).card + ((S ∩ T).filter (v ∈ ·)).card := by
        rw [← card_union_of_disjoint]
        · congr 1; ext e; simp only [mem_filter, mem_union, mem_sdiff, mem_inter]; tauto
        · rw [Finset.disjoint_left]; intro e h1 h2
          simp only [mem_filter, mem_sdiff, mem_inter] at h1 h2; tauto
      have a3 : (Z.filter (v ∈ ·)).card = ((S \ T).filter (v ∈ ·)).card + ((T \ S).filter (v ∈ ·)).card := by
        rw [hZdef, filter_union, card_union_of_disjoint]
        rw [Finset.disjoint_left]; intro e h1 h2
        simp only [mem_filter, mem_sdiff] at h1 h2; tauto
      omega
    have hs := hSe v
    have ht := hTe v
    rcases hs with ⟨a, ha⟩
    rcases ht with ⟨b, hb⟩
    exact ⟨a + b - ((S ∩ T).filter (v ∈ ·)).card, by omega⟩
  -- sizes: each edge in exactly two of S, T, Z
  have hsum : #S + #T + #Z = 2 * #G.edgeFinset := by
    have b1 := Finset.card_sdiff_add_card_inter S T
    have b2 := Finset.card_sdiff_add_card_inter T S
    rw [Finset.inter_comm] at b2
    have b3 : #Z = #(S \ T) + #(T \ S) := by
      rw [hZdef, card_union_of_disjoint]
      rw [Finset.disjoint_left]; intro e h1 h2; simp only [mem_sdiff] at h1 h2; tauto
    have b4 := Finset.card_union_add_card_inter S T
    rw [hU] at b4
    omega
  -- any two of the three sets cover all edges
  have pair (X Y : Finset (Sym2 V)) (hX : X ⊆ G.edgeFinset) (hY : Y ⊆ G.edgeFinset)
      (hXe : ∀ v, Even (X.filter (v ∈ ·)).card) (hYe : ∀ v, Even (Y.filter (v ∈ ·)).card)
      (hXY : ∀ e ∈ G.edgeFinset, e ∈ X ∨ e ∈ Y) (hsz : 3 * (#X + #Y) ≤ 4 * #G.edgeFinset) :
      ∃ C : Multiset (Cycle G), Arxiv.«2607.06396».IsCycleCover G C ∧
        3 * Arxiv.«2607.06396».totalLength C ≤ 4 * #G.edgeFinset := by
    obtain ⟨C1, h1, l1⟩ := even_set_cover G X hX hXe
    obtain ⟨C2, h2, l2⟩ := even_set_cover G Y hY hYe
    refine ⟨C1 + C2, ?_, ?_⟩
    · intro e he
      rcases hXY e he with h | h
      · obtain ⟨c, hc, hce⟩ := h1 e h
        exact ⟨c, Multiset.mem_add.mpr (Or.inl hc), hce⟩
      · obtain ⟨c, hc, hce⟩ := h2 e h
        exact ⟨c, Multiset.mem_add.mpr (Or.inr hc), hce⟩
    · rw [Arxiv.«2607.06396».totalLength_add]
      omega
  have memZ : ∀ e, e ∈ Z ↔ (e ∈ S ∧ e ∉ T) ∨ (e ∈ T ∧ e ∉ S) := by
    intro e; simp [hZdef, mem_union, mem_sdiff]
  have inU : ∀ e ∈ G.edgeFinset, e ∈ S ∨ e ∈ T := by
    intro e he; rw [← hU] at he; exact mem_union.mp he
  by_cases c1 : 3 * (#S + #T) ≤ 4 * #G.edgeFinset
  · exact pair S T hS hT hSe hTe inU c1
  by_cases c2 : 3 * (#S + #Z) ≤ 4 * #G.edgeFinset
  · refine pair S Z hS hZ hSe hZe ?_ c2
    intro e he
    rcases inU e he with h | h
    · exact Or.inl h
    · by_cases hs : e ∈ S
      · exact Or.inl hs
      · exact Or.inr ((memZ e).mpr (Or.inr ⟨h, hs⟩))
  · refine pair T Z hT hZ hTe hZe ?_ (by omega)
    intro e he
    rcases inU e he with h | h
    · by_cases ht : e ∈ T
      · exact Or.inl ht
      · exact Or.inr ((memZ e).mpr (Or.inl ⟨h, ht⟩))
    · exact Or.inl h



/-- A closed trail is covered by cycles of total length at most its length. -/
lemma trail_cover {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {u : V} (c : G.Walk u u) (hc : c.IsTrail) :
    ∃ C : Multiset (Cycle G), (∀ e ∈ c.edges, ∃ d ∈ C, e ∈ d.edges) ∧
      Arxiv.«2607.06396».totalLength C ≤ c.length := by
  set S : Finset (Sym2 V) := c.edges.toFinset with hS
  have hsub : S ⊆ G.edgeFinset := by
    intro e he
    rw [hS, List.mem_toFinset] at he
    exact mem_edgeFinset.mpr (c.edges_subset_edgeSet he)
  have hev : ∀ x, Even (S.filter (x ∈ ·)).card := by
    intro x
    have hcnt : Even (c.edges.countP fun e => decide (x ∈ e)) :=
      (hc.even_countP_edges_iff x).mpr (fun h => absurd rfl h)
    have hcnt' : (c.edges.countP fun e => decide (x ∈ e)) = (S.filter (x ∈ ·)).card := by
      rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hc.edges_nodup.filter _),
        hS, List.toFinset_filter]
      simp
    rw [← hcnt']; exact hcnt
  obtain ⟨C, hC, hl⟩ := even_set_cover G S hsub hev
  refine ⟨C, fun e he => hC e (by rw [hS, List.mem_toFinset]; exact he), ?_⟩
  have : #S = c.length := by
    rw [hS, List.toFinset_card_of_nodup hc.edges_nodup, Walk.length_edges]
  omega

/-- Covers transfer along a graph homomorphism that is injective on edges and hits every edge:
each cycle maps to a closed trail, which Veblen splits into cycles. -/
lemma cover_transfer {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (G' : SimpleGraph W) [DecidableRel G'.Adj]
    (f : G' →g G)
    (hinj : ∀ e₁ ∈ G'.edgeSet, ∀ e₂ ∈ G'.edgeSet, e₁.map f = e₂.map f → e₁ = e₂)
    (hsurj : ∀ e ∈ G.edgeSet, ∃ e' ∈ G'.edgeSet, e'.map f = e)
    (C' : Multiset (Cycle G')) (hC' : Arxiv.«2607.06396».IsCycleCover G' C') :
    ∃ C : Multiset (Cycle G), Arxiv.«2607.06396».IsCycleCover G C ∧
      Arxiv.«2607.06396».totalLength C ≤ Arxiv.«2607.06396».totalLength C' := by
  have key : ∀ D : Multiset (Cycle G'), ∃ C : Multiset (Cycle G),
      (∀ d ∈ D, ∀ e ∈ d.edges, ∃ c ∈ C, Sym2.map f e ∈ c.edges) ∧
      Arxiv.«2607.06396».totalLength C ≤ Arxiv.«2607.06396».totalLength D := by
    intro D
    induction D using Multiset.induction_on with
    | empty => exact ⟨0, by simp, by simp⟩
    | cons d D ih =>
      obtain ⟨C, hC, hl⟩ := ih
      have htr : (d.walk.map f).IsTrail := by
        rw [Walk.isTrail_def, Walk.edges_map]
        refine List.Nodup.map_on ?_ d.isCycle.isTrail.edges_nodup
        intro x hx y hy hxy
        exact hinj x (d.walk.edges_subset_edgeSet hx) y (d.walk.edges_subset_edgeSet hy) hxy
      obtain ⟨E, hE, hlE⟩ := trail_cover G _ htr
      refine ⟨E + C, ?_, ?_⟩
      · intro d' hd' e he
        rcases Multiset.mem_cons.mp hd' with h | h
        · subst h
          obtain ⟨c, hc, hce⟩ := hE (Sym2.map f e) (by
            rw [Walk.edges_map]; exact List.mem_map_of_mem he)
          exact ⟨c, Multiset.mem_add.mpr (Or.inl hc), hce⟩
        · obtain ⟨c, hc, hce⟩ := hC d' h e he
          exact ⟨c, Multiset.mem_add.mpr (Or.inr hc), hce⟩
      · rw [Arxiv.«2607.06396».totalLength_add]
        simp only [Arxiv.«2607.06396».totalLength, Multiset.map_cons, Multiset.sum_cons] at hl hlE ⊢
        rw [Walk.length_map] at hlE
        have : d.length = d.walk.length := rfl
        omega
  obtain ⟨C, hC, hl⟩ := key C'
  refine ⟨C, ?_, hl⟩
  intro e he
  obtain ⟨e', he', rfl⟩ := hsurj e (mem_edgeFinset.mp he)
  obtain ⟨d, hd, hde⟩ := hC' e' (mem_edgeFinset.mpr he')
  exact hC d hd e' hde


/-- Two even edge sets `S`, `T` (not necessarily covering `G`): their union is covered by cycles of
total length at most `4/3 |S ∪ T|` (the two smallest of `S`, `T`, `S ∆ T`). -/
lemma cover_union_two_even {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S T : Finset (Sym2 V)) (hS : S ⊆ G.edgeFinset) (hT : T ⊆ G.edgeFinset)
    (hSe : ∀ v, Even (S.filter (v ∈ ·)).card) (hTe : ∀ v, Even (T.filter (v ∈ ·)).card) :
    ∃ C : Multiset (Cycle G), (∀ e ∈ S ∪ T, ∃ c ∈ C, e ∈ c.edges) ∧
      3 * Arxiv.«2607.06396».totalLength C ≤ 4 * #(S ∪ T) := by
  classical
  set Z := (S \ T) ∪ (T \ S) with hZdef
  have hZ : Z ⊆ G.edgeFinset := by
    intro e he
    rcases mem_union.mp he with h | h
    · exact hS (mem_sdiff.mp h).1
    · exact hT (mem_sdiff.mp h).1
  have hZe : ∀ v, Even (Z.filter (v ∈ ·)).card := by
    intro v
    have a1 : (S.filter (v ∈ ·)).card = ((S \ T).filter (v ∈ ·)).card + ((S ∩ T).filter (v ∈ ·)).card := by
      rw [← card_union_of_disjoint]
      · congr 1; ext e; simp only [mem_filter, mem_union, mem_sdiff, mem_inter]; tauto
      · rw [Finset.disjoint_left]; intro e h1 h2
        simp only [mem_filter, mem_sdiff, mem_inter] at h1 h2; tauto
    have a2 : (T.filter (v ∈ ·)).card = ((T \ S).filter (v ∈ ·)).card + ((S ∩ T).filter (v ∈ ·)).card := by
      rw [← card_union_of_disjoint]
      · congr 1; ext e; simp only [mem_filter, mem_union, mem_sdiff, mem_inter]; tauto
      · rw [Finset.disjoint_left]; intro e h1 h2
        simp only [mem_filter, mem_sdiff, mem_inter] at h1 h2; tauto
    have a3 : (Z.filter (v ∈ ·)).card = ((S \ T).filter (v ∈ ·)).card + ((T \ S).filter (v ∈ ·)).card := by
      rw [hZdef, filter_union, card_union_of_disjoint]
      rw [Finset.disjoint_left]; intro e h1 h2
      simp only [mem_filter, mem_sdiff] at h1 h2; tauto
    rcases hSe v with ⟨a, ha⟩
    rcases hTe v with ⟨b, hb⟩
    exact ⟨a + b - ((S ∩ T).filter (v ∈ ·)).card, by omega⟩
  have hsum : #S + #T + #Z = 2 * #(S ∪ T) := by
    have b1 := Finset.card_sdiff_add_card_inter S T
    have b2 := Finset.card_sdiff_add_card_inter T S
    rw [Finset.inter_comm] at b2
    have b3 : #Z = #(S \ T) + #(T \ S) := by
      rw [hZdef, card_union_of_disjoint]
      rw [Finset.disjoint_left]; intro e h1 h2; simp only [mem_sdiff] at h1 h2; tauto
    have b4 := Finset.card_union_add_card_inter S T
    omega
  have pair (X Y : Finset (Sym2 V)) (hX : X ⊆ G.edgeFinset) (hY : Y ⊆ G.edgeFinset)
      (hXe : ∀ v, Even (X.filter (v ∈ ·)).card) (hYe : ∀ v, Even (Y.filter (v ∈ ·)).card)
      (hXY : ∀ e ∈ S ∪ T, e ∈ X ∨ e ∈ Y) (hsz : 3 * (#X + #Y) ≤ 4 * #(S ∪ T)) :
      ∃ C : Multiset (Cycle G), (∀ e ∈ S ∪ T, ∃ c ∈ C, e ∈ c.edges) ∧
        3 * Arxiv.«2607.06396».totalLength C ≤ 4 * #(S ∪ T) := by
    obtain ⟨C1, h1, l1⟩ := even_set_cover G X hX hXe
    obtain ⟨C2, h2, l2⟩ := even_set_cover G Y hY hYe
    refine ⟨C1 + C2, ?_, ?_⟩
    · intro e he
      rcases hXY e he with h | h
      · obtain ⟨c, hc, hce⟩ := h1 e h
        exact ⟨c, Multiset.mem_add.mpr (Or.inl hc), hce⟩
      · obtain ⟨c, hc, hce⟩ := h2 e h
        exact ⟨c, Multiset.mem_add.mpr (Or.inr hc), hce⟩
    · rw [Arxiv.«2607.06396».totalLength_add]
      omega
  have memZ : ∀ e, e ∈ Z ↔ (e ∈ S ∧ e ∉ T) ∨ (e ∈ T ∧ e ∉ S) := by
    intro e; simp [hZdef, mem_union, mem_sdiff]
  have inU : ∀ e ∈ S ∪ T, e ∈ S ∨ e ∈ T := fun e he => mem_union.mp he
  by_cases c1 : 3 * (#S + #T) ≤ 4 * #(S ∪ T)
  · exact pair S T hS hT hSe hTe inU c1
  by_cases c2 : 3 * (#S + #Z) ≤ 4 * #(S ∪ T)
  · refine pair S Z hS hZ hSe hZe ?_ c2
    intro e he
    rcases inU e he with h | h
    · exact Or.inl h
    · by_cases hs : e ∈ S
      · exact Or.inl hs
      · exact Or.inr ((memZ e).mpr (Or.inr ⟨h, hs⟩))
  · refine pair T Z hT hZ hTe hZe ?_ (by omega)
    intro e he
    rcases inU e he with h | h
    · by_cases ht : e ∈ T
      · exact Or.inl ht
      · exact Or.inr ((memZ e).mpr (Or.inl ⟨h, ht⟩))
    · exact Or.inl h

/-- Near a 4-flow: two even sets `S`, `T` plus cycles `D` through the remaining edges give a cover of
length at most `4/3 |S ∪ T| + len D`. -/
lemma cover_of_near_two_even {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S T : Finset (Sym2 V)) (hS : S ⊆ G.edgeFinset) (hT : T ⊆ G.edgeFinset)
    (hSe : ∀ v, Even (S.filter (v ∈ ·)).card) (hTe : ∀ v, Even (T.filter (v ∈ ·)).card)
    (D : Multiset (Cycle G)) (hD : ∀ e ∈ G.edgeFinset, e ∉ S ∪ T → ∃ c ∈ D, e ∈ c.edges) :
    ∃ C : Multiset (Cycle G), Arxiv.«2607.06396».IsCycleCover G C ∧
      3 * Arxiv.«2607.06396».totalLength C ≤
        4 * #(S ∪ T) + 3 * Arxiv.«2607.06396».totalLength D := by
  obtain ⟨C, hC, hl⟩ := cover_union_two_even G S T hS hT hSe hTe
  refine ⟨C + D, ?_, ?_⟩
  · intro e he
    by_cases h : e ∈ S ∪ T
    · obtain ⟨c, hc, hce⟩ := hC e h
      exact ⟨c, Multiset.mem_add.mpr (Or.inl hc), hce⟩
    · obtain ⟨c, hc, hce⟩ := hD e he h
      exact ⟨c, Multiset.mem_add.mpr (Or.inr hc), hce⟩
  · rw [Arxiv.«2607.06396».totalLength_add]
    omega

/-! ## Splitting a vertex: moving two edges `vu`, `vw` to a new vertex `none` of `Option V`.
`G'` is any graph on `Option V` with the adjacencies of the split graph (`hss`, `hns`). -/

lemma sp_adj_sn {V : Type} (G' : SimpleGraph (Option V)) (u w : V)
    (hns : ∀ b, G'.Adj none (some b) ↔ b = u ∨ b = w) (b : V) :
    G'.Adj (some b) none ↔ b = u ∨ b = w := by
  rw [adj_comm]; exact hns b

lemma sp_adj_map {V : Type} (G : SimpleGraph V) (v u w : V) (G' : SimpleGraph (Option V))
    (hss : ∀ a b, G'.Adj (some a) (some b) ↔ G.Adj a b ∧ s(a, b) ≠ s(v, u) ∧ s(a, b) ≠ s(v, w))
    (hns : ∀ b, G'.Adj none (some b) ↔ b = u ∨ b = w) (hu : G.Adj v u) (hw : G.Adj v w)
    {x y : Option V} (h : G'.Adj x y) : G.Adj (x.getD v) (y.getD v) := by
  rcases x with _ | a <;> rcases y with _ | b
  · exact absurd h (G'.irrefl)
  · rcases (hns b).mp h with rfl | rfl <;> assumption
  · rcases (sp_adj_sn G' u w hns a).mp h with rfl | rfl
    · exact hu.symm
    · exact hw.symm
  · exact ((hss a b).mp h).1

lemma sp_map_mem {V : Type} (G : SimpleGraph V) (v u w : V) (G' : SimpleGraph (Option V))
    (hss : ∀ a b, G'.Adj (some a) (some b) ↔ G.Adj a b ∧ s(a, b) ≠ s(v, u) ∧ s(a, b) ≠ s(v, w))
    (hns : ∀ b, G'.Adj none (some b) ↔ b = u ∨ b = w) (hu : G.Adj v u) (hw : G.Adj v w)
    (e : Sym2 (Option V)) (he : e ∈ G'.edgeSet) :
    e.map (fun x => x.getD v) ∈ G.edgeSet := by
  induction e using Sym2.ind with
  | _ x y => exact sp_adj_map G v u w G' hss hns hu hw he

lemma sp_map_injOn {V : Type} [DecidableEq V] (G : SimpleGraph V) (v u w : V)
    (G' : SimpleGraph (Option V))
    (hss : ∀ a b, G'.Adj (some a) (some b) ↔ G.Adj a b ∧ s(a, b) ≠ s(v, u) ∧ s(a, b) ≠ s(v, w))
    (hns : ∀ b, G'.Adj none (some b) ↔ b = u ∨ b = w) (huw : u ≠ w) :
    ∀ e₁ ∈ G'.edgeSet, ∀ e₂ ∈ G'.edgeSet,
      e₁.map (fun x => x.getD v) = e₂.map (fun x => x.getD v) → e₁ = e₂ := by
  have hvw : s(v, w) ≠ s(v, u) := by
    intro h; rcases Sym2.eq_iff.mp h with h | h
    · exact huw h.2.symm
    · exact huw (h.1.symm.trans h.2.symm)
  have key : ∀ e ∈ G'.edgeSet, (fun f : Sym2 V => if f = s(v, u) then s(none, some u) else
      if f = s(v, w) then s(none, some w) else f.map some) (e.map (fun x => x.getD v)) = e := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
    rw [mem_edgeSet] at he
    rcases x with _ | a <;> rcases y with _ | b
    · exact absurd he (G'.irrefl)
    · rcases (hns b).mp he with rfl | rfl
      · simp
      · simp [hvw]
    · rcases (sp_adj_sn G' u w hns a).mp he with rfl | rfl
      · simp [Sym2.eq_swap]
      · simp [Sym2.eq_swap, hvw]
    · obtain ⟨_, h1, h2⟩ := (hss a b).mp he
      simp [h1, h2]
  intro e₁ h₁ e₂ h₂ h
  rw [← key e₁ h₁, ← key e₂ h₂, h]

lemma sp_map_surj {V : Type} (G : SimpleGraph V) (v u w : V) (G' : SimpleGraph (Option V))
    (hss : ∀ a b, G'.Adj (some a) (some b) ↔ G.Adj a b ∧ s(a, b) ≠ s(v, u) ∧ s(a, b) ≠ s(v, w))
    (hns : ∀ b, G'.Adj none (some b) ↔ b = u ∨ b = w) :
    ∀ e ∈ G.edgeSet, ∃ e' ∈ G'.edgeSet, e'.map (fun x => x.getD v) = e := by
  intro e he
  by_cases h1 : e = s(v, u)
  · subst h1
    exact ⟨s(none, some u), (hns u).mpr (Or.inl rfl), by simp⟩
  by_cases h2 : e = s(v, w)
  · subst h2
    exact ⟨s(none, some w), (hns w).mpr (Or.inr rfl), by simp⟩
  induction e using Sym2.ind with
  | _ a b =>
  exact ⟨s(some a, some b), (hss a b).mpr ⟨he, h1, h2⟩, by simp⟩

lemma sp_deg_eq_filter {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (x : W) : H.degree x = #(H.edgeFinset.filter (x ∈ ·)) := by
  rw [← card_incidenceFinset_eq_degree, incidenceFinset_eq_filter]

lemma sp_image_edgeFinset {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v u w : V) (G' : SimpleGraph (Option V)) [DecidableRel G'.Adj]
    (hss : ∀ a b, G'.Adj (some a) (some b) ↔ G.Adj a b ∧ s(a, b) ≠ s(v, u) ∧ s(a, b) ≠ s(v, w))
    (hns : ∀ b, G'.Adj none (some b) ↔ b = u ∨ b = w) (hu : G.Adj v u) (hw : G.Adj v w) :
    G'.edgeFinset.image (Sym2.map (fun x => x.getD v)) = G.edgeFinset := by
  ext e
  simp only [mem_image, mem_edgeFinset]
  constructor
  · rintro ⟨e', he', rfl⟩
    exact sp_map_mem G v u w G' hss hns hu hw e' he'
  · intro he
    exact sp_map_surj G v u w G' hss hns e he

lemma sp_card_edgeFinset {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v u w : V) (G' : SimpleGraph (Option V)) [DecidableRel G'.Adj]
    (hss : ∀ a b, G'.Adj (some a) (some b) ↔ G.Adj a b ∧ s(a, b) ≠ s(v, u) ∧ s(a, b) ≠ s(v, w))
    (hns : ∀ b, G'.Adj none (some b) ↔ b = u ∨ b = w) (hu : G.Adj v u) (hw : G.Adj v w)
    (huw : u ≠ w) : #G'.edgeFinset = #G.edgeFinset := by
  rw [← sp_image_edgeFinset G v u w G' hss hns hu hw, card_image_of_injOn]
  intro a ha b hb h
  exact sp_map_injOn G v u w G' hss hns huw a (mem_edgeFinset.mp ha) b (mem_edgeFinset.mp hb) h

lemma sp_filter_card {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v u w : V) (G' : SimpleGraph (Option V)) [DecidableRel G'.Adj]
    (hss : ∀ a b, G'.Adj (some a) (some b) ↔ G.Adj a b ∧ s(a, b) ≠ s(v, u) ∧ s(a, b) ≠ s(v, w))
    (hns : ∀ b, G'.Adj none (some b) ↔ b = u ∨ b = w) (hu : G.Adj v u) (hw : G.Adj v w)
    (huw : u ≠ w) (x : V) :
    #(G.edgeFinset.filter (x ∈ ·)) =
      #(G'.edgeFinset.filter (fun e => x ∈ e.map (fun y => y.getD v))) := by
  rw [← sp_image_edgeFinset G v u w G' hss hns hu hw, filter_image, card_image_of_injOn]
  intro a ha b hb h
  exact sp_map_injOn G v u w G' hss hns huw a (mem_edgeFinset.mp (mem_filter.mp ha).1) b
    (mem_edgeFinset.mp (mem_filter.mp hb).1) h

lemma sp_degree_some {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v u w : V) (G' : SimpleGraph (Option V)) [DecidableRel G'.Adj]
    (hss : ∀ a b, G'.Adj (some a) (some b) ↔ G.Adj a b ∧ s(a, b) ≠ s(v, u) ∧ s(a, b) ≠ s(v, w))
    (hns : ∀ b, G'.Adj none (some b) ↔ b = u ∨ b = w) (hu : G.Adj v u) (hw : G.Adj v w)
    (huw : u ≠ w) (x : V) (hx : x ≠ v) : G'.degree (some x) = G.degree x := by
  rw [sp_deg_eq_filter, sp_deg_eq_filter, sp_filter_card G v u w G' hss hns hu hw huw]
  congr 1
  apply filter_congr
  intro e _
  rw [Sym2.mem_map]
  constructor
  · intro h; exact ⟨some x, h, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rcases y with _ | z
    · exact absurd hyx.symm hx
    · have : z = x := hyx
      subst this; exact hy

lemma sp_degree_none {V : Type} [Fintype V] [DecidableEq V] (u w : V)
    (G' : SimpleGraph (Option V)) [DecidableRel G'.Adj]
    (hns : ∀ b, G'.Adj none (some b) ↔ b = u ∨ b = w) (huw : u ≠ w) : G'.degree none = 2 := by
  rw [← card_neighborFinset_eq_degree]
  have : G'.neighborFinset none = {some u, some w} := by
    ext y
    rw [mem_neighborFinset]
    rcases y with _ | b
    · simp [G'.irrefl]
    · rw [hns]; simp
  rw [this, card_pair (by simpa using huw)]

lemma sp_degree_v {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v u w : V) (G' : SimpleGraph (Option V)) [DecidableRel G'.Adj]
    (hss : ∀ a b, G'.Adj (some a) (some b) ↔ G.Adj a b ∧ s(a, b) ≠ s(v, u) ∧ s(a, b) ≠ s(v, w))
    (hns : ∀ b, G'.Adj none (some b) ↔ b = u ∨ b = w) (hu : G.Adj v u) (hw : G.Adj v w)
    (huw : u ≠ w) : G.degree v = G'.degree (some v) + 2 := by
  rw [← sp_degree_none u w G' hns huw, sp_deg_eq_filter, sp_deg_eq_filter, sp_deg_eq_filter,
    sp_filter_card G v u w G' hss hns hu hw huw, ← card_union_of_disjoint]
  · congr 1
    ext e
    simp only [mem_filter, mem_union, Sym2.mem_map]
    constructor
    · rintro ⟨he, y, hy, hyv⟩
      rcases y with _ | z
      · exact Or.inr ⟨he, hy⟩
      · have : z = v := hyv
        subst this; exact Or.inl ⟨he, hy⟩
    · rintro (⟨he, hy⟩ | ⟨he, hy⟩)
      · exact ⟨he, some v, hy, rfl⟩
      · exact ⟨he, none, hy, rfl⟩
  · rw [Finset.disjoint_left]
    intro e h1 h2
    simp only [mem_filter, mem_edgeFinset] at h1 h2
    have hne : (some v : Option V) ≠ none := by simp
    have : e = s(some v, none) := (Sym2.mem_and_mem_iff hne).mp ⟨h1.2, h2.2⟩
    rw [this, mem_edgeSet, sp_adj_sn G' u w hns] at h1
    rcases h1.1 with h | h
    · exact hu.ne h
    · exact hw.ne h

/-- The subcubic graphs with an odd vertex and a vertex of degree two whose edges are not the
union of two even edge sets, nor two even sets plus cycles of total length at most `|E|/15`. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsBridgeless → (∃ v, Odd (G.degree v)) → (∀ v, G.degree v ≤ 3) → (∃ v, G.degree v = 2) →
    (¬ ∃ S T : Finset (Sym2 V), S ⊆ G.edgeFinset ∧ T ⊆ G.edgeFinset ∧ S ∪ T = G.edgeFinset ∧
      (∀ v, Even (S.filter (v ∈ ·)).card) ∧ (∀ v, Even (T.filter (v ∈ ·)).card)) →
    (¬ ∃ (S T : Finset (Sym2 V)) (D : Multiset (Cycle G)), S ⊆ G.edgeFinset ∧ T ⊆ G.edgeFinset ∧
      (∀ v, Even (S.filter (v ∈ ·)).card) ∧ (∀ v, Even (T.filter (v ∈ ·)).card) ∧
      (∀ e ∈ G.edgeFinset, e ∉ S ∪ T → ∃ c ∈ D, e ∈ c.edges) ∧
      15 * Arxiv.«2607.06396».totalLength D ≤ #G.edgeFinset) →
      ∃ C : Multiset (Cycle G), Arxiv.«2607.06396».IsCycleCover G C ∧
        (Arxiv.«2607.06396».totalLength C : ℚ) ≤ 7 / 5 * #G.edgeFinset

/-- Fleischner's splitting lemma: at a vertex `v` of degree at least four of a bridgeless graph,
some two edges `vu`, `vw` can be moved to a new vertex (`none`) without creating a bridge. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsBridgeless → ∀ v : V, 4 ≤ G.degree v →
      ∃ u w : V, u ≠ w ∧ G.Adj v u ∧ G.Adj v w ∧
        (SimpleGraph.fromRel (fun x y : Option V => match x, y with
          | some a, some b => G.Adj a b ∧ s(a, b) ≠ s(v, u) ∧ s(a, b) ≠ s(v, w)
          | none, some b => b = u ∨ b = w
          | _, _ => False)).IsBridgeless

lemma all_cases (h1 : H1) (h2 : H2) : ∀ (n : ℕ) (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj], ∑ x, (G.degree x - 3) = n → G.IsBridgeless →
    (∃ v, Odd (G.degree v)) → ((∃ v, 4 ≤ G.degree v) ∨ (∃ v, G.degree v = 2)) →
      ∃ C : Multiset (Cycle G), Arxiv.«2607.06396».IsCycleCover G C ∧
        (Arxiv.«2607.06396».totalLength C : ℚ) ≤ 7 / 5 * #G.edgeFinset := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ G _ hμ hb hodd h42
  by_cases h2e : ∃ S T : Finset (Sym2 V), S ⊆ G.edgeFinset ∧ T ⊆ G.edgeFinset ∧
      S ∪ T = G.edgeFinset ∧ (∀ v, Even (S.filter (v ∈ ·)).card) ∧
      (∀ v, Even (T.filter (v ∈ ·)).card)
  · obtain ⟨S, T, hS, hT, hU, hSe, hTe⟩ := h2e
    obtain ⟨C, hC, hl⟩ := cover_of_two_even G S T hS hT hU hSe hTe
    refine ⟨C, hC, ?_⟩
    have hq : (3 * Arxiv.«2607.06396».totalLength C : ℚ) ≤ 4 * #G.edgeFinset := by exact_mod_cast hl
    have : (0 : ℚ) ≤ #G.edgeFinset := by positivity
    linarith
  by_cases hw : ∃ (S T : Finset (Sym2 V)) (D : Multiset (Cycle G)), S ⊆ G.edgeFinset ∧
      T ⊆ G.edgeFinset ∧ (∀ v, Even (S.filter (v ∈ ·)).card) ∧
      (∀ v, Even (T.filter (v ∈ ·)).card) ∧
      (∀ e ∈ G.edgeFinset, e ∉ S ∪ T → ∃ c ∈ D, e ∈ c.edges) ∧
      15 * Arxiv.«2607.06396».totalLength D ≤ #G.edgeFinset
  · obtain ⟨S, T, D, hS, hT, hSe, hTe, hD, hl⟩ := hw
    obtain ⟨C, hC, hlC⟩ := cover_of_near_two_even G S T hS hT hSe hTe D hD
    refine ⟨C, hC, ?_⟩
    have hU : #(S ∪ T) ≤ #G.edgeFinset := card_le_card (union_subset hS hT)
    have : 15 * Arxiv.«2607.06396».totalLength C ≤ 21 * #G.edgeFinset := by omega
    have hq : (15 * Arxiv.«2607.06396».totalLength C : ℚ) ≤ 21 * #G.edgeFinset := by
      exact_mod_cast this
    linarith
  by_cases hsub : ∀ v, G.degree v ≤ 3
  · have h2v : ∃ v, G.degree v = 2 := by
      rcases h42 with ⟨v, hv⟩ | h
      · exact absurd (hsub v) (by omega)
      · exact h
    exact h1 V G hb hodd hsub h2v h2e hw
  push_neg at hsub
  obtain ⟨v, hv⟩ := hsub
  obtain ⟨u, w, huw, hu, hw, hbr⟩ := h2 V G hb v hv
  classical
  set G' : SimpleGraph (Option V) := SimpleGraph.fromRel (fun x y : Option V => match x, y with
          | some a, some b => G.Adj a b ∧ s(a, b) ≠ s(v, u) ∧ s(a, b) ≠ s(v, w)
          | none, some b => b = u ∨ b = w
          | _, _ => False) with hG'
  have hss : ∀ a b, G'.Adj (some a) (some b) ↔
      G.Adj a b ∧ s(a, b) ≠ s(v, u) ∧ s(a, b) ≠ s(v, w) := by
    intro a b
    rw [hG', fromRel_adj]
    simp only [ne_eq, Option.some.injEq]
    constructor
    · rintro ⟨_, h | h⟩
      · exact h
      · refine ⟨h.1.symm, ?_, ?_⟩
        · rw [Sym2.eq_swap]; exact h.2.1
        · rw [Sym2.eq_swap]; exact h.2.2
    · intro h
      exact ⟨h.1.ne, Or.inl h⟩
  have hns : ∀ b, G'.Adj none (some b) ↔ b = u ∨ b = w := by
    intro b
    rw [hG', fromRel_adj]
    simp
  have hdv := sp_degree_v G v u w G' hss hns hu hw huw
  have hds := sp_degree_some G v u w G' hss hns hu hw huw
  have hdn := sp_degree_none u w G' hns huw
  have hlt : ∑ x, (G'.degree x - 3) < n := by
    rw [Fintype.sum_option, hdn, ← hμ, Nat.zero_add]
    apply Finset.sum_lt_sum
    · intro x _
      by_cases hx : x = v
      · subst hx; omega
      · rw [hds x hx]
    · exact ⟨v, mem_univ _, by omega⟩
  have hodd' : ∃ x, Odd (G'.degree x) := by
    obtain ⟨x, hx⟩ := hodd
    by_cases hxv : x = v
    · subst hxv
      refine ⟨some x, ?_⟩
      rw [hdv] at hx
      obtain ⟨k, hk⟩ := hx
      exact ⟨k - 1, by omega⟩
    · exact ⟨some x, by rw [hds x hxv]; exact hx⟩
  obtain ⟨C', hC', hl'⟩ := ih _ hlt (Option V) G' rfl hbr hodd' (Or.inr ⟨none, hdn⟩)
  obtain ⟨C, hC, hl⟩ := cover_transfer G G'
    ⟨fun x => x.getD v, fun h => sp_adj_map G v u w G' hss hns hu hw h⟩
    (sp_map_injOn G v u w G' hss hns huw) (sp_map_surj G v u w G' hss hns) C' hC'
  refine ⟨C, hC, ?_⟩
  rw [sp_card_edgeFinset G v u w G' hss hns hu hw huw] at hl'
  have : (Arxiv.«2607.06396».totalLength C : ℚ) ≤ Arxiv.«2607.06396».totalLength C' := by
    exact_mod_cast hl
  linarith

theorem main : H1 → H2 → OMA.R_Arxiv_2607_06396_alon_tarsi_short_cycle_cover_R1_H2_R1.H2 := by
  intro h1 h2 V _ _ G _ hb hodd h4 _
  exact all_cases h1 h2 _ V G rfl hb hodd (Or.inl h4)

end OMA.R_Arxiv_2607_06396_alon_tarsi_short_cycle_cover_R1_H2_R1_H2_R1
