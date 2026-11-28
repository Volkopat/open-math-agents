import OMAReductions.R_Arxiv_2607_06396_alon_tarsi_short_cycle_cover_R1_H2_R1_H1_R1

-- Reduction Arxiv.2607.06396.alon_tarsi_short_cycle_cover.R1.H2.R1.H1.R1.H1.R1 of step Arxiv.2607.06396.alon_tarsi_short_cycle_cover.R1.H2.R1.H1.R1.H1
-- Credit: @sovrana

/-!
# Alon-Tarsi snark core: heavy edges on short cycles

Call an edge `pq` of a cubic graph heavy if it lies in no triangle and `G - p - q` is
3-edge-colourable (almost every snark edge is heavy: snarks are usually critical). Proved below
(`heavy_edge`): for a heavy edge, two even edge sets cover every edge except possibly `pq`
(the unions of two colour classes, repaired at the double star of `pq`, `fix_parity`). With a
cycle `c` through `pq` and Veblen's theorem this gives a cycle cover of length at most
`4/3 (|E| - 1) + len c`, hence `7/5 |E|` as soon as `15 len c ≤ |E| + 20`: for example every
cubic graph with at least 55 edges and a heavy edge on a pentagon (compare Karabas, Macajova,
Nedela and Skoviera 2025, who get `4/3 |E| + 1` for heavy pentagons by structure theory).
What is left is split by whether the graph has a heavy edge at all:
* `H1`: a heavy edge exists, but every cycle through a heavy edge is longer than `(|E| + 20)/15`;
* `H2`: no heavy edge (or a vertex of degree zero).
-/

open Finset SimpleGraph

namespace OMA.R_Arxiv_2607_06396_alon_tarsi_short_cycle_cover_R1_H2_R1_H1_R1_H1_R1

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

/-- Oddness two, adjacent odd circuits: a cubic graph with a perfect matching `M ∋ pq` and a
perfect matching `A` of `G - p - q` disjoint from `M` (so the 2-factor `E \ M` has exactly two odd
circuits, joined by `pq`) has a cycle cover of length at most `7/5 |E|` as soon as some cycle
through `pq` has length at most `|E|/15`. -/

lemma sum_filter_mem {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (X : Finset (Sym2 V)) (hX : X ⊆ G.edgeFinset) :
    ∑ v, (X.filter (v ∈ ·)).card = 2 * #X := by
  classical
  simp only [card_filter]
  rw [sum_comm]
  rw [mul_comm, ← smul_eq_mul, ← sum_const]
  apply sum_congr rfl
  intro e he
  have hne := G.not_isDiag_of_mem_edgeSet (mem_edgeFinset.mp (hX he))
  induction e using Sym2.ind with
  | _ a b =>
  have hab : a ≠ b := fun h => hne (Sym2.mk_isDiag_iff.mpr h)
  rw [← card_filter]
  have : univ.filter (fun v => v ∈ s(a, b)) = {a, b} := by ext v; simp
  rw [this, card_pair hab]


/-- Edges `s(a, x)`, `x ∈ O`, meet `v` once if `v ∈ O`, and `#O` times at `a`. -/
lemma img_filter_card {V : Type} [DecidableEq V] (a : V) (O : Finset V) (ha : a ∉ O) (v : V) :
    ((O.image (fun x => s(a, x))).filter (v ∈ ·)).card =
      if v = a then O.card else (if v ∈ O then 1 else 0) := by
  rw [filter_image, card_image_of_injective _ (fun x y h => Sym2.congr_right.mp h)]
  by_cases hv : v = a
  · subst hv; simp
  · rw [if_neg hv]
    have : O.filter (fun x => v ∈ s(a, x)) = O.filter (fun x => x = v) := by
      ext x; simp only [mem_filter, Sym2.mem_iff]
      constructor
      · rintro ⟨h1, h | h⟩
        · exact absurd h hv
        · exact ⟨h1, h.symm⟩
      · rintro ⟨h1, h⟩; exact ⟨h1, Or.inr h.symm⟩
    rw [this, filter_eq']
    split_ifs <;> simp

/-- Parity repair on the double star at an edge `pq` that lies in no triangle: an edge set `K`
avoiding `p` and `q` whose odd vertices are neighbours of `p` or `q` becomes even after adding
some star edges, and every star edge at an odd vertex is added. -/
lemma fix_parity {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (p q : V) (hpq : G.Adj p q) (hnc : ∀ x, G.Adj p x → G.Adj q x → False)
    (K : Finset (Sym2 V)) (hK : K ⊆ G.edgeFinset) (hKpq : ∀ e ∈ K, p ∉ e ∧ q ∉ e)
    (hodd : ∀ v, Odd (K.filter (v ∈ ·)).card → G.Adj p v ∨ G.Adj q v) :
    ∃ Z : Finset (Sym2 V), Z ⊆ G.edgeFinset ∧ (∀ v, Even ((K ∪ Z).filter (v ∈ ·)).card) ∧
      (∀ x, G.Adj p x → Odd (K.filter (x ∈ ·)).card → s(p, x) ∈ Z) ∧
      (∀ y, G.Adj q y → Odd (K.filter (y ∈ ·)).card → s(q, y) ∈ Z) := by
  have hne : p ≠ q := G.ne_of_adj hpq
  set O := univ.filter (fun v => Odd (K.filter (v ∈ ·)).card) with hO
  have hdeg0 : ∀ v, (v = p ∨ v = q) → (K.filter (v ∈ ·)).card = 0 := by
    intro v hv; rw [card_eq_zero, filter_eq_empty_iff]
    intro e he hve; rcases hv with rfl | rfl
    · exact (hKpq e he).1 hve
    · exact (hKpq e he).2 hve
  have hpO : p ∉ O := by simp [hO, hdeg0 p (Or.inl rfl)]
  have hqO : q ∉ O := by simp [hO, hdeg0 q (Or.inr rfl)]
  have hOe : Even O.card := by
    have h := sum_filter_mem G K hK
    have : Even (∑ v, (K.filter (v ∈ ·)).card) := ⟨#K, by omega⟩
    exact (even_sum_iff_even_card_odd _).mp this
  set Op := O.filter (fun x => G.Adj p x) with hOp
  set Oq := O.filter (fun x => ¬ G.Adj p x) with hOq
  have hpOp : p ∉ Op := fun h => hpO (mem_filter.mp h).1
  have hqOq : q ∉ Oq := fun h => hqO (mem_filter.mp h).1
  have hpOq : p ∉ Oq := fun h => hpO (mem_filter.mp h).1
  have hqOp : q ∉ Op := fun h => hqO (mem_filter.mp h).1
  have hsplit : Op.card + Oq.card = O.card := card_filter_add_card_filter_not _
  set A := Op.image (fun x => s(p, x)) with hA
  set B := Oq.image (fun y => s(q, y)) with hB
  set P : Finset (Sym2 V) := if Odd Op.card then {s(p, q)} else ∅ with hP
  refine ⟨A ∪ B ∪ P, ?_, ?_, ?_, ?_⟩
  · intro e he
    rcases mem_union.mp he with h | h
    · rcases mem_union.mp h with h | h
      · obtain ⟨x, hx, rfl⟩ := mem_image.mp h
        exact mem_edgeFinset.mpr (mem_filter.mp hx).2
      · obtain ⟨y, hy, rfl⟩ := mem_image.mp h
        have hyO := (mem_filter.mp hy).1
        have := hodd y (mem_filter.mp hyO).2
        rcases this with h1 | h1
        · exact absurd h1 (mem_filter.mp hy).2
        · exact mem_edgeFinset.mpr h1
    · rw [hP] at h; split_ifs at h
      · rw [mem_singleton.mp h]; exact mem_edgeFinset.mpr hpq
      · simp at h
  · intro v
    have hAB : Disjoint A B := by
      rw [Finset.disjoint_left]; intro e h1 h2
      obtain ⟨x, hx, rfl⟩ := mem_image.mp h1
      obtain ⟨y, hy, hxy⟩ := mem_image.mp h2
      rcases Sym2.eq_iff.mp hxy with ⟨h3, _⟩ | ⟨_, h4⟩
      · exact hne h3.symm
      · exact hpOq (h4 ▸ hy)
    have hABP : Disjoint (A ∪ B) P := by
      rw [hP]; split_ifs
      · rw [disjoint_singleton_right]; intro h
        rcases mem_union.mp h with h | h
        · obtain ⟨x, hx, hx2⟩ := mem_image.mp h
          rcases Sym2.eq_iff.mp hx2 with ⟨_, h3⟩ | ⟨h3, _⟩
          · exact hqOp (h3 ▸ hx)
          · exact hne h3
        · obtain ⟨y, hy, hy2⟩ := mem_image.mp h
          rcases Sym2.eq_iff.mp hy2 with ⟨h3, _⟩ | ⟨_, h3⟩
          · exact hne h3.symm
          · exact hpOq (h3 ▸ hy)
      · exact disjoint_empty_right _
    have hKZ : Disjoint K (A ∪ B ∪ P) := by
      rw [Finset.disjoint_left]; intro e he h
      have hk := hKpq e he
      rcases mem_union.mp h with h | h
      · rcases mem_union.mp h with h | h
        · obtain ⟨x, _, rfl⟩ := mem_image.mp h; exact hk.1 (Sym2.mem_mk_left _ _)
        · obtain ⟨y, _, rfl⟩ := mem_image.mp h; exact hk.2 (Sym2.mem_mk_left _ _)
      · rw [hP] at h; split_ifs at h
        · rw [mem_singleton.mp h] at hk; exact hk.1 (Sym2.mem_mk_left _ _)
        · simp at h
    rw [filter_union, card_union_of_disjoint (disjoint_filter_filter hKZ), filter_union,
      card_union_of_disjoint (disjoint_filter_filter hABP), filter_union,
      card_union_of_disjoint (disjoint_filter_filter hAB), hA, hB,
      img_filter_card p Op hpOp v, img_filter_card q Oq hqOq v]
    have hPc : (P.filter (v ∈ ·)).card = if (v = p ∨ v = q) ∧ Odd Op.card then 1 else 0 := by
      rw [hP]; by_cases ho : Odd Op.card
      · rw [if_pos ho, filter_singleton]
        by_cases hv : v = p ∨ v = q
        · rw [if_pos (by rcases hv with rfl | rfl <;> simp), if_pos ⟨hv, ho⟩]; rfl
        · rw [if_neg (by simp only [Sym2.mem_iff]; exact hv), if_neg (fun h => hv h.1)]; rfl
      · rw [if_neg ho, if_neg (fun h => ho h.2)]; simp
    rw [hPc]
    have hvO : v ∈ O ↔ Odd (K.filter (v ∈ ·)).card := by simp [hO]
    have hOp1 : v ∈ Op → v ∈ O := fun h => (mem_filter.mp h).1
    have hOq1 : v ∈ Oq → v ∈ O := fun h => (mem_filter.mp h).1
    have hOpq : v ∈ O → (v ∈ Op ∨ v ∈ Oq) := by
      intro h; by_cases ha : G.Adj p v
      · exact Or.inl (mem_filter.mpr ⟨h, ha⟩)
      · exact Or.inr (mem_filter.mpr ⟨h, ha⟩)
    have hOpq2 : ¬ (v ∈ Op ∧ v ∈ Oq) := fun h => (mem_filter.mp h.2).2 (mem_filter.mp h.1).2
    have hd0 := hdeg0 v
    by_cases hvp : v = p
    · subst hvp
      rw [hd0 (Or.inl rfl), if_pos rfl, if_neg hne, if_neg hpOq]
      by_cases ho : Odd Op.card
      · rw [if_pos ⟨Or.inl rfl, ho⟩]; rw [Nat.odd_iff] at ho; rw [Nat.even_iff]; omega
      · rw [if_neg (fun h => ho h.2)]; rw [Nat.not_odd_iff_even, Nat.even_iff] at ho
        rw [Nat.even_iff]; omega
    · by_cases hvq : v = q
      · subst hvq
        rw [hd0 (Or.inr rfl), if_neg (Ne.symm hne), if_neg hqOp, if_pos rfl]
        have he := hOe; rw [Nat.even_iff] at he
        by_cases ho : Odd Op.card
        · rw [if_pos ⟨Or.inr rfl, ho⟩]; rw [Nat.odd_iff] at ho; rw [Nat.even_iff]; omega
        · rw [if_neg (fun h => ho h.2)]; rw [Nat.not_odd_iff_even, Nat.even_iff] at ho
          rw [Nat.even_iff]; omega
      · rw [if_neg hvp, if_neg hvq,
          if_neg (show ¬ ((v = p ∨ v = q) ∧ Odd Op.card) from fun h => h.1.elim hvp hvq)]
        by_cases hv : v ∈ O
        · have ho := hvO.mp hv
          rcases hOpq hv with h | h
          · rw [if_pos h, if_neg (fun h' => hOpq2 ⟨h, h'⟩)]
            rw [Nat.odd_iff] at ho; rw [Nat.even_iff]; omega
          · rw [if_neg (fun h' => hOpq2 ⟨h', h⟩), if_pos h]
            rw [Nat.odd_iff] at ho; rw [Nat.even_iff]; omega
        · rw [if_neg (fun h => hv (hOp1 h)), if_neg (fun h => hv (hOq1 h))]
          have : ¬ Odd (K.filter (v ∈ ·)).card := fun h => hv (hvO.mpr h)
          rw [Nat.not_odd_iff_even] at this; simpa using this
  · intro x hx ho
    have hxO : x ∈ O := by simp [hO, ho]
    exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl (mem_image.mpr ⟨x, mem_filter.mpr ⟨hxO, hx⟩, rfl⟩))))
  · intro y hy ho
    have hyO : y ∈ O := by simp [hO, ho]
    have hny : ¬ G.Adj p y := fun h => hnc y h hy
    exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inr (mem_image.mpr ⟨y, mem_filter.mpr ⟨hyO, hny⟩, rfl⟩))))

/-- The edges at `v` through a vertex `a ≠ v`: one if `a` is a neighbour, none otherwise. -/
lemma star_through {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v a : V) (hva : v ≠ a) :
    ((G.edgeFinset.filter (v ∈ ·)).filter (a ∈ ·)).card = if G.Adj a v then 1 else 0 := by
  by_cases h : G.Adj a v
  · rw [if_pos h, card_eq_one]; refine ⟨s(v, a), ?_⟩
    ext e; simp only [mem_filter, mem_singleton, mem_edgeFinset]
    constructor
    · rintro ⟨⟨_, h1⟩, h2⟩; exact (Sym2.mem_and_mem_iff hva).mp ⟨h1, h2⟩
    · rintro rfl; exact ⟨⟨h.symm, Sym2.mem_mk_left _ _⟩, Sym2.mem_mk_right _ _⟩
  · rw [if_neg h, card_eq_zero, filter_eq_empty_iff]
    intro e he ha
    have h1 := (Sym2.mem_and_mem_iff hva).mp ⟨(mem_filter.mp he).2, ha⟩
    have h2 := (mem_filter.mp he).1
    rw [h1, mem_edgeFinset, mem_edgeSet] at h2
    exact h h2.symm

/-- Heavy edge. Let `G` be cubic and `pq` an edge in no triangle such that `G - p - q` is
3-edge-colourable (colour classes `M 0, M 1, M 2`). Then two even edge sets cover every edge except
possibly `pq` (colour-pair unions repaired on the double star at `pq`). -/
lemma heavy_edge {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcub : ∀ v, G.degree v = 3) (p q : V) (hpq : G.Adj p q)
    (hnc : ∀ x, G.Adj p x → G.Adj q x → False) (M : Fin 3 → Finset (Sym2 V))
    (hM : ∀ i, M i ⊆ G.edgeFinset) (hdisj : ∀ i j, i ≠ j → Disjoint (M i) (M j))
    (hcol : ∀ i v, ((M i).filter (v ∈ ·)).card ≤ 1) (hav : ∀ i, ∀ e ∈ M i, p ∉ e ∧ q ∉ e)
    (hcov : ∀ e ∈ G.edgeFinset, p ∉ e → q ∉ e → ∃ i, e ∈ M i) :
    ∃ S T : Finset (Sym2 V), S ⊆ G.edgeFinset ∧ T ⊆ G.edgeFinset ∧
      (∀ v, Even (S.filter (v ∈ ·)).card) ∧ (∀ v, Even (T.filter (v ∈ ·)).card) ∧
      (∀ e ∈ G.edgeFinset, e ∉ S ∪ T → e = s(p, q)) := by
  have hne : p ≠ q := G.ne_of_adj hpq
  have hstar : ∀ v, (G.edgeFinset.filter (v ∈ ·)).card = 3 := by
    intro v; rw [← incidenceFinset_eq_filter, card_incidenceFinset_eq_degree, hcub]
  -- colour count at a vertex other than p, q
  have hcount : ∀ v, v ≠ p → v ≠ q →
      ((M 0).filter (v ∈ ·)).card + ((M 1).filter (v ∈ ·)).card + ((M 2).filter (v ∈ ·)).card +
      (if G.Adj p v then 1 else 0) + (if G.Adj q v then 1 else 0) = 3 := by
    intro v hvp hvq
    set F := G.edgeFinset.filter (v ∈ ·)
    have h1 := card_filter_add_card_filter_not (s := F) (fun e => p ∈ e)
    have h2 := card_filter_add_card_filter_not (s := F.filter (fun e => p ∉ e)) (fun e => q ∈ e)
    have h3 : (F.filter (fun e => p ∉ e)).filter (fun e => q ∈ e) = F.filter (q ∈ ·) := by
      ext e; simp only [F, mem_filter]
      constructor
      · rintro ⟨⟨h, _⟩, hq⟩; exact ⟨h, hq⟩
      · rintro ⟨⟨he, hv⟩, hq⟩
        refine ⟨⟨⟨he, hv⟩, ?_⟩, hq⟩
        rw [(Sym2.mem_and_mem_iff hvq).mp ⟨hv, hq⟩, Sym2.mem_iff]
        rintro (h | h)
        · exact hvp h.symm
        · exact hne h
    have h4 : (F.filter (fun e => p ∉ e)).filter (fun e => ¬ q ∈ e) =
        ((M 0 ∪ M 1) ∪ M 2).filter (v ∈ ·) := by
      ext e; simp only [F, mem_filter, mem_union]
      constructor
      · rintro ⟨⟨⟨he, hv⟩, hp⟩, hq⟩
        obtain ⟨i, hi⟩ := hcov e he hp hq
        refine ⟨?_, hv⟩
        fin_cases i
        · exact Or.inl (Or.inl hi)
        · exact Or.inl (Or.inr hi)
        · exact Or.inr hi
      · rintro ⟨h, hv⟩
        rcases h with (h | h) | h
        · exact ⟨⟨⟨hM 0 h, hv⟩, (hav 0 e h).1⟩, (hav 0 e h).2⟩
        · exact ⟨⟨⟨hM 1 h, hv⟩, (hav 1 e h).1⟩, (hav 1 e h).2⟩
        · exact ⟨⟨⟨hM 2 h, hv⟩, (hav 2 e h).1⟩, (hav 2 e h).2⟩
    have d01 : Disjoint ((M 0).filter (v ∈ ·)) ((M 1).filter (v ∈ ·)) :=
      disjoint_filter_filter (hdisj 0 1 (by decide))
    have d2 : Disjoint ((M 0 ∪ M 1).filter (v ∈ ·)) ((M 2).filter (v ∈ ·)) := by
      rw [filter_union]
      exact disjoint_union_left.mpr ⟨disjoint_filter_filter (hdisj 0 2 (by decide)),
        disjoint_filter_filter (hdisj 1 2 (by decide))⟩
    have h5 : (((M 0 ∪ M 1) ∪ M 2).filter (v ∈ ·)).card = ((M 0).filter (v ∈ ·)).card +
        ((M 1).filter (v ∈ ·)).card + ((M 2).filter (v ∈ ·)).card := by
      rw [filter_union, card_union_of_disjoint d2, filter_union, card_union_of_disjoint d01]
    rw [h3, star_through G v q hvq] at h2
    rw [h4, h5] at h2
    rw [star_through G v p hvp, hstar] at h1
    omega
  have hdeg0 : ∀ i v, (v = p ∨ v = q) → ((M i).filter (v ∈ ·)).card = 0 := by
    intro i v hv; rw [card_eq_zero, filter_eq_empty_iff]
    intro e he hve; rcases hv with rfl | rfl
    · exact (hav i e he).1 hve
    · exact (hav i e he).2 hve
  have hKdeg : ∀ i j, i ≠ j → ∀ v, ((M i ∪ M j).filter (v ∈ ·)).card =
      ((M i).filter (v ∈ ·)).card + ((M j).filter (v ∈ ·)).card := by
    intro i j hij v
    rw [filter_union, card_union_of_disjoint (disjoint_filter_filter (hdisj i j hij))]
  have hc := hcol
  -- the two colour-pair unions
  have hodd : ∀ j : Fin 3, j ≠ 0 → ∀ v, Odd ((M 0 ∪ M j).filter (v ∈ ·)).card →
      G.Adj p v ∨ G.Adj q v := by
    intro j hj v ho
    by_contra hn
    push_neg at hn
    rw [hKdeg 0 j (Ne.symm hj)] at ho
    by_cases hv : v = p ∨ v = q
    · rw [hdeg0 0 v hv, hdeg0 j v hv] at ho; simp at ho
    · push_neg at hv
      have := hcount v hv.1 hv.2
      rw [if_neg hn.1, if_neg hn.2] at this
      have a0 := hc 0 v; have a1 := hc 1 v; have a2 := hc 2 v
      rw [Nat.odd_iff] at ho
      fin_cases j
      · exact hj rfl
      · simp only [Fin.mk_one] at ho; omega
      · simp only [Fin.reduceFinMk] at ho; omega
  have hKsub : ∀ j, M 0 ∪ M j ⊆ G.edgeFinset := fun j => union_subset (hM 0) (hM j)
  have hKpq : ∀ j, ∀ e ∈ M 0 ∪ M j, p ∉ e ∧ q ∉ e := by
    intro j e he
    rcases mem_union.mp he with h | h
    · exact hav 0 e h
    · exact hav j e h
  obtain ⟨Z1, hZ1, hS1, hp1, hq1⟩ := fix_parity G p q hpq hnc (M 0 ∪ M 1) (hKsub 1) (hKpq 1)
    (hodd 1 (by decide))
  obtain ⟨Z2, hZ2, hS2, hp2, hq2⟩ := fix_parity G p q hpq hnc (M 0 ∪ M 2) (hKsub 2) (hKpq 2)
    (hodd 2 (by decide))
  refine ⟨(M 0 ∪ M 1) ∪ Z1, (M 0 ∪ M 2) ∪ Z2, union_subset (hKsub 1) hZ1,
    union_subset (hKsub 2) hZ2, hS1, hS2, ?_⟩
  intro e he hn
  simp only [mem_union, not_or] at hn
  obtain ⟨⟨⟨n0, n1⟩, nz1⟩, ⟨⟨_, n2⟩, nz2⟩⟩ := hn
  by_cases hp : p ∈ e
  · obtain ⟨x, rfl⟩ := Sym2.mem_iff_exists.mp hp
    have hx : G.Adj p x := mem_edgeFinset.mp he
    by_cases hxq : x = q
    · exact hxq ▸ rfl
    exfalso
    have hxp : x ≠ p := (G.ne_of_adj hx).symm
    have hqx : ¬ G.Adj q x := fun h => hnc x hx h
    have := hcount x hxp hxq
    rw [if_pos hx, if_neg hqx] at this
    have a0 := hc 0 x; have a1 := hc 1 x; have a2 := hc 2 x
    by_cases h1 : Odd ((M 0 ∪ M 1).filter (x ∈ ·)).card
    · exact nz1 (hp1 x hx h1)
    · have h2 : Odd ((M 0 ∪ M 2).filter (x ∈ ·)).card := by
        rw [hKdeg 0 1 (by decide)] at h1; rw [hKdeg 0 2 (by decide)]
        rw [Nat.not_odd_iff_even, Nat.even_iff] at h1; rw [Nat.odd_iff]; omega
      exact nz2 (hp2 x hx h2)
  · by_cases hq : q ∈ e
    · obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hq
      have hy : G.Adj q y := mem_edgeFinset.mp he
      by_cases hyp : y = p
      · rw [hyp]; exact Sym2.eq_swap
      exfalso
      have hyq : y ≠ q := (G.ne_of_adj hy).symm
      have hpy : ¬ G.Adj p y := fun h => hnc y h hy
      have := hcount y hyp hyq
      rw [if_pos hy, if_neg hpy] at this
      have a0 := hc 0 y; have a1 := hc 1 y; have a2 := hc 2 y
      by_cases h1 : Odd ((M 0 ∪ M 1).filter (y ∈ ·)).card
      · exact nz1 (hq1 y hy h1)
      · have h2 : Odd ((M 0 ∪ M 2).filter (y ∈ ·)).card := by
          rw [hKdeg 0 1 (by decide)] at h1; rw [hKdeg 0 2 (by decide)]
          rw [Nat.not_odd_iff_even, Nat.even_iff] at h1; rw [Nat.odd_iff]; omega
        exact nz2 (hq2 y hy h2)
    · exfalso
      obtain ⟨i, hi⟩ := hcov e he hp hq
      fin_cases i
      · exact n0 hi
      · exact n1 hi
      · exact n2 hi


/-- Snark core with a heavy edge, every cycle through a heavy edge being long. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsBridgeless → (∃ v, Odd (G.degree v)) → (∀ v, G.degree v ≤ 3) → (∀ v, G.degree v ≠ 2) →
    (¬ ∃ S T : Finset (Sym2 V), S ⊆ G.edgeFinset ∧ T ⊆ G.edgeFinset ∧ S ∪ T = G.edgeFinset ∧
      (∀ v, Even (S.filter (v ∈ ·)).card) ∧ (∀ v, Even (T.filter (v ∈ ·)).card)) →
    (¬ ∃ (S T : Finset (Sym2 V)) (D : Multiset (Cycle G)), S ⊆ G.edgeFinset ∧ T ⊆ G.edgeFinset ∧
      (∀ v, Even (S.filter (v ∈ ·)).card) ∧ (∀ v, Even (T.filter (v ∈ ·)).card) ∧
      (∀ e ∈ G.edgeFinset, e ∉ S ∪ T → ∃ c ∈ D, e ∈ c.edges) ∧
      15 * Arxiv.«2607.06396».totalLength D ≤ #G.edgeFinset) →
    (¬ ((∀ v, G.degree v = 3) ∧ ∃ M : Fin 4 → Finset (Sym2 V), (∀ i, M i ⊆ G.edgeFinset) ∧
      (∀ i v, ((M i).filter (v ∈ ·)).card = 1) ∧ (∀ e ∈ G.edgeFinset, ∃ i, e ∈ M i))) →
    (¬ ((∀ v, G.degree v = 3) ∧ (∃ (p q : V) (M : Fin 3 → Finset (Sym2 V)), G.Adj p q ∧ (∃ c : Cycle G, s(p, q) ∈ c.edges ∧
      15 * c.length ≤ #G.edgeFinset + 20) ∧ (∀ x, G.Adj p x → G.Adj q x → False) ∧
      (∀ i, M i ⊆ G.edgeFinset) ∧ (∀ i j, i ≠ j → Disjoint (M i) (M j)) ∧
      (∀ i v, ((M i).filter (v ∈ ·)).card ≤ 1) ∧ (∀ i, ∀ e ∈ M i, p ∉ e ∧ q ∉ e) ∧
      (∀ e ∈ G.edgeFinset, p ∉ e → q ∉ e → ∃ i, e ∈ M i)))) →
    ((∀ v, G.degree v = 3) ∧ (∃ (p q : V) (M : Fin 3 → Finset (Sym2 V)), G.Adj p q ∧ (∀ x, G.Adj p x → G.Adj q x → False) ∧
      (∀ i, M i ⊆ G.edgeFinset) ∧ (∀ i j, i ≠ j → Disjoint (M i) (M j)) ∧
      (∀ i v, ((M i).filter (v ∈ ·)).card ≤ 1) ∧ (∀ i, ∀ e ∈ M i, p ∉ e ∧ q ∉ e) ∧
      (∀ e ∈ G.edgeFinset, p ∉ e → q ∉ e → ∃ i, e ∈ M i))) →
      ∃ C : Multiset (Cycle G), Arxiv.«2607.06396».IsCycleCover G C ∧
        (Arxiv.«2607.06396».totalLength C : ℚ) ≤ 7 / 5 * #G.edgeFinset

/-- Snark core without heavy edges (or with an isolated vertex). -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsBridgeless → (∃ v, Odd (G.degree v)) → (∀ v, G.degree v ≤ 3) → (∀ v, G.degree v ≠ 2) →
    (¬ ∃ S T : Finset (Sym2 V), S ⊆ G.edgeFinset ∧ T ⊆ G.edgeFinset ∧ S ∪ T = G.edgeFinset ∧
      (∀ v, Even (S.filter (v ∈ ·)).card) ∧ (∀ v, Even (T.filter (v ∈ ·)).card)) →
    (¬ ∃ (S T : Finset (Sym2 V)) (D : Multiset (Cycle G)), S ⊆ G.edgeFinset ∧ T ⊆ G.edgeFinset ∧
      (∀ v, Even (S.filter (v ∈ ·)).card) ∧ (∀ v, Even (T.filter (v ∈ ·)).card) ∧
      (∀ e ∈ G.edgeFinset, e ∉ S ∪ T → ∃ c ∈ D, e ∈ c.edges) ∧
      15 * Arxiv.«2607.06396».totalLength D ≤ #G.edgeFinset) →
    (¬ ((∀ v, G.degree v = 3) ∧ ∃ M : Fin 4 → Finset (Sym2 V), (∀ i, M i ⊆ G.edgeFinset) ∧
      (∀ i v, ((M i).filter (v ∈ ·)).card = 1) ∧ (∀ e ∈ G.edgeFinset, ∃ i, e ∈ M i))) →
    (¬ ((∀ v, G.degree v = 3) ∧ (∃ (p q : V) (M : Fin 3 → Finset (Sym2 V)), G.Adj p q ∧ (∃ c : Cycle G, s(p, q) ∈ c.edges ∧
      15 * c.length ≤ #G.edgeFinset + 20) ∧ (∀ x, G.Adj p x → G.Adj q x → False) ∧
      (∀ i, M i ⊆ G.edgeFinset) ∧ (∀ i j, i ≠ j → Disjoint (M i) (M j)) ∧
      (∀ i v, ((M i).filter (v ∈ ·)).card ≤ 1) ∧ (∀ i, ∀ e ∈ M i, p ∉ e ∧ q ∉ e) ∧
      (∀ e ∈ G.edgeFinset, p ∉ e → q ∉ e → ∃ i, e ∈ M i)))) →
    (¬ ((∀ v, G.degree v = 3) ∧ (∃ (p q : V) (M : Fin 3 → Finset (Sym2 V)), G.Adj p q ∧ (∀ x, G.Adj p x → G.Adj q x → False) ∧
      (∀ i, M i ⊆ G.edgeFinset) ∧ (∀ i j, i ≠ j → Disjoint (M i) (M j)) ∧
      (∀ i v, ((M i).filter (v ∈ ·)).card ≤ 1) ∧ (∀ i, ∀ e ∈ M i, p ∉ e ∧ q ∉ e) ∧
      (∀ e ∈ G.edgeFinset, p ∉ e → q ∉ e → ∃ i, e ∈ M i)))) →
      ∃ C : Multiset (Cycle G), Arxiv.«2607.06396».IsCycleCover G C ∧
        (Arxiv.«2607.06396».totalLength C : ℚ) ≤ 7 / 5 * #G.edgeFinset

theorem main : H1 → H2 → OMA.R_Arxiv_2607_06396_alon_tarsi_short_cycle_cover_R1_H2_R1_H1_R1.H1 := by
  intro h1 h2 V _ _ G _ hb hodd hsub h2e htwo hnear h4
  by_cases hh : (∀ v, G.degree v = 3) ∧ (∃ (p q : V) (M : Fin 3 → Finset (Sym2 V)), G.Adj p q ∧ (∃ c : Cycle G, s(p, q) ∈ c.edges ∧
          15 * c.length ≤ #G.edgeFinset + 20) ∧ (∀ x, G.Adj p x → G.Adj q x → False) ∧
          (∀ i, M i ⊆ G.edgeFinset) ∧ (∀ i j, i ≠ j → Disjoint (M i) (M j)) ∧
          (∀ i v, ((M i).filter (v ∈ ·)).card ≤ 1) ∧ (∀ i, ∀ e ∈ M i, p ∉ e ∧ q ∉ e) ∧
          (∀ e ∈ G.edgeFinset, p ∉ e → q ∉ e → ∃ i, e ∈ M i))
  · obtain ⟨hc, p, q, M, hpq, ⟨c, hcpq, hcl⟩, hnc, hM, hdj, hcol, hav, hcov⟩ := hh
    obtain ⟨S, T, hS, hT, hSe, hTe, hST⟩ := heavy_edge G hc p q hpq hnc M hM hdj hcol hav hcov
    by_cases hin : s(p, q) ∈ S ∪ T
    · exfalso
      refine htwo ⟨S, T, hS, hT, ?_, hSe, hTe⟩
      apply Subset.antisymm (union_subset hS hT)
      intro e he
      by_contra hn
      exact hn ((hST e he hn) ▸ hin)
    · obtain ⟨C, hC, hl⟩ := cover_of_near_two_even G S T hS hT hSe hTe {c}
        (fun e he hn => ⟨c, Multiset.mem_singleton_self _, (hST e he hn) ▸ hcpq⟩)
      refine ⟨C, hC, ?_⟩
      have hsub' : S ∪ T ⊆ G.edgeFinset.erase s(p, q) := by
        intro e he
        exact mem_erase.mpr ⟨fun h => hin (h ▸ he), union_subset hS hT he⟩
      have hU := card_le_card hsub'
      have hpqE : s(p, q) ∈ G.edgeFinset := mem_edgeFinset.mpr hpq
      rw [card_erase_of_mem hpqE] at hU
      have hE1 : 1 ≤ #G.edgeFinset := card_pos.mpr ⟨_, hpqE⟩
      have hlc : Arxiv.«2607.06396».totalLength ({c} : Multiset (Cycle G)) = c.length := by
        simp [Arxiv.«2607.06396».totalLength]
      rw [hlc] at hl
      have : 15 * Arxiv.«2607.06396».totalLength C ≤ 21 * #G.edgeFinset := by omega
      have hq : (15 * Arxiv.«2607.06396».totalLength C : ℚ) ≤ 21 * #G.edgeFinset := by
        exact_mod_cast this
      linarith
  · by_cases hx : (∀ v, G.degree v = 3) ∧ (∃ (p q : V) (M : Fin 3 → Finset (Sym2 V)), G.Adj p q ∧ (∀ x, G.Adj p x → G.Adj q x → False) ∧
          (∀ i, M i ⊆ G.edgeFinset) ∧ (∀ i j, i ≠ j → Disjoint (M i) (M j)) ∧
          (∀ i v, ((M i).filter (v ∈ ·)).card ≤ 1) ∧ (∀ i, ∀ e ∈ M i, p ∉ e ∧ q ∉ e) ∧
          (∀ e ∈ G.edgeFinset, p ∉ e → q ∉ e → ∃ i, e ∈ M i))
    · exact h1 V G hb hodd hsub h2e htwo hnear h4 hh hx
    · exact h2 V G hb hodd hsub h2e htwo hnear h4 hh hx

end OMA.R_Arxiv_2607_06396_alon_tarsi_short_cycle_cover_R1_H2_R1_H1_R1_H1_R1
