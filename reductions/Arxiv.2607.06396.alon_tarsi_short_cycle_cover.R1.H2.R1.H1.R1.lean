import OMAReductions.R_Arxiv_2607_06396_alon_tarsi_short_cycle_cover_R1_H2_R1

-- Reduction Arxiv.2607.06396.alon_tarsi_short_cycle_cover.R1.H2.R1.H1.R1 of step Arxiv.2607.06396.alon_tarsi_short_cycle_cover.R1.H2.R1.H1
-- Credit: @sovrana

/-!
# Alon-Tarsi, subcubic case: graphs close to a 4-flow are proved

Proved below (`cover_of_near_two_even`, in the spirit of Hagglund and Markstrom 2013): if `S` and `T`
are even edge sets and a family `D` of cycles passes through every edge outside `S ∪ T`, then `G`
has a cycle cover of length at most `4/3 |S ∪ T| + len D` (the two smallest of `S`, `T`, `S ∆ T`,
each split into cycles by Veblen's theorem, proved again here, plus `D`). Hence the bound `7/5 |E|`
holds as soon as `len D ≤ |E|/15`. This covers for example the flower snarks `J_k`, `k ≥ 15` odd:
a 2-factor with exactly two odd circuits joined by a matching edge `e` gives `S` (the 2-factor) and
`T` (the matching plus near-perfect matchings of the circuits, minus `e`), with `E \ (S ∪ T) = {e}`
on a 6-cycle (`oddness_two_adjacent` proves the general form of this example: a cubic graph with
a perfect matching `M ∋ pq` and a perfect matching of `G - p - q` disjoint from `M`, and a cycle of
length at most `|E|/15` through `pq`). Also proved (`four_matchings`, Steffen 2015, Thm 3.1): a cubic
graph whose edges are covered by four perfect matchings `M i` has a cycle cover of length at most
`4/3 |E|` (the sets `M i ∆ E2`, `E2` the edges in two of the matchings, are even and have total size
`4/3 |E|`). `near_of_parity` shows the near-4-flow case also contains every cubic graph with a 2-factor whose
odd circuits can be paired up by cycles of total length at most `|E|/15` (for oddness two: one
cycle through both odd circuits). What is left is split by whether the graph has a vertex of degree two:
* `H1`: no vertex of degree two, and not cubic with a cover by four perfect matchings (the snark
  core, for example the Petersen graph, with isolated vertices allowed);
* `H2`: some vertex of degree two.
-/

open Finset SimpleGraph

namespace OMA.R_Arxiv_2607_06396_alon_tarsi_short_cycle_cover_R1_H2_R1_H1_R1

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
lemma oddness_two_adjacent {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcub : ∀ v, G.degree v = 3) (M A : Finset (Sym2 V)) (p q : V)
    (hM : M ⊆ G.edgeFinset) (hA : A ⊆ G.edgeFinset) (hMA : Disjoint M A) (he : s(p, q) ∈ M)
    (hMv : ∀ v, (M.filter (v ∈ ·)).card = 1)
    (hAv : ∀ v, v ≠ p → v ≠ q → (A.filter (v ∈ ·)).card = 1)
    (hAp : (A.filter (p ∈ ·)).card = 0) (hAq : (A.filter (q ∈ ·)).card = 0)
    (c : Cycle G) (hc : s(p, q) ∈ c.edges) (hsize : 15 * c.length ≤ #G.edgeFinset) :
    ∃ C : Multiset (Cycle G), Arxiv.«2607.06396».IsCycleCover G C ∧
      (Arxiv.«2607.06396».totalLength C : ℚ) ≤ 7 / 5 * #G.edgeFinset := by
  classical
  set S := G.edgeFinset \ M with hSdef
  set T := M.erase s(p, q) ∪ A with hTdef
  have hdeg : ∀ v, (G.edgeFinset.filter (v ∈ ·)).card = 3 := by
    intro v; rw [← incidenceFinset_eq_filter, card_incidenceFinset_eq_degree, hcub]
  have hS : S ⊆ G.edgeFinset := sdiff_subset
  have hT : T ⊆ G.edgeFinset := union_subset ((erase_subset _ _).trans hM) hA
  have hSe : ∀ v, Even (S.filter (v ∈ ·)).card := by
    intro v
    have h1 : S.filter (v ∈ ·) = G.edgeFinset.filter (v ∈ ·) \ M.filter (v ∈ ·) := by
      ext e; simp only [hSdef, mem_filter, mem_sdiff]; tauto
    rw [h1, card_sdiff_of_subset (filter_subset_filter _ hM), hdeg, hMv]
    exact ⟨1, rfl⟩
  have hpq : p ≠ q := by
    intro h; subst h
    exact G.not_isDiag_of_mem_edgeSet (mem_edgeFinset.mp (hM he)) (Sym2.mk_isDiag_iff.mpr rfl)
  have hTe : ∀ v, Even (T.filter (v ∈ ·)).card := by
    intro v
    have hdis : Disjoint ((M.erase s(p, q)).filter (v ∈ ·)) (A.filter (v ∈ ·)) :=
      disjoint_filter_filter (Finset.disjoint_of_subset_left (erase_subset _ _) hMA)
    rw [hTdef, filter_union, card_union_of_disjoint hdis, filter_erase]
    by_cases hv : v ∈ s(p, q)
    · rw [card_erase_of_mem (mem_filter.mpr ⟨he, hv⟩), hMv]
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · rw [hAp]; exact ⟨0, rfl⟩
      · rw [hAq]; exact ⟨0, rfl⟩
    · rw [erase_eq_of_notMem (show s(p, q) ∉ M.filter (v ∈ ·) from fun h => hv (mem_filter.mp h).2), hMv]
      have hvp : v ≠ p := fun h => hv (h ▸ Sym2.mem_mk_left _ _)
      have hvq : v ≠ q := fun h => hv (h ▸ Sym2.mem_mk_right _ _)
      rw [hAv v hvp hvq]; exact ⟨1, rfl⟩
  have hD : ∀ e ∈ G.edgeFinset, e ∉ S ∪ T → ∃ d ∈ ({c} : Multiset (Cycle G)), e ∈ d.edges := by
    intro e he' hn
    have heM : e ∈ M := by
      by_contra h; exact hn (mem_union.mpr (Or.inl (mem_sdiff.mpr ⟨he', h⟩)))
    have : e = s(p, q) := by
      by_contra h
      exact hn (mem_union.mpr (Or.inr (mem_union.mpr (Or.inl (mem_erase.mpr ⟨h, heM⟩)))))
    exact ⟨c, Multiset.mem_singleton_self c, this ▸ hc⟩
  obtain ⟨C, hC, hl⟩ := cover_of_near_two_even G S T hS hT hSe hTe {c} hD
  refine ⟨C, hC, ?_⟩
  have hU : #(S ∪ T) ≤ #G.edgeFinset := card_le_card (union_subset hS hT)
  have hlen : Arxiv.«2607.06396».totalLength ({c} : Multiset (Cycle G)) = c.length := by
    simp [Arxiv.«2607.06396».totalLength]
  rw [hlen] at hl
  have : 15 * Arxiv.«2607.06396».totalLength C ≤ 21 * #G.edgeFinset := by omega
  have hq : (15 * Arxiv.«2607.06396».totalLength C : ℚ) ≤ 21 * #G.edgeFinset := by
    exact_mod_cast this
  linarith


/-- Double counting: an edge set meets the vertices `2 |X|` times. -/
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

/-- Steffen: a cubic graph whose edges are covered by four perfect matchings has a cycle cover of
length `4/3 |E|` (the four even sets `M i ∆ E₂`, with `E₂` the edges lying in two matchings). -/
lemma four_matchings {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcub : ∀ v, G.degree v = 3) (M : Fin 4 → Finset (Sym2 V))
    (hM : ∀ i, M i ⊆ G.edgeFinset) (hpm : ∀ i v, ((M i).filter (v ∈ ·)).card = 1)
    (hcov : ∀ e ∈ G.edgeFinset, ∃ i, e ∈ M i) :
    ∃ C : Multiset (Cycle G), Arxiv.«2607.06396».IsCycleCover G C ∧
      3 * Arxiv.«2607.06396».totalLength C ≤ 4 * #G.edgeFinset := by
  classical
  set cnt : Sym2 V → ℕ := fun e => (univ.filter (fun i : Fin 4 => e ∈ M i)).card with hcnt
  set E2 := G.edgeFinset.filter (fun e => 2 ≤ cnt e) with hE2
  have hstar : ∀ v, (G.edgeFinset.filter (v ∈ ·)).card = 3 := by
    intro v; rw [← incidenceFinset_eq_filter, card_incidenceFinset_eq_degree, hcub]
  have hsum : ∀ v, ∑ e ∈ G.edgeFinset.filter (v ∈ ·), cnt e = 4 := by
    intro v
    simp only [hcnt, card_filter]
    rw [sum_comm]
    have : ∀ i : Fin 4, (∑ e ∈ G.edgeFinset.filter (v ∈ ·), if e ∈ M i then 1 else 0) = 1 := by
      intro i
      rw [← card_filter, ← hpm i v]
      congr 1; ext e
      simp only [mem_filter, mem_edgeFinset]
      constructor
      · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨mem_edgeFinset.mp (hM i h1), h2⟩, h1⟩
    simp [this]
  have hpos : ∀ e ∈ G.edgeFinset, 1 ≤ cnt e := by
    intro e he
    obtain ⟨i, hi⟩ := hcov e he
    exact card_pos.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
  -- at each vertex exactly one edge lies in two matchings, and none in three
  have hv2 : ∀ v, ((G.edgeFinset.filter (v ∈ ·)).filter (fun e => 2 ≤ cnt e)).card = 1 ∧
      ∀ e ∈ G.edgeFinset.filter (v ∈ ·), cnt e ≤ 2 := by
    intro v
    set st := G.edgeFinset.filter (v ∈ ·)
    have h3 : st.card = 3 := hstar v
    have hlow : ∑ e ∈ st, (1 + (if 2 ≤ cnt e then 1 else 0) + (if 3 ≤ cnt e then 1 else 0)) ≤
        ∑ e ∈ st, cnt e := by
      apply sum_le_sum; intro e he
      have := hpos e (mem_filter.mp he).1
      split_ifs <;> omega
    rw [sum_add_distrib, sum_add_distrib, ← card_filter, ← card_filter, hsum v] at hlow
    simp only [sum_const, smul_eq_mul, mul_one] at hlow
    have hne : (st.filter (fun e => 2 ≤ cnt e)).card ≠ 0 := by
      intro h0
      have hup : ∑ e ∈ st, cnt e ≤ ∑ e ∈ st, 1 := by
        apply sum_le_sum; intro e he
        by_contra hc
        have : e ∈ st.filter (fun e => 2 ≤ cnt e) := mem_filter.mpr ⟨he, by omega⟩
        rw [card_eq_zero.mp h0] at this; simp at this
      rw [hsum v] at hup; simp at hup; omega
    refine ⟨by omega, ?_⟩
    intro e he
    by_contra hc
    have : 0 < (st.filter (fun e => 3 ≤ cnt e)).card := card_pos.mpr ⟨e, mem_filter.mpr ⟨he, by omega⟩⟩
    have : 0 < (st.filter (fun e => 2 ≤ cnt e)).card := card_pos.mpr ⟨e, mem_filter.mpr ⟨he, by omega⟩⟩
    omega
  set F : Fin 4 → Finset (Sym2 V) := fun i => (M i \ E2) ∪ (E2 \ M i) with hFdef
  have hE2sub : E2 ⊆ G.edgeFinset := filter_subset _ _
  have hFsub : ∀ i, F i ⊆ G.edgeFinset := by
    intro i e he
    rcases mem_union.mp he with h | h
    · exact hM i (mem_sdiff.mp h).1
    · exact hE2sub (mem_sdiff.mp h).1
  have hB : ∀ v, E2.filter (v ∈ ·) = (G.edgeFinset.filter (v ∈ ·)).filter (fun e => 2 ≤ cnt e) := by
    intro v; ext e; simp only [hE2, mem_filter]; tauto
  have hFv : ∀ i v, ((F i).filter (v ∈ ·)).card + 2 * (((M i).filter (v ∈ ·)) ∩ E2.filter (v ∈ ·)).card = 2 := by
    intro i v
    have hBc : (E2.filter (v ∈ ·)).card = 1 := by rw [hB]; exact (hv2 v).1
    have hA : ((M i).filter (v ∈ ·)).card = 1 := hpm i v
    set A := (M i).filter (v ∈ ·)
    set B := E2.filter (v ∈ ·)
    have h1 : (F i).filter (v ∈ ·) = (A \ B) ∪ (B \ A) := by
      ext e; simp only [hFdef, A, B, mem_filter, mem_sdiff, mem_union]; tauto
    have hd : Disjoint (A \ B) (B \ A) := by
      rw [Finset.disjoint_left]; intro e h1 h2; simp only [mem_sdiff] at h1 h2; tauto
    rw [h1, card_union_of_disjoint hd]
    have a1 := card_sdiff_add_card_inter A B
    have a2 := card_sdiff_add_card_inter B A
    rw [inter_comm] at a2
    omega
  have hFe : ∀ i, ∀ v, Even ((F i).filter (v ∈ ·)).card := by
    intro i v
    have := hFv i v
    exact ⟨1 - (((M i).filter (v ∈ ·)) ∩ E2.filter (v ∈ ·)).card, by omega⟩
  have hcnt2 : ∀ e ∈ G.edgeFinset, cnt e ≤ 2 := by
    intro e he
    have hne := G.not_isDiag_of_mem_edgeSet (mem_edgeFinset.mp he)
    induction e using Sym2.ind with
    | _ a b =>
    exact (hv2 a).2 _ (mem_filter.mpr ⟨he, Sym2.mem_mk_left _ _⟩)
  have hcovF : ∀ e ∈ G.edgeFinset, ∃ i, e ∈ F i := by
    intro e he
    by_cases h2 : 2 ≤ cnt e
    · have heE2 : e ∈ E2 := mem_filter.mpr ⟨he, h2⟩
      by_contra hall
      push_neg at hall
      have hin : ∀ i, e ∈ M i := by
        intro i; by_contra hi
        exact hall i (mem_union.mpr (Or.inr (mem_sdiff.mpr ⟨heE2, hi⟩)))
      have : cnt e = 4 := by
        simp only [hcnt]; rw [filter_true_of_mem (fun i _ => hin i)]; rfl
      have := hcnt2 e he; omega
    · obtain ⟨i, hi⟩ := hcov e he
      refine ⟨i, mem_union.mpr (Or.inl (mem_sdiff.mpr ⟨hi, fun h => h2 (mem_filter.mp h).2⟩))⟩
  -- total size
  have hvsum : ∀ v, ∑ i, ((F i).filter (v ∈ ·)).card = 4 := by
    intro v
    obtain ⟨e0, he0⟩ := card_eq_one.mp (hv2 v).1
    have he0m : e0 ∈ (G.edgeFinset.filter (v ∈ ·)).filter (fun e => 2 ≤ cnt e) := by
      rw [he0]; exact mem_singleton_self _
    simp only [mem_filter] at he0m
    have hc0 : cnt e0 = 2 := le_antisymm (hcnt2 e0 he0m.1.1) he0m.2
    have hk : ∀ i, (((M i).filter (v ∈ ·)) ∩ E2.filter (v ∈ ·)).card =
        if e0 ∈ M i then 1 else 0 := by
      intro i
      rw [hB v, he0]
      split_ifs with h
      · rw [card_eq_one]; refine ⟨e0, ?_⟩
        ext e; simp only [mem_inter, mem_filter, mem_singleton]
        constructor
        · rintro ⟨_, rfl⟩; rfl
        · rintro rfl; exact ⟨⟨h, he0m.1.2⟩, rfl⟩
      · rw [card_eq_zero]; ext e; simp only [mem_inter, mem_filter, mem_singleton]
        simp only [Finset.notMem_empty, iff_false, not_and]
        rintro ⟨hm, _⟩ rfl; exact h hm
    have hs : ∑ i, (((M i).filter (v ∈ ·)) ∩ E2.filter (v ∈ ·)).card = 2 := by
      simp only [hk]; rw [← card_filter]; exact hc0
    have htot : ∑ i, (((F i).filter (v ∈ ·)).card +
        2 * (((M i).filter (v ∈ ·)) ∩ E2.filter (v ∈ ·)).card) = 8 := by
      simp only [hFv]; simp
    rw [sum_add_distrib, ← mul_sum, hs] at htot
    omega
  have hsize : 3 * ∑ i, (F i).card = 4 * #G.edgeFinset := by
    have h1 : ∑ i, 2 * (F i).card = ∑ v : V, 4 := by
      rw [← sum_congr rfl (fun i _ => sum_filter_mem G (F i) (hFsub i)), sum_comm]
      exact sum_congr rfl (fun v _ => hvsum v)
    have h2 := G.sum_degrees_eq_twice_card_edges
    simp only [hcub, sum_const, card_univ, smul_eq_mul] at h1 h2
    rw [← mul_sum] at h1
    omega
  obtain ⟨C0, c0, l0⟩ := even_set_cover G (F 0) (hFsub 0) (hFe 0)
  obtain ⟨C1, c1, l1⟩ := even_set_cover G (F 1) (hFsub 1) (hFe 1)
  obtain ⟨C2, c2, l2⟩ := even_set_cover G (F 2) (hFsub 2) (hFe 2)
  obtain ⟨C3, c3, l3⟩ := even_set_cover G (F 3) (hFsub 3) (hFe 3)
  refine ⟨C0 + C1 + C2 + C3, ?_, ?_⟩
  · intro e he
    obtain ⟨i, hi⟩ := hcovF e he
    fin_cases i
    · obtain ⟨c, hc, hce⟩ := c0 e hi; exact ⟨c, by simp [hc], hce⟩
    · obtain ⟨c, hc, hce⟩ := c1 e hi; exact ⟨c, by simp [hc], hce⟩
    · obtain ⟨c, hc, hce⟩ := c2 e hi; exact ⟨c, by simp [hc], hce⟩
    · obtain ⟨c, hc, hce⟩ := c3 e hi; exact ⟨c, by simp [hc], hce⟩
  · simp only [Arxiv.«2607.06396».totalLength_add]
    rw [Fin.sum_univ_four] at hsize
    omega

/-- Two edge sets that are odd at the same vertices: their symmetric difference is even. -/
lemma even_symmDiff_filter {V : Type} [DecidableEq V] (T0 P : Finset (Sym2 V)) (v : V)
    (h : Even (T0.filter (v ∈ ·)).card ↔ Even (P.filter (v ∈ ·)).card) :
    Even (((T0 \ P) ∪ (P \ T0)).filter (v ∈ ·)).card := by
  have hd : Disjoint ((T0 \ P).filter (v ∈ ·)) ((P \ T0).filter (v ∈ ·)) := by
    rw [Finset.disjoint_left]; intro e h1 h2; simp only [mem_filter, mem_sdiff] at h1 h2; tauto
  have h1 : ((T0 \ P) ∪ (P \ T0)).filter (v ∈ ·) =
      (T0.filter (v ∈ ·) \ P.filter (v ∈ ·)) ∪ (P.filter (v ∈ ·) \ T0.filter (v ∈ ·)) := by
    ext e; simp only [mem_filter, mem_sdiff, mem_union]; tauto
  have hd2 : Disjoint (T0.filter (v ∈ ·) \ P.filter (v ∈ ·)) (P.filter (v ∈ ·) \ T0.filter (v ∈ ·)) := by
    rw [Finset.disjoint_left]; intro e h1 h2; simp only [mem_sdiff] at h1 h2; tauto
  rw [h1, card_union_of_disjoint hd2]
  have a1 := card_sdiff_add_card_inter (T0.filter (v ∈ ·)) (P.filter (v ∈ ·))
  have a2 := card_sdiff_add_card_inter (P.filter (v ∈ ·)) (T0.filter (v ∈ ·))
  rw [inter_comm] at a2
  have hev : Even ((T0.filter (v ∈ ·)).card + (P.filter (v ∈ ·)).card) := by
    rw [Nat.even_add]; exact h
  obtain ⟨r, hr⟩ := hev
  exact ⟨r - ((T0.filter (v ∈ ·)) ∩ P.filter (v ∈ ·)).card, by omega⟩

/-- Parity repair. Let `S` be even and `S ∪ T0 = E`. If an edge set `P` is odd at exactly the
vertices where `T0` is odd (for example a union of paths pairing them up) and every edge of `P` lies
on a cycle of a family `D` with `15 len D ≤ |E|`, then `G` has a near-witness (`T0 ∆ P` is even and
only edges of `P` are left). Example: `S` a 2-factor, `T0` the complementary perfect matching plus
near-perfect matchings of the circuits, odd at one chosen vertex of each odd circuit, and `D` short
cycles pairing up the odd circuits (for oddness two, one cycle through both odd circuits). -/
lemma near_of_parity {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S T0 P : Finset (Sym2 V)) (hS : S ⊆ G.edgeFinset)
    (hT0 : T0 ⊆ G.edgeFinset) (hSe : ∀ v, Even (S.filter (v ∈ ·)).card)
    (hpar : ∀ v, Even (T0.filter (v ∈ ·)).card ↔ Even (P.filter (v ∈ ·)).card)
    (hP : P ⊆ G.edgeFinset) (hU : S ∪ T0 = G.edgeFinset) (D : Multiset (Cycle G))
    (hc : ∀ e ∈ P, ∃ c ∈ D, e ∈ c.edges)
    (hl : 15 * Arxiv.«2607.06396».totalLength D ≤ #G.edgeFinset) :
    ∃ (S T : Finset (Sym2 V)) (D : Multiset (Cycle G)), S ⊆ G.edgeFinset ∧
      T ⊆ G.edgeFinset ∧ (∀ v, Even (S.filter (v ∈ ·)).card) ∧
      (∀ v, Even (T.filter (v ∈ ·)).card) ∧
      (∀ e ∈ G.edgeFinset, e ∉ S ∪ T → ∃ c ∈ D, e ∈ c.edges) ∧
      15 * Arxiv.«2607.06396».totalLength D ≤ #G.edgeFinset := by
  refine ⟨S, (T0 \ P) ∪ (P \ T0), D, hS, ?_, hSe, ?_, ?_, hl⟩
  · intro e he
    rcases mem_union.mp he with h | h
    · exact hT0 (mem_sdiff.mp h).1
    · exact hP (mem_sdiff.mp h).1
  · intro v
    exact even_symmDiff_filter T0 P v (hpar v)
  · intro e he hn
    apply hc e
    have h1 : e ∈ T0 := by
      have : e ∈ S ∪ T0 := hU ▸ he
      rcases mem_union.mp this with h | h
      · exact absurd (mem_union.mpr (Or.inl h)) hn
      · exact h
    by_contra hp
    exact hn (mem_union.mpr (Or.inr (mem_union.mpr (Or.inl (mem_sdiff.mpr ⟨h1, hp⟩)))))

/-- Subcubic core, no vertex of degree two, not within a short family of cycles of a 4-flow,
and not a cubic graph whose edges are covered by four perfect matchings. -/
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
      ∃ C : Multiset (Cycle G), Arxiv.«2607.06396».IsCycleCover G C ∧
        (Arxiv.«2607.06396».totalLength C : ℚ) ≤ 7 / 5 * #G.edgeFinset

/-- Subcubic core with a vertex of degree two, not within a short family of cycles of a 4-flow. -/
def H2 : Prop :=
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

theorem main : H1 → H2 → OMA.R_Arxiv_2607_06396_alon_tarsi_short_cycle_cover_R1_H2_R1.H1 := by
  intro h1 h2 V _ _ G _ hb hodd hsub h2e
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
  · by_cases h2v : ∃ v, G.degree v = 2
    · exact h2 V G hb hodd hsub h2v h2e hw
    · push_neg at h2v
      by_cases h4 : (∀ v, G.degree v = 3) ∧ ∃ M : Fin 4 → Finset (Sym2 V),
          (∀ i, M i ⊆ G.edgeFinset) ∧ (∀ i v, ((M i).filter (v ∈ ·)).card = 1) ∧
          (∀ e ∈ G.edgeFinset, ∃ i, e ∈ M i)
      · obtain ⟨hc, M, hM, hpm, hcov⟩ := h4
        obtain ⟨C, hC, hl⟩ := four_matchings G hc M hM hpm hcov
        refine ⟨C, hC, ?_⟩
        have hq : (3 * Arxiv.«2607.06396».totalLength C : ℚ) ≤ 4 * #G.edgeFinset := by
          exact_mod_cast hl
        have h0 : (0 : ℚ) ≤ #G.edgeFinset := by positivity
        linarith
      · exact h1 V G hb hodd hsub h2v h2e hw h4

end OMA.R_Arxiv_2607_06396_alon_tarsi_short_cycle_cover_R1_H2_R1_H1_R1
