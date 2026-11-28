import OMAReductions.R_Arxiv_2607_06396_alon_tarsi_short_cycle_cover_R1

-- Reduction Arxiv.2607.06396.alon_tarsi_short_cycle_cover.R1.H2.R1 of step Arxiv.2607.06396.alon_tarsi_short_cycle_cover.R1.H2
-- Credit: @sovrana

/-!
# Alon-Tarsi with an odd vertex: the 4-flow case is proved, the snark-like core is split by degree

Proved below, with no hypothesis (`cover_of_two_even`, after Bermond, Jackson and Jaeger 1983):
if the edge set of `G` is the union of two even edge sets `S` and `T` (every vertex meets an even
number of edges of each; for bridgeless graphs this is the same as having a nowhere-zero 4-flow, and
it holds for example for every 3-edge-colourable cubic graph), then `G` has a cycle cover of total
length at most `4/3 |E|`, below the `7/5 |E|` asked for. The three even sets `S`, `T` and `S ∆ T`
contain every edge exactly twice, so the two smallest have total size at most `4/3 |E|`; any two of
them cover every edge, and each splits into edge-disjoint cycles by Veblen's theorem (proved here
again, `veblen`: a longest path in an acyclic graph ends at a vertex of degree one, and deleting the
edges of a cycle keeps every degree even).

What is left are the bridgeless graphs whose edges are not the union of two even sets (no
nowhere-zero 4-flow, e.g. the Petersen graph and the other snarks), split by maximum degree:
* `H1`: every degree at most `3` (the subcubic case, which contains all snarks);
* `H2`: some vertex of degree at least `4`.
-/

open Finset SimpleGraph

namespace OMA.R_Arxiv_2607_06396_alon_tarsi_short_cycle_cover_R1_H2_R1

/-- The subcubic graphs with an odd vertex whose edges are not the union of two even edge sets. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsBridgeless → (∃ v, Odd (G.degree v)) → (∀ v, G.degree v ≤ 3) →
    (¬ ∃ S T : Finset (Sym2 V), S ⊆ G.edgeFinset ∧ T ⊆ G.edgeFinset ∧ S ∪ T = G.edgeFinset ∧
      (∀ v, Even (S.filter (v ∈ ·)).card) ∧ (∀ v, Even (T.filter (v ∈ ·)).card)) →
      ∃ C : Multiset (Cycle G), Arxiv.«2607.06396».IsCycleCover G C ∧
        (Arxiv.«2607.06396».totalLength C : ℚ) ≤ 7 / 5 * #G.edgeFinset

/-- The graphs with an odd vertex and a vertex of degree at least four whose edges are not the
union of two even edge sets. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsBridgeless → (∃ v, Odd (G.degree v)) → (∃ v, 4 ≤ G.degree v) →
    (¬ ∃ S T : Finset (Sym2 V), S ⊆ G.edgeFinset ∧ T ⊆ G.edgeFinset ∧ S ∪ T = G.edgeFinset ∧
      (∀ v, Even (S.filter (v ∈ ·)).card) ∧ (∀ v, Even (T.filter (v ∈ ·)).card)) →
      ∃ C : Multiset (Cycle G), Arxiv.«2607.06396».IsCycleCover G C ∧
        (Arxiv.«2607.06396».totalLength C : ℚ) ≤ 7 / 5 * #G.edgeFinset


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


theorem main : H1 → H2 → OMA.R_Arxiv_2607_06396_alon_tarsi_short_cycle_cover_R1.H2 := by
  intro h1 h2 V _ _ G _ hbr hodd
  by_cases h4 : ∃ S T : Finset (Sym2 V), S ⊆ G.edgeFinset ∧ T ⊆ G.edgeFinset ∧
      S ∪ T = G.edgeFinset ∧ (∀ v, Even (S.filter (v ∈ ·)).card) ∧
      (∀ v, Even (T.filter (v ∈ ·)).card)
  · obtain ⟨S, T, hS, hT, hU, hSe, hTe⟩ := h4
    obtain ⟨C, hC, hl⟩ := cover_of_two_even G S T hS hT hU hSe hTe
    refine ⟨C, hC, ?_⟩
    have hq : (3 : ℚ) * Arxiv.«2607.06396».totalLength C ≤ 4 * #G.edgeFinset := by
      exact_mod_cast hl
    have h0 : (0 : ℚ) ≤ #G.edgeFinset := by positivity
    linarith
  · by_cases hd : ∀ v, G.degree v ≤ 3
    · exact h1 V G hbr hodd hd h4
    · push Not at hd
      obtain ⟨v, hv⟩ := hd
      exact h2 V G hbr hodd ⟨v, by omega⟩ h4

end OMA.R_Arxiv_2607_06396_alon_tarsi_short_cycle_cover_R1_H2_R1
