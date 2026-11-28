import OMAReductions.R_Arxiv_2607_06396_alon_tarsi_short_cycle_cover_R1

-- Step Arxiv.2607.06396.alon_tarsi_short_cycle_cover.R1.H1: hypothesis H1 of reduction Arxiv.2607.06396.alon_tarsi_short_cycle_cover.R1
-- Credit: @sovrana
-- H1 := ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],     (∀ v, Even (G.degree v)) →       ∃ C : Multiset (Cycle G), Arxiv.«2607.06396».IsCycleCover G C ∧         Arxiv.«2607.06396».totalLength C ≤ #G.edgeFinset

/-! Veblen's theorem (1912): a finite simple graph with every degree even is an edge-disjoint union
of cycles, so its edges are covered by cycles of total length at most the number of edges. -/

open Finset SimpleGraph

namespace VeblenAux

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

end VeblenAux

theorem OMA.solution : OMA.R_Arxiv_2607_06396_alon_tarsi_short_cycle_cover_R1.H1 := by
  intro V _ _ G _ hev
  exact VeblenAux.veblen _ G rfl hev
