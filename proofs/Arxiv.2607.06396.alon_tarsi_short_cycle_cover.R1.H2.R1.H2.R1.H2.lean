import OMAReductions.R_Arxiv_2607_06396_alon_tarsi_short_cycle_cover_R1_H2_R1_H2_R1

-- Step Arxiv.2607.06396.alon_tarsi_short_cycle_cover.R1.H2.R1.H2.R1.H2: hypothesis H2 of reduction Arxiv.2607.06396.alon_tarsi_short_cycle_cover.R1.H2.R1.H2.R1
-- Credit: @sovrana

/-! Fleischner's splitting lemma, for the split that moves two edges `vu`, `vw` to a new vertex.
Cuts are counted with darts. A split creates a bridge only if `G` has a 3-edge cut `X` with `v`
inside and `u`, `w` outside (`bad_of_not_bridgeless`). Given any edge `vu₁`, if every partner `vw`
were bad, take a smallest such `X` (for `w = uⱼ`), a neighbour `uₖ` of `v` inside `X` (it exists as
`deg v ≥ 4`) and a bad `Y` for `uₖ`; counting darts between the four regions cut out by `X` and `Y`,
bridgelessness and the minimality of `X` are contradictory (`partner`). -/

namespace SplitAux
open Finset SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The relation defining the split graph: the edges `vu`, `vw` are moved to a new vertex `none`. -/
def rel (G : SimpleGraph V) (v u w : V) : Option V → Option V → Prop :=
  fun x y => match x, y with
    | some a, some b => G.Adj a b ∧ s(a, b) ≠ s(v, u) ∧ s(a, b) ≠ s(v, w)
    | none, some b => b = u ∨ b = w
    | _, _ => False

/-- The split graph. -/
def split (G : SimpleGraph V) (v u w : V) : SimpleGraph (Option V) :=
  SimpleGraph.fromRel (rel G v u w)

lemma adj_ss (G : SimpleGraph V) (v u w a b : V) :
    (split G v u w).Adj (some a) (some b) ↔ G.Adj a b ∧ s(a, b) ≠ s(v, u) ∧ s(a, b) ≠ s(v, w) := by
  simp only [split, fromRel_adj, rel, ne_eq, Option.some.injEq]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · refine ⟨h.1.symm, ?_, ?_⟩
      · rw [Sym2.eq_swap]; exact h.2.1
      · rw [Sym2.eq_swap]; exact h.2.2
  · intro h
    exact ⟨h.1.ne, Or.inl h⟩

lemma adj_ns (G : SimpleGraph V) (v u w b : V) :
    (split G v u w).Adj none (some b) ↔ b = u ∨ b = w := by
  simp only [split, fromRel_adj, rel, ne_eq, reduceCtorEq, not_false_eq_true, true_and, or_false]

lemma adj_sn (G : SimpleGraph V) (v u w b : V) :
    (split G v u w).Adj (some b) none ↔ b = u ∨ b = w := by
  rw [adj_comm]; exact adj_ns G v u w b

lemma not_adj_nn (G : SimpleGraph V) (v u w : V) : ¬ (split G v u w).Adj none none :=
  (split G v u w).irrefl

/-- The projection merging the new vertex back into `v`. -/
def proj (G : SimpleGraph V) (v u w : V) (hu : G.Adj v u) (hw : G.Adj v w) :
    split G v u w →g G where
  toFun := fun x => x.getD v
  map_rel' := by
    intro x y h
    rcases x with _ | a <;> rcases y with _ | b
    · exact absurd h (not_adj_nn G v u w)
    · rcases (adj_ns G v u w b).mp h with rfl | rfl <;> assumption
    · rcases (adj_sn G v u w a).mp h with rfl | rfl
      · exact hu.symm
      · exact hw.symm
    · exact ((adj_ss G v u w a b).mp h).1

/-- The left inverse of the projection on edges. -/
def back (v u w : V) (e : Sym2 V) : Sym2 (Option V) :=
  if e = s(v, u) then s(none, some u) else if e = s(v, w) then s(none, some w) else e.map some

lemma back_map (G : SimpleGraph V) (v u w : V) (hu : G.Adj v u) (hw : G.Adj v w) (huw : u ≠ w)
    (e : Sym2 (Option V)) (he : e ∈ (split G v u w).edgeSet) :
    back v u w (e.map (proj G v u w hu hw)) = e := by
  induction e using Sym2.ind with
  | _ x y =>
  rw [mem_edgeSet] at he
  have hvw : s(v, w) ≠ s(v, u) := by
    intro h; rcases Sym2.eq_iff.mp h with h | h
    · exact huw h.2.symm
    · exact huw (h.1.symm.trans h.2.symm)
  rcases x with _ | a <;> rcases y with _ | b
  · exact absurd he (not_adj_nn G v u w)
  · rcases (adj_ns G v u w b).mp he with rfl | rfl
    · simp [back, proj]
    · simp [back, proj, hvw]
  · rcases (adj_sn G v u w a).mp he with rfl | rfl
    · simp [back, proj, Sym2.eq_swap]
    · have : s(a, v) ≠ s(v, u) := by rw [Sym2.eq_swap]; exact hvw
      simp [back, proj, Sym2.eq_swap, hvw]
  · obtain ⟨_, h1, h2⟩ := (adj_ss G v u w a b).mp he
    simp [back, proj, h1, h2]

lemma map_injOn (G : SimpleGraph V) (v u w : V) (hu : G.Adj v u) (hw : G.Adj v w) (huw : u ≠ w) :
    ∀ e₁ ∈ (split G v u w).edgeSet, ∀ e₂ ∈ (split G v u w).edgeSet,
      e₁.map (proj G v u w hu hw) = e₂.map (proj G v u w hu hw) → e₁ = e₂ := by
  intro e₁ h₁ e₂ h₂ h
  rw [← back_map G v u w hu hw huw e₁ h₁, ← back_map G v u w hu hw huw e₂ h₂, h]

lemma map_surj (G : SimpleGraph V) (v u w : V) (hu : G.Adj v u) (hw : G.Adj v w) :
    ∀ e ∈ G.edgeSet, ∃ e' ∈ (split G v u w).edgeSet, e'.map (proj G v u w hu hw) = e := by
  intro e he
  by_cases h1 : e = s(v, u)
  · subst h1
    exact ⟨s(none, some u), (adj_ns G v u w u).mpr (Or.inl rfl), by simp [proj]⟩
  by_cases h2 : e = s(v, w)
  · subst h2
    exact ⟨s(none, some w), (adj_ns G v u w w).mpr (Or.inr rfl), by simp [proj]⟩
  induction e using Sym2.ind with
  | _ a b =>
  exact ⟨s(some a, some b), (adj_ss G v u w a b).mpr ⟨he, h1, h2⟩, by simp [proj]⟩

end SplitAux

namespace SplitAux
open Finset SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V]

lemma deg_eq_filter (H : SimpleGraph V) [DecidableRel H.Adj] (x : V) :
    H.degree x = #(H.edgeFinset.filter (x ∈ ·)) := by
  rw [← card_incidenceFinset_eq_degree, incidenceFinset_eq_filter]


lemma image_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj] (v u w : V) (hu : G.Adj v u) (hw : G.Adj v w)
    (huw : u ≠ w) [DecidableRel (split G v u w).Adj]
    :
    (split G v u w).edgeFinset.image (Sym2.map (proj G v u w hu hw)) = G.edgeFinset := by
  ext e
  simp only [mem_image, mem_edgeFinset]
  constructor
  · rintro ⟨e', he', rfl⟩
    exact (proj G v u w hu hw).map_mem_edgeSet he'
  · intro he
    exact map_surj G v u w hu hw e he

lemma card_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj] (v u w : V) (hu : G.Adj v u) (hw : G.Adj v w)
    (huw : u ≠ w) [DecidableRel (split G v u w).Adj]
    : #(split G v u w).edgeFinset = #G.edgeFinset := by
  rw [← image_edgeFinset G v u w hu hw huw, card_image_of_injOn]
  intro a ha b hb h
  exact map_injOn G v u w hu hw huw a (mem_edgeFinset.mp ha) b (mem_edgeFinset.mp hb) h

lemma filter_card (G : SimpleGraph V) [DecidableRel G.Adj] (v u w : V) (hu : G.Adj v u) (hw : G.Adj v w)
    (huw : u ≠ w) [DecidableRel (split G v u w).Adj]
    (x : V) :
    #(G.edgeFinset.filter (x ∈ ·)) =
      #((split G v u w).edgeFinset.filter (fun e => x ∈ e.map (proj G v u w hu hw))) := by
  rw [← image_edgeFinset G v u w hu hw huw, filter_image, card_image_of_injOn]
  intro a ha b hb h
  exact map_injOn G v u w hu hw huw a (mem_edgeFinset.mp (mem_filter.mp ha).1) b
    (mem_edgeFinset.mp (mem_filter.mp hb).1) h

lemma degree_some (G : SimpleGraph V) [DecidableRel G.Adj] (v u w : V) (hu : G.Adj v u) (hw : G.Adj v w)
    (huw : u ≠ w) [DecidableRel (split G v u w).Adj]
    (x : V) (hx : x ≠ v) : (split G v u w).degree (some x) = G.degree x := by
  rw [deg_eq_filter, deg_eq_filter, filter_card G v u w hu hw huw]
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

lemma degree_none (G : SimpleGraph V) [DecidableRel G.Adj] (v u w : V) (hu : G.Adj v u) (hw : G.Adj v w)
    (huw : u ≠ w) [DecidableRel (split G v u w).Adj]
    : (split G v u w).degree none = 2 := by
  rw [← card_neighborFinset_eq_degree]
  have : (split G v u w).neighborFinset none = {some u, some w} := by
    ext y
    rw [mem_neighborFinset]
    rcases y with _ | b
    · simp [not_adj_nn]
    · rw [adj_ns]; simp
  rw [this, card_pair (by simpa using huw)]

lemma degree_v (G : SimpleGraph V) [DecidableRel G.Adj] (v u w : V) (hu : G.Adj v u) (hw : G.Adj v w)
    (huw : u ≠ w) [DecidableRel (split G v u w).Adj]
    : G.degree v = (split G v u w).degree (some v) + 2 := by
  rw [← degree_none G v u w hu hw huw, deg_eq_filter, deg_eq_filter, deg_eq_filter,
    filter_card G v u w hu hw huw, ← card_union_of_disjoint]
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
    rw [this, mem_edgeSet, adj_sn] at h1
    rcases h1.1 with h | h
    · exact hu.ne h
    · exact hw.ne h

end SplitAux

namespace FlAux
open Finset SimpleGraph

variable {W : Type} [Fintype W] [DecidableEq W]

/-- Number of darts leaving `S` (= number of edges between `S` and its complement). -/
def cut (H : SimpleGraph W) [DecidableRel H.Adj] (S : Finset W) : ℕ :=
  #(univ.filter (fun d : H.Dart => d.fst ∈ S ∧ d.snd ∉ S))

lemma cut_ne_one (H : SimpleGraph W) [DecidableRel H.Adj] (hb : H.IsBridgeless) (S : Finset W) :
    cut H S ≠ 1 := by
  intro h
  obtain ⟨d, hd⟩ := card_eq_one.mp h
  have hdm : d ∈ univ.filter (fun d : H.Dart => d.fst ∈ S ∧ d.snd ∉ S) := by rw [hd]; simp
  obtain ⟨hdS, hdS'⟩ := (mem_filter.mp hdm).2
  have hnb := hb s(d.fst, d.snd) d.adj
  rw [isBridge_iff, not_not] at hnb
  obtain ⟨p⟩ := hnb
  obtain ⟨d', hd'p, h1, h2⟩ := p.exists_boundary_dart (S : Set W) hdS hdS'
  have hadj := d'.adj
  rw [deleteEdges_adj] at hadj
  let d'' : H.Dart := ⟨d'.toProd, hadj.1⟩
  have : d'' ∈ univ.filter (fun d : H.Dart => d.fst ∈ S ∧ d.snd ∉ S) :=
    mem_filter.mpr ⟨mem_univ _, h1, h2⟩
  rw [hd, mem_singleton] at this
  apply hadj.2
  have e1 : d'.fst = d.fst := congrArg (fun d : SimpleGraph.Dart _ => d.fst) this
  have e2 : d'.snd = d.snd := congrArg (fun d : SimpleGraph.Dart _ => d.snd) this
  show s(d'.toProd.1, d'.toProd.2) ∈ _
  change s(d'.fst, d'.snd) ∈ _
  rw [e1, e2]; rfl

lemma bridgeless_of_cut (H : SimpleGraph W) [DecidableRel H.Adj] (h : ∀ S, cut H S ≠ 1) :
    H.IsBridgeless := by
  intro e he hbr
  induction e using Sym2.ind with
  | _ a b =>
  rw [isBridge_iff] at hbr
  rw [mem_edgeSet] at he
  apply h (univ.filter (fun z => (H.deleteEdges {s(a, b)}).Reachable a z))
  apply card_eq_one.mpr
  refine ⟨⟨(a, b), he⟩, ?_⟩
  ext d
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases hde : s(d.fst, d.snd) = s(a, b)
    · rcases Sym2.eq_iff.mp hde with ⟨x, y⟩ | ⟨x, y⟩
      · apply Dart.ext; exact Prod.ext x y
      · exfalso; rw [x] at h1; exact hbr h1
    · exfalso; apply h2
      exact h1.trans (Adj.reachable (by rw [deleteEdges_adj]; exact ⟨d.adj, by simpa using hde⟩))
  · rintro rfl
    exact ⟨Reachable.refl _, hbr⟩

lemma cut_compl (H : SimpleGraph W) [DecidableRel H.Adj] (S : Finset W) : cut H Sᶜ = cut H S := by
  unfold cut
  apply card_bij (fun d _ => d.symm)
  · intro d hd
    simp only [mem_filter, mem_univ, true_and, mem_compl, not_not] at hd ⊢
    exact ⟨hd.2, hd.1⟩
  · intro d₁ _ d₂ _ h
    simpa using congrArg Dart.symm h
  · intro d hd
    refine ⟨d.symm, ?_, by simp⟩
    simp only [mem_filter, mem_univ, true_and, mem_compl, not_not] at hd ⊢
    exact ⟨hd.2, hd.1⟩

/-- Darts out of a vertex `v ∈ S` to neighbours outside `S` are cut darts. -/
lemma card_nbr_le_cut (H : SimpleGraph W) [DecidableRel H.Adj] (S : Finset W) (v : W)
    (hv : v ∈ S) : #(H.neighborFinset v \ S) ≤ cut H S := by
  unfold cut
  rw [← card_attach]
  refine card_le_card_of_injOn (fun z => (⟨(v, z.1), (mem_neighborFinset _ _ _).mp
    (mem_sdiff.mp z.2).1⟩ : H.Dart)) ?_ ?_
  · intro z _
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
    exact ⟨hv, (mem_sdiff.mp z.2).2⟩
  · intro z₁ _ z₂ _ h
    have : z₁.1 = z₂.1 := congrArg (fun d : H.Dart => d.snd) h
    exact Subtype.ext this

end FlAux

namespace FlAux
open Finset SimpleGraph

variable {W : Type} [Fintype W] [DecidableEq W]

lemma cut_insert (H : SimpleGraph W) [DecidableRel H.Adj] (S : Finset W) (z : W) (hz : z ∉ S) :
    cut H (insert z S) + 2 * #(univ.filter (fun d : H.Dart => d.fst = z ∧ d.snd ∈ S)) =
      cut H S + H.degree z := by
  have hsym : #(univ.filter (fun d : H.Dart => d.snd = z ∧ d.fst ∈ S)) =
      #(univ.filter (fun d : H.Dart => d.fst = z ∧ d.snd ∈ S)) := by
    apply card_bij (fun d _ => d.symm)
    · intro d hd; simp only [mem_filter, mem_univ, true_and] at hd ⊢; exact ⟨hd.1, hd.2⟩
    · intro d₁ _ d₂ _ h; simpa using congrArg Dart.symm h
    · intro d hd; refine ⟨d.symm, ?_, by simp⟩
      simp only [mem_filter, mem_univ, true_and] at hd ⊢; exact ⟨hd.1, hd.2⟩
  have hdeg : #(univ.filter (fun d : H.Dart => d.fst = z)) = H.degree z :=
    H.dart_fst_fiber_card_eq_degree z
  rw [two_mul, ← hdeg]
  nth_rewrite 2 [← hsym]
  unfold cut
  simp only [card_filter]
  rw [← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro d _
  have hne := d.adj.ne
  by_cases ha : d.fst = z <;> by_cases hb : d.snd = z <;> by_cases hA : d.fst ∈ S <;>
    by_cases hB : d.snd ∈ S <;> simp_all

end FlAux

namespace SplitAux
open Finset SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V]


/-- The projection on darts. -/
def pd (G : SimpleGraph V) [DecidableRel G.Adj] (v u w : V) (hu : G.Adj v u) (hw : G.Adj v w)
    (d : (split G v u w).Dart) : G.Dart :=
  ⟨(d.fst.getD v, d.snd.getD v), (proj G v u w hu hw).map_adj d.adj⟩

lemma pd_injective (G : SimpleGraph V) [DecidableRel G.Adj] (v u w : V) (hu : G.Adj v u) (hw : G.Adj v w)
    (huw : u ≠ w)
    : Function.Injective (pd G v u w hu hw) := by
  intro d₁ d₂ h
  have h1 : d₁.fst.getD v = d₂.fst.getD v := congrArg (fun d : G.Dart => d.fst) h
  have h2 : d₁.snd.getD v = d₂.snd.getD v := congrArg (fun d : G.Dart => d.snd) h
  have he : d₁.edge = d₂.edge := by
    apply map_injOn G v u w hu hw huw _ d₁.edge_mem _ d₂.edge_mem
    show Sym2.map (fun x => x.getD v) s(d₁.fst, d₁.snd) = Sym2.map (fun x => x.getD v) s(d₂.fst, d₂.snd)
    simp only [Sym2.map_pair_eq, h1, h2]
  rcases (dart_edge_eq_iff d₁ d₂).mp he with h | h
  · exact h
  · exfalso
    have a1 : d₁.fst = d₂.snd := by rw [h]; rfl
    have a2 : d₁.snd = d₂.fst := by rw [h]; rfl
    have := ((proj G v u w hu hw).map_adj d₂.adj).ne
    apply this
    show d₂.fst.getD v = d₂.snd.getD v
    rw [← a2]; exact h2

end SplitAux

namespace SplitAux
open Finset SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V]


lemma pd_bijective (G : SimpleGraph V) [DecidableRel G.Adj] (v u w : V) (hu : G.Adj v u) (hw : G.Adj v w)
    (huw : u ≠ w) [DecidableRel (split G v u w).Adj]
    : Function.Bijective (pd G v u w hu hw) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨pd_injective G v u w hu hw huw, ?_⟩
  rw [dart_card_eq_twice_card_edges, dart_card_eq_twice_card_edges,
    card_edgeFinset G v u w hu hw huw]

lemma cut_eq (G : SimpleGraph V) [DecidableRel G.Adj] (v u w : V) (hu : G.Adj v u) (hw : G.Adj v w)
    (huw : u ≠ w) [DecidableRel (split G v u w).Adj]
    (X : Finset V) (X'' : Finset (Option V)) (hX : ∀ z, z ∈ X'' ↔ z.getD v ∈ X) :
    FlAux.cut G X = FlAux.cut (split G v u w) X'' := by
  unfold FlAux.cut
  symm
  apply card_bij (fun d _ => pd G v u w hu hw d)
  · intro d hd
    simp only [mem_filter, mem_univ, true_and] at hd ⊢
    rw [hX, hX] at hd
    exact hd
  · intro d₁ _ d₂ _ h
    exact pd_injective G v u w hu hw huw h
  · intro d hd
    obtain ⟨d', rfl⟩ := (pd_bijective G v u w hu hw huw).2 d
    refine ⟨d', ?_, rfl⟩
    simp only [mem_filter, mem_univ, true_and] at hd ⊢
    rw [hX, hX]
    exact hd

lemma bad_of_not_bridgeless (G : SimpleGraph V) [DecidableRel G.Adj] (v u w : V) (hu : G.Adj v u) (hw : G.Adj v w)
    (huw : u ≠ w) [DecidableRel (split G v u w).Adj]
    (hb : G.IsBridgeless) (hnb : ¬ (split G v u w).IsBridgeless) :
    ∃ X : Finset V, v ∈ X ∧ u ∉ X ∧ w ∉ X ∧ FlAux.cut G X = 3 := by
  have h1 : ∃ S, FlAux.cut (split G v u w) S = 1 := by
    by_contra h
    push_neg at h
    exact hnb (FlAux.bridgeless_of_cut _ h)
  obtain ⟨X1, hX1, hv1⟩ : ∃ S, FlAux.cut (split G v u w) S = 1 ∧ some v ∈ S := by
    obtain ⟨S, hS⟩ := h1
    by_cases hv : some v ∈ S
    · exact ⟨S, hS, hv⟩
    · exact ⟨Sᶜ, by rw [FlAux.cut_compl]; exact hS, mem_compl.mpr hv⟩
  set X : Finset V := univ.filter (fun a => some a ∈ X1) with hXdef
  have hvX : v ∈ X := by simp [hXdef, hv1]
  have hsome : ∀ a, a ∈ X ↔ some a ∈ X1 := by intro a; simp [hXdef]
  by_cases hn : none ∈ X1
  · exfalso
    have hag : ∀ z, z ∈ X1 ↔ z.getD v ∈ X := by
      intro z; rcases z with _ | a
      · simp [hn, hvX]
      · simp [hsome]
    have := cut_eq G v u w hu hw huw X X1 hag
    exact FlAux.cut_ne_one G hb X (by rw [this, hX1])
  · have hag : ∀ z, z ∈ insert none X1 ↔ z.getD v ∈ X := by
      intro z; rcases z with _ | a
      · simp [hvX]
      · simp [hsome]
    have hc := cut_eq G v u w hu hw huw X _ hag
    have hins := FlAux.cut_insert (split G v u w) X1 none hn
    rw [degree_none G v u w hu hw huw, hX1, ← hc] at hins
    have hne := FlAux.cut_ne_one G hb X
    set k := #(univ.filter (fun d : (split G v u w).Dart => d.fst = none ∧ d.snd ∈ X1)) with hk
    have hk0 : k = 0 := by omega
    have hmem : ∀ b, (b = u ∨ b = w) → b ∉ X := by
      intro b hb' hbX
      have hd : (⟨(none, some b), (adj_ns G v u w b).mpr hb'⟩ : (split G v u w).Dart) ∈
          univ.filter (fun d : (split G v u w).Dart => d.fst = none ∧ d.snd ∈ X1) := by
        rw [mem_filter]
        exact ⟨mem_univ _, rfl, (hsome b).mp hbX⟩
      have : 0 < k := card_pos.mpr ⟨_, hd⟩
      omega
    exact ⟨X, hvX, hmem u (Or.inl rfl), hmem w (Or.inr rfl), by omega⟩

end SplitAux

namespace FlAux
open Finset SimpleGraph

variable {W : Type} [Fintype W] [DecidableEq W]

/-- Darts from region `i` to region `j`. -/
def m (H : SimpleGraph W) [DecidableRel H.Adj] (reg : W → Fin 4) (i j : Fin 4) : ℕ :=
  #(univ.filter (fun d : H.Dart => reg d.fst = i ∧ reg d.snd = j))

lemma m_symm (H : SimpleGraph W) [DecidableRel H.Adj] (reg : W → Fin 4) (i j : Fin 4) :
    m H reg i j = m H reg j i := by
  unfold m
  apply card_bij (fun d _ => d.symm)
  · intro d hd; simp only [mem_filter, mem_univ, true_and] at hd ⊢; exact ⟨hd.2, hd.1⟩
  · intro d₁ _ d₂ _ h; simpa using congrArg Dart.symm h
  · intro d hd; refine ⟨d.symm, ?_, by simp⟩
    simp only [mem_filter, mem_univ, true_and] at hd ⊢; exact ⟨hd.2, hd.1⟩

lemma cut_reg (H : SimpleGraph W) [DecidableRel H.Adj] (reg : W → Fin 4) (T : Finset (Fin 4)) :
    cut H (univ.filter (fun z => reg z ∈ T)) =
      ∑ i, ∑ j, if i ∈ T ∧ j ∉ T then m H reg i j else 0 := by
  unfold cut m
  simp only [card_filter, mem_filter, mem_univ, true_and]
  have : ∀ i j : Fin 4, (if i ∈ T ∧ j ∉ T then
      ∑ d : H.Dart, (if reg d.fst = i ∧ reg d.snd = j then 1 else 0) else 0) =
      ∑ d : H.Dart, (if reg d.fst = i then (if reg d.snd = j then
        (if i ∈ T ∧ j ∉ T then 1 else 0) else 0) else 0) := by
    intro i j
    split_ifs with h
    · apply sum_congr rfl; intro d _
      by_cases h1 : reg d.fst = i <;> by_cases h2 : reg d.snd = j <;> simp [h1, h2, h]
    · symm; apply sum_eq_zero; intro d _
      by_cases h1 : reg d.fst = i <;> by_cases h2 : reg d.snd = j <;> simp [h1, h2, h]
  simp only [this]
  symm
  calc _ = ∑ i : Fin 4, ∑ d : H.Dart, ∑ j : Fin 4, (if reg d.fst = i then (if reg d.snd = j then
        (if i ∈ T ∧ j ∉ T then 1 else 0) else 0) else 0) :=
        sum_congr rfl (fun i _ => sum_comm)
    _ = ∑ d : H.Dart, ∑ i : Fin 4, ∑ j : Fin 4, (if reg d.fst = i then (if reg d.snd = j then
        (if i ∈ T ∧ j ∉ T then 1 else 0) else 0) else 0) := sum_comm
    _ = _ := by
        apply sum_congr rfl; intro d _
        simp [Finset.sum_ite_eq']

end FlAux

namespace FlAux
open Finset SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V]

/-- For every edge `vu₁` at a vertex of degree at least four there is a partner `vw` such that
no 3-edge cut separates `v` from `u₁` and `w`. -/
lemma partner (G : SimpleGraph V) [DecidableRel G.Adj] (hb : G.IsBridgeless) (v u1 : V)
    (hu1 : G.Adj v u1) (hdeg : 4 ≤ G.degree v) :
    ∃ w, w ≠ u1 ∧ G.Adj v w ∧ ¬ ∃ X : Finset V, v ∈ X ∧ u1 ∉ X ∧ w ∉ X ∧ cut G X = 3 := by
  classical
  by_contra hcon
  push_neg at hcon
  have hN : 1 < #(G.neighborFinset v) := by rw [card_neighborFinset_eq_degree]; omega
  obtain ⟨w0, hw0, hw0ne⟩ := exists_mem_ne hN u1
  have hex : ∃ n, ∃ w X, w ≠ u1 ∧ G.Adj v w ∧ v ∈ X ∧ u1 ∉ X ∧ w ∉ X ∧ cut G X = 3 ∧
      #X = n := by
    obtain ⟨X, h1, h2, h3, h4⟩ := hcon w0 hw0ne ((mem_neighborFinset _ _ _).mp hw0)
    exact ⟨_, w0, X, hw0ne, (mem_neighborFinset _ _ _).mp hw0, h1, h2, h3, h4, rfl⟩
  obtain ⟨uj, X, hj1, hj2, hvX, hu1X, hujX, hcX, hXn⟩ := Nat.find_spec hex
  obtain ⟨uk, hukN, hukX⟩ : ∃ z ∈ G.neighborFinset v, z ∈ X := by
    by_contra h
    push_neg at h
    have h1 : G.neighborFinset v \ X = G.neighborFinset v :=
      sdiff_eq_self_of_disjoint (Finset.disjoint_left.mpr h)
    have h2 := card_nbr_le_cut G X v hvX
    rw [h1, card_neighborFinset_eq_degree] at h2
    omega
  have hukA := (mem_neighborFinset _ _ _).mp hukN
  have huk1 : uk ≠ u1 := fun h => hu1X (h ▸ hukX)
  obtain ⟨Y, hvY, hu1Y, hukY, hcY⟩ := hcon uk huk1 hukA
  have hcA : cut G (X ∩ Y) ≠ 3 := by
    intro h
    have hlt : #(X ∩ Y) < Nat.find hex := by
      rw [← hXn]; apply card_lt_card
      exact ⟨inter_subset_left, fun hsub => hukY (mem_inter.mp (hsub hukX)).2⟩
    exact Nat.find_min hex hlt ⟨uj, X ∩ Y, hj1, hj2, mem_inter.mpr ⟨hvX, hvY⟩,
      fun h => hu1X (mem_inter.mp h).1, fun h => hujX (mem_inter.mp h).1, h, rfl⟩
  let reg : V → Fin 4 := fun z =>
    if z ∈ X then (if z ∈ Y then 0 else 1) else (if z ∈ Y then 2 else 3)
  have eX : univ.filter (fun z => reg z ∈ ({0, 1} : Finset (Fin 4))) = X := by
    ext z; simp only [mem_filter, mem_univ, true_and, reg]; split_ifs <;> simp_all
  have eY : univ.filter (fun z => reg z ∈ ({0, 2} : Finset (Fin 4))) = Y := by
    ext z; simp only [mem_filter, mem_univ, true_and, reg]; split_ifs <;> simp_all
  have eA : univ.filter (fun z => reg z ∈ ({0} : Finset (Fin 4))) = X ∩ Y := by
    ext z; simp only [mem_filter, mem_univ, true_and, reg, mem_inter]; split_ifs <;> simp_all
  have cX := cut_reg G reg {0, 1}
  have cY := cut_reg G reg {0, 2}
  have cA := cut_reg G reg {0}
  have cP := cut_reg G reg {1}
  have cQ := cut_reg G reg {2}
  have cR := cut_reg G reg {3}
  rw [eX] at cX
  rw [eY] at cY
  rw [eA] at cA
  have nP := cut_ne_one G hb (univ.filter (fun z => reg z ∈ ({1} : Finset (Fin 4))))
  have nQ := cut_ne_one G hb (univ.filter (fun z => reg z ∈ ({2} : Finset (Fin 4))))
  have nR := cut_ne_one G hb (univ.filter (fun z => reg z ∈ ({3} : Finset (Fin 4))))
  rw [cP] at nP
  rw [cQ] at nQ
  rw [cR] at nR
  simp [Fin.sum_univ_four] at cX cY cA nP nQ nR
  have s01 := m_symm G reg 0 1
  have s02 := m_symm G reg 0 2
  have s03 := m_symm G reg 0 3
  have s12 := m_symm G reg 1 2
  have s13 := m_symm G reg 1 3
  have s23 := m_symm G reg 2 3
  have rv : reg v = 0 := by simp [reg, hvX, hvY]
  have r1 : reg u1 = 3 := by simp [reg, hu1X, hu1Y]
  have rk : reg uk = 1 := by simp [reg, hukX, hukY]
  have b03 : 1 ≤ m G reg 0 3 := by
    apply card_pos.mpr
    exact ⟨⟨(v, u1), hu1⟩, by simp only [mem_filter, mem_univ, true_and]; exact ⟨rv, r1⟩⟩
  have b01 : 1 ≤ m G reg 0 1 := by
    apply card_pos.mpr
    exact ⟨⟨(v, uk), hukA⟩, by simp only [mem_filter, mem_univ, true_and]; exact ⟨rv, rk⟩⟩
  have b023 : 2 ≤ m G reg 0 2 + m G reg 0 3 := by
    by_cases hujY : uj ∈ Y
    · have rj : reg uj = 2 := by simp [reg, hujX, hujY]
      have : 1 ≤ m G reg 0 2 := by
        apply card_pos.mpr
        exact ⟨⟨(v, uj), hj2⟩, by simp only [mem_filter, mem_univ, true_and]; exact ⟨rv, rj⟩⟩
      omega
    · have rj : reg uj = 3 := by simp [reg, hujX, hujY]
      have : 1 < m G reg 0 3 := by
        apply one_lt_card.mpr
        refine ⟨⟨(v, u1), hu1⟩, ?_, ⟨(v, uj), hj2⟩, ?_, ?_⟩
        · simp only [mem_filter, mem_univ, true_and]; exact ⟨rv, r1⟩
        · simp only [mem_filter, mem_univ, true_and]; exact ⟨rv, rj⟩
        · intro h
          exact hj1 (congrArg (fun d : G.Dart => d.snd) h).symm
      omega
  omega

end FlAux

open Finset SimpleGraph in
theorem OMA.solution : OMA.R_Arxiv_2607_06396_alon_tarsi_short_cycle_cover_R1_H2_R1_H2_R1.H2 := by
  intro V _ _ G _ hb v hv
  classical
  have hpos : 0 < #(G.neighborFinset v) := by rw [card_neighborFinset_eq_degree]; omega
  obtain ⟨u1, hu1N⟩ := card_pos.mp hpos
  have hu1 := (mem_neighborFinset _ _ _).mp hu1N
  obtain ⟨w, hw1, hw, hno⟩ := FlAux.partner G hb v u1 hu1 hv
  refine ⟨u1, w, hw1.symm, hu1, hw, ?_⟩
  show (SplitAux.split G v u1 w).IsBridgeless
  by_contra hnb
  exact hno (SplitAux.bad_of_not_bridgeless G v u1 w hu1 hw hw1.symm hb hnb)
