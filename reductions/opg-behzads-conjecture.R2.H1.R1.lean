import OMAReductions.R_opg_behzads_conjecture_R2

-- Reduction opg-behzads-conjecture.R2.H1.R1 of step opg-behzads-conjecture.R2.H1
-- Credit: @neoKMS0

/-!
# Reduction of `3 ≤ Δ ≤ 5` Total Colouring to Connected Graphs on `Fin n` with `δ ≥ 3`

This file reduces `OMA.R_opg_behzads_conjecture_R2.H1` (every finite simple graph with `3 ≤ Δ ≤ 5`
admits a `(Δ + 2)`-total colouring) to three independent statements on connected graphs on `Fin n`:

* `H1`: connected cubic (`3`-regular) graphs on `Fin n` admit a `5`-total colouring
  (Rosenfeld 1971, Vijayaditya 1971);
* `H2`: connected graphs on `Fin n` with `3 ≤ δ` and `Δ = 4` admit a `6`-total colouring
  (Kostochka 1977);
* `H3`: connected graphs on `Fin n` with `3 ≤ δ` and `Δ = 5` admit a `7`-total colouring
  (Kostochka 1996).

The reduction proves:
1. connected-component decomposition (`glue_disjoint_cut`),
2. greedy vertex-deletion extension for vertices of degree `≤ 2` when `3 ≤ d` and `Δ ≤ d`
   (`extend_vertex_deg_le_two`),
3. reuse of `coloring_four_of_maxDegree_le_two` from the parent reduction whenever `Δ ≤ 2`, and
4. transport along `V ≃ Fin n` (`iso_pullback_coloring`).
-/

namespace OMA.R_opg_behzads_conjecture_R2_H1_R1

open OMA.S_opg_behzads_conjecture

/-- Total Colouring Conjecture for connected cubic graphs (`Δ = 3`). -/
def H1 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.Connected → G.IsRegularOfDegree 3 →
      ∃ (cv : Fin n → Fin 5) (ce : G.edgeSet → Fin 5), IsTotalColoring G cv ce

/-- Total Colouring Conjecture for connected graphs with `3 ≤ δ` and `Δ = 4`. -/
def H2 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.Connected → 3 ≤ G.minDegree → G.maxDegree = 4 →
      ∃ (cv : Fin n → Fin 6) (ce : G.edgeSet → Fin 6), IsTotalColoring G cv ce

/-- Total Colouring Conjecture for connected graphs with `3 ≤ δ` and `Δ = 5`. -/
def H3 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.Connected → 3 ≤ G.minDegree → G.maxDegree = 5 →
      ∃ (cv : Fin n → Fin 7) (ce : G.edgeSet → Fin 7), IsTotalColoring G cv ce

section Helpers

private lemma cast_coloring {V : Type} {G : SimpleGraph V} {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂)
    (h : ∃ (cv : V → Fin k₁) (ce : G.edgeSet → Fin k₁), IsTotalColoring G cv ce) :
    ∃ (cv : V → Fin k₂) (ce : G.edgeSet → Fin k₂), IsTotalColoring G cv ce := by
  obtain ⟨cv, ce, h1, h2, h3⟩ := h
  refine ⟨fun v => Fin.castLE hk (cv v), fun e => Fin.castLE hk (ce e), ?_, ?_, ?_⟩
  · intro u v huv hc
    exact h1 u v huv (Fin.castLE_injective hk hc)
  · intro e f hef hs hc
    exact h2 e f hef hs (Fin.castLE_injective hk hc)
  · intro e v hv hc
    exact h3 e v hv (Fin.castLE_injective hk hc)

private lemma iso_pullback_coloring {V W : Type} {G : SimpleGraph V} {G' : SimpleGraph W}
    (φ : G ≃g G') {k : ℕ}
    (h : ∃ (cv : W → Fin k) (ce : G'.edgeSet → Fin k), IsTotalColoring G' cv ce) :
    ∃ (cv : V → Fin k) (ce : G.edgeSet → Fin k), IsTotalColoring G cv ce := by
  obtain ⟨cv', ce', h1, h2, h3⟩ := h
  refine ⟨fun v => cv' (φ v), fun e => ce' (φ.mapEdgeSet e), ?_, ?_, ?_⟩
  · intro u v huv
    exact h1 (φ u) (φ v) (φ.map_adj_iff.mpr huv)
  · rintro e f hef ⟨v, hve, hvf⟩
    refine h2 (φ.mapEdgeSet e) (φ.mapEdgeSet f) (fun heq => hef (φ.mapEdgeSet.injective heq)) ?_
    exact ⟨φ v, Sym2.mem_map.mpr ⟨v, hve, rfl⟩, Sym2.mem_map.mpr ⟨v, hvf, rfl⟩⟩
  · intro e v hve
    exact h3 (φ.mapEdgeSet e) (φ v) (Sym2.mem_map.mpr ⟨v, hve, rfl⟩)

private lemma iso_degree_eq {V W : Type} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {G' : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (φ : G ≃g G') (v : V) : G.degree v = G'.degree (φ v) := by
  rw [← G.card_neighborSet_eq_degree, ← G'.card_neighborSet_eq_degree]
  exact Fintype.card_congr (φ.mapNeighborSet v)

private lemma iso_maxDegree_eq {V W : Type} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {G' : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (φ : G ≃g G') : G.maxDegree = G'.maxDegree := by
  apply le_antisymm
  · refine G.maxDegree_le_of_forall_degree_le _ fun v => ?_
    rw [iso_degree_eq φ v]
    exact G'.degree_le_maxDegree (φ v)
  · refine G'.maxDegree_le_of_forall_degree_le _ fun w => ?_
    have h := G.degree_le_maxDegree (φ.symm w)
    rw [iso_degree_eq φ (φ.symm w)] at h
    simpa using h

private lemma exists_edge_induce {V : Type} {G : SimpleGraph V} (S : Set V)
    (e : G.edgeSet) (hs : ∀ v ∈ (e : Sym2 V), v ∈ S) :
    ∃ e' : (G.induce S).edgeSet, Sym2.map Subtype.val e'.1 = e.1 := by
  rcases e with ⟨z, hz⟩
  induction z using Sym2.ind with
  | _ u v =>
    refine ⟨⟨s(⟨u, hs u (Sym2.mem_mk_left u v)⟩, ⟨v, hs v (Sym2.mem_mk_right u v)⟩), ?_⟩, rfl⟩
    simpa [SimpleGraph.mem_edgeSet] using hz

private lemma induce_edge_mem_iff {V : Type} {G : SimpleGraph V} {S : Set V}
    {e : G.edgeSet} {e' : (G.induce S).edgeSet} (he : Sym2.map Subtype.val e'.1 = e.1)
    (v : S) : v ∈ e'.1 ↔ v.1 ∈ e.1 := by
  rw [← he, Sym2.mem_map]
  constructor
  · intro hv
    exact ⟨v, hv, rfl⟩
  · rintro ⟨w, hw, hvw⟩
    exact Subtype.ext hvw ▸ hw

private lemma induce_edge_inj {V : Type} {G : SimpleGraph V} {S : Set V}
    {e₁ e₂ : G.edgeSet} {e₁' e₂' : (G.induce S).edgeSet}
    (h1 : Sym2.map Subtype.val e₁'.1 = e₁.1) (h2 : Sym2.map Subtype.val e₂'.1 = e₂.1)
    (he : e₁' = e₂') : e₁ = e₂ := by
  apply Subtype.ext
  rw [← h1, ← h2, he]

private lemma glue_disjoint_cut {V : Type} {G : SimpleGraph V}
    (P : V → Prop) [DecidablePred P] (hcut : ∀ u v, G.Adj u v → (P u ↔ P v)) {k : ℕ}
    (hP : ∃ (cv : {x | P x} → Fin k) (ce : (G.induce {x | P x}).edgeSet → Fin k),
      IsTotalColoring (G.induce {x | P x}) cv ce)
    (hNP : ∃ (cv : {x | ¬ P x} → Fin k) (ce : (G.induce {x | ¬ P x}).edgeSet → Fin k),
      IsTotalColoring (G.induce {x | ¬ P x}) cv ce) :
    ∃ (cv : V → Fin k) (ce : G.edgeSet → Fin k), IsTotalColoring G cv ce := by
  classical
  obtain ⟨cv₁, ce₁, h1v, h1e, h1i⟩ := hP
  obtain ⟨cv₂, ce₂, h2v, h2e, h2i⟩ := hNP
  have hallP : ∀ (e : G.edgeSet), (∃ x ∈ (e : Sym2 V), P x) → ∀ v ∈ (e : Sym2 V), P v := by
    rintro ⟨z, hz⟩ ⟨x, hx, hPx⟩ v hv
    induction z using Sym2.ind with
    | _ a b =>
      simp only [SimpleGraph.mem_edgeSet] at hz
      simp only [Sym2.mem_iff] at hx hv
      rcases hx with rfl | rfl <;> rcases hv with rfl | rfl
      · exact hPx
      · exact (hcut x v hz).mp hPx
      · exact (hcut v x hz).mpr hPx
      · exact hPx
  have hallNP : ∀ (e : G.edgeSet), ¬ (∃ x ∈ (e : Sym2 V), P x) → ∀ v ∈ (e : Sym2 V), ¬ P v := by
    intro e hnex v hv hPv
    exact hnex ⟨v, hv, hPv⟩
  let cv : V → Fin k := fun v => if h : P v then cv₁ ⟨v, h⟩ else cv₂ ⟨v, h⟩
  let ce : G.edgeSet → Fin k := fun e =>
    if h : ∃ x ∈ (e : Sym2 V), P x then
      ce₁ (Classical.choose (exists_edge_induce {x | P x} e (hallP e h)))
    else
      ce₂ (Classical.choose (exists_edge_induce {x | ¬ P x} e (hallNP e h)))
  refine ⟨cv, ce, ?_, ?_, ?_⟩
  · intro u v huv
    by_cases hu : P u
    · have hv : P v := (hcut u v huv).mp hu
      simp only [cv, dif_pos hu, dif_pos hv]
      exact h1v ⟨u, hu⟩ ⟨v, hv⟩ huv
    · have hv : ¬ P v := fun h => hu ((hcut u v huv).mpr h)
      simp only [cv, dif_neg hu, dif_neg hv]
      exact h2v ⟨u, hu⟩ ⟨v, hv⟩ huv
  · rintro e f hef ⟨v, hve, hvf⟩
    by_cases hv : P v
    · have heP : ∃ x ∈ (e : Sym2 V), P x := ⟨v, hve, hv⟩
      have hfP : ∃ x ∈ (f : Sym2 V), P x := ⟨v, hvf, hv⟩
      simp only [ce, dif_pos heP, dif_pos hfP]
      let e' := Classical.choose (exists_edge_induce {x | P x} e (hallP e heP))
      let f' := Classical.choose (exists_edge_induce {x | P x} f (hallP f hfP))
      have he' : Sym2.map Subtype.val e'.1 = e.1 :=
        Classical.choose_spec (exists_edge_induce {x | P x} e (hallP e heP))
      have hf' : Sym2.map Subtype.val f'.1 = f.1 :=
        Classical.choose_spec (exists_edge_induce {x | P x} f (hallP f hfP))
      refine h1e e' f' (fun heq => hef (induce_edge_inj he' hf' heq)) ?_
      exact ⟨⟨v, hv⟩, (induce_edge_mem_iff he' ⟨v, hv⟩).mpr hve,
        (induce_edge_mem_iff hf' ⟨v, hv⟩).mpr hvf⟩
    · have heNP : ¬ (∃ x ∈ (e : Sym2 V), P x) := fun h => hv (hallP e h v hve)
      have hfNP : ¬ (∃ x ∈ (f : Sym2 V), P x) := fun h => hv (hallP f h v hvf)
      simp only [ce, dif_neg heNP, dif_neg hfNP]
      let e' := Classical.choose (exists_edge_induce {x | ¬ P x} e (hallNP e heNP))
      let f' := Classical.choose (exists_edge_induce {x | ¬ P x} f (hallNP f hfNP))
      have he' : Sym2.map Subtype.val e'.1 = e.1 :=
        Classical.choose_spec (exists_edge_induce {x | ¬ P x} e (hallNP e heNP))
      have hf' : Sym2.map Subtype.val f'.1 = f.1 :=
        Classical.choose_spec (exists_edge_induce {x | ¬ P x} f (hallNP f hfNP))
      refine h2e e' f' (fun heq => hef (induce_edge_inj he' hf' heq)) ?_
      exact ⟨⟨v, hv⟩, (induce_edge_mem_iff he' ⟨v, hv⟩).mpr hve,
        (induce_edge_mem_iff hf' ⟨v, hv⟩).mpr hvf⟩
  · intro e v hv
    by_cases hPv : P v
    · have heP : ∃ x ∈ (e : Sym2 V), P x := ⟨v, hv, hPv⟩
      simp only [ce, cv, dif_pos heP, dif_pos hPv]
      let e' := Classical.choose (exists_edge_induce {x | P x} e (hallP e heP))
      have he' : Sym2.map Subtype.val e'.1 = e.1 :=
        Classical.choose_spec (exists_edge_induce {x | P x} e (hallP e heP))
      exact h1i e' ⟨v, hPv⟩ ((induce_edge_mem_iff he' ⟨v, hPv⟩).mpr hv)
    · have heNP : ¬ (∃ x ∈ (e : Sym2 V), P x) := fun h => hPv (hallP e h v hv)
      simp only [ce, cv, dif_neg heNP, dif_neg hPv]
      let e' := Classical.choose (exists_edge_induce {x | ¬ P x} e (hallNP e heNP))
      have he' : Sym2.map Subtype.val e'.1 = e.1 :=
        Classical.choose_spec (exists_edge_induce {x | ¬ P x} e (hallNP e heNP))
      exact h2i e' ⟨v, hPv⟩ ((induce_edge_mem_iff he' ⟨v, hPv⟩).mpr hv)

private lemma induce_maxDegree_le {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Set V) [Fintype S] [DecidableRel (G.induce S).Adj] :
    (G.induce S).maxDegree ≤ G.maxDegree := by
  refine (G.induce S).maxDegree_le_of_forall_degree_le _ fun x => ?_
  have hdeg : (G.induce S).degree x ≤ G.degree x.1 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
    have hsub : ((G.induce S).neighborFinset x).map ⟨Subtype.val, Subtype.val_injective⟩ ⊆
        G.neighborFinset x.1 := by
      intro w hw
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hw
      rw [SimpleGraph.mem_neighborFinset] at hy ⊢
      exact hy
    simpa [Finset.card_map] using Finset.card_le_card hsub
  exact hdeg.trans (G.degree_le_maxDegree x.1)

private lemma induce_compl_degree_lt {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) [Fintype {x : V | x ≠ v}] [DecidableRel (G.induce {x : V | x ≠ v}).Adj]
    (u : {x : V | x ≠ v}) (hvu : G.Adj v u.1) :
    (G.induce {x : V | x ≠ v}).degree u + 1 ≤ G.degree u.1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  have hsub : ((G.induce {x : V | x ≠ v}).neighborFinset u).map
      ⟨Subtype.val, Subtype.val_injective⟩ ⊆ (G.neighborFinset u.1).erase v := by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hw
    rw [SimpleGraph.mem_neighborFinset] at hy
    exact Finset.mem_erase.mpr ⟨y.2, (G.mem_neighborFinset u.1 y.1).mpr hy⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_map, Finset.card_erase_of_mem ((G.mem_neighborFinset u.1 v).mpr hvu.symm)] at hcard
  have hpos : 0 < (G.neighborFinset u.1).card :=
    Finset.card_pos.mpr ⟨v, (G.mem_neighborFinset u.1 v).mpr hvu.symm⟩
  omega

private lemma choose_edge_color {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hΔ : G.maxDegree ≤ d) (v : V)
    [Fintype {x : V | x ≠ v}] [DecidableRel (G.induce {x : V | x ≠ v}).Adj]
    (cv' : {x : V | x ≠ v} → Fin (d + 2))
    (ce' : (G.induce {x : V | x ≠ v}).edgeSet → Fin (d + 2))
    (u : {x : V | x ≠ v}) (hvu : G.Adj v u.1)
    (forb : Finset (Fin (d + 2))) (hforb : forb.card ≤ 1) :
    ∃ c : Fin (d + 2), c ≠ cv' u ∧ c ∉ forb ∧
      ∀ (e' : (G.induce {x : V | x ≠ v}).edgeSet), u ∈ e'.1 → c ≠ ce' e' := by
  let adjColors : Finset (Fin (d + 2)) :=
    ((G.induce {x : V | x ≠ v}).neighborFinset u).attach.image fun w =>
      ce' ⟨s(u, w.1), (SimpleGraph.mem_edgeSet (G.induce {x : V | x ≠ v})).mpr
        (((G.induce {x : V | x ≠ v}).mem_neighborFinset u w.1).mp w.2)⟩
  let used := insert (cv' u) (adjColors ∪ forb)
  have hadj : adjColors.card ≤ (G.induce {x : V | x ≠ v}).degree u := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact Finset.card_image_le.trans (by simp)
  have hdeg : (G.induce {x : V | x ≠ v}).degree u + 1 ≤ d :=
    (induce_compl_degree_lt G v u hvu).trans ((G.degree_le_maxDegree u.1).trans hΔ)
  have hused : used.card < Fintype.card (Fin (d + 2)) := by
    have h1 : used.card ≤ (adjColors ∪ forb).card + 1 := Finset.card_insert_le _ _
    have h2 := Finset.card_union_le adjColors forb
    rw [Fintype.card_fin]
    omega
  have hne : (Finset.univ \ used).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
    omega
  obtain ⟨c, hc⟩ := hne
  rw [Finset.mem_sdiff] at hc
  have hnu : c ∉ used := hc.2
  refine ⟨c, ?_, ?_, ?_⟩
  · intro heq
    exact hnu (heq ▸ Finset.mem_insert_self _ _)
  · intro hcf
    exact hnu (Finset.mem_insert_of_mem (Finset.mem_union_right _ hcf))
  · intro e' hue' heq
    obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.mp hue'
    have huw : (G.induce {x : V | x ≠ v}).Adj u w := by
      have hm := e'.2
      rw [hw, SimpleGraph.mem_edgeSet] at hm
      exact hm
    have hwmem : w ∈ (G.induce {x : V | x ≠ v}).neighborFinset u :=
      ((G.induce {x : V | x ≠ v}).mem_neighborFinset u w).mpr huw
    have hcmem : c ∈ adjColors := by
      rw [heq]
      refine Finset.mem_image.mpr ⟨⟨w, hwmem⟩, Finset.mem_attach _ _, ?_⟩
      congr 1
      exact Subtype.ext hw.symm
    exact hnu (Finset.mem_insert_of_mem (Finset.mem_union_left _ hcmem))

private lemma extend_vertex_deg_le_two {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hd3 : 3 ≤ d) (hΔ : G.maxDegree ≤ d) (v : V) (hdeg : G.degree v ≤ 2)
    [Fintype {x : V | x ≠ v}] [DecidableRel (G.induce {x : V | x ≠ v}).Adj]
    (hsub : ∃ (cv' : {x : V | x ≠ v} → Fin (d + 2))
      (ce' : (G.induce {x : V | x ≠ v}).edgeSet → Fin (d + 2)),
      IsTotalColoring (G.induce {x : V | x ≠ v}) cv' ce') :
    ∃ (cv : V → Fin (d + 2)) (ce : G.edgeSet → Fin (d + 2)), IsTotalColoring G cv ce := by
  classical
  obtain ⟨cv', ce', h1', h2', h3'⟩ := hsub
  let G' := G.induce {x : V | x ≠ v}
  have hnb : (G.neighborFinset v).card ≤ 2 := by
    rwa [SimpleGraph.card_neighborFinset_eq_degree]
  have hcard_split : (G.neighborFinset v).card = 0 ∨
      (G.neighborFinset v).card = 1 ∨ (G.neighborFinset v).card = 2 := by omega
  rcases hcard_split with h0 | h1c | h2c
  · -- Degree 0: `v` is isolated
    rw [Finset.card_eq_zero] at h0
    have hno : ∀ w, ¬ G.Adj v w := fun w hvw => by
      have : w ∈ G.neighborFinset v := (G.mem_neighborFinset v w).mpr hvw
      rw [h0] at this
      exact Finset.notMem_empty w this
    have hne_edge : ∀ (e : G.edgeSet), ∀ x ∈ (e : Sym2 V), x ≠ v := by
      rintro ⟨z, hz⟩ x hx rfl
      obtain ⟨y, hy⟩ := Sym2.mem_iff_exists.mp hx
      change z = s(x, y) at hy
      rw [hy, SimpleGraph.mem_edgeSet] at hz
      exact hno y hz
    let cv : V → Fin (d + 2) := fun x => if hx : x = v then 0 else cv' ⟨x, hx⟩
    let ce : G.edgeSet → Fin (d + 2) := fun e =>
      ce' (Classical.choose (exists_edge_induce {x | x ≠ v} e (hne_edge e)))
    refine ⟨cv, ce, ?_, ?_, ?_⟩
    · intro x y hxy
      have hxv : x ≠ v := fun h => hno y (h ▸ hxy)
      have hyv : y ≠ v := fun h => hno x (h ▸ hxy.symm)
      simp only [cv, dif_neg hxv, dif_neg hyv]
      exact h1' ⟨x, hxv⟩ ⟨y, hyv⟩ hxy
    · rintro e f hef ⟨x, hxe, hxf⟩
      have hxv : x ≠ v := hne_edge e x hxe
      let e' := Classical.choose (exists_edge_induce {x | x ≠ v} e (hne_edge e))
      let f' := Classical.choose (exists_edge_induce {x | x ≠ v} f (hne_edge f))
      have he' : Sym2.map Subtype.val e'.1 = e.1 :=
        Classical.choose_spec (exists_edge_induce {x | x ≠ v} e (hne_edge e))
      have hf' : Sym2.map Subtype.val f'.1 = f.1 :=
        Classical.choose_spec (exists_edge_induce {x | x ≠ v} f (hne_edge f))
      refine h2' e' f' (fun heq => hef (induce_edge_inj he' hf' heq)) ?_
      exact ⟨⟨x, hxv⟩, (induce_edge_mem_iff he' ⟨x, hxv⟩).mpr hxe,
        (induce_edge_mem_iff hf' ⟨x, hxv⟩).mpr hxf⟩
    · intro e x hxe
      have hxv : x ≠ v := hne_edge e x hxe
      simp only [cv, dif_neg hxv]
      let e' := Classical.choose (exists_edge_induce {x | x ≠ v} e (hne_edge e))
      have he' : Sym2.map Subtype.val e'.1 = e.1 :=
        Classical.choose_spec (exists_edge_induce {x | x ≠ v} e (hne_edge e))
      exact h3' e' ⟨x, hxv⟩ ((induce_edge_mem_iff he' ⟨x, hxv⟩).mpr hxe)
  · -- Degree 1: `v` has a single neighbour `u`
    obtain ⟨u, hu_eq⟩ := Finset.card_eq_one.mp h1c
    have hvu : G.Adj v u := (G.mem_neighborFinset v u).mp (hu_eq ▸ Finset.mem_singleton_self u)
    have huv : u ≠ v := G.ne_of_adj hvu.symm
    have honly : ∀ y, G.Adj v y → y = u := fun y hvy => by
      have : y ∈ G.neighborFinset v := (G.mem_neighborFinset v y).mpr hvy
      rw [hu_eq, Finset.mem_singleton] at this
      exact this
    obtain ⟨c1, hc1_u, _, hc1_edges⟩ :=
      choose_edge_color G hΔ v cv' ce' ⟨u, huv⟩ hvu ∅ (by simp)
    have hv_avail : (Finset.univ \ ({cv' ⟨u, huv⟩, c1} : Finset (Fin (d + 2)))).Nonempty := by
      rw [← Finset.card_pos, Finset.card_sdiff]
      have hle : ({cv' ⟨u, huv⟩, c1} : Finset (Fin (d + 2))).card ≤ 2 :=
        (Finset.card_insert_le _ _).trans (by simp)
      simp only [Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨cv0, hcv0⟩ := hv_avail
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hcv0
    have hcv0_u : cv0 ≠ cv' ⟨u, huv⟩ := hcv0.2.1
    have hcv0_c1 : cv0 ≠ c1 := hcv0.2.2
    have hnotv_of_ne : ∀ (e : G.edgeSet), e.1 ≠ s(v, u) → ∀ x ∈ (e : Sym2 V), x ≠ v := by
      rintro ⟨z, hz⟩ hne x hx rfl
      obtain ⟨y, hy⟩ := Sym2.mem_iff_exists.mp hx
      change z = s(x, y) at hy
      have hadj : G.Adj x y := by rw [hy, SimpleGraph.mem_edgeSet] at hz; exact hz
      exact hne (hy.trans (congrArg (s(x, ·)) (honly y hadj)))
    let cv : V → Fin (d + 2) := fun x => if hx : x = v then cv0 else cv' ⟨x, hx⟩
    let ce : G.edgeSet → Fin (d + 2) := fun e =>
      if h : e.1 = s(v, u) then c1
      else ce' (Classical.choose (exists_edge_induce {x | x ≠ v} e (hnotv_of_ne e h)))
    refine ⟨cv, ce, ?_, ?_, ?_⟩
    · intro x y hxy
      by_cases hxv : x = v
      · subst x
        have hyu : y = u := honly y hxy
        subst y
        simp only [cv, dif_pos rfl, dif_neg huv]
        exact hcv0_u
      · by_cases hyv : y = v
        · subst y
          have hxu : x = u := honly x hxy.symm
          subst x
          simp only [cv, dif_pos rfl, dif_neg huv]
          exact hcv0_u.symm
        · simp only [cv, dif_neg hxv, dif_neg hyv]
          exact h1' ⟨x, hxv⟩ ⟨y, hyv⟩ hxy
    · rintro e f hef ⟨x, hxe, hxf⟩
      by_cases he : e.1 = s(v, u)
      · have hf : f.1 ≠ s(v, u) := fun h => hef (Subtype.ext (he.trans h.symm))
        simp only [ce, dif_pos he, dif_neg hf]
        have hxv : x ≠ v := hnotv_of_ne f hf x hxf
        have hxu : x = u := by
          rw [he, Sym2.mem_iff] at hxe
          exact hxe.resolve_left hxv
        subst x
        let f' := Classical.choose (exists_edge_induce {x | x ≠ v} f (hnotv_of_ne f hf))
        have hf' : Sym2.map Subtype.val f'.1 = f.1 :=
          Classical.choose_spec (exists_edge_induce {x | x ≠ v} f (hnotv_of_ne f hf))
        exact hc1_edges f' ((induce_edge_mem_iff hf' ⟨u, huv⟩).mpr hxf)
      · by_cases hf : f.1 = s(v, u)
        · simp only [ce, dif_neg he, dif_pos hf]
          have hxv : x ≠ v := hnotv_of_ne e he x hxe
          have hxu : x = u := by
            rw [hf, Sym2.mem_iff] at hxf
            exact hxf.resolve_left hxv
          subst x
          let e' := Classical.choose (exists_edge_induce {x | x ≠ v} e (hnotv_of_ne e he))
          have he' : Sym2.map Subtype.val e'.1 = e.1 :=
            Classical.choose_spec (exists_edge_induce {x | x ≠ v} e (hnotv_of_ne e he))
          exact (hc1_edges e' ((induce_edge_mem_iff he' ⟨u, huv⟩).mpr hxe)).symm
        · simp only [ce, dif_neg he, dif_neg hf]
          have hxv : x ≠ v := hnotv_of_ne e he x hxe
          let e' := Classical.choose (exists_edge_induce {x | x ≠ v} e (hnotv_of_ne e he))
          let f' := Classical.choose (exists_edge_induce {x | x ≠ v} f (hnotv_of_ne f hf))
          have he' : Sym2.map Subtype.val e'.1 = e.1 :=
            Classical.choose_spec (exists_edge_induce {x | x ≠ v} e (hnotv_of_ne e he))
          have hf' : Sym2.map Subtype.val f'.1 = f.1 :=
            Classical.choose_spec (exists_edge_induce {x | x ≠ v} f (hnotv_of_ne f hf))
          refine h2' e' f' (fun heq => hef (induce_edge_inj he' hf' heq)) ?_
          exact ⟨⟨x, hxv⟩, (induce_edge_mem_iff he' ⟨x, hxv⟩).mpr hxe,
            (induce_edge_mem_iff hf' ⟨x, hxv⟩).mpr hxf⟩
    · intro e x hxe
      by_cases he : e.1 = s(v, u)
      · simp only [ce, dif_pos he]
        rw [he, Sym2.mem_iff] at hxe
        rcases hxe with rfl | rfl
        · simp only [cv, dif_pos rfl]
          exact hcv0_c1.symm
        · simp only [cv, dif_neg huv]
          exact hc1_u
      · have hxv : x ≠ v := hnotv_of_ne e he x hxe
        simp only [ce, cv, dif_neg he, dif_neg hxv]
        let e' := Classical.choose (exists_edge_induce {x | x ≠ v} e (hnotv_of_ne e he))
        have he' : Sym2.map Subtype.val e'.1 = e.1 :=
          Classical.choose_spec (exists_edge_induce {x | x ≠ v} e (hnotv_of_ne e he))
        exact h3' e' ⟨x, hxv⟩ ((induce_edge_mem_iff he' ⟨x, hxv⟩).mpr hxe)
  · -- Degree 2: `v` has two distinct neighbours `u` and `w`
    obtain ⟨u, w, huw, huw_eq⟩ := Finset.card_eq_two.mp h2c
    have hvu : G.Adj v u :=
      (G.mem_neighborFinset v u).mp (huw_eq ▸ Finset.mem_insert_self u {w})
    have hvw : G.Adj v w :=
      (G.mem_neighborFinset v w).mp (huw_eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self w))
    have huv : u ≠ v := G.ne_of_adj hvu.symm
    have hwv : w ≠ v := G.ne_of_adj hvw.symm
    have honly : ∀ y, G.Adj v y → y = u ∨ y = w := fun y hvy => by
      have : y ∈ G.neighborFinset v := (G.mem_neighborFinset v y).mpr hvy
      rw [huw_eq, Finset.mem_insert, Finset.mem_singleton] at this
      exact this
    obtain ⟨c1, hc1_u, _, hc1_edges⟩ :=
      choose_edge_color G hΔ v cv' ce' ⟨u, huv⟩ hvu ∅ (by simp)
    obtain ⟨c2, hc2_w, hc2_ne, hc2_edges⟩ :=
      choose_edge_color G hΔ v cv' ce' ⟨w, hwv⟩ hvw {c1} (by simp)
    have hc12 : c1 ≠ c2 := fun h => hc2_ne (Finset.mem_singleton.mpr h.symm)
    let forbV : Finset (Fin (d + 2)) := {cv' ⟨u, huv⟩, cv' ⟨w, hwv⟩, c1, c2}
    have hv_avail : (Finset.univ \ forbV).Nonempty := by
      rw [← Finset.card_pos, Finset.card_sdiff]
      have hf1 : forbV.card ≤ ({cv' ⟨w, hwv⟩, c1, c2} : Finset (Fin (d + 2))).card + 1 :=
        Finset.card_insert_le _ _
      have hf2 := Finset.card_insert_le (cv' ⟨w, hwv⟩) {c1, c2}
      have hf3 := Finset.card_insert_le c1 ({c2} : Finset (Fin (d + 2)))
      have hf4 : ({c2} : Finset (Fin (d + 2))).card = 1 := Finset.card_singleton c2
      simp only [Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨cv0, hcv0⟩ := hv_avail
    rw [Finset.mem_sdiff] at hcv0
    have hcv0_nf : cv0 ∉ forbV := hcv0.2
    have hcv0_u : cv0 ≠ cv' ⟨u, huv⟩ := fun h => hcv0_nf (h ▸ Finset.mem_insert_self _ _)
    have hcv0_w : cv0 ≠ cv' ⟨w, hwv⟩ :=
      fun h => hcv0_nf (Finset.mem_insert_of_mem (h ▸ Finset.mem_insert_self _ _))
    have hcv0_c1 : cv0 ≠ c1 := fun h =>
      hcv0_nf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (h ▸ Finset.mem_insert_self _ _)))
    have hcv0_c2 : cv0 ≠ c2 := fun h =>
      hcv0_nf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (h ▸ Finset.mem_singleton_self _))))
    have hnotv_of_ne : ∀ (e : G.edgeSet), e.1 ≠ s(v, u) → e.1 ≠ s(v, w) →
        ∀ x ∈ (e : Sym2 V), x ≠ v := by
      rintro ⟨z, hz⟩ hne1 hne2 x hx rfl
      obtain ⟨y, hy⟩ := Sym2.mem_iff_exists.mp hx
      change z = s(x, y) at hy
      have hadj : G.Adj x y := by rw [hy, SimpleGraph.mem_edgeSet] at hz; exact hz
      rcases honly y hadj with rfl | rfl
      · exact hne1 hy
      · exact hne2 hy
    have heuw : s(v, u) ≠ s(v, w) := fun h => huw (Sym2.congr_right.mp h)
    let cv : V → Fin (d + 2) := fun x => if hx : x = v then cv0 else cv' ⟨x, hx⟩
    let ce : G.edgeSet → Fin (d + 2) := fun e =>
      if h1 : e.1 = s(v, u) then c1
      else if h2 : e.1 = s(v, w) then c2
      else ce' (Classical.choose (exists_edge_induce {x | x ≠ v} e (hnotv_of_ne e h1 h2)))
    refine ⟨cv, ce, ?_, ?_, ?_⟩
    · intro x y hxy
      by_cases hxv : x = v
      · subst x
        rcases honly y hxy with rfl | rfl
        · simp only [cv, dif_pos rfl, dif_neg huv]; exact hcv0_u
        · simp only [cv, dif_pos rfl, dif_neg hwv]; exact hcv0_w
      · by_cases hyv : y = v
        · subst y
          rcases honly x hxy.symm with rfl | rfl
          · simp only [cv, dif_pos rfl, dif_neg huv]; exact hcv0_u.symm
          · simp only [cv, dif_pos rfl, dif_neg hwv]; exact hcv0_w.symm
        · simp only [cv, dif_neg hxv, dif_neg hyv]
          exact h1' ⟨x, hxv⟩ ⟨y, hyv⟩ hxy
    · rintro e f hef ⟨x, hxe, hxf⟩
      by_cases he1 : e.1 = s(v, u)
      · have hf1 : f.1 ≠ s(v, u) := fun h => hef (Subtype.ext (he1.trans h.symm))
        by_cases hf2 : f.1 = s(v, w)
        · simp only [ce, dif_pos he1, dif_neg hf1, dif_pos hf2]
          exact hc12
        · simp only [ce, dif_pos he1, dif_neg hf1, dif_neg hf2]
          have hxv : x ≠ v := hnotv_of_ne f hf1 hf2 x hxf
          have hxu : x = u := by
            rw [he1, Sym2.mem_iff] at hxe
            exact hxe.resolve_left hxv
          subst x
          let f' := Classical.choose (exists_edge_induce {x | x ≠ v} f (hnotv_of_ne f hf1 hf2))
          have hf' : Sym2.map Subtype.val f'.1 = f.1 :=
            Classical.choose_spec (exists_edge_induce {x | x ≠ v} f (hnotv_of_ne f hf1 hf2))
          exact hc1_edges f' ((induce_edge_mem_iff hf' ⟨u, huv⟩).mpr hxf)
      · by_cases he2 : e.1 = s(v, w)
        · have hf2 : f.1 ≠ s(v, w) := fun h => hef (Subtype.ext (he2.trans h.symm))
          by_cases hf1 : f.1 = s(v, u)
          · simp only [ce, dif_neg he1, dif_pos he2, dif_pos hf1]
            exact hc12.symm
          · simp only [ce, dif_neg he1, dif_pos he2, dif_neg hf1, dif_neg hf2]
            have hxv : x ≠ v := hnotv_of_ne f hf1 hf2 x hxf
            have hxw : x = w := by
              rw [he2, Sym2.mem_iff] at hxe
              exact hxe.resolve_left hxv
            subst x
            let f' := Classical.choose (exists_edge_induce {x | x ≠ v} f (hnotv_of_ne f hf1 hf2))
            have hf' : Sym2.map Subtype.val f'.1 = f.1 :=
              Classical.choose_spec (exists_edge_induce {x | x ≠ v} f (hnotv_of_ne f hf1 hf2))
            exact hc2_edges f' ((induce_edge_mem_iff hf' ⟨w, hwv⟩).mpr hxf)
        · by_cases hf1 : f.1 = s(v, u)
          · simp only [ce, dif_neg he1, dif_neg he2, dif_pos hf1]
            have hxv : x ≠ v := hnotv_of_ne e he1 he2 x hxe
            have hxu : x = u := by
              rw [hf1, Sym2.mem_iff] at hxf
              exact hxf.resolve_left hxv
            subst x
            let e' := Classical.choose (exists_edge_induce {x | x ≠ v} e (hnotv_of_ne e he1 he2))
            have he' : Sym2.map Subtype.val e'.1 = e.1 :=
              Classical.choose_spec (exists_edge_induce {x | x ≠ v} e (hnotv_of_ne e he1 he2))
            exact (hc1_edges e' ((induce_edge_mem_iff he' ⟨u, huv⟩).mpr hxe)).symm
          · by_cases hf2 : f.1 = s(v, w)
            · simp only [ce, dif_neg he1, dif_neg he2, dif_neg hf1, dif_pos hf2]
              have hxv : x ≠ v := hnotv_of_ne e he1 he2 x hxe
              have hxw : x = w := by
                rw [hf2, Sym2.mem_iff] at hxf
                exact hxf.resolve_left hxv
              subst x
              let e' := Classical.choose (exists_edge_induce {x | x ≠ v} e (hnotv_of_ne e he1 he2))
              have he' : Sym2.map Subtype.val e'.1 = e.1 :=
                Classical.choose_spec (exists_edge_induce {x | x ≠ v} e (hnotv_of_ne e he1 he2))
              exact (hc2_edges e' ((induce_edge_mem_iff he' ⟨w, hwv⟩).mpr hxe)).symm
            · simp only [ce, dif_neg he1, dif_neg he2, dif_neg hf1, dif_neg hf2]
              have hxv : x ≠ v := hnotv_of_ne e he1 he2 x hxe
              let e' := Classical.choose (exists_edge_induce {x | x ≠ v} e (hnotv_of_ne e he1 he2))
              let f' := Classical.choose (exists_edge_induce {x | x ≠ v} f (hnotv_of_ne f hf1 hf2))
              have he' : Sym2.map Subtype.val e'.1 = e.1 :=
                Classical.choose_spec (exists_edge_induce {x | x ≠ v} e (hnotv_of_ne e he1 he2))
              have hf' : Sym2.map Subtype.val f'.1 = f.1 :=
                Classical.choose_spec (exists_edge_induce {x | x ≠ v} f (hnotv_of_ne f hf1 hf2))
              refine h2' e' f' (fun heq => hef (induce_edge_inj he' hf' heq)) ?_
              exact ⟨⟨x, hxv⟩, (induce_edge_mem_iff he' ⟨x, hxv⟩).mpr hxe,
                (induce_edge_mem_iff hf' ⟨x, hxv⟩).mpr hxf⟩
    · intro e x hxe
      by_cases he1 : e.1 = s(v, u)
      · simp only [ce, dif_pos he1]
        rw [he1, Sym2.mem_iff] at hxe
        rcases hxe with rfl | rfl
        · simp only [cv, dif_pos rfl]; exact hcv0_c1.symm
        · simp only [cv, dif_neg huv]; exact hc1_u
      · by_cases he2 : e.1 = s(v, w)
        · simp only [ce, dif_neg he1, dif_pos he2]
          rw [he2, Sym2.mem_iff] at hxe
          rcases hxe with rfl | rfl
          · simp only [cv, dif_pos rfl]; exact hcv0_c2.symm
          · simp only [cv, dif_neg hwv]; exact hc2_w
        · have hxv : x ≠ v := hnotv_of_ne e he1 he2 x hxe
          simp only [ce, cv, dif_neg he1, dif_neg he2, dif_neg hxv]
          let e' := Classical.choose (exists_edge_induce {x | x ≠ v} e (hnotv_of_ne e he1 he2))
          have he' : Sym2.map Subtype.val e'.1 = e.1 :=
            Classical.choose_spec (exists_edge_induce {x | x ≠ v} e (hnotv_of_ne e he1 he2))
          exact h3' e' ⟨x, hxv⟩ ((induce_edge_mem_iff he' ⟨x, hxv⟩).mpr hxe)

private lemma total_color_of_maxDegree_le
    (h1 : H1) (h2 : H2) (h3 : H3)
    (d : ℕ) (hd3 : 3 ≤ d) (hd5 : d ≤ 5) :
    ∀ (n : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = n → G.maxDegree ≤ d →
        ∃ (cv : V → Fin (d + 2)) (ce : G.edgeSet → Fin (d + 2)),
          IsTotalColoring G cv ce := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ G _ hn hΔ
    classical
    by_cases hle2 : G.maxDegree ≤ 2
    · exact cast_coloring (by omega)
        (OMA.R_opg_behzads_conjecture_R2.coloring_four_of_maxDegree_le_two G hle2)
    · have hneV : Nonempty V := by
        by_contra! hempty
        have := hempty
        have hsub : G.maxDegree = 0 := SimpleGraph.maxDegree_of_subsingleton G
        omega
      by_cases hconn : G.Connected
      · by_cases hlow : ∃ v : V, G.degree v ≤ 2
        · obtain ⟨v, hv⟩ := hlow
          let S : Set V := {x : V | x ≠ v}
          have hcardS : Fintype.card S < n := by
            rw [← hn, Fintype.card_subtype]
            refine Finset.card_lt_card ?_
            rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
            exact ⟨v, Finset.mem_univ v, by simp [S]⟩
          have hΔS : (G.induce S).maxDegree ≤ d :=
            (induce_maxDegree_le G S).trans hΔ
          exact extend_vertex_deg_le_two G hd3 hΔ v hv
            (ih (Fintype.card S) hcardS S (G.induce S) rfl hΔS)
        · have hge3 : ∀ v : V, 3 ≤ G.degree v := by
            intro v
            by_contra! hlt
            exact hlow ⟨v, by omega⟩
          let e : V ≃ Fin n := (Fintype.equivFin V).trans (finCongr hn)
          let G₀ : SimpleGraph (Fin n) := G.comap e.symm
          let φ : G₀ ≃g G := SimpleGraph.Iso.comap e.symm G
          have hconn₀ : G₀.Connected := (φ.connected_iff).mpr hconn
          have : Nonempty (Fin n) := hconn₀.nonempty
          have hmin₀ : 3 ≤ G₀.minDegree := by
            refine G₀.le_minDegree_of_forall_le_degree 3 fun i => ?_
            rw [iso_degree_eq φ i]
            exact hge3 (φ i)
          have hΔ₀ : G₀.maxDegree = G.maxDegree := iso_maxDegree_eq φ
          have hΔ_lo : 3 ≤ G₀.maxDegree := by omega
          have hΔ_hi : G₀.maxDegree ≤ d := by omega
          have hΔ_five : G₀.maxDegree ≤ 5 := by omega
          interval_cases hΔval : G₀.maxDegree
          · have hreg : G₀.IsRegularOfDegree 3 := by
              intro i
              have hi_lo : 3 ≤ G₀.degree i := hmin₀.trans (G₀.minDegree_le_degree i)
              have hi_hi : G₀.degree i ≤ 3 := (G₀.degree_le_maxDegree i).trans_eq hΔval
              omega
            exact iso_pullback_coloring φ.symm
              (cast_coloring (by omega : 5 ≤ d + 2) (h1 n G₀ hconn₀ hreg))
          · exact iso_pullback_coloring φ.symm
              (cast_coloring (by omega : 6 ≤ d + 2) (h2 n G₀ hconn₀ hmin₀ hΔval))
          · exact iso_pullback_coloring φ.symm
              (cast_coloring (by omega : 7 ≤ d + 2) (h3 n G₀ hconn₀ hmin₀ hΔval))
      · have hnp : ¬ G.Preconnected := fun hp => hconn ⟨hp⟩
        simp only [SimpleGraph.Preconnected, not_forall] at hnp
        obtain ⟨v₀, v₁, hnr⟩ := hnp
        let P : V → Prop := fun x => G.Reachable v₀ x
        have hcut : ∀ u v, G.Adj u v → (P u ↔ P v) := by
          intro u v huv
          exact ⟨fun h => h.trans huv.reachable, fun h => h.trans huv.symm.reachable⟩
        have hcardP : Fintype.card {x : V | P x} < n := by
          rw [← hn, Fintype.card_subtype]
          refine Finset.card_lt_card ?_
          rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
          exact ⟨v₁, Finset.mem_univ v₁, by simp [P, hnr]⟩
        have hcardNP : Fintype.card {x : V | ¬ P x} < n := by
          rw [← hn, Fintype.card_subtype]
          refine Finset.card_lt_card ?_
          rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
          exact ⟨v₀, Finset.mem_univ v₀, by simp [P]⟩
        have hΔP : (G.induce {x : V | P x}).maxDegree ≤ d :=
          (induce_maxDegree_le G {x : V | P x}).trans hΔ
        have hΔNP : (G.induce {x : V | ¬ P x}).maxDegree ≤ d :=
          (induce_maxDegree_le G {x : V | ¬ P x}).trans hΔ
        exact glue_disjoint_cut P hcut
          (ih (Fintype.card {x : V | P x}) hcardP {x : V | P x} (G.induce {x : V | P x}) rfl hΔP)
          (ih (Fintype.card {x : V | ¬ P x}) hcardNP {x : V | ¬ P x}
            (G.induce {x : V | ¬ P x}) rfl hΔNP)

end Helpers

theorem main : H1 → H2 → H3 → OMA.R_opg_behzads_conjecture_R2.H1 := by
  intro h1 h2 h3 V _ G _ h3le hle5
  exact total_color_of_maxDegree_le h1 h2 h3 G.maxDegree h3le hle5 (Fintype.card V) V G rfl le_rfl

end OMA.R_opg_behzads_conjecture_R2_H1_R1
