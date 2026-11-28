import OMAReductions.R_opg_intersecting_two_perfect_matchings_R1
import Mathlib.Combinatorics.SimpleGraph.Tutte

open scoped BigOperators
open Finset SimpleGraph

namespace OMA.CubicMatching

variable {V : Type}

private noncomputable def arcs (G : SimpleGraph V) (s t : Finset V) : Finset (V × V) := by
  classical
  exact (s ×ˢ t).filter (fun e => G.Adj e.1 e.2)

private theorem mem_arcs {G : SimpleGraph V} {s t : Finset V} {e : V × V} :
    e ∈ arcs G s t ↔ e.1 ∈ s ∧ e.2 ∈ t ∧ G.Adj e.1 e.2 := by
  classical
  simp [arcs, and_assoc]

variable [Fintype V] [DecidableEq V]

private theorem card_arcs_out (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsRegularOfDegree 3) (s : Finset V) :
    (arcs G s univ).card = 3 * s.card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := s)
    (fun e he => (mem_arcs.mp he).1)]
  calc
    _ = ∑ _u ∈ s, (3 : ℕ) := by
      apply Finset.sum_congr rfl
      intro u hu
      have hfilter : ((arcs G s univ).filter fun e => e.1 = u) =
          (G.neighborFinset u).image (fun v => (u,v)) := by
        ext e
        rcases e with ⟨x,y⟩
        simp only [Finset.mem_filter, mem_arcs, Finset.mem_univ, true_and, Finset.mem_image,
          SimpleGraph.mem_neighborFinset, Prod.mk.injEq]
        constructor
        · rintro ⟨⟨_,hxy⟩,rfl⟩
          exact ⟨y,hxy,rfl,rfl⟩
        · rintro ⟨w,huw,rfl,rfl⟩
          exact ⟨⟨hu,huw⟩,rfl⟩
      rw [hfilter, Finset.card_image_of_injective _ (fun _ _ hxy => congrArg Prod.snd hxy),
        SimpleGraph.card_neighborFinset_eq_degree, h u]
    _ = _ := by simp [Nat.mul_comm]

private theorem arcs_card_swap (G : SimpleGraph V) (s t : Finset V) :
    (arcs G s t).card = (arcs G t s).card := by
  apply Finset.card_bijective Prod.swap (Equiv.prodComm V V).bijective
  rintro ⟨u,v⟩
  simp only [mem_arcs, Prod.swap_prod_mk]
  rw [G.adj_comm v u]
  tauto

private theorem inside_even (G : SimpleGraph V) (s : Finset V) :
    Even (arcs G s s).card := by
  classical
  let label := Fintype.equivFin V
  let up := (arcs G s s).filter fun e => label e.1 < label e.2
  let down := (arcs G s s).filter fun e => ¬ label e.1 < label e.2
  have hsum : up.card + down.card = (arcs G s s).card :=
    Finset.card_filter_add_card_filter_not _
  have he : up.card = down.card := by
    apply Finset.card_bijective Prod.swap (Equiv.prodComm V V).bijective
    rintro ⟨u,v⟩
    simp only [up, down, Finset.mem_filter, mem_arcs, Prod.swap_prod_mk]
    constructor
    · rintro ⟨⟨hu,hv,ha⟩,hlabel⟩
      exact ⟨⟨hv,hu,ha.symm⟩,not_lt_of_ge hlabel.le⟩
    · rintro ⟨⟨hv,hu,ha⟩,hlabel⟩
      refine ⟨⟨hu,hv,ha.symm⟩,lt_of_le_of_ne (le_of_not_gt hlabel) ?_⟩
      exact fun h => ha.ne (label.injective h).symm
  exact ⟨up.card, by omega⟩

private theorem arcs_split (G : SimpleGraph V) (s : Finset V) :
    (arcs G s s).card + (arcs G s sᶜ).card = (arcs G s univ).card := by
  classical
  have h (t : Finset V) :
      ((arcs G s univ).filter fun e => e.2 ∈ t) = arcs G s t := by
    ext e
    simp only [Finset.mem_filter, mem_arcs, Finset.mem_univ, true_and]
    tauto
  have hf := (arcs G s univ).card_filter_add_card_filter_not (fun e => e.2 ∈ s)
  simpa only [← h s, ← h sᶜ, Finset.mem_compl] using hf

omit [Fintype V] [DecidableEq V] in
private theorem walk_closed {G : SimpleGraph V} {s : Finset V}
    (h : ∀ a b, G.Adj a b → a ∈ s → b ∈ s)
    {a b : V} (w : G.Walk a b) (ha : a ∈ s) : b ∈ s := by
  induction w with
  | nil => exact ha
  | cons hab _ ih => exact ih (h _ _ hab ha)

private theorem cut_ne_one (G : SimpleGraph V)
    (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) (s : Finset V) :
    (arcs G s sᶜ).card ≠ 1 := by
  classical
  intro h
  obtain ⟨⟨a,b⟩,ha⟩ := Finset.card_eq_one.mp h
  have he : (a,b) ∈ arcs G s sᶜ := by simp [ha]
  obtain ⟨a_in,b_not,hab⟩ := mem_arcs.mp he
  have hclosed u v (huv : (G.deleteEdges {s(a,b)}).Adj u v) (hu : u ∈ s) : v ∈ s := by
    by_contra hv
    obtain ⟨hadj,hedge⟩ := SimpleGraph.deleteEdges_adj.mp huv
    have hmem : (u,v) ∈ arcs G s sᶜ := mem_arcs.mpr
      ⟨hu, Finset.mem_compl.mpr hv, hadj⟩
    rw [ha, Finset.mem_singleton] at hmem
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj hmem
    exact hedge (Set.mem_singleton _)
  apply hb s(a,b) (G.mem_edgeSet.mpr hab)
  apply SimpleGraph.isBridge_iff.mpr
  rintro ⟨w⟩
  exact (Finset.mem_compl.mp b_not) (walk_closed hclosed w a_in)

private theorem cut_large (G : SimpleGraph V) [DecidableRel G.Adj]
    (hr : G.IsRegularOfDegree 3) (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e)
    (s : Finset V) (hs : Odd s.card) : 3 ≤ (arcs G s sᶜ).card := by
  have hh := arcs_split G s
  rw [card_arcs_out G hr] at hh
  obtain ⟨k,hk⟩ := hs
  obtain ⟨l,hl⟩ := inside_even G s
  have hn := cut_ne_one G hb s
  omega

private theorem odd_components_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (hr : G.IsRegularOfDegree 3) (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e)
    (U : Set V) :
    ((⊤ : G.Subgraph).deleteVerts U).coe.oddComponents.ncard ≤ U.ncard := by
  classical
  let H := (⊤ : G.Subgraph).deleteVerts U
  letI : Fintype H.verts := Fintype.ofFinite _
  letI : Fintype H.coe.ConnectedComponent := Fintype.ofFinite _
  let O := H.coe.oddComponents.toFinset
  let block (C : H.coe.ConnectedComponent) : Finset V := C.supp.toFinset.image Subtype.val
  let cut (C : H.coe.ConnectedComponent) := arcs G (block C) (block C)ᶜ
  have mem_block {C} {v : V} :
      v ∈ block C ↔ ∃ w : H.verts, w ∈ C.supp ∧ w.val = v := by
    simp [block]
  have outside (x : H.verts) : x.val ∉ U := by
    exact (show x.val ∈ Set.univ \ U from x.property).2
  have inside {v : V} (hv : v ∉ U) : v ∈ H.verts := by
    exact ⟨Set.mem_univ v,hv⟩
  have adj_in (x y : H.verts) (hxy : G.Adj x.val y.val) : H.coe.Adj x y := by
    change ((⊤ : G.Subgraph).deleteVerts U).Adj x.val y.val
    rw [Subgraph.deleteVerts_adj]
    simpa only [Subgraph.top_adj, Subgraph.verts_top, Set.mem_univ, true_and] using
      And.intro (outside x) (And.intro (outside y) hxy)
  have card_block (C : H.coe.ConnectedComponent) : (block C).card = C.supp.ncard := by
    change (C.supp.toFinset.image Subtype.val).card = C.supp.ncard
    rw [Finset.card_image_of_injective _ Subtype.val_injective, Set.ncard_eq_toFinset_card']
  have hmin (C : H.coe.ConnectedComponent) (hC : C ∈ O) : 3 ≤ (cut C).card := by
    apply cut_large G hr hb
    rw [card_block]
    have hm : C ∈ H.coe.oddComponents := Set.mem_toFinset.mp
      (show C ∈ H.coe.oddComponents.toFinset from hC)
    exact hm
  have hdis : (O : Set H.coe.ConnectedComponent).PairwiseDisjoint cut := by
    intro C _ D _ hCD
    refine Finset.disjoint_left.mpr ?_
    intro e hC hD
    obtain ⟨x,hx,he⟩ := mem_block.mp (mem_arcs.mp hC).1
    obtain ⟨y,hy,he'⟩ := mem_block.mp (mem_arcs.mp hD).1
    have hxy : x = y := Subtype.ext (he.trans he'.symm)
    subst y
    exact hCD (ConnectedComponent.eq_of_common_vertex hx hy)
  have hsub : O.biUnion cut ⊆ arcs G univ U.toFinset := by
    intro e he
    obtain ⟨C,_,hC⟩ := Finset.mem_biUnion.mp he
    obtain ⟨h1,h2,h3⟩ := mem_arcs.mp hC
    refine mem_arcs.mpr ⟨Finset.mem_univ _, Set.mem_toFinset.mpr ?_,h3⟩
    by_contra he2
    obtain ⟨x,hx,hxe⟩ := mem_block.mp h1
    let y : H.verts := ⟨e.2,inside he2⟩
    have hxy : H.coe.Adj x y := adj_in x y (by simpa only [hxe, y] using h3)
    have hyC := (C.mem_supp_congr_adj hxy).mp hx
    exact (Finset.mem_compl.mp h2) (mem_block.mpr ⟨y, hyC, rfl⟩)
  have hLo : 3 * O.card ≤ ∑ C ∈ O, (cut C).card := by
    simpa [Nat.mul_comm] using
      (Finset.sum_le_sum (s := O) (f := fun _ => (3 : ℕ)) (g := fun C => (cut C).card) hmin)
  have hHi : (∑ C ∈ O, (cut C).card) ≤ 3 * U.toFinset.card := calc
    _ = (O.biUnion cut).card := (Finset.card_biUnion hdis).symm
    _ ≤ (arcs G univ U.toFinset).card := Finset.card_le_card hsub
    _ = (arcs G U.toFinset univ).card := arcs_card_swap _ _ _
    _ = _ := card_arcs_out G hr _
  have ho : O.card = H.coe.oddComponents.ncard := (Set.ncard_eq_toFinset_card' _).symm
  have hu : U.toFinset.card = U.ncard := (Set.ncard_eq_toFinset_card' _).symm
  change H.coe.oddComponents.ncard ≤ U.ncard
  omega

end OMA.CubicMatching

open OMA.CubicMatching in
theorem OMA.solution : OMA.R_opg_intersecting_two_perfect_matchings_R1.H1 := by
  intro V _ G _ hr hb
  classical
  apply SimpleGraph.tutte.mpr
  intro U hU
  exact (not_lt_of_ge (odd_components_bound G hr hb U)) hU