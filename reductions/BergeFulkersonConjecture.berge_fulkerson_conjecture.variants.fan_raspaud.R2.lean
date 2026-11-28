import FormalConjectures.Wikipedia.BergeFulkersonConjecture

/-!
# Fan–Raspaud: reduction to snarks in which every two perfect matchings share three edges

Strong Petersen theorem (Schönberger): a bridgeless cubic graph has a perfect matching avoiding
any two prescribed edges (proved here from Tutte's theorem by counting odd cuts). Hence if two
perfect matchings share at most two edges, a third one avoiding the shared edges completes a
Fan–Raspaud triple (`of_two_pm`). This covers all 3-edge-colourable cubic graphs (`class_one`,
which needs no bridgelessness) and, for example, the Petersen graph, where any two distinct perfect
matchings share exactly one edge.

The remaining snarks (every two perfect matchings share at least three edges) are split by
oddness: `H1` oddness 2 (covered by Máčajová–Škoviera 2005), `H2` oddness at least 4 (open).
-/

open SimpleGraph BergeFulkersonConjecture
open scoped Classical

namespace OMA.R_BergeFulkersonConjecture_berge_fulkerson_conjecture_variants_fan_raspaud_R2

/-- Fan–Raspaud for oddness-2 snarks in which any two perfect matchings share at least three
edges. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    IsCubic G → G.IsBridgeless → ¬ G.lineGraph.Colorable 3 →
    (∀ M₁ M₂ : G.Subgraph, M₁.IsPerfectMatching → M₂.IsPerfectMatching →
      2 < (M₁.edgeSet ∩ M₂.edgeSet).ncard) →
    (∃ F : G.Subgraph, F.IsPerfectMatching ∧
      {c : (G.deleteEdges F.edgeSet).ConnectedComponent | Odd c.supp.ncard}.ncard ≤ 2) →
    ∃ M : Fin 3 → G.Subgraph, (∀ i, (M i).IsPerfectMatching) ∧
      ∀ e, ¬ (e ∈ (M 0).edgeSet ∧ e ∈ (M 1).edgeSet ∧ e ∈ (M 2).edgeSet)

/-- Fan–Raspaud for snarks of oddness at least 4 in which any two perfect matchings share at
least three edges. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    IsCubic G → G.IsBridgeless → ¬ G.lineGraph.Colorable 3 →
    (∀ M₁ M₂ : G.Subgraph, M₁.IsPerfectMatching → M₂.IsPerfectMatching →
      2 < (M₁.edgeSet ∩ M₂.edgeSet).ncard) →
    (∀ F : G.Subgraph, F.IsPerfectMatching →
      2 < {c : (G.deleteEdges F.edgeSet).ConnectedComponent | Odd c.supp.ncard}.ncard) →
    ∃ M : Fin 3 → G.Subgraph, (∀ i, (M i).IsPerfectMatching) ∧
      ∀ e, ¬ (e ∈ (M 0).edgeSet ∧ e ∈ (M 1).edgeSet ∧ e ∈ (M 2).edgeSet)

lemma edges_mem {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (p : V × V) :
    p ∈ ((A ×ˢ B).filter fun p => G.Adj p.1 p.2) ↔ p.1 ∈ A ∧ p.2 ∈ B ∧ G.Adj p.1 p.2 := by
  simp [Finset.mem_product, and_assoc]

lemma edges_count {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    (((A ×ˢ B).filter fun p => G.Adj p.1 p.2)).card = ∑ x ∈ A, (G.neighborFinset x ∩ B).card := by
  have hproj : (↑(((A ×ˢ B).filter fun p => G.Adj p.1 p.2)) : Set (V × V)).MapsTo Prod.fst ↑A :=
    fun p hp => ((edges_mem G A B p).mp hp).1
  rw [Finset.card_eq_sum_card_fiberwise hproj]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.card_nbij' Prod.snd (fun y => (x, y))
  · intro p hp
    obtain ⟨hmem, heq⟩ := Finset.mem_filter.mp hp
    obtain ⟨_, hb, hadj⟩ := (edges_mem G A B p).mp hmem
    exact Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset x p.2).mpr (heq ▸ hadj), hb⟩
  · intro y hy
    obtain ⟨hn, hb⟩ := Finset.mem_inter.mp hy
    exact Finset.mem_filter.mpr
      ⟨(edges_mem G A B (x, y)).mpr ⟨hx, hb, (G.mem_neighborFinset x y).mp hn⟩, rfl⟩
  · intro p hp
    exact Prod.ext ((Finset.mem_filter.mp hp).2.symm) rfl
  · intro y _
    rfl

lemma edges_swap {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) :
    (((A ×ˢ B).filter fun p => G.Adj p.1 p.2)).card = (((B ×ˢ A).filter fun p => G.Adj p.1 p.2)).card := by
  apply Finset.card_equiv (Equiv.prodComm V V)
  intro p
  rw [edges_mem, edges_mem]
  change (p.1 ∈ A ∧ p.2 ∈ B ∧ G.Adj p.1 p.2) ↔
      (p.2 ∈ B ∧ p.1 ∈ A ∧ G.Adj p.2 p.1)
  rw [G.adj_comm p.2 p.1]
  tauto

lemma cut_mem {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Set V) (p : V × V) :
    p ∈ (Finset.univ.filter fun p : V × V => p.1 ∈ A ∧ p.2 ∉ A ∧ G.Adj p.1 p.2) ↔ p.1 ∈ A ∧ p.2 ∉ A ∧ G.Adj p.1 p.2 := by
  simp

lemma cut_balance {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : IsCubic G)
    (A : Set V) :
    3 * A.ncard = 2 * (G.induce A).edgeFinset.card + ((Finset.univ.filter fun p : V × V => p.1 ∈ A ∧ p.2 ∉ A ∧ G.Adj p.1 p.2)).card := by
  let inside (v : V) := (G.neighborFinset v ∩ A.toFinset).card
  let outside (v : V) := (G.neighborFinset v ∩ Aᶜ.toFinset).card
  have hsplit (v : V) : inside v + outside v = G.degree v := by
    have hI : G.neighborFinset v ∩ A.toFinset = (G.neighborFinset v).filter (· ∈ A) := by
      ext w
      simp
    have hO : G.neighborFinset v ∩ Aᶜ.toFinset = (G.neighborFinset v).filter (· ∉ A) := by
      ext w
      simp
    dsimp [inside, outside]
    rw [hI, hO, Finset.card_filter_add_card_filter_not, G.card_neighborFinset_eq_degree]
  have hinside (v : A) : inside v = (G.induce A).degree v := by
    calc
      inside v = (((G.induce A).neighborFinset v).map
          (Function.Embedding.subtype (· ∈ A))).card :=
        congrArg Finset.card (G.map_neighborFinset_induce v).symm
      _ = _ := by rw [Finset.card_map, SimpleGraph.card_neighborFinset_eq_degree]
  have hInSum : (∑ v ∈ A.toFinset, inside v) = 2 * (G.induce A).edgeFinset.card := by
    rw [← Finset.sum_set_coe A]
    calc
      (∑ v : A, inside v) = ∑ v : A, (G.induce A).degree v :=
        Finset.sum_congr rfl (fun v _ => hinside v)
      _ = _ := (G.induce A).sum_degrees_eq_twice_card_edges
  calc
    3 * A.ncard = ∑ v ∈ A.toFinset, G.degree v := by
      rw [Set.ncard_eq_toFinset_card' A]
      simp [show ∀ v : V, G.degree v = 3 from hcubic, Nat.mul_comm]
    _ = ∑ v ∈ A.toFinset, (inside v + outside v) :=
      Finset.sum_congr rfl (fun v _ => (hsplit v).symm)
    _ = _ := by
      have hcutEq : (Finset.univ.filter fun p : V × V => p.1 ∈ A ∧ p.2 ∉ A ∧ G.Adj p.1 p.2) =
          ((A.toFinset ×ˢ Aᶜ.toFinset).filter fun p => G.Adj p.1 p.2) := by
        ext p
        simp [Finset.mem_product, and_assoc]
      rw [Finset.sum_add_distrib, hInSum, hcutEq, edges_count]

lemma cut_not_singleton {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hbridge : G.IsBridgeless) (A : Set V) :
    ((Finset.univ.filter fun p : V × V => p.1 ∈ A ∧ p.2 ∉ A ∧ G.Adj p.1 p.2)).card ≠ 1 := by
  intro hcard
  obtain ⟨⟨x, y⟩, hsingle⟩ := Finset.card_eq_one.mp hcard
  have hxy : (x, y) ∈ (Finset.univ.filter fun p : V × V => p.1 ∈ A ∧ p.2 ∉ A ∧ G.Adj p.1 p.2) := by rw [hsingle]; simp
  obtain ⟨hxA, hyA, ha⟩ := (cut_mem G A (x, y)).mp hxy
  apply hbridge s(x, y) (show s(x, y) ∈ G.edgeSet from ha)
  rw [SimpleGraph.isBridge_iff]
  intro hReach
  let D := G.deleteEdges ({s(x, y)} : Set (Sym2 V))
  have hclosed {a b : V} (hA : a ∈ A) (hab : D.Adj a b) : b ∈ A := by
    by_contra hB
    obtain ⟨habG, hne⟩ := SimpleGraph.deleteEdges_adj.mp hab
    have habCut := (cut_mem G A (a, b)).mpr ⟨hA, hB, habG⟩
    rw [hsingle] at habCut
    have heq : (a, b) = (x, y) := Finset.mem_singleton.mp habCut
    exact hne (by rw [(Prod.mk.inj heq).1, (Prod.mk.inj heq).2]; simp)
  have hwalk {a b : V} (p : D.Walk a b) : a ∈ A → b ∈ A := by
    induction p with
    | nil => exact id
    | cons hadj _ ih => exact fun ha => ih (hclosed ha hadj)
  obtain ⟨p⟩ := hReach
  exact hyA (hwalk p hxA)

lemma cut_min {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : IsCubic G)
    (hbridge : G.IsBridgeless) (A : Set V) (hOdd : Odd A.ncard) :
    3 ≤ ((Finset.univ.filter fun p : V × V => p.1 ∈ A ∧ p.2 ∉ A ∧ G.Adj p.1 p.2)).card := by
  obtain ⟨a, ha⟩ := hOdd
  have hbalance := cut_balance G hcubic A
  have hsingle := cut_not_singleton G hbridge A
  omega

/-- A cubic graph has an even number of vertices. -/
lemma even_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : IsCubic G) :
    Even (Fintype.card V) := by
  have h := G.sum_degrees_eq_twice_card_edges
  simp only [show ∀ v : V, G.degree v = 3 from hcubic, Finset.sum_const,
    Finset.card_univ, smul_eq_mul] at h
  rw [Nat.even_iff]
  omega

/-- Ordered pairs representing edges of a set `E0`: at most `2 * E0.ncard`. -/
lemma card_pairs_le {V : Type*} [Fintype V] [DecidableEq V] (E0 : Set (Sym2 V)) :
    ((Finset.univ : Finset (V × V)).filter fun p => s(p.1, p.2) ∈ E0).card ≤ 2 * E0.ncard := by
  let X := (Finset.univ : Finset (V × V)).filter fun p => s(p.1, p.2) ∈ E0
  have h1 := Finset.card_le_mul_card_image (f := fun p : V × V => s(p.1, p.2)) X 2 (by
    intro b hb
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hb
    have hsub : X.filter (fun a : V × V => s(a.1, a.2) = s(q.1, q.2)) ⊆ {q, q.swap} := by
      intro a ha
      have := (Finset.mem_filter.mp ha).2
      rw [Sym2.mk_eq_mk_iff] at this
      rcases this with h | h <;> simp [h]
    exact (Finset.card_le_card hsub).trans (Finset.card_le_two))
  have h2 : (X.image fun p : V × V => s(p.1, p.2)).card ≤ E0.ncard := by
    rw [Set.ncard_eq_toFinset_card']
    apply Finset.card_le_card
    intro b hb
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
    exact Set.mem_toFinset.mpr (Finset.mem_filter.mp hq).2
  exact h1.trans (Nat.mul_le_mul_left 2 h2)

set_option maxHeartbeats 1000000 in
/-- **Strong Petersen theorem (Schönberger).** A bridgeless cubic graph has a perfect matching
avoiding any two prescribed edges. -/
theorem avoid_two {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcubic : IsCubic G) (hbridge : G.IsBridgeless) (E0 : Set (Sym2 V))
    (hE0 : E0.ncard ≤ 2) :
    ∃ M : G.Subgraph, M.IsPerfectMatching ∧ ∀ e ∈ E0, e ∉ M.edgeSet := by
  let G' := G.deleteEdges E0
  have hPM : ∃ M : G'.Subgraph, M.IsPerfectMatching := by
    apply (SimpleGraph.tutte (G := G')).mpr
    intro U
    let D := (⊤ : G'.Subgraph).deleteVerts U
    let C := D.coe
    let part (c : C.ConnectedComponent) : Set V := Subtype.val '' c.supp
    let odd := C.oddComponents.toFinset
    let cutc (c : C.ConnectedComponent) := (Finset.univ.filter fun p : V × V => p.1 ∈ part c ∧ p.2 ∉ part c ∧ G.Adj p.1 p.2)
    let X := (Finset.univ : Finset (V × V)).filter
      fun p => s(p.1, p.2) ∈ E0
    have hOutside (x : V) : x ∈ D.verts ↔ x ∉ U := by simp [D]
    have hclosed (c : C.ConnectedComponent) {x y : V} (hx : x ∈ part c) (hy : y ∉ U)
        (hAdj : G'.Adj x y) : y ∈ part c := by
      have hxd : x ∈ D.verts := by
        obtain ⟨x', _, rfl⟩ := hx
        exact x'.property
      have hAdjD : D.Adj x y := Subgraph.deleteVerts_adj.mpr
        ⟨by simp, (hOutside x).mp hxd, by simp, hy, hAdj⟩
      exact ConnectedComponent.mem_coe_supp_of_adj hx ((hOutside y).mpr hy) hAdjD
    have hcut (c : C.ConnectedComponent) (hc : c ∈ odd) : 3 ≤ (cutc c).card := by
      have hOdd : Odd c.supp.ncard :=
        (Set.mem_toFinset (s := C.oddComponents) (a := c)).mp hc
      have hpartCard : (part c).ncard = c.supp.ncard :=
        Set.ncard_image_of_injective _ Subtype.val_injective
      have hOddPart : Odd (part c).ncard := by rwa [hpartCard]
      exact cut_min G hcubic hbridge (part c) hOddPart
    have hdisjoint : (odd : Set C.ConnectedComponent).PairwiseDisjoint cutc := by
      intro c _ c' _ hne
      apply Finset.disjoint_left.mpr
      intro p hp hp'
      have hx : p.1 ∈ part c := ((cut_mem G (part c) p).mp hp).1
      have hx' : p.1 ∈ part c' := ((cut_mem G (part c') p).mp hp').1
      obtain ⟨a, ha, heq⟩ := hx
      obtain ⟨b, hb, hbeq⟩ := hx'
      have hab : a = b := Subtype.val_injective (heq.trans hbeq.symm)
      subst b
      exact hne (ConnectedComponent.eq_of_common_vertex ha hb)
    have hsub : odd.biUnion cutc ⊆ ((Finset.univ ×ˢ U.toFinset).filter fun p => G.Adj p.1 p.2) ∪ X := by
      intro p hp
      obtain ⟨c, _, hpc⟩ := Finset.mem_biUnion.mp hp
      have hmem := (cut_mem G (part c) p).mp hpc
      by_cases hX : s(p.1, p.2) ∈ E0
      · exact Finset.mem_union_right _ (by simp [X, hX])
      · apply Finset.mem_union_left
        have hyU : p.2 ∈ U := by
          by_contra h
          apply hmem.2.1
          refine hclosed c hmem.1 h ?_
          refine SimpleGraph.deleteEdges_adj.mpr ⟨hmem.2.2, ?_⟩
          exact hX
        exact (edges_mem G _ _ p).mpr
          ⟨Finset.mem_univ _, Set.mem_toFinset.mpr hyU, hmem.2.2⟩
    have hUpper : (((Finset.univ ×ˢ U.toFinset).filter fun p => G.Adj p.1 p.2)).card = 3 * U.ncard := by
      rw [edges_swap, edges_count]
      rw [Set.ncard_eq_toFinset_card' U]
      simp [show ∀ v : V, G.degree v = 3 from hcubic, Nat.mul_comm]
    have hLo : 3 * odd.card ≤ (odd.biUnion cutc).card := by
      rw [Finset.card_biUnion hdisjoint]
      calc
        3 * odd.card = ∑ _ ∈ odd, (3 : ℕ) := by simp [Nat.mul_comm]
        _ ≤ _ := Finset.sum_le_sum hcut
    have hTotal := hLo.trans ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _))
    rw [hUpper] at hTotal
    have hX4 : X.card ≤ 4 := (card_pairs_le E0).trans (by omega)
    have hOddCard : C.oddComponents.ncard = odd.card :=
      Set.ncard_eq_toFinset_card' C.oddComponents
    -- parity
    have hpar := odd_ncard_oddComponents (G := C)
    have hNat : Nat.card D.verts = Fintype.card V - U.ncard := by
      rw [Nat.card_coe_set_eq]
      have hverts : D.verts = Set.univ \ U := by
        simp [D]
      rw [hverts, Set.ncard_sdiff (Set.subset_univ U), Set.ncard_univ, Nat.card_eq_fintype_card]
    have hUle : U.ncard ≤ Fintype.card V := by
      rw [← Nat.card_eq_fintype_card, ← Set.ncard_univ]
      exact Set.ncard_le_ncard (Set.subset_univ U)
    have hEven := even_card G hcubic
    rw [hNat, hOddCard] at hpar
    show ¬ U.ncard < C.oddComponents.ncard
    rw [hOddCard]
    intro hlt
    rw [Nat.odd_iff, Nat.odd_iff] at hpar
    rw [Nat.even_iff] at hEven
    omega
  obtain ⟨M', hM'⟩ := hPM
  let M : G.Subgraph :=
    { verts := M'.verts
      Adj := M'.Adj
      adj_sub := fun h => (SimpleGraph.deleteEdges_adj.mp (M'.adj_sub h)).1
      edge_vert := M'.edge_vert
      symm := M'.symm }
  have hsubset : M.edgeSet ⊆ G'.edgeSet := M'.edgeSet_subset
  refine ⟨M, ?_, ?_⟩
  · rw [Subgraph.isPerfectMatching_iff]
    exact Subgraph.isPerfectMatching_iff.mp hM'
  · intro e he hM
    have := hsubset hM
    rw [SimpleGraph.edgeSet_deleteEdges] at this
    exact this.2 he

/-- **Main partial result.** A bridgeless cubic graph with two perfect matchings sharing at most
two edges satisfies the Fan–Raspaud conjecture. -/
theorem of_two_pm {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcubic : IsCubic G) (hbridge : G.IsBridgeless)
    (M₁ M₂ : G.Subgraph) (h₁ : M₁.IsPerfectMatching) (h₂ : M₂.IsPerfectMatching)
    (hsmall : (M₁.edgeSet ∩ M₂.edgeSet).ncard ≤ 2) :
    ∃ M : Fin 3 → G.Subgraph, (∀ i, (M i).IsPerfectMatching) ∧
      ∀ e, ¬ (e ∈ (M 0).edgeSet ∧ e ∈ (M 1).edgeSet ∧ e ∈ (M 2).edgeSet) := by
  obtain ⟨M₃, h₃, hav⟩ := avoid_two G hcubic hbridge _ hsmall
  refine ⟨![M₁, M₂, M₃], ?_, ?_⟩
  · intro i
    fin_cases i
    · exact h₁
    · exact h₂
    · exact h₃
  · rintro x ⟨hx1, hx2, hx3⟩
    exact hav x ⟨hx1, hx2⟩ hx3

/-- Two edges at `v` with the same colour are the same edge. -/
lemma same_colour_eq {V : Type} {G : SimpleGraph V} (c : G.lineGraph.Coloring (Fin 3))
    {v w w' : V} (h : G.Adj v w) (h' : G.Adj v w')
    (hc : c ⟨s(v, w), h⟩ = c ⟨s(v, w'), h'⟩) : w = w' := by
  by_contra hne
  have hadj : G.lineGraph.Adj ⟨s(v, w), h⟩ ⟨s(v, w'), h'⟩ := by
    rw [lineGraph_adj_iff_exists]
    refine ⟨?_, v, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩
    intro heq
    exact hne (Sym2.congr_right.mp (congrArg Subtype.val heq))
  exact c.valid hadj hc

/-- Every colour appears at every vertex of a cubic graph. -/
lemma colour_hit {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (hcub : IsCubic G) (c : G.lineGraph.Coloring (Fin 3)) (v : V)
    (i : Fin 3) : ∃ w, ∃ h : G.Adj v w, c ⟨s(v, w), h⟩ = i := by
  have hst : (Finset.univ : Finset (Fin 3)).card ≤ (G.neighborFinset v).card := by
    rw [G.card_neighborFinset_eq_degree, hcub v]
    simp
  obtain ⟨w, hw, hwi⟩ := Finset.surj_on_of_inj_on_of_card_le
    (fun w hw => c ⟨s(v, w), (G.mem_neighborFinset v w).mp hw⟩)
    (fun _ _ => Finset.mem_univ _)
    (fun a₁ a₂ ha₁ ha₂ h => same_colour_eq c _ _ h) hst i (Finset.mem_univ _)
  exact ⟨w, (G.mem_neighborFinset v w).mp hw, hwi.symm⟩

/-- **Class 1 case.** A 3-edge-colourable cubic graph has three perfect matchings with no edge
common to all three (the colour classes). -/
theorem class_one {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcub : IsCubic G) (hcol : G.lineGraph.Colorable 3) :
    ∃ M : Fin 3 → G.Subgraph, (∀ i, (M i).IsPerfectMatching) ∧
      ∀ e, ¬ (e ∈ (M 0).edgeSet ∧ e ∈ (M 1).edgeSet ∧ e ∈ (M 2).edgeSet) := by
  obtain ⟨c⟩ := hcol
  refine ⟨fun i =>
    { verts := Set.univ
      Adj := fun u v => ∃ h : G.Adj u v, c ⟨s(u, v), h⟩ = i
      adj_sub := fun ⟨h, _⟩ => h
      edge_vert := fun _ => Set.mem_univ _
      symm := ⟨fun u v huv => by
        obtain ⟨h, hc⟩ := huv
        refine ⟨h.symm, ?_⟩
        rw [show (⟨s(v, u), h.symm⟩ : G.edgeSet) = ⟨s(u, v), h⟩ from Subtype.ext Sym2.eq_swap]
        exact hc⟩ }, fun i => ?_, ?_⟩
  · rw [Subgraph.isPerfectMatching_iff]
    intro v
    obtain ⟨w, hw, hwi⟩ := colour_hit hcub c v i
    refine ⟨w, show ∃ h : G.Adj v w, c ⟨s(v, w), h⟩ = i from ⟨hw, hwi⟩, ?_⟩
    intro w' hw'
    obtain ⟨h', hc'⟩ := (show ∃ h : G.Adj v w', c ⟨s(v, w'), h⟩ = i from hw')
    exact same_colour_eq c h' hw (hc'.trans hwi.symm)
  · intro e
    induction e using Sym2.ind with
    | h u v =>
      rintro ⟨h0, h1, -⟩
      rw [Subgraph.mem_edgeSet] at h0 h1
      obtain ⟨a0, c0⟩ := (show ∃ h : G.Adj u v, c ⟨s(u, v), h⟩ = 0 from h0)
      obtain ⟨a1, c1⟩ := (show ∃ h : G.Adj u v, c ⟨s(u, v), h⟩ = 1 from h1)
      have h01 : (0 : Fin 3) = 1 := c0.symm.trans c1
      exact absurd h01 (by decide)

theorem main : H1 → H2 →
    type_of% @BergeFulkersonConjecture.berge_fulkerson_conjecture.variants.fan_raspaud := by
  intro h1 h2 V _ _ G _ hcub hbr
  by_cases hcol : G.lineGraph.Colorable 3
  · exact class_one G hcub hcol
  by_cases hsmall : ∃ M₁ M₂ : G.Subgraph, M₁.IsPerfectMatching ∧ M₂.IsPerfectMatching ∧
      (M₁.edgeSet ∩ M₂.edgeSet).ncard ≤ 2
  · obtain ⟨M₁, M₂, h₁, h₂, hs⟩ := hsmall
    exact of_two_pm G hcub hbr M₁ M₂ h₁ h₂ hs
  have hbig : ∀ M₁ M₂ : G.Subgraph, M₁.IsPerfectMatching → M₂.IsPerfectMatching →
      2 < (M₁.edgeSet ∩ M₂.edgeSet).ncard := fun M₁ M₂ h₁ h₂ =>
    lt_of_not_ge fun hle => hsmall ⟨M₁, M₂, h₁, h₂, hle⟩
  by_cases hodd : ∃ F : G.Subgraph, F.IsPerfectMatching ∧
      {c : (G.deleteEdges F.edgeSet).ConnectedComponent | Odd c.supp.ncard}.ncard ≤ 2
  · exact h1 G hcub hbr hcol hbig hodd
  · exact h2 G hcub hbr hcol hbig fun F hF => lt_of_not_ge fun hle => hodd ⟨F, hF, hle⟩

end OMA.R_BergeFulkersonConjecture_berge_fulkerson_conjecture_variants_fan_raspaud_R2
