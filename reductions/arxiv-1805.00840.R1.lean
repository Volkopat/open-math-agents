import OMAStatements.S_arxiv_1805_00840

-- Credit: @ryansolves
-- Matching-split proof and six-slot reduction for Conjecture 2 of arXiv:1805.00840.

namespace OMA.R_arxiv_1805_00840_R1
open SimpleGraph OMA.S_arxiv_1805_00840

variable {V : Type*} {G : SimpleGraph V} {A N : G.Subgraph} {u v : V}

/-- Restricting a matching to a set closed under taking partners preserves matching. -/
theorem matching_induce_closed (hN : N.IsMatching) {s : Set V} (hs : s ⊆ N.verts)
    (hc : ∀ {x y}, x ∈ s → N.Adj x y → y ∈ s) : (N.induce s).IsMatching := by
  intro x hx
  obtain ⟨y, hy, _⟩ := hN (hs hx)
  exact ⟨y, ⟨hx, hc hx hy, hy⟩, fun z hz => hN.eq_of_adj_left hz.2.2 hy⟩

/-- A matching already covering every vertex of a larger matching is maximal inside it. -/
theorem matching_eq_of_le_verts (hA : A.IsMatching) (hN : N.IsMatching)
    (hle : A ≤ N) (hv : N.verts = A.verts) : N = A := by
  apply le_antisymm _ hle
  refine ⟨hv.le, ?_⟩
  intro x y hxy
  obtain ⟨z, hz, _⟩ := hA (hv ▸ hxy.fst_mem)
  rwa [hN.eq_of_adj_left hxy (hle.2 hz)]

/-- If u cannot reach an old covered vertex, its new partner v is forced. -/
theorem uniquelyRestricted_add_forced (hA : IsUniquelyRestricted A) (e : G.Adj u v)
    (hu : u ∉ A.verts) (hv : v ∉ A.verts)
    (hfree : ∀ x ∈ A.verts, ¬G.Adj u x) :
    IsUniquelyRestricted (A ⊔ G.subgraphOfAdj e) := by
  have hd : Disjoint A.support (G.subgraphOfAdj e).support := by
    apply Set.disjoint_left.mpr
    intro x hx he
    have hxa := A.support_subset_verts hx
    have hxe := (G.subgraphOfAdj e).support_subset_verts he
    simp only [subgraphOfAdj_verts, Set.mem_insert_iff, Set.mem_singleton_iff] at hxe
    rcases hxe with rfl | rfl
    · exact hu hxa
    · exact hv hxa
  have hsup := hA.1.sup (Subgraph.IsMatching.subgraphOfAdj e) hd
  refine ⟨hsup, ?_⟩
  intro N hN hverts
  have memN (x : V) : x ∈ N.verts ↔ x ∈ A.verts ∨ x = u ∨ x = v := by
    rw [hverts]
    change x ∈ A.verts ∪ {u, v} ↔ _
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  obtain ⟨w, hw, _⟩ := hN ((memN u).2 (.inr (.inl rfl)))
  have forced : N.Adj u v := by
    rcases (memN w).1 hw.snd_mem with ha | rfl | rfl
    · exact (hfree w ha (N.adj_sub hw)).elim
    · exact (G.loopless.irrefl _ (N.adj_sub hw)).elim
    · exact hw
  have closed {x y : V} (hx : x ∈ A.verts) (hxy : N.Adj x y) : y ∈ A.verts := by
    rcases (memN y).1 hxy.snd_mem with h | rfl | rfl
    · exact h
    · exact (hv (hN.eq_of_adj_left hxy.symm forced ▸ hx)).elim
    · exact (hu (hN.eq_of_adj_left hxy.symm forced.symm ▸ hx)).elim
  have hres := matching_induce_closed hN (fun x hx => (memN x).2 (.inl hx)) @closed
  have heq := hA.2 (N.induce A.verts) hres rfl
  apply matching_eq_of_le_verts hsup hN _ hverts
  apply sup_le
  · refine ⟨fun x hx => (memN x).2 (.inl hx), ?_⟩
    intro x y ha
    have h : (N.induce A.verts).Adj x y := heq ▸ ha
    exact h.2.2
  · exact (subgraphOfAdj_le_iff e N).2 forced

end OMA.R_arxiv_1805_00840_R1

namespace OMA.R_arxiv_1805_00840_R1
open SimpleGraph OMA.S_arxiv_1805_00840
variable {V : Type*} {G : SimpleGraph V}


theorem empty_ur : IsUniquelyRestricted (⊥ : G.Subgraph) := by
  constructor
  · intro x hx
    exact hx.elim
  · intro N _ hv
    apply bot_unique
    exact ⟨hv.le, fun _ _ h => (hv.le h.fst_mem).elim⟩

/-- A peeled edge can go into one of the two classes when at most one other
    neighbor of its first endpoint belongs to the old matching. -/
theorem split_insert {M : G.Subgraph} (hM : M.IsMatching) {u v : V} (e : M.Adj u v)
    (hlow : ∀ x ∈ M.verts, ∀ y ∈ M.verts, G.Adj u x → G.Adj u y →
      x ≠ v → y ≠ v → x = y)
    (h : ∃ A B : G.Subgraph, IsUniquelyRestricted A ∧ IsUniquelyRestricted B ∧ Disjoint A.verts B.verts ∧ A ⊔ B = M.induce {x | x ∈ M.verts ∧ x ≠ u ∧ x ≠ v}) : ∃ A B : G.Subgraph, IsUniquelyRestricted A ∧ IsUniquelyRestricted B ∧ Disjoint A.verts B.verts ∧ A ⊔ B = M := by
  classical
  obtain ⟨A, B, hA, hB, hAB, heq⟩ := h
  let S := {x | x ∈ M.verts ∧ x ≠ u ∧ x ≠ v}
  have cover : A.verts ∪ B.verts = S := congrArg Subgraph.verts heq
  have inS {x : V} (hx : x ∈ A.verts ∪ B.verts) : x ∈ M.verts ∧ x ≠ u ∧ x ≠ v :=
    show x ∈ S from cover ▸ hx
  have oldle : M.induce S ≤ M := ⟨fun _ hx => hx.1, fun _ _ h => h.2.2⟩
  have attach {P Q : G.Subgraph} (hP : IsUniquelyRestricted P) (hQ : IsUniquelyRestricted Q)
      (hd : Disjoint P.verts Q.verts) (hPQ : P ⊔ Q = M.induce S)
      (hf : ∀ x ∈ P.verts, ¬G.Adj u x) : ∃ A B : G.Subgraph, IsUniquelyRestricted A ∧ IsUniquelyRestricted B ∧ Disjoint A.verts B.verts ∧ A ⊔ B = M := by
    have vPQ : P.verts ∪ Q.verts = S := congrArg Subgraph.verts hPQ
    have bound {x : V} (hx : x ∈ P.verts ∪ Q.verts) : x ∈ M.verts ∧ x ≠ u ∧ x ≠ v :=
      show x ∈ S from vPQ ▸ hx
    have hnew := uniquelyRestricted_add_forced hP (M.adj_sub e)
      (fun hu => (bound (.inl hu)).2.1 rfl) (fun hv => (bound (.inl hv)).2.2 rfl) hf
    let E := G.subgraphOfAdj (M.adj_sub e)
    have vertsE (x : V) : x ∈ E.verts ↔ x = u ∨ x = v := by
      simp [E]
    have disj : Disjoint (P ⊔ E).verts Q.verts := by
      apply Set.disjoint_left.mpr
      intro x hx hq
      rcases hx with hp | he
      · exact Set.disjoint_left.mp hd hp hq
      · rcases (vertsE x).1 he with hx | hx
        · exact (bound (.inr hq)).2.1 hx
        · exact (bound (.inr hq)).2.2 hx
    refine ⟨P ⊔ E, Q, hnew, hQ, disj, ?_⟩
    have lePQ : P ⊔ Q ≤ M := hPQ ▸ oldle
    have hle : (P ⊔ E) ⊔ Q ≤ M := sup_le
      (sup_le (le_sup_left.trans lePQ) (subgraphOfAdj_le_of_adj M e)) (le_sup_right.trans lePQ)
    have hverts : M.verts = ((P ⊔ E) ⊔ Q).verts := by
      apply Set.Subset.antisymm _ hle.1
      intro x hx
      by_cases he : x = u ∨ x = v
      · exact Or.inl (Or.inr ((vertsE x).2 he))
      · have hs : x ∈ S := ⟨hx, fun h => he (.inl h), fun h => he (.inr h)⟩
        rcases vPQ.symm ▸ hs with hp | hq
        · exact Or.inl (Or.inl hp)
        · exact Or.inr hq
    exact (matching_eq_of_le_verts (hnew.1.sup hQ.1
      (disj.mono (P ⊔ E).support_subset_verts Q.support_subset_verts)) hM hle hverts).symm
  by_cases hf : ∀ x ∈ A.verts, ¬G.Adj u x
  · exact attach hA hB hAB heq hf
  · push Not at hf
    obtain ⟨x, hx, hux⟩ := hf
    apply attach hB hA hAB.symm ((sup_comm B A).trans heq)
    intro y hy huy
    have hxs := inS (.inl hx)
    have hys := inS (.inr hy)
    have eq := hlow x hxs.1 y hys.1 hux huy hxs.2.2 hys.2.2
    exact Set.disjoint_left.mp hAB hx (eq ▸ hy)

end OMA.R_arxiv_1805_00840_R1

namespace OMA.R_arxiv_1805_00840_R1
open SimpleGraph OMA.S_arxiv_1805_00840
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- In every nonempty vertex set of a connected noncubic subcubic graph,
    some vertex has at most two neighbors inside that set. -/
theorem subcubic_sparse_vertex (hc : G.Connected) (hd : ∀ v, G.degree v ≤ 3)
    (hn : ∃ v, G.degree v < 3) (s : Finset V) (hs : s.Nonempty) :
    ∃ u ∈ s, ((G.neighborFinset u).filter (· ∈ s)).card ≤ 2 := by
  classical
  by_contra! h
  have sat {u : V} (hu : u ∈ s) : (G.neighborFinset u).filter (· ∈ s) = G.neighborFinset u := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset ..)
    have h1 := h u hu
    have h2 := hd u
    rw [← G.card_neighborFinset_eq_degree u] at h2
    omega
  obtain ⟨a, ha⟩ := hs
  have all_mem (v : V) : v ∈ s := by
    have path := (G.reachable_iff_reflTransGen a v).1 (hc.preconnected a v)
    induction path with
    | refl => exact ha
    | tail _ e ih =>
      have he := (G.mem_neighborFinset ..).2 e
      rw [← sat ih] at he
      exact (Finset.mem_filter.mp he).2
  obtain ⟨v, hv⟩ := hn
  have h3 := h v (all_mem v)
  rw [sat (all_mem v), G.card_neighborFinset_eq_degree v] at h3
  omega

/-- Deleting the designated neighbor from a set of at most two leaves at most one. -/
theorem unique_other_neighbor {s : Finset V} {u v : V} (hv : v ∈ s) (huv : G.Adj u v)
    (hd : ((G.neighborFinset u).filter (· ∈ s)).card ≤ 2)
    {x y : V} (hx : x ∈ s) (hy : y ∈ s) (hux : G.Adj u x) (huy : G.Adj u y)
    (hxv : x ≠ v) (hyv : y ≠ v) : x = y := by
  classical
  by_contra hxy
  have hsub : ({x, y, v} : Finset V) ⊆ (G.neighborFinset u).filter (· ∈ s) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).2 hux, hx⟩
    · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).2 huy, hy⟩
    · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).2 huv, hv⟩
  have hcard := Finset.card_le_card hsub
  simp [hxy, hxv, hyv] at hcard
  omega

end OMA.R_arxiv_1805_00840_R1

namespace OMA.R_arxiv_1805_00840_R1
open SimpleGraph OMA.S_arxiv_1805_00840
variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Every matching of a connected noncubic subcubic graph is a disjoint union of
    two uniquely restricted matchings of the original graph. -/
theorem subcubic_matching_split (hc : G.Connected) (hd : ∀ v, G.degree v ≤ 3)
    (hn : ∃ v, G.degree v < 3) (M : G.Subgraph) (hM : M.IsMatching) : ∃ A B : G.Subgraph, IsUniquelyRestricted A ∧ IsUniquelyRestricted B ∧ Disjoint A.verts B.verts ∧ A ⊔ B = M := by
  classical
  by_cases hne : M.verts.Nonempty
  · obtain ⟨u, hu, hd2⟩ := subcubic_sparse_vertex hc hd hn M.verts.toFinset
      (Set.toFinset_nonempty.mpr hne)
    have hum : u ∈ M.verts := Set.mem_toFinset.mp hu
    obtain ⟨v, e, _⟩ := hM hum
    let S : Set V := {x | x ∈ M.verts ∧ x ≠ u ∧ x ≠ v}
    have closed {x y : V} (hx : x ∈ S) (hxy : M.Adj x y) : y ∈ S := by
      refine ⟨hxy.snd_mem, ?_, ?_⟩
      · rintro rfl
        exact hx.2.2 (hM.eq_of_adj_left hxy.symm e)
      · rintro rfl
        exact hx.2.1 (hM.eq_of_adj_left hxy.symm e.symm)
    have hm' := matching_induce_closed hM (s := S) (fun _ hx => hx.1) @closed
    apply split_insert hM e _ (subcubic_matching_split hc hd hn (M.induce S) hm')
    intro x hx y hy hux huy hxv hyv
    exact unique_other_neighbor (Set.mem_toFinset.mpr e.snd_mem) (M.adj_sub e) hd2
      (Set.mem_toFinset.mpr hx) (Set.mem_toFinset.mpr hy) hux huy hxv hyv
  · have hbot : M = ⊥ := by
      apply bot_unique
      exact ⟨fun x hx => (hne ⟨x,hx⟩).elim, fun x _ h => (hne ⟨x,h.fst_mem⟩).elim⟩
    exact ⟨⊥, ⊥, empty_ur, empty_ur, disjoint_bot_left, by simp [hbot]⟩
termination_by M.verts.ncard
decreasing_by
  refine Set.ncard_lt_ncard ?_ (Set.toFinite _)
  exact Set.ssubset_iff_subset_ne.mpr ⟨fun _ h => h.1, fun he =>
    have h : u ∈ S := (congrArg (fun t : Set V => u ∈ t) he).mpr hum
    h.2.1 rfl⟩

end OMA.R_arxiv_1805_00840_R1

namespace OMA.R_arxiv_1805_00840_R1
open SimpleGraph OMA.S_arxiv_1805_00840
variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Three copies of each half of a matching give enough internal edges in
    aggregate, while leaving every vertex free in at least three slots. -/
theorem six_slots_from_matching (hc : G.Connected) (hd : ∀ v, G.degree v ≤ 3)
    (hn : ∃ v, G.degree v < 3) (M : G.Subgraph) (hm : M.IsMatching)
    (hsize : G.edgeFinset.card ≤ 3 * M.edgeSet.ncard) :
    ∃ L : Fin 6 → G.Subgraph, (∀ i, IsUniquelyRestricted (L i)) ∧
      G.edgeFinset.card ≤ ∑ i, (L i).edgeSet.ncard ∧
      ∀ x, 3 ≤ {i : Fin 6 | x ∉ (L i).verts}.ncard := by
  classical
  obtain ⟨A, B, hA, hB, hab, heq⟩ := subcubic_matching_split hc hd hn M hm
  let L (i : Fin 6) := if i.val < 3 then A else B
  refine ⟨L, fun i => by dsimp [L]; split <;> assumption, ?_, ?_⟩
  · rw [← heq, Subgraph.edgeSet_sup] at hsize
    have hsum := Set.ncard_union_le A.edgeSet B.edgeSet
    simp [L, Fin.sum_univ_succ]
    omega
  · intro x
    by_cases hx : x ∈ A.verts
    · have hb : x ∉ B.verts := Set.disjoint_left.mp hab hx
      have hs : ({3,4,5} : Set (Fin 6)) ⊆ {i : Fin 6 | x ∉ (L i).verts} := by
        intro i hi
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
        rcases hi with rfl | rfl | rfl <;> simpa [L] using hb
      exact le_trans (by decide : 3 ≤ ({3,4,5} : Finset (Fin 6)).card)
        (by simpa using Set.ncard_le_ncard hs)
    · have hs : ({0,1,2} : Set (Fin 6)) ⊆ {i : Fin 6 | x ∉ (L i).verts} := by
        intro i hi
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
        rcases hi with rfl | rfl | rfl <;> simpa [L] using hx
      exact le_trans (by decide : 3 ≤ ({0,1,2} : Finset (Fin 6)).card)
        (by simpa using Set.ncard_le_ncard hs)

end OMA.R_arxiv_1805_00840_R1

namespace OMA.R_arxiv_1805_00840_R1
open SimpleGraph OMA.S_arxiv_1805_00840
end OMA.R_arxiv_1805_00840_R1

namespace BridgeMatching
open SimpleGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem cut_not_one (nb : ∀ e ∈ G.edgeSet, ¬G.IsBridge e) (s : Set V) :
    Nat.card ((Σ x : s, {y : G.neighborSet x // (y : V) ∉ s})) ≠ 1 := by
  intro h
  obtain ⟨huniq, ⟨d⟩⟩ := Nat.card_eq_one_iff_unique.mp h
  let a : V := d.1
  let b : V := d.2.1
  have he : G.Adj a b := d.2.1.2
  apply nb s(a,b) he
  apply isBridge_iff.mpr
  intro reach
  have path := ((G.deleteEdges {s(a,b)}).reachable_iff_reflTransGen a b).1 reach
  have closed {x y : V} (hx : x ∈ s) (e : (G.deleteEdges {s(a,b)}).Adj x y) : y ∈ s := by
    by_contra hy
    let f : (Σ x : s, {y : G.neighborSet x // (y : V) ∉ s}) := ⟨⟨x,hx⟩, ⟨⟨y,e.1⟩,hy⟩⟩
    have eq := huniq.elim f d
    have ex : x = a := congrArg (fun z : (Σ x : s, {y : G.neighborSet x // (y : V) ∉ s}) => (z.1 : V)) eq
    have ey : y = b := congrArg (fun z : (Σ x : s, {y : G.neighborSet x // (y : V) ∉ s}) => (z.2.1 : V)) eq
    exact e.2 (by simp [ex,ey,he.ne])
  have step {z : V} (p : Relation.ReflTransGen (G.deleteEdges {s(a,b)}).Adj a z) : z ∈ s := by
    induction p with
    | refl => exact d.1.2
    | tail _ e ih => exact closed ih e
  exact d.2.2 (step path)

theorem cut_handshake (s : Set V) [Fintype s] [DecidablePred (· ∈ s)] :
    Nat.card ((Σ x : s, {y : G.neighborSet x // (y : V) ∉ s})) + 2 * (G.induce s).edgeFinset.card = ∑ x : s, G.degree x := by
  classical
  have inner (x : s) : {y : G.neighborSet x // (y : V) ∈ s} ≃ (G.induce s).neighborSet x :=
    { toFun := fun y => ⟨⟨y.1.1, y.2⟩, y.1.2⟩
      invFun := fun y => ⟨⟨y.1.1, y.2⟩, y.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have split (x : s) :
      Nat.card {y : G.neighborSet x // (y : V) ∉ s} + (G.induce s).degree x = G.degree x := by
    have eq := Nat.card_congr (Equiv.sumCompl (fun y : G.neighborSet x => (y : V) ∈ s))
    rw [Nat.card_sum, Nat.card_congr (inner x)] at eq
    have a : Nat.card ((G.induce s).neighborSet x) = (G.induce s).degree x :=
      Nat.card_eq_fintype_card.trans (card_neighborSet_eq_degree _ _)
    have b : Nat.card (G.neighborSet x) = G.degree x :=
      Nat.card_eq_fintype_card.trans (card_neighborSet_eq_degree _ _)
    rw [a,b,add_comm] at eq
    exact eq
  rw [← (G.induce s).sum_degrees_eq_twice_card_edges, Nat.card_sigma, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun x _ => split x)

theorem cubic_odd_cut (hd : ∀ x, G.degree x = 3) (hb : ∀ e ∈ G.edgeSet, ¬G.IsBridge e)
    (s : Set V) (hs : Odd s.ncard) : 3 ≤ Nat.card ((Σ x : s, {y : G.neighborSet x // (y : V) ∉ s})) := by
  classical
  have h := cut_handshake G s
  simp only [hd, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  have hc : s.ncard = Fintype.card s := by rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  obtain ⟨k,hk⟩ := hs
  have h1 := cut_not_one G hb s
  omega

theorem cut_pair_injective (s : Set V) :
    Function.Injective (fun e : (Σ x : s, {y : G.neighborSet x // (y : V) ∉ s}) => ((e.1 : V), (e.2.1 : V))) := by
  rintro ⟨⟨x,hx⟩, ⟨⟨y,hxy⟩,hy⟩⟩ ⟨⟨a,ha⟩, ⟨⟨b,hab⟩,hb⟩⟩ heq
  cases Prod.mk.inj heq with
  | intro h1 h2 => cases h1; cases h2; rfl

/-- Every odd component after vertex deletion requires at least three incident
    cut edges. Their opposite darts inject into the three incidences per deleted vertex. -/
theorem bridgeless_cubic_perfect (hd : ∀ x, G.degree x = 3)
    (hb : ∀ e ∈ G.edgeSet, ¬G.IsBridge e) : ∃ M : G.Subgraph, M.IsPerfectMatching := by
  classical
  apply tutte.mpr
  intro U
  let H := (⊤ : G.Subgraph).deleteVerts U
  let S (c : H.coe.oddComponents) : Set V := Subtype.val '' c.1.supp
  have lower (c : H.coe.oddComponents) : 3 ≤ Nat.card ((Σ x : (S c), {y : G.neighborSet x // (y : V) ∉ (S c)})) := by
    apply cubic_odd_cut G hd hb
    rw [show (S c).ncard = c.1.supp.ncard from Set.ncard_image_of_injective _ Subtype.val_injective]
    exact c.2
  have endsIn (c : H.coe.oddComponents) (d : (Σ x : (S c), {y : G.neighborSet x // (y : V) ∉ (S c)})) : (d.2.1 : V) ∈ U := by
    by_contra hout
    obtain ⟨x, hx, he⟩ := d.1.2
    let y : H.verts := ⟨d.2.1, ⟨Set.mem_univ _, hout⟩⟩
    have ha : H.coe.Adj x y := by
      change x.1 ∈ H.verts ∧ y.1 ∈ H.verts ∧ G.Adj x.1 y.1
      exact ⟨x.2, y.2, he.symm ▸ d.2.1.2⟩
    exact d.2.2 ⟨y, c.1.mem_supp_of_adj_mem_supp hx ha, rfl⟩
  let f (e : Σ c : H.coe.oddComponents, (Σ x : (S c), {y : G.neighborSet x // (y : V) ∉ (S c)})) : Σ v : U, G.neighborSet v :=
    ⟨⟨e.2.2.1, endsIn e.1 e.2⟩, ⟨e.2.1, e.2.2.1.2.symm⟩⟩
  have inj : Function.Injective f := by
    rintro ⟨c,d⟩ ⟨c',d'⟩ he
    have hx : (d.1 : V) = (d'.1 : V) := congrArg (fun z : Σ v : U, G.neighborSet v => (z.2 : V)) he
    have hy : (d.2.1 : V) = (d'.2.1 : V) := congrArg (fun z : Σ v : U, G.neighborSet v => (z.1 : V)) he
    obtain ⟨v, hv, ev⟩ := d.1.2
    obtain ⟨w, hw, ew⟩ := d'.1.2
    have vw : v = w := Subtype.ext (ev.trans (hx.trans ew.symm))
    have cc : c = c' := Subtype.ext ((c.1.mem_supp_iff v).mp hv |>.symm.trans
      ((c'.1.mem_supp_iff v).mp (vw ▸ hw)))
    subst c'
    have ed := cut_pair_injective G (S c) (Prod.ext hx hy)
    cases ed
    rfl
  have hcount := Nat.card_le_card_of_injective f inj
  rw [Nat.card_sigma, Nat.card_sigma] at hcount
  have below := Finset.sum_le_sum (s := Finset.univ) (fun c _ => lower c)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card] at below
  simp only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree, hd, Finset.sum_const,
    Finset.card_univ, smul_eq_mul] at hcount
  change ¬ U.ncard < H.coe.oddComponents.ncard
  rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
  simp only [Set.toFinset_card]
  omega

theorem matching_size {G : SimpleGraph V} [Finite V] (M : G.Subgraph) (hm : M.IsMatching) :
    2 * M.edgeSet.ncard = M.verts.ncard := by
  classical
  letI := Fintype.ofFinite V
  have cardE : M.edgeSet.ncard = M.coe.edgeFinset.card := by
    rw [← M.image_coe_edgeSet_coe, Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective),
      SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard]
  rw [cardE, ← M.coe.sum_degrees_eq_twice_card_edges]
  calc
    _ = ∑ _ : M.verts, 1 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [@SimpleGraph.degree_eq_one_iff_existsUnique_adj _ M.coe x (Subtype.fintype _)]
      obtain ⟨y,hy,hu⟩ := hm x.2
      exact ⟨⟨y,hy.snd_mem⟩,hy,fun z hz => Subtype.ext (hu z hz)⟩
    _ = M.verts.ncard := by
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, Set.fintypeCard_eq_ncard]

theorem deficit_identity {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hd : ∀ x, 2 ≤ G.degree x ∧ G.degree x ≤ 3) :
    2 * G.edgeFinset.card + {x | G.degree x = 2}.ncard = 3 * Fintype.card V := by
  classical
  let P : Set V := {x | G.degree x = 2}
  have per (x : V) : G.degree x + (if x ∈ P then 1 else 0) = 3 := by
    change G.degree x + (if G.degree x = 2 then 1 else 0) = 3
    split <;> have := hd x <;> omega
  have hh := Finset.sum_congr (s₁ := Finset.univ) rfl (fun x _ => per x)
  rw [Finset.sum_add_distrib, G.sum_degrees_eq_twice_card_edges] at hh
  have hcard : (∑ x : V, if x ∈ P then 1 else 0) = P.ncard := by
    rw [← Finset.sum_filter]
    simp [← Set.fintypeCard_eq_ncard, Fintype.card_subtype]
  rw [hcard] at hh
  simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_comm (Fintype.card V) 3] using hh

theorem ordinary_block_bound :
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
      (∀ e ∈ G.edgeSet, ¬ G.IsBridge e) → (∀ x, 2 ≤ G.degree x ∧ G.degree x ≤ 3) →
      (∃ u v, u ≠ v ∧ G.degree u = 2 ∧ G.degree v = 2) →
      ∃ M : G.Subgraph, M.IsMatching ∧ G.edgeFinset.card ≤ 3 * M.edgeSet.ncard := by
  intro V _ G _ hc hb hd htwo
  classical
  let P : Set V := {x | G.degree x = 2}
  have ports : ∃ p q : P, p ≠ q := by
    obtain ⟨u,v,huv,hu,hv⟩ := htwo
    exact ⟨⟨u,hu⟩,⟨v,hv⟩, fun he => huv (congrArg Subtype.val he)⟩
  let tripleAdj : ((Fin 3 × V) ⊕ P) → ((Fin 3 × V) ⊕ P) → Prop := fun
    | .inl (i,x), .inl (j,y) => i = j ∧ G.Adj x y
    | .inl (_,x), .inr p => x = p.1
    | .inr p, .inl (_,y) => y = p.1
    | .inr _, .inr _ => False
  let tripleGraph : SimpleGraph (((Fin 3 × V) ⊕ P)) := {
    Adj := tripleAdj
    symm := ⟨by
      rintro (⟨i,x⟩ | p) (⟨j,y⟩ | q) h
      · exact ⟨h.1.symm,h.2.symm⟩
      · exact h
      · exact h
      · exact h⟩
    loopless := ⟨by
      rintro (⟨i,x⟩ | p) h
      · exact h.2.ne rfl
      · exact h⟩ }
  let copyNeighbors (i : Fin 3) (v : V) :
      (tripleGraph).neighborSet (.inl (i,v)) ≃ G.neighborSet v ⊕ {p : P // p.1 = v} := {
    toFun := fun
      | ⟨.inl (_,y),h⟩ => .inl ⟨y,h.2⟩
      | ⟨.inr p,h⟩ => .inr ⟨p,Eq.symm h⟩
    invFun := fun
      | .inl y => ⟨.inl (i,y.1),rfl,y.2⟩
      | .inr p => ⟨.inr p.1,Eq.symm p.2⟩
    left_inv := by
      rintro ⟨(⟨j,y⟩ | p),h⟩
      · have ij : i = j := h.1
        subst j; rfl
      · rfl
    right_inv := by rintro (y|p) <;> rfl }
  let hubNeighbors (p : P) : (tripleGraph).neighborSet (.inr p) ≃ Fin 3 := {
    toFun := fun
      | ⟨.inl (i,_),_⟩ => i
      | ⟨.inr _,h⟩ => False.elim h
    invFun i := ⟨.inl (i,p.1),rfl⟩
    left_inv := by
      rintro ⟨(⟨i,y⟩ | q),h⟩
      · have ey : y = p.1 := h
        subst y; rfl
      · exact False.elim h
    right_inv _ := rfl }
  have triple_cubic 
      (hdeg : ∀ v, 2 ≤ G.degree v ∧ G.degree v ≤ 3)
      (hport : ∀ v, v ∈ P ↔ G.degree v = 2) : ∀ x, (tripleGraph).degree x = 3 := by
    classical
    rintro (⟨i,v⟩ | p)
    · have h := Nat.card_congr (copyNeighbors i v)
      rw [Nat.card_sum] at h
      by_cases hv : v ∈ P
      · have one : Nat.card {p : P // p.1 = v} = 1 := Nat.card_eq_one_iff_unique.mpr
          ⟨⟨fun a b => Subtype.ext (Subtype.ext (a.2.trans b.2.symm))⟩, ⟨⟨⟨v,hv⟩,rfl⟩⟩⟩
        rw [one] at h
        simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree, (hport v).mp hv] using h
      · haveI : IsEmpty {p : P // p.1 = v} := ⟨fun p => hv (p.2 ▸ p.1.2)⟩
        have hv3 : G.degree v = 3 := by
          have := hdeg v
          have := mt (hport v).mpr hv
          omega
        simpa only [Nat.card_of_isEmpty, add_zero, Nat.card_eq_fintype_card, card_neighborSet_eq_degree, hv3] using h
    · simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree, Fintype.card_fin] using
        Nat.card_congr (hubNeighbors p)
  have triple_spoke_detour (hc : G.Connected) (ports : ∃ p q : P, p ≠ q) (i : Fin 3) (p : P) :
      ((tripleGraph).deleteEdges {s(Sum.inl (i,p.1), Sum.inr p)}).Reachable
        (Sum.inl (i,p.1)) (.inr p) := by
    classical
    obtain ⟨a,b,hab⟩ := ports
    obtain ⟨q,hq⟩ : ∃ q : P, q ≠ p := by
      by_cases h : a = p
      · exact ⟨b,h ▸ hab.symm⟩
      · exact ⟨a,h⟩
    obtain ⟨j,hj⟩ : ∃ j : Fin 3, j ≠ i := by fin_cases i <;> decide
    let H := (tripleGraph).deleteEdges {s(Sum.inl (i,p.1), Sum.inr p)}
    let layer (k : Fin 3) : G →g H :=
      { toFun := fun x => .inl (k,x)
        map_rel' := fun {x y} h => deleteEdges_adj.mpr ⟨⟨rfl,h⟩, by simp [Sym2.eq_iff]⟩ }
    have spoke (k : Fin 3) (r : P) (ok : k ≠ i ∨ r ≠ p) : H.Adj (.inl (k,r.1)) (.inr r) := by
      apply deleteEdges_adj.mpr
      refine ⟨rfl, ?_⟩
      simp only [Set.mem_singleton_iff, Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq,
        reduceCtorEq, and_false, or_false, Prod.mk.injEq]
      tauto
    exact ((hc.preconnected p.1 q.1).map (layer i)).trans
      ((spoke i q (.inr hq)).reachable.trans
      ((spoke j q (.inl hj)).symm.reachable.trans
      (((hc.preconnected q.1 p.1).map (layer j)).trans (spoke j p (.inl hj)).reachable)))
  have triple_bridgeless (hc : G.Connected) (hb : ∀ e ∈ G.edgeSet, ¬G.IsBridge e)
      (ports : ∃ p q : P, p ≠ q) : ∀ e ∈ (tripleGraph).edgeSet, ¬(tripleGraph).IsBridge e := by
    classical
    intro e he
    induction e using Sym2.inductionOn with
    | _ a b =>
      rcases a with ⟨i,x⟩ | p <;> rcases b with ⟨j,y⟩ | q
      · obtain ⟨hij,hxy⟩ : i = j ∧ G.Adj x y := he
        subst j
        have path : (G.deleteEdges {s(x,y)}).Reachable x y :=
          Classical.not_not.mp (fun h => hb s(x,y) hxy (isBridge_iff.mpr h))
        let target := (tripleGraph).deleteEdges {s(Sum.inl (i,x), Sum.inl (i,y))}
        let lift' : G.deleteEdges {s(x,y)} →g target :=
          { toFun := fun z => .inl (i,z)
            map_rel' := by
              intro v w h
              obtain ⟨hvw,hn⟩ := deleteEdges_adj.mp h
              apply deleteEdges_adj.mpr
              refine ⟨⟨rfl,hvw⟩, ?_⟩
              simpa [Sym2.eq_iff] using hn }
        exact fun h => (isBridge_iff.mp h) (path.map lift')
      · have h : x = q.1 := he
        subst x
        exact fun hb => (isBridge_iff.mp hb) (triple_spoke_detour hc ports i q)
      · have h : y = p.1 := he
        subst y
        rw [Sym2.eq_swap]
        exact fun hb => (isBridge_iff.mp hb) (triple_spoke_detour hc ports j p)
      · exact False.elim he
  let layerMatching (M : (tripleGraph).Subgraph) (i : Fin 3) : G.Subgraph := {
    verts := {x | ∃ y, M.Adj (.inl (i,x)) (.inl (i,y))}
    Adj x y := M.Adj (.inl (i,x)) (.inl (i,y))
    adj_sub h := (M.adj_sub h).2
    edge_vert h := ⟨_,h⟩
    symm := ⟨fun _ _ h => M.adj_symm h⟩ }
  have layer_is_matching (M : (tripleGraph).Subgraph) (hm : M.IsMatching) (i : Fin 3) :
      (layerMatching M i).IsMatching := by
    rintro x ⟨y,hy⟩
    refine ⟨y,hy,fun z hz => ?_⟩
    exact (Prod.mk.inj (Sum.inl.inj (hm.eq_of_adj_left hz hy))).2
  have projected_size (M : (tripleGraph).Subgraph) (hm : M.IsPerfectMatching) :
      3 * Fintype.card V ≤ (∑ i, (layerMatching M i).verts.ncard) + P.ncard := by
    classical
    have seat (p : P) : ∃ i : Fin 3, M.Adj (.inr p) (.inl (i,p.1)) := by
      obtain ⟨(⟨i,x⟩ | q),h,-⟩ := Subgraph.isPerfectMatching_iff.mp hm (.inr p)
      · have ex : x = p.1 := M.adj_sub h
        exact ⟨i,ex ▸ h⟩
      · exact False.elim (M.adj_sub h)
    choose sit hsit using seat
    let readout : ((Σ i : Fin 3, (layerMatching M i).verts) ⊕ P) → Fin 3 × V
      | .inl ⟨i,x⟩ => (i,x.1)
      | .inr p => (sit p,p.1)
    have onto : Function.Surjective readout := by
      rintro ⟨i,x⟩
      obtain ⟨(⟨j,y⟩ | p),h,-⟩ := Subgraph.isPerfectMatching_iff.mp hm (.inl (i,x))
      · have hij : i = j := (M.adj_sub h).1
        subst j
        exact ⟨.inl ⟨i,⟨x,⟨y,h⟩⟩⟩,rfl⟩
      · have ex : x = p.1 := M.adj_sub h
        have same := hm.1.eq_of_adj_left (hsit p) h.symm
        exact ⟨.inr p, Prod.ext (Prod.mk.inj (Sum.inl.inj same)).1 ex.symm⟩
    have count := Nat.card_le_card_of_surjective readout onto
    rw [Nat.card_prod, Nat.card_fin, Nat.card_sum, Nat.card_sigma] at count
    simpa only [Nat.card_eq_fintype_card, Set.fintypeCard_eq_ncard] using count
  have cubic := triple_cubic hd (fun _ => Iff.rfl)
  have nb := triple_bridgeless hc hb ports
  obtain ⟨M,hm⟩ := bridgeless_cubic_perfect (tripleGraph) cubic nb
  let L := layerMatching M
  have hl (i : Fin 3) : (L i).IsMatching := layer_is_matching M hm.1 i
  have hsize := projected_size M hm
  have hdef : 2 * G.edgeFinset.card + P.ncard = 3 * Fintype.card V := deficit_identity G hd
  change 3 * Fintype.card V ≤ (∑ i, (L i).verts.ncard) + P.ncard at hsize
  simp_rw [← matching_size _ (hl _)] at hsize
  rw [← Finset.mul_sum] at hsize
  let f (i : Fin 3) := (L i).edgeSet.ncard
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ f (by simp)
  have hmax : ∑ j, (L j).edgeSet.ncard ≤ 3 * (L i).edgeSet.ncard :=
    (Finset.sum_le_sum (fun j hj => hi j hj)).trans (by simp [f])
  exact ⟨L i, hl i, by omega⟩

end BridgeMatching

namespace OMA.R_arxiv_1805_00840_R1
open SimpleGraph OMA.S_arxiv_1805_00840
variable {V : Type*} [Finite V] {G : SimpleGraph V}

/-- Free any chosen port in a uniquely restricted matching at a cost of at most one edge. -/
theorem free_port (M : G.Subgraph) (hm : IsUniquelyRestricted M) (x : V) :
    ∃ A : G.Subgraph, IsUniquelyRestricted A ∧ x ∉ A.verts ∧ M.edgeSet.ncard ≤ A.edgeSet.ncard + 1 := by
  classical
  by_cases hx : x ∈ M.verts
  · obtain ⟨y, e, _⟩ := hm.1 hx
    let S : Set V := {z | z ∈ M.verts ∧ z ≠ x ∧ z ≠ y}
    let A := M.induce S
    let E := G.subgraphOfAdj (M.adj_sub e)
    have ev (z : V) : z ∈ E.verts ↔ z = x ∨ z = y := by simp [E]
    have hE : E.IsMatching := Subgraph.IsMatching.subgraphOfAdj _
    have closed {z w : V} (hz : z ∈ S) (hzw : M.Adj z w) : w ∈ S := by
      refine ⟨hzw.snd_mem, ?_, ?_⟩
      · rintro rfl
        exact hz.2.2 (hm.1.eq_of_adj_left hzw.symm e)
      · rintro rfl
        exact hz.2.1 (hm.1.eq_of_adj_left hzw.symm e.symm)
    have hA : A.IsMatching := matching_induce_closed hm.1 (fun _ hz => hz.1) @closed
    have combine (T : G.Subgraph) (ht : T.IsMatching) (hv : T.verts = S) :
        (T ⊔ E).IsMatching ∧ (T ⊔ E).verts = M.verts := by
      constructor
      · apply ht.sup hE
        apply Set.disjoint_left.mpr
        intro z ht' he'
        have hz : z ∈ S := hv ▸ T.support_subset_verts ht'
        exact ((ev z).1 (E.support_subset_verts he')).elim hz.2.1 hz.2.2
      · ext z
        change z ∈ T.verts ∨ z ∈ E.verts ↔ z ∈ M.verts
        rw [hv, ev]
        change (z ∈ M.verts ∧ z ≠ x ∧ z ≠ y) ∨ z = x ∨ z = y ↔ _
        grind [e.snd_mem]
    have ae := combine A hA rfl
    have rebuild := hm.2 _ ae.1 ae.2
    refine ⟨A, ⟨hA, ?_⟩, fun h => h.2.1 rfl, ?_⟩
    · intro T ht hv
      have full := combine T ht hv
      have eq := hm.2 _ full.1 full.2
      have leM : T ≤ M := eq ▸ le_sup_left
      apply (matching_eq_of_le_verts ht hA _ hv.symm).symm
      exact ⟨hv.le, fun z w h => ⟨hv.le h.fst_mem, hv.le h.snd_mem,leM.2 h⟩⟩
    · have card := Set.ncard_union_le A.edgeSet E.edgeSet
      rw [← Subgraph.edgeSet_sup, rebuild] at card
      simpa [E,edgeSet_subgraphOfAdj] using card
  · exact ⟨M,hm,hx,by omega⟩

end OMA.R_arxiv_1805_00840_R1

namespace BridgeMatching
open SimpleGraph OMA.S_arxiv_1805_00840 OMA.R_arxiv_1805_00840_R1

theorem small_degree_singleton {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (hb : ∀ e ∈ G.edgeSet, ¬G.IsBridge e) (x : V) (hx : G.degree x < 2) :
    ∀ y, y = x := by
  classical
  have no_adj (y : V) : ¬G.Adj x y := by
    intro he
    have hpos := (G.degree_pos_iff_exists_adj x).2 ⟨y,he⟩
    have deg : G.degree x = 1 := by omega
    have unique := (degree_eq_one_iff_existsUnique_adj.mp deg)
    apply hb s(x,y) he
    apply isBridge_iff.mpr
    intro r
    have walk := ((G.deleteEdges {s(x,y)}).reachable_iff_reflTransGen x y).1 r
    have only {z : V} (p : Relation.ReflTransGen (G.deleteEdges {s(x,y)}).Adj x z) : z = x := by
      induction p with
      | refl => rfl
      | tail _ e ih =>
        subst_vars
        obtain ⟨ea,en⟩ := deleteEdges_adj.mp e
        have eq := unique.unique ea he
        exact (en (by simp [eq])).elim
    exact he.ne (only walk).symm
  intro y
  have path := (G.reachable_iff_reflTransGen x y).1 (hc.preconnected x y)
  induction path with
  | refl => rfl
  | tail _ e ih => exact (no_adj _ (ih ▸ e)).elim

/-- On one-port blocks two slots omit the port edge. The congruence for
    the number of edges pays for both omissions. -/
theorem one_port_slots {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) (t : V → ℕ) (ht : t u ≤ 1) (hz : ∀ x, x ≠ u → t x = 0)
    (residue : G.edgeFinset.card % 3 = 1)
    (M : G.Subgraph) (hm : IsUniquelyRestricted M) (large : G.edgeFinset.card ≤ 6 * M.edgeSet.ncard) :
    ∃ L : Fin 6 → G.Subgraph, (∀ i, IsUniquelyRestricted (L i)) ∧
      G.edgeFinset.card ≤ ∑ i, (L i).edgeSet.ncard ∧
      ∀ x, 2 * t x ≤ {i : Fin 6 | x ∉ (L i).verts}.ncard := by
  classical
  obtain ⟨A,ha,hfree,loss⟩ := free_port M hm u
  let L (i : Fin 6) := if i.val < 2 then A else M
  refine ⟨L, fun i => by dsimp [L]; split <;> assumption, ?_, ?_⟩
  · simp [L, Fin.sum_univ_succ]
    omega
  · intro x
    by_cases eq : x = u
    · subst x
      have sub : ({0,1} : Set (Fin 6)) ⊆ {i : Fin 6 | u ∉ (L i).verts} := by
        intro i hi
        rcases (show i = 0 ∨ i = 1 from hi) with rfl | rfl <;> simpa [L] using hfree
      have count := Set.ncard_le_ncard sub
      rw [Set.ncard_pair (by decide)] at count
      omega
    · simp [hz x eq]

end BridgeMatching

namespace BridgeMatching
open SimpleGraph OMA.S_arxiv_1805_00840 OMA.R_arxiv_1805_00840_R1

/-- The exceptional slot statement follows from the unweighted published bound
    on cubic graphs and on graphs with a single degree-two vertex. -/
theorem exceptional_from_unweighted
    (base : ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.Connected → (∀ e ∈ G.edgeSet, ¬ G.IsBridge e) → (∀ x, 2 ≤ G.degree x ∧ G.degree x ≤ 3) →
      IsEmpty (G ≃g completeBipartiteGraph (Fin 3) (Fin 3)) →
      (∀ u v, G.degree u = 2 → G.degree v = 2 → u = v) →
      ∃ M : G.Subgraph, IsUniquelyRestricted M ∧ G.edgeFinset.card ≤ 6 * M.edgeSet.ncard) :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
    (∀ e ∈ G.edgeSet, ¬ G.IsBridge e) → (∀ x, G.degree x ≤ 3) →
    IsEmpty (G ≃g completeBipartiteGraph (Fin 3) (Fin 3)) →
    ((∃ x, G.degree x < 2) ∨ ∀ u v, G.degree u = 2 → G.degree v = 2 → u = v) →
    ∀ t : V → ℕ, (∀ x, G.degree x + t x ≤ 3) →
    ∃ L : Fin 6 → G.Subgraph, (∀ i, IsUniquelyRestricted (L i)) ∧
      G.edgeFinset.card ≤ ∑ i, (L i).edgeSet.ncard ∧
      ∀ x, 2 * t x ≤ {i : Fin 6 | x ∉ (L i).verts}.ncard := by
  intro V _ G _ hc hb hd hk hex t ht
  classical
  by_cases hmin : ∀ v, 2 ≤ G.degree v
  · have hone : ∀ u v, G.degree u = 2 → G.degree v = 2 → u = v :=
      hex.resolve_left (fun ⟨x,hx⟩ => (hmin x).not_gt hx)
    obtain ⟨M,hm,hlarge⟩ := base V G hc hb (fun x => ⟨hmin x,hd x⟩) hk hone
    by_cases hport : ∃ x, G.degree x = 2
    · obtain ⟨u,hu⟩ := hport
      have singleton : {x | G.degree x = 2} = {u} :=
        Set.ext (fun x => ⟨fun hx => hone x u hx hu, fun h => (show x = u from h) ▸ hu⟩)
      have counts := deficit_identity G (fun x => ⟨hmin x,hd x⟩)
      rw [singleton, Set.ncard_singleton] at counts
      apply one_port_slots G u t _ _ (by omega) M hm hlarge
      · have := ht u
        omega
      · intro x hxu
        have hn : G.degree x ≠ 2 := fun h => hxu (hone x u h hu)
        have := hmin x
        have := ht x
        omega
    · refine ⟨fun _ => M, fun _ => hm, ?_, ?_⟩
      · simpa using hlarge
      · intro x
        have n2 : G.degree x ≠ 2 := fun h => hport ⟨x,h⟩
        have := ht x
        have := hmin x
        have hz : t x = 0 := by omega
        simp [hz]
  · obtain ⟨u,hu⟩ : ∃ x, G.degree x < 2 := by simpa using hmin
    have all_eq := small_degree_singleton G hc hb u hu
    have no_edges : G.edgeFinset = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      induction e using Sym2.inductionOn with
      | _ x y =>
        have ed : G.Adj x y := G.mem_edgeFinset.mp he
        exact ed.ne ((all_eq x).trans (all_eq y).symm)
    refine ⟨fun _ => ⊥, fun _ => empty_ur, by simp [no_edges], ?_⟩
    intro x
    have := ht x
    have hslots : {i : Fin 6 | x ∉ (⊥ : G.Subgraph).verts} = Set.univ := by ext; simp
    rw [hslots]
    simp only [Set.ncard_univ, Nat.card_fin]
    omega

end BridgeMatching

namespace OMA.R_arxiv_1805_00840_R1
open SimpleGraph OMA.S_arxiv_1805_00840

end OMA.R_arxiv_1805_00840_R1

namespace BridgeCubic
open SimpleGraph OMA.S_arxiv_1805_00840 OMA.R_arxiv_1805_00840_R1 BridgeMatching
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem sparse_proper (hc : G.Connected) (hd : ∀ v, G.degree v ≤ 3)
    (s : Finset V) (hs : s.Nonempty) (hn : ∃ v, v ∉ s) :
    ∃ u ∈ s, ((G.neighborFinset u).filter (· ∈ s)).card ≤ 2 := by
  classical
  by_contra! h
  have sat {u : V} (hu : u ∈ s) : (G.neighborFinset u).filter (· ∈ s) = G.neighborFinset u := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset ..)
    have h1 := h u hu
    have h2 := hd u
    rw [← G.card_neighborFinset_eq_degree u] at h2
    omega
  obtain ⟨a, ha⟩ := hs
  have all_mem (v : V) : v ∈ s := by
    have path := (G.reachable_iff_reflTransGen a v).1 (hc.preconnected a v)
    induction path with
    | refl => exact ha
    | tail _ e ih =>
      have he := (G.mem_neighborFinset ..).2 e
      rw [← sat ih] at he
      exact (Finset.mem_filter.mp he).2
  obtain ⟨v,hv⟩ := hn
  exact hv (all_mem v)

theorem split_proper (hc : G.Connected) (hd : ∀ v, G.degree v ≤ 3)
    (M : G.Subgraph) (hM : M.IsMatching) (hn : ∃ v, v ∉ M.verts) : ∃ A B : G.Subgraph, IsUniquelyRestricted A ∧ IsUniquelyRestricted B ∧ Disjoint A.verts B.verts ∧ A ⊔ B = M := by
  classical
  by_cases hne : M.verts.Nonempty
  · obtain ⟨u, hu, hd2⟩ := sparse_proper hc hd M.verts.toFinset
      (Set.toFinset_nonempty.mpr hne) (by simpa using hn)
    have hum : u ∈ M.verts := Set.mem_toFinset.mp hu
    obtain ⟨v, e, _⟩ := hM hum
    let S : Set V := {x | x ∈ M.verts ∧ x ≠ u ∧ x ≠ v}
    have closed {x y : V} (hx : x ∈ S) (hxy : M.Adj x y) : y ∈ S := by
      refine ⟨hxy.snd_mem, ?_, ?_⟩
      · rintro rfl
        exact hx.2.2 (hM.eq_of_adj_left hxy.symm e)
      · rintro rfl
        exact hx.2.1 (hM.eq_of_adj_left hxy.symm e.symm)
    have hm' := matching_induce_closed hM (s := S) (fun _ hx => hx.1) @closed
    apply split_insert hM e _ (split_proper hc hd (M.induce S) hm' ⟨u, fun h => h.2.1 rfl⟩)
    intro x hx y hy hux huy hxv hyv
    exact unique_other_neighbor (Set.mem_toFinset.mpr e.snd_mem) (M.adj_sub e) hd2
      (Set.mem_toFinset.mpr hx) (Set.mem_toFinset.mpr hy) hux huy hxv hyv
  · have hbot : M = ⊥ := by
      apply bot_unique
      exact ⟨fun x hx => (hne ⟨x,hx⟩).elim, fun x _ h => (hne ⟨x,h.fst_mem⟩).elim⟩
    exact ⟨⊥, ⊥, empty_ur, empty_ur, disjoint_bot_left, by simp [hbot]⟩
termination_by M.verts.ncard
decreasing_by
  refine Set.ncard_lt_ncard ?_ (Set.toFinite _)
  exact Set.ssubset_iff_subset_ne.mpr ⟨fun _ h => h.1, fun he =>
    have h : u ∈ S := (congrArg (fun t : Set V => u ∈ t) he).mpr hum
    h.2.1 rfl⟩


theorem drop_one (M : G.Subgraph) (hm : M.IsMatching) (x : V) :
    ∃ A : G.Subgraph, A.IsMatching ∧ x ∉ A.verts ∧ M.edgeSet.ncard ≤ A.edgeSet.ncard + 1 := by
  classical
  by_cases hx : x ∈ M.verts
  · obtain ⟨y,e,_⟩ := hm hx
    let S : Set V := {z | z ∈ M.verts ∧ z ≠ x ∧ z ≠ y}
    let A := M.induce S
    have closed {z w : V} (hz : z ∈ S) (h : M.Adj z w) : w ∈ S := by
      refine ⟨h.snd_mem,?_,?_⟩
      · rintro rfl
        exact hz.2.2 (hm.eq_of_adj_left h.symm e)
      · rintro rfl
        exact hz.2.1 (hm.eq_of_adj_left h.symm e.symm)
    have ma : A.IsMatching := matching_induce_closed hm (fun _ hz => hz.1) @closed
    refine ⟨A,ma,fun h => h.2.1 rfl,?_⟩
    have sub : M.verts ⊆ A.verts ∪ {x,y} := by
      intro z hz
      change (z ∈ M.verts ∧ z ≠ x ∧ z ≠ y) ∨ z = x ∨ z = y
      tauto
    have card := (Set.ncard_le_ncard sub).trans (Set.ncard_union_le _ _)
    rw [Set.ncard_pair e.ne] at card
    have h1 := matching_size M hm
    have h2 := matching_size A ma
    omega
  · exact ⟨M,hm,hx,by omega⟩

theorem cubic_four (hc : G.Connected) (hd : ∀ v, G.degree v = 3)
    (hb : ∀ e ∈ G.edgeSet, ¬G.IsBridge e) (four : 4 ∣ Fintype.card V) :
    ∃ M : G.Subgraph, IsUniquelyRestricted M ∧ G.edgeFinset.card ≤ 6 * M.edgeSet.ncard := by
  classical
  obtain ⟨P,hP⟩ := bridgeless_cubic_perfect G hd hb
  obtain ⟨x⟩ := hc.nonempty
  obtain ⟨A,hA,miss,loss⟩ := drop_one P hP.1 x
  obtain ⟨L,R,hL,hR,_,eq⟩ := split_proper hc (fun x => (hd x).le) A hA ⟨x,miss⟩
  have pe := matching_size P hP.1
  rw [hP.2.verts_eq_univ, Set.ncard_univ, Nat.card_eq_fintype_card] at pe
  have edges := G.sum_degrees_eq_twice_card_edges
  simp only [hd,Finset.sum_const,Finset.card_univ,smul_eq_mul] at edges
  have split := Set.ncard_union_le L.edgeSet R.edgeSet
  rw [← Subgraph.edgeSet_sup,eq] at split
  obtain ⟨k,hk⟩ := four
  by_cases h : L.edgeSet.ncard ≤ R.edgeSet.ncard
  · exact ⟨R,hR,by omega⟩
  · exact ⟨L,hL,by omega⟩

end BridgeCubic

namespace BridgePortHelpers
open SimpleGraph
variable {V : Type*} [Finite V] {G : SimpleGraph V}
theorem lift_in_side {s : Set V} (M : (G.induce s).Subgraph) : (M.map (Embedding.induce s).toHom).verts ⊆ s := by
  rintro x ⟨y,_,rfl⟩
  exact y.2

theorem lift_size {s : Set V} (M : (G.induce s).Subgraph) :
    (M.map (Embedding.induce s).toHom).edgeSet.ncard = M.edgeSet.ncard := by
  rw [Subgraph.edgeSet_map]
  exact Set.ncard_image_of_injective _ (Sym2.map.injective (Embedding.induce (G := G) s).injective)

theorem sup_size (A B : G.Subgraph) (hd : Disjoint A.verts B.verts) :
    (A ⊔ B).edgeSet.ncard = A.edgeSet.ncard + B.edgeSet.ncard := by
  rw [Subgraph.edgeSet_sup]
  refine Set.ncard_union_eq ?_ (Set.toFinite _) (Set.toFinite _)
  apply Set.disjoint_left.mpr
  intro e ea eb
  obtain ⟨x,y⟩ := e
  exact Set.disjoint_left.mp hd (A.edge_vert ea) (B.edge_vert eb)


end BridgePortHelpers

namespace BridgePort
open SimpleGraph BridgeMatching OMA.S_arxiv_1805_00840
variable {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem odd_internal_cut (hb : ∀ e ∈ G.edgeSet, ¬G.IsBridge e)
    (s : Set V) (hs : Odd s.ncard) (hd : ∀ x : s, G.degree x = 3) :
    3 ≤ Nat.card (Σ x : s, {y : G.neighborSet x // (y : V) ∉ s}) := by
  classical
  have h := cut_handshake G s
  simp only [hd,Finset.sum_const,Finset.card_univ,smul_eq_mul] at h
  have hc : s.ncard = Fintype.card s := by rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  obtain ⟨k,hk⟩ := hs
  have := cut_not_one G hb s
  omega


end BridgePort

namespace BridgePort
open SimpleGraph BridgeMatching
variable {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]


/-- An even region of cubic vertices with at most five incoming edges has a perfect matching. -/
theorem perfect_small_cut (W : Set V) (even : Even W.ncard) (hd : ∀ x : W, G.degree x = 3)
    (hb : ∀ e ∈ G.edgeSet, ¬G.IsBridge e) (small : Nat.card ((Σ v : ↥(Wᶜ), {y : G.neighborSet v // (y : V) ∈ W})) ≤ 5) :
    ∃ P : (G.induce W).Subgraph, P.IsPerfectMatching := by
  classical
  let B := G.induce W
  apply tutte.mpr
  intro U
  let H := (⊤ : B.Subgraph).deleteVerts U
  let emb (x : H.verts) : V := x.1.1
  have embInj : Function.Injective emb := fun _ _ e => Subtype.ext (Subtype.ext e)
  let S (c : H.coe.oddComponents) := emb '' c.1.supp
  let D (c : H.coe.oddComponents) := Σ x : S c, {y : G.neighborSet x // (y : V) ∉ S c}
  have win (c : H.coe.oddComponents) : S c ⊆ W := by
    rintro _ ⟨x,_,rfl⟩
    exact x.1.2
  have lower (c : H.coe.oddComponents) : 3 ≤ Nat.card (D c) := by
    apply odd_internal_cut hb
    · rw [show (S c).ncard = c.1.supp.ncard from Set.ncard_image_of_injective _ embInj]
      exact c.2
    · exact fun x => hd ⟨x,win c x.2⟩
  have endsIn (c : H.coe.oddComponents) (d : D c) (hy : (d.2.1 : V) ∈ W) :
      (⟨d.2.1,hy⟩ : W) ∈ U := by
    by_contra hout
    let w : H.verts := ⟨⟨d.2.1,hy⟩,Set.mem_univ _,hout⟩
    obtain ⟨v,hv,eq⟩ := d.1.2
    have edge : H.coe.Adj v w := by
      change v.1 ∈ H.verts ∧ w.1 ∈ H.verts ∧ G.Adj (emb v) (d.2.1 : V)
      exact ⟨v.2,w.2,eq.symm ▸ d.2.1.2⟩
    exact d.2.2 ⟨w,c.1.mem_supp_of_adj_mem_supp hv edge,rfl⟩
  let Z := (Σ x : U, G.neighborSet x.1.1) ⊕ (Σ v : ↥(Wᶜ), {y : G.neighborSet v // (y : V) ∈ W})
  let f (d : Σ c : H.coe.oddComponents, D c) : Z :=
    if h : (d.2.2.1 : V) ∈ W then
      Sum.inl ⟨⟨⟨d.2.2.1,h⟩,endsIn d.1 d.2 h⟩,⟨d.2.1,d.2.2.1.2.symm⟩⟩
    else Sum.inr ⟨⟨d.2.2.1,h⟩,⟨⟨d.2.1,d.2.2.1.2.symm⟩,win d.1 d.2.1.2⟩⟩
  let read : Z → V × V := Sum.elim (fun z => (z.2.1,z.1.1.1)) (fun z => (z.2.1.1,z.1.1))
  have val (d : Σ c : H.coe.oddComponents, D c) : read (f d) = (d.2.1.1,d.2.2.1.1) := by
    simp only [f]
    split <;> rfl
  have inj : Function.Injective f := by
    rintro ⟨c,d⟩ ⟨c',d'⟩ he
    have same := (val ⟨c,d⟩).symm.trans ((congrArg read he).trans (val ⟨c',d'⟩))
    obtain ⟨hx,hy⟩ := Prod.mk.inj same
    obtain ⟨v,hv,ev⟩ := d.1.2
    obtain ⟨w,hw,ew⟩ := d'.1.2
    have vw := embInj (ev.trans (hx.trans ew.symm))
    have cc : c = c' := Subtype.ext ((c.1.mem_supp_iff v).mp hv |>.symm.trans
      ((c'.1.mem_supp_iff v).mp (vw ▸ hw)))
    subst c'
    have ed := cut_pair_injective G (S c) (Prod.ext hx hy)
    cases ed
    rfl
  have cap := Nat.card_le_card_of_injective f inj
  change Nat.card (Σ c, D c) ≤ Nat.card ((Σ x : U, G.neighborSet x.1.1) ⊕ (Σ v : ↥(Wᶜ), {y : G.neighborSet v // (y : V) ∈ W})) at cap
  rw [Nat.card_sum,Nat.card_sigma,Nat.card_sigma] at cap
  have valU (v : U) : Nat.card (G.neighborSet v.1.1) = 3 :=
    Nat.card_eq_fintype_card.trans ((card_neighborSet_eq_degree _ _).trans (hd v.1))
  simp only [valU,Finset.sum_const,Finset.card_univ,smul_eq_mul] at cap
  have lo := Finset.sum_le_sum (s := Finset.univ) (fun c _ => lower c)
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at lo
  have parity := odd_ncard_oddComponents H.coe
  have del : Nat.card H.verts = W.ncard - U.ncard := by
    rw [Nat.card_coe_set_eq]
    change ((Set.univ : Set W) \ U).ncard = _
    rw [← Set.compl_eq_univ_sdiff,Set.ncard_compl, Nat.card_coe_set_eq]
  rw [del] at parity
  have sub : U.ncard ≤ W.ncard := by
    simpa only [Set.ncard_univ,Nat.card_coe_set_eq] using (Set.ncard_le_ncard (Set.subset_univ U))
  change ¬ U.ncard < H.coe.oddComponents.ncard
  rw [Set.fintypeCard_eq_ncard] at cap lo
  simp only [Nat.odd_iff] at parity
  obtain ⟨k,hk⟩ := even
  omega

end BridgePort

namespace BridgePort
open SimpleGraph BridgePortHelpers BridgeMatching OMA.S_arxiv_1805_00840
variable {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem add_outside_star (hc : G.Connected) (hd : ∀ x, G.degree x ≤ 3)
    (W : Set V) {p u : V} (e : G.Adj p u) (miss : p ∉ W)
    (outside : ∀ x ∈ W, ¬G.Adj p x)
    (P : (G.induce W).Subgraph) (hp : P.IsPerfectMatching) :
    ∃ M : G.Subgraph, IsUniquelyRestricted M ∧ W.ncard + 4 ≤ 4 * M.edgeSet.ncard := by
  classical
  let A := P.map (Embedding.induce W).toHom
  have ha : A.IsMatching := hp.1.map _ (Embedding.induce (G := G) W).injective
  obtain ⟨L,R,hL,hR,_,eq⟩ := BridgeCubic.split_proper hc hd A ha ⟨p,fun h => miss (lift_in_side P h)⟩
  have pe := matching_size P hp.1
  rw [hp.2.verts_eq_univ, Set.ncard_univ, Nat.card_coe_set_eq] at pe
  have sizes := Set.ncard_union_le L.edgeSet R.edgeSet
  rw [← Subgraph.edgeSet_sup,eq,lift_size] at sizes
  have extend (T : G.Subgraph) (ht : IsUniquelyRestricted T) (leA : T ≤ A)
      (large : W.ncard ≤ 4*T.edgeSet.ncard) :
      ∃ M : G.Subgraph, IsUniquelyRestricted M ∧ W.ncard + 4 ≤ 4*M.edgeSet.ncard := by
    have cover : T.verts ⊆ W := fun _ h => lift_in_side P (leA.1 h)
    have mp : p ∉ T.verts := fun h => miss (cover h)
    have mu : u ∉ T.verts := fun h => outside u (cover h) e
    have dis : Disjoint T.verts (G.subgraphOfAdj e).verts := by
      apply Set.disjoint_left.mpr
      intro z hz he
      rcases (show z = p ∨ z = u from he) with rfl | rfl <;> contradiction
    refine ⟨_,OMA.R_arxiv_1805_00840_R1.uniquelyRestricted_add_forced ht e mp mu
      (fun x hx => outside x (cover hx)),?_⟩
    rw [sup_size _ _ dis,edgeSet_subgraphOfAdj,Set.ncard_singleton]
    omega
  by_cases h : L.edgeSet.ncard ≤ R.edgeSet.ncard
  · exact extend R hR (eq ▸ le_sup_right) (by omega)
  · exact extend L hL (eq ▸ le_sup_left) (by omega)

theorem cut_cap (d : ∀ x, G.degree x ≤ 3) (D : Set V) :
    Nat.card ((Σ v : ↥(Dᶜᶜ), {y : G.neighborSet v // (y : V) ∈ Dᶜ})) + 2 * (G.induce D).edgeSet.ncard ≤ 3 * D.ncard := by
  classical
  have cut := cut_handshake G D
  have inc : Nat.card ((Σ v : ↥(Dᶜᶜ), {y : G.neighborSet v // (y : V) ∈ Dᶜ})) =
      Nat.card (Σ v : D, {y : G.neighborSet v // (y : V) ∉ D}) := by
    exact Nat.card_congr
      { toFun := fun ⟨v,y⟩ => ⟨⟨v.1,not_not.mp v.2⟩,y⟩
        invFun := fun ⟨v,y⟩ => ⟨⟨v.1,not_not.mpr v.2⟩,y⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have cap := Finset.sum_le_sum (s := Finset.univ) (fun x _ => d (x : D).1)
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,Set.fintypeCard_eq_ncard] at cap
  rw [edgeFinset_card,Set.fintypeCard_eq_ncard] at cut
  omega

theorem star_cost (p : V) (d : ∀ x, G.degree x ≤ 3)
    (D : Set V) (inside : p ∈ D) (neighbors : G.neighborSet p ⊆ D) :
    Nat.card ((Σ v : ↥(Dᶜᶜ), {y : G.neighborSet v // (y : V) ∈ Dᶜ})) + 2 * G.degree p ≤ 3 * D.ncard := by
  classical
  have cut := cut_cap d D
  have deg := (G.induce D).degree_le_card_edgeFinset (⟨p,inside⟩ : D)
  rw [degree_induce_of_neighborSet_subset neighbors] at deg
  change G.degree p ≤ (G.induce D).edgeFinset.card at deg
  rw [edgeFinset_card,Set.fintypeCard_eq_ncard] at deg
  omega

/-- Delete the degree-two vertex and its two neighbors. The remaining even
region has a perfect matching. One half of its split, plus an edge at the
deleted vertex, gives the unweighted lower bound. -/
theorem one_port_bound (hc : G.Connected) (p : V) (hp : G.degree p = 2)
    (hd : ∀ x, x ≠ p → G.degree x = 3) (hb : ∀ e ∈ G.edgeSet, ¬G.IsBridge e) :
    ∃ M : G.Subgraph, IsUniquelyRestricted M ∧ G.edgeFinset.card ≤ 6 * M.edgeSet.ncard := by
  classical
  let D : Set V := insert p (G.neighborSet p)
  have din : p ∈ D := Set.mem_insert _ _
  have dn : G.neighborSet p ⊆ D := Set.subset_insert _ _
  have dcard : D.ncard = 3 := by
    have hn : (G.neighborSet p).ncard = 2 := by
      rw [← Set.fintypeCard_eq_ncard,card_neighborSet_eq_degree,hp]
    rw [show D = insert p (G.neighborSet p) from rfl, Set.ncard_insert_of_notMem,hn]
    exact G.irrefl
  have deg (x : V) : 2 ≤ G.degree x ∧ G.degree x ≤ 3 := by
    by_cases e : x = p
    · subst x
      exact ⟨hp.ge,hp.le.trans (by decide)⟩
    · rw [hd x e]
      decide
  have edges := deficit_identity G deg
  have sing : {v | G.degree v = 2} = {p} := by
    ext x
    by_cases e : x = p <;> simp [e,hp,hd]
  rw [sing,Set.ncard_singleton] at edges
  have total := Set.ncard_add_ncard_compl D
  rw [dcard,Nat.card_eq_fintype_card] at total
  have cost := star_cost p (fun x => (deg x).2) D din dn
  have even : Even Dᶜ.ncard := by
    rw [Nat.even_iff]
    omega
  obtain ⟨P,hP⟩ := perfect_small_cut Dᶜ even
    (fun x => hd x (fun e => x.2 (e ▸ din))) hb (by omega)
  have nonempty : (G.neighborFinset p).Nonempty := Finset.card_pos.mp (by rw [card_neighborFinset_eq_degree,hp]; decide)
  obtain ⟨u,hu⟩ := nonempty
  obtain ⟨M,hm,size⟩ := add_outside_star hc (fun x => (deg x).2) Dᶜ
    ((G.mem_neighborFinset p u).mp hu) (fun h => h din) (fun _ h adj => h (dn adj)) P hP
  exact ⟨M,hm,by omega⟩

end BridgePort

namespace BridgePort
open SimpleGraph BridgeMatching OMA.S_arxiv_1805_00840
variable {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/- The closed neighborhood of a vertex on a triangle contains four vertices
and at least four edges. At most four edges cross out, so its even complement
has a perfect matching by the small-cut lemma. -/
set_option maxHeartbeats 1200000 in
theorem cubic_triangle (hc : G.Connected) (hd : ∀ x, G.degree x = 3)
    (hb : ∀ e ∈ G.edgeSet, ¬G.IsBridge e) {p u v : V}
    (pu : G.Adj p u) (pv : G.Adj p v) (uv : G.Adj u v) :
    ∃ M : G.Subgraph, IsUniquelyRestricted M ∧ G.edgeFinset.card ≤ 6 * M.edgeSet.ncard := by
  classical
  let D : Set V := insert p (G.neighborSet p)
  letI : Fintype D := Subtype.fintype (· ∈ D)
  have din : p ∈ D := Set.mem_insert _ _
  have dn : G.neighborSet p ⊆ D := Set.subset_insert _ _
  have dcard : D.ncard = 4 := by
    have hn : (G.neighborSet p).ncard = 3 := by
      rw [← Set.fintypeCard_eq_ncard,card_neighborSet_eq_degree,hd]
    rw [show D = insert p (G.neighborSet p) from rfl, Set.ncard_insert_of_notMem,hn]
    exact G.irrefl
  let B := G.induce D
  let z : D := ⟨p,din⟩
  let x : D := ⟨u,dn pu⟩
  let y : D := ⟨v,dn pv⟩
  have inside : s(x,y) ∈ B.edgeFinset := B.mem_edgeFinset.mpr uv
  have apart : s(x,y) ∉ B.incidenceFinset z := by
    rw [B.incidenceFinset_eq_filter]
    intro h
    rcases Sym2.mem_iff.mp (Finset.mem_filter.mp h).2 with h | h
    · exact pu.ne (congrArg Subtype.val h)
    · exact pv.ne (congrArg Subtype.val h)
  have strict := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨B.incidenceFinset_subset z,fun e => apart (e.symm ▸ inside)⟩)
  rw [card_incidenceFinset_eq_degree] at strict
  have db : B.degree z = G.degree p := by
    convert! degree_induce_of_neighborSet_subset (v := z) dn using 1
  have inside_count : 3 < B.edgeFinset.card := (db.trans (hd p)).symm.trans_lt strict
  rw [edgeFinset_card,Set.fintypeCard_eq_ncard] at inside_count
  have cost := cut_cap (fun x => (hd x).le) D
  have edges := G.sum_degrees_eq_twice_card_edges
  simp only [hd,Finset.sum_const,Finset.card_univ,smul_eq_mul] at edges
  have total := Set.ncard_add_ncard_compl D
  rw [dcard,Nat.card_eq_fintype_card] at total
  have even : Even Dᶜ.ncard := by rw [Nat.even_iff]; omega
  change 3 < (G.induce D).edgeSet.ncard at inside_count
  obtain ⟨P,hP⟩ := perfect_small_cut Dᶜ even (fun x => hd x) hb (by omega)
  obtain ⟨M,hm,size⟩ := add_outside_star hc (fun x => (hd x).le) Dᶜ pu
    (fun h => h din) (fun _ h adj => h (dn adj)) P hP
  exact ⟨M,hm,by omega⟩

end BridgePort

namespace OMA.R_arxiv_1805_00840_R1
open SimpleGraph OMA.S_arxiv_1805_00840

/-- The remaining triangle-free cubic case of the published unweighted bound. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → (∀ e ∈ G.edgeSet, ¬G.IsBridge e) → (∀ x, G.degree x = 3) →
    IsEmpty (G ≃g completeBipartiteGraph (Fin 3) (Fin 3)) →
    Fintype.card V % 4 = 2 → (∀ p u v, G.Adj p u → G.Adj p v → ¬G.Adj u v) →
    ∃ M : G.Subgraph, IsUniquelyRestricted M ∧ G.edgeFinset.card ≤ 6 * M.edgeSet.ncard

theorem unweighted_from_residual (residual : H1) :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.Connected → (∀ e ∈ G.edgeSet, ¬ G.IsBridge e) → (∀ x, 2 ≤ G.degree x ∧ G.degree x ≤ 3) →
      IsEmpty (G ≃g completeBipartiteGraph (Fin 3) (Fin 3)) →
      (∀ u v, G.degree u = 2 → G.degree v = 2 → u = v) →
      ∃ M : G.Subgraph, IsUniquelyRestricted M ∧ G.edgeFinset.card ≤ 6 * M.edgeSet.ncard := by
  intro V _ G _ hc hb hd hk uniquePort
  classical
  by_cases port : ∃ p, G.degree p = 2
  · obtain ⟨p,hp⟩ := port
    apply BridgePort.one_port_bound hc p hp _ hb
    intro x hx
    have neq : G.degree x ≠ 2 := fun h => hx (uniquePort x p h hp)
    have := hd x
    omega
  · have cubic (x : V) : G.degree x = 3 := by
      have ne : G.degree x ≠ 2 := fun h => port ⟨x,h⟩
      have := hd x
      omega
    by_cases mult : 4 ∣ Fintype.card V
    · exact BridgeCubic.cubic_four hc cubic hb mult
    by_cases triangle : ∃ p u v, G.Adj p u ∧ G.Adj p v ∧ G.Adj u v
    · obtain ⟨p,u,v,pu,pv,uv⟩ := triangle
      exact BridgePort.cubic_triangle hc cubic hb pu pv uv
    have edges := G.sum_degrees_eq_twice_card_edges
    simp only [cubic,Finset.sum_const,Finset.card_univ,smul_eq_mul] at edges
    apply residual V G hc hb cubic hk (by omega)
    exact fun p u v pu pv uv => triangle ⟨p,u,v,pu,pv,uv⟩


/-- Assemble the two sides of one bridge, keeping enough slots free for future joins. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
    (∀ x, G.degree x ≤ 3) → IsEmpty (G ≃g completeBipartiteGraph (Fin 3) (Fin 3)) →
    ∀ e ∈ G.edgeSet, G.IsBridge e →
    (∀ c : (G.deleteEdges {e}).ConnectedComponent,
      let B := G.induce c.supp
      ∀ [Fintype c.supp] [DecidableRel B.Adj], Fintype.card c.supp < Fintype.card V →
      B.Connected → (∀ x, B.degree x ≤ 3) →
      IsEmpty (B ≃g completeBipartiteGraph (Fin 3) (Fin 3)) →
      ∀ t : c.supp → ℕ, (∀ x, B.degree x + t x ≤ 3) →
      ∃ L : Fin 6 → B.Subgraph, (∀ i, IsUniquelyRestricted (L i)) ∧
        B.edgeFinset.card + {f ∈ B.edgeSet | B.IsBridge f}.ncard ≤ ∑ i, (L i).edgeSet.ncard ∧
        ∀ x, 2 * t x ≤ {i : Fin 6 | x ∉ (L i).verts}.ncard) →
    ∀ t : V → ℕ, (∀ x, G.degree x + t x ≤ 3) →
    ∃ L : Fin 6 → G.Subgraph, (∀ i, IsUniquelyRestricted (L i)) ∧
      G.edgeFinset.card + {f ∈ G.edgeSet | G.IsBridge f}.ncard ≤ ∑ i, (L i).edgeSet.ncard ∧
      ∀ x, 2 * t x ≤ {i : Fin 6 | x ∉ (L i).verts}.ncard

theorem certificates_by_order (hbase : H1) (hglue : H2) (n : ℕ) :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj], Fintype.card V = n →
    G.Connected → (∀ x, G.degree x ≤ 3) → IsEmpty (G ≃g completeBipartiteGraph (Fin 3) (Fin 3)) →
    ∀ t : V → ℕ, (∀ x, G.degree x + t x ≤ 3) →
    ∃ L : Fin 6 → G.Subgraph, (∀ i, IsUniquelyRestricted (L i)) ∧
      G.edgeFinset.card + {f ∈ G.edgeSet | G.IsBridge f}.ncard ≤ ∑ i, (L i).edgeSet.ncard ∧
      ∀ x, 2 * t x ≤ {i : Fin 6 | x ∉ (L i).verts}.ncard := by
  classical
  have h1 := BridgeMatching.ordinary_block_bound
  have h2 := BridgeMatching.exceptional_from_unweighted (unweighted_from_residual hbase)
  have h3 := hglue
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ G _ horder hc hd hk t ht
    by_cases hb : ∃ e ∈ G.edgeSet, G.IsBridge e
    · obtain ⟨e, he, heb⟩ := hb
      apply h3 V G hc hd hk e he heb _ t ht
      intro c
      dsimp only
      intro _ _ hlt
      exact ih _ (hlt.trans_le horder.le) c.supp (G.induce c.supp) rfl
    · have noBridge : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e := by simpa using hb
      have hempty : {e ∈ G.edgeSet | G.IsBridge e} = ∅ := by
        exact Set.eq_empty_iff_forall_notMem.mpr (fun e h => noBridge e h.1 h.2)
      simp only [hempty, Set.ncard_empty, Nat.add_zero]
      by_cases hmin : ∀ x, 2 ≤ G.degree x
      · by_cases htwo : ∃ u v, u ≠ v ∧ G.degree u = 2 ∧ G.degree v = 2
        · obtain ⟨M, hm, hsize⟩ := h1 V G hc noBridge (fun x => ⟨hmin x, hd x⟩) htwo
          obtain ⟨u, _, _, hu, _⟩ := htwo
          obtain ⟨L, hL, hs, hf⟩ := six_slots_from_matching hc hd ⟨u, by omega⟩ M hm hsize
          refine ⟨L, hL, hs, fun x => ?_⟩
          have := ht x
          have := hmin x
          have := hf x
          omega
        · apply h2 V G hc noBridge hd hk (.inr ?_) t ht
          intro u v hu hv
          by_contra hne
          exact htwo ⟨u,v,hne,hu,hv⟩
      · apply h2 V G hc noBridge hd hk (.inl ?_) t ht
        simpa using hmin

theorem main : H1 → H2 → type_of% @OMA.S_arxiv_1805_00840.main := by
  intro h1 h2 V _ G _ hc hd hk
  classical
  obtain ⟨L, hL, hs, _⟩ := certificates_by_order h1 h2 _ V G rfl hc hd hk (fun _ => 0)
    (by simpa using hd)
  let f (i : Fin 6) := (L i).edgeSet.ncard
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ f (by simp)
  refine ⟨L i, hL i, hs.trans ?_⟩
  exact (Finset.sum_le_sum (fun j hj => hi j hj)).trans (by simp [f])

end OMA.R_arxiv_1805_00840_R1
