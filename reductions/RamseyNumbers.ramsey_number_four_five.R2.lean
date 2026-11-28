import FormalConjectures.Wikipedia.RamseyNumbers
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# A four-page book reduction for R(4,5) = 25

Fix an edge with four common neighbors and delete these six vertices.
The two ends give disjoint cones over the remaining 19 vertices.

Credit: @yuka30240
-/
open RamseyNumbers SimpleGraph

namespace OMA.R_RamseyNumbers_ramsey_number_four_five_R2

-- Angeltveit and McKay, R(5,5) ≤ 48, Table 1 (arXiv:1703.08768).
-- In every edge-count row,
-- the minimum number of triangles exceeds the edge count.
def H1 : Prop :=
  ∀ (G : SimpleGraph (Fin 24)) [DecidableRel G.Adj],
    G.CliqueFree 4 → Gᶜ.CliqueFree 5 →
    (G.cliqueFinset 2).card < (G.cliqueFinset 3).card

-- N i contains the neighbors in the core of the i-th independent page vertex.
-- A cone attaches one end of the book spine. It must hit every independent four
-- and its neighbors, including the four pages, must induce a triangle-free graph.
def H2 : Prop :=
  ∀ (C : SimpleGraph (Fin 19)) (N : Fin 4 → Finset (Fin 19)), C.CliqueFree 4 →
    (∀ i t, C.IsNClique 3 t → ¬ t ⊆ N i) →
    (∀ t : Finset (Fin 19), Cᶜ.IsClique t →
      t.card + (Finset.univ.filter (fun i => Disjoint t (N i))).card ≤ 4) →
    let cone := fun X : Finset (Fin 19) =>
      (∀ t, C.IsNClique 3 t → ¬ t ⊆ X) ∧
      (∀ i, C.IsIndepSet (↑(X ∩ N i) : Set (Fin 19))) ∧
      (∀ t, Cᶜ.IsNClique 4 t → ¬ Disjoint t X)
    ∀ X Y, cone X → cone Y → ¬ Disjoint X Y

-- The 24-vertex certificate and its pruning lemma are from TheWaler's R1.
-- A clique search branches on its least vertex, retaining only larger neighbours.
lemma exclude_search {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ)
    (cert : (Nat.rec (motive := fun _ => List (Fin n) → Bool) (fun _ => true)
      (fun j rec vs => if vs.length < j+1 then false else vs.any fun v => rec (vs.filter fun w => decide (v < w ∧ G.Adj v w)))
      k (List.finRange n)) = false) : G.CliqueFree k := by
  let search := Nat.rec (motive := fun _ => List (Fin n) → Bool) (fun _ => true)
    (fun j rec vs => if vs.length < j+1 then false else vs.any fun v => rec (vs.filter fun w => decide (v < w ∧ G.Adj v w)))
  have found (j : ℕ) (vs : List (Fin n)) (s : Finset (Fin n)) (hs : G.IsNClique j s)
      (hsub : ∀ x ∈ s, x ∈ vs) : search j vs = true := by
    induction j generalizing vs s with
    | zero => rfl
    | succ j ih =>
      have hne : s.Nonempty := Finset.card_pos.mp (by rw [hs.card_eq]; omega)
      let v := s.min' hne
      have hv : v ∈ s := s.min'_mem hne
      have hlen : s.card ≤ vs.length :=
        (Finset.card_le_card (show s ⊆ vs.toFinset from fun x hx => List.mem_toFinset.mpr (hsub x hx))).trans
          (List.toFinset_card_le vs)
      have enough : ¬ vs.length < j+1 := by rw [hs.card_eq] at hlen; omega
      change (if vs.length < j+1 then false else vs.any _) = true
      rw [if_neg enough]
      apply List.any_eq_true.mpr
      refine ⟨v, hsub v hv, ih _ (s.erase v) (hs.erase_of_mem hv) ?_⟩
      intro w hw
      obtain ⟨hne, hw⟩ := Finset.mem_erase.mp hw
      exact List.mem_filter.mpr ⟨hsub w hw, decide_eq_true
        ⟨lt_of_le_of_ne (s.min'_le _ hw) hne.symm, hs.isClique hv hw hne.symm⟩⟩
  intro s hs
  have yes := found k (List.finRange n) s hs (by simp)
  change search k (List.finRange n) = false at cert
  simp_all

-- Data from McKay's combinatorial data collection (CC BY 4.0), r45_24.g6,
-- first graph of the McKay--Angeltveit collection, recoded as binary masks.
-- The size pruning and mask representation follow VinnyMo's proof in PR 1435.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 12000000 in
lemma twentyfour_fails : ¬ IsGraphRamsey 24 4 5 := by
  let rows : Array ℕ := #[0xd3ac00, 0xec5300, 0xe2e2c0, 0x39f030, 0x86dc28, 0xcd2518, 0x599684, 0xe7944, 0xbca0a2, 0xab1846, 0x616871, 0xb21691, 0x142ada, 0x2095ad, 0xad049e, 0x9a215d, 0x964669, 0x4d8a95, 0x5351b2, 0x42c3ea, 0x659949, 0x506f0e, 0x3e0467, 0x1cb37]
  let G : SimpleGraph (Fin 24) :=
    { Adj := fun u v => u ≠ v ∧ rows[min u.val v.val]!.testBit (max u.val v.val) = true
      symm := ⟨fun {u v} h => ⟨h.1.symm, by simpa only [min_comm v.val u.val, max_comm v.val u.val] using h.2⟩⟩
      loopless := ⟨fun u h => h.1 rfl⟩ }
  let : DecidableRel G.Adj := fun u v => inferInstanceAs
    (Decidable (u ≠ v ∧ rows[min u.val v.val]!.testBit (max u.val v.val) = true))
  intro h
  exact h G ⟨exclude_search G 4 (by dsimp +zetaDelta only; decide +kernel), exclude_search Gᶜ 5 (by dsimp +zetaDelta only; decide +kernel)⟩

-- Every triangle contains three edges. A strict excess of triangles forces
-- four distinct third vertices over a single edge.
private lemma book_of_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (more : (G.cliqueFinset 2).card < (G.cliqueFinset 3).card) :
    ∃ a b : Fin n, G.Adj a b ∧ ∃ pages : Fin 4 ↪ Fin n,
      ∀ i, G.Adj a (pages i) ∧ G.Adj b (pages i) := by
  classical
  let edges := G.cliqueFinset 2
  let triangles := G.cliqueFinset 3
  let incident := fun (t e : Finset (Fin n)) => e ⊆ t
  have three (t) (ht : t ∈ triangles) :
      3 ≤ (edges.bipartiteAbove incident t).card := by
    have tri := G.mem_cliqueFinset_iff.mp ht
    have sub : t.powersetCard 2 ⊆ edges.bipartiteAbove incident t := by
      intro e he
      obtain ⟨hin, hsize⟩ := Finset.mem_powersetCard.mp he
      exact Finset.mem_filter.mpr
        ⟨G.mem_cliqueFinset_iff.mpr ⟨tri.isClique.subset hin, hsize⟩, hin⟩
    simpa [Finset.card_powersetCard, tri.card_eq] using Finset.card_le_card sub
  have crowded : ∃ e ∈ edges, 4 ≤ (triangles.bipartiteBelow incident e).card := by
    by_contra! h
    have count := Finset.card_nsmul_le_card_nsmul incident three
      (fun e he => Nat.le_of_lt_succ (h e he))
    change triangles.card * 3 ≤ edges.card * 3 at count
    change edges.card < triangles.card at more
    omega
  obtain ⟨e, he, hcount⟩ := crowded
  have edge := G.mem_cliqueFinset_iff.mp he
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp edge.card_eq
  have adj : G.Adj a b := edge.isClique (by simp) (by simp) hab
  let common := G.neighborFinset a ∩ G.neighborFinset b
  have cover : triangles.bipartiteBelow incident {a, b} ⊆
      common.image (fun v => insert v {a, b}) := by
    intro t ht
    obtain ⟨ht, hpair⟩ := Finset.mem_filter.mp ht
    have tri := G.mem_cliqueFinset_iff.mp ht
    obtain ⟨v, hv, hvEq⟩ := Finset.exists_eq_insert_iff.mpr
      ⟨hpair, by rw [tri.card_eq, Finset.card_pair hab]⟩
    have hvt : v ∈ t := hvEq ▸ Finset.mem_insert_self _ _
    have hvab : v ≠ a ∧ v ≠ b := by simpa using hv
    have hvcommon : v ∈ common := Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset _ _).mpr (tri.isClique (hpair (by simp)) hvt hvab.1.symm),
       (G.mem_neighborFinset _ _).mpr (tri.isClique (hpair (by simp)) hvt hvab.2.symm)⟩
    exact Finset.mem_image.mpr ⟨v, hvcommon, hvEq⟩
  obtain ⟨p, hp⟩ := Function.Embedding.exists_of_card_le_finset (α := Fin 4)
    (s := common) (by simpa using hcount.trans ((Finset.card_le_card cover).trans Finset.card_image_le))
  exact ⟨a, b, adj, p, fun i => by simpa [common] using hp ⟨i, rfl⟩⟩

-- Two adjacent vertices in a common neighborhood would complete a four-clique.
private lemma common_independent {n : ℕ} {G : SimpleGraph (Fin n)} (hG : G.CliqueFree 4)
    {a b x y} (ab : G.Adj a b) (ax : G.Adj a x) (bx : G.Adj b x)
    (ay : G.Adj a y) (by' : G.Adj b y) : ¬ G.Adj x y := by
  intro xy
  have edge : G.IsNClique 2 {a,b} :=
    ⟨by simpa only [Finset.coe_insert, Finset.coe_singleton, isClique_pair] using
          (fun _ : a ≠ b => ab), Finset.card_pair ab.ne⟩
  have tri := edge.insert (a := x) (by simpa [forall_and] using And.intro ax.symm bx.symm)
  exact hG _ (tri.insert (a := y) (by simpa using And.intro xy.symm (And.intro ay.symm by'.symm)))

private lemma send_clique {n m k : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    (f : G ↪g H) {s : Finset (Fin n)} (hs : G.IsNClique k s) :
    H.IsNClique k (s.map f.toEmbedding) := by
  refine ⟨?_, (Finset.card_map _).trans hs.card_eq⟩
  intro a ha b hb hab
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp ha
  obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hb
  exact f.map_adj_iff.mpr (hs.isClique hi hj (fun h => hab (congrArg f h)))

private lemma exclude_book (intersect : H2) (G : SimpleGraph (Fin 25))
    (hG : G.CliqueFree 4) (hI : Gᶜ.CliqueFree 5) {a b} (ab : G.Adj a b)
    (p : Fin 4 ↪ Fin 25) (hp : ∀ i, G.Adj a (p i) ∧ G.Adj b (p i)) : False := by
  classical
  let pages := Finset.univ.map p
  have not_page {v} (h : ∀ i, G.Adj v (p i)) : v ∉ pages := by
    rintro hv
    obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hv
    exact (h i).ne hi.symm
  have ha := not_page (fun i => (hp i).1)
  have hb := not_page (fun i => (hp i).2)
  let anchor := insert a (insert b pages)
  have anchor_size : anchor.card = 6 := by
    simp [anchor, ab.ne, ha, hb, pages, Finset.card_insert_of_notMem]
  obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset (α := Fin 19)
    (s := anchorᶜ) (by simp [Finset.card_compl, anchor_size])
  have outside (x : Fin 19) : f x ≠ a ∧ f x ≠ b ∧ f x ∉ pages := by
    simpa [anchor, and_comm, and_assoc, and_left_comm] using hf ⟨x, rfl⟩
  have off_page (x : Fin 19) (i : Fin 4) : f x ≠ p i := by
    intro eq
    exact (outside x).2.2 (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, eq.symm⟩)
  let C := G.comap f
  let emb := SimpleGraph.Embedding.comap f G
  let embc := SimpleGraph.Embedding.complEquiv emb
  let around := fun (v : Fin 25) => Finset.univ.filter (fun x : Fin 19 => G.Adj v (f x))
  have mem (v x) : x ∈ around v ↔ G.Adj v (f x) := by simp [around]
  have triangle (v t) (ht : C.IsNClique 3 t) : ¬ t ⊆ around v := by
    intro h
    apply hG _ ((send_clique emb ht).insert (a := v) ?_)
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hz
    exact (mem v x).mp (h hx)
  have independent (t : Finset (Fin 19)) (ht : Cᶜ.IsClique t) :
      t.card + (Finset.univ.filter (fun i => Disjoint t (around (p i)))).card ≤ 4 := by
    let missed := Finset.univ.filter (fun i => Disjoint t (around (p i)))
    let left := t.map f
    let right := missed.map p
    have sep : Disjoint left right := by
      refine Finset.disjoint_left.mpr ?_
      intro z hl hr
      obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp hl
      obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hr
      exact off_page x i hi.symm
    have full : Gᶜ.IsClique (↑(left ∪ right) : Set (Fin 25)) := by
      let _ : Std.Symm Gᶜ.Adj := Gᶜ.symm
      rw [Finset.coe_union, isClique_iff, Set.pairwise_union_of_symm]
      refine ⟨(send_clique embc (show Cᶜ.IsNClique t.card t from ⟨ht, rfl⟩)).isClique, ?_, ?_⟩
      · intro u hu v hv huv
        obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hu
        obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hv
        exact ⟨huv, common_independent hG ab (hp i).1 (hp i).2 (hp j).1 (hp j).2⟩
      · intro u hu v hv huv
        obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hu
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hv
        exact ⟨huv, fun ad => (Finset.disjoint_left.mp (Finset.mem_filter.mp hi).2 hx)
          ((mem _ _).mpr ad.symm)⟩
    have size : (left ∪ right).card ≤ 4 := by
      by_contra! big
      exact hI.mono big _ ⟨full, rfl⟩
    simpa only [Finset.card_union_of_disjoint sep, left, right, Finset.card_map, missed] using size
  have cones := intersect C (fun i => around (p i)) (CliqueFree.comap emb.isContained hG)
    (fun i => triangle (p i)) independent
  have pole (v : Fin 25) (hv : ∀ i, G.Adj v (p i)) (hvout : ∀ x, v ≠ f x) :
      (∀ t, C.IsNClique 3 t → ¬ t ⊆ around v) ∧
      (∀ i, C.IsIndepSet (↑(around v ∩ around (p i)) : Set (Fin 19))) ∧
      (∀ t, Cᶜ.IsNClique 4 t → ¬ Disjoint t (around v)) := by
    refine ⟨triangle v, ?_, ?_⟩
    · intro i x hx y hy _
      obtain ⟨hxv, hxi⟩ := Finset.mem_inter.mp hx
      obtain ⟨hyv, hyi⟩ := Finset.mem_inter.mp hy
      exact common_independent hG (hv i) ((mem _ _).mp hxv) ((mem _ _).mp hxi)
        ((mem _ _).mp hyv) ((mem _ _).mp hyi)
    · intro t ht dis
      apply hI _ ((send_clique embc ht).insert (a := v) ?_)
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hz
      exact ⟨hvout x, fun ad => Finset.disjoint_left.mp dis hx ((mem _ _).mpr ad)⟩
  apply cones (around a) (around b) (pole a (fun i => (hp i).1) (fun x => (outside x).1.symm))
    (pole b (fun i => (hp i).2) (fun x => (outside x).2.1.symm))
  refine Finset.disjoint_left.mpr ?_
  intro x xa xb
  have ax := (mem _ _).mp xa
  have bx := (mem _ _).mp xb
  have four : Gᶜ.IsNClique 4 pages := by
    refine ⟨?_, by simp [pages]⟩
    intro u hu v hv huv
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hv
    exact ⟨huv, common_independent hG ab (hp i).1 (hp i).2 (hp j).1 (hp j).2⟩
  apply hI _ (four.insert (a := f x) ?_)
  intro z hz
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hz
  exact ⟨off_page x i, common_independent hG ab ax bx (hp i).1 (hp i).2⟩

theorem main : H1 → H2 → type_of% @RamseyNumbers.ramsey_number_four_five := by
  classical
  intro census intersect
  have upper : IsGraphRamsey 25 4 5 := by
    rintro G ⟨hG, hI⟩
    let f : Fin 24 ↪ Fin 25 := Fin.castSuccEmb
    let K := G.comap f
    let e := SimpleGraph.Embedding.comap f G
    obtain ⟨a, b, ab, p, hp⟩ := book_of_count K
      (census K (CliqueFree.comap e.isContained hG)
        (CliqueFree.comap (SimpleGraph.Embedding.complEquiv e).isContained hI))
    exact exclude_book intersect G hG hI (a := f a) (b := f b) ab (p.trans f) hp
  rw [classicalRamsey_eq_sInf]
  apply IsLeast.csInf_eq
  refine ⟨upper, ?_⟩
  intro n hn
  by_contra! hlt
  have mono : Monotone (fun m => IsGraphRamsey m 4 5) :=
    monotone_nat_of_le_succ fun m => IsGraphRamsey.succ m 4 5
  exact twentyfour_fails (mono (show n ≤ 24 by omega) hn)

end OMA.R_RamseyNumbers_ramsey_number_four_five_R2
