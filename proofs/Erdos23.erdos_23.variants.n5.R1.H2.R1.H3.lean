import OMAReductions.R_Erdos23_erdos_23_variants_n5_R1_H2_R1
import Mathlib

/-! A dense nonbipartite eleven-vertex core has a five-cycle with two singleton classes, providing a cut of cost at most fourteen. -/

namespace Erdos23Degree13

open Finset

def c5Pair (i : Fin 5) : Finset (Fin 5) := {i - 1, i + 1}

private theorem opposite_iff : ∀ i j : Fin 5, Disjoint (c5Pair i) (c5Pair j) ↔
    j = i - 1 ∨ j = i + 1 := by decide +kernel

private theorem no_rectangle : ∀ i j k l : Fin 5, i ≠ j → k ≠ l →
    Disjoint (c5Pair i) (c5Pair k) → Disjoint (c5Pair i) (c5Pair l) →
    Disjoint (c5Pair j) (c5Pair k) → Disjoint (c5Pair j) (c5Pair l) → False := by
  decide +kernel

/-- In the equality case of Mantel on the six external vertices, pairwise
attachment compatibility makes one of the two classes use a single type. -/
theorem opposite_type_center (left right : Fin 3 → Fin 5)
    (compatible : ∀ i j, Disjoint (c5Pair (left i)) (c5Pair (right j))) :
    ((∀ i, left i = left 0) ∧ (∀ j, right j = left 0 - 1 ∨ right j = left 0 + 1)) ∨
      ((∀ j, right j = right 0) ∧ (∀ i, left i = right 0 - 1 ∨ left i = right 0 + 1)) := by
  by_cases constant : ∀ i, left i = left 0
  · exact Or.inl ⟨constant, fun j => (opposite_iff _ _).mp (compatible 0 j)⟩
  · push Not at constant
    obtain ⟨i, hi⟩ := constant
    refine Or.inr ⟨?_, fun j => (opposite_iff _ _).mp (compatible j 0).symm⟩
    intro j
    by_contra hj
    exact no_rectangle _ _ _ _ hi hj (compatible i j) (compatible i 0)
      (compatible 0 j) (compatible 0 0)

section RootedGraph

open SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V]

def rootCore (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  (insert v (G.neighborFinset v))ᶜ

theorem rootCore_card (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (v : Fin 25)
    (degree13 : G.degree v = 13) : (rootCore G v).card = 11 := by
  rw [rootCore, Finset.card_compl, Fintype.card_fin, Finset.card_insert_of_notMem
    (by simp), card_neighborFinset_eq_degree, degree13]

open scoped Classical in
/-- The monochromatic edges of a neighborhood cut are exactly those in the
induced graph outside the root and its neighbors. -/
theorem rootCore_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangleFree : G.CliqueFree 3) (v : V)
    [DecidablePred (fun e : Sym2 V => ∀ x ∈ e, ∀ y ∈ e,
      (x ∈ G.neighborFinset v ↔ y ∈ G.neighborFinset v))] :
    (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e,
      (x ∈ G.neighborFinset v ↔ y ∈ G.neighborFinset v))).card =
    (G.induce (rootCore G v : Set V)).edgeFinset.card := by
  let W : Set V := rootCore G v
  let edgeEmbedding : Sym2 W ↪ Sym2 V :=
    ⟨Sym2.map Subtype.val, Sym2.map.injective Subtype.val_injective⟩
  have equal : G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e,
      (x ∈ G.neighborFinset v ↔ y ∈ G.neighborFinset v)) =
      (G.induce W).edgeFinset.map edgeEmbedding := by
    ext e
    constructor
    · induction e using Sym2.ind with
      | h x y =>
        intro he
        rw [Finset.mem_filter, mem_edgeFinset, mem_edgeSet] at he
        have follow := he.2 x (Sym2.mem_mk_left x y) y (Sym2.mem_mk_right x y)
        have hxN : x ∉ G.neighborFinset v := by
          intro hx
          have hy := follow.mp hx
          rw [mem_neighborFinset] at hx hy
          exact triangleFree {v, x, y} (is3Clique_triple_iff.2 ⟨hx, hy, he.1⟩)
        have hyN : y ∉ G.neighborFinset v := fun hy => hxN (follow.mpr hy)
        have hxv : x ≠ v := by
          intro h
          subst x
          exact hyN ((mem_neighborFinset _ _ _).2 he.1)
        have hyv : y ≠ v := by
          intro h
          subst y
          exact hxN ((mem_neighborFinset _ _ _).2 he.1.symm)
        have hx : x ∈ W := by
          change x ∈ rootCore G v
          rw [rootCore, Finset.mem_compl, Finset.mem_insert, not_or]
          exact ⟨hxv, hxN⟩
        have hy : y ∈ W := by
          change y ∈ rootCore G v
          rw [rootCore, Finset.mem_compl, Finset.mem_insert, not_or]
          exact ⟨hyv, hyN⟩
        rw [Finset.mem_map]
        refine ⟨s(⟨x, hx⟩, ⟨y, hy⟩), ?_, rfl⟩
        rw [mem_edgeFinset, mem_edgeSet, comap_adj]
        exact he.1
    · intro he
      obtain ⟨original, horiginal, rfl⟩ := Finset.mem_map.mp he
      induction original using Sym2.ind with
      | h x y =>
        rw [mem_edgeFinset, mem_edgeSet, comap_adj] at horiginal
        change s((x : V), (y : V)) ∈ G.edgeFinset.filter _
        rw [Finset.mem_filter, mem_edgeFinset, mem_edgeSet]
        refine ⟨horiginal, ?_⟩
        have hxW : (x : V) ∈ W := x.property
        have hyW : (y : V) ∈ W := y.property
        change (x : V) ∈ rootCore G v at hxW
        change (y : V) ∈ rootCore G v at hyW
        rw [rootCore, Finset.mem_compl, Finset.mem_insert, not_or] at hxW hyW
        have hxN := hxW.2
        have hyN := hyW.2
        simp only [Sym2.mem_iff]
        rintro a (rfl | rfl) b (rfl | rfl) <;> simp [hxN, hyN]
  rw [equal, Finset.card_map]


open scoped Classical in
theorem rootCore_bounds (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    (triangleFree : G.CliqueFree 3) (v : Fin 25) (degree13 : G.degree v = 13)
    (residual : 25 < (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e,
      (x ∈ G.neighborFinset v ↔ y ∈ G.neighborFinset v))).card) :
    26 ≤ (G.induce (rootCore G v : Set (Fin 25))).edgeFinset.card ∧
      (G.induce (rootCore G v : Set (Fin 25))).edgeFinset.card ≤ 30 := by
  rw [rootCore_edges G triangleFree v] at residual
  refine ⟨residual, ?_⟩
  have coreFree : (G.induce (rootCore G v : Set (Fin 25))).CliqueFree 3 :=
    triangleFree.comap (Embedding.induce _).isContained
  have bound := CliqueFree.card_edgeFinset_le (r := 2) coreFree
  have card : Fintype.card ↑(↑(rootCore G v) : Set (Fin 25)) = 11 := by
    have h : Fintype.card ↑(↑(rootCore G v) : Set (Fin 25)) = (rootCore G v).card := by simp
    exact h.trans (rootCore_card G v degree13)
  dsimp only at bound
  rw [card] at bound
  norm_num at bound
  exact bound


open scoped Classical in
omit [DecidableEq V] in
/-- A six-vertex triangle-free core with nine edges is K3,3, represented
by the parity bipartition of the canonical Turán graph. -/
theorem six_mantel (H : SimpleGraph V) (vertices : Fintype.card V = 6)
    (triangleFree : H.CliqueFree 3) (edges : H.edgeFinset.card = 9) :
    Nonempty (H ≃g turanGraph 6 2) := by
  have maximal : H.IsTuranMaximal 2 := by
    refine ⟨triangleFree, ?_⟩
    intro G _ free
    have bound := CliqueFree.card_edgeFinset_le (r := 2) free
    dsimp only at bound
    rw [vertices] at bound
    rw [edges]
    norm_num at bound
    exact bound
  have iso := maximal.nonempty_iso_turanGraph
  rwa [vertices] at iso

end RootedGraph

end Erdos23Degree13

namespace Erdos23RootedCuts

open Finset SimpleGraph
open scoped Classical

variable {V : Type} [Fintype V] [DecidableEq V]

def near (G : SimpleGraph V) [DecidableRel G.Adj] (a : V) (S : Finset V) : Finset V :=
  S.filter (G.Adj a)

def incident (G : SimpleGraph V) [DecidableRel G.Adj] (a : V) (S : Finset V) :
    Finset (Sym2 V) :=
  (near G a S).map ⟨fun x => s(a, x), by
    intro x y hp
    rcases Sym2.eq_iff.mp hp with h | h
    · exact h.2
    · exact h.2.trans h.1⟩

omit [Fintype V] [DecidableEq V] in
theorem incident_card (G : SimpleGraph V) [DecidableRel G.Adj] (a : V) (S : Finset V) :
    (incident G a S).card = (near G a S).card :=
  Finset.card_map _

omit [Fintype V] [DecidableEq V] in
theorem mem_incident (G : SimpleGraph V) [DecidableRel G.Adj] {a b : V} {S : Finset V}
    (hadj : G.Adj a b) (hb : b ∈ S) : s(a, b) ∈ incident G a S := by
  exact Finset.mem_map.2 ⟨b, Finset.mem_filter.2 ⟨hb, hadj⟩, rfl⟩

def mono (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))

theorem mem_mono (G : SimpleGraph V) [DecidableRel G.Adj] {a b : V} {S : Finset V} :
    s(a, b) ∈ mono G S ↔ G.Adj a b ∧ (a ∈ S ↔ b ∈ S) := by
  simp only [mono, Finset.mem_filter, mem_edgeFinset, mem_edgeSet]
  rw [OMA.R_Erdos23_erdos_23_variants_n5_R1.same_mk]

theorem mono_matches (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    [DecidablePred (fun e : Sym2 V => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))] :
    mono G S = G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S)) := by
  ext e
  simp only [mono, Finset.mem_filter]

omit [Fintype V] in
theorem near_union_card (G : SimpleGraph V) [DecidableRel G.Adj] (a : V)
    {L R : Finset V} (disjoint : Disjoint L R) :
    (near G a (L ∪ R)).card = (near G a L).card + (near G a R).card := by
  simp only [near, Finset.filter_union]
  apply Finset.card_union_of_disjoint
  exact disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

omit [Fintype V] [DecidableEq V] in
theorem adj_into_neighbor (G : SimpleGraph V) (triangleFree : G.CliqueFree 3)
    {v a b : V} (ha : G.Adj v a) (hb : G.Adj v b) : ¬ G.Adj a b := by
  intro h
  exact triangleFree {v, a, b} (is3Clique_triple_iff.2 ⟨ha, hb, h⟩)

omit [DecidableEq V] in
theorem neighbor_independent (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangleFree : G.CliqueFree 3) (v : V) :
    ∀ a ∈ G.neighborFinset v, ∀ b ∈ G.neighborFinset v, ¬ G.Adj a b := by
  intro a ha b hb
  exact adj_into_neighbor G triangleFree ((mem_neighborFinset G v a).mp ha)
    ((mem_neighborFinset G v b).mp hb)

theorem rooted_cut (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangleFree : G.CliqueFree 3) (v : V) {L R : Finset V}
    (left : L = (G.neighborFinset v)ᶜ \ R) :
    ∃ S : Finset V, (mono G S).card ≤ ((mono G L) ∩ (mono G (G.neighborFinset v))).card +
      ∑ a ∈ G.neighborFinset v, min (near G a L).card (near G a R).card := by
  let A := G.neighborFinset v
  let cheaper := fun a => (near G a L).card ≤ (near G a R).card
  let S := L ∪ A.filter cheaper
  let pieces := fun a => incident G a (if cheaper a then L else R)
  have side (a : V) (ha : a ∈ A) : a ∈ S ↔ cheaper a := by
    have hn : a ∉ L := by simp [left, A, ha]
    simp [S, hn, ha]
  have outside (a : V) (ha : a ∉ A) : a ∈ S ↔ a ∈ L := by
    simp [S, ha]
  have right_side (a : V) (ha : a ∉ A) : a ∈ R ↔ a ∉ L := by
    simp [left, A, ha]
  have cover : mono G S ⊆ ((mono G L) ∩ (mono G A)) ∪ A.biUnion pieces := by
    intro e he
    induction e using Sym2.ind with
    | h a b =>
      obtain ⟨adj, same⟩ := (mem_mono G).mp he
      by_cases ha : a ∈ A
      · have hb : b ∉ A := fun h => neighbor_independent G triangleFree v a ha b h adj
        refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨a, ha, ?_⟩)
        have relevant : cheaper a ↔ b ∈ L := (side a ha).symm.trans
          (same.trans (outside b hb))
        by_cases hc : cheaper a
        · simpa only [pieces, if_pos hc] using mem_incident G adj (relevant.mp hc)
        · simpa only [pieces, if_neg hc] using
            mem_incident G adj ((right_side b hb).mpr (fun hl => hc (relevant.mpr hl)))
      · by_cases hb : b ∈ A
        · refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨b, hb, ?_⟩)
          rw [Sym2.eq_swap]
          have relevant : cheaper b ↔ a ∈ L := (side b hb).symm.trans
            (same.symm.trans (outside a ha))
          by_cases hc : cheaper b
          · simpa only [pieces, if_pos hc] using mem_incident G adj.symm (relevant.mp hc)
          · simpa only [pieces, if_neg hc] using
              mem_incident G adj.symm ((right_side a ha).mpr (fun hl => hc (relevant.mpr hl)))
        · refine Finset.mem_union_left _ (Finset.mem_inter.2 ⟨?_, ?_⟩)
          · exact (mem_mono G).mpr ⟨adj, (outside a ha).symm.trans (same.trans (outside b hb))⟩
          · exact (mem_mono G).mpr ⟨adj, by simp [ha, hb]⟩
  refine ⟨S, (Finset.card_le_card cover).trans ((Finset.card_union_le _ _).trans ?_)⟩
  apply Nat.add_le_add_left
  refine Finset.card_biUnion_le.trans ?_
  apply Finset.sum_le_sum
  intro a _
  change (incident G a (if cheaper a then L else R)).card ≤ _
  rw [incident_card]
  by_cases hc : cheaper a
  · simp [hc, Nat.min_eq_left (show (near G a L).card ≤ (near G a R).card from hc)]
  · simp [hc, Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge hc))]


theorem core_endpoints (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (triangleFree : G.CliqueFree 3) {x y : V}
    (edge : s(x, y) ∈ mono G (G.neighborFinset v)) :
    x ∈ (insert v (G.neighborFinset v))ᶜ ∧ y ∈ (insert v (G.neighborFinset v))ᶜ := by
  obtain ⟨adj, same⟩ := (mem_mono G).mp edge
  have nx : x ∉ G.neighborFinset v := fun hx => neighbor_independent G triangleFree v
    x hx y (same.mp hx) adj
  have ny : y ∉ G.neighborFinset v := fun hy => nx (same.mpr hy)
  have hx : x ≠ v := by
    rintro rfl
    exact ny ((mem_neighborFinset _ _ _).mpr adj)
  have hy : y ≠ v := by
    rintro rfl
    exact nx ((mem_neighborFinset _ _ _).mpr adj.symm)
  simp only [Finset.mem_compl, Finset.mem_insert, not_or]
  exact ⟨⟨hx, nx⟩, hy, ny⟩


end Erdos23RootedCuts

namespace Erdos23OddCore

open SimpleGraph

variable {V : Type}

theorem bipartite_of_even_closed (G : SimpleGraph V)
    (allEven : ∀ a (w : G.Walk a a), Even w.length) :
    G.IsBipartite := by
  classical
  let root := fun a => Quot.out (G.connectedComponentMk a)
  have reachable (a) : G.Reachable (root a) a :=
    ConnectedComponent.exact (Quot.out_eq (G.connectedComponentMk a))
  let path : ∀ a, G.Walk (root a) a := fun a => (reachable a).some
  let color : V → Fin 2 := fun a => if Even (path a).length then 0 else 1
  refine ⟨Coloring.mk color ?_⟩
  intro a b hab
  have sameRoot : root a = root b := congrArg Quot.out
    (ConnectedComponent.connectedComponentMk_eq_of_adj hab)
  let tail : G.Walk (root a) b := (path b).copy sameRoot.symm rfl
  have parity := allEven (root a) (((path a).concat hab).append tail.reverse)
  simp only [Walk.length_append, Walk.length_concat, Walk.length_reverse, tail, Walk.length_copy]
    at parity
  dsimp only [color]
  split_ifs with ha hb hb
  · simp only [Nat.even_iff] at parity ha hb
    omega
  · decide
  · decide
  · simp only [Nat.even_iff] at parity ha hb
    omega

theorem odd_of_not_bipartite (G : SimpleGraph V) (nonbipartite : ¬ G.IsBipartite) :
    ∃ (a : V) (w : G.Walk a a), Odd w.length := by
  by_contra absent
  apply nonbipartite
  apply bipartite_of_even_closed
  intro a w
  exact Nat.not_odd_iff_even.mp (fun hw => absent ⟨a, w, hw⟩)

theorem shortest_odd (G : SimpleGraph V) (nonbipartite : ¬ G.IsBipartite) :
    ∃ (a : V) (w : G.Walk a a), Odd w.length ∧
      ∀ b (u : G.Walk b b), Odd u.length → w.length ≤ u.length := by
  classical
  let data (n : ℕ) := ∃ (a : V) (w : G.Walk a a), Odd w.length ∧ w.length = n
  obtain ⟨a, w, odd⟩ := odd_of_not_bipartite G nonbipartite
  have existsData : ∃ n, data n := ⟨w.length, a, w, odd, rfl⟩
  obtain ⟨start, cycle, cycleOdd, minimal⟩ := Nat.find_spec existsData
  refine ⟨start, cycle, cycleOdd, ?_⟩
  intro b u oddU
  rw [minimal]
  exact Nat.find_min' existsData ⟨b, u, oddU, rfl⟩

/-- The two arcs of a shortest odd closed walk admit no path shorter than both
arcs between their endpoints. The path would give two shorter closed walks
of opposite parity. -/
theorem shortest_shortcut {G : SimpleGraph V} {a : V} {w : G.Walk a a}
    (odd : Odd w.length)
    (shortest : ∀ b (u : G.Walk b b), Odd u.length → w.length ≤ u.length)
    {i j : ℕ} (ij : i ≤ j) (last : j ≤ w.length)
    (p : G.Walk (w.getVert i) (w.getVert j)) :
    min (j - i) (w.length - (j - i)) ≤ p.length := by
  by_contra! h
  have first : p.length < j - i := lt_of_lt_of_le h (Nat.min_le_left _ _)
  have second : p.length < w.length - (j - i) := lt_of_lt_of_le h (Nat.min_le_right _ _)
  have target : (w.drop i).getVert (j - i) = w.getVert j := by
    rw [Walk.drop_getVert, Nat.add_sub_of_le ij]
  let middle := ((w.drop i).take (j - i)).copy rfl target
  let arcA : G.Walk (w.getVert i) (w.getVert i) := middle.append p.reverse
  let arcB : G.Walk a a := ((w.take i).append p).append (w.drop j)
  have lengthA : arcA.length = (j - i) + p.length := by
    simp only [arcA, middle, Walk.length_append, Walk.length_copy, Walk.take_length,
      Walk.drop_length, Walk.length_reverse]
    rw [min_eq_left (by omega)]
  have lengthB : arcB.length = i + p.length + (w.length - j) := by
    simp only [arcB, Walk.length_append, Walk.take_length, Walk.drop_length]
    rw [min_eq_left (ij.trans last)]
  have hA : ¬ Odd arcA.length := fun h => by
    have bound := shortest _ arcA h
    omega
  have hB : ¬ Odd arcB.length := fun h => by
    have bound := shortest _ arcB h
    omega
  simp only [Nat.odd_iff] at odd hA hB
  omega

theorem shortest_getVert_injective {G : SimpleGraph V} {a : V} {w : G.Walk a a}
    (odd : Odd w.length)
    (shortest : ∀ b (u : G.Walk b b), Odd u.length → w.length ≤ u.length) :
    Function.Injective (fun i : Fin w.length => w.getVert i.val) := by
  intro i j eq
  suffices noOrder : ∀ (i j : Fin w.length), i.val < j.val →
      w.getVert i.val ≠ w.getVert j.val by
    rcases lt_trichotomy i.val j.val with lt | same | gt
    · exact (noOrder i j lt eq).elim
    · exact Fin.ext same
    · exact (noOrder j i gt eq.symm).elim
  intro l r order same
  have length := shortest_shortcut odd shortest (Nat.le_of_lt order) (Nat.le_of_lt r.isLt)
    ((Walk.nil : G.Walk (w.getVert l.val) (w.getVert l.val)).copy rfl same)
  simp only [Walk.length_copy, Walk.length_nil] at length
  have lpos : 0 < r.val - l.val := by omega
  have rpos : 0 < w.length - (r.val - l.val) := by have := r.isLt; omega
  omega


theorem shortest_length_lower {G : SimpleGraph V} {a : V} {w : G.Walk a a}
    (triangleFree : G.CliqueFree 3) (odd : Odd w.length) : 5 ≤ w.length := by
  classical
  have not1 : w.length ≠ 1 := fun h => G.irrefl (w.adj_of_length_eq_one h)
  have not3 : w.length ≠ 3 := by
    intro h
    have e01 := w.adj_getVert_succ (i := 0) (by omega)
    have e12 := w.adj_getVert_succ (i := 1) (by omega)
    have e23 := w.adj_getVert_succ (i := 2) (by omega)
    change G.Adj (w.getVert 2) (w.getVert 3) at e23
    rw [← h, Walk.getVert_length] at e23
    rw [Walk.getVert_zero] at e01
    exact triangleFree {a, w.getVert 1, w.getVert 2}
      (is3Clique_triple_iff.mpr ⟨e01, e23.symm, e12⟩)
  simp only [Nat.odd_iff] at odd
  omega

theorem shortest_edge_ends {G : SimpleGraph V} {a : V} {w : G.Walk a a}
    (odd : Odd w.length)
    (shortest : ∀ b (u : G.Walk b b), Odd u.length → w.length ≤ u.length)
    {i j : Fin w.length} (lt : i.val < j.val)
    (edge : G.Adj (w.getVert i.val) (w.getVert j.val)) :
    j.val = i.val + 1 ∨ j.val + 1 = i.val + w.length := by
  have bound := shortest_shortcut odd shortest lt.le j.isLt.le edge.toWalk
  rw [Adj.length_toWalk] at bound
  have jlt := j.isLt
  omega

theorem shortest_near_ordered {G : SimpleGraph V} {a : V} {w : G.Walk a a}
    (triangleFree : G.CliqueFree 3) (odd : Odd w.length)
    (shortest : ∀ b (u : G.Walk b b), Odd u.length → w.length ≤ u.length)
    {v : V} {i j : Fin w.length} (lt : i.val < j.val)
    (left : G.Adj v (w.getVert i.val)) (right : G.Adj v (w.getVert j.val)) :
    j.val = i.val + 2 ∨ j.val + 2 = i.val + w.length := by
  classical
  have bound := shortest_shortcut odd shortest lt.le j.isLt.le
    (left.symm.toWalk.concat right)
  rw [Walk.length_concat, Adj.length_toWalk] at bound
  have miss : ¬ G.Adj (w.getVert i.val) (w.getVert j.val) := fun h =>
    triangleFree {v, w.getVert i.val, w.getVert j.val}
      (is3Clique_triple_iff.mpr ⟨left, right, h⟩)
  have not1 : j.val ≠ i.val + 1 := fun h =>
    miss (h ▸ w.adj_getVert_succ i.isLt)
  have notWrap : j.val + 1 ≠ i.val + w.length := by
    intro h
    have jlt := j.isLt
    have hi0 : i.val = 0 := by omega
    have last : j.val + 1 = w.length := by omega
    have edge := w.adj_getVert_succ j.isLt
    rw [last, Walk.getVert_length] at edge
    apply miss
    rw [hi0, Walk.getVert_zero]
    exact edge.symm
  have jlt := j.isLt
  omega

private theorem no_two_step_triplet (n i j k : ℕ) (hl : 5 ≤ n) (odd : Odd n)
    (hi : i < n) (hj : j < n) (hk : k < n)
    (ij : j = i + 2 ∨ j + 2 = i + n ∨ i = j + 2 ∨ i + 2 = j + n)
    (ik : k = i + 2 ∨ k + 2 = i + n ∨ i = k + 2 ∨ i + 2 = k + n)
    (jk : k = j + 2 ∨ k + 2 = j + n ∨ j = k + 2 ∨ j + 2 = k + n) :
    False := by
  simp only [Nat.odd_iff] at odd
  omega

open scoped Classical in
theorem shortest_at_most_two_neighbors {G : SimpleGraph V} {a : V} {w : G.Walk a a}
    (triangleFree : G.CliqueFree 3) (odd : Odd w.length)
    (shortest : ∀ b (u : G.Walk b b), Odd u.length → w.length ≤ u.length) (v : V) :
    (Finset.univ.filter (fun i : Fin w.length => G.Adj v (w.getVert i.val))).card ≤ 2 := by
  by_contra! tooMany
  obtain ⟨i, j, k, hi, hj, hk, ij, ik, jk⟩ := Finset.two_lt_card_iff.mp tooMany
  have near (l r : Fin w.length) (ne : l ≠ r)
      (hl : G.Adj v (w.getVert l.val)) (hr : G.Adj v (w.getVert r.val)) :
      r.val = l.val + 2 ∨ r.val + 2 = l.val + w.length ∨
        l.val = r.val + 2 ∨ l.val + 2 = r.val + w.length := by
    rcases lt_or_gt_of_ne ne with lt | gt
    · rcases shortest_near_ordered triangleFree odd shortest lt hl hr with a | b
      · exact Or.inl a
      · exact Or.inr (Or.inl b)
    · exact Or.inr (Or.inr (shortest_near_ordered triangleFree odd shortest gt hr hl))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj hk
  exact no_two_step_triplet w.length i.val j.val k.val
    (shortest_length_lower triangleFree odd) odd i.isLt j.isLt k.isLt
    (near i j ij hi hj) (near i k ik hi hk) (near j k jk hj hk)


section Counting

open Finset
open scoped Classical

variable [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def cycleVerts {a : V} (w : G.Walk a a) : Finset V :=
  univ.image (fun i : Fin w.length => w.getVert i.val)

def cycleEdges {a : V} (w : G.Walk a a) : Finset (Sym2 V) :=
  univ.image (fun i : Fin w.length => s(w.getVert i.val, w.getVert ((i.val + 1) % w.length)))

omit [Fintype V] [DecidableRel G.Adj] in
theorem mem_cycleVerts {a : V} (w : G.Walk a a) (x : V) :
    x ∈ cycleVerts w ↔ ∃ i : Fin w.length, w.getVert i.val = x := by
  simp [cycleVerts]

omit [Fintype V] [DecidableRel G.Adj] in
theorem card_cycleVerts {a : V} (w : G.Walk a a) (odd : Odd w.length)
    (shortest : ∀ b (u : G.Walk b b), Odd u.length → w.length ≤ u.length) :
    (cycleVerts w).card = w.length := by
  rw [cycleVerts, Finset.card_image_of_injective _ (shortest_getVert_injective odd shortest)]
  simp

omit [Fintype V] [DecidableRel G.Adj] in
theorem mem_cycleEdges_of_adj {a : V} (w : G.Walk a a) (odd : Odd w.length)
    (shortest : ∀ b (u : G.Walk b b), Odd u.length → w.length ≤ u.length)
    {x y : V} (hx : x ∈ cycleVerts w) (hy : y ∈ cycleVerts w) (adj : G.Adj x y) :
    s(x, y) ∈ cycleEdges w := by
  obtain ⟨i, rfl⟩ := (mem_cycleVerts w x).mp hx
  obtain ⟨j, rfl⟩ := (mem_cycleVerts w y).mp hy
  have ordered (i j : Fin w.length) (lt : i.val < j.val)
      (adj : G.Adj (w.getVert i.val) (w.getVert j.val)) :
      s(w.getVert i.val, w.getVert j.val) ∈ cycleEdges w := by
    rcases shortest_edge_ends odd shortest lt adj with next | wrap
    · apply Finset.mem_image.mpr
      refine ⟨i, mem_univ i, ?_⟩
      rw [← next, Nat.mod_eq_of_lt j.isLt]
    · have jl := j.isLt
      have i0 : i.val = 0 := by omega
      have jw : j.val + 1 = w.length := by omega
      apply Finset.mem_image.mpr
      refine ⟨j, mem_univ j, ?_⟩
      rw [jw, Nat.mod_self, i0, Sym2.eq_swap]
  have ne : i ≠ j := fun h => G.irrefl (h ▸ adj)
  rcases lt_or_gt_of_ne ne with lt | gt
  · exact ordered i j lt adj
  · rw [Sym2.eq_swap]
    exact ordered j i gt adj.symm

omit [Fintype V] in
theorem count_cycle_neighbors {a x : V} (w : G.Walk a a) (odd : Odd w.length)
    (shortest : ∀ b (u : G.Walk b b), Odd u.length → w.length ≤ u.length)
    (triangleFree : G.CliqueFree 3) :
    (Erdos23RootedCuts.near G x (cycleVerts w)).card ≤ 2 := by
  rw [Erdos23RootedCuts.near, cycleVerts, Finset.filter_image,
    Finset.card_image_of_injective _ (shortest_getVert_injective odd shortest)]
  convert shortest_at_most_two_neighbors triangleFree odd shortest x using 1
  congr 1
  ext i
  simp

theorem count_core {a : V} (w : G.Walk a a) (odd : Odd w.length)
    (shortest : ∀ b (u : G.Walk b b), Odd u.length → w.length ≤ u.length) :
    G.edgeFinset.card ≤ w.length + (∑ x ∈ (cycleVerts w)ᶜ,
      (Erdos23RootedCuts.near G x (cycleVerts w)).card) +
      (G.induce (↑((cycleVerts w)ᶜ) : Set V)).edgeFinset.card := by
  let C := cycleVerts w
  let O := Cᶜ
  let U : Set V := O
  let coeEdge : Sym2 U ↪ Sym2 V :=
    ⟨Sym2.map Subtype.val, Sym2.map.injective Subtype.val_injective⟩
  let outside := (G.induce U).edgeFinset.map coeEdge
  let cross := O.biUnion (fun x => Erdos23RootedCuts.incident G x C)
  have cover : G.edgeFinset ⊆ (cycleEdges w ∪ cross) ∪ outside := by
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      have adj := mem_edgeFinset.mp he
      rw [mem_edgeSet] at adj
      by_cases hx : x ∈ C
      · by_cases hy : y ∈ C
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (mem_cycleEdges_of_adj w odd shortest hx hy adj))
        · apply Finset.mem_union_left _
          apply Finset.mem_union_right _
          apply Finset.mem_biUnion.mpr
          refine ⟨y, Finset.mem_compl.mpr hy, ?_⟩
          rw [Sym2.eq_swap]
          exact Erdos23RootedCuts.mem_incident G adj.symm hx
      · by_cases hy : y ∈ C
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨x, Finset.mem_compl.mpr hx,
              Erdos23RootedCuts.mem_incident G adj hy⟩))
        · apply Finset.mem_union_right _
          apply Finset.mem_map.mpr
          refine ⟨s(⟨x, Finset.mem_compl.mpr hx⟩, ⟨y, Finset.mem_compl.mpr hy⟩), ?_, rfl⟩
          rw [mem_edgeFinset, mem_edgeSet, comap_adj]
          exact adj
  have cycleBound : (cycleEdges w).card ≤ w.length := by
    unfold cycleEdges
    simpa using Finset.card_image_le
      (s := (univ : Finset (Fin w.length)))
      (f := fun i => s(w.getVert i.val, w.getVert ((i.val + 1) % w.length)))
  have crossBound : cross.card ≤ ∑ x ∈ O, (Erdos23RootedCuts.near G x C).card := by
    unfold cross
    simpa only [Erdos23RootedCuts.incident_card] using
      (Finset.card_biUnion_le (s := O) (t := fun x => Erdos23RootedCuts.incident G x C))
  have outCard : outside.card = (G.induce U).edgeFinset.card := by simp [outside]
  calc
    G.edgeFinset.card ≤ ((cycleEdges w ∪ cross) ∪ outside).card := Finset.card_le_card cover
    _ ≤ (cycleEdges w ∪ cross).card + outside.card := Finset.card_union_le _ _
    _ ≤ (cycleEdges w).card + cross.card + outside.card :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ w.length + (∑ x ∈ O, (Erdos23RootedCuts.near G x C).card) +
          (G.induce U).edgeFinset.card := by omega


private theorem dense_counts (k crossings outside : ℕ)
    (lo : 5 ≤ k) (hi : k ≤ 11) (odd : Odd k)
    (crossingBound : crossings ≤ 2 * (11 - k))
    (outsideBound : outside ≤ ((11 - k) ^ 2 - ((11 - k) % 2) ^ 2) * (2 - 1) /
      (2 * 2) + ((11 - k) % 2).choose 2)
    (dense : 26 ≤ k + crossings + outside) :
    k = 5 ∧ crossings = 12 ∧ outside = 9 := by
  interval_cases k <;> norm_num [Nat.odd_iff] at * <;> omega

theorem dense_eleven_cycle (vertices : Fintype.card V = 11)
    (triangleFree : G.CliqueFree 3) (dense : 26 ≤ G.edgeFinset.card)
    (nonbipartite : ¬ G.IsBipartite) :
    ∃ (a : V) (w : G.Walk a a), w.length = 5 ∧ Odd w.length ∧
      (∀ b (u : G.Walk b b), Odd u.length → w.length ≤ u.length) ∧
      (G.induce (↑((cycleVerts w)ᶜ) : Set V)).edgeFinset.card = 9 ∧
      ∀ x ∉ cycleVerts w, (Erdos23RootedCuts.near G x (cycleVerts w)).card = 2 := by
  obtain ⟨a, w, odd, shortest⟩ := shortest_odd G nonbipartite
  let C := cycleVerts w
  let O := Cᶜ
  let U : Set V := O
  let outside := (G.induce U).edgeFinset.card
  let nearC := fun x => (Erdos23RootedCuts.near G x C).card
  let crossings := ∑ x ∈ O, nearC x
  have cardC : C.card = w.length := card_cycleVerts w odd shortest
  have cardO : O.card = 11 - w.length := by
    change Cᶜ.card = _
    rw [Finset.card_compl, vertices, cardC]
  have cardU : Fintype.card U = 11 - w.length := by
    have coeCard : Fintype.card U = O.card := by simp [U]
    exact coeCard.trans cardO
  have lengthBound : w.length ≤ 11 :=
    cardC ▸ vertices ▸ Finset.card_le_univ C
  have nearBound (x : V) : nearC x ≤ 2 :=
    count_cycle_neighbors w odd shortest triangleFree
  have crossingBound : crossings ≤ 2 * (11 - w.length) := by
    calc
      crossings ≤ ∑ _x ∈ O, (2 : ℕ) := Finset.sum_le_sum (fun x _ => nearBound x)
      _ = _ := by simp [cardO, Nat.mul_comm]
  have outsideFree : (G.induce U).CliqueFree 3 :=
    triangleFree.comap (Embedding.induce _).isContained
  have outsideBound := CliqueFree.card_edgeFinset_le (r := 2) outsideFree
  dsimp only at outsideBound
  rw [cardU] at outsideBound
  have enough : 26 ≤ w.length + crossings + outside :=
    dense.trans (count_core w odd shortest)
  obtain ⟨five, twelve, nine⟩ := dense_counts w.length crossings outside
    (shortest_length_lower triangleFree odd) lengthBound odd crossingBound outsideBound enough
  refine ⟨a, w, five, odd, shortest, nine, ?_⟩
  intro x hx
  change nearC x = 2
  by_contra ne
  have lt := lt_of_le_of_ne (nearBound x) ne
  have sumLt := Finset.sum_lt_sum (fun y (_ : y ∈ O) => nearBound y)
    ⟨x, Finset.mem_compl.mpr hx, lt⟩
  have exactSum : (∑ _x ∈ O, (2 : ℕ)) = 12 := by simp [cardO, five]
  change crossings < _ at sumLt
  omega

end Counting

end Erdos23OddCore

namespace Erdos23CycleCut

open SimpleGraph Finset Erdos23RootedCuts
open scoped Classical

def cyclic (i j : Fin 5) : Prop := i + 1 = j ∨ j + 1 = i

instance (i j : Fin 5) : Decidable (cyclic i j) := inferInstanceAs (Decidable (_ ∨ _))

def side (i : Fin 5) : Prop := i = 0 ∨ i = 2 ∨ i = 3

instance (i : Fin 5) : Decidable (side i) := inferInstanceAs (Decidable (_ ∨ _ ∨ _))

theorem same_side_edge : ∀ i j : Fin 5, cyclic i j → (side i ↔ side j) →
    (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) := by decide +kernel

theorem opposite_side_nonedge : ∀ i j : Fin 5, ¬ side i → side j → ¬ cyclic i j →
    (i = 1 ∧ j = 3) ∨ (i = 4 ∧ j = 2) := by decide +kernel

theorem cut_of_cycle_types (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    (triangleFree : G.CliqueFree 3) (v : Fin 25) (degree13 : G.degree v = 13)
    (tag : {x : Fin 25 // x ∈ (insert v (G.neighborFinset v))ᶜ} → Fin 5)
    (shape : ∀ x y, G.Adj x.val y.val ↔ cyclic (tag x) (tag y))
    (onlyTwo : ∀ x y, tag x = 2 → tag y = 2 → x = y)
    (onlyThree : ∀ x y, tag x = 3 → tag y = 3 → x = y) :
    ∃ S : Finset (Fin 25), (mono G S).card ≤ 14 := by
  classical
  let A := G.neighborFinset v
  let W := (insert v A)ᶜ
  let L := W.filter (fun x => ∃ hx : x ∈ W, side (tag ⟨x, hx⟩))
  let R := Aᶜ \ L
  have memW (x : Fin 25) : x ∈ W ↔ x ≠ v ∧ x ∉ A := by
    simp only [W, Finset.mem_compl, Finset.mem_insert, not_or]
  have ltag (x : Fin 25) (hx : x ∈ W) : x ∈ L ↔ side (tag ⟨x, hx⟩) := by
    constructor
    · intro h
      obtain ⟨h', hs⟩ := (Finset.mem_filter.mp h).2
      exact hs
    · intro h
      exact Finset.mem_filter.mpr ⟨hx, hx, h⟩
  have sub : L ⊆ Aᶜ := fun x hx =>
    Finset.mem_compl.mpr ((memW x).mp (Finset.mem_filter.mp hx).1).2
  have left : L = Aᶜ \ R := by
    ext x
    have implies : x ∈ L → x ∈ Aᶜ := fun h => sub h
    change x ∈ L ↔ x ∈ Aᶜ \ (Aᶜ \ L)
    simp only [Finset.mem_sdiff]
    tauto
  have monoEnds (e : Sym2 (Fin 25)) (he : e ∈ mono G L ∩ mono G A) :
      ∃ x y : {x : Fin 25 // x ∈ W}, tag x = 2 ∧ tag y = 3 ∧ s(x.val, y.val) = e := by
    induction e using Sym2.ind with
    | h x y =>
      obtain ⟨hl, hn⟩ := Finset.mem_inter.mp he
      obtain ⟨adj, same⟩ := (mem_mono G).mp hl
      have ⟨hx, hy⟩ := core_endpoints G v triangleFree hn
      have equal := (ltag x hx).symm.trans (same.trans (ltag y hy))
      rcases same_side_edge (tag ⟨x, hx⟩) (tag ⟨y, hy⟩) ((shape _ _).mp adj) equal with h | h
      · exact ⟨⟨x, hx⟩, ⟨y, hy⟩, h.1, h.2, rfl⟩
      · exact ⟨⟨y, hy⟩, ⟨x, hx⟩, h.2, h.1, Sym2.eq_swap⟩
  have monoBound : (mono G L ∩ mono G A).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro e he f hf
    obtain ⟨x, y, x2, y3, rfl⟩ := monoEnds e he
    obtain ⟨x', y', x'2, y'3, rfl⟩ := monoEnds f hf
    rw [onlyTwo x x' x2 x'2, onlyThree y y' y3 y'3]
  have cheapest (a : Fin 25) : min (near G a L).card (near G a R).card ≤ 1 := by
    by_contra! tooMuch
    have hL := lt_of_lt_of_le tooMuch (Nat.min_le_left (near G a L).card (near G a R).card)
    have hR := lt_of_lt_of_le tooMuch (Nat.min_le_right (near G a L).card (near G a R).card)
    obtain ⟨x, hx, y, hy, xy⟩ := Finset.one_lt_card.mp hL
    have hasB : ∃ b ∈ near G a R, b ≠ v := by
      by_contra! no
      have leOne : (near G a R).card ≤ 1 := Finset.card_le_one.mpr
        (fun s hs t ht => (no s hs).trans (no t ht).symm)
      omega
    obtain ⟨b, hb, bv⟩ := hasB
    have ⟨hbR, adjb⟩ := Finset.mem_filter.mp hb
    have br := Finset.mem_sdiff.mp hbR
    have hbW : b ∈ W := (memW b).mpr ⟨bv, Finset.mem_compl.mp br.1⟩
    have notSide : ¬ side (tag ⟨b, hbW⟩) := fun hs => br.2 ((ltag b hbW).mpr hs)
    have trueType (c : Fin 25) (hc : c ∈ near G a L) :
        ∃ hcW : c ∈ W, (tag ⟨b, hbW⟩ = 1 ∧ tag ⟨c, hcW⟩ = 3) ∨
          (tag ⟨b, hbW⟩ = 4 ∧ tag ⟨c, hcW⟩ = 2) := by
      obtain ⟨hcL, adjc⟩ := Finset.mem_filter.mp hc
      have hcW : c ∈ W := (Finset.mem_filter.mp hcL).1
      have noAdj := adj_into_neighbor G triangleFree adjb adjc
      exact ⟨hcW, opposite_side_nonedge _ _ notSide ((ltag c hcW).mp hcL)
        (fun cycle => noAdj ((shape _ _).mpr cycle))⟩
    obtain ⟨hxW, hxt⟩ := trueType x hx
    obtain ⟨hyW, hyt⟩ := trueType y hy
    rcases hxt with hxt | hxt <;> rcases hyt with hyt | hyt
    · exact xy (congrArg Subtype.val (onlyThree _ _ hxt.2 hyt.2))
    · exact (by decide : (1 : Fin 5) ≠ 4) (hxt.1.symm.trans hyt.1)
    · exact (by decide : (4 : Fin 5) ≠ 1) (hxt.1.symm.trans hyt.1)
    · exact xy (congrArg Subtype.val (onlyTwo _ _ hxt.2 hyt.2))
  obtain ⟨S, budget⟩ := rooted_cut G triangleFree v left
  refine ⟨S, budget.trans ?_⟩
  have total : (∑ a ∈ A, min (near G a L).card (near G a R).card) ≤ 13 := by
    calc
      _ ≤ ∑ _a ∈ A, (1 : ℕ) := Finset.sum_le_sum (fun a _ => cheapest a)
      _ = 13 := by simp [A, card_neighborFinset_eq_degree, degree13]
  change (mono G L ∩ mono G A).card +
    (∑ a ∈ A, min (near G a L).card (near G a R).card) ≤ 14
  omega

end Erdos23CycleCut

namespace Erdos23CycleModel

open SimpleGraph Finset Erdos23OddCore Erdos23CycleCut Erdos23Degree13
open scoped Classical

variable {V : Type} {G : SimpleGraph V}

private theorem cyclic_nat : ∀ i j : Fin 5, cyclic i j ↔
    j.val = i.val + 1 ∨ j.val + 1 = i.val + 5 ∨
      i.val = j.val + 1 ∨ i.val + 1 = j.val + 5 := by decide +kernel

private theorem cyclic_pair : ∀ i j : Fin 5, cyclic i j ↔
    j = i - 1 ∨ j = i + 1 := by decide +kernel

private theorem cyclic_disjoint : ∀ i j : Fin 5,
    Disjoint (c5Pair i) (c5Pair j) ↔ cyclic i j := by decide +kernel

private theorem pair_type_exists : ∀ i j : Fin 5, i ≠ j → ¬ cyclic i j →
    ∃ t : Fin 5, ({i, j} : Finset (Fin 5)) = c5Pair t := by decide +kernel

private theorem no_cyclic_self : ∀ i : Fin 5, ¬ cyclic i i := by decide +kernel

private theorem no_cyclic_within_neighbors : ∀ t i j : Fin 5,
    i ∈ c5Pair t → j ∈ c5Pair t → ¬ cyclic i j := by decide +kernel

private theorem cyclic_translate : ∀ i j c : Fin 5,
    cyclic (i - c) (j - c) ↔ cyclic i j := by decide +kernel

private theorem outside_translate : ∀ i c : Fin 5,
    i = c ∨ i ∈ c5Pair c → i - c ≠ 2 ∧ i - c ≠ 3 := by decide +kernel

private theorem translate_injective : ∀ i j c : Fin 5,
    i - c = j - c → i = j := by decide +kernel

private theorem pair_mem (i j : Fin 5) : i ∈ c5Pair j ↔ cyclic j i := by
  rw [cyclic_pair]
  simp [c5Pair]

private theorem cyclic_flip (i j : Fin 5) : cyclic i j ↔ cyclic j i :=
  or_comm

def cv {a : V} (w : G.Walk a a) (i : Fin 5) : V := w.getVert i.val

theorem cv_injective {a : V} (w : G.Walk a a) (h5 : w.length = 5)
    (odd : Odd w.length)
    (shortest : ∀ b (u : G.Walk b b), Odd u.length → w.length ≤ u.length) :
    Function.Injective (cv w) := by
  intro i j eq
  have h := shortest_getVert_injective odd shortest (a₁ := i.cast h5.symm)
    (a₂ := j.cast h5.symm) eq
  exact Fin.ext (congrArg (fun k : Fin w.length => k.val) h)

theorem mem_cycle_fin5 [DecidableEq V] {a : V} (w : G.Walk a a)
    (h5 : w.length = 5) (x : V) : x ∈ cycleVerts w ↔ ∃ i : Fin 5, cv w i = x := by
  rw [mem_cycleVerts]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i.cast h5, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i.cast h5.symm, hi⟩

theorem cv_adj {a : V} (w : G.Walk a a) (h5 : w.length = 5)
    (odd : Odd w.length)
    (shortest : ∀ b (u : G.Walk b b), Odd u.length → w.length ≤ u.length)
    (i j : Fin 5) : G.Adj (cv w i) (cv w j) ↔ cyclic i j := by
  have forward (i j : Fin 5) (lt : i.val < j.val) (adj : G.Adj (cv w i) (cv w j)) :
      j.val = i.val + 1 ∨ j.val + 1 = i.val + 5 := by
    have step := shortest_edge_ends odd shortest (i := i.cast h5.symm) (j := j.cast h5.symm)
      lt adj
    simpa only [Fin.val_cast, h5] using step
  have ordinary (i j : Fin 5) (step : j.val = i.val + 1) : G.Adj (cv w i) (cv w j) := by
    unfold cv
    rw [step]
    exact w.adj_getVert_succ (by rw [h5]; exact i.isLt)
  have wrap (i j : Fin 5) (step : j.val + 1 = i.val + 5) : G.Adj (cv w i) (cv w j) := by
    have hlt := j.isLt
    have hz : i.val = 0 := by omega
    have last : j.val + 1 = w.length := by omega
    have adj := w.adj_getVert_succ (i := j.val) (by rw [h5]; exact j.isLt)
    rw [last, Walk.getVert_length] at adj
    unfold cv
    rw [hz, Walk.getVert_zero]
    exact adj.symm
  rw [cyclic_nat]
  constructor
  · intro adj
    have ne : i ≠ j := fun h => G.irrefl (h ▸ adj)
    rcases lt_or_gt_of_ne ne with lt | gt
    · rcases forward i j lt adj with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (forward j i gt adj.symm))
  · rintro (h | h | h | h)
    · exact ordinary i j h
    · exact wrap i j h
    · exact (ordinary j i h).symm
    · exact (wrap j i h).symm

theorem attachment_type [DecidableEq V] [DecidableRel G.Adj] {a : V}
    (w : G.Walk a a) (h5 : w.length = 5) (odd : Odd w.length)
    (shortest : ∀ b (u : G.Walk b b), Odd u.length → w.length ≤ u.length)
    (triangleFree : G.CliqueFree 3) (x : V)
    (two : (Erdos23RootedCuts.near G x (cycleVerts w)).card = 2) :
    ∃ t : Fin 5, ∀ i : Fin 5, G.Adj x (cv w i) ↔ i ∈ c5Pair t := by
  obtain ⟨u, v, ne, pair⟩ := Finset.card_eq_two.mp two
  have memU : u ∈ Erdos23RootedCuts.near G x (cycleVerts w) := by rw [pair]; simp
  have memV : v ∈ Erdos23RootedCuts.near G x (cycleVerts w) := by rw [pair]; simp
  obtain ⟨hu, xu⟩ := Finset.mem_filter.mp memU
  obtain ⟨hv, xv⟩ := Finset.mem_filter.mp memV
  obtain ⟨i, rfl⟩ := (mem_cycle_fin5 w h5 u).mp hu
  obtain ⟨j, rfl⟩ := (mem_cycle_fin5 w h5 v).mp hv
  have diff : i ≠ j := fun eq => ne (congrArg (cv w) eq)
  have notCyclic : ¬ cyclic i j := fun h => Erdos23RootedCuts.adj_into_neighbor G triangleFree
    xu xv ((cv_adj w h5 odd shortest i j).mpr h)
  obtain ⟨t, ht⟩ := pair_type_exists i j diff notCyclic
  refine ⟨t, fun k => ?_⟩
  have embed : cv w k ∈ cycleVerts w := (mem_cycle_fin5 w h5 _).mpr ⟨k, rfl⟩
  have near : G.Adj x (cv w k) ↔ cv w k ∈ Erdos23RootedCuts.near G x (cycleVerts w) :=
    ⟨fun e => Finset.mem_filter.mpr ⟨embed, e⟩, fun e => (Finset.mem_filter.mp e).2⟩
  rw [near, pair, ← ht]
  simp only [Finset.mem_insert, Finset.mem_singleton, (cv_injective w h5 odd shortest).eq_iff]

def even6 (i : Fin 3) : Fin 6 := ⟨2 * i.val, by have := i.isLt; omega⟩

def odd6 (i : Fin 3) : Fin 6 := ⟨2 * i.val + 1, by have := i.isLt; omega⟩

private theorem parity6 : ∀ i : Fin 6, (∃ j : Fin 3, i = even6 j) ∨
    (∃ j : Fin 3, i = odd6 j) := by decide +kernel

private theorem across6 : ∀ i j : Fin 3, (turanGraph 6 2).Adj (even6 i) (odd6 j) := by
  decide +kernel

private theorem even_nonedges6 : ∀ i j : Fin 3, ¬ (turanGraph 6 2).Adj (even6 i) (even6 j) := by
  decide +kernel

private theorem odd_nonedges6 : ∀ i j : Fin 3, ¬ (turanGraph 6 2).Adj (odd6 i) (odd6 j) := by
  decide +kernel


private theorem parity_type_model (f : Fin 6 → Fin 5)
    (compatible : ∀ i j : Fin 3, Disjoint (c5Pair (f (even6 i))) (c5Pair (f (odd6 j)))) :
    ∃ c : Fin 5, (∀ i, f i = c ∨ f i ∈ c5Pair c) ∧
      ∀ i j, (turanGraph 6 2).Adj i j ↔ cyclic (f i) (f j) := by
  obtain ⟨c, center⟩ : ∃ c : Fin 5,
      ((∀ i : Fin 3, f (even6 i) = c) ∧ (∀ j : Fin 3, f (odd6 j) ∈ c5Pair c)) ∨
        ((∀ j : Fin 3, f (odd6 j) = c) ∧ (∀ i : Fin 3, f (even6 i) ∈ c5Pair c)) := by
    rcases opposite_type_center (fun i => f (even6 i)) (fun j => f (odd6 j)) compatible with
      h | h
    · refine ⟨f (even6 0), Or.inl ⟨h.1, fun j => ?_⟩⟩
      exact (pair_mem _ _).mpr ((cyclic_pair _ _).mpr (h.2 j))
    · refine ⟨f (odd6 0), Or.inr ⟨h.1, fun i => ?_⟩⟩
      exact (pair_mem _ _).mpr ((cyclic_pair _ _).mpr (h.2 i))
  have evenConflict (i j : Fin 3) : ¬ cyclic (f (even6 i)) (f (even6 j)) := by
    rcases center with e | o
    · rw [e.1 i, e.1 j]
      exact no_cyclic_self c
    · exact no_cyclic_within_neighbors c _ _ (o.2 i) (o.2 j)
  have oddConflict (i j : Fin 3) : ¬ cyclic (f (odd6 i)) (f (odd6 j)) := by
    rcases center with e | o
    · exact no_cyclic_within_neighbors c _ _ (e.2 i) (e.2 j)
    · rw [o.1 i, o.1 j]
      exact no_cyclic_self c
  refine ⟨c, ?_, ?_⟩
  · intro i
    rcases parity6 i with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rcases center with h | h
      · exact Or.inl (h.1 k)
      · exact Or.inr (h.2 k)
    · rcases center with h | h
      · exact Or.inr (h.2 k)
      · exact Or.inl (h.1 k)
  · intro i j
    rcases parity6 i with ⟨s, rfl⟩ | ⟨s, rfl⟩ <;>
      rcases parity6 j with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · exact iff_of_false (even_nonedges6 s t) (evenConflict s t)
    · exact iff_of_true (across6 s t) ((cyclic_disjoint _ _).mp (compatible s t))
    · exact iff_of_true (across6 t s).symm
        ((cyclic_flip _ _).mp ((cyclic_disjoint _ _).mp (compatible t s)))
    · exact iff_of_false (odd_nonedges6 s t) (oddConflict s t)

theorem eleven_blowup [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (vertices : Fintype.card V = 11) (triangleFree : G.CliqueFree 3)
    (dense : 26 ≤ G.edgeFinset.card) (nonbipartite : ¬ G.IsBipartite) :
    ∃ tag : V → Fin 5, (∀ x y, G.Adj x y ↔ cyclic (tag x) (tag y)) ∧
      (∀ x y, tag x = 2 → tag y = 2 → x = y) ∧
      (∀ x y, tag x = 3 → tag y = 3 → x = y) := by
  classical
  obtain ⟨a, w, h5, odd, shortest, outsideEdges, two⟩ :=
    dense_eleven_cycle vertices triangleFree dense nonbipartite
  let C := cycleVerts w
  let O : Set V := ↑(Cᶜ)
  have numberOutside : Fintype.card O = 6 := by
    have card : Fintype.card O = Cᶜ.card :=
      Fintype.card_of_finset' Cᶜ (fun _ => Iff.rfl)
    rw [card, Finset.card_compl, vertices, show C.card = w.length from card_cycleVerts w odd shortest, h5]
  have outsideFree : (G.induce O).CliqueFree 3 :=
    triangleFree.comap (Embedding.induce _).isContained
  obtain ⟨iso⟩ := six_mantel (G.induce O) numberOutside outsideFree (by
    convert outsideEdges using 1
    apply congrArg Finset.card
    ext e
    simp only [mem_edgeFinset, O, C])
  have existence (x : O) :
      ∃ t : Fin 5, ∀ i : Fin 5, G.Adj x.val (cv w i) ↔ i ∈ c5Pair t :=
    attachment_type w h5 odd shortest triangleFree x.val
      (two x.val (Finset.mem_compl.mp x.property))
  let external : O → Fin 5 := fun x => Classical.choose (existence x)
  have externalSpec (x : O) (i : Fin 5) :
      G.Adj x.val (cv w i) ↔ i ∈ c5Pair (external x) :=
    Classical.choose_spec (existence x) i
  let f : Fin 6 → Fin 5 := fun i => external (iso.symm i)
  have compatible (i j : Fin 3) :
      Disjoint (c5Pair (f (even6 i))) (c5Pair (f (odd6 j))) := by
    apply Finset.disjoint_left.mpr
    intro k hkLeft hkRight
    let l := iso.symm (even6 i)
    let r := iso.symm (odd6 j)
    have lr : G.Adj l.val r.val := by
      change (G.induce O).Adj l r
      apply iso.map_adj_iff.mp
      simpa [l, r] using across6 i j
    have lk := (externalSpec l k).mpr hkLeft
    have rk := (externalSpec r k).mpr hkRight
    exact Erdos23RootedCuts.adj_into_neighbor G triangleFree lk.symm rk.symm lr
  obtain ⟨c, classes, adjParity⟩ := parity_type_model f compatible
  have externalShape (x y : O) :
      G.Adj x.val y.val ↔ cyclic (external x) (external y) := by
    have eq := adjParity (iso x) (iso y)
    change (G.induce O).Adj x y ↔ _
    rw [← iso.map_adj_iff]
    simpa [f] using eq
  have existsIdx (x : V) (hx : x ∈ C) : ∃ i : Fin 5, cv w i = x :=
    (mem_cycle_fin5 w h5 x).mp hx
  let idx (x : V) (hx : x ∈ C) := Classical.choose (existsIdx x hx)
  have idxSpec (x : V) (hx : x ∈ C) : cv w (idx x hx) = x :=
    Classical.choose_spec (existsIdx x hx)
  let out (x : V) (hx : x ∉ C) : O := ⟨x, Finset.mem_compl.mpr hx⟩
  let raw (x : V) := if hx : x ∈ C then idx x hx else external (out x hx)
  have rawShape (x y : V) : G.Adj x y ↔ cyclic (raw x) (raw y) := by
    by_cases hx : x ∈ C <;> by_cases hy : y ∈ C
    · simp only [raw, dif_pos hx, dif_pos hy]
      calc
        G.Adj x y ↔ G.Adj (cv w (idx x hx)) (cv w (idx y hy)) := by rw [idxSpec x hx, idxSpec y hy]
        _ ↔ _ := cv_adj w h5 odd shortest _ _
    · simp only [raw, dif_pos hx, dif_neg hy]
      calc
        G.Adj x y ↔ G.Adj (out y hy).val (cv w (idx x hx)) := by
          rw [idxSpec x hx]
          exact G.adj_comm x y
        _ ↔ idx x hx ∈ c5Pair (external (out y hy)) := externalSpec _ _
        _ ↔ _ := (pair_mem _ _).trans (cyclic_flip _ _)
    · simp only [raw, dif_neg hx, dif_pos hy]
      calc
        G.Adj x y ↔ G.Adj (out x hx).val (cv w (idx y hy)) := by rw [idxSpec y hy]
        _ ↔ idx y hy ∈ c5Pair (external (out x hx)) := externalSpec _ _
        _ ↔ _ := pair_mem _ _
    · simpa only [raw, dif_neg hx, dif_neg hy] using externalShape (out x hx) (out y hy)
  have outsideCannot (x : V) (hx : x ∉ C) : raw x - c ≠ 2 ∧ raw x - c ≠ 3 := by
    apply outside_translate
    simpa [raw, hx, f] using classes (iso (out x hx))
  have unique (k : Fin 5) (hk : k = 2 ∨ k = 3) (x y : V)
      (ex : raw x - c = k) (ey : raw y - c = k) : x = y := by
    have onCycle (a : V) (ha : raw a - c = k) : a ∈ C := by
      by_contra notOn
      rcases hk with h2 | h3
      · exact (outsideCannot a notOn).1 (ha.trans h2)
      · exact (outsideCannot a notOn).2 (ha.trans h3)
    have xc := onCycle x ex
    have yc := onCycle y ey
    have same : raw x = raw y := translate_injective _ _ c (ex.trans ey.symm)
    have sameIdx : idx x xc = idx y yc := by simpa [raw, xc, yc] using same
    exact (idxSpec x xc).symm.trans ((congrArg (cv w) sameIdx).trans (idxSpec y yc))
  exact ⟨fun x => raw x - c, fun x y => (rawShape x y).trans (cyclic_translate _ _ c).symm,
    unique 2 (Or.inl rfl), unique 3 (Or.inr rfl)⟩

end Erdos23CycleModel

open SimpleGraph Finset

open Erdos23Degree13 Erdos23CycleModel Erdos23CycleCut Erdos23RootedCuts in
theorem OMA.solution : OMA.R_Erdos23_erdos_23_variants_n5_R1_H2_R1.H3 := by
  intro G inst triangleFree v degree13 residual nonbipartite
  classical
  let W : Finset (Fin 25) := rootCore G v
  let U : Set (Fin 25) := W
  let H := G.induce U
  have vertices : Fintype.card U = 11 := by
    have card : Fintype.card U = W.card := by simp [U]
    exact card.trans (rootCore_card G v degree13)
  have free : H.CliqueFree 3 := triangleFree.comap (Embedding.induce _).isContained
  have dense : 26 ≤ H.edgeFinset.card := (rootCore_bounds G triangleFree v degree13 residual).1
  obtain ⟨tag, shape, onlyTwo, onlyThree⟩ := eleven_blowup (G := H) vertices free dense nonbipartite
  obtain ⟨S, hS⟩ := cut_of_cycle_types G triangleFree v degree13 tag shape onlyTwo onlyThree
  refine ⟨S, ?_⟩
  rw [← mono_matches G S]
  exact hS.trans (by decide)