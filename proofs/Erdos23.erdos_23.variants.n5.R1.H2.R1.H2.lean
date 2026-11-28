import OMAReductions.R_Erdos23_erdos_23_variants_n5_R1_H2_R1
import Mathlib

/-! The bipartite induced core at a degree-13 root supplies two explicit cut orientations. -/

namespace Erdos23Degree13

open Finset

private theorem all_two (f : Fin 13 → ℕ) (bound : ∀ i, f i ≤ 2)
    (large : 25 < ∑ i, f i) (i : Fin 13) : f i = 2 := by
  by_contra different
  have strict := lt_of_le_of_ne (bound i) different
  have total := Finset.sum_lt_sum (fun j (_ : j ∈ univ) => bound j) ⟨i, mem_univ _, strict⟩
  have two : (∑ _j : Fin 13, (2 : ℕ)) = 26 := by simp
  rw [two] at total
  omega

/-- Both bipartition orientations cannot cost 26 when the two sides have at
most four missing cross edges and the rooted graph has at least 93 edges. -/
theorem bipartite_cut_counts (core : ℕ) (left right : Fin 13 → ℕ)
    (dense : 26 ≤ core)
    (missing : ∀ i, core + left i * right i ≤ 30)
    (edges : 93 ≤ 13 + core + ∑ i, (left i + right i)) :
    (∑ i, min (1 + left i) (right i)) ≤ 25 ∨
      (∑ i, min (left i) (1 + right i)) ≤ 25 := by
  have first (i : Fin 13) : min (1 + left i) (right i) ≤ 2 := by
    by_contra! large
    have hl := Nat.min_le_left (1 + left i) (right i)
    have hr := Nat.min_le_right (1 + left i) (right i)
    have prod := Nat.mul_le_mul (show 2 ≤ left i by omega) (show 3 ≤ right i by omega)
    have hi := missing i
    omega
  have second (i : Fin 13) : min (left i) (1 + right i) ≤ 2 := by
    by_contra! large
    have hl := Nat.min_le_left (left i) (1 + right i)
    have hr := Nat.min_le_right (left i) (1 + right i)
    have prod := Nat.mul_le_mul (show 3 ≤ left i by omega) (show 2 ≤ right i by omega)
    have hi := missing i
    omega
  by_contra! bad
  have small (i : Fin 13) : left i = 2 ∧ right i = 2 ∧ core = 26 := by
    have h₁ := all_two _ first bad.1 i
    have h₂ := all_two _ second bad.2 i
    have hl := Nat.min_le_left (left i) (1 + right i)
    have hr := Nat.min_le_right (1 + left i) (right i)
    have hl₂ : 2 ≤ left i := by omega
    have hr₂ : 2 ≤ right i := by omega
    have prod := Nat.mul_le_mul hl₂ hr₂
    have hi := missing i
    have hc : core = 26 := by omega
    have left_le : left i ≤ 2 := by
      by_contra! large
      have badProduct := Nat.mul_le_mul (show 3 ≤ left i by omega) hr₂
      omega
    have right_le : right i ≤ 2 := by
      by_contra! large
      have badProduct := Nat.mul_le_mul hl₂ (show 3 ≤ right i by omega)
      omega
    omega
  have cross : (∑ i, (left i + right i)) = 52 := by
    calc
      (∑ i, (left i + right i)) = ∑ _i : Fin 13, (4 : ℕ) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [(small i).1, (small i).2.1]
      _ = 52 := by simp
  have c := (small 0).2.2
  omega

theorem balanced_capacity (left right : ℕ) (total : left + right = 11) :
    left * right ≤ 30 := by
  have h : left ≤ 11 := by omega
  interval_cases left <;> omega

section RootedGraph

open SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V]

def rootCore (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  (insert v (G.neighborFinset v))ᶜ

theorem rootCore_card (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (v : Fin 25)
    (degree13 : G.degree v = 13) : (rootCore G v).card = 11 := by
  rw [rootCore, Finset.card_compl, Fintype.card_fin, Finset.card_insert_of_notMem
    (by simp), card_neighborFinset_eq_degree, degree13]

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


omit [Fintype V] in
theorem bipartite_parts (G : SimpleGraph V) (W : Finset V)
    (bipartite : (G.induce (W : Set V)).IsBipartite) :
    ∃ L R : Finset V, L ∪ R = W ∧ Disjoint L R ∧
      ∀ x ∈ W, ∀ y ∈ W, G.Adj x y → (x ∈ L ∧ y ∈ R) ∨ (y ∈ L ∧ x ∈ R) := by
  obtain ⟨color⟩ := bipartite
  let L := W.filter (fun x => ∃ hx : x ∈ W, color ⟨x, hx⟩ = 0)
  let R := W \ L
  have subset : L ⊆ W := Finset.filter_subset _ _
  refine ⟨L, R, ?_, ?_, ?_⟩
  · exact Finset.union_sdiff_of_subset subset
  · exact Finset.disjoint_sdiff
  · intro x hx y hy adj
    have diff : color ⟨x, hx⟩ ≠ color ⟨y, hy⟩ := color.valid adj
    have value (a : V) (ha : a ∈ W) : a ∈ L ↔ color ⟨a, ha⟩ = 0 := by
      constructor
      · rintro h
        obtain ⟨h', hh⟩ := (Finset.mem_filter.mp h).2
        exact hh
      · intro h
        exact Finset.mem_filter.mpr ⟨ha, ha, h⟩
    by_cases hc : color ⟨x, hx⟩ = 0
    · exact Or.inl ⟨(value x hx).mpr hc, Finset.mem_sdiff.mpr ⟨hy, fun h =>
        diff (hc.trans ((value y hy).mp h).symm)⟩⟩
    · have hcy : color ⟨y, hy⟩ = 0 := by
        have cx : (color ⟨x, hx⟩).val < 2 := (color ⟨x, hx⟩).isLt
        have cy : (color ⟨y, hy⟩).val < 2 := (color ⟨y, hy⟩).isLt
        simp only [← Fin.val_inj, Fin.val_zero] at hc diff ⊢
        omega
      exact Or.inr ⟨(value y hy).mpr hcy, Finset.mem_sdiff.mpr ⟨hx, fun h =>
        hc ((value x hx).mp h)⟩⟩

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

theorem core_le_cross (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (triangleFree : G.CliqueFree 3) {L R : Finset V}
    (cross : ∀ x ∈ (insert v (G.neighborFinset v))ᶜ,
      ∀ y ∈ (insert v (G.neighborFinset v))ᶜ, G.Adj x y →
        (x ∈ L ∧ y ∈ R) ∨ (y ∈ L ∧ x ∈ R)) :
    (mono G (G.neighborFinset v)).card ≤ (G.interedges L R).card := by
  apply Finset.card_le_card_of_surjOn (fun p : V × V => s(p.1, p.2))
  intro e he
  change e ∈ mono G (G.neighborFinset v) at he
  induction e using Sym2.ind with
  | h x y =>
    have adj := ((mem_mono G).mp he).1
    have ⟨hx, hy⟩ := core_endpoints G v triangleFree he
    rcases cross x hx y hy adj with ⟨hxl, hyr⟩ | ⟨hyl, hxr⟩
    · exact ⟨(x, y), G.mk_mem_interedges_iff.mpr ⟨hxl, hyr, adj⟩, rfl⟩
    · exact ⟨(y, x), G.mk_mem_interedges_iff.mpr ⟨hyl, hxr, adj.symm⟩, Sym2.eq_swap⟩

omit [Fintype V] [DecidableEq V] in
theorem cross_capacity (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangleFree : G.CliqueFree 3) (a : V) (L R : Finset V) :
    (G.interedges L R).card + (near G a L).card * (near G a R).card ≤ L.card * R.card := by
  let missing := (L ×ˢ R).filter (fun p => ¬ G.Adj p.1 p.2)
  have subset : near G a L ×ˢ near G a R ⊆ missing := by
    rintro ⟨x, y⟩ h
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp h
    obtain ⟨hxL, hax⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyR, hay⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hxL, hyR⟩,
      adj_into_neighbor G triangleFree hax hay⟩
  have card := Finset.card_le_card subset
  rw [Finset.card_product] at card
  have sum := Finset.card_filter_add_card_filter_not (s := L ×ˢ R)
    (fun p => G.Adj p.1 p.2)
  change (G.interedges L R).card + missing.card = (L ×ˢ R).card at sum
  rw [Finset.card_product] at sum
  omega

omit [Fintype V] in
theorem near_root_add (G : SimpleGraph V) [DecidableRel G.Adj]
    {a v : V} (adj : G.Adj a v) {T : Finset V} (hv : v ∉ T) :
    (near G a (insert v T)).card = 1 + (near G a T).card := by
  simp only [near, Finset.filter_insert, adj, if_true]
  rw [Finset.card_insert_of_notMem (fun h => hv (Finset.mem_filter.mp h).1), Nat.add_comm]

theorem degree_from_core (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangleFree : G.CliqueFree 3) (v : V) (L R : Finset V)
    (partition : L ∪ R = (insert v (G.neighborFinset v))ᶜ)
    (disjoint : Disjoint L R) (a : V) (ha : a ∈ G.neighborFinset v) :
    G.degree a = 1 + (near G a L).card + (near G a R).card := by
  have vnot : v ∉ L ∪ R := by simp [partition]
  have incident_all : G.neighborFinset a = near G a (insert v (L ∪ R)) := by
    ext x
    rw [mem_neighborFinset, near, Finset.mem_filter]
    refine ⟨fun hadj => ⟨?_, hadj⟩, And.right⟩
    by_cases eq : x = v
    · simp [eq]
    · have nx : x ∉ G.neighborFinset v := fun h =>
        neighbor_independent G triangleFree v a ha x h hadj
      simp [partition, nx]
  rw [← card_neighborFinset_eq_degree, incident_all,
    near_root_add G ((mem_neighborFinset G v a).mp ha).symm vnot,
    near_union_card G a disjoint]
  omega

theorem bipartite_core_mono_empty (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (triangleFree : G.CliqueFree 3) {L R S : Finset V}
    (disjoint : Disjoint L R)
    (cross : ∀ x ∈ (insert v (G.neighborFinset v))ᶜ,
      ∀ y ∈ (insert v (G.neighborFinset v))ᶜ, G.Adj x y →
        (x ∈ L ∧ y ∈ R) ∨ (y ∈ L ∧ x ∈ R))
    (agrees : ∀ x ∈ (insert v (G.neighborFinset v))ᶜ, x ∈ S ↔ x ∈ L) :
    mono G S ∩ mono G (G.neighborFinset v) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e h
  obtain ⟨hs, hn⟩ := Finset.mem_inter.mp h
  induction e using Sym2.ind with
  | h x y =>
    have ⟨adj, same⟩ := (mem_mono G).mp hs
    have ⟨hx, hy⟩ := core_endpoints G v triangleFree hn
    have equal := (agrees x hx).symm.trans (same.trans (agrees y hy))
    rcases cross x hx y hy adj with ⟨hxl, hyr⟩ | ⟨hyl, hxr⟩
    · exact Finset.disjoint_left.mp disjoint (equal.mp hxl) hyr
    · exact Finset.disjoint_left.mp disjoint (equal.mpr hyl) hxr

end Erdos23RootedCuts

open SimpleGraph Finset

open Erdos23Degree13 Erdos23RootedCuts in
theorem OMA.solution : OMA.R_Erdos23_erdos_23_variants_n5_R1_H2_R1.H2 := by
  intro G inst triangleFree lo v degree13 residual bipartite
  classical
  let A := G.neighborFinset v
  let W := rootCore G v
  have acard : A.card = 13 := (card_neighborFinset_eq_degree G v).trans degree13
  have wcard : W.card = 11 := rootCore_card G v degree13
  have memW (a : Fin 25) : a ∈ W ↔ a ≠ v ∧ a ∉ A := by
    simp only [W, rootCore, A, Finset.mem_compl, Finset.mem_insert, not_or]
  have vnotA : v ∉ A := by simp [A]
  obtain ⟨L, R, partition, disjoint, cross⟩ := bipartite_parts G W bipartite
  have bothLeft : L ⊆ W := fun _ hx => partition ▸ Finset.mem_union_left R hx
  have bothRight : R ⊆ W := fun _ hx => partition ▸ Finset.mem_union_right L hx
  have vnotL : v ∉ L := fun h => ((memW v).mp (bothLeft h)).1 rfl
  have vnotR : v ∉ R := fun h => ((memW v).mp (bothRight h)).1 rfl
  have orient (X Y : Finset (Fin 25)) (pieces : X ∪ Y = W) (apart : Disjoint X Y) :
      insert v X = Aᶜ \ Y := by
    ext x
    have cover : x ∈ X ∨ x ∈ Y ↔ x ∈ W := by rw [← pieces, Finset.mem_union]
    have exclusive : x ∈ X → x ∉ Y := fun hx hy => Finset.disjoint_left.mp apart hx hy
    have coverRoot : v ∈ X ∨ v ∈ Y ↔ v ∈ W := by rw [← pieces, Finset.mem_union]
    have vnotY : v ∉ Y := fun hy => ((memW v).mp (coverRoot.mp (Or.inr hy))).1 rfl
    simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_compl]
    by_cases eq : x = v
    · subst x
      simp [vnotA, vnotY]
    · rw [memW] at cover
      tauto
  have sizes : L.card + R.card = 11 := by
    rw [← Finset.card_union_of_disjoint disjoint, partition, wcard]
  have capacity := balanced_capacity L.card R.card sizes
  let l := fun a => (near G a L).card
  let r := fun a => (near G a R).card
  let core := (mono G A).card
  have dense : 26 ≤ core := by
    rw [show core = (mono G (G.neighborFinset v)).card from rfl, mono_matches]
    exact residual
  have core_cross : core ≤ (G.interedges L R).card := core_le_cross G v triangleFree cross
  have missing a : core + l a * r a ≤ 30 :=
    ((Nat.add_le_add_right core_cross _).trans (cross_capacity G triangleFree a L R)).trans capacity
  have total : core + (∑ a ∈ A, G.degree a) = G.edgeFinset.card := by
    have actual := OMA.R_Erdos23_erdos_23_variants_n5_R1.cut_card_nbhd
      (fun S e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))
      OMA.R_Erdos23_erdos_23_variants_n5_R1.same_mk G triangleFree v
    convert actual using 2
    change (mono G A).card = _
    apply congrArg Finset.card
    ext e
    simp only [A, mono, Finset.mem_filter]
  have degrees : (∑ a ∈ A, G.degree a) = 13 + ∑ a ∈ A, (l a + r a) := by
    calc
      _ = ∑ a ∈ A, (1 + (l a + r a)) := by
        refine Finset.sum_congr rfl ?_
        intro a ha
        have h := degree_from_core G triangleFree v L R partition disjoint a ha
        change G.degree a = 1 + l a + r a at h
        omega
      _ = _ := by simp [Finset.sum_add_distrib, acard]
  let index : Fin 13 ≃ ↑A := (Fintype.equivFinOfCardEq (by simpa using acard)).symm
  have sumIndex (f : Fin 25 → ℕ) : (∑ i : Fin 13, f (index i).val) = ∑ a ∈ A, f a := by
    have eq := Equiv.sum_comp index (fun a : ↑A => f a.val)
    change (∑ i : Fin 13, f (index i).val) = ∑ a ∈ A.attach, f a.val at eq
    simpa only [Finset.sum_attach] using eq
  have lower : 93 ≤ 13 + core + ∑ i : Fin 13, (l (index i).val + r (index i).val) := by
    rw [sumIndex (fun a => l a + r a)]
    omega
  have emptyL : mono G (insert v L) ∩ mono G A = ∅ := by
    apply bipartite_core_mono_empty G v triangleFree disjoint cross
    intro x hx
    simp [((memW x).mp hx).1]
  have emptyR : mono G (insert v R) ∩ mono G A = ∅ := by
    apply bipartite_core_mono_empty G v triangleFree disjoint.symm
    · intro x hx y hy hadj
      rcases cross x hx y hy hadj with h | h
      · exact Or.inr ⟨h.2, h.1⟩
      · exact Or.inl ⟨h.2, h.1⟩
    · intro x hx
      simp [((memW x).mp hx).1]
  obtain caseL | caseR := bipartite_cut_counts core (fun i => l (index i).val)
    (fun i => r (index i).val) dense (fun i => missing (index i).val) lower
  · obtain ⟨S, hs⟩ := rooted_cut G triangleFree v (orient L R partition disjoint)
    rw [show G.neighborFinset v = A from rfl, emptyL, Finset.card_empty, zero_add] at hs
    rw [sumIndex (fun a => min (1 + l a) (r a))] at caseL
    refine ⟨S, ?_⟩
    rw [← mono_matches G S]
    refine hs.trans ?_
    have budget : (∑ a ∈ A, min (near G a (insert v L)).card (near G a R).card) =
        ∑ a ∈ A, min (1 + l a) (r a) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [near_root_add G ((mem_neighborFinset G v a).mp ha).symm vnotL]
    rwa [budget]
  · have reversed : R ∪ L = W := (Finset.union_comm _ _).trans partition
    obtain ⟨S, hs⟩ := rooted_cut G triangleFree v (orient R L reversed disjoint.symm)
    rw [show G.neighborFinset v = A from rfl, emptyR, Finset.card_empty, zero_add] at hs
    rw [sumIndex (fun a => min (l a) (1 + r a))] at caseR
    refine ⟨S, ?_⟩
    rw [← mono_matches G S]
    refine hs.trans ?_
    have budget : (∑ a ∈ A, min (near G a (insert v R)).card (near G a L).card) =
        ∑ a ∈ A, min (l a) (1 + r a) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [near_root_add G ((mem_neighborFinset G v a).mp ha).symm vnotR]
      exact Nat.min_comm _ _
    rwa [budget]