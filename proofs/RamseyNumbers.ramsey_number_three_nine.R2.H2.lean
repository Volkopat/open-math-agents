import OMAReductions.R_RamseyNumbers_ramsey_number_three_nine_R2
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic.FinCases

/-!
# Classification of 21-vertex 51-edge (3,7)-Ramsey graphs

We prove `OMA.R_RamseyNumbers_ramsey_number_three_nine_R2.H2`: every triangle-free graph on 21
vertices with 51 edges and independence number at most 6 has a vertex ordering whose forward
adjacency code is one of the four published codes.

The small Ramsey bounds R(3,2)..R(3,6) and root-splitting machinery adapt
`RamseyNumbers.ramsey_number_three_nine.R1.H2.R1.H2.R1.H1` and
`RamseyNumbers.ramsey_number_three_nine.R2.H3`.
-/

namespace OMA.Ramsey37Density

open RamseyNumbers SimpleGraph Finset
lemma degree_lt {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hc : Gᶜ.CliqueFree k) (v : Fin n) : G.degree v < k := by
  by_contra! h
  apply hc.mono h (G.neighborFinset v)
  refine ⟨?_, rfl⟩
  rw [G.coe_neighborFinset, G.isClique_compl]
  exact G.isIndepSet_neighborSet_of_triangleFree hG v

lemma nonneighbors_lt {n k m : ℕ} (hr : IsGraphRamsey m 3 k)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (hc : Gᶜ.CliqueFree (k + 1)) (v : Fin n) : Gᶜ.degree v < m := by
  classical
  by_contra! h
  obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin m) (s := Gᶜ.neighborFinset v) (by simpa using h)
  have hv (i : Fin m) : Gᶜ.Adj v (f i) :=
    (Gᶜ.mem_neighborFinset v (f i)).mp (hf ⟨i, rfl⟩)
  let H := G.comap f
  let e : H ↪g G := SimpleGraph.Embedding.comap f G
  let ec : Hᶜ ↪g Gᶜ := SimpleGraph.Embedding.complEquiv e
  apply hr H
  refine ⟨CliqueFree.comap e.isContained hG, ?_⟩
  intro t ht
  have hs : Gᶜ.IsNClique k (t.map f) := by
    refine ⟨?_, (Finset.card_map _).trans ht.card_eq⟩
    intro x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hy
    exact ec.map_adj_iff.mpr (ht.isClique hi hj (fun he => hxy (congrArg f he)))
  apply hc _ (hs.insert (a := v) ?_)
  intro w hw
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hw
  exact hv i

lemma three_works : IsGraphRamsey 3 3 2 := by
  classical
  rintro G ⟨hG, hc⟩
  apply hG Finset.univ
  refine ⟨?_, by simp⟩
  intro u _ v _ hne
  by_contra h
  apply hc {u, v}
  refine ⟨?_, Finset.card_pair hne⟩
  intro a ha b hb hab
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  refine ⟨hab, ?_⟩
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact (hab rfl).elim
  · exact h
  · exact fun h' => h h'.symm
  · exact (hab rfl).elim

lemma six_works : IsGraphRamsey 6 3 3 := by
  classical
  rintro G ⟨hG, hc⟩
  have hd := degree_lt G hG hc 0
  have hdc := degree_lt Gᶜ hc (by simpa using hG : Gᶜᶜ.CliqueFree 3) 0
  rw [G.degree_compl, Fintype.card_fin] at hdc
  omega

lemma nine_works : IsGraphRamsey 9 3 4 := by
  classical
  rintro G ⟨hG, hc⟩
  have hdegree (v : Fin 9) : G.degree v = 3 := by
    have hd := degree_lt G hG hc v
    have hdc := nonneighbors_lt six_works G hG hc v
    rw [G.degree_compl, Fintype.card_fin] at hdc
    omega
  have hsum := G.sum_degrees_eq_twice_card_edges
  simp [hdegree] at hsum
  omega

lemma fourteen_works : IsGraphRamsey 14 3 5 := by
  classical
  rintro G ⟨hG, hc⟩
  have hd := degree_lt G hG hc 0
  have hdc := nonneighbors_lt nine_works G hG hc 0
  rw [G.degree_compl, Fintype.card_fin] at hdc
  omega

end OMA.Ramsey37Density

section Ramsey36Regular
open SimpleGraph Finset

namespace OMA.RamseyRegular

def mask : Fin 18 → Finset (Fin 18) :=
  ![∅, ∅, ∅, ∅, ∅, ∅, {1}, {2}, {3}, {4}, {1, 3}, {1, 4}, {1, 5},
    {2, 3}, {2, 4}, {2, 5}, {3, 5}, {4, 5}]

private def blocked (i j : Fin 18) : Bool :=
  decide ((1 ≤ i.val ∧ i.val < 6 ∧ 1 ≤ j.val ∧ j.val < 6) ∨
    (1 ≤ i.val ∧ i.val < 6 ∧ 6 ≤ j.val ∧ i ∉ mask j) ∨
    (∃ k : Fin 18, 1 ≤ k.val ∧ k.val < 6 ∧ k ∈ mask i ∧ k ∈ mask j ∧ 6 ≤ i.val ∧ 6 ≤ j.val))

private theorem edge_in_six {V : Type*} (G : SimpleGraph V) (hc : Gᶜ.CliqueFree 6)
    (f : Fin 18 ↪ V) (s : Finset (Fin 18)) (hs : s.card = 6) :
    ∃ i ∈ s, ∃ j ∈ s, i < j ∧ G.Adj (f i) (f j) := by
  classical
  by_contra! hn
  apply hc (s.map f)
  refine ⟨?_, (card_map ..).trans hs⟩
  intro x hx y hy hne
  obtain ⟨i, hi, rfl⟩ := mem_map.mp hx
  obtain ⟨j, hj, rfl⟩ := mem_map.mp hy
  refine ⟨hne, ?_⟩
  rcases lt_or_gt_of_ne (fun h => hne (congrArg f h)) with h | h
  · exact hn i hi j hj h
  · exact fun ha => hn j hj i hi h ha.symm

theorem canonical_impossible {V : Type*} (G : SimpleGraph V)
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 6) (f : Fin 18 ↪ V)
    (ha : ∀ i j : Fin 18, 1 ≤ i.val → i.val < 6 → 1 ≤ j.val → j.val < 6 →
      ¬ G.Adj (f i) (f j))
    (hab : ∀ i j : Fin 18, 1 ≤ i.val → i.val < 6 → 6 ≤ j.val →
      (G.Adj (f i) (f j) ↔ i ∈ mask j)) : False := by
  classical
  have impossible (i j : Fin 18) (h : blocked i j) : ¬ G.Adj (f i) (f j) := by
    simp only [blocked, decide_eq_true_eq] at h
    rcases h with ⟨hi, hi', hj, hj'⟩ | ⟨hi, hi', hj, hm⟩ | ⟨k, hk, hk', hki, hkj, hi, hj⟩
    · exact ha i j hi hi' hj hj'
    · exact fun hadj => hm ((hab i j hi hi' hj).mp hadj)
    · intro hadj
      exact (G.isIndepSet_neighborSet_of_triangleFree ht (f k))
        ((hab k i hk hk' hi).mpr hki) ((hab k j hk hk' hj).mpr hkj) hadj.ne hadj
  have forced (s : Finset (Fin 18)) (a b : Fin 18) (hs : s.card = 6)
      (only : ∀ i ∈ s, ∀ j ∈ s, i < j → blocked i j ∨ (i = a ∧ j = b)) :
      G.Adj (f a) (f b) := by
    obtain ⟨i, hi, j, hj, hij, he⟩ := edge_in_six G hc f s hs
    rcases only i hi j hj hij with hn | ⟨rfl, rfl⟩
    · exact (impossible i j hn he).elim
    · exact he
  have e78 := forced {1,4,5,7,8,13} 7 8 (by decide +kernel) (by decide +kernel)
  have e79 := forced {1,3,5,7,9,14} 7 9 (by decide +kernel) (by decide +kernel)
  have e716 := forced {1,4,7,13,15,16} 7 16 (by decide +kernel) (by decide +kernel)
  have e717 := forced {1,3,7,14,15,17} 7 17 (by decide +kernel) (by decide +kernel)
  let neighbors : Finset (Fin 18) := {8,9,16,17}
  have adjacent (i : Fin 18) (hi : i ∈ neighbors) : G.Adj (f 7) (f i) := by
    simp only [neighbors, mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> assumption
  let six : Finset (Fin 18) := {1,2,8,9,16,17}
  have cases : ∀ i ∈ six, ∀ j ∈ six, i < j → blocked i j ∨
      (i ∈ neighbors ∧ j ∈ neighbors) := by decide +kernel
  obtain ⟨i, hi, j, hj, hij, he⟩ := edge_in_six G hc f six (by decide +kernel)
  rcases cases i hi j hj hij with hn | ⟨hni, hnj⟩
  · exact impossible i j hn he
  · exact (G.isIndepSet_neighborSet_of_triangleFree ht (f 7))
      (adjacent i hni) (adjacent j hnj) he.ne he

end OMA.RamseyRegular

namespace OMA.RamseyRegular

def shape : Fin 15 → Finset (Fin 5) :=
  ![{0}, {1}, {2}, {3}, {4}, {0, 1}, {0, 2}, {0, 3}, {0, 4}, {1, 2}, {1, 3}, {1, 4}, {2, 3}, {2, 4}, {3, 4}]

def template : Fin 12 → Finset (Fin 5) :=
  ![{0}, {1}, {2}, {3}, {0, 2}, {0, 3}, {0, 4}, {1, 2}, {1, 3}, {1, 4}, {2, 4}, {3, 4}]

def permRow : Fin 15 → Fin 5 → Fin 5 :=
  ![![1, 2, 3, 4, 0],
    ![1, 3, 2, 4, 0],
    ![1, 4, 2, 3, 0],
    ![0, 2, 3, 4, 1],
    ![0, 3, 2, 4, 1],
    ![0, 4, 2, 3, 1],
    ![0, 1, 3, 4, 2],
    ![0, 3, 1, 4, 2],
    ![0, 4, 1, 3, 2],
    ![0, 1, 2, 4, 3],
    ![0, 2, 1, 4, 3],
    ![0, 4, 1, 2, 3],
    ![0, 1, 2, 3, 4],
    ![0, 2, 1, 3, 4],
    ![0, 3, 1, 2, 4]]

def imageIndex : Fin 15 → Fin 12 → Fin 15 :=
  ![![1, 2, 3, 4, 10, 11, 5, 12, 13, 6, 7, 8],
    ![1, 3, 2, 4, 9, 11, 5, 12, 14, 7, 6, 8],
    ![1, 4, 2, 3, 9, 10, 5, 13, 14, 8, 6, 7],
    ![0, 2, 3, 4, 7, 8, 5, 12, 13, 9, 10, 11],
    ![0, 3, 2, 4, 6, 8, 5, 12, 14, 10, 9, 11],
    ![0, 4, 2, 3, 6, 7, 5, 13, 14, 11, 9, 10],
    ![0, 1, 3, 4, 7, 8, 6, 10, 11, 9, 12, 13],
    ![0, 3, 1, 4, 5, 8, 6, 10, 14, 12, 9, 13],
    ![0, 4, 1, 3, 5, 7, 6, 11, 14, 13, 9, 12],
    ![0, 1, 2, 4, 6, 8, 7, 9, 11, 10, 12, 14],
    ![0, 2, 1, 4, 5, 8, 7, 9, 13, 12, 10, 14],
    ![0, 4, 1, 2, 5, 6, 7, 11, 13, 14, 10, 12],
    ![0, 1, 2, 3, 6, 7, 8, 9, 10, 11, 13, 14],
    ![0, 2, 1, 3, 5, 7, 8, 9, 12, 13, 11, 14],
    ![0, 3, 1, 2, 5, 6, 8, 10, 12, 14, 11, 13]]

private theorem row_injective (r : Fin 15) : Function.Injective (permRow r) := by
  exact (show ∀ d i j, permRow d i = permRow d j → i = j by decide +kernel) r

def patternPerm (r : Fin 15) : Fin 5 ↪ Fin 5 :=
  ⟨permRow r, row_injective r⟩

private theorem image_correct : ∀ (r : Fin 15) (j : Fin 12),
    shape (imageIndex r j) = (template j).map (patternPerm r) := by decide +kernel

private def Covers (a b c : Fin 15) : Prop :=
  let T := ({a,b,c} : Finset (Fin 15))ᶜ
  (∀ x : Fin 5, (T.filter (fun i => x ∈ shape i)).card = 4) →
  ∃ r : Fin 15, ∀ t : Fin 12, imageIndex r t ∈ T

private instance (a b c : Fin 15) : Decidable (Covers a b c) := by
  unfold Covers
  infer_instance

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem cover : ∀ a b c, Covers a b c := by
  intro a
  fin_cases a <;> decide +kernel

theorem normalize_masks (S : Finset (Fin 15)) (hS : S.card = 12)
    (hrow : ∀ x : Fin 5, (S.filter (fun i => x ∈ shape i)).card = 4) :
    ∃ p : Fin 5 ↪ Fin 5, ∀ j : Fin 12, ∃ k ∈ S, shape k = (template j).map p := by
  have hthree : Sᶜ.card = 3 := by rw [Finset.card_compl, Fintype.card_fin, hS]
  obtain ⟨a,b,c, _, _, _, h⟩ := Finset.card_eq_three.mp hthree
  have hS' : S = ({a,b,c} : Finset (Fin 15))ᶜ := by
    simpa using congrArg (fun s : Finset (Fin 15) => sᶜ) h
  subst S
  obtain ⟨r, hr⟩ := cover a b c hrow
  exact ⟨patternPerm r, fun j => ⟨imageIndex r j, hr j, image_correct r j⟩⟩

end OMA.RamseyRegular

namespace OMA.Ramsey36Canonical


open SimpleGraph

private lemma nonneighbors_five_regular
    (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 6)
    (x : Fin 18) (hx : G.degree x = 5)
    (y : Fin 18) (hy : y ∈ Gᶜ.neighborFinset x) :
    (Gᶜ.neighborFinset x ∩ G.neighborFinset y).card ∈ ({3,4} : Finset ℕ) := by
  classical
  have hcard : (Gᶜ.neighborFinset x).card = 12 := by
    rw [Gᶜ.card_neighborFinset_eq_degree, G.degree_compl, Fintype.card_fin, hx]
  obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 12) (s := Gᶜ.neighborFinset x) (by simp [hcard])
  have hsub_map : Finset.univ.map f ⊆ Gᶜ.neighborFinset x := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hz
    exact hf ⟨i, rfl⟩
  have hmap : Finset.univ.map f = Gᶜ.neighborFinset x :=
    Finset.eq_of_subset_of_card_le hsub_map (by simp [hcard])
  let H := G.comap f
  let e : H ↪g G := SimpleGraph.Embedding.comap f G
  let ec : Hᶜ ↪g Gᶜ := SimpleGraph.Embedding.complEquiv e
  have hH : H.CliqueFree 3 := CliqueFree.comap e.isContained hG
  have hHc : Hᶜ.CliqueFree 5 := by
    intro t ht
    have hs : Gᶜ.IsNClique 5 (t.map f) := by
      refine ⟨?_, (Finset.card_map _).trans ht.card_eq⟩
      intro u hu v hv huv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hu
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hv
      exact ec.map_adj_iff.mpr (ht.isClique hi hj (fun he => huv (congrArg f he)))
    apply hc _ (hs.insert (a := x) ?_)
    intro w hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hw
    exact (Gᶜ.mem_neighborFinset x (f i)).mp (hf ⟨i, rfl⟩)
  have hdeg_all : ∀ i : Fin 12, H.degree i ∈ ({3,4} : Finset ℕ) := by
    intro i
    have hlt := OMA.Ramsey37Density.degree_lt H hH hHc i
    have hnl := OMA.Ramsey37Density.nonneighbors_lt
      OMA.Ramsey37Density.nine_works H hH hHc i
    rw [H.degree_compl, Fintype.card_fin] at hnl
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp (hmap ▸ hy)
  have hinter : Gᶜ.neighborFinset x ∩ G.neighborFinset (f i) = (H.neighborFinset i).map f := by
    ext w
    simp only [← hmap, Finset.mem_inter, Finset.mem_map, Finset.mem_univ, true_and,
      SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨⟨j, rfl⟩, hadj⟩
      exact ⟨j, hadj, rfl⟩
    · rintro ⟨j, hadj, rfl⟩
      exact ⟨⟨j, rfl⟩, hadj⟩
  rw [hinter, Finset.card_map, H.card_neighborFinset_eq_degree]
  exact hdeg_all i

theorem mask_arity (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 6) (hdeg : ∀ x, G.degree x = 5)
    (v u : Fin 18) (hu : u ∈ Gᶜ.neighborFinset v) :
    (G.neighborFinset v ∩ G.neighborFinset u).card ∈ ({1,2} : Finset ℕ) := by
  have hv := hdeg v
  let A := G.neighborFinset v
  let B := Gᶜ.neighborFinset v
  have hAB_disj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro w hwA hwB
    rw [G.mem_neighborFinset] at hwA
    rw [Gᶜ.mem_neighborFinset] at hwB
    exact hwB.2 hwA
  have hA_deg_u : ∀ u ∈ B, (A ∩ G.neighborFinset u).card ∈ ({1,2} : Finset ℕ) := by
    intro u hu
    have hB_reg := nonneighbors_five_regular G hG hc v hv u hu
    have hsub : G.neighborFinset u ⊆ A ∪ B := by
      intro w hw
      rw [G.mem_neighborFinset] at hw
      have hvw : v ≠ w := by
        rintro rfl
        exact ((Gᶜ.mem_neighborFinset v u).mp hu).2 hw.symm
      by_cases hvw_adj : G.Adj v w
      · exact Finset.mem_union_left _ ((G.mem_neighborFinset v w).mpr hvw_adj)
      · exact Finset.mem_union_right _ ((Gᶜ.mem_neighborFinset v w).mpr ⟨hvw, hvw_adj⟩)
    have hsplit : G.neighborFinset u = (A ∩ G.neighborFinset u) ∪ (B ∩ G.neighborFinset u) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · intro hw
        rcases Finset.mem_union.mp (hsub hw) with hA | hB
        · exact Or.inl ⟨hA, hw⟩
        · exact Or.inr ⟨hB, hw⟩
      · rintro (⟨_, hw⟩ | ⟨_, hw⟩) <;> exact hw
    have hdisj_u : Disjoint (A ∩ G.neighborFinset u) (B ∩ G.neighborFinset u) :=
      hAB_disj.mono Finset.inter_subset_left Finset.inter_subset_left
    have hdeg_u : G.degree u = (A ∩ G.neighborFinset u).card + (B ∩ G.neighborFinset u).card := by
      conv_lhs => rw [← G.card_neighborFinset_eq_degree, hsplit, Finset.card_union_of_disjoint hdisj_u]
    change (B ∩ G.neighborFinset u).card ∈ ({3,4} : Finset ℕ) at hB_reg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hB_reg ⊢
    have := hdeg u
    omega
  exact hA_deg_u u hu

private theorem shared_neighbor_forbids (G : SimpleGraph (Fin 18))
    (hG : G.CliqueFree 3) {a x y : Fin 18} (hx : G.Adj a x) (hy : G.Adj a y) :
    ¬ G.Adj x y := fun h =>
  G.isIndepSet_neighborSet_of_triangleFree hG a hx hy (G.ne_of_adj h) h

theorem row_degree (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hdeg : ∀ x, G.degree x = 5)
    {v a : Fin 18} (ha : a ∈ G.neighborFinset v) :
    (Gᶜ.neighborFinset v ∩ G.neighborFinset a).card = 4 := by
  have hva := (G.mem_neighborFinset v a).mp ha
  have hv_mem : v ∈ G.neighborFinset a := (G.mem_neighborFinset _ _).mpr hva.symm
  have heq : Gᶜ.neighborFinset v ∩ G.neighborFinset a = (G.neighborFinset a).erase v := by
    ext w
    simp only [Finset.mem_inter, Finset.mem_erase, Gᶜ.mem_neighborFinset, G.mem_neighborFinset]
    constructor
    · rintro ⟨⟨hvw, _⟩, haw⟩
      exact ⟨hvw.symm, haw⟩
    · rintro ⟨hwv, haw⟩
      exact ⟨⟨hwv.symm, shared_neighbor_forbids G hG hva.symm haw⟩, haw⟩
  rw [heq, Finset.card_erase_of_mem hv_mem, G.card_neighborFinset_eq_degree, hdeg]

theorem distinct_masks (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 6) (hdeg : ∀ x, G.degree x = 5)
    (v : Fin 18) :
    Set.InjOn (fun u => G.neighborFinset v ∩ G.neighborFinset u) (Gᶜ.neighborFinset v) := by
  intro x hx y hy heq
  by_contra hxy
  let A := G.neighborFinset v
  let mask := fun u => A ∩ G.neighborFinset u
  change mask x = mask y at heq
  have hx' := (Gᶜ.mem_neighborFinset v x).mp hx
  have hy' := (Gᶜ.mem_neighborFinset v y).mp hy
  have hadj {u z : Fin 18} (h : z ∈ mask u) : G.Adj u z :=
    (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp h).2
  have hA {u z : Fin 18} (h : z ∈ mask u) : G.Adj v z :=
    (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp h).1
  have hcard := mask_arity G hG hc hdeg v x hx
  change (mask x).card ∈ ({1,2} : Finset ℕ) at hcard
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcard
  rcases hcard with h1 | h2
  · obtain ⟨a, hmask⟩ := Finset.card_eq_one.mp h1
    have ham : a ∈ mask x := by simp [hmask]
    have hya : a ∈ mask y := heq ▸ ham
    have hsub : Gᶜ.IsNClique 4 (A.erase a) := by
      refine ⟨?_, ?_⟩
      · intro i hi j hj hij
        exact ⟨hij, shared_neighbor_forbids G hG
          ((G.mem_neighborFinset _ _).mp (Finset.mem_of_mem_erase hi))
          ((G.mem_neighborFinset _ _).mp (Finset.mem_of_mem_erase hj))⟩
      · have ha : a ∈ A := Finset.mem_inter.mp ham |>.1
        rw [Finset.card_erase_of_mem ha]
        change (G.neighborFinset v).card - 1 = 4
        rw [G.card_neighborFinset_eq_degree, hdeg]
    have join {u : Fin 18} (hu : u ∈ Gᶜ.neighborFinset v) (hm : mask u = {a}) :
        ∀ w ∈ A.erase a, Gᶜ.Adj u w := by
      intro w hw
      have hwA := Finset.mem_of_mem_erase hw
      have hnot := ((Gᶜ.mem_neighborFinset v u).mp hu).2
      refine ⟨?_, ?_⟩
      · intro he
        exact hnot (he ▸ (G.mem_neighborFinset v w).mp hwA)
      · intro huw
        have hwM : w ∈ mask u := Finset.mem_inter.mpr ⟨hwA,(G.mem_neighborFinset _ _).mpr huw⟩
        exact (Finset.ne_of_mem_erase hw) (Finset.mem_singleton.mp (hm ▸ hwM))
    have hxjoin := hsub.insert (join hx hmask)
    apply hc _ (hxjoin.insert (a := y) ?_)
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact ⟨fun h => hxy h.symm, shared_neighbor_forbids G hG (hadj hya).symm (hadj ham).symm⟩
    · exact join hy (heq.symm.trans hmask) w hw
  · obtain ⟨a,b,hab,hm⟩ := Finset.card_eq_two.mp h2
    have hax : a ∈ mask x := by simp [hm]
    have hbx : b ∈ mask x := by simp [hm]
    have hay : a ∈ mask y := heq ▸ hax
    have hby : b ∈ mask y := heq ▸ hbx
    have hcompl : b ∈ Gᶜ.neighborFinset a :=
      (Gᶜ.mem_neighborFinset _ _).mpr ⟨hab, shared_neighbor_forbids G hG (hA hax) (hA hbx)⟩
    have htwo := mask_arity G hG hc hdeg a b hcompl
    simp only [Finset.mem_insert,Finset.mem_singleton] at htwo
    have hmem {z : Fin 18} (haz : G.Adj z a) (hbz : G.Adj z b) :
        z ∈ G.neighborFinset a ∩ G.neighborFinset b :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr haz.symm,
        (G.mem_neighborFinset _ _).mpr hbz.symm⟩
    have hsub : ({v,x,y} : Finset (Fin 18)) ⊆ G.neighborFinset a ∩ G.neighborFinset b := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact hmem (hA hax) (hA hbx)
      · exact hmem (hadj hax) (hadj hbx)
      · exact hmem (hadj hay) (hadj hby)
    have hle := Finset.card_le_card hsub
    rw [Finset.card_triple_eq_three_iff.mpr ⟨hx'.1,hy'.1,hxy⟩] at hle
    omega

private theorem enumerateVertices {n : ℕ} (s : Finset (Fin 18)) (hn : s.card = n) :
    ∃ e : Fin n ↪ Fin 18, (∀ i, e i ∈ s) ∧ (∀ z ∈ s, ∃ i, e i = z) := by
  classical
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin n) (s := s) (by simp [hn])
  have hin (i) : e i ∈ s := he ⟨i,rfl⟩
  have hsub : Finset.univ.map e ⊆ s := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hz
    exact hin i
  have hmap := Finset.eq_of_subset_of_card_le hsub (by simp [hn])
  refine ⟨e, hin, fun z hz => ?_⟩
  obtain ⟨i,_,hi⟩ := Finset.mem_map.mp (hmap ▸ hz)
  exact ⟨i,hi⟩

theorem canonical_parts
    (shape : Fin 15 → Finset (Fin 5)) (template : Fin 12 → Finset (Fin 5))
    (shape_full : ∀ t : Finset (Fin 5), t.card ∈ ({1,2} : Finset ℕ) → ∃ k, shape k = t)
    (template_inj : Function.Injective template)
    (normalize : ∀ S : Finset (Fin 15), S.card = 12 →
      (∀ a : Fin 5, (S.filter (fun i => a ∈ shape i)).card = 4) →
      ∃ p : Fin 5 ↪ Fin 5, ∀ j : Fin 12, ∃ k ∈ S, shape k = (template j).map p)
    (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (hc : Gᶜ.CliqueFree 6) (hdeg : ∀ x, G.degree x = 5) (v : Fin 18) :
    ∃ r : Fin 5 ↪ Fin 18, ∃ s : Fin 12 ↪ Fin 18,
      (∀ i, r i ∈ G.neighborFinset v) ∧ (∀ j, s j ∈ Gᶜ.neighborFinset v) ∧
      (∀ i j, G.Adj (r i) (s j) ↔ i ∈ template j) := by
  classical
  let A := G.neighborFinset v
  let B := Gᶜ.neighborFinset v
  have hAc : A.card = 5 := (G.card_neighborFinset_eq_degree v).trans (hdeg v)
  have hBc : B.card = 12 := by
    rw [Gᶜ.card_neighborFinset_eq_degree, G.degree_compl, Fintype.card_fin, hdeg]
  obtain ⟨f,hf,fcover⟩ := enumerateVertices A hAc
  obtain ⟨g,hg,gcover⟩ := enumerateVertices B hBc
  let m (j : Fin 12) := Finset.univ.filter fun i => G.Adj (f i) (g j)
  have mem_m (i : Fin 5) (j : Fin 12) : i ∈ m j ↔ G.Adj (f i) (g j) := by simp [m]
  have map_m (j : Fin 12) : (m j).map f = A ∩ G.neighborFinset (g j) := by
    ext z
    constructor
    · intro hz
      obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hz
      exact Finset.mem_inter.mpr ⟨hf a,(G.mem_neighborFinset _ _).mpr ((mem_m _ _).mp ha).symm⟩
    · intro hz
      obtain ⟨ha,hadj⟩ := Finset.mem_inter.mp hz
      obtain ⟨a,rfl⟩ := fcover _ ha
      exact Finset.mem_map.mpr ⟨a,(mem_m _ _).mpr ((G.mem_neighborFinset _ _).mp hadj).symm,rfl⟩
  have size_m (j : Fin 12) : (m j).card ∈ ({1,2} : Finset ℕ) := by
    have h := mask_arity G hG hc hdeg v (g j) (hg j)
    change (A ∩ G.neighborFinset (g j)).card ∈ ({1,2} : Finset ℕ) at h
    rwa [← map_m, Finset.card_map] at h
  choose code code_spec using fun j => shape_full (m j) (size_m j)
  have cinj : Function.Injective code := by
    intro i j hij
    have hm : m i = m j := (code_spec i).symm.trans ((congrArg shape hij).trans (code_spec j))
    apply g.injective
    apply distinct_masks G hG hc hdeg v (hg i) (hg j)
    change A ∩ G.neighborFinset (g i) = A ∩ G.neighborFinset (g j)
    rw [← map_m, ← map_m, hm]
  let S := Finset.univ.image code
  have size_S : S.card = 12 := by simp [S, Finset.card_image_of_injective _ cinj]
  have rows (a : Fin 5) : (S.filter (fun i => a ∈ shape i)).card = 4 := by
    let T := Finset.univ.filter fun j => G.Adj (f a) (g j)
    have hinT (j : Fin 12) : j ∈ T ↔ G.Adj (f a) (g j) := by simp [T]
    have hfilter : S.filter (fun i => a ∈ shape i) = T.image code := by
      ext z
      constructor
      · intro hz
        obtain ⟨hz,ha⟩ := Finset.mem_filter.mp hz
        obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hz
        rw [code_spec] at ha
        exact Finset.mem_image.mpr ⟨j,(hinT j).mpr ((mem_m _ _).mp ha),rfl⟩
      · intro hz
        obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
        refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩,?_⟩
        rw [code_spec]
        exact (mem_m _ _).mpr ((hinT _).mp hj)
    have Tmap : T.map g = B ∩ G.neighborFinset (f a) := by
      ext z
      constructor
      · intro hz
        obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hz
        exact Finset.mem_inter.mpr ⟨hg j,(G.mem_neighborFinset _ _).mpr ((hinT _).mp hj)⟩
      · intro hz
        obtain ⟨hz,hz'⟩ := Finset.mem_inter.mp hz
        obtain ⟨j,rfl⟩ := gcover _ hz
        exact Finset.mem_map.mpr ⟨j,(hinT _).mpr ((G.mem_neighborFinset _ _).mp hz'),rfl⟩
    rw [hfilter, Finset.card_image_of_injective _ cinj, ← Finset.card_map g, Tmap]
    exact row_degree G hG hdeg (hf a)
  obtain ⟨p,hp⟩ := normalize S size_S rows
  have realize (i : Fin 12) : ∃ j, m j = (template i).map p := by
    obtain ⟨k,hk,hshape⟩ := hp i
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hk
    exact ⟨j,(code_spec j).symm.trans hshape⟩
  choose sel hsel using realize
  have sel_inj : Function.Injective sel := by
    intro i j heq
    apply template_inj
    apply Finset.map_injective p
    rw [← hsel, ← hsel, heq]
  let e : Fin 12 ↪ Fin 12 := ⟨sel,sel_inj⟩
  refine ⟨p.trans f,e.trans g,fun i => hf (p i),fun j => hg (sel j),?_⟩
  intro i j
  change G.Adj (f (p i)) (g (sel j)) ↔ i ∈ template j
  rw [← mem_m, hsel]
  exact Finset.mem_map' p


private def joinVertices {V : Type*} (v : V) (r : Fin 5 ↪ V) (s : Fin 12 ↪ V)
    (i : Fin 18) : V :=
  if i.val = 0 then v else if h : i.val < 6 then r ⟨i.val-1, by omega⟩
  else s ⟨i.val-6, by omega⟩

private theorem join_injective {V : Type*} (v : V) (r : Fin 5 ↪ V) (s : Fin 12 ↪ V)
    (hvr : ∀ i, v ≠ r i) (hvs : ∀ j, v ≠ s j) (hrs : ∀ i j, r i ≠ s j) :
    Function.Injective (joinVertices v r s) := by
  intro i j hh
  apply Fin.ext
  unfold joinVertices at hh
  split_ifs at hh
  all_goals first
    | omega
    | exact False.elim (hvr _ hh)
    | exact False.elim (hvr _ hh.symm)
    | exact False.elim (hvs _ hh)
    | exact False.elim (hvs _ hh.symm)
    | exact False.elim (hrs _ _ hh)
    | exact False.elim (hrs _ _ hh.symm)
    | have e := congrArg Fin.val (r.injective hh); dsimp at e; omega
    | have e := congrArg Fin.val (s.injective hh); dsimp at e; omega

private def rowTag (i : Fin 5) : Fin 18 := ⟨i.val+1, by omega⟩
private def colTag (j : Fin 12) : Fin 18 := ⟨j.val+6, by omega⟩
open OMA.RamseyRegular

private theorem template_agrees : ∀ (i : Fin 5) (j : Fin 12),
    i ∈ template j ↔ rowTag i ∈ mask (colTag j) := by decide +kernel

private theorem shapes_complete : ∀ t : Finset (Fin 5),
    t.card ∈ ({1,2} : Finset ℕ) → ∃ k, shape k = t := by decide +kernel

private theorem template_injective : Function.Injective template := by
  intro i j
  exact (show ∀ i j : Fin 12, template i = template j → i = j by decide +kernel) i j

theorem regular_impossible (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hdeg : ∀ x, G.degree x = 5) (hc : Gᶜ.CliqueFree 6) : False := by
  classical
  let v : Fin 18 := 0
  obtain ⟨r,s,hr,hs,hadj⟩ := canonical_parts shape template shapes_complete template_injective normalize_masks G hG hc hdeg v
  have ra (i : Fin 5) : G.Adj v (r i) := (G.mem_neighborFinset _ _).mp (hr i)
  have sb (j : Fin 12) : Gᶜ.Adj v (s j) := (Gᶜ.mem_neighborFinset _ _).mp (hs j)
  have sep (i : Fin 5) (j : Fin 12) : r i ≠ s j := by
    intro he
    exact (sb j).2 (he ▸ ra i)
  let f : Fin 18 ↪ Fin 18 :=
    ⟨joinVertices v r s, join_injective v r s (fun i => (ra i).ne) (fun j => (sb j).1) sep⟩
  have row (i : Fin 18) (hl : 1 ≤ i.val) (hu : i.val < 6) :
      f i = r ⟨i.val-1, by omega⟩ := by
    have h0 : i.val ≠ 0 := by omega
    simp [f, joinVertices, h0, hu]
  have col (j : Fin 18) (hl : 6 ≤ j.val) :
      f j = s ⟨j.val-6, by omega⟩ := by
    have h0 : j.val ≠ 0 := by omega
    have h1 : ¬j.val < 6 := by omega
    simp [f, joinVertices, h0, h1]
  apply canonical_impossible G hG hc f
  · intro i j hil hiu hjl hju
    rw [row i hil hiu, row j hjl hju]
    exact shared_neighbor_forbids G hG (ra _) (ra _)
  · intro i j hil hiu hj
    let a : Fin 5 := ⟨i.val-1,by omega⟩
    let b : Fin 12 := ⟨j.val-6,by omega⟩
    have ai : rowTag a = i := Fin.ext (by dsimp [rowTag,a]; omega)
    have bj : colTag b = j := Fin.ext (by dsimp [colTag,b]; omega)
    rw [row i hil hiu, col j hj]
    exact (hadj a b).trans (by simpa only [ai,bj] using template_agrees a b)


end OMA.Ramsey36Canonical
end Ramsey36Regular

section RamseyFiniteSection
open SimpleGraph
namespace OMA.RamseyFinite

private def bits : List Bool → Nat
  | [] => 0
  | b::bs => 2 * bits bs + b.toNat

private theorem bits_lt (b : List Bool) : bits b < 2 ^ b.length := by
  induction b with
  | nil => decide
  | cons a l ih => cases a <;> simp [bits, pow_succ] <;> omega

private theorem bits_append (a b : List Bool) : bits (a ++ b) = bits a + 2 ^ a.length * bits b := by
  induction a with
  | nil => simp [bits]
  | cons c a ih => simp [bits, ih, pow_succ]; ring

private theorem bits_replicate_false (n : Nat) : bits (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, bits, ih]

private theorem bits_replicate_true (n : Nat) : bits (List.replicate n true) + 1 = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, bits, pow_succ]; omega

private def encode {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] : List V → List Nat
  | [] => []
  | v::vs => bits (vs.map fun x => decide (G.Adj v x)) :: encode G vs

private def shifted : List Nat → List Nat
  | [] => []
  | s::ss => 2 ^ ss.length * s :: shifted ss

private def attach (blocks base : List Nat) : List Nat :=
  (2 ^ blocks.length - 1) :: (shifted blocks ++ base)

private theorem contacts {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (front base : List V) (hi : ∀ x ∈ front, ∀ y ∈ front, ¬ G.Adj x y) :
    encode G (front ++ base) =
      shifted (front.map fun x => bits (base.map fun y => decide (G.Adj x y))) ++ encode G base := by
  induction front with
  | nil => rfl
  | cons a as ih =>
    have nh (x) (hx : x∈as) := hi a (by simp) x (by simp [hx])
    have nils : as.map (fun x => decide (G.Adj a x)) = List.replicate as.length false := by
      apply List.eq_replicate_iff.mpr
      exact ⟨by simp, fun x hx => by obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx; simp [nh b hb]⟩
    simp [encode, shifted, bits_append, nils, bits_replicate_false,
      ih (fun x hx y hy => hi x (by simp [hx]) y (by simp [hy]))]

private theorem root_encoding {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V) (front base : List V) (hfront : ∀ x∈front, G.Adj r x)
    (hbase : ∀ x∈base, ¬ G.Adj r x) (ht : G.CliqueFree 3) :
    encode G (r::front++base) = attach
      (front.map fun x => bits (base.map fun y => decide (G.Adj x y))) (encode G base) := by
  have hf : front.map (fun x => decide (G.Adj r x)) = List.replicate front.length true := by
    apply List.eq_replicate_iff.mpr
    exact ⟨by simp, fun x hx => by obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx; simp [hfront b hb]⟩
  have hb : base.map (fun x => decide (G.Adj r x)) = List.replicate base.length false := by
    apply List.eq_replicate_iff.mpr
    exact ⟨by simp, fun x hx => by obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx; simp [hbase b hb]⟩
  have hi (x) (hx : x ∈ front) (y) (hy : y ∈ front) (h : G.Adj x y) : False :=
    G.isIndepSet_neighborSet_of_triangleFree ht r (hfront x hx) (hfront y hy) h.ne h
  simp [encode, attach, bits_append, hf, hb, bits_replicate_false, contacts G front base hi]
  have := bits_replicate_true front.length
  omega

private def mark {V : Type*} [DecidableEq V] (vs : List V) (s : Finset V) : Nat :=
  bits (vs.map fun x => decide (x ∈ s))

private theorem bit_form (b : Bool) (n : Nat) : Nat.bit b n = 2 * n + b.toNat := by
  cases b <;> simp [Nat.bit, Nat.two_mul]

private theorem and_mask {V : Type*} (vs : List V) (f g : V → Bool) :
    bits (vs.map f) &&& bits (vs.map g) = 0 ↔ ∀ x ∈ vs, f x = true → g x = false := by
  induction vs with
  | nil => simp [bits]
  | cons a l ih =>
    simp only [List.map_cons, bits, ← bit_form, Nat.land_bit, List.forall_mem_cons]
    rw [bit_form]
    cases f a <;> cases g a <;> simp [ih]

private def ind0 (p : Nat × Nat) : Nat × Nat := (2*p.1,p.2)
private def ind1 (p : Nat × Nat) : Nat × Nat := (2*p.1+1,p.2+1)

private def inds : List Nat → List (Nat × Nat)
  | [] => [(0,0)]
  | m::rows =>
    let t := inds rows
    t.map ind0 ++ (t.filter fun p => m &&& p.1 == 0).map ind1

private theorem mark_congr {V : Type*} [DecidableEq V] (vs : List V) (s t : Finset V)
    (h : ∀ x∈vs, x∈s ↔ x∈t) : mark vs s = mark vs t := by
  unfold mark
  congr 1
  exact List.map_congr_left (fun x hx => by simp only [h x hx])

private theorem inds_sound {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (vs : List V) (hn : vs.Nodup) {p : Nat × Nat} (hp : p ∈ inds (encode G vs)) :
    ∃ S : Finset V, S ⊆ vs.toFinset ∧ Gᶜ.IsClique (S : Set V) ∧ p = (mark vs S,S.card) := by
  induction vs generalizing p with
  | nil =>
    simp [encode,inds] at hp
    exact ⟨∅,by simp,by simp,by simp [hp,mark,bits]⟩
  | cons a l ih =>
    have hn' := List.nodup_cons.mp hn
    simp only [encode,inds,List.mem_append,List.mem_map,List.mem_filter] at hp
    rcases hp with ⟨q,hq,rfl⟩ | ⟨q,⟨hq,hd⟩,rfl⟩
    · obtain ⟨S,hS,hI,rfl⟩ := ih hn'.2 hq
      have ha : a ∉ S := fun h => hn'.1 (List.mem_toFinset.mp (hS h))
      exact ⟨S,by simpa using hS.trans (Finset.subset_insert a _),hI,by simp [ind0,mark,bits,ha]⟩
    · obtain ⟨S,hS,hI,rfl⟩ := ih hn'.2 hq
      have ha : a ∉ S := fun h => hn'.1 (List.mem_toFinset.mp (hS h))
      have hz := (and_mask l (fun x => decide (G.Adj a x)) (fun x => decide (x∈S))).mp (beq_iff_eq.mp hd)
      have hi : Gᶜ.IsClique (insert a S : Finset V) := by
        rw [Finset.coe_insert, SimpleGraph.isClique_insert_of_notMem ha]
        refine ⟨hI,fun x hx => ⟨?_,?_⟩⟩
        · exact fun e => ha (e ▸ hx)
        · intro adj
          have := hz x (List.mem_toFinset.mp (hS hx)) (by simpa using adj)
          exact (of_decide_eq_false this) hx
      have hm := mark_congr l (insert a S) S (by intro x hx; simp [show x ≠ a from fun e => hn'.1 (e ▸ hx)])
      refine ⟨insert a S, by simpa using Finset.insert_subset_insert a hS, hi, ?_⟩
      simp [ind1,mark,bits,Finset.card_insert_of_notMem ha] at hm ⊢
      omega

private theorem inds_complete {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (vs : List V) (hn : vs.Nodup) (S : Finset V) (hS : S ⊆ vs.toFinset) (hI : Gᶜ.IsClique (S : Set V)) :
    (mark vs S,S.card) ∈ inds (encode G vs) := by
  induction vs generalizing S with
  | nil =>
    have e : S=∅ := Finset.subset_empty.mp (by simpa using hS)
    simp [e,encode,inds,mark,bits]
  | cons a l ih =>
    have hn' := List.nodup_cons.mp hn
    simp only [encode,inds,List.mem_append,List.mem_map,List.mem_filter]
    by_cases ha : a ∈ S
    · let T := S.erase a
      have hT : T ⊆ l.toFinset := by
        intro x hx
        have m := Finset.mem_erase.mp hx
        have h := List.mem_cons.mp (List.mem_toFinset.mp (hS m.2))
        exact List.mem_toFinset.mpr (h.resolve_left m.1)
      have hI' := hI.subset (show (T : Set V) ⊆ (S : Set V) from Finset.erase_subset ..)
      have hmark := mark_congr l S T (by intro x hx; simp [T,show x≠a from fun e => hn'.1 (e ▸ hx)])
      have hcard : T.card + 1 = S.card := Finset.card_erase_add_one ha
      right
      refine ⟨(mark l T,T.card),⟨ih hn'.2 T hT hI', ?_⟩,?_⟩
      · apply beq_iff_eq.mpr
        apply (and_mask l (fun x => decide (G.Adj a x)) (fun x => decide (x∈T))).mpr
        intro x _ hx
        apply decide_eq_false
        intro hm
        have hmem := Finset.mem_erase.mp hm
        exact (hI ha hmem.2 hmem.1.symm).2 (of_decide_eq_true hx)
      · simp [ind1,mark,bits,ha,hcard] at hmark ⊢
        omega
    · have hT : S ⊆ l.toFinset := by
        intro x hx
        have h := List.mem_cons.mp (List.mem_toFinset.mp (hS hx))
        exact List.mem_toFinset.mpr (h.resolve_left (fun e => ha (e ▸ hx)))
      exact Or.inl ⟨_,ih hn'.2 S hT hI,by simp [ind0,mark,bits,ha]⟩


private def countBits : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,x => (x%2) + countBits n (x/2)

private def bump (m : Nat) : List Nat → List Nat
  | [] => []
  | x::xs => (x+m%2)::bump (m/2) xs

private def degrees : List Nat → List Nat
  | [] => []
  | m::ms => countBits ms.length m :: bump m (degrees ms)

private def sizeAt {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (vs : List V) (x : V) :=
  (vs.filter fun y => decide (G.Adj x y)).length

private theorem half_step (x : Nat) : (2*x+1)/2=x := by omega

private theorem count_map {V : Type*} (vs : List V) (f : V → Bool) :
    countBits vs.length (bits (vs.map f)) = (vs.filter f).length := by
  induction vs with
  | nil => rfl
  | cons a l ih =>
    cases ha : f a <;> simp [countBits,bits,ha,ih,half_step]
    omega

private theorem bump_map {V : Type*} (vs : List V) (f : V → Bool) (d : V → Nat) :
    bump (bits (vs.map f)) (vs.map d) = vs.map (fun x => d x + (f x).toNat) := by
  induction vs with
  | nil => rfl
  | cons a l ih => cases ha : f a <;> simp [bump,bits,ha,ih,half_step]

private theorem encode_length {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (vs : List V) :
    (encode G vs).length=vs.length := by induction vs with | nil => rfl | cons a as ih => simp [encode,ih]

private theorem degrees_encode {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (vs : List V) :
    degrees (encode G vs) = vs.map (sizeAt G vs) := by
  induction vs with
  | nil => rfl
  | cons a l ih =>
    simp only [encode,degrees,encode_length,count_map,ih,bump_map,List.map_cons,List.cons.injEq]
    refine ⟨by simp [sizeAt], List.map_congr_left ?_⟩
    intro x _
    by_cases h : G.Adj a x <;> simp [sizeAt,h,G.adj_comm x a]

private theorem sizeAt_finset {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {vs : List V} (hn : vs.Nodup) (x : V) :
    sizeAt G vs x = (vs.toFinset.filter (G.Adj x)).card := by
  have h := List.toFinset_filter vs (fun y => decide (G.Adj x y))
  simp only [decide_eq_true_eq] at h
  rw [← h, List.toFinset_card_of_nodup (hn.filter _)]
  rfl


private def Small {V : Type*} (G : SimpleGraph V) (A : Finset V) (k : Nat) :=
  ∀ I ⊆ A, Gᶜ.IsClique (I : Set V) → I.card < k

private theorem row_mark {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (base : List V) (x : V) :
    bits (base.map fun y => decide (G.Adj x y)) = mark base (base.toFinset.filter (G.Adj x)) := by
  unfold mark
  congr 1
  exact List.map_congr_left (fun y hy => by simp [hy])

private theorem neighbors_small {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (A : Finset V) (x : V) :
    Gᶜ.IsClique ((A.filter (G.Adj x) : Finset V) : Set V) := by
  rw [G.isClique_compl]
  intro y hy z hz hn
  exact G.isIndepSet_neighborSet_of_triangleFree ht x (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hz).2 hn

private theorem degrees_bound {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (A : Finset V) (k : Nat) (hs : Small G A k)
    (l : List V) (hn : l.Nodup) (hsub : l.toFinset ⊆ A) :
    (degrees (encode G l)).all (· < k) = true := by
  rw [degrees_encode, List.all_eq_true]
  intro y hy
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp hy
  simp only [decide_eq_true_eq, sizeAt_finset G hn]
  exact hs _ ((Finset.filter_subset _ _).trans hsub) (neighbors_small G ht _ x)

private def okContacts (k : Nat) (isets : List (Nat × Nat)) (cs : List Nat) : Bool :=
  isets.all fun p => p.2 + (cs.filter fun v => v &&& p.1 == 0).length < k

private theorem ok_contacts {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : Nat) (hs : Small G A k) (front base : List V)
    (hn : (front++base).Nodup) (hsub : (front++base).toFinset ⊆ A)
    (hi : Gᶜ.IsClique (front.toFinset : Set V)) :
    okContacts k (inds (encode G base)) (front.map fun x => bits (base.map fun y => decide (G.Adj x y))) := by
  rw [okContacts,List.all_eq_true]
  intro q hq
  obtain ⟨hh,hb,hd⟩ := List.nodup_append.mp hn
  obtain ⟨S,hS,hI,rfl⟩ := inds_sound G base hb hq
  let pred (v : V) : Bool := bits (base.map fun y => decide (G.Adj v y)) &&& mark base S == 0
  let F := front.filter pred
  have hF (x) (hx : x∈F) : x∈front := (List.mem_filter.mp hx).1
  have sep (x) (hx : x∈F) (y) (hy : y∈S) : Gᶜ.Adj x y := by
    have hx' := List.mem_filter.mp hx
    have hy' := List.mem_toFinset.mp (hS hy)
    have neq : x ≠ y := hd x hx'.1 y hy'
    exact ⟨neq,fun ha => by
      have e := (and_mask base (fun z => decide (G.Adj x z)) (fun z => decide (z ∈ S))).mp
        (beq_iff_eq.mp hx'.2) y hy' (by simpa using ha)
      exact of_decide_eq_false e hy⟩
  have sub : F.toFinset ∪ S ⊆ A := by
    apply Finset.union_subset
    · exact fun x hx => hsub (by simp [hF x (List.mem_toFinset.mp hx)])
    · exact fun x hx => hsub (by simp [List.mem_toFinset.mp (hS hx)])
  have together : Gᶜ.IsClique ((F.toFinset ∪ S : Finset V) : Set V) := by
    rw [Finset.coe_union, SimpleGraph.IsClique, Set.pairwise_union]
    refine ⟨hi.subset ?_,hI,?_⟩
    · exact fun x hx => List.mem_toFinset.mpr (hF x (List.mem_toFinset.mp hx))
    · intro x hx y hy _
      exact ⟨sep x (List.mem_toFinset.mp hx) y hy,(sep x (List.mem_toFinset.mp hx) y hy).symm⟩
  have dis : Disjoint F.toFinset S := Finset.disjoint_left.mpr fun x hx hy =>
    (sep x (List.mem_toFinset.mp hx) x hy).ne rfl
  have w := hs _ sub together
  rw [Finset.card_union_of_disjoint dis,List.toFinset_card_of_nodup (hh.filter _)] at w
  simp only [decide_eq_true_eq,List.filter_map,List.length_map]
  change S.card + F.length < k
  simpa only [F, Nat.add_comm S.card] using w


private theorem bit_and {α : Type*} (l : List α) (f g : α → Bool) :
    bits (l.map f) &&& bits (l.map g) = bits (l.map fun x => f x && g x) := by
  induction l with
  | nil => simp [bits]
  | cons a l ih => simp only [List.map_cons,bits,← bit_form,Nat.land_bit,ih]

private theorem bit_or {α : Type*} (l : List α) (f g : α → Bool) :
    bits (l.map f) ||| bits (l.map g) = bits (l.map fun x => f x || g x) := by
  induction l with
  | nil => simp [bits]
  | cons a l ih => simp only [List.map_cons,bits,← bit_form,Nat.lor_bit,ih]

private def compat (I : List (Nat × Nat)) (a : Nat) := bits (I.map fun p => a &&& p.1 == 0)
private def universal (I : List (Nat × Nat)) := bits (I.map fun _=>true)
private def threshold (k : Nat) (I : List (Nat × Nat)) (acc : List Nat) (j : Nat) :=
  bits (I.map fun p => decide (k≤p.2 + (acc.filter fun a => a &&& p.1 == 0).length+j))

private theorem saturated (k : Nat) (I : List (Nat × Nat)) (acc : List Nat) (j : Nat) (h : k≤j) :
    threshold k I acc j=universal I := by
  unfold threshold universal
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [decide_eq_true_eq]; omega

private theorem threshold_cons (k : Nat) (I : List (Nat × Nat)) (a : Nat) (acc : List Nat) (j : Nat) :
    threshold k I (a::acc) j = threshold k I acc j ||| (compat I a &&& threshold k I acc (j+1)) := by
  unfold threshold compat
  rw [bit_and,bit_or]
  congr 1
  apply List.map_congr_left
  intro p _
  apply Bool.eq_iff_iff.mpr
  by_cases e : a &&& p.1=0 <;> simp [e] <;> omega

private def cells (k : Nat) (I : List (Nat × Nat)) (acc : List Nat) : Nat → Nat → List Nat
  | 0,_ => []
  | n+1,j => threshold k I acc j :: cells k I acc n (j+1)

private def tick (u m : Nat) : List Nat → List Nat
  | [] => []
  | a::as => (a ||| (m &&& as.headD u)) :: tick u m as

private theorem tick_cells (k : Nat) (I : List (Nat × Nat)) (acc : List Nat) (a n j : Nat) (h : k ≤ j+n) :
    tick (universal I) (compat I a) (cells k I acc n j) = cells k I (a::acc) n j := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    simp only [cells,tick,List.cons.injEq]
    refine ⟨?_,ih (j+1) (by omega)⟩
    rw [threshold_cons]
    cases n with
    | zero => simp [cells,saturated k I acc (j+1) (by omega)]
    | succ n => rfl

private theorem can_add (k : Nat) (I : List (Nat × Nat)) (acc : List Nat) (a : Nat)
    (h : okContacts k I (a::acc)) : compat I a &&& threshold k I acc 1=0 := by
  apply (and_mask I _ _).mpr
  intro p hp e
  have b := List.all_eq_true.mp h p hp
  simp only [List.filter_cons,e,if_true,List.length_cons,decide_eq_true_eq] at b
  apply decide_eq_false
  omega

private def traverse (opts : List (Nat × Nat)) (u : Nat) (ending : List (Nat × Nat) → Bool) :
    Nat → Nat → List (Nat × Nat) → List Nat → List (List (Nat × Nat))
  | 0,_,acc,_ => if ending acc then [acc] else []
  | fuel+1,lo,acc,st => opts.flatMap fun a =>
    if lo ≤ a.1 && a.2 &&& st.headD u == 0 then
      traverse opts u ending fuel a.1 (a::acc) (tick u a.2 st) else []

private theorem traverse_complete (opts : List (Nat × Nat)) (I : List (Nat × Nat)) (k : Nat) (hk : 0<k)
    (ending : List (Nat × Nat) → Bool) (next acc : List (Nat × Nat)) (lo : Nat)
    (hc : ∀ a∈next,a∈opts) (vals : ∀ a∈next,a.2=compat I a.1)
    (hl : ∀ a∈next,lo≤a.1) (hs : next.Pairwise (fun a b => a.1 ≤ b.1))
    (hg : ∀ u w,next=u++w → okContacts k I ((u.reverse++acc).map Prod.fst)) (hf : ending (next.reverse++acc)) :
    next.reverse++acc ∈ traverse opts (universal I) ending next.length lo acc (cells k I (acc.map Prod.fst) k 1) := by
  induction next generalizing acc lo with
  | nil => simpa [traverse,hf] using hf
  | cons a rest ih =>
    simp only [List.length_cons,traverse,List.mem_flatMap]
    refine ⟨a,hc a (by simp),?_⟩
    have hd : (cells k I (acc.map Prod.fst) k 1).headD (universal I)=threshold k I (acc.map Prod.fst) 1 := by
      cases k with | zero => omega | succ k => rfl
    have an := vals a (by simp)
    have allow := can_add k I (acc.map Prod.fst) a.1 (by simpa using hg [a] rest rfl)
    simp only [hl a (by simp),decide_true,Bool.true_and,an,hd,allow,beq_self_eq_true,if_true,tick_cells k I (acc.map Prod.fst) a.1 k 1 (by omega)]
    simpa [List.append_assoc] using ih (a::acc) a.1 (fun x hx => hc x (by simp [hx]))
      (fun x hx => vals x (by simp [hx])) (List.pairwise_cons.mp hs).1 (List.pairwise_cons.mp hs).2
      (by intro u w h; simpa [List.append_assoc] using hg (a::u) w (by simp [h]))
      (by simpa [List.append_assoc] using hf)


private def contactsOf {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (base front : List V) :=
  front.map fun x => bits (base.map fun y => decide (G.Adj x y))

private def usable (k d : Nat) (base : List Nat) : List Nat :=
  ((inds base).filter fun p => d ≤ p.2+1 && p.2+1 < k).map Prod.fst

private def guardRows (k : Nat) (base : List Nat) (isets : List (Nat × Nat)) (cs : List Nat) :=
  okContacts k isets cs && (degrees (shifted cs ++ base)).all (·<k)

private def tagged (k d : Nat) (base : List Nat) :=
  (usable k d base).map fun x => (x,compat (inds base) x)

private def assemble (k d : Nat) (base : List Nat) (opts : List (Nat × Nat)) (bits0 : Nat) (lims : List Nat) :=
  let ending := fun cs : List (Nat × Nat) => (degrees (attach (cs.reverse.map Prod.fst) base)).all (d≤·)
  (traverse opts bits0 ending d 0 [] lims).map (fun cs => attach (cs.reverse.map Prod.fst) base)

private def grow (k d : Nat) (base : List Nat) : List (List Nat) :=
  assemble k d base (tagged k d base) (universal (inds base)) (cells k (inds base) [] k 1)

private theorem grow_complete {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k d : Nat) (ht : G.CliqueFree 3) (hs : Small G A k)
    (r : V) (front base : List V) (hn : (r::front++base).Nodup)
    (hall : (r::front++base).toFinset=A) (hd : front.length=d)
    (ha : ∀ x∈front,G.Adj r x) (hb : ∀ x∈base,¬G.Adj r x)
    (hcount : ∀ x∈front,d≤ sizeAt G base x+1 ∧ sizeAt G base x+1 < k)
    (hmin : ∀ x∈A,d≤(A.filter (G.Adj x)).card)
    (horder : (contactsOf G base front).Pairwise (·≤·)) :
    encode G (r::front++base) ∈ grow k d (encode G base) := by
  let cs := contactsOf G base front
  have split := root_encoding G r front base ha hb ht
  change encode G (r::front++base) = attach cs (encode G base) at split
  have hbnd := (List.nodup_append.mp (List.nodup_cons.mp hn).2).2.1
  have hc (s) (mem : s ∈ cs) : s ∈ usable k d (encode G base) := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp mem
    let S := base.toFinset.filter (G.Adj x)
    have row := inds_complete G base hbnd S (Finset.filter_subset ..) (neighbors_small G ht _ x)
    have m := hcount x hx
    rw [sizeAt_finset G hbnd] at m
    change bits (base.map fun y => decide (G.Adj x y)) ∈ _
    rw [row_mark]
    exact List.mem_map.mpr ⟨_,List.mem_filter.mpr ⟨row,by simpa [S] using m⟩,rfl⟩
  have guard_ (u w : List Nat) (h : cs=u++w) : guardRows k (encode G base) (inds (encode G base)) u := by
    let sl := front.take u.length
    have hu : contactsOf G base sl = u := by
      change (front.take u.length).map _=u
      rw [List.map_take, show front.map _=u++w from h, List.take_left]
    have ssub := (List.take_sublist u.length front).append (List.Sublist.refl base)
    have nodup : (sl++base).Nodup := (List.nodup_cons.mp hn).2.sublist ssub
    have sub : (sl++base).toFinset ⊆ A := by
      intro x hx
      rw [← hall]
      exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (ssub.subset (List.mem_toFinset.mp hx)))
    have ha' (x) (hx : x∈sl) := ha x ((List.take_sublist u.length front).subset hx)
    have indep : Gᶜ.IsClique (sl.toFinset : Set V) := by
      rw [G.isClique_compl]
      intro x hx y hy hxy
      exact G.isIndepSet_neighborSet_of_triangleFree ht r (ha' x (List.mem_toFinset.mp hx)) (ha' y (List.mem_toFinset.mp hy)) hxy
    have em := contacts G sl base (by intro x hx y hy adj; exact G.isIndepSet_neighborSet_of_triangleFree ht r (ha' x hx) (ha' y hy) adj.ne adj)
    change encode G (sl++base)=shifted (contactsOf G base sl)++encode G base at em
    rw [← hu]
    apply Bool.and_eq_true_iff.mpr
    refine ⟨ok_contacts G A k hs sl base nodup sub indep,?_⟩
    rw [← em]
    exact degrees_bound G ht A k hs _ nodup sub
  have final_ : (degrees (attach cs (encode G base))).all (d≤·) = true := by
    rw [← split,degrees_encode,List.all_eq_true]
    intro n hh
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hh
    simpa only [decide_eq_true_eq,sizeAt_finset G hn,hall] using hmin x (hall ▸ List.mem_toFinset.mpr hx)
  have csl : cs.length=d := by simp [cs,contactsOf,hd]
  let base' := encode G base
  let tag (x : Nat) := (x,compat (inds base') x)
  let ts := cs.map tag
  have ret (ss : List Nat) : (ss.map tag).map Prod.fst = ss := by simp [tag,Function.comp_def]
  have tg (a) (ma : a∈ts) : a ∈ tagged k d base' := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ma
    exact List.mem_map.mpr ⟨x,hc x hx,rfl⟩
  have gg (u w : List (Nat × Nat)) (h : ts=u++w) : okContacts k (inds base') (u.reverse.map Prod.fst) := by
    let sl := cs.take u.length
    have split_ : cs=sl++cs.drop u.length := (List.take_append_drop u.length cs).symm
    have hu : sl.map tag=u := by
      change (cs.take u.length).map tag=u
      rw [List.map_take,show cs.map tag=u++w from h,List.take_left]
    have gh := Bool.and_eq_true_iff.mp (guard_ sl (cs.drop u.length) split_)
    rw [← hu,List.map_reverse,ret]
    simpa [okContacts] using gh.1
  have tslen : ts.length=d := by simp [ts,csl]
  have tsord : ts.Pairwise (fun a b => a.1 ≤ b.1) := List.pairwise_map.mpr horder
  rw [split]
  apply List.mem_map.mpr
  refine ⟨ts.reverse,?_,by simp [ts,ret]⟩
  have hk : 0<k := hs ∅ (by simp) (by simp)
  simpa only [List.append_nil,tslen,List.map_nil] using traverse_complete (tagged k d base') (inds base') k hk
    (fun u => (degrees (attach (u.reverse.map Prod.fst) base')).all (d≤·)) ts [] 0 tg
    (by intro a ha; obtain ⟨x,_,rfl⟩ := List.mem_map.mp ha; rfl) (by simp) tsord
    (by simpa using gg) (by simpa only [List.append_nil,List.reverse_reverse,ts,ret,base'] using final_)

private def levels (norm : List Nat → List Nat) : Nat → Nat → Nat → List (List Nat)
  | 0,_,_ => []
  | k+1,n,cap => if n=0 then [[]] else
    ((List.range (min cap (min k (n-1)) + 1)).flatMap fun d =>
      (levels norm k (n-1-d) (k-1)).flatMap fun base => (grow (k+1) d base).map norm).eraseDups

private theorem sorted_neigh {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (N : Finset V) (base : List V) :
    ∃ l : List V, l.Nodup ∧ l.toFinset=N ∧ (contactsOf G base l).Pairwise (·≤·) := by
  let key (x : V) := bits (base.map fun y => decide (G.Adj x y))
  let ord (a b : V) := decide (key a ≤ key b)
  let l := N.toList.mergeSort ord
  have h := List.mergeSort_perm N.toList ord
  refine ⟨l,h.nodup_iff.mpr N.nodup_toList,?_,?_⟩
  · ext x
    simp [l]
  · have htr (a b c) : ord a b → ord b c → ord a c := by simp only [ord,decide_eq_true_eq]; omega
    have htot (a b) : ord a b || ord b a := by simp [ord,le_total]
    have sort_ := List.pairwise_mergeSort htr htot N.toList
    apply List.pairwise_map.mpr
    simpa only [ord,decide_eq_true_eq] using sort_

private theorem levels_complete {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (norm : List Nat → List Nat)
    (hnorm : ∀ l : List V, ∃ l' : List V, l'.Perm l ∧ encode G l'=norm (encode G l))
    (k : Nat) (A : Finset V) (cap : Nat) (hs : Small G A k)
    (hu : A.Nonempty → ∃ x∈A,(A.filter (G.Adj x)).card ≤ cap) :
    ∃ vs : List V, vs.Nodup ∧ vs.toFinset=A ∧ encode G vs ∈ levels norm k A.card cap := by
  induction k generalizing A cap with
  | zero => have h := hs ∅ (by simp) (by simp); simp at h
  | succ k ih =>
    by_cases empty : A=∅
    · subst A; exact ⟨[],by simp,by simp,by simp [encode,levels]⟩
    have non := Finset.nonempty_iff_ne_empty.mpr empty
    obtain ⟨r,hr,hmin⟩ := A.exists_min_image (fun x => (A.filter (G.Adj x)).card) non
    let N := A.filter (G.Adj r)
    let B := A \ insert r N
    let d := N.card
    have hNr : r∉N := by simp [N]
    have hNA : N⊆A := Finset.filter_subset ..
    have hBA : B⊆A := Finset.sdiff_subset
    have hu' : d≤cap := by obtain ⟨x,hx,hh⟩ := hu non; exact (hmin x hx).trans hh
    have hdk : d≤k := Nat.le_of_lt_succ (hs N hNA (neighbors_small G ht A r))
    have hBcard : B.card + d + 1 = A.card := by
      have hh := Finset.card_sdiff_add_card_eq_card (Finset.insert_subset hr hNA)
      rw [Finset.card_insert_of_notMem hNr] at hh
      omega
    have rB : r∉B := by simp [B]
    have hbase (x) (hx : x∈B) : ¬G.Adj r x := by
      have h := Finset.mem_sdiff.mp hx
      exact fun ha => h.2 (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨h.1,ha⟩))
    have noK : Small G B k := by
      intro S hS hI
      have rn : r∉S := fun h => rB (hS h)
      have indep : Gᶜ.IsClique (insert r S : Finset V) := by
        rw [Finset.coe_insert,SimpleGraph.isClique_insert_of_notMem rn]
        exact ⟨hI,fun x hx => ⟨fun e => rn (e ▸ hx),hbase x (hS hx)⟩⟩
      have hh := hs (insert r S) (Finset.insert_subset hr (hS.trans hBA)) indep
      rw [Finset.card_insert_of_notMem rn] at hh
      omega
    obtain ⟨base,hbn,hb,cls⟩ := ih B (k-1) noK (by
      rintro ⟨x,hx⟩
      have mm := noK (B.filter (G.Adj x)) (Finset.filter_subset ..) (neighbors_small G ht B x)
      exact ⟨x,hx,by omega⟩)
    obtain ⟨front,hfn,hf,sorted_⟩ := sorted_neigh G N base
    have ha (x) (hx : x∈front) : G.Adj r x := (Finset.mem_filter.mp (hf ▸ List.mem_toFinset.mpr hx)).2
    have hnot (x) (hx : x∈base) := hbase x (hb ▸ List.mem_toFinset.mpr hx)
    have dl : front.length=d := by rw [← List.toFinset_card_of_nodup hfn,hf]
    have nodup : (r::front++base).Nodup := by
      apply List.nodup_cons.mpr
      constructor
      · change r ∉ front++base
        rw [List.mem_append,not_or]
        exact ⟨fun h => hNr (hf ▸ List.mem_toFinset.mpr h), fun h => rB (hb ▸ List.mem_toFinset.mpr h)⟩
      · exact List.nodup_append.mpr ⟨hfn,hbn,fun x hx y hy e => hnot y hy (e ▸ ha x hx)⟩
    have cover : (r::front++base).toFinset=A := by
      ext x
      simp only [List.toFinset_cons,List.toFinset_append,hf,hb,B,Finset.mem_insert,Finset.mem_union,Finset.mem_sdiff]
      have h1 : x=r → x∈A := fun h => h ▸ hr
      have h2 : x∈N → x∈A := fun h => hNA h
      grind
    have hcount (x) (hx : x∈front) : d≤ sizeAt G base x+1 ∧ sizeAt G base x+1 < k+1 := by
      have xN : x∈N := hf ▸ List.mem_toFinset.mpr hx
      have adj := ha x hx
      have eq : A.filter (G.Adj x)=insert r (B.filter (G.Adj x)) := by
        ext y
        simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_sdiff,B]
        constructor
        · rintro ⟨yA,xy⟩
          by_cases yr : y=r
          · exact Or.inl yr
          · exact Or.inr ⟨⟨yA,not_or.mpr ⟨yr,fun yN => G.isIndepSet_neighborSet_of_triangleFree ht r adj (Finset.mem_filter.mp yN).2 xy.ne xy⟩⟩,xy⟩
        · rintro (rfl|⟨⟨yA,_⟩,xy⟩)
          · exact ⟨hr,adj.symm⟩
          · exact ⟨yA,xy⟩
      have mm := hmin x (hNA xN)
      have mx := hs (A.filter (G.Adj x)) (Finset.filter_subset ..) (neighbors_small G ht A x)
      have rn : r∉B.filter (G.Adj x) := fun h => rB (Finset.mem_filter.mp h).1
      rw [eq,Finset.card_insert_of_notMem rn] at mm mx
      rw [sizeAt_finset G hbn,hb]
      exact ⟨mm,mx⟩
    have grown := grow_complete G A (k+1) d ht hs r front base nodup cover dl ha hnot hcount hmin sorted_
    obtain ⟨l,hperm,heq⟩ := hnorm (r::front++base)
    refine ⟨l,hperm.nodup_iff.mpr nodup,?_,?_⟩
    · rw [← cover]
      ext x
      exact List.mem_toFinset.trans (hperm.mem_iff.trans List.mem_toFinset.symm)
    · rw [heq,levels,if_neg (Finset.card_ne_zero.mpr non)]
      apply List.mem_eraseDups.mpr
      apply List.mem_flatMap.mpr
      refine ⟨d,List.mem_range.mpr (by omega),List.mem_flatMap.mpr ⟨encode G base,?_,List.mem_map.mpr ⟨_,grown,rfl⟩⟩⟩
      simpa only [show A.card-1-d=B.card by omega] using cls


private def swapAt {α : Type*} : Nat → List α → List α
  | 0,x::y::xs => y::x::xs
  | i+1,x::xs => x::swapAt i xs
  | _,l => l

private theorem swap_perm {α : Type*} (i : Nat) (l : List α) : (swapAt i l).Perm l := by
  induction i generalizing l with
  | zero => cases l with | nil => rfl | cons a l => cases l with | nil => rfl | cons b l => exact List.Perm.swap a b l
  | succ i ih => cases l with | nil => rfl | cons a l => exact List.Perm.cons a (ih l)

private def exchange : Nat → Nat → Nat
  | 0,x => 4*(x/4)+2*(x%2)+((x/2)%2)
  | i+1,x => 2*exchange i (x/2)+x%2

private theorem bits_swap (i : Nat) (l : List Bool) (h : i+2≤l.length) :
    bits (swapAt i l)=exchange i (bits l) := by
  induction i generalizing l with
  | zero =>
    obtain ⟨a,b,l,rfl⟩ : ∃ a b t,l=a::b::t := by cases l with | nil => simp at h | cons a l => cases l with | nil => simp at h | cons b t => exact ⟨_,_,_,rfl⟩
    cases a <;> cases b <;> simp [swapAt,bits,exchange] <;> omega
  | succ i ih =>
    cases l with
    | nil => simp at h
    | cons a t =>
      have e := ih t (by simp at h; omega)
      cases a <;> simp [swapAt,bits,exchange,half_step,e]

private theorem swap_map {α β : Type*} (f : α→β) (i : Nat) (l : List α) :
    (swapAt i l).map f=swapAt i (l.map f) := by
  induction i generalizing l with
  | zero => cases l with | nil => rfl | cons a l => cases l <;> rfl
  | succ i ih => cases l with | nil => rfl | cons a l => simp [swapAt,ih]

private def swapCode : Nat → List Nat → List Nat
  | 0,p::q::rs => (p%2+2*q)::(p/2)::rs
  | i+1,p::rs => exchange i p :: swapCode i rs
  | _,l => l

private theorem swap_encode {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (i : Nat) (l : List V) (h : i+2≤l.length) : encode G (swapAt i l) = swapCode i (encode G l) := by
  induction i generalizing l with
  | zero =>
    obtain ⟨a,b,t,rfl⟩ : ∃ a b t,l=a::b::t := by cases l with | nil => simp at h | cons a l => cases l with | nil => simp at h | cons b t => exact ⟨_,_,_,rfl⟩
    by_cases adj : G.Adj a b <;> simp [swapAt,swapCode,encode,bits,adj,G.adj_comm b a,Nat.add_comm]
    omega
  | succ i ih =>
    cases l with
    | nil => simp at h
    | cons a t =>
      have hi : i+2≤t.length := by simp at h; omega
      simp only [swapAt,encode,swap_map,swapCode,List.cons.injEq]
      exact ⟨bits_swap i _ (by simpa using hi),ih t hi⟩

private def relabel (swaps rows : List Nat) :=
  swaps.foldl (fun l i => if i+2≤l.length then swapCode i l else l) rows

private theorem relabel_real {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (swaps : List Nat) (l : List V) : ∃ l', l'.Perm l ∧ encode G l'=relabel swaps (encode G l) := by
  induction swaps generalizing l with
  | nil => exact ⟨l,.refl _,rfl⟩
  | cons i is ih =>
    by_cases hi : i+2≤l.length
    · obtain ⟨t,ht,he⟩ := ih (swapAt i l)
      exact ⟨t,ht.trans (swap_perm ..),by simpa [relabel,encode_length,hi,swap_encode G i l hi] using he⟩
    · simpa [relabel,encode_length,hi] using ih l


private def renumber : List Nat → List Nat
  | [1,2,1,0] => [2]
  | [1,2,3,2,2,1,0] => [2,4]
  | [1,4,3,2,2,1,0] => [3,2,5,4]
  | [1,8,3,2,2,1,0] => [4,3,2,3,5,4]
  | [1,9,3,2,2,1,0] => [2,4]
  | [1,12,3,2,2,1,0] => [5,4,3,2,4,3,5,4]
  | [1,16,3,2,2,1,0] => [5,4,3,2,4,3,5,4]
  | [1,17,3,2,2,1,0] => [3,2,5,4]
  | [1,18,3,2,2,1,0] => [4,3,2,3,5,4]
  | [3,2,2,3,2,1,0] => [5,4,3,2,1,0,5,4,3,2,1,5,4,3,2,5,4,3,4]
  | [3,2,4,3,2,1,0] => [5,4,3,2,1,0,4,3,2,1,5,4,3,2,5,4,3,4]
  | [3,2,6,3,2,1,0] => [5,4,3,2,1,0,4,3,2,1,5,4,3,2,4,3]
  | [3,2,10,1,1,1,0] => [4,3,2,1,0,5,4,3,2,1,5,4,3,2,4,3]
  | [3,4,8,3,2,1,0] => [4,3,2,1,0,3,2,1,5,4,3,2,5,4,3,4]
  | [3,4,9,1,1,1,0] => [2,1,0,2,1,3,2,5]
  | [3,4,9,3,2,1,0] => [4,3,2,1,0,3,2,1,5,4,3,2,4,3]
  | [3,4,9,3,2,2,1,0] => [3,5]
  | [3,8,8,3,2,1,0] => [3,2,1,0,3,2,1,5,4,3,2,5,4,3,4]
  | [3,8,9,1,1,1,0] => [5,4,3,2,1,0,2,1,5,4,3,2]
  | [3,8,9,3,2,1,0] => [3,2,1,0,3,2,1,5,4,3,2,4,3]
  | [3,8,17,3,2,2,1,0] => [4,3,6,5]
  | [3,10,8,1,1,1,0] => [3,2,1,0,3,2,1,4,3,2,3]
  | [3,10,10,1,1,1,0] => [2,1,0,3,2,1,2,4,3,5,4,5]
  | [3,12,8,3,2,1,0] => [2,1,0,3,2,1,4,3,2,3]
  | [3,12,9,1,0,1,0] => [1,5]
  | [3,12,17,3,2,2,1,0] => [4,6]
  | [3,16,9,1,1,1,0] => [0,5,4,3,2]
  | [3,16,18,3,2,2,1,0] => [5,4,3,4,6,5]
  | [3,18,10,1,1,1,0] => [1,5,4,3,5,4,5]
  | [3,18,18,3,2,2,1,0] => [3,5,4,6]
  | [3,24,16,3,2,2,1,0] => [1,6,5,4,3,5,4,6,5]
  | [3,24,17,3,2,2,1,0] => [6,5,4,3,5,4,6,5]
  | [3,24,18,3,2,2,1,0] => [6,5,4,3,6,5,4,6,5,6]
  | [7,24,66,137,3,12,9,3,2,2,1,0] => [0,4,3,2,5,4,3,5,4,8,7,10,9]
  | [7,24,130,145,3,12,9,3,2,2,1,0] => [0,5,4,3,2,5,4,3,5,4,9,8,7,8,10,9]
  | [7,24,146,145,3,12,9,3,2,2,1,0] => [5,7,9]
  | [7,24,194,129,3,2,6,3,2,2,1,0] => [2,8,10]
  | [7,24,194,129,3,12,9,3,2,2,1,0] => [0,5,4,3,2,5,4,3,5,4,5,10,9,8,7,9,8,10,9]
  | [7,24,194,137,3,2,6,3,2,2,1,0] => [2,8,10]
  | [7,24,194,137,3,12,9,3,2,2,1,0] => [7,6,5,4,3,2,1,0,9,8,7,6,5,4,3,2,1,8,7,6,5,4,3,2,7,6,5,4,3,9,8,7,6,5,4,10,9,8,7,6,5,7,6,8,7,9,8,10]
  | [7,24,194,145,3,12,9,3,2,2,1,0] => [6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,8,7,6,5,4,3,2,8,7,6,5,4,3,9,8,7,6,5,4,10,9,8,7,6,5,7,6,8,7,9,8,10]
  | [7,36,132,146,3,2,6,3,2,2,1,0] => [4,6]
  | [7,36,140,146,3,2,6,3,2,2,1,0] => [4,6]
  | [7,36,196,130,3,2,6,3,2,2,1,0] => [2,4,6,8,10]
  | [7,36,196,134,3,2,6,3,2,2,1,0] => [2,4,6,8,10]
  | [7,36,196,146,3,2,6,3,2,2,1,0] => [4,6]
  | [7,260,140,144,3,2,6,3,2,2,1,0] => [2,1,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,260,140,145,3,2,6,3,2,2,1,0] => [4,3,2,1,0,6,5,4,3,2,1,3,2,5,4,3,6,5,4,8,7,6,5,8,7,6,10,9,8,7,9,8,10,9]
  | [7,260,140,146,3,2,6,3,2,2,1,0] => [3,2,1,0,1,4,3,2,5,4,3,4,9,8,7,6,8,10,9]
  | [7,260,268,145,3,2,6,3,2,2,1,0] => [9,8,7,6,5,4,3,2,1,0,1,10,9,8,7,6,5,4,3,2,9,8,7,6,5,4,3,5,4,6,8,10]
  | [7,260,268,145,3,12,9,3,2,2,1,0] => [5,7,9]
  | [7,264,146,144,3,2,6,3,2,2,1,0] => [2,1,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,264,146,145,3,2,6,3,2,2,1,0] => [4,3,2,1,0,1,4,3,2,6,5,4,3,4,9,8,7,6,8,10,9]
  | [7,264,146,146,3,2,6,3,2,2,1,0] => [3,2,1,0,5,4,3,2,1,3,2,5,4,3,6,5,4,8,7,6,5,8,7,6,10,9,8,7,9,8,10,9]
  | [7,264,274,146,3,2,6,3,2,2,1,0] => [9,8,7,6,5,4,3,2,1,0,1,10,9,8,7,6,5,4,3,2,9,8,7,6,5,4,3,5,4,7,6,9,8,10]
  | [7,280,146,144,3,2,6,3,2,2,1,0] => [2,1,2,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,280,146,146,3,2,6,3,2,2,1,0] => [1,4,6]
  | [7,280,194,129,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,3,2,1,0,3,2,1,10,9,8,7,6,5,4,3,2,10,9,8,7,6,5,4,3,5,4,6,8,10]
  | [7,280,194,144,3,2,6,3,2,2,1,0] => [2,1,2,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,280,194,145,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,3,2,1,0,3,2,1,10,9,8,7,6,5,4,3,2,10,9,8,7,6,5,4,3,5,4,6,8,10]
  | [7,280,194,146,3,2,6,3,2,2,1,0] => [2,1,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,280,274,146,3,2,6,3,2,2,1,0] => [1,2,4,6,8,10]
  | [7,292,196,130,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,3,2,1,0,3,2,1,10,9,8,7,6,5,4,3,2,10,9,8,7,6,5,4,3,5,4,7,6,9,8,10]
  | [7,292,196,134,3,2,6,3,2,2,1,0] => [4,6]
  | [7,292,196,144,3,2,6,3,2,2,1,0] => [2,1,2,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,292,196,145,3,2,6,3,2,2,1,0] => [2,1,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,292,196,146,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,3,2,1,0,3,2,1,10,9,8,7,6,5,4,3,2,10,9,8,7,6,5,4,3,5,4,7,6,9,8,10]
  | [7,292,268,145,3,2,6,3,2,2,1,0] => [1,2,8,10]
  | [7,292,268,145,3,12,9,3,2,2,1,0] => [5,7,9]
  | [7,384,258,134,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,384,258,134,3,12,9,3,2,2,1,0] => [0,8,7,6,5,4,3,2,9,8,7,6,5,4,3,10,9,8,7,6,5,4,8]
  | [7,384,260,137,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,384,260,145,3,12,9,3,2,2,1,0] => [0,8,7,6,5,4,3,2,9,8,7,6,5,4,3,10,9,8,7,6,5,4,7,10,9,8,10]
  | [7,384,264,137,3,12,9,3,2,2,1,0] => [0,9,8,7,6,5,4,3,2,9,8,7,6,5,4,3,10,9,8,7,6,5,4,8,7,9,8,10]
  | [7,384,268,137,3,2,6,3,2,2,1,0] => [2,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,384,268,137,3,12,9,3,2,2,1,0] => [7,6,5,4,3,2,1,0,5,4,3,2,1,7,6,5,4,3,2,9,8,7,6,5,4,3,8,7,6,5,4,8,7,6,5,7,6,8,7,10,9,8,10]
  | [7,384,268,145,3,2,6,3,2,2,1,0] => [2,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,384,268,145,3,12,9,3,2,2,1,0] => [6,5,4,3,2,1,0,6,5,4,3,2,1,7,6,5,4,3,2,8,7,6,5,4,3,8,7,6,5,4,8,7,6,5,7,6,8,7,10,9,8,10]
  | [7,384,274,146,3,2,6,3,2,2,1,0] => [2,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,384,274,148,3,12,9,3,2,2,1,0] => [2,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,9,8,7,10,9,8,10,9,10]
  | [7,384,276,145,3,12,9,3,2,2,1,0] => [10,9,8,7,6,5,4,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,9,10]
  | [7,388,258,134,3,2,6,3,2,2,1,0] => [4,3,2,1,0,6,5,4,3,2,1,4,3,2,5,4,3,6,5,4,7,6,5,8,7,6,9,8,7,8,10,9]
  | [7,388,260,137,3,2,6,3,2,2,1,0] => [4,3,2,1,0,2,1,4,3,2,6,5,4,3,5,4,10,9,8,7,6,9,8,10,9]
  | [7,388,260,145,3,12,9,3,2,2,1,0] => [1,10,9,8,7,6,5,4,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,9,10]
  | [7,388,264,137,3,12,9,3,2,2,1,0] => [1,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,9,8,7,10,9,8,10,9,10]
  | [7,388,268,137,3,2,6,3,2,2,1,0] => [1,2,8,10]
  | [7,388,268,145,3,2,6,3,2,2,1,0] => [9,8,7,6,5,4,3,2,1,0,1,10,9,8,7,6,5,4,3,2,9,8,7,6,5,4,3,5,4,6,8,10]
  | [7,388,268,145,3,12,9,3,2,2,1,0] => [5,7,9]
  | [7,388,274,146,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,388,274,148,3,12,9,3,2,2,1,0] => [2,1,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,9,8,7,10,9,8,10,9,10]
  | [7,388,276,145,3,12,9,3,2,2,1,0] => [1,10,9,8,7,6,5,4,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,9,10]
  | [7,392,258,134,3,2,6,3,2,2,1,0] => [3,2,1,0,2,1,4,3,2,5,4,3,5,4,10,9,8,7,6,9,8,10,9]
  | [7,392,260,137,3,2,6,3,2,2,1,0] => [3,2,1,0,5,4,3,2,1,4,3,2,5,4,3,6,5,4,7,6,5,8,7,6,9,8,7,8,10,9]
  | [7,392,268,137,3,2,6,3,2,2,1,0] => [2,1,2,4,6,8,10]
  | [7,392,268,145,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,392,274,146,3,2,6,3,2,2,1,0] => [9,8,7,6,5,4,3,2,1,0,1,10,9,8,7,6,5,4,3,2,9,8,7,6,5,4,3,5,4,7,6,9,8,10]
  | [15,304,164,162,82,3,2,9,1,1,1,0] => [2,1,0,10,9,8,7,6,5,4,3,2,1,9,8,7,6,5,4,3,2,6,5,4,3,6,5,7,6,8,7,9,10]
  | [15,304,196,138,73,1,6,3,2,2,1,0] => [2,1,3,2,8,10]
  | [15,584,392,268,145,3,2,6,3,2,2,1,0] => [5,7]
  | _ => []

private def normalized (g : List Nat) := relabel (renumber g) g

private def roots0 : List (List Nat) := []
private def roots1 : List (List Nat) := []
private def roots2 : List (List Nat) := []
private def roots3 : List (List Nat) := [[15,560,388,274,146,3,2,6,3,2,2,1,0]]
private def roots4 : List (List Nat) := [[7,24,130,145,3,2,6,3,2,2,1,0],
  [7,24,146,145,3,2,6,3,2,2,1,0],
  [7,24,194,145,3,2,6,3,2,2,1,0],
  [7,280,146,145,3,2,6,3,2,2,1,0],
  [7,280,194,137,3,2,6,3,2,2,1,0],
  [7,24,98,137,3,12,9,3,2,2,1,0],
  [7,132,268,137,3,12,9,3,2,2,1,0],
  [7,196,268,137,3,12,9,3,2,2,1,0],
  [7,388,258,134,3,12,9,3,2,2,1,0],
  [7,388,268,137,3,12,9,3,2,2,1,0],
  [15,296,196,140,73,1,6,3,2,2,1,0],
  [15,352,196,146,82,3,10,10,1,0,1,0]]

theorem degrees_length (g : List Nat) : (degrees g).length=g.length := by
  have step (xs : List Nat) (m : Nat) : (bump m xs).length=xs.length := by
    induction xs generalizing m with | nil => rfl | cons a xs ih => simp [bump,ih]
  induction g with | nil => rfl | cons a g ih => simp [degrees,step,ih]

theorem bump_sum (xs : List Nat) (m : Nat) : (bump m xs).sum=xs.sum+countBits xs.length m := by
  induction xs generalizing m with | nil => rfl | cons a xs ih => simp [bump,countBits,ih]; omega

def edges_ : List Nat → Nat
  | [] => 0
  | m::t => countBits t.length m + edges_ t

theorem energy (rows : List Nat) : (degrees rows).sum=2*edges_ rows := by
  induction rows with
  | nil => rfl
  | cons m t ih => simp [degrees,edges_,bump_sum,degrees_length,ih]; omega

theorem count_shift (n a j : Nat) : countBits (j+n) (2^j*a)=countBits n a := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : 2^(j+1)*a=2*(2^j*a) := by rw [pow_succ]; ring
    rw [Nat.succ_add,countBits,e]
    simp [ih]

theorem count_full (d n : Nat) : countBits (d+n) (2^d-1)=d := by
  induction d with
  | zero =>
    have h (t : Nat) : countBits t 0=0 := by induction t with | zero => rfl | succ k ih => simp [countBits,ih]
    simp [h]
  | succ d ih =>
    have hp : 0 < 2^d := Nat.two_pow_pos _
    have split : 2^(d+1)-1=2*(2^d-1)+1 := by rw [pow_succ]; omega
    rw [Nat.succ_add,countBits,split,half_step,ih]
    omega

theorem shifted_length (xs : List Nat) : (shifted xs).length=xs.length := by
  induction xs with | nil => rfl | cons a xs ih => simp [shifted,ih]

theorem edges_attached (xs b : List Nat) : edges_ (attach xs b) =
    xs.length + (xs.map (countBits b.length)).sum + edges_ b := by
  have h (ls : List Nat) : edges_ (shifted ls++b)=(ls.map (countBits b.length)).sum+edges_ b := by
    induction ls with
    | nil => simp [shifted]
    | cons a ls ih => simp [shifted,edges_,shifted_length,count_shift,ih,Nat.add_assoc]
  simp [attach,edges_,shifted_length,count_full,h,Nat.add_assoc]

def Extension (k d : Nat) (b cs : List Nat) : Prop :=
  cs.length = d ∧ (∀ x ∈ cs, x ∈ usable k d b) ∧ okContacts k (inds b) cs = true ∧ cs.Pairwise (· ≤ ·)
theorem graphExtension {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k d : Nat) (ht : G.CliqueFree 3) (hs : Small G A k)
    (r : V) (front base : List V) (hn : (r::front++base).Nodup)
    (hall : (r::front++base).toFinset=A) (hd : front.length=d)
    (ha : ∀ x∈front,G.Adj r x) (hb : ∀ x∈base,¬G.Adj r x)
    (hcount : ∀ x∈front,d≤ sizeAt G base x+1 ∧ sizeAt G base x+1 < k)
    (hmin : ∀ x∈A,d≤(A.filter (G.Adj x)).card)
    (horder : (contactsOf G base front).Pairwise (·≤·)) :
    ∃ cs, Extension k d (encode G base) cs ∧ encode G (r::front++base) = attach cs (encode G base) := by
  let cs := contactsOf G base front
  have split := root_encoding G r front base ha hb ht
  change encode G (r::front++base) = attach cs (encode G base) at split
  have hbnd := (List.nodup_append.mp (List.nodup_cons.mp hn).2).2.1
  have hc (s) (mem : s ∈ cs) : s ∈ usable k d (encode G base) := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp mem
    let S := base.toFinset.filter (G.Adj x)
    have row := inds_complete G base hbnd S (Finset.filter_subset ..) (neighbors_small G ht _ x)
    have m := hcount x hx
    rw [sizeAt_finset G hbnd] at m
    change bits (base.map fun y => decide (G.Adj x y)) ∈ _
    rw [row_mark]
    exact List.mem_map.mpr ⟨_,List.mem_filter.mpr ⟨row,by simpa [S] using m⟩,rfl⟩
  have guard_ (u w : List Nat) (h : cs=u++w) : guardRows k (encode G base) (inds (encode G base)) u := by
    let sl := front.take u.length
    have hu : contactsOf G base sl = u := by
      change (front.take u.length).map _=u
      rw [List.map_take, show front.map _=u++w from h, List.take_left]
    have ssub := (List.take_sublist u.length front).append (List.Sublist.refl base)
    have nodup : (sl++base).Nodup := (List.nodup_cons.mp hn).2.sublist ssub
    have sub : (sl++base).toFinset ⊆ A := by
      intro x hx
      rw [← hall]
      exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (ssub.subset (List.mem_toFinset.mp hx)))
    have ha' (x) (hx : x∈sl) := ha x ((List.take_sublist u.length front).subset hx)
    have indep : Gᶜ.IsClique (sl.toFinset : Set V) := by
      rw [G.isClique_compl]
      intro x hx y hy hxy
      exact G.isIndepSet_neighborSet_of_triangleFree ht r (ha' x (List.mem_toFinset.mp hx)) (ha' y (List.mem_toFinset.mp hy)) hxy
    have em := contacts G sl base (by intro x hx y hy adj; exact G.isIndepSet_neighborSet_of_triangleFree ht r (ha' x hx) (ha' y hy) adj.ne adj)
    change encode G (sl++base)=shifted (contactsOf G base sl)++encode G base at em
    rw [← hu]
    apply Bool.and_eq_true_iff.mpr
    refine ⟨ok_contacts G A k hs sl base nodup sub indep,?_⟩
    rw [← em]
    exact degrees_bound G ht A k hs _ nodup sub
  exact ⟨cs, ⟨by simp [cs,contactsOf,hd], hc,
    (Bool.and_eq_true_iff.mp (guard_ cs [] (by simp))).1, horder⟩, split⟩

theorem rootSplitting {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (norm : List Nat → List Nat)
    (hnorm : ∀ l : List V, ∃ l' : List V, l'.Perm l ∧ encode G l'=norm (encode G l))
    (k : Nat) (A : Finset V) (non : A.Nonempty) (cap : Nat) (hs : Small G A (k+1))
    (hu : A.Nonempty → ∃ x∈A,(A.filter (G.Adj x)).card ≤ cap) :
    ∃ (vs : List V) (d : Nat) (b cs : List Nat), vs.Nodup ∧ vs.toFinset=A ∧ d≤cap ∧
      b∈levels norm k (A.card-1-d) (k-1) ∧ Extension (k+1) d b cs ∧ encode G vs=attach cs b ∧ ∃ r ∈ A, (A.filter (G.Adj r)).card = d := by
    obtain ⟨r,hr,hmin⟩ := A.exists_min_image (fun x => (A.filter (G.Adj x)).card) non
    let N := A.filter (G.Adj r)
    let B := A \ insert r N
    let d := N.card
    have hNr : r∉N := by simp [N]
    have hNA : N⊆A := Finset.filter_subset ..
    have hBA : B⊆A := Finset.sdiff_subset
    have hu' : d≤cap := by obtain ⟨x,hx,hh⟩ := hu non; exact (hmin x hx).trans hh
    have hdk : d≤k := Nat.le_of_lt_succ (hs N hNA (neighbors_small G ht A r))
    have hBcard : B.card + d + 1 = A.card := by
      have hh := Finset.card_sdiff_add_card_eq_card (Finset.insert_subset hr hNA)
      rw [Finset.card_insert_of_notMem hNr] at hh
      omega
    have rB : r∉B := by simp [B]
    have hbase (x) (hx : x∈B) : ¬G.Adj r x := by
      have h := Finset.mem_sdiff.mp hx
      exact fun ha => h.2 (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨h.1,ha⟩))
    have noK : Small G B k := by
      intro S hS hI
      have rn : r∉S := fun h => rB (hS h)
      have indep : Gᶜ.IsClique (insert r S : Finset V) := by
        rw [Finset.coe_insert,SimpleGraph.isClique_insert_of_notMem rn]
        exact ⟨hI,fun x hx => ⟨fun e => rn (e ▸ hx),hbase x (hS hx)⟩⟩
      have hh := hs (insert r S) (Finset.insert_subset hr (hS.trans hBA)) indep
      rw [Finset.card_insert_of_notMem rn] at hh
      omega
    obtain ⟨base,hbn,hb,cls⟩ := levels_complete G ht norm hnorm k B (k-1) noK (by
      rintro ⟨x,hx⟩
      have mm := noK (B.filter (G.Adj x)) (Finset.filter_subset ..) (neighbors_small G ht B x)
      exact ⟨x,hx,by omega⟩)
    obtain ⟨front,hfn,hf,sorted_⟩ := sorted_neigh G N base
    have ha (x) (hx : x∈front) : G.Adj r x := (Finset.mem_filter.mp (hf ▸ List.mem_toFinset.mpr hx)).2
    have hnot (x) (hx : x∈base) := hbase x (hb ▸ List.mem_toFinset.mpr hx)
    have dl : front.length=d := by rw [← List.toFinset_card_of_nodup hfn,hf]
    have nodup : (r::front++base).Nodup := by
      apply List.nodup_cons.mpr
      constructor
      · change r ∉ front++base
        rw [List.mem_append,not_or]
        exact ⟨fun h => hNr (hf ▸ List.mem_toFinset.mpr h), fun h => rB (hb ▸ List.mem_toFinset.mpr h)⟩
      · exact List.nodup_append.mpr ⟨hfn,hbn,fun x hx y hy e => hnot y hy (e ▸ ha x hx)⟩
    have cover : (r::front++base).toFinset=A := by
      ext x
      simp only [List.toFinset_cons,List.toFinset_append,hf,hb,B,Finset.mem_insert,Finset.mem_union,Finset.mem_sdiff]
      have h1 : x=r → x∈A := fun h => h ▸ hr
      have h2 : x∈N → x∈A := fun h => hNA h
      grind
    have hcount (x) (hx : x∈front) : d≤ sizeAt G base x+1 ∧ sizeAt G base x+1 < k+1 := by
      have xN : x∈N := hf ▸ List.mem_toFinset.mpr hx
      have adj := ha x hx
      have eq : A.filter (G.Adj x)=insert r (B.filter (G.Adj x)) := by
        ext y
        simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_sdiff,B]
        constructor
        · rintro ⟨yA,xy⟩
          by_cases yr : y=r
          · exact Or.inl yr
          · exact Or.inr ⟨⟨yA,not_or.mpr ⟨yr,fun yN => G.isIndepSet_neighborSet_of_triangleFree ht r adj (Finset.mem_filter.mp yN).2 xy.ne xy⟩⟩,xy⟩
        · rintro (rfl|⟨⟨yA,_⟩,xy⟩)
          · exact ⟨hr,adj.symm⟩
          · exact ⟨yA,xy⟩
      have mm := hmin x (hNA xN)
      have mx := hs (A.filter (G.Adj x)) (Finset.filter_subset ..) (neighbors_small G ht A x)
      have rn : r∉B.filter (G.Adj x) := fun h => rB (Finset.mem_filter.mp h).1
      rw [eq,Finset.card_insert_of_notMem rn] at mm mx
      rw [sizeAt_finset G hbn,hb]
      exact ⟨mm,mx⟩
    obtain ⟨cs,hcs,enc⟩ := graphExtension G A (k+1) d ht hs r front base nodup cover dl ha hnot hcount hmin sorted_
    exact ⟨r::front++base, d, encode G base, cs, nodup, cover, hu', by simpa only [show A.card-1-d=B.card by omega] using cls, hcs, enc, ⟨r, hr, rfl⟩⟩


private abbrev WeightedRow := (Nat × Nat) × Nat

private def rowScore (W : List WeightedRow) (x : Nat) : Nat :=
  ((W.filter (fun w => x &&& w.1.1 == 0)).map Prod.snd).sum

private def rowCapacity (W : List WeightedRow) : Nat :=
  (W.map fun w => (5-w.1.2)*w.2).sum

private def penalty (f : Nat → Bool) (x : Nat) := (f x).toNat

private theorem rowScore_cons (w : WeightedRow) (W : List WeightedRow) (cs : List Nat) :
    (cs.map (rowScore (w::W))).sum =
    (cs.filter (fun x => x &&& w.1.1 == 0)).length*w.2 + (cs.map (rowScore W)).sum := by
  induction cs with
  | nil => simp
  | cons x cs ih =>
    by_cases e : x &&& w.1.1 = 0
    · simp [rowScore,e,Nat.succ_mul] at ih ⊢
      omega
    · simp [rowScore,e] at ih ⊢
      omega

private theorem rowScore_le (b cs : List Nat) (W : List WeightedRow)
    (valid : ∀ w∈W,w.1∈inds b) (good : okContacts 6 (inds b) cs=true) :
    (cs.map (rowScore W)).sum ≤ rowCapacity W := by
  induction W with
  | nil =>
    have h : rowScore [] = fun _ => 0 := rfl
    simp [h,rowCapacity]
  | cons w W ih =>
    have sub := ih (fun t ht => valid t (.tail _ ht))
    have hm := of_decide_eq_true (List.all_eq_true.mp good w.1 (valid w (.head _)))
    have lecap : (cs.filter (fun x => x &&& w.1.1 == 0)).length ≤ 5-w.1.2 := by omega
    have lh := Nat.mul_le_mul_right w.2 lecap
    rw [rowScore_cons]
    change _ ≤ (5-w.1.2)*w.2 + rowCapacity W
    omega

private theorem rowScore_ge (b : List Nat) (f : Nat → Bool) (edgeWeight extraWeight low : Nat) (W : List WeightedRow)
    (cs : List Nat) (h : ∀ x∈cs, low ≤ countBits b.length x * edgeWeight + penalty f x * extraWeight + rowScore W x) :
    cs.length*low ≤ (cs.map (countBits b.length)).sum * edgeWeight +
      (cs.map (penalty f)).sum * extraWeight + (cs.map (rowScore W)).sum := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have hh := ih (fun x hx => h x (.tail _ hx))
    have hc := h c (.head _)
    simp only [List.length_cons,Nat.succ_mul,List.map_cons,List.sum_cons,Nat.add_mul]
    omega


private def dualCheckSimple (limit : Nat) (b : List Nat) (d edgeWeight low : Nat)
    (W : List WeightedRow) : Bool :=
  W.all (fun w => decide (w.1 ∈ inds b)) &&
  (usable 6 d b).all (fun x => decide (low ≤ countBits b.length x * edgeWeight + rowScore W x)) &&
  decide ((limit - edges_ b - d) * edgeWeight + rowCapacity W < d * low)

private theorem viaDualImpossible (b cs : List Nat) (d low : Nat) (W : List WeightedRow)
    (ext : Extension 6 d b cs)
    (check : dualCheckSimple 0 b d 0 low W = true) : False := by
  obtain ⟨len, mem, good, _⟩ := ext
  obtain ⟨both, last⟩ := Bool.and_eq_true_iff.mp check
  obtain ⟨valid, opts⟩ := Bool.and_eq_true_iff.mp both
  have upper := rowScore_le b cs W (fun w hw => of_decide_eq_true (List.all_eq_true.mp valid w hw)) good
  have lower := rowScore_ge b (fun _ => false) 0 0 low W cs (fun x hx => by
    have hx' := of_decide_eq_true (List.all_eq_true.mp opts x (mem x hx))
    simp only [Nat.mul_zero, Nat.zero_add] at hx' ⊢
    exact hx')
  simp only [Nat.mul_zero, Nat.zero_add] at lower
  have hl := of_decide_eq_true last
  simp only [Nat.mul_zero, Nat.zero_add] at hl
  rw [len] at lower
  omega

private theorem viaDual32 (b cs : List Nat) (d edgeWeight low : Nat) (W : List WeightedRow)
    (ext : Extension 6 d b cs)
    (check : dualCheckSimple 31 b d edgeWeight low W = true) :
    32 ≤ edges_ (attach cs b) := by
  by_contra! small
  obtain ⟨len, mem, good, _⟩ := ext
  obtain ⟨both, last⟩ := Bool.and_eq_true_iff.mp check
  obtain ⟨valid, opts⟩ := Bool.and_eq_true_iff.mp both
  have upper := rowScore_le b cs W (fun w hw => of_decide_eq_true (List.all_eq_true.mp valid w hw)) good
  have lower := rowScore_ge b (fun _ => false) edgeWeight 0 low W cs (fun x hx => by
    have hx' := of_decide_eq_true (List.all_eq_true.mp opts x (mem x hx))
    simp only [Nat.mul_zero, Nat.add_zero]
    exact hx')
  simp only [Nat.mul_zero, Nat.add_zero] at lower
  rw [edges_attached, len] at small
  have e : (cs.map (countBits b.length)).sum ≤ 31 - edges_ b - d := by omega
  have he := Nat.mul_le_mul_right edgeWeight e
  have hl := of_decide_eq_true last
  rw [len] at lower
  omega

private def allInd4 (b : List Nat) : List WeightedRow :=
  ((inds b).filter (fun p => p.2 == 4)).map (fun p => (p, 1))

private abbrev b3_0 : List Nat := [15,560,388,274,146,3,2,6,3,2,2,1,0]
private abbrev b4_0 : List Nat := [7,24,130,145,3,2,6,3,2,2,1,0]
private abbrev b4_1 : List Nat := [7,24,146,145,3,2,6,3,2,2,1,0]
private abbrev b4_2 : List Nat := [7,24,194,145,3,2,6,3,2,2,1,0]
private abbrev b4_3 : List Nat := [7,280,146,145,3,2,6,3,2,2,1,0]
private abbrev b4_4 : List Nat := [7,280,194,137,3,2,6,3,2,2,1,0]
private abbrev b4_5 : List Nat := [7,24,98,137,3,12,9,3,2,2,1,0]
private abbrev b4_6 : List Nat := [7,132,268,137,3,12,9,3,2,2,1,0]
private abbrev b4_7 : List Nat := [7,196,268,137,3,12,9,3,2,2,1,0]
private abbrev b4_8 : List Nat := [7,388,258,134,3,12,9,3,2,2,1,0]
private abbrev b4_9 : List Nat := [7,388,268,137,3,12,9,3,2,2,1,0]
private abbrev b4_10 : List Nat := [15,296,196,140,73,1,6,3,2,2,1,0]
private abbrev b4_11 : List Nat := [15,352,196,146,82,3,10,10,1,0,1,0]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 30000000 in
private theorem smaller3 : (levels normalized 5 13 4).all (fun b => decide (b ∈ roots3)) = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 30000000 in
private theorem smaller4 : (levels normalized 5 12 4).all (fun b => decide (b ∈ roots4)) = true := by
  decide +kernel

/- Degree-4 case of R(3,6) = 18: b3_0 has no d=4 extension. -/

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b3_0_deg4_cert : dualCheckSimple 0 b3_0 4 0 11 (allInd4 b3_0) = true := by
  decide +kernel

theorem no_deg4_18 (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree 6)
    (hmin : ∀ v, 4 ≤ G.degree v) (h4 : ∃ v, G.degree v = 4) : False := by
  classical
  let U : Finset (Fin 18) := Finset.univ
  have bounded : Small G U 6 := by
    intro I _ hI
    by_contra! hc
    exact (hi.mono hc) I ⟨hI, rfl⟩
  have low : U.Nonempty → ∃ x ∈ U, (U.filter (G.Adj x)).card ≤ 4 := by
    intro _
    obtain ⟨v, hv⟩ := h4
    refine ⟨v, Finset.mem_univ v, ?_⟩
    simp only [U, ← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree]
    omega
  have hn (l : List (Fin 18)) := relabel_real G (renumber (encode G l)) l
  obtain ⟨vs, d, b, cs, _, _, hd, hb, hcs, _, ⟨r, _, hr⟩⟩ :=
    rootSplitting G ht normalized hn 5 U (by simp [U]) 4 bounded low
  have hdlb : 4 ≤ d := by
    have hmr := hmin r
    simp only [U, ← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree] at hr
    omega
  have hdeq : d = 4 := by omega
  subst hdeq
  have hb' : b ∈ levels normalized 5 13 4 := by simpa [U] using hb
  have ok := of_decide_eq_true (List.all_eq_true.mp smaller3 b hb')
  simp only [roots3, List.mem_cons, List.not_mem_nil, or_false] at ok
  subst ok
  exact viaDualImpossible b3_0 cs 4 11 (allInd4 b3_0) hcs b3_0_deg4_cert


/- Zero-branching dual certificates for 40 <= edges and 41 <= edges on 17-vertex (3,6)-graphs. -/


/- ## Generic Nat LP dual checker, tight filter, and exact sorted enumerators -/

private def hitScore (W : List WeightedRow) (x : Nat) : Nat :=
  ((W.filter (fun w => x &&& w.1.1 != 0)).map Prod.snd).sum

private def hitRhs (K d : Nat) (W : List WeightedRow) : Nat :=
  (W.map (fun w => (d + w.1.2 + 1 - K) * w.2)).sum

private theorem hitScore_cons (w : WeightedRow) (W : List WeightedRow) (cs : List Nat) :
    (cs.map (hitScore (w :: W))).sum =
    (cs.filter (fun x => x &&& w.1.1 != 0)).length * w.2 + (cs.map (hitScore W)).sum := by
  induction cs with
  | nil => simp
  | cons x cs ih =>
    by_cases e : x &&& w.1.1 = 0
    · simp [hitScore, e] at ih ⊢
      omega
    · simp [hitScore, e, Nat.succ_mul] at ih ⊢
      omega

private theorem hitScore_ge (K d : Nat) (b cs : List Nat) (W : List WeightedRow)
    (hlen : cs.length = d)
    (valid : ∀ w ∈ W, w.1 ∈ inds b ∧ K ≤ d + w.1.2 + 1)
    (good : okContacts K (inds b) cs = true) :
    hitRhs K d W ≤ (cs.map (hitScore W)).sum := by
  induction W with
  | nil =>
    have h : hitScore [] = fun _ => 0 := rfl
    simp [h, hitRhs]
  | cons w W ih =>
    have sub := ih (fun t ht => valid t (.tail _ ht))
    have hv := valid w (.head _)
    have hm := of_decide_eq_true (List.all_eq_true.mp good w.1 hv.1)
    have hsplit : (cs.filter (fun x => x &&& w.1.1 == 0)).length +
        (cs.filter (fun x => x &&& w.1.1 != 0)).length = cs.length := by
      clear * -
      induction cs with
      | nil => simp
      | cons x xs ihs =>
        by_cases h : x &&& w.1.1 = 0 <;> simp [h] <;> omega
    have hge : d + w.1.2 + 1 - K ≤ (cs.filter (fun x => x &&& w.1.1 != 0)).length := by omega
    have lh := Nat.mul_le_mul_right w.2 hge
    rw [hitScore_cons]
    change (d + w.1.2 + 1 - K) * w.2 + hitRhs K d W ≤ _
    omega

private theorem hitScore_le_sum (n ew bpos bneg : Nat) (W : List WeightedRow) (cs : List Nat)
    (h : ∀ x ∈ cs, hitScore W x + bneg ≤ countBits n x * ew + bpos) :
    (cs.map (hitScore W)).sum + cs.length * bneg ≤
    (cs.map (countBits n)).sum * ew + cs.length * bpos := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have hh := ih (fun x hx => h x (.tail _ hx))
    have hc := h c (.head _)
    simp only [List.length_cons, Nat.succ_mul, List.map_cons, List.sum_cons, Nat.add_mul]
    omega

private theorem hitScore_tight_mem (n ew bpos bneg : Nat) (W : List WeightedRow) (cs : List Nat)
    (h : ∀ x ∈ cs, hitScore W x + bneg ≤ countBits n x * ew + bpos)
    (heq : (cs.map (hitScore W)).sum + cs.length * bneg =
      (cs.map (countBits n)).sum * ew + cs.length * bpos) :
    ∀ x ∈ cs, hitScore W x + bneg = countBits n x * ew + bpos := by
  induction cs with
  | nil => intro x hx; cases hx
  | cons c cs ih =>
    have htail := hitScore_le_sum n ew bpos bneg W cs (fun x hx => h x (.tail _ hx))
    have hc := h c (.head _)
    simp only [List.length_cons, Nat.succ_mul, List.map_cons, List.sum_cons, Nat.add_mul] at heq
    have hc_eq : hitScore W c + bneg = countBits n c * ew + bpos := by omega
    have htail_eq : (cs.map (hitScore W)).sum + cs.length * bneg =
        (cs.map (countBits n)).sum * ew + cs.length * bpos := by omega
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hc_eq
    · exact ih (fun y hy => h y (.tail _ hy)) htail_eq x hx'

private def dualCheckGen (K d minSz budget ew bpos bneg : Nat) (b : List Nat) (W : List WeightedRow) : Bool :=
  let is := inds b
  let cands := (is.filter (fun p => minSz ≤ p.2 && p.2 < K - 1)).map Prod.fst
  W.all (fun w => decide (w.1 ∈ is ∧ K ≤ d + w.1.2 + 1)) &&
  cands.all (fun x => decide (hitScore W x + bneg ≤ countBits b.length x * ew + bpos)) &&
  decide (budget * ew + d * bpos < hitRhs K d W + d * bneg)

private theorem viaDualGen (K d minSz budget ew bpos bneg : Nat) (b cs : List Nat) (W : List WeightedRow)
    (hlen : cs.length = d)
    (hmem : ∀ x ∈ cs, ∃ p ∈ inds b, p.1 = x ∧ minSz ≤ p.2 ∧ p.2 < K - 1)
    (hok : okContacts K (inds b) cs = true)
    (hsum : (cs.map (countBits b.length)).sum ≤ budget)
    (hcert : dualCheckGen K d minSz budget ew bpos bneg b W = true) : False := by
  unfold dualCheckGen at hcert
  dsimp only at hcert
  obtain ⟨both, hlast⟩ := Bool.and_eq_true_iff.mp hcert
  obtain ⟨hvalid, hopts⟩ := Bool.and_eq_true_iff.mp both
  have hge := hitScore_ge K d b cs W hlen
    (fun w hw => of_decide_eq_true (List.all_eq_true.mp hvalid w hw)) hok
  have hpt : ∀ x ∈ cs, hitScore W x + bneg ≤ countBits b.length x * ew + bpos := by
    intro x hx
    obtain ⟨p, hp, rfl, hp1, hp2⟩ := hmem x hx
    have hpm : p.1 ∈ ((inds b).filter (fun q => minSz ≤ q.2 && q.2 < K - 1)).map Prod.fst :=
      List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hp, by simp [hp1, hp2]⟩, rfl⟩
    exact of_decide_eq_true (List.all_eq_true.mp hopts p.1 hpm)
  have hle := hitScore_le_sum b.length ew bpos bneg W cs hpt
  rw [hlen] at hle
  have hmul := Nat.mul_le_mul_right ew hsum
  have hlt := of_decide_eq_true hlast
  omega

private def dualFilterGen (K d minSz budget ew bpos bneg : Nat) (b : List Nat)
    (W : List WeightedRow) (tight : List Nat) : Bool :=
  let is := inds b
  let cands := (is.filter (fun p => minSz ≤ p.2 && p.2 < K - 1)).map Prod.fst
  W.all (fun w => decide (w.1 ∈ is ∧ K ≤ d + w.1.2 + 1)) &&
  cands.all (fun x => decide (hitScore W x + bneg ≤ countBits b.length x * ew + bpos)) &&
  decide (budget * ew + d * bpos = hitRhs K d W + d * bneg) &&
  cands.all (fun x => !(hitScore W x + bneg == countBits b.length x * ew + bpos) || decide (x ∈ tight))

private theorem viaDualFilter (K d minSz budget ew bpos bneg : Nat) (b cs : List Nat)
    (W : List WeightedRow) (tight : List Nat)
    (hlen : cs.length = d)
    (hmem : ∀ x ∈ cs, ∃ p ∈ inds b, p.1 = x ∧ minSz ≤ p.2 ∧ p.2 < K - 1)
    (hok : okContacts K (inds b) cs = true)
    (hsum : (cs.map (countBits b.length)).sum ≤ budget)
    (hcert : dualFilterGen K d minSz budget ew bpos bneg b W tight = true) :
    ∀ x ∈ cs, x ∈ tight := by
  unfold dualFilterGen at hcert
  dsimp only at hcert
  obtain ⟨h123, h4⟩ := Bool.and_eq_true_iff.mp hcert
  obtain ⟨h12, h3⟩ := Bool.and_eq_true_iff.mp h123
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h12
  have hge := hitScore_ge K d b cs W hlen
    (fun w hw => of_decide_eq_true (List.all_eq_true.mp h1 w hw)) hok
  have hin : ∀ x ∈ cs, x ∈ ((inds b).filter (fun q => minSz ≤ q.2 && q.2 < K - 1)).map Prod.fst := by
    intro x hx
    obtain ⟨p, hp, rfl, hp1, hp2⟩ := hmem x hx
    exact List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hp, by simp [hp1, hp2]⟩, rfl⟩
  have hpt : ∀ x ∈ cs, hitScore W x + bneg ≤ countBits b.length x * ew + bpos :=
    fun x hx => of_decide_eq_true (List.all_eq_true.mp h2 x (hin x hx))
  have hle := hitScore_le_sum b.length ew bpos bneg W cs hpt
  rw [hlen] at hle
  have heq_rhs : budget * ew + d * bpos = hitRhs K d W + d * bneg := of_decide_eq_true h3
  have hmul := Nat.mul_le_mul_right ew hsum
  have htot_eq : (cs.map (hitScore W)).sum + cs.length * bneg =
      (cs.map (countBits b.length)).sum * ew + cs.length * bpos := by
    rw [hlen]; omega
  have htight := hitScore_tight_mem b.length ew bpos bneg W cs hpt htot_eq
  intro x hx
  have hx4 := List.all_eq_true.mp h4 x (hin x hx)
  have hxt := htight x hx
  simp [hxt] at hx4
  exact hx4

private theorem countBits_bits_eq {n : Nat} : ∀ bs : List Bool, bs.length = n →
    countBits n (bits bs) = (bs.filter id).length
  | [], h => by subst h; rfl
  | b :: bs, h => by
    subst h
    simp only [List.length_cons, countBits, bits]
    have ih := countBits_bits_eq bs rfl
    cases b
    · simp only [Bool.toNat_false, Nat.add_zero, List.filter, id_eq,
        Nat.mul_mod_right, Nat.mul_div_right _ (by decide : 0 < 2)]
      omega
    · simp only [Bool.toNat_true, List.filter, id_eq, List.length_cons]
      have h1 : (2 * bits bs + 1) % 2 = 1 := by omega
      have h2 : (2 * bits bs + 1) / 2 = bits bs := by omega
      rw [h1, h2, ih]
      omega

private theorem sizeAt_eq_filter_id {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (vs : List V) (u : V) :
    ((vs.map fun y => decide (G.Adj u y)).filter id).length = sizeAt G vs u := by
  induction vs with
  | nil => rfl
  | cons y ys ih => by_cases h : G.Adj u y <;> simp [sizeAt, h, ih]

private theorem countBits_inds_eq : ∀ (b : List Nat) (p : Nat × Nat), p ∈ inds b →
    countBits b.length p.1 = p.2 := by
  intro b
  induction b with
  | nil =>
    intro p hp
    simp [inds] at hp
    rcases hp with rfl
    rfl
  | cons m ms ih =>
    intro p hp
    simp only [inds, List.mem_append, List.mem_map, List.mem_filter] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, ⟨hq, _⟩, rfl⟩
    · simp only [ind0, List.length_cons, countBits, Nat.mul_mod_right,
        Nat.mul_div_right _ (by decide : 0 < 2), Nat.zero_add]
      exact ih q hq
    · simp only [ind1, List.length_cons, countBits]
      have h1 : (2 * q.1 + 1) % 2 = 1 := by omega
      have h2 : (2 * q.1 + 1) / 2 = q.1 := by omega
      rw [h1, h2, ih q hq]
      omega

private theorem ext_on_rep {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (K : Nat) (hi : Gᶜ.CliqueFree K)
    (v : V) (d minSz : Nat) (hdegv : G.degree v = d)
    (hminN : ∀ u ∈ G.neighborFinset v, minSz + 1 ≤ G.degree u)
    (vsB : List V) (hvsB_nd : vsB.Nodup) (hvsB_cov : vsB.toFinset = Gᶜ.neighborFinset v)
    (target : List Nat) (hvsB_enc : encode G vsB = target) :
    ∃ (front : List V) (cs : List Nat),
      front.Nodup ∧ front.toFinset = G.neighborFinset v ∧
      (v :: front ++ vsB).Nodup ∧ (v :: front ++ vsB).toFinset = Finset.univ ∧
      encode G (v :: front ++ vsB) = attach cs target ∧
      cs.length = d ∧
      (∀ x ∈ cs, ∃ p ∈ inds target, p.1 = x ∧ minSz ≤ p.2 ∧ p.2 < K - 1) ∧
      okContacts K (inds target) cs = true ∧
      cs.Pairwise (· ≤ ·) ∧
      (cs.map (countBits target.length)).sum + d = ∑ u ∈ G.neighborFinset v, G.degree u := by
  classical
  let N := G.neighborFinset v
  let B := Gᶜ.neighborFinset v
  obtain ⟨front, hfn, hfcov, hfsort⟩ := sorted_neigh G N vsB
  let cs := contactsOf G vsB front
  have hfl : front.length = d := by
    rw [← List.toFinset_card_of_nodup hfn, hfcov]
    simpa [N] using hdegv
  have ha (u : V) (hu : u ∈ front) : G.Adj v u := by
    have huN : u ∈ N := hfcov ▸ List.mem_toFinset.mpr hu
    exact (G.mem_neighborFinset v u).mp huN
  have hnot (y : V) (hy : y ∈ vsB) : ¬ G.Adj v y :=
    ((Gᶜ.mem_neighborFinset v y).mp (hvsB_cov ▸ List.mem_toFinset.mpr hy)).2
  have hv_notB : v ∉ B := fun h => ((Gᶜ.mem_neighborFinset v v).mp h).1 rfl
  have hv_notN : v ∉ N := fun h => (G.mem_neighborFinset v v).mp h |>.ne rfl
  have hnd : (v :: front ++ vsB).Nodup := by
    rw [List.cons_append]
    apply List.nodup_cons.mpr
    refine ⟨?_, List.nodup_append.mpr ⟨hfn, hvsB_nd, fun x hx y hy e => hnot y hy (e ▸ ha x hx)⟩⟩
    rw [List.mem_append, not_or]
    exact ⟨fun h => hv_notN (hfcov ▸ List.mem_toFinset.mpr h),
           fun h => hv_notB (show v ∈ Gᶜ.neighborFinset v from hvsB_cov ▸ List.mem_toFinset.mpr h)⟩
  have hcov : (v :: front ++ vsB).toFinset = Finset.univ := by
    ext x
    rw [List.cons_append]
    simp only [List.toFinset_cons, List.toFinset_append, hfcov, hvsB_cov,
      Finset.mem_insert, Finset.mem_union, Finset.mem_univ, iff_true, N, B,
      SimpleGraph.mem_neighborFinset, SimpleGraph.compl_adj]
    by_cases hvx : x = v
    · exact Or.inl hvx
    · by_cases hadj : G.Adj v x
      · exact Or.inr (Or.inl hadj)
      · exact Or.inr (Or.inr ⟨Ne.symm hvx, hadj⟩)
  have hNind : ∀ x ∈ front, ∀ y ∈ front, ¬ G.Adj x y := fun x hx y hy hxy =>
    G.isIndepSet_neighborSet_of_triangleFree ht v (ha x hx) (ha y hy) hxy.ne hxy
  have henc : encode G (v :: front ++ vsB) = attach cs target := by
    rw [← hvsB_enc]
    exact root_encoding G v front vsB ha hnot ht
  have hsmallK : Small G Finset.univ K := by
    intro I _ hI
    by_contra! hc
    exact (hi.mono hc) I ⟨hI, rfl⟩
  have hdeg_split (u : V) (hu : u ∈ N) : (B.filter (G.Adj u)).card + 1 = G.degree u := by
    have hvu : G.Adj v u := (G.mem_neighborFinset v u).mp hu
    have heq : G.neighborFinset u = insert v (B.filter (G.Adj u)) := by
      ext x
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_filter, B,
        SimpleGraph.compl_adj]
      constructor
      · intro hux
        by_cases hxv : x = v
        · exact Or.inl hxv
        · refine Or.inr ⟨⟨Ne.symm hxv, ?_⟩, hux⟩
          intro hvx
          exact G.isIndepSet_neighborSet_of_triangleFree ht v hvu hvx hux.ne hux
      · rintro (rfl | ⟨_, hux⟩)
        · exact hvu.symm
        · exact hux
    have hv_not : v ∉ B.filter (G.Adj u) := fun h => hv_notB (Finset.mem_filter.mp h).1
    rw [← G.card_neighborFinset_eq_degree u, heq, Finset.card_insert_of_notMem hv_not]
  have hmem : ∀ x ∈ cs, ∃ p ∈ inds target, p.1 = x ∧ minSz ≤ p.2 ∧ p.2 < K - 1 := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
    have huN : u ∈ N := hfcov ▸ List.mem_toFinset.mpr hu
    let S := vsB.toFinset.filter (G.Adj u)
    have hrow := inds_complete G vsB hvsB_nd S (Finset.filter_subset ..) (neighbors_small G ht _ u)
    rw [hvsB_enc] at hrow
    have hScard : S.card + 1 = G.degree u := by
      simpa [S, hvsB_cov] using hdeg_split u huN
    have hltK : G.degree u < K := by
      by_contra! hge
      apply hi.mono hge (G.neighborFinset u)
      refine ⟨?_, rfl⟩
      rw [G.coe_neighborFinset, G.isClique_compl]
      exact G.isIndepSet_neighborSet_of_triangleFree ht u
    have hminu := hminN u huN
    refine ⟨(mark vsB S, S.card), hrow, (row_mark G vsB u).symm, by omega, by omega⟩
  have hok : okContacts K (inds target) cs = true := by
    have hnd_app : (front ++ vsB).Nodup := (List.nodup_cons.mp hnd).2
    have hNcl : Gᶜ.IsClique (front.toFinset : Set V) := by
      intro x hx y hy hne
      exact ⟨hne, hNind x (List.mem_toFinset.mp hx) y (List.mem_toFinset.mp hy)⟩
    have h := ok_contacts G Finset.univ K hsmallK front vsB hnd_app (Finset.subset_univ _) hNcl
    rwa [hvsB_enc] at h
  have hsum : (cs.map (countBits target.length)).sum + d = ∑ u ∈ N, G.degree u := by
    rw [← hvsB_enc, encode_length]
    have hmap : cs.map (countBits vsB.length) = front.map (fun u => (B.filter (G.Adj u)).card) := by
      simp only [cs, contactsOf, List.map_map]
      apply List.map_congr_left
      intro u _
      simp only [Function.comp_apply]
      rw [countBits_bits_eq _ (List.length_map ..), sizeAt_eq_filter_id, sizeAt_finset G hvsB_nd, hvsB_cov]
    rw [hmap]
    have hst := List.sum_toFinset (fun u => (B.filter (G.Adj u)).card) hfn
    rw [hfcov] at hst
    have hsum_deg := Finset.sum_congr (s₁ := N) (s₂ := N) rfl (fun u hu => hdeg_split u hu)
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at hsum_deg
    have hNc : N.card = d := by simpa [N] using hdegv
    omega
  exact ⟨front, cs, hfn, hfcov, hnd, hcov, henc, by simp [cs, contactsOf, hfl], hmem, hok, hfsort, hsum⟩

private theorem ext_on_subset {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (A : Finset V) (K : Nat) (hsmall : Small G A K)
    (v : V) (hvA : v ∈ A) (d minSz : Nat)
    (hdegv : (A.filter (G.Adj v)).card = d)
    (hminN : ∀ u ∈ A.filter (G.Adj v), minSz + 1 ≤ (A.filter (G.Adj u)).card)
    (vsB : List V) (hvsB_nd : vsB.Nodup) (hvsB_cov : vsB.toFinset = A \ insert v (A.filter (G.Adj v)))
    (target : List Nat) (hvsB_enc : encode G vsB = target) :
    ∃ (front : List V) (cs : List Nat),
      (v :: front ++ vsB).Nodup ∧ (v :: front ++ vsB).toFinset = A ∧
      encode G (v :: front ++ vsB) = attach cs target ∧
      cs.length = d ∧
      (∀ x ∈ cs, ∃ p ∈ inds target, p.1 = x ∧ minSz ≤ p.2 ∧ p.2 < K - 1) ∧
      okContacts K (inds target) cs = true ∧
      cs.Pairwise (· ≤ ·) ∧
      edges_ (attach cs target) = edges_ target + d + (cs.map (countBits target.length)).sum := by
  classical
  let N := A.filter (G.Adj v)
  let B := A \ insert v N
  obtain ⟨front, hfn, hfcov, hfsort⟩ := sorted_neigh G N vsB
  let cs := contactsOf G vsB front
  have hfl : front.length = d := by
    rw [← List.toFinset_card_of_nodup hfn, hfcov]; exact hdegv
  have ha (u : V) (hu : u ∈ front) : G.Adj v u :=
    (Finset.mem_filter.mp (hfcov ▸ List.mem_toFinset.mpr hu)).2
  have hnot (y : V) (hy : y ∈ vsB) : ¬ G.Adj v y := by
    have hmem := Finset.mem_sdiff.mp (hvsB_cov ▸ List.mem_toFinset.mpr hy)
    exact fun hadj => hmem.2 (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hmem.1, hadj⟩))
  have hv_notB : v ∉ B := by simp [B]
  have hv_notN : v ∉ N := by simp [N]
  have hnd : (v :: front ++ vsB).Nodup := by
    rw [List.cons_append]
    apply List.nodup_cons.mpr
    refine ⟨?_, List.nodup_append.mpr ⟨hfn, hvsB_nd, fun x hx y hy e => hnot y hy (e ▸ ha x hx)⟩⟩
    rw [List.mem_append, not_or]
    exact ⟨fun h => hv_notN (hfcov ▸ List.mem_toFinset.mpr h),
           fun h => hv_notB (show v ∈ A \ insert v (A.filter (G.Adj v)) from hvsB_cov ▸ List.mem_toFinset.mpr h)⟩
  have hcov : (v :: front ++ vsB).toFinset = A := by
    ext x
    rw [List.cons_append]
    simp only [List.toFinset_cons, List.toFinset_append, hfcov, hvsB_cov,
      Finset.mem_insert, Finset.mem_union, Finset.mem_sdiff, B]
    have h1 : x = v → x ∈ A := fun h => h ▸ hvA
    have h2 : x ∈ N → x ∈ A := fun h => (Finset.mem_filter.mp h).1
    grind
  have hNind : ∀ x ∈ front, ∀ y ∈ front, ¬ G.Adj x y := fun x hx y hy hxy =>
    G.isIndepSet_neighborSet_of_triangleFree ht v (ha x hx) (ha y hy) hxy.ne hxy
  have henc : encode G (v :: front ++ vsB) = attach cs target := by
    rw [← hvsB_enc]
    exact root_encoding G v front vsB ha hnot ht
  have hdeg_split (u : V) (hu : u ∈ N) : (B.filter (G.Adj u)).card + 1 = (A.filter (G.Adj u)).card := by
    have hvu : G.Adj v u := (Finset.mem_filter.mp hu).2
    have heq : A.filter (G.Adj u) = insert v (B.filter (G.Adj u)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_sdiff, B]
      constructor
      · rintro ⟨hxA, hux⟩
        by_cases hxv : x = v
        · exact Or.inl hxv
        · refine Or.inr ⟨⟨hxA, ?_⟩, hux⟩
          simp only [Finset.mem_insert, hxv, false_or, N, Finset.mem_filter]
          rintro ⟨_, hvx⟩
          exact G.isIndepSet_neighborSet_of_triangleFree ht v hvu hvx hux.ne hux
      · rintro (rfl | ⟨⟨hxA, _⟩, hux⟩)
        · exact ⟨hvA, hvu.symm⟩
        · exact ⟨hxA, hux⟩
    have hv_not : v ∉ B.filter (G.Adj u) := fun h => hv_notB (Finset.mem_filter.mp h).1
    rw [heq, Finset.card_insert_of_notMem hv_not]
  have hmem : ∀ x ∈ cs, ∃ p ∈ inds target, p.1 = x ∧ minSz ≤ p.2 ∧ p.2 < K - 1 := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
    have huN : u ∈ N := hfcov ▸ List.mem_toFinset.mpr hu
    let S := vsB.toFinset.filter (G.Adj u)
    have hrow := inds_complete G vsB hvsB_nd S (Finset.filter_subset ..) (neighbors_small G ht _ u)
    rw [hvsB_enc] at hrow
    have hScard : S.card + 1 = (A.filter (G.Adj u)).card := by
      simpa [S, hvsB_cov] using hdeg_split u huN
    have hltK := hsmall (A.filter (G.Adj u)) (Finset.filter_subset ..) (neighbors_small G ht A u)
    have hminu := hminN u huN
    refine ⟨(mark vsB S, S.card), hrow, (row_mark G vsB u).symm, by omega, by omega⟩
  have hok : okContacts K (inds target) cs = true := by
    have hnd_app : (front ++ vsB).Nodup := (List.nodup_cons.mp (List.cons_append .. ▸ hnd)).2
    have hsub_app : (front ++ vsB).toFinset ⊆ A := by
      intro x hx
      rw [← hcov, List.cons_append, List.toFinset_cons]
      exact Finset.mem_insert_of_mem hx
    have hNcl : Gᶜ.IsClique (front.toFinset : Set V) := by
      intro x hx y hy hne
      exact ⟨hne, hNind x (List.mem_toFinset.mp hx) y (List.mem_toFinset.mp hy)⟩
    have h := ok_contacts G A K hsmall front vsB hnd_app hsub_app hNcl
    rwa [hvsB_enc] at h
  have hedges : edges_ (attach cs target) = edges_ target + d + (cs.map (countBits target.length)).sum := by
    rw [edges_attached, show cs.length = d by simp [cs, contactsOf, hfl]]
    omega
  exact ⟨front, cs, hnd, hcov, henc, by simp [cs, contactsOf, hfl], hmem, hok, hfsort, hedges⟩

private def missMask (top : List Nat) (x : Nat) : Nat :=
  bits (top.map (fun I => decide (x &&& I == 0)))

private theorem land_two_mul_add (a b : Nat) (b1 b2 : Bool) :
    (2 * a + b1.toNat) &&& (2 * b + b2.toNat) = 2 * (a &&& b) + (b1 && b2).toNat := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  cases i with
  | zero =>
    simp only [Nat.testBit_zero]
    cases b1 <;> cases b2 <;> simp <;> omega
  | succ i =>
    simp only [Nat.testBit_succ]
    have h1 : (2 * a + b1.toNat) / 2 = a := by cases b1 <;> simp <;> omega
    have h2 : (2 * b + b2.toNat) / 2 = b := by cases b2 <;> simp <;> omega
    have h3 : (2 * (a &&& b) + (b1 && b2).toNat) / 2 = a &&& b := by cases b1 <;> cases b2 <;> simp <;> omega
    rw [h1, h2, h3, Nat.testBit_and]

private theorem missMask_and_ne_zero : ∀ (top : List Nat) (x y : Nat),
    missMask top x &&& missMask top y ≠ 0 →
    ∃ I ∈ top, x &&& I = 0 ∧ y &&& I = 0
  | [], _, _, h => by simp [missMask, bits] at h
  | I :: rest, x, y, h => by
    simp only [missMask, List.map_cons, bits, land_two_mul_add] at h
    by_cases h1 : (decide (x &&& I == 0) && decide (y &&& I == 0)) = true
    · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1
      exact ⟨I, .head _, h1.1, h1.2⟩
    · have h0 : (decide (x &&& I == 0) && decide (y &&& I == 0)).toNat = 0 := by
        cases hc : (decide (x &&& I == 0) && decide (y &&& I == 0))
        · rfl
        · exact absurd hc h1
      rw [h0, Nat.add_zero] at h
      have hne : missMask rest x &&& missMask rest y ≠ 0 := by
        intro heq
        unfold missMask at heq
        rw [heq] at h
        exact h (Nat.mul_zero 2)
      obtain ⟨J, hJ, hx, hy⟩ := missMask_and_ne_zero rest x y hne
      exact ⟨J, .tail _ hJ, hx, hy⟩

private theorem missMask_ok_disj (K : Nat) (allInds topInds : List (Nat × Nat))
    (htop : ∀ p ∈ topInds, p ∈ allInds ∧ K - 2 ≤ p.2)
    (acc : List Nat) (x y : Nat) (xs : List Nat) (hy : y ∈ xs)
    (hok : okContacts K allInds (acc.reverse ++ (x :: xs)) = true) :
    missMask (topInds.map Prod.fst) y &&& missMask (topInds.map Prod.fst) x = 0 := by
  by_contra hne
  obtain ⟨I, hI_mem, hyI, hxI⟩ := missMask_and_ne_zero (topInds.map Prod.fst) y x hne
  obtain ⟨p, hp_top, rfl⟩ := List.mem_map.mp hI_mem
  obtain ⟨hp_all, hp_sz⟩ := htop p hp_top
  have hfull := of_decide_eq_true (List.all_eq_true.mp hok p hp_all)
  have hsub1 : [y].Sublist xs := List.singleton_sublist.mpr hy
  have hsub2 : [x, y].Sublist (x :: xs) := List.Sublist.cons_cons x hsub1
  have hsub3 : [x, y].Sublist (acc.reverse ++ (x :: xs)) :=
    hsub2.trans (List.sublist_append_right acc.reverse (x :: xs))
  have hle := (hsub3.filter (fun z => z &&& p.1 == 0)).length_le
  simp only [List.filter, hxI, hyI, beq_self_eq_true, List.length_cons, List.length_nil] at hle
  omega

private def enumGenItemsLoop (minSz d budget : Nat) (acc : List Nat)
    (step : Nat → List (Nat × Nat × Nat) → List Nat → List (List Nat)) :
    List (Nat × Nat × Nat) → List (List Nat)
  | [] => []
  | q :: rest =>
    let withQ :=
      if q.2.1 + d * minSz ≤ budget then
        let nxt := if d == 0 then [] else (q :: rest).filter (fun r => r.2.2 &&& q.2.2 == 0)
        step (budget - q.2.1) nxt (q.1 :: acc)
      else []
    withQ ++ enumGenItemsLoop minSz d budget acc step rest

private def enumGenItems (K : Nat) (allInds : List (Nat × Nat)) (minSz : Nat) :
    Nat → Nat → List (Nat × Nat × Nat) → List Nat → List (List Nat)
  | 0, _, _, acc =>
    let cs := acc.reverse
    if okContacts K allInds cs then [cs] else []
  | d + 1, budget, items, acc =>
    enumGenItemsLoop minSz d budget acc (enumGenItems K allInds minSz d) items

private def enumGenAux (K n : Nat) (allInds topInds : List (Nat × Nat))
    (minSz d budget : Nat) (pool acc : List Nat) : List (List Nat) :=
  let top := topInds.map Prod.fst
  let items := pool.map (fun c => (c, countBits n c, missMask top c))
  enumGenItems K allInds minSz d budget items acc

private theorem enumGenItems_complete (K n : Nat) (allInds topInds : List (Nat × Nat))
    (htop : ∀ p ∈ topInds, p ∈ allInds ∧ K - 2 ≤ p.2) (minSz : Nat) :
    ∀ (d budget : Nat) (items : List (Nat × Nat × Nat)) (acc suf : List Nat),
      (∀ q ∈ items, q.2.1 = countBits n q.1 ∧ q.2.2 = missMask (topInds.map Prod.fst) q.1) →
      items.Pairwise (fun a b => a.1 < b.1) →
      suf.length = d →
      (∀ x ∈ suf, (∃ q ∈ items, q.1 = x) ∧ minSz ≤ countBits n x) →
      suf.Pairwise (· ≤ ·) →
      (suf.map (countBits n)).sum ≤ budget →
      okContacts K allInds (acc.reverse ++ suf) = true →
      (acc.reverse ++ suf) ∈ enumGenItems K allInds minSz d budget items acc := by
  intro d
  induction d with
  | zero =>
    intro budget items acc suf _ _ hlen _ _ _ hok
    cases suf with
    | nil =>
      simp only [List.append_nil] at hok ⊢
      simp [enumGenItems, hok]
    | cons _ _ => simp at hlen
  | succ d ihd =>
    intro budget items
    induction items with
    | nil =>
      intro acc suf _ _ hlen hmem _ _ _
      cases suf with
      | nil => simp at hlen
      | cons x _ => obtain ⟨⟨q, hq, _⟩, _⟩ := hmem x (.head _); cases hq
    | cons q rest ihpool =>
      intro acc suf hitems hpw hlen hmem hsort hsum hok
      cases suf with
      | nil => simp at hlen
      | cons x xs =>
        have hq_prop := hitems q (.head _)
        have hpw_lt : ∀ r ∈ rest, q.1 < r.1 := (List.pairwise_cons.mp hpw).1
        have hpw_rest : rest.Pairwise (fun a b => a.1 < b.1) := (List.pairwise_cons.mp hpw).2
        obtain ⟨⟨r, hr_mem, hrx⟩, _⟩ := hmem x (.head _)
        rcases List.mem_cons.mp hr_mem with hrq | hr_rest
        · rw [hrq] at hrx; subst hrx
          have hxs_len : xs.length = d := by simp at hlen; omega
          have hxs_ge : d * minSz ≤ (xs.map (countBits n)).sum := by
            have aux : ∀ l : List Nat, (∀ y ∈ l, minSz ≤ countBits n y) → l.length * minSz ≤ (l.map (countBits n)).sum := by
              intro l hl
              induction l with
              | nil => simp
              | cons a as iha =>
                have h1 := hl a (.head _)
                have h2 := iha (fun y hy => hl y (.tail _ hy))
                simp only [List.length_cons, Nat.succ_mul, List.map_cons, List.sum_cons]
                omega
            rw [← hxs_len]
            exact aux xs (fun y hy => (hmem y (.tail _ hy)).2)
          simp only [List.map_cons, List.sum_cons] at hsum
          have hbud1 : q.2.1 + d * minSz ≤ budget := by rw [hq_prop.1]; omega
          have hbud2 : (xs.map (countBits n)).sum ≤ budget - q.2.1 := by rw [hq_prop.1]; omega
          let nxt := if d == 0 then [] else (q :: rest).filter (fun r => r.2.2 &&& q.2.2 == 0)
          have hnxt_items : ∀ u ∈ nxt, u.2.1 = countBits n u.1 ∧ u.2.2 = missMask (topInds.map Prod.fst) u.1 := by
            intro u hu
            cases d with
            | zero => simp [nxt] at hu
            | succ d' =>
              simp only [nxt, Nat.succ_ne_zero, beq_iff_eq, ite_false, List.mem_filter] at hu
              exact hitems u hu.1
          have hnxt_pw : nxt.Pairwise (fun a b => a.1 < b.1) := by
            cases d with
            | zero => simp [nxt]
            | succ d' =>
              simp only [nxt, Nat.succ_ne_zero, beq_iff_eq, ite_false]
              exact hpw.sublist List.filter_sublist
          have hnxt_mem : ∀ y ∈ xs, (∃ u ∈ nxt, u.1 = y) ∧ minSz ≤ countBits n y := by
            intro y hy
            obtain ⟨⟨u, hu, rfl⟩, hy_sz⟩ := hmem y (.tail _ hy)
            refine ⟨⟨u, ?_, rfl⟩, hy_sz⟩
            cases d with
            | zero => cases xs with | nil => cases hy | cons _ _ => simp at hxs_len
            | succ d' =>
              simp only [nxt, Nat.succ_ne_zero, beq_iff_eq, ite_false, List.mem_filter, beq_iff_eq]
              refine ⟨hu, ?_⟩
              rw [(hitems u hu).2, hq_prop.2]
              exact missMask_ok_disj K allInds topInds htop acc q.1 u.1 xs hy hok
          have hrec := ihd (budget - q.2.1) nxt (q.1 :: acc) xs hnxt_items hnxt_pw hxs_len hnxt_mem
            (List.pairwise_cons.mp hsort).2 hbud2
            (by simpa [List.reverse_cons, List.append_assoc] using hok)
          simp only [enumGenItems, enumGenItemsLoop, hbud1, ite_true, List.mem_append]
          exact Or.inl (by simpa [nxt, List.reverse_cons, List.append_assoc] using hrec)
        · have hqx : q.1 < x := hrx ▸ hpw_lt r hr_rest
          have hmem_rest : ∀ y ∈ x :: xs, (∃ u ∈ rest, u.1 = y) ∧ minSz ≤ countBits n y := by
            intro y hy
            obtain ⟨⟨u, hu, rfl⟩, hy_sz⟩ := hmem y hy
            refine ⟨?_, hy_sz⟩
            rcases List.mem_cons.mp hu with huq | hur
            · rcases List.mem_cons.mp hy with hxy | hys
              · rw [huq] at hxy; omega
              · have := (List.pairwise_cons.mp hsort).1 u.1 hys; rw [huq] at this; omega
            · exact ⟨u, hur, rfl⟩
          have hrec := ihpool acc (x :: xs) (fun u hu => hitems u (.tail _ hu)) hpw_rest hlen hmem_rest hsort hsum hok
          simp only [enumGenItems, enumGenItemsLoop, List.mem_append]
          exact Or.inr hrec

private theorem enumGenAux_complete (K n : Nat) (allInds topInds : List (Nat × Nat))
    (htop : ∀ p ∈ topInds, p ∈ allInds ∧ K - 2 ≤ p.2) (minSz : Nat) :
    ∀ (d budget : Nat) (pool acc suf : List Nat),
      suf.length = d →
      (∀ x ∈ suf, x ∈ pool ∧ minSz ≤ countBits n x) →
      suf.Pairwise (· ≤ ·) →
      pool.Pairwise (· < ·) →
      (suf.map (countBits n)).sum ≤ budget →
      okContacts K allInds (acc.reverse ++ suf) = true →
      (acc.reverse ++ suf) ∈ enumGenAux K n allInds topInds minSz d budget pool acc := by
  intro d budget pool acc suf hlen hmem hsort hpool hsum hok
  unfold enumGenAux
  refine enumGenItems_complete K n allInds topInds htop minSz d budget _ acc suf ?_ ?_ hlen ?_ hsort hsum hok
  · intro q hq
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hq
    exact ⟨rfl, rfl⟩
  · exact List.pairwise_map.mpr (hpool.imp fun h => h)
  · intro x hx
    obtain ⟨hx_in, hx_sz⟩ := hmem x hx
    exact ⟨⟨(x, countBits n x, missMask (topInds.map Prod.fst) x), List.mem_map.mpr ⟨x, hx_in, rfl⟩, rfl⟩, hx_sz⟩

/- ### Degree-capped enumerator for 4-regular (3,6;16) graphs -/

private theorem bump_mono (m : Nat) : ∀ l₁ l₂ : List Nat, List.Forall₂ (· ≤ ·) l₁ l₂ →
    List.Forall₂ (· ≤ ·) (bump m l₁) (bump m l₂)
  | _, _, .nil => .nil
  | _ :: as, _ :: bs, .cons h1 h2 => by
    simp only [bump]
    exact .cons (by omega) (bump_mono (m / 2) as bs h2)

private theorem bump_le_self (m : Nat) : ∀ l : List Nat, List.Forall₂ (· ≤ ·) l (bump m l)
  | [] => .nil
  | _ :: as => by
    simp only [bump]
    exact .cons (by omega) (bump_le_self (m / 2) as)

private theorem foldl_bump_mono (ms : List Nat) : ∀ l₁ l₂ : List Nat, List.Forall₂ (· ≤ ·) l₁ l₂ →
    List.Forall₂ (· ≤ ·) (ms.foldl (fun d m => bump m d) l₁) (ms.foldl (fun d m => bump m d) l₂) := by
  induction ms with
  | nil => intro _ _ h; exact h
  | cons m ms ih => intro l₁ l₂ h; exact ih _ _ (bump_mono m l₁ l₂ h)

private theorem forall2_le_trans {l₁ l₂ l₃ : List Nat}
    (h1 : List.Forall₂ (· ≤ ·) l₁ l₂) (h2 : List.Forall₂ (· ≤ ·) l₂ l₃) :
    List.Forall₂ (· ≤ ·) l₁ l₃ := by
  induction h1 generalizing l₃ with
  | nil => cases h2; exact .nil
  | cons hab _ ih => cases h2 with | cons hbc h2' => exact .cons (Nat.le_trans hab hbc) (ih h2')

private theorem foldl_bump_le (ms : List Nat) (l : List Nat) :
    List.Forall₂ (· ≤ ·) l (ms.foldl (fun d m => bump m d) l) := by
  induction ms generalizing l with
  | nil =>
    induction l with
    | nil => exact .nil
    | cons _ as ih => exact .cons (Nat.le_refl _) ih
  | cons m ms ih =>
    have h1 := bump_le_self m l
    exact forall2_le_trans h1 (ih (bump m l))

private theorem bump_comm (m₁ m₂ : Nat) : ∀ l : List Nat, bump m₁ (bump m₂ l) = bump m₂ (bump m₁ l)
  | [] => rfl
  | _ :: as => by
    simp only [bump, List.cons.injEq]
    exact ⟨by omega, bump_comm (m₁ / 2) (m₂ / 2) as⟩

private theorem foldl_bump_perm {l₁ l₂ : List Nat} (hp : l₁.Perm l₂) (init : List Nat) :
    l₁.foldl (fun d m => bump m d) init = l₂.foldl (fun d m => bump m d) init := by
  induction hp generalizing init with
  | nil => rfl
  | cons _ _ ih => exact ih _
  | swap _ _ _ => simp only [List.foldl_cons, bump_comm]
  | trans _ _ ih1 ih2 => exact (ih1 init).trans (ih2 init)

private theorem bump_pow_append (c : Nat) : ∀ (l₁ l₂ : List Nat),
    bump (2 ^ l₁.length * c) (l₁ ++ l₂) = l₁ ++ bump c l₂
  | [], l₂ => by simp
  | a :: l₁, l₂ => by
    simp only [List.length_cons, pow_succ, List.cons_append, bump, List.cons.injEq]
    have h0 : 2 ^ l₁.length * 2 * c = 2 * (2 ^ l₁.length * c) := by ring
    rw [h0, Nat.mul_mod_right, Nat.mul_div_right _ (by decide : 0 < 2), Nat.add_zero]
    exact ⟨rfl, bump_pow_append c l₁ l₂⟩

private theorem bump_ones_append : ∀ (l₁ l₂ : List Nat),
    bump (2 ^ l₁.length - 1) (l₁ ++ l₂) = l₁.map (· + 1) ++ l₂
  | [], l₂ => by simp [bump]; induction l₂ with | nil => rfl | cons _ _ ih => simp [bump, ih]
  | a :: l₁, l₂ => by
    have hpos : 1 ≤ 2 ^ l₁.length := Nat.one_le_two_pow
    simp only [List.length_cons, pow_succ, List.cons_append, bump, List.map_cons, List.cons.injEq]
    have h1 : (2 ^ l₁.length * 2 - 1) % 2 = 1 := by omega
    have h2 : (2 ^ l₁.length * 2 - 1) / 2 = 2 ^ l₁.length - 1 := by omega
    rw [h1, h2]
    exact ⟨rfl, bump_ones_append l₁ l₂⟩

private theorem degrees_shifted_drop (cs base : List Nat) :
    (degrees (shifted cs ++ base)).drop cs.length =
    cs.foldl (fun d m => bump m d) (degrees base) := by
  induction cs generalizing base with
  | nil => simp [shifted]
  | cons c cs ih =>
    simp only [shifted, List.cons_append, degrees, List.length_cons, List.drop_succ_cons]
    have hlen : ((degrees (shifted cs ++ base)).take cs.length).length = cs.length := by
      rw [List.length_take, degrees_length, List.length_append, shifted_length]
      omega
    generalize hds : degrees (shifted cs ++ base) = ds at hlen ⊢
    have hb := bump_pow_append c (ds.take cs.length) (ds.drop cs.length)
    rw [hlen, List.take_append_drop] at hb
    rw [hb, List.drop_left' hlen, ← hds, ih base]
    rw [foldl_bump_perm (List.perm_append_singleton c cs).symm]
    simp [List.foldl_append]

private theorem degrees_attach_drop (cs base : List Nat) :
    (degrees (attach cs base)).drop (cs.length + 1) =
    cs.foldl (fun d m => bump m d) (degrees base) := by
  unfold attach
  simp only [degrees, List.drop_succ_cons]
  have hlen : ((degrees (shifted cs ++ base)).take cs.length).length = cs.length := by
    rw [List.length_take, degrees_length, List.length_append, shifted_length]
    omega
  generalize hds : degrees (shifted cs ++ base) = ds at hlen ⊢
  have hb := bump_ones_append (ds.take cs.length) (ds.drop cs.length)
  rw [hlen, List.take_append_drop] at hb
  have hmlen : ((ds.take cs.length).map (· + 1)).length = cs.length := by rw [List.length_map, hlen]
  rw [hb, List.drop_left' hmlen, ← hds, degrees_shifted_drop]

private def enum4RegItemsLoop (d : Nat) (acc curDeg : List Nat)
    (step : List (Nat × Nat) → List Nat → List Nat → List (List Nat)) :
    List (Nat × Nat) → List (List Nat)
  | [] => []
  | q :: rest =>
    let nxtDeg := bump q.1 curDeg
    let withQ :=
      if nxtDeg.all (fun x => decide (x ≤ 4)) then
        let nxt := if d == 0 then [] else (q :: rest).filter (fun r => r.2 &&& q.2 == 0)
        step nxt (q.1 :: acc) nxtDeg
      else []
    withQ ++ enum4RegItemsLoop d acc curDeg step rest

private def enum4RegItems (allInds : List (Nat × Nat)) (base : List Nat) :
    Nat → List (Nat × Nat) → List Nat → List Nat → List (List Nat)
  | 0, _, acc, curDeg =>
    let cs := acc.reverse
    if okContacts 6 allInds cs && decide (curDeg = List.replicate 11 4) then [cs] else []
  | d + 1, items, acc, curDeg =>
    enum4RegItemsLoop d acc curDeg (enum4RegItems allInds base d) items

private def enum4RegAux (allInds topInds : List (Nat × Nat)) (base : List Nat)
    (d : Nat) (pool acc curDeg : List Nat) : List (List Nat) :=
  let top := topInds.map Prod.fst
  let items := pool.map (fun c => (c, missMask top c))
  enum4RegItems allInds base d items acc curDeg

private theorem forall2_le_all_le {l₁ l₂ : List Nat} (h : List.Forall₂ (· ≤ ·) l₁ l₂)
    (h2 : l₂.all (fun x => decide (x ≤ 4)) = true) :
    l₁.all (fun x => decide (x ≤ 4)) = true := by
  induction h with
  | nil => rfl
  | cons hab _ ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h2 ⊢
    exact ⟨Nat.le_trans hab h2.1, ih h2.2⟩

private theorem enum4RegItems_complete (allInds topInds : List (Nat × Nat))
    (htop : ∀ p ∈ topInds, p ∈ allInds ∧ 4 ≤ p.2) (base : List Nat) :
    ∀ (d : Nat) (items : List (Nat × Nat)) (acc curDeg suf : List Nat),
      (∀ q ∈ items, q.2 = missMask (topInds.map Prod.fst) q.1) →
      items.Pairwise (fun a b => a.1 < b.1) →
      curDeg = acc.reverse.foldl (fun dg m => bump m dg) (degrees base) →
      suf.length = d →
      (∀ x ∈ suf, ∃ q ∈ items, q.1 = x) →
      suf.Pairwise (· ≤ ·) →
      okContacts 6 allInds (acc.reverse ++ suf) = true →
      (acc.reverse ++ suf).foldl (fun dg m => bump m dg) (degrees base) = List.replicate 11 4 →
      (acc.reverse ++ suf) ∈ enum4RegItems allInds base d items acc curDeg := by
  intro d
  induction d with
  | zero =>
    intro items acc curDeg suf _ _ hcur hlen _ _ hok hreg
    cases suf with
    | nil =>
      simp only [List.append_nil] at hok hreg ⊢
      rw [← hcur] at hreg
      simp [enum4RegItems, hok, hreg]
    | cons _ _ => simp at hlen
  | succ d ihd =>
    intro items
    induction items with
    | nil =>
      intro acc curDeg suf _ _ _ hlen hmem _ _ _
      cases suf with
      | nil => simp at hlen
      | cons x _ => obtain ⟨q, hq, _⟩ := hmem x (.head _); cases hq
    | cons q rest ihpool =>
      intro acc curDeg suf hitems hpw hcur hlen hmem hsort hok hreg
      cases suf with
      | nil => simp at hlen
      | cons x xs =>
        have hq_prop := hitems q (.head _)
        have hpw_lt : ∀ r ∈ rest, q.1 < r.1 := (List.pairwise_cons.mp hpw).1
        have hpw_rest : rest.Pairwise (fun a b => a.1 < b.1) := (List.pairwise_cons.mp hpw).2
        obtain ⟨r, hr_mem, hrx⟩ := hmem x (.head _)
        rcases List.mem_cons.mp hr_mem with hrq | hr_rest
        · rw [hrq] at hrx; subst hrx
          have hxs_len : xs.length = d := by simp at hlen; omega
          have hnxt_deg : bump q.1 curDeg = (q.1 :: acc).reverse.foldl (fun dg m => bump m dg) (degrees base) := by
            rw [hcur, List.reverse_cons, List.foldl_append]; rfl
          have hdeg_le : List.Forall₂ (· ≤ ·) (bump q.1 curDeg) (List.replicate 11 4) := by
            rw [hnxt_deg, ← hreg]
            have hstep : (acc.reverse ++ (q.1 :: xs)).foldl (fun dg m => bump m dg) (degrees base) =
                xs.foldl (fun dg m => bump m dg) ((q.1 :: acc).reverse.foldl (fun dg m => bump m dg) (degrees base)) := by
              simp [List.reverse_cons, List.foldl_append]
            rw [hstep]
            exact foldl_bump_le xs _
          have hcap_ok : (bump q.1 curDeg).all (fun z => decide (z ≤ 4)) = true :=
            forall2_le_all_le hdeg_le (by decide)
          let nxt := if d == 0 then [] else (q :: rest).filter (fun r => r.2 &&& q.2 == 0)
          have hnxt_items : ∀ u ∈ nxt, u.2 = missMask (topInds.map Prod.fst) u.1 := by
            intro u hu
            cases d with
            | zero => simp [nxt] at hu
            | succ d' =>
              simp only [nxt, Nat.succ_ne_zero, beq_iff_eq, ite_false, List.mem_filter] at hu
              exact hitems u hu.1
          have hnxt_pw : nxt.Pairwise (fun a b => a.1 < b.1) := by
            cases d with
            | zero => simp [nxt]
            | succ d' =>
              simp only [nxt, Nat.succ_ne_zero, beq_iff_eq, ite_false]
              exact hpw.sublist List.filter_sublist
          have hnxt_mem : ∀ y ∈ xs, ∃ u ∈ nxt, u.1 = y := by
            intro y hy
            obtain ⟨u, hu, rfl⟩ := hmem y (.tail _ hy)
            refine ⟨u, ?_, rfl⟩
            cases d with
            | zero => cases xs with | nil => cases hy | cons _ _ => simp at hxs_len
            | succ d' =>
              simp only [nxt, Nat.succ_ne_zero, beq_iff_eq, ite_false, List.mem_filter, beq_iff_eq]
              refine ⟨hu, ?_⟩
              rw [hitems u hu, hq_prop]
              exact missMask_ok_disj 6 allInds topInds htop acc q.1 u.1 xs hy hok
          have hrec := ihd nxt (q.1 :: acc) (bump q.1 curDeg) xs hnxt_items hnxt_pw hnxt_deg hxs_len hnxt_mem
            (List.pairwise_cons.mp hsort).2
            (by simpa [List.reverse_cons, List.append_assoc] using hok)
            (by simpa [List.reverse_cons, List.append_assoc] using hreg)
          simp only [enum4RegItems, enum4RegItemsLoop, hcap_ok, ite_true, List.mem_append]
          exact Or.inl (by simpa [nxt, List.reverse_cons, List.append_assoc] using hrec)
        · have hqx : q.1 < x := hrx ▸ hpw_lt r hr_rest
          have hmem_rest : ∀ y ∈ x :: xs, ∃ u ∈ rest, u.1 = y := by
            intro y hy
            obtain ⟨u, hu, rfl⟩ := hmem y hy
            rcases List.mem_cons.mp hu with huq | hur
            · rcases List.mem_cons.mp hy with hxy | hys
              · rw [huq] at hxy; omega
              · have := (List.pairwise_cons.mp hsort).1 u.1 hys; rw [huq] at this; omega
            · exact ⟨u, hur, rfl⟩
          have hrec := ihpool acc curDeg (x :: xs) (fun u hu => hitems u (.tail _ hu)) hpw_rest hcur hlen hmem_rest hsort hok hreg
          simp only [enum4RegItems, enum4RegItemsLoop, List.mem_append]
          exact Or.inr hrec

private theorem enum4RegAux_complete (allInds topInds : List (Nat × Nat))
    (htop : ∀ p ∈ topInds, p ∈ allInds ∧ 4 ≤ p.2) (base : List Nat) :
    ∀ (d : Nat) (pool acc curDeg suf : List Nat),
      curDeg = acc.reverse.foldl (fun dg m => bump m dg) (degrees base) →
      suf.length = d →
      (∀ x ∈ suf, x ∈ pool) →
      suf.Pairwise (· ≤ ·) →
      pool.Pairwise (· < ·) →
      okContacts 6 allInds (acc.reverse ++ suf) = true →
      (acc.reverse ++ suf).foldl (fun dg m => bump m dg) (degrees base) = List.replicate 11 4 →
      (acc.reverse ++ suf) ∈ enum4RegAux allInds topInds base d pool acc curDeg := by
  intro d pool acc curDeg suf hcur hlen hmem hsort hpool hok hreg
  unfold enum4RegAux
  refine enum4RegItems_complete allInds topInds htop base d _ acc curDeg suf ?_ ?_ hcur hlen ?_ hsort hok hreg
  · intro q hq
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hq
    rfl
  · exact List.pairwise_map.mpr (hpool.imp fun h => h)
  · intro x hx
    exact ⟨(x, missMask (topInds.map Prod.fst) x), List.mem_map.mpr ⟨x, hmem x hx, rfl⟩, rfl⟩


/- ## 11-vertex (3,5,11) graphs with <= 16 edges (47 -> 7 representatives) -/

private def g11_0 : List Nat := [153,145,1,1,18,10,1,0,2,1,0]
private def g11_1 : List Nat := [25,145,33,33,2,2,1,0,2,1,0]
private def g11_2 : List Nat := [25,145,33,33,2,10,1,0,2,1,0]
private def g11_3 : List Nat := [153,145,33,1,2,10,1,0,2,1,0]
private def g11_4 : List Nat := [153,17,65,1,2,10,1,1,2,1,0]
private def g11_5 : List Nat := [153,17,1,1,2,10,5,1,2,1,0]
private def g11_6 : List Nat := [25,17,33,33,2,6,1,2,2,1,0]
private def g11Rep (i : Nat) : List Nat :=
  match i with
  | 0 => g11_0 | 1 => g11_1 | 2 => g11_2 | 3 => g11_3 | 4 => g11_4 | 5 => g11_5 | _ => g11_6
private def l11Map : List (List Nat × Nat × List Nat) := [
  ([3,128,144,3,2,6,3,2,2,1,0], 1, [4,1,5,3,2,0,6,5,4,3,1,7,6,5,4,2,8,7,6,5,3,9,8,7,6,5,4,1]),
  ([3,128,146,3,2,6,3,2,2,1,0], 2, [0,1,2,1,0,3,2,1,0,4,3,2,1,5,4,3,2,1,0,6,5,4,3,2,1,7,6,5,4,3,2,8,7,6,5,4,3,2,9,8,7,6,5,4,3]),
  ([3,128,145,3,2,6,3,2,2,1,0], 2, [0,1,2,1,0,3,2,1,4,3,2,1,5,4,3,2,0,6,5,4,3,2,1,7,6,5,4,3,2,8,7,6,5,4,3,2,9,8,7,6,5,4,3]),
  ([3,64,140,3,2,6,3,2,2,1,0], 0, [4,5,3,6,5,4,7,6,5,8,7,6,1,0,9,8,7,6,4,2,1,0]),
  ([3,192,128,3,2,6,3,2,2,1,0], 1, [4,5,3,2,0,6,5,4,3,1,7,6,5,4,2,8,7,6,5,3,9,8,7,6,4,2,1]),
  ([3,192,144,3,2,6,3,2,2,1,0], 5, [0,1,2,1,0,3,2,1,4,3,2,5,4,3,6,5,4,7,6,5,8,7,6,4,1,0,9,8,7,6,5,3,2,1,0]),
  ([3,192,136,3,2,6,3,2,2,1,0], 2, [0,4,1,0,5,3,2,1,0,6,5,4,3,2,1,7,6,5,4,3,2,8,7,6,5,4,3,1,0,9,8,7,6,5,4,3,2,1,0]),
  ([3,192,132,3,2,6,3,2,2,1,0], 2, [3,0,4,1,0,5,4,3,2,1,0,6,5,4,3,2,1,7,6,5,4,3,2,8,7,6,5,4,3,1,0,9,8,7,6,5,4,3,2,1,0]),
  ([3,192,130,3,2,6,3,2,2,1,0], 4, [3,4,3,5,4,3,6,5,4,7,6,5,4,1,0,8,7,6,5,3,2,1,0,9,8,7,6,5,4,3,2,1]),
  ([3,192,129,3,2,6,3,2,2,1,0], 4, [4,3,5,4,6,5,4,7,6,5,4,1,0,8,7,6,5,3,2,1,0,9,8,7,6,5,4,3,2,1]),
  ([3,32,76,3,2,6,3,2,2,1,0], 0, [4,5,3,6,5,4,7,6,5,8,7,6,1,0,9,8,7,2,1,0]),
  ([3,16,50,3,2,6,3,2,2,1,0], 0, [1,2,0,3,1,4,2,1,5,3,2,6,5,4,3,2,1,7,6,5,4,3,2,8,7,6,5,4,3,2,9,8,7,6,5,4,3]),
  ([3,144,144,3,2,6,3,2,2,1,0], 2, [0,4,1,5,3,2,1,0,6,5,4,3,2,1,7,6,5,4,3,2,8,7,6,5,4,3,0,9,8,7,6,5,4,2,1,0]),
  ([3,8,49,3,2,6,3,2,2,1,0], 0, [1,2,0,3,1,4,2,5,4,3,2,6,5,4,3,2,1,7,6,5,4,3,2,8,7,6,5,4,3,2,9,8,7,6,5,4,3]),
  ([3,136,144,3,2,6,3,2,2,1,0], 2, [3,0,4,1,5,4,3,2,1,0,6,5,4,3,2,1,7,6,5,4,3,2,8,7,6,5,4,3,0,9,8,7,6,5,4,2,1,0]),
  ([3,24,48,3,2,6,3,2,2,1,0], 0, [0,4,1,5,3,2,1,0,6,5,4,3,2,1,7,6,5,4,3,2,8,7,6,5,4,3,2,9,8,7,6,5,4,3]),
  ([3,4,9,3,2,6,3,2,2,1,0], 1, [1,2,0,3,1,4,3,2,5,4,3,6,5,4,7,6,5,8,7,6,2,1,0,9,8,7,5,3,2,1,0]),
  ([3,4,137,3,2,6,3,2,2,1,0], 2, [0,1,2,1,0,3,2,1,4,3,2,5,4,3,6,5,4,7,6,5,0,8,7,6,4,2,1,0,9,8,7,6,5,3,2,1,0]),
  ([3,4,73,3,2,6,3,2,2,1,0], 2, [0,1,2,1,0,3,2,1,4,3,2,5,4,3,6,5,4,7,6,5,0,8,7,6,2,1,0,9,8,7,5,3,2,1,0]),
  ([3,132,144,3,2,6,3,2,2,1,0], 4, [3,4,3,5,4,3,6,5,4,7,6,5,0,8,7,6,5,3,2,1,0,9,8,7,6,4,3,2,1]),
  ([3,132,129,3,2,6,3,2,2,1,0], 6, [0,1,2,1,0,3,2,1,4,3,2,5,4,3,6,5,4,7,6,5,0,8,7,6,2,1,0,9,8,7,5,3,2,1,0]),
  ([3,68,136,3,2,6,3,2,2,1,0], 3, [3,4,5,4,3,6,5,4,7,6,5,0,8,7,6,2,1,0,9,8,7,6,4,3,2,1]),
  ([3,196,128,3,2,6,3,2,2,1,0], 2, [0,1,0,2,1,0,3,2,1,0,4,3,2,1,5,4,3,2,1,0,6,5,4,3,2,1,7,6,5,4,3,2,1,8,7,6,5,4,3,2,9,8,7,6,5,4,3,2]),
  ([3,36,72,3,2,6,3,2,2,1,0], 3, [3,4,5,4,3,6,5,4,7,6,5,0,8,7,6,2,1,0,9,8,7,3,2,1]),
  ([3,12,129,3,2,6,3,2,2,1,0], 4, [1,0,4,2,1,0,9,7,6,5,3,2,1,0]),
  ([3,12,65,3,2,6,3,2,2,1,0], 4, [1,0,4,2,1,0,6,5,3,2,1,0]),
  ([3,12,33,3,2,6,3,2,2,1,0], 2, [0,1,0,2,1,0,3,2,1,4,3,2,1,5,4,3,2,8,6,5,4,3,2]),
  ([3,12,17,3,2,6,3,2,2,1,0], 2, [0,1,0,2,1,0,3,2,1,4,3,2,1,7,5,4,3,2,9,8,6,5,4,3,2]),
  ([3,12,9,3,2,6,3,2,2,1,0], 5, [0,1,2,1,0,3,2,1,4,3,2,1,5,4,3,2,0,6,5,4,3,2,1,7,6,5,4,3,2,8,7,6,5,4,3,2,9,8,7,6,5,4,3]),
  ([3,2,6,3,2,6,3,2,2,1,0], 1, [1,2,0,3,2,1,4,3,2,5,4,3,6,5,4,7,6,5,8,7,6,1,0,9,8,7,5,3,2,1,0]),
  ([3,2,134,3,2,6,3,2,2,1,0], 2, [0,1,2,1,0,3,2,1,4,3,2,5,4,3,6,5,4,7,6,5,8,7,6,4,1,0,9,8,7,6,5,3,2,1,0]),
  ([3,2,70,3,2,6,3,2,2,1,0], 2, [0,1,2,1,0,3,2,1,4,3,2,5,4,3,6,5,4,7,6,5,8,7,6,1,0,9,8,7,5,3,2,1,0]),
  ([3,130,144,3,2,6,3,2,2,1,0], 4, [4,3,5,4,6,5,4,7,6,5,0,8,7,6,5,3,2,1,0,9,8,7,6,4,3,2,1]),
  ([3,130,130,3,2,6,3,2,2,1,0], 6, [0,1,2,1,0,3,2,1,4,3,2,5,4,3,6,5,4,7,6,5,8,7,6,1,0,9,8,7,5,3,2,1,0]),
  ([3,66,132,3,2,6,3,2,2,1,0], 3, [4,5,3,6,5,4,7,6,5,0,8,7,6,2,1,0,9,8,7,6,4,3,2,1]),
  ([3,194,128,3,2,6,3,2,2,1,0], 2, [0,1,0,2,1,0,3,2,1,4,3,2,1,5,4,3,2,0,6,5,4,3,2,1,7,6,5,4,3,2,1,8,7,6,5,4,3,2,9,8,7,6,5,4,3,2]),
  ([3,34,68,3,2,6,3,2,2,1,0], 3, [4,5,3,6,5,4,7,6,5,0,8,7,6,2,1,0,9,8,7,3,2,1]),
  ([3,18,130,3,2,6,3,2,2,1,0], 4, [3,1,0,5,4,2,1,0,9,7,6,5,3,2,1,0]),
  ([3,18,66,3,2,6,3,2,2,1,0], 4, [3,1,0,5,4,2,1,0,6,5,3,2,1,0]),
  ([3,18,34,3,2,6,3,2,2,1,0], 2, [0,1,0,2,1,0,3,2,1,0,4,3,2,1,5,4,3,2,1,8,6,5,4,3,2]),
  ([3,18,18,3,2,6,3,2,2,1,0], 2, [0,1,0,2,1,0,3,2,1,0,4,3,2,1,7,5,4,3,2,1,9,8,6,5,4,3,2]),
  ([3,128,144,3,12,9,3,2,2,1,0], 2, [1,2,0,3,1,4,2,1,5,3,2,1,6,4,3,2,1,7,5,4,3,2,8,6,5,4,3,0,9,8,7,6,5,4,3,1]),
  ([3,64,136,3,12,9,3,2,2,1,0], 2, [1,2,0,3,1,4,2,1,5,3,2,6,4,3,2,1,7,5,4,3,2,8,7,6,5,4,3,0,9,8,7,6,5,4,3,1,0]),
  ([3,192,128,3,12,9,3,2,2,1,0], 5, [3,4,5,4,3,6,5,4,7,6,5,4,8,7,6,5,3,0,9,8,7,6,5,4,2,1,0]),
  ([3,8,9,3,12,9,3,2,2,1,0], 2, [1,2,0,3,1,4,2,5,4,3,6,5,4,7,6,5,8,7,6,2,1,0,9,8,7,5,3,2,1,0]),
  ([3,4,17,3,12,9,3,2,2,1,0], 2, [1,2,0,3,1,4,3,2,5,4,3,6,5,4,7,6,5,8,7,6,2,1,0,9,8,7,3,2,1]),
  ([3,2,6,3,12,9,3,2,2,1,0], 5, [1,0,6,5,3,2,1,0])
]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 40000000 in
private theorem l11_cover :
    ((levels normalized 5 11 4).filter (fun b => decide (edges_ b ≤ 16))).all
      (fun b => l11Map.any (fun e => decide (e.1 = b))) = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
private theorem l11_relabel_ok :
    l11Map.all (fun e => decide (e.2.1 < 7 ∧ relabel e.2.2 e.1 = g11Rep e.2.1)) = true := by
  decide +kernel

private theorem l11_to_rep {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (vs : List V) (hb : encode G vs ∈ levels normalized 5 11 4)
    (he : edges_ (encode G vs) ≤ 16) :
    ∃ r < 7, ∃ vs' : List V, vs'.Perm vs ∧ encode G vs' = g11Rep r := by
  have hmem : encode G vs ∈ (levels normalized 5 11 4).filter (fun b => decide (edges_ b ≤ 16)) :=
    List.mem_filter.mpr ⟨hb, decide_eq_true he⟩
  have hany := List.all_eq_true.mp l11_cover (encode G vs) hmem
  obtain ⟨e, he_in, he_eq⟩ := List.any_eq_true.mp hany
  have he1 : e.1 = encode G vs := of_decide_eq_true he_eq
  have hrel := of_decide_eq_true (List.all_eq_true.mp l11_relabel_ok e he_in)
  obtain ⟨vs', hperm, henc⟩ := relabel_real G e.2.2 vs
  rw [← he1, hrel.2] at henc
  exact ⟨e.2.1, hrel.1, vs', hperm, henc⟩


/- ## e(3,6;17) >= 40 via 12 zero-branching duals + b4_0 enum -/

private def pool17_b4_0 : List Nat := [14,44,76,97,100,104,108,134,138,140,142,145,146,193,196,200,204,262,273,274,289,292,518,522,524,526,529,530,545,548,552,556,769,770,772,774,784,785,786,800,801,804,1034,1041,1042,1057,1064,1089,1096,1120,1121,1128,1153,1154,1160,1162,1168,1169,1170,1216,1217,1224,1537,1538,1544,1546,1552,1553,1554,1568,1569,1576,2054,2065,2066,2081,2084,2113,2116,2144,2145,2148,2177,2178,2180,2182,2192,2193,2194,2240,2241,2244,2305,2306,2308,2310,2320,2321,2322,2336,2337,2340]
set_option maxRecDepth 24000 in set_option maxHeartbeats 25000000 in
private theorem enum17_b4_0_empty :
    enumGenAux 6 12 (inds b4_0) ((inds b4_0).filter (fun p => p.2 == 4)) 3 4 15 pool17_b4_0 [] = [] ∧
    pool17_b4_0.Pairwise (· < ·) ∧
    (inds b4_0).all (fun p => !(3 ≤ p.2 && p.2 < 5) || decide (p.1 ∈ pool17_b4_0)) = true := by
  decide +kernel

private def w17_40_b3_0 : List WeightedRow := [((2337,4),7),((4385,4),36),((1569,4),7),((4641,4),7),((3105,4),36),((2241,4),36),((4289,4),7),((1601,4),7),((4673,4),36),((3137,4),7),((2433,4),7),((4481,4),7),((30,4),36),((526,4),7),((278,4),7),((4358,4),7),((4614,4),36),((1050,4),7),((1546,4),7),((306,4),36),((1074,4),7),((4386,4),7),((1570,4),36),((4642,4),7),((156,4),7),((204,4),36),((588,4),7),((404,4),7),((4292,4),7),((4676,4),7),((4484,4),36),((2200,4),7),((3096,4),36),((2248,4),7),((1608,4),36),((3144,4),7),((2352,4),7),((3120,4),7),((2448,4),36)]
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert17_40_b3_0 : dualCheckGen 6 3 2 10 63 218 0 b3_0 w17_40_b3_0 = true := by decide +kernel
private def w17_40_b4_1 : List WeightedRow := [((1169,4),138),((785,4),105),((2321,4),115),((1553,4),61),((1121,4),166),((2145,4),38),((801,4),61),((2337,4),51),((2241,4),189),((526,4),189),((2310,4),199),((1162,4),143),((1546,4),56),((1170,4),46),((2194,4),199),((786,4),115),((1554,4),33),((108,4),135),((2148,4),143),((804,4),138),((2340,4),46),((1576,4),166),((1224,4),135),((76,3),92),((200,3),92),((260,2),38),((144,2),38),((272,2),61)]
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert17_40_b4_1 : dualCheckGen 6 4 3 14 304 1053 0 b4_1 w17_40_b4_1 = true := by decide +kernel
private def w17_40_b4_2 : List WeightedRow := [((1169,4),36),((2193,4),36),((2321,4),70),((1553,4),70),((1121,4),36),((2145,4),36),((801,4),70),((142,4),70),((2310,4),70),((1546,4),70),((1170,4),36),((2194,4),36),((786,4),105),((108,4),105),((2340,4),70),((2244,4),70),((1576,4),70),((1224,4),70)]
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert17_40_b4_2 : dualCheckGen 6 4 3 14 126 398 0 b4_2 w17_40_b4_2 = true := by decide +kernel
private def w17_40_b4_3 : List WeightedRow := [((1169,4),945),((785,4),630),((2321,4),504),((1121,4),1120),((2145,4),252),((801,4),252),((2241,4),840),((526,4),1080),((2310,4),1400),((2194,4),1080),((786,4),1080),((108,4),315),((2148,4),1080),((804,4),840),((1576,4),840),((1224,4),1080),((138,3),630),((76,3),630),((1168,3),315),((1552,3),315)]
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert17_40_b4_3 : dualCheckGen 6 4 3 13 2520 2726 0 b4_3 w17_40_b4_3 = true := by decide +kernel
private def w17_40_b4_4 : List WeightedRow := [((2193,4),3),((1553,4),3),((1121,4),3),((2337,4),3),((2310,4),3),((786,4),3),((108,4),3),((2244,4),3),((808,4),3),((14,3),3),((146,3),3),((1544,3),3),((1216,3),3)]
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert17_40_b4_4 : dualCheckGen 6 4 3 13 7 3 0 b4_4 w17_40_b4_4 = true := by decide +kernel
private def w17_40_b4_5 : List WeightedRow := [((785,4),855),((2321,4),171),((1553,4),855),((2145,4),760),((1185,4),855),((2209,4),171),((833,4),342),((2369,4),760),((1038,4),760),((1158,4),171),((2182,4),855),((778,4),342),((1546,4),760),((786,4),855),((2322,4),855),((1554,4),171),((108,4),1710),((1068,4),342),((2148,4),342),((1188,4),855),((2212,4),855),((840,4),1710),((164,3),540),((784,3),540),((144,2),760)]
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert17_40_b4_5 : dualCheckGen 6 4 3 13 3420 1015 0 b4_5 w17_40_b4_5 = true := by decide +kernel
private def w17_40_b4_6 : List WeightedRow := [((2193,4),17),((785,4),18),((1553,4),13),((2145,4),21),((1185,4),11),((833,4),1),((2369,4),3),((270,4),19),((1158,4),4),((106,4),8),((1066,4),9),((1186,4),12),((2210,4),12),((2370,4),17),((1548,4),22),((1172,4),14),((788,4),13),((840,4),11),((577,3),1),((134,3),4),((148,3),10),((104,3),14),((584,3),10),((2192,3),8),((2320,3),3)]
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert17_40_b4_6 : dualCheckGen 6 4 3 13 44 48 0 b4_6 w17_40_b4_6 = true := by decide +kernel
private def w17_40_b4_7 : List WeightedRow := [((2193,4),1),((785,4),1),((2321,4),1),((2145,4),1),((1158,4),1),((106,4),1),((2146,4),1),((1186,4),1),((2210,4),1),((780,4),1),((1548,4),1),((1172,4),1),((788,4),1),((840,4),1),((14,3),1),((2368,3),1)]
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert17_40_b4_7 : dualCheckGen 6 4 3 12 0 11 0 b4_7 w17_40_b4_7 = true := by decide +kernel
private def w17_40_b4_8 : List WeightedRow := [((2193,4),3),((2321,4),3),((1553,4),3),((2145,4),3),((1185,4),3),((833,4),3),((142,4),3),((270,4),3),((102,4),3),((2210,4),3),((2370,4),3),((1548,4),3),((1188,4),3),((836,4),3),((1176,4),3),((792,4),3)]
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert17_40_b4_8 : dualCheckGen 6 4 3 13 10 3 0 b4_8 w17_40_b4_8 = true := by decide +kernel
private def w17_40_b4_9 : List WeightedRow := [((2193,4),1),((1553,4),1),((2145,4),1),((2369,4),1),((106,4),1),((2210,4),1),((2370,4),1),((1548,4),1),((1172,4),1),((788,4),1),((840,4),1),((14,3),1),((1184,3),1)]
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert17_40_b4_9 : dualCheckGen 6 4 3 12 0 9 0 b4_9 w17_40_b4_9 = true := by decide +kernel
private def w17_40_b4_10 : List WeightedRow := [((1185,4),1),((2209,4),1),((801,4),1),((2337,4),1),((1569,4),1),((1217,4),1),((2241,4),1),((30,4),1),((270,4),1),((86,4),1),((2118,4),1),((2310,4),1),((538,4),1),((778,4),1),((212,4),1),((2244,4),1),((1560,4),1),((808,4),1),((1576,4),1),((1232,4),1)]
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert17_40_b4_10 : dualCheckGen 6 4 3 11 0 14 0 b4_10 w17_40_b4_10 = true := by decide +kernel
private def w17_40_b4_11 : List WeightedRow := [((2337,4),3),((1569,4),3),((2625,4),3),((1409,4),3),((30,4),3),((2118,4),3),((586,4),3),((2594,4),3),((204,4),3),((404,4),3),((1176,4),3),((1328,4),3),((193,3),1),((50,3),1),((2308,3),1),((1544,3),1)]
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert17_40_b4_11 : dualCheckGen 6 4 3 11 0 28 0 b4_11 w17_40_b4_11 = true := by decide +kernel

/- ## (3,6;14, <= 20) -> unique g14_20 -> d=6 dual obstruction -/

private def g14_20 : List Nat := [2073,145,33,33,2,34,1,16,2,1,0,2,1,0]
private def g14Sols : List (List Nat × List Nat) := [
  ([32,129], [1,2,0,3,1,4,2,5,3,6,4,7,5,8,7,6,0,9,8,7,1,10,9,8,2,11,10,9,3,12,11,10,4]),
  ([96,128], [2,0,3,1,4,2,5,3,6,4,7,5,4,1,8,6,5,4,3,2,0,9,7,6,5,4,3,2,1]),
  ([256,1028], [1,2,0,3,1,4,2,5,3,6,4,1,10,9,8,7,5,2,11,10,9,8,7,6,5,4,3,0,12,11,10,9,8,7,6,5,4,3,1]),
  ([768,1024], [2,0,3,1,4,2,5,3,6,4,1,10,9,8,7,5,2,11,10,9,8,6,5,4,3,2,0,12,11,10,9,7,6,5,4,3,2,1])
]
private def pool14_0 : List Nat := [1,2,4,5,8,9,10,16,18,20,32,34,36,40,42,48,50,52,64,65,68,69,72,73,96,100,104,128,129,130,132,133,136,137,138,144,146,148,256,258,260,264,266,272,274,276,288,290,292,296,298,304,306,308,320,324,328,352,356,360,384,386,388,392,394,400,402,404,512,513,516,517,520,521,576,577,580,581,584,585,640,641,644,645,648,649,768,772,776,832,836,840,896,900,904,1024,1025,1026,1028,1029,1032,1033,1034,1040,1042,1044,1056,1058,1060,1064,1066,1072,1074,1076,1088,1089,1092,1093,1096,1097,1120,1124,1128,1152,1153,1154,1156,1157,1160,1161,1162,1168,1170,1172]
set_option maxRecDepth 20000 in set_option maxHeartbeats 10000000 in
private theorem enum14_0_empty : enumGenAux 6 11 (inds g11_0) ((inds g11_0).filter (fun p => p.2 == 4)) 1 2 2 pool14_0 [] = [] ∧ pool14_0.Pairwise (· < ·) ∧ (inds g11_0).all (fun p => !(1 ≤ p.2 && p.2 < 5) || decide (p.1 ∈ pool14_0)) = true := by decide +kernel
private def pool14_1 : List Nat := [1,2,4,5,8,9,10,16,18,20,32,34,36,40,42,48,50,52,64,65,68,69,72,73,96,100,104,128,129,130,132,133,136,137,138,144,146,148,256,257,258,264,265,266,272,274,288,290,296,298,304,306,320,321,328,329,352,360,384,385,386,392,393,394,400,402,512,513,516,517,528,532,544,548,560,564,576,577,580,581,608,612,640,641,644,645,656,660,768,769,784,800,816,832,833,864,896,897,912,1024,1025,1026,1028,1029,1032,1033,1034,1040,1042,1044,1056,1058,1060,1064,1066,1072,1074,1076,1088,1089,1092,1093,1096,1097,1120,1124,1128,1152,1153,1154,1156,1157,1160,1161,1162,1168,1170,1172]
set_option maxRecDepth 20000 in set_option maxHeartbeats 10000000 in
private theorem enum14_1_ok : (enumGenAux 6 11 (inds g11_1) ((inds g11_1).filter (fun p => p.2 == 4)) 1 2 3 pool14_1 []).all (fun cs => g14Sols.any (fun e => decide (e.1 = cs))) = true ∧ g14Sols.all (fun e => decide (relabel e.2 (attach e.1 g11_1) = g14_20)) = true ∧ pool14_1.Pairwise (· < ·) ∧ (inds g11_1).all (fun p => !(1 ≤ p.2 && p.2 < 5) || decide (p.1 ∈ pool14_1)) = true := by decide +kernel
private def pool14_2 : List Nat := [1,2,4,5,8,9,10,16,18,20,32,34,36,40,42,48,50,52,64,65,68,69,72,73,96,100,104,128,129,130,132,133,136,137,138,144,146,148,256,257,258,264,265,266,272,274,288,290,296,298,304,306,320,321,328,329,352,360,384,385,386,392,393,394,400,402,512,513,516,517,528,532,576,577,580,581,640,641,644,645,656,660,768,769,784,832,833,896,897,912,1024,1025,1026,1028,1029,1032,1033,1034,1040,1042,1044,1056,1058,1060,1064,1066,1072,1074,1076,1088,1089,1092,1093,1096,1097,1120,1124,1128,1152,1153,1154,1156,1157,1160,1161,1162,1168,1170,1172]
set_option maxRecDepth 20000 in set_option maxHeartbeats 10000000 in
private theorem enum14_2_empty : enumGenAux 6 11 (inds g11_2) ((inds g11_2).filter (fun p => p.2 == 4)) 1 2 2 pool14_2 [] = [] ∧ pool14_2.Pairwise (· < ·) ∧ (inds g11_2).all (fun p => !(1 ≤ p.2 && p.2 < 5) || decide (p.1 ∈ pool14_2)) = true := by decide +kernel
private def pool14_3 : List Nat := [1,2,4,5,8,9,10,16,18,20,32,34,36,40,42,48,50,52,64,65,68,69,72,73,96,100,104,128,129,130,132,133,136,137,138,144,146,148,256,258,264,266,272,274,288,290,296,298,304,306,320,328,352,360,384,386,392,394,400,402,512,513,516,517,520,521,528,532,576,577,580,581,584,585,640,641,644,645,648,649,656,660,768,776,784,832,840,896,904,912,1024,1025,1026,1028,1029,1032,1033,1034,1040,1042,1044,1056,1058,1060,1064,1066,1072,1074,1076,1088,1089,1092,1093,1096,1097,1120,1124,1128,1152,1153,1154,1156,1157,1160,1161,1162,1168,1170,1172]
set_option maxRecDepth 20000 in set_option maxHeartbeats 10000000 in
private theorem enum14_3_empty : enumGenAux 6 11 (inds g11_3) ((inds g11_3).filter (fun p => p.2 == 4)) 1 2 2 pool14_3 [] = [] ∧ pool14_3.Pairwise (· < ·) ∧ (inds g11_3).all (fun p => !(1 ≤ p.2 && p.2 < 5) || decide (p.1 ∈ pool14_3)) = true := by decide +kernel
private def pool14_4 : List Nat := [1,2,4,5,8,9,10,16,18,20,32,34,36,40,42,48,50,52,64,65,68,69,72,73,96,100,104,128,129,130,132,133,136,137,138,144,146,148,256,258,260,264,266,272,274,276,288,290,292,296,298,304,306,308,320,324,328,352,356,360,512,513,514,520,521,522,528,530,576,577,584,585,640,641,642,648,649,650,656,658,768,770,776,778,784,786,832,840,1024,1025,1026,1028,1029,1032,1033,1034,1040,1042,1044,1056,1058,1060,1064,1066,1072,1074,1076,1088,1089,1092,1093,1096,1097,1120,1124,1128,1152,1153,1154,1156,1157,1160,1161,1162,1168,1170,1172]
set_option maxRecDepth 20000 in set_option maxHeartbeats 10000000 in
private theorem enum14_4_empty : enumGenAux 6 11 (inds g11_4) ((inds g11_4).filter (fun p => p.2 == 4)) 1 2 2 pool14_4 [] = [] ∧ pool14_4.Pairwise (· < ·) ∧ (inds g11_4).all (fun p => !(1 ≤ p.2 && p.2 < 5) || decide (p.1 ∈ pool14_4)) = true := by decide +kernel
private def pool14_5 : List Nat := [1,2,4,5,8,9,10,16,18,20,32,34,36,40,42,48,50,52,64,65,68,69,72,73,96,100,104,128,129,130,132,133,136,137,138,144,146,148,256,258,260,264,266,272,274,276,288,290,292,296,298,304,306,308,320,324,328,352,356,360,512,513,514,516,517,520,521,522,528,530,532,640,641,642,644,645,648,649,650,656,658,660,768,770,772,776,778,784,786,788,1024,1025,1026,1028,1029,1032,1033,1034,1040,1042,1044,1056,1058,1060,1064,1066,1072,1074,1076,1088,1089,1092,1093,1096,1097,1120,1124,1128,1152,1153,1154,1156,1157,1160,1161,1162,1168,1170,1172]
set_option maxRecDepth 20000 in set_option maxHeartbeats 10000000 in
private theorem enum14_5_empty : enumGenAux 6 11 (inds g11_5) ((inds g11_5).filter (fun p => p.2 == 4)) 1 2 2 pool14_5 [] = [] ∧ pool14_5.Pairwise (· < ·) ∧ (inds g11_5).all (fun p => !(1 ≤ p.2 && p.2 < 5) || decide (p.1 ∈ pool14_5)) = true := by decide +kernel
private def pool14_6 : List Nat := [1,2,4,5,8,9,10,16,18,20,32,34,36,40,42,48,50,52,64,65,68,69,72,73,96,100,104,128,129,130,132,133,136,137,138,144,146,148,256,257,258,264,265,266,272,274,320,321,328,329,384,385,386,392,393,394,400,402,512,513,514,516,517,528,530,532,544,546,548,560,562,564,576,577,580,581,608,612,768,769,770,784,786,832,833,1024,1025,1026,1028,1029,1032,1033,1034,1040,1042,1044,1056,1058,1060,1064,1066,1072,1074,1076,1088,1089,1092,1093,1096,1097,1120,1124,1128,1152,1153,1154,1156,1157,1160,1161,1162,1168,1170,1172]
set_option maxRecDepth 20000 in set_option maxHeartbeats 10000000 in
private theorem enum14_6_empty : enumGenAux 6 11 (inds g11_6) ((inds g11_6).filter (fun p => p.2 == 4)) 1 2 2 pool14_6 [] = [] ∧ pool14_6.Pairwise (· < ·) ∧ (inds g11_6).all (fun p => !(1 ≤ p.2 && p.2 < 5) || decide (p.1 ∈ pool14_6)) = true := by decide +kernel
private def w14_to_21 : List WeightedRow := [((2629,5),166),((8773,5),163),((9285,5),12),((2693,5),76),((8837,5),76),((3205,5),136),((9349,5),136),((2377,5),30),((8521,5),30),((3145,5),30),((9289,5),18),((2441,5),46),((8585,5),46),((3209,5),46),((9353,5),46),((2945,5),136),((9089,5),136),((4394,5),76),((8490,5),136),((5162,5),76),((9258,5),136),((2442,5),30),((8586,5),30),((3210,5),30),((9354,5),30),((6410,5),136),((7178,5),136),((4402,5),143),((5170,5),25),((2450,5),30),((8594,5),30),((3218,5),30),((9362,5),30),((4660,5),62),((8756,5),143),((5172,5),141),((9268,5),62),((2708,5),23),((8852,5),23),((6676,5),143),((7188,5),62),((4708,5),62),((8804,5),3),((5220,5),143),((9316,5),50),((7236,5),62),((4456,5),23),((5224,5),23),((9320,5),12),((4912,5),23),((9008,5),62),((6928,5),62),((4960,5),143),((9056,5),62),((6976,5),62),((73,3),168),((138,3),16),((146,3),168),((1,1),46),((2,1),46)]
set_option maxRecDepth 24000 in set_option maxHeartbeats 25000000 in
private theorem cert14_to_21 : dualCheckGen 7 6 2 25 290 2210 0 g14_20 w14_to_21 = true := by decide +kernel

/- ## (3,6;15, <= 25) -> unique g15_25 -> d=5 dual obstruction -/

private def g15_25 : List Nat := [1049,145,1057,33,2,194,1,8,10,1,4,4,2,1,0]
private def w15_d2_b4_0 : List WeightedRow := [((1169,4),72),((2193,4),90),((2321,4),45),((1553,4),45),((2145,4),72),((801,4),45),((1217,4),90),((526,4),108),((1162,4),90),((1546,4),45),((786,4),45),((2322,4),160),((204,4),90),((2148,4),90),((804,4),160),((1128,4),90),((1224,4),36)]
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert15_d2_b4_0 : dualCheckGen 6 2 1 3 360 115 0 b4_0 w15_d2_b4_0 = true := by decide +kernel
private def w15_d2_b4_1 : List WeightedRow := [((2193,4),1),((1553,4),1),((2145,4),1),((774,4),1),((1162,4),1),((786,4),1),((108,4),1),((2340,4),1),((1224,4),1)]
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert15_d2_b4_1 : dualCheckGen 6 2 1 2 10 0 7 b4_1 w15_d2_b4_1 = true := by decide +kernel
private def w15_d2_b4_2 : List WeightedRow := [((785,4),1),((1162,4),1),((2148,4),1)]
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert15_d2_b4_2 : dualCheckGen 6 2 1 2 4 0 3 b4_2 w15_d2_b4_2 = true := by decide +kernel
private def w15_d2_b4_3 : List WeightedRow := []
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert15_d2_b4_3 : dualCheckGen 6 2 1 1 1 0 1 b4_3 w15_d2_b4_3 = true := by decide +kernel
private def w15_d2_b4_4 : List WeightedRow := []
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert15_d2_b4_4 : dualCheckGen 6 2 1 1 1 0 1 b4_4 w15_d2_b4_4 = true := by decide +kernel
private def w15_d2_b4_5 : List WeightedRow := []
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert15_d2_b4_5 : dualCheckGen 6 2 1 1 1 0 1 b4_5 w15_d2_b4_5 = true := by decide +kernel
private def w15_d2_b4_6 : List WeightedRow := []
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert15_d2_b4_6 : dualCheckGen 6 2 1 1 1 0 1 b4_6 w15_d2_b4_6 = true := by decide +kernel
private def w15_d2_b4_7 : List WeightedRow := []
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert15_d2_b4_7 : dualCheckGen 6 2 1 0 1 0 1 b4_7 w15_d2_b4_7 = true := by decide +kernel
private def w15_d2_b4_8 : List WeightedRow := []
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert15_d2_b4_8 : dualCheckGen 6 2 1 1 1 0 1 b4_8 w15_d2_b4_8 = true := by decide +kernel
private def w15_d2_b4_9 : List WeightedRow := []
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert15_d2_b4_9 : dualCheckGen 6 2 1 0 1 0 1 b4_9 w15_d2_b4_9 = true := by decide +kernel
private def w15_d3_0 : List WeightedRow := [((581,4),285),((1093,4),114),((645,4),190),((585,4),285),((1097,4),190),((649,4),190),((1066,4),285),((394,4),480),((306,4),285),((1074,4),285),((402,4),190),((1170,4),190),((308,4),285),((1172,4),480),((356,4),114),((836,4),190),((1128,4),114),((840,4),114),((577,3),114),((50,3),114)]
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert15_d3_0 : dualCheckGen 6 3 2 6 2280 0 1786 g11_0 w15_d3_0 = true := by decide +kernel
private def w15_d3_2 : List WeightedRow := [((581,4),2),((1161,4),1),((833,4),1),((298,4),1),((1066,4),1),((394,4),1),((306,4),1),((1170,4),1),((1076,4),1),((660,4),1),((1128,4),1),((912,4),1)]
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert15_d3_2 : dualCheckGen 6 3 2 6 8 0 8 g11_2 w15_d3_2 = true := by decide +kernel
private def w15_d3_3 : List WeightedRow := [((581,4),1),((1093,4),1),((645,4),1),((585,4),1),((1066,4),1),((394,4),1),((1162,4),1),((306,4),2),((1170,4),1),((660,4),1),((1124,4),1),((840,4),1)]
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert15_d3_3 : dualCheckGen 6 3 2 6 8 0 8 g11_3 w15_d3_3 = true := by decide +kernel
private def w15_d3_4 : List WeightedRow := [((1093,4),10),((585,4),10),((1097,4),7),((649,4),10),((298,4),7),((1066,4),10),((1162,4),7),((1074,4),7),((658,4),14),((786,4),7),((308,4),7),((1172,4),7),((356,4),14),((133,3),7),((577,3),7)]
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert15_d3_4 : dualCheckGen 6 3 2 6 70 0 58 g11_4 w15_d3_4 = true := by decide +kernel
private def w15_d3_5 : List WeightedRow := [((1093,4),1),((645,4),1),((1097,4),2),((649,4),1),((778,4),1),((306,4),1),((658,4),1),((1170,4),1),((1076,4),1),((788,4),1),((356,4),1),((360,4),1)]
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert15_d3_5 : dualCheckGen 6 3 2 6 8 0 8 g11_5 w15_d3_5 = true := by decide +kernel
private def w15_d3_6 : List WeightedRow := [((1157,4),1),((393,4),1),((833,4),1),((1066,4),1),((394,4),1),((786,4),1),((564,4),1),((1172,4),1),((612,4),1),((1128,4),1)]
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert15_d3_6 : dualCheckGen 6 3 2 6 8 0 10 g11_6 w15_d3_6 = true := by decide +kernel
private def pool15_1 : List Nat := [5,9,10,18,20,34,36,40,42,48,50,52,65,68,69,72,73,96,100,104,129,130,132,133,136,137,138,144,146,148,257,258,264,265,266,272,274,288,290,296,298,304,306,320,321,328,329,352,360,384,385,386,392,393,394,400,402,513,516,517,528,532,544,548,560,564,576,577,580,581,608,612,640,641,644,645,656,660,768,769,784,800,816,832,833,864,896,897,912,1025,1026,1028,1029,1032,1033,1034,1040,1042,1044,1056,1058,1060,1064,1066,1072,1074,1076,1088,1089,1092,1093,1096,1097,1120,1124,1128,1152,1153,1154,1156,1157,1160,1161,1162,1168,1170,1172]
private def g15Sols : List (List Nat × List Nat) := [
  ([129,288,1060], [5,6,7,6,8,7,9,8,2,0,10,9,3,1,0,11,10,8,6,4,2,1,13,12,11,9,8,7,5,4,3,2,1]),
  ([129,800,1056], [6,5,7,6,5,8,7,6,9,8,7,10,9,8,0,11,10,9,7,5,3,1,0,12,11,10,9,8,7,6,4,2,1,13,12,11,10,9,8,7,5,3,2,1]),
  ([288,385,1028], [3,0,4,1,5,2,6,5,3,7,6,4,0,8,7,5,4,1,9,8,6,5,4,2,10,9,7,6,5,3,11,10,8,7,6,4,3,12,11,9,8,7,5,4,13,12,10,9,8,6,5]),
  ([352,384,1028], [3,0,4,1,5,2,6,5,3,7,6,4,8,7,5,4,1,9,8,6,5,4,2,10,9,7,6,5,3,11,10,8,7,6,4,12,11,9,8,7,5,1,13,12,10,9,8,6,5,3,2,1]),
  ([96,384,1156], [1,2,3,0,4,1,5,2,6,3,7,4,0,8,5,2,1,9,6,3,2,10,9,8,7,6,5,4,3,11,10,9,8,7,6,5,4,12,11,10,9,8,7,6,5,4,3,13,12,11,10,9,8,7,6,5,4,1]),
  ([96,896,1152], [1,2,3,0,4,1,5,2,6,3,7,4,8,5,2,1,9,6,3,2,10,9,8,7,6,5,4,3,11,10,9,8,7,6,5,4,12,11,10,9,8,7,6,5,3,13,12,11,10,9,8,7,6,4,3,2,1]),
  ([768,1056,1153], [1,2,3,0,4,1,5,2,6,3,7,4,0,8,5,1,9,6,5,2,10,7,6,5,4,3,11,8,7,6,5,4,3,12,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5]),
  ([768,1120,1152], [1,2,3,0,4,1,5,2,6,3,7,4,8,5,1,9,6,5,2,10,7,6,5,4,3,11,8,7,6,5,4,12,9,8,7,6,5,1,13,12,11,10,9,8,7,6,5,3,2,1])
]

set_option maxRecDepth 24000 in set_option maxHeartbeats 15000000 in
private theorem enum15_1_ok :
    (enumGenAux 6 11 (inds g11_1) ((inds g11_1).filter (fun p => p.2 == 4)) 2 3 7 pool15_1 []).all
      (fun cs => g15Sols.any (fun e => decide (e.1 = cs))) = true ∧
    g15Sols.all (fun e => decide (relabel e.2 (attach e.1 g11_1) = g15_25)) = true ∧
    pool15_1.Pairwise (· < ·) ∧
    (inds g11_1).all (fun p => !(2 ≤ p.2 && p.2 < 5) || decide (p.1 ∈ pool15_1)) = true := by
  decide +kernel

private def w15_to_21 : List WeightedRow := [((4677,5),5),((16965,5),7),((5189,5),7),((17029,5),5),((5253,5),9),((17541,5),9),((8521,5),9),((16713,5),2),((17481,5),2),((12361,5),7),((16777,5),1),((17545,5),2),((12425,5),5),((9025,5),9),((9089,5),5),((17281,5),3),((12929,5),7),((16682,5),9),((3114,5),7),((17450,5),9),((8586,5),7),((5258,5),2),((17546,5),2),((10506,5),5),((14346,5),7),((2354,5),7),((16690,5),5),((3122,5),5),((8594,5),5),((16786,5),3),((5266,5),2),((17554,5),1),((12434,5),9),((14354,5),9),((2612,5),9),((16948,5),5),((17460,5),7),((4756,5),1),((17044,5),3),((5268,5),2),((6676,5),2),((7188,5),2),((2660,5),9),((3172,5),7),((17508,5),5),((2408,5),2),((16744,5),2),((7240,5),7),((17200,5),3),((9104,5),3),((17296,5),2),((11024,5),1),((14864,5),2),((2912,5),2),((17248,5),1),((11072,5),2),((14912,5),2)]
set_option maxRecDepth 24000 in set_option maxHeartbeats 25000000 in
private theorem cert15_to_21 : dualCheckGen 7 5 2 21 20 131 0 g15_25 w15_to_21 = true := by decide +kernel

/- ## (3,6;16, <= 32): 4-regular (killed), d=2 (empty), d=3 (3 reps) -/

private def g4reg_0 : List Nat := [1049,145,545,545,514,74,65,72,50,1,3,8,4,2,1,0]
private def w4reg_to_21_0 : List WeightedRow := [((33349,5),2),((33861,5),2),((8837,5),1),((33413,5),1),((9349,5),3),((25093,5),1),((25605,5),2),((4425,5),1),((17481,5),2),((20553,5),2),((4489,5),3),((33161,5),1),((33929,5),2),((4929,5),1),((33601,5),3),((21057,5),1),((33665,5),1),((12929,5),2),((29185,5),3),((2346,5),1),((33066,5),1),((17450,5),2),((18474,5),1),((4490,5),2),((33162,5),1),((33930,5),3),((22538,5),3),((2354,5),2),((33074,5),3),((9266,5),1),((33842,5),1),((9362,5),2),((33938,5),1),((12434,5),2),((6418,5),2),((25634,5),3),((26658,5),1),((30722,5),2),((9268,5),1),((33844,5),2),((10292,5),3),((33428,5),3),((9364,5),1),((33940,5),1),((10772,5),2),((17508,5),2),((33892,5),1),((18532,5),2),((26660,5),1),((19012,5),3),((27140,5),1),((2408,5),3),((33128,5),2),((33896,5),2),((6472,5),1),((22600,5),1),((5008,5),2),((33680,5),2),((6928,5),1),((14864,5),2),((6976,5),2),((23104,5),1)]
set_option maxRecDepth 24000 in set_option maxHeartbeats 25000000 in
private theorem cert4reg_to_21_0 : dualCheckGen 7 4 3 15 12 37 0 g4reg_0 w4reg_to_21_0 = true := by decide +kernel
private def g4reg_1 : List Nat := [153,145,289,769,514,42,33,96,10,17,5,8,4,2,1,0]
private def w4reg_to_21_1 : List WeightedRow := [((8773,5),40),((33349,5),40),((17477,5),11),((33861,5),11),((24645,5),11),((4741,5),11),((33413,5),11),((5253,5),40),((33925,5),11),((12805,5),11),((21509,5),40),((28677,5),11),((2633,5),11),((33353,5),11),((17481,5),40),((33865,5),11),((18505,5),40),((2697,5),40),((33417,5),11),((33929,5),40),((10817,5),11),((26689,5),11),((6785,5),40),((14849,5),11),((30721,5),40),((16682,5),11),((33066,5),11),((17450,5),40),((33834,5),11),((2442,5),40),((33162,5),11),((33930,5),40),((18698,5),40),((8498,5),40),((33074,5),40),((5170,5),11),((33842,5),11),((12338,5),11),((2450,5),11),((33170,5),11),((5266,5),40),((33938,5),11),((6290,5),40),((10514,5),11),((14354,5),11),((24866,5),11),((21538,5),40),((28706,5),11),((26882,5),11),((30722,5),40),((5172,5),11),((33844,5),40),((12340,5),40),((4756,5),11),((33428,5),40),((5268,5),11),((33940,5),11),((12820,5),40),((17508,5),11),((33892,5),40),((24676,5),40),((21540,5),11),((28708,5),11),((16744,5),11),((33128,5),40),((17512,5),11),((33896,5),11),((2888,5),11),((33608,5),40),((18760,5),11),((2952,5),11),((33672,5),11),((2960,5),11),((33680,5),40),((6800,5),11),((11024,5),40),((14864,5),11),((24928,5),40),((11072,5),40),((26944,5),11)]
set_option maxRecDepth 24000 in set_option maxHeartbeats 25000000 in
private theorem cert4reg_to_21_1 : dualCheckGen 7 4 3 15 220 514 0 g4reg_1 w4reg_to_21_1 = true := by decide +kernel
private def g4regRep (i : Nat) : List Nat := if i == 0 then g4reg_0 else g4reg_1
private def pool4reg_0 : List Nat := [42,50,52,69,73,100,104,133,137,138,146,148,266,274,276,290,292,296,304,324,328,352,386,388,392,400,517,521,577,580,584,641,644,648,772,776,832,896,1029,1033,1034,1042,1044,1058,1060,1064,1072,1089,1092,1096,1120,1153,1154,1156,1160,1168]
set_option maxRecDepth 24000 in set_option maxHeartbeats 15000000 in
private theorem enum4reg_0_empty : enum4RegAux (inds g11_0) ((inds g11_0).filter (fun p => p.2 == 4)) g11_0 4 pool4reg_0 [] (degrees g11_0) = [] ∧ pool4reg_0.Pairwise (· < ·) ∧ (inds g11_0).all (fun p => !(p.2 == 3) || decide (p.1 ∈ pool4reg_0)) = true := by decide +kernel
private def pool4reg_2 : List Nat := [42,50,52,69,73,100,104,133,137,138,146,148,265,266,274,290,296,304,321,328,352,385,386,392,400,517,532,577,580,641,644,656,769,784,832,896,1029,1033,1034,1042,1044,1058,1060,1064,1072,1089,1092,1096,1120,1153,1154,1156,1160,1168]
private def g4regSols_2 : List (List Nat × Nat × List Nat) := [
  ([328,400,1060,1153], 0, [1,2,3,8,7,4,9,8,5,10,9,7,6,11,10,8,7,1,12,11,9,8,7,5,2,1,13,12,10,9,8,7,6,3,2,14,13,12,11,10,9,8,7,6,4,3])
]
set_option maxRecDepth 24000 in set_option maxHeartbeats 15000000 in
private theorem enum4reg_2_ok : (enum4RegAux (inds g11_2) ((inds g11_2).filter (fun p => p.2 == 4)) g11_2 4 pool4reg_2 [] (degrees g11_2)).all (fun cs => g4regSols_2.any (fun e => decide (e.1 = cs))) = true ∧ g4regSols_2.all (fun e => decide (e.2.1 < 2 ∧ relabel e.2.2 (attach e.1 g11_2) = g4regRep e.2.1)) = true ∧ pool4reg_2.Pairwise (· < ·) ∧ (inds g11_2).all (fun p => !(p.2 == 3) || decide (p.1 ∈ pool4reg_2)) = true := by decide +kernel
private def pool4reg_3 : List Nat := [42,50,52,69,73,100,104,133,137,138,146,148,266,274,290,296,304,328,352,386,392,400,517,521,532,577,580,584,641,644,648,656,776,784,832,896,1029,1033,1034,1042,1044,1058,1060,1064,1072,1089,1092,1096,1120,1153,1154,1156,1160,1168]
private def g4regSols_3 : List (List Nat × Nat × List Nat) := [
  ([148,776,1120,1160], 0, [2,3,4,5,6,4,7,5,8,6,5,4,9,7,6,5,10,8,7,6,0,11,9,8,7,4,3,1,13,12,10,9,8,7,5,4,3,2,1,14,13,11,10,9,8,6,5,4,3,2,1]),
  ([104,896,1044,1160], 0, [2,3,4,5,6,7,5,8,6,4,9,7,5,10,8,6,0,11,9,8,7,6,3,1,12,10,9,8,7,4,2,1,14,13,11,10,9,8,5,3,2,1]),
  ([328,656,1060,1160], 1, [6,7,5,8,6,5,9,7,6,10,8,7,3,11,10,9,8,4,12,11,10,9,7,5,2,1,13,12,11,10,8,7,6,5,4,3,2,14,13,12,11,10,9,8,7,6,5,4,3,2])
]
set_option maxRecDepth 24000 in set_option maxHeartbeats 15000000 in
private theorem enum4reg_3_ok : (enum4RegAux (inds g11_3) ((inds g11_3).filter (fun p => p.2 == 4)) g11_3 4 pool4reg_3 [] (degrees g11_3)).all (fun cs => g4regSols_3.any (fun e => decide (e.1 = cs))) = true ∧ g4regSols_3.all (fun e => decide (e.2.1 < 2 ∧ relabel e.2.2 (attach e.1 g11_3) = g4regRep e.2.1)) = true ∧ pool4reg_3.Pairwise (· < ·) ∧ (inds g11_3).all (fun p => !(p.2 == 3) || decide (p.1 ∈ pool4reg_3)) = true := by decide +kernel
private def pool4reg_4 : List Nat := [42,50,52,69,73,100,104,133,137,138,146,148,266,274,276,290,292,296,304,324,328,352,521,522,530,577,584,641,642,648,656,770,776,784,832,1029,1033,1034,1042,1044,1058,1060,1064,1072,1089,1092,1096,1120,1153,1154,1156,1160,1168]
set_option maxRecDepth 24000 in set_option maxHeartbeats 15000000 in
private theorem enum4reg_4_empty : enum4RegAux (inds g11_4) ((inds g11_4).filter (fun p => p.2 == 4)) g11_4 4 pool4reg_4 [] (degrees g11_4) = [] ∧ pool4reg_4.Pairwise (· < ·) ∧ (inds g11_4).all (fun p => !(p.2 == 3) || decide (p.1 ∈ pool4reg_4)) = true := by decide +kernel
private def pool4reg_5 : List Nat := [42,50,52,69,73,100,104,133,137,138,146,148,266,274,276,290,292,296,304,324,328,352,517,521,522,530,532,641,642,644,648,656,770,772,776,784,1029,1033,1034,1042,1044,1058,1060,1064,1072,1089,1092,1096,1120,1153,1154,1156,1160,1168]
set_option maxRecDepth 24000 in set_option maxHeartbeats 15000000 in
private theorem enum4reg_5_empty : enum4RegAux (inds g11_5) ((inds g11_5).filter (fun p => p.2 == 4)) g11_5 4 pool4reg_5 [] (degrees g11_5) = [] ∧ pool4reg_5.Pairwise (· < ·) ∧ (inds g11_5).all (fun p => !(p.2 == 3) || decide (p.1 ∈ pool4reg_5)) = true := by decide +kernel
private def pool4reg_6 : List Nat := [42,50,52,69,73,100,104,133,137,138,146,148,265,266,274,321,328,385,386,392,400,517,530,532,546,548,560,577,580,608,769,770,784,832,1029,1033,1034,1042,1044,1058,1060,1064,1072,1089,1092,1096,1120,1153,1154,1156,1160,1168]
set_option maxRecDepth 24000 in set_option maxHeartbeats 15000000 in
private theorem enum4reg_6_empty : enum4RegAux (inds g11_6) ((inds g11_6).filter (fun p => p.2 == 4)) g11_6 4 pool4reg_6 [] (degrees g11_6) = [] ∧ pool4reg_6.Pairwise (· < ·) ∧ (inds g11_6).all (fun p => !(p.2 == 3) || decide (p.1 ∈ pool4reg_6)) = true := by decide +kernel
private def pool16_b3 : List Nat := [1,2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,32,33,34,48,50,64,65,68,72,76,128,129,132,136,140,144,148,152,156,192,193,196,200,204,256,257,258,260,262,272,274,276,278,288,289,290,304,306,384,385,388,400,404,512,513,514,516,518,520,522,524,526,544,545,546,576,577,580,584,588,1024,1025,1026,1032,1034,1040,1042,1048,1050,1056,1057,1058,1072,1074,1088,1089,1096,1536,1537,1538,1544,1546,1568,1569,1570,1600,1601,1608,2048,2049,2056,2064,2072,2080,2081,2096,2112,2113,2120,2176,2177,2184,2192,2200,2240,2241,2248,2304,2305,2320,2336,2337,2352,2432,2433,2448,3072,3073,3080,3088,3096,3104,3105,3120,3136,3137,3144,4096,4097,4098,4100,4102,4128,4129,4130,4160,4161,4164,4224,4225,4228,4288,4289,4292,4352,4353,4354,4356,4358,4384,4385,4386,4480,4481,4484,4608,4609,4610,4612,4614,4640,4641,4642,4672,4673,4676]

set_option maxRecDepth 24000 in set_option maxHeartbeats 15000000 in
private theorem enum16_b3_empty :
    enumGenAux 6 13 (inds b3_0) ((inds b3_0).filter (fun p => p.2 == 4)) 1 2 4 pool16_b3 [] = [] ∧
    pool16_b3.Pairwise (· < ·) ∧
    (inds b3_0).all (fun p => !(1 ≤ p.2 && p.2 < 5) || decide (p.1 ∈ pool16_b3)) = true := by
  decide +kernel

private def w16_b4_1 : List WeightedRow := [((1169,4),87),((785,4),128),((2321,4),99),((1553,4),13),((1121,4),64),((2145,4),14),((801,4),12),((2241,4),114),((526,4),113),((2310,4),114),((1162,4),102),((1546,4),13),((1170,4),12),((2194,4),114),((786,4),100),((108,4),115),((556,4),1),((2148,4),99),((804,4),87),((2340,4),12),((1576,4),61),((1224,4),113),((76,3),24),((200,3),24)]
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert16_b4_1 : dualCheckGen 6 3 2 8 240 426 0 b4_1 w16_b4_1 = true := by decide +kernel
private def w16_b4_2 : List WeightedRow := [((1169,4),14),((2193,4),14),((785,4),28),((2321,4),21),((1553,4),21),((1121,4),14),((2145,4),14),((801,4),21),((1217,4),14),((2241,4),14),((142,4),21),((2310,4),42),((1546,4),42),((1170,4),14),((2194,4),14),((786,4),36),((108,4),36),((204,4),28),((2340,4),42),((2244,4),21),((1576,4),42),((1224,4),21)]
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert16_b4_2 : dualCheckGen 6 3 2 8 84 128 0 b4_2 w16_b4_2 = true := by decide +kernel
private def w16_b4_3 : List WeightedRow := [((1169,4),3),((785,4),2),((2321,4),1),((2145,4),2),((801,4),2),((2241,4),1),((526,4),3),((2310,4),2),((2194,4),3),((786,4),2),((108,4),3),((804,4),1),((2340,4),2),((1576,4),1),((1224,4),4)]
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert16_b4_3 : dualCheckGen 6 3 2 7 8 2 0 b4_3 w16_b4_3 = true := by decide +kernel
private def w16_b4_4 : List WeightedRow := [((1553,4),3),((2337,4),3),((1217,4),3),((270,4),3),((2194,4),3),((786,4),3),((108,4),3),((2244,4),3),((1576,4),3)]
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert16_b4_4 : dualCheckGen 6 3 2 7 7 1 0 b4_4 w16_b4_4 = true := by decide +kernel
private def w16_b4_5 : List WeightedRow := [((1553,4),3),((1185,4),3),((2369,4),3),((1038,4),3),((2194,4),3),((786,4),3),((108,4),3),((2212,4),3),((840,4),3)]
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert16_b4_5 : dualCheckGen 6 3 2 7 7 1 0 b4_5 w16_b4_5 = true := by decide +kernel
private def w16_b4_6 : List WeightedRow := [((2193,4),12),((2321,4),25),((2145,4),12),((1185,4),12),((270,4),12),((106,4),25),((2210,4),12),((1548,4),12),((1172,4),25),((788,4),12),((840,4),12)]
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert16_b4_6 : dualCheckGen 6 3 2 7 40 18 0 b4_6 w16_b4_6 = true := by decide +kernel
private def w16_b4_7 : List WeightedRow := [((2193,4),1),((2321,4),1),((2145,4),1),((1185,4),1),((2369,4),1),((1038,4),1),((106,4),2),((1186,4),1),((2210,4),1),((1172,4),2),((788,4),2),((840,4),2)]
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert16_b4_7 : dualCheckGen 6 3 2 6 20 0 31 b4_7 w16_b4_7 = true := by decide +kernel
private def w16_b4_8 : List WeightedRow := [((2193,4),7),((2321,4),7),((1553,4),15),((1185,4),7),((833,4),7),((142,4),7),((270,4),7),((2146,4),15),((2210,4),7),((2370,4),7),((1548,4),15),((1188,4),7),((836,4),7),((1176,4),7),((792,4),7)]
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert16_b4_8 : dualCheckGen 6 3 2 7 35 3 0 b4_8 w16_b4_8 = true := by decide +kernel
private def w16_b4_9 : List WeightedRow := [((2193,4),4),((1553,4),4),((1185,4),4),((833,4),5),((270,4),4),((106,4),4),((2210,4),5),((2370,4),4),((1548,4),5),((1172,4),4),((840,4),4)]
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert16_b4_9 : dualCheckGen 6 3 2 6 40 0 51 b4_9 w16_b4_9 = true := by decide +kernel
private def w16_b4_10 : List WeightedRow := []
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert16_b4_10 : dualCheckGen 6 3 2 5 1 0 2 b4_10 w16_b4_10 = true := by decide +kernel
private def w16_b4_11 : List WeightedRow := []
set_option maxRecDepth 20000 in set_option maxHeartbeats 15000000 in
private theorem cert16_b4_11 : dualCheckGen 6 3 2 5 1 0 2 b4_11 w16_b4_11 = true := by decide +kernel
private def g16_0 : List Nat := [10247,2072,1154,657,3,258,6,19,34,18,1,0,4,2,1,0]
private def g16_1 : List Nat := [10247,2072,1154,657,3,2,134,67,2,6,1,4,4,2,1,0]
private def g16_2 : List Nat := [2055,24,3202,145,131,130,6,67,2,10,3,4,4,2,1,0]
private def g16Rep (i : Nat) : List Nat := match i with | 0 => g16_0 | 1 => g16_1 | _ => g16_2
private def pool16_b40 : List Nat := [6,10,12,14,17,18,33,36,40,44,65,68,72,76,96,97,100,104,108,129,130,132,134,136,138,140,142,144,145,146,192,193,196,200,204,257,258,260,262,272,273,274,288,289,292,513,514,516,518,520,522,524,526,528,529,530,544,545,548,552,556,768,769,770,772,774,784,785,786,800,801,804,1025,1026,1032,1034,1040,1041,1042,1056,1057,1064,1088,1089,1096,1120,1121,1128,1152,1153,1154,1160,1162,1168,1169,1170,1216,1217,1224,1536,1537,1538,1544,1546,1552,1553,1554,1568,1569,1576,2049,2050,2052,2054,2064,2065,2066,2080,2081,2084,2112,2113,2116,2144,2145,2148,2176,2177,2178,2180,2182,2192,2193,2194,2240,2241,2244,2304,2305,2306,2308,2310,2320,2321,2322,2336,2337,2340]
private def g16Sols : List (List Nat × Nat × List Nat) := [
  ([14,129,801], 0, [0,2,1,3,2,6,4,3,1,7,5,4,2,8,6,5,3,9,7,6,4,10,8,7,5,12,11,9,8,6,2,1,0,14,13,12,10,9,8,7,5,3,2,1]),
  ([129,142,800], 0, [1,0,2,1,3,2,0,7,4,3,2,1,8,5,4,3,2,9,6,5,4,3,2,1,10,7,6,5,4,3,2,1,11,8,7,6,5,4,3,2,1,12,9,8,7,6,5,4,3,2,0,13,12,10,9,8,7,6,5,4,3,2,1,0]),
  ([14,513,2241], 1, [2,3,0,4,3,1,5,4,2,6,5,3,2,0,7,6,4,3,1,8,7,5,4,2,9,8,6,5,3,1,10,9,7,6,5,4,3,2,1,11,10,8,7,6,5,4,3,2,12,11,9,8,7,6,5,4,3,13,12,11,10,9,8,7,6,5,4,1,14,13,12,11,10,9,8,7,6,5,4,3,2,1]),
  ([513,526,2240], 1, [1,2,3,0,4,1,5,3,2,6,4,3,7,5,4,1,8,6,5,2,9,7,6,3,10,8,7,4,11,9,8,5,12,10,9,6,13,12,11,10,7,14,13,12,11,8]),
  ([97,1026,2310], 0, [0,2,1,3,2,4,3,1,5,4,2,6,5,3,11,9,7,6,4,12,11,10,8,7,5,3,1,13,12,11,10,9,8,6,4,3,2,1,0,14,13,12,11,10,9,8,7,5,4,3,2,1,0]),
  ([1026,1121,2308], 0, [1,0,2,1,3,2,0,4,3,1,5,4,3,2,6,5,4,3,1,10,7,6,5,4,2,11,8,7,6,5,3,1,13,12,10,9,8,7,6,5,4,3,2,0,14,13,11,10,9,8,7,6,5,4,3,1,0]),
  ([97,1546,2050], 1, [3,0,4,1,5,4,2,6,5,3,2,0,7,6,4,3,2,1,8,7,5,4,3,2,9,8,6,5,4,3,2,10,9,7,6,5,4,3,2,11,10,8,7,6,5,4,3,2,12,11,9,8,7,6,5,4,3,2,13,12,10,9,8,7,6,5,4,3,2,1,14,13,11,10,9,8,7,6,5,4,3,2]),
  ([1544,2050,2145], 1, [2,3,0,4,1,5,2,6,4,3,0,7,5,4,1,8,6,5,2,9,7,6,3,10,8,7,4,11,9,8,5,12,10,9,6,3,2,13,11,10,8,7,4,3,2,14,12,11,10,9,8,7,5,4,3]),
  ([132,804,1041], 1, [1,2,3,0,4,1,5,2,6,5,3,7,6,4,1,8,7,5,2,9,8,6,3,1,10,9,7,4,3,2,11,10,9,8,5,4,3,2,1,12,11,10,9,6,5,4,3,2,13,12,11,10,7,6,5,4,3,2,14,13,12,11,10,8,7,6,5,4,3,2]),
  ([132,800,1169], 1, [1,2,3,0,4,1,5,2,6,3,0,7,5,4,1,8,6,5,3,2,9,7,6,4,3,10,8,7,6,5,4,11,10,9,8,7,6,5,4,12,11,10,9,8,7,6,5,13,12,11,10,9,8,7,6,5,4,2,14,13,12,11,10,9,8,7,6,5,3,2,1]),
  ([516,1041,2244], 0, [5,1,0,6,4,2,1,7,5,3,2,8,6,4,3,1,9,7,5,4,2,10,9,8,7,6,5,3,11,10,9,8,7,6,4,12,11,10,9,8,7,5,4,13,12,11,10,9,8,7,6,5,1,0,14,13,12,11,10,9,8,7,6,4,2,1,0]),
  ([516,1553,2240], 0, [1,0,2,1,3,2,0,5,4,3,1,9,8,6,5,4,3,2,1,10,9,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,1,12,11,10,9,8,7,6,5,4,2,13,12,11,10,9,8,7,6,5,3,0,14,13,12,11,10,9,8,7,6,5,4,1]),
  ([146,1056,2340], 1, [2,3,0,4,1,5,2,6,3,0,7,4,1,8,5,2,9,8,6,3,10,9,7,4,2,11,10,8,5,3,1,12,11,9,8,6,4,2,13,12,10,9,7,6,5,4,3,2,14,13,12,11,10,9,8,7,6,5,4,3,2]),
  ([1056,1170,2308], 1, [1,2,3,0,4,1,5,2,6,3,7,4,2,1,8,5,4,3,2,9,6,5,4,3,2,10,8,7,6,5,4,3,11,9,8,7,6,5,4,12,10,9,8,7,6,5,13,11,10,9,8,7,6,14,13,12,11,10,9,8,7,5,3,2,1]),
  ([146,1576,2080], 0, [4,5,0,6,4,1,7,6,5,4,3,2,8,7,6,5,4,3,1,9,8,7,6,5,4,2,10,9,8,7,6,5,3,11,10,9,8,7,6,4,12,11,10,9,8,7,5,13,12,11,10,9,8,6,0,14,13,12,11,10,9,7,2,1]),
  ([1544,2080,2194], 0, [0,6,2,1,7,4,3,2,8,7,5,4,3,1,9,8,6,5,4,2,1,10,9,7,6,5,4,3,2,11,10,8,7,6,5,4,3,12,11,9,8,7,6,5,4,3,2,13,12,10,9,8,7,6,5,4,3,0,14,13,12,11,10,9,8,7,6,5,4,3,1]),
  ([140,145,800], 1, [6,7,8,5,0,9,6,3,1,10,7,4,2,1,12,11,9,8,5,3,2,14,13,12,10,9,7,6,4,3,1,0]),
  ([524,529,2240], 1, [5,6,4,7,5,8,6,9,7,10,9,8,7,0,11,10,9,8,3,1,0,12,11,10,9,8,4,2,1,13,12,11,10,9,7,5,3,2,14,13,12,11,10,9,8,6,4,3,2,1,0]),
  ([548,1041,2180], 2, [5,6,7,4,8,5,9,6,10,9,8,7,5,11,10,9,8,6,1,12,11,10,9,8,7,6,3,2,13,12,11,10,9,8,7,4,3,2,14,13,12,11,10,9,8,6,5,4,3,0]),
  ([196,772,1041], 1, [5,9,8,6,10,9,7,6,4,0,11,10,9,8,7,5,3,1,12,11,10,9,8,6,4,3,2,1,13,12,11,10,9,7,5,4,3,2,14,13,12,11,10,8,6,5,4,3,2,0]),
  ([97,1538,2054], 2, [11,7,12,11,9,8,7,3,2,13,12,11,10,9,8,6,4,3,14,13,12,11,10,9,7,5,4,3,2,0]),
  ([97,1034,2306], 1, [1,2,0,10,6,4,3,1,0,11,8,7,5,4,3,2,1,13,12,10,9,8,7,6,5,4,3,2,1,14,13,11,10,9,8,7,6,5,4,3,2,0]),
  ([14,545,2177], 2, [6,7,8,2,9,7,3,2,12,10,9,8,4,3,2,14,13,11,10,9,7,5,4,3,2,0]),
  ([1057,1154,2308], 2, [1,10,4,2,1,11,10,8,7,5,4,3,2,13,12,11,9,8,7,6,5,4,3,14,13,12,10,9,8,7,6,5,4,2,0]),
  ([1544,2081,2178], 2, [6,4,7,5,8,7,6,9,8,7,10,9,8,4,11,10,9,7,5,12,11,10,8,6,3,2,13,12,11,9,8,7,6,5,4,3,14,13,12,11,10,9,8,7,6,5,4,0]),
  ([14,193,769], 1, [7,8,1,9,2,0,10,7,3,1,0,11,8,7,6,5,4,3,2,1,12,9,8,7,6,5,4,3,2,1,13,12,10,9,8,7,6,5,4,3,2,1,0]),
  ([134,800,1153], 2, [7,8,9,1,10,7,2,11,8,6,5,4,3,2,12,9,8,7,6,5,4,3,13,10,9,8,7,6,5,4,3,2,0]),
  ([518,1537,2240], 2, [5,6,9,8,7,10,9,8,6,4,11,10,9,8,7,5,2,1,12,11,10,9,8,7,6,4,3,2,13,12,11,10,9,8,7,5,4,3,14,13,12,11,10,9,8,7,6,5,4,3,0]),
  ([146,1568,2084], 2, [4,5,6,7,6,5,4,8,7,6,5,9,8,7,6,10,9,8,7,11,10,9,8,6,2,12,11,10,9,8,7,3,2,13,12,11,10,9,8,4,3,14,13,12,11,10,9,8,7,5,4,3,0]),
  ([146,1064,2336], 1, [6,7,4,8,7,5,9,8,6,1,10,9,7,4,2,0,11,10,8,7,5,3,1,12,11,9,8,6,4,2,1,13,12,10,9,7,6,5,4,3,2,14,13,12,11,10,9,8,7,6,5,4,3,2,0]),
  ([1042,1120,2308], 1, [4,5,0,11,9,7,6,3,1,0,12,11,10,8,7,5,4,2,1,13,12,11,10,9,8,6,5,3,2,14,13,12,11,10,9,7,6,4,3,2,1,0]),
  ([1544,2066,2144], 1, [4,5,6,4,7,6,5,4,8,7,6,5,9,8,7,6,1,10,9,8,7,2,0,11,10,9,8,3,1,12,11,10,9,8,7,4,2,1,13,12,11,10,9,8,5,3,2,14,13,12,11,10,9,8,7,6,4,3,0])
]

set_option maxRecDepth 30000 in set_option maxHeartbeats 30000000 in
private theorem enum16_b40_ok :
    (enumGenAux 6 12 (inds b4_0) ((inds b4_0).filter (fun p => p.2 == 4)) 2 3 9 pool16_b40 []).all
      (fun cs => g16Sols.any (fun e => decide (e.1 = cs))) = true ∧
    g16Sols.all (fun e => decide (e.2.1 < 3 ∧ relabel e.2.2 (attach e.1 b4_0) = g16Rep e.2.1)) = true ∧
    pool16_b40.Pairwise (· < ·) ∧
    (inds b4_0).all (fun p => !(2 ≤ p.2 && p.2 < 5) || decide (p.1 ∈ pool16_b40)) = true := by
  decide +kernel


set_option maxRecDepth 16000 in
private theorem g16Sols_edges32 :
    g16Sols.all (fun e => decide (9 ≤ (e.1.map (countBits 12)).sum)) = true := by
  decide +kernel


/- ## 21-vertex 51-edge extensions of g16_0, g16_1, g16_2 -> 4 published codes -/

private abbrev targetCode_0 : List Nat := [229544,82088,12417,17536,16784,2244,4264,680,1092,145,4,17,4,1,3,0,8,4,2,1,0]
private abbrev targetCode_1 : List Nat := [229544,65704,45185,9344,16784,1220,4264,424,1092,81,68,1,4,1,1,2,8,4,2,1,0]
private abbrev targetCode_2 : List Nat := [229544,49320,12417,9344,16784,4292,4264,1192,1092,273,68,17,4,1,1,0,8,4,2,1,0]
private abbrev targetCode_3 : List Nat := [229544,16552,28801,17536,16784,2244,4264,680,1092,17,132,1,4,5,1,4,8,4,2,1,0]
private def targetCodes : List (List Nat) := [targetCode_0, targetCode_1, targetCode_2, targetCode_3]
private def w21_filt_0 : List WeightedRow := [((9361,5),1),((33937,5),1),((8977,5),1),((33553,5),1),((10513,5),3),((35089,5),1),((9745,5),2),((9313,5),2),((10337,5),1),((8993,5),1),((33569,5),3),((10529,5),1),((35105,5),1),((34337,5),1),((35009,5),1),((16526,5),1),((32910,5),2),((33294,5),1),((20494,5),3),((35078,5),1),((22534,5),1),((17546,5),1),((34314,5),1),((21514,5),1),((17554,5),1),((18578,5),2),((4882,5),2),((33554,5),1),((4204,5),1),((32876,5),2),((16588,5),1),((20556,5),1),((4900,5),1),((6436,5),1),((18628,5),2),((5672,5),1),((17608,5),3),((33992,5),1),((21576,5),1),((14608,5),1),((29712,5),1),((13088,5),2),((26816,5),1),((30784,5),1)]
private def tight21_0 : List Nat := [193,262,552,556,774,1128,1217,1544,1546,1554,1576,2148,2241,2308,2310,2322,2340,4358,4648,5138,5160,5216,5224,5634,5640,5648,5650,6162,6180,6240,6244,6402,6404,6418,8385,12384,13344,13376,13408,13824,14400,14432,20498,21520,21522,22544,22546,24592,24720,25616,26640,28672,28688,28736,29696,30720,32865,32897,32913,32914,32961,33030,33320,33810,33832,33857,33888,33889,33896,33921,33936,33938,34306,34312,34322,34834,34852,34881,34884,34912,34913,34916,34945,34946,34948,34960,34962,35074,35076,35090]
set_option maxRecDepth 30000 in set_option maxHeartbeats 30000000 in
private theorem cert21_filt_0 : dualFilterGen 7 4 3 15 4 30 0 g16_0 w21_filt_0 tight21_0 = true ∧ tight21_0.Pairwise (· < ·) := by decide +kernel
private def g21Sols_0 : List (List Nat × List Nat) := [
  ([5138,5216,6404,32897], [0,1,2,4,3,5,4,6,5,7,6,3,8,7,4,9,8,5,10,9,6,11,10,7,12,11,8,13,12,10,9,6,14,13,11,10,9,8,7,3,2,15,14,12,11,10,9,8,4,3,1,16,15,13,12,11,10,9,8,6,5,4,3,2,1,0,17,16,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0,18,17,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,19,18,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2]),
  ([5640,6162,6240,32897], [7,8,9,5,10,6,3,0,11,8,7,4,1,12,9,8,5,2,1,13,10,9,6,3,2,14,11,10,9,7,4,3,0,15,14,12,11,10,8,5,4,1,16,15,13,12,11,9,6,5,2,17,16,14,13,12,10,9,7,6,4,3,18,17,16,15,14,13,12,11,10,8,7,6,5,4,3,0,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,1,0]),
  ([2308,5138,5216,33921], [1,0,2,1,3,2,4,3,5,4,6,5,7,6,8,7,5,3,9,8,6,4,3,10,9,7,5,4,11,10,8,6,5,12,11,9,7,6,5,13,12,10,8,7,6,14,13,11,10,9,8,7,4,2,0,15,14,12,11,10,9,8,5,4,3,1,16,15,14,13,12,11,10,9,6,5,4,2,0,17,16,15,14,13,12,11,10,9,7,6,5,3,2,1,18,17,16,15,14,13,12,11,10,8,7,6,4,3,2,0,19,18,17,16,15,14,13,12,11,9,8,7,5,4,3,1,0]),
  ([2308,29696,33810,33888], [3,0,4,1,12,7,5,2,13,10,8,6,3,2,14,11,9,7,4,3,2,15,13,12,11,10,8,6,5,4,3,1,16,14,13,12,11,10,9,7,6,5,4,3,2,1,17,16,15,14,13,12,11,10,8,7,6,5,4,3,2,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,0,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,2,1,0]),
  ([1544,6162,6240,34945], [7,6,8,7,6,3,0,9,8,7,4,1,10,9,8,5,2,1,11,10,9,6,3,2,12,11,10,7,4,3,13,12,11,8,5,4,1,14,13,12,11,9,8,6,5,2,15,14,13,12,10,9,8,7,6,3,18,16,15,14,13,12,11,10,9,8,7,5,4,3,0,19,17,16,15,14,13,12,11,10,9,8,6,5,4,1]),
  ([1544,30720,34834,34912], [1,0,2,1,3,2,4,3,5,4,6,5,7,6,8,7,9,8,10,9,6,11,10,7,4,12,11,8,5,0,13,12,9,7,6,1,14,13,10,8,7,2,15,14,13,12,11,9,8,3,2,1,16,15,14,13,12,10,9,6,5,4,3,2,0,17,16,15,14,13,11,10,7,6,5,4,3,1,18,17,16,15,14,12,11,8,7,6,5,4,2,1,19,18,17,16,15,14,13,12,10,9,8,7,6,5,3,2,1,0]),
  ([28672,33810,33888,35076], [2,3,0,4,1,5,2,1,6,4,3,2,14,12,11,7,6,5,4,3,15,13,12,8,7,6,5,4,3,2,1,16,15,14,13,9,8,7,6,5,4,3,2,1,17,16,15,14,10,9,8,7,6,5,4,3,2,18,17,16,15,11,10,9,8,7,6,5,4,3,0,19,18,17,16,15,14,12,11,10,9,8,7,6,5,4,3,1,0]),
  ([28672,34312,34834,34912], [1,0,2,1,3,2,4,3,5,4,6,5,7,6,8,7,9,8,10,9,11,10,6,12,11,7,6,0,13,12,8,7,1,14,13,9,8,7,4,2,0,15,14,10,9,8,5,3,1,16,15,11,10,9,6,5,4,2,0,17,16,15,12,11,10,7,6,5,3,1,18,17,16,15,13,12,11,8,7,6,5,4,2,1,0,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0])
]
set_option maxRecDepth 30000 in set_option maxHeartbeats 30000000 in
private theorem enum21_0_ok : (enumGenAux 7 16 (inds g16_0) ((inds g16_0).filter (fun p => p.2 == 5)) 3 4 15 tight21_0 []).all (fun cs => g21Sols_0.any (fun e => decide (e.1 = cs))) = true ∧ g21Sols_0.all (fun e => decide (relabel e.2 (attach e.1 g16_0) ∈ targetCodes)) = true := by decide +kernel
private def w21_filt_1 : List WeightedRow := [((9361,5),6),((10385,5),7),((33553,5),7),((10513,5),7),((9745,5),4),((34321,5),7),((9313,5),11),((10337,5),12),((33569,5),4),((9409,5),4),((35009,5),13),((32910,5),7),((33294,5),6),((20494,5),13),((6278,5),3),((34950,5),3),((17158,5),7),((35078,5),3),((17930,5),12),((6290,5),3),((17170,5),7),((4204,5),3),((32876,5),10),((16940,5),4),((20524,5),4),((4300,5),1),((32972,5),1),((17188,5),6),((6340,5),7),((17960,5),2),((5320,5),10),((33992,5),7),((28944,5),7),((29712,5),4),((25376,5),4),((28960,5),7),((26144,5),1),((14528,5),6)]
private def tight21_1 : List Nat := [146,1128,1162,1170,1569,2148,2308,2340,4164,4172,4242,5138,5152,5160,5216,5250,5258,5266,6162,6180,6212,6278,6404,6418,6432,6436,9760,12432,13344,13376,13408,13440,13456,14624,21522,21536,21544,25632,26112,28672,28688,28704,28928,29696,29728,32914,32968,33281,33297,33313,33316,33320,33537,33572,33810,33824,33825,33832,33888,33889,33922,33938,34305,34322,34336,34337,34344,34852,34884,34916,34950,35073,35074,35076,35090,35104,35105,35108]
set_option maxRecDepth 30000 in set_option maxHeartbeats 30000000 in
private theorem cert21_filt_1 : dualFilterGen 7 4 3 15 14 120 0 g16_1 w21_filt_1 tight21_1 = true ∧ tight21_1.Pairwise (· < ·) := by decide +kernel
private def g21Sols_1 : List (List Nat × List Nat) := [
  ([4242,5152,6436,33281], [4,5,6,7,3,8,4,1,9,5,2,10,6,3,11,7,4,12,9,8,5,13,10,9,7,6,3,14,11,10,8,7,4,15,12,11,10,9,8,5,3,0,16,13,12,11,10,9,6,4,1,0,18,17,14,13,12,11,10,9,7,6,5,4,3,2,1]),
  ([5152,5266,6404,33281], [1,2,0,3,1,4,2,5,3,6,4,7,5,8,6,9,7,3,10,9,8,4,11,10,9,5,12,11,10,6,5,13,12,11,7,6,14,13,12,8,7,6,15,14,13,12,9,8,7,4,16,15,14,13,10,9,8,5,17,16,15,14,13,11,10,9,8,6,5,3,18,17,16,15,14,12,11,10,9,7,6,4,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2]),
  ([4242,5160,6432,33281], [0,1,2,4,3,5,4,6,5,7,6,3,8,7,4,9,8,5,10,9,6,11,10,7,6,5,12,11,8,7,6,3,0,13,12,9,8,7,5,4,1,14,13,10,9,8,6,5,2,0,15,14,12,11,10,9,8,7,6,3,1,16,15,13,12,11,10,9,8,7,6,4,3,2,0,17,16,14,13,12,11,10,9,8,7,6,5,4,3,2,1,18,17,15,14,13,12,11,10,9,8,7,6,5,4,3,2,0,19,18,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1]),
  ([5138,5216,6404,33281], [4,5,6,7,8,9,10,11,12,3,13,10,4,2,14,11,8,5,4,3,1,15,12,11,9,8,6,5,4,2,16,13,12,10,9,7,6,5,4,3,2,18,17,14,13,12,11,10,8,7,6,5,4,3,2,0]),
  ([146,5152,6436,33313], [2,0,3,1,4,2,5,3,6,4,7,5,8,6,3,9,7,4,10,8,5,11,9,6,12,10,8,7,13,11,9,8,5,14,12,10,9,7,6,15,14,13,11,10,8,7,16,15,14,12,11,9,8,4,3,17,16,15,14,13,12,10,9,6,5,4,18,17,16,15,14,13,11,10,8,7,6,5,3,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,0]),
  ([146,2340,5152,34337], [0,1,0,2,1,3,2,1,0,4,3,2,1,0,5,4,3,2,1,6,5,4,3,2,0,7,6,5,4,3,1,8,7,6,5,4,2,9,8,7,6,5,3,2,10,9,8,7,6,4,3,11,10,9,8,7,5,4,12,11,10,9,8,6,5,4,1,13,12,11,10,9,7,6,5,2,14,13,12,11,10,8,7,6,3,0,15,14,13,12,11,9,8,7,6,4,3,1,16,15,14,13,12,10,9,8,7,5,4,2,0,17,16,15,14,13,11,10,9,8,6,5,3,2,1,18,17,16,15,14,12,11,10,9,7,6,5,4,3,2,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2]),
  ([146,2340,29728,33824], [3,2,5,4,3,6,5,4,7,6,5,8,7,6,1,9,8,7,2,10,9,8,7,6,3,2,11,10,9,8,7,4,3,14,12,11,10,9,8,5,4,2,15,13,12,11,10,9,8,6,5,3,17,16,14,13,12,11,10,9,8,7,6,4,2,18,17,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0,19,18,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0]),
  ([146,28704,33824,35108], [0,1,0,2,1,3,2,1,0,4,3,2,1,0,5,4,3,2,1,6,5,4,3,2,0,7,6,5,4,3,1,8,7,6,5,4,2,9,8,7,6,5,3,2,10,9,8,7,6,4,3,11,10,9,8,7,5,4,12,11,10,9,8,6,5,4,1,13,12,11,10,9,7,6,5,2,14,13,12,11,10,8,7,6,3,0,15,14,13,12,11,9,8,7,6,4,3,1,16,15,14,13,12,10,9,8,7,5,4,2,0,17,16,15,14,13,11,10,9,8,6,5,3,2,1,18,17,16,15,14,12,11,10,9,7,6,5,4,3,2,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2]),
  ([146,5160,6432,33313], [7,8,9,5,0,10,6,1,11,8,7,3,2,12,9,8,7,4,3,13,10,9,8,5,4,1,14,11,10,9,8,6,5,2,1,15,14,12,11,10,9,7,6,5,3,2,16,15,13,12,11,10,9,8,7,6,4,3,17,16,14,13,12,11,10,9,8,7,5,4,3,0,18,17,16,15,14,13,12,11,10,9,8,6,5,4,1,0,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1]),
  ([146,2340,21536,33825], [4,5,2,6,3,7,4,1,8,5,2,9,6,3,10,7,4,11,9,8,5,12,10,9,7,6,3,13,11,10,8,7,4,14,12,11,10,9,8,5,3,0,15,13,12,11,10,9,6,4,1,0,18,17,16,14,13,12,11,10,9,7,6,5,4,3,2,1]),
  ([146,2340,13344,34336], [0,1,0,2,1,0,3,2,1,0,4,3,2,1,0,5,4,3,2,1,6,5,4,3,2,0,7,6,5,4,3,1,8,7,6,5,4,2,9,8,7,6,5,3,2,10,9,8,7,6,4,3,11,10,9,8,7,5,4,12,11,10,9,8,6,5,4,1,13,12,11,10,9,7,6,5,2,14,13,12,11,10,8,7,6,3,0,15,14,13,12,11,9,8,7,6,4,3,1,16,15,14,13,12,10,9,8,7,5,4,2,0,17,16,15,14,13,11,10,9,8,6,5,3,2,1,18,17,16,15,14,12,11,10,9,7,6,5,4,3,2,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2]),
  ([146,28704,33832,35104], [3,4,5,7,6,2,8,7,3,9,8,4,1,10,9,5,2,11,10,6,4,3,12,11,8,7,5,4,13,12,11,9,8,6,5,15,14,13,12,10,9,7,6,16,15,14,13,12,11,10,8,7,4,17,16,15,14,13,12,11,9,8,5,0,18,17,16,15,14,13,12,10,9,6,5,2,1,0,19,18,17,16,15,14,13,12,11,10,8,7,6,4,3,2,1]),
  ([2308,5152,5266,34305], [0,1,0,2,1,0,3,2,1,4,3,2,1,0,5,4,3,2,1,0,6,5,4,3,2,1,7,6,5,4,3,2,8,7,6,5,4,3,9,8,7,6,5,4,10,9,8,7,6,5,2,11,10,9,8,7,6,3,12,11,10,9,8,7,5,4,13,12,11,10,9,8,6,5,1,0,14,13,12,11,10,9,7,6,2,1,15,14,13,12,11,10,8,7,4,3,2,0,16,15,14,13,12,11,9,8,6,5,4,3,1,17,16,15,14,13,12,10,9,7,6,5,4,2,1,18,17,16,15,14,13,11,10,8,7,6,5,4,3,2,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,0]),
  ([1170,2308,5152,34337], [1,2,4,3,5,4,6,5,7,6,1,8,7,2,9,8,3,10,9,4,11,10,7,5,3,12,11,8,7,6,4,13,12,9,8,7,5,3,14,13,11,10,9,8,6,4,1,0,18,17,15,14,13,12,11,10,9,7,6,5,4,3,2,1]),
  ([1170,2308,29728,33824], [0,1,2,1,3,2,0,4,3,2,1,0,5,4,3,2,1,0,6,5,4,3,2,1,7,6,5,4,3,2,8,7,6,5,4,3,9,8,7,6,5,4,10,9,8,7,6,5,2,11,10,9,8,7,6,3,12,11,10,9,8,7,5,4,13,12,11,10,9,8,6,5,1,0,14,13,12,11,10,9,7,6,2,1,15,14,13,12,11,10,8,7,4,3,2,0,16,15,14,13,12,11,9,8,6,5,4,3,1,17,16,15,14,13,12,10,9,7,6,5,4,2,1,18,17,16,15,14,13,11,10,8,7,6,5,4,3,2,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,0]),
  ([2308,29696,33824,33938], [0,3,1,4,2,5,3,6,4,7,5,8,6,9,7,3,10,9,8,4,11,10,9,5,12,11,10,6,5,13,12,11,7,6,14,13,12,8,7,6,15,14,13,9,8,7,4,16,15,14,12,10,9,8,5,17,16,15,13,11,10,9,8,6,5,3,18,17,16,14,12,11,10,9,7,6,4,19,18,17,15,13,12,11,10,8,7,6,5,4,3,1,0]),
  ([1170,2308,21536,33825], [3,4,1,5,4,2,6,5,3,7,6,4,1,8,7,5,2,9,8,6,3,10,9,7,6,4,2,11,10,8,7,5,3,14,12,11,9,8,6,5,4,2,15,13,12,10,9,7,6,5,3,17,16,14,13,12,11,10,9,8,7,6,4,2,0,18,17,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0,19,18,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0]),
  ([2308,5138,5216,34305], [4,5,6,7,8,1,9,2,10,3,11,10,4,2,12,11,8,5,4,3,1,13,12,11,9,8,6,5,4,2,14,13,12,10,9,7,6,5,4,3,2,18,15,14,13,12,11,10,8,7,6,5,4,3,2,0]),
  ([1170,2308,13344,34336], [0,1,2,1,0,3,2,1,4,3,2,1,0,5,4,3,2,1,0,6,5,4,3,2,1,7,6,5,4,3,2,8,7,6,5,4,3,9,8,7,6,5,4,10,9,8,7,6,5,2,11,10,9,8,7,6,3,12,11,10,9,8,7,5,4,13,12,11,10,9,8,6,5,1,0,14,13,12,11,10,9,7,6,2,1,15,14,13,12,11,10,8,7,4,3,2,0,16,15,14,13,12,11,9,8,6,5,4,3,1,17,16,15,14,13,12,10,9,7,6,5,4,2,1,18,17,16,15,14,13,11,10,8,7,6,5,4,3,2,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,0]),
  ([2308,29696,33810,33888], [0,1,10,3,2,12,11,4,3,13,12,7,5,4,14,13,12,11,8,6,5,3,2,1,15,14,13,12,9,7,6,5,4,3,2,16,15,14,13,11,10,8,7,6,5,4,3,2,17,16,15,14,12,11,9,8,7,6,5,4,3,1,0,18,17,16,15,13,12,10,9,8,7,6,5,4,2,1,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,3,2,1]),
  ([1170,5152,6404,33313], [1,2,4,3,5,4,6,5,7,6,8,7,2,9,8,3,10,9,4,11,10,7,5,3,12,11,8,7,6,4,13,12,9,8,7,5,3,14,13,11,10,9,8,6,4,1,0,18,15,14,13,12,11,10,9,7,6,5,4,3,2,1]),
  ([2340,4242,5152,34305], [4,1,5,2,6,3,7,4,1,8,5,2,9,6,3,10,7,4,11,9,8,5,12,10,9,7,6,3,13,11,10,8,7,4,14,12,11,10,9,8,5,3,0,15,13,12,11,10,9,6,4,1,0,18,16,14,13,12,11,10,9,7,6,5,4,3,2,1]),
  ([28672,32914,33824,35108], [0,3,1,4,2,5,3,6,4,7,5,8,6,3,9,7,4,10,8,5,11,9,8,6,12,10,9,7,13,11,10,8,5,14,12,11,9,7,6,15,14,13,12,10,8,7,16,15,14,13,11,9,8,4,3,17,16,15,14,12,10,9,6,5,4,0,18,17,16,15,13,11,10,8,7,6,5,3,1,19,18,17,16,14,12,11,9,8,7,6,5,4,3,2,0]),
  ([28672,33824,33938,35076], [1,2,3,4,5,4,6,5,2,7,6,3,8,7,4,9,8,5,2,10,9,6,3,11,10,7,6,4,2,12,11,8,7,5,3,14,13,12,9,8,6,5,4,2,15,14,13,10,9,7,6,5,3,17,16,15,14,12,11,10,9,8,7,6,4,2,0,18,17,16,15,13,12,11,10,9,8,7,6,5,4,3,2,1,0,19,18,17,16,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0]),
  ([1170,28704,33824,35076], [2,3,5,4,1,6,5,2,7,6,3,8,7,4,9,8,5,2,10,9,6,3,11,10,7,6,4,2,12,11,8,7,5,3,14,13,12,9,8,6,5,4,2,15,14,13,10,9,7,6,5,3,17,16,15,14,12,11,10,9,8,7,6,4,2,0,18,17,16,15,13,12,11,10,9,8,7,6,5,4,3,2,1,0,19,18,17,16,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0]),
  ([2340,29696,32914,33824], [2,1,5,3,2,6,4,3,7,5,4,8,6,5,9,7,6,1,10,8,7,2,11,9,8,7,6,3,2,12,10,9,8,7,4,3,14,13,11,10,9,8,5,4,2,15,14,12,11,10,9,8,6,5,3,17,16,15,13,12,11,10,9,8,7,6,4,2,18,17,16,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0,19,18,17,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0]),
  ([28672,32914,33832,35104], [1,2,3,4,5,4,6,5,7,6,8,7,9,8,6,10,9,7,6,1,11,10,8,7,6,2,12,11,9,8,7,4,3,1,14,13,12,10,9,8,5,4,2,15,14,13,11,10,9,8,6,5,3,1,17,16,15,14,12,11,10,9,8,7,6,4,3,2,18,17,16,15,13,12,11,10,9,8,7,6,5,4,3,2,1,19,18,17,16,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0]),
  ([28672,33810,33888,35076], [1,0,2,1,3,2,4,3,5,4,6,5,7,6,8,7,9,8,10,9,11,10,12,11,13,12,14,13,7,2,15,14,9,8,4,3,1,16,15,11,10,9,5,4,2,0,17,16,15,12,11,10,7,6,5,4,3,2,1,18,17,16,15,13,12,11,10,8,7,6,5,4,3,2,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0])
]
set_option maxRecDepth 30000 in set_option maxHeartbeats 30000000 in
private theorem enum21_1_ok : (enumGenAux 7 16 (inds g16_1) ((inds g16_1).filter (fun p => p.2 == 5)) 3 4 15 tight21_1 []).all (fun cs => g21Sols_1.any (fun e => decide (e.1 = cs))) = true ∧ g21Sols_1.all (fun e => decide (relabel e.2 (attach e.1 g16_1) ∈ targetCodes)) = true := by decide +kernel
private def w21_filt_2 : List WeightedRow := [((9361,5),59),((33937,5),118),((10385,5),7),((34961,5),191),((10513,5),111),((35089,5),68),((24849,5),174),((17937,5),70),((34321,5),79),((25617,5),69),((17505,5),85),((17185,5),123),((34337,5),176),((9409,5),7),((10433,5),72),((25665,5),67),((4238,5),75),((32910,5),38),((4622,5),124),((33294,5),48),((34950,5),10),((4870,5),183),((33542,5),11),((6406,5),75),((12426,5),176),((9362,5),24),((33938,5),51),((10386,5),89),((17170,5),15),((33554,5),1),((10514,5),24),((24850,5),99),((17938,5),84),((34322,5),39),((4204,5),63),((4652,5),62),((33324,5),20),((4300,5),73),((32972,5),92),((6244,5),178),((34916,5),99),((4900,5),4),((33572,5),87),((6436,5),109),((35108,5),31),((35012,5),7),((17512,5),6),((20584,5),65),((17960,5),124),((21032,5),4),((9416,5),118),((25672,5),5),((28744,5),91),((21280,5),71),((14528,5),119)]
private def tight21_2 : List Nat := [97,545,801,1121,1217,1569,2145,2193,4868,6432,9226,9281,9354,10497,10514,12416,12418,12424,14464,14466,14594,16481,16914,17448,17512,20520,20576,21000,21002,21250,24641,24850,25672,28672,28674,28680,28736,28928,32865,32910,32964,33030,33294,33313,33542,33569,33802,33832,33930,33938,33985,34314,34322,34344,34834,34916,34962,35009,35074,35078,35090,35105,35108]
set_option maxRecDepth 30000 in set_option maxHeartbeats 30000000 in
private theorem cert21_filt_2 : dualFilterGen 7 4 3 15 198 2310 0 g16_2 w21_filt_2 tight21_2 = true ∧ tight21_2.Pairwise (· < ·) := by decide +kernel
private def g21Sols_2 : List (List Nat × List Nat) := [
  ([97,28674,33802,35074], [1,0,2,1,3,2,4,3,5,4,3,6,5,4,7,6,5,8,7,6,9,8,7,10,9,8,11,10,9,8,7,12,11,10,9,8,0,13,12,11,10,9,1,14,13,12,11,10,2,15,14,13,12,11,3,1,16,15,14,13,12,5,4,3,2,0,17,16,15,14,13,11,10,6,5,4,3,1,18,17,16,15,14,12,11,8,7,6,5,4,2,19,18,17,16,15,14,13,12,9,8,7,6,5,3]),
  ([28672,32865,33802,35074], [1,0,2,1,3,2,4,3,5,4,6,5,7,6,8,7,9,8,10,9,11,10,12,11,4,0,13,12,6,5,1,14,13,9,7,6,2,15,14,10,8,7,6,3,1,16,15,11,10,9,8,7,4,2,1,0,17,16,15,12,11,10,9,8,5,4,3,2,1,18,17,16,13,12,11,10,9,6,5,4,3,2,1,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0])
]
set_option maxRecDepth 30000 in set_option maxHeartbeats 30000000 in
private theorem enum21_2_ok : (enumGenAux 7 16 (inds g16_2) ((inds g16_2).filter (fun p => p.2 == 5)) 3 4 15 tight21_2 []).all (fun cs => g21Sols_2.any (fun e => decide (e.1 = cs))) = true ∧ g21Sols_2.all (fun e => decide (relabel e.2 (attach e.1 g16_2) ∈ targetCodes)) = true := by decide +kernel

/- ## Structural glue: R(3,6)=18, non-neighborhood edge bounds, forcing lemma, and H2 -/

private theorem eighteen_works : RamseyNumbers.IsGraphRamsey 18 3 6 := by
  classical
  rintro G ⟨ht, hc⟩
  have hdeg (v : Fin 18) : 4 ≤ G.degree v ∧ G.degree v ≤ 5 := by
    have hd := OMA.Ramsey37Density.degree_lt G ht hc v
    have hdc := OMA.Ramsey37Density.nonneighbors_lt OMA.Ramsey37Density.fourteen_works G ht hc v
    rw [G.degree_compl, Fintype.card_fin] at hdc
    omega
  by_cases h4 : ∃ v : Fin 18, G.degree v = 4
  · exact no_deg4_18 G ht hc (fun v => (hdeg v).1) h4
  · push Not at h4
    exact OMA.Ramsey36Canonical.regular_impossible G ht
      (fun v => by have := hdeg v; have := h4 v; omega) hc

private theorem induce_edges_eq_encode {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V) (vs : List V) (hnd : vs.Nodup) (hcov : vs.toFinset = B) :
    edges_ (encode G vs) = (G.induce (B : Set V)).edgeFinset.card := by
  classical
  let D := G.induce (B : Set V)
  have hB_deg_eq (x : B) : (B.filter (G.Adj x.1)).card = D.degree x := by
    rw [← D.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
    refine Finset.card_bij (fun y hy => ⟨y, (Finset.mem_filter.mp hy).1⟩) ?_ ?_ ?_
    · intro y hy; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
    · intro _ _ _ _ h; exact congrArg Subtype.val h
    · intro y hy; exact ⟨y.1, Finset.mem_filter.mpr ⟨y.2, (Finset.mem_filter.mp hy).2⟩, rfl⟩
  have hB_sum_deg : ∑ x ∈ B, (B.filter (G.Adj x)).card = 2 * D.edgeFinset.card := by
    calc ∑ x ∈ B, (B.filter (G.Adj x)).card
        = ∑ x : B, (B.filter (G.Adj x.1)).card := (Finset.sum_coe_sort B _).symm
      _ = ∑ x : B, D.degree x := Finset.sum_congr rfl (fun x _ => hB_deg_eq x)
      _ = 2 * D.edgeFinset.card := D.sum_degrees_eq_twice_card_edges
  have dg : degrees (encode G vs) = vs.map (fun x => (B.filter (G.Adj x)).card) := by
    rw [degrees_encode]
    apply List.map_congr_left
    intro x _
    rw [sizeAt_finset G hnd, hcov]
  have hsum_vs := List.sum_toFinset (fun x => (B.filter (G.Adj x)).card) hnd
  rw [hcov, hB_sum_deg] at hsum_vs
  have he := energy (encode G vs)
  rw [dg, ← hsum_vs] at he
  dsimp only [D] at he
  omega

private theorem induce_small_of_nonneighbors {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Nat) (hi : Gᶜ.CliqueFree (K + 1)) (v : V) :
    Small G (Gᶜ.neighborFinset v) K := by
  intro S hSB hSind
  by_contra! hK
  have hvS : v ∉ S := fun hvS => ((Gᶜ.mem_neighborFinset v v).mp (hSB hvS)).1 rfl
  apply hi.mono (show K + 1 ≤ (insert v S).card by rw [Finset.card_insert_of_notMem hvS]; omega) (insert v S)
  refine ⟨?_, rfl⟩
  rw [Finset.coe_insert, SimpleGraph.isClique_insert_of_notMem hvS]
  exact ⟨hSind, fun x hx => (Gᶜ.mem_neighborFinset v x).mp (hSB hx)⟩

private theorem subset_min_deg {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ht : G.CliqueFree 3)
    (B : Finset V) (k m : Nat) (hr : RamseyNumbers.IsGraphRamsey m 3 k)
    (hB : Small G B (k + 1)) (x : V) (hx : x ∈ B) :
    B.card ≤ (B.filter (G.Adj x)).card + m := by
  classical
  by_contra! hlt
  let R := (B.erase x).filter (fun y => ¬ G.Adj x y)
  have hR_card : m ≤ R.card := by
    have h1 : (B.erase x).card + 1 = B.card := Finset.card_erase_add_one hx
    have h2 := Finset.card_filter_add_card_filter_not (s := B.erase x) (p := G.Adj x)
    have h3 : ((B.erase x).filter (G.Adj x)).card ≤ (B.filter (G.Adj x)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset x B))
    change ((B.erase x).filter (G.Adj x)).card + R.card = (B.erase x).card at h2
    omega
  obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset (α := Fin m) (s := R) (by simpa using hR_card)
  let K := G.comap f
  let emb : K ↪g G := SimpleGraph.Embedding.comap f G
  apply hr K
  refine ⟨SimpleGraph.CliqueFree.comap emb.isContained ht, ?_⟩
  intro S hS
  let S' := S.map f
  have hS'R : ∀ y ∈ S', y ∈ R := fun y hy => by
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hy
    exact hf ⟨i, rfl⟩
  have hx_not : x ∉ S' := fun hxS => (Finset.mem_erase.mp (Finset.mem_filter.mp (hS'R x hxS)).1).1 rfl
  have hS'ind : Gᶜ.IsClique (S' : Set V) := by
    intro a ha b hb hne
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hb
    exact (SimpleGraph.Embedding.complEquiv emb).map_adj_iff.mpr
      (hS.isClique hi hj (fun h => hne (congrArg f h)))
  have hins : Gᶜ.IsClique ((insert x S' : Finset V) : Set V) := by
    rw [Finset.coe_insert, SimpleGraph.isClique_insert_of_notMem hx_not]
    refine ⟨hS'ind, fun y hy => ?_⟩
    have hyR := Finset.mem_filter.mp (hS'R y hy)
    exact ⟨(Finset.mem_erase.mp hyR.1).1.symm, hyR.2⟩
  have hsub : insert x S' ⊆ B := Finset.insert_subset hx (fun y hy =>
    Finset.erase_subset x B (Finset.mem_filter.mp (hS'R y hy)).1)
  have hltK := hB (insert x S') hsub hins
  rw [Finset.card_insert_of_notMem hx_not, Finset.card_map, hS.card_eq] at hltK
  omega

private theorem ext_to_gen_mem (K d : Nat) (b cs : List Nat) (h : Extension K d b cs) :
    cs.length = d ∧
    (∀ x ∈ cs, ∃ p ∈ inds b, p.1 = x ∧ d - 1 ≤ p.2 ∧ p.2 < K - 1) ∧
    okContacts K (inds b) cs = true ∧
    cs.Pairwise (· ≤ ·) := by
  obtain ⟨hlen, hmem, hok, hsort⟩ := h
  refine ⟨hlen, fun x hx => ?_, hok, hsort⟩
  have hu := hmem x hx
  unfold usable at hu
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hu
  obtain ⟨hp1, hp2⟩ := List.mem_filter.mp hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp2
  exact ⟨p, hp1, rfl, by omega, by omega⟩

private theorem e36_17_ge_40 {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (B : Finset V) (hBcard : B.card = 17) (hB : Small G B 6) :
    40 ≤ (G.induce (B : Set V)).edgeFinset.card := by
  classical
  by_contra! hlt
  have hmin : ∀ x ∈ B, 3 ≤ (B.filter (G.Adj x)).card := fun x hx => by
    have := subset_min_deg G ht B 5 14 OMA.Ramsey37Density.fourteen_works hB x hx; omega
  have hB_low : B.Nonempty → ∃ x ∈ B, (B.filter (G.Adj x)).card ≤ 4 := by
    intro _
    by_contra! hall5
    have hD : ∑ x ∈ B, (B.filter (G.Adj x)).card = 2 * (G.induce (B : Set V)).edgeFinset.card := by
      let D := G.induce (B : Set V)
      have hdeg (x : B) : (B.filter (G.Adj x.1)).card = D.degree x := by
        rw [← D.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
        refine Finset.card_bij (fun y hy => ⟨y, (Finset.mem_filter.mp hy).1⟩) ?_ ?_ ?_
        · intro y hy; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
        · intro _ _ _ _ h; exact congrArg Subtype.val h
        · intro y hy; exact ⟨y.1, Finset.mem_filter.mpr ⟨y.2, (Finset.mem_filter.mp hy).2⟩, rfl⟩
      calc ∑ x ∈ B, (B.filter (G.Adj x)).card
          = ∑ x : B, (B.filter (G.Adj x.1)).card := (Finset.sum_coe_sort B _).symm
        _ = ∑ x : B, D.degree x := Finset.sum_congr rfl (fun x _ => hdeg x)
        _ = 2 * D.edgeFinset.card := D.sum_degrees_eq_twice_card_edges
    have h85 : 85 ≤ ∑ x ∈ B, (B.filter (G.Adj x)).card := by
      calc 85 = ∑ _x ∈ B, (5 : ℕ) := by rw [Finset.sum_const, smul_eq_mul, hBcard]
        _ ≤ ∑ x ∈ B, (B.filter (G.Adj x)).card := Finset.sum_le_sum (fun x hx => hall5 x hx)
    omega
  have hn (l : List V) := relabel_real G (renumber (encode G l)) l
  obtain ⟨vs, d, b, cs, hnd, hcov, hd4, hb, hcs, henc, ⟨r, hrB, hrd⟩⟩ :=
    rootSplitting G ht normalized hn 5 B (Finset.card_pos.mp (by omega)) 4 hB hB_low
  have hd3 : 3 ≤ d := hrd ▸ hmin r hrB
  have hedges : edges_ (attach cs b) ≤ 39 := by
    rw [← henc, induce_edges_eq_encode G B vs hnd hcov]; omega
  obtain ⟨hlen, hmem, hok, hsort⟩ := ext_to_gen_mem 6 d b cs hcs
  rw [edges_attached, hlen] at hedges
  rcases (show d = 3 ∨ d = 4 by omega) with rfl | rfl
  · have hb' : b ∈ levels normalized 5 13 4 := by simpa [hBcard] using hb
    have ok := of_decide_eq_true (List.all_eq_true.mp smaller3 b hb')
    unfold roots3 at ok
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ok
    subst ok
    have he0 : edges_ b3_0 = 26 := by decide
    have hsum_le : (cs.map (countBits b3_0.length)).sum ≤ 10 := by
      change 3 + (cs.map (countBits b3_0.length)).sum + edges_ b3_0 ≤ 39 at hedges; omega
    exact viaDualGen 6 3 2 10 _ _ _ b3_0 cs w17_40_b3_0 hlen hmem hok hsum_le cert17_40_b3_0
  · have hb' : b ∈ levels normalized 5 12 4 := by simpa [hBcard] using hb
    have ok := of_decide_eq_true (List.all_eq_true.mp smaller4 b hb')
    unfold roots4 at ok
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ok
    rcases ok with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have : edges_ b4_0 = 20 := by decide
      have hsum_le : (cs.map (countBits 12)).sum ≤ 15 := by
        change 4 + (cs.map (countBits 12)).sum + edges_ b4_0 ≤ 39 at hedges; omega
      have hin := enumGenAux_complete 6 12 (inds b4_0) _ (fun p hp => ⟨(List.mem_filter.mp hp).1, Nat.le_of_eq (beq_iff_eq.mp (List.mem_filter.mp hp).2).symm⟩) 3 4 15 pool17_b4_0 [] cs hlen
        (fun x hx => by
          obtain ⟨p, hp, rfl, hp1, hp2⟩ := hmem x hx
          have hp2' : p.2 < 5 := by omega
          have h4 := List.all_eq_true.mp enum17_b4_0_empty.2.2 p hp
          simp [hp1, hp2'] at h4
          exact ⟨h4, by change 3 ≤ countBits b4_0.length p.1; rw [countBits_inds_eq b4_0 p hp]; exact hp1⟩)
        hsort enum17_b4_0_empty.2.1 hsum_le (by simpa using hok)
      simp only [List.reverse_nil, List.nil_append, enum17_b4_0_empty.1] at hin; cases hin
    · have : edges_ b4_1 = 21 := by decide
      have hs : (cs.map (countBits b4_1.length)).sum ≤ 14 := by change 4 + (cs.map (countBits b4_1.length)).sum + edges_ b4_1 ≤ 39 at hedges; omega
      exact viaDualGen 6 4 3 14 _ _ _ b4_1 cs w17_40_b4_1 hlen hmem hok hs cert17_40_b4_1
    · have : edges_ b4_2 = 21 := by decide
      have hs : (cs.map (countBits b4_2.length)).sum ≤ 14 := by change 4 + (cs.map (countBits b4_2.length)).sum + edges_ b4_2 ≤ 39 at hedges; omega
      exact viaDualGen 6 4 3 14 _ _ _ b4_2 cs w17_40_b4_2 hlen hmem hok hs cert17_40_b4_2
    · have : edges_ b4_3 = 22 := by decide
      have hs : (cs.map (countBits b4_3.length)).sum ≤ 13 := by change 4 + (cs.map (countBits b4_3.length)).sum + edges_ b4_3 ≤ 39 at hedges; omega
      exact viaDualGen 6 4 3 13 _ _ _ b4_3 cs w17_40_b4_3 hlen hmem hok hs cert17_40_b4_3
    · have : edges_ b4_4 = 22 := by decide
      have hs : (cs.map (countBits b4_4.length)).sum ≤ 13 := by change 4 + (cs.map (countBits b4_4.length)).sum + edges_ b4_4 ≤ 39 at hedges; omega
      exact viaDualGen 6 4 3 13 _ _ _ b4_4 cs w17_40_b4_4 hlen hmem hok hs cert17_40_b4_4
    · have : edges_ b4_5 = 22 := by decide
      have hs : (cs.map (countBits b4_5.length)).sum ≤ 13 := by change 4 + (cs.map (countBits b4_5.length)).sum + edges_ b4_5 ≤ 39 at hedges; omega
      exact viaDualGen 6 4 3 13 _ _ _ b4_5 cs w17_40_b4_5 hlen hmem hok hs cert17_40_b4_5
    · have : edges_ b4_6 = 22 := by decide
      have hs : (cs.map (countBits b4_6.length)).sum ≤ 13 := by change 4 + (cs.map (countBits b4_6.length)).sum + edges_ b4_6 ≤ 39 at hedges; omega
      exact viaDualGen 6 4 3 13 _ _ _ b4_6 cs w17_40_b4_6 hlen hmem hok hs cert17_40_b4_6
    · have : edges_ b4_7 = 23 := by decide
      have hs : (cs.map (countBits b4_7.length)).sum ≤ 12 := by change 4 + (cs.map (countBits b4_7.length)).sum + edges_ b4_7 ≤ 39 at hedges; omega
      exact viaDualGen 6 4 3 12 _ _ _ b4_7 cs w17_40_b4_7 hlen hmem hok hs cert17_40_b4_7
    · have : edges_ b4_8 = 22 := by decide
      have hs : (cs.map (countBits b4_8.length)).sum ≤ 13 := by change 4 + (cs.map (countBits b4_8.length)).sum + edges_ b4_8 ≤ 39 at hedges; omega
      exact viaDualGen 6 4 3 13 _ _ _ b4_8 cs w17_40_b4_8 hlen hmem hok hs cert17_40_b4_8
    · have : edges_ b4_9 = 23 := by decide
      have hs : (cs.map (countBits b4_9.length)).sum ≤ 12 := by change 4 + (cs.map (countBits b4_9.length)).sum + edges_ b4_9 ≤ 39 at hedges; omega
      exact viaDualGen 6 4 3 12 _ _ _ b4_9 cs w17_40_b4_9 hlen hmem hok hs cert17_40_b4_9
    · have : edges_ b4_10 = 24 := by decide
      have hs : (cs.map (countBits b4_10.length)).sum ≤ 11 := by change 4 + (cs.map (countBits b4_10.length)).sum + edges_ b4_10 ≤ 39 at hedges; omega
      exact viaDualGen 6 4 3 11 _ _ _ b4_10 cs w17_40_b4_10 hlen hmem hok hs cert17_40_b4_10
    · have : edges_ b4_11 = 24 := by decide
      have hs : (cs.map (countBits b4_11.length)).sum ≤ 11 := by change 4 + (cs.map (countBits b4_11.length)).sum + edges_ b4_11 ≤ 39 at hedges; omega
      exact viaDualGen 6 4 3 11 _ _ _ b4_11 cs w17_40_b4_11 hlen hmem hok hs cert17_40_b4_11

private theorem root_split_relabel11 {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (B : Finset V) (hB : Small G B 6)
    (d : Nat) (hBsize : B.card = 12 + d)
    (r : V) (hrB : r ∈ B) (hmin : ∀ x ∈ B, d ≤ (B.filter (G.Adj x)).card)
    (hrd : (B.filter (G.Adj r)).card = d)
    (hrem16 : (G.induce ((B \ insert r (B.filter (G.Adj r)) : Finset V) : Set V)).edgeFinset.card ≤ 16) :
    ∃ (idx : Nat), idx < 7 ∧ ∃ (vs11 : List V), vs11.Nodup ∧
      vs11.toFinset = B \ insert r (B.filter (G.Adj r)) ∧ encode G vs11 = g11Rep idx := by
  classical
  let N := B.filter (G.Adj r)
  let B1 := B \ insert r N
  have hrN : r ∉ N := by simp [N]
  have hB1card : B1.card = 11 := by
    have h1 := Finset.card_sdiff_add_card_eq_card (Finset.insert_subset hrB (Finset.filter_subset (G.Adj r) B))
    change B1.card + (insert r N).card = B.card at h1
    rw [Finset.card_insert_of_notMem hrN] at h1
    dsimp only [N] at h1
    omega
  have hB1_small : Small G B1 5 := by
    intro S hS hI
    have hrS : r ∉ S := fun h => by have := Finset.mem_sdiff.mp (hS h); simp at this
    have hind : Gᶜ.IsClique (insert r S : Finset V) := by
      rw [Finset.coe_insert, SimpleGraph.isClique_insert_of_notMem hrS]
      refine ⟨hI, fun x hx => ?_⟩
      have hx1 := Finset.mem_sdiff.mp (hS hx)
      exact ⟨fun e => hrS (e ▸ hx), fun ha => hx1.2 (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hx1.1, ha⟩))⟩
    have hlt := hB (insert r S) (Finset.insert_subset hrB (hS.trans Finset.sdiff_subset)) hind
    rw [Finset.card_insert_of_notMem hrS] at hlt
    omega
  have hn (l : List V) := relabel_real G (renumber (encode G l)) l
  obtain ⟨base, hbn, hbcov, hbcls⟩ := levels_complete G ht normalized hn 5 B1 4 hB1_small (by
    rintro ⟨x, hx⟩
    have mm := hB1_small (B1.filter (G.Adj x)) (Finset.filter_subset (G.Adj x) B1) (neighbors_small G ht B1 x)
    exact ⟨x, hx, by omega⟩)
  rw [hB1card] at hbcls
  have hed : edges_ (encode G base) ≤ 16 := by
    rw [induce_edges_eq_encode G B1 base hbn hbcov]; exact hrem16
  obtain ⟨idx, hidx, vs11, hperm, henc⟩ := l11_to_rep G base hbcls hed
  exact ⟨idx, hidx, vs11, hperm.nodup_iff.mpr hbn, by change vs11.toFinset = B1; rw [← hbcov]; ext x; simp [hperm.mem_iff], henc⟩

private theorem e35_12_ge_20 {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (B : Finset V) (hBcard : B.card = 12) (hB : Small G B 5) :
    20 ≤ (G.induce (B : Set V)).edgeFinset.card := by
  classical
  have hn (l : List V) := relabel_real G (renumber (encode G l)) l
  obtain ⟨vs, hnd, hcov, hcls⟩ := levels_complete G ht normalized hn 5 B 4 hB (by
    rintro ⟨x, hx⟩
    have mm := hB (B.filter (G.Adj x)) (Finset.filter_subset ..) (neighbors_small G ht B x)
    exact ⟨x, hx, by omega⟩)
  rw [hBcard] at hcls
  have ok := of_decide_eq_true (List.all_eq_true.mp smaller4 (encode G vs) hcls)
  rw [← induce_edges_eq_encode G B vs hnd hcov]
  simp only [roots4, List.mem_cons, List.not_mem_nil, or_false] at ok
  rcases ok with h | h | h | h | h | h | h | h | h | h | h | h <;> (rw [h]; decide)

private theorem e35_13_ge_26 {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (B : Finset V) (hBcard : B.card = 13) (hB : Small G B 5) :
    26 ≤ (G.induce (B : Set V)).edgeFinset.card := by
  classical
  have hn (l : List V) := relabel_real G (renumber (encode G l)) l
  obtain ⟨vs, hnd, hcov, hcls⟩ := levels_complete G ht normalized hn 5 B 4 hB (by
    rintro ⟨x, hx⟩
    have mm := hB (B.filter (G.Adj x)) (Finset.filter_subset ..) (neighbors_small G ht B x)
    exact ⟨x, hx, by omega⟩)
  rw [hBcard] at hcls
  have ok := of_decide_eq_true (List.all_eq_true.mp smaller3 (encode G vs) hcls)
  rw [← induce_edges_eq_encode G B vs hnd hcov]
  simp only [roots3, List.mem_cons, List.not_mem_nil, or_false] at ok
  rw [ok]; decide

private theorem removed_subset {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ht : G.CliqueFree 3)
    (B : Finset V) (r : V) (hr : r ∈ B) :
    (G.induce ((B \ insert r (B.filter (G.Adj r)) : Finset V) : Set V)).edgeFinset.card +
      ∑ u ∈ B.filter (G.Adj r), (B.filter (G.Adj u)).card ≤
      (G.induce (B : Set V)).edgeFinset.card := by
  classical
  let D := G.induce (B : Set V)
  let N := B.filter (G.Adj r)
  let B1 := B \ insert r N
  let emb : B1 ↪ B := ⟨fun x => ⟨x.1, (Finset.mem_sdiff.mp x.2).1⟩,
    fun _ _ h => Subtype.ext (by simpa using congrArg Subtype.val h)⟩
  let eMap : Sym2 B1 ↪ Sym2 B := ⟨Sym2.map emb, Sym2.map.injective emb.injective⟩
  let E1 : Finset (Sym2 B) := (G.induce (B1 : Set V)).edgeFinset.map eMap
  let EN (u : V) : Finset (Sym2 B) := if h : u ∈ B then D.incidenceFinset ⟨u, h⟩ else ∅
  have hE1_card : E1.card = (G.induce (B1 : Set V)).edgeFinset.card := Finset.card_map _
  have hE1_sub : E1 ⊆ D.edgeFinset := by
    intro e he
    obtain ⟨e', he', rfl⟩ := Finset.mem_map.mp he
    refine Sym2.inductionOn e' (fun x y hxy => ?_) he'
    simp only [SimpleGraph.mem_edgeFinset, eMap, Function.Embedding.coeFn_mk, Sym2.map_pair_eq] at hxy ⊢
    exact hxy
  have hEN_sub (u : V) : EN u ⊆ D.edgeFinset := by
    intro e he
    by_cases hu : u ∈ B
    · simp only [EN, dif_pos hu, SimpleGraph.mem_incidenceFinset] at he
      exact (SimpleGraph.mem_edgeFinset).mpr he.1
    · simp [EN, dif_neg hu] at he
  have hEN_card (u : V) (hu : u ∈ N) : (EN u).card = (B.filter (G.Adj u)).card := by
    have huB : u ∈ B := (Finset.mem_filter.mp hu).1
    simp only [EN, dif_pos huB, D.card_incidenceFinset_eq_degree]
    rw [← D.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
    refine Finset.card_bij (fun y _ => y.1) ?_ ?_ ?_
    · intro y hy; exact Finset.mem_filter.mpr ⟨y.2, (Finset.mem_filter.mp hy).2⟩
    · intro _ _ _ _ h; exact Subtype.ext h
    · intro y hy; exact ⟨⟨y, (Finset.mem_filter.mp hy).1⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩, rfl⟩
  have hEN_disj : (N : Set V).PairwiseDisjoint EN := by
    intro u hu v hv huv
    refine Finset.disjoint_left.mpr fun e heu hev => ?_
    have huB : u ∈ B := (Finset.mem_filter.mp hu).1
    have hvB : v ∈ B := (Finset.mem_filter.mp hv).1
    have hru : G.Adj r u := (Finset.mem_filter.mp hu).2
    have hrv : G.Adj r v := (Finset.mem_filter.mp hv).2
    simp only [EN, dif_pos huB, dif_pos hvB, SimpleGraph.mem_incidenceFinset] at heu hev
    refine Sym2.inductionOn e (fun a b hab => ?_) heu.1 heu.2 hev.2
    intro ha hb
    have hau : a.1 = u ∨ b.1 = u := by
      simp only [Sym2.mem_iff] at ha; rcases ha with h | h <;> [exact Or.inl (congrArg Subtype.val h).symm; exact Or.inr (congrArg Subtype.val h).symm]
    have hbv : a.1 = v ∨ b.1 = v := by
      simp only [Sym2.mem_iff] at hb; rcases hb with h | h <;> [exact Or.inl (congrArg Subtype.val h).symm; exact Or.inr (congrArg Subtype.val h).symm]
    have hadj_uv : G.Adj u v := by
      change G.Adj a.1 b.1 at hab
      rcases hau with h1 | h1 <;> rcases hbv with h2 | h2
      · exact absurd (h1.symm.trans h2) huv
      · rw [← h1, ← h2]; exact hab
      · rw [← h1, ← h2]; exact hab.symm
      · exact absurd (h1.symm.trans h2) huv
    exact ht {r, u, v} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hru, hrv, hadj_uv⟩)
  have hE1_EN_disj : Disjoint E1 (N.biUnion EN) := by
    refine Finset.disjoint_left.mpr fun e he1 he2 => ?_
    obtain ⟨u, huN, heu⟩ := Finset.mem_biUnion.mp he2
    have huB : u ∈ B := (Finset.mem_filter.mp huN).1
    simp only [EN, dif_pos huB, SimpleGraph.mem_incidenceFinset] at heu
    obtain ⟨e', _, rfl⟩ := Finset.mem_map.mp he1
    refine Sym2.inductionOn e' (fun x y hmem => ?_) heu.2
    simp only [eMap, Function.Embedding.coeFn_mk, Sym2.map_pair_eq, Sym2.mem_iff] at hmem
    have huB1 : u ∈ B1 := by
      rcases hmem with h | h
      · have hv : u = x.1 := congrArg Subtype.val h
        rw [hv]; exact x.2
      · have hv : u = y.1 := congrArg Subtype.val h
        rw [hv]; exact y.2
    exact (Finset.mem_sdiff.mp huB1).2 (Finset.mem_insert_of_mem huN)
  have hsub_tot : E1 ∪ N.biUnion EN ⊆ D.edgeFinset :=
    Finset.union_subset hE1_sub (Finset.biUnion_subset.mpr fun u _ => hEN_sub u)
  have hle := Finset.card_le_card hsub_tot
  rw [Finset.card_union_of_disjoint hE1_EN_disj, hE1_card, Finset.card_biUnion hEN_disj,
    Finset.sum_congr rfl (fun u hu => hEN_card u hu)] at hle
  exact hle

private theorem e36_14_unique_and_kill (G : SimpleGraph (Fin 21)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree 7) (h51 : G.edgeFinset.card = 51)
    (hmin3 : ∀ u : Fin 21, 3 ≤ G.degree u)
    (w : Fin 21) (hw : G.degree w = 6) :
    21 ≤ (G.induce ((Gᶜ.neighborFinset w : Finset (Fin 21)) : Set (Fin 21))).edgeFinset.card := by
  classical
  set B := Gᶜ.neighborFinset w
  have hBcard : B.card = 14 := by
    have hc := G.degree_compl w; rw [Fintype.card_fin] at hc; change Gᶜ.degree w = 14; omega
  have hBsmall : Small G B 6 := induce_small_of_nonneighbors G 6 hi w
  by_contra! hlt
  have hD_le20 : (G.induce (B : Set (Fin 21))).edgeFinset.card ≤ 20 := by omega
  obtain ⟨r, hrB, hmin⟩ := B.exists_min_image (fun x => (B.filter (G.Adj x)).card) (Finset.card_pos.mp (by omega))
  set d := (B.filter (G.Adj r)).card with hd_def
  have hd_le2 : d ≤ 2 := by
    by_contra! hge3
    set D := G.induce (B : Set (Fin 21))
    have hdeg (x : B) : (B.filter (G.Adj x.1)).card = D.degree x := by
      rw [← D.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
      refine Finset.card_bij (fun y hy => ⟨y, (Finset.mem_filter.mp hy).1⟩) ?_ ?_ ?_
      · intro y hy; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
      · intro _ _ _ _ h; exact congrArg Subtype.val h
      · intro y hy; exact ⟨y.1, Finset.mem_filter.mpr ⟨y.2, (Finset.mem_filter.mp hy).2⟩, rfl⟩
    have hsum : ∑ x ∈ B, (B.filter (G.Adj x)).card = 2 * D.edgeFinset.card := by
      calc ∑ x ∈ B, (B.filter (G.Adj x)).card
          = ∑ x : B, (B.filter (G.Adj x.1)).card := (Finset.sum_coe_sort B _).symm
        _ = ∑ x : B, D.degree x := Finset.sum_congr rfl (fun x _ => hdeg x)
        _ = 2 * D.edgeFinset.card := D.sum_degrees_eq_twice_card_edges
    have h42 : 42 ≤ ∑ x ∈ B, (B.filter (G.Adj x)).card := by
      calc 42 = ∑ _x ∈ B, (3 : ℕ) := by rw [Finset.sum_const, smul_eq_mul, hBcard]
        _ ≤ ∑ x ∈ B, (B.filter (G.Adj x)).card := Finset.sum_le_sum (fun x hx => by have := hmin x hx; omega)
    dsimp only [D] at hsum
    omega
  have hrem := removed_subset G ht B r hrB
  set N := B.filter (G.Adj r)
  set B1 := B \ insert r N
  change (G.induce (B1 : Set (Fin 21))).edgeFinset.card + ∑ u ∈ N, (B.filter (G.Adj u)).card ≤ (G.induce (B : Set (Fin 21))).edgeFinset.card at hrem
  have hrN : r ∉ N := by simp [N]
  have hB1card : B1.card = 13 - d := by
    have h1 := Finset.card_sdiff_add_card_eq_card (Finset.insert_subset hrB (Finset.filter_subset (G.Adj r) B))
    change B1.card + (insert r N).card = B.card at h1
    rw [Finset.card_insert_of_notMem hrN] at h1
    dsimp only [N] at h1; omega
  have hB1small : Small G B1 5 := by
    intro S hS hI
    have hrS : r ∉ S := fun h => by have := Finset.mem_sdiff.mp (hS h); simp at this
    have hind : Gᶜ.IsClique (insert r S : Finset (Fin 21)) := by
      rw [Finset.coe_insert, SimpleGraph.isClique_insert_of_notMem hrS]
      refine ⟨hI, fun x hx => ?_⟩
      have hx1 := Finset.mem_sdiff.mp (hS hx)
      exact ⟨fun e => hrS (e ▸ hx), fun ha => hx1.2 (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hx1.1, ha⟩))⟩
    have hlt' := hBsmall (insert r S) (Finset.insert_subset hrB (hS.trans Finset.sdiff_subset)) hind
    rw [Finset.card_insert_of_notMem hrS] at hlt'; omega
  have hsumN : d * d ≤ ∑ u ∈ N, (B.filter (G.Adj u)).card := by
    calc d * d = ∑ _u ∈ N, d := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ u ∈ N, (B.filter (G.Adj u)).card := Finset.sum_le_sum (fun u hu => hmin u (Finset.mem_filter.mp hu).1)
  rcases (show d = 0 ∨ d = 1 ∨ d = 2 by omega) with hd0 | hd1 | hd2
  · have := e35_13_ge_26 G ht B1 (by omega) hB1small; omega
  · rw [hd1] at hsumN; have := e35_12_ge_20 G ht B1 (by omega) hB1small; omega
  · rw [hd2] at hsumN
    have hB1_le16 : (G.induce (B1 : Set (Fin 21))).edgeFinset.card ≤ 16 := by omega
    obtain ⟨idx, hidx, vs11, hvs11_nd, hvs11_cov, hvs11_enc⟩ :=
      root_split_relabel11 G ht B hBsmall 2 (by omega) r hrB (fun x hx => hd2 ▸ hmin x hx) hd2 hB1_le16
    obtain ⟨front, cs, hnd14, hcov14, henc14, hlen, hmem, hok, hsort, hedges⟩ :=
      ext_on_subset G ht B 6 hBsmall r hrB 2 1 hd2 (fun u hu => by have := hmin u (Finset.mem_filter.mp hu).1; omega)
        vs11 hvs11_nd hvs11_cov (g11Rep idx) hvs11_enc
    have hed20 : edges_ (attach cs (g11Rep idx)) ≤ 20 := by
      rw [← henc14, induce_edges_eq_encode G B _ hnd14 hcov14]; exact hD_le20
    have htop_sub (g : List Nat) : ∀ p ∈ (inds g).filter (fun p => p.2 == 4), p ∈ inds g ∧ 4 ≤ p.2 :=
      fun p hp => ⟨(List.mem_filter.mp hp).1, by have := (List.mem_filter.mp hp).2; simp only [beq_iff_eq] at this; omega⟩
    have hvs_g14 : ∃ vs14 : List (Fin 21), vs14.Nodup ∧ vs14.toFinset = B ∧ encode G vs14 = g14_20 := by
      have hidx_cases : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨ idx = 6 := by omega
      rcases hidx_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [show g11Rep 0 = g11_0 from rfl] at hmem hok hedges hed20
        have he : edges_ g11_0 = 16 := by decide
        have hin := enumGenAux_complete 6 11 (inds g11_0) _ (htop_sub g11_0) 1 2 2 pool14_0 [] cs hlen
          (fun x hx => by
            obtain ⟨p, hp, rfl, hp1, hp2⟩ := hmem x hx
            have hp2' : p.2 < 5 := by omega
            have h4 := List.all_eq_true.mp enum14_0_empty.2.2 p hp
            simp [hp1, hp2'] at h4
            exact ⟨h4, by change 1 ≤ countBits g11_0.length p.1; rw [countBits_inds_eq g11_0 p hp]; exact hp1⟩)
          hsort enum14_0_empty.2.1 (by change (cs.map (countBits g11_0.length)).sum ≤ 2; omega) (by simpa using hok)
        simp only [List.reverse_nil, List.nil_append, enum14_0_empty.1] at hin; cases hin
      · rw [show g11Rep 1 = g11_1 from rfl] at hmem hok hedges hed20 henc14
        have he : edges_ g11_1 = 15 := by decide
        have hin := enumGenAux_complete 6 11 (inds g11_1) _ (htop_sub g11_1) 1 2 3 pool14_1 [] cs hlen
          (fun x hx => by
            obtain ⟨p, hp, rfl, hp1, hp2⟩ := hmem x hx
            have hp2' : p.2 < 5 := by omega
            have h4 := List.all_eq_true.mp enum14_1_ok.2.2.2 p hp
            simp [hp1, hp2'] at h4
            exact ⟨h4, by change 1 ≤ countBits g11_1.length p.1; rw [countBits_inds_eq g11_1 p hp]; exact hp1⟩)
          hsort enum14_1_ok.2.2.1 (by change (cs.map (countBits g11_1.length)).sum ≤ 3; omega) (by simpa using hok)
        simp only [List.reverse_nil, List.nil_append] at hin
        have hany := List.all_eq_true.mp enum14_1_ok.1 cs hin
        obtain ⟨e, he_in, he_eq⟩ := List.any_eq_true.mp hany
        have he1 : e.1 = cs := of_decide_eq_true he_eq
        have hrel := of_decide_eq_true (List.all_eq_true.mp enum14_1_ok.2.1 e he_in)
        obtain ⟨vs14, hperm, henc'⟩ := relabel_real G e.2 (r :: front ++ vs11)
        rw [henc14, ← he1] at henc'
        change encode G vs14 = relabel e.2 (attach e.1 g11_1) at henc'
        rw [hrel] at henc'
        exact ⟨vs14, hperm.nodup_iff.mpr hnd14, by rw [← hcov14]; ext x; simp [hperm.mem_iff], henc'⟩
      · rw [show g11Rep 2 = g11_2 from rfl] at hmem hok hedges hed20
        have he : edges_ g11_2 = 16 := by decide
        have hin := enumGenAux_complete 6 11 (inds g11_2) _ (htop_sub g11_2) 1 2 2 pool14_2 [] cs hlen
          (fun x hx => by
            obtain ⟨p, hp, rfl, hp1, hp2⟩ := hmem x hx
            have hp2' : p.2 < 5 := by omega
            have h4 := List.all_eq_true.mp enum14_2_empty.2.2 p hp
            simp [hp1, hp2'] at h4
            exact ⟨h4, by change 1 ≤ countBits g11_2.length p.1; rw [countBits_inds_eq g11_2 p hp]; exact hp1⟩)
          hsort enum14_2_empty.2.1 (by change (cs.map (countBits g11_2.length)).sum ≤ 2; omega) (by simpa using hok)
        simp only [List.reverse_nil, List.nil_append, enum14_2_empty.1] at hin; cases hin
      · rw [show g11Rep 3 = g11_3 from rfl] at hmem hok hedges hed20
        have he : edges_ g11_3 = 16 := by decide
        have hin := enumGenAux_complete 6 11 (inds g11_3) _ (htop_sub g11_3) 1 2 2 pool14_3 [] cs hlen
          (fun x hx => by
            obtain ⟨p, hp, rfl, hp1, hp2⟩ := hmem x hx
            have hp2' : p.2 < 5 := by omega
            have h4 := List.all_eq_true.mp enum14_3_empty.2.2 p hp
            simp [hp1, hp2'] at h4
            exact ⟨h4, by change 1 ≤ countBits g11_3.length p.1; rw [countBits_inds_eq g11_3 p hp]; exact hp1⟩)
          hsort enum14_3_empty.2.1 (by change (cs.map (countBits g11_3.length)).sum ≤ 2; omega) (by simpa using hok)
        simp only [List.reverse_nil, List.nil_append, enum14_3_empty.1] at hin; cases hin
      · rw [show g11Rep 4 = g11_4 from rfl] at hmem hok hedges hed20
        have he : edges_ g11_4 = 16 := by decide
        have hin := enumGenAux_complete 6 11 (inds g11_4) _ (htop_sub g11_4) 1 2 2 pool14_4 [] cs hlen
          (fun x hx => by
            obtain ⟨p, hp, rfl, hp1, hp2⟩ := hmem x hx
            have hp2' : p.2 < 5 := by omega
            have h4 := List.all_eq_true.mp enum14_4_empty.2.2 p hp
            simp [hp1, hp2'] at h4
            exact ⟨h4, by change 1 ≤ countBits g11_4.length p.1; rw [countBits_inds_eq g11_4 p hp]; exact hp1⟩)
          hsort enum14_4_empty.2.1 (by change (cs.map (countBits g11_4.length)).sum ≤ 2; omega) (by simpa using hok)
        simp only [List.reverse_nil, List.nil_append, enum14_4_empty.1] at hin; cases hin
      · rw [show g11Rep 5 = g11_5 from rfl] at hmem hok hedges hed20
        have he : edges_ g11_5 = 16 := by decide
        have hin := enumGenAux_complete 6 11 (inds g11_5) _ (htop_sub g11_5) 1 2 2 pool14_5 [] cs hlen
          (fun x hx => by
            obtain ⟨p, hp, rfl, hp1, hp2⟩ := hmem x hx
            have hp2' : p.2 < 5 := by omega
            have h4 := List.all_eq_true.mp enum14_5_empty.2.2 p hp
            simp [hp1, hp2'] at h4
            exact ⟨h4, by change 1 ≤ countBits g11_5.length p.1; rw [countBits_inds_eq g11_5 p hp]; exact hp1⟩)
          hsort enum14_5_empty.2.1 (by change (cs.map (countBits g11_5.length)).sum ≤ 2; omega) (by simpa using hok)
        simp only [List.reverse_nil, List.nil_append, enum14_5_empty.1] at hin; cases hin
      · rw [show g11Rep 6 = g11_6 from rfl] at hmem hok hedges hed20
        have he : edges_ g11_6 = 16 := by decide
        have hin := enumGenAux_complete 6 11 (inds g11_6) _ (htop_sub g11_6) 1 2 2 pool14_6 [] cs hlen
          (fun x hx => by
            obtain ⟨p, hp, rfl, hp1, hp2⟩ := hmem x hx
            have hp2' : p.2 < 5 := by omega
            have h4 := List.all_eq_true.mp enum14_6_empty.2.2 p hp
            simp [hp1, hp2'] at h4
            exact ⟨h4, by change 1 ≤ countBits g11_6.length p.1; rw [countBits_inds_eq g11_6 p hp]; exact hp1⟩)
          hsort enum14_6_empty.2.1 (by change (cs.map (countBits g11_6.length)).sum ≤ 2; omega) (by simpa using hok)
        simp only [List.reverse_nil, List.nil_append, enum14_6_empty.1] at hin; cases hin
    -- Now kill extending g14_20 by w (deg 6) to 21 vertices with 51 edges!
    obtain ⟨vs14, hnd14', hcov14', henc14'⟩ := hvs_g14
    have hrem_w := RamseyDeficiency.removed G ht w
    dsimp only at hrem_w
    rw [h51] at hrem_w
    change (G.induce (B : Set (Fin 21))).edgeFinset.card + ∑ u ∈ G.neighborFinset w, G.degree u ≤ 51 at hrem_w
    have hed_g14 : (G.induce (B : Set (Fin 21))).edgeFinset.card = 20 := by
      rw [← induce_edges_eq_encode G B vs14 hnd14' hcov14', henc14']; decide
    obtain ⟨_, cs6, _, _, _, _, _, hlen6, hmem6, hok6, _, hsum6⟩ :=
      ext_on_rep G ht 7 hi w 6 2 hw (fun u _ => hmin3 u) vs14 hnd14' hcov14' g14_20 henc14'
    have hbud : (cs6.map (countBits g14_20.length)).sum ≤ 25 := by omega
    exact viaDualGen 7 6 2 25 _ _ _ g14_20 cs6 w14_to_21 hlen6 hmem6 hok6 hbud cert14_to_21

private theorem e36_15_unique_and_kill (G : SimpleGraph (Fin 21)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree 7) (h51 : G.edgeFinset.card = 51)
    (hmin3 : ∀ u : Fin 21, 3 ≤ G.degree u)
    (w : Fin 21) (hw : G.degree w = 5) :
    26 ≤ (G.induce ((Gᶜ.neighborFinset w : Finset (Fin 21)) : Set (Fin 21))).edgeFinset.card := by
  classical
  set B := Gᶜ.neighborFinset w
  have hBcard : B.card = 15 := by
    have hc := G.degree_compl w; rw [Fintype.card_fin] at hc; change Gᶜ.degree w = 15; omega
  have hBsmall : Small G B 6 := induce_small_of_nonneighbors G 6 hi w
  by_contra! hlt
  have hD_le25 : (G.induce (B : Set (Fin 21))).edgeFinset.card ≤ 25 := by omega
  obtain ⟨r, hrB, hmin⟩ := B.exists_min_image (fun x => (B.filter (G.Adj x)).card) (Finset.card_pos.mp (by omega))
  set d := (B.filter (G.Adj r)).card with hd_def
  have hd_ge1 : 1 ≤ d := by
    have := subset_min_deg G ht B 5 14 OMA.Ramsey37Density.fourteen_works hBsmall r hrB; omega
  have hd_le3 : d ≤ 3 := by
    by_contra! hge4
    set D := G.induce (B : Set (Fin 21))
    have hdeg (x : B) : (B.filter (G.Adj x.1)).card = D.degree x := by
      rw [← D.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
      refine Finset.card_bij (fun y hy => ⟨y, (Finset.mem_filter.mp hy).1⟩) ?_ ?_ ?_
      · intro y hy; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
      · intro _ _ _ _ h; exact congrArg Subtype.val h
      · intro y hy; exact ⟨y.1, Finset.mem_filter.mpr ⟨y.2, (Finset.mem_filter.mp hy).2⟩, rfl⟩
    have hsum : ∑ x ∈ B, (B.filter (G.Adj x)).card = 2 * D.edgeFinset.card := by
      calc ∑ x ∈ B, (B.filter (G.Adj x)).card
          = ∑ x : B, (B.filter (G.Adj x.1)).card := (Finset.sum_coe_sort B _).symm
        _ = ∑ x : B, D.degree x := Finset.sum_congr rfl (fun x _ => hdeg x)
        _ = 2 * D.edgeFinset.card := D.sum_degrees_eq_twice_card_edges
    have h60 : 60 ≤ ∑ x ∈ B, (B.filter (G.Adj x)).card := by
      calc 60 = ∑ _x ∈ B, (4 : ℕ) := by rw [Finset.sum_const, smul_eq_mul, hBcard]
        _ ≤ ∑ x ∈ B, (B.filter (G.Adj x)).card := Finset.sum_le_sum (fun x hx => by have := hmin x hx; omega)
    dsimp only [D] at hsum
    omega
  have hrem := removed_subset G ht B r hrB
  set N := B.filter (G.Adj r)
  set B1 := B \ insert r N
  change (G.induce (B1 : Set (Fin 21))).edgeFinset.card + ∑ u ∈ N, (B.filter (G.Adj u)).card ≤ (G.induce (B : Set (Fin 21))).edgeFinset.card at hrem
  have hrN : r ∉ N := by simp [N]
  have hB1card : B1.card = 14 - d := by
    have h1 := Finset.card_sdiff_add_card_eq_card (Finset.insert_subset hrB (Finset.filter_subset (G.Adj r) B))
    change B1.card + (insert r N).card = B.card at h1
    rw [Finset.card_insert_of_notMem hrN] at h1
    dsimp only [N] at h1; omega
  have hB1small : Small G B1 5 := by
    intro S hS hI
    have hrS : r ∉ S := fun h => by have := Finset.mem_sdiff.mp (hS h); simp at this
    have hind : Gᶜ.IsClique (insert r S : Finset (Fin 21)) := by
      rw [Finset.coe_insert, SimpleGraph.isClique_insert_of_notMem hrS]
      refine ⟨hI, fun x hx => ?_⟩
      have hx1 := Finset.mem_sdiff.mp (hS hx)
      exact ⟨fun e => hrS (e ▸ hx), fun ha => hx1.2 (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hx1.1, ha⟩))⟩
    have hlt' := hBsmall (insert r S) (Finset.insert_subset hrB (hS.trans Finset.sdiff_subset)) hind
    rw [Finset.card_insert_of_notMem hrS] at hlt'; omega
  have hsumN : d * d ≤ ∑ u ∈ N, (B.filter (G.Adj u)).card := by
    calc d * d = ∑ _u ∈ N, d := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ u ∈ N, (B.filter (G.Adj u)).card := Finset.sum_le_sum (fun u hu => hmin u (Finset.mem_filter.mp hu).1)
  rcases (show d = 1 ∨ d = 2 ∨ d = 3 by omega) with hd1 | hd2 | hd3
  · have := e35_13_ge_26 G ht B1 (by omega) hB1small; omega
  · -- d = 2: B1 has 12 vertices -> b4_0..b4_11 -> 10 duals + b4_10/11 trivial!
    have hn (l : List (Fin 21)) := relabel_real G (renumber (encode G l)) l
    obtain ⟨vs12, hvs12_nd, hvs12_cov, hvs12_cls⟩ := levels_complete G ht normalized hn 5 B1 4 hB1small (by
      rintro ⟨x, hx⟩
      have mm := hB1small (B1.filter (G.Adj x)) (Finset.filter_subset (G.Adj x) B1) (neighbors_small G ht B1 x)
      exact ⟨x, hx, by omega⟩)
    rw [show B1.card = 12 by omega] at hvs12_cls
    have ok := of_decide_eq_true (List.all_eq_true.mp smaller4 (encode G vs12) hvs12_cls)
    obtain ⟨_, cs, hnd15, hcov15, henc15, hlen, hmem, hok, _, hedges⟩ :=
      ext_on_subset G ht B 6 hBsmall r hrB 2 1 hd2 (fun u hu => by have := hmin u (Finset.mem_filter.mp hu).1; omega)
        vs12 hvs12_nd hvs12_cov (encode G vs12) rfl
    have hed25 : edges_ (attach cs (encode G vs12)) ≤ 25 := by
      rw [← henc15, induce_edges_eq_encode G B _ hnd15 hcov15]; exact hD_le25
    unfold roots4 at ok
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ok
    rcases ok with h | h | h | h | h | h | h | h | h | h | h | h
    · rw [h] at hmem hok hedges hed25; have : edges_ b4_0 = 20 := by decide
      have hs : (cs.map (countBits b4_0.length)).sum ≤ 3 := by change edges_ (attach cs b4_0) = edges_ b4_0 + 2 + (cs.map (countBits b4_0.length)).sum at hedges; change edges_ (attach cs b4_0) ≤ 25 at hed25; omega
      exact viaDualGen 6 2 1 3 _ _ _ b4_0 cs w15_d2_b4_0 hlen hmem hok hs cert15_d2_b4_0
    · rw [h] at hmem hok hedges hed25; have : edges_ b4_1 = 21 := by decide
      have hs : (cs.map (countBits b4_1.length)).sum ≤ 2 := by change edges_ (attach cs b4_1) = edges_ b4_1 + 2 + (cs.map (countBits b4_1.length)).sum at hedges; change edges_ (attach cs b4_1) ≤ 25 at hed25; omega
      exact viaDualGen 6 2 1 2 _ _ _ b4_1 cs w15_d2_b4_1 hlen hmem hok hs cert15_d2_b4_1
    · rw [h] at hmem hok hedges hed25; have : edges_ b4_2 = 21 := by decide
      have hs : (cs.map (countBits b4_2.length)).sum ≤ 2 := by change edges_ (attach cs b4_2) = edges_ b4_2 + 2 + (cs.map (countBits b4_2.length)).sum at hedges; change edges_ (attach cs b4_2) ≤ 25 at hed25; omega
      exact viaDualGen 6 2 1 2 _ _ _ b4_2 cs w15_d2_b4_2 hlen hmem hok hs cert15_d2_b4_2
    · rw [h] at hmem hok hedges hed25; have : edges_ b4_3 = 22 := by decide
      have hs : (cs.map (countBits b4_3.length)).sum ≤ 1 := by change edges_ (attach cs b4_3) = edges_ b4_3 + 2 + (cs.map (countBits b4_3.length)).sum at hedges; change edges_ (attach cs b4_3) ≤ 25 at hed25; omega
      exact viaDualGen 6 2 1 1 _ _ _ b4_3 cs w15_d2_b4_3 hlen hmem hok hs cert15_d2_b4_3
    · rw [h] at hmem hok hedges hed25; have : edges_ b4_4 = 22 := by decide
      have hs : (cs.map (countBits b4_4.length)).sum ≤ 1 := by change edges_ (attach cs b4_4) = edges_ b4_4 + 2 + (cs.map (countBits b4_4.length)).sum at hedges; change edges_ (attach cs b4_4) ≤ 25 at hed25; omega
      exact viaDualGen 6 2 1 1 _ _ _ b4_4 cs w15_d2_b4_4 hlen hmem hok hs cert15_d2_b4_4
    · rw [h] at hmem hok hedges hed25; have : edges_ b4_5 = 22 := by decide
      have hs : (cs.map (countBits b4_5.length)).sum ≤ 1 := by change edges_ (attach cs b4_5) = edges_ b4_5 + 2 + (cs.map (countBits b4_5.length)).sum at hedges; change edges_ (attach cs b4_5) ≤ 25 at hed25; omega
      exact viaDualGen 6 2 1 1 _ _ _ b4_5 cs w15_d2_b4_5 hlen hmem hok hs cert15_d2_b4_5
    · rw [h] at hmem hok hedges hed25; have : edges_ b4_6 = 22 := by decide
      have hs : (cs.map (countBits b4_6.length)).sum ≤ 1 := by change edges_ (attach cs b4_6) = edges_ b4_6 + 2 + (cs.map (countBits b4_6.length)).sum at hedges; change edges_ (attach cs b4_6) ≤ 25 at hed25; omega
      exact viaDualGen 6 2 1 1 _ _ _ b4_6 cs w15_d2_b4_6 hlen hmem hok hs cert15_d2_b4_6
    · rw [h] at hmem hok hedges hed25; have : edges_ b4_7 = 23 := by decide
      have hs : (cs.map (countBits b4_7.length)).sum ≤ 0 := by change edges_ (attach cs b4_7) = edges_ b4_7 + 2 + (cs.map (countBits b4_7.length)).sum at hedges; change edges_ (attach cs b4_7) ≤ 25 at hed25; omega
      exact viaDualGen 6 2 1 0 _ _ _ b4_7 cs w15_d2_b4_7 hlen hmem hok hs cert15_d2_b4_7
    · rw [h] at hmem hok hedges hed25; have : edges_ b4_8 = 22 := by decide
      have hs : (cs.map (countBits b4_8.length)).sum ≤ 1 := by change edges_ (attach cs b4_8) = edges_ b4_8 + 2 + (cs.map (countBits b4_8.length)).sum at hedges; change edges_ (attach cs b4_8) ≤ 25 at hed25; omega
      exact viaDualGen 6 2 1 1 _ _ _ b4_8 cs w15_d2_b4_8 hlen hmem hok hs cert15_d2_b4_8
    · rw [h] at hmem hok hedges hed25; have : edges_ b4_9 = 23 := by decide
      have hs : (cs.map (countBits b4_9.length)).sum ≤ 0 := by change edges_ (attach cs b4_9) = edges_ b4_9 + 2 + (cs.map (countBits b4_9.length)).sum at hedges; change edges_ (attach cs b4_9) ≤ 25 at hed25; omega
      exact viaDualGen 6 2 1 0 _ _ _ b4_9 cs w15_d2_b4_9 hlen hmem hok hs cert15_d2_b4_9
    · rw [h] at hedges hed25
      have : edges_ b4_10 = 24 := by decide
      change edges_ (attach cs b4_10) = edges_ b4_10 + 2 + (cs.map (countBits b4_10.length)).sum at hedges
      change edges_ (attach cs b4_10) ≤ 25 at hed25
      omega
    · rw [h] at hedges hed25
      have : edges_ b4_11 = 24 := by decide
      change edges_ (attach cs b4_11) = edges_ b4_11 + 2 + (cs.map (countBits b4_11.length)).sum at hedges
      change edges_ (attach cs b4_11) ≤ 25 at hed25
      omega
  · -- d = 3: B1 has 11 vertices with <= 16 edges -> g11_0..6 -> 6 duals + g11_1 -> g15_25 -> d=5 dual!
    rw [hd3] at hsumN
    have hB1_le16 : (G.induce (B1 : Set (Fin 21))).edgeFinset.card ≤ 16 := by omega
    obtain ⟨idx, hidx, vs11, hvs11_nd, hvs11_cov, hvs11_enc⟩ :=
      root_split_relabel11 G ht B hBsmall 3 (by omega) r hrB (fun x hx => hd3 ▸ hmin x hx) hd3 hB1_le16
    obtain ⟨front, cs, hnd15, hcov15, henc15, hlen, hmem, hok, hsort, hedges⟩ :=
      ext_on_subset G ht B 6 hBsmall r hrB 3 2 hd3 (fun u hu => by have := hmin u (Finset.mem_filter.mp hu).1; omega)
        vs11 hvs11_nd hvs11_cov (g11Rep idx) hvs11_enc
    have hed25 : edges_ (attach cs (g11Rep idx)) ≤ 25 := by
      rw [← henc15, induce_edges_eq_encode G B _ hnd15 hcov15]; exact hD_le25
    have htop_sub (g : List Nat) : ∀ p ∈ (inds g).filter (fun p => p.2 == 4), p ∈ inds g ∧ 4 ≤ p.2 :=
      fun p hp => ⟨(List.mem_filter.mp hp).1, by have := (List.mem_filter.mp hp).2; simp only [beq_iff_eq] at this; omega⟩
    have hvs_g15 : ∃ vs15 : List (Fin 21), vs15.Nodup ∧ vs15.toFinset = B ∧ encode G vs15 = g15_25 := by
      have hidx_cases : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨ idx = 6 := by omega
      rcases hidx_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [show g11Rep 0 = g11_0 from rfl] at hmem hok hedges hed25
        have : edges_ g11_0 = 16 := by decide
        exact (viaDualGen 6 3 2 6 _ _ _ g11_0 cs w15_d3_0 hlen hmem hok (by omega) cert15_d3_0).elim
      · rw [show g11Rep 1 = g11_1 from rfl] at hmem hok hedges hed25 henc15
        have : edges_ g11_1 = 15 := by decide
        have hin := enumGenAux_complete 6 11 (inds g11_1) _ (htop_sub g11_1) 2 3 7 pool15_1 [] cs hlen
          (fun x hx => by
            obtain ⟨p, hp, rfl, hp1, hp2⟩ := hmem x hx
            have hp2' : p.2 < 5 := by omega
            have h4 := List.all_eq_true.mp enum15_1_ok.2.2.2 p hp
            simp [hp1, hp2'] at h4
            exact ⟨h4, by change 2 ≤ countBits g11_1.length p.1; rw [countBits_inds_eq g11_1 p hp]; exact hp1⟩)
          hsort enum15_1_ok.2.2.1 (by change (cs.map (countBits g11_1.length)).sum ≤ 7; omega) (by simpa using hok)
        simp only [List.reverse_nil, List.nil_append] at hin
        have hany := List.all_eq_true.mp enum15_1_ok.1 cs hin
        obtain ⟨e, he_in, he_eq⟩ := List.any_eq_true.mp hany
        have he1 : e.1 = cs := of_decide_eq_true he_eq
        have hrel := of_decide_eq_true (List.all_eq_true.mp enum15_1_ok.2.1 e he_in)
        obtain ⟨vs15, hperm, henc'⟩ := relabel_real G e.2 (r :: front ++ vs11)
        rw [henc15, ← he1] at henc'
        change encode G vs15 = relabel e.2 (attach e.1 g11_1) at henc'
        rw [hrel] at henc'
        exact ⟨vs15, hperm.nodup_iff.mpr hnd15, by rw [← hcov15]; ext x; simp [hperm.mem_iff], henc'⟩
      · rw [show g11Rep 2 = g11_2 from rfl] at hmem hok hedges hed25
        have : edges_ g11_2 = 16 := by decide
        exact (viaDualGen 6 3 2 6 _ _ _ g11_2 cs w15_d3_2 hlen hmem hok (by omega) cert15_d3_2).elim
      · rw [show g11Rep 3 = g11_3 from rfl] at hmem hok hedges hed25
        have : edges_ g11_3 = 16 := by decide
        exact (viaDualGen 6 3 2 6 _ _ _ g11_3 cs w15_d3_3 hlen hmem hok (by omega) cert15_d3_3).elim
      · rw [show g11Rep 4 = g11_4 from rfl] at hmem hok hedges hed25
        have : edges_ g11_4 = 16 := by decide
        exact (viaDualGen 6 3 2 6 _ _ _ g11_4 cs w15_d3_4 hlen hmem hok (by omega) cert15_d3_4).elim
      · rw [show g11Rep 5 = g11_5 from rfl] at hmem hok hedges hed25
        have : edges_ g11_5 = 16 := by decide
        exact (viaDualGen 6 3 2 6 _ _ _ g11_5 cs w15_d3_5 hlen hmem hok (by omega) cert15_d3_5).elim
      · rw [show g11Rep 6 = g11_6 from rfl] at hmem hok hedges hed25
        have : edges_ g11_6 = 16 := by decide
        exact (viaDualGen 6 3 2 6 _ _ _ g11_6 cs w15_d3_6 hlen hmem hok (by omega) cert15_d3_6).elim
    obtain ⟨vs15, hnd15', hcov15', henc15'⟩ := hvs_g15
    have hrem_w := RamseyDeficiency.removed G ht w
    dsimp only at hrem_w
    rw [h51] at hrem_w
    change (G.induce (B : Set (Fin 21))).edgeFinset.card + ∑ u ∈ G.neighborFinset w, G.degree u ≤ 51 at hrem_w
    have hed_g15 : (G.induce (B : Set (Fin 21))).edgeFinset.card = 25 := by
      rw [← induce_edges_eq_encode G B vs15 hnd15' hcov15', henc15']; decide
    obtain ⟨_, cs5, _, _, _, _, _, hlen5, hmem5, hok5, _, hsum5⟩ :=
      ext_on_rep G ht 7 hi w 5 2 hw (fun u _ => hmin3 u) vs15 hnd15' hcov15' g15_25 henc15'
    have hbud : (cs5.map (countBits g15_25.length)).sum ≤ 21 := by omega
    exact viaDualGen 7 5 2 21 _ _ _ g15_25 cs5 w15_to_21 hlen5 hmem5 hok5 hbud cert15_to_21

private theorem classify_16_le32 {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (B : Finset V) (hBcard : B.card = 16) (hBsmall : Small G B 6)
    (hBle32 : (G.induce (B : Set V)).edgeFinset.card ≤ 32) :
    (G.induce (B : Set V)).edgeFinset.card = 32 ∧
    ((∃ i < 2, ∃ vs16 : List V, vs16.Nodup ∧ vs16.toFinset = B ∧ encode G vs16 = g4regRep i) ∨
     (∃ i < 3, ∃ vs16 : List V, vs16.Nodup ∧ vs16.toFinset = B ∧ encode G vs16 = g16Rep i)) := by
  classical
  obtain ⟨r, hrB, hmin⟩ := B.exists_min_image (fun x => (B.filter (G.Adj x)).card) (Finset.card_pos.mp (by omega))
  set d := (B.filter (G.Adj r)).card with hd_def
  have hd_ge2 : 2 ≤ d := by
    have := subset_min_deg G ht B 5 14 OMA.Ramsey37Density.fourteen_works hBsmall r hrB; omega
  have hB_sum_deg : ∑ x ∈ B, (B.filter (G.Adj x)).card = 2 * (G.induce (B : Set V)).edgeFinset.card := by
    let D := G.induce (B : Set V)
    have hdeg (x : B) : (B.filter (G.Adj x.1)).card = D.degree x := by
      rw [← D.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
      refine Finset.card_bij (fun y hy => ⟨y, (Finset.mem_filter.mp hy).1⟩) ?_ ?_ ?_
      · intro y hy; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
      · intro _ _ _ _ h; exact congrArg Subtype.val h
      · intro y hy; exact ⟨y.1, Finset.mem_filter.mpr ⟨y.2, (Finset.mem_filter.mp hy).2⟩, rfl⟩
    calc ∑ x ∈ B, (B.filter (G.Adj x)).card
        = ∑ x : B, (B.filter (G.Adj x.1)).card := (Finset.sum_coe_sort B _).symm
      _ = ∑ x : B, D.degree x := Finset.sum_congr rfl (fun x _ => hdeg x)
      _ = 2 * D.edgeFinset.card := D.sum_degrees_eq_twice_card_edges
  have hd_le4 : d ≤ 4 := by
    by_contra! hge5
    have h80 : 80 ≤ ∑ x ∈ B, (B.filter (G.Adj x)).card := by
      calc 80 = ∑ _x ∈ B, (5 : ℕ) := by rw [Finset.sum_const, smul_eq_mul, hBcard]
        _ ≤ ∑ x ∈ B, (B.filter (G.Adj x)).card := Finset.sum_le_sum (fun x hx => by have := hmin x hx; omega)
    omega
  have htop_sub (g : List Nat) : ∀ p ∈ (inds g).filter (fun p => p.2 == 4), p ∈ inds g ∧ 4 ≤ p.2 :=
    fun p hp => ⟨(List.mem_filter.mp hp).1, by have := (List.mem_filter.mp hp).2; simp at this; omega⟩
  rcases (show d = 2 ∨ d = 3 ∨ d = 4 by omega) with hd2 | hd3 | hd4
  · -- d = 2: B1 has 13 vertices -> b3_0 -> enum16_b3_empty!
    set N := B.filter (G.Adj r)
    set B1 := B \ insert r N
    have hrN : r ∉ N := by simp [N]
    have hB1card : B1.card = 13 := by
      have h1 := Finset.card_sdiff_add_card_eq_card (Finset.insert_subset hrB (Finset.filter_subset (G.Adj r) B))
      change B1.card + (insert r N).card = B.card at h1
      rw [Finset.card_insert_of_notMem hrN] at h1
      dsimp only [N] at h1; omega
    have hB1small : Small G B1 5 := by
      intro S hS hI
      have hrS : r ∉ S := fun h => by have := Finset.mem_sdiff.mp (hS h); simp at this
      have hind : Gᶜ.IsClique (insert r S : Finset V) := by
        rw [Finset.coe_insert, SimpleGraph.isClique_insert_of_notMem hrS]
        refine ⟨hI, fun x hx => ?_⟩
        have hx1 := Finset.mem_sdiff.mp (hS hx)
        exact ⟨fun e => hrS (e ▸ hx), fun ha => hx1.2 (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hx1.1, ha⟩))⟩
      have hlt' := hBsmall (insert r S) (Finset.insert_subset hrB (hS.trans Finset.sdiff_subset)) hind
      rw [Finset.card_insert_of_notMem hrS] at hlt'; omega
    have hn (l : List V) := relabel_real G (renumber (encode G l)) l
    obtain ⟨vs13, hvs13_nd, hvs13_cov, hvs13_cls⟩ := levels_complete G ht normalized hn 5 B1 4 hB1small (by
      rintro ⟨x, hx⟩
      have mm := hB1small (B1.filter (G.Adj x)) (Finset.filter_subset (G.Adj x) B1) (neighbors_small G ht B1 x)
      exact ⟨x, hx, by omega⟩)
    rw [hB1card] at hvs13_cls
    have ok := of_decide_eq_true (List.all_eq_true.mp smaller3 (encode G vs13) hvs13_cls)
    unfold roots3 at ok
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ok
    obtain ⟨_, cs, hnd16, hcov16, henc16, hlen, hmem, hok, hsort, hedges⟩ :=
      ext_on_subset G ht B 6 hBsmall r hrB 2 1 hd2 (fun u hu => by have := hmin u (Finset.mem_filter.mp hu).1; omega)
        vs13 hvs13_nd hvs13_cov b3_0 ok
    have hed32 : edges_ (attach cs b3_0) ≤ 32 := by
      rw [← henc16, induce_edges_eq_encode G B _ hnd16 hcov16]; exact hBle32
    have : edges_ b3_0 = 26 := by decide
    have hsum_le : (cs.map (countBits 13)).sum ≤ 4 := by
      change edges_ (attach cs b3_0) = edges_ b3_0 + 2 + (cs.map (countBits 13)).sum at hedges
      change edges_ (attach cs b3_0) ≤ 32 at hed32; omega
    have hin := enumGenAux_complete 6 13 (inds b3_0) _ (htop_sub b3_0) 1 2 4 pool16_b3 [] cs hlen
      (fun x hx => by
        obtain ⟨p, hp, rfl, hp1, hp2⟩ := hmem x hx
        have hp2' : p.2 < 5 := by omega
        have h4 := List.all_eq_true.mp enum16_b3_empty.2.2 p hp
        simp [hp1, hp2'] at h4
        exact ⟨h4, by change 1 ≤ countBits b3_0.length p.1; rw [countBits_inds_eq b3_0 p hp]; exact hp1⟩)
      hsort enum16_b3_empty.2.1 hsum_le (by simpa using hok)
    simp only [List.reverse_nil, List.nil_append, enum16_b3_empty.1] at hin; cases hin
  · -- d = 3: B1 has 12 vertices -> b4_0..b4_11 -> b4_1..11 killed by duals, b4_0 -> g16_0..2!
    set N := B.filter (G.Adj r)
    set B1 := B \ insert r N
    have hrN : r ∉ N := by simp [N]
    have hB1card : B1.card = 12 := by
      have h1 := Finset.card_sdiff_add_card_eq_card (Finset.insert_subset hrB (Finset.filter_subset (G.Adj r) B))
      change B1.card + (insert r N).card = B.card at h1
      rw [Finset.card_insert_of_notMem hrN] at h1
      dsimp only [N] at h1; omega
    have hB1small : Small G B1 5 := by
      intro S hS hI
      have hrS : r ∉ S := fun h => by have := Finset.mem_sdiff.mp (hS h); simp at this
      have hind : Gᶜ.IsClique (insert r S : Finset V) := by
        rw [Finset.coe_insert, SimpleGraph.isClique_insert_of_notMem hrS]
        refine ⟨hI, fun x hx => ?_⟩
        have hx1 := Finset.mem_sdiff.mp (hS hx)
        exact ⟨fun e => hrS (e ▸ hx), fun ha => hx1.2 (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hx1.1, ha⟩))⟩
      have hlt' := hBsmall (insert r S) (Finset.insert_subset hrB (hS.trans Finset.sdiff_subset)) hind
      rw [Finset.card_insert_of_notMem hrS] at hlt'; omega
    have hn (l : List V) := relabel_real G (renumber (encode G l)) l
    obtain ⟨vs12, hvs12_nd, hvs12_cov, hvs12_cls⟩ := levels_complete G ht normalized hn 5 B1 4 hB1small (by
      rintro ⟨x, hx⟩
      have mm := hB1small (B1.filter (G.Adj x)) (Finset.filter_subset (G.Adj x) B1) (neighbors_small G ht B1 x)
      exact ⟨x, hx, by omega⟩)
    rw [hB1card] at hvs12_cls
    have ok := of_decide_eq_true (List.all_eq_true.mp smaller4 (encode G vs12) hvs12_cls)
    obtain ⟨front, cs, hnd16, hcov16, henc16, hlen, hmem, hok, hsort, hedges⟩ :=
      ext_on_subset G ht B 6 hBsmall r hrB 3 2 hd3 (fun u hu => by have := hmin u (Finset.mem_filter.mp hu).1; omega)
        vs12 hvs12_nd hvs12_cov (encode G vs12) rfl
    have hed32 : edges_ (attach cs (encode G vs12)) ≤ 32 := by
      rw [← henc16, induce_edges_eq_encode G B _ hnd16 hcov16]; exact hBle32
    unfold roots4 at ok
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ok
    rcases ok with h | h | h | h | h | h | h | h | h | h | h | h
    · rw [h] at henc16 hmem hok hedges hed32
      have hb0 : edges_ b4_0 = 20 := by decide
      have hsum_le : (cs.map (countBits 12)).sum ≤ 9 := by
        change edges_ (attach cs b4_0) = edges_ b4_0 + 3 + (cs.map (countBits 12)).sum at hedges
        change edges_ (attach cs b4_0) ≤ 32 at hed32; omega
      have hin := enumGenAux_complete 6 12 (inds b4_0) _ (htop_sub b4_0) 2 3 9 pool16_b40 [] cs hlen
        (fun x hx => by
          obtain ⟨p, hp, rfl, hp1, hp2⟩ := hmem x hx
          have hp2' : p.2 < 5 := by omega
          have h4 := List.all_eq_true.mp enum16_b40_ok.2.2.2 p hp
          simp [hp1, hp2'] at h4
          exact ⟨h4, by change 2 ≤ countBits b4_0.length p.1; rw [countBits_inds_eq b4_0 p hp]; exact hp1⟩)
        hsort enum16_b40_ok.2.2.1 hsum_le (by simpa using hok)
      simp only [List.reverse_nil, List.nil_append] at hin
      have hany := List.all_eq_true.mp enum16_b40_ok.1 cs hin
      obtain ⟨e, he_in, he_eq⟩ := List.any_eq_true.mp hany
      have he1 : e.1 = cs := of_decide_eq_true he_eq
      have hge9 := of_decide_eq_true (List.all_eq_true.mp g16Sols_edges32 e he_in)
      rw [he1] at hge9
      have hcard32 : (G.induce (B : Set V)).edgeFinset.card = 32 := by
        rw [← induce_edges_eq_encode G B _ hnd16 hcov16, henc16]
        change edges_ (attach cs b4_0) = edges_ b4_0 + 3 + (cs.map (countBits 12)).sum at hedges
        change edges_ (attach cs b4_0) ≤ 32 at hed32
        change edges_ (attach cs b4_0) = 32
        omega
      have hrel := of_decide_eq_true (List.all_eq_true.mp enum16_b40_ok.2.1 e he_in)
      obtain ⟨vs16, hperm, henc'⟩ := relabel_real G e.2.2 (r :: front ++ vs12)
      rw [henc16, ← he1, hrel.2] at henc'
      exact ⟨hcard32, Or.inr ⟨e.2.1, hrel.1, vs16, hperm.nodup_iff.mpr hnd16,
        by rw [← hcov16]; ext x; simp [hperm.mem_iff], henc'⟩⟩
    · rw [h] at hmem hok hedges hed32; have : edges_ b4_1 = 21 := by decide
      have hs : (cs.map (countBits b4_1.length)).sum ≤ 8 := by change edges_ (attach cs b4_1) = edges_ b4_1 + 3 + (cs.map (countBits b4_1.length)).sum at hedges; change edges_ (attach cs b4_1) ≤ 32 at hed32; omega
      exact (viaDualGen 6 3 2 8 _ _ _ b4_1 cs w16_b4_1 hlen hmem hok hs cert16_b4_1).elim
    · rw [h] at hmem hok hedges hed32; have : edges_ b4_2 = 21 := by decide
      have hs : (cs.map (countBits b4_2.length)).sum ≤ 8 := by change edges_ (attach cs b4_2) = edges_ b4_2 + 3 + (cs.map (countBits b4_2.length)).sum at hedges; change edges_ (attach cs b4_2) ≤ 32 at hed32; omega
      exact (viaDualGen 6 3 2 8 _ _ _ b4_2 cs w16_b4_2 hlen hmem hok hs cert16_b4_2).elim
    · rw [h] at hmem hok hedges hed32; have : edges_ b4_3 = 22 := by decide
      have hs : (cs.map (countBits b4_3.length)).sum ≤ 7 := by change edges_ (attach cs b4_3) = edges_ b4_3 + 3 + (cs.map (countBits b4_3.length)).sum at hedges; change edges_ (attach cs b4_3) ≤ 32 at hed32; omega
      exact (viaDualGen 6 3 2 7 _ _ _ b4_3 cs w16_b4_3 hlen hmem hok hs cert16_b4_3).elim
    · rw [h] at hmem hok hedges hed32; have : edges_ b4_4 = 22 := by decide
      have hs : (cs.map (countBits b4_4.length)).sum ≤ 7 := by change edges_ (attach cs b4_4) = edges_ b4_4 + 3 + (cs.map (countBits b4_4.length)).sum at hedges; change edges_ (attach cs b4_4) ≤ 32 at hed32; omega
      exact (viaDualGen 6 3 2 7 _ _ _ b4_4 cs w16_b4_4 hlen hmem hok hs cert16_b4_4).elim
    · rw [h] at hmem hok hedges hed32; have : edges_ b4_5 = 22 := by decide
      have hs : (cs.map (countBits b4_5.length)).sum ≤ 7 := by change edges_ (attach cs b4_5) = edges_ b4_5 + 3 + (cs.map (countBits b4_5.length)).sum at hedges; change edges_ (attach cs b4_5) ≤ 32 at hed32; omega
      exact (viaDualGen 6 3 2 7 _ _ _ b4_5 cs w16_b4_5 hlen hmem hok hs cert16_b4_5).elim
    · rw [h] at hmem hok hedges hed32; have : edges_ b4_6 = 22 := by decide
      have hs : (cs.map (countBits b4_6.length)).sum ≤ 7 := by change edges_ (attach cs b4_6) = edges_ b4_6 + 3 + (cs.map (countBits b4_6.length)).sum at hedges; change edges_ (attach cs b4_6) ≤ 32 at hed32; omega
      exact (viaDualGen 6 3 2 7 _ _ _ b4_6 cs w16_b4_6 hlen hmem hok hs cert16_b4_6).elim
    · rw [h] at hmem hok hedges hed32; have : edges_ b4_7 = 23 := by decide
      have hs : (cs.map (countBits b4_7.length)).sum ≤ 6 := by change edges_ (attach cs b4_7) = edges_ b4_7 + 3 + (cs.map (countBits b4_7.length)).sum at hedges; change edges_ (attach cs b4_7) ≤ 32 at hed32; omega
      exact (viaDualGen 6 3 2 6 _ _ _ b4_7 cs w16_b4_7 hlen hmem hok hs cert16_b4_7).elim
    · rw [h] at hmem hok hedges hed32; have : edges_ b4_8 = 22 := by decide
      have hs : (cs.map (countBits b4_8.length)).sum ≤ 7 := by change edges_ (attach cs b4_8) = edges_ b4_8 + 3 + (cs.map (countBits b4_8.length)).sum at hedges; change edges_ (attach cs b4_8) ≤ 32 at hed32; omega
      exact (viaDualGen 6 3 2 7 _ _ _ b4_8 cs w16_b4_8 hlen hmem hok hs cert16_b4_8).elim
    · rw [h] at hmem hok hedges hed32; have : edges_ b4_9 = 23 := by decide
      have hs : (cs.map (countBits b4_9.length)).sum ≤ 6 := by change edges_ (attach cs b4_9) = edges_ b4_9 + 3 + (cs.map (countBits b4_9.length)).sum at hedges; change edges_ (attach cs b4_9) ≤ 32 at hed32; omega
      exact (viaDualGen 6 3 2 6 _ _ _ b4_9 cs w16_b4_9 hlen hmem hok hs cert16_b4_9).elim
    · rw [h] at hmem hok hedges hed32; have : edges_ b4_10 = 24 := by decide
      have hs : (cs.map (countBits b4_10.length)).sum ≤ 5 := by change edges_ (attach cs b4_10) = edges_ b4_10 + 3 + (cs.map (countBits b4_10.length)).sum at hedges; change edges_ (attach cs b4_10) ≤ 32 at hed32; omega
      exact (viaDualGen 6 3 2 5 _ _ _ b4_10 cs w16_b4_10 hlen hmem hok hs cert16_b4_10).elim
    · rw [h] at hmem hok hedges hed32; have : edges_ b4_11 = 24 := by decide
      have hs : (cs.map (countBits b4_11.length)).sum ≤ 5 := by change edges_ (attach cs b4_11) = edges_ b4_11 + 3 + (cs.map (countBits b4_11.length)).sum at hedges; change edges_ (attach cs b4_11) ≤ 32 at hed32; omega
      exact (viaDualGen 6 3 2 5 _ _ _ b4_11 cs w16_b4_11 hlen hmem hok hs cert16_b4_11).elim
  · -- d = 4: 4-regular (3,6;16)!
    have h64 : 64 ≤ ∑ x ∈ B, (B.filter (G.Adj x)).card := by
      calc 64 = ∑ _x ∈ B, (4 : ℕ) := by rw [Finset.sum_const, smul_eq_mul, hBcard]
        _ ≤ ∑ x ∈ B, (B.filter (G.Adj x)).card := Finset.sum_le_sum (fun x hx => by have := hmin x hx; omega)
    have hcard32 : (G.induce (B : Set V)).edgeFinset.card = 32 := by omega
    have hall4 : ∀ x ∈ B, (B.filter (G.Adj x)).card = 4 := by
      intro x hx
      by_contra hne
      have hge5 : 5 ≤ (B.filter (G.Adj x)).card := by have := hmin x hx; omega
      have hgt : 64 < ∑ y ∈ B, (B.filter (G.Adj y)).card := by
        have hs := Finset.sum_le_sum (s := B.erase x) (fun y hy => show 4 ≤ (B.filter (G.Adj y)).card by
          have := hmin y (Finset.mem_erase.mp hy).2; omega)
        rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem hx, hBcard] at hs
        have hsp := Finset.add_sum_erase B (fun y => (B.filter (G.Adj y)).card) hx
        omega
      omega
    have hrem := removed_subset G ht B r hrB
    set N := B.filter (G.Adj r)
    set B1 := B \ insert r N
    change (G.induce (B1 : Set V)).edgeFinset.card + ∑ u ∈ N, (B.filter (G.Adj u)).card ≤ (G.induce (B : Set V)).edgeFinset.card at hrem
    have hsumN : ∑ u ∈ N, (B.filter (G.Adj u)).card = 16 := by
      calc ∑ u ∈ N, (B.filter (G.Adj u)).card
          = ∑ _u ∈ N, (4 : ℕ) := Finset.sum_congr rfl (fun u hu => hall4 u (Finset.mem_filter.mp hu).1)
        _ = 16 := by rw [Finset.sum_const, smul_eq_mul, show N.card = 4 from hd4]
    have hB1_le16 : (G.induce (B1 : Set V)).edgeFinset.card ≤ 16 := by omega
    obtain ⟨idx, hidx, vs11, hvs11_nd, hvs11_cov, hvs11_enc⟩ :=
      root_split_relabel11 G ht B hBsmall 4 (by omega) r hrB (fun x hx => hd4 ▸ hmin x hx) hd4 hB1_le16
    obtain ⟨front, cs, hnd16, hcov16, henc16, hlen, hmem, hok, hsort, hedges⟩ :=
      ext_on_subset G ht B 6 hBsmall r hrB 4 3 hd4 (fun u hu => by have := hall4 u (Finset.mem_filter.mp hu).1; omega)
        vs11 hvs11_nd hvs11_cov (g11Rep idx) hvs11_enc
    have hcs_deg : cs.foldl (fun dg m => bump m dg) (degrees (g11Rep idx)) = List.replicate 11 4 := by
      have h1 := degrees_attach_drop cs (g11Rep idx)
      rw [← henc16, hlen, degrees_encode] at h1
      have hmap : (r :: front ++ vs11).map (sizeAt G (r :: front ++ vs11)) = List.replicate 16 4 := by
        apply List.eq_replicate_iff.mpr
        refine ⟨?_, ?_⟩
        · rw [List.length_map, ← List.toFinset_card_of_nodup hnd16, hcov16, hBcard]
        · intro y hy
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
          rw [sizeAt_finset G hnd16, hcov16]
          exact hall4 x (hcov16 ▸ List.mem_toFinset.mpr hx)
      rw [hmap] at h1
      simpa using h1.symm
    have hcs_sz3 : ∀ x ∈ cs, ∃ p ∈ inds (g11Rep idx), p.1 = x ∧ p.2 = 3 := by
      have hed32 : edges_ (attach cs (g11Rep idx)) = 32 := by
        rw [← henc16, induce_edges_eq_encode G B _ hnd16 hcov16, hcard32]
      have hsum_ge : 12 ≤ (cs.map (countBits (g11Rep idx).length)).sum := by
        have aux : ∀ l : List Nat, (∀ y ∈ l, 3 ≤ countBits (g11Rep idx).length y) →
            l.length * 3 ≤ (l.map (countBits (g11Rep idx).length)).sum := by
          intro l hl; induction l with | nil => simp | cons a as iha =>
            have h1 := hl a (.head _); have h2 := iha (fun y hy => hl y (.tail _ hy))
            simp only [List.length_cons, Nat.succ_mul, List.map_cons, List.sum_cons]; omega
        have h12 := aux cs (fun y hy => by
          obtain ⟨p, hp, rfl, hp1, _⟩ := hmem y hy; rw [countBits_inds_eq _ p hp]; exact hp1)
        rw [hlen] at h12; exact h12
      have hsum_eq12 : (cs.map (countBits (g11Rep idx).length)).sum = 12 := by
        have hed11 : edges_ (g11Rep idx) = 16 := by
          have hed_le : edges_ (g11Rep idx) ≤ 16 := by
            rw [← hvs11_enc, induce_edges_eq_encode G B1 vs11 hvs11_nd hvs11_cov]; exact hB1_le16
          have hed_ge : 16 ≤ edges_ (g11Rep idx) := by
            have hsum_deg11 : (degrees (g11Rep idx)).sum + (cs.map (countBits 11)).sum = 44 := by
              have hlen11 : (g11Rep idx).length = 11 := by
                have hc : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨ idx = 6 := by omega
                rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
              have hb_sum : ∀ m (l : List Nat), (bump m l).sum = l.sum + countBits l.length m := by
                intro m l; induction l generalizing m with
                | nil => simp [bump, countBits]
                | cons a as ihl => simp [bump, countBits, ihl]; omega
              have hfold : ∀ (ms l : List Nat), (ms.foldl (fun dg m => bump m dg) l).sum =
                  l.sum + (ms.map (countBits l.length)).sum := by
                intro ms; induction ms with
                | nil => intro l; simp
                | cons m ms ihm =>
                  intro l
                  have hbl : (bump m l).length = l.length := by
                    clear * -; induction l generalizing m with | nil => rfl | cons _ _ ih => simp [bump, ih]
                  simp only [List.foldl_cons, List.map_cons, List.sum_cons, ihm, hbl, hb_sum]; omega
              have h44 := congrArg List.sum hcs_deg
              rw [hfold, degrees_length, hlen11, List.sum_replicate, smul_eq_mul] at h44
              exact h44
            have hlen11 : (g11Rep idx).length = 11 := by
              have hc : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨ idx = 6 := by omega
              rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
            have hen := energy (g11Rep idx)
            rw [hlen11] at hedges
            omega
          omega
        omega
      intro x hx
      obtain ⟨p, hp, rfl, hp1, hp2⟩ := hmem x hx
      refine ⟨p, hp, rfl, ?_⟩
      by_contra hne3
      have hge4 : 4 ≤ countBits (g11Rep idx).length p.1 := by rw [countBits_inds_eq _ p hp]; omega
      have haux : ∀ l : List Nat, (∀ y ∈ l, 3 ≤ countBits (g11Rep idx).length y) →
          p.1 ∈ l → 4 ≤ countBits (g11Rep idx).length p.1 →
          l.length * 3 + 1 ≤ (l.map (countBits (g11Rep idx).length)).sum := by
        intro l hl hm h4
        induction l with
        | nil => cases hm
        | cons a as iha =>
          simp only [List.length_cons, Nat.succ_mul, List.map_cons, List.sum_cons]
          rcases List.mem_cons.mp hm with rfl | htail
          · have : as.length * 3 ≤ (as.map (countBits (g11Rep idx).length)).sum := by
              clear * - hl; induction as with | nil => simp | cons b bs ihb =>
                have h1 := hl b (.tail _ (.head _))
                have h2 := ihb (fun y hy => hl y (by rcases List.mem_cons.mp hy with rfl | ht; exact .head _; exact .tail _ (.tail _ ht)))
                simp only [List.length_cons, Nat.succ_mul, List.map_cons, List.sum_cons]; omega
            omega
          · have h1 := hl a (.head _)
            have h2 := iha (fun y hy => hl y (.tail _ hy)) htail
            omega
      have hgt := haux cs (fun y hy => by obtain ⟨q, hq, rfl, hq1, _⟩ := hmem y hy; rw [countBits_inds_eq _ q hq]; exact hq1) hx hge4
      rw [hlen] at hgt; omega
    have hidx_ne1 : idx ≠ 1 := by
      rintro rfl
      rw [show g11Rep 1 = g11_1 from rfl] at henc16 hcs_sz3 hedges
      have hed32 : edges_ (attach cs g11_1) = 32 := by rw [← henc16, induce_edges_eq_encode G B _ hnd16 hcov16, hcard32]
      have h15 : edges_ g11_1 = 15 := by decide
      have hsum12 : (cs.map (countBits g11_1.length)).sum = 12 := by
        have hmap : cs.map (countBits g11_1.length) = List.replicate cs.length 3 := by
          apply List.eq_replicate_iff.mpr
          refine ⟨List.length_map .., fun y hy => ?_⟩
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
          obtain ⟨p, hp, rfl, hp3⟩ := hcs_sz3 x hx
          rw [countBits_inds_eq _ p hp, hp3]
        rw [hmap, List.sum_replicate, smul_eq_mul, hlen]
      omega
    refine ⟨hcard32, Or.inl ?_⟩
    have hidx_c : idx = 0 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨ idx = 6 := by omega
    rcases hidx_c with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [show g11Rep 0 = g11_0 from rfl] at hcs_sz3 hok hcs_deg
      have hin := enum4RegAux_complete (inds g11_0) _ (htop_sub g11_0) g11_0 4 pool4reg_0 [] (degrees g11_0) cs rfl hlen
        (fun x hx => by obtain ⟨p, hp, rfl, hp3⟩ := hcs_sz3 x hx; have h4 := List.all_eq_true.mp enum4reg_0_empty.2.2 p hp; simp [hp3] at h4; exact h4)
        hsort enum4reg_0_empty.2.1 (by simpa using hok) (by simpa using hcs_deg)
      simp only [List.reverse_nil, List.nil_append, enum4reg_0_empty.1] at hin; cases hin
    · rw [show g11Rep 2 = g11_2 from rfl] at hcs_sz3 hok hcs_deg henc16
      have hin := enum4RegAux_complete (inds g11_2) _ (htop_sub g11_2) g11_2 4 pool4reg_2 [] (degrees g11_2) cs rfl hlen
        (fun x hx => by obtain ⟨p, hp, rfl, hp3⟩ := hcs_sz3 x hx; have h4 := List.all_eq_true.mp enum4reg_2_ok.2.2.2 p hp; simp [hp3] at h4; exact h4)
        hsort enum4reg_2_ok.2.2.1 (by simpa using hok) (by simpa using hcs_deg)
      simp only [List.reverse_nil, List.nil_append] at hin
      have hany := List.all_eq_true.mp enum4reg_2_ok.1 cs hin
      obtain ⟨e, he_in, he_eq⟩ := List.any_eq_true.mp hany
      have he1 : e.1 = cs := of_decide_eq_true he_eq
      have hrel := of_decide_eq_true (List.all_eq_true.mp enum4reg_2_ok.2.1 e he_in)
      obtain ⟨vs16, hperm, henc'⟩ := relabel_real G e.2.2 (r :: front ++ vs11)
      rw [henc16, ← he1] at henc'
      change encode G vs16 = relabel e.2.2 (attach e.1 g11_2) at henc'
      rw [hrel.2] at henc'
      exact ⟨e.2.1, hrel.1, vs16, hperm.nodup_iff.mpr hnd16, by rw [← hcov16]; ext x; simp [hperm.mem_iff], henc'⟩
    · rw [show g11Rep 3 = g11_3 from rfl] at hcs_sz3 hok hcs_deg henc16
      have hin := enum4RegAux_complete (inds g11_3) _ (htop_sub g11_3) g11_3 4 pool4reg_3 [] (degrees g11_3) cs rfl hlen
        (fun x hx => by obtain ⟨p, hp, rfl, hp3⟩ := hcs_sz3 x hx; have h4 := List.all_eq_true.mp enum4reg_3_ok.2.2.2 p hp; simp [hp3] at h4; exact h4)
        hsort enum4reg_3_ok.2.2.1 (by simpa using hok) (by simpa using hcs_deg)
      simp only [List.reverse_nil, List.nil_append] at hin
      have hany := List.all_eq_true.mp enum4reg_3_ok.1 cs hin
      obtain ⟨e, he_in, he_eq⟩ := List.any_eq_true.mp hany
      have he1 : e.1 = cs := of_decide_eq_true he_eq
      have hrel := of_decide_eq_true (List.all_eq_true.mp enum4reg_3_ok.2.1 e he_in)
      obtain ⟨vs16, hperm, henc'⟩ := relabel_real G e.2.2 (r :: front ++ vs11)
      rw [henc16, ← he1] at henc'
      change encode G vs16 = relabel e.2.2 (attach e.1 g11_3) at henc'
      rw [hrel.2] at henc'
      exact ⟨e.2.1, hrel.1, vs16, hperm.nodup_iff.mpr hnd16, by rw [← hcov16]; ext x; simp [hperm.mem_iff], henc'⟩
    · rw [show g11Rep 4 = g11_4 from rfl] at hcs_sz3 hok hcs_deg
      have hin := enum4RegAux_complete (inds g11_4) _ (htop_sub g11_4) g11_4 4 pool4reg_4 [] (degrees g11_4) cs rfl hlen
        (fun x hx => by obtain ⟨p, hp, rfl, hp3⟩ := hcs_sz3 x hx; have h4 := List.all_eq_true.mp enum4reg_4_empty.2.2 p hp; simp [hp3] at h4; exact h4)
        hsort enum4reg_4_empty.2.1 (by simpa using hok) (by simpa using hcs_deg)
      simp only [List.reverse_nil, List.nil_append, enum4reg_4_empty.1] at hin; cases hin
    · rw [show g11Rep 5 = g11_5 from rfl] at hcs_sz3 hok hcs_deg
      have hin := enum4RegAux_complete (inds g11_5) _ (htop_sub g11_5) g11_5 4 pool4reg_5 [] (degrees g11_5) cs rfl hlen
        (fun x hx => by obtain ⟨p, hp, rfl, hp3⟩ := hcs_sz3 x hx; have h4 := List.all_eq_true.mp enum4reg_5_empty.2.2 p hp; simp [hp3] at h4; exact h4)
        hsort enum4reg_5_empty.2.1 (by simpa using hok) (by simpa using hcs_deg)
      simp only [List.reverse_nil, List.nil_append, enum4reg_5_empty.1] at hin; cases hin
    · rw [show g11Rep 6 = g11_6 from rfl] at hcs_sz3 hok hcs_deg
      have hin := enum4RegAux_complete (inds g11_6) _ (htop_sub g11_6) g11_6 4 pool4reg_6 [] (degrees g11_6) cs rfl hlen
        (fun x hx => by obtain ⟨p, hp, rfl, hp3⟩ := hcs_sz3 x hx; have h4 := List.all_eq_true.mp enum4reg_6_empty.2.2 p hp; simp [hp3] at h4; exact h4)
        hsort enum4reg_6_empty.2.1 (by simpa using hok) (by simpa using hcs_deg)
      simp only [List.reverse_nil, List.nil_append, enum4reg_6_empty.1] at hin; cases hin

private theorem e36_16_ge_32 {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (B : Finset V) (hBcard : B.card = 16) (hBsmall : Small G B 6) :
    32 ≤ (G.induce (B : Set V)).edgeFinset.card := by
  by_contra! hlt
  have ⟨h32, _⟩ := classify_16_le32 G ht B hBcard hBsmall (by omega)
  omega

set_option maxHeartbeats 800000 in
/-- Stage 3: Every 21-vertex 51-edge (3,7)-graph has min degree >= 4 and a degree-4 vertex
whose 16-vertex non-neighborhood has exactly 32 edges. -/
private theorem exists_deg4_e32 (G : SimpleGraph (Fin 21)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree 7) (h51 : G.edgeFinset.card = 51) :
    (∀ v : Fin 21, 4 ≤ G.degree v) ∧
    ∃ v : Fin 21, G.degree v = 4 ∧
      (G.induce ((Gᶜ.neighborFinset v : Finset (Fin 21)) : Set (Fin 21))).edgeFinset.card = 32 := by
  classical
  have hdeg_bounds (v : Fin 21) : 3 ≤ G.degree v ∧ G.degree v ≤ 6 := by
    have hd := OMA.Ramsey37Density.degree_lt G ht hi v
    have hdc := OMA.Ramsey37Density.nonneighbors_lt eighteen_works G ht hi v
    rw [G.degree_compl, Fintype.card_fin] at hdc
    omega
  have hmin3 : ∀ v, 3 ≤ G.degree v := fun v => (hdeg_bounds v).1
  let eH (v : Fin 21) : Nat := (G.induce ((Gᶜ.neighborFinset v : Finset (Fin 21)) : Set (Fin 21))).edgeFinset.card
  let lb (d : Nat) : Nat := if d = 3 then 40 else if d = 4 then 32 else if d = 5 then 26 else 21
  have hBcard (v : Fin 21) : (Gᶜ.neighborFinset v).card = 20 - G.degree v := by
    have hc := G.degree_compl v; rw [Fintype.card_fin] at hc
    rw [SimpleGraph.card_neighborFinset_eq_degree]; omega
  have h_eH_ge (v : Fin 21) : lb (G.degree v) ≤ eH v := by
    have hb := hdeg_bounds v
    have hsm := induce_small_of_nonneighbors G 6 hi v
    rcases (show G.degree v = 3 ∨ G.degree v = 4 ∨ G.degree v = 5 ∨ G.degree v = 6 by omega) with h | h | h | h
    · simpa [lb, h, eH] using e36_17_ge_40 G ht (Gᶜ.neighborFinset v) (by rw [hBcard, h]) hsm
    · simpa [lb, h, eH] using e36_16_ge_32 G ht (Gᶜ.neighborFinset v) (by rw [hBcard, h]) hsm
    · simpa [lb, h, eH] using e36_15_unique_and_kill G ht hi h51 hmin3 v h
    · simpa [lb, h, eH] using e36_14_unique_and_kill G ht hi h51 hmin3 v h
  have hlocal (v : Fin 21) : eH v + ∑ u ∈ G.neighborFinset v, G.degree u ≤ 51 := by
    have hrem := RamseyDeficiency.removed G ht v
    dsimp only at hrem
    rw [h51] at hrem
    exact hrem
  have hsum_deg_sq : ∑ v : Fin 21, ∑ u ∈ G.neighborFinset v, G.degree u = ∑ v : Fin 21, G.degree v ^ 2 := by
    calc ∑ v : Fin 21, ∑ u ∈ G.neighborFinset v, G.degree u
        = ∑ v : Fin 21, ∑ u : Fin 21, if G.Adj v u then G.degree u else 0 := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [← Finset.sum_filter, SimpleGraph.neighborFinset_eq_filter]
      _ = ∑ u : Fin 21, ∑ v : Fin 21, if G.Adj v u then G.degree u else 0 := Finset.sum_comm
      _ = ∑ u : Fin 21, ∑ v ∈ G.neighborFinset u, G.degree u := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
          refine Finset.sum_congr rfl fun v _ => by simp [G.adj_comm]
      _ = ∑ u : Fin 21, G.degree u ^ 2 := by
          refine Finset.sum_congr rfl fun u _ => by
            rw [Finset.sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree, sq]
  let V3 := Finset.univ.filter (fun v : Fin 21 => G.degree v = 3)
  let V4 := Finset.univ.filter (fun v : Fin 21 => G.degree v = 4)
  let V5 := Finset.univ.filter (fun v : Fin 21 => G.degree v = 5)
  let V6 := Finset.univ.filter (fun v : Fin 21 => G.degree v = 6)
  have hpart (f : Fin 21 → Nat) :
      ∑ v : Fin 21, f v = (∑ v ∈ V3, f v) + (∑ v ∈ V4, f v) + (∑ v ∈ V5, f v) + (∑ v ∈ V6, f v) := by
    have hsplit (v : Fin 21) : f v =
        (if G.degree v = 3 then f v else 0) + (if G.degree v = 4 then f v else 0) +
        (if G.degree v = 5 then f v else 0) + (if G.degree v = 6 then f v else 0) := by
      have := hdeg_bounds v
      rcases (show G.degree v = 3 ∨ G.degree v = 4 ∨ G.degree v = 5 ∨ G.degree v = 6 by omega) with h | h | h | h <;> simp [h]
    calc ∑ v : Fin 21, f v
        = ∑ v : Fin 21, ((if G.degree v = 3 then f v else 0) + (if G.degree v = 4 then f v else 0) +
            (if G.degree v = 5 then f v else 0) + (if G.degree v = 6 then f v else 0)) :=
          Finset.sum_congr rfl (fun v _ => hsplit v)
      _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.sum_filter]; rfl
  have hcnt : V3.card + V4.card + V5.card + V6.card = 21 := by
    have h := hpart (fun _ => 1)
    simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin] at h
    omega
  have hdeg_sum : 3 * V3.card + 4 * V4.card + 5 * V5.card + 6 * V6.card = 102 := by
    have h := hpart (fun v => G.degree v)
    have htot := G.sum_degrees_eq_twice_card_edges
    rw [h51] at htot
    have h3 : ∑ v ∈ V3, G.degree v = 3 * V3.card := by
      rw [Finset.sum_congr rfl (fun v hv => (Finset.mem_filter.mp hv).2), Finset.sum_const, smul_eq_mul, mul_comm]
    have h4 : ∑ v ∈ V4, G.degree v = 4 * V4.card := by
      rw [Finset.sum_congr rfl (fun v hv => (Finset.mem_filter.mp hv).2), Finset.sum_const, smul_eq_mul, mul_comm]
    have h5 : ∑ v ∈ V5, G.degree v = 5 * V5.card := by
      rw [Finset.sum_congr rfl (fun v hv => (Finset.mem_filter.mp hv).2), Finset.sum_const, smul_eq_mul, mul_comm]
    have h6 : ∑ v ∈ V6, G.degree v = 6 * V6.card := by
      rw [Finset.sum_congr rfl (fun v hv => (Finset.mem_filter.mp hv).2), Finset.sum_const, smul_eq_mul, mul_comm]
    omega
  have hsq_lb : 49 * V3.card + 48 * V4.card + 51 * V5.card + 57 * V6.card +
      ∑ v ∈ V4, (eH v - 32) ≤ 1071 := by
    have hsum_all := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 21))) (fun v _ => hlocal v)
    rw [Finset.sum_add_distrib, hsum_deg_sq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum_all
    have hpt_ge (v : Fin 21) : (lb (G.degree v) + G.degree v ^ 2) + (if G.degree v = 4 then eH v - 32 else 0) ≤
        eH v + G.degree v ^ 2 := by
      have hge := h_eH_ge v
      by_cases h4 : G.degree v = 4
      · simp only [h4, ite_true, lb, (by decide : (4:Nat) ≠ 3), ite_false] at hge ⊢; omega
      · simp only [h4, ite_false]; omega
    have hle2 : (∑ v : Fin 21, (lb (G.degree v) + G.degree v ^ 2)) + ∑ v ∈ V4, (eH v - 32) ≤
        (∑ v : Fin 21, eH v) + ∑ v : Fin 21, G.degree v ^ 2 := by
      calc (∑ v : Fin 21, (lb (G.degree v) + G.degree v ^ 2)) + ∑ v ∈ V4, (eH v - 32)
          = (∑ v : Fin 21, (lb (G.degree v) + G.degree v ^ 2)) + ∑ v : Fin 21, if G.degree v = 4 then eH v - 32 else 0 := by
            rw [Finset.sum_filter]
        _ = ∑ v : Fin 21, ((lb (G.degree v) + G.degree v ^ 2) + if G.degree v = 4 then eH v - 32 else 0) :=
            (Finset.sum_add_distrib).symm
        _ ≤ ∑ v : Fin 21, (eH v + G.degree v ^ 2) := Finset.sum_le_sum (fun v _ => hpt_ge v)
        _ = (∑ v : Fin 21, eH v) + ∑ v : Fin 21, G.degree v ^ 2 := Finset.sum_add_distrib
    have hpart_val := hpart (fun v => lb (G.degree v) + G.degree v ^ 2)
    have h3 : ∑ v ∈ V3, (lb (G.degree v) + G.degree v ^ 2) = 49 * V3.card := by
      rw [Finset.sum_congr (g := fun _ => 49) rfl (fun v hv => by simp [(Finset.mem_filter.mp hv).2, lb]), Finset.sum_const, smul_eq_mul, mul_comm]
    have h4 : ∑ v ∈ V4, (lb (G.degree v) + G.degree v ^ 2) = 48 * V4.card := by
      rw [Finset.sum_congr (g := fun _ => 48) rfl (fun v hv => by simp [(Finset.mem_filter.mp hv).2, lb]), Finset.sum_const, smul_eq_mul, mul_comm]
    have h5 : ∑ v ∈ V5, (lb (G.degree v) + G.degree v ^ 2) = 51 * V5.card := by
      rw [Finset.sum_congr (g := fun _ => 51) rfl (fun v hv => by simp [(Finset.mem_filter.mp hv).2, lb]), Finset.sum_const, smul_eq_mul, mul_comm]
    have h6 : ∑ v ∈ V6, (lb (G.degree v) + G.degree v ^ 2) = 57 * V6.card := by
      rw [Finset.sum_congr (g := fun _ => 57) rfl (fun v hv => by simp [(Finset.mem_filter.mp hv).2, lb]), Finset.sum_const, smul_eq_mul, mul_comm]
    rw [hpart_val, h3, h4, h5, h6] at hle2
    exact hle2.trans hsum_all
  have hV3_le1 : V3.card ≤ 1 := by omega
  have hV3_zero : V3.card = 0 := by
    by_contra hne
    have hV3_eq1 : V3.card = 1 := by omega
    obtain ⟨v3, hv3⟩ := Finset.card_eq_one.mp hV3_eq1
    have hv3_mem : v3 ∈ V3 := hv3 ▸ Finset.mem_singleton_self v3
    have hv3_deg : G.degree v3 = 3 := (Finset.mem_filter.mp hv3_mem).2
    have hN_ge4 : ∀ u ∈ G.neighborFinset v3, 4 ≤ G.degree u := by
      intro u hu
      have hne' : u ≠ v3 := ((G.mem_neighborFinset v3 u).mp hu).ne.symm
      have hu_not3 : G.degree u ≠ 3 := by
        intro h3
        have : u ∈ V3 := Finset.mem_filter.mpr ⟨Finset.mem_univ u, h3⟩
        rw [hv3, Finset.mem_singleton] at this
        exact hne' this
      have := hmin3 u; omega
    have hsum12 : 12 ≤ ∑ u ∈ G.neighborFinset v3, G.degree u := by
      calc 12 = ∑ _u ∈ G.neighborFinset v3, (4 : ℕ) := by
            rw [Finset.sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree, hv3_deg]
        _ ≤ ∑ u ∈ G.neighborFinset v3, G.degree u := Finset.sum_le_sum hN_ge4
    have h40 : 40 ≤ eH v3 := by simpa [lb, hv3_deg] using h_eH_ge v3
    have hloc := hlocal v3
    omega
  have hmin4 : ∀ v : Fin 21, 4 ≤ G.degree v := by
    intro v
    have h3 := hmin3 v
    by_contra! hlt
    have hv3 : v ∈ V3 := Finset.mem_filter.mpr ⟨Finset.mem_univ v, by omega⟩
    have := Finset.card_pos.mpr ⟨v, hv3⟩
    omega
  refine ⟨hmin4, ?_⟩
  by_contra! hno32
  have hall_ge33 : ∀ v ∈ V4, 1 ≤ eH v - 32 := by
    intro v hv
    have hv4 : G.degree v = 4 := (Finset.mem_filter.mp hv).2
    have hge32 : 32 ≤ eH v := by simpa [lb, hv4] using h_eH_ge v
    have hne32 : eH v ≠ 32 := hno32 v hv4
    omega
  have hsum_v4 : V4.card ≤ ∑ v ∈ V4, (eH v - 32) := by
    calc V4.card = ∑ _v ∈ V4, (1 : ℕ) := by rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ v ∈ V4, (eH v - 32) := Finset.sum_le_sum hall_ge33
  -- From hcnt, hdeg_sum, hsq_lb, hV3_zero, hsum_v4: V6.card = 0 (V4.card = 3) or V6.card = 1 (V4.card = 4)!
  have hV6_le1 : V6.card = 0 ∨ V6.card = 1 := by omega
  have hsum_split (s t : Finset (Fin 21)) (f : Fin 21 → Nat) :
      ∑ u ∈ s, f u = (∑ u ∈ s ∩ t, f u) + (∑ u ∈ s \ t, f u) := by
    have hu : (s ∩ t) ∪ (s \ t) = s := by
      ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      by_cases hx : x ∈ t <;> simp [hx]
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter s t).symm, hu]
  have hV4_deg_ge2 : ∀ v ∈ V4, 2 ≤ (V4.filter (G.Adj v)).card := by
    intro v hv
    have hv4 : G.degree v = 4 := (Finset.mem_filter.mp hv).2
    have hge33 : 33 ≤ eH v := by have := hall_ge33 v hv; omega
    have hloc := hlocal v
    have hsum18 : ∑ u ∈ G.neighborFinset v, G.degree u ≤ 18 := by omega
    by_contra! hlt2
    have hsplit_N : ∑ u ∈ G.neighborFinset v, G.degree u ≥
        4 * (G.neighborFinset v ∩ V4).card + 5 * (G.neighborFinset v \ V4).card := by
      rw [hsum_split (G.neighborFinset v) V4 (fun u => G.degree u)]
      have h1 : 4 * (G.neighborFinset v ∩ V4).card ≤ ∑ u ∈ G.neighborFinset v ∩ V4, G.degree u := by
        calc 4 * (G.neighborFinset v ∩ V4).card = ∑ _u ∈ G.neighborFinset v ∩ V4, (4 : ℕ) := by
              rw [Finset.sum_const, smul_eq_mul, mul_comm]
          _ ≤ _ := Finset.sum_le_sum (fun u _ => hmin4 u)
      have h2 : 5 * (G.neighborFinset v \ V4).card ≤ ∑ u ∈ G.neighborFinset v \ V4, G.degree u := by
        calc 5 * (G.neighborFinset v \ V4).card = ∑ _u ∈ G.neighborFinset v \ V4, (5 : ℕ) := by
              rw [Finset.sum_const, smul_eq_mul, mul_comm]
          _ ≤ _ := Finset.sum_le_sum (fun u hu => by
              have hu4 := hmin4 u
              have hnot4 : u ∉ V4 := (Finset.mem_sdiff.mp hu).2
              have : G.degree u ≠ 4 := fun h => hnot4 (Finset.mem_filter.mpr ⟨Finset.mem_univ u, h⟩)
              omega)
      omega
    have heq_inter : G.neighborFinset v ∩ V4 = V4.filter (G.Adj v) := by
      ext u; simp [SimpleGraph.mem_neighborFinset, and_comm]
    have hcard_split : (G.neighborFinset v ∩ V4).card + (G.neighborFinset v \ V4).card = 4 := by
      rw [Finset.card_inter_add_card_sdiff, SimpleGraph.card_neighborFinset_eq_degree, hv4]
    rw [heq_inter] at hsplit_N hcard_split
    omega
  rcases hV6_le1 with hV6_0 | hV6_1
  · -- V6 = 0 => V4.card = 3, triangle-free on 3 vertices with min deg >= 2 => K3 contradiction!
    have hV4_3 : V4.card = 3 := by omega
    obtain ⟨a, b, c, hab, hac, hbc, hV4_eq⟩ := Finset.card_eq_three.mp hV4_3
    have ha : a ∈ V4 := hV4_eq ▸ by simp
    have hb : b ∈ V4 := hV4_eq ▸ by simp
    have hc : c ∈ V4 := hV4_eq ▸ by simp
    have adj_all (x y z : Fin 21) (hx : x ∈ V4) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
        (heq : V4 = {x, y, z}) : G.Adj x y ∧ G.Adj x z := by
      have h2 := hV4_deg_ge2 x hx
      have hsub : V4.filter (G.Adj x) ⊆ {y, z} := by
        intro u hu
        obtain ⟨huV, hxu⟩ := Finset.mem_filter.mp hu
        rw [heq] at huV
        simp only [Finset.mem_insert, Finset.mem_singleton] at huV ⊢
        rcases huV with rfl | rfl | rfl
        · exact (hxu.ne rfl).elim
        · exact Or.inl rfl
        · exact Or.inr rfl
      have hcard2 : ({y, z} : Finset (Fin 21)).card = 2 := Finset.card_pair hyz
      have heq2 : V4.filter (G.Adj x) = {y, z} := Finset.eq_of_subset_of_card_le hsub (by omega)
      exact ⟨(Finset.mem_filter.mp (heq2 ▸ (by simp : y ∈ ({y, z} : Finset (Fin 21))))).2,
             (Finset.mem_filter.mp (heq2 ▸ (by simp : z ∈ ({y, z} : Finset (Fin 21))))).2⟩
    have h1 := adj_all a b c ha hab hac hbc hV4_eq
    have h2 := adj_all b a c hb hab.symm hbc hac (by rw [hV4_eq]; exact Finset.insert_comm a b {c})
    exact ht {a, b, c} (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1.1, h1.2, h2.2⟩)
  · -- V6 = 1, V4 = 4, V5 = 16: C4 + R(3,4)=9 argument!
    have hV4_4 : V4.card = 4 := by omega
    obtain ⟨w, hw_eq⟩ := Finset.card_eq_one.mp hV6_1
    have hw_mem : w ∈ V6 := hw_eq ▸ Finset.mem_singleton_self w
    have hw6 : G.degree w = 6 := (Finset.mem_filter.mp hw_mem).2
    -- Every v in V4 has a_4(v) = 2 (triangle-free on 4 verts with min deg >= 2 -> C4!)
    have hV4_deg_eq2 (v : Fin 21) (hv : v ∈ V4) : (V4.filter (G.Adj v)).card = 2 := by
      have hge2 := hV4_deg_ge2 v hv
      by_contra hne2
      have hge3 : 3 ≤ (V4.filter (G.Adj v)).card := by omega
      -- v is adjacent to all 3 other vertices of V4; pick any one u of them, u has >= 2 neighbors in V4,
      -- so u has a neighbor z != v in V4, giving triangle v-u-z!
      have hsub : V4.filter (G.Adj v) ⊆ V4.erase v := by
        intro u hu; exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hu).2.ne.symm, (Finset.mem_filter.mp hu).1⟩
      have heq3 : V4.filter (G.Adj v) = V4.erase v :=
        Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_erase_of_mem hv, hV4_4]; omega)
      obtain ⟨u, hu⟩ := Finset.card_pos.mp (show 0 < (V4.filter (G.Adj v)).card by omega)
      have huV : u ∈ V4 := (Finset.mem_filter.mp hu).1
      have hvu : G.Adj v u := (Finset.mem_filter.mp hu).2
      have hu2 := hV4_deg_ge2 u huV
      have hne_v : ((V4.filter (G.Adj u)).erase v).Nonempty :=
        Finset.card_pos.mp (by have := Finset.pred_card_le_card_erase (s := V4.filter (G.Adj u)) (a := v); omega)
      obtain ⟨z, hz⟩ := hne_v
      have hzv : z ≠ v := (Finset.mem_erase.mp hz).1
      have hzV : z ∈ V4 := (Finset.mem_filter.mp (Finset.mem_erase.mp hz).2).1
      have huz : G.Adj u z := (Finset.mem_filter.mp (Finset.mem_erase.mp hz).2).2
      have hvz : G.Adj v z := (Finset.mem_filter.mp (heq3 ▸ Finset.mem_erase.mpr ⟨hzv, hzV⟩)).2
      exact ht {v, u, z} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hvu, hvz, huz⟩)
    -- No edge between V4 and w (since sum_{u in N(v)} d(u) <= 18 and 2 neighbors in V4 have deg 4, other 2 have deg >= 5 -> both must be 5!)
    have hV4_not_w (v : Fin 21) (hv : v ∈ V4) : ¬ G.Adj v w := by
      intro hvw
      have hv4 : G.degree v = 4 := (Finset.mem_filter.mp hv).2
      have hge33 : 33 ≤ eH v := by have := hall_ge33 v hv; omega
      have hloc := hlocal v
      have hsum18 : ∑ u ∈ G.neighborFinset v, G.degree u ≤ 18 := by omega
      have heq_inter : G.neighborFinset v ∩ V4 = V4.filter (G.Adj v) := by
        ext u; simp [SimpleGraph.mem_neighborFinset, and_comm]
      have hcard_diff : (G.neighborFinset v \ V4).card = 2 := by
        have h1 := Finset.card_inter_add_card_sdiff (G.neighborFinset v) V4
        rw [SimpleGraph.card_neighborFinset_eq_degree, hv4, heq_inter, hV4_deg_eq2 v hv] at h1; omega
      have hw_in : w ∈ G.neighborFinset v \ V4 := by
        refine Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset v w).mpr hvw, ?_⟩
        intro hw4; have := (Finset.mem_filter.mp hw4).2; omega
      have hsum_ge : 19 ≤ ∑ u ∈ G.neighborFinset v, G.degree u := by
        rw [hsum_split (G.neighborFinset v) V4 (fun u => G.degree u)]
        have h1 : 8 ≤ ∑ u ∈ G.neighborFinset v ∩ V4, G.degree u := by
          calc 8 = ∑ _u ∈ G.neighborFinset v ∩ V4, (4 : ℕ) := by
                rw [Finset.sum_const, smul_eq_mul, heq_inter, hV4_deg_eq2 v hv]
            _ ≤ _ := Finset.sum_le_sum (fun u _ => hmin4 u)
        have h2 : 11 ≤ ∑ u ∈ G.neighborFinset v \ V4, G.degree u := by
          rw [← Finset.add_sum_erase _ _ hw_in, hw6]
          have hrest : 5 ≤ ∑ u ∈ (G.neighborFinset v \ V4).erase w, G.degree u := by
            calc 5 = ∑ _u ∈ (G.neighborFinset v \ V4).erase w, (5 : ℕ) := by
                  rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem hw_in, hcard_diff]
              _ ≤ _ := Finset.sum_le_sum (fun u hu => by
                  have hnot4 : u ∉ V4 := (Finset.mem_sdiff.mp (Finset.mem_erase.mp hu).2).2
                  have h4 := hmin4 u
                  have : G.degree u ≠ 4 := fun h => hnot4 (Finset.mem_filter.mpr ⟨Finset.mem_univ u, h⟩)
                  omega)
          omega
        omega
      omega
    -- Every u in N(w) is in V5, and since eH u >= 26 => sum d(N(u)) <= 25, u must have >= 1 neighbor in V4!
    have hNw_hit_V4 (u : Fin 21) (hu : u ∈ G.neighborFinset w) : 1 ≤ (V4.filter (G.Adj u)).card := by
      have hwu : G.Adj w u := (G.mem_neighborFinset w u).mp hu
      have hu_not4 : u ∉ V4 := fun h4 => hV4_not_w u h4 hwu.symm
      have hu_not6 : u ∉ V6 := fun h6 => hwu.ne (by rw [hw_eq, Finset.mem_singleton] at h6; exact h6.symm)
      have hu5 : G.degree u = 5 := by
        have := hdeg_bounds u; have := hmin4 u
        have h1 : G.degree u ≠ 4 := fun h => hu_not4 (Finset.mem_filter.mpr ⟨Finset.mem_univ u, h⟩)
        have h2 : G.degree u ≠ 6 := fun h => hu_not6 (Finset.mem_filter.mpr ⟨Finset.mem_univ u, h⟩)
        omega
      have h26 : 26 ≤ eH u := by simpa [lb, hu5] using h_eH_ge u
      have hloc := hlocal u
      by_contra! h0
      have hdisj : ∀ z ∈ G.neighborFinset u, 5 ≤ G.degree z := by
        intro z hz
        have h4 := hmin4 z
        by_contra! hlt5
        have hz4 : z ∈ V4 := Finset.mem_filter.mpr ⟨Finset.mem_univ z, by omega⟩
        have hmem : z ∈ V4.filter (G.Adj u) := Finset.mem_filter.mpr ⟨hz4, (G.mem_neighborFinset u z).mp hz⟩
        have := Finset.card_pos.mpr ⟨z, hmem⟩
        omega
      have hw_in : w ∈ G.neighborFinset u := (G.mem_neighborFinset u w).mpr hwu.symm
      have h26sum : 26 ≤ ∑ z ∈ G.neighborFinset u, G.degree z := by
        rw [← Finset.add_sum_erase _ _ hw_in, hw6]
        have h20 : 20 ≤ ∑ z ∈ (G.neighborFinset u).erase w, G.degree z := by
          calc 20 = ∑ _z ∈ (G.neighborFinset u).erase w, (5 : ℕ) := by
                rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem hw_in,
                  SimpleGraph.card_neighborFinset_eq_degree, hu5]
            _ ≤ _ := Finset.sum_le_sum (fun z hz => hdisj z (Finset.mem_erase.mp hz).2)
        omega
      omega
    -- Double-count edges between V4 and B_w \ V4: total edges from V4 outside V4 is 8, >= 6 go to N(w), so <= 2 go to B_w \ V4!
    let Bw := Gᶜ.neighborFinset w
    have hV4_sub_Bw : V4 ⊆ Bw := by
      intro v hv
      have hne : v ≠ w := fun h => by
        have hv4 := (Finset.mem_filter.mp hv).2; subst h; omega
      exact (Gᶜ.mem_neighborFinset w v).mpr ⟨hne.symm, fun hadj => hV4_not_w v hv hadj.symm⟩
    let ext (v : Fin 21) : Nat := ((Bw \ V4).filter (G.Adj v)).card
    have hext_sum : ∑ v ∈ V4, ext v ≤ 2 := by
      have hV4_out : ∑ v ∈ V4, ((Finset.univ \ V4).filter (G.Adj v)).card = 8 := by
        calc ∑ v ∈ V4, ((Finset.univ \ V4).filter (G.Adj v)).card
            = ∑ v ∈ V4, (2 : ℕ) := Finset.sum_congr rfl fun v hv => by
              have h1 := Finset.card_inter_add_card_sdiff (G.neighborFinset v) V4
              have h2 : G.neighborFinset v ∩ V4 = V4.filter (G.Adj v) := by
                ext u; simp [SimpleGraph.mem_neighborFinset, and_comm]
              have h3 : G.neighborFinset v \ V4 = (Finset.univ \ V4).filter (G.Adj v) := by
                ext u; simp [SimpleGraph.mem_neighborFinset, and_comm]
              rw [SimpleGraph.card_neighborFinset_eq_degree, (Finset.mem_filter.mp hv).2,
                h2, hV4_deg_eq2 v hv, h3] at h1
              omega
          _ = 8 := by rw [Finset.sum_const, smul_eq_mul, hV4_4]
      have h_to_Nw : 6 ≤ ∑ v ∈ V4, ((G.neighborFinset w).filter (G.Adj v)).card := by
        have hcomm : ∑ v ∈ V4, ((G.neighborFinset w).filter (G.Adj v)).card =
            ∑ u ∈ G.neighborFinset w, (V4.filter (G.Adj u)).card := by
          simp only [Finset.card_filter]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by simp [G.adj_comm]
        rw [hcomm]
        calc 6 = ∑ _u ∈ G.neighborFinset w, (1 : ℕ) := by
              rw [Finset.sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree, hw6, mul_one]
          _ ≤ _ := Finset.sum_le_sum hNw_hit_V4
      have hsplit_out (v : Fin 21) (hv : v ∈ V4) :
          ext v + ((G.neighborFinset w).filter (G.Adj v)).card ≤ ((Finset.univ \ V4).filter (G.Adj v)).card := by
        have hdisj : Disjoint ((Bw \ V4).filter (G.Adj v)) ((G.neighborFinset w).filter (G.Adj v)) := by
          refine Finset.disjoint_left.mpr fun u hu1 hu2 => ?_
          exact ((Gᶜ.mem_neighborFinset w u).mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hu1).1).1).2
            ((G.mem_neighborFinset w u).mp (Finset.mem_filter.mp hu2).1)
        rw [← Finset.card_union_of_disjoint hdisj]
        refine Finset.card_le_card fun u hu => ?_
        rcases Finset.mem_union.mp hu with h1 | h2
        · exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ u,
            (Finset.mem_sdiff.mp (Finset.mem_filter.mp h1).1).2⟩, (Finset.mem_filter.mp h1).2⟩
        · have huN := (Finset.mem_filter.mp h2).1
          have hu_not4 : u ∉ V4 := fun h4 => hV4_not_w u h4 ((G.mem_neighborFinset w u).mp huN).symm
          exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, hu_not4⟩,
            (Finset.mem_filter.mp h2).2⟩
      have htot := Finset.sum_le_sum hsplit_out
      rw [Finset.sum_add_distrib, hV4_out] at htot
      omega
    -- Every v in V4 has a unique opposite vertex opp(v) in V4 \ {v} nonadjacent to v (C4 structure);
    -- if ext v = 0, then v has degree 2 in Bw, so opp(v) lies in the 11-vertex (3,5)-graph Bw \ ({v} U N_Bw(v))
    -- with degree ext (opp v), forcing 2 <= ext (opp v) by R(3,4) = 9!
    have h_opp_ext (v : Fin 21) (hv : v ∈ V4) (h0 : ext v = 0) :
        ∃ u ∈ V4, u ≠ v ∧ ¬ G.Adj v u ∧ 2 ≤ ext u := by
      have h_other : ((V4.erase v) \ (V4.filter (G.Adj v))).card = 1 := by
        have hsub : V4.filter (G.Adj v) ⊆ V4.erase v := fun x hx =>
          Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hx).2.ne.symm, (Finset.mem_filter.mp hx).1⟩
        have h1 := Finset.card_sdiff_add_card_eq_card hsub
        rw [Finset.card_erase_of_mem hv, hV4_4, hV4_deg_eq2 v hv] at h1; omega
      obtain ⟨u, hu_eq⟩ := Finset.card_eq_one.mp h_other
      have hu_mem : u ∈ (V4.erase v) \ (V4.filter (G.Adj v)) := hu_eq ▸ Finset.mem_singleton_self u
      have hu_er := (Finset.mem_sdiff.mp hu_mem).1
      have huv : u ≠ v := (Finset.mem_erase.mp hu_er).1
      have huV4 : u ∈ V4 := (Finset.mem_erase.mp hu_er).2
      have hnot_adj : ¬ G.Adj v u := fun ha => (Finset.mem_sdiff.mp hu_mem).2 (Finset.mem_filter.mpr ⟨huV4, ha⟩)
      have hNBw_eq : Bw.filter (G.Adj v) = V4.filter (G.Adj v) := by
        ext x
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hxB, hvx⟩
          by_cases hx4 : x ∈ V4
          · exact ⟨hx4, hvx⟩
          · exfalso
            have : x ∈ (Bw \ V4).filter (G.Adj v) := Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hxB, hx4⟩, hvx⟩
            have := Finset.card_pos.mpr ⟨x, this⟩
            dsimp only [ext] at h0
            exact absurd h0 (by omega)
        · rintro ⟨hx4, hvx⟩; exact ⟨hV4_sub_Bw hx4, hvx⟩
      let B1 := Bw \ insert v (Bw.filter (G.Adj v))
      have hB1card : B1.card = 11 := by
        have hvN : v ∉ Bw.filter (G.Adj v) := by simp
        have h1 := Finset.card_sdiff_add_card_eq_card (Finset.insert_subset (hV4_sub_Bw hv) (Finset.filter_subset (G.Adj v) Bw))
        change B1.card + (insert v (Bw.filter (G.Adj v))).card = Bw.card at h1
        rw [Finset.card_insert_of_notMem hvN, hNBw_eq, hV4_deg_eq2 v hv, hBcard w, hw6] at h1; omega
      have hB1small : Small G B1 5 := by
        have hBws := induce_small_of_nonneighbors G 6 hi w
        intro S hS hI
        have hvS : v ∉ S := fun h => by have := Finset.mem_sdiff.mp (hS h); simp at this
        have hind : Gᶜ.IsClique (insert v S : Finset (Fin 21)) := by
          rw [Finset.coe_insert, SimpleGraph.isClique_insert_of_notMem hvS]
          refine ⟨hI, fun x hx => ?_⟩
          have hx1 := Finset.mem_sdiff.mp (hS hx)
          exact ⟨fun e => hvS (e ▸ hx), fun ha => hx1.2 (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hx1.1, ha⟩))⟩
        have hlt := hBws (insert v S) (Finset.insert_subset (hV4_sub_Bw hv) (hS.trans Finset.sdiff_subset)) hind
        rw [Finset.card_insert_of_notMem hvS] at hlt; omega
      have huB1 : u ∈ B1 := by
        refine Finset.mem_sdiff.mpr ⟨hV4_sub_Bw huV4, ?_⟩
        simp only [Finset.mem_insert, hNBw_eq, Finset.mem_filter, not_or]
        exact ⟨huv, fun h => hnot_adj h.2⟩
      have hdegB1 := subset_min_deg G ht B1 4 9 OMA.Ramsey37Density.nine_works hB1small u huB1
      have hB1_sub : B1.filter (G.Adj u) ⊆ (Bw \ V4).filter (G.Adj u) := by
        intro x hx
        obtain ⟨hxB1, hux⟩ := Finset.mem_filter.mp hx
        obtain ⟨hxBw, hxnot⟩ := Finset.mem_sdiff.mp hxB1
        refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hxBw, ?_⟩, hux⟩
        intro hx4
        by_cases hxv : x = v
        · exact hxnot (Finset.mem_insert.mpr (Or.inl hxv))
        · by_cases hxu : x = u
          · exact hux.ne hxu.symm
          · have hx_in : x ∈ V4.filter (G.Adj v) := by
              by_contra hnot
              have : x ∈ (V4.erase v) \ (V4.filter (G.Adj v)) :=
                Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hxv, hx4⟩, hnot⟩
              rw [hu_eq, Finset.mem_singleton] at this
              exact hxu this
            rw [← hNBw_eq] at hx_in
            exact hxnot (Finset.mem_insert_of_mem hx_in)
      have hle := Finset.card_le_card hB1_sub
      exact ⟨u, huV4, huv, hnot_adj, by change 2 ≤ ((Bw \ V4).filter (G.Adj u)).card; omega⟩
    -- Since sum_{v in V4} ext v <= 2 and |V4| = 4, at least 2 vertices of V4 have ext = 0!
    let Z := V4.filter (fun v => ext v = 0)
    have hZ_ge2 : 2 ≤ Z.card := by
      by_contra! hlt2
      have hpos : 3 ≤ (V4 \ Z).card := by
        have h1 := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (fun v => ext v = 0) V4)
        change (V4 \ Z).card + Z.card = V4.card at h1
        omega
      have h3 : 3 ≤ ∑ v ∈ V4, ext v := by
        calc 3 ≤ (V4 \ Z).card := hpos
          _ = ∑ _v ∈ V4 \ Z, (1 : ℕ) := by rw [Finset.sum_const, smul_eq_mul, mul_one]
          _ ≤ ∑ v ∈ V4 \ Z, ext v := Finset.sum_le_sum fun v hv => by
              have hv4 := (Finset.mem_sdiff.mp hv).1
              have hnotZ := (Finset.mem_sdiff.mp hv).2
              have : ext v ≠ 0 := fun h0 => hnotZ (Finset.mem_filter.mpr ⟨hv4, h0⟩)
              omega
          _ ≤ ∑ v ∈ V4, ext v := Finset.sum_le_sum_of_subset Finset.sdiff_subset
      omega
    obtain ⟨v₁, hv₁, v₂, hv₂, hv12⟩ := Finset.one_lt_card.mp (by omega : 1 < Z.card)
    have hv₁4 : v₁ ∈ V4 := (Finset.mem_filter.mp hv₁).1
    have hv₂4 : v₂ ∈ V4 := (Finset.mem_filter.mp hv₂).1
    have hv₁0 : ext v₁ = 0 := (Finset.mem_filter.mp hv₁).2
    have hv₂0 : ext v₂ = 0 := (Finset.mem_filter.mp hv₂).2
    obtain ⟨u₁, hu₁4, hu1v1, hnot1, hu1_ge2⟩ := h_opp_ext v₁ hv₁4 hv₁0
    obtain ⟨u₂, hu₂4, hu2v2, hnot2, hu2_ge2⟩ := h_opp_ext v₂ hv₂4 hv₂0
    -- u1 != u2 because in C4 opposite vertices are distinct!
    have hu12 : u₁ ≠ u₂ := by
      intro heq
      subst heq
      -- Both v1 and v2 are nonadjacent to u1 in V4; together with u1 that's 3 vertices in V4 with u1 adjacent to <= 1, contradicting deg(u1)=2!
      have hsub : V4.filter (G.Adj u₁) ⊆ ((V4.erase u₁).erase v₁).erase v₂ := by
        intro x hx
        obtain ⟨hx4, hux⟩ := Finset.mem_filter.mp hx
        refine Finset.mem_erase.mpr ⟨fun h => hnot2 (h ▸ hux.symm),
          Finset.mem_erase.mpr ⟨fun h => hnot1 (h ▸ hux.symm),
          Finset.mem_erase.mpr ⟨hux.ne.symm, hx4⟩⟩⟩
      have hcard1 : (((V4.erase u₁).erase v₁).erase v₂).card = 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hv12.symm, Finset.mem_erase.mpr ⟨hu2v2.symm, hv₂4⟩⟩),
          Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hu1v1.symm, hv₁4⟩),
          Finset.card_erase_of_mem hu₁4, hV4_4]
      have := (Finset.card_le_card hsub).trans_eq hcard1
      have := hV4_deg_eq2 u₁ hu₁4
      omega
    have h4sum : 4 ≤ ∑ v ∈ V4, ext v := by
      have hsub : ({u₁, u₂} : Finset (Fin 21)) ⊆ V4 := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      have h2 := Finset.sum_le_sum_of_subset (f := ext) hsub
      rw [Finset.sum_pair hu12] at h2
      omega
    omega

/-- Stage 4: Classify every 21-vertex 51-edge (3,7)-graph on `Fin 21` into the 4 published codes. -/
private theorem classify_21_51 (G : SimpleGraph (Fin 21)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree 7) (h51 : G.edgeFinset.card = 51) :
    ∃ vs : List (Fin 21), vs.Nodup ∧ (∀ x, x ∈ vs) ∧ encode G vs ∈ targetCodes := by
  classical
  obtain ⟨hmin4, v0, hv0_deg, hv0_e32⟩ := exists_deg4_e32 G ht hi h51
  set B := Gᶜ.neighborFinset v0
  have hBcard : B.card = 16 := by
    have hc := G.degree_compl v0; rw [Fintype.card_fin] at hc
    rw [SimpleGraph.card_neighborFinset_eq_degree]; omega
  have hBsmall : Small G B 6 := induce_small_of_nonneighbors G 6 hi v0
  have hrem := RamseyDeficiency.removed G ht v0
  dsimp only at hrem
  rw [h51] at hrem
  change (G.induce (B : Set (Fin 21))).edgeFinset.card + ∑ u ∈ G.neighborFinset v0, G.degree u ≤ 51 at hrem
  have hsumN_le19 : ∑ u ∈ G.neighborFinset v0, G.degree u ≤ 19 := by omega
  obtain ⟨_, h4reg | hg16⟩ := classify_16_le32 G ht B hBcard hBsmall (by omega)
  · -- 4-regular (3,6;16): killed by dual cert4reg_to_21_0 / _1!
    obtain ⟨i, hi2, vs16, hnd16, hcov16, henc16⟩ := h4reg
    obtain ⟨_, cs, _, _, _, _, _, hlen, hmem, hok, _, hsum⟩ :=
      ext_on_rep G ht 7 hi v0 4 3 hv0_deg (fun u _ => hmin4 u) vs16 hnd16 hcov16 (g4regRep i) henc16
    have hbud : (cs.map (countBits (g4regRep i).length)).sum ≤ 15 := by omega
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · rw [show g4regRep 0 = g4reg_0 from rfl] at hmem hok hbud
      exact (viaDualGen 7 4 3 15 _ _ _ g4reg_0 cs w4reg_to_21_0 hlen hmem hok hbud cert4reg_to_21_0).elim
    · rw [show g4regRep 1 = g4reg_1 from rfl] at hmem hok hbud
      exact (viaDualGen 7 4 3 15 _ _ _ g4reg_1 cs w4reg_to_21_1 hlen hmem hok hbud cert4reg_to_21_1).elim
  · -- g16_0, g16_1, g16_2: tight dual filter + exact sorted enum + relabel to targetCodes!
    obtain ⟨i, hi3, vs16, hnd16, hcov16, henc16⟩ := hg16
    obtain ⟨front, cs, _, _, hnd21, hcov21, henc21, hlen, hmem, hok, hsort, hsum⟩ :=
      ext_on_rep G ht 7 hi v0 4 3 hv0_deg (fun u _ => hmin4 u) vs16 hnd16 hcov16 (g16Rep i) henc16
    have hbud : (cs.map (countBits (g16Rep i).length)).sum ≤ 15 := by omega
    have htop_sub (g : List Nat) : ∀ p ∈ (inds g).filter (fun p => p.2 == 5), p ∈ inds g ∧ 5 ≤ p.2 :=
      fun p hp => ⟨(List.mem_filter.mp hp).1, by have := (List.mem_filter.mp hp).2; simp only [beq_iff_eq] at this; omega⟩
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · rw [show g16Rep 0 = g16_0 from rfl] at hmem hok hbud henc21
      have htight := viaDualFilter 7 4 3 15 _ _ _ g16_0 cs w21_filt_0 tight21_0 hlen hmem hok hbud cert21_filt_0.1
      have hin := enumGenAux_complete 7 16 (inds g16_0) _ (htop_sub g16_0) 3 4 15 tight21_0 [] cs hlen
        (fun x hx => ⟨htight x hx, by obtain ⟨p, hp, rfl, hp1, _⟩ := hmem x hx; change 3 ≤ countBits g16_0.length p.1; rw [countBits_inds_eq g16_0 p hp]; exact hp1⟩)
        hsort cert21_filt_0.2 hbud (by simpa using hok)
      simp only [List.reverse_nil, List.nil_append] at hin
      have hany := List.all_eq_true.mp enum21_0_ok.1 cs hin
      obtain ⟨e, he_in, he_eq⟩ := List.any_eq_true.mp hany
      have he1 : e.1 = cs := of_decide_eq_true he_eq
      have hrel := of_decide_eq_true (List.all_eq_true.mp enum21_0_ok.2 e he_in)
      obtain ⟨vs21, hperm, henc'⟩ := relabel_real G e.2 (v0 :: front ++ vs16)
      rw [henc21, ← he1] at henc'
      change encode G vs21 = relabel e.2 (attach e.1 g16_0) at henc'
      exact ⟨vs21, hperm.nodup_iff.mpr hnd21, fun x => hperm.mem_iff.mpr (List.mem_toFinset.mp (hcov21 ▸ Finset.mem_univ x)), henc' ▸ hrel⟩
    · rw [show g16Rep 1 = g16_1 from rfl] at hmem hok hbud henc21
      have htight := viaDualFilter 7 4 3 15 _ _ _ g16_1 cs w21_filt_1 tight21_1 hlen hmem hok hbud cert21_filt_1.1
      have hin := enumGenAux_complete 7 16 (inds g16_1) _ (htop_sub g16_1) 3 4 15 tight21_1 [] cs hlen
        (fun x hx => ⟨htight x hx, by obtain ⟨p, hp, rfl, hp1, _⟩ := hmem x hx; change 3 ≤ countBits g16_1.length p.1; rw [countBits_inds_eq g16_1 p hp]; exact hp1⟩)
        hsort cert21_filt_1.2 hbud (by simpa using hok)
      simp only [List.reverse_nil, List.nil_append] at hin
      have hany := List.all_eq_true.mp enum21_1_ok.1 cs hin
      obtain ⟨e, he_in, he_eq⟩ := List.any_eq_true.mp hany
      have he1 : e.1 = cs := of_decide_eq_true he_eq
      have hrel := of_decide_eq_true (List.all_eq_true.mp enum21_1_ok.2 e he_in)
      obtain ⟨vs21, hperm, henc'⟩ := relabel_real G e.2 (v0 :: front ++ vs16)
      rw [henc21, ← he1] at henc'
      change encode G vs21 = relabel e.2 (attach e.1 g16_1) at henc'
      exact ⟨vs21, hperm.nodup_iff.mpr hnd21, fun x => hperm.mem_iff.mpr (List.mem_toFinset.mp (hcov21 ▸ Finset.mem_univ x)), henc' ▸ hrel⟩
    · rw [show g16Rep 2 = g16_2 from rfl] at hmem hok hbud henc21
      have htight := viaDualFilter 7 4 3 15 _ _ _ g16_2 cs w21_filt_2 tight21_2 hlen hmem hok hbud cert21_filt_2.1
      have hin := enumGenAux_complete 7 16 (inds g16_2) _ (htop_sub g16_2) 3 4 15 tight21_2 [] cs hlen
        (fun x hx => ⟨htight x hx, by obtain ⟨p, hp, rfl, hp1, _⟩ := hmem x hx; change 3 ≤ countBits g16_2.length p.1; rw [countBits_inds_eq g16_2 p hp]; exact hp1⟩)
        hsort cert21_filt_2.2 hbud (by simpa using hok)
      simp only [List.reverse_nil, List.nil_append] at hin
      have hany := List.all_eq_true.mp enum21_2_ok.1 cs hin
      obtain ⟨e, he_in, he_eq⟩ := List.any_eq_true.mp hany
      have he1 : e.1 = cs := of_decide_eq_true he_eq
      have hrel := of_decide_eq_true (List.all_eq_true.mp enum21_2_ok.2 e he_in)
      obtain ⟨vs21, hperm, henc'⟩ := relabel_real G e.2 (v0 :: front ++ vs16)
      rw [henc21, ← he1] at henc'
      change encode G vs21 = relabel e.2 (attach e.1 g16_2) at henc'
      exact ⟨vs21, hperm.nodup_iff.mpr hnd21, fun x => hperm.mem_iff.mpr (List.mem_toFinset.mp (hcov21 ▸ Finset.mem_univ x)), henc' ▸ hrel⟩

private theorem bits_eq_foldr (bs : List Bool) :
    bits bs = bs.foldr (fun b k => 2 * k + b.toNat) 0 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [bits, ih]

private theorem encode_eq_foldr {V : Type*} (D : SimpleGraph V) [DecidableRel D.Adj] (vs : List V) :
    (vs.foldr (fun v (p : List V × List ℕ) =>
      (v :: p.1, (p.1.map fun x => decide (D.Adj v x)).foldr (fun b k => 2 * k + b.toNat) 0 :: p.2)) ([], [])).1 = vs ∧
    (vs.foldr (fun v (p : List V × List ℕ) =>
      (v :: p.1, (p.1.map fun x => decide (D.Adj v x)).foldr (fun b k => 2 * k + b.toNat) 0 :: p.2)) ([], [])).2 =
    encode D vs := by
  induction vs with
  | nil => exact ⟨rfl, rfl⟩
  | cons v vs ih =>
    simp only [List.foldr_cons, ih.1, ih.2, encode, bits_eq_foldr, and_self]

private theorem encode_comap_map {α β : Type*} (D : SimpleGraph β) [DecidableRel D.Adj]
    (e : α ≃ β) (vs : List α) :
    encode D (vs.map e) = encode (D.comap e) vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.map_cons, encode, List.map_map, ih]
    rfl

theorem h2_solution : OMA.R_RamseyNumbers_ramsey_number_three_nine_R2.H2 := by
  classical
  intro V _ _ D _ hcard ht hi hedges
  let e : Fin 21 ≃ V := (Fintype.equivFinOfCardEq hcard).symm
  let G : SimpleGraph (Fin 21) := D.comap e
  let iso : G ≃g D := { toEquiv := e, map_rel_iff' := Iff.rfl }
  have hG3 : G.CliqueFree 3 := SimpleGraph.CliqueFree.comap iso.toEmbedding.isContained ht
  have hG7 : Gᶜ.CliqueFree 7 := SimpleGraph.CliqueFree.comap (SimpleGraph.Embedding.complEquiv iso.toEmbedding).isContained hi
  have hGe : G.edgeFinset.card = 51 := by
    have h1 := G.sum_degrees_eq_twice_card_edges
    have h2 := D.sum_degrees_eq_twice_card_edges
    have hsum : ∑ i, G.degree i = ∑ x, D.degree x := by
      calc ∑ i, G.degree i = ∑ i, D.degree (e i) := Finset.sum_congr rfl (fun i _ => (iso.degree_eq i).symm)
        _ = ∑ x, D.degree x := Equiv.sum_comp e (fun x => D.degree x)
    omega
  obtain ⟨vs, hnd, hall, hcode⟩ := classify_21_51 G hG3 hG7 hGe
  refine ⟨vs.map e, hnd.map e.injective, fun x => List.mem_map.mpr ⟨e.symm x, hall _, e.apply_symm_apply x⟩, ?_⟩
  change (vs.map e |>.foldr _ ([], [])).2 ∈ targetCodes
  rw [(encode_eq_foldr D (vs.map e)).2, encode_comap_map D e vs]
  exact hcode

end OMA.RamseyFinite
end RamseyFiniteSection

theorem OMA.solution : OMA.R_RamseyNumbers_ramsey_number_three_nine_R2.H2 :=
  OMA.RamseyFinite.h2_solution

