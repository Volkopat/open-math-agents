import OMAReductions.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1_H2_R1
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic.FinCases

/-!
# The 22-vertex extremal edge bound e(3,7;22) >= 59

We prove that every triangle-free graph on 22 vertices without an independent set of size 7
has at least 59 edges, establishing `OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1_H2_R1.H1`.

The proof consists of three parts:
1. Small Ramsey numbers R(3,2) = 3, R(3,3) = 6, R(3,4) = 9, R(3,5) = 14, and R(3,6) = 18.
   The 5-regular case of R(3,6) adapts the canonical neighborhood proof of
   `RamseyNumbers.ramsey_number_three_six.R1.H2` by @MrSeizy and @michielkosters; the
   degree-4 case is excluded by a single uniform dual packing certificate on the unique
   (3,5)-graph on 13 vertices.
2. The 16-vertex extremal bound e(3,6;16) >= 32, proved by adapting the finite graph
   enumeration and dual packing framework of `RamseyNumbers.ramsey_number_three_seven.R1.H2.R1.H1`
   to orders 12 and 13 with 13 zero-branching dual certificates.
3. The Graver--Yackel averaging ladder from e(3,3;3..5) through e(3,4;4..8),
   e(3,5;9..13), e(3,6;15..17), and finally e(3,7;22) >= 59.
-/

namespace OMA.Ramsey37Density

open RamseyNumbers SimpleGraph Finset
open OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1 (degree_lt nonneighbors_lt)

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
    have hlt := OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1.degree_lt H hH hHc i
    have hnl := OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1.nonneighbors_lt
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
  cs.length = d ∧ (∀ x ∈ cs, x ∈ usable k d b) ∧ okContacts k (inds b) cs = true
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
    (Bool.and_eq_true_iff.mp (guard_ cs [] (by simp))).1⟩, split⟩

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
  obtain ⟨len, mem, good⟩ := ext
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
  obtain ⟨len, mem, good⟩ := ext
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

/- Zero-branching dual certificates for e(3,6;16) >= 32. -/

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b3_0_32_cert : dualCheckSimple 31 b3_0 2 4 26 (allInd4 b3_0) = true := by
  decide +kernel

private def b4_0_32_w : List WeightedRow :=
  [((1224,4),3),((1576,4),2),((1128,4),1),((2244,4),2),((2340,4),2),((804,4),2),((204,4),1),
   ((108,4),3),((2322,4),1),((786,4),3),((2194,4),2),((1170,4),2),((1546,4),2),((2310,4),2),
   ((526,4),2),((142,4),2),((2241,4),2),((801,4),2),((2145,4),2),((1121,4),2),((1553,4),2),
   ((2321,4),3),((785,4),1),((1169,4),2)]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_0_32_cert : dualCheckSimple 31 b4_0 3 5 30 b4_0_32_w = true := by
  decide +kernel

private def b4_1_32_w : List WeightedRow :=
  [((1224,4),2),((2340,4),1),((804,4),1),((108,4),2),((786,4),1),((2194,4),1),((1170,4),1),
   ((2310,4),1),((526,4),1),((2241,4),1),((2321,4),1),((785,4),1),((1169,4),1)]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_1_32_cert : dualCheckSimple 31 b4_1 3 2 10 b4_1_32_w = true := by
  decide +kernel

private def b4_2_32_w : List WeightedRow :=
  [((1224,4),2),((1576,4),2),((2244,4),2),((2340,4),3),((204,4),1),((108,4),4),((786,4),4),
   ((2194,4),1),((1170,4),1),((1546,4),2),((2310,4),2),((142,4),2),((2241,4),1),((801,4),1),
   ((2145,4),1),((1121,4),1),((1553,4),3),((2321,4),3),((785,4),1),((1169,4),1)]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_2_32_cert : dualCheckSimple 31 b4_2 3 5 25 b4_2_32_w = true := by
  decide +kernel

private def b4_3_32_w : List WeightedRow :=
  [((1224,4),2),((804,4),1),((108,4),2),((2322,4),1),((786,4),1),((2194,4),1),((2310,4),1),
   ((526,4),1),((1121,4),1),((2321,4),1),((1169,4),2)]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_3_32_cert : dualCheckSimple 31 b4_3 3 3 11 b4_3_32_w = true := by
  decide +kernel

private def b4_4_32_w : List WeightedRow :=
  [((1576,4),1),((2244,4),1),((108,4),1),((786,4),1),((2194,4),1),((270,4),1),((1217,4),1),
   ((1553,4),1)]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_4_32_cert : dualCheckSimple 31 b4_4 3 2 7 b4_4_32_w = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_5_32_cert : dualCheckSimple 31 b4_5 3 3 15 (allInd4 b4_5) = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_6_32_cert : dualCheckSimple 31 b4_6 3 3 15 (allInd4 b4_6) = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_7_32_cert : dualCheckSimple 31 b4_7 3 1 2 [] = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_8_32_cert : dualCheckSimple 31 b4_8 3 2 13 (allInd4 b4_8) = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_9_32_cert : dualCheckSimple 31 b4_9 3 1 2 [] = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_10_32_cert : dualCheckSimple 31 b4_10 3 1 2 [] = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_11_32_cert : dualCheckSimple 31 b4_11 3 1 2 [] = true := by
  decide +kernel

theorem density16_of_min_deg (G : SimpleGraph (Fin 16)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree 6)
    (hmin : ∀ v, 2 ≤ G.degree v) : 32 ≤ G.edgeFinset.card := by
  classical
  by_contra! hsmall
  let U : Finset (Fin 16) := Finset.univ
  have bounded : Small G U 6 := by
    intro I _ hI
    by_contra! hc
    exact (hi.mono hc) I ⟨hI, rfl⟩
  have low : U.Nonempty → ∃ x ∈ U, (U.filter (G.Adj x)).card ≤ 3 := by
    intro _
    by_contra! hn
    have h4 (x : Fin 16) : 4 ≤ G.degree x := by
      have hh := hn x (Finset.mem_univ _)
      simp only [U, ← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree] at hh
      omega
    have w := Finset.sum_le_sum (s := U) (f := fun _ => 4) (g := fun x => G.degree x) (fun x _ => h4 x)
    have tot := G.sum_degrees_eq_twice_card_edges
    simp [U] at w
    omega
  have hn (l : List (Fin 16)) := relabel_real G (renumber (encode G l)) l
  obtain ⟨vs, d, b, cs, hv, cover, hd, hb, hcs, enc, ⟨r, _, hr⟩⟩ :=
    rootSplitting G ht normalized hn 5 U (by simp [U]) 3 bounded low
  have hdlb : 2 ≤ d := by
    have hmr := hmin r
    simp only [U, ← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree] at hr
    omega
  have h32 : 32 ≤ edges_ (attach cs b) := by
    have hb' : b ∈ levels normalized 5 (15 - d) 4 := by simpa [U] using hb
    interval_cases d
    · have ok := of_decide_eq_true (List.all_eq_true.mp smaller3 b hb')
      simp only [roots3, List.mem_cons, List.not_mem_nil, or_false] at ok
      subst ok
      exact viaDual32 b3_0 cs 2 4 26 (allInd4 b3_0) hcs b3_0_32_cert
    · have ok := of_decide_eq_true (List.all_eq_true.mp smaller4 b hb')
      simp only [roots4, List.mem_cons, List.not_mem_nil, or_false] at ok
      rcases ok with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact viaDual32 b4_0 cs 3 5 30 b4_0_32_w hcs b4_0_32_cert
      · exact viaDual32 b4_1 cs 3 2 10 b4_1_32_w hcs b4_1_32_cert
      · exact viaDual32 b4_2 cs 3 5 25 b4_2_32_w hcs b4_2_32_cert
      · exact viaDual32 b4_3 cs 3 3 11 b4_3_32_w hcs b4_3_32_cert
      · exact viaDual32 b4_4 cs 3 2 7 b4_4_32_w hcs b4_4_32_cert
      · exact viaDual32 b4_5 cs 3 3 15 (allInd4 b4_5) hcs b4_5_32_cert
      · exact viaDual32 b4_6 cs 3 3 15 (allInd4 b4_6) hcs b4_6_32_cert
      · exact viaDual32 b4_7 cs 3 1 2 [] hcs b4_7_32_cert
      · exact viaDual32 b4_8 cs 3 2 13 (allInd4 b4_8) hcs b4_8_32_cert
      · exact viaDual32 b4_9 cs 3 1 2 [] hcs b4_9_32_cert
      · exact viaDual32 b4_10 cs 3 1 2 [] hcs b4_10_32_cert
      · exact viaDual32 b4_11 cs 3 1 2 [] hcs b4_11_32_cert
  rw [← enc] at h32
  have dg : degrees (encode G vs) = vs.map (fun x => G.degree x) := by
    rw [degrees_encode]
    apply List.map_congr_left
    intro x _
    rw [sizeAt_finset G hv, cover]
    simp only [U, ← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree]
  have w := List.sum_toFinset (fun x => G.degree x) hv
  rw [cover] at w
  have tot := G.sum_degrees_eq_twice_card_edges
  have hh : 64 ≤ (degrees (encode G vs)).sum := by rw [energy]; omega
  rw [dg, ← w] at hh
  exact (by change 64 ≤ ∑ i, G.degree i at hh; omega : False)

end OMA.RamseyFinite
end RamseyFiniteSection

namespace OMA.Ramsey37Density

open RamseyNumbers SimpleGraph Finset
open OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1 (degree_lt nonneighbors_lt)
open OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1_H2_R1 (removed sum_neighbor_degrees)

lemma eighteen_works : IsGraphRamsey 18 3 6 := by
  classical
  rintro G ⟨hG, hc⟩
  have hdeg (v : Fin 18) : G.degree v = 4 ∨ G.degree v = 5 := by
    have hd := degree_lt G hG hc v
    have hdc := nonneighbors_lt fourteen_works G hG hc v
    rw [G.degree_compl, Fintype.card_fin] at hdc
    omega
  by_cases h4 : ∃ v, G.degree v = 4
  · exact OMA.RamseyFinite.no_deg4_18 G hG hc (fun v => by rcases hdeg v with h | h <;> omega) h4
  · push Not at h4
    have hreg : ∀ v, G.degree v = 5 := fun v => by
      rcases hdeg v with h | h
      · exact (h4 v h).elim
      · exact h
    exact OMA.Ramsey36Canonical.regular_impossible G hG hreg hc

lemma card_edgeFinset_ge_sub {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hc : Gᶜ.CliqueFree k) : n + 1 - k ≤ G.edgeFinset.card := by
  classical
  let S : Finset (Fin n) := G.edgeFinset.image (fun e => e.out.1)
  have hS : S.card ≤ G.edgeFinset.card := Finset.card_image_le
  have hindep : Gᶜ.IsClique ((Sᶜ : Finset (Fin n)) : Set (Fin n)) := by
    intro u hu v hv hne
    refine ⟨hne, fun hadj => ?_⟩
    let e : Sym2 (Fin n) := s(u, v)
    have hmem : e ∈ G.edgeFinset := G.mem_edgeFinset.mpr hadj
    have hpt : e.out.1 ∈ e := by
      have hq : s(e.out.1, e.out.2) = e := Quot.out_eq e
      exact Eq.mp (congrArg (fun x => e.out.1 ∈ x) hq) (by simp)
    have hinS : e.out.1 ∈ S := Finset.mem_image.mpr ⟨e, hmem, rfl⟩
    rcases Sym2.mem_iff.mp hpt with heq | heq
    · rw [heq] at hinS
      exact (Finset.mem_compl.mp (Finset.mem_coe.mp hu)) hinS
    · rw [heq] at hinS
      exact (Finset.mem_compl.mp (Finset.mem_coe.mp hv)) hinS
  have hlt : Sᶜ.card < k := by
    by_contra! hge
    exact hc.mono hge Sᶜ ⟨hindep, rfl⟩
  have hcompl := Finset.card_compl_add_card S
  rw [Fintype.card_fin] at hcompl
  omega

lemma gy_step {n k m : ℕ} (hr : IsGraphRamsey m 3 k) (lb : ℕ → ℕ)
    (hlb : ∀ d, n - 1 - d < m → ∀ (H : SimpleGraph (Fin (n - 1 - d))) [DecidableRel H.Adj],
      H.CliqueFree 3 → Hᶜ.CliqueFree k → lb (n - 1 - d) ≤ H.edgeFinset.card)
    (a b : ℕ)
    (hstep : ∀ d, d ≤ k → n - 1 - d < m → a + b * d ≤ d ^ 2 + lb (n - 1 - d))
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree (k + 1)) :
    n * a + 2 * b * G.edgeFinset.card ≤ n * G.edgeFinset.card := by
  have hlocal (v : Fin n) :
      lb (n - 1 - G.degree v) + ∑ w ∈ G.neighborFinset v, G.degree w ≤ G.edgeFinset.card := by
    have hdc := nonneighbors_lt hr G ht hc v
    rw [G.degree_compl, Fintype.card_fin] at hdc
    let B := Gᶜ.neighborFinset v
    let D := G.induce (B : Set (Fin n))
    have hBcard : Fintype.card B = n - 1 - G.degree v := by
      rw [Fintype.card_coe, SimpleGraph.card_neighborFinset_eq_degree, G.degree_compl, Fintype.card_fin]
    let eB : Fin (n - 1 - G.degree v) ≃ B := (Fintype.equivFinOfCardEq hBcard).symm
    let f : Fin (n - 1 - G.degree v) ↪ Fin n := eB.toEmbedding.trans (Function.Embedding.subtype _)
    let H := G.comap f
    let emb : H ↪g G := SimpleGraph.Embedding.comap f G
    let ec : Hᶜ ↪g Gᶜ := SimpleGraph.Embedding.complEquiv emb
    have hH3 : H.CliqueFree 3 := CliqueFree.comap emb.isContained ht
    have hHk : Hᶜ.CliqueFree k := by
      intro t ht'
      have hs : Gᶜ.IsNClique k (t.map f) := by
        refine ⟨?_, (Finset.card_map _).trans ht'.card_eq⟩
        intro x hx y hy hxy
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
        obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hy
        exact ec.map_adj_iff.mpr (ht'.isClique hi hj (fun he => hxy (congrArg f he)))
      apply hc _ (hs.insert (a := v) ?_)
      intro w hw
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hw
      exact (Gᶜ.mem_neighborFinset v (f i)).mp (eB i).2
    have hHlb : lb (n - 1 - G.degree v) ≤ H.edgeFinset.card := hlb (G.degree v) hdc H hH3 hHk
    let iso : H ≃g D := { toEquiv := eB, map_rel_iff' := Iff.rfl }
    have hdeg_sum : ∑ i, H.degree i = ∑ x, D.degree x := by
      calc ∑ i, H.degree i = ∑ i, D.degree (eB i) :=
            Finset.sum_congr rfl (fun i _ => (iso.degree_eq i).symm)
        _ = ∑ x, D.degree x := Equiv.sum_comp eB (fun x => D.degree x)
    have hcard_eq : H.edgeFinset.card = D.edgeFinset.card := by
      have h1 := H.sum_degrees_eq_twice_card_edges
      have h2 := D.sum_degrees_eq_twice_card_edges
      omega
    have hrem := removed G ht v
    dsimp only at hrem
    change D.edgeFinset.card + ∑ i ∈ G.neighborFinset v, G.degree i ≤ G.edgeFinset.card at hrem
    omega
  have hsum_local := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun v _ => hlocal v)
  rw [Finset.sum_add_distrib, sum_neighbor_degrees, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at hsum_local
  have hpoint (v : Fin n) : a + b * G.degree v ≤ G.degree v ^ 2 + lb (n - 1 - G.degree v) := by
    have hd := degree_lt G ht hc v
    have hdc := nonneighbors_lt hr G ht hc v
    rw [G.degree_compl, Fintype.card_fin] at hdc
    exact hstep (G.degree v) (by omega) hdc
  have hsum_pt := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun v _ => hpoint v)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum, G.sum_degrees_eq_twice_card_edges] at hsum_pt
  have hcomm : b * (2 * G.edgeFinset.card) = 2 * b * G.edgeFinset.card := by ring
  omega

/- Extremal edge bounds ladder. -/

lemma e33_3 (G : SimpleGraph (Fin 3)) [DecidableRel G.Adj]
    (_ : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 3) : 1 ≤ G.edgeFinset.card :=
  card_edgeFinset_ge_sub G hc

lemma e33_4 (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj]
    (_ : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 3) : 2 ≤ G.edgeFinset.card :=
  card_edgeFinset_ge_sub G hc

lemma e33_5 (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 3) : 5 ≤ G.edgeFinset.card := by
  have hdeg (v : Fin 5) : 2 ≤ G.degree v := by
    have hdc := nonneighbors_lt three_works G ht hc v
    rw [G.degree_compl, Fintype.card_fin] at hdc
    omega
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 5))) (fun v _ => hdeg v)
  have htot := G.sum_degrees_eq_twice_card_edges
  simp at hsum
  omega

private def lb33 : ℕ → ℕ
  | 3 => 1
  | 4 => 2
  | 5 => 5
  | _ => 0

private lemma lb33_ok : ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj],
    H.CliqueFree 3 → Hᶜ.CliqueFree 3 → lb33 m ≤ H.edgeFinset.card
  | 3, H, _, ht, hc => e33_3 H ht hc
  | 4, H, _, ht, hc => e33_4 H ht hc
  | 5, H, _, ht, hc => e33_5 H ht hc
  | 0, _, _, _, _ | 1, _, _, _, _ | 2, _, _, _, _ | _ + 6, _, _, _, _ => Nat.zero_le _

lemma e34_4 (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj]
    (_ : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 4) : 1 ≤ G.edgeFinset.card :=
  card_edgeFinset_ge_sub G hc

lemma e34_5 (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj]
    (_ : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 4) : 2 ≤ G.edgeFinset.card :=
  card_edgeFinset_ge_sub G hc

lemma e34_6 (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj]
    (_ : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 4) : 3 ≤ G.edgeFinset.card :=
  card_edgeFinset_ge_sub G hc

lemma e34_7 (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 4) : 6 ≤ G.edgeFinset.card := by
  have h := gy_step six_works lb33 (fun _ _ => lb33_ok _) 6 0
    (fun d hd hlt => by interval_cases d <;> simp [lb33] at hlt ⊢) G ht hc
  omega

lemma e34_8 (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 4) : 10 ≤ G.edgeFinset.card := by
  have h := gy_step six_works lb33 (fun _ _ => lb33_ok _) 7 1
    (fun d hd hlt => by interval_cases d <;> simp [lb33] at hlt ⊢) G ht hc
  omega

private def lb34 : ℕ → ℕ
  | 4 => 1
  | 5 => 2
  | 6 => 3
  | 7 => 6
  | 8 => 10
  | _ => 0

private lemma lb34_ok : ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj],
    H.CliqueFree 3 → Hᶜ.CliqueFree 4 → lb34 m ≤ H.edgeFinset.card
  | 4, H, _, ht, hc => e34_4 H ht hc
  | 5, H, _, ht, hc => e34_5 H ht hc
  | 6, H, _, ht, hc => e34_6 H ht hc
  | 7, H, _, ht, hc => e34_7 H ht hc
  | 8, H, _, ht, hc => e34_8 H ht hc
  | 0, _, _, _, _ | 1, _, _, _, _ | 2, _, _, _, _ | 3, _, _, _, _ | _ + 9, _, _, _, _ => Nat.zero_le _

lemma e35_9 (G : SimpleGraph (Fin 9)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 5) : 7 ≤ G.edgeFinset.card := by
  have h := gy_step nine_works lb34 (fun _ _ => lb34_ok _) 7 0
    (fun d hd hlt => by interval_cases d <;> simp [lb34] at hlt ⊢) G ht hc
  omega

lemma e35_10 (G : SimpleGraph (Fin 10)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 5) : 10 ≤ G.edgeFinset.card := by
  have h := gy_step nine_works lb34 (fun _ _ => lb34_ok _) 10 0
    (fun d hd hlt => by interval_cases d <;> simp [lb34] at hlt ⊢) G ht hc
  omega

lemma e35_11 (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 5) : 15 ≤ G.edgeFinset.card := by
  have h := gy_step nine_works lb34 (fun _ _ => lb34_ok _) 12 1
    (fun d hd hlt => by interval_cases d <;> simp [lb34] at hlt ⊢) G ht hc
  omega

lemma e35_12 (G : SimpleGraph (Fin 12)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 5) : 20 ≤ G.edgeFinset.card := by
  have h := gy_step nine_works lb34 (fun _ _ => lb34_ok _) 16 1
    (fun d hd hlt => by interval_cases d <;> simp [lb34] at hlt ⊢) G ht hc
  omega

lemma e35_13 (G : SimpleGraph (Fin 13)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 5) : 26 ≤ G.edgeFinset.card := by
  have hdeg (v : Fin 13) : 4 ≤ G.degree v := by
    have hdc := nonneighbors_lt nine_works G ht hc v
    rw [G.degree_compl, Fintype.card_fin] at hdc
    omega
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 13))) (fun v _ => hdeg v)
  have htot := G.sum_degrees_eq_twice_card_edges
  simp at hsum
  omega

private def lb35 : ℕ → ℕ
  | 9 => 7
  | 10 => 10
  | 11 => 15
  | 12 => 20
  | 13 => 26
  | _ => 0

private lemma lb35_ok : ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj],
    H.CliqueFree 3 → Hᶜ.CliqueFree 5 → lb35 m ≤ H.edgeFinset.card
  | 9, H, _, ht, hc => e35_9 H ht hc
  | 10, H, _, ht, hc => e35_10 H ht hc
  | 11, H, _, ht, hc => e35_11 H ht hc
  | 12, H, _, ht, hc => e35_12 H ht hc
  | 13, H, _, ht, hc => e35_13 H ht hc
  | 0, _, _, _, _ | 1, _, _, _, _ | 2, _, _, _, _ | 3, _, _, _, _ | 4, _, _, _, _
  | 5, _, _, _, _ | 6, _, _, _, _ | 7, _, _, _, _ | 8, _, _, _, _ | _ + 14, _, _, _, _ => Nat.zero_le _

lemma e36_15 (G : SimpleGraph (Fin 15)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 6) : 25 ≤ G.edgeFinset.card := by
  have h := gy_step fourteen_works lb35 (fun _ _ => lb35_ok _) 21 1
    (fun d hd hlt => by interval_cases d <;> simp [lb35] at hlt ⊢) G ht hc
  omega

lemma e36_16 (G : SimpleGraph (Fin 16)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 6) : 32 ≤ G.edgeFinset.card := by
  have hmin (v : Fin 16) : 2 ≤ G.degree v := by
    have hdc := nonneighbors_lt fourteen_works G ht hc v
    rw [G.degree_compl, Fintype.card_fin] at hdc
    omega
  exact OMA.RamseyFinite.density16_of_min_deg G ht hc hmin

lemma e36_17 (G : SimpleGraph (Fin 17)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 6) : 38 ≤ G.edgeFinset.card := by
  have h := gy_step fourteen_works lb35 (fun _ _ => lb35_ok _) 24 3
    (fun d hd hlt => by interval_cases d <;> simp [lb35] at hlt ⊢) G ht hc
  omega

private def lb36 : ℕ → ℕ
  | 15 => 25
  | 16 => 32
  | 17 => 38
  | _ => 0

private lemma lb36_ok : ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj],
    H.CliqueFree 3 → Hᶜ.CliqueFree 6 → lb36 m ≤ H.edgeFinset.card
  | 15, H, _, ht, hc => e36_15 H ht hc
  | 16, H, _, ht, hc => e36_16 H ht hc
  | 17, H, _, ht, hc => e36_17 H ht hc
  | 0, _, _, _, _ | 1, _, _, _, _ | 2, _, _, _, _ | 3, _, _, _, _ | 4, _, _, _, _
  | 5, _, _, _, _ | 6, _, _, _, _ | 7, _, _, _, _ | 8, _, _, _, _ | 9, _, _, _, _
  | 10, _, _, _, _ | 11, _, _, _, _ | 12, _, _, _, _ | 13, _, _, _, _ | 14, _, _, _, _
  | _ + 18, _, _, _, _ => Nat.zero_le _

theorem e37_22 : OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1_H2_R1.H1 := by
  intro G inst ht hc
  have h := gy_step eighteen_works lb36 (fun _ _ => lb36_ok _) 37 4
    (fun d hd hlt => by interval_cases d <;> simp [lb36] at hlt ⊢) G ht hc
  omega

end OMA.Ramsey37Density

theorem OMA.solution : OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1_H2_R1.H1 := by
  exact OMA.Ramsey37Density.e37_22
