import OMAReductions.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1_H1_R1
import Mathlib

/-!
# Erdős 1182: complement embeddings of orders four through six

The four-vertex case extends an independent triple. In the other cases,
the neighborhood masks into four independent vertices give a finite
supergraph of the original graph. The kernel checks a list of candidate
embeddings for each sorted mask profile. An independent five-set gives a
separate direct witness at order six.

Credit: @justusklocke-cloud
-/

open SimpleGraph

lemma erdos1182_independent_triple (C : SimpleGraph (Fin 7)) (ht : C.CliqueFree 3) :
    ∃ a b c : Fin 7, Cᶜ.Adj a b ∧ Cᶜ.Adj a c ∧ Cᶜ.Adj b c := by
  classical
  by_cases hlarge : ∃ v : Fin 7, 3 ≤ C.degree v
  · obtain ⟨v, hv⟩ := hlarge
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp (by
      rw [C.card_neighborFinset_eq_degree v]
      omega : 2 < (C.neighborFinset v).card)
    have hind := isIndepSet_neighborSet_of_triangleFree C ht v
    have ha' : a ∈ C.neighborSet v := (C.mem_neighborFinset v a).mp ha
    have hb' : b ∈ C.neighborSet v := (C.mem_neighborFinset v b).mp hb
    have hc' : c ∈ C.neighborSet v := (C.mem_neighborFinset v c).mp hc
    exact ⟨a, b, c, ⟨hab, hind ha' hb' hab⟩, ⟨hac, hind ha' hc' hac⟩, ⟨hbc, hind hb' hc' hbc⟩⟩
  · have hdeg (v : Fin 7) : 4 ≤ (Cᶜ.neighborFinset v).card := by
      have hv : C.degree v < 3 := Nat.lt_of_not_ge (fun h => hlarge ⟨v, h⟩)
      rw [Cᶜ.card_neighborFinset_eq_degree v, C.degree_compl v, Fintype.card_fin]
      omega
    let a : Fin 7 := 0
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (show 0 < (Cᶜ.neighborFinset a).card from by
      have := hdeg a
      omega)
    have hu : (Cᶜ.neighborFinset a ∪ Cᶜ.neighborFinset b).card ≤ 7 := by
      simpa only [Fintype.card_fin] using
        (Finset.card_le_univ (Cᶜ.neighborFinset a ∪ Cᶜ.neighborFinset b))
    have hs := Finset.card_union_add_card_inter (Cᶜ.neighborFinset a) (Cᶜ.neighborFinset b)
    obtain ⟨c, hc⟩ := Finset.card_pos.mp (show 0 < (Cᶜ.neighborFinset a ∩ Cᶜ.neighborFinset b).card from by
      have ha := hdeg a
      have hb := hdeg b
      omega)
    obtain ⟨hca, hcb⟩ := Finset.mem_inter.mp hc
    exact ⟨a, b, c, (Cᶜ.mem_neighborFinset a b).mp hb, (Cᶜ.mem_neighborFinset a c).mp hca,
      (Cᶜ.mem_neighborFinset b c).mp hcb⟩

open Finset

lemma erdos1182_extend_triple (C : SimpleGraph (Fin 7)) (hC : C.CliqueFree 3)
    (S : Finset (Fin 7)) (hS : C.IsIndepSet (S : Set (Fin 7))) (hThree : S.card = 3) :
    ∃ T : Finset (Fin 7), T.card = 4 ∧ ∃ v w : Fin 7,
      ∀ x ∈ T, ∀ y ∈ T, C.Adj x y → (x = v ∧ y = w) ∨ (x = w ∧ y = v) := by
  classical
  by_cases hsmall : ∃ v ∉ S, (S.filter (C.Adj v)).card ≤ 1
  · obtain ⟨v, hv, hcard⟩ := hsmall
    obtain ⟨w, hw⟩ := card_le_one_iff_subset_singleton.mp hcard
    refine ⟨insert v S, by rw [card_insert_of_notMem hv, hThree], v, w, ?_⟩
    intro x hx y hy hxy
    rcases mem_insert.mp hx with hxv | hx
    · subst x
      rcases mem_insert.mp hy with hyv | hy
      · subst y
        exact (hxy.ne rfl).elim
      · exact Or.inl ⟨rfl, mem_singleton.mp (hw (mem_filter.mpr ⟨hy, hxy⟩))⟩
    · rcases mem_insert.mp hy with hyv | hy
      · subst y
        exact Or.inr ⟨mem_singleton.mp (hw (mem_filter.mpr ⟨hx, hxy.symm⟩)), rfl⟩
      · exact (hS hx hy hxy.ne hxy).elim
  · push Not at hsmall
    let T : Finset (Fin 7) := univ \ S
    have hT : T.card = 4 := by
      change (univ \ S).card = 4
      rw [card_sdiff_of_subset (subset_univ S), card_univ, Fintype.card_fin, hThree]
    refine ⟨T, hT, 0, 0, ?_⟩
    intro x hx y hy hxy
    have hcx := hsmall x (mem_sdiff.mp hx).2
    have hcy := hsmall y (mem_sdiff.mp hy).2
    have hcommon : ∃ z, z ∈ S.filter (C.Adj x) ∧ z ∈ S.filter (C.Adj y) := by
      by_contra hn
      have hdisj : Disjoint (S.filter (C.Adj x)) (S.filter (C.Adj y)) :=
        disjoint_left.mpr fun z hz₁ hz₂ => hn ⟨z, hz₁, hz₂⟩
      have hsub : (S.filter (C.Adj x)) ∪ (S.filter (C.Adj y)) ⊆ S :=
        union_subset (filter_subset _ _) (filter_subset _ _)
      have hsum := card_le_card hsub
      rw [card_union_of_disjoint hdisj, hThree] at hsum
      omega
    obtain ⟨z, hxz, hyz⟩ := hcommon
    have hindep := C.isIndepSet_neighborSet_of_triangleFree hC z
    exact (hindep (mem_filter.mp hxz).2.symm (mem_filter.mp hyz).2.symm hxy.ne hxy).elim

lemma erdos1182_four (C : SimpleGraph (Fin 7)) (hC : C.CliqueFree 3) :
    ∃ T : Finset (Fin 7), T.card = 4 ∧ ∃ v w : Fin 7,
      ∀ x ∈ T, ∀ y ∈ T, C.Adj x y → (x = v ∧ y = w) ∨ (x = w ∧ y = v) := by
  obtain ⟨a,b,c,hab,hac,hbc⟩ := erdos1182_independent_triple C hC
  have hab' := (C.compl_adj a b).mp hab
  have hac' := (C.compl_adj a c).mp hac
  have hbc' := (C.compl_adj b c).mp hbc
  apply erdos1182_extend_triple C hC {a,b,c}
  · intro x hx y hy hne hxy
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | exact hne rfl | exact hab'.2 hxy | exact hab'.2 hxy.symm | exact hac'.2 hxy | exact hac'.2 hxy.symm | exact hbc'.2 hxy | exact hbc'.2 hxy.symm
  · simp [hab'.1, hac'.1, hbc'.1]


lemma erdos1182_embed_four (C : SimpleGraph (Fin 7)) (hC : C.CliqueFree 3) :
    ∃ f : Fin 4 ↪ Fin 7, ∀ i j, i < j →
      (2048 : Nat).testBit (i.val*4+j.val) = false → ¬ C.Adj (f i) (f j) := by
  classical
  obtain ⟨T, hT, r, s, he⟩ := erdos1182_four C hC
  obtain ⟨v, w, hv, hw, hvw, hedge⟩ :
      ∃ v w, v ∈ T ∧ w ∈ T ∧ v ≠ w ∧
        ∀ x ∈ T, ∀ y ∈ T, C.Adj x y → (x = v ∧ y = w) ∨ (x = w ∧ y = v) := by
    by_cases hadj : ∃ x ∈ T, ∃ y ∈ T, C.Adj x y
    · obtain ⟨x, hx, y, hy, hxy⟩ := hadj
      rcases he x hx y hy hxy with ⟨hxr, hys⟩ | ⟨hxs, hyr⟩
      · subst x
        subst y
        exact ⟨r, s, hx, hy, hxy.ne, he⟩
      · subst x
        subst y
        exact ⟨r, s, hy, hx, hxy.ne.symm, he⟩
    · obtain ⟨v, hv, w, hw, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < T.card)
      exact ⟨v, w, hv, hw, hne, fun x hx y hy hxy => (hadj ⟨x, hx, y, hy, hxy⟩).elim⟩
  have hsub : ({v,w} : Finset (Fin 7)) ⊆ T := by
    intro x hx
    simpa using (Finset.mem_insert.mp hx).elim (fun e => e ▸ hv)
      (fun e => (Finset.mem_singleton.mp e).symm ▸ hw)
  have hrem : (T \ {v,w}).card = 2 := by
    rw [card_sdiff_of_subset hsub, hT]
    simp [hvw]
  obtain ⟨a, b, hab, habset⟩ := Finset.card_eq_two.mp hrem
  have ha : a ∈ T \ {v,w} := by rw [habset]; simp
  have hb : b ∈ T \ {v,w} := by rw [habset]; simp
  have hav : a ≠ v := fun h => (mem_sdiff.mp ha).2 (by simp [h])
  have haw : a ≠ w := fun h => (mem_sdiff.mp ha).2 (by simp [h])
  have hbv : b ≠ v := fun h => (mem_sdiff.mp hb).2 (by simp [h])
  have hbw : b ≠ w := fun h => (mem_sdiff.mp hb).2 (by simp [h])
  let f : Fin 4 → Fin 7 := ![a,b,v,w]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [f]
  have hmem (i : Fin 4) : f i ∈ T := by
    fin_cases i
    · exact (mem_sdiff.mp ha).1
    · exact (mem_sdiff.mp hb).1
    · exact hv
    · exact hw
  refine ⟨⟨f, hf⟩, ?_⟩
  intro i j hij hbit hxy
  change C.Adj (f i) (f j) at hxy
  have hv' : f 2 = v := rfl
  have hw' : f 3 = w := rfl
  rcases hedge _ (hmem i) _ (hmem j) hxy with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · have hi' := hf (hi.trans hv'.symm)
    have hj' := hf (hj.trans hw'.symm)
    subst i
    subst j
    exact Bool.noConfusion hbit
  · have hi' := hf (hi.trans hw'.symm)
    have hj' := hf (hj.trans hv'.symm)
    subst i
    subst j
    omega

/- The upper Ramsey bound R(3,4) ≤ 9. -/

open SimpleGraph

private lemma erdos1182_triple_of_six {V : Type} [Fintype V] (C : SimpleGraph V)
    (ht : C.CliqueFree 3) (hV : 6 ≤ Fintype.card V) :
    ∃ a b c : V, Cᶜ.Adj a b ∧ Cᶜ.Adj a c ∧ Cᶜ.Adj b c := by
  classical
  have htriple (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (hv : 3 ≤ G.degree v) :
      ∃ a b c : V, G.Adj v a ∧ G.Adj v b ∧ G.Adj v c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
    simpa only [G.mem_neighborFinset] using (Finset.two_lt_card_iff.mp (by
      rw [G.card_neighborFinset_eq_degree v]
      omega : 2 < (G.neighborFinset v).card))
  by_cases hlarge : ∃ v : V, 3 ≤ C.degree v
  · obtain ⟨v, hv⟩ := hlarge
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := htriple C v hv
    have hind := isIndepSet_neighborSet_of_triangleFree C ht v
    exact ⟨a, b, c, ⟨hab, hind ha hb hab⟩, ⟨hac, hind ha hc hac⟩, ⟨hbc, hind hb hc hbc⟩⟩
  · obtain ⟨v⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
    have hdeg : C.degree v < 3 := Nat.lt_of_not_ge (fun h => hlarge ⟨v, h⟩)
    have hv : 3 ≤ Cᶜ.degree v := by rw [C.degree_compl v]; omega
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := htriple Cᶜ v hv
    by_cases hab' : C.Adj a b
    · by_cases hac' : C.Adj a c
      · have hind := isIndepSet_neighborSet_of_triangleFree C ht a
        exact ⟨v, b, c, hb, hc, ⟨hbc, hind hab' hac' hbc⟩⟩
      · exact ⟨v, a, c, ha, hc, ⟨hac, hac'⟩⟩
    · exact ⟨v, a, b, ha, hb, ⟨hab, hab'⟩⟩

lemma erdos1182_independent_four (C : SimpleGraph (Fin 9)) (ht : C.CliqueFree 3) :
    ∃ a b c d : Fin 9, Cᶜ.Adj a b ∧ Cᶜ.Adj a c ∧ Cᶜ.Adj a d ∧
      Cᶜ.Adj b c ∧ Cᶜ.Adj b d ∧ Cᶜ.Adj c d := by
  classical
  by_contra hfour
  have hupper (v : Fin 9) : C.degree v ≤ 3 := by
    by_contra! hv
    obtain ⟨a, b, c, d, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd⟩ :=
      Finset.three_lt_card_iff.mp (by rwa [C.card_neighborFinset_eq_degree v])
    have hind := isIndepSet_neighborSet_of_triangleFree C ht v
    have ha' : a ∈ C.neighborSet v := (C.mem_neighborFinset v a).mp ha
    have hb' : b ∈ C.neighborSet v := (C.mem_neighborFinset v b).mp hb
    have hc' : c ∈ C.neighborSet v := (C.mem_neighborFinset v c).mp hc
    have hd' : d ∈ C.neighborSet v := (C.mem_neighborFinset v d).mp hd
    exact hfour ⟨a, b, c, d, ⟨hab, hind ha' hb' hab⟩, ⟨hac, hind ha' hc' hac⟩,
      ⟨had, hind ha' hd' had⟩, ⟨hbc, hind hb' hc' hbc⟩, ⟨hbd, hind hb' hd' hbd⟩,
      ⟨hcd, hind hc' hd' hcd⟩⟩
  have hlower (v : Fin 9) : 3 ≤ C.degree v := by
    by_contra! hv
    let s := Cᶜ.neighborSet v
    have hs : 6 ≤ Fintype.card s := by
      change 6 ≤ Fintype.card (Cᶜ.neighborSet v)
      rw [Cᶜ.card_neighborSet_eq_degree v, C.degree_compl v, Fintype.card_fin]
      omega
    have hcs : (C.induce s).CliqueFree 3 := (C.cliqueFree_induce_iff s 3).mpr ht.cliqueFreeOn
    obtain ⟨a, b, c, hab, hac, hbc⟩ := erdos1182_triple_of_six (C.induce s) hcs hs
    have lift {x y : s} (h : (C.induce s)ᶜ.Adj x y) : Cᶜ.Adj x.val y.val :=
      ⟨fun hxy => h.1 (Subtype.ext hxy), h.2⟩
    exact hfour ⟨v, a.val, b.val, c.val, a.property, b.property, c.property,
      lift hab, lift hac, lift hbc⟩
  have hreg (v : Fin 9) : C.degree v = 3 := le_antisymm (hupper v) (hlower v)
  have hs := C.sum_degrees_eq_twice_card_edges
  simp only [hreg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  omega

/- Saturation by the neighborhoods into an independent set. -/

namespace Erdos1182SaturatedProfiles

open SimpleGraph Finset

private theorem getD_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (i : Fin n) (d : α) :
    (List.ofFn f).getD i.val d = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using i.isLt), List.getElem_ofFn]

def mask {V : Type} {r : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (left : Fin r → V) (x : V) : ℕ :=
  (BitVec.ofBoolListLE (List.ofFn fun i => decide (G.Adj (left i) x))).toNat

theorem mask_lt {V : Type} {r : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (left : Fin r → V) (x : V) : mask G left x < 2^r := by
  unfold mask
  simpa only [List.length_ofFn] using BitVec.isLt
    (x := BitVec.ofBoolListLE (List.ofFn fun i => decide (G.Adj (left i) x)))

theorem mask_at {V : Type} {r : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (left : Fin r → V) (x : V) (i : Fin r) :
    (mask G left x).testBit i.val = decide (G.Adj (left i) x) := by
  change (BitVec.ofBoolListLE (List.ofFn fun j => decide (G.Adj (left j) x))).getLsbD i.val = _
  rw [BitVec.getLsbD_ofBoolListLE, getD_ofFn]

theorem masks_disjoint_of_adjacent {V : Type} {r : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] (ht : G.CliqueFree 3)
    (left : Fin r → V) {x y : V} (hxy : G.Adj x y) :
    mask G left x &&& mask G left y = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.zero_testBit]
  by_cases h : i < r
  · let j : Fin r := ⟨i,h⟩
    change ((mask G left x).testBit j.val && (mask G left y).testBit j.val) = false
    rw [mask_at, mask_at]
    by_cases hx : G.Adj (left j) x
    · have hy : ¬ G.Adj (left j) y := fun hy =>
        G.isIndepSet_neighborSet_of_triangleFree ht (left j) hx hy hxy.ne hxy
      simp [hx, hy]
    · simp [hx]
  · have hx : (mask G left x).testBit i = false := Nat.testBit_eq_false_of_lt
      ((mask_lt G left x).trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hx]

/-- All edges allowed by the neighborhoods of the right-hand vertices. -/
def saturated (r : ℕ) (profile : List ℕ) (i j : ℕ) : Bool :=
  if i < r then
    if j < r then false else (profile.getD (j-r) 0).testBit i
  else if j < r then (profile.getD (i-r) 0).testBit j
  else (profile.getD (i-r) 0 &&& profile.getD (j-r) 0) == 0

theorem edge_in_saturated {V : Type} {r s : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (left : Fin r → V) (right : Fin s → V)
    (hi : ∀ i j, ¬ G.Adj (left i) (left j))
    (i j : Fin (r+s)) (he : G.Adj (Fin.addCases left right i) (Fin.addCases left right j)) :
    saturated r (List.ofFn (mask G left ∘ right)) i.val j.val = true := by
  revert he
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [Fin.addCases_left]
      exact fun h => (hi i j h).elim
    | right j =>
      simp only [Fin.addCases_left,Fin.addCases_right]
      intro h
      have hi' : (Fin.castAdd s i).val < r := i.isLt
      have hj' : ¬ (Fin.natAdd r j).val < r := by simp [Fin.natAdd]
      have hidx : (Fin.natAdd r j).val - r = j.val := by simp
      rw [saturated, if_pos hi', if_neg hj', hidx]
      rw [getD_ofFn]
      exact (mask_at G left (right j) i).trans (decide_eq_true h)
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [Fin.addCases_left,Fin.addCases_right]
      intro h
      have hi' : ¬ (Fin.natAdd r i).val < r := by simp [Fin.natAdd]
      have hj' : (Fin.castAdd s j).val < r := j.isLt
      have hidx : (Fin.natAdd r i).val - r = i.val := by simp
      rw [saturated, if_neg hi', if_pos hj', hidx]
      rw [getD_ofFn]
      exact (mask_at G left (right i) j).trans (decide_eq_true h.symm)
    | right j =>
      simp only [Fin.addCases_right]
      intro h
      have hi' : ¬ (Fin.natAdd r i).val < r := by simp [Fin.natAdd]
      have hj' : ¬ (Fin.natAdd r j).val < r := by simp [Fin.natAdd]
      have hidxi : (Fin.natAdd r i).val - r = i.val := by simp
      have hidxj : (Fin.natAdd r j).val - r = j.val := by simp
      rw [saturated, if_neg hi', if_neg hj', hidxi, hidxj]
      rw [getD_ofFn, getD_ofFn]
      simp [masks_disjoint_of_adjacent G ht left h]

theorem sort_outside {V : Type} [Fintype V] [DecidableEq V] {r s : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (hs : Sᶜ.card = s) (left : Fin r → V) :
    ∃ right : Fin s ↪ V, (∀ j, right j ∉ S) ∧
      (List.ofFn (mask G left ∘ right)).Pairwise (· ≤ ·) := by
  let cmp (v w : V) : Bool := decide (mask G left v ≤ mask G left w)
  let ordered := Sᶜ.toList.mergeSort cmp
  have hlen : ordered.length = s := by simp [ordered, hs]
  have hnodup : ordered.Nodup :=
    (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)
  let index (j : Fin s) : Fin ordered.length := ⟨j.val, by simpa [hlen] using j.isLt⟩
  let right : Fin s ↪ V := ⟨fun j => ordered.get (index j), by
    intro a b h
    exact Fin.ext (congrArg (fun x : Fin ordered.length => x.val) (hnodup.injective_get h))⟩
  have hr (j : Fin s) : right j ∉ S := by
    have hj := List.get_mem ordered (index j)
    have hU := (List.mergeSort_perm Sᶜ.toList cmp).mem_iff.mp hj
    simpa [right, List.get_eq_getElem] using hU
  have hpair : ordered.Pairwise (fun a b => mask G left a ≤ mask G left b) := by
    have h := List.pairwise_mergeSort (le := cmp)
      (fun a b c hab hbc => by
        simp only [cmp, decide_eq_true_eq] at hab hbc ⊢
        exact hab.trans hbc)
      (fun a b => by
        simp only [cmp, Bool.or_eq_true, decide_eq_true_eq]
        exact le_total _ _) Sᶜ.toList
    exact h.imp (fun h => of_decide_eq_true h)
  refine ⟨right, hr, ?_⟩
  have heq : List.ofFn (mask G left ∘ right) = ordered.map (mask G left) := by
    apply List.ext_getElem (by simp [hlen])
    intro n h₁ h₂
    simp [right, index, List.get_eq_getElem]
  rw [heq, List.pairwise_map]
  exact hpair

def unionEmbedding {V : Type} {r s : ℕ} (left : Fin r ↪ V) (right : Fin s ↪ V)
    (apart : ∀ i j, left i ≠ right j) : Fin (r+s) ↪ V where
  toFun := Fin.addCases left right
  inj' := by
    intro i j
    induction i using Fin.addCases with
    | left i =>
      induction j using Fin.addCases with
      | left j => simpa only [Fin.addCases_left, Fin.castAdd_inj] using left.injective.eq_iff.mp
      | right j =>
        simp only [Fin.addCases_left, Fin.addCases_right]
        exact fun h => (apart i j h).elim
    | right i =>
      induction j using Fin.addCases with
      | left j =>
        simp only [Fin.addCases_left, Fin.addCases_right]
        exact fun h => (apart j i h.symm).elim
      | right j => simpa only [Fin.addCases_right, Fin.natAdd_inj] using right.injective.eq_iff.mp

end Erdos1182SaturatedProfiles

namespace Erdos1182SaturatedProfiles

private def validEmbedding (r s k cap : ℕ) (profile vertex : List ℕ) : Bool :=
  decide (vertex.length = k ∧ vertex.Nodup ∧ ∀ x ∈ vertex, x < r+s) &&
    (List.range k).all (fun i => (List.range k).all (fun j =>
      !decide (i < j) || cap.testBit (i*k+j) ||
        !saturated r profile (vertex.getD i 0) (vertex.getD j 0)))

private theorem validEmbedding_sound {r s k cap : ℕ} {profile vertex : List ℕ}
    (h : validEmbedding r s k cap profile vertex = true) :
    ∃ f : Fin k ↪ Fin (r+s), (∀ i, (f i).val ∈ vertex) ∧
      ∀ i j, i < j → cap.testBit (i.val*k+j.val) = false →
        saturated r profile (f i).val (f j).val = false := by
  unfold validEmbedding at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hlen, hnodup, hbounds⟩, hpairs⟩ := h
  let index (i : Fin k) : Fin vertex.length := ⟨i.val, by simpa [hlen] using i.isLt⟩
  let f : Fin k ↪ Fin (r+s) := ⟨fun i => ⟨vertex.get (index i),
    hbounds _ (List.get_mem vertex (index i))⟩, by
      intro i j hij
      have e := hnodup.injective_get (congrArg (fun v : Fin (r+s) => v.val) hij)
      exact Fin.ext (congrArg (fun v : Fin vertex.length => v.val) e)⟩
  refine ⟨f, fun i => List.get_mem vertex (index i), ?_⟩
  intro i j hij hcap
  have hi := (List.all_eq_true.mp hpairs) i.val (List.mem_range.mpr i.isLt)
  have hpair := (List.all_eq_true.mp hi) j.val (List.mem_range.mpr j.isLt)
  rw [decide_eq_true (show i.val < j.val from hij), hcap] at hpair
  simp only [Bool.not_true, Bool.false_or, Bool.not_eq_true_eq_eq_false] at hpair
  rw [List.getD_eq_getElem _ _ (by simpa [hlen] using i.isLt),
    List.getD_eq_getElem _ _ (by simpa [hlen] using j.isLt)] at hpair
  exact hpair

private theorem saturated_append {r i j : ℕ} {initial tail : List ℕ}
    (hi : i < r + initial.length) (hj : j < r + initial.length) :
    saturated r (initial++tail) i j = saturated r initial i j := by
  have same {n : ℕ} (hn : n < initial.length) :
      (initial++tail).getD n 0 = initial.getD n 0 := by
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hn,
      List.getD_eq_getElem _ _ hn]
  unfold saturated
  split <;> split
  · rfl
  · rw [same (by omega : j-r < initial.length)]
  · rw [same (by omega : i-r < initial.length)]
  · rw [same (by omega : i-r < initial.length), same (by omega : j-r < initial.length)]

private inductive WitnessTree where
  | solved (vertex : List ℕ)
  | split (children : List WitnessTree)

private def validLeaf (r s k cap : ℕ) (initial vertex : List ℕ) : Bool :=
  validEmbedding r s k cap initial vertex &&
    vertex.all (fun v => decide (v < r + initial.length))

private def checkTree (r s k cap : ℕ) : ℕ → ℕ → List ℕ → WitnessTree → Bool
  | 0, _, initial, .solved v => validLeaf r s k cap initial v
  | 0, _, _, .split _ => false
  | _+1, _, initial, .solved v => validLeaf r s k cap initial v
  | len+1, low, initial, .split children =>
    decide (children.length = 2^r-low) && (List.range children.length).all (fun j =>
      checkTree r s k cap len (low+j) (initial++[low+j]) (children.getD j (.solved [])))

private theorem validLeaf_sound {r s k cap : ℕ} {initial tail v : List ℕ}
    (h : validLeaf r s k cap initial v = true) :
    ∃ f : Fin k ↪ Fin (r+s), ∀ i j, i < j →
      cap.testBit (i.val*k+j.val) = false →
      saturated r (initial++tail) (f i).val (f j).val = false := by
  unfold validLeaf at h
  rw [Bool.and_eq_true] at h
  obtain ⟨f,hrange,hf⟩ := validEmbedding_sound h.1
  refine ⟨f, fun i j hij hcap => ?_⟩
  have hb (i : Fin k) : (f i).val < r + initial.length :=
    of_decide_eq_true ((List.all_eq_true.mp h.2) _ (hrange i))
  rw [saturated_append (hb i) (hb j)]
  exact hf i j hij hcap

private theorem checkTree_sound {r s k cap : ℕ} {tree : WitnessTree}
    {low : ℕ} {initial tail : List ℕ}
    (h : checkTree r s k cap tail.length low initial tree = true)
    (hlo : ∀ x ∈ tail, low ≤ x) (hhi : ∀ x ∈ tail, x < 2^r)
    (hs : tail.Pairwise (· ≤ ·)) :
    ∃ f : Fin k ↪ Fin (r+s), ∀ i j, i < j →
      cap.testBit (i.val*k+j.val) = false →
      saturated r (initial++tail) (f i).val (f j).val = false := by
  induction tail generalizing tree initial low with
  | nil =>
    cases tree with
    | solved v => exact validLeaf_sound h
    | split _ => exact (Bool.false_ne_true h).elim
  | cons a rest ih =>
    cases tree with
    | solved v => exact validLeaf_sound h
    | split children =>
      change (decide (children.length = 2^r-low) && _) = true at h
      rw [Bool.and_eq_true, decide_eq_true_eq] at h
      have ha := hlo a (List.mem_cons_self)
      have ha' := hhi a (List.mem_cons_self)
      have hb : a-low < children.length := by omega
      have h' := (List.all_eq_true.mp h.2) (a-low) (List.mem_range.mpr hb)
      rw [Nat.add_sub_of_le ha] at h'
      have hrest := ih h' (fun x hx => (List.pairwise_cons.mp hs).1 x hx)
        (fun x hx => hhi x (List.mem_cons_of_mem a hx)) hs.of_cons
      simpa only [List.append_assoc, List.singleton_append] using hrest

private theorem verify_profile {r s k cap minimum : ℕ}
    {trees : ℕ → WitnessTree}
    (hs2 : 1 ≤ s)
    (certificate : ∀ a : Fin (2^r), minimum ≤ a.val →
      checkTree r s k cap (s-1) a.val [a.val] (trees a.val) = true)
    {profile : List ℕ} (hlen : profile.length = s)
    (hlo : ∀ x ∈ profile, minimum ≤ x) (hhi : ∀ x ∈ profile, x < 2^r)
    (hs : profile.Pairwise (· ≤ ·)) :
    ∃ f : Fin k ↪ Fin (r+s), ∀ i j, i < j →
      cap.testBit (i.val*k+j.val) = false →
      saturated r profile (f i).val (f j).val = false := by
  rcases profile with _ | ⟨a,tail⟩
  · simp at hlen; omega
  · have ha : minimum ≤ a := hlo _ (by simp)
    have htail : tail.length = s-1 := by simp at hlen; omega
    have hc := certificate ⟨a,hhi _ (by simp)⟩ ha
    rw [← htail] at hc
    exact checkTree_sound hc (fun x hx => (List.pairwise_cons.mp hs).1 _ hx)
      (fun x hx => hhi _ (by simp [hx])) hs.of_cons

end Erdos1182SaturatedProfiles

namespace Erdos1182SaturatedProfiles

private def tree5a0 : WitnessTree :=
  .solved [0, 1, 2, 3, 4]

private def tree5a1 : WitnessTree :=
  .solved [1, 2, 0, 3, 4]

private def tree5a2 : WitnessTree :=
  .solved [0, 2, 1, 3, 4]

private def tree5a3 : WitnessTree :=
  .solved [2, 3, 0, 1, 4]

private def tree5a4 : WitnessTree :=
  .solved [0, 1, 2, 3, 4]

private def tree5a5 : WitnessTree :=
  .solved [1, 3, 0, 2, 4]

private def tree5a6 : WitnessTree :=
  .solved [0, 3, 1, 2, 4]

private def tree5a7 : WitnessTree :=
  .split [
    .split [
      .split [
        .solved [3, 4, 5, 6, 7],
        .solved [0, 1, 2, 3, 7],
        .solved [1, 2, 0, 3, 7],
        .solved [0, 2, 1, 3, 7],
        .solved [4, 5, 3, 6, 7],
        .solved [0, 1, 2, 3, 7],
        .solved [4, 5, 3, 6, 7],
        .solved [4, 5, 3, 6, 7],
        .solved [4, 5, 3, 6, 7]
      ],
      .solved [0, 1, 2, 3, 6],
      .solved [1, 2, 0, 3, 6],
      .solved [0, 2, 1, 3, 6],
      .split [
        .solved [6, 7, 4, 5, 2],
        .solved [0, 1, 2, 3, 7],
        .solved [4, 5, 6, 7, 3],
        .solved [4, 5, 6, 7, 3],
        .solved [4, 5, 6, 7, 3]
      ],
      .solved [0, 1, 2, 3, 6],
      .split [
        .solved [6, 7, 4, 5, 1],
        .solved [4, 5, 6, 7, 3],
        .solved [4, 5, 6, 7, 3]
      ],
      .split [
        .solved [6, 7, 4, 5, 0],
        .solved [4, 5, 6, 7, 3]
      ],
      .split [
        .solved [4, 5, 6, 7, 3]
      ]
    ],
    .solved [0, 1, 2, 3, 5],
    .solved [1, 2, 0, 3, 5],
    .solved [0, 2, 1, 3, 5],
    .split [
      .split [
        .solved [5, 6, 2, 7, 4],
        .solved [0, 1, 2, 3, 7],
        .solved [5, 6, 4, 7, 2],
        .solved [5, 6, 4, 7, 2],
        .solved [5, 6, 4, 7, 2]
      ],
      .solved [0, 1, 2, 3, 6],
      .split [
        .solved [6, 7, 4, 5, 1],
        .split [
          .solved [7, 8, 4, 5, 0],
          .solved [4, 5, 6, 7, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 8]
        ]
      ],
      .split [
        .solved [6, 7, 4, 5, 0],
        .split [
          .solved [4, 5, 6, 7, 8]
        ]
      ],
      .split [
        .split [
          .solved [4, 5, 6, 7, 8]
        ]
      ]
    ],
    .solved [0, 1, 2, 3, 5],
    .split [
      .split [
        .solved [5, 6, 1, 7, 4],
        .solved [5, 6, 4, 7, 1],
        .solved [5, 6, 4, 7, 1]
      ],
      .split [
        .solved [6, 7, 4, 5, 0],
        .split [
          .solved [4, 5, 6, 7, 8]
        ]
      ],
      .split [
        .split [
          .solved [4, 5, 6, 7, 8]
        ]
      ]
    ],
    .split [
      .split [
        .solved [5, 6, 0, 7, 4],
        .solved [5, 6, 4, 7, 0]
      ],
      .split [
        .split [
          .solved [4, 5, 6, 7, 8]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [4, 5, 6, 7, 8]
        ]
      ]
    ]
  ]

private def tree5a8 : WitnessTree :=
  .solved [0, 1, 2, 3, 4]

private def tree5a9 : WitnessTree :=
  .solved [1, 2, 0, 3, 4]

private def tree5a10 : WitnessTree :=
  .solved [0, 2, 1, 3, 4]

private def tree5a11 : WitnessTree :=
  .split [
    .split [
      .split [
        .solved [2, 4, 5, 6, 7],
        .solved [0, 1, 2, 3, 7],
        .solved [4, 5, 2, 6, 7],
        .solved [4, 5, 2, 6, 7],
        .solved [4, 5, 2, 6, 7]
      ],
      .solved [0, 1, 2, 3, 6],
      .split [
        .solved [6, 7, 4, 5, 1],
        .solved [4, 5, 6, 7, 2],
        .solved [4, 5, 6, 7, 2]
      ],
      .split [
        .solved [6, 7, 4, 5, 0],
        .solved [4, 5, 6, 7, 2]
      ],
      .split [
        .solved [4, 5, 6, 7, 2]
      ]
    ],
    .solved [0, 1, 2, 3, 5],
    .split [
      .split [
        .solved [5, 6, 1, 7, 4],
        .solved [5, 6, 4, 7, 1],
        .solved [5, 6, 4, 7, 1]
      ],
      .split [
        .solved [6, 7, 4, 5, 0],
        .split [
          .solved [4, 5, 6, 7, 8]
        ]
      ],
      .split [
        .split [
          .solved [4, 5, 6, 7, 8]
        ]
      ]
    ],
    .split [
      .split [
        .solved [5, 6, 0, 7, 4],
        .solved [5, 6, 4, 7, 0]
      ],
      .split [
        .split [
          .solved [4, 5, 6, 7, 8]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [4, 5, 6, 7, 8]
        ]
      ]
    ]
  ]

private def tree5a12 : WitnessTree :=
  .solved [0, 1, 2, 3, 4]

private def tree5a13 : WitnessTree :=
  .split [
    .split [
      .split [
        .solved [1, 4, 5, 6, 7],
        .solved [4, 5, 1, 6, 7],
        .solved [4, 5, 1, 6, 7]
      ],
      .split [
        .solved [6, 7, 4, 5, 0],
        .solved [4, 5, 6, 7, 1]
      ],
      .split [
        .solved [4, 5, 6, 7, 1]
      ]
    ],
    .split [
      .split [
        .solved [5, 6, 0, 7, 4],
        .solved [5, 6, 4, 7, 0]
      ],
      .split [
        .split [
          .solved [4, 5, 6, 7, 8]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [4, 5, 6, 7, 8]
        ]
      ]
    ]
  ]

private def tree5a14 : WitnessTree :=
  .split [
    .split [
      .split [
        .solved [0, 4, 5, 6, 7],
        .solved [4, 5, 0, 6, 7]
      ],
      .split [
        .solved [4, 5, 6, 7, 0]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [4, 5, 6, 7, 8]
        ]
      ]
    ]
  ]

private def tree5a15 : WitnessTree :=
  .split [
    .split [
      .split [
        .split [
          .solved [4, 5, 6, 7, 8]
        ]
      ]
    ]
  ]

private def trees5 : ℕ → WitnessTree
  | 0 => tree5a0
  | 1 => tree5a1
  | 2 => tree5a2
  | 3 => tree5a3
  | 4 => tree5a4
  | 5 => tree5a5
  | 6 => tree5a6
  | 7 => tree5a7
  | 8 => tree5a8
  | 9 => tree5a9
  | 10 => tree5a10
  | 11 => tree5a11
  | 12 => tree5a12
  | 13 => tree5a13
  | 14 => tree5a14
  | 15 => tree5a15
  | _ => .solved []

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem masks5 (a : Fin 16) (hlo : 0 ≤ a.val) :
    checkTree 4 5 5 540672 4 a.val [a.val] (trees5 a.val) = true := by
  fin_cases a <;> norm_num at hlo
  all_goals as_aux_lemma => decide +kernel

private def tree6a1 : WitnessTree :=
  .split [
    .solved [1, 2, 3, 4, 0, 5],
    .solved [0, 2, 3, 1, 5, 4],
    .solved [1, 2, 3, 4, 0, 5],
    .solved [0, 1, 3, 2, 5, 4],
    .solved [2, 1, 3, 4, 0, 5],
    .split [
      .split [
        .split [
          .solved [0, 3, 5, 6, 7, 8],
          .solved [0, 3, 5, 6, 7, 8],
          .solved [0, 1, 2, 3, 8, 4],
          .solved [3, 1, 2, 4, 0, 8],
          .solved [0, 5, 6, 3, 8, 7],
          .solved [0, 5, 6, 7, 3, 8],
          .solved [0, 5, 6, 3, 8, 7],
          .solved [0, 5, 6, 7, 3, 8],
          .solved [0, 5, 6, 3, 8, 7],
          .solved [0, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [3, 5, 6, 7, 0, 8],
          .solved [0, 1, 2, 3, 8, 4],
          .solved [3, 1, 2, 4, 0, 8],
          .solved [0, 5, 6, 3, 8, 7],
          .solved [3, 5, 6, 7, 0, 8],
          .solved [0, 5, 6, 3, 8, 7],
          .solved [3, 5, 6, 7, 0, 8],
          .solved [0, 5, 6, 3, 8, 7],
          .solved [3, 5, 6, 7, 0, 8]
        ],
        .solved [0, 1, 2, 3, 7, 4],
        .solved [3, 1, 2, 4, 0, 7],
        .split [
          .solved [0, 7, 8, 5, 2, 6],
          .solved [0, 5, 6, 7, 3, 8],
          .solved [0, 5, 6, 7, 3, 8],
          .solved [0, 5, 6, 7, 3, 8],
          .solved [0, 5, 6, 7, 3, 8],
          .solved [0, 5, 6, 7, 3, 8]
        ],
        .split [
          .split [
            .solved [2, 7, 8, 9, 4, 5],
            .solved [0, 5, 6, 9, 3, 7],
            .solved [4, 7, 8, 9, 2, 5],
            .solved [0, 5, 6, 9, 3, 7],
            .solved [4, 7, 8, 9, 2, 5]
          ],
          .solved [0, 5, 6, 8, 3, 7],
          .split [
            .solved [4, 8, 9, 7, 1, 5],
            .solved [0, 5, 6, 9, 3, 7],
            .solved [5, 7, 8, 9, 6, 4]
          ],
          .solved [0, 5, 6, 8, 3, 7],
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ],
        .split [
          .solved [0, 7, 8, 5, 1, 6],
          .solved [0, 5, 6, 7, 3, 8],
          .solved [0, 5, 6, 7, 3, 8],
          .solved [0, 5, 6, 7, 3, 8]
        ],
        .split [
          .split [
            .solved [1, 7, 8, 9, 4, 5],
            .solved [0, 5, 6, 9, 3, 7],
            .solved [4, 7, 8, 9, 1, 5]
          ],
          .solved [0, 5, 6, 8, 3, 7],
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ],
        .split [
          .solved [0, 5, 6, 7, 3, 8],
          .solved [0, 5, 6, 7, 3, 8]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ]
      ],
      .split [
        .split [
          .solved [3, 6, 7, 4, 5, 8],
          .solved [0, 1, 2, 3, 8, 4],
          .solved [3, 1, 2, 4, 0, 8],
          .solved [3, 6, 7, 5, 4, 8],
          .solved [3, 6, 7, 4, 5, 8],
          .solved [3, 6, 7, 5, 4, 8],
          .solved [3, 6, 7, 4, 5, 8],
          .solved [3, 6, 7, 5, 4, 8],
          .solved [3, 6, 7, 4, 5, 8]
        ],
        .solved [0, 1, 2, 3, 7, 4],
        .solved [3, 1, 2, 4, 0, 7],
        .split [
          .solved [0, 7, 8, 5, 2, 6],
          .split [
            .solved [4, 8, 9, 6, 2, 5],
            .solved [5, 7, 9, 6, 0, 8],
            .solved [5, 6, 8, 9, 7, 4],
            .solved [5, 7, 9, 6, 0, 8],
            .solved [5, 6, 8, 9, 7, 4]
          ],
          .split [
            .solved [0, 8, 9, 5, 1, 6],
            .solved [5, 7, 8, 6, 0, 9],
            .solved [0, 5, 7, 8, 9, 6],
            .solved [5, 7, 8, 6, 0, 9]
          ],
          .split [
            .solved [4, 8, 9, 6, 1, 5],
            .solved [5, 7, 9, 6, 0, 8],
            .solved [5, 6, 8, 9, 7, 4]
          ],
          .split [
            .solved [0, 5, 7, 8, 9, 6],
            .solved [5, 7, 8, 6, 0, 9]
          ],
          .split [
            .solved [5, 6, 8, 9, 7, 4]
          ]
        ],
        .split [
          .solved [4, 7, 8, 6, 2, 5],
          .split [
            .solved [0, 8, 9, 5, 1, 6],
            .solved [5, 6, 7, 9, 8, 4],
            .solved [5, 8, 9, 6, 0, 7],
            .solved [5, 6, 7, 9, 8, 4]
          ],
          .split [
            .solved [4, 8, 9, 6, 1, 5],
            .solved [5, 6, 7, 8, 9, 4],
            .solved [4, 6, 7, 8, 9, 5]
          ],
          .split [
            .solved [5, 8, 9, 6, 0, 7],
            .solved [5, 6, 7, 9, 8, 4]
          ],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .solved [0, 7, 8, 5, 1, 6],
          .split [
            .solved [4, 8, 9, 6, 1, 5],
            .solved [5, 7, 9, 6, 0, 8],
            .solved [5, 6, 8, 9, 7, 4]
          ],
          .split [
            .solved [0, 5, 7, 8, 9, 6],
            .solved [5, 7, 8, 6, 0, 9]
          ],
          .split [
            .solved [5, 6, 8, 9, 7, 4]
          ]
        ],
        .split [
          .solved [4, 7, 8, 6, 1, 5],
          .split [
            .solved [5, 8, 9, 6, 0, 7],
            .solved [5, 6, 7, 9, 8, 4]
          ],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .split [
            .solved [0, 5, 7, 8, 9, 6],
            .solved [5, 7, 8, 6, 0, 9]
          ],
          .split [
            .solved [5, 6, 8, 9, 7, 4]
          ]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .solved [0, 1, 2, 3, 6, 4],
      .solved [3, 1, 2, 4, 0, 6],
      .split [
        .split [
          .solved [0, 6, 7, 2, 5, 8],
          .solved [0, 6, 7, 2, 5, 8],
          .solved [0, 6, 7, 5, 2, 8],
          .solved [0, 6, 7, 5, 2, 8],
          .solved [0, 6, 7, 5, 2, 8],
          .solved [0, 6, 7, 5, 2, 8]
        ],
        .split [
          .solved [2, 7, 8, 6, 4, 5],
          .split [
            .solved [0, 8, 9, 5, 1, 6],
            .solved [5, 6, 8, 7, 0, 9],
            .solved [0, 5, 6, 8, 9, 7],
            .solved [5, 6, 8, 7, 0, 9]
          ],
          .split [
            .solved [4, 8, 9, 7, 1, 5],
            .solved [5, 6, 9, 7, 0, 8],
            .solved [5, 7, 8, 9, 6, 4]
          ],
          .split [
            .solved [0, 5, 6, 8, 9, 7],
            .solved [5, 6, 8, 7, 0, 9]
          ],
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ],
        .split [
          .solved [0, 7, 8, 5, 1, 6],
          .split [
            .solved [5, 6, 7, 8, 0, 9],
            .solved [0, 5, 6, 7, 9, 8],
            .solved [5, 6, 7, 8, 0, 9]
          ],
          .split [
            .solved [0, 5, 6, 7, 8, 9],
            .solved [0, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [5, 6, 7, 8, 0, 9]
          ]
        ],
        .split [
          .split [
            .solved [1, 7, 8, 9, 4, 5],
            .solved [5, 6, 9, 7, 0, 8],
            .solved [4, 7, 8, 9, 1, 5]
          ],
          .split [
            .solved [0, 5, 6, 8, 9, 7],
            .solved [5, 6, 8, 7, 0, 9]
          ],
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ],
        .split [
          .split [
            .solved [0, 5, 6, 7, 8, 9],
            .solved [0, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [5, 6, 7, 8, 0, 9]
          ]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ]
      ],
      .split [
        .split [
          .solved [2, 6, 7, 8, 4, 5],
          .split [
            .solved [0, 8, 9, 5, 1, 6],
            .solved [4, 6, 7, 9, 2, 5],
            .solved [5, 8, 9, 6, 0, 7],
            .solved [4, 6, 7, 9, 2, 5]
          ],
          .solved [4, 6, 7, 8, 2, 5],
          .split [
            .solved [5, 8, 9, 6, 0, 7],
            .solved [4, 6, 7, 9, 2, 5]
          ],
          .solved [4, 6, 7, 8, 2, 5]
        ],
        .split [
          .solved [0, 7, 8, 5, 1, 6],
          .split [
            .solved [4, 8, 9, 6, 1, 5],
            .solved [5, 7, 9, 6, 0, 8],
            .solved [5, 6, 8, 9, 7, 4]
          ],
          .split [
            .solved [0, 5, 7, 8, 9, 6],
            .solved [5, 7, 8, 6, 0, 9]
          ],
          .split [
            .solved [5, 6, 8, 9, 7, 4]
          ]
        ],
        .split [
          .solved [4, 7, 8, 6, 1, 5],
          .split [
            .solved [5, 8, 9, 6, 0, 7],
            .solved [5, 6, 7, 9, 8, 4]
          ],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .split [
            .solved [0, 5, 7, 8, 9, 6],
            .solved [5, 7, 8, 6, 0, 9]
          ],
          .split [
            .solved [5, 6, 8, 9, 7, 4]
          ]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 6, 7, 1, 5, 8],
          .solved [0, 6, 7, 1, 5, 8],
          .solved [0, 6, 7, 5, 1, 8],
          .solved [0, 6, 7, 5, 1, 8]
        ],
        .split [
          .solved [1, 7, 8, 6, 4, 5],
          .split [
            .solved [0, 5, 6, 8, 9, 7],
            .solved [5, 6, 8, 7, 0, 9]
          ],
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ],
        .split [
          .split [
            .solved [0, 5, 6, 7, 8, 9],
            .solved [0, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [5, 6, 7, 8, 0, 9]
          ]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ]
      ],
      .split [
        .split [
          .solved [1, 6, 7, 8, 4, 5],
          .split [
            .solved [5, 8, 9, 6, 0, 7],
            .solved [4, 6, 7, 9, 1, 5]
          ],
          .solved [4, 6, 7, 8, 1, 5]
        ],
        .split [
          .split [
            .solved [0, 5, 7, 8, 9, 6],
            .solved [5, 7, 8, 6, 0, 9]
          ],
          .split [
            .solved [5, 6, 8, 9, 7, 4]
          ]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [0, 5, 6, 7, 8, 9],
            .solved [0, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [5, 6, 7, 8, 0, 9]
          ]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [3, 4, 5, 6, 7, 8],
          .solved [0, 1, 2, 3, 8, 4],
          .solved [3, 1, 2, 4, 0, 8],
          .solved [3, 5, 6, 7, 4, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 5, 6, 7, 4, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 5, 6, 7, 4, 8],
          .solved [3, 4, 5, 6, 7, 8]
        ],
        .solved [0, 1, 2, 3, 7, 4],
        .solved [3, 1, 2, 4, 0, 7],
        .split [
          .split [
            .solved [0, 7, 8, 9, 2, 5],
            .solved [2, 7, 8, 9, 0, 5],
            .solved [0, 7, 8, 9, 2, 5],
            .solved [4, 5, 6, 9, 3, 7],
            .solved [0, 7, 8, 9, 2, 5],
            .solved [4, 5, 6, 9, 3, 7]
          ],
          .solved [4, 5, 6, 8, 3, 7],
          .split [
            .solved [0, 8, 9, 7, 1, 5],
            .solved [4, 5, 6, 9, 3, 7],
            .solved [5, 7, 8, 9, 6, 0],
            .solved [4, 5, 6, 9, 3, 7]
          ],
          .solved [4, 5, 6, 8, 3, 7],
          .split [
            .solved [5, 7, 8, 9, 6, 0],
            .solved [4, 5, 6, 9, 3, 7]
          ],
          .solved [4, 5, 6, 8, 3, 7]
        ],
        .split [
          .solved [4, 7, 8, 5, 2, 6],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .split [
            .solved [0, 7, 8, 9, 1, 5],
            .solved [1, 7, 8, 9, 0, 5],
            .solved [0, 7, 8, 9, 1, 5],
            .solved [4, 5, 6, 9, 3, 7]
          ],
          .solved [4, 5, 6, 8, 3, 7],
          .split [
            .solved [5, 7, 8, 9, 6, 0],
            .solved [4, 5, 6, 9, 3, 7]
          ],
          .solved [4, 5, 6, 8, 3, 7]
        ],
        .split [
          .solved [4, 7, 8, 5, 1, 6],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 0],
            .solved [4, 5, 6, 9, 3, 7]
          ],
          .solved [4, 5, 6, 8, 3, 7]
        ],
        .split [
          .solved [4, 5, 6, 7, 3, 8]
        ]
      ],
      .solved [0, 1, 2, 3, 6, 4],
      .solved [3, 1, 2, 4, 0, 6],
      .split [
        .split [
          .solved [0, 6, 7, 8, 2, 5],
          .solved [2, 6, 7, 8, 0, 5],
          .solved [0, 6, 7, 8, 2, 5],
          .split [
            .solved [4, 8, 9, 5, 1, 6],
            .solved [0, 6, 7, 9, 2, 5],
            .solved [5, 8, 9, 6, 4, 7]
          ],
          .solved [0, 6, 7, 8, 2, 5],
          .split [
            .solved [5, 8, 9, 6, 4, 7]
          ]
        ],
        .split [
          .solved [2, 7, 8, 4, 6, 5],
          .split [
            .solved [0, 8, 9, 6, 1, 5],
            .solved [5, 7, 9, 6, 4, 8],
            .solved [5, 6, 8, 9, 7, 0],
            .solved [5, 7, 9, 6, 4, 8]
          ],
          .split [
            .solved [4, 8, 9, 5, 1, 6],
            .solved [5, 7, 8, 6, 4, 9],
            .solved [4, 5, 7, 8, 9, 6]
          ],
          .split [
            .solved [5, 6, 8, 9, 7, 0],
            .solved [5, 7, 9, 6, 4, 8]
          ],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .solved [0, 7, 8, 6, 1, 5],
          .split [
            .solved [4, 8, 9, 5, 1, 6],
            .solved [5, 6, 7, 9, 8, 0],
            .solved [5, 8, 9, 6, 4, 7]
          ],
          .split [
            .solved [0, 6, 7, 8, 9, 5],
            .solved [5, 6, 7, 8, 9, 0]
          ],
          .split [
            .solved [5, 8, 9, 6, 4, 7]
          ]
        ],
        .split [
          .solved [4, 7, 8, 5, 1, 6],
          .split [
            .solved [5, 6, 8, 9, 7, 0],
            .solved [5, 7, 9, 6, 4, 8]
          ],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .split [
            .solved [0, 6, 7, 8, 9, 5],
            .solved [5, 6, 7, 8, 9, 0]
          ],
          .split [
            .solved [5, 8, 9, 6, 4, 7]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ]
      ],
      .split [
        .split [
          .solved [2, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 2, 8],
          .solved [4, 6, 7, 5, 2, 8],
          .solved [4, 6, 7, 5, 2, 8],
          .solved [4, 6, 7, 5, 2, 8]
        ],
        .split [
          .split [
            .solved [0, 7, 8, 9, 1, 5],
            .solved [1, 7, 8, 9, 0, 5],
            .solved [0, 7, 8, 9, 1, 5],
            .solved [5, 6, 9, 7, 4, 8]
          ],
          .split [
            .solved [4, 8, 9, 5, 1, 6],
            .solved [5, 6, 8, 7, 4, 9],
            .solved [4, 5, 6, 8, 9, 7]
          ],
          .split [
            .solved [5, 7, 8, 9, 6, 0],
            .solved [5, 6, 9, 7, 4, 8]
          ],
          .split [
            .solved [4, 5, 6, 8, 9, 7]
          ]
        ],
        .split [
          .solved [4, 7, 8, 5, 1, 6],
          .split [
            .solved [5, 6, 7, 8, 4, 9],
            .solved [4, 5, 6, 7, 9, 8]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 0],
            .solved [5, 6, 9, 7, 4, 8]
          ],
          .split [
            .solved [4, 5, 6, 8, 9, 7]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 6, 7, 8, 1, 5],
          .solved [1, 6, 7, 8, 0, 5],
          .solved [0, 6, 7, 8, 1, 5],
          .split [
            .solved [5, 8, 9, 6, 4, 7]
          ]
        ],
        .split [
          .solved [1, 7, 8, 4, 6, 5],
          .split [
            .solved [5, 6, 8, 9, 7, 0],
            .solved [5, 7, 9, 6, 4, 8]
          ],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .split [
            .solved [0, 6, 7, 8, 9, 5],
            .solved [5, 6, 7, 8, 9, 0]
          ],
          .split [
            .solved [5, 8, 9, 6, 4, 7]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ]
      ],
      .split [
        .split [
          .solved [1, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 1, 8],
          .solved [4, 6, 7, 5, 1, 8]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 0],
            .solved [5, 6, 9, 7, 4, 8]
          ],
          .split [
            .solved [4, 5, 6, 8, 9, 7]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [0, 6, 7, 8, 9, 5],
            .solved [5, 6, 7, 8, 9, 0]
          ],
          .split [
            .solved [5, 8, 9, 6, 4, 7]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .solved [0, 1, 2, 3, 5, 4],
    .solved [3, 1, 2, 4, 0, 5],
    .split [
      .split [
        .split [
          .solved [0, 2, 5, 6, 7, 8],
          .solved [0, 2, 5, 6, 7, 8],
          .solved [0, 5, 6, 2, 8, 7],
          .solved [0, 5, 6, 7, 2, 8],
          .solved [0, 5, 6, 2, 8, 7],
          .solved [0, 5, 6, 7, 2, 8]
        ],
        .split [
          .solved [2, 5, 6, 7, 0, 8],
          .solved [0, 5, 6, 2, 8, 7],
          .solved [2, 5, 6, 7, 0, 8],
          .solved [0, 5, 6, 2, 8, 7],
          .solved [2, 5, 6, 7, 0, 8]
        ],
        .split [
          .solved [0, 7, 8, 5, 1, 6],
          .solved [0, 5, 6, 7, 2, 8],
          .solved [0, 5, 6, 7, 2, 8],
          .solved [0, 5, 6, 7, 2, 8]
        ],
        .split [
          .split [
            .solved [1, 7, 8, 9, 4, 5],
            .solved [0, 5, 6, 9, 2, 7],
            .solved [4, 7, 8, 9, 1, 5]
          ],
          .solved [0, 5, 6, 8, 2, 7],
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ],
        .split [
          .solved [0, 5, 6, 7, 2, 8],
          .solved [0, 5, 6, 7, 2, 8]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ]
      ],
      .split [
        .split [
          .solved [2, 6, 7, 4, 5, 8],
          .solved [2, 6, 7, 5, 4, 8],
          .solved [2, 6, 7, 4, 5, 8],
          .solved [2, 6, 7, 5, 4, 8],
          .solved [2, 6, 7, 4, 5, 8]
        ],
        .split [
          .solved [0, 7, 8, 5, 1, 6],
          .split [
            .solved [4, 8, 9, 6, 1, 5],
            .solved [5, 7, 9, 6, 0, 8],
            .solved [5, 6, 8, 9, 7, 4]
          ],
          .split [
            .solved [0, 5, 7, 8, 9, 6],
            .solved [5, 7, 8, 6, 0, 9]
          ],
          .split [
            .solved [5, 6, 8, 9, 7, 4]
          ]
        ],
        .split [
          .solved [4, 7, 8, 6, 1, 5],
          .split [
            .solved [5, 8, 9, 6, 0, 7],
            .solved [5, 6, 7, 9, 8, 4]
          ],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .split [
            .solved [0, 5, 7, 8, 9, 6],
            .solved [5, 7, 8, 6, 0, 9]
          ],
          .split [
            .solved [5, 6, 8, 9, 7, 4]
          ]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 6, 7, 1, 5, 8],
          .solved [0, 6, 7, 1, 5, 8],
          .solved [0, 6, 7, 5, 1, 8],
          .solved [0, 6, 7, 5, 1, 8]
        ],
        .split [
          .solved [1, 7, 8, 6, 4, 5],
          .split [
            .solved [0, 5, 6, 8, 9, 7],
            .solved [5, 6, 8, 7, 0, 9]
          ],
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ],
        .split [
          .split [
            .solved [0, 5, 6, 7, 8, 9],
            .solved [0, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [5, 6, 7, 8, 0, 9]
          ]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ]
      ],
      .split [
        .split [
          .solved [1, 6, 7, 8, 4, 5],
          .split [
            .solved [5, 8, 9, 6, 0, 7],
            .solved [4, 6, 7, 9, 1, 5]
          ],
          .solved [4, 6, 7, 8, 1, 5]
        ],
        .split [
          .split [
            .solved [0, 5, 7, 8, 9, 6],
            .solved [5, 7, 8, 6, 0, 9]
          ],
          .split [
            .solved [5, 6, 8, 9, 7, 4]
          ]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [0, 5, 6, 7, 8, 9],
            .solved [0, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [5, 6, 7, 8, 0, 9]
          ]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 5, 6, 7, 4, 8],
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 5, 6, 7, 4, 8],
          .solved [2, 4, 5, 6, 7, 8]
        ],
        .split [
          .split [
            .solved [0, 7, 8, 9, 1, 5],
            .solved [1, 7, 8, 9, 0, 5],
            .solved [0, 7, 8, 9, 1, 5],
            .solved [4, 5, 6, 9, 2, 7]
          ],
          .solved [4, 5, 6, 8, 2, 7],
          .split [
            .solved [5, 7, 8, 9, 6, 0],
            .solved [4, 5, 6, 9, 2, 7]
          ],
          .solved [4, 5, 6, 8, 2, 7]
        ],
        .split [
          .solved [4, 7, 8, 5, 1, 6],
          .solved [4, 5, 6, 7, 2, 8],
          .solved [4, 5, 6, 7, 2, 8]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 0],
            .solved [4, 5, 6, 9, 2, 7]
          ],
          .solved [4, 5, 6, 8, 2, 7]
        ],
        .split [
          .solved [4, 5, 6, 7, 2, 8]
        ]
      ],
      .split [
        .split [
          .solved [0, 6, 7, 8, 1, 5],
          .solved [1, 6, 7, 8, 0, 5],
          .solved [0, 6, 7, 8, 1, 5],
          .split [
            .solved [5, 8, 9, 6, 4, 7]
          ]
        ],
        .split [
          .solved [1, 7, 8, 4, 6, 5],
          .split [
            .solved [5, 6, 8, 9, 7, 0],
            .solved [5, 7, 9, 6, 4, 8]
          ],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .split [
            .solved [0, 6, 7, 8, 9, 5],
            .solved [5, 6, 7, 8, 9, 0]
          ],
          .split [
            .solved [5, 8, 9, 6, 4, 7]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ]
      ],
      .split [
        .split [
          .solved [1, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 1, 8],
          .solved [4, 6, 7, 5, 1, 8]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 0],
            .solved [5, 6, 9, 7, 4, 8]
          ],
          .split [
            .solved [4, 5, 6, 8, 9, 7]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [0, 6, 7, 8, 9, 5],
            .solved [5, 6, 7, 8, 9, 0]
          ],
          .split [
            .solved [5, 8, 9, 6, 4, 7]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [0, 1, 5, 6, 7, 8],
          .solved [0, 1, 5, 6, 7, 8],
          .solved [0, 5, 6, 1, 8, 7],
          .solved [0, 5, 6, 7, 1, 8]
        ],
        .split [
          .solved [1, 5, 6, 7, 0, 8],
          .solved [0, 5, 6, 1, 8, 7],
          .solved [1, 5, 6, 7, 0, 8]
        ],
        .split [
          .solved [0, 5, 6, 7, 1, 8],
          .solved [0, 5, 6, 7, 1, 8]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ]
      ],
      .split [
        .split [
          .solved [1, 6, 7, 4, 5, 8],
          .solved [1, 6, 7, 5, 4, 8],
          .solved [1, 6, 7, 4, 5, 8]
        ],
        .split [
          .split [
            .solved [0, 5, 7, 8, 9, 6],
            .solved [5, 7, 8, 6, 0, 9]
          ],
          .split [
            .solved [5, 6, 8, 9, 7, 4]
          ]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [0, 5, 6, 7, 8, 9],
            .solved [0, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [5, 6, 7, 8, 0, 9]
          ]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [1, 4, 5, 6, 7, 8],
          .solved [1, 5, 6, 7, 4, 8],
          .solved [1, 4, 5, 6, 7, 8]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 0],
            .solved [4, 5, 6, 9, 1, 7]
          ],
          .solved [4, 5, 6, 8, 1, 7]
        ],
        .split [
          .solved [4, 5, 6, 7, 1, 8]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [0, 6, 7, 8, 9, 5],
            .solved [5, 6, 7, 8, 9, 0]
          ],
          .split [
            .solved [5, 8, 9, 6, 4, 7]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .split [
            .solved [0, 5, 6, 7, 8, 9],
            .solved [0, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [5, 6, 7, 8, 0, 9]
          ]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ]
  ]

private def tree6a2 : WitnessTree :=
  .split [
    .solved [0, 2, 3, 4, 1, 5],
    .solved [0, 2, 3, 4, 1, 5],
    .solved [1, 0, 3, 2, 5, 4],
    .split [
      .split [
        .split [
          .solved [1, 3, 5, 6, 7, 8],
          .solved [2, 0, 3, 4, 1, 8],
          .solved [1, 3, 5, 6, 7, 8],
          .solved [1, 0, 2, 3, 8, 4],
          .solved [1, 5, 6, 3, 8, 7],
          .solved [3, 0, 2, 4, 1, 8],
          .solved [1, 5, 6, 7, 3, 8],
          .solved [1, 5, 6, 3, 8, 7],
          .solved [1, 5, 6, 3, 8, 7],
          .solved [1, 5, 6, 7, 3, 8],
          .solved [1, 5, 6, 7, 3, 8]
        ],
        .solved [2, 0, 3, 4, 1, 7],
        .split [
          .solved [3, 5, 6, 7, 1, 8],
          .solved [1, 0, 2, 3, 8, 4],
          .solved [1, 5, 6, 3, 8, 7],
          .solved [3, 0, 2, 4, 1, 8],
          .solved [3, 5, 6, 7, 1, 8],
          .solved [1, 5, 6, 3, 8, 7],
          .solved [1, 5, 6, 3, 8, 7],
          .solved [3, 5, 6, 7, 1, 8],
          .solved [3, 5, 6, 7, 1, 8]
        ],
        .solved [1, 0, 2, 3, 7, 4],
        .split [
          .solved [1, 7, 8, 5, 2, 6],
          .solved [3, 0, 2, 4, 1, 8],
          .solved [1, 5, 6, 7, 3, 8],
          .solved [1, 5, 6, 7, 3, 8],
          .solved [1, 5, 6, 7, 3, 8],
          .solved [1, 5, 6, 7, 3, 8],
          .solved [1, 5, 6, 7, 3, 8]
        ],
        .solved [3, 0, 2, 4, 1, 7],
        .split [
          .split [
            .solved [2, 7, 8, 9, 4, 5],
            .solved [1, 5, 6, 9, 3, 7],
            .solved [1, 5, 6, 9, 3, 7],
            .solved [4, 7, 8, 9, 2, 5],
            .solved [4, 7, 8, 9, 2, 5]
          ],
          .solved [1, 5, 6, 8, 3, 7],
          .solved [1, 5, 6, 8, 3, 7],
          .split [
            .solved [4, 8, 9, 7, 0, 5],
            .solved [5, 7, 8, 9, 6, 4]
          ],
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ],
        .split [
          .solved [1, 7, 8, 5, 0, 6],
          .solved [1, 5, 6, 7, 3, 8],
          .solved [1, 5, 6, 7, 3, 8],
          .solved [1, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [1, 5, 6, 7, 3, 8],
          .solved [1, 5, 6, 7, 3, 8],
          .solved [1, 5, 6, 7, 3, 8]
        ],
        .split [
          .split [
            .solved [0, 7, 8, 9, 4, 5],
            .solved [4, 7, 8, 9, 0, 5]
          ],
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ]
      ],
      .solved [2, 0, 3, 4, 1, 6],
      .split [
        .split [
          .solved [3, 6, 7, 4, 5, 8],
          .solved [1, 0, 2, 3, 8, 4],
          .solved [3, 6, 7, 5, 4, 8],
          .solved [3, 0, 2, 4, 1, 8],
          .solved [3, 6, 7, 4, 5, 8],
          .solved [3, 6, 7, 5, 4, 8],
          .solved [3, 6, 7, 5, 4, 8],
          .solved [3, 6, 7, 4, 5, 8],
          .solved [3, 6, 7, 4, 5, 8]
        ],
        .solved [1, 0, 2, 3, 7, 4],
        .split [
          .solved [1, 7, 8, 5, 2, 6],
          .solved [3, 0, 2, 4, 1, 8],
          .split [
            .solved [4, 8, 9, 6, 2, 5],
            .solved [5, 7, 9, 6, 1, 8],
            .solved [5, 7, 9, 6, 1, 8],
            .solved [5, 6, 8, 9, 7, 4],
            .solved [5, 6, 8, 9, 7, 4]
          ],
          .split [
            .solved [1, 8, 9, 5, 0, 6],
            .solved [1, 5, 7, 8, 9, 6],
            .solved [5, 7, 8, 6, 1, 9],
            .solved [5, 7, 8, 6, 1, 9]
          ],
          .split [
            .solved [1, 5, 7, 8, 9, 6],
            .solved [5, 7, 8, 6, 1, 9],
            .solved [5, 7, 8, 6, 1, 9]
          ],
          .split [
            .solved [4, 8, 9, 6, 0, 5],
            .solved [5, 6, 8, 9, 7, 4]
          ],
          .split [
            .solved [5, 6, 8, 9, 7, 4]
          ]
        ],
        .solved [3, 0, 2, 4, 1, 7],
        .split [
          .solved [4, 7, 8, 6, 2, 5],
          .split [
            .solved [1, 8, 9, 5, 0, 6],
            .solved [5, 8, 9, 6, 1, 7],
            .solved [5, 6, 7, 9, 8, 4],
            .solved [5, 6, 7, 9, 8, 4]
          ],
          .split [
            .solved [5, 8, 9, 6, 1, 7],
            .solved [5, 6, 7, 9, 8, 4],
            .solved [5, 6, 7, 9, 8, 4]
          ],
          .split [
            .solved [4, 8, 9, 6, 0, 5],
            .solved [4, 6, 7, 8, 9, 5]
          ],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .solved [1, 7, 8, 5, 0, 6],
          .split [
            .solved [1, 5, 7, 8, 9, 6],
            .solved [5, 7, 8, 6, 1, 9],
            .solved [5, 7, 8, 6, 1, 9]
          ],
          .split [
            .solved [4, 8, 9, 6, 0, 5],
            .solved [5, 6, 8, 9, 7, 4]
          ],
          .split [
            .solved [5, 6, 8, 9, 7, 4]
          ]
        ],
        .split [
          .split [
            .solved [1, 5, 7, 8, 9, 6],
            .solved [5, 7, 8, 6, 1, 9],
            .solved [5, 7, 8, 6, 1, 9]
          ],
          .split [
            .solved [4, 8, 9, 6, 0, 5],
            .solved [5, 6, 8, 9, 7, 4]
          ],
          .split [
            .solved [5, 6, 8, 9, 7, 4]
          ]
        ],
        .split [
          .solved [4, 7, 8, 6, 0, 5],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .solved [1, 0, 2, 3, 6, 4],
      .split [
        .split [
          .solved [1, 6, 7, 2, 5, 8],
          .solved [3, 0, 2, 4, 1, 8],
          .solved [1, 6, 7, 2, 5, 8],
          .solved [1, 6, 7, 5, 2, 8],
          .solved [1, 6, 7, 5, 2, 8],
          .solved [1, 6, 7, 5, 2, 8],
          .solved [1, 6, 7, 5, 2, 8]
        ],
        .solved [3, 0, 2, 4, 1, 7],
        .split [
          .solved [2, 7, 8, 6, 4, 5],
          .split [
            .solved [1, 8, 9, 5, 0, 6],
            .solved [1, 5, 6, 8, 9, 7],
            .solved [5, 6, 8, 7, 1, 9],
            .solved [5, 6, 8, 7, 1, 9]
          ],
          .split [
            .solved [1, 5, 6, 8, 9, 7],
            .solved [5, 6, 8, 7, 1, 9],
            .solved [5, 6, 8, 7, 1, 9]
          ],
          .split [
            .solved [4, 8, 9, 7, 0, 5],
            .solved [5, 7, 8, 9, 6, 4]
          ],
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ],
        .split [
          .solved [1, 7, 8, 5, 0, 6],
          .split [
            .solved [1, 5, 6, 7, 8, 9],
            .solved [1, 5, 6, 7, 8, 9],
            .solved [1, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [0, 8, 9, 7, 4, 5],
            .solved [5, 6, 7, 8, 1, 9]
          ],
          .split [
            .solved [5, 6, 7, 8, 1, 9]
          ]
        ],
        .split [
          .split [
            .solved [1, 5, 6, 7, 8, 9],
            .solved [1, 5, 6, 7, 8, 9],
            .solved [1, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [5, 6, 7, 8, 1, 9],
            .solved [5, 6, 7, 8, 1, 9]
          ],
          .split [
            .solved [5, 6, 7, 8, 1, 9]
          ]
        ],
        .split [
          .split [
            .solved [0, 7, 8, 9, 4, 5],
            .solved [4, 7, 8, 9, 0, 5]
          ],
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ]
      ],
      .solved [3, 0, 2, 4, 1, 6],
      .split [
        .split [
          .solved [2, 6, 7, 8, 4, 5],
          .split [
            .solved [1, 8, 9, 5, 0, 6],
            .solved [5, 8, 9, 6, 1, 7],
            .solved [4, 6, 7, 9, 2, 5],
            .solved [4, 6, 7, 9, 2, 5]
          ],
          .split [
            .solved [5, 8, 9, 6, 1, 7],
            .solved [4, 6, 7, 9, 2, 5],
            .solved [4, 6, 7, 9, 2, 5]
          ],
          .solved [4, 6, 7, 8, 2, 5],
          .solved [4, 6, 7, 8, 2, 5]
        ],
        .split [
          .solved [1, 7, 8, 5, 0, 6],
          .split [
            .solved [1, 5, 7, 8, 9, 6],
            .solved [5, 7, 8, 6, 1, 9],
            .solved [5, 7, 8, 6, 1, 9]
          ],
          .split [
            .solved [4, 8, 9, 6, 0, 5],
            .solved [5, 6, 8, 9, 7, 4]
          ],
          .split [
            .solved [5, 6, 8, 9, 7, 4]
          ]
        ],
        .split [
          .split [
            .solved [1, 5, 7, 8, 9, 6],
            .solved [5, 7, 8, 6, 1, 9],
            .solved [5, 7, 8, 6, 1, 9]
          ],
          .split [
            .solved [4, 8, 9, 6, 0, 5],
            .solved [5, 6, 8, 9, 7, 4]
          ],
          .split [
            .solved [5, 6, 8, 9, 7, 4]
          ]
        ],
        .split [
          .solved [4, 7, 8, 6, 0, 5],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 1, 6, 7, 8, 5],
          .solved [1, 6, 7, 5, 0, 8],
          .solved [0, 6, 7, 1, 8, 5],
          .solved [1, 6, 7, 5, 0, 8]
        ],
        .split [
          .split [
            .solved [1, 5, 6, 7, 8, 9],
            .solved [1, 5, 6, 7, 8, 9],
            .solved [1, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [0, 8, 9, 6, 4, 5],
            .solved [5, 6, 7, 8, 1, 9]
          ],
          .split [
            .solved [5, 6, 7, 8, 1, 9]
          ]
        ],
        .split [
          .solved [0, 7, 8, 6, 4, 5],
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [1, 5, 6, 7, 8, 9],
            .solved [1, 5, 6, 7, 8, 9],
            .solved [1, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [5, 6, 7, 8, 1, 9],
            .solved [5, 6, 7, 8, 1, 9]
          ],
          .split [
            .solved [5, 6, 7, 8, 1, 9]
          ]
        ],
        .split [
          .split [
            .solved [0, 7, 8, 9, 4, 5],
            .solved [4, 7, 8, 9, 0, 5]
          ],
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 6, 7, 8, 4, 5],
          .solved [4, 6, 7, 8, 0, 5]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ]
    ],
    .solved [2, 0, 3, 4, 1, 5],
    .split [
      .split [
        .split [
          .solved [3, 4, 5, 6, 7, 8],
          .solved [1, 0, 2, 3, 8, 4],
          .solved [3, 5, 6, 7, 4, 8],
          .solved [3, 0, 2, 4, 1, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 5, 6, 7, 4, 8],
          .solved [3, 5, 6, 7, 4, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 4, 5, 6, 7, 8]
        ],
        .solved [1, 0, 2, 3, 7, 4],
        .split [
          .split [
            .solved [1, 7, 8, 9, 2, 5],
            .solved [3, 0, 2, 4, 1, 9],
            .solved [2, 7, 8, 9, 1, 5],
            .solved [1, 7, 8, 9, 2, 5],
            .solved [1, 7, 8, 9, 2, 5],
            .solved [4, 5, 6, 9, 3, 7],
            .solved [4, 5, 6, 9, 3, 7]
          ],
          .solved [3, 0, 2, 4, 1, 8],
          .solved [4, 5, 6, 8, 3, 7],
          .split [
            .solved [1, 8, 9, 7, 0, 5],
            .solved [5, 7, 8, 9, 6, 1],
            .solved [4, 5, 6, 9, 3, 7],
            .solved [4, 5, 6, 9, 3, 7]
          ],
          .split [
            .solved [5, 7, 8, 9, 6, 1],
            .solved [4, 5, 6, 9, 3, 7],
            .solved [4, 5, 6, 9, 3, 7]
          ],
          .solved [4, 5, 6, 8, 3, 7],
          .solved [4, 5, 6, 8, 3, 7]
        ],
        .solved [3, 0, 2, 4, 1, 7],
        .split [
          .solved [4, 7, 8, 5, 2, 6],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .split [
            .solved [0, 7, 8, 9, 1, 5],
            .solved [1, 7, 8, 9, 0, 5],
            .solved [0, 7, 8, 9, 1, 5],
            .solved [4, 5, 6, 9, 3, 7]
          ],
          .split [
            .solved [5, 7, 8, 9, 6, 1],
            .solved [4, 5, 6, 9, 3, 7],
            .solved [4, 5, 6, 9, 3, 7]
          ],
          .solved [4, 5, 6, 8, 3, 7],
          .solved [4, 5, 6, 8, 3, 7]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 1],
            .solved [4, 5, 6, 9, 3, 7],
            .solved [4, 5, 6, 9, 3, 7]
          ],
          .solved [4, 5, 6, 8, 3, 7],
          .solved [4, 5, 6, 8, 3, 7]
        ],
        .split [
          .solved [4, 7, 8, 5, 0, 6],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 3, 8]
        ]
      ],
      .solved [1, 0, 2, 3, 6, 4],
      .split [
        .split [
          .solved [1, 6, 7, 8, 2, 5],
          .solved [3, 0, 2, 4, 1, 8],
          .solved [2, 6, 7, 8, 1, 5],
          .solved [1, 6, 7, 8, 2, 5],
          .solved [1, 6, 7, 8, 2, 5],
          .split [
            .solved [4, 8, 9, 5, 0, 6],
            .solved [5, 8, 9, 6, 4, 7]
          ],
          .split [
            .solved [5, 8, 9, 6, 4, 7]
          ]
        ],
        .solved [3, 0, 2, 4, 1, 7],
        .split [
          .solved [2, 7, 8, 4, 6, 5],
          .split [
            .solved [1, 8, 9, 6, 0, 5],
            .solved [5, 6, 8, 9, 7, 1],
            .solved [5, 7, 9, 6, 4, 8],
            .solved [5, 7, 9, 6, 4, 8]
          ],
          .split [
            .solved [5, 6, 8, 9, 7, 1],
            .solved [5, 7, 9, 6, 4, 8],
            .solved [5, 7, 9, 6, 4, 8]
          ],
          .split [
            .solved [4, 8, 9, 5, 0, 6],
            .solved [4, 5, 7, 8, 9, 6]
          ],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .solved [1, 7, 8, 6, 0, 5],
          .split [
            .solved [1, 6, 7, 8, 9, 5],
            .solved [5, 6, 7, 8, 9, 1],
            .solved [5, 6, 7, 8, 9, 1]
          ],
          .split [
            .solved [4, 8, 9, 5, 0, 6],
            .solved [5, 8, 9, 6, 4, 7]
          ],
          .split [
            .solved [5, 8, 9, 6, 4, 7]
          ]
        ],
        .split [
          .split [
            .solved [1, 6, 7, 8, 9, 5],
            .solved [5, 6, 7, 8, 9, 1],
            .solved [5, 6, 7, 8, 9, 1]
          ],
          .split [
            .solved [4, 8, 9, 5, 0, 6],
            .solved [5, 8, 9, 6, 4, 7]
          ],
          .split [
            .solved [5, 8, 9, 6, 4, 7]
          ]
        ],
        .split [
          .solved [4, 7, 8, 5, 0, 6],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ]
      ],
      .solved [3, 0, 2, 4, 1, 6],
      .split [
        .split [
          .solved [2, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 2, 8],
          .solved [4, 6, 7, 5, 2, 8],
          .solved [4, 6, 7, 5, 2, 8],
          .solved [4, 6, 7, 5, 2, 8]
        ],
        .split [
          .split [
            .solved [0, 7, 8, 9, 1, 5],
            .solved [1, 7, 8, 9, 0, 5],
            .solved [0, 7, 8, 9, 1, 5],
            .solved [5, 6, 9, 7, 4, 8]
          ],
          .split [
            .solved [5, 7, 8, 9, 6, 1],
            .solved [5, 6, 9, 7, 4, 8],
            .solved [5, 6, 9, 7, 4, 8]
          ],
          .split [
            .solved [4, 8, 9, 5, 0, 6],
            .solved [4, 5, 6, 8, 9, 7]
          ],
          .split [
            .solved [4, 5, 6, 8, 9, 7]
          ]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 1],
            .solved [5, 6, 9, 7, 4, 8],
            .solved [5, 6, 9, 7, 4, 8]
          ],
          .split [
            .solved [4, 8, 9, 5, 0, 6],
            .solved [4, 5, 6, 8, 9, 7]
          ],
          .split [
            .solved [4, 5, 6, 8, 9, 7]
          ]
        ],
        .split [
          .solved [4, 7, 8, 5, 0, 6],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 6, 7, 8, 1, 5],
          .solved [1, 6, 7, 8, 0, 5],
          .solved [0, 6, 7, 8, 1, 5],
          .split [
            .solved [5, 8, 9, 6, 4, 7]
          ]
        ],
        .split [
          .split [
            .solved [1, 6, 7, 8, 9, 5],
            .solved [5, 6, 7, 8, 9, 1],
            .solved [5, 6, 7, 8, 9, 1]
          ],
          .split [
            .solved [0, 8, 9, 4, 6, 5],
            .solved [5, 8, 9, 6, 4, 7]
          ],
          .split [
            .solved [5, 8, 9, 6, 4, 7]
          ]
        ],
        .split [
          .solved [0, 7, 8, 4, 6, 5],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [1, 6, 7, 8, 9, 5],
            .solved [5, 6, 7, 8, 9, 1],
            .solved [5, 6, 7, 8, 9, 1]
          ],
          .split [
            .solved [4, 8, 9, 5, 0, 6],
            .solved [5, 8, 9, 6, 4, 7]
          ],
          .split [
            .solved [5, 8, 9, 6, 4, 7]
          ]
        ],
        .split [
          .solved [4, 7, 8, 5, 0, 6],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 0, 8]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .solved [1, 0, 2, 3, 5, 4],
    .split [
      .split [
        .split [
          .solved [1, 2, 5, 6, 7, 8],
          .solved [3, 0, 2, 4, 1, 8],
          .solved [1, 2, 5, 6, 7, 8],
          .solved [1, 5, 6, 2, 8, 7],
          .solved [1, 5, 6, 2, 8, 7],
          .solved [1, 5, 6, 7, 2, 8],
          .solved [1, 5, 6, 7, 2, 8]
        ],
        .solved [3, 0, 2, 4, 1, 7],
        .split [
          .solved [2, 5, 6, 7, 1, 8],
          .solved [1, 5, 6, 2, 8, 7],
          .solved [1, 5, 6, 2, 8, 7],
          .solved [2, 5, 6, 7, 1, 8],
          .solved [2, 5, 6, 7, 1, 8]
        ],
        .split [
          .solved [1, 7, 8, 5, 0, 6],
          .solved [1, 5, 6, 7, 2, 8],
          .solved [1, 5, 6, 7, 2, 8],
          .solved [1, 5, 6, 7, 2, 8]
        ],
        .split [
          .solved [1, 5, 6, 7, 2, 8],
          .solved [1, 5, 6, 7, 2, 8],
          .solved [1, 5, 6, 7, 2, 8]
        ],
        .split [
          .split [
            .solved [0, 7, 8, 9, 4, 5],
            .solved [4, 7, 8, 9, 0, 5]
          ],
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ]
      ],
      .solved [3, 0, 2, 4, 1, 6],
      .split [
        .split [
          .solved [2, 6, 7, 4, 5, 8],
          .solved [2, 6, 7, 5, 4, 8],
          .solved [2, 6, 7, 5, 4, 8],
          .solved [2, 6, 7, 4, 5, 8],
          .solved [2, 6, 7, 4, 5, 8]
        ],
        .split [
          .solved [1, 7, 8, 5, 0, 6],
          .split [
            .solved [1, 5, 7, 8, 9, 6],
            .solved [5, 7, 8, 6, 1, 9],
            .solved [5, 7, 8, 6, 1, 9]
          ],
          .split [
            .solved [4, 8, 9, 6, 0, 5],
            .solved [5, 6, 8, 9, 7, 4]
          ],
          .split [
            .solved [5, 6, 8, 9, 7, 4]
          ]
        ],
        .split [
          .split [
            .solved [1, 5, 7, 8, 9, 6],
            .solved [5, 7, 8, 6, 1, 9],
            .solved [5, 7, 8, 6, 1, 9]
          ],
          .split [
            .solved [4, 8, 9, 6, 0, 5],
            .solved [5, 6, 8, 9, 7, 4]
          ],
          .split [
            .solved [5, 6, 8, 9, 7, 4]
          ]
        ],
        .split [
          .solved [4, 7, 8, 6, 0, 5],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 1, 6, 7, 8, 5],
          .solved [1, 6, 7, 5, 0, 8],
          .solved [0, 6, 7, 1, 8, 5],
          .solved [1, 6, 7, 5, 0, 8]
        ],
        .split [
          .split [
            .solved [1, 5, 6, 7, 8, 9],
            .solved [1, 5, 6, 7, 8, 9],
            .solved [1, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [0, 8, 9, 6, 4, 5],
            .solved [5, 6, 7, 8, 1, 9]
          ],
          .split [
            .solved [5, 6, 7, 8, 1, 9]
          ]
        ],
        .split [
          .solved [0, 7, 8, 6, 4, 5],
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [1, 5, 6, 7, 8, 9],
            .solved [1, 5, 6, 7, 8, 9],
            .solved [1, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [5, 6, 7, 8, 1, 9],
            .solved [5, 6, 7, 8, 1, 9]
          ],
          .split [
            .solved [5, 6, 7, 8, 1, 9]
          ]
        ],
        .split [
          .split [
            .solved [0, 7, 8, 9, 4, 5],
            .solved [4, 7, 8, 9, 0, 5]
          ],
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 6, 7, 8, 4, 5],
          .solved [4, 6, 7, 8, 0, 5]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ]
    ],
    .solved [3, 0, 2, 4, 1, 5],
    .split [
      .split [
        .split [
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 5, 6, 7, 4, 8],
          .solved [2, 5, 6, 7, 4, 8],
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 4, 5, 6, 7, 8]
        ],
        .split [
          .split [
            .solved [0, 7, 8, 9, 1, 5],
            .solved [1, 7, 8, 9, 0, 5],
            .solved [0, 7, 8, 9, 1, 5],
            .solved [4, 5, 6, 9, 2, 7]
          ],
          .split [
            .solved [5, 7, 8, 9, 6, 1],
            .solved [4, 5, 6, 9, 2, 7],
            .solved [4, 5, 6, 9, 2, 7]
          ],
          .solved [4, 5, 6, 8, 2, 7],
          .solved [4, 5, 6, 8, 2, 7]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 1],
            .solved [4, 5, 6, 9, 2, 7],
            .solved [4, 5, 6, 9, 2, 7]
          ],
          .solved [4, 5, 6, 8, 2, 7],
          .solved [4, 5, 6, 8, 2, 7]
        ],
        .split [
          .solved [4, 7, 8, 5, 0, 6],
          .solved [4, 5, 6, 7, 2, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 2, 8]
        ]
      ],
      .split [
        .split [
          .solved [0, 6, 7, 8, 1, 5],
          .solved [1, 6, 7, 8, 0, 5],
          .solved [0, 6, 7, 8, 1, 5],
          .split [
            .solved [5, 8, 9, 6, 4, 7]
          ]
        ],
        .split [
          .split [
            .solved [1, 6, 7, 8, 9, 5],
            .solved [5, 6, 7, 8, 9, 1],
            .solved [5, 6, 7, 8, 9, 1]
          ],
          .split [
            .solved [0, 8, 9, 4, 6, 5],
            .solved [5, 8, 9, 6, 4, 7]
          ],
          .split [
            .solved [5, 8, 9, 6, 4, 7]
          ]
        ],
        .split [
          .solved [0, 7, 8, 4, 6, 5],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [1, 6, 7, 8, 9, 5],
            .solved [5, 6, 7, 8, 9, 1],
            .solved [5, 6, 7, 8, 9, 1]
          ],
          .split [
            .solved [4, 8, 9, 5, 0, 6],
            .solved [5, 8, 9, 6, 4, 7]
          ],
          .split [
            .solved [5, 8, 9, 6, 4, 7]
          ]
        ],
        .split [
          .solved [4, 7, 8, 5, 0, 6],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 0, 8]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [0, 1, 5, 6, 7, 8],
          .solved [0, 1, 5, 6, 7, 8],
          .solved [0, 5, 6, 1, 8, 7],
          .solved [0, 5, 6, 7, 1, 8]
        ],
        .split [
          .solved [1, 5, 6, 7, 0, 8],
          .solved [0, 5, 6, 1, 8, 7],
          .solved [1, 5, 6, 7, 0, 8]
        ],
        .split [
          .solved [0, 5, 6, 7, 1, 8],
          .solved [0, 5, 6, 7, 1, 8]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [1, 5, 6, 7, 8, 9],
            .solved [1, 5, 6, 7, 8, 9],
            .solved [1, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [0, 8, 9, 5, 4, 6],
            .solved [5, 6, 7, 8, 1, 9]
          ],
          .split [
            .solved [5, 6, 7, 8, 1, 9]
          ]
        ],
        .split [
          .solved [0, 7, 8, 5, 4, 6],
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 6, 7, 4, 5, 8],
          .solved [0, 6, 7, 4, 5, 8]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .split [
            .solved [1, 5, 6, 7, 8, 9],
            .solved [1, 5, 6, 7, 8, 9],
            .solved [1, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [5, 6, 7, 8, 1, 9],
            .solved [5, 6, 7, 8, 1, 9]
          ],
          .split [
            .solved [5, 6, 7, 8, 1, 9]
          ]
        ],
        .split [
          .split [
            .solved [0, 7, 8, 9, 4, 5],
            .solved [4, 7, 8, 9, 0, 5]
          ],
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 6, 7, 8, 4, 5],
          .solved [4, 6, 7, 8, 0, 5]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [0, 4, 5, 6, 7, 8],
          .solved [0, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 0, 8]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ]
  ]

private def tree6a3 : WitnessTree :=
  .split [
    .split [
      .split [
        .solved [2, 3, 4, 5, 6, 7],
        .split [
          .solved [0, 1, 3, 7, 2, 8],
          .solved [0, 1, 3, 7, 2, 8],
          .solved [1, 0, 3, 7, 2, 8],
          .solved [2, 3, 4, 5, 6, 8],
          .solved [2, 0, 1, 3, 8, 7],
          .solved [2, 4, 5, 3, 8, 6],
          .solved [2, 4, 5, 3, 8, 6],
          .solved [2, 4, 5, 3, 8, 6],
          .solved [3, 0, 1, 7, 2, 8],
          .solved [2, 4, 5, 6, 3, 8],
          .solved [2, 4, 5, 6, 3, 8],
          .solved [2, 4, 5, 6, 3, 8]
        ],
        .solved [2, 3, 4, 5, 6, 7],
        .solved [2, 3, 4, 5, 6, 7],
        .solved [2, 3, 4, 5, 6, 7],
        .split [
          .solved [0, 1, 2, 7, 3, 8],
          .solved [0, 1, 2, 7, 3, 8],
          .solved [1, 0, 2, 7, 3, 8],
          .solved [2, 4, 5, 3, 8, 6],
          .solved [2, 0, 1, 7, 3, 8],
          .solved [2, 4, 5, 6, 3, 8],
          .solved [2, 4, 5, 6, 3, 8],
          .solved [2, 4, 5, 6, 3, 8]
        ],
        .solved [2, 4, 5, 3, 7, 6],
        .solved [2, 4, 5, 3, 7, 6],
        .solved [2, 4, 5, 3, 7, 6],
        .split [
          .split [
            .split [
              .solved [0, 1, 7, 8, 9, 10],
              .solved [0, 1, 7, 8, 9, 10],
              .solved [0, 7, 8, 1, 10, 9],
              .solved [0, 7, 8, 9, 1, 10]
            ],
            .solved [2, 4, 5, 6, 3, 9],
            .solved [2, 4, 5, 6, 3, 9],
            .solved [2, 4, 5, 6, 3, 9]
          ],
          .solved [2, 4, 5, 6, 3, 8],
          .solved [2, 4, 5, 6, 3, 8],
          .solved [2, 4, 5, 6, 3, 8]
        ],
        .solved [2, 4, 5, 6, 3, 7],
        .solved [2, 4, 5, 6, 3, 7],
        .solved [2, 4, 5, 6, 3, 7]
      ],
      .split [
        .solved [0, 1, 3, 6, 2, 7],
        .solved [0, 1, 3, 6, 2, 7],
        .solved [1, 0, 3, 6, 2, 7],
        .split [
          .solved [3, 4, 5, 7, 2, 8],
          .solved [2, 0, 1, 3, 8, 6],
          .solved [2, 4, 5, 3, 8, 7],
          .solved [2, 4, 5, 3, 8, 7],
          .solved [2, 4, 5, 3, 8, 7],
          .solved [3, 0, 1, 6, 2, 8],
          .solved [3, 4, 5, 7, 2, 8],
          .solved [3, 4, 5, 7, 2, 8],
          .solved [3, 4, 5, 7, 2, 8]
        ],
        .solved [2, 0, 1, 3, 7, 6],
        .split [
          .solved [2, 7, 8, 4, 1, 5],
          .solved [2, 4, 5, 7, 3, 8],
          .solved [2, 4, 5, 7, 3, 8],
          .solved [3, 0, 1, 6, 2, 8],
          .solved [2, 4, 5, 7, 3, 8],
          .solved [2, 4, 5, 7, 3, 8],
          .solved [2, 4, 5, 7, 3, 8]
        ],
        .split [
          .solved [2, 7, 8, 4, 0, 5],
          .solved [2, 4, 5, 7, 3, 8],
          .solved [3, 0, 1, 6, 2, 8],
          .solved [2, 4, 5, 7, 3, 8],
          .solved [2, 4, 5, 7, 3, 8],
          .solved [2, 4, 5, 7, 3, 8]
        ],
        .split [
          .solved [2, 4, 5, 7, 3, 8],
          .solved [3, 0, 1, 6, 2, 8],
          .solved [2, 4, 5, 7, 3, 8],
          .solved [2, 4, 5, 7, 3, 8],
          .solved [2, 4, 5, 7, 3, 8]
        ],
        .solved [3, 0, 1, 6, 2, 7],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 1],
            .solved [6, 7, 8, 9, 1, 4],
            .solved [6, 7, 8, 9, 1, 4]
          ],
          .split [
            .solved [6, 8, 9, 7, 0, 4],
            .solved [4, 7, 8, 9, 5, 6]
          ],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [6, 7, 8, 9, 0, 4]
          ],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ]
      ],
      .split [
        .solved [3, 6, 7, 4, 1, 5],
        .solved [3, 4, 5, 6, 2, 7],
        .solved [3, 4, 5, 6, 2, 7],
        .split [
          .solved [0, 1, 2, 7, 3, 8],
          .solved [0, 1, 2, 7, 3, 8],
          .solved [1, 0, 2, 7, 3, 8],
          .solved [2, 4, 5, 3, 8, 6],
          .solved [2, 0, 1, 7, 3, 8],
          .solved [3, 4, 5, 6, 2, 8],
          .solved [3, 4, 5, 6, 2, 8],
          .solved [3, 4, 5, 6, 2, 8]
        ],
        .solved [2, 4, 5, 3, 7, 6],
        .solved [2, 4, 5, 3, 7, 6],
        .solved [2, 4, 5, 3, 7, 6],
        .split [
          .split [
            .solved [0, 1, 7, 8, 9, 6],
            .solved [1, 7, 8, 6, 0, 9],
            .solved [0, 7, 8, 1, 9, 6],
            .solved [1, 7, 8, 6, 0, 9]
          ],
          .solved [3, 4, 5, 6, 2, 8],
          .solved [3, 4, 5, 6, 2, 8],
          .solved [3, 4, 5, 6, 2, 8]
        ],
        .solved [3, 4, 5, 6, 2, 7],
        .solved [3, 4, 5, 6, 2, 7],
        .solved [3, 4, 5, 6, 2, 7]
      ],
      .split [
        .solved [3, 6, 7, 4, 0, 5],
        .solved [3, 4, 5, 6, 2, 7],
        .split [
          .solved [0, 1, 2, 7, 3, 8],
          .solved [0, 1, 2, 7, 3, 8],
          .solved [1, 0, 2, 7, 3, 8],
          .solved [2, 4, 5, 3, 8, 6],
          .solved [2, 0, 1, 7, 3, 8],
          .solved [3, 4, 5, 6, 2, 8],
          .solved [3, 4, 5, 6, 2, 8],
          .solved [3, 4, 5, 6, 2, 8]
        ],
        .solved [2, 4, 5, 3, 7, 6],
        .solved [2, 4, 5, 3, 7, 6],
        .solved [2, 4, 5, 3, 7, 6],
        .split [
          .split [
            .solved [0, 7, 8, 1, 6, 9],
            .solved [0, 7, 8, 1, 6, 9],
            .solved [0, 7, 8, 6, 1, 9],
            .solved [0, 7, 8, 6, 1, 9]
          ],
          .solved [3, 4, 5, 6, 2, 8],
          .solved [3, 4, 5, 6, 2, 8],
          .solved [3, 4, 5, 6, 2, 8]
        ],
        .solved [3, 4, 5, 6, 2, 7],
        .solved [3, 4, 5, 6, 2, 7],
        .solved [3, 4, 5, 6, 2, 7]
      ],
      .split [
        .solved [3, 4, 5, 6, 2, 7],
        .split [
          .solved [0, 1, 2, 7, 3, 8],
          .solved [0, 1, 2, 7, 3, 8],
          .solved [1, 0, 2, 7, 3, 8],
          .solved [2, 4, 5, 3, 8, 6],
          .solved [2, 0, 1, 7, 3, 8],
          .solved [3, 4, 5, 6, 2, 8],
          .solved [3, 4, 5, 6, 2, 8],
          .solved [3, 4, 5, 6, 2, 8]
        ],
        .solved [2, 4, 5, 3, 7, 6],
        .solved [2, 4, 5, 3, 7, 6],
        .solved [2, 4, 5, 3, 7, 6],
        .split [
          .split [
            .solved [0, 7, 8, 9, 1, 6],
            .solved [1, 7, 8, 9, 0, 6],
            .solved [0, 7, 8, 9, 1, 6],
            .solved [3, 4, 5, 6, 2, 9]
          ],
          .solved [3, 4, 5, 6, 2, 8],
          .solved [3, 4, 5, 6, 2, 8],
          .solved [3, 4, 5, 6, 2, 8]
        ],
        .solved [3, 4, 5, 6, 2, 7],
        .solved [3, 4, 5, 6, 2, 7],
        .solved [3, 4, 5, 6, 2, 7]
      ],
      .split [
        .solved [0, 1, 2, 6, 3, 7],
        .solved [0, 1, 2, 6, 3, 7],
        .solved [1, 0, 2, 6, 3, 7],
        .split [
          .solved [2, 4, 5, 7, 3, 8],
          .solved [2, 0, 1, 6, 3, 8],
          .solved [2, 4, 5, 7, 3, 8],
          .solved [2, 4, 5, 7, 3, 8],
          .solved [2, 4, 5, 7, 3, 8]
        ],
        .solved [2, 0, 1, 6, 3, 7],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 1],
            .solved [6, 7, 8, 9, 1, 4],
            .solved [6, 7, 8, 9, 1, 4]
          ],
          .split [
            .solved [6, 8, 9, 7, 0, 4],
            .solved [4, 7, 8, 9, 5, 6]
          ],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [6, 7, 8, 9, 0, 4]
          ],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ]
      ],
      .split [
        .solved [2, 6, 7, 4, 1, 5],
        .solved [2, 4, 5, 6, 3, 7],
        .solved [2, 4, 5, 6, 3, 7],
        .split [
          .split [
            .solved [0, 1, 7, 8, 9, 6],
            .solved [1, 7, 8, 6, 0, 9],
            .solved [0, 7, 8, 1, 9, 6],
            .solved [1, 7, 8, 6, 0, 9]
          ],
          .solved [2, 4, 5, 6, 3, 8],
          .solved [2, 4, 5, 6, 3, 8],
          .solved [2, 4, 5, 6, 3, 8]
        ],
        .solved [2, 4, 5, 6, 3, 7],
        .solved [2, 4, 5, 6, 3, 7],
        .solved [2, 4, 5, 6, 3, 7]
      ],
      .split [
        .solved [2, 6, 7, 4, 0, 5],
        .solved [2, 4, 5, 6, 3, 7],
        .split [
          .split [
            .solved [0, 7, 8, 1, 6, 9],
            .solved [0, 7, 8, 1, 6, 9],
            .solved [0, 7, 8, 6, 1, 9],
            .solved [0, 7, 8, 6, 1, 9]
          ],
          .solved [2, 4, 5, 6, 3, 8],
          .solved [2, 4, 5, 6, 3, 8],
          .solved [2, 4, 5, 6, 3, 8]
        ],
        .solved [2, 4, 5, 6, 3, 7],
        .solved [2, 4, 5, 6, 3, 7],
        .solved [2, 4, 5, 6, 3, 7]
      ],
      .split [
        .solved [2, 4, 5, 6, 3, 7],
        .split [
          .split [
            .solved [0, 7, 8, 9, 1, 6],
            .solved [1, 7, 8, 9, 0, 6],
            .solved [0, 7, 8, 9, 1, 6],
            .solved [2, 4, 5, 6, 3, 9]
          ],
          .solved [2, 4, 5, 6, 3, 8],
          .solved [2, 4, 5, 6, 3, 8],
          .solved [2, 4, 5, 6, 3, 8]
        ],
        .solved [2, 4, 5, 6, 3, 7],
        .solved [2, 4, 5, 6, 3, 7],
        .solved [2, 4, 5, 6, 3, 7]
      ],
      .split [
        .split [
          .split [
            .solved [0, 1, 6, 7, 8, 9],
            .solved [0, 1, 6, 7, 8, 9],
            .solved [0, 6, 7, 1, 9, 8],
            .solved [0, 6, 7, 8, 1, 9]
          ],
          .split [
            .solved [1, 6, 7, 8, 0, 9],
            .solved [0, 6, 7, 1, 9, 8],
            .solved [1, 6, 7, 8, 0, 9]
          ],
          .split [
            .solved [0, 6, 7, 8, 1, 9],
            .solved [0, 6, 7, 8, 1, 9]
          ],
          .split [
            .split [
              .solved [4, 8, 9, 10, 5, 6]
            ]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 1],
            .solved [6, 7, 8, 9, 1, 4],
            .solved [6, 7, 8, 9, 1, 4]
          ],
          .split [
            .solved [6, 8, 9, 7, 0, 4],
            .solved [4, 7, 8, 9, 5, 6]
          ],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [6, 7, 8, 9, 0, 4]
          ],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 1],
          .split [
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .solved [0, 1, 3, 5, 2, 6],
      .solved [0, 1, 3, 5, 2, 6],
      .solved [1, 0, 3, 5, 2, 6],
      .split [
        .split [
          .solved [3, 6, 7, 4, 5, 8],
          .solved [2, 0, 1, 3, 8, 5],
          .solved [3, 6, 7, 4, 5, 8],
          .solved [3, 6, 7, 4, 5, 8],
          .solved [3, 6, 7, 4, 5, 8],
          .solved [3, 0, 1, 5, 2, 8],
          .solved [3, 6, 7, 4, 5, 8],
          .solved [3, 6, 7, 4, 5, 8],
          .solved [3, 6, 7, 4, 5, 8]
        ],
        .solved [2, 0, 1, 3, 7, 5],
        .split [
          .solved [2, 7, 8, 4, 1, 6],
          .split [
            .solved [2, 8, 9, 4, 0, 6],
            .solved [2, 4, 7, 8, 9, 6],
            .solved [3, 0, 1, 5, 2, 9],
            .solved [4, 7, 8, 6, 2, 9],
            .solved [4, 7, 8, 6, 2, 9],
            .solved [4, 7, 8, 6, 2, 9]
          ],
          .split [
            .solved [2, 4, 7, 8, 9, 6],
            .solved [3, 0, 1, 5, 2, 9],
            .solved [4, 7, 8, 6, 2, 9],
            .solved [4, 7, 8, 6, 2, 9],
            .solved [4, 7, 8, 6, 2, 9]
          ],
          .solved [3, 0, 1, 5, 2, 8],
          .split [
            .solved [5, 8, 9, 6, 1, 4],
            .solved [4, 6, 8, 9, 7, 5],
            .solved [4, 6, 8, 9, 7, 5]
          ],
          .split [
            .solved [5, 8, 9, 6, 0, 4],
            .solved [4, 6, 8, 9, 7, 5]
          ],
          .split [
            .solved [4, 6, 8, 9, 7, 5]
          ]
        ],
        .split [
          .solved [2, 7, 8, 4, 0, 6],
          .split [
            .solved [2, 4, 7, 8, 9, 6],
            .solved [3, 0, 1, 5, 2, 9],
            .solved [4, 7, 8, 6, 2, 9],
            .solved [4, 7, 8, 6, 2, 9],
            .solved [4, 7, 8, 6, 2, 9]
          ],
          .solved [3, 0, 1, 5, 2, 8],
          .split [
            .solved [5, 8, 9, 6, 1, 4],
            .solved [4, 6, 8, 9, 7, 5],
            .solved [4, 6, 8, 9, 7, 5]
          ],
          .split [
            .solved [5, 8, 9, 6, 0, 4],
            .solved [4, 6, 8, 9, 7, 5]
          ],
          .split [
            .solved [4, 6, 8, 9, 7, 5]
          ]
        ],
        .split [
          .split [
            .solved [2, 4, 7, 8, 9, 6],
            .solved [3, 0, 1, 5, 2, 9],
            .solved [4, 7, 8, 6, 2, 9],
            .solved [4, 7, 8, 6, 2, 9],
            .solved [4, 7, 8, 6, 2, 9]
          ],
          .solved [3, 0, 1, 5, 2, 8],
          .split [
            .solved [5, 8, 9, 6, 1, 4],
            .solved [4, 6, 8, 9, 7, 5],
            .solved [4, 6, 8, 9, 7, 5]
          ],
          .split [
            .solved [5, 8, 9, 6, 0, 4],
            .solved [4, 6, 8, 9, 7, 5]
          ],
          .split [
            .solved [4, 6, 8, 9, 7, 5]
          ]
        ],
        .solved [3, 0, 1, 5, 2, 7],
        .split [
          .solved [5, 7, 8, 6, 1, 4],
          .split [
            .solved [5, 8, 9, 6, 0, 4],
            .solved [4, 6, 7, 8, 9, 5]
          ],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .solved [5, 7, 8, 6, 0, 4],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .solved [2, 0, 1, 3, 6, 5],
      .split [
        .split [
          .solved [1, 2, 6, 7, 8, 4],
          .solved [2, 6, 7, 4, 1, 8],
          .solved [2, 6, 7, 4, 1, 8],
          .solved [3, 0, 1, 5, 2, 8],
          .solved [1, 6, 7, 2, 8, 4],
          .solved [2, 6, 7, 4, 1, 8],
          .solved [2, 6, 7, 4, 1, 8]
        ],
        .split [
          .solved [2, 7, 8, 4, 0, 6],
          .split [
            .solved [2, 4, 6, 7, 8, 9],
            .solved [3, 0, 1, 5, 2, 9],
            .solved [2, 4, 6, 7, 8, 9],
            .solved [2, 4, 6, 7, 8, 9],
            .solved [2, 4, 6, 7, 8, 9]
          ],
          .solved [3, 0, 1, 5, 2, 8],
          .split [
            .solved [1, 8, 9, 6, 5, 4],
            .solved [4, 6, 7, 8, 2, 9],
            .solved [4, 6, 7, 8, 2, 9]
          ],
          .split [
            .solved [0, 8, 9, 7, 5, 4],
            .solved [4, 6, 7, 8, 2, 9]
          ],
          .split [
            .solved [4, 6, 7, 8, 2, 9]
          ]
        ],
        .split [
          .split [
            .solved [2, 4, 6, 7, 8, 9],
            .solved [3, 0, 1, 5, 2, 9],
            .solved [2, 4, 6, 7, 8, 9],
            .solved [2, 4, 6, 7, 8, 9],
            .solved [2, 4, 6, 7, 8, 9]
          ],
          .solved [3, 0, 1, 5, 2, 8],
          .split [
            .solved [1, 8, 9, 6, 5, 4],
            .solved [4, 6, 7, 8, 2, 9],
            .solved [4, 6, 7, 8, 2, 9]
          ],
          .split [
            .solved [4, 6, 7, 8, 2, 9],
            .solved [4, 6, 7, 8, 2, 9]
          ],
          .split [
            .solved [4, 6, 7, 8, 2, 9]
          ]
        ],
        .solved [3, 0, 1, 5, 2, 7],
        .split [
          .solved [1, 7, 8, 6, 5, 4],
          .split [
            .solved [5, 8, 9, 7, 0, 4],
            .solved [4, 7, 8, 9, 6, 5]
          ],
          .split [
            .solved [4, 7, 8, 9, 6, 5]
          ]
        ],
        .split [
          .split [
            .solved [0, 7, 8, 9, 5, 4],
            .solved [5, 7, 8, 9, 0, 4]
          ],
          .split [
            .solved [4, 7, 8, 9, 6, 5]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 6, 5]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 2, 6, 7, 8, 4],
          .solved [2, 6, 7, 4, 0, 8],
          .solved [3, 0, 1, 5, 2, 8],
          .solved [2, 6, 7, 4, 0, 8],
          .solved [0, 6, 7, 2, 8, 4],
          .solved [2, 6, 7, 4, 0, 8]
        ],
        .split [
          .split [
            .solved [2, 4, 6, 7, 8, 9],
            .solved [3, 0, 1, 5, 2, 9],
            .solved [2, 4, 6, 7, 8, 9],
            .solved [2, 4, 6, 7, 8, 9],
            .solved [2, 4, 6, 7, 8, 9]
          ],
          .solved [3, 0, 1, 5, 2, 8],
          .split [
            .solved [4, 6, 7, 8, 2, 9],
            .solved [4, 6, 7, 8, 2, 9],
            .solved [4, 6, 7, 8, 2, 9]
          ],
          .split [
            .solved [0, 8, 9, 6, 5, 4],
            .solved [4, 6, 7, 8, 2, 9]
          ],
          .split [
            .solved [4, 6, 7, 8, 2, 9]
          ]
        ],
        .solved [3, 0, 1, 5, 2, 7],
        .split [
          .split [
            .solved [1, 7, 8, 9, 5, 4],
            .solved [5, 7, 8, 9, 1, 4],
            .solved [5, 7, 8, 9, 1, 4]
          ],
          .split [
            .solved [0, 8, 9, 6, 5, 4],
            .solved [4, 7, 8, 9, 6, 5]
          ],
          .split [
            .solved [4, 7, 8, 9, 6, 5]
          ]
        ],
        .split [
          .solved [0, 7, 8, 6, 5, 4],
          .split [
            .solved [4, 7, 8, 9, 6, 5]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 6, 5]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [2, 4, 6, 7, 8, 9],
            .solved [3, 0, 1, 5, 2, 9],
            .solved [2, 4, 6, 7, 8, 9],
            .solved [2, 4, 6, 7, 8, 9],
            .solved [2, 4, 6, 7, 8, 9]
          ],
          .solved [3, 0, 1, 5, 2, 8],
          .split [
            .solved [4, 6, 7, 8, 2, 9],
            .solved [4, 6, 7, 8, 2, 9],
            .solved [4, 6, 7, 8, 2, 9]
          ],
          .split [
            .solved [4, 6, 7, 8, 2, 9],
            .solved [4, 6, 7, 8, 2, 9]
          ],
          .split [
            .solved [4, 6, 7, 8, 2, 9]
          ]
        ],
        .solved [3, 0, 1, 5, 2, 7],
        .split [
          .split [
            .solved [1, 7, 8, 9, 5, 4],
            .solved [5, 7, 8, 9, 1, 4],
            .solved [5, 7, 8, 9, 1, 4]
          ],
          .split [
            .solved [5, 8, 9, 7, 0, 4],
            .solved [4, 7, 8, 9, 6, 5]
          ],
          .split [
            .solved [4, 7, 8, 9, 6, 5]
          ]
        ],
        .split [
          .split [
            .solved [0, 7, 8, 9, 5, 4],
            .solved [5, 7, 8, 9, 0, 4]
          ],
          .split [
            .solved [4, 7, 8, 9, 6, 5]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 6, 5]
          ]
        ]
      ],
      .solved [3, 0, 1, 5, 2, 6],
      .split [
        .split [
          .solved [1, 6, 7, 8, 5, 4],
          .solved [5, 6, 7, 8, 1, 4],
          .solved [5, 6, 7, 8, 1, 4]
        ],
        .split [
          .solved [5, 7, 8, 6, 0, 4],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 6, 7, 8, 5, 4],
          .solved [5, 6, 7, 8, 0, 4]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .solved [1, 3, 5, 6, 7, 4],
        .solved [3, 5, 6, 4, 1, 7],
        .solved [3, 5, 6, 4, 1, 7],
        .split [
          .solved [0, 1, 2, 7, 3, 8],
          .solved [0, 1, 2, 7, 3, 8],
          .solved [1, 0, 2, 7, 3, 8],
          .solved [3, 5, 6, 4, 1, 8],
          .solved [2, 0, 1, 7, 3, 8],
          .solved [1, 5, 6, 3, 8, 4],
          .solved [3, 5, 6, 4, 1, 8],
          .solved [3, 5, 6, 4, 1, 8]
        ],
        .solved [1, 5, 6, 3, 7, 4],
        .split [
          .split [
            .solved [0, 2, 7, 8, 9, 4],
            .solved [2, 7, 8, 4, 0, 9],
            .solved [0, 7, 8, 2, 9, 4],
            .solved [2, 7, 8, 4, 0, 9],
            .solved [0, 7, 8, 2, 9, 4],
            .solved [2, 7, 8, 4, 0, 9]
          ],
          .solved [3, 5, 6, 4, 1, 8],
          .solved [1, 5, 6, 3, 8, 4],
          .solved [1, 5, 6, 3, 8, 4],
          .solved [3, 5, 6, 4, 1, 8],
          .solved [3, 5, 6, 4, 1, 8]
        ],
        .solved [3, 5, 6, 4, 1, 7],
        .solved [1, 5, 6, 3, 7, 4],
        .solved [1, 5, 6, 3, 7, 4],
        .solved [3, 5, 6, 4, 1, 7],
        .solved [3, 5, 6, 4, 1, 7]
      ],
      .split [
        .solved [3, 6, 7, 4, 0, 5],
        .split [
          .solved [3, 4, 5, 6, 7, 8],
          .split [
            .solved [0, 1, 2, 8, 3, 9],
            .solved [0, 1, 2, 8, 3, 9],
            .solved [1, 0, 2, 8, 3, 9],
            .solved [3, 4, 5, 6, 7, 9],
            .solved [2, 0, 1, 8, 3, 9],
            .solved [3, 4, 5, 6, 7, 9],
            .solved [3, 4, 5, 6, 7, 9],
            .solved [3, 4, 5, 6, 7, 9]
          ],
          .solved [3, 4, 5, 7, 6, 8],
          .solved [3, 4, 6, 7, 5, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 5, 6, 7, 4, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [0, 1, 2, 7, 3, 8],
          .solved [0, 1, 2, 7, 3, 8],
          .solved [1, 0, 2, 7, 3, 8],
          .split [
            .solved [4, 8, 9, 5, 2, 6],
            .solved [2, 0, 1, 7, 3, 9],
            .solved [4, 5, 6, 8, 3, 9],
            .solved [4, 5, 6, 8, 3, 9],
            .solved [4, 5, 6, 8, 3, 9]
          ],
          .solved [2, 0, 1, 7, 3, 8],
          .split [
            .solved [4, 5, 8, 9, 6, 1],
            .solved [4, 5, 6, 8, 3, 9],
            .solved [4, 5, 6, 8, 3, 9]
          ],
          .split [
            .solved [4, 6, 8, 9, 5, 0],
            .solved [4, 5, 6, 8, 3, 9]
          ],
          .split [
            .solved [4, 5, 6, 8, 3, 9]
          ]
        ],
        .split [
          .solved [1, 7, 8, 2, 5, 4],
          .split [
            .solved [0, 8, 9, 2, 6, 4],
            .solved [5, 4, 9, 7, 6, 2],
            .split [
              .solved [0, 9, 10, 1, 6, 5],
              .solved [9, 6, 8, 10, 0, 4],
              .solved [4, 6, 10, 8, 5, 0],
              .solved [9, 6, 8, 10, 0, 4]
            ],
            .solved [4, 5, 9, 7, 6, 1],
            .solved [4, 6, 9, 8, 5, 0],
            .solved [8, 4, 7, 9, 2, 5]
          ],
          .solved [5, 4, 8, 7, 6, 2],
          .split [
            .solved [0, 8, 9, 1, 6, 5],
            .solved [4, 5, 9, 7, 6, 1],
            .solved [5, 6, 9, 8, 4, 0],
            .solved [8, 5, 7, 9, 1, 4]
          ],
          .solved [4, 5, 8, 7, 6, 1],
          .solved [6, 4, 5, 8, 3, 7],
          .solved [6, 4, 5, 8, 3, 7]
        ],
        .split [
          .solved [0, 7, 8, 2, 6, 4],
          .solved [6, 4, 8, 7, 5, 2],
          .split [
            .solved [0, 8, 9, 1, 6, 5],
            .solved [8, 6, 7, 9, 0, 4],
            .solved [4, 6, 9, 7, 5, 0],
            .solved [8, 6, 7, 9, 0, 4]
          ],
          .solved [5, 4, 6, 8, 3, 7],
          .solved [4, 6, 8, 7, 5, 0],
          .solved [5, 4, 6, 8, 3, 7]
        ],
        .split [
          .solved [4, 7, 8, 5, 2, 6],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [0, 7, 8, 1, 6, 5],
          .solved [6, 5, 8, 7, 4, 1],
          .solved [5, 6, 8, 7, 4, 0],
          .solved [4, 5, 6, 8, 3, 7]
        ],
        .split [
          .solved [4, 5, 7, 8, 6, 1],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [4, 6, 7, 8, 5, 0],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 3, 8]
        ]
      ],
      .split [
        .split [
          .solved [3, 4, 5, 6, 7, 8],
          .split [
            .solved [0, 1, 2, 8, 3, 9],
            .solved [0, 1, 2, 8, 3, 9],
            .solved [1, 0, 2, 8, 3, 9],
            .solved [3, 4, 5, 6, 7, 9],
            .solved [2, 0, 1, 8, 3, 9],
            .solved [3, 4, 5, 6, 7, 9],
            .solved [3, 4, 5, 6, 7, 9],
            .solved [3, 4, 5, 6, 7, 9]
          ],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 4, 6, 7, 5, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 5, 6, 7, 4, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [0, 1, 2, 7, 3, 8],
          .solved [0, 1, 2, 7, 3, 8],
          .solved [1, 0, 2, 7, 3, 8],
          .split [
            .solved [4, 8, 9, 5, 2, 6],
            .solved [2, 0, 1, 7, 3, 9],
            .solved [4, 5, 6, 8, 3, 9],
            .solved [4, 5, 6, 8, 3, 9],
            .solved [4, 5, 6, 8, 3, 9]
          ],
          .solved [2, 0, 1, 7, 3, 8],
          .split [
            .solved [4, 5, 8, 9, 6, 1],
            .solved [4, 5, 6, 8, 3, 9],
            .solved [4, 5, 6, 8, 3, 9]
          ],
          .split [
            .solved [4, 5, 6, 8, 3, 9],
            .solved [4, 5, 6, 8, 3, 9]
          ],
          .split [
            .solved [4, 5, 6, 8, 3, 9]
          ]
        ],
        .split [
          .solved [1, 7, 8, 2, 5, 4],
          .solved [6, 4, 7, 8, 5, 2],
          .solved [4, 7, 8, 5, 2, 6],
          .solved [6, 5, 7, 8, 4, 1],
          .solved [4, 5, 7, 8, 6, 1],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [2, 7, 8, 4, 0, 6],
          .solved [6, 4, 8, 7, 5, 2],
          .split [
            .solved [1, 8, 9, 5, 0, 6],
            .solved [6, 5, 9, 8, 4, 1],
            .solved [6, 7, 9, 8, 4, 0],
            .solved [5, 4, 6, 9, 3, 7]
          ],
          .solved [5, 4, 6, 8, 3, 7],
          .solved [5, 4, 6, 8, 3, 7],
          .solved [5, 4, 6, 8, 3, 7]
        ],
        .split [
          .solved [4, 7, 8, 5, 2, 6],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [1, 7, 8, 5, 0, 6],
          .solved [6, 5, 8, 7, 4, 1],
          .solved [4, 5, 6, 8, 3, 7],
          .solved [4, 5, 6, 8, 3, 7]
        ],
        .split [
          .solved [4, 5, 7, 8, 6, 1],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 3, 8]
        ]
      ],
      .split [
        .solved [0, 1, 2, 6, 3, 7],
        .solved [0, 1, 2, 6, 3, 7],
        .solved [1, 0, 2, 6, 3, 7],
        .split [
          .solved [2, 7, 8, 4, 6, 5],
          .solved [2, 0, 1, 6, 3, 8],
          .split [
            .solved [1, 8, 9, 5, 6, 4],
            .solved [4, 7, 8, 9, 5, 6],
            .solved [4, 7, 8, 9, 5, 6]
          ],
          .split [
            .solved [6, 8, 9, 7, 0, 4],
            .solved [4, 7, 8, 9, 5, 6]
          ],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .solved [2, 0, 1, 6, 3, 7],
        .split [
          .solved [1, 7, 8, 5, 6, 4],
          .split [
            .solved [6, 8, 9, 7, 0, 4],
            .solved [4, 7, 8, 9, 5, 6]
          ],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [6, 7, 8, 9, 0, 4]
          ],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ]
      ],
      .split [
        .solved [1, 6, 7, 2, 5, 4],
        .split [
          .solved [2, 7, 8, 4, 0, 6],
          .solved [2, 4, 6, 8, 7, 5],
          .split [
            .solved [1, 8, 9, 5, 0, 6],
            .solved [4, 6, 9, 5, 7, 1],
            .solved [6, 7, 9, 8, 4, 0],
            .solved [8, 5, 6, 9, 1, 4]
          ],
          .solved [4, 6, 8, 5, 7, 1],
          .solved [7, 4, 6, 8, 2, 5],
          .solved [7, 4, 6, 8, 2, 5]
        ],
        .split [
          .solved [2, 4, 6, 7, 8, 5],
          .solved [7, 5, 6, 8, 4, 1],
          .solved [4, 5, 6, 8, 7, 1],
          .solved [4, 6, 7, 5, 2, 8],
          .solved [4, 6, 7, 5, 2, 8]
        ],
        .split [
          .solved [1, 7, 8, 5, 0, 6],
          .solved [1, 5, 6, 8, 7, 4],
          .solved [7, 5, 6, 8, 1, 4],
          .solved [7, 5, 6, 8, 1, 4]
        ],
        .split [
          .solved [1, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 1],
          .solved [4, 5, 6, 7, 8, 1]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 2, 6, 7, 8, 4],
          .solved [2, 6, 7, 4, 0, 8],
          .solved [0, 6, 7, 2, 8, 4],
          .solved [2, 6, 7, 4, 0, 8],
          .solved [0, 6, 7, 2, 8, 4],
          .solved [2, 6, 7, 4, 0, 8]
        ],
        .split [
          .solved [2, 4, 7, 8, 6, 5],
          .split [
            .solved [0, 8, 9, 1, 6, 5],
            .solved [7, 5, 9, 8, 4, 1],
            .solved [7, 6, 9, 8, 4, 0],
            .solved [6, 4, 7, 9, 2, 5]
          ],
          .solved [6, 4, 7, 8, 2, 5],
          .solved [6, 4, 7, 8, 2, 5],
          .solved [6, 4, 7, 8, 2, 5]
        ],
        .split [
          .solved [0, 7, 8, 1, 6, 5],
          .split [
            .solved [4, 8, 9, 5, 6, 1],
            .solved [7, 6, 9, 8, 0, 4],
            .solved [7, 5, 8, 9, 1, 4]
          ],
          .split [
            .solved [4, 8, 9, 6, 5, 0],
            .solved [7, 6, 8, 9, 0, 4]
          ],
          .split [
            .solved [4, 8, 9, 5, 6, 7]
          ]
        ],
        .split [
          .solved [4, 7, 8, 5, 6, 1],
          .split [
            .solved [4, 8, 9, 6, 5, 0],
            .solved [4, 7, 8, 5, 6, 9]
          ],
          .split [
            .solved [4, 7, 8, 5, 6, 9]
          ]
        ],
        .split [
          .solved [4, 7, 8, 6, 5, 0],
          .split [
            .solved [4, 7, 8, 5, 6, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 5, 6, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [2, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 2, 8],
          .solved [4, 6, 7, 5, 2, 8],
          .solved [4, 6, 7, 5, 2, 8],
          .solved [4, 6, 7, 5, 2, 8]
        ],
        .split [
          .solved [1, 7, 8, 5, 0, 6],
          .solved [6, 5, 8, 7, 4, 1],
          .split [
            .solved [5, 8, 9, 7, 4, 0],
            .solved [4, 5, 6, 8, 9, 7]
          ],
          .split [
            .solved [4, 5, 6, 8, 9, 7]
          ]
        ],
        .split [
          .solved [4, 5, 7, 8, 6, 1],
          .split [
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 1, 6, 7, 8, 5],
          .solved [1, 6, 7, 5, 0, 8],
          .solved [0, 6, 7, 1, 8, 5],
          .solved [1, 6, 7, 5, 0, 8]
        ],
        .split [
          .solved [1, 5, 7, 8, 6, 4],
          .solved [6, 5, 7, 8, 1, 4],
          .solved [6, 5, 7, 8, 1, 4]
        ],
        .split [
          .solved [5, 7, 8, 6, 4, 0],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ]
      ],
      .split [
        .split [
          .solved [1, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 1],
          .solved [4, 5, 6, 7, 8, 1]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .solved [0, 3, 5, 6, 7, 4],
        .solved [3, 5, 6, 4, 0, 7],
        .split [
          .solved [0, 1, 2, 7, 3, 8],
          .solved [0, 1, 2, 7, 3, 8],
          .solved [1, 0, 2, 7, 3, 8],
          .solved [3, 5, 6, 4, 0, 8],
          .solved [2, 0, 1, 7, 3, 8],
          .solved [3, 5, 6, 4, 0, 8],
          .solved [0, 5, 6, 3, 8, 4],
          .solved [3, 5, 6, 4, 0, 8]
        ],
        .split [
          .split [
            .solved [1, 2, 7, 8, 9, 4],
            .solved [0, 5, 6, 3, 9, 4],
            .solved [3, 5, 6, 4, 0, 9],
            .solved [0, 5, 6, 3, 9, 4],
            .solved [3, 5, 6, 4, 0, 9],
            .solved [0, 5, 6, 3, 9, 4],
            .solved [3, 5, 6, 4, 0, 9]
          ],
          .solved [0, 5, 6, 3, 8, 4],
          .solved [3, 5, 6, 4, 0, 8],
          .solved [0, 5, 6, 3, 8, 4],
          .solved [3, 5, 6, 4, 0, 8],
          .solved [0, 5, 6, 3, 8, 4],
          .solved [3, 5, 6, 4, 0, 8]
        ],
        .solved [0, 5, 6, 3, 7, 4],
        .solved [3, 5, 6, 4, 0, 7],
        .solved [0, 5, 6, 3, 7, 4],
        .solved [3, 5, 6, 4, 0, 7],
        .solved [0, 5, 6, 3, 7, 4],
        .solved [3, 5, 6, 4, 0, 7]
      ],
      .split [
        .split [
          .solved [3, 4, 5, 6, 7, 8],
          .split [
            .solved [0, 1, 2, 8, 3, 9],
            .solved [0, 1, 2, 8, 3, 9],
            .solved [1, 0, 2, 8, 3, 9],
            .solved [3, 4, 5, 6, 7, 9],
            .solved [2, 0, 1, 8, 3, 9],
            .solved [3, 4, 5, 6, 7, 9],
            .solved [3, 4, 5, 6, 7, 9],
            .solved [3, 4, 5, 6, 7, 9]
          ],
          .solved [3, 4, 6, 7, 5, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 5, 6, 7, 4, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [0, 1, 2, 7, 3, 8],
          .solved [0, 1, 2, 7, 3, 8],
          .solved [1, 0, 2, 7, 3, 8],
          .split [
            .solved [4, 8, 9, 5, 2, 6],
            .solved [2, 0, 1, 7, 3, 9],
            .solved [4, 5, 6, 8, 3, 9],
            .solved [4, 5, 6, 8, 3, 9],
            .solved [4, 5, 6, 8, 3, 9]
          ],
          .solved [2, 0, 1, 7, 3, 8],
          .split [
            .solved [4, 5, 6, 8, 3, 9],
            .solved [4, 5, 6, 8, 3, 9],
            .solved [4, 5, 6, 8, 3, 9]
          ],
          .split [
            .solved [4, 5, 8, 9, 6, 0],
            .solved [4, 5, 6, 8, 3, 9]
          ],
          .split [
            .solved [4, 5, 6, 8, 3, 9]
          ]
        ],
        .split [
          .solved [2, 7, 8, 4, 1, 6],
          .solved [6, 4, 8, 7, 5, 2],
          .solved [6, 4, 8, 7, 5, 2],
          .split [
            .solved [0, 8, 9, 5, 1, 6],
            .solved [6, 7, 9, 8, 4, 1],
            .solved [6, 5, 9, 8, 4, 0],
            .solved [5, 4, 6, 9, 3, 7]
          ],
          .solved [5, 4, 6, 8, 3, 7],
          .solved [5, 4, 6, 8, 3, 7],
          .solved [5, 4, 6, 8, 3, 7]
        ],
        .split [
          .solved [0, 7, 8, 2, 5, 4],
          .solved [4, 7, 8, 5, 2, 6],
          .solved [6, 5, 7, 8, 4, 0],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 7, 8, 6, 0],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [4, 7, 8, 5, 2, 6],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [0, 7, 8, 5, 1, 6],
          .solved [4, 5, 6, 8, 3, 7],
          .solved [6, 5, 8, 7, 4, 0],
          .solved [4, 5, 6, 8, 3, 7]
        ],
        .split [
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [4, 5, 7, 8, 6, 0],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 3, 8]
        ]
      ],
      .split [
        .solved [0, 1, 2, 6, 3, 7],
        .solved [0, 1, 2, 6, 3, 7],
        .solved [1, 0, 2, 6, 3, 7],
        .split [
          .solved [2, 7, 8, 4, 6, 5],
          .solved [2, 0, 1, 6, 3, 8],
          .split [
            .solved [6, 8, 9, 7, 1, 4],
            .solved [4, 7, 8, 9, 5, 6],
            .solved [4, 7, 8, 9, 5, 6]
          ],
          .split [
            .solved [0, 8, 9, 5, 6, 4],
            .solved [4, 7, 8, 9, 5, 6]
          ],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .solved [2, 0, 1, 6, 3, 7],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 1],
            .solved [6, 7, 8, 9, 1, 4],
            .solved [6, 7, 8, 9, 1, 4]
          ],
          .split [
            .solved [0, 8, 9, 5, 6, 4],
            .solved [4, 7, 8, 9, 5, 6]
          ],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .split [
          .solved [0, 7, 8, 5, 6, 4],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ]
      ],
      .split [
        .split [
          .solved [1, 2, 6, 7, 8, 4],
          .solved [2, 6, 7, 4, 1, 8],
          .solved [2, 6, 7, 4, 1, 8],
          .solved [1, 6, 7, 2, 8, 4],
          .solved [1, 6, 7, 2, 8, 4],
          .solved [2, 6, 7, 4, 1, 8],
          .solved [2, 6, 7, 4, 1, 8]
        ],
        .split [
          .solved [0, 7, 8, 2, 5, 4],
          .solved [2, 4, 7, 8, 6, 5],
          .split [
            .solved [0, 8, 9, 1, 5, 6],
            .solved [8, 5, 7, 9, 0, 4],
            .solved [4, 7, 9, 5, 6, 0],
            .solved [8, 5, 7, 9, 0, 4]
          ],
          .solved [6, 4, 7, 8, 2, 5],
          .solved [4, 7, 8, 5, 6, 0],
          .solved [6, 4, 7, 8, 2, 5]
        ],
        .split [
          .solved [2, 4, 7, 8, 6, 5],
          .split [
            .solved [0, 8, 9, 1, 5, 6],
            .solved [7, 6, 9, 8, 4, 1],
            .solved [7, 5, 9, 8, 4, 0],
            .solved [6, 4, 7, 9, 2, 5]
          ],
          .solved [6, 4, 7, 8, 2, 5],
          .solved [6, 4, 7, 8, 2, 5],
          .solved [6, 4, 7, 8, 2, 5]
        ],
        .split [
          .solved [0, 7, 8, 1, 5, 6],
          .split [
            .solved [4, 8, 9, 6, 5, 1],
            .solved [7, 5, 9, 8, 0, 4],
            .solved [7, 6, 8, 9, 1, 4]
          ],
          .split [
            .solved [4, 8, 9, 5, 6, 0],
            .solved [7, 5, 8, 9, 0, 4]
          ],
          .split [
            .solved [4, 8, 9, 5, 6, 7]
          ]
        ],
        .split [
          .solved [4, 7, 8, 6, 5, 1],
          .split [
            .solved [4, 8, 9, 5, 6, 0],
            .solved [4, 7, 8, 5, 6, 9]
          ],
          .split [
            .solved [4, 7, 8, 5, 6, 9]
          ]
        ],
        .split [
          .solved [4, 7, 8, 5, 6, 0],
          .split [
            .solved [4, 7, 8, 5, 6, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 5, 6, 9]
          ]
        ]
      ],
      .split [
        .solved [0, 6, 7, 2, 5, 4],
        .split [
          .solved [2, 4, 6, 7, 8, 5],
          .solved [7, 5, 6, 8, 4, 0],
          .solved [4, 6, 7, 5, 2, 8],
          .solved [4, 5, 6, 8, 7, 0],
          .solved [4, 6, 7, 5, 2, 8]
        ],
        .split [
          .solved [0, 7, 8, 5, 1, 6],
          .solved [7, 5, 6, 8, 0, 4],
          .solved [0, 5, 6, 8, 7, 4],
          .solved [7, 5, 6, 8, 0, 4]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 1],
            .solved [4, 5, 6, 9, 7, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .solved [4, 5, 6, 8, 7, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [0, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 0]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [2, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 2, 8],
          .solved [4, 6, 7, 5, 2, 8],
          .solved [4, 6, 7, 5, 2, 8],
          .solved [4, 6, 7, 5, 2, 8]
        ],
        .split [
          .solved [0, 7, 8, 5, 1, 6],
          .split [
            .solved [5, 8, 9, 7, 4, 1],
            .solved [6, 5, 9, 7, 4, 0],
            .solved [4, 5, 6, 8, 9, 7]
          ],
          .solved [6, 5, 8, 7, 4, 0],
          .split [
            .solved [4, 5, 6, 8, 9, 7]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 1],
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 8, 9, 6, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [4, 5, 7, 8, 6, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 6, 7, 1, 5, 8],
          .solved [0, 6, 7, 1, 5, 8],
          .solved [0, 6, 7, 5, 1, 8],
          .solved [0, 6, 7, 5, 1, 8]
        ],
        .split [
          .solved [5, 7, 8, 6, 4, 1],
          .solved [6, 5, 8, 7, 0, 4],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .solved [0, 5, 7, 8, 6, 4],
          .solved [6, 5, 7, 8, 0, 4]
        ],
        .split [
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 1],
          .split [
            .solved [4, 5, 8, 9, 6, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [4, 5, 7, 8, 6, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 0]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [3, 4, 5, 6, 7, 8],
          .split [
            .solved [0, 1, 2, 8, 3, 9],
            .solved [0, 1, 2, 8, 3, 9],
            .solved [1, 0, 2, 8, 3, 9],
            .solved [3, 4, 5, 6, 7, 9],
            .solved [2, 0, 1, 8, 3, 9],
            .solved [3, 4, 5, 6, 7, 9],
            .solved [3, 4, 5, 6, 7, 9],
            .solved [3, 4, 5, 6, 7, 9]
          ],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 5, 6, 7, 4, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [0, 1, 2, 7, 3, 8],
          .solved [0, 1, 2, 7, 3, 8],
          .solved [1, 0, 2, 7, 3, 8],
          .split [
            .solved [4, 8, 9, 5, 2, 6],
            .solved [2, 0, 1, 7, 3, 9],
            .solved [4, 5, 6, 8, 3, 9],
            .solved [4, 5, 6, 8, 3, 9],
            .solved [4, 5, 6, 8, 3, 9]
          ],
          .solved [2, 0, 1, 7, 3, 8],
          .split [
            .solved [4, 5, 6, 8, 3, 9],
            .solved [4, 5, 6, 8, 3, 9],
            .solved [4, 5, 6, 8, 3, 9]
          ],
          .split [
            .solved [4, 5, 6, 8, 3, 9],
            .solved [4, 5, 6, 8, 3, 9]
          ],
          .split [
            .solved [4, 5, 6, 8, 3, 9]
          ]
        ],
        .split [
          .solved [2, 7, 8, 4, 1, 5],
          .solved [4, 7, 8, 5, 2, 6],
          .solved [4, 7, 8, 5, 2, 6],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [2, 7, 8, 4, 0, 5],
          .solved [4, 7, 8, 5, 2, 6],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [4, 7, 8, 5, 2, 6],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .split [
            .solved [0, 7, 8, 9, 1, 5],
            .solved [1, 7, 8, 9, 0, 5],
            .solved [0, 7, 8, 9, 1, 5],
            .solved [4, 5, 6, 9, 3, 7]
          ],
          .solved [4, 5, 6, 8, 3, 7],
          .solved [4, 5, 6, 8, 3, 7],
          .solved [4, 5, 6, 8, 3, 7]
        ],
        .split [
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 3, 8]
        ]
      ],
      .split [
        .solved [0, 1, 2, 6, 3, 7],
        .solved [0, 1, 2, 6, 3, 7],
        .solved [1, 0, 2, 6, 3, 7],
        .split [
          .solved [2, 7, 8, 4, 6, 5],
          .solved [2, 0, 1, 6, 3, 8],
          .split [
            .solved [6, 8, 9, 7, 1, 4],
            .solved [4, 7, 8, 9, 5, 6],
            .solved [4, 7, 8, 9, 5, 6]
          ],
          .split [
            .solved [6, 8, 9, 7, 0, 4],
            .solved [4, 7, 8, 9, 5, 6]
          ],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .solved [2, 0, 1, 6, 3, 7],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 1],
            .solved [6, 7, 8, 9, 1, 4],
            .solved [6, 7, 8, 9, 1, 4]
          ],
          .split [
            .solved [6, 8, 9, 7, 0, 4],
            .solved [4, 7, 8, 9, 5, 6]
          ],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [6, 7, 8, 9, 0, 4]
          ],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ]
      ],
      .split [
        .solved [2, 6, 7, 4, 1, 5],
        .split [
          .solved [2, 7, 8, 4, 0, 5],
          .solved [2, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 2, 8],
          .solved [4, 6, 7, 5, 2, 8],
          .solved [4, 6, 7, 5, 2, 8],
          .solved [4, 6, 7, 5, 2, 8]
        ],
        .split [
          .solved [2, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 2, 8],
          .solved [4, 6, 7, 5, 2, 8],
          .solved [4, 6, 7, 5, 2, 8],
          .solved [4, 6, 7, 5, 2, 8]
        ],
        .split [
          .solved [1, 7, 8, 6, 0, 5],
          .solved [5, 6, 8, 7, 4, 1],
          .split [
            .solved [5, 8, 9, 7, 4, 0],
            .solved [4, 5, 6, 8, 9, 7]
          ],
          .split [
            .solved [4, 5, 6, 8, 9, 7]
          ]
        ],
        .split [
          .solved [4, 6, 7, 8, 5, 1],
          .split [
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .solved [2, 6, 7, 4, 0, 5],
        .split [
          .solved [2, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 2, 8],
          .solved [4, 6, 7, 5, 2, 8],
          .solved [4, 6, 7, 5, 2, 8],
          .solved [4, 6, 7, 5, 2, 8]
        ],
        .split [
          .solved [0, 7, 8, 6, 1, 5],
          .split [
            .solved [5, 8, 9, 7, 4, 1],
            .solved [5, 6, 9, 7, 4, 0],
            .solved [4, 5, 6, 8, 9, 7]
          ],
          .solved [5, 6, 8, 7, 4, 0],
          .split [
            .solved [4, 5, 6, 8, 9, 7]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 1],
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 6, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [4, 6, 7, 8, 5, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [2, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 2, 8],
          .solved [4, 6, 7, 5, 2, 8],
          .solved [4, 6, 7, 5, 2, 8],
          .solved [4, 6, 7, 5, 2, 8]
        ],
        .split [
          .split [
            .solved [0, 7, 8, 9, 1, 5],
            .solved [1, 7, 8, 9, 0, 5],
            .solved [0, 7, 8, 9, 1, 5],
            .solved [5, 6, 9, 7, 4, 8]
          ],
          .split [
            .solved [5, 8, 9, 7, 4, 1],
            .solved [4, 5, 6, 8, 9, 7],
            .solved [4, 5, 6, 8, 9, 7]
          ],
          .split [
            .solved [5, 8, 9, 7, 4, 0],
            .solved [4, 5, 6, 8, 9, 7]
          ],
          .split [
            .solved [4, 5, 6, 8, 9, 7]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 1],
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 6, 7, 8, 1, 5],
          .solved [1, 6, 7, 8, 0, 5],
          .solved [0, 6, 7, 8, 1, 5],
          .split [
            .solved [5, 8, 9, 6, 4, 7]
          ]
        ],
        .split [
          .solved [5, 7, 8, 6, 4, 1],
          .split [
            .solved [5, 8, 9, 6, 4, 0],
            .solved [4, 5, 7, 8, 9, 6]
          ],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .solved [5, 7, 8, 6, 4, 0],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 1],
          .split [
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .solved [0, 1, 2, 5, 3, 6],
      .solved [0, 1, 2, 5, 3, 6],
      .solved [1, 0, 2, 5, 3, 6],
      .split [
        .split [
          .solved [2, 6, 7, 4, 5, 8],
          .solved [2, 0, 1, 5, 3, 8],
          .solved [2, 6, 7, 4, 5, 8],
          .solved [2, 6, 7, 4, 5, 8],
          .solved [2, 6, 7, 4, 5, 8]
        ],
        .solved [2, 0, 1, 5, 3, 7],
        .split [
          .solved [5, 7, 8, 6, 1, 4],
          .split [
            .solved [5, 8, 9, 6, 0, 4],
            .solved [4, 6, 7, 8, 9, 5]
          ],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .solved [5, 7, 8, 6, 0, 4],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .solved [2, 0, 1, 5, 3, 6],
      .split [
        .split [
          .solved [1, 6, 7, 8, 5, 4],
          .solved [5, 6, 7, 8, 1, 4],
          .solved [5, 6, 7, 8, 1, 4]
        ],
        .split [
          .solved [5, 7, 8, 6, 0, 4],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 6, 7, 8, 5, 4],
          .solved [5, 6, 7, 8, 0, 4]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .solved [1, 2, 5, 6, 7, 4],
        .solved [2, 5, 6, 4, 1, 7],
        .solved [2, 5, 6, 4, 1, 7],
        .solved [1, 5, 6, 2, 7, 4],
        .solved [1, 5, 6, 2, 7, 4],
        .solved [2, 5, 6, 4, 1, 7],
        .solved [2, 5, 6, 4, 1, 7]
      ],
      .split [
        .solved [2, 6, 7, 4, 0, 5],
        .split [
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 5, 6, 7, 4, 8],
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [0, 7, 8, 1, 6, 5],
          .solved [6, 5, 8, 7, 4, 1],
          .solved [5, 6, 8, 7, 4, 0],
          .solved [4, 5, 6, 8, 2, 7]
        ],
        .split [
          .solved [4, 5, 7, 8, 6, 1],
          .solved [4, 5, 6, 7, 2, 8],
          .solved [4, 5, 6, 7, 2, 8]
        ],
        .split [
          .solved [4, 6, 7, 8, 5, 0],
          .solved [4, 5, 6, 7, 2, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 2, 8]
        ]
      ],
      .split [
        .split [
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 5, 6, 7, 4, 8],
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [1, 7, 8, 5, 0, 6],
          .solved [6, 5, 8, 7, 4, 1],
          .solved [4, 5, 6, 8, 2, 7],
          .solved [4, 5, 6, 8, 2, 7]
        ],
        .split [
          .solved [4, 5, 7, 8, 6, 1],
          .solved [4, 5, 6, 7, 2, 8],
          .solved [4, 5, 6, 7, 2, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 2, 8],
          .solved [4, 5, 6, 7, 2, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 2, 8]
        ]
      ],
      .split [
        .split [
          .solved [0, 1, 6, 7, 8, 5],
          .solved [1, 6, 7, 5, 0, 8],
          .solved [0, 6, 7, 1, 8, 5],
          .solved [1, 6, 7, 5, 0, 8]
        ],
        .split [
          .solved [1, 5, 7, 8, 6, 4],
          .solved [6, 5, 7, 8, 1, 4],
          .solved [6, 5, 7, 8, 1, 4]
        ],
        .split [
          .solved [5, 7, 8, 6, 4, 0],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ]
      ],
      .split [
        .split [
          .solved [1, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 1],
          .solved [4, 5, 6, 7, 8, 1]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .solved [0, 2, 5, 6, 7, 4],
        .solved [2, 5, 6, 4, 0, 7],
        .solved [0, 5, 6, 2, 7, 4],
        .solved [2, 5, 6, 4, 0, 7],
        .solved [0, 5, 6, 2, 7, 4],
        .solved [2, 5, 6, 4, 0, 7]
      ],
      .split [
        .split [
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 5, 6, 7, 4, 8],
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [0, 7, 8, 5, 1, 6],
          .solved [4, 5, 6, 8, 2, 7],
          .solved [6, 5, 8, 7, 4, 0],
          .solved [4, 5, 6, 8, 2, 7]
        ],
        .split [
          .solved [4, 5, 6, 7, 2, 8],
          .solved [4, 5, 6, 7, 2, 8],
          .solved [4, 5, 6, 7, 2, 8]
        ],
        .split [
          .solved [4, 5, 7, 8, 6, 0],
          .solved [4, 5, 6, 7, 2, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 2, 8]
        ]
      ],
      .split [
        .split [
          .solved [0, 6, 7, 1, 5, 8],
          .solved [0, 6, 7, 1, 5, 8],
          .solved [0, 6, 7, 5, 1, 8],
          .solved [0, 6, 7, 5, 1, 8]
        ],
        .split [
          .solved [5, 7, 8, 6, 4, 1],
          .solved [6, 5, 8, 7, 0, 4],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .solved [0, 5, 7, 8, 6, 4],
          .solved [6, 5, 7, 8, 0, 4]
        ],
        .split [
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 1],
          .split [
            .solved [4, 5, 8, 9, 6, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [4, 5, 7, 8, 6, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 0]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 5, 6, 7, 4, 8],
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 4, 5, 6, 7, 8]
        ],
        .split [
          .split [
            .solved [0, 7, 8, 9, 1, 5],
            .solved [1, 7, 8, 9, 0, 5],
            .solved [0, 7, 8, 9, 1, 5],
            .solved [4, 5, 6, 9, 2, 7]
          ],
          .solved [4, 5, 6, 8, 2, 7],
          .solved [4, 5, 6, 8, 2, 7],
          .solved [4, 5, 6, 8, 2, 7]
        ],
        .split [
          .solved [4, 5, 6, 7, 2, 8],
          .solved [4, 5, 6, 7, 2, 8],
          .solved [4, 5, 6, 7, 2, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 2, 8],
          .solved [4, 5, 6, 7, 2, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 2, 8]
        ]
      ],
      .split [
        .split [
          .solved [0, 6, 7, 8, 1, 5],
          .solved [1, 6, 7, 8, 0, 5],
          .solved [0, 6, 7, 8, 1, 5],
          .split [
            .solved [5, 8, 9, 6, 4, 7]
          ]
        ],
        .split [
          .solved [5, 7, 8, 6, 4, 1],
          .split [
            .solved [5, 8, 9, 6, 4, 0],
            .solved [4, 5, 7, 8, 9, 6]
          ],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .solved [5, 7, 8, 6, 4, 0],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 1],
          .split [
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [0, 1, 5, 6, 7, 8],
          .solved [0, 1, 5, 6, 7, 8],
          .solved [0, 5, 6, 1, 8, 7],
          .solved [0, 5, 6, 7, 1, 8]
        ],
        .split [
          .solved [1, 5, 6, 7, 0, 8],
          .solved [0, 5, 6, 1, 8, 7],
          .solved [1, 5, 6, 7, 0, 8]
        ],
        .split [
          .solved [0, 5, 6, 7, 1, 8],
          .solved [0, 5, 6, 7, 1, 8]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ]
      ],
      .split [
        .split [
          .solved [1, 6, 7, 8, 5, 4],
          .solved [5, 6, 7, 8, 1, 4],
          .solved [5, 6, 7, 8, 1, 4]
        ],
        .split [
          .solved [5, 7, 8, 6, 0, 4],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 6, 7, 8, 5, 4],
          .solved [5, 6, 7, 8, 0, 4]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [1, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 1],
          .solved [4, 5, 6, 7, 8, 1]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [0, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 0]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ]
  ]

private def tree6a4 : WitnessTree :=
  .split [
    .solved [0, 1, 3, 4, 2, 5],
    .solved [0, 1, 3, 4, 2, 5],
    .solved [1, 0, 3, 4, 2, 5],
    .split [
      .split [
        .split [
          .solved [3, 4, 5, 6, 7, 8],
          .solved [2, 0, 1, 3, 8, 4],
          .solved [3, 5, 6, 7, 4, 8],
          .solved [3, 5, 6, 7, 4, 8],
          .solved [3, 5, 6, 7, 4, 8],
          .solved [3, 0, 1, 4, 2, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 4, 5, 6, 7, 8]
        ],
        .solved [2, 0, 1, 3, 7, 4],
        .split [
          .split [
            .solved [1, 7, 8, 9, 2, 5],
            .solved [2, 7, 8, 9, 1, 5],
            .solved [2, 7, 8, 9, 1, 5],
            .solved [3, 0, 1, 4, 2, 9],
            .solved [1, 7, 8, 9, 2, 5],
            .solved [4, 5, 6, 9, 3, 7],
            .solved [4, 5, 6, 9, 3, 7]
          ],
          .split [
            .solved [2, 8, 9, 7, 0, 5],
            .solved [5, 7, 8, 9, 6, 2],
            .solved [3, 0, 1, 4, 2, 9],
            .solved [4, 5, 6, 9, 3, 7],
            .solved [4, 5, 6, 9, 3, 7],
            .solved [4, 5, 6, 9, 3, 7]
          ],
          .split [
            .solved [5, 7, 8, 9, 6, 2],
            .solved [3, 0, 1, 4, 2, 9],
            .solved [4, 5, 6, 9, 3, 7],
            .solved [4, 5, 6, 9, 3, 7],
            .solved [4, 5, 6, 9, 3, 7]
          ],
          .solved [3, 0, 1, 4, 2, 8],
          .solved [4, 5, 6, 8, 3, 7],
          .solved [4, 5, 6, 8, 3, 7],
          .solved [4, 5, 6, 8, 3, 7]
        ],
        .split [
          .split [
            .solved [0, 7, 8, 9, 2, 5],
            .solved [2, 7, 8, 9, 0, 5],
            .solved [3, 0, 1, 4, 2, 9],
            .solved [4, 5, 6, 9, 3, 7],
            .solved [0, 7, 8, 9, 2, 5],
            .solved [4, 5, 6, 9, 3, 7]
          ],
          .split [
            .solved [5, 7, 8, 9, 6, 2],
            .solved [3, 0, 1, 4, 2, 9],
            .solved [4, 5, 6, 9, 3, 7],
            .solved [4, 5, 6, 9, 3, 7],
            .solved [4, 5, 6, 9, 3, 7]
          ],
          .solved [3, 0, 1, 4, 2, 8],
          .solved [4, 5, 6, 8, 3, 7],
          .solved [4, 5, 6, 8, 3, 7],
          .solved [4, 5, 6, 8, 3, 7]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 2],
            .solved [3, 0, 1, 4, 2, 9],
            .solved [4, 5, 6, 9, 3, 7],
            .solved [4, 5, 6, 9, 3, 7],
            .solved [4, 5, 6, 9, 3, 7]
          ],
          .solved [3, 0, 1, 4, 2, 8],
          .solved [4, 5, 6, 8, 3, 7],
          .solved [4, 5, 6, 8, 3, 7],
          .solved [4, 5, 6, 8, 3, 7]
        ],
        .solved [3, 0, 1, 4, 2, 7],
        .split [
          .solved [4, 7, 8, 5, 1, 6],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [4, 7, 8, 5, 0, 6],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 3, 8]
        ]
      ],
      .solved [2, 0, 1, 3, 6, 4],
      .split [
        .split [
          .solved [1, 6, 7, 8, 2, 5],
          .solved [2, 6, 7, 8, 1, 5],
          .solved [2, 6, 7, 8, 1, 5],
          .solved [3, 0, 1, 4, 2, 8],
          .solved [1, 6, 7, 8, 2, 5],
          .split [
            .solved [4, 8, 9, 5, 0, 6],
            .solved [5, 8, 9, 6, 4, 7]
          ],
          .split [
            .solved [5, 8, 9, 6, 4, 7]
          ]
        ],
        .split [
          .solved [2, 7, 8, 6, 0, 5],
          .split [
            .solved [2, 6, 7, 8, 9, 5],
            .solved [3, 0, 1, 4, 2, 9],
            .solved [5, 6, 7, 8, 9, 2],
            .solved [5, 6, 7, 8, 9, 2],
            .solved [5, 6, 7, 8, 9, 2]
          ],
          .solved [3, 0, 1, 4, 2, 8],
          .split [
            .solved [1, 8, 9, 4, 6, 5],
            .solved [5, 8, 9, 6, 4, 7],
            .solved [5, 8, 9, 6, 4, 7]
          ],
          .split [
            .solved [4, 8, 9, 5, 0, 6],
            .solved [5, 8, 9, 6, 4, 7]
          ],
          .split [
            .solved [5, 8, 9, 6, 4, 7]
          ]
        ],
        .split [
          .split [
            .solved [2, 6, 7, 8, 9, 5],
            .solved [3, 0, 1, 4, 2, 9],
            .solved [5, 6, 7, 8, 9, 2],
            .solved [5, 6, 7, 8, 9, 2],
            .solved [5, 6, 7, 8, 9, 2]
          ],
          .solved [3, 0, 1, 4, 2, 8],
          .split [
            .solved [1, 8, 9, 4, 6, 5],
            .solved [5, 8, 9, 6, 4, 7],
            .solved [5, 8, 9, 6, 4, 7]
          ],
          .split [
            .solved [4, 8, 9, 5, 0, 6],
            .solved [5, 8, 9, 6, 4, 7]
          ],
          .split [
            .solved [5, 8, 9, 6, 4, 7]
          ]
        ],
        .solved [3, 0, 1, 4, 2, 7],
        .split [
          .solved [1, 7, 8, 4, 6, 5],
          .split [
            .solved [4, 8, 9, 5, 0, 6],
            .solved [4, 5, 7, 8, 9, 6]
          ],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .solved [4, 7, 8, 5, 0, 6],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 6, 7, 8, 2, 5],
          .solved [2, 6, 7, 8, 0, 5],
          .solved [3, 0, 1, 4, 2, 8],
          .split [
            .solved [4, 8, 9, 5, 1, 6],
            .solved [0, 6, 7, 9, 2, 5],
            .solved [5, 8, 9, 6, 4, 7]
          ],
          .solved [0, 6, 7, 8, 2, 5],
          .split [
            .solved [5, 8, 9, 6, 4, 7]
          ]
        ],
        .split [
          .split [
            .solved [2, 6, 7, 8, 9, 5],
            .solved [3, 0, 1, 4, 2, 9],
            .solved [5, 6, 7, 8, 9, 2],
            .solved [5, 6, 7, 8, 9, 2],
            .solved [5, 6, 7, 8, 9, 2]
          ],
          .solved [3, 0, 1, 4, 2, 8],
          .split [
            .solved [4, 8, 9, 5, 1, 6],
            .solved [5, 8, 9, 6, 4, 7],
            .solved [5, 8, 9, 6, 4, 7]
          ],
          .split [
            .solved [0, 8, 9, 4, 6, 5],
            .solved [5, 8, 9, 6, 4, 7]
          ],
          .split [
            .solved [5, 8, 9, 6, 4, 7]
          ]
        ],
        .solved [3, 0, 1, 4, 2, 7],
        .split [
          .solved [4, 7, 8, 5, 1, 6],
          .split [
            .solved [0, 8, 9, 4, 6, 5],
            .solved [4, 5, 7, 8, 9, 6]
          ],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .solved [0, 7, 8, 4, 6, 5],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [2, 6, 7, 8, 9, 5],
            .solved [3, 0, 1, 4, 2, 9],
            .solved [5, 6, 7, 8, 9, 2],
            .solved [5, 6, 7, 8, 9, 2],
            .solved [5, 6, 7, 8, 9, 2]
          ],
          .solved [3, 0, 1, 4, 2, 8],
          .split [
            .solved [4, 8, 9, 5, 1, 6],
            .solved [5, 8, 9, 6, 4, 7],
            .solved [5, 8, 9, 6, 4, 7]
          ],
          .split [
            .solved [4, 8, 9, 5, 0, 6],
            .solved [5, 8, 9, 6, 4, 7]
          ],
          .split [
            .solved [5, 8, 9, 6, 4, 7]
          ]
        ],
        .solved [3, 0, 1, 4, 2, 7],
        .split [
          .solved [4, 7, 8, 5, 1, 6],
          .split [
            .solved [4, 8, 9, 5, 0, 6],
            .solved [4, 5, 7, 8, 9, 6]
          ],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .solved [4, 7, 8, 5, 0, 6],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ]
      ],
      .solved [3, 0, 1, 4, 2, 6],
      .split [
        .split [
          .solved [1, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 1, 8],
          .solved [4, 6, 7, 5, 1, 8]
        ],
        .split [
          .solved [4, 7, 8, 5, 0, 6],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 0, 8]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .solved [2, 0, 1, 3, 5, 4],
    .split [
      .split [
        .split [
          .solved [1, 2, 5, 6, 7, 8],
          .solved [1, 2, 5, 6, 7, 8],
          .solved [1, 2, 5, 6, 7, 8],
          .solved [3, 0, 1, 4, 2, 8],
          .solved [1, 5, 6, 2, 8, 7],
          .solved [1, 5, 6, 7, 2, 8],
          .solved [1, 5, 6, 7, 2, 8]
        ],
        .split [
          .solved [2, 7, 8, 5, 0, 6],
          .solved [2, 5, 6, 7, 1, 8],
          .solved [3, 0, 1, 4, 2, 8],
          .solved [1, 5, 6, 2, 8, 7],
          .solved [2, 5, 6, 7, 1, 8],
          .solved [2, 5, 6, 7, 1, 8]
        ],
        .split [
          .solved [2, 5, 6, 7, 1, 8],
          .solved [3, 0, 1, 4, 2, 8],
          .solved [1, 5, 6, 2, 8, 7],
          .solved [2, 5, 6, 7, 1, 8],
          .solved [2, 5, 6, 7, 1, 8]
        ],
        .solved [3, 0, 1, 4, 2, 7],
        .split [
          .solved [1, 5, 6, 7, 2, 8],
          .solved [1, 5, 6, 7, 2, 8],
          .solved [1, 5, 6, 7, 2, 8]
        ],
        .split [
          .split [
            .solved [0, 7, 8, 9, 4, 5],
            .solved [4, 7, 8, 9, 0, 5]
          ],
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 2, 6, 7, 8, 5],
          .solved [2, 6, 7, 5, 0, 8],
          .solved [3, 0, 1, 4, 2, 8],
          .solved [2, 6, 7, 5, 0, 8],
          .solved [0, 6, 7, 2, 8, 5],
          .solved [2, 6, 7, 5, 0, 8]
        ],
        .split [
          .split [
            .solved [2, 5, 6, 7, 8, 9],
            .solved [3, 0, 1, 4, 2, 9],
            .solved [2, 5, 6, 7, 8, 9],
            .solved [2, 5, 6, 7, 8, 9],
            .solved [2, 5, 6, 7, 8, 9]
          ],
          .solved [3, 0, 1, 4, 2, 8],
          .split [
            .solved [1, 8, 9, 5, 4, 6],
            .solved [5, 6, 7, 8, 2, 9],
            .solved [5, 6, 7, 8, 2, 9]
          ],
          .split [
            .solved [0, 8, 9, 6, 4, 5],
            .solved [5, 6, 7, 8, 2, 9]
          ],
          .split [
            .solved [5, 6, 7, 8, 2, 9]
          ]
        ],
        .solved [3, 0, 1, 4, 2, 7],
        .split [
          .solved [1, 7, 8, 5, 4, 6],
          .split [
            .solved [0, 8, 9, 6, 4, 5],
            .solved [5, 7, 8, 9, 6, 4]
          ],
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ],
        .split [
          .solved [0, 7, 8, 6, 4, 5],
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [2, 5, 6, 7, 8, 9],
            .solved [3, 0, 1, 4, 2, 9],
            .solved [2, 5, 6, 7, 8, 9],
            .solved [2, 5, 6, 7, 8, 9],
            .solved [2, 5, 6, 7, 8, 9]
          ],
          .solved [3, 0, 1, 4, 2, 8],
          .split [
            .solved [1, 8, 9, 5, 4, 6],
            .solved [5, 6, 7, 8, 2, 9],
            .solved [5, 6, 7, 8, 2, 9]
          ],
          .split [
            .solved [5, 6, 7, 8, 2, 9],
            .solved [5, 6, 7, 8, 2, 9]
          ],
          .split [
            .solved [5, 6, 7, 8, 2, 9]
          ]
        ],
        .solved [3, 0, 1, 4, 2, 7],
        .split [
          .solved [1, 7, 8, 5, 4, 6],
          .split [
            .solved [4, 8, 9, 7, 0, 5],
            .solved [5, 7, 8, 9, 6, 4]
          ],
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ],
        .split [
          .split [
            .solved [0, 7, 8, 9, 4, 5],
            .solved [4, 7, 8, 9, 0, 5]
          ],
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ]
      ],
      .solved [3, 0, 1, 4, 2, 6],
      .split [
        .split [
          .solved [1, 6, 7, 4, 5, 8],
          .solved [1, 6, 7, 4, 5, 8],
          .solved [1, 6, 7, 4, 5, 8]
        ],
        .split [
          .solved [4, 7, 8, 6, 0, 5],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 6, 7, 8, 4, 5],
          .solved [4, 6, 7, 8, 0, 5]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [0, 2, 5, 6, 7, 8],
          .solved [0, 2, 5, 6, 7, 8],
          .solved [3, 0, 1, 4, 2, 8],
          .solved [0, 5, 6, 7, 2, 8],
          .solved [0, 5, 6, 2, 8, 7],
          .solved [0, 5, 6, 7, 2, 8]
        ],
        .split [
          .solved [2, 5, 6, 7, 0, 8],
          .solved [3, 0, 1, 4, 2, 8],
          .solved [2, 5, 6, 7, 0, 8],
          .solved [0, 5, 6, 2, 8, 7],
          .solved [2, 5, 6, 7, 0, 8]
        ],
        .solved [3, 0, 1, 4, 2, 7],
        .split [
          .split [
            .solved [1, 7, 8, 9, 4, 5],
            .solved [0, 5, 6, 9, 2, 7],
            .solved [4, 7, 8, 9, 1, 5]
          ],
          .solved [0, 5, 6, 8, 2, 7],
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ],
        .split [
          .solved [0, 5, 6, 7, 2, 8],
          .solved [0, 5, 6, 7, 2, 8]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [2, 5, 6, 7, 8, 9],
            .solved [3, 0, 1, 4, 2, 9],
            .solved [2, 5, 6, 7, 8, 9],
            .solved [2, 5, 6, 7, 8, 9],
            .solved [2, 5, 6, 7, 8, 9]
          ],
          .solved [3, 0, 1, 4, 2, 8],
          .split [
            .solved [5, 6, 7, 8, 2, 9],
            .solved [5, 6, 7, 8, 2, 9],
            .solved [5, 6, 7, 8, 2, 9]
          ],
          .split [
            .solved [0, 8, 9, 5, 4, 6],
            .solved [5, 6, 7, 8, 2, 9]
          ],
          .split [
            .solved [5, 6, 7, 8, 2, 9]
          ]
        ],
        .solved [3, 0, 1, 4, 2, 7],
        .split [
          .split [
            .solved [1, 7, 8, 9, 4, 5],
            .solved [4, 7, 8, 9, 1, 5],
            .solved [4, 7, 8, 9, 1, 5]
          ],
          .split [
            .solved [0, 8, 9, 5, 4, 6],
            .solved [5, 7, 8, 9, 6, 4]
          ],
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ],
        .split [
          .solved [0, 7, 8, 5, 4, 6],
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ]
      ],
      .solved [3, 0, 1, 4, 2, 6],
      .split [
        .split [
          .solved [1, 6, 7, 8, 4, 5],
          .solved [4, 6, 7, 8, 1, 5],
          .solved [4, 6, 7, 8, 1, 5]
        ],
        .split [
          .solved [0, 7, 8, 4, 5, 6],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 6, 7, 4, 5, 8],
          .solved [0, 6, 7, 4, 5, 8]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .split [
            .solved [2, 5, 6, 7, 8, 9],
            .solved [3, 0, 1, 4, 2, 9],
            .solved [2, 5, 6, 7, 8, 9],
            .solved [2, 5, 6, 7, 8, 9],
            .solved [2, 5, 6, 7, 8, 9]
          ],
          .solved [3, 0, 1, 4, 2, 8],
          .split [
            .solved [5, 6, 7, 8, 2, 9],
            .solved [5, 6, 7, 8, 2, 9],
            .solved [5, 6, 7, 8, 2, 9]
          ],
          .split [
            .solved [5, 6, 7, 8, 2, 9],
            .solved [5, 6, 7, 8, 2, 9]
          ],
          .split [
            .solved [5, 6, 7, 8, 2, 9]
          ]
        ],
        .solved [3, 0, 1, 4, 2, 7],
        .split [
          .split [
            .solved [1, 7, 8, 9, 4, 5],
            .solved [4, 7, 8, 9, 1, 5],
            .solved [4, 7, 8, 9, 1, 5]
          ],
          .split [
            .solved [4, 8, 9, 7, 0, 5],
            .solved [5, 7, 8, 9, 6, 4]
          ],
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ],
        .split [
          .split [
            .solved [0, 7, 8, 9, 4, 5],
            .solved [4, 7, 8, 9, 0, 5]
          ],
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ]
      ],
      .solved [3, 0, 1, 4, 2, 6],
      .split [
        .split [
          .solved [1, 6, 7, 8, 4, 5],
          .solved [4, 6, 7, 8, 1, 5],
          .solved [4, 6, 7, 8, 1, 5]
        ],
        .split [
          .solved [4, 7, 8, 6, 0, 5],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 6, 7, 8, 4, 5],
          .solved [4, 6, 7, 8, 0, 5]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ]
    ],
    .solved [3, 0, 1, 4, 2, 5],
    .split [
      .split [
        .split [
          .solved [1, 4, 5, 6, 7, 8],
          .solved [1, 4, 5, 6, 7, 8],
          .solved [1, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [4, 7, 8, 5, 0, 6],
          .solved [4, 5, 6, 7, 1, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 1, 8]
        ]
      ],
      .split [
        .split [
          .solved [0, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 0, 8]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [0, 4, 5, 6, 7, 8],
          .solved [0, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 0, 8]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ]
  ]

private def tree6a5 : WitnessTree :=
  .split [
    .split [
      .split [
        .solved [1, 3, 4, 5, 6, 7],
        .solved [1, 3, 4, 5, 6, 7],
        .solved [1, 3, 4, 5, 6, 7],
        .split [
          .solved [0, 1, 2, 7, 3, 8],
          .solved [0, 1, 2, 7, 3, 8],
          .solved [1, 0, 2, 7, 3, 8],
          .solved [1, 4, 5, 6, 3, 8],
          .solved [2, 0, 1, 7, 3, 8],
          .solved [1, 4, 5, 3, 8, 6],
          .solved [1, 4, 5, 6, 3, 8],
          .solved [1, 4, 5, 6, 3, 8]
        ],
        .solved [1, 4, 5, 3, 7, 6],
        .split [
          .split [
            .split [
              .solved [0, 2, 7, 8, 9, 10],
              .solved [0, 2, 7, 8, 9, 10],
              .solved [0, 7, 8, 2, 10, 9],
              .solved [0, 7, 8, 9, 2, 10],
              .solved [0, 7, 8, 2, 10, 9],
              .solved [0, 7, 8, 9, 2, 10]
            ],
            .solved [1, 4, 5, 6, 3, 9],
            .solved [1, 4, 5, 3, 9, 6],
            .solved [1, 4, 5, 3, 9, 6],
            .solved [1, 4, 5, 6, 3, 9],
            .solved [1, 4, 5, 6, 3, 9]
          ],
          .solved [1, 4, 5, 6, 3, 8],
          .solved [1, 4, 5, 3, 8, 6],
          .solved [1, 4, 5, 3, 8, 6],
          .solved [1, 4, 5, 6, 3, 8],
          .solved [1, 4, 5, 6, 3, 8]
        ],
        .solved [1, 4, 5, 6, 3, 7],
        .solved [1, 4, 5, 3, 7, 6],
        .solved [1, 4, 5, 3, 7, 6],
        .solved [1, 4, 5, 6, 3, 7],
        .solved [1, 4, 5, 6, 3, 7]
      ],
      .split [
        .solved [3, 6, 7, 4, 0, 5],
        .solved [3, 4, 5, 6, 1, 7],
        .split [
          .solved [0, 1, 2, 7, 3, 8],
          .solved [0, 1, 2, 7, 3, 8],
          .solved [1, 0, 2, 7, 3, 8],
          .solved [3, 4, 5, 6, 1, 8],
          .solved [2, 0, 1, 7, 3, 8],
          .solved [1, 4, 5, 3, 8, 6],
          .solved [3, 4, 5, 6, 1, 8],
          .solved [3, 4, 5, 6, 1, 8]
        ],
        .solved [1, 4, 5, 3, 7, 6],
        .split [
          .split [
            .solved [0, 7, 8, 2, 6, 9],
            .solved [0, 7, 8, 2, 6, 9],
            .solved [0, 7, 8, 6, 2, 9],
            .solved [0, 7, 8, 6, 2, 9],
            .solved [0, 7, 8, 6, 2, 9],
            .solved [0, 7, 8, 6, 2, 9]
          ],
          .solved [3, 4, 5, 6, 1, 8],
          .solved [1, 4, 5, 3, 8, 6],
          .solved [1, 4, 5, 3, 8, 6],
          .solved [3, 4, 5, 6, 1, 8],
          .solved [3, 4, 5, 6, 1, 8]
        ],
        .solved [3, 4, 5, 6, 1, 7],
        .solved [1, 4, 5, 3, 7, 6],
        .solved [1, 4, 5, 3, 7, 6],
        .solved [3, 4, 5, 6, 1, 7],
        .solved [3, 4, 5, 6, 1, 7]
      ],
      .split [
        .solved [3, 4, 5, 6, 1, 7],
        .split [
          .solved [0, 1, 2, 7, 3, 8],
          .solved [0, 1, 2, 7, 3, 8],
          .solved [1, 0, 2, 7, 3, 8],
          .solved [3, 4, 5, 6, 1, 8],
          .solved [2, 0, 1, 7, 3, 8],
          .solved [1, 4, 5, 3, 8, 6],
          .solved [3, 4, 5, 6, 1, 8],
          .solved [3, 4, 5, 6, 1, 8]
        ],
        .solved [1, 4, 5, 3, 7, 6],
        .split [
          .split [
            .solved [0, 7, 8, 9, 2, 6],
            .solved [2, 7, 8, 9, 0, 6],
            .solved [0, 7, 8, 9, 2, 6],
            .solved [1, 4, 5, 3, 9, 6],
            .solved [0, 7, 8, 9, 2, 6],
            .solved [3, 4, 5, 6, 1, 9]
          ],
          .solved [3, 4, 5, 6, 1, 8],
          .solved [1, 4, 5, 3, 8, 6],
          .solved [1, 4, 5, 3, 8, 6],
          .solved [3, 4, 5, 6, 1, 8],
          .solved [3, 4, 5, 6, 1, 8]
        ],
        .solved [3, 4, 5, 6, 1, 7],
        .solved [1, 4, 5, 3, 7, 6],
        .solved [1, 4, 5, 3, 7, 6],
        .solved [3, 4, 5, 6, 1, 7],
        .solved [3, 4, 5, 6, 1, 7]
      ],
      .split [
        .solved [0, 1, 2, 6, 3, 7],
        .solved [0, 1, 2, 6, 3, 7],
        .solved [1, 0, 2, 6, 3, 7],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 2],
            .solved [2, 0, 1, 6, 3, 9],
            .solved [1, 4, 5, 9, 3, 7],
            .solved [6, 7, 8, 9, 2, 4],
            .solved [6, 7, 8, 9, 2, 4]
          ],
          .solved [2, 0, 1, 6, 3, 8],
          .solved [1, 4, 5, 8, 3, 7],
          .split [
            .solved [6, 8, 9, 7, 0, 4],
            .solved [4, 7, 8, 9, 5, 6]
          ],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .solved [2, 0, 1, 6, 3, 7],
        .split [
          .solved [1, 4, 5, 7, 3, 8],
          .solved [1, 4, 5, 7, 3, 8],
          .solved [1, 4, 5, 7, 3, 8]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [6, 7, 8, 9, 0, 4]
          ],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ]
      ],
      .split [
        .solved [1, 6, 7, 4, 2, 5],
        .split [
          .split [
            .solved [0, 2, 7, 8, 9, 6],
            .solved [2, 7, 8, 6, 0, 9],
            .solved [0, 7, 8, 2, 9, 6],
            .solved [2, 7, 8, 6, 0, 9],
            .solved [0, 7, 8, 2, 9, 6],
            .solved [2, 7, 8, 6, 0, 9]
          ],
          .solved [1, 4, 5, 6, 3, 8],
          .solved [1, 4, 5, 6, 3, 8],
          .solved [1, 4, 5, 6, 3, 8],
          .solved [1, 4, 5, 6, 3, 8],
          .solved [1, 4, 5, 6, 3, 8]
        ],
        .solved [1, 4, 5, 6, 3, 7],
        .solved [1, 4, 5, 6, 3, 7],
        .solved [1, 4, 5, 6, 3, 7],
        .solved [1, 4, 5, 6, 3, 7],
        .solved [1, 4, 5, 6, 3, 7]
      ],
      .split [
        .split [
          .split [
            .solved [0, 2, 6, 7, 8, 9],
            .solved [0, 2, 6, 7, 8, 9],
            .solved [0, 6, 7, 2, 9, 8],
            .solved [0, 6, 7, 8, 2, 9],
            .solved [0, 6, 7, 2, 9, 8],
            .solved [0, 6, 7, 8, 2, 9]
          ],
          .split [
            .solved [2, 6, 7, 8, 0, 9],
            .solved [0, 6, 7, 2, 9, 8],
            .solved [2, 6, 7, 8, 0, 9],
            .solved [0, 6, 7, 2, 9, 8],
            .solved [2, 6, 7, 8, 0, 9]
          ],
          .split [
            .solved [1, 8, 9, 4, 0, 5],
            .solved [0, 6, 7, 8, 2, 9],
            .solved [0, 6, 7, 8, 2, 9],
            .solved [0, 6, 7, 8, 2, 9]
          ],
          .split [
            .solved [1, 4, 5, 8, 3, 9],
            .solved [0, 6, 7, 9, 2, 8],
            .solved [1, 4, 5, 8, 3, 9]
          ],
          .split [
            .solved [0, 6, 7, 8, 2, 9],
            .solved [0, 6, 7, 8, 2, 9]
          ],
          .split [
            .split [
              .solved [4, 8, 9, 10, 5, 6]
            ]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 2],
            .solved [1, 4, 5, 9, 3, 7],
            .solved [1, 4, 5, 9, 3, 7],
            .solved [6, 7, 8, 9, 2, 4],
            .solved [6, 7, 8, 9, 2, 4]
          ],
          .solved [1, 4, 5, 8, 3, 7],
          .solved [1, 4, 5, 8, 3, 7],
          .split [
            .solved [6, 8, 9, 7, 0, 4],
            .solved [4, 7, 8, 9, 5, 6]
          ],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .split [
          .solved [1, 7, 8, 4, 0, 5],
          .solved [1, 4, 5, 7, 3, 8],
          .solved [1, 4, 5, 7, 3, 8],
          .solved [1, 4, 5, 7, 3, 8]
        ],
        .split [
          .solved [1, 4, 5, 7, 3, 8],
          .solved [1, 4, 5, 7, 3, 8],
          .solved [1, 4, 5, 7, 3, 8]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [6, 7, 8, 9, 0, 4]
          ],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 2],
          .solved [1, 4, 5, 8, 3, 6],
          .solved [1, 4, 5, 8, 3, 6],
          .split [
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .solved [1, 4, 5, 7, 3, 6],
        .solved [1, 4, 5, 7, 3, 6],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .solved [1, 6, 7, 4, 0, 5],
        .solved [1, 4, 5, 6, 3, 7],
        .solved [1, 4, 5, 6, 3, 7],
        .solved [1, 4, 5, 6, 3, 7]
      ],
      .split [
        .solved [1, 4, 5, 6, 3, 7],
        .solved [1, 4, 5, 6, 3, 7],
        .solved [1, 4, 5, 6, 3, 7]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .solved [0, 3, 5, 6, 7, 4],
        .solved [3, 5, 6, 4, 0, 7],
        .split [
          .solved [0, 1, 2, 7, 3, 8],
          .solved [0, 1, 2, 7, 3, 8],
          .solved [1, 0, 2, 7, 3, 8],
          .solved [3, 5, 6, 4, 0, 8],
          .solved [2, 0, 1, 7, 3, 8],
          .solved [3, 5, 6, 4, 0, 8],
          .solved [0, 5, 6, 3, 8, 4],
          .solved [3, 5, 6, 4, 0, 8]
        ],
        .split [
          .split [
            .solved [1, 7, 8, 2, 4, 9],
            .solved [0, 5, 6, 3, 9, 4],
            .solved [3, 5, 6, 4, 0, 9],
            .solved [0, 5, 6, 3, 9, 4],
            .solved [3, 5, 6, 4, 0, 9],
            .solved [0, 5, 6, 3, 9, 4],
            .solved [3, 5, 6, 4, 0, 9]
          ],
          .solved [0, 5, 6, 3, 8, 4],
          .solved [3, 5, 6, 4, 0, 8],
          .solved [0, 5, 6, 3, 8, 4],
          .solved [3, 5, 6, 4, 0, 8],
          .solved [0, 5, 6, 3, 8, 4],
          .solved [3, 5, 6, 4, 0, 8]
        ],
        .solved [0, 5, 6, 3, 7, 4],
        .solved [3, 5, 6, 4, 0, 7],
        .solved [0, 5, 6, 3, 7, 4],
        .solved [3, 5, 6, 4, 0, 7],
        .solved [0, 5, 6, 3, 7, 4],
        .solved [3, 5, 6, 4, 0, 7]
      ],
      .split [
        .split [
          .solved [3, 4, 5, 6, 7, 8],
          .split [
            .solved [0, 1, 2, 8, 3, 9],
            .solved [0, 1, 2, 8, 3, 9],
            .solved [1, 0, 2, 8, 3, 9],
            .solved [3, 4, 5, 6, 7, 9],
            .solved [2, 0, 1, 8, 3, 9],
            .solved [3, 4, 5, 6, 7, 9],
            .solved [3, 4, 5, 6, 7, 9],
            .solved [3, 4, 5, 6, 7, 9]
          ],
          .solved [3, 4, 6, 7, 5, 8],
          .solved [3, 5, 6, 7, 4, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [0, 1, 2, 7, 3, 8],
          .solved [0, 1, 2, 7, 3, 8],
          .solved [1, 0, 2, 7, 3, 8],
          .split [
            .solved [4, 5, 6, 8, 3, 9],
            .solved [2, 0, 1, 7, 3, 9],
            .solved [4, 5, 6, 8, 3, 9],
            .solved [4, 5, 6, 8, 3, 9],
            .solved [4, 5, 6, 8, 3, 9]
          ],
          .solved [2, 0, 1, 7, 3, 8],
          .split [
            .solved [4, 8, 9, 5, 1, 6],
            .solved [4, 5, 6, 8, 3, 9],
            .solved [4, 5, 6, 8, 3, 9]
          ],
          .split [
            .solved [4, 5, 8, 9, 6, 0],
            .solved [4, 5, 6, 8, 3, 9]
          ],
          .split [
            .solved [4, 5, 6, 8, 3, 9]
          ]
        ],
        .split [
          .solved [1, 7, 8, 4, 2, 6],
          .split [
            .solved [0, 8, 9, 5, 2, 6],
            .solved [6, 7, 9, 8, 4, 2],
            .solved [6, 5, 9, 8, 4, 0],
            .solved [6, 4, 9, 7, 5, 1],
            .solved [6, 5, 9, 8, 4, 0],
            .solved [5, 4, 6, 9, 3, 7]
          ],
          .solved [5, 4, 6, 8, 3, 7],
          .solved [6, 4, 8, 7, 5, 1],
          .solved [6, 4, 8, 7, 5, 1],
          .solved [5, 4, 6, 8, 3, 7],
          .solved [5, 4, 6, 8, 3, 7]
        ],
        .split [
          .solved [0, 7, 8, 5, 2, 6],
          .solved [4, 5, 6, 8, 3, 7],
          .solved [6, 5, 8, 7, 4, 0],
          .solved [4, 5, 6, 8, 3, 7],
          .solved [6, 5, 8, 7, 4, 0],
          .solved [4, 5, 6, 8, 3, 7]
        ],
        .split [
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [0, 7, 8, 1, 5, 4],
          .solved [4, 7, 8, 5, 1, 6],
          .solved [4, 5, 7, 8, 6, 0],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [4, 7, 8, 5, 1, 6],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [4, 5, 7, 8, 6, 0],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 3, 8]
        ]
      ],
      .split [
        .solved [0, 1, 2, 6, 3, 7],
        .solved [0, 1, 2, 6, 3, 7],
        .solved [1, 0, 2, 6, 3, 7],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 2],
            .solved [2, 0, 1, 6, 3, 9],
            .solved [6, 7, 8, 9, 2, 4],
            .solved [6, 7, 8, 9, 2, 4],
            .solved [6, 7, 8, 9, 2, 4]
          ],
          .solved [2, 0, 1, 6, 3, 8],
          .split [
            .solved [1, 8, 9, 4, 6, 5],
            .solved [4, 7, 8, 9, 5, 6],
            .solved [4, 7, 8, 9, 5, 6]
          ],
          .split [
            .solved [0, 8, 9, 5, 6, 4],
            .solved [4, 7, 8, 9, 5, 6]
          ],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .solved [2, 0, 1, 6, 3, 7],
        .split [
          .solved [1, 7, 8, 4, 6, 5],
          .split [
            .solved [0, 8, 9, 5, 6, 4],
            .solved [4, 7, 8, 9, 5, 6]
          ],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .split [
          .solved [0, 7, 8, 5, 6, 4],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ]
      ],
      .split [
        .split [
          .solved [1, 6, 7, 2, 4, 8],
          .solved [1, 6, 7, 2, 4, 8],
          .solved [1, 6, 7, 2, 4, 8],
          .solved [1, 6, 7, 4, 2, 8],
          .solved [1, 6, 7, 4, 2, 8],
          .solved [1, 6, 7, 4, 2, 8],
          .solved [1, 6, 7, 4, 2, 8]
        ],
        .split [
          .solved [0, 7, 8, 2, 5, 6],
          .split [
            .solved [4, 8, 9, 6, 5, 2],
            .solved [7, 5, 9, 8, 0, 4],
            .solved [6, 4, 9, 8, 1, 5],
            .solved [7, 5, 9, 8, 0, 4],
            .solved [7, 6, 8, 9, 2, 4]
          ],
          .split [
            .solved [0, 8, 9, 1, 5, 4],
            .solved [7, 5, 8, 9, 0, 4],
            .solved [4, 8, 9, 5, 6, 0],
            .solved [7, 5, 8, 9, 0, 4]
          ],
          .split [
            .solved [1, 4, 8, 9, 6, 5],
            .solved [7, 5, 9, 8, 0, 4],
            .solved [6, 4, 8, 9, 1, 5]
          ],
          .split [
            .solved [4, 8, 9, 5, 6, 0],
            .solved [7, 5, 8, 9, 0, 4]
          ],
          .split [
            .solved [4, 8, 9, 5, 6, 7]
          ]
        ],
        .split [
          .solved [4, 7, 8, 6, 5, 2],
          .solved [6, 4, 8, 7, 1, 5],
          .solved [6, 4, 8, 7, 1, 5],
          .split [
            .solved [4, 8, 9, 5, 6, 0],
            .solved [4, 7, 8, 5, 6, 9]
          ],
          .split [
            .solved [4, 7, 8, 5, 6, 9]
          ]
        ],
        .split [
          .solved [0, 7, 8, 1, 5, 4],
          .solved [1, 4, 7, 8, 6, 5],
          .solved [4, 7, 8, 5, 6, 0],
          .solved [6, 4, 7, 8, 1, 5]
        ],
        .split [
          .solved [1, 4, 7, 8, 6, 5],
          .solved [6, 4, 7, 8, 1, 5],
          .solved [6, 4, 7, 8, 1, 5]
        ],
        .split [
          .solved [4, 7, 8, 5, 6, 0],
          .split [
            .solved [4, 7, 8, 5, 6, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 5, 6, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 6, 7, 2, 5, 8],
          .solved [0, 6, 7, 2, 5, 8],
          .solved [0, 6, 7, 5, 2, 8],
          .solved [0, 6, 7, 5, 2, 8],
          .solved [0, 6, 7, 5, 2, 8],
          .solved [0, 6, 7, 5, 2, 8]
        ],
        .split [
          .solved [5, 7, 8, 6, 4, 2],
          .solved [6, 5, 8, 7, 0, 4],
          .split [
            .solved [4, 8, 9, 5, 1, 6],
            .solved [6, 5, 9, 7, 0, 4],
            .solved [4, 5, 7, 8, 9, 6]
          ],
          .solved [6, 5, 8, 7, 0, 4],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .solved [0, 7, 8, 1, 5, 4],
          .solved [6, 5, 7, 8, 0, 4],
          .solved [0, 5, 7, 8, 6, 4],
          .solved [6, 5, 7, 8, 0, 4]
        ],
        .split [
          .solved [4, 7, 8, 5, 1, 6],
          .solved [6, 5, 8, 7, 0, 4],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .solved [0, 5, 7, 8, 6, 4],
          .solved [6, 5, 7, 8, 0, 4]
        ],
        .split [
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 2],
          .split [
            .solved [0, 8, 9, 1, 5, 4],
            .solved [4, 8, 9, 5, 1, 6],
            .solved [4, 5, 8, 9, 6, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 8, 9, 5, 1, 6],
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 8, 9, 6, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [0, 7, 8, 1, 5, 4],
          .solved [4, 7, 8, 5, 1, 6],
          .solved [4, 5, 7, 8, 6, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [4, 7, 8, 5, 1, 6],
          .split [
            .solved [4, 5, 8, 9, 6, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [4, 5, 7, 8, 6, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .solved [0, 6, 7, 1, 5, 4],
        .split [
          .solved [1, 4, 6, 7, 8, 5],
          .solved [4, 5, 6, 8, 7, 0],
          .solved [4, 6, 7, 5, 1, 8]
        ],
        .split [
          .solved [0, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 0]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [1, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 1, 8],
          .solved [4, 6, 7, 5, 1, 8]
        ],
        .split [
          .solved [4, 5, 7, 8, 6, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 0]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [3, 4, 5, 6, 7, 8],
          .split [
            .solved [0, 1, 2, 8, 3, 9],
            .solved [0, 1, 2, 8, 3, 9],
            .solved [1, 0, 2, 8, 3, 9],
            .solved [3, 4, 5, 6, 7, 9],
            .solved [2, 0, 1, 8, 3, 9],
            .solved [3, 4, 5, 6, 7, 9],
            .solved [3, 4, 5, 6, 7, 9],
            .solved [3, 4, 5, 6, 7, 9]
          ],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 5, 6, 7, 4, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [0, 1, 2, 7, 3, 8],
          .solved [0, 1, 2, 7, 3, 8],
          .solved [1, 0, 2, 7, 3, 8],
          .split [
            .solved [4, 5, 6, 8, 3, 9],
            .solved [2, 0, 1, 7, 3, 9],
            .solved [4, 5, 6, 8, 3, 9],
            .solved [4, 5, 6, 8, 3, 9],
            .solved [4, 5, 6, 8, 3, 9]
          ],
          .solved [2, 0, 1, 7, 3, 8],
          .split [
            .solved [4, 8, 9, 5, 1, 6],
            .solved [4, 5, 6, 8, 3, 9],
            .solved [4, 5, 6, 8, 3, 9]
          ],
          .split [
            .solved [4, 5, 6, 8, 3, 9],
            .solved [4, 5, 6, 8, 3, 9]
          ],
          .split [
            .solved [4, 5, 6, 8, 3, 9]
          ]
        ],
        .split [
          .solved [1, 7, 8, 4, 2, 5],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 7, 8, 5, 1, 6],
          .solved [4, 7, 8, 5, 1, 6],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .split [
            .solved [0, 7, 8, 9, 2, 5],
            .solved [2, 7, 8, 9, 0, 5],
            .solved [0, 7, 8, 9, 2, 5],
            .solved [4, 5, 6, 9, 3, 7],
            .solved [0, 7, 8, 9, 2, 5],
            .solved [4, 5, 6, 9, 3, 7]
          ],
          .solved [4, 5, 6, 8, 3, 7],
          .solved [4, 5, 6, 8, 3, 7],
          .solved [4, 5, 6, 8, 3, 7],
          .solved [4, 5, 6, 8, 3, 7],
          .solved [4, 5, 6, 8, 3, 7]
        ],
        .split [
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [1, 7, 8, 4, 0, 5],
          .solved [4, 7, 8, 5, 1, 6],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [4, 7, 8, 5, 1, 6],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 3, 8]
        ]
      ],
      .split [
        .solved [0, 1, 2, 6, 3, 7],
        .solved [0, 1, 2, 6, 3, 7],
        .solved [1, 0, 2, 6, 3, 7],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 2],
            .solved [2, 0, 1, 6, 3, 9],
            .solved [6, 7, 8, 9, 2, 4],
            .solved [6, 7, 8, 9, 2, 4],
            .solved [6, 7, 8, 9, 2, 4]
          ],
          .solved [2, 0, 1, 6, 3, 8],
          .split [
            .solved [1, 8, 9, 4, 6, 5],
            .solved [4, 7, 8, 9, 5, 6],
            .solved [4, 7, 8, 9, 5, 6]
          ],
          .split [
            .solved [6, 8, 9, 7, 0, 4],
            .solved [4, 7, 8, 9, 5, 6]
          ],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .solved [2, 0, 1, 6, 3, 7],
        .split [
          .solved [1, 7, 8, 4, 6, 5],
          .split [
            .solved [6, 8, 9, 7, 0, 4],
            .solved [4, 7, 8, 9, 5, 6]
          ],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [6, 7, 8, 9, 0, 4]
          ],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ]
      ],
      .split [
        .solved [1, 6, 7, 4, 2, 5],
        .split [
          .solved [2, 7, 8, 6, 0, 5],
          .solved [5, 6, 8, 7, 4, 2],
          .solved [4, 6, 8, 5, 1, 7],
          .solved [4, 6, 8, 5, 1, 7],
          .split [
            .solved [5, 8, 9, 7, 4, 0],
            .solved [4, 5, 6, 8, 9, 7]
          ],
          .split [
            .solved [4, 5, 6, 8, 9, 7]
          ]
        ],
        .split [
          .solved [4, 6, 7, 8, 5, 2],
          .solved [4, 6, 8, 5, 1, 7],
          .solved [4, 6, 8, 5, 1, 7],
          .split [
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [1, 7, 8, 4, 0, 5],
          .solved [1, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 1, 8],
          .solved [4, 6, 7, 5, 1, 8]
        ],
        .split [
          .solved [1, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 1, 8],
          .solved [4, 6, 7, 5, 1, 8]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 6, 7, 8, 2, 5],
          .solved [2, 6, 7, 8, 0, 5],
          .solved [0, 6, 7, 8, 2, 5],
          .split [
            .solved [4, 8, 9, 5, 1, 6],
            .solved [0, 6, 7, 9, 2, 5],
            .solved [5, 8, 9, 6, 4, 7]
          ],
          .solved [0, 6, 7, 8, 2, 5],
          .split [
            .solved [5, 8, 9, 6, 4, 7]
          ]
        ],
        .split [
          .solved [5, 7, 8, 6, 4, 2],
          .split [
            .solved [1, 8, 9, 4, 0, 5],
            .solved [4, 8, 9, 5, 1, 6],
            .solved [5, 8, 9, 6, 4, 0],
            .solved [4, 5, 7, 8, 9, 6]
          ],
          .split [
            .solved [4, 8, 9, 5, 1, 6],
            .solved [4, 5, 7, 8, 9, 6],
            .solved [4, 5, 7, 8, 9, 6]
          ],
          .split [
            .solved [5, 8, 9, 6, 4, 0],
            .solved [4, 5, 7, 8, 9, 6]
          ],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .solved [1, 7, 8, 4, 0, 5],
          .solved [4, 7, 8, 5, 1, 6],
          .solved [5, 7, 8, 6, 4, 0],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .solved [4, 7, 8, 5, 1, 6],
          .split [
            .solved [5, 8, 9, 6, 4, 0],
            .solved [4, 5, 7, 8, 9, 6]
          ],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .solved [5, 7, 8, 6, 4, 0],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 2],
          .split [
            .solved [1, 8, 9, 4, 0, 5],
            .solved [4, 8, 9, 5, 1, 6],
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 8, 9, 5, 1, 6],
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [1, 7, 8, 4, 0, 5],
          .solved [4, 7, 8, 5, 1, 6],
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [4, 7, 8, 5, 1, 6],
          .split [
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .solved [1, 6, 7, 4, 0, 5],
        .split [
          .solved [1, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 1, 8],
          .solved [4, 6, 7, 5, 1, 8]
        ],
        .split [
          .solved [4, 6, 7, 8, 5, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [1, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 1, 8],
          .solved [4, 6, 7, 5, 1, 8]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .solved [0, 1, 2, 5, 3, 6],
      .solved [0, 1, 2, 5, 3, 6],
      .solved [1, 0, 2, 5, 3, 6],
      .split [
        .split [
          .solved [2, 6, 7, 8, 5, 4],
          .solved [2, 0, 1, 5, 3, 8],
          .solved [5, 6, 7, 8, 2, 4],
          .solved [5, 6, 7, 8, 2, 4],
          .solved [5, 6, 7, 8, 2, 4]
        ],
        .solved [2, 0, 1, 5, 3, 7],
        .split [
          .solved [1, 7, 8, 4, 5, 6],
          .split [
            .solved [5, 8, 9, 6, 0, 4],
            .solved [4, 6, 7, 8, 9, 5]
          ],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .solved [5, 7, 8, 6, 0, 4],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .solved [2, 0, 1, 5, 3, 6],
      .split [
        .split [
          .solved [1, 6, 7, 4, 5, 8],
          .solved [1, 6, 7, 4, 5, 8],
          .solved [1, 6, 7, 4, 5, 8]
        ],
        .split [
          .solved [5, 7, 8, 6, 0, 4],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 6, 7, 8, 5, 4],
          .solved [5, 6, 7, 8, 0, 4]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .solved [1, 5, 6, 2, 4, 7],
        .solved [1, 5, 6, 2, 4, 7],
        .solved [1, 5, 6, 2, 4, 7],
        .solved [1, 5, 6, 4, 2, 7],
        .solved [1, 5, 6, 4, 2, 7],
        .solved [1, 5, 6, 4, 2, 7],
        .solved [1, 5, 6, 4, 2, 7]
      ],
      .split [
        .split [
          .solved [0, 2, 6, 7, 8, 5],
          .solved [2, 6, 7, 5, 0, 8],
          .solved [0, 6, 7, 2, 8, 5],
          .solved [2, 6, 7, 5, 0, 8],
          .solved [0, 6, 7, 2, 8, 5],
          .solved [2, 6, 7, 5, 0, 8]
        ],
        .split [
          .solved [2, 5, 7, 8, 6, 4],
          .solved [4, 5, 8, 7, 1, 6],
          .solved [4, 5, 8, 7, 1, 6],
          .solved [6, 5, 7, 8, 2, 4],
          .solved [6, 5, 7, 8, 2, 4]
        ],
        .split [
          .solved [1, 7, 8, 4, 0, 5],
          .solved [1, 5, 7, 8, 4, 6],
          .solved [5, 7, 8, 6, 4, 0],
          .solved [4, 5, 7, 8, 1, 6]
        ],
        .split [
          .solved [1, 5, 7, 8, 4, 6],
          .solved [4, 5, 7, 8, 1, 6],
          .solved [4, 5, 7, 8, 1, 6]
        ],
        .split [
          .solved [5, 7, 8, 6, 4, 0],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ]
      ],
      .split [
        .split [
          .solved [2, 5, 6, 7, 8, 4],
          .solved [4, 5, 8, 6, 1, 7],
          .solved [4, 5, 8, 6, 1, 7],
          .solved [4, 5, 6, 7, 8, 2],
          .solved [4, 5, 6, 7, 8, 2]
        ],
        .split [
          .solved [1, 7, 8, 4, 0, 5],
          .solved [1, 4, 5, 7, 8, 6],
          .solved [4, 5, 7, 6, 1, 8],
          .solved [4, 5, 7, 6, 1, 8]
        ],
        .split [
          .solved [1, 4, 5, 7, 8, 6],
          .solved [4, 5, 7, 6, 1, 8],
          .solved [4, 5, 7, 6, 1, 8]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .solved [1, 6, 7, 4, 0, 5],
        .split [
          .solved [1, 4, 5, 6, 7, 8],
          .solved [1, 4, 5, 6, 7, 8],
          .solved [1, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [4, 6, 7, 8, 5, 0],
          .solved [4, 5, 6, 7, 1, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 1, 8]
        ]
      ],
      .split [
        .split [
          .solved [1, 4, 5, 6, 7, 8],
          .solved [1, 4, 5, 6, 7, 8],
          .solved [1, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 1, 8],
          .solved [4, 5, 6, 7, 1, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 1, 8]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [0, 2, 5, 6, 7, 8],
          .solved [0, 2, 5, 6, 7, 8],
          .solved [0, 5, 6, 2, 8, 7],
          .solved [0, 5, 6, 7, 2, 8],
          .solved [0, 5, 6, 2, 8, 7],
          .solved [0, 5, 6, 7, 2, 8]
        ],
        .split [
          .solved [2, 5, 6, 7, 0, 8],
          .solved [0, 5, 6, 2, 8, 7],
          .solved [2, 5, 6, 7, 0, 8],
          .solved [0, 5, 6, 2, 8, 7],
          .solved [2, 5, 6, 7, 0, 8]
        ],
        .split [
          .solved [0, 7, 8, 1, 5, 4],
          .solved [0, 5, 6, 7, 2, 8],
          .solved [0, 5, 6, 7, 2, 8],
          .solved [0, 5, 6, 7, 2, 8]
        ],
        .split [
          .split [
            .solved [1, 7, 8, 9, 4, 5],
            .solved [0, 5, 6, 9, 2, 7],
            .solved [4, 7, 8, 9, 1, 5]
          ],
          .solved [0, 5, 6, 8, 2, 7],
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ],
        .split [
          .solved [0, 5, 6, 7, 2, 8],
          .solved [0, 5, 6, 7, 2, 8]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ]
      ],
      .split [
        .split [
          .solved [2, 6, 7, 8, 5, 4],
          .solved [5, 6, 7, 8, 2, 4],
          .solved [5, 6, 7, 8, 2, 4],
          .solved [5, 6, 7, 8, 2, 4],
          .solved [5, 6, 7, 8, 2, 4]
        ],
        .split [
          .solved [0, 7, 8, 1, 5, 4],
          .solved [4, 7, 8, 6, 1, 5],
          .solved [5, 7, 8, 6, 0, 4],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .solved [4, 7, 8, 6, 1, 5],
          .split [
            .solved [5, 8, 9, 6, 0, 4],
            .solved [4, 6, 7, 8, 9, 5]
          ],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .solved [5, 7, 8, 6, 0, 4],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .solved [0, 6, 7, 1, 5, 4],
        .split [
          .solved [1, 6, 7, 8, 4, 5],
          .solved [5, 6, 8, 7, 0, 4],
          .solved [4, 6, 7, 8, 1, 5]
        ],
        .split [
          .solved [0, 6, 7, 8, 5, 4],
          .solved [5, 6, 7, 8, 0, 4]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .solved [1, 6, 7, 8, 4, 5],
          .solved [4, 6, 7, 8, 1, 5],
          .solved [4, 6, 7, 8, 1, 5]
        ],
        .split [
          .solved [5, 7, 8, 6, 0, 4],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 6, 7, 8, 5, 4],
          .solved [5, 6, 7, 8, 0, 4]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [2, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 2],
          .solved [4, 5, 6, 7, 8, 2],
          .solved [4, 5, 6, 7, 8, 2],
          .solved [4, 5, 6, 7, 8, 2]
        ],
        .split [
          .solved [1, 7, 8, 4, 0, 5],
          .solved [4, 7, 8, 5, 1, 6],
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [4, 7, 8, 5, 1, 6],
          .split [
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .solved [1, 6, 7, 4, 0, 5],
        .split [
          .solved [1, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 1, 8],
          .solved [4, 6, 7, 5, 1, 8]
        ],
        .split [
          .solved [4, 6, 7, 8, 5, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [1, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 1, 8],
          .solved [4, 6, 7, 5, 1, 8]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .solved [0, 1, 5, 6, 7, 4],
        .solved [1, 5, 6, 4, 0, 7],
        .solved [0, 5, 6, 1, 7, 4],
        .solved [1, 5, 6, 4, 0, 7]
      ],
      .split [
        .split [
          .solved [1, 4, 5, 6, 7, 8],
          .solved [1, 4, 5, 6, 7, 8],
          .solved [1, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [4, 5, 7, 8, 6, 0],
          .solved [4, 5, 6, 7, 1, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 1, 8]
        ]
      ],
      .split [
        .split [
          .solved [0, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 0]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [1, 4, 5, 6, 7, 8],
          .solved [1, 4, 5, 6, 7, 8],
          .solved [1, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 1, 8],
          .solved [4, 5, 6, 7, 1, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 1, 8]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [0, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 0]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ]
  ]

private def tree6a6 : WitnessTree :=
  .split [
    .split [
      .split [
        .solved [0, 3, 4, 5, 6, 7],
        .solved [0, 3, 4, 5, 6, 7],
        .split [
          .solved [0, 1, 2, 7, 3, 8],
          .solved [0, 1, 2, 7, 3, 8],
          .solved [1, 0, 2, 7, 3, 8],
          .solved [0, 4, 5, 6, 3, 8],
          .solved [2, 0, 1, 7, 3, 8],
          .solved [0, 4, 5, 6, 3, 8],
          .solved [0, 4, 5, 3, 8, 6],
          .solved [0, 4, 5, 6, 3, 8]
        ],
        .split [
          .split [
            .split [
              .solved [1, 2, 7, 8, 9, 10],
              .solved [0, 4, 5, 3, 10, 6],
              .solved [0, 4, 5, 6, 3, 10],
              .solved [0, 4, 5, 3, 10, 6],
              .solved [0, 4, 5, 6, 3, 10],
              .solved [0, 4, 5, 3, 10, 6],
              .solved [0, 4, 5, 6, 3, 10]
            ],
            .solved [0, 4, 5, 3, 9, 6],
            .solved [0, 4, 5, 6, 3, 9],
            .solved [0, 4, 5, 3, 9, 6],
            .solved [0, 4, 5, 6, 3, 9],
            .solved [0, 4, 5, 3, 9, 6],
            .solved [0, 4, 5, 6, 3, 9]
          ],
          .solved [0, 4, 5, 3, 8, 6],
          .solved [0, 4, 5, 6, 3, 8],
          .solved [0, 4, 5, 3, 8, 6],
          .solved [0, 4, 5, 6, 3, 8],
          .solved [0, 4, 5, 3, 8, 6],
          .solved [0, 4, 5, 6, 3, 8]
        ],
        .solved [0, 4, 5, 3, 7, 6],
        .solved [0, 4, 5, 6, 3, 7],
        .solved [0, 4, 5, 3, 7, 6],
        .solved [0, 4, 5, 6, 3, 7],
        .solved [0, 4, 5, 3, 7, 6],
        .solved [0, 4, 5, 6, 3, 7]
      ],
      .split [
        .solved [3, 4, 5, 6, 0, 7],
        .split [
          .solved [0, 1, 2, 7, 3, 8],
          .solved [0, 1, 2, 7, 3, 8],
          .solved [1, 0, 2, 7, 3, 8],
          .solved [3, 4, 5, 6, 0, 8],
          .solved [2, 0, 1, 7, 3, 8],
          .solved [3, 4, 5, 6, 0, 8],
          .solved [0, 4, 5, 3, 8, 6],
          .solved [3, 4, 5, 6, 0, 8]
        ],
        .split [
          .split [
            .solved [1, 7, 8, 9, 2, 6],
            .solved [0, 4, 5, 3, 9, 6],
            .solved [3, 4, 5, 6, 0, 9],
            .solved [0, 4, 5, 3, 9, 6],
            .solved [3, 4, 5, 6, 0, 9],
            .solved [0, 4, 5, 3, 9, 6],
            .solved [3, 4, 5, 6, 0, 9]
          ],
          .solved [0, 4, 5, 3, 8, 6],
          .solved [3, 4, 5, 6, 0, 8],
          .solved [0, 4, 5, 3, 8, 6],
          .solved [3, 4, 5, 6, 0, 8],
          .solved [0, 4, 5, 3, 8, 6],
          .solved [3, 4, 5, 6, 0, 8]
        ],
        .solved [0, 4, 5, 3, 7, 6],
        .solved [3, 4, 5, 6, 0, 7],
        .solved [0, 4, 5, 3, 7, 6],
        .solved [3, 4, 5, 6, 0, 7],
        .solved [0, 4, 5, 3, 7, 6],
        .solved [3, 4, 5, 6, 0, 7]
      ],
      .split [
        .solved [0, 1, 2, 6, 3, 7],
        .solved [0, 1, 2, 6, 3, 7],
        .solved [1, 0, 2, 6, 3, 7],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 2],
            .solved [2, 0, 1, 6, 3, 9],
            .solved [6, 7, 8, 9, 2, 4],
            .solved [0, 4, 5, 9, 3, 7],
            .solved [6, 7, 8, 9, 2, 4]
          ],
          .solved [2, 0, 1, 6, 3, 8],
          .split [
            .solved [6, 8, 9, 7, 1, 4],
            .solved [0, 4, 5, 9, 3, 7],
            .solved [4, 7, 8, 9, 5, 6]
          ],
          .solved [0, 4, 5, 8, 3, 7],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .solved [2, 0, 1, 6, 3, 7],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 1],
            .solved [0, 4, 5, 9, 3, 7],
            .solved [6, 7, 8, 9, 1, 4]
          ],
          .solved [0, 4, 5, 8, 3, 7],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .split [
          .solved [0, 4, 5, 7, 3, 8],
          .solved [0, 4, 5, 7, 3, 8]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [1, 2, 6, 7, 8, 9],
            .solved [1, 2, 6, 7, 8, 9],
            .solved [1, 2, 6, 7, 8, 9],
            .solved [1, 6, 7, 2, 9, 8],
            .solved [1, 6, 7, 2, 9, 8],
            .solved [1, 6, 7, 8, 2, 9],
            .solved [1, 6, 7, 8, 2, 9]
          ],
          .split [
            .solved [0, 8, 9, 4, 2, 5],
            .solved [0, 4, 5, 8, 3, 9],
            .solved [0, 4, 5, 8, 3, 9],
            .solved [0, 4, 5, 8, 3, 9],
            .solved [0, 4, 5, 8, 3, 9],
            .solved [0, 4, 5, 8, 3, 9]
          ],
          .split [
            .solved [2, 6, 7, 8, 1, 9],
            .solved [0, 4, 5, 9, 3, 8],
            .solved [1, 6, 7, 2, 9, 8],
            .solved [0, 4, 5, 9, 3, 8],
            .solved [2, 6, 7, 8, 1, 9]
          ],
          .split [
            .solved [0, 8, 9, 4, 1, 5],
            .solved [0, 4, 5, 8, 3, 9],
            .solved [0, 4, 5, 8, 3, 9],
            .solved [0, 4, 5, 8, 3, 9]
          ],
          .split [
            .solved [1, 6, 7, 8, 2, 9],
            .solved [0, 4, 5, 9, 3, 8],
            .solved [1, 6, 7, 8, 2, 9]
          ],
          .split [
            .solved [0, 4, 5, 8, 3, 9],
            .solved [0, 4, 5, 8, 3, 9]
          ],
          .split [
            .split [
              .solved [4, 8, 9, 10, 5, 6]
            ]
          ]
        ],
        .split [
          .solved [0, 7, 8, 4, 2, 5],
          .solved [0, 4, 5, 7, 3, 8],
          .solved [0, 4, 5, 7, 3, 8],
          .solved [0, 4, 5, 7, 3, 8],
          .solved [0, 4, 5, 7, 3, 8],
          .solved [0, 4, 5, 7, 3, 8]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 2],
            .solved [0, 4, 5, 9, 3, 7],
            .solved [6, 7, 8, 9, 2, 4],
            .solved [0, 4, 5, 9, 3, 7],
            .solved [6, 7, 8, 9, 2, 4]
          ],
          .solved [0, 4, 5, 8, 3, 7],
          .split [
            .solved [6, 8, 9, 7, 1, 4],
            .solved [0, 4, 5, 9, 3, 7],
            .solved [4, 7, 8, 9, 5, 6]
          ],
          .solved [0, 4, 5, 8, 3, 7],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .split [
          .solved [0, 7, 8, 4, 1, 5],
          .solved [0, 4, 5, 7, 3, 8],
          .solved [0, 4, 5, 7, 3, 8],
          .solved [0, 4, 5, 7, 3, 8]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 1],
            .solved [0, 4, 5, 9, 3, 7],
            .solved [6, 7, 8, 9, 1, 4]
          ],
          .solved [0, 4, 5, 8, 3, 7],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .split [
          .solved [0, 4, 5, 7, 3, 8],
          .solved [0, 4, 5, 7, 3, 8]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ]
      ],
      .split [
        .solved [0, 6, 7, 4, 2, 5],
        .solved [0, 4, 5, 6, 3, 7],
        .solved [0, 4, 5, 6, 3, 7],
        .solved [0, 4, 5, 6, 3, 7],
        .solved [0, 4, 5, 6, 3, 7],
        .solved [0, 4, 5, 6, 3, 7]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 2],
          .solved [0, 4, 5, 8, 3, 6],
          .split [
            .solved [4, 5, 6, 7, 8, 9],
            .solved [0, 4, 5, 9, 3, 6],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .solved [0, 4, 5, 8, 3, 6],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .solved [0, 4, 5, 7, 3, 6],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 1],
            .solved [0, 4, 5, 9, 3, 6],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .solved [0, 4, 5, 8, 3, 6],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .solved [0, 4, 5, 7, 3, 6],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .solved [0, 6, 7, 4, 1, 5],
        .solved [0, 4, 5, 6, 3, 7],
        .solved [0, 4, 5, 6, 3, 7],
        .solved [0, 4, 5, 6, 3, 7]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 1],
          .solved [0, 4, 5, 8, 3, 6],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .solved [0, 4, 5, 7, 3, 6],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .solved [0, 4, 5, 6, 3, 7],
        .solved [0, 4, 5, 6, 3, 7]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [3, 4, 5, 6, 7, 8],
          .split [
            .solved [0, 1, 2, 8, 3, 9],
            .solved [0, 1, 2, 8, 3, 9],
            .solved [1, 0, 2, 8, 3, 9],
            .solved [3, 4, 5, 6, 7, 9],
            .solved [2, 0, 1, 8, 3, 9],
            .solved [3, 4, 5, 6, 7, 9],
            .solved [3, 4, 5, 6, 7, 9],
            .solved [3, 4, 5, 6, 7, 9]
          ],
          .solved [3, 5, 6, 7, 4, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [0, 1, 2, 7, 3, 8],
          .solved [0, 1, 2, 7, 3, 8],
          .solved [1, 0, 2, 7, 3, 8],
          .split [
            .solved [4, 5, 6, 8, 3, 9],
            .solved [2, 0, 1, 7, 3, 9],
            .solved [4, 5, 6, 8, 3, 9],
            .solved [4, 5, 6, 8, 3, 9],
            .solved [4, 5, 6, 8, 3, 9]
          ],
          .solved [2, 0, 1, 7, 3, 8],
          .split [
            .solved [4, 5, 6, 8, 3, 9],
            .solved [4, 5, 6, 8, 3, 9],
            .solved [4, 5, 6, 8, 3, 9]
          ],
          .split [
            .solved [4, 8, 9, 5, 0, 6],
            .solved [4, 5, 6, 8, 3, 9]
          ],
          .split [
            .solved [4, 5, 6, 8, 3, 9]
          ]
        ],
        .split [
          .split [
            .solved [1, 7, 8, 9, 2, 5],
            .solved [2, 7, 8, 9, 1, 5],
            .solved [2, 7, 8, 9, 1, 5],
            .solved [1, 7, 8, 9, 2, 5],
            .solved [1, 7, 8, 9, 2, 5],
            .solved [4, 5, 6, 9, 3, 7],
            .solved [4, 5, 6, 9, 3, 7]
          ],
          .solved [4, 5, 6, 8, 3, 7],
          .solved [4, 5, 6, 8, 3, 7],
          .solved [4, 5, 6, 8, 3, 7],
          .solved [4, 5, 6, 8, 3, 7],
          .solved [4, 5, 6, 8, 3, 7],
          .solved [4, 5, 6, 8, 3, 7]
        ],
        .split [
          .solved [0, 7, 8, 4, 2, 5],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 7, 8, 5, 0, 6],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 7, 8, 5, 0, 6],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [0, 7, 8, 4, 1, 5],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 7, 8, 5, 0, 6],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [4, 7, 8, 5, 0, 6],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 3, 8]
        ]
      ],
      .split [
        .solved [0, 1, 2, 6, 3, 7],
        .solved [0, 1, 2, 6, 3, 7],
        .solved [1, 0, 2, 6, 3, 7],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 2],
            .solved [2, 0, 1, 6, 3, 9],
            .solved [6, 7, 8, 9, 2, 4],
            .solved [6, 7, 8, 9, 2, 4],
            .solved [6, 7, 8, 9, 2, 4]
          ],
          .solved [2, 0, 1, 6, 3, 8],
          .split [
            .solved [6, 8, 9, 7, 1, 4],
            .solved [4, 7, 8, 9, 5, 6],
            .solved [4, 7, 8, 9, 5, 6]
          ],
          .split [
            .solved [0, 8, 9, 4, 6, 5],
            .solved [4, 7, 8, 9, 5, 6]
          ],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .solved [2, 0, 1, 6, 3, 7],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 1],
            .solved [6, 7, 8, 9, 1, 4],
            .solved [6, 7, 8, 9, 1, 4]
          ],
          .split [
            .solved [0, 8, 9, 4, 6, 5],
            .solved [4, 7, 8, 9, 5, 6]
          ],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .split [
          .solved [0, 7, 8, 4, 6, 5],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ]
      ],
      .split [
        .split [
          .solved [1, 6, 7, 8, 2, 5],
          .solved [2, 6, 7, 8, 1, 5],
          .solved [2, 6, 7, 8, 1, 5],
          .solved [1, 6, 7, 8, 2, 5],
          .solved [1, 6, 7, 8, 2, 5],
          .split [
            .solved [4, 8, 9, 5, 0, 6],
            .solved [5, 8, 9, 6, 4, 7]
          ],
          .split [
            .solved [5, 8, 9, 6, 4, 7]
          ]
        ],
        .split [
          .solved [0, 7, 8, 4, 2, 5],
          .solved [5, 7, 8, 6, 4, 2],
          .solved [4, 7, 8, 5, 0, 6],
          .split [
            .solved [5, 8, 9, 6, 4, 1],
            .solved [4, 7, 9, 5, 0, 6],
            .solved [4, 5, 7, 8, 9, 6]
          ],
          .solved [4, 7, 8, 5, 0, 6],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .solved [5, 7, 8, 6, 4, 2],
          .split [
            .solved [0, 8, 9, 4, 1, 5],
            .solved [5, 8, 9, 6, 4, 1],
            .solved [4, 8, 9, 5, 0, 6],
            .solved [4, 5, 7, 8, 9, 6]
          ],
          .split [
            .solved [5, 8, 9, 6, 4, 1],
            .solved [4, 5, 7, 8, 9, 6],
            .solved [4, 5, 7, 8, 9, 6]
          ],
          .split [
            .solved [4, 8, 9, 5, 0, 6],
            .solved [4, 5, 7, 8, 9, 6]
          ],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .solved [0, 7, 8, 4, 1, 5],
          .solved [5, 7, 8, 6, 4, 1],
          .solved [4, 7, 8, 5, 0, 6],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .solved [5, 7, 8, 6, 4, 1],
          .split [
            .solved [4, 8, 9, 5, 0, 6],
            .solved [4, 5, 7, 8, 9, 6]
          ],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .solved [4, 7, 8, 5, 0, 6],
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 7, 8, 9, 6]
          ]
        ]
      ],
      .split [
        .solved [0, 6, 7, 4, 2, 5],
        .split [
          .solved [4, 6, 7, 8, 5, 2],
          .solved [4, 6, 8, 5, 0, 7],
          .split [
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 6, 9, 5, 0, 7],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .solved [4, 6, 8, 5, 0, 7],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [0, 7, 8, 4, 1, 5],
          .solved [4, 6, 7, 5, 0, 8],
          .solved [0, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 0, 8]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 1],
            .solved [4, 6, 9, 5, 0, 7],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .solved [4, 6, 8, 5, 0, 7],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [0, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 0, 8]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 2],
          .split [
            .solved [0, 8, 9, 4, 1, 5],
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 8, 9, 5, 0, 6],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 8, 9, 5, 0, 6],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [0, 7, 8, 4, 1, 5],
          .split [
            .solved [4, 7, 8, 9, 5, 1],
            .solved [4, 7, 9, 5, 0, 6],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .solved [4, 7, 8, 5, 0, 6],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 1],
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 8, 9, 5, 0, 6],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [4, 7, 8, 5, 0, 6],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .solved [0, 6, 7, 4, 1, 5],
        .split [
          .solved [4, 6, 7, 8, 5, 1],
          .solved [4, 6, 8, 5, 0, 7],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [0, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 0, 8]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 1],
          .split [
            .solved [4, 8, 9, 5, 0, 6],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [4, 7, 8, 5, 0, 6],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 0, 8]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .solved [0, 1, 2, 5, 3, 6],
      .solved [0, 1, 2, 5, 3, 6],
      .solved [1, 0, 2, 5, 3, 6],
      .split [
        .split [
          .solved [2, 6, 7, 8, 5, 4],
          .solved [2, 0, 1, 5, 3, 8],
          .solved [5, 6, 7, 8, 2, 4],
          .solved [5, 6, 7, 8, 2, 4],
          .solved [5, 6, 7, 8, 2, 4]
        ],
        .solved [2, 0, 1, 5, 3, 7],
        .split [
          .solved [5, 7, 8, 6, 1, 4],
          .split [
            .solved [0, 8, 9, 4, 5, 6],
            .solved [4, 6, 7, 8, 9, 5]
          ],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .solved [0, 7, 8, 4, 5, 6],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .solved [2, 0, 1, 5, 3, 6],
      .split [
        .split [
          .solved [1, 6, 7, 8, 5, 4],
          .solved [5, 6, 7, 8, 1, 4],
          .solved [5, 6, 7, 8, 1, 4]
        ],
        .split [
          .solved [0, 7, 8, 4, 5, 6],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 6, 7, 4, 5, 8],
          .solved [0, 6, 7, 4, 5, 8]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [1, 2, 5, 6, 7, 8],
          .solved [1, 2, 5, 6, 7, 8],
          .solved [1, 2, 5, 6, 7, 8],
          .solved [1, 5, 6, 2, 8, 7],
          .solved [1, 5, 6, 2, 8, 7],
          .solved [1, 5, 6, 7, 2, 8],
          .solved [1, 5, 6, 7, 2, 8]
        ],
        .split [
          .solved [0, 7, 8, 2, 4, 5],
          .solved [2, 5, 6, 7, 1, 8],
          .solved [1, 5, 6, 2, 8, 7],
          .solved [1, 5, 6, 2, 8, 7],
          .solved [2, 5, 6, 7, 1, 8],
          .solved [2, 5, 6, 7, 1, 8]
        ],
        .split [
          .solved [2, 5, 6, 7, 1, 8],
          .solved [1, 5, 6, 2, 8, 7],
          .solved [1, 5, 6, 2, 8, 7],
          .solved [2, 5, 6, 7, 1, 8],
          .solved [2, 5, 6, 7, 1, 8]
        ],
        .split [
          .solved [0, 7, 8, 1, 4, 5],
          .solved [1, 5, 6, 7, 2, 8],
          .solved [1, 5, 6, 7, 2, 8],
          .solved [1, 5, 6, 7, 2, 8]
        ],
        .split [
          .solved [1, 5, 6, 7, 2, 8],
          .solved [1, 5, 6, 7, 2, 8],
          .solved [1, 5, 6, 7, 2, 8]
        ],
        .split [
          .split [
            .solved [0, 7, 8, 9, 4, 5],
            .solved [4, 7, 8, 9, 0, 5]
          ],
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ],
        .split [
          .split [
            .solved [5, 7, 8, 9, 6, 4]
          ]
        ]
      ],
      .split [
        .solved [0, 6, 7, 2, 4, 5],
        .split [
          .solved [2, 6, 7, 8, 5, 4],
          .solved [4, 6, 8, 7, 0, 5],
          .solved [5, 6, 7, 8, 2, 4],
          .solved [4, 6, 8, 7, 0, 5],
          .solved [5, 6, 7, 8, 2, 4]
        ],
        .split [
          .solved [0, 7, 8, 1, 4, 5],
          .solved [4, 6, 7, 8, 0, 5],
          .solved [0, 6, 7, 8, 4, 5],
          .solved [4, 6, 7, 8, 0, 5]
        ],
        .split [
          .solved [5, 7, 8, 6, 1, 4],
          .solved [4, 6, 8, 7, 0, 5],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .solved [0, 6, 7, 8, 4, 5],
          .solved [4, 6, 7, 8, 0, 5]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .solved [2, 6, 7, 8, 5, 4],
          .solved [5, 6, 7, 8, 2, 4],
          .solved [5, 6, 7, 8, 2, 4],
          .solved [5, 6, 7, 8, 2, 4],
          .solved [5, 6, 7, 8, 2, 4]
        ],
        .split [
          .solved [0, 7, 8, 1, 4, 5],
          .solved [5, 7, 8, 6, 1, 4],
          .solved [4, 7, 8, 6, 0, 5],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .solved [5, 7, 8, 6, 1, 4],
          .split [
            .solved [4, 8, 9, 6, 0, 5],
            .solved [4, 6, 7, 8, 9, 5]
          ],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .solved [4, 7, 8, 6, 0, 5],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .solved [0, 6, 7, 1, 4, 5],
        .split [
          .solved [1, 6, 7, 8, 5, 4],
          .solved [4, 6, 8, 7, 0, 5],
          .solved [5, 6, 7, 8, 1, 4]
        ],
        .split [
          .solved [0, 6, 7, 8, 4, 5],
          .solved [4, 6, 7, 8, 0, 5]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .solved [1, 6, 7, 8, 5, 4],
          .solved [5, 6, 7, 8, 1, 4],
          .solved [5, 6, 7, 8, 1, 4]
        ],
        .split [
          .solved [4, 7, 8, 6, 0, 5],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 6, 7, 8, 4, 5],
          .solved [4, 6, 7, 8, 0, 5]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .solved [0, 5, 6, 2, 4, 7],
        .solved [0, 5, 6, 2, 4, 7],
        .solved [0, 5, 6, 4, 2, 7],
        .solved [0, 5, 6, 4, 2, 7],
        .solved [0, 5, 6, 4, 2, 7],
        .solved [0, 5, 6, 4, 2, 7]
      ],
      .split [
        .split [
          .solved [2, 5, 6, 7, 8, 4],
          .solved [4, 5, 8, 6, 0, 7],
          .solved [4, 5, 6, 7, 8, 2],
          .solved [4, 5, 8, 6, 0, 7],
          .solved [4, 5, 6, 7, 8, 2]
        ],
        .split [
          .solved [0, 7, 8, 4, 1, 5],
          .solved [4, 5, 7, 6, 0, 8],
          .solved [0, 4, 5, 7, 8, 6],
          .solved [4, 5, 7, 6, 0, 8]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 1],
            .solved [4, 5, 9, 6, 0, 7],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .solved [4, 5, 8, 6, 0, 7],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [0, 4, 5, 7, 8, 6],
          .solved [4, 5, 7, 6, 0, 8]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .solved [0, 6, 7, 4, 1, 5],
        .split [
          .solved [4, 5, 6, 7, 0, 8],
          .solved [0, 4, 5, 6, 8, 7],
          .solved [4, 5, 6, 7, 0, 8]
        ],
        .split [
          .solved [0, 4, 5, 6, 7, 8],
          .solved [0, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 0, 8]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 1],
          .solved [4, 5, 8, 6, 0, 7],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [0, 4, 5, 7, 8, 6],
          .solved [4, 5, 7, 6, 0, 8]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 4, 5, 6, 7, 8],
          .solved [0, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 0, 8]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [2, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 2],
          .solved [4, 5, 6, 7, 8, 2],
          .solved [4, 5, 6, 7, 8, 2],
          .solved [4, 5, 6, 7, 8, 2]
        ],
        .split [
          .solved [0, 7, 8, 4, 1, 5],
          .split [
            .solved [4, 7, 8, 9, 5, 1],
            .solved [4, 7, 9, 5, 0, 6],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .solved [4, 7, 8, 5, 0, 6],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 1],
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 8, 9, 5, 0, 6],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [4, 7, 8, 5, 0, 6],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .solved [0, 6, 7, 4, 1, 5],
        .split [
          .solved [4, 6, 7, 8, 5, 1],
          .solved [4, 6, 8, 5, 0, 7],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [0, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 0, 8]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 1],
          .split [
            .solved [4, 8, 9, 5, 0, 6],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [4, 7, 8, 5, 0, 6],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 0, 8]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .solved [0, 5, 6, 1, 4, 7],
        .solved [0, 5, 6, 1, 4, 7],
        .solved [0, 5, 6, 4, 1, 7],
        .solved [0, 5, 6, 4, 1, 7]
      ],
      .split [
        .split [
          .solved [1, 5, 6, 7, 8, 4],
          .solved [4, 5, 8, 6, 0, 7],
          .solved [4, 5, 6, 7, 8, 1]
        ],
        .split [
          .solved [0, 4, 5, 7, 8, 6],
          .solved [4, 5, 7, 6, 0, 8]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 4, 5, 6, 7, 8],
          .solved [0, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 0, 8]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [1, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 1],
          .solved [4, 5, 6, 7, 8, 1]
        ],
        .split [
          .solved [4, 7, 8, 5, 0, 6],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 0, 8]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [0, 4, 5, 6, 7, 8],
          .solved [0, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 0, 8]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ]
  ]

private def tree6a7 : WitnessTree :=
  .split [
    .split [
      .split [
        .split [
          .solved [3, 4, 5, 6, 7, 8],
          .split [
            .solved [0, 1, 2, 8, 3, 9],
            .solved [0, 1, 2, 8, 3, 9],
            .solved [1, 0, 2, 8, 3, 9],
            .solved [3, 4, 5, 6, 7, 9],
            .solved [2, 0, 1, 8, 3, 9],
            .solved [3, 4, 5, 6, 7, 9],
            .solved [3, 4, 5, 6, 7, 9],
            .solved [3, 4, 5, 6, 7, 9]
          ],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 4, 5, 6, 7, 8],
          .solved [3, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [0, 1, 2, 7, 3, 8],
          .solved [0, 1, 2, 7, 3, 8],
          .solved [1, 0, 2, 7, 3, 8],
          .split [
            .solved [4, 5, 6, 8, 3, 9],
            .solved [2, 0, 1, 7, 3, 9],
            .solved [4, 5, 6, 8, 3, 9],
            .solved [4, 5, 6, 8, 3, 9],
            .solved [4, 5, 6, 8, 3, 9]
          ],
          .solved [2, 0, 1, 7, 3, 8],
          .split [
            .solved [4, 5, 6, 8, 3, 9],
            .solved [4, 5, 6, 8, 3, 9],
            .solved [4, 5, 6, 8, 3, 9]
          ],
          .split [
            .solved [4, 5, 6, 8, 3, 9],
            .solved [4, 5, 6, 8, 3, 9]
          ],
          .split [
            .solved [4, 5, 6, 8, 3, 9]
          ]
        ],
        .split [
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 3, 8],
          .solved [4, 5, 6, 7, 3, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 3, 8]
        ]
      ],
      .split [
        .solved [0, 1, 2, 6, 3, 7],
        .solved [0, 1, 2, 6, 3, 7],
        .solved [1, 0, 2, 6, 3, 7],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 2],
            .solved [2, 0, 1, 6, 3, 9],
            .solved [6, 7, 8, 9, 2, 4],
            .solved [6, 7, 8, 9, 2, 4],
            .solved [6, 7, 8, 9, 2, 4]
          ],
          .solved [2, 0, 1, 6, 3, 8],
          .split [
            .solved [6, 8, 9, 7, 1, 4],
            .solved [4, 7, 8, 9, 5, 6],
            .solved [4, 7, 8, 9, 5, 6]
          ],
          .split [
            .solved [6, 8, 9, 7, 0, 4],
            .solved [4, 7, 8, 9, 5, 6]
          ],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .solved [2, 0, 1, 6, 3, 7],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 1],
            .solved [6, 7, 8, 9, 1, 4],
            .solved [6, 7, 8, 9, 1, 4]
          ],
          .split [
            .solved [6, 8, 9, 7, 0, 4],
            .solved [4, 7, 8, 9, 5, 6]
          ],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [6, 7, 8, 9, 0, 4]
          ],
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 6]
          ]
        ]
      ],
      .split [
        .split [
          .solved [1, 6, 7, 8, 2, 4],
          .solved [2, 6, 7, 8, 1, 4],
          .solved [2, 6, 7, 8, 1, 4],
          .solved [1, 6, 7, 8, 2, 4],
          .solved [1, 6, 7, 8, 2, 4],
          .split [
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [2, 7, 8, 6, 0, 4],
          .solved [4, 6, 7, 8, 5, 2],
          .split [
            .solved [1, 8, 9, 6, 0, 4],
            .solved [4, 6, 8, 9, 5, 1],
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 6, 8, 9, 5, 1],
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [4, 6, 7, 8, 5, 2],
          .split [
            .solved [1, 8, 9, 6, 0, 4],
            .solved [4, 6, 8, 9, 5, 1],
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 6, 8, 9, 5, 1],
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [1, 7, 8, 6, 0, 4],
          .solved [4, 6, 7, 8, 5, 1],
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [4, 6, 7, 8, 5, 1],
          .split [
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 6, 7, 8, 2, 4],
          .solved [2, 6, 7, 8, 0, 4],
          .solved [0, 6, 7, 8, 2, 4],
          .split [
            .solved [4, 5, 6, 7, 8, 9],
            .solved [0, 6, 7, 9, 2, 4],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .solved [0, 6, 7, 8, 2, 4],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [4, 6, 7, 8, 5, 2],
          .split [
            .solved [0, 8, 9, 6, 1, 4],
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 6, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 6, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [0, 7, 8, 6, 1, 4],
          .split [
            .solved [4, 7, 8, 9, 5, 1],
            .solved [4, 6, 7, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .solved [4, 6, 7, 8, 5, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 1],
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 6, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [4, 6, 7, 8, 5, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 2],
          .split [
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [0, 7, 8, 9, 1, 4],
            .solved [1, 7, 8, 9, 0, 4],
            .solved [0, 7, 8, 9, 1, 4],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 7, 8, 9, 5, 1],
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 1],
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 6, 7, 8, 1, 4],
          .solved [1, 6, 7, 8, 0, 4],
          .solved [0, 6, 7, 8, 1, 4],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [4, 6, 7, 8, 5, 1],
          .split [
            .solved [4, 6, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [4, 6, 7, 8, 5, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 1],
          .split [
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .solved [0, 1, 2, 5, 3, 6],
      .solved [0, 1, 2, 5, 3, 6],
      .solved [1, 0, 2, 5, 3, 6],
      .split [
        .split [
          .solved [2, 6, 7, 8, 5, 4],
          .solved [2, 0, 1, 5, 3, 8],
          .solved [5, 6, 7, 8, 2, 4],
          .solved [5, 6, 7, 8, 2, 4],
          .solved [5, 6, 7, 8, 2, 4]
        ],
        .solved [2, 0, 1, 5, 3, 7],
        .split [
          .solved [5, 7, 8, 6, 1, 4],
          .split [
            .solved [5, 8, 9, 6, 0, 4],
            .solved [4, 6, 7, 8, 9, 5]
          ],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .solved [5, 7, 8, 6, 0, 4],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .solved [2, 0, 1, 5, 3, 6],
      .split [
        .split [
          .solved [1, 6, 7, 8, 5, 4],
          .solved [5, 6, 7, 8, 1, 4],
          .solved [5, 6, 7, 8, 1, 4]
        ],
        .split [
          .solved [5, 7, 8, 6, 0, 4],
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 6, 7, 8, 5, 4],
          .solved [5, 6, 7, 8, 0, 4]
        ],
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 6, 7, 8, 9, 5]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .solved [1, 5, 6, 7, 2, 4],
        .solved [2, 5, 6, 7, 1, 4],
        .solved [2, 5, 6, 7, 1, 4],
        .solved [1, 5, 6, 7, 2, 4],
        .solved [1, 5, 6, 7, 2, 4],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .solved [2, 6, 7, 5, 0, 4],
        .split [
          .solved [2, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 2],
          .solved [4, 5, 6, 7, 8, 2],
          .solved [4, 5, 6, 7, 8, 2],
          .solved [4, 5, 6, 7, 8, 2]
        ],
        .split [
          .solved [1, 7, 8, 5, 0, 4],
          .solved [4, 5, 7, 8, 6, 1],
          .solved [4, 6, 7, 8, 5, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [4, 5, 7, 8, 6, 1],
          .split [
            .solved [4, 6, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [4, 6, 7, 8, 5, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [2, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 2],
          .solved [4, 5, 6, 7, 8, 2],
          .solved [4, 5, 6, 7, 8, 2],
          .solved [4, 5, 6, 7, 8, 2]
        ],
        .split [
          .solved [1, 7, 8, 5, 0, 4],
          .solved [4, 5, 7, 8, 6, 1],
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [4, 5, 7, 8, 6, 1],
          .split [
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .solved [1, 6, 7, 5, 0, 4],
        .split [
          .solved [1, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 1],
          .solved [4, 5, 6, 7, 8, 1]
        ],
        .split [
          .solved [4, 6, 7, 8, 5, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [1, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 1],
          .solved [4, 5, 6, 7, 8, 1]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .solved [0, 5, 6, 7, 2, 4],
        .solved [2, 5, 6, 7, 0, 4],
        .solved [0, 5, 6, 7, 2, 4],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 1],
            .solved [0, 5, 6, 9, 2, 4],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .solved [0, 5, 6, 8, 2, 4],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .solved [0, 5, 6, 7, 2, 4],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [2, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 2],
          .solved [4, 5, 6, 7, 8, 2],
          .solved [4, 5, 6, 7, 8, 2],
          .solved [4, 5, 6, 7, 8, 2]
        ],
        .split [
          .solved [0, 7, 8, 5, 1, 4],
          .split [
            .solved [4, 7, 8, 9, 5, 1],
            .solved [4, 5, 7, 9, 6, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .solved [4, 5, 7, 8, 6, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 1],
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 8, 9, 6, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [4, 5, 7, 8, 6, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .solved [0, 6, 7, 5, 1, 4],
        .split [
          .solved [4, 6, 7, 8, 5, 1],
          .solved [4, 5, 6, 8, 7, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [0, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 0]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 1],
          .split [
            .solved [4, 5, 8, 9, 6, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [4, 5, 7, 8, 6, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 0]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [2, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 2],
          .solved [4, 5, 6, 7, 8, 2],
          .solved [4, 5, 6, 7, 8, 2],
          .solved [4, 5, 6, 7, 8, 2]
        ],
        .split [
          .split [
            .solved [0, 7, 8, 9, 1, 4],
            .solved [1, 7, 8, 9, 0, 4],
            .solved [0, 7, 8, 9, 1, 4],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 7, 8, 9, 5, 1],
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 1],
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 6, 7, 8, 1, 4],
          .solved [1, 6, 7, 8, 0, 4],
          .solved [0, 6, 7, 8, 1, 4],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [4, 6, 7, 8, 5, 1],
          .split [
            .solved [4, 6, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [4, 6, 7, 8, 5, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 1],
          .split [
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .solved [0, 5, 6, 7, 1, 4],
        .solved [1, 5, 6, 7, 0, 4],
        .solved [0, 5, 6, 7, 1, 4],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [1, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 1],
          .solved [4, 5, 6, 7, 8, 1]
        ],
        .split [
          .solved [4, 5, 7, 8, 6, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 0]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [1, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 1],
          .solved [4, 5, 6, 7, 8, 1]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [0, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 0]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ]
  ]

private def tree6a8 : WitnessTree :=
  .split [
    .solved [0, 1, 2, 4, 3, 5],
    .solved [0, 1, 2, 4, 3, 5],
    .solved [1, 0, 2, 4, 3, 5],
    .split [
      .split [
        .split [
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 0, 1, 4, 3, 8],
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 4, 5, 6, 7, 8]
        ],
        .solved [2, 0, 1, 4, 3, 7],
        .split [
          .solved [4, 7, 8, 5, 1, 6],
          .solved [4, 5, 6, 7, 2, 8],
          .solved [4, 5, 6, 7, 2, 8]
        ],
        .split [
          .solved [4, 7, 8, 5, 0, 6],
          .solved [4, 5, 6, 7, 2, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 2, 8]
        ]
      ],
      .solved [2, 0, 1, 4, 3, 6],
      .split [
        .split [
          .solved [1, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 1, 8],
          .solved [4, 6, 7, 5, 1, 8]
        ],
        .split [
          .solved [4, 7, 8, 5, 0, 6],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 0, 8]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .solved [2, 0, 1, 4, 3, 5],
    .split [
      .split [
        .split [
          .solved [1, 4, 5, 6, 7, 8],
          .solved [1, 4, 5, 6, 7, 8],
          .solved [1, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [4, 7, 8, 5, 0, 6],
          .solved [4, 5, 6, 7, 1, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 1, 8]
        ]
      ],
      .split [
        .split [
          .solved [0, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 0, 8]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [0, 4, 5, 6, 7, 8],
          .solved [0, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 0, 8]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ]
  ]

private def tree6a9 : WitnessTree :=
  .split [
    .split [
      .split [
        .solved [1, 2, 4, 5, 6, 7],
        .solved [1, 2, 4, 5, 6, 7],
        .solved [1, 2, 4, 5, 6, 7],
        .solved [1, 4, 5, 2, 7, 6],
        .solved [1, 4, 5, 2, 7, 6],
        .solved [1, 4, 5, 6, 2, 7],
        .solved [1, 4, 5, 6, 2, 7]
      ],
      .split [
        .solved [2, 6, 7, 4, 0, 5],
        .solved [2, 4, 5, 6, 1, 7],
        .solved [1, 4, 5, 2, 7, 6],
        .solved [1, 4, 5, 2, 7, 6],
        .solved [2, 4, 5, 6, 1, 7],
        .solved [2, 4, 5, 6, 1, 7]
      ],
      .split [
        .solved [2, 4, 5, 6, 1, 7],
        .solved [1, 4, 5, 2, 7, 6],
        .solved [1, 4, 5, 2, 7, 6],
        .solved [2, 4, 5, 6, 1, 7],
        .solved [2, 4, 5, 6, 1, 7]
      ],
      .split [
        .solved [1, 6, 7, 4, 0, 5],
        .solved [1, 4, 5, 6, 2, 7],
        .solved [1, 4, 5, 6, 2, 7],
        .solved [1, 4, 5, 6, 2, 7]
      ],
      .split [
        .solved [1, 4, 5, 6, 2, 7],
        .solved [1, 4, 5, 6, 2, 7],
        .solved [1, 4, 5, 6, 2, 7]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .solved [0, 2, 5, 6, 7, 4],
        .solved [2, 5, 6, 4, 0, 7],
        .solved [0, 5, 6, 2, 7, 4],
        .solved [2, 5, 6, 4, 0, 7],
        .solved [0, 5, 6, 2, 7, 4],
        .solved [2, 5, 6, 4, 0, 7]
      ],
      .split [
        .split [
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [0, 7, 8, 1, 5, 4],
          .solved [4, 7, 8, 5, 1, 6],
          .solved [4, 5, 7, 8, 6, 0],
          .solved [4, 5, 6, 7, 2, 8]
        ],
        .split [
          .solved [4, 7, 8, 5, 1, 6],
          .solved [4, 5, 6, 7, 2, 8],
          .solved [4, 5, 6, 7, 2, 8]
        ],
        .split [
          .solved [4, 5, 7, 8, 6, 0],
          .solved [4, 5, 6, 7, 2, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 2, 8]
        ]
      ],
      .split [
        .solved [0, 6, 7, 1, 5, 4],
        .split [
          .solved [1, 4, 6, 7, 8, 5],
          .solved [4, 5, 6, 8, 7, 0],
          .solved [4, 6, 7, 5, 1, 8]
        ],
        .split [
          .solved [0, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 0]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [1, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 1, 8],
          .solved [4, 6, 7, 5, 1, 8]
        ],
        .split [
          .solved [4, 5, 7, 8, 6, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 0]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [1, 7, 8, 4, 0, 5],
          .solved [4, 7, 8, 5, 1, 6],
          .solved [4, 5, 6, 7, 2, 8],
          .solved [4, 5, 6, 7, 2, 8]
        ],
        .split [
          .solved [4, 7, 8, 5, 1, 6],
          .solved [4, 5, 6, 7, 2, 8],
          .solved [4, 5, 6, 7, 2, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 2, 8],
          .solved [4, 5, 6, 7, 2, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 2, 8]
        ]
      ],
      .split [
        .solved [1, 6, 7, 4, 0, 5],
        .split [
          .solved [1, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 1, 8],
          .solved [4, 6, 7, 5, 1, 8]
        ],
        .split [
          .solved [4, 6, 7, 8, 5, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [1, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 1, 8],
          .solved [4, 6, 7, 5, 1, 8]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .solved [0, 1, 5, 6, 7, 4],
        .solved [1, 5, 6, 4, 0, 7],
        .solved [0, 5, 6, 1, 7, 4],
        .solved [1, 5, 6, 4, 0, 7]
      ],
      .split [
        .split [
          .solved [1, 4, 5, 6, 7, 8],
          .solved [1, 4, 5, 6, 7, 8],
          .solved [1, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [4, 5, 7, 8, 6, 0],
          .solved [4, 5, 6, 7, 1, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 1, 8]
        ]
      ],
      .split [
        .split [
          .solved [0, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 0]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [1, 4, 5, 6, 7, 8],
          .solved [1, 4, 5, 6, 7, 8],
          .solved [1, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 1, 8],
          .solved [4, 5, 6, 7, 1, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 1, 8]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [0, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 0]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ]
  ]

private def tree6a10 : WitnessTree :=
  .split [
    .split [
      .split [
        .solved [0, 2, 4, 5, 6, 7],
        .solved [0, 2, 4, 5, 6, 7],
        .solved [0, 4, 5, 2, 7, 6],
        .solved [0, 4, 5, 6, 2, 7],
        .solved [0, 4, 5, 2, 7, 6],
        .solved [0, 4, 5, 6, 2, 7]
      ],
      .split [
        .solved [2, 4, 5, 6, 0, 7],
        .solved [0, 4, 5, 2, 7, 6],
        .solved [2, 4, 5, 6, 0, 7],
        .solved [0, 4, 5, 2, 7, 6],
        .solved [2, 4, 5, 6, 0, 7]
      ],
      .split [
        .solved [0, 6, 7, 4, 1, 5],
        .solved [0, 4, 5, 6, 2, 7],
        .solved [0, 4, 5, 6, 2, 7],
        .solved [0, 4, 5, 6, 2, 7]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 1],
          .solved [0, 4, 5, 8, 2, 6],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .solved [0, 4, 5, 7, 2, 6],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .solved [0, 4, 5, 6, 2, 7],
        .solved [0, 4, 5, 6, 2, 7]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [0, 7, 8, 4, 1, 5],
          .solved [4, 5, 6, 7, 2, 8],
          .solved [4, 7, 8, 5, 0, 6],
          .solved [4, 5, 6, 7, 2, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 2, 8],
          .solved [4, 5, 6, 7, 2, 8],
          .solved [4, 5, 6, 7, 2, 8]
        ],
        .split [
          .solved [4, 7, 8, 5, 0, 6],
          .solved [4, 5, 6, 7, 2, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 2, 8]
        ]
      ],
      .split [
        .solved [0, 6, 7, 4, 1, 5],
        .split [
          .solved [4, 6, 7, 8, 5, 1],
          .solved [4, 6, 8, 5, 0, 7],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [0, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 0, 8]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 1],
          .split [
            .solved [4, 8, 9, 5, 0, 6],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [4, 7, 8, 5, 0, 6],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 0, 8]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .solved [0, 5, 6, 1, 4, 7],
        .solved [0, 5, 6, 1, 4, 7],
        .solved [0, 5, 6, 4, 1, 7],
        .solved [0, 5, 6, 4, 1, 7]
      ],
      .split [
        .split [
          .solved [1, 5, 6, 7, 8, 4],
          .solved [4, 5, 8, 6, 0, 7],
          .solved [4, 5, 6, 7, 8, 1]
        ],
        .split [
          .solved [0, 4, 5, 7, 8, 6],
          .solved [4, 5, 7, 6, 0, 8]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 4, 5, 6, 7, 8],
          .solved [0, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 0, 8]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [1, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 1],
          .solved [4, 5, 6, 7, 8, 1]
        ],
        .split [
          .solved [4, 7, 8, 5, 0, 6],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 0, 8]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [0, 4, 5, 6, 7, 8],
          .solved [0, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 0, 8]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ]
  ]

private def tree6a11 : WitnessTree :=
  .split [
    .split [
      .split [
        .split [
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 4, 5, 6, 7, 8],
          .solved [2, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 2, 8],
          .solved [4, 5, 6, 7, 2, 8],
          .solved [4, 5, 6, 7, 2, 8],
          .solved [4, 5, 6, 7, 2, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 2, 8],
          .solved [4, 5, 6, 7, 2, 8],
          .solved [4, 5, 6, 7, 2, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 2, 8],
          .solved [4, 5, 6, 7, 2, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 2, 8]
        ]
      ],
      .split [
        .split [
          .solved [0, 6, 7, 8, 1, 4],
          .solved [1, 6, 7, 8, 0, 4],
          .solved [0, 6, 7, 8, 1, 4],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [4, 6, 7, 8, 5, 1],
          .split [
            .solved [4, 6, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .solved [4, 6, 7, 8, 5, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 1],
          .split [
            .solved [4, 5, 6, 7, 8, 9],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .solved [0, 5, 6, 7, 1, 4],
        .solved [1, 5, 6, 7, 0, 4],
        .solved [0, 5, 6, 7, 1, 4],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [1, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 1],
          .solved [4, 5, 6, 7, 8, 1]
        ],
        .split [
          .solved [4, 5, 7, 8, 6, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [0, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 0]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [1, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 1],
          .solved [4, 5, 6, 7, 8, 1]
        ],
        .split [
          .split [
            .solved [4, 7, 8, 9, 5, 0],
            .solved [4, 5, 6, 7, 8, 9]
          ],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [0, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 0]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ]
  ]

private def tree6a12 : WitnessTree :=
  .split [
    .split [
      .split [
        .solved [0, 1, 4, 5, 6, 7],
        .solved [0, 1, 4, 5, 6, 7],
        .solved [0, 4, 5, 1, 7, 6],
        .solved [0, 4, 5, 6, 1, 7]
      ],
      .split [
        .solved [1, 4, 5, 6, 0, 7],
        .solved [0, 4, 5, 1, 7, 6],
        .solved [1, 4, 5, 6, 0, 7]
      ],
      .split [
        .solved [0, 4, 5, 6, 1, 7],
        .solved [0, 4, 5, 6, 1, 7]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [1, 4, 5, 6, 7, 8],
          .solved [1, 4, 5, 6, 7, 8],
          .solved [1, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [4, 7, 8, 5, 0, 6],
          .solved [4, 5, 6, 7, 1, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 1, 8]
        ]
      ],
      .split [
        .split [
          .solved [0, 4, 6, 7, 8, 5],
          .solved [4, 6, 7, 5, 0, 8]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [0, 4, 5, 6, 7, 8],
          .solved [0, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 0, 8]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ]
  ]

private def tree6a13 : WitnessTree :=
  .split [
    .split [
      .split [
        .split [
          .solved [1, 4, 5, 6, 7, 8],
          .solved [1, 4, 5, 6, 7, 8],
          .solved [1, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 1, 8],
          .solved [4, 5, 6, 7, 1, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 1, 8]
        ]
      ],
      .split [
        .split [
          .solved [4, 6, 7, 8, 5, 0],
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .solved [0, 5, 6, 7, 8, 4],
          .solved [4, 5, 6, 7, 8, 0]
        ],
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ]
  ]

private def tree6a14 : WitnessTree :=
  .split [
    .split [
      .split [
        .split [
          .solved [0, 4, 5, 6, 7, 8],
          .solved [0, 4, 5, 6, 7, 8]
        ],
        .split [
          .solved [4, 5, 6, 7, 0, 8]
        ]
      ],
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ],
    .split [
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ]
  ]

private def tree6a15 : WitnessTree :=
  .split [
    .split [
      .split [
        .split [
          .split [
            .solved [4, 5, 6, 7, 8, 9]
          ]
        ]
      ]
    ]
  ]

private def trees6 : ℕ → WitnessTree
  | 1 => tree6a1
  | 2 => tree6a2
  | 3 => tree6a3
  | 4 => tree6a4
  | 5 => tree6a5
  | 6 => tree6a6
  | 7 => tree6a7
  | 8 => tree6a8
  | 9 => tree6a9
  | 10 => tree6a10
  | 11 => tree6a11
  | 12 => tree6a12
  | 13 => tree6a13
  | 14 => tree6a14
  | 15 => tree6a15
  | _ => .solved []

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem masks6 (a : Fin 16) (hlo : 1 ≤ a.val) :
    checkTree 4 7 6 541065248 6 a.val [a.val] (trees6 a.val) = true := by
  fin_cases a <;> norm_num at hlo
  all_goals as_aux_lemma => decide +kernel

end Erdos1182SaturatedProfiles

namespace Erdos1182SaturatedProfiles

open SimpleGraph Finset

private theorem independent_four_on_nine (C : SimpleGraph (Fin 9)) (hC : C.CliqueFree 3) :
    ∃ S : Finset (Fin 9), Cᶜ.IsNClique 4 S := by
  obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd⟩ := erdos1182_independent_four C hC
  refine ⟨{a,b,c,d},?_,?_⟩
  · intro x hx y hy hxy
    simp only [coe_insert,coe_singleton,Set.mem_insert_iff,Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl
    all_goals
      first
      | exact (hxy rfl).elim
      | exact hab
      | exact hac
      | exact had
      | exact hbc
      | exact hbd
      | exact hcd
      | exact hab.symm
      | exact hac.symm
      | exact had.symm
      | exact hbc.symm
      | exact hbd.symm
      | exact hcd.symm
  · simp [hab.ne,hac.ne,had.ne,hbc.ne,hbd.ne,hcd.ne]

private theorem independent_four_on_eleven (C : SimpleGraph (Fin 11)) (hC : C.CliqueFree 3) :
    ∃ S : Finset (Fin 11), Cᶜ.IsNClique 4 S := by
  let e : Fin 9 ↪ Fin 11 := ⟨Fin.castAdd 2, Fin.castAdd_injective 9 2⟩
  let D := C.comap e
  let f : D ↪g C := SimpleGraph.Embedding.comap e C
  let fc : Dᶜ ↪g Cᶜ := SimpleGraph.Embedding.complEquiv f
  obtain ⟨S,hS⟩ := independent_four_on_nine D (CliqueFree.comap f.isContained hC)
  refine ⟨S.map fc.toEmbedding, hS.map.mono ?_⟩
  intro x y h
  obtain ⟨a,b,hab,rfl,rfl⟩ := (SimpleGraph.map_adj fc.toEmbedding Dᶜ x y).mp h
  exact fc.map_adj_iff.mpr hab

private noncomputable def leftEquiv {V : Type} [DecidableEq V] (S : Finset V) {r : ℕ} (hs : S.card = r) :
    Fin r ≃ S := (Fintype.equivFinOfCardEq (by simpa using hs : Fintype.card S = r)).symm

private def coeEmbedding {V : Type} [DecidableEq V] {S : Finset V} {r : ℕ}
    (f : Fin r ≃ S) : Fin r ↪ V := f.toEmbedding.trans (Function.Embedding.subtype _)

private theorem embed_using_profile {r s k cap minimum : ℕ}
    {trees : ℕ → WitnessTree}
    (hs2 : 1 ≤ s)
    (certificate : ∀ a : Fin (2^r), minimum ≤ a.val →
      checkTree r s k cap (s-1) a.val [a.val] (trees a.val) = true)
    (C : SimpleGraph (Fin (r+s))) [DecidableRel C.Adj] (hC : C.CliqueFree 3)
    (S : Finset (Fin (r+s))) (hS : Cᶜ.IsNClique r S)
    (hlo : ∀ x, x ∉ S → minimum ≤ mask C (coeEmbedding (leftEquiv S hS.card_eq)) x) :
    ∃ f : Fin k ↪ Fin (r+s), ∀ i j, i < j →
      cap.testBit (i.val*k+j.val) = false → ¬ C.Adj (f i) (f j) := by
  let left : Fin r ↪ Fin (r+s) := coeEmbedding (leftEquiv S hS.card_eq)
  have hleft (i : Fin r) : left i ∈ S := (leftEquiv S hS.card_eq i).property
  obtain ⟨right, hRight, hs⟩ := sort_outside C S
    (by simp [Finset.card_compl, hS.card_eq]) left (s := s)
  let profile := List.ofFn (mask C left ∘ right)
  obtain ⟨f,hf⟩ := verify_profile hs2 certificate (profile := profile) (by simp [profile])
    (fun x hx => by
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
      exact hlo _ (hRight i))
    (fun x hx => by
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
      exact mask_lt C left (right i)) hs
  let join := unionEmbedding left right (fun i j e => hRight j (e ▸ hleft i))
  refine ⟨f.trans join, ?_⟩
  intro i j hij hcap hedge
  have hleftInd (a b : Fin r) : ¬ C.Adj (left a) (left b) := fun h =>
    (hS.isClique (hleft a) (hleft b) h.ne).2 h
  exact Bool.false_ne_true ((hf i j hij hcap).symm.trans
    (edge_in_saturated C hC left right hleftInd (f i) (f j) hedge))

private def lowMask (n : ℕ) : Bool :=
  decide (((List.range 5).filter (fun i => n.testBit i)).length ≤ 2)

private def placement (mask : ℕ) : List ℕ :=
  let missing := (List.range 5).filter (fun i => !mask.testBit i)
  let rem := (List.range 5).filter (fun i => !((missing.take 3).contains i))
  [rem.getD 0 0, missing.getD 0 0, missing.getD 1 0, missing.getD 2 0, rem.getD 1 0]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem small_place : ∀ q : Fin 32, lowMask q.val = true →
    let l := placement q.val
    l.length = 5 ∧ l.Nodup ∧ (∀ j ∈ l, j < 5) ∧
      (List.range 5).all (fun i => (541065248 : ℕ).testBit (i*6+5) || !q.val.testBit (l.getD i 0)) = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem overlap : ∀ a b : Fin 32, lowMask a.val = false → lowMask b.val = false →
    a.val &&& b.val ≠ 0 := by
  decide +kernel

private theorem six_of_independent_five (C : SimpleGraph (Fin 11)) [DecidableRel C.Adj]
    (hC : C.CliqueFree 3) (S : Finset (Fin 11)) (hS : Cᶜ.IsNClique 5 S) :
    ∃ f : Fin 6 ↪ Fin 11, ∀ i j, i < j →
      (541065248 : ℕ).testBit (i.val*6+j.val) = false → ¬ C.Adj (f i) (f j) := by
  let left := coeEmbedding (leftEquiv S hS.card_eq)
  have hl (i : Fin 5) : left i ∈ S := (leftEquiv S hS.card_eq i).property
  by_cases hp : ∃ v : Fin 11, v ∉ S ∧ lowMask (mask C left v) = true
  · obtain ⟨v, hv, hlow⟩ := hp
    let q := mask C left v
    have hqlt : q < 32 := mask_lt C left v
    let l := placement q
    obtain ⟨hlen,hnodup,hbounds,hcheck⟩ := small_place ⟨q,hqlt⟩ hlow
    change l.length = 5 at hlen
    let index (i : Fin 5) : Fin l.length := ⟨i.val, by rw [hlen]; exact i.isLt⟩
    let re : Fin 5 ↪ Fin 5 := ⟨fun i => ⟨l.get (index i),
      hbounds _ (List.get_mem l (index i))⟩, by
      intro i j hij
      have hi := hnodup.injective_get (congrArg (fun p : Fin 5 => p.val) hij)
      exact Fin.ext (congrArg (fun p : Fin l.length => p.val) hi)⟩
    let endpt : Fin 1 ↪ Fin 11 := ⟨fun _ => v, fun _ _ _ => Subsingleton.elim _ _⟩
    let f : Fin (5+1) ↪ Fin 11 := unionEmbedding (re.trans left) endpt (by
      intro i j e
      change left (re i) = v at e
      exact hv (e ▸ hl (re i)))
    have hfLeft (i : Fin 5) : f (Fin.castAdd 1 i) = left (re i) := by
      change Fin.addCases (motive := fun _ => Fin 11) (re.trans left) endpt (Fin.castAdd 1 i) = _
      exact Fin.addCases_left i
    have hfRight (i : Fin 1) : f (Fin.natAdd 5 i) = v := by
      change Fin.addCases (motive := fun _ => Fin 11) (re.trans left) endpt (Fin.natAdd 5 i) = _
      exact Fin.addCases_right i
    refine ⟨f, show ∀ i j : Fin (5+1), i < j → _ from ?_⟩
    intro i j
    induction i using Fin.addCases with
    | left i =>
      induction j using Fin.addCases with
      | left j =>
        intro _ _ he
        have he' : C.Adj (left (re i)) (left (re j)) := by
          simpa only [hfLeft] using he
        exact (hS.isClique (hl (re i)) (hl (re j)) he'.ne).2 he'
      | right j =>
        intro _ hcap he
        have hj : j.val = 0 := by omega
        have hcap' : (541065248 : ℕ).testBit (i.val*6+5) = false := by
          simpa [Fin.natAdd, hj] using hcap
        have ht := (List.all_eq_true.mp hcheck) i.val (List.mem_range.mpr i.isLt)
        rw [hcap', Bool.false_or, Bool.not_eq_true_eq_eq_false] at ht
        have hindex : i.val < (placement q).length := by
          change i.val < l.length
          rw [hlen]
          exact i.isLt
        rw [List.getD_eq_getElem _ _ hindex] at ht
        have he' : C.Adj (left (re i)) v := by
          simpa only [hfLeft,hfRight] using he
        exact Bool.false_ne_true (ht.symm.trans ((mask_at C left v (re i)).trans (decide_eq_true he')))
    | right i =>
      induction j using Fin.addCases with
      | left j =>
        intro h
        have ht : (Fin.natAdd 5 i).val < (Fin.castAdd 1 j).val := h
        simp [Fin.natAdd] at ht
        omega
      | right j =>
        intro h
        change 5 + i.val < 5 + j.val at h
        omega
  · have hhi (v : Fin 11) (hv : v ∉ S) : lowMask (mask C left v) = false := by
      exact Bool.eq_false_iff.mpr (fun h => hp ⟨v,hv,h⟩)
    let f := coeEmbedding (leftEquiv (Sᶜ) (by simp [Finset.card_compl,hS.card_eq] : Sᶜ.card = 6))
    refine ⟨f, fun i j _ _ he => ?_⟩
    have hf (i : Fin 6) : f i ∉ S := Finset.mem_compl.mp
      (leftEquiv (Sᶜ) (by simp [Finset.card_compl,hS.card_eq] : Sᶜ.card = 6) i).property
    exact overlap ⟨_,mask_lt C left (f i)⟩ ⟨_,mask_lt C left (f j)⟩ (hhi _ (hf i)) (hhi _ (hf j))
      (masks_disjoint_of_adjacent C hC left he)

private theorem five (C : SimpleGraph (Fin 9)) [DecidableRel C.Adj] (hC : C.CliqueFree 3) :
    ∃ f : Fin 5 ↪ Fin 9, ∀ i j, i < j →
      (540672 : ℕ).testBit (i.val*5+j.val) = false → ¬ C.Adj (f i) (f j) := by
  obtain ⟨S,hS⟩ := independent_four_on_nine C hC
  exact embed_using_profile (r := 4) (s := 5) (k := 5) (cap := 540672) (minimum := 0)
    (by decide) masks5 C hC S hS (fun _ _ => Nat.zero_le _)

private theorem six (C : SimpleGraph (Fin 11)) [DecidableRel C.Adj] (hC : C.CliqueFree 3) :
    ∃ f : Fin 6 ↪ Fin 11, ∀ i j, i < j →
      (541065248 : ℕ).testBit (i.val*6+j.val) = false → ¬ C.Adj (f i) (f j) := by
  by_cases hf : Cᶜ.CliqueFree 5
  · obtain ⟨S,hS⟩ := independent_four_on_eleven C hC
    apply embed_using_profile (r := 4) (s := 7) (k := 6) (cap := 541065248) (minimum := 1)
      (by decide) masks6 C hC S hS
    intro x hx
    by_contra! hm
    let e := leftEquiv S hS.card_eq
    change mask C (coeEmbedding e) x < 1 at hm
    have hm' : mask C (coeEmbedding e) x = 0 := by omega
    have hind (v : Fin 11) (hv : v ∈ S) : Cᶜ.Adj x v := by
      let i := e.symm ⟨v,hv⟩
      have hmv := mask_at C (coeEmbedding e) x i
      rw [hm',Nat.zero_testBit] at hmv
      refine ⟨fun h => hx (h.symm ▸ hv),fun h => ?_⟩
      have hv' : coeEmbedding e i = v := congrArg Subtype.val (e.apply_symm_apply ⟨v,hv⟩)
      rw [hv',decide_eq_true h.symm] at hmv
      contradiction
    have hc : Cᶜ.IsClique (insert x (S : Set (Fin 11))) :=
      hS.isClique.insert (fun v hv _ => hind v hv)
    exact hf (insert x S) ⟨by simpa only [Finset.coe_insert] using hc,
      by rw [Finset.card_insert_of_notMem hx,hS.card_eq]⟩
  · obtain ⟨S,hS⟩ : ∃ S, Cᶜ.IsNClique 5 S := by
      simpa only [CliqueFree,not_forall,not_not] using hf
    exact six_of_independent_five C hC S hS

end Erdos1182SaturatedProfiles

theorem OMA.solution : OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1_H1_R1.H1 := by
  intro t
  fin_cases t <;> dsimp only
  · exact erdos1182_embed_four
  · intro C hC
    classical
    exact Erdos1182SaturatedProfiles.five C hC
  · intro C hC
    classical
    exact Erdos1182SaturatedProfiles.six C hC
