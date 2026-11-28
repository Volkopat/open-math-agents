import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H4_R1_H2_R1_H2_R1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Choose.Basic

-- Credit: @avivorly
open Finset
open scoped BigOperators

lemma third_point_for_disjoint_heavy_support
    (M : Fin 6 ⊕ (Fin 37 ⊕ Fin 68) → Fin 19 ⊕ Fin 92 → Bool)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true)
    (colPairs : ∀ p q, p ≠ q → ∃! l, M l p = true ∧ M l q = true)
    (bSizes : ∀ b : Fin 37, (Finset.univ.filter fun p : Fin 19 => M (.inr (.inl b)) (.inl p) = true).card = 3)
    (cSizes : ∀ c : Fin 68, (Finset.univ.filter fun p : Fin 19 => M (.inr (.inr c)) (.inl p) = true).card = 1)
    (C : Fin 19 → Finset (Fin 6))
    (loc : ∀ p a, a ∈ C p ↔ M (.inl a) (.inl p) = true)
    (p q : Fin 19) (ne : p ≠ q) (apart : Disjoint (C p) (C q)) :
    ∃ t, t ≠ p ∧ t ≠ q ∧ Disjoint (C t) (C p ∪ C q) := by
  obtain ⟨l,hl,_⟩ := colPairs (.inl p) (.inl q) (fun e => ne (Sum.inl.inj e))
  cases l with
  | inl a =>
    exact False.elim (Finset.disjoint_left.mp apart ((loc p a).mpr hl.1) ((loc q a).mpr hl.2))
  | inr l =>
    cases l with
    | inr c =>
      let onLine := Finset.univ.filter fun x : Fin 19 => M (.inr (.inr c)) (.inl x) = true
      have one : onLine.card ≤ 1 := (cSizes c).le
      exact False.elim (ne (Finset.card_le_one.mp one p (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl.1⟩)
        q (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl.2⟩)))
    | inl b =>
      let onLine := Finset.univ.filter fun x : Fin 19 => M (.inr (.inl b)) (.inl x) = true
      have sz : onLine.card = 3 := bSizes b
      have newPoint : (onLine \ {p,q}).Nonempty := by
        apply Finset.sdiff_nonempty.mpr
        intro sub
        have le := Finset.card_le_card sub
        have lim : ({p,q} : Finset (Fin 19)).card ≤ 2 :=
          (Finset.card_insert_le p {q}).trans_eq (by simp)
        omega
      obtain ⟨t,ht⟩ := newPoint
      obtain ⟨onB,notOld⟩ := Finset.mem_sdiff.mp ht
      have tOnB := (Finset.mem_filter.mp onB).2
      have tp : t ≠ p := fun same => notOld (same ▸ Finset.mem_insert_self _ _)
      have tq : t ≠ q := fun same => notOld (same ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      refine ⟨t,tp,tq,Finset.disjoint_left.mpr ?_⟩
      intro a onT onOld
      have tOnA := (loc t a).mp onT
      obtain ⟨_,_,unique⟩ := rowPairs (.inl a) (.inr (.inl b)) (by simp)
      rcases Finset.mem_union.mp onOld with onP | onQ
      · exact tp (Sum.inl.inj ((unique (.inl t) ⟨tOnA,tOnB⟩).trans
          (unique (.inl p) ⟨(loc p a).mp onP,hl.1⟩).symm))
      · exact tq (Sum.inl.inj ((unique (.inl t) ⟨tOnA,tOnB⟩).trans
          (unique (.inl q) ⟨(loc q a).mp onQ,hl.2⟩).symm))

lemma layout_total (A : Fin 6 → Fin 19 → Bool) (C : Fin 19 → Finset (Fin 6))
    (column_form : ∀ p, C p = Finset.univ.filter fun a => A a p = true)
    (sizes : ∀ a, (Finset.univ.filter fun p => A a p = true).card = 5) :
    (∑ p : Fin 19, (C p).card) = 30 := by
  calc
    _ = ∑ p : Fin 19, ∑ a : Fin 6, if A a p = true then (1 : Nat) else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      rw [← Finset.sum_filter, column_form p]
      simp
    _ = ∑ a : Fin 6, ∑ p : Fin 19, if A a p = true then (1 : Nat) else 0 := Finset.sum_comm
    _ = ∑ _a : Fin 6, (5 : Nat) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_filter]
      simpa using sizes a
    _ = _ := by simp

lemma layout_counts (C : Fin 19 → Finset (Fin 6)) (total : (∑ p : Fin 19, (C p).card) = 30)
    (overlap : ∀ p q, p ≠ q → (C p ∩ C q).card ≤ 1) :
    let F := (Finset.univ.filter fun p => 2 ≤ (C p).card).image C
    (Finset.univ.filter fun p => 0 < (C p).card).card + ∑ T ∈ F, (T.card - 1) = 30 := by
  let shared := Finset.univ.filter fun p => 2 ≤ (C p).card
  let used := Finset.univ.filter fun p => 0 < (C p).card
  have using_columns : (shared : Set (Fin 19)).InjOn C := by
    intro p hp q hq same
    by_contra different
    have small := overlap p q different
    rw [same,Finset.inter_self] at small
    have many := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2
    omega
  have split (p : Fin 19) : (C p).card =
      (if 0 < (C p).card then 1 else 0) +
      (if 2 ≤ (C p).card then (C p).card - 1 else 0) := by
    split_ifs <;> omega
  have sum_split : (∑ p : Fin 19, (C p).card) =
      used.card + ∑ p ∈ shared, ((C p).card - 1) := by
    calc
      _ = ∑ p : Fin 19, ((if 0 < (C p).card then 1 else 0) +
          (if 2 ≤ (C p).card then (C p).card - 1 else 0)) :=
        Finset.sum_congr rfl (fun p _ => split p)
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
        simp [used,shared]
  change used.card + ∑ T ∈ shared.image C, (T.card - 1) = 30
  rw [Finset.sum_image using_columns]
  exact sum_split.symm.trans total

theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H4_R1_H2_R1_H2_R1.H4 := by
  classical
  unfold OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H4_R1_H2_R1_H2_R1.H4
  dsimp only
  rintro ⟨M,_,_,rowPairs,colPairs,aSizes,bSizes,cSizes,_,_,atMost,triples,pairs,p,q,pThree,qThree,union⟩
  let A (a : Fin 6) (p : Fin 19) := M (.inl a) (.inl p)
  let C (p : Fin 19) := Finset.univ.filter fun a : Fin 6 => A a p = true
  let F := (Finset.univ.filter fun p => 2 ≤ (C p).card).image C
  let x := (F.filter fun T => T.card = 2).card
  let y := (F.filter fun T => T.card = 3).card
  let used := Finset.univ.filter fun p => 0 < (C p).card
  have x_size : x = 7 := pairs
  have y_size : y = 2 := triples
  have loc (p : Fin 19) (a : Fin 6) : a ∈ C p ↔ A a p = true := by simp [C]
  have csize (T : Finset (Fin 6)) (ht : T ∈ F) : 2 ≤ T.card ∧ T.card ≤ 3 := by
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ht
    exact ⟨(Finset.mem_filter.mp hr).2,atMost r⟩
  have per_support (T : Finset (Fin 6)) (ht : T ∈ F) :
      T.card-1 = (if T.card = 2 then 1 else 0) + (if T.card = 3 then 2 else 0) := by
    have limits := csize T ht
    split_ifs <;> omega
  have savings : (∑ T ∈ F, (T.card - 1)) = 11 := by
    calc
      _ = ∑ T ∈ F, ((if T.card = 2 then 1 else 0) + (if T.card = 3 then 2 else 0)) :=
        Finset.sum_congr rfl per_support
      _ = x + 2*y := by
        rw [Finset.sum_add_distrib,← Finset.sum_filter,← Finset.sum_filter]
        simp [x,y,Nat.mul_comm]
      _ = 11 := by rw [x_size,y_size]
  have overlap (p q : Fin 19) (different : p ≠ q) : (C p ∩ C q).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have on_both (z : Fin 6) (hz : z ∈ C p ∩ C q) : A z p = true ∧ A z q = true := by
      obtain ⟨hp,hq⟩ := Finset.mem_inter.mp hz
      exact ⟨(loc p z).mp hp,(loc q z).mp hq⟩
    obtain ⟨_,_,same⟩ := colPairs (.inl p) (.inl q) (fun e => different (Sum.inl.inj e))
    exact Sum.inl.inj ((same (.inl a) (on_both a ha)).trans (same (.inl b) (on_both b hb)).symm)
  have totals : used.card + ∑ T ∈ F, (T.card - 1) = 30 :=
    layout_counts C (layout_total A C (fun _ => rfl) aSizes) overlap
  have allUsed : used = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ,Fintype.card_fin]
    omega
  change (C p).card = 3 at pThree
  change (C q).card = 3 at qThree
  change C p ∪ C q = Finset.univ at union
  have sum := Finset.card_union_add_card_inter (C p) (C q)
  rw [union,Finset.card_univ,Fintype.card_fin,pThree,qThree] at sum
  have emptyInter : (C p ∩ C q).card = 0 := by omega
  have apart := Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp emptyInter)
  have diff : p ≠ q := by
    intro equal
    rw [equal,Finset.inter_self,qThree] at emptyInter
    omega
  obtain ⟨t,_,_,empty⟩ := third_point_for_disjoint_heavy_support M rowPairs colPairs bSizes cSizes
    C loc p q diff apart
  rw [union] at empty
  have in_use : t ∈ used := allUsed ▸ Finset.mem_univ _
  have found := Finset.card_pos.mp ((Finset.mem_filter.mp in_use).2)
  obtain ⟨a,ha⟩ := found
  exact Finset.disjoint_left.mp empty ha (Finset.mem_univ _)
