import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H4_R1_H2_R1_H3_R1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Choose.Basic

open Finset
open scoped BigOperators

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

theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H4_R1_H2_R1_H3_R1.H1 := by
  classical
  unfold OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H4_R1_H2_R1_H3_R1.H1
  dsimp only
  rintro ⟨M,_,_,rowPairs,colPairs,aSizes,bSizes,cSizes,inside,_,U,hu,four,noTriple,eight,covered⟩
  let A (a : Fin 6) (p : Fin 19) := M (.inl a) (.inl p)
  let C (p : Fin 19) := Finset.univ.filter fun a : Fin 6 => A a p = true
  let F := (Finset.univ.filter fun p => 2 ≤ (C p).card).image C
  let Pairs := F.filter fun T => T.card = 2
  have count8 : Pairs.card = 8 := eight
  let used := Finset.univ.filter fun p => 0 < (C p).card
  have loc (p : Fin 19) (a : Fin 6) : a ∈ C p ↔ A a p = true := by simp [C]
  have at_most (p : Fin 19) : (C p).card ≤ 4 := by
    have seen := inside p
    change _ + 2 * (C p).card = 9 at seen
    omega
  have overlap (p q : Fin 19) (different : p ≠ q) : (C p ∩ C q).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have on_both (x : Fin 6) (hx : x ∈ C p ∩ C q) : A x p = true ∧ A x q = true := by
      obtain ⟨hp,hq⟩ := Finset.mem_inter.mp hx
      exact ⟨(loc p x).mp hp,(loc q x).mp hq⟩
    obtain ⟨_,_,same⟩ := colPairs (.inl p) (.inl q) (fun e => different (Sum.inl.inj e))
    exact Sum.inl.inj ((same (.inl a) (on_both a ha)).trans (same (.inl b) (on_both b hb)).symm)
  have sizes (T : Finset (Fin 6)) (ht : T ∈ F) : 2 ≤ T.card ∧ T.card ≤ 4 := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
    exact ⟨(Finset.mem_filter.mp hp).2,at_most p⟩
  have uniq (T : Finset (Fin 6)) (ht : T ∈ F) (tFour : T.card = 4) : T = U := by
    by_contra different
    have small : (T ∩ U).card ≤ 1 := by
      obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨q,_,same⟩ := Finset.mem_image.mp hu
      rw [← same]
      exact overlap p q (fun equal => different ((congrArg C equal).trans same))
    have sum := Finset.card_union_add_card_inter T U
    have bound : (T ∪ U).card ≤ 6 :=
      (Finset.card_le_card (Finset.subset_univ _)).trans_eq (Fintype.card_fin _)
    omega
  have residue : F.erase U = Pairs := by
    ext T
    simp only [Pairs, Finset.mem_erase, Finset.mem_filter]
    constructor
    · rintro ⟨ne,ht⟩
      refine ⟨ht,?_⟩
      have ⟨lo,hi⟩ := sizes T ht
      have n3 := noTriple T ht
      have n4 : T.card ≠ 4 := fun eq => ne (uniq T ht eq)
      omega
    · rintro ⟨ht,two⟩
      refine ⟨?_,ht⟩
      intro eq
      rw [eq,four] at two
      omega
  have sumPairs : (∑ T ∈ Pairs, (T.card - 1)) = Pairs.card := by
    calc
      _ = ∑ _T ∈ Pairs, 1 := by
        apply Finset.sum_congr rfl
        intro T ht
        rw [(Finset.mem_filter.mp ht).2]
      _ = _ := by simp
  have sum := Finset.sum_erase_add F (fun T => T.card - 1) hu
  rw [residue,sumPairs,count8,four] at sum
  have usedCount : used.card + ∑ T ∈ F, (T.card - 1) = 30 :=
    layout_counts C (layout_total A C (fun _ => rfl) aSizes) overlap
  have allUsed : used = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ,Fintype.card_fin]
    omega
  have nonempty (p : Fin 19) : (C p).Nonempty := by
    apply Finset.card_pos.mp
    have hp : p ∈ used := allUsed ▸ Finset.mem_univ _
    exact (Finset.mem_filter.mp hp).2
  obtain ⟨p,_,point⟩ := Finset.mem_image.mp hu
  obtain ⟨q,_,other⟩ := Finset.mem_image.mp (Finset.mem_filter.mp covered).1
  change C p = U at point
  change C q = Finset.univ \ U at other
  have q_two : (C q).card = 2 := other.symm ▸ (Finset.mem_filter.mp covered).2
  have ne : p ≠ q := by
    intro same
    rw [← same,point,four] at q_two
    omega
  obtain ⟨l,hl,_⟩ := colPairs (.inl p) (.inl q) (fun e => ne (Sum.inl.inj e))
  have noHeavy (a : Fin 6) (hp : A a p = true) (hq : A a q = true) : False := by
    have hp' := (loc p a).mpr hp
    have hq' := (loc q a).mpr hq
    rw [point] at hp'
    rw [other] at hq'
    exact (Finset.mem_sdiff.mp hq').2 hp'
  cases l with
  | inl a => exact noHeavy a hl.1 hl.2
  | inr l =>
    cases l with
    | inr c =>
      let onLine := Finset.univ.filter fun x : Fin 19 => M (.inr (.inr c)) (.inl x) = true
      have one : onLine.card ≤ 1 := (cSizes c).le
      exact ne (Finset.card_le_one.mp one p (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl.1⟩)
        q (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl.2⟩))
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
      obtain ⟨a,belongs⟩ := nonempty t
      have tOnA := (loc t a).mp belongs
      obtain ⟨_,_,unique⟩ := rowPairs (.inl a) (.inr (.inl b)) (by simp)
      by_cases inU : a ∈ U
      · have onA : A a p = true := (loc p a).mp (point.symm ▸ inU)
        exact tp (Sum.inl.inj ((unique (.inl t) ⟨tOnA,tOnB⟩).trans
          (unique (.inl p) ⟨onA,hl.1⟩).symm))
      · have outside : a ∈ Finset.univ \ U := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,inU⟩
        have onA : A a q = true := (loc q a).mp (other.symm ▸ outside)
        exact tq (Sum.inl.inj ((unique (.inl t) ⟨tOnA,tOnB⟩).trans
          (unique (.inl q) ⟨onA,hl.2⟩).symm))
