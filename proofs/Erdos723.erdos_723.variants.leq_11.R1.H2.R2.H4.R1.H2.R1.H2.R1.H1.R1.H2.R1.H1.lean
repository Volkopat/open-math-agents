import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1_H1_R1_H2_R1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-! Classify the marked supports with one triple by explicit relabeling witnesses. -/

namespace WeightNineteenSupportRelabel

open Finset
open scoped BigOperators

abbrev Columns := Fin 19 → Finset (Fin 6)

def shared (C : Columns) : Finset (Fin 19) :=
  Finset.univ.filter fun p => 2 ≤ (C p).card

def layout (C : Columns) : Finset (Finset (Fin 6)) :=
  (shared C).image C

def fiber (C : Columns) (s : Finset (Fin 6)) : Finset (Fin 19) :=
  Finset.univ.filter fun p => C p = s

lemma mem_fiber (C : Columns) (s : Finset (Fin 6)) (p : Fin 19) :
    p ∈ fiber C s ↔ C p = s := by simp [fiber]

lemma injective_shared (C : Columns)
    (overlap : ∀ p q, p ≠ q → (C p ∩ C q).card ≤ 1) :
    (shared C : Set (Fin 19)).InjOn C := by
  intro p hp q hq same
  by_contra different
  have small := overlap p q different
  rw [same,Finset.inter_self] at small
  have many := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2
  omega

lemma high_fiber (C : Columns)
    (overlap : ∀ p q, p ≠ q → (C p ∩ C q).card ≤ 1)
    (s : Finset (Fin 6)) (many : 2 ≤ s.card) :
    (fiber C s).card = if s ∈ layout C then 1 else 0 := by
  by_cases yes : s ∈ layout C
  · rw [if_pos yes]
    obtain ⟨p,hp,eq⟩ := Finset.mem_image.mp yes
    apply Finset.card_eq_one.mpr
    refine ⟨p,?_⟩
    ext q
    rw [mem_fiber,Finset.mem_singleton]
    constructor
    · intro hs
      have hq : q ∈ shared C := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs.symm ▸ many⟩
      exact injective_shared C overlap hq hp (hs.trans eq.symm)
    · rintro rfl
      exact eq
  · rw [if_neg yes]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_of_forall_notMem
    intro p hp
    have hs := (mem_fiber C s p).mp hp
    have here : p ∈ shared C := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs.symm ▸ many⟩
    exact yes (hs ▸ Finset.mem_image_of_mem C here)

lemma single_fiber (C : Columns)
    (overlap : ∀ p q, p ≠ q → (C p ∩ C q).card ≤ 1)
    (a : Fin 6) :
    (fiber C {a}).card + ((layout C).filter fun s => a ∈ s).card =
      (Finset.univ.filter fun p => a ∈ C p).card := by
  let high := (shared C).filter fun p => a ∈ C p
  have image_high : high.image C = (layout C).filter fun s => a ∈ s := by
    ext s
    constructor
    · rintro hs
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨sharedp,one⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ sharedp,one⟩
    · rintro hs
      obtain ⟨in_layout,one⟩ := Finset.mem_filter.mp hs
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp in_layout
      exact Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,one⟩,rfl⟩
  have inj : (high : Set (Fin 19)).InjOn C := by
    intro p hp q hq same
    exact injective_shared C overlap (Finset.filter_subset _ _ hp) (Finset.filter_subset _ _ hq) same
  have high_count := Finset.card_image_of_injOn inj
  rw [image_high] at high_count
  have apart : Disjoint (fiber C {a}) high := by
    rw [Finset.disjoint_left]
    intro p hf hp
    have hs := (mem_fiber C {a} p).mp hf
    have many := (Finset.mem_filter.mp ((Finset.mem_filter.mp hp).1)).2
    rw [hs,Finset.card_singleton] at many
    omega
  have cover : fiber C {a} ∪ high = Finset.univ.filter fun p => a ∈ C p := by
    ext p
    rw [Finset.mem_union, mem_fiber]
    have hit : p ∈ (Finset.univ.filter fun p => a ∈ C p) ↔ a ∈ C p := by simp
    rw [hit]
    constructor
    · rintro (one | above)
      · rw [one]
        simp
      · exact (Finset.mem_filter.mp above).2
    · intro on_a
      by_cases many : 2 ≤ (C p).card
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ p,many⟩,on_a⟩)
      · apply Or.inl
        symm
        apply Finset.eq_of_subset_of_card_le ((Finset.singleton_subset_iff).mpr on_a)
        rw [Finset.card_singleton]
        omega
  rw [high_count,← Finset.card_union_of_disjoint apart,cover]

lemma sum_fibers (C : Columns) : (∑ s : Finset (Fin 6), (fiber C s).card) = 19 := by
  calc
    _ = ∑ s : Finset (Fin 6), ∑ p : Fin 19, if C p = s then (1 : Nat) else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      rw [← Finset.sum_filter]
      simp [fiber]
    _ = ∑ p : Fin 19, ∑ s : Finset (Fin 6), if C p = s then (1 : Nat) else 0 := Finset.sum_comm
    _ = 19 := by simp [eq_comm]

theorem relabel_columns (C D : Columns)
    (c_overlap : ∀ p q, p ≠ q → (C p ∩ C q).card ≤ 1)
    (d_overlap : ∀ p q, p ≠ q → (D p ∩ D q).card ≤ 1)
    (c_row : ∀ a, (Finset.univ.filter fun p => a ∈ C p).card = 5)
    (d_row : ∀ a, (Finset.univ.filter fun p => a ∈ D p).card = 5)
    (same : layout C = layout D) :
    ∃ e : Equiv.Perm (Fin 19), ∀ p, D (e p) = C p := by
  classical
  have counts_ne (s : Finset (Fin 6)) (nonzero : s ≠ ∅) : (fiber C s).card = (fiber D s).card := by
    by_cases large : 2 ≤ s.card
    · rw [high_fiber C c_overlap s large,high_fiber D d_overlap s large,same]
    · have pos : 0 < s.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr nonzero)
      obtain ⟨a,rfl⟩ := Finset.card_eq_one.mp (by omega : s.card = 1)
      have left := single_fiber C c_overlap a
      have right := single_fiber D d_overlap a
      rw [same,c_row] at left
      rw [d_row] at right
      omega
  have all_counts (s : Finset (Fin 6)) : (fiber C s).card = (fiber D s).card := by
    by_cases zero : s = ∅
    · subst s
      let nonempty := (Finset.univ : Finset (Finset (Fin 6))).erase ∅
      have agree : (∑ s ∈ nonempty, (fiber C s).card) = ∑ s ∈ nonempty, (fiber D s).card := by
        apply Finset.sum_congr rfl
        intro s hs
        exact counts_ne s (Finset.ne_of_mem_erase hs)
      have hc := Finset.sum_erase_add Finset.univ (fun s => (fiber C s).card) (Finset.mem_univ ∅)
      have hd := Finset.sum_erase_add Finset.univ (fun s => (fiber D s).card) (Finset.mem_univ ∅)
      rw [sum_fibers] at hc hd
      change (∑ s ∈ nonempty, (fiber C s).card) + (fiber C ∅).card = 19 at hc
      change (∑ s ∈ nonempty, (fiber D s).card) + (fiber D ∅).card = 19 at hd
      omega
    · exact counts_ne s zero
  let match_card (s : Finset (Fin 6)) : Fintype.card ↥(fiber C s) = Fintype.card ↥(fiber D s) := by
    rw [Fintype.card_coe,Fintype.card_coe,all_counts]
  let fibers (s : Finset (Fin 6)) : ↥(fiber C s) ≃ ↥(fiber D s) :=
    (Fintype.equivOfCardEq (match_card s))
  let as_fiber (W : Columns) (s : Finset (Fin 6)) : {p // W p = s} ≃ ↥(fiber W s) :=
    Equiv.subtypeEquivProp (funext fun p => propext (mem_fiber W s p).symm)
  let mapped (s : Finset (Fin 6)) : {p // C p = s} ≃ {p // D p = s} :=
    ((as_fiber C s).trans (fibers s)).trans (as_fiber D s).symm
  let e : Equiv.Perm (Fin 19) :=
    (Equiv.sigmaFiberEquiv C).symm.trans
      ((Equiv.sigmaCongrRight mapped).trans (Equiv.sigmaFiberEquiv D))
  exact ⟨e,fun p => (mapped (C p) ⟨p,rfl⟩).property⟩

def supportMask (X : Finset (Fin 6)) : Nat := ∑ a ∈ X, 2^a.val

def moveRows (C : Columns) (e : Equiv.Perm (Fin 6)) : Columns :=
  fun p => (C p).map e.toEmbedding

lemma row_bounds_after_permutation (C : Columns)
    (rows : ∀ a, (Finset.univ.filter fun p => a ∈ C p).card = 5)
    (e : Equiv.Perm (Fin 6)) (a : Fin 6) :
    (Finset.univ.filter fun p => a ∈ moveRows C e p).card = 5 := by
  have same : (Finset.univ.filter fun p => a ∈ moveRows C e p) =
      Finset.univ.filter fun p => e.symm a ∈ C p := by
    ext p
    simp only [moveRows,Finset.mem_filter,Finset.mem_map_equiv]
  rw [same,rows]

lemma overlap_after_permutation (C : Columns)
    (pairwise : ∀ p q, p ≠ q → (C p ∩ C q).card ≤ 1)
    (e : Equiv.Perm (Fin 6)) (p q : Fin 19) (ne : p ≠ q) :
    (moveRows C e p ∩ moveRows C e q).card ≤ 1 := by
  have same : moveRows C e p ∩ moveRows C e q = (C p ∩ C q).map e.toEmbedding := by
    ext a
    simp only [moveRows,Finset.mem_inter,Finset.mem_map_equiv]
  rw [same,Finset.card_map]
  exact pairwise p q ne

lemma layout_after_permutation (C : Columns) (e : Equiv.Perm (Fin 6)) :
    layout (moveRows C e) = (layout C).image (Finset.map e.toEmbedding) := by
  have same : shared (moveRows C e) = shared C := by
    ext p
    simp only [shared,Finset.mem_filter,moveRows,Finset.card_map]
  unfold layout
  rw [same,Finset.image_image]
  rfl

end WeightNineteenSupportRelabel


open Finset WeightNineteenSupportRelabel
open scoped BigOperators

private abbrev Support := Finset (Fin 6)
private abbrev Family := Finset Support

def codeMap (code : Nat) (a : Fin 6) : Fin 6 :=
  ⟨((code >>> (3*a.val)) &&& 7) % 6, Nat.mod_lt _ (by decide)⟩

def move (code : Nat) (F : Family) : Family := F.image (Finset.image (codeMap code))

inductive Witness where
  | leaf (code : Nat)
  | fork (bound : Nat) (lower upper : Witness)

def lookup (key : Nat) : Witness → Nat
  | .leaf code => code
  | .fork bound lo hi => if key < bound then lookup key lo else lookup key hi
lemma image_of_injective {X Y : Type} [DecidableEq Y] (f : X ↪ Y)
    [DecidableEq X] (A : Finset X) : A.image f = A.map f := by
  exact (Finset.map_eq_image _ _).symm

lemma moved_family (code : Nat) (injective : Function.Injective (codeMap code)) :
    ∃ e : Equiv.Perm (Fin 6), ∀ F : Family,
      move code F = F.image (Finset.map e.toEmbedding) := by
  let e := Equiv.ofBijective (codeMap code) ((Finite.injective_iff_bijective).mp injective)
  refine ⟨e,?_⟩
  intro F
  apply Finset.image_congr
  intro S _
  exact image_of_injective e.toEmbedding S

lemma first_triple_map (S : Support) (size : S.card = 3) :
    ∃ e : Equiv.Perm (Fin 6), S.map e.toEmbedding = {0,1,2} := by
  classical
  let t := Finset.univ \ S
  have card_t : t.card = 3 := by
    change (Finset.univ \ S).card = 3
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S),Finset.card_univ,Fintype.card_fin,size]
  let left : Fin 3 ≃ ↥S := (Fintype.equivFinOfCardEq (by rwa [Fintype.card_coe])).symm
  let right : Fin 3 ≃ ↥t := (Fintype.equivFinOfCardEq (by rwa [Fintype.card_coe])).symm
  let asComplement : ↥t ≃ {i // i ∉ S} :=
    Equiv.subtypeEquivProp (funext fun i => propext (by simp [t]))
  let pack := (Equiv.sumCongr left (right.trans asComplement)).trans (Equiv.sumCompl (· ∈ S))
  let fromSum : Fin 3 ⊕ Fin 3 ≃ Fin 6 := finSumFinEquiv
  let e : Equiv.Perm (Fin 6) := pack.symm.trans fromSum
  have form (y : Fin 6) : y ∈ S ↔ (e y).val < 3 := by
    let z := pack.symm y
    have yz : pack z = y := pack.apply_symm_apply _
    change y ∈ S ↔ (fromSum z).val < 3
    cases found : z with
    | inl a =>
      have ya : y = (left a).val := yz.symm.trans (by rw [found]; rfl)
      exact ⟨fun _ => a.isLt, fun _ => ya.symm ▸ (left a).property⟩
    | inr a =>
      have ya : y = (right a).val := yz.symm.trans (by rw [found]; rfl)
      have absent : y ∉ S := fun yes => (Finset.mem_sdiff.mp (right a).property).2 (ya ▸ yes)
      have large : ¬ (fromSum (.inr a)).val < 3 := by
        change ¬ (3 + a.val) < 3
        omega
      exact ⟨fun yes => (absent yes).elim, fun small => (large small).elim⟩
  have known : ∀ y : Fin 6, y.val < 3 ↔ y ∈ ({0,1,2} : Support) := by decide +kernel
  refine ⟨e,?_⟩
  ext y
  rw [Finset.mem_map_equiv,form,e.apply_symm_apply,known]

lemma map_support_overlap (e : Equiv.Perm (Fin 6)) (S U : Support) :
    (S.map e.toEmbedding ∩ U.map e.toEmbedding).card = (S ∩ U).card := by
  have both : S.map e.toEmbedding ∩ U.map e.toEmbedding = (S ∩ U).map e.toEmbedding := by
    ext a
    simp only [Finset.mem_inter,Finset.mem_map_equiv]
  simp only [both,Finset.card_map]

lemma compose_moves (e f : Equiv.Perm (Fin 6)) (F : Family) :
    (F.image (Finset.map e.toEmbedding)).image (Finset.map f.toEmbedding) =
      F.image (Finset.map (e.trans f).toEmbedding) := by
  rw [Finset.image_image]
  apply Finset.image_congr
  intro S _
  rw [Function.comp_apply,Finset.map_map]
  rfl



private def concrete (i : Fin 18) (p : Fin 19) : Finset (Fin 6) :=
  ((([[[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [2, 3], [0, 4], [1, 4], [2, 4], [3, 4, 5], [0], [1], [2], [3], [4], [5], [5], [5], [5]],
   [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [2, 3], [0, 4], [1, 4], [2, 5], [3, 4, 5], [0], [1], [2], [3], [4], [4], [5], [5], [5]],
   [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [0, 4], [1, 4], [2, 3, 4], [2, 5], [3, 5], [0], [1], [2], [3], [4], [4], [5], [5], [5]],
   [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [0, 4], [2, 4], [3, 4], [0, 5], [2, 3, 5], [1], [1], [2], [3], [4], [4], [5], [5], [5]],
   [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [0, 4], [2, 4], [3, 4], [1, 5], [2, 3, 5], [0], [1], [2], [3], [4], [4], [5], [5], [5]],
   [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [0, 4], [2, 4], [0, 5], [3, 5], [1, 4, 5], [1], [2], [2], [3], [3], [4], [4], [5], [5]],
   [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [0, 4], [2, 4], [1, 5], [2, 5], [3, 4, 5], [0], [1], [2], [3], [3], [4], [4], [5], [5]],
   [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [0, 4], [2, 4], [1, 5], [2, 3, 5], [4, 5], [0], [1], [2], [3], [3], [4], [4], [5], [5]],
   [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [0, 4], [2, 3, 4], [2, 5], [3, 5], [4, 5], [0], [1], [1], [2], [3], [4], [4], [5], [5]],
   [[0, 1], [0, 2], [0, 3], [1, 2, 3], [1, 4], [2, 4], [3, 4], [1, 5], [2, 5], [3, 5], [0], [0], [1], [2], [3], [4], [4], [5], [5]],
   [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [2, 3], [0, 4], [1, 4], [2, 4], [0, 5], [3, 4, 5], [1], [2], [3], [4], [5], [5], [5], []],
   [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [2, 3], [0, 4], [1, 4], [0, 5], [2, 5], [3, 4, 5], [1], [2], [3], [4], [4], [5], [5], []],
   [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [0, 4], [1, 4], [2, 3, 4], [0, 5], [2, 5], [3, 5], [1], [2], [3], [4], [4], [5], [5], []],
   [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [0, 4], [1, 4], [2, 3, 4], [2, 5], [3, 5], [4, 5], [0], [1], [2], [3], [4], [5], [5], []],
   [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [0, 4], [2, 4], [3, 4], [1, 5], [2, 3, 5], [4, 5], [0], [1], [2], [3], [4], [5], [5], []],
   [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [2, 3], [0, 4], [1, 4], [2, 4], [0, 5], [1, 5], [3, 4, 5], [2], [3], [4], [5], [5], [], []],
   [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [0, 4], [1, 4], [2, 3, 4], [0, 5], [2, 5], [3, 5], [4, 5], [1], [2], [3], [4], [5], [], []],
   [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [2, 3], [0, 4], [1, 4], [2, 4], [0, 5], [1, 5], [2, 5], [3, 4, 5], [3], [4], [5], [], [], []]] : List (List (List (Fin 6))))[i.val]!)[p.val]!).toFinset

private def forbiddenMasks : List (List Nat) := [[3, 5, 6, 9, 10, 12, 17, 18, 33, 34, 52], [3, 5, 6, 9, 10, 12, 17, 18, 33, 52], [3, 5, 6, 9, 10, 17, 18, 28, 33, 34], [3, 5, 6, 9, 10, 17, 18, 28, 33, 36], [3, 5, 6, 9, 10, 17, 18, 33, 36, 56], [3, 5, 6, 9, 10, 20, 24, 36, 40, 49]]

private def forbiddenFamily (i : Fin 6) : Family :=
  (([[[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [2, 3], [0, 4], [1, 4], [0, 5], [1, 5], [2, 4, 5]], [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [2, 3], [0, 4], [1, 4], [0, 5], [2, 4, 5]], [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [0, 4], [1, 4], [2, 3, 4], [0, 5], [1, 5]], [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [0, 4], [1, 4], [2, 3, 4], [0, 5], [2, 5]], [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [0, 4], [1, 4], [0, 5], [2, 5], [3, 4, 5]], [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [2, 4], [3, 4], [2, 5], [3, 5], [0, 4, 5]]] : List (List (List (Fin 6))))[i.val]!.map List.toFinset).toFinset

private def orbitFamily (i : Fin 24) : Family :=
  if h : i.val < 6 then forbiddenFamily ⟨i.val, h⟩
  else layout (concrete ⟨i.val - 6, by omega⟩)

private def anchor : Support := {0,1,2}

private def admissible : Family := (univ : Support).powersetCard 2 \ anchor.powersetCard 2

private def familyMask (F : Family) : Nat := ∑ T ∈ F, 2^(supportMask T)

private def table : Witness := (.fork 0x1010601060680 (.fork 0x1000601161280 (.fork 0x11401161680 (.fork 0x10601161280 (.fork 0x1601161480 (.fork 0x1601061680 (.fork 0x1401161680 (.fork 0x1201161680 (.leaf 0x3d9a78) (.leaf 0x3d9538)) (.fork 0x1600161680 (.leaf 0x3d93e8) (.leaf 0x4213a7))) (.fork 0x1601141680 (.fork 0x1601121680 (.leaf 0x3d9a7e) (.leaf 0x3d953e)) (.fork 0x1601160680 (.leaf 0x3d93ee) (.fork 0x1601161280 (.leaf 0x3c4a7e) (.leaf 0x3c453e))))) (.fork 0x10600161680 (.fork 0x10201161680 (.fork 0x1601161680 (.leaf 0x3c43ee) (.leaf 0x3d9a83)) (.fork 0x10401161680 (.leaf 0x3d9a73) (.leaf 0x3d99cb))) (.fork 0x10601121680 (.fork 0x10601061680 (.leaf 0x139a7e) (.leaf 0x31a079)) (.fork 0x10601141680 (.leaf 0x271be3) (.fork 0x10601160680 (.leaf 0x271943) (.leaf 0x31a07a)))))) (.fork 0x11201161280 (.fork 0x11200161680 (.fork 0x10601161680 (.fork 0x10601161480 (.leaf 0x3195fd) (.leaf 0x319405)) (.fork 0x11001161680 (.leaf 0x3d9a82) (.leaf 0x3d8f4b))) (.fork 0x11201121680 (.fork 0x11201061680 (.leaf 0x13953e) (.leaf 0x272123)) (.fork 0x11201141680 (.leaf 0x3195f9) (.fork 0x11201160680 (.leaf 0x270983) (.leaf 0x31a07d))))) (.fork 0x11401121680 (.fork 0x11201161680 (.fork 0x11201161480 (.leaf 0x3195fa) (.leaf 0x318ec5)) (.fork 0x11400161680 (.leaf 0x3d9542) (.fork 0x11401061680 (.leaf 0x1393ee) (.leaf 0x271f2b)))) (.fork 0x11401160680 (.fork 0x11401141680 (.leaf 0x270a2b) (.leaf 0x319401)) (.fork 0x11401161280 (.leaf 0x319fd5) (.fork 0x11401161480 (.leaf 0x319015) (.leaf 0x319402))))))) (.fork 0x11601121680 (.fork 0x11601041680 (.fork 0x11600160680 (.fork 0x11600121680 (.fork 0x11600061680 (.leaf 0x3d93f2) (.leaf 0x139a78)) (.fork 0x11600141680 (.leaf 0x139538) (.leaf 0x1393e8))) (.fork 0x11600161480 (.fork 0x11600161280 (.leaf 0x7ca7e) (.leaf 0x7c53e)) (.fork 0x11600161680 (.leaf 0x7c3ee) (.fork 0x11601021680 (.leaf 0x139a83) (.leaf 0x139a73))))) (.fork 0x11601061680 (.fork 0x11601061280 (.fork 0x11601060680 (.leaf 0x1399cb) (.leaf 0x12207a)) (.fork 0x11601061480 (.leaf 0x1215fd) (.leaf 0x121405))) (.fork 0x11601120680 (.fork 0x11601101680 (.leaf 0x139a82) (.leaf 0x138f4b)) (.fork 0x11601121280 (.leaf 0x12207d) (.fork 0x11601121480 (.leaf 0x1215fa) (.leaf 0x120ec5)))))) (.fork 0x11601161280 (.fork 0x11601141680 (.fork 0x11601141280 (.fork 0x11601140680 (.leaf 0x139542) (.leaf 0x121fd5)) (.fork 0x11601141480 (.leaf 0x121015) (.leaf 0x121402))) (.fork 0x11601160480 (.fork 0x11601160280 (.leaf 0x1393f2) (.leaf 0x275105)) (.fork 0x11601160680 (.leaf 0x274e65) (.fork 0x11601161080 (.leaf 0x31a084) (.leaf 0x273425))))) (.fork 0x1000600161680 (.fork 0x11601161680 (.fork 0x11601161480 (.leaf 0x319604) (.leaf 0x31940c)) (.fork 0x1000201161680 (.leaf 0x3d9a86) (.fork 0x1000401161680 (.leaf 0x3c4a73) (.leaf 0x3c49cb)))) (.fork 0x1000601121680 (.fork 0x1000601061680 (.leaf 0xd0a7e) (.leaf 0x30507a)) (.fork 0x1000601141680 (.leaf 0x3045fd) (.fork 0x1000601160680 (.leaf 0x304405) (.leaf 0x305079)))))))) (.fork 0x1001601121680 (.fork 0x1001401161480 (.fork 0x1001201161280 (.fork 0x1001200161680 (.fork 0x1000601161680 (.fork 0x1000601161480 (.leaf 0x247be3) (.leaf 0x247943)) (.fork 0x1001001161680 (.leaf 0x3c4a82) (.leaf 0x3c3f4b))) (.fork 0x1001201121680 (.fork 0x1001201061680 (.leaf 0xd053e) (.leaf 0x30507d)) (.fork 0x1001201141680 (.leaf 0x3045fa) (.fork 0x1001201160680 (.leaf 0x303ec5) (.leaf 0x248123))))) (.fork 0x1001401061680 (.fork 0x1001201161680 (.fork 0x1001201161480 (.leaf 0x3045f9) (.leaf 0x246983)) (.fork 0x1001400161680 (.leaf 0x3c4542) (.leaf 0xd03ee))) (.fork 0x1001401141680 (.fork 0x1001401121680 (.leaf 0x304fd5) (.leaf 0x304015)) (.fork 0x1001401160680 (.leaf 0x304402) (.fork 0x1001401161280 (.leaf 0x247f2b) (.leaf 0x246a2b)))))) (.fork 0x1001601021680 (.fork 0x1001600141680 (.fork 0x1001600061680 (.fork 0x1001401161680 (.leaf 0x304401) (.leaf 0x3c43f2)) (.fork 0x1001600121680 (.leaf 0x28a7e) (.leaf 0x2853e))) (.fork 0x1001600161280 (.fork 0x1001600160680 (.leaf 0x283ee) (.leaf 0xd0a78)) (.fork 0x1001600161480 (.leaf 0xd0538) (.fork 0x1001600161680 (.leaf 0xd03e8) (.leaf 0xd0a83))))) (.fork 0x1001601061680 (.fork 0x1001601060680 (.fork 0x1001601041680 (.leaf 0x260105) (.leaf 0x25fe65)) (.fork 0x1001601061280 (.leaf 0xce07a) (.fork 0x1001601061480 (.leaf 0xce07d) (.leaf 0xcdfd5)))) (.fork 0x1001601120680 (.fork 0x1001601101680 (.leaf 0x305084) (.leaf 0x25e425)) (.fork 0x1001601121280 (.leaf 0xcd5fd) (.fork 0x1001601121480 (.leaf 0xcd5fa) (.leaf 0xcd015))))))) (.fork 0x1010201161480 (.fork 0x1001601161280 (.fork 0x1001601141680 (.fork 0x1001601141280 (.fork 0x1001601140680 (.leaf 0x304604) (.leaf 0xcd405)) (.fork 0x1001601141480 (.leaf 0xccec5) (.leaf 0xcd402))) (.fork 0x1001601160480 (.fork 0x1001601160280 (.leaf 0x30440c) (.leaf 0xd0a73)) (.fork 0x1001601160680 (.leaf 0xd09cb) (.fork 0x1001601161080 (.leaf 0xd0a82) (.leaf 0xcff4b))))) (.fork 0x1010201061680 (.fork 0x1001601161680 (.fork 0x1001601161480 (.leaf 0xd0542) (.leaf 0xd03f2)) (.fork 0x1010001161680 (.leaf 0x3c4a86) (.fork 0x1010200161680 (.leaf 0x3d9a72) (.leaf 0x110105)))) (.fork 0x1010201141680 (.fork 0x1010201121680 (.leaf 0x25a131) (.leaf 0x259bf1)) (.fork 0x1010201160680 (.leaf 0x199abc) (.fork 0x1010201161280 (.leaf 0x245131) (.leaf 0x244bf1)))))) (.fork 0x1010401161680 (.fork 0x1010401121680 (.fork 0x1010400161680 (.fork 0x1010201161680 (.leaf 0x184abc) (.leaf 0x25a130)) (.fork 0x1010401061680 (.leaf 0x10fe65) (.leaf 0x259fe1))) (.fork 0x1010401160680 (.fork 0x1010401141680 (.leaf 0x199c0c) (.leaf 0x2599f9)) (.fork 0x1010401161280 (.leaf 0x244fe1) (.fork 0x1010401161480 (.leaf 0x184c0c) (.leaf 0x2449f9))))) (.fork 0x1010600161280 (.fork 0x1010600121680 (.fork 0x1010600061680 (.leaf 0x259fe0) (.leaf 0x6507a)) (.fork 0x1010600141680 (.leaf 0x6507d) (.fork 0x1010600160680 (.leaf 0x64fd5) (.leaf 0x2607a)))) (.fork 0x1010600161680 (.fork 0x1010600161480 (.leaf 0x2607d) (.leaf 0x25fd5)) (.fork 0x1010601021680 (.leaf 0x65084) (.fork 0x1010601041680 (.leaf 0x10a131) (.leaf 0x109fe1))))))))) (.fork 0x1011401140680 (.fork 0x1011201060680 (.fork 0x1010601161480 (.fork 0x1010601140680 (.fork 0x1010601101680 (.fork 0x1010601061480 (.fork 0x1010601061280 (.leaf 0x19a14e) (.leaf 0xc814f)) (.fork 0x1010601061680 (.leaf 0xc80a7) (.leaf 0x19a158))) (.fork 0x1010601121280 (.fork 0x1010601120680 (.leaf 0xf214c) (.leaf 0xf214f)) (.fork 0x1010601121480 (.leaf 0x199c0f) (.fork 0x1010601121680 (.leaf 0x199584) (.leaf 0x199c19))))) (.fork 0x1010601160280 (.fork 0x1010601141480 (.fork 0x1010601141280 (.leaf 0xf20a7) (.leaf 0x19962c)) (.fork 0x1010601141680 (.leaf 0x199abf) (.leaf 0x199ac9))) (.fork 0x1010601160680 (.fork 0x1010601160480 (.leaf 0xcb131) (.leaf 0xcafe1)) (.fork 0x1010601161080 (.leaf 0x185158) (.fork 0x1010601161280 (.leaf 0xc814c) (.leaf 0x184c19)))))) (.fork 0x1011001161680 (.fork 0x1011001121680 (.fork 0x1011000161680 (.fork 0x1010601161680 (.leaf 0x184ac9) (.leaf 0x19a15d)) (.fork 0x1011001061680 (.leaf 0x10e425) (.leaf 0x19a14c))) (.fork 0x1011001160680 (.fork 0x1011001141680 (.leaf 0x259021) (.leaf 0x258f79)) (.fork 0x1011001161280 (.leaf 0x18514c) (.fork 0x1011001161480 (.leaf 0x244021) (.leaf 0x243f79))))) (.fork 0x1011200161280 (.fork 0x1011200121680 (.fork 0x1011200061680 (.leaf 0x259020) (.leaf 0x645fd)) (.fork 0x1011200141680 (.leaf 0x645fa) (.fork 0x1011200160680 (.leaf 0x64015) (.leaf 0x255fd)))) (.fork 0x1011200161680 (.fork 0x1011200161480 (.leaf 0x255fa) (.leaf 0x25015)) (.fork 0x1011201021680 (.leaf 0x64604) (.fork 0x1011201041680 (.leaf 0x109bf1) (.leaf 0xf1c0c))))))) (.fork 0x1011201161680 (.fork 0x1011201140680 (.fork 0x1011201101680 (.fork 0x1011201061480 (.fork 0x1011201061280 (.leaf 0x19a14f) (.leaf 0xf1c0f)) (.fork 0x1011201061680 (.leaf 0x199ac4) (.leaf 0x19a159))) (.fork 0x1011201121280 (.fork 0x1011201120680 (.leaf 0x109021) (.leaf 0xc7c0f)) (.fork 0x1011201121480 (.leaf 0x199c0e) (.fork 0x1011201121680 (.leaf 0xc7627) (.leaf 0x199c18))))) (.fork 0x1011201160480 (.fork 0x1011201141480 (.fork 0x1011201141280 (.leaf 0x19a0ac) (.leaf 0xf1627)) (.fork 0x1011201141680 (.leaf 0x19957f) (.fork 0x1011201160280 (.leaf 0x199589) (.leaf 0xcabf1)))) (.fork 0x1011201161080 (.fork 0x1011201160680 (.leaf 0xc7c0c) (.leaf 0x185159)) (.fork 0x1011201161280 (.leaf 0xca021) (.fork 0x1011201161480 (.leaf 0x184c18) (.leaf 0x184589)))))) (.fork 0x1011401041680 (.fork 0x1011400160680 (.fork 0x1011400121680 (.fork 0x1011400061680 (.leaf 0x199c1d) (.leaf 0x64405)) (.fork 0x1011400141680 (.leaf 0x63ec5) (.leaf 0x64402))) (.fork 0x1011400161480 (.fork 0x1011400161280 (.leaf 0x25405) (.leaf 0x24ec5)) (.fork 0x1011400161680 (.leaf 0x25402) (.fork 0x1011401021680 (.leaf 0x6440c) (.leaf 0xf1abc))))) (.fork 0x1011401101680 (.fork 0x1011401061280 (.fork 0x1011401060680 (.leaf 0x1099f9) (.leaf 0x19a0a7)) (.fork 0x1011401061480 (.leaf 0x199c14) (.fork 0x1011401061680 (.leaf 0xf1abf) (.leaf 0x19a0b1)))) (.fork 0x1011401121280 (.fork 0x1011401120680 (.leaf 0x108f79) (.leaf 0x19a154)) (.fork 0x1011401121480 (.leaf 0x199627) (.fork 0x1011401121680 (.leaf 0xf157f) (.leaf 0x199631)))))))) (.fork 0x1011601021680 (.fork 0x1011600120680 (.fork 0x1011401161480 (.fork 0x1011401160280 (.fork 0x1011401141480 (.fork 0x1011401141280 (.leaf 0xc7abf) (.leaf 0xc757f)) (.fork 0x1011401141680 (.leaf 0x199abe) (.leaf 0x199ac8))) (.fork 0x1011401160680 (.fork 0x1011401160480 (.leaf 0xc7abc) (.leaf 0xca9f9)) (.fork 0x1011401161080 (.leaf 0x1850b1) (.fork 0x1011401161280 (.leaf 0xc9f79) (.leaf 0x184631))))) (.fork 0x1011600060680 (.fork 0x1011600021680 (.fork 0x1011401161680 (.leaf 0x184ac8) (.leaf 0x199acd)) (.fork 0x1011600041680 (.leaf 0x7ca73) (.leaf 0x7c9cb))) (.fork 0x1011600061480 (.fork 0x1011600061280 (.leaf 0x65079) (.leaf 0x4fbe3)) (.fork 0x1011600061680 (.leaf 0x4f943) (.fork 0x1011600101680 (.leaf 0x7ca82) (.leaf 0x7bf4b)))))) (.fork 0x1011600160480 (.fork 0x1011600140680 (.fork 0x1011600121480 (.fork 0x1011600121280 (.leaf 0x50123) (.leaf 0x645f9)) (.fork 0x1011600121680 (.leaf 0x4e983) (.leaf 0x7c542))) (.fork 0x1011600141480 (.fork 0x1011600141280 (.leaf 0x4ff2b) (.leaf 0x4ea2b)) (.fork 0x1011600141680 (.leaf 0x64401) (.fork 0x1011600160280 (.leaf 0x7c3f2) (.leaf 0x28a73))))) (.fork 0x1011600161680 (.fork 0x1011600161080 (.fork 0x1011600160680 (.leaf 0x289cb) (.leaf 0x28a82)) (.fork 0x1011600161280 (.leaf 0x27f4b) (.fork 0x1011600161480 (.leaf 0x28542) (.leaf 0x283f2)))) (.fork 0x1011601020680 (.fork 0x1011601001680 (.leaf 0x7ca86) (.leaf 0x139a72)) (.fork 0x1011601021280 (.leaf 0x4d131) (.fork 0x1011601021480 (.leaf 0x4cbf1) (.leaf 0x34abc))))))) (.fork 0x1011601121080 (.fork 0x1011601061280 (.fork 0x1011601041680 (.fork 0x1011601041280 (.fork 0x1011601040680 (.leaf 0x10a130) (.leaf 0x4cfe1)) (.fork 0x1011601041480 (.leaf 0x34c0c) (.leaf 0x4c9f9))) (.fork 0x1011601060480 (.fork 0x1011601060280 (.leaf 0x109fe0) (.leaf 0x23131)) (.fork 0x1011601060680 (.leaf 0x22fe1) (.fork 0x1011601061080 (.leaf 0x35158) (.leaf 0x2014c))))) (.fork 0x1011601101480 (.fork 0x1011601061680 (.fork 0x1011601061480 (.leaf 0x34c19) (.leaf 0x34ac9)) (.fork 0x1011601100680 (.leaf 0xf215d) (.fork 0x1011601101280 (.leaf 0x3514c) (.leaf 0x4c021)))) (.fork 0x1011601120280 (.fork 0x1011601101680 (.leaf 0x4bf79) (.leaf 0x109020)) (.fork 0x1011601120480 (.leaf 0x22bf1) (.fork 0x1011601120680 (.leaf 0x1fc0c) (.leaf 0x35159)))))) (.fork 0x1011601141480 (.fork 0x1011601140280 (.fork 0x1011601121480 (.fork 0x1011601121280 (.leaf 0x22021) (.leaf 0x34c18)) (.fork 0x1011601121680 (.leaf 0x34589) (.leaf 0xf1c1d))) (.fork 0x1011601140680 (.fork 0x1011601140480 (.leaf 0x1fabc) (.leaf 0x229f9)) (.fork 0x1011601141080 (.leaf 0x350b1) (.fork 0x1011601141280 (.leaf 0x21f79) (.leaf 0x34631))))) (.fork 0x1011601160680 (.fork 0x1011601160080 (.fork 0x1011601141680 (.leaf 0x34ac8) (.leaf 0xf1acd)) (.fork 0x1011601160280 (.leaf 0xd0a72) (.fork 0x1011601160480 (.leaf 0xcb130) (.leaf 0xcafe0)))) (.fork 0x1011601161280 (.fork 0x1011601161080 (.leaf 0xc815d) (.leaf 0xca020)) (.fork 0x1011601161480 (.leaf 0xc7c1d) (.fork 0x1011601161680 (.leaf 0xc7acd) (.leaf 0x19a15f))))))))))

private def entry (P : Family) : Nat := lookup (familyMask (insert anchor P)) table

private def orbit (w : Nat) : Fin 24 := ⟨w % 24, Nat.mod_lt _ (by decide)⟩

private def certified (P : Family) : Prop :=
  let w := entry P
  (∀ a b : Fin 6, codeMap (w / 24) a = codeMap (w / 24) b → a = b) ∧
    move (w / 24) (insert anchor P) = orbitFamily (orbit w)

private instance (P : Family) : Decidable (certified P) := by
  unfold certified
  infer_instance

private def admissibleList : List Support :=
  ([[0, 3], [0, 4], [0, 5], [1, 3], [1, 4], [1, 5], [2, 3], [2, 4], [2, 5], [3, 4], [3, 5], [4, 5]] : List (List (Fin 6))).map List.toFinset

private lemma admissibleList_exact : admissibleList.toFinset = admissible := by decide +kernel
private lemma admissibleList_nodup : admissibleList.Nodup := by decide +kernel

private def candidates (n : Nat) : List Family := (List.sublistsLen n admissibleList).map List.toFinset

private lemma mem_candidates (P : Family) (n : Nat) (fits : P ∈ admissible.powersetCard n) :
    P ∈ candidates n := by
  obtain ⟨subset, card⟩ := Finset.mem_powersetCard.mp fits
  let chosen := admissibleList.filter fun U => decide (U ∈ P)
  have listed : chosen.toFinset = P := by
    ext U
    constructor
    · intro hU
      exact of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp hU)).2
    · intro hU
      have member : U ∈ admissibleList := by
        apply List.mem_toFinset.mp
        rw [admissibleList_exact]
        exact subset hU
      exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨member, decide_eq_true hU⟩)
  have nodup : chosen.Nodup := List.Nodup.filter _ admissibleList_nodup
  have length : chosen.length = n := by
    rw [← List.toFinset_card_of_nodup nodup, listed, card]
  exact List.mem_map.mpr ⟨chosen, List.mem_sublistsLen.mpr ⟨List.filter_sublist, length⟩, listed⟩

private lemma candidate_length (n : Nat) : (candidates n).length = (12 : Nat).choose n := by
  rw [candidates, List.length_map, List.length_sublistsLen, show admissibleList.length = 12 by rfl]

private def chunkChecked (n j : Nat) : Bool :=
  (((candidates n).drop (16*j)).take 16).all (fun P => decide (certified P))

set_option maxRecDepth 15000 in
private lemma forbidden_exact : ∀ i : Fin 6,
    (forbiddenFamily i).image supportMask = (forbiddenMasks[i.val]!).toFinset := by decide +kernel

private lemma all_of_chunks {α : Type} (xs : List α) (good : α → Bool) (n : Nat)
    (cover : xs.length ≤ 16 * n)
    (check : ∀ j < n, (((xs.drop (16*j)).take 16).all good) = true) : xs.all good = true := by
  apply List.all_eq_true.mpr
  intro a occurs
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp occurs
  have inList := (List.getElem?_eq_some_iff.mp hi).choose
  have block : i / 16 < n := by omega
  have remainder : i % 16 < 16 := Nat.mod_lt _ (by decide)
  have there : (((xs.drop (16*(i/16))).take 16)[i % 16]?) = some a := by
    rw [List.getElem?_take_of_lt remainder, List.getElem?_drop]
    have index : 16 * (i / 16) + i % 16 = i := by omega
    rwa [index]
  exact List.all_eq_true.mp (check (i / 16) block) _ (List.mem_iff_getElem?.mpr ⟨_, there⟩)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 200000000 in
private lemma chunk_9_0 : chunkChecked 9 0 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 200000000 in
private lemma chunk_9_1 : chunkChecked 9 1 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 200000000 in
private lemma chunk_9_2 : chunkChecked 9 2 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 200000000 in
private lemma chunk_9_3 : chunkChecked 9 3 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 200000000 in
private lemma chunk_9_4 : chunkChecked 9 4 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 200000000 in
private lemma chunk_9_5 : chunkChecked 9 5 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 200000000 in
private lemma chunk_9_6 : chunkChecked 9 6 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 200000000 in
private lemma chunk_9_7 : chunkChecked 9 7 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 200000000 in
private lemma chunk_9_8 : chunkChecked 9 8 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 200000000 in
private lemma chunk_9_9 : chunkChecked 9 9 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 200000000 in
private lemma chunk_9_10 : chunkChecked 9 10 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 200000000 in
private lemma chunk_9_11 : chunkChecked 9 11 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 200000000 in
private lemma chunk_9_12 : chunkChecked 9 12 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 200000000 in
private lemma chunk_9_13 : chunkChecked 9 13 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 200000000 in
private lemma chunk_10_0 : chunkChecked 10 0 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 200000000 in
private lemma chunk_10_1 : chunkChecked 10 1 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 200000000 in
private lemma chunk_10_2 : chunkChecked 10 2 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 200000000 in
private lemma chunk_10_3 : chunkChecked 10 3 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 200000000 in
private lemma chunk_10_4 : chunkChecked 10 4 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 200000000 in
private lemma chunk_11_0 : chunkChecked 11 0 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 200000000 in
private lemma chunk_12_0 : chunkChecked 12 0 = true := by decide +kernel

private lemma all_9 : (candidates 9).all (fun P => decide (certified P)) = true := by
  apply all_of_chunks _ _ 14
  · rw [candidate_length]
    decide
  intro j inside
  change chunkChecked 9 j = true
  interval_cases j
  · exact chunk_9_0
  · exact chunk_9_1
  · exact chunk_9_2
  · exact chunk_9_3
  · exact chunk_9_4
  · exact chunk_9_5
  · exact chunk_9_6
  · exact chunk_9_7
  · exact chunk_9_8
  · exact chunk_9_9
  · exact chunk_9_10
  · exact chunk_9_11
  · exact chunk_9_12
  · exact chunk_9_13

private lemma all_10 : (candidates 10).all (fun P => decide (certified P)) = true := by
  apply all_of_chunks _ _ 5
  · rw [candidate_length]
    decide
  intro j inside
  change chunkChecked 10 j = true
  interval_cases j
  · exact chunk_10_0
  · exact chunk_10_1
  · exact chunk_10_2
  · exact chunk_10_3
  · exact chunk_10_4

private lemma all_11 : (candidates 11).all (fun P => decide (certified P)) = true := by
  apply all_of_chunks _ _ 1
  · rw [candidate_length]
    decide
  intro j inside
  change chunkChecked 11 j = true
  interval_cases j
  · exact chunk_11_0

private lemma all_12 : (candidates 12).all (fun P => decide (certified P)) = true := by
  apply all_of_chunks _ _ 1
  · rw [candidate_length]
    decide
  intro j inside
  change chunkChecked 12 j = true
  interval_cases j
  · exact chunk_12_0

set_option maxRecDepth 15000 in
set_option maxHeartbeats 20000000 in
private lemma rows_0 : ∀ a : Fin 6,
    (univ.filter fun p => a ∈ concrete 0 p).card = 5 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 30000000 in
private lemma overlap_0 : ∀ p q : Fin 19, p ≠ q →
    (concrete 0 p ∩ concrete 0 q).card ≤ 1 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 20000000 in
private lemma rows_1 : ∀ a : Fin 6,
    (univ.filter fun p => a ∈ concrete 1 p).card = 5 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 30000000 in
private lemma overlap_1 : ∀ p q : Fin 19, p ≠ q →
    (concrete 1 p ∩ concrete 1 q).card ≤ 1 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 20000000 in
private lemma rows_2 : ∀ a : Fin 6,
    (univ.filter fun p => a ∈ concrete 2 p).card = 5 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 30000000 in
private lemma overlap_2 : ∀ p q : Fin 19, p ≠ q →
    (concrete 2 p ∩ concrete 2 q).card ≤ 1 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 20000000 in
private lemma rows_3 : ∀ a : Fin 6,
    (univ.filter fun p => a ∈ concrete 3 p).card = 5 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 30000000 in
private lemma overlap_3 : ∀ p q : Fin 19, p ≠ q →
    (concrete 3 p ∩ concrete 3 q).card ≤ 1 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 20000000 in
private lemma rows_4 : ∀ a : Fin 6,
    (univ.filter fun p => a ∈ concrete 4 p).card = 5 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 30000000 in
private lemma overlap_4 : ∀ p q : Fin 19, p ≠ q →
    (concrete 4 p ∩ concrete 4 q).card ≤ 1 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 20000000 in
private lemma rows_5 : ∀ a : Fin 6,
    (univ.filter fun p => a ∈ concrete 5 p).card = 5 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 30000000 in
private lemma overlap_5 : ∀ p q : Fin 19, p ≠ q →
    (concrete 5 p ∩ concrete 5 q).card ≤ 1 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 20000000 in
private lemma rows_6 : ∀ a : Fin 6,
    (univ.filter fun p => a ∈ concrete 6 p).card = 5 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 30000000 in
private lemma overlap_6 : ∀ p q : Fin 19, p ≠ q →
    (concrete 6 p ∩ concrete 6 q).card ≤ 1 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 20000000 in
private lemma rows_7 : ∀ a : Fin 6,
    (univ.filter fun p => a ∈ concrete 7 p).card = 5 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 30000000 in
private lemma overlap_7 : ∀ p q : Fin 19, p ≠ q →
    (concrete 7 p ∩ concrete 7 q).card ≤ 1 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 20000000 in
private lemma rows_8 : ∀ a : Fin 6,
    (univ.filter fun p => a ∈ concrete 8 p).card = 5 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 30000000 in
private lemma overlap_8 : ∀ p q : Fin 19, p ≠ q →
    (concrete 8 p ∩ concrete 8 q).card ≤ 1 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 20000000 in
private lemma rows_9 : ∀ a : Fin 6,
    (univ.filter fun p => a ∈ concrete 9 p).card = 5 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 30000000 in
private lemma overlap_9 : ∀ p q : Fin 19, p ≠ q →
    (concrete 9 p ∩ concrete 9 q).card ≤ 1 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 20000000 in
private lemma rows_10 : ∀ a : Fin 6,
    (univ.filter fun p => a ∈ concrete 10 p).card = 5 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 30000000 in
private lemma overlap_10 : ∀ p q : Fin 19, p ≠ q →
    (concrete 10 p ∩ concrete 10 q).card ≤ 1 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 20000000 in
private lemma rows_11 : ∀ a : Fin 6,
    (univ.filter fun p => a ∈ concrete 11 p).card = 5 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 30000000 in
private lemma overlap_11 : ∀ p q : Fin 19, p ≠ q →
    (concrete 11 p ∩ concrete 11 q).card ≤ 1 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 20000000 in
private lemma rows_12 : ∀ a : Fin 6,
    (univ.filter fun p => a ∈ concrete 12 p).card = 5 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 30000000 in
private lemma overlap_12 : ∀ p q : Fin 19, p ≠ q →
    (concrete 12 p ∩ concrete 12 q).card ≤ 1 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 20000000 in
private lemma rows_13 : ∀ a : Fin 6,
    (univ.filter fun p => a ∈ concrete 13 p).card = 5 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 30000000 in
private lemma overlap_13 : ∀ p q : Fin 19, p ≠ q →
    (concrete 13 p ∩ concrete 13 q).card ≤ 1 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 20000000 in
private lemma rows_14 : ∀ a : Fin 6,
    (univ.filter fun p => a ∈ concrete 14 p).card = 5 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 30000000 in
private lemma overlap_14 : ∀ p q : Fin 19, p ≠ q →
    (concrete 14 p ∩ concrete 14 q).card ≤ 1 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 20000000 in
private lemma rows_15 : ∀ a : Fin 6,
    (univ.filter fun p => a ∈ concrete 15 p).card = 5 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 30000000 in
private lemma overlap_15 : ∀ p q : Fin 19, p ≠ q →
    (concrete 15 p ∩ concrete 15 q).card ≤ 1 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 20000000 in
private lemma rows_16 : ∀ a : Fin 6,
    (univ.filter fun p => a ∈ concrete 16 p).card = 5 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 30000000 in
private lemma overlap_16 : ∀ p q : Fin 19, p ≠ q →
    (concrete 16 p ∩ concrete 16 q).card ≤ 1 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 20000000 in
private lemma rows_17 : ∀ a : Fin 6,
    (univ.filter fun p => a ∈ concrete 17 p).card = 5 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 30000000 in
private lemma overlap_17 : ∀ p q : Fin 19, p ≠ q →
    (concrete 17 p ∩ concrete 17 q).card ≤ 1 := by decide +kernel

private lemma concrete_rows (i : Fin 18) : ∀ a : Fin 6, (univ.filter fun p => a ∈ concrete i p).card = 5 := by
  fin_cases i
  · exact rows_0
  · exact rows_1
  · exact rows_2
  · exact rows_3
  · exact rows_4
  · exact rows_5
  · exact rows_6
  · exact rows_7
  · exact rows_8
  · exact rows_9
  · exact rows_10
  · exact rows_11
  · exact rows_12
  · exact rows_13
  · exact rows_14
  · exact rows_15
  · exact rows_16
  · exact rows_17

private lemma concrete_overlap (i : Fin 18) : ∀ p q : Fin 19, p ≠ q → (concrete i p ∩ concrete i q).card ≤ 1 := by
  fin_cases i
  · exact overlap_0
  · exact overlap_1
  · exact overlap_2
  · exact overlap_3
  · exact overlap_4
  · exact overlap_5
  · exact overlap_6
  · exact overlap_7
  · exact overlap_8
  · exact overlap_9
  · exact overlap_10
  · exact overlap_11
  · exact overlap_12
  · exact overlap_13
  · exact overlap_14
  · exact overlap_15
  · exact overlap_16
  · exact overlap_17

private lemma certified_choice (P : Family) (n : Nat)
    (fits : P ∈ admissible.powersetCard n) (lo : 9 ≤ n) (hi : n ≤ 12) : certified P := by
  have all : (candidates n).all (fun A => decide (certified A)) = true := by
    interval_cases n
    · exact all_9
    · exact all_10
    · exact all_11
    · exact all_12
  exact of_decide_eq_true (List.all_eq_true.mp all P (mem_candidates P n fits))

set_option maxRecDepth 15000 in
theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1_H1_R1_H2_R1.H1 := by
  classical
  intro C overlap rows atMost
  dsimp only
  intro oneTriple lower upper allowed
  change ∃ (i : Fin 18) (e : Equiv.Perm (Fin 6)) (π : Equiv.Perm (Fin 19)),
    ∀ p, (C (π p)).map e.toEmbedding = concrete i p
  let F := layout C
  let P := F.filter fun T => T.card = 2
  have sizes (T : Support) (ht : T ∈ F) : 2 ≤ T.card ∧ T.card ≤ 3 := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
    exact ⟨(Finset.mem_filter.mp hp).2, atMost p⟩
  have linear (T U : Support) (ht : T ∈ F) (hu : U ∈ F) (ne : T ≠ U) : (T ∩ U).card ≤ 1 := by
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hu
    exact overlap p q (fun eq => ne (congrArg C eq))
  change (F.filter fun T => T.card = 3).card = 1 at oneTriple
  obtain ⟨T, unique⟩ := Finset.card_eq_one.mp oneTriple
  have tMem : T ∈ F.filter (fun U => U.card = 3) := by rw [unique]; simp
  have tSize := (Finset.mem_filter.mp tMem).2
  have full : F = insert T P := by
    ext U
    rw [Finset.mem_insert]
    constructor
    · intro hu
      have size := sizes U hu
      by_cases two : U.card = 2
      · exact Or.inr (Finset.mem_filter.mpr ⟨hu, two⟩)
      · have three : U.card = 3 := by omega
        have member : U ∈ F.filter (fun V => V.card = 3) := Finset.mem_filter.mpr ⟨hu, three⟩
        rw [unique] at member
        exact Or.inl (Finset.mem_singleton.mp member)
    · rintro (rfl | hu)
      · exact (Finset.mem_filter.mp tMem).1
      · exact (Finset.mem_filter.mp hu).1
  obtain ⟨e₀, fixed⟩ := first_triple_map T tSize
  change T.map e₀.toEmbedding = anchor at fixed
  let P₀ := P.image (Finset.map e₀.toEmbedding)
  have pAllowed : P₀ ⊆ admissible := by
    rintro U hu
    obtain ⟨V, hv, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨vIn, vSize⟩ := Finset.mem_filter.mp hv
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.card_map _).trans vSize⟩, ?_⟩
    intro contained
    have sub := (Finset.mem_powersetCard.mp contained).1
    rw [← fixed] at sub
    have original : V ⊆ T := Finset.map_subset_map.mp sub
    have ne : V ≠ T := fun eq => by rw [eq] at vSize; omega
    have small := linear V T vIn (Finset.mem_filter.mp tMem).1 ne
    rw [Finset.inter_eq_left.mpr original, vSize] at small
    omega
  have sizesMatch : P₀.card = P.card := Finset.card_image_of_injective P (Finset.map_injective _)
  change 9 ≤ P.card at lower
  change P.card ≤ 12 at upper
  have eligible : P₀ ∈ admissible.powersetCard P.card :=
    Finset.mem_powersetCard.mpr ⟨pAllowed, sizesMatch⟩
  let word := entry P₀
  let i₀ : Fin 24 := orbit word
  have checked := certified_choice P₀ P.card eligible lower upper
  change (∀ a b : Fin 6, codeMap (word / 24) a = codeMap (word / 24) b → a = b) ∧
    move (word / 24) (insert anchor P₀) = orbitFamily i₀ at checked
  obtain ⟨e₁, represented⟩ := moved_family (word / 24) (fun _ _ => checked.1 _ _)
  let e := e₀.trans e₁
  have anchored : F.image (Finset.map e₀.toEmbedding) = insert anchor P₀ := by
    rw [full, Finset.image_insert, fixed]
  have moved : F.image (Finset.map e.toEmbedding) = orbitFamily i₀ := by
    change F.image (Finset.map (e₀.trans e₁).toEmbedding) = orbitFamily i₀
    rw [← compose_moves e₀ e₁, anchored, ← represented]
    exact checked.2
  by_cases forbidden : i₀.val < 6
  · let j : Fin 6 := ⟨i₀.val, forbidden⟩
    have bad : F.image (Finset.map e.toEmbedding) = forbiddenFamily j := by
      simpa only [orbitFamily, dif_pos forbidden, j] using moved
    exfalso
    apply allowed
    refine ⟨e, j, ?_⟩
    change F.image (fun X => supportMask (X.map e.toEmbedding)) = (forbiddenMasks[j.val]!).toFinset
    have masks : (F.image (Finset.map e.toEmbedding)).image supportMask =
        (forbiddenMasks[j.val]!).toFinset := by rw [bad, forbidden_exact]
    rw [Finset.image_image] at masks
    exact masks
  · let i : Fin 18 := ⟨i₀.val - 6, by omega⟩
    have same : layout (moveRows C e) = layout (concrete i) := by
      rw [layout_after_permutation]
      simpa only [orbitFamily, dif_neg forbidden, i] using moved
    obtain ⟨π, matched⟩ := relabel_columns (moveRows C e) (concrete i)
      (overlap_after_permutation C overlap e) (concrete_overlap i)
      (row_bounds_after_permutation C rows e) (concrete_rows i) same
    refine ⟨i, e, π.symm, ?_⟩
    intro p
    have point := matched (π.symm p)
    rw [Equiv.apply_symm_apply] at point
    exact point.symm
