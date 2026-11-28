import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H3_R1
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Normalize the eight four-secants and seventy-two two-secants to a partial incidence matrix. -/
-- Credit: @LordMike
-- Port of reductions/Erdos723.erdos_723.variants.leq_11.R1.H2.R2.H3.R1.H2.R1.lean by @avivorly (PR #1915) onto the identical hypothesis statement Erdos723.erdos_723.variants.leq_11.R1.H2.R1.H3.R1.H2.
namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H3_R1_H2_R1

def H1 : Prop :=
  let A (M : Fin 8 ⊕ Fin 72 → Fin 111 → Bool) (p : Fin 111) :=
    (Finset.univ.filter fun l : Fin 8 => M (.inl l) p = true).card
  let B (M : Fin 8 ⊕ Fin 72 → Fin 111 → Bool) (p : Fin 111) :=
    (Finset.univ.filter fun l : Fin 72 => M (.inr l) p = true).card
  ¬ ∃ (M : Fin 8 ⊕ Fin 72 → Fin 111 → Bool) (S : Finset (Fin 111)),
    S.card = 16 ∧
    (∀ l, (Finset.univ.filter fun p => M l p = true).card = 11) ∧
    (∀ l : Fin 8, (S.filter fun p => M (.inl l) p = true).card = 4) ∧
    (∀ l : Fin 72, (S.filter fun p => M (.inr l) p = true).card = 2) ∧
    (∀ p ∈ S, A M p = 2 ∧ B M p = 9) ∧
    (∀ p ∉ S, 2 * A M p + B M p = 8) ∧
    (∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true) ∧
    (∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l = m) ∧
    ∀ p ∉ S, A M p ≤ 2

def H2 : Prop :=
  let A (M : Fin 8 ⊕ Fin 72 → Fin 111 → Bool) (p : Fin 111) :=
    (Finset.univ.filter fun l : Fin 8 => M (.inl l) p = true).card
  let B (M : Fin 8 ⊕ Fin 72 → Fin 111 → Bool) (p : Fin 111) :=
    (Finset.univ.filter fun l : Fin 72 => M (.inr l) p = true).card
  ¬ ∃ (M : Fin 8 ⊕ Fin 72 → Fin 111 → Bool) (S : Finset (Fin 111)),
    S.card = 16 ∧
    (∀ l, (Finset.univ.filter fun p => M l p = true).card = 11) ∧
    (∀ l : Fin 8, (S.filter fun p => M (.inl l) p = true).card = 4) ∧
    (∀ l : Fin 72, (S.filter fun p => M (.inr l) p = true).card = 2) ∧
    (∀ p ∈ S, A M p = 2 ∧ B M p = 9) ∧
    (∀ p ∉ S, 2 * A M p + B M p = 8) ∧
    (∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true) ∧
    (∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l = m) ∧
    ∃ p ∉ S, 3 ≤ A M p

open Finset
open scoped BigOperators

lemma sum_outside_pencil (I : Fin 111 → Fin 111 → Bool)
    (lines : ∀ p q, p ≠ q → ∃! l, I l p = true ∧ I l q = true)
    (S : Finset (Fin 111)) (p : Fin 111) (outside : p ∉ S) :
    (∑ l ∈ Finset.univ.filter (fun l => I l p = true),
      (S.filter fun q => I l q = true).card) = S.card := by
  classical
  calc
    _ = ∑ l ∈ Finset.univ.filter (fun l => I l p = true),
        ∑ q ∈ S, if I l q = true then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro l _
      rw [← Finset.sum_filter]
      simp
    _ = ∑ q ∈ S, (1 : ℕ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      have distinct : p ≠ q := fun eq => outside (eq.symm ▸ hq)
      obtain ⟨l, together, unique⟩ := lines p q distinct
      have one : (Finset.univ.filter (fun r => I r p = true)).filter
          (fun r => I r q = true) = {l} := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨unique r, fun eq => eq.symm ▸ together⟩
      rw [← Finset.sum_filter, one]
      simp
    _ = _ := by simp

lemma card_relabel_filter {n : Nat} (T : Finset (Fin 111)) (e : Fin n ≃ ↥T)
    (Q : Fin 111 → Prop) [DecidablePred Q] :
    (Finset.univ.filter fun i : Fin n => Q (e i).val).card = (T.filter Q).card := by
  apply Finset.card_bij (fun i _ => (e i).val)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨(e i).property, (Finset.mem_filter.mp hi).2⟩
  · intro i _ j _ same
    exact e.injective (Subtype.ext same)
  · intro x hx
    obtain ⟨inside, yes⟩ := Finset.mem_filter.mp hx
    refine ⟨e.symm ⟨x, inside⟩, ?_, ?_⟩
    · simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.apply_symm_apply] using yes
    · exact congrArg Subtype.val (e.apply_symm_apply ⟨x, inside⟩)

set_option maxHeartbeats 3000000 in
theorem main : H1 → H2 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H3_R1.H2 := by
  intro sparse dense I rowSizes columnSizes rowPairs columnPairs
  dsimp only
  rintro ⟨S, ⟨sizeS, permitted, ⟨fourCount, twoCount, _⟩, degree⟩, noSix⟩
  classical
  let k (l : Fin 111) := (S.filter fun p => I l p = true).card
  let four : Finset (Fin 111) := Finset.univ.filter fun l => k l = 4
  let two : Finset (Fin 111) := Finset.univ.filter fun l => k l = 2
  let Acount (p : Fin 111) := (four.filter fun l => I l p = true).card
  let Bcount (p : Fin 111) := (two.filter fun l => I l p = true).card
  have sizeFour : four.card = 8 := by
    change four.card + 3 * (Finset.univ.filter fun l => k l = 6).card = 8 at fourCount
    change (Finset.univ.filter fun l => k l = 6).card = 0 at noSix
    omega
  have sizeTwo : two.card = 72 := by
    change two.card = 72 + 3 * (Finset.univ.filter fun l => k l = 6).card at twoCount
    change (Finset.univ.filter fun l => k l = 6).card = 0 at noSix
    omega
  have four_mem (l : Fin 111) : l ∈ four ↔ k l = 4 := by simp [four]
  have two_mem (l : Fin 111) : l ∈ two ↔ k l = 2 := by simp [two]
  have no_six (l : Fin 111) : k l ≠ 6 := by
    intro six
    change (Finset.univ.filter fun l => k l = 6).card = 0 at noSix
    have listed : l ∈ Finset.univ.filter (fun l => k l = 6) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ l, six⟩
    have none := Finset.card_eq_zero.mp noSix
    rw [none] at listed
    exact Finset.notMem_empty _ listed
  have values (l : Fin 111) : k l = 0 ∨ k l = 2 ∨ k l = 4 := by
    have allowed : 2 ∣ k l ∧ k l ≤ 6 := permitted l
    obtain ⟨⟨d, exactD⟩, bounded⟩ := allowed
    have forbidden := no_six l
    omega
  let eA : Fin 8 ≃ ↥four := (Fintype.equivFinOfCardEq (by simpa using sizeFour)).symm
  let eB : Fin 72 ≃ ↥two := (Fintype.equivFinOfCardEq (by simpa using sizeTwo)).symm
  let chosen : Fin 8 ⊕ Fin 72 → Fin 111 := Sum.elim (fun l => (eA l).val) (fun l => (eB l).val)
  let M (r : Fin 8 ⊕ Fin 72) (p : Fin 111) := I (chosen r) p
  have pickedA (l : Fin 8) : k (eA l).val = 4 := (four_mem _).mp (eA l).property
  have pickedB (l : Fin 72) : k (eB l).val = 2 := (two_mem _).mp (eB l).property
  have selected_injective : Function.Injective chosen := by
    intro r s equal
    cases r with
    | inl a =>
      cases s with
      | inl b => exact congrArg Sum.inl (eA.injective (Subtype.ext equal))
      | inr b =>
        have numbers : k (eA a).val = k (eB b).val := congrArg k equal
        have one := pickedA a
        have other := pickedB b
        omega
    | inr a =>
      cases s with
      | inl b =>
        have numbers : k (eB a).val = k (eA b).val := congrArg k equal
        have one := pickedB a
        have other := pickedA b
        omega
      | inr b => exact congrArg Sum.inr (eB.injective (Subtype.ext equal))
  have line_sizes (r : Fin 8 ⊕ Fin 72) :
      (Finset.univ.filter fun p => M r p = true).card = 11 := rowSizes (chosen r)
  have A_sizes (r : Fin 8) : (S.filter fun p => M (.inl r) p = true).card = 4 := pickedA r
  have B_sizes (r : Fin 72) : (S.filter fun p => M (.inr r) p = true).card = 2 := pickedB r
  have rows_share (r s : Fin 8 ⊕ Fin 72) (different : r ≠ s) :
      ∃! p, M r p = true ∧ M s p = true :=
    rowPairs _ _ (fun equal => different (selected_injective equal))
  have columns_unique (p q : Fin 111) (different : p ≠ q) (r s : Fin 8 ⊕ Fin 72)
      (rp : M r p = true) (rq : M r q = true) (sp : M s p = true) (sq : M s q = true) : r = s := by
    obtain ⟨_, _, unique⟩ := columnPairs p q different
    exact selected_injective ((unique (chosen r) ⟨rp,rq⟩).trans (unique (chosen s) ⟨sp,sq⟩).symm)
  have inside_counts (p : Fin 111) (hp : p ∈ S) : Acount p = 2 ∧ Bcount p = 9 := by
    have a : Acount p = 2 := by
      have degrees := degree p hp
      have zero : (Finset.univ.filter (fun l => k l = 6 ∧ I l p = true)).card = 0 := by
        have empty : Finset.univ.filter (fun l => k l = 6 ∧ I l p = true) = ∅ := by
          ext l
          simp [no_six]
        rw [empty, Finset.card_empty]
      have sameA : four.filter (fun l => I l p = true) =
          Finset.univ.filter (fun l => k l = 4 ∧ I l p = true) := by
        ext l
        simp [four, Finset.mem_filter]
      change ((Finset.univ.filter fun l => k l = 4 ∧ I l p = true).card) +
        2 * (Finset.univ.filter fun l => k l = 6 ∧ I l p = true).card = 2 at degrees
      rw [← sameA, zero] at degrees
      simpa [Acount] using degrees
    have disjoint : Disjoint (four.filter (fun l => I l p = true))
        (two.filter (fun l => I l p = true)) := by
      rw [Finset.disjoint_left]
      intro l left right
      have q := (four_mem l).mp (Finset.mem_of_mem_filter l left)
      have r := (two_mem l).mp (Finset.mem_of_mem_filter l right)
      omega
    have complete : four.filter (fun l => I l p = true) ∪ two.filter (fun l => I l p = true) =
        Finset.univ.filter (fun l => I l p = true) := by
      ext l
      simp only [Finset.mem_union, Finset.mem_filter, four_mem, two_mem, Finset.mem_univ, true_and]
      constructor
      · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
      · intro inc
        have positive : 0 < k l := Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, inc⟩⟩
        rcases values l with zero | other | other
        · omega
        · exact Or.inr ⟨other,inc⟩
        · exact Or.inl ⟨other,inc⟩
    have total : Acount p + Bcount p = 11 := by
      change (four.filter (fun l => I l p = true)).card + (two.filter (fun l => I l p = true)).card = 11
      rw [← Finset.card_union_of_disjoint disjoint, complete, columnSizes p]
    exact ⟨a, by omega⟩
  have outside_counts (p : Fin 111) (hp : p ∉ S) : 2 * Acount p + Bcount p = 8 := by
    let through := Finset.univ.filter fun l => I l p = true
    have counted : (∑ l ∈ through, k l) = 16 := by
      rw [sum_outside_pencil I columnPairs S p hp, sizeS]
    have shape (l : Fin 111) :
        k l = (if l ∈ four then 4 else 0) + (if l ∈ two then 2 else 0) := by
      rcases values l with zero | pair | quadruple
      · simp [four_mem, two_mem, zero]
      · simp [four_mem, two_mem, pair]
      · simp [four_mem, two_mem, quadruple]
    have sameA : through.filter (fun l => l ∈ four) = four.filter (fun l => I l p = true) := by
      ext l
      simp only [through, Finset.mem_filter, Finset.mem_univ, true_and]
      exact and_comm
    have sameB : through.filter (fun l => l ∈ two) = two.filter (fun l => I l p = true) := by
      ext l
      simp only [through, Finset.mem_filter, Finset.mem_univ, true_and]
      exact and_comm
    have totals : (∑ l ∈ through, k l) = 4 * Acount p + 2 * Bcount p := by
      simp_rw [shape]
      rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter, sameA, sameB]
      simp [Acount, Bcount, Nat.mul_comm]
    omega
  have transfersA (p : Fin 111) :
      (Finset.univ.filter fun l : Fin 8 => M (.inl l) p = true).card = Acount p :=
    card_relabel_filter four eA (fun l => I l p = true)
  have transfersB (p : Fin 111) :
      (Finset.univ.filter fun l : Fin 72 => M (.inr l) p = true).card = Bcount p :=
    card_relabel_filter two eB (fun l => I l p = true)
  have counts_inside (p : Fin 111) (hp : p ∈ S) :
      (Finset.univ.filter fun l : Fin 8 => M (.inl l) p = true).card = 2 ∧
      (Finset.univ.filter fun l : Fin 72 => M (.inr l) p = true).card = 9 := by
    rw [transfersA p, transfersB p]
    exact inside_counts p hp
  have counts_outside (p : Fin 111) (hp : p ∉ S) :
      2 * (Finset.univ.filter fun l : Fin 8 => M (.inl l) p = true).card +
        (Finset.univ.filter fun l : Fin 72 => M (.inr l) p = true).card = 8 := by
    rw [transfersA p, transfersB p]
    exact outside_counts p hp
  by_cases large : ∃ p ∉ S, 3 ≤ Acount p
  · apply dense
    refine ⟨M,S,sizeS,line_sizes,A_sizes,B_sizes,counts_inside,counts_outside,rows_share,columns_unique,?_⟩
    obtain ⟨p, hp, many⟩ := large
    refine ⟨p, hp, ?_⟩
    change 3 ≤ (Finset.univ.filter fun l : Fin 8 => M (.inl l) p = true).card
    rw [transfersA p]
    exact many
  · apply sparse
    refine ⟨M,S,sizeS,line_sizes,A_sizes,B_sizes,counts_inside,counts_outside,rows_share,columns_unique,?_⟩
    intro p hp
    change (Finset.univ.filter fun l : Fin 8 => M (.inl l) p = true).card ≤ 2
    rw [transfersA p]
    by_contra absent
    exact large ⟨p,hp,by omega⟩

end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H3_R1_H2_R1
