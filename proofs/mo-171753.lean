import OMAStatements.S_mo_171753
import Mathlib

-- Retains @AkiRA-COM-FP’s separating-clause construction from PR #17304.
-- Finite nonempty union closure follows from Mathlib’s supremum-closure theorem.

open Finset

open OMA.S_mo_171753

private theorem union_over_nonempty {n : ℕ} {F : Set (Finset (Fin n))}
    (hUnion : ∀ s ∈ F, ∀ t ∈ F, s ∪ t ∈ F) :
    ∀ A : Finset (Finset (Fin n)), A.Nonempty → (∀ t ∈ A, t ∈ F) → A.sup id ∈ F := by
  intro A hA hF
  simpa only [Finset.sup'_eq_sup] using Finset.sup'_mem F hUnion A hA id hF

private theorem clause_separates_missing {n : ℕ} {F : Set (Finset (Fin n))}
    (hUnion : ∀ s ∈ F, ∀ t ∈ F, s ∪ t ∈ F) {s : Finset (Fin n)} (hs : s ∉ F) :
    ∃ c : CoHornClause n, (∀ t ∈ F, SatisfiesCoHorn t c) ∧ ¬ SatisfiesCoHorn s c := by
  classical
  let P : Finset (Fin n) := univ \ s
  let included : Finset (Finset (Fin n)) := univ.filter (fun t => t ∈ F ∧ t ⊆ s)
  have hOfOutside (t : Finset (Fin n)) (hSub : ¬ t ⊆ s) :
      ∃ i ∈ P, i ∈ t := by
    change ¬ (∀ i, i ∈ t → i ∈ s) at hSub
    push Not at hSub
    obtain ⟨i,hi,his⟩ := hSub
    exact ⟨i,mem_sdiff.mpr ⟨mem_univ _,his⟩,hi⟩
  have hNotPositive : ¬ (∃ i ∈ P, i ∈ s) := by
    rintro ⟨i,hi,his⟩
    exact (mem_sdiff.mp hi).2 his
  by_cases hNonempty : included.Nonempty
  · let W := included.sup id
    have hInF : W ∈ F := union_over_nonempty hUnion included hNonempty fun t ht =>
      (mem_filter.mp ht).2.1
    have hWS : W ⊆ s := by
      apply Finset.sup_le_iff.mpr
      intro t ht
      exact (mem_filter.mp ht).2.2
    have hMissing : ∃ i ∈ s, i ∉ W := by
      by_contra! h
      have he : W = s := Finset.Subset.antisymm hWS (by intro i hi; exact h i hi)
      exact hs (he ▸ hInF)
    obtain ⟨i,his,hiW⟩ := hMissing
    refine ⟨⟨P,some i⟩,?_,?_⟩
    · intro t ht
      by_cases hSub : t ⊆ s
      · right
        refine ⟨i,rfl,fun hi => hiW ?_⟩
        have hInc : t ∈ included := mem_filter.mpr ⟨mem_univ _,ht,hSub⟩
        exact (le_sup (f := id) hInc : t ⊆ W) hi
      · exact Or.inl (hOfOutside t hSub)
    · rintro (h | ⟨j,hEq,hN⟩)
      · exact hNotPositive h
      · exact hN (Option.some.inj hEq ▸ his)
  · refine ⟨⟨P,none⟩,?_,?_⟩
    · intro t ht
      apply Or.inl
      apply hOfOutside
      intro hSub
      exact hNonempty ⟨t,mem_filter.mpr ⟨mem_univ _,ht,hSub⟩⟩
    · rintro (h | ⟨j,hEq,_⟩)
      · exact hNotPositive h
      · contradiction

theorem OMA.solution : type_of% @OMA.S_mo_171753.main := by
  classical
  intro n F hUnion
  let missing : Finset (Finset (Fin n)) := univ.filter (fun s => s ∉ F)
  let selected (s : Finset (Fin n)) : CoHornClause n :=
    if h : s ∉ F then (clause_separates_missing hUnion h).choose else ⟨∅,none⟩
  have hOne (s : Finset (Fin n)) (hs : s ∉ F) :
      (∀ t ∈ F, SatisfiesCoHorn t (selected s)) ∧ ¬ SatisfiesCoHorn s (selected s) := by
    simpa only [selected,dif_pos hs] using (clause_separates_missing hUnion hs).choose_spec
  refine ⟨missing.toList.map selected,?_⟩
  intro s
  constructor
  · intro hSat
    by_contra hs
    have hList : s ∈ missing.toList := by
      rw [mem_toList]
      exact mem_filter.mpr ⟨mem_univ _,hs⟩
    exact (hOne s hs).2 (hSat (selected s) (List.mem_map.mpr ⟨s,hList,rfl⟩))
  · intro hs c hc
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hc
    have hMiss : t ∉ F := (mem_filter.mp (mem_toList.mp ht)).2
    exact (hOne t hMiss).1 s hs
