import OMAStatements.S_mo_201121
import Mathlib

open OMA.S_mo_201121

def tbl : List (Fin 8) := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 4, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 0, 3, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 6, 3, 0, 0, 0, 0, 6, 0, 5, 4, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 2, 7, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 7, 2, 0, 0, 0, 0, 7, 0, 0, 1, 0, 0, 5, 4, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 7, 0, 0, 1, 0, 0, 0, 0, 0, 0, 7, 2, 0, 0, 6, 3, 0, 4, 0, 0, 0, 0, 0, 0, 1, 0, 2, 7, 0, 0, 3, 6, 0, 5, 0, 0, 0, 0, 4, 5, 0, 6, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0]

theorem mo201121_key :
    ∀ A ∈ (Finset.univ : Finset (Fin 8)).powersetCard 5,
      ∀ B ∈ (Finset.univ : Finset (Fin 8)).powersetCard 5,
        (tbl.getD (∑ i ∈ A, 2 ^ (i : ℕ)) 0) ∈ A ∧
        ((A ∩ B).card = 4 →
          tbl.getD (∑ i ∈ A, 2 ^ (i : ℕ)) 0 ≠
          tbl.getD (∑ i ∈ B, 2 ^ (i : ℕ)) 0) := by
  decide +kernel

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_201121.main) := by
  intro h
  apply h 8 5 (by norm_num) (by norm_num)
  refine ⟨fun A => tbl.getD (∑ i ∈ A, 2 ^ (i : ℕ)) 0, ?_, ?_⟩
  · intro A hA
    have hA' : A ∈ (Finset.univ : Finset (Fin 8)).powersetCard 5 :=
      Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hA⟩
    exact (mo201121_key A hA' A hA').1
  · intro A B hA hB hAB
    have hA' : A ∈ (Finset.univ : Finset (Fin 8)).powersetCard 5 :=
      Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hA⟩
    have hB' : B ∈ (Finset.univ : Finset (Fin 8)).powersetCard 5 :=
      Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hB⟩
    exact (mo201121_key A hA' B hB').2 (by simpa using hAB)
