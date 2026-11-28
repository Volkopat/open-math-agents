import OMAStatements.S_mo_178688
import Mathlib

open scoped BigOperators

open OMA.S_mo_178688



theorem OMA.solution : type_of% @OMA.S_mo_178688.main := by
  intro n x h
  refine ⟨h.injective,?_⟩
  intro p u v _ _ he
  have hz : ∑ i, (((u i : ℚ) - (v i : ℚ)) • x i) = 0 := by
    simp_rw [sub_smul,Finset.sum_sub_distrib,Rat.smul_def,Rat.cast_natCast]
    exact sub_eq_zero.mpr he
  have hv := Fintype.linearIndependent_iff.mp h _ hz
  funext i
  exact_mod_cast sub_eq_zero.mp (hv i)
