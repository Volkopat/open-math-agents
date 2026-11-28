import OMAStatements.S_mo_429559
import Mathlib

theorem OMA.solution : type_of% @OMA.S_mo_429559.main := by
  intro F E _ _ _ a b h
  set K := IntermediateField.adjoin F ({a, b} : Set E)
  have : Algebra.FiniteType F K.toSubalgebra := h ▸ .adjoin_of_finite (Set.toFinite _)
  have := finite_of_finite_type_of_isJacobsonRing F K
  have t x (hx : x ∈ ({a, b} : Set E)) :=
    IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic (⟨x, IntermediateField.subset_adjoin F _ hx⟩ : K))
  exact ⟨t a (by simp), t b (by simp)⟩
