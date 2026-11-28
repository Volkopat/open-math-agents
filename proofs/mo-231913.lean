import OMAStatements.S_mo_231913
import Mathlib

/-!
Uses @caa1982’s complete alternative proof #25729, pinned at
695f261085d0ecb43619e144db46ba64787d53d0. The same scalar block witness
is divided by two: the block at index zero is now the identity, so standard identity
positivity replaces the explicit diagonal positivity argument.
The complete main proof by @ivillar (#25719) was also reviewed.
Statement: @caa1982 (#20034); question: Obriareos, MO231913.
-/

open OMA.S_mo_231913
open Matrix
open scoped ComplexOrder

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_231913.main) := by
  intro h
  let C : ℤ → Matrix (Fin 1) (Fin 1) ℂ := fun l => if l = 0 then 1 else -1
  have h0 : (C 0).PosSemidef := by
    simp only [C, if_pos rfl]
    exact PosSemidef.one
  have hadj : ∀ l : ℤ, C (-l) = (C l)ᴴ := by
    intro l
    by_cases hl : l = 0 <;> simp [C, hl]
  have hnorm : ∀ l : ℤ, -((3 : ℕ) : ℤ) < l → l < (3 : ℕ) → hsNormSq (C l) ≤ hsNormSq (C 0) := by
    intro l _ _
    by_cases hl : l = 0 <;> simp [hsNormSq, C, hl]
  have hM := h 3 1 C h0 hadj hnorm
  have hv := hM.dotProduct_mulVec_nonneg (fun _ => 1)
  simp [dotProduct, mulVec, blockToeplitz, Fintype.sum_prod_type, Fin.sum_univ_three, C] at hv
  norm_num at hv
