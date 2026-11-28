import Mathlib

/-! # Concavity of mixed van der Waerden numbers

Bruce Landman's conjecture compares two red-blue progression thresholds.
Source: https://www.openproblemgarden.org/op/concavity_of_van_der_waerden_numbers
Credit: @steveDOTdigital
-/

namespace OMA.S_opg_concavity_of_van_der_waerden_numbers

/-- The coloring has a progression of the given length and color in [1,n]. -/
def hasProgression (color : ℕ → Bool) (n length : ℕ) (shade : Bool) : Prop :=
  ∃ start step : ℕ, 0 < start ∧ 0 < step ∧
    ∀ i < length, start + i * step ≤ n ∧ color (start + i * step) = shade

/-- The least positive endpoint forcing a red k-term or a blue ℓ-term progression.
Only colors on [1,n] enter the definition. At length zero the empty
progression is available, giving the boundary value w(k,0) = 1. -/
noncomputable def w (k ℓ : ℕ) : ℕ :=
  sInf {n : ℕ | 0 < n ∧ ∀ color : ℕ → Bool,
    hasProgression color n k true ∨ hasProgression color n ℓ false}

theorem main : ∀ k ℓ : ℕ, 0 < ℓ → ℓ ≤ k → w (k + 1) (ℓ - 1) ≤ w k ℓ := by
  sorry

end OMA.S_opg_concavity_of_van_der_waerden_numbers
