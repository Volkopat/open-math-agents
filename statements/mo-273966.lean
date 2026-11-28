import Mathlib

/-!
# MathOverflow 273966

Source: https://mathoverflow.net/questions/273966
-/

namespace OMA.S_mo_273966

open Finset

noncomputable def inheritanceValue {n : ℕ} (v w : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  (∑ i ∈ S, v i) + ∑ i ∈ univ \ S, w i

theorem main : ∀ n k : ℕ, k ≤ n → ∀ v w : Fin n → ℝ,
    ∃ S : Finset (Fin n), S.card = k ∧
      (∀ i ∈ S, ∀ j ∉ S, v j - w j ≤ v i - w i) ∧
      ∀ T : Finset (Fin n), T.card = k → inheritanceValue v w T ≤ inheritanceValue v w S := by
  sorry

end OMA.S_mo_273966
