import Mathlib

/-!
# MathOverflow 154707

Source: https://mathoverflow.net/questions/154707
-/

namespace OMA.S_mo_154707

open Set

/-- Every sequence of relatively open covers admits a covering choice. -/
def OneFromEachOpenCover (X : Set ℝ) : Prop :=
  ∀ U : ℕ → Set (Set X),
    (∀ n V, V ∈ U n → IsOpen V) →
    (∀ n, ⋃₀ U n = univ) →
    ∃ V : ℕ → Set X, (∀ n, V n ∈ U n) ∧ ⋃ n, V n = univ

/-- Cover by open intervals shorter than arbitrary prescribed lengths. -/
def StrongMeasureZero (X : Set ℝ) : Prop :=
  ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) →
    ∃ a b : ℕ → ℝ, (∀ n, a n < b n ∧ b n - a n < ε n) ∧
      X ⊆ ⋃ n, Ioo (a n) (b n)

theorem main : ∀ X : Set ℝ, OneFromEachOpenCover X → StrongMeasureZero X := by
  sorry

end OMA.S_mo_154707
