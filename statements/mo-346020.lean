import Mathlib

/-!
# MathOverflow 346020

Source: https://mathoverflow.net/questions/346020
-/

namespace OMA.S_mo_346020

open Set MeasureTheory

def AnalyticFibre {n m : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ)) (p : Fin n → ℝ) :
    Set (Fin n → ℝ) := {x | f x = f p}

theorem main : ∀ (n m : ℕ) (f : (Fin n → ℝ) → (Fin m → ℝ)),
    AnalyticOnNhd ℝ f univ →
    ∃ U : Set (Fin n → ℝ), volume Uᶜ = 0 ∧
      ∀ p ∈ U, ∀ q ∈ U, Cardinal.mk (AnalyticFibre f p) = Cardinal.mk (AnalyticFibre f q) := by
  sorry

end OMA.S_mo_346020
