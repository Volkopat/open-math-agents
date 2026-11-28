import Mathlib

/-!
# Rokhlin's multiple mixing problem

Source: https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics
(entry: Rokhlin's multiple mixing problem – are all strongly mixing systems also strongly
3-mixing?)
Credit: @shc261392

Reading used here (stated in the affirmative):
* A system is an invertible measure-preserving transformation `T` of a probability space
  `(X, μ)`, given as a measurable equivalence `T : X ≃ᵐ X` with `MeasurePreserving T μ μ`.
* `T` is strongly mixing when `μ (T^{-n} A ∩ B) → μ A * μ B` as `n → ∞` for all measurable
  `A`, `B`.
* `T` is strongly 3-mixing (mixing of order 3) when
  `μ (A ∩ T^{-m} B ∩ T^{-(m+n)} C) → μ A * μ B * μ C` as `m, n → ∞` (jointly: the limit is along
  `atTop` on `ℕ × ℕ`) for all measurable `A`, `B`, `C`.

Rokhlin asked whether every strongly mixing system is strongly 3-mixing.
-/

namespace OMA.S_wp_rokhlin_s

open Filter Topology MeasureTheory

theorem main :
    ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (T : X ≃ᵐ X),
      MeasurePreserving T μ μ →
      (∀ A B : Set X, MeasurableSet A → MeasurableSet B →
        Tendsto (fun n : ℕ => μ ((⇑T)^[n] ⁻¹' A ∩ B)) atTop (𝓝 (μ A * μ B))) →
      ∀ A B C : Set X, MeasurableSet A → MeasurableSet B → MeasurableSet C →
        Tendsto (fun p : ℕ × ℕ => μ (A ∩ (⇑T)^[p.1] ⁻¹' B ∩ (⇑T)^[p.1 + p.2] ⁻¹' C))
          atTop (𝓝 (μ A * μ B * μ C)) := by
  sorry

end OMA.S_wp_rokhlin_s
