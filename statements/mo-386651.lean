import Mathlib

/-!
# Is there a rate for approximation of Borel step functions by Lipschitz maps?

Source: https://mathoverflow.net/questions/386651 (AB_IM, CC BY-SA 4.0).
Credit: @connoranderson

For fixed input data the best L¹ error tends to zero. There is no universal
decay rate, even allowing constants depending on the data: for any prescribed
sequence of Lipschitz budgets one probability measure on the real line and
the same singleton indicator have error at least 2^(-k-3) at budget k.
The budgets may be chosen to grow as rapidly as desired.
-/

namespace OMA.S_mo_386651
open MeasureTheory
open scoped ENNReal NNReal
noncomputable section

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

def stepFunction {n m N : ℕ} (E : Fin N → Set (Space n)) (v : Fin N → Space m) :
    Space n → Space m := ∑ i, (E i).indicator (fun _ => v i)

def singletonStep : ℝ → ℝ := ({0} : Set ℝ).indicator (fun _ => (1:ℝ))

theorem main :
    (∀ (n m N : ℕ) (μ : Measure (Space n)) [IsFiniteMeasure μ]
      (E : Fin N → Set (Space n)) (v : Fin N → Space m),
      (∀ i, MeasurableSet (E i)) → (∀ i j, 0 ≤ v i j) →
      ∀ ε : ℝ, 0 < ε → ∃ K : ℝ≥0, ∀ L ≥ K, ∃ g : Space n → Space m,
        LipschitzWith L g ∧ eLpNorm (stepFunction E v - g) 1 μ ≤ ENNReal.ofReal ε) ∧
    (∀ L : ℕ → ℝ≥0, ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      ∀ (k : ℕ) (g : ℝ → ℝ), LipschitzWith (L k) g →
        (2⁻¹ : ℝ≥0∞)^(k+3) ≤ eLpNorm (singletonStep - g) 1 μ) := by
  sorry

end
end OMA.S_mo_386651
