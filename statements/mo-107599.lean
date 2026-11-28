import Mathlib

/-! Source: https://mathoverflow.net/questions/107599 -/

open Filter MeasureTheory
open scoped ENNReal Topology

namespace OMA.S_mo_107599

/-- A countable field of sets on which every finitely additive probability is countably
additive whenever the disjoint union stays in the field. -/
def MaoStandardField {Ω : Type} (F : Set (Set Ω)) : Prop :=
  F.Countable ∧ ∅ ∈ F ∧
    (∀ A ∈ F, Aᶜ ∈ F) ∧
    (∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F) ∧
    ∀ v : Set Ω → ℝ≥0∞, v ∅ = 0 → v Set.univ = 1 →
      (∀ A ∈ F, ∀ B ∈ F, Disjoint A B → v (A ∪ B) = v A + v B) →
      ∀ s : ℕ → Set Ω, (∀ n, s n ∈ F) →
        Pairwise (fun i j => Disjoint (s i) (s j)) → (⋃ n, s n) ∈ F →
        v (⋃ n, s n) = ∑' n, v (s n)

/-- Does convergence on a standard generating field imply convergence on its sigma-field?
The measure m records the extension of the pointwise limit on the field. -/
theorem main :
    ∀ (Ω : Type) (F : Set (Set Ω)), MaoStandardField F →
      ∀ (mSeq : ℕ → @Measure Ω (MeasurableSpace.generateFrom F))
        (m : @Measure Ω (MeasurableSpace.generateFrom F)),
        (∀ n, IsProbabilityMeasure (mSeq n)) → IsProbabilityMeasure m →
        (∀ A ∈ F, Tendsto (fun n => mSeq n A) atTop (𝓝 (m A))) →
        ∀ A, @MeasurableSet Ω (MeasurableSpace.generateFrom F) A →
          Tendsto (fun n => mSeq n A) atTop (𝓝 (m A)) := by
  sorry

end OMA.S_mo_107599
