import Mathlib

/-!
# MathOverflow 293857

Source: https://mathoverflow.net/questions/293857
-/

namespace OMA.S_mo_293857

open Set Filter MeasureTheory
open scoped Topology

abbrev BaireSequences := ℕ → ℕ

def eventuallyEqualAtAllIndices (x y : BaireSequences) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → x n = y n

def verticalSection (P : Set (BaireSequences × BaireSequences)) (x : BaireSequences) :
    Set BaireSequences := {y | (x,y) ∈ P}

theorem main : ∃ P : Set (BaireSequences × BaireSequences), MeasurableSet P ∧
      (∀ x y, eventuallyEqualAtAllIndices x y → verticalSection P x = verticalSection P y) ∧
      (¬ ∀ x y, verticalSection P x = verticalSection P y) ∧
      ∀ S : Set BaireSequences, (∀ x ∈ S, ∀ y ∈ S, verticalSection P x = verticalSection P y) →
        IsMeagre S ∧ ∀ (μ : Measure BaireSequences), NullSingletonClass μ → μ S = 0 := by
  sorry

end OMA.S_mo_293857
