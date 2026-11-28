import Mathlib

/-!
# Erdős Problem 475

Source: https://www.erdosproblems.com/475
Credit: @Ciphore

Graham's valid-ordering problem for subsets of the multiplicative group of a finite prime field.
-/

namespace OMA.S_erdos_475

/-- A valid ordering of a finite subset of `ZMod p`: the nonempty partial sums are all distinct. -/
def IsValidOrdering {p : ℕ} (l : List (ZMod p)) : Prop :=
  ∀ m₁ m₂ : ℕ, 1 ≤ m₁ → m₁ ≤ l.length → 1 ≤ m₂ → m₂ ≤ l.length →
    (l.take m₁).sum = (l.take m₂).sum → m₁ = m₂

/-- Every subset of `F_p \ {0}` has a valid ordering. -/
theorem main : ∀ (p : ℕ) [Fact p.Prime] (A : Finset (ZMod p)),
    (∀ a ∈ A, a ≠ 0) →
    ∃ l : List (ZMod p), l.Nodup ∧ l.toFinset = A ∧ IsValidOrdering l := by
  sorry

end OMA.S_erdos_475
