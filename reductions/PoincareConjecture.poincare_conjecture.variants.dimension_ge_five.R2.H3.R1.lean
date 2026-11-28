import OMAReductions.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R2

-- Reduction PoincareConjecture.poincare_conjecture.variants.dimension_ge_five.R2.H3.R1 of step PoincareConjecture.poincare_conjecture.variants.dimension_ge_five.R2.H3

namespace OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R2_H3_R1

open Set Metric

/-- Stallings engulfing, in the form needed here: a contractible charted space whose
    complement of every compact set contains a punctured open ball is an increasing
    union of open Euclidean balls. -/
def H1 : Prop :=
  ∀ n : ℕ, 5 ≤ n → ∀ (X : Type) [TopologicalSpace X] [T2Space X]
  [SecondCountableTopology X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [ContractibleSpace X],
  (∀ K : Set X, IsCompact K → ∃ U : Set X, IsOpen U ∧ IsCompact Uᶜ ∧ Disjoint K U ∧
    ∃ (c : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r ∧ Nonempty (U ≃ₜ ↥(ball c r \ {c}))) →
  ∃ V : ℕ → Set X,
    (∀ i, IsOpen (V i)) ∧
    (∀ i, Nonempty (V i ≃ₜ EuclideanSpace ℝ (Fin n))) ∧
    (∀ i, V i ⊆ V (i+1)) ∧
    (⋃ i, V i) = univ

/-- Brown's monotone union theorem: an increasing union of open Euclidean balls is
    homeomorphic to Euclidean space. -/
def H2 : Prop :=
  ∀ n : ℕ, ∀ (X : Type) [TopologicalSpace X],
  (∃ V : ℕ → Set X,
    (∀ i, IsOpen (V i)) ∧
    (∀ i, Nonempty (V i ≃ₜ EuclideanSpace ℝ (Fin n))) ∧
    (∀ i, V i ⊆ V (i+1)) ∧
    (⋃ i, V i) = univ) →
  Nonempty (X ≃ₜ EuclideanSpace ℝ (Fin n))

theorem main : H1 → H2 → OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R2.H3 := by
  intro hEngulf hBrown n hn X _ _ _ _ _ hEnd
  exact hBrown n X (hEngulf n hn X hEnd)

end OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R2_H3_R1
