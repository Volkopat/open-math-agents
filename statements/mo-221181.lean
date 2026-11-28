import Mathlib

namespace OMA.S_mo_221181

/-- Can a finite Euclidean set fail to embed isometrically into some
infinite-dimensional Banach space? -/
theorem main :
    ∃ (d : ℕ) (F : Finset (EuclideanSpace ℝ (Fin d)))
      (X : Type) (addNorm : NormedAddCommGroup X),
      letI : NormedAddCommGroup X := addNorm
      ∃ scalar : NormedSpace ℝ X,
        letI : NormedSpace ℝ X := scalar
        CompleteSpace X ∧ ¬ FiniteDimensional ℝ X ∧
          ¬ ∃ embed : F → X, Isometry embed := by
  sorry

end OMA.S_mo_221181
