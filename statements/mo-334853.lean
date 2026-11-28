import Mathlib

namespace OMA.S_mo_334853

open scoped TensorProduct

/-- Every positive integer occurs as the Mordell–Weil rank of an elliptic curve
over a number field that may depend on the requested rank. -/
theorem main :
    ∀ n : ℕ, 0 < n →
      ∃ (K : Type) (fieldK : Field K),
        letI : Field K := fieldK
        letI : DecidableEq K := Classical.decEq K
        NumberField K ∧
          ∃ E : WeierstrassCurve K, E.IsElliptic ∧
            Module.rank ℚ (ℚ ⊗[ℤ] E.toAffine.Point) = (n : Cardinal) := by
  sorry

end OMA.S_mo_334853
