import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.LinearIndependent.Defs

namespace OMA.S_mo_363158

/-- A polynomial map separating the union of independent hyperplanes from its
complement has total coordinate degree at least the number of hyperplanes. -/
theorem main :
    ∀ (K : Type*) [Field K] (n : ℕ)
      (forms : Fin n → (Fin n → K) →ₗ[K] K),
      LinearIndependent K forms →
        ∀ P : Fin n → MvPolynomial (Fin n) K,
          let X : Set (Fin n → K) := {x | ∃ i : Fin n, forms i x = 0}
          let F : (Fin n → K) → (Fin n → K) := fun x i => MvPolynomial.eval x (P i)
          Disjoint (F '' X) (F '' Xᶜ) →
            n ≤ ∑ i : Fin n, (P i).totalDegree := by
  sorry

end OMA.S_mo_363158
