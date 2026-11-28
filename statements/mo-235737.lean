import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped ComplexOrder

namespace OMA.S_mo_235737

/-- If A and B are positive definite and AUB is Hermitian, conjugating A by
the unitary U cannot increase the spectral radius of the sum. -/
theorem main :
    ∀ (n : ℕ), 0 < n →
      ∀ (A B U : Matrix (Fin n) (Fin n) ℂ),
        A.PosDef → B.PosDef →
          U.conjTranspose * U = 1 → U * U.conjTranspose = 1 →
            (A * U * B).IsHermitian →
              spectralRadius ℂ (U.conjTranspose * A * U + B) ≤
                spectralRadius ℂ (A + B) := by
  sorry

end OMA.S_mo_235737
