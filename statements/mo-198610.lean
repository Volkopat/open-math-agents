import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace

open scoped ComplexOrder

namespace OMA.S_mo_198610

/-- The Schatten one norm is the sum of square roots of the Gram matrix eigenvalues. -/
noncomputable def traceNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ i : Fin n, Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i)

/-- The proposed weighted Powers–Størmer estimate with a single universal constant. -/
theorem main :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (A B X : Matrix (Fin n) (Fin n) ℂ),
        A.PosSemidef → B.PosSemidef → X.PosSemidef →
          X * X = A * A + B * B →
            (Matrix.trace ((A - B) * (X * X) * (A - B))).re ≤
              C * traceNorm (X * (A * A) * X - X * (B * B) * X) := by
  sorry

end OMA.S_mo_198610
