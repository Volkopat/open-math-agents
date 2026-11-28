import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic

/-!
# An inequality related to matrix trace

Source: https://mathoverflow.net/questions/454408
Question author: Wayne. Credit for formalization: @etaubman.

The source writes A as m-by-n and U as n-by-n, but its displayed products
require U to be m-by-m. We make this dimension correction explicitly.
The diagonal entries of Sigma are nonnegative, and absolute value is entrywise.
-/

namespace OMA.S_mo_454408

theorem main : ∀ (m n : ℕ), 0 < m → 0 < n →
    ∀ (A : Matrix (Fin m) (Fin n) ℝ)
      (U : Matrix (Fin m) (Fin m) ℝ) (σ : Fin m → ℝ),
    U.transpose * U = 1 → (∀ i, 0 ≤ σ i) →
      Matrix.trace (A * (A.transpose * U * Matrix.diagonal σ * U.transpose).map abs) ≤
        Matrix.trace (A * A.transpose * U * Matrix.diagonal σ * U.transpose) := by
  sorry

end OMA.S_mo_454408
