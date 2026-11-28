import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Perm
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace OMA.S_mo_126666

abbrev RealMatrix (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

/-- Singular values in descending order, from the eigenvalues of Aᵀ A. -/
noncomputable def singularValue {d : ℕ} (A : RealMatrix d) (i : Fin d) : ℝ :=
  Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀
    (Fin.cast (Fintype.card_fin d).symm i))

/-- The proposed weak majorization fails for a family of real positive
definite matrices. -/
theorem main :
    ∃ (n d : ℕ) (A : Fin n → RealMatrix d),
      0 < n ∧ (∀ i : Fin n, (A i).PosDef) ∧
        let productMean : RealMatrix d :=
          (1 / (n.factorial : ℝ)) •
            (∑ order : Equiv.Perm (Fin n), (List.ofFn fun i => A (order i)).prod)
        let arithmeticMean : RealMatrix d :=
          (1 / (n : ℝ)) • (∑ i : Fin n, A i)
        ∃ k : Fin d,
          (∑ i ∈ Finset.Iic k, singularValue arithmeticMean i) <
            ∑ i ∈ Finset.Iic k, (singularValue productMean i) ^ (1 / (n : ℝ)) := by
  sorry

end OMA.S_mo_126666
