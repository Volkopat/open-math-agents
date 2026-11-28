import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Equality in the entrywise spectral radius bound

Source: https://mathoverflow.net/questions/351449/case-of-equality-in-entrywise-spectral-radius-bound
Question by Julian (2020), CC BY-SA 4.0.
Credit: @etaubman

The proposed necessary condition is a single common complex phase, not
conjugation by a diagonal unitary matrix. The real matrix b is automatically
nonnegative under the entrywise norm hypothesis.
-/

namespace OMA.S_mo_351449

theorem main :
  ∀ (n : ℕ) (a : Matrix (Fin n) (Fin n) ℂ) (b : Matrix (Fin n) (Fin n) ℝ),
    (∀ i j, ‖a i j‖ ≤ b i j) →
    spectralRadius ℂ a = spectralRadius ℂ (b.map (algebraMap ℝ ℂ)) →
    ∃ φ : ℝ, φ ∈ Set.Icc 0 (2 * Real.pi) ∧
      ∀ i j, a i j = Complex.exp (Complex.I * (φ : ℂ)) * (b i j : ℂ)
 := by
  sorry

end OMA.S_mo_351449
