import Mathlib.Analysis.Matrix.Spectrum

/-!
# Ranks of commutators of normal matrices

Source: https://mathoverflow.net/questions/469453
Cross-post: https://math.stackexchange.com/questions/4897021

For two normal complex matrices whose spectra lie in the union of the real
axis and the unit circle, must replacing the first matrix by its adjoint
preserve the rank of their commutator? `IsStarNormal` is the actual normality
predicate for the matrix star operation, which is conjugate transpose. The
spectrum and matrix rank are Mathlib's standard definitions. A complex number
lies on the real axis exactly when its imaginary part is zero.
-/

namespace OMA.S_mo_469453

open scoped Matrix

theorem main : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ),
    IsStarNormal A → IsStarNormal B →
    (∀ z ∈ spectrum ℂ A, z.im = 0 ∨ ‖z‖ = 1) →
    (∀ z ∈ spectrum ℂ B, z.im = 0 ∨ ‖z‖ = 1) →
    (A * B - B * A).rank = (Aᴴ * B - B * Aᴴ).rank := by
  sorry

end OMA.S_mo_469453
