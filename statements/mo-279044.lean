import Mathlib

/-!
For positive semidefinite B its real spectral power is obtained by applying
the scalar real power to the eigenvalues. At exponent zero it is the identity.
The two traces are real, since each is the trace of a product of Hermitian matrices.
Source: https://mathoverflow.net/questions/279044/a-conjectured-trace-inequality-for-some-products-of-powers-of-matrices-ii
-/
namespace OMA.S_mo_279044
open scoped ComplexOrder

theorem main : ∀ (n : ℕ) (B R : Matrix (Fin n) (Fin n) ℂ) (hB : B.PosSemidef),
    R.IsHermitian → ∀ s : ℝ, 0 ≤ s →
      (Matrix.trace (hB.isHermitian.cfc (fun x => x ^ s) * (1 + B * R^2 * B)⁻¹)).re ≤
      (Matrix.trace (hB.isHermitian.cfc (fun x => x ^ s) * (1 + R * B^2 * R)⁻¹)).re := by
  sorry
end OMA.S_mo_279044
