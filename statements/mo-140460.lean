import Mathlib

/-!
# Trace norm inequality for the normalized discrete Fourier transform

Source: John, https://mathoverflow.net/questions/140460 .
The finite-dimensional trace norm has the variational formula
‖A‖₁ = sup { |tr(AU)| : U unitary }. The entries of the negative-exponent
Fourier matrix are powers of the inverse of exp(2πi/N), normalized by √N.

Credit: @connoranderson
-/

namespace OMA.S_mo_140460
open Matrix
open scoped ComplexOrder

noncomputable def traceNorm {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  sSup {r | ∃ U ∈ Matrix.unitaryGroup (Fin N) ℂ, r = ‖(A*U).trace‖}

noncomputable def fourier (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => ((Real.sqrt N : ℂ)⁻¹) *
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / N))⁻¹ ^ (i.val*j.val)

theorem main : ∀ (N : ℕ), 0<N → ∀ f g : Fin N → ℂ, (diagonal f).PosSemidef →
  traceNorm (diagonal f * fourier N * diagonal g * (fourier N).conjTranspose) ≤
    (Real.sqrt N)⁻¹ * traceNorm (diagonal f) * traceNorm (diagonal g) := by
  sorry

end OMA.S_mo_140460
