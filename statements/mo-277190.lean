import Mathlib

/-!
# Eigenvalues of block-Hermitian matrices with zero diagonal blocks

Unwieldy Bob asks for the spectrum of the Hermitian dilation of a square complex
matrix, including what multiplicity two for its original eigenvalues implies.
David Handelman and Surb identify the singular values in the comments. The
factorization below counts both signs with algebraic multiplicity, including
zero. A matrix with characteristic polynomial `(X - 1)²` can have a dilation
with four simple eigenvalues.

Source: https://mathoverflow.net/questions/277190
-/

namespace OMA.S_mo_277190

open Polynomial Matrix
open scoped Polynomial ComplexOrder

/-- Hermitian matrix with the original matrix and its adjoint as off-diagonal blocks. -/
noncomputable def dilation {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :=
  fromBlocks 0 M M.conjTranspose 0

/-- Singular values enumerated with multiplicity via the eigenvalues of `M M*`. -/
noncomputable def singular {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : ℝ :=
  Real.sqrt ((posSemidef_self_mul_conjTranspose M).isHermitian.eigenvalues i)

/-- The dilation has the signed singular values as its eigenvalues. Repeated eigenvalues
of the input do not force repeated eigenvalues of the dilation. -/
theorem main : (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ),
    (dilation M).charpoly = ∏ i, ((X - C (singular M i : ℂ)) * (X + C (singular M i : ℂ)))) ∧
    ∃ M : Matrix (Fin 2) (Fin 2) ℂ, M.charpoly = (X - 1)^2 ∧ (dilation M).charpoly.Separable := by
  sorry

end OMA.S_mo_277190
