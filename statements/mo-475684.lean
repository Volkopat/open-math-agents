import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Complex.Module

/-!
# A rank-one matrix in a real subspace of Hermitian matrices

Source: Michał Jan, https://mathoverflow.net/questions/475684

The question asks whether every real subspace of the Hermitian n-by-n matrices,
of dimension (n-1)^2+1 and containing the identity, contains a rank-one matrix.
The real scalar field is explicit in the discussion: with complex coefficients,
the corresponding complex-subspace assertion has a different answer.

We use an actual real submodule of complex matrices, require every member to be
Hermitian, and take its dimension over the reals. Matrix rank is over the complex
numbers. The subspace formulation is equivalent to the source's linearly
independent family with the identity as its first member.
-/

namespace OMA.S_mo_475684

theorem main :
    ∀ n : ℕ, 0 < n → ∀ S : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ),
      Module.finrank ℝ S = (n - 1) ^ 2 + 1 →
      (1 : Matrix (Fin n) (Fin n) ℂ) ∈ S →
      (∀ A ∈ S, A.IsHermitian) →
      ∃ A ∈ S, A.rank = 1 := by
  sorry

end OMA.S_mo_475684
