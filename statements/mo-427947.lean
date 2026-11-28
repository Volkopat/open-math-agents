import Mathlib

/-!
# Unimodular eigenvalues of H-self-adjoint matrices

Source: https://mathoverflow.net/questions/427947
Asked by MathOverflow user Leo.

Let `A, H ∈ ℂ^{n×n}` with `H` Hermitian and invertible, and suppose `A = H⁻¹ A* H`, i.e. `A`
is `H`-self-adjoint. Assume moreover that `A` is invertible, that `A` is not `H`-unitary, and
that `A` has an eigenvalue `λ₀` with `|λ₀| = 1`. The asker conjectures that every eigenvector
`v` with `A v = λ₀ v` satisfies `A* v = conj(λ₀) v`.

Translation choices.
* Matrices are `Matrix (Fin n) (Fin n) ℂ`, `A*` is the conjugate transpose `Aᴴ`, and
  invertibility is expressed by `IsUnit` of the determinant.
* `A` is `H`-unitary when `A* H A = H`; the hypothesis is that this fails.
* `main` is the conjecture.
-/

namespace OMA.S_mo_427947

open Matrix

theorem main :
    ∀ (n : ℕ) (A H : Matrix (Fin n) (Fin n) ℂ), H.IsHermitian → IsUnit H.det →
      A = H⁻¹ * Aᴴ * H → IsUnit A.det → Aᴴ * H * A ≠ H →
      ∀ (μ : ℂ) (v : Fin n → ℂ), ‖μ‖ = 1 → v ≠ 0 → A *ᵥ v = μ • v →
        Aᴴ *ᵥ v = star μ • v := by
  sorry

end OMA.S_mo_427947
