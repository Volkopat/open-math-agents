import Mathlib

/-!
# Complex unit-vector correlations need not be unitary correlations

Source: user3826143, https://mathoverflow.net/questions/453669 (CC BY-SA).
The four-vector obstruction is known from Corollary 2.11 of Ken Dykema and
Kate Juschenko, "Matrices of unitary moments", https://arxiv.org/abs/0901.0288.
Formalization with rational coordinates: @connoranderson.

The complex inner product is conjugate-linear in the first argument.
For matrices of size N, the normalized Hilbert–Schmidt product divides the
usual trace inner product by N. Four vectors in complex dimension two suffice
for a counterexample in every positive matrix dimension.
-/

namespace OMA.S_mo_453669
open Matrix
abbrev Mat (N : ℕ) := Matrix (Fin N) (Fin N) ℂ

theorem main : ∃ v : Fin 4 → Fin 2 → ℂ,
    (∀ i, star (v i) ⬝ᵥ v i = 1) ∧ ∀ N : ℕ, 0 < N →
      ¬ ∃ U : Fin 4 → Matrix.unitaryGroup (Fin N) ℂ, ∀ i j,
        (((U i : Mat N)ᴴ * (U j : Mat N)).trace / (N : ℂ)) = star (v i) ⬝ᵥ v j := by
  sorry
end OMA.S_mo_453669
