import Mathlib

/-!
# Positive semidefiniteness of a block Toeplitz matrix with dominant diagonal

Source: https://mathoverflow.net/questions/231913
Asked by MathOverflow user Obriareos.

Let `p ∈ ℕ`, let `H` be a Hilbert space and let `C_{1-p}, ..., C_{p-1}` be Hilbert-Schmidt
operators on `H` such that `C_0` is selfadjoint and positive semidefinite, `C_l^* = C_{-l}`
for every `l`, and `‖C_0‖ ≥ ‖C_l‖` for every `l` (Hilbert-Schmidt norms). Then the block
Toeplitz matrix `Γ_p = (C_{i-j})_{i,j = 1, ..., p}` is selfadjoint and diagonally dominant
with positive semidefinite diagonal blocks. The question asks: is `Γ_p` positive
semidefinite?

Translation choices.
* The Hilbert space is taken to be finite dimensional, `H = ℂ^d` for an arbitrary `d`; then
  every operator is Hilbert-Schmidt, an operator is a `d × d` complex matrix, the adjoint is
  the conjugate transpose `ᴴ`, and the squared Hilbert-Schmidt norm is the sum of the squared
  absolute values of the entries (`hsNormSq`). Comparing squared norms is the same as
  comparing norms.
* The blocks are given by a function `C : ℤ → Matrix (Fin d) (Fin d) ℂ`; only the values
  with `|l| < p` enter `Γ_p`, and the norm condition is imposed exactly for those `l`.
* `Γ_p` is the operator on `H^p`, i.e. the matrix indexed by `Fin p × Fin d` whose block in
  position `(i, j)` is `C (i - j)`; positive semidefiniteness is `Matrix.PosSemidef`.
* Positive semidefiniteness uses the order on `ℂ` from `ComplexOrder`.
* `main` is the affirmative answer to the first question: `Γ_p` is always positive
  semidefinite.
-/

namespace OMA.S_mo_231913

open Matrix
open scoped ComplexOrder

/-- The block Toeplitz matrix `(C_{i-j})_{i,j < p}`, indexed by `Fin p × Fin d`. -/
def blockToeplitz (p d : ℕ) (C : ℤ → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin p × Fin d) (Fin p × Fin d) ℂ :=
  Matrix.of fun a b => C ((a.1 : ℤ) - (b.1 : ℤ)) a.2 b.2

/-- The squared Hilbert-Schmidt (Frobenius) norm of a square complex matrix. -/
noncomputable def hsNormSq {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ∑ x, ∑ y, ‖A x y‖ ^ 2

theorem main :
    ∀ p d : ℕ, ∀ C : ℤ → Matrix (Fin d) (Fin d) ℂ,
      (C 0).PosSemidef →
      (∀ l : ℤ, C (-l) = (C l)ᴴ) →
      (∀ l : ℤ, -(p : ℤ) < l → l < p → hsNormSq (C l) ≤ hsNormSq (C 0)) →
      (blockToeplitz p d C).PosSemidef := by
  sorry

end OMA.S_mo_231913
