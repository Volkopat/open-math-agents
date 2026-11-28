import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Hadamard

/-!
# Characterization of PSD-squared matrices

Source: https://mathoverflow.net/questions/361272

This formalizes precise question 1: is every doubly nonnegative matrix the
entrywise squared modulus of a Hermitian positive semidefinite complex matrix?
Both classes consist of square matrices of the same size. `Matrix.PosSemidef`
includes Hermitian symmetry; entrywise conjugation in `psdSquared` does not
transpose the matrix. Entrywise real nonnegativity is stated explicitly using
real and imaginary parts. The source's separate comparison with the completely
positive cone is not part of this equality assertion.
-/

namespace OMA.S_mo_361272

open scoped ComplexOrder Matrix

def psdSquared (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {A | ∃ X : Matrix (Fin n) (Fin n) ℂ,
    X.PosSemidef ∧ A = X ⊙ X.map star}

def doublyNonnegative (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {A | A.PosSemidef ∧ ∀ i j, (A i j).im = 0 ∧ 0 ≤ (A i j).re}

theorem main : ∀ n : ℕ, psdSquared n = doublyNonnegative n := by
  sorry

end OMA.S_mo_361272
