import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Linear general position and quadratic images

Source: https://mathoverflow.net/questions/67775
Question by vanvu, 14 June 2011; CC BY-SA 3.0.
Credit: @etaubman

This is the explicit conjecture in the source: six integer vectors in linear
general position have linearly independent quadratic images. General position
means every three distinct vectors form a nonsingular matrix. For integer
square matrices, nonzero determinant is equivalent to linear independence
over the rationals, reals, or integers. The quadratic coordinates appear in
the exact order given in the question.
-/

namespace OMA.S_mo_67775

def quadratic (x : Fin 3 → ℤ) : Fin 6 → ℤ :=
  ![x 0 ^ 2, x 1 ^ 2, x 2 ^ 2, x 0 * x 1, x 0 * x 2, x 1 * x 2]

def tripleMatrix (u : Fin 6 → Fin 3 → ℤ) (i j k : Fin 6) :
    Matrix (Fin 3) (Fin 3) ℤ := ![u i, u j, u k]

def GeneralPosition (u : Fin 6 → Fin 3 → ℤ) : Prop :=
  ∀ i j k : Fin 6, i ≠ j → i ≠ k → j ≠ k → (tripleMatrix u i j k).det ≠ 0

def quadraticMatrix (u : Fin 6 → Fin 3 → ℤ) : Matrix (Fin 6) (Fin 6) ℤ :=
  fun i => quadratic (u i)

theorem main : ∀ u : Fin 6 → Fin 3 → ℤ,
    GeneralPosition u → (quadraticMatrix u).det ≠ 0 := by
  sorry

end OMA.S_mo_67775
