import Mathlib

/-!
# MathOverflow 40478

Source: https://mathoverflow.net/questions/40478
-/

namespace OMA.S_mo_40478

open Matrix Finset Set
open scoped BigOperators

def cyclicDiagonalSums {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    {i : Fin n // i.val ≠ 0} → ℝ :=
  fun i => ∑ j, A j (j+i.val)

def orthogonalCyclicImage {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Set ({i : Fin n // i.val ≠ 0} → ℝ) :=
  {v | ∃ R : Matrix (Fin n) (Fin n) ℝ,
    R.transpose*R = 1 ∧ R.det = 1 ∧ cyclicDiagonalSums (R.transpose*A*R) = v}

theorem main : (¬ (∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), ∃ R : Matrix (Fin n) (Fin n) ℝ,
      R.transpose*R=1 ∧ cyclicDiagonalSums (R.transpose*A*R)=0)) ∧
    (¬ (∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), Convex ℝ (orthogonalCyclicImage A))) := by
  sorry

end OMA.S_mo_40478
