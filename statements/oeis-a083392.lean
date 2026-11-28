import Mathlib

/-!
# OEIS A083392

Spezia's determinant conjecture, proved by Sela Fried, Theorem 4 of
https://arxiv.org/abs/2606.09913.
-/

open scoped BigOperators Matrix

namespace OMA.S_oeis_a083392

/-- The alternating partial sum of the first triangular numbers through index m. -/
def a (m : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (m+1), (-1 : ℤ)^i * ((i*(i+1)/2 : ℕ) : ℤ)

/-- The symmetric Toeplitz matrix with first row 0, 1, 1, 2, 2, … . -/
def toeplitz (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => ((((i.val - j.val) + (j.val - i.val) + 1) / 2 : ℕ) : ℤ)

/-- Spezia's conjecture identifying the determinant with an alternating triangular sum. -/
theorem main : ∀ n : ℕ, 0 < n → (toeplitz n).det = a (n-1) := by
  sorry

end OMA.S_oeis_a083392
