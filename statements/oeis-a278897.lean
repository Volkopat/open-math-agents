import Mathlib

/-!
# Positivity of the first series of Hankel determinants of the Bell numbers at squares

Source: Karol A. Penson, https://oeis.org/A278897 (OEIS Foundation, CC BY-SA 4.0).
Credit: @connoranderson.

The sequence uses the determinant of the n by n matrix, including the empty
determinant at index zero. The entry in zero-based row i and column j is the
Bell number with index (i+j)².
-/

namespace OMA.S_oeis_a278897

def hankel (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => (Nat.bell ((i.val+j.val)^2) : ℤ)

/-- All Hankel determinants of the Bell numbers at square indices are positive. -/
theorem main : ∀ n : ℕ, 0 < (hankel n).det := by
  sorry

end OMA.S_oeis_a278897
