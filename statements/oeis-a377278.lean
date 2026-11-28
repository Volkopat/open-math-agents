import Mathlib

/-!
# Reciprocal row sums of the harmonic triangle A377278

Write d(k) = 2^k − 1. The row n has denominator d(k)d(k+1) at
columns 1 ≤ k < n and d(n) on the diagonal. The harmonic triangle uses
numerator one at every entry. Werner Schulte conjectured that its row
sum is A204243(n)/A005329(n).

The numerator is the determinant of the n-by-n leading principal
submatrix of A204242. Its first row and column are all ones, and the
remaining block is diagonal with entries d(2), ..., d(n). The denominator
A005329(n) is the product d(1)⋯d(n), where d(1)=1. Below r=n-1; this
includes the first row n=1 with an empty diagonal block.
Sources: https://oeis.org/A377278, https://oeis.org/A204243, https://oeis.org/A204242, https://oeis.org/A005329
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a377278
open Matrix Finset

def rowDivisor (k : ℕ) : ℚ := 2^k-1

def row (r : ℕ) : ℚ :=
  (∑ j ∈ range r, 1/(rowDivisor (j+1)*rowDivisor (j+2))) + 1/rowDivisor (r+1)

def principal (r : ℕ) : Matrix (Fin 1 ⊕ Fin r) (Fin 1 ⊕ Fin r) ℚ :=
  Matrix.fromBlocks (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 1)
    (Matrix.diagonal (fun i : Fin r => rowDivisor (i.val+2)))

def twoFactorial (r : ℕ) : ℚ := ∏ i : Fin r, rowDivisor (i.val+2)

theorem main : ∀ r : ℕ, row r = (principal r).det / twoFactorial r := by
  sorry

end OMA.S_oeis_a377278
