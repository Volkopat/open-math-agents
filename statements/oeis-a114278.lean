import Mathlib

/-!
# Row sums of the inverse Sierpiński-related triangle A114278

Column k has generating function x^k times the binomial-parity
polynomial of row k divided by (1−x)^(k+1). Expanding the denominator
gives the finite coefficient formula used in entry. For k>n it is zero.

The conjecture says that inverse row n sums to 0^n (one for row zero).
For a unit lower triangular matrix that row is the last row of the
inverse of the leading (n+1)-by-(n+1) block, so the sum is finite.
Source: https://oeis.org/A114278
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a114278
open Finset Matrix

def entry (n k : ℕ) : ℕ :=
  ∑ j ∈ range (k+1), (Nat.choose k j % 2) * Nat.choose (n-j) k

def corner (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℚ :=
  Matrix.of fun i j => (entry i.val j.val : ℚ)

theorem main : ∀ n : ℕ, ∑ j : Fin (n+1), (corner n)⁻¹ (Fin.last n) j = (0:ℚ)^n := by
  sorry

end OMA.S_oeis_a114278
