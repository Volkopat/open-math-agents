import Mathlib

/-!
# Inverse row sums of the generalized Pascal triangle A114213

OEIS A114213 gives the entry in row n, column k as the parity of the
sum of choose(k,j) choose(n-k,j) over the even j from 0 to n-k.
Both indices start at zero. Entries above the diagonal are zero.

The conjecture concerns the ordinary matrix inverse of this integer
triangle. Its nth row can be read from the inverse of the leading
(n+1)-by-(n+1) block over the rationals.
Source: https://oeis.org/A114213
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a114213

def entry (n k : ℕ) : ℕ :=
  if k ≤ n then
    (∑ j ∈ Finset.range (n - k + 1),
      if j % 2 = 0 then Nat.choose k j * Nat.choose (n - k) j else 0) % 2
  else 0

def corner (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  Matrix.of fun i j => (entry i.val j.val : ℚ)

theorem main : ∀ n : ℕ,
    ∑ j : Fin (n + 1), (corner n)⁻¹ (Fin.last n) j = (0 : ℚ) ^ n := by
  sorry

end OMA.S_oeis_a114213
