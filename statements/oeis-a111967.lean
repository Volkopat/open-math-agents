import Mathlib

/-!
# The row sums of the inverse triangle A111967

The zero-based triangle A101688 has entry 1 at (i,j) exactly when
j ≤ i ≤ 2j. This is the support of the binomial coefficient
choose(j,i-j) on and below the diagonal, as recorded by Paul Barry.
A111967 is its ordinary matrix inverse. As the triangle is unit lower
triangular, row n of that inverse is row n of the inverse of the leading
(n+1)-by-(n+1) block. A036987 is 1 exactly at indices 2^r-1.
Sources: https://oeis.org/A111967, https://oeis.org/A101688,
https://oeis.org/A036987
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a111967

def corner (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℚ :=
  Matrix.of fun i j => if j.val ≤ i.val ∧ i.val ≤ 2*j.val then 1 else 0

noncomputable def fredholm (j : ℕ) : ℚ := by
  classical exact if ∃ r : ℕ, j+1 = 2^r then 1 else 0

theorem main : ∀ n : ℕ, (∑ j : Fin (n+1), (corner n)⁻¹ (Fin.last n) j) = fredholm n := by
  sorry

end OMA.S_oeis_a111967
