import Mathlib

/-!
# A000382: Restricted permutations.

Source: https://oeis.org/A000382
Credit: @maxarndt132-svg

OEIS gives the recurrence without a starting index. At `n = 7` its right side
is `20 + 11 + 6 - 2 = 35`, while the listed term is 36. We interpret the
conjecture as starting at `n = 8`, where `36 + 20 + 11 - 2 = 65`.

We use the entry's alternative Maple program to define the sequence. At
`n = 8` the fourth column of https://oeis.org/A008305 gives `264 / 4 = 66`,
whereas A000382 lists 65.
-/

namespace OMA.S_oeis_a000382

/-- The row vector after `k` multiplications in Alois P. Heinz's Maple program. -/
private def matrixRow : ℕ → ℤ × ℤ × ℤ × ℤ
  | 0 => (11, 7, 4, 2)
  | k + 1 =>
      let (w, x, y, z) := matrixRow k
      (2 * w - z, w, x, y)

/-- A000382, using the fourth coordinate in the matrix branch of the program. -/
def a (n : ℕ) : ℤ :=
  if n < 4 then 0
  else if n = 4 then 6
  else (matrixRow (n - 2)).2.2.2

/-- The conjectured recurrence for A000382, with the starting index inferred above. -/
theorem main :
    ∀ n : ℕ, 8 ≤ n → a n = a (n - 1) + a (n - 2) + a (n - 3) - 2 := by
  sorry

end OMA.S_oeis_a000382
