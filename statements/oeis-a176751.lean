import Mathlib

/-!
# A176751: Quadratic convolution recurrence a(0) = 1, a(1) = 5, a(n+1) = sum a(p)*a(n-p) - 1

Source: https://oeis.org/A176751

Conjecture (R. J. Mathar):
For all `n ≥ 4`,
`(n + 1) * a(n) + 2 * (1 - 3*n) * a(n - 1) + (19 - 7*n) * a(n - 2)`
`+ 4 * (8*n - 25) * a(n - 3) + 20 * (4 - n) * a(n - 4) = 0`.

Conventions:
- Offset: `0`, with initial terms `1, 5, 9, 42, 173, 846, 4177, ...`.
- Computed in `ℤ` via structural recursion accumulating the prefix list `[a 0, ..., a n]`.
-/

namespace OMA.S_oeis_a176751

/-- Prefix list `[a 0, a 1, ..., a n]` of the sequence A176751. -/
def aList : ℕ → List ℤ
  | 0 => [1]
  | 1 => [1, 5]
  | n + 2 =>
    let prev := aList (n + 1)
    let next := (∑ p ∈ Finset.range (n + 2), prev.getD p 0 * prev.getD (n + 1 - p) 0) - 1
    prev ++ [next]

/-- The sequence A176751. -/
def a (n : ℕ) : ℤ := (aList n).getD n 0

/-- Conjecture (R. J. Mathar): P-recursive linear recurrence for A176751 for `n ≥ 4`. -/
theorem main :
    ∀ n : ℕ, 4 ≤ n →
      ((n : ℤ) + 1) * a n
      + 2 * (1 - 3 * (n : ℤ)) * a (n - 1)
      + (19 - 7 * (n : ℤ)) * a (n - 2)
      + 4 * (8 * (n : ℤ) - 25) * a (n - 3)
      + 20 * (4 - (n : ℤ)) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a176751
