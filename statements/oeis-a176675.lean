import Mathlib

/-!
# A176675: Quadratic convolution recurrence a(0) = 1, a(1) = 0, a(n+1) = sum a(p)*a(n-p) - 1

Source: https://oeis.org/A176675

Conjecture (R. J. Mathar):
For all `n ≥ 3`,
`(n + 1) * a(n) + 2 * (-3*n + 1) * a(n - 1) + (13*n - 21) * a(n - 2)`
`+ 4 * (-2*n + 5) * a(n - 3) = 0`.

Conventions:
- Offset: `0`, with initial terms `1, 0, -1, -3, -7, -14, -23, -24, 21, ...`.
- Computed in `ℤ` via structural recursion accumulating the prefix list `[a 0, ..., a n]`.
-/

namespace OMA.S_oeis_a176675

/-- Prefix list `[a 0, a 1, ..., a n]` of the sequence A176675. -/
def aList : ℕ → List ℤ
  | 0 => [1]
  | 1 => [1, 0]
  | n + 2 =>
    let prev := aList (n + 1)
    let next := (∑ p ∈ Finset.range (n + 2), prev.getD p 0 * prev.getD (n + 1 - p) 0) - 1
    prev ++ [next]

/-- The sequence A176675. -/
def a (n : ℕ) : ℤ := (aList n).getD n 0

/-- Conjecture (R. J. Mathar): P-recursive linear recurrence for A176675 for `n ≥ 3`. -/
theorem main :
    ∀ n : ℕ, 3 ≤ n →
      ((n : ℤ) + 1) * a n
      + 2 * (-3 * (n : ℤ) + 1) * a (n - 1)
      + (13 * (n : ℤ) - 21) * a (n - 2)
      + 4 * (-2 * (n : ℤ) + 5) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a176675
