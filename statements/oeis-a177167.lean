import Mathlib

/-!
# A177167: Quadratic convolution recurrence a(0) = 1, a(1) = 10, a(n+1) = sum a(p)*a(n-p) - 1

Source: https://oeis.org/A177167

Conjecture (R. J. Mathar):
For all `n ≥ 4`,
`(n + 1) * a(n) + 2 * (1 - 3*n) * a(n - 1) + (59 - 27*n) * a(n - 2)`
`+ 4 * (18*n - 55) * a(n - 3) + 40 * (4 - n) * a(n - 4) = 0`.

Conventions:
- Offset: `0`, with initial terms `1, 10, 19, 137, 653, 4406, 27077, 185856, ...`.
- Computed in `ℤ` via structural recursion accumulating the prefix list `[a 0, ..., a n]`.
-/

namespace OMA.S_oeis_a177167

/-- Prefix list `[a 0, a 1, ..., a n]` of the sequence A177167. -/
def aList : ℕ → List ℤ
  | 0 => [1]
  | 1 => [1, 10]
  | n + 2 =>
    let prev := aList (n + 1)
    let next := (∑ p ∈ Finset.range (n + 2), prev.getD p 0 * prev.getD (n + 1 - p) 0) - 1
    prev ++ [next]

/-- The sequence A177167. -/
def a (n : ℕ) : ℤ := (aList n).getD n 0

/-- Conjecture (R. J. Mathar): P-recursive linear recurrence for A177167 for `n ≥ 4`. -/
theorem main :
    ∀ n : ℕ, 4 ≤ n →
      ((n : ℤ) + 1) * a n
      + 2 * (1 - 3 * (n : ℤ)) * a (n - 1)
      + (59 - 27 * (n : ℤ)) * a (n - 2)
      + 4 * (18 * (n : ℤ) - 55) * a (n - 3)
      + 40 * (4 - (n : ℤ)) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a177167
