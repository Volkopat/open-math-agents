import Mathlib

/-!
# A176754: Quadratic convolution recurrence a(0) = 1, a(1) = 2, a(n+1) = sum a(p)*a(n-p) - 2

Source: https://oeis.org/A176754

Conjecture (R. J. Mathar):
For all `n ≥ 4`,
`(n + 1) * a(n) + 2 * (-3*n + 1) * a(n - 1) + 5 * (n - 1) * a(n - 2)`
`+ 6 * (2*n - 7) * a(n - 3) + 12 * (-n + 4) * a(n - 4) = 0`.

Conventions:
- Offset: `0`, with initial terms `1, 2, 2, 6, 18, 62, 218, 790, ...`.
- Computed in `ℤ` via structural recursion accumulating the prefix list `[a 0, ..., a n]`.
-/

namespace OMA.S_oeis_a176754

/-- Prefix list `[a 0, a 1, ..., a n]` of the sequence A176754. -/
def aList : ℕ → List ℤ
  | 0 => [1]
  | 1 => [1, 2]
  | n + 2 =>
    let prev := aList (n + 1)
    let next := (∑ p ∈ Finset.range (n + 2), prev.getD p 0 * prev.getD (n + 1 - p) 0) - 2
    prev ++ [next]

/-- The sequence A176754. -/
def a (n : ℕ) : ℤ := (aList n).getD n 0

/-- Conjecture (R. J. Mathar): P-recursive linear recurrence for A176754 for `n ≥ 4`. -/
theorem main :
    ∀ n : ℕ, 4 ≤ n →
      ((n : ℤ) + 1) * a n
      + 2 * (-3 * (n : ℤ) + 1) * a (n - 1)
      + 5 * ((n : ℤ) - 1) * a (n - 2)
      + 6 * (2 * (n : ℤ) - 7) * a (n - 3)
      + 12 * (-(n : ℤ) + 4) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a176754
