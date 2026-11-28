import Mathlib

/-!
# A176607: Quadratic convolution recurrence a(0) = 1, a(1) = 4, a(n+1) = sum a(p)*a(n-p) + 1

Source: https://oeis.org/A176607

Conjecture (R. J. Mathar):
For all `n ≥ 4`,
`(n + 1) * a(n) + 2 * (-3*n + 1) * a(n - 1) + (-3*n + 11) * a(n - 2)`
`+ 16 * (n - 3) * a(n - 3) + 8 * (-n + 4) * a(n - 4) = 0`.

Conventions:
- Offset: `0`, with initial terms `1, 4, 9, 35, 143, 648, 3071, ...`.
- Computed in `ℤ` via structural recursion accumulating the prefix list `[a 0, ..., a n]`.
-/

namespace OMA.S_oeis_a176607

/-- Prefix list `[a 0, a 1, ..., a n]` of the sequence A176607. -/
def aList : ℕ → List ℤ
  | 0 => [1]
  | 1 => [1, 4]
  | n + 2 =>
    let prev := aList (n + 1)
    let next := (∑ p ∈ Finset.range (n + 2), prev.getD p 0 * prev.getD (n + 1 - p) 0) + 1
    prev ++ [next]

/-- The sequence A176607. -/
def a (n : ℕ) : ℤ := (aList n).getD n 0

/-- Conjecture (R. J. Mathar): P-recursive linear recurrence for A176607 for `n ≥ 4`. -/
theorem main :
    ∀ n : ℕ, 4 ≤ n →
      ((n : ℤ) + 1) * a n
      + 2 * (-3 * (n : ℤ) + 1) * a (n - 1)
      + (-3 * (n : ℤ) + 11) * a (n - 2)
      + 16 * ((n : ℤ) - 3) * a (n - 3)
      + 8 * (-(n : ℤ) + 4) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a176607
