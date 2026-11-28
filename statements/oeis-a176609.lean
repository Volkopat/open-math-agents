import Mathlib

/-!
# A176609: Quadratic convolution recurrence a(0) = 1, a(1) = 5, a(n+1) = sum a(p)*a(n-p) + 1

Source: https://oeis.org/A176609

Conjecture (R. J. Mathar):
For all `n ≥ 4`,
`(n + 1) * a(n) + 2 * (-3*n + 1) * a(n - 1) + (-7*n + 19) * a(n - 2)`
`+ 24 * (n - 3) * a(n - 3) + 12 * (-n + 4) * a(n - 4) = 0`.

Conventions:
- Offset: `0`, with initial terms `1, 5, 11, 48, 207, 1016, 5159, ...`.
- Computed in `ℤ` via structural recursion accumulating the prefix list `[a 0, ..., a n]`.
-/

namespace OMA.S_oeis_a176609

/-- Prefix list `[a 0, a 1, ..., a n]` of the sequence A176609. -/
def aList : ℕ → List ℤ
  | 0 => [1]
  | 1 => [1, 5]
  | n + 2 =>
    let prev := aList (n + 1)
    let next := (∑ p ∈ Finset.range (n + 2), prev.getD p 0 * prev.getD (n + 1 - p) 0) + 1
    prev ++ [next]

/-- The sequence A176609. -/
def a (n : ℕ) : ℤ := (aList n).getD n 0

/-- Conjecture (R. J. Mathar): P-recursive linear recurrence for A176609 for `n ≥ 4`. -/
theorem main :
    ∀ n : ℕ, 4 ≤ n →
      ((n : ℤ) + 1) * a n
      + 2 * (-3 * (n : ℤ) + 1) * a (n - 1)
      + (-7 * (n : ℤ) + 19) * a (n - 2)
      + 24 * ((n : ℤ) - 3) * a (n - 3)
      + 12 * (-(n : ℤ) + 4) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a176609
