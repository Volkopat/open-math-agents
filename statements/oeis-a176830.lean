import Mathlib

/-!
# A176830: Quadratic convolution recurrence a(0) = 1, a(1) = 4, a(n+1) = sum a(p)*a(n-p) + n

Source: https://oeis.org/A176830

Conjecture (R. J. Mathar):
For all `n ≥ 5`,
`(n + 1) * a(n) + (-7*n + 2) * a(n - 1) + 3 * (n + 1) * a(n - 2)`
`+ (19*n - 62) * a(n - 3) + 4 * (-7*n + 29) * a(n - 4) + 12 * (n - 5) * a(n - 5) = 0`.

Conventions:
- Offset: `0`, with initial terms `1, 4, 9, 36, 147, 667, 3163, ...`.
- Computed in `ℤ` via structural recursion accumulating the prefix list `[a 0, ..., a n]`.
-/

namespace OMA.S_oeis_a176830

/-- Prefix list `[a 0, a 1, ..., a n]` of the sequence A176830. -/
def aList : ℕ → List ℤ
  | 0 => [1]
  | 1 => [1, 4]
  | n + 2 =>
    let prev := aList (n + 1)
    let next := (∑ p ∈ Finset.range (n + 2), prev.getD p 0 * prev.getD (n + 1 - p) 0)
      + ((n : ℤ) + 1)
    prev ++ [next]

/-- The sequence A176830. -/
def a (n : ℕ) : ℤ := (aList n).getD n 0

/-- Conjecture (R. J. Mathar): P-recursive linear recurrence for A176830 for `n ≥ 5`. -/
theorem main :
    ∀ n : ℕ, 5 ≤ n →
      ((n : ℤ) + 1) * a n
      + (-7 * (n : ℤ) + 2) * a (n - 1)
      + 3 * ((n : ℤ) + 1) * a (n - 2)
      + (19 * (n : ℤ) - 62) * a (n - 3)
      + 4 * (-7 * (n : ℤ) + 29) * a (n - 4)
      + 12 * ((n : ℤ) - 5) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a176830
