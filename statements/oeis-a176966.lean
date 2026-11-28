import Mathlib

/-!
# A176966: Quadratic convolution recurrence a(0) = 1, a(1) = 4, a(n+1) = sum a(p)*a(n-p) - (n+1) + 1

Source: https://oeis.org/A176966

Conjecture (R. J. Mathar):
For all `n ≥ 5`,
`(n + 1) * a(n) + (-7*n + 2) * a(n - 1) + 3 * (n + 1) * a(n - 2)`
`+ 9 * (3*n - 10) * a(n - 3) + 36 * (-n + 4) * a(n - 4) + 12 * (n - 5) * a(n - 5) = 0`.

Conventions:
- Offset: `0`, with initial terms `1, 4, 7, 28, 109, 487, 2233, 10666, ...`.
- Computed in `ℤ` via structural recursion accumulating the prefix list `[a 0, ..., a n]`.
-/

namespace OMA.S_oeis_a176966

/-- Prefix list `[a 0, a 1, ..., a n]` of the sequence A176966. -/
def aList : ℕ → List ℤ
  | 0 => [1]
  | 1 => [1, 4]
  | n + 2 =>
    let prev := aList (n + 1)
    let next := (∑ p ∈ Finset.range (n + 2), prev.getD p 0 * prev.getD (n + 1 - p) 0)
      - ((n : ℤ) + 2) + 1
    prev ++ [next]

/-- The sequence A176966. -/
def a (n : ℕ) : ℤ := (aList n).getD n 0

/-- Conjecture (R. J. Mathar): P-recursive linear recurrence for A176966 for `n ≥ 5`. -/
theorem main :
    ∀ n : ℕ, 5 ≤ n →
      ((n : ℤ) + 1) * a n
      + (-7 * (n : ℤ) + 2) * a (n - 1)
      + 3 * ((n : ℤ) + 1) * a (n - 2)
      + 9 * (3 * (n : ℤ) - 10) * a (n - 3)
      + 36 * (-(n : ℤ) + 4) * a (n - 4)
      + 12 * ((n : ℤ) - 5) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a176966
