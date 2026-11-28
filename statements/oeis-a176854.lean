import Mathlib

/-!
# A176854: Quadratic convolution recurrence a(0) = 1, a(1) = 0, a(n+1) = sum a(p)*a(n-p) - (n+1)

Source: https://oeis.org/A176854

Conjecture (R. J. Mathar):
For all `n ≥ 4`,
`(n + 1) * a(n) + (-7*n + 2) * a(n - 1) + (19*n - 29) * a(n - 2)`
`+ (-17*n + 40) * a(n - 3) + 2 * (2*n - 7) * a(n - 4) = 0`.

Conventions:
- Offset: `0`, with initial terms `1, 0, -2, -7, -18, -37, -52, 10, ...`.
- Computed in `ℤ` via structural recursion accumulating the prefix list `[a 0, ..., a n]`.
-/

namespace OMA.S_oeis_a176854

/-- Prefix list `[a 0, a 1, ..., a n]` of the sequence A176854. -/
def aList : ℕ → List ℤ
  | 0 => [1]
  | 1 => [1, 0]
  | n + 2 =>
    let prev := aList (n + 1)
    let next := (∑ p ∈ Finset.range (n + 2), prev.getD p 0 * prev.getD (n + 1 - p) 0)
      - ((n : ℤ) + 2)
    prev ++ [next]

/-- The sequence A176854. -/
def a (n : ℕ) : ℤ := (aList n).getD n 0

/-- Conjecture (R. J. Mathar): P-recursive linear recurrence for A176854 for `n ≥ 4`. -/
theorem main :
    ∀ n : ℕ, 4 ≤ n →
      ((n : ℤ) + 1) * a n
      + (-7 * (n : ℤ) + 2) * a (n - 1)
      + (19 * (n : ℤ) - 29) * a (n - 2)
      + (-17 * (n : ℤ) + 40) * a (n - 3)
      + 2 * (2 * (n : ℤ) - 7) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a176854
