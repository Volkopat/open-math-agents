import Mathlib

/-!
# A176753: Quadratic convolution recurrence a(0) = 1, a(1) = 1, a(n+1) = sum a(p)*a(n-p) - 2

Source: https://oeis.org/A176753

Conjecture (R. J. Mathar):
For all `n ≥ 4`,
`(n + 1) * a(n) + 2 * (1 - 3*n) * a(n - 1) + (9*n - 13) * a(n - 2)`
`+ 2 * (2*n - 9) * a(n - 3) + 8 * (4 - n) * a(n - 4) = 0`.

Conventions:
- Offset: `0`, with initial terms `1, 1, 0, -1, -4, -12, -34, -93, ...`.
- Computed in `ℤ` via structural recursion accumulating the prefix list `[a 0, ..., a n]`.
-/

namespace OMA.S_oeis_a176753

/-- Prefix list `[a 0, a 1, ..., a n]` of the sequence A176753. -/
def aList : ℕ → List ℤ
  | 0 => [1]
  | 1 => [1, 1]
  | n + 2 =>
    let prev := aList (n + 1)
    let next := (∑ p ∈ Finset.range (n + 2), prev.getD p 0 * prev.getD (n + 1 - p) 0) - 2
    prev ++ [next]

/-- The sequence A176753. -/
def a (n : ℕ) : ℤ := (aList n).getD n 0

/-- Conjecture (R. J. Mathar): P-recursive linear recurrence for A176753 for `n ≥ 4`. -/
theorem main :
    ∀ n : ℕ, 4 ≤ n →
      ((n : ℤ) + 1) * a n
      + 2 * (1 - 3 * (n : ℤ)) * a (n - 1)
      + (9 * (n : ℤ) - 13) * a (n - 2)
      + 2 * (2 * (n : ℤ) - 9) * a (n - 3)
      + 8 * (4 - (n : ℤ)) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a176753
