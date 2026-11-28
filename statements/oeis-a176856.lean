import Mathlib

/-!
# A176856: Quadratic convolution recurrence a(0) = 1, a(1) = 2, a(n+1) = sum a(p)*a(n-p) - (n+1)

Source: https://oeis.org/A176856

Conjecture (R. J. Mathar):
For all `n ≥ 5`,
`(n + 1) * a(n) + (-7*n + 2) * a(n - 1) + (11*n - 13) * a(n - 2)`
`+ (7*n - 32) * a(n - 3) + 2 * (-10*n + 41) * a(n - 4) + 8 * (n - 5) * a(n - 5) = 0`.

Conventions:
- Offset: `0`, with initial terms `1, 2, 2, 5, 14, 47, 164, 590, ...`.
- Computed in `ℤ` via structural recursion accumulating the prefix list `[a 0, ..., a n]`.
-/

namespace OMA.S_oeis_a176856

/-- Prefix list `[a 0, a 1, ..., a n]` of the sequence A176856. -/
def aList : ℕ → List ℤ
  | 0 => [1]
  | 1 => [1, 2]
  | n + 2 =>
    let prev := aList (n + 1)
    let next := (∑ p ∈ Finset.range (n + 2), prev.getD p 0 * prev.getD (n + 1 - p) 0)
      - ((n : ℤ) + 2)
    prev ++ [next]

/-- The sequence A176856. -/
def a (n : ℕ) : ℤ := (aList n).getD n 0

/-- Conjecture (R. J. Mathar): P-recursive linear recurrence for A176856 for `n ≥ 5`. -/
theorem main :
    ∀ n : ℕ, 5 ≤ n →
      ((n : ℤ) + 1) * a n
      + (-7 * (n : ℤ) + 2) * a (n - 1)
      + (11 * (n : ℤ) - 13) * a (n - 2)
      + (7 * (n : ℤ) - 32) * a (n - 3)
      + 2 * (-10 * (n : ℤ) + 41) * a (n - 4)
      + 8 * ((n : ℤ) - 5) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a176856
