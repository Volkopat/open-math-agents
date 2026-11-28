import Mathlib

/-!
# A177131: Quadratic convolution recurrence a(0) = 1, a(1) = 10, a(n+1) = sum a(p)*a(n-p) + 1

Source: https://oeis.org/A177131

Conjecture (R. J. Mathar):
For all `n ≥ 4`,
`(n + 1) * a(n) + 2 * (-3*n + 1) * a(n - 1) + (-27*n + 59) * a(n - 2)`
`+ 64 * (n - 3) * a(n - 3) + 32 * (-n + 4) * a(n - 4) = 0`.

Conventions:
- Offset: `0`, with initial terms `1, 10, 21, 143, 707, 4716, 29579, 203622, ...`.
- Computed in `ℤ` via structural recursion accumulating the prefix list `[a 0, ..., a n]`.
-/

namespace OMA.S_oeis_a177131

/-- Prefix list `[a 0, a 1, ..., a n]` of the sequence A177131. -/
def aList : ℕ → List ℤ
  | 0 => [1]
  | 1 => [1, 10]
  | n + 2 =>
    let prev := aList (n + 1)
    let next := (∑ p ∈ Finset.range (n + 2), prev.getD p 0 * prev.getD (n + 1 - p) 0) + 1
    prev ++ [next]

/-- The sequence A177131. -/
def a (n : ℕ) : ℤ := (aList n).getD n 0

/-- Conjecture (R. J. Mathar): P-recursive linear recurrence for A177131 for `n ≥ 4`. -/
theorem main :
    ∀ n : ℕ, 4 ≤ n →
      ((n : ℤ) + 1) * a n
      + 2 * (-3 * (n : ℤ) + 1) * a (n - 1)
      + (-27 * (n : ℤ) + 59) * a (n - 2)
      + 64 * ((n : ℤ) - 3) * a (n - 3)
      + 32 * (-(n : ℤ) + 4) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a177131
