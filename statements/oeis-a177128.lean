import Mathlib

/-!
# A177128: Quadratic convolution recurrence a(0) = 1, a(1) = 7, a(n+1) = sum a(p)*a(n-p) + 1

Source: https://oeis.org/A177128

Conjecture (R. J. Mathar):
For all `n ≥ 4`,
`(n + 1) * a(n) + 2 * (-3*n + 1) * a(n - 1) + 5 * (-3*n + 7) * a(n - 2)`
`+ 40 * (n - 3) * a(n - 3) + 20 * (-n + 4) * a(n - 4) = 0`.

Conventions:
- Offset: `0`, with initial terms `1, 7, 15, 80, 371, 2088, 11771, 70305, ...`.
- Computed in `ℤ` via structural recursion accumulating the prefix list `[a 0, ..., a n]`.
-/

namespace OMA.S_oeis_a177128

/-- Prefix list `[a 0, a 1, ..., a n]` of the sequence A177128. -/
def aList : ℕ → List ℤ
  | 0 => [1]
  | 1 => [1, 7]
  | n + 2 =>
    let prev := aList (n + 1)
    let next := (∑ p ∈ Finset.range (n + 2), prev.getD p 0 * prev.getD (n + 1 - p) 0) + 1
    prev ++ [next]

/-- The sequence A177128. -/
def a (n : ℕ) : ℤ := (aList n).getD n 0

/-- Conjecture (R. J. Mathar): P-recursive linear recurrence for A177128 for `n ≥ 4`. -/
theorem main :
    ∀ n : ℕ, 4 ≤ n →
      ((n : ℤ) + 1) * a n
      + 2 * (-3 * (n : ℤ) + 1) * a (n - 1)
      + 5 * (-3 * (n : ℤ) + 7) * a (n - 2)
      + 40 * ((n : ℤ) - 3) * a (n - 3)
      + 20 * (-(n : ℤ) + 4) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a177128
