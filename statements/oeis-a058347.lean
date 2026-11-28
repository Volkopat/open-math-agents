import Mathlib

/-!
# A058347: Array T(n,k) for the double-support algorithm.

Source: https://oeis.org/A058347
Credit: @rot13maxi

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a058347

/-- A058347: the total number of checks required by the double-support algorithm
on `n` by `k` zero-one matrices. Defined by the OEIS recurrence
`T(0,k)=0`, `T(n,0)=0`, and for `n,k>0` the formula in the OEIS Formula section. -/
def T : ℕ → ℕ → ℕ
  | 0, _ => 0
  | 1, 0 => 0
  | 1, k + 1 => (k + 1) * 2 ^ (k + 1)
  | _n + 2, 0 => 0
  | n + 2, 1 => (n + 3) * 2 ^ (n + 1) + T (n + 1) 1
  | n + 2, k + 2 =>
      (2 ^ (k + 3) - 2) * 2 ^ ((n + 1) * (k + 2)) +
      2 ^ ((n + 1) * (k + 1)) * (k * 2 ^ (k + 2) + 2) +
      (n + 1) * (2 ^ (k + 2) - 1) * 2 ^ (n * (k + 2) + 1) +
      T (n + 1) (k + 2) +
      2 ^ (n + 1) * (2 ^ (k + 2) - 1) * T (n + 1) (k + 1)

/-- OEIS A058347 conjecture: the array is symmetric, `T(n,k) = T(k,n)`. -/
theorem main : ∀ n k : ℕ, T n k = T k n := by
  sorry

end OMA.S_oeis_a058347
