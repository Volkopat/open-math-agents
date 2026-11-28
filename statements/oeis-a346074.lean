import Mathlib

/-!
# A346074: a(n) = 1 + Sum_{k=0..n-5} a(k) * a(n-k-5)

Source: https://oeis.org/A346074 (conjecture by R. J. Mathar, Feb 17 2022)

`a(n)` (offset 0) is defined by `a(n) = 1 + Sum_{k=0..n-5} a(k) * a(n-k-5)` for all `n >= 0`;
the sum is empty for `n < 5`, so `a(0) = ... = a(4) = 1`. Below, the case `n + 5` is written with
`k` ranging over `Fin (n + 1)`, i.e. `k = 0..n`, and `a(n + 5 - k - 5) = a(n - k)`.
Values are taken in `ℤ` so that the recurrence can be stated without truncated subtraction.

The conjecture: D-finite with recurrence
`(n+5)*a(n) +2*(-n-4)*a(n-1) +(n+3)*a(n-2) +2*(-2*n+5)*a(n-5) +4*(n-3)*a(n-6) = 0`,
stated for `n >= 6`, where every index is defined.
-/

namespace OMA.S_oeis_a346074

/-- The sequence A346074. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | n + 5 => 1 + ∑ k : Fin (n + 1), a k * a (n - k)
decreasing_by all_goals omega

theorem main : ∀ n : ℕ, 6 ≤ n →
      ((n : ℤ) + 5) * a n + 2 * (-(n : ℤ) - 4) * a (n - 1) + ((n : ℤ) + 3) * a (n - 2) +
        2 * (-2 * (n : ℤ) + 5) * a (n - 5) + 4 * ((n : ℤ) - 3) * a (n - 6) = 0 := by
  sorry

end OMA.S_oeis_a346074
