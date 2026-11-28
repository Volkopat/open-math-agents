import Mathlib

/-!
# A177122: a(n+1) = Sum_{p=0..n} (a(p)*a(n-p)+k) + l for n >= 1, a(0)=1, a(1)=6, k=1, l=1

Source: https://oeis.org/A177122 (conjecture by R. J. Mathar)

`a(n)` (offset 0) is defined by `a(0) = 1`, `a(1) = 6` and, for `n >= 1`,
`a(n+1) = Sum_{p=0..n} (a(p)*a(n-p) + k) + l` with `k = 1`, `l = 1`; below the recursion is
written for `a(n+2)` with `p` ranging over `Fin (n+2)`.

The conjecture: the stated linear recurrence with polynomial coefficients, for `n >= 5`, where every
index is defined.
-/

namespace OMA.S_oeis_a177122

open PowerSeries

/-- The sequence A177122. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 6
  | n + 2 => (∑ p : Fin (n + 2), (a p * a (n + 1 - p) + 1)) + 1
decreasing_by all_goals omega

theorem main : ∀ n : ℕ, 5 ≤ n →
      (((n : ℤ)+1)) * a n +
        ((-7*(n : ℤ)+2)) * a (n - 1) +
        ((-5*(n : ℤ)+19)) * a (n - 2) +
        ((35*(n : ℤ)-106)) * a (n - 3) +
        (36*(-(n : ℤ)+4)) * a (n - 4) +
        (12*((n : ℤ)-5)) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a177122
