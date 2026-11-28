import Mathlib

/-!
# A176826: a(n+1) = Sum_{p=0..n} (a(p)*a(n-p)+k) + l for n >= 1, a(0)=1, a(1)=1, k=1, l=-1

Source: https://oeis.org/A176826 (conjecture by R. J. Mathar, Feb 18 2016)

`a(n)` (offset 0) is defined by `a(0) = 1`, `a(1) = 1` and, for `n >= 1`,
`a(n+1) = Sum_{p=0..n} (a(p)*a(n-p) + k) + l` with `k = 1`, `l = -1`; below the recursion
is written for `a(n+2)` with `p` ranging over `Fin (n+2)`.

The conjecture, stated for `n >= 4` (where every index is defined):
Conjecture: (n+1)*a(n) +(-7*n+2)*a(n-1) +3*(5*n-7)*a(n-2) +(-17*n+46)*a(n-3) +4*(2*n-7)*a(n-4)=0.
-/

namespace OMA.S_oeis_a176826

open PowerSeries

/-- The sequence A176826. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => (∑ p : Fin (n + 2), (a p * a (n + 1 - p) + 1)) + (-1)
decreasing_by all_goals omega

theorem main : ∀ n : ℕ, 4 ≤ n →
      (((n : ℤ)+1)) * a n +
        ((-7*(n : ℤ)+2)) * a (n - 1) +
        (3*(5*(n : ℤ)-7)) * a (n - 2) +
        ((-17*(n : ℤ)+46)) * a (n - 3) +
        (4*(2*(n : ℤ)-7)) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a176826
