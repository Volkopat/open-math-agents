import Mathlib

/-!
# A177179: a(n+1) = Sum_{p=0..n} (a(p)*a(n-p)+k) + l for n >= 1, a(0)=1, a(1)=9, k=1, l=-1

Source: https://oeis.org/A177179 (conjecture by R. J. Mathar, Mar 02 2016)

`a(n)` (offset 0) is defined by `a(0) = 1`, `a(1) = 9` and, for `n >= 1`,
`a(n+1) = Sum_{p=0..n} (a(p)*a(n-p) + k) + l` with `k = 1`, `l = -1`; below the recursion
is written for `a(n+2)` with `p` ranging over `Fin (n+2)`.

The conjecture, stated for `n >= 5` (where every index is defined):
Conjecture: +(n+1)*a(n) +(-7*n+2)*a(n-1) +(-17*n+43)*a(n-2) +(79*n-242)*a(n-3) +4*(-22*n+89)*a(n-4) +32*(n-5)*a(n-5)=0.
-/

namespace OMA.S_oeis_a177179

open PowerSeries

/-- The sequence A177179. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 9
  | n + 2 => (∑ p : Fin (n + 2), (a p * a (n + 1 - p) + 1)) + (-1)
decreasing_by all_goals omega

theorem main : ∀ n : ℕ, 5 ≤ n →
      (((n : ℤ)+1)) * a n +
        ((-7*(n : ℤ)+2)) * a (n - 1) +
        ((-17*(n : ℤ)+43)) * a (n - 2) +
        ((79*(n : ℤ)-242)) * a (n - 3) +
        (4*(-22*(n : ℤ)+89)) * a (n - 4) +
        (32*((n : ℤ)-5)) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a177179
