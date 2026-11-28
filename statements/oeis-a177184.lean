import Mathlib

/-!
# A177184: a(n+1) = Sum_{p=0..n} (a(p)*a(n-p)+k) + l for n >= 1, a(0)=1, a(1)=9, k=-1, l=-1

Source: https://oeis.org/A177184 (conjecture by R. J. Mathar, Mar 02 2016)

`a(n)` (offset 0) is defined by `a(0) = 1`, `a(1) = 9` and, for `n >= 1`,
`a(n+1) = Sum_{p=0..n} (a(p)*a(n-p) + k) + l` with `k = -1`, `l = -1`; below the recursion
is written for `a(n+2)` with `p` ranging over `Fin (n+2)`.

The conjecture, stated for `n >= 5` (where every index is defined):
Conjecture: +(n+1)*a(n) +(-7*n+2)*a(n-1) +(-17*n+43)*a(n-2) +(95*n-298)*a(n-3) +4*(-28*n+113)*a(n-4) +40*(n-5)*a(n-5)=0.
-/

namespace OMA.S_oeis_a177184

open PowerSeries

/-- The sequence A177184. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 9
  | n + 2 => (∑ p : Fin (n + 2), (a p * a (n + 1 - p) + (-1))) + (-1)
decreasing_by all_goals omega

theorem main : ∀ n : ℕ, 5 ≤ n →
      (((n : ℤ)+1)) * a n +
        ((-7*(n : ℤ)+2)) * a (n - 1) +
        ((-17*(n : ℤ)+43)) * a (n - 2) +
        ((95*(n : ℤ)-298)) * a (n - 3) +
        (4*(-28*(n : ℤ)+113)) * a (n - 4) +
        (40*((n : ℤ)-5)) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a177184
