import Mathlib

/-!
# A177178: a(n+1) = Sum_{p=0..n} (a(p)*a(n-p)+k) + l for n >= 1, a(0)=1, a(1)=8, k=1, l=-1

Source: https://oeis.org/A177178 (conjecture by R. J. Mathar, Mar 02 2016)

`a(n)` (offset 0) is defined by `a(0) = 1`, `a(1) = 8` and, for `n >= 1`,
`a(n+1) = Sum_{p=0..n} (a(p)*a(n-p) + k) + l` with `k = 1`, `l = -1`; below the recursion
is written for `a(n+2)` with `p` ranging over `Fin (n+2)`.

The conjecture, stated for `n >= 5` (where every index is defined):
Conjecture: +(n+1)*a(n) +(-7*n+2)*a(n-1) +(-13*n+35)*a(n-2) +(67*n-206)*a(n-3) +4*(-19*n+77)*a(n-4) +28*(n-5)*a(n-5)=0.
-/

namespace OMA.S_oeis_a177178

open PowerSeries

/-- The sequence A177178. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 8
  | n + 2 => (∑ p : Fin (n + 2), (a p * a (n + 1 - p) + 1)) + (-1)
decreasing_by all_goals omega

theorem main : ∀ n : ℕ, 5 ≤ n →
      (((n : ℤ)+1)) * a n +
        ((-7*(n : ℤ)+2)) * a (n - 1) +
        ((-13*(n : ℤ)+35)) * a (n - 2) +
        ((67*(n : ℤ)-206)) * a (n - 3) +
        (4*(-19*(n : ℤ)+77)) * a (n - 4) +
        (28*((n : ℤ)-5)) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a177178
