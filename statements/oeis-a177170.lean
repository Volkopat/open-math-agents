import Mathlib

/-!
# A177170: a(n+1) = Sum_{p=0..n} (a(p)*a(n-p)+k) + l for n >= 1, a(0)=1, a(1)=8, k=0, l=-2

Source: https://oeis.org/A177170 (conjecture by R. J. Mathar, Jun 14 2016)

`a(n)` (offset 0) is defined by `a(0) = 1`, `a(1) = 8` and, for `n >= 1`,
`a(n+1) = Sum_{p=0..n} (a(p)*a(n-p) + k) + l` with `k = 0`, `l = -2`; below the recursion
is written for `a(n+2)` with `p` ranging over `Fin (n+2)`.

The conjecture, stated for `n >= 4` (where every index is defined):
Conjecture: (n+1)*a(n) +2*(-3*n+1)*a(n-1) +(-19*n+43)*a(n-2) +6*(10*n-31)*a(n-3) +36*(-n+4)*a(n-4)=0.
-/

namespace OMA.S_oeis_a177170

open PowerSeries

/-- The sequence A177170. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 8
  | n + 2 => (∑ p : Fin (n + 2), (a p * a (n + 1 - p) + 0)) + (-2)
decreasing_by all_goals omega

theorem main : ∀ n : ℕ, 4 ≤ n →
      (((n : ℤ)+1)) * a n +
        (2*(-3*(n : ℤ)+1)) * a (n - 1) +
        ((-19*(n : ℤ)+43)) * a (n - 2) +
        (6*(10*(n : ℤ)-31)) * a (n - 3) +
        (36*(-(n : ℤ)+4)) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a177170
