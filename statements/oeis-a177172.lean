import Mathlib

/-!
# A177172: a(n+1) = Sum_{p=0..n} (a(p)*a(n-p)+k) + l for n >= 1, a(0)=1, a(1)=10, k=0, l=-2

Source: https://oeis.org/A177172 (conjecture by R. J. Mathar, Feb 21 2016)

`a(n)` (offset 0) is defined by `a(0) = 1`, `a(1) = 10` and, for `n >= 1`,
`a(n+1) = Sum_{p=0..n} (a(p)*a(n-p) + k) + l` with `k = 0`, `l = -2`; below the recursion
is written for `a(n+2)` with `p` ranging over `Fin (n+2)`.

The conjecture, stated for `n >= 4` (where every index is defined):
Conjecture: (n+1)*a(n) +2*(-3*n+1)*a(n-1) +(-27*n+59)*a(n-2) +2*(38*n-117)*a(n-3) +44*(-n+4)*a(n-4)=0.
-/

namespace OMA.S_oeis_a177172

open PowerSeries

/-- The sequence A177172. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 10
  | n + 2 => (∑ p : Fin (n + 2), (a p * a (n + 1 - p) + 0)) + (-2)
decreasing_by all_goals omega

theorem main : ∀ n : ℕ, 4 ≤ n →
      (((n : ℤ)+1)) * a n +
        (2*(-3*(n : ℤ)+1)) * a (n - 1) +
        ((-27*(n : ℤ)+59)) * a (n - 2) +
        (2*(38*(n : ℤ)-117)) * a (n - 3) +
        (44*(-(n : ℤ)+4)) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a177172
