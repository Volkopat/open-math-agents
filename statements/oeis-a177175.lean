import Mathlib

/-!
# A177175: a(n+1) = Sum_{p=0..n} (a(p)*a(n-p)+k) + l for n >= 1, a(0)=1, a(1)=6, k=1, l=-1

Source: https://oeis.org/A177175 (conjecture by R. J. Mathar, Jul 24 2012)

`a(n)` (offset 0) is defined by `a(0) = 1`, `a(1) = 6` and, for `n >= 1`,
`a(n+1) = Sum_{p=0..n} (a(p)*a(n-p) + k) + l` with `k = 1`, `l = -1`; below the recursion
is written for `a(n+2)` with `p` ranging over `Fin (n+2)`.

The conjecture, stated for `n >= 5` (where every index is defined):
Conjecture: (n+1)*a(n) +(2-7*n)*a(n-1) +(19-5*n)*a(n-2) +(43*n-134)*a(n-3) +4*(53-13*n)*a(n-4) +20*(n-5)*a(n-5)=0.
-/

namespace OMA.S_oeis_a177175

open PowerSeries

/-- The sequence A177175. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 6
  | n + 2 => (∑ p : Fin (n + 2), (a p * a (n + 1 - p) + 1)) + (-1)
decreasing_by all_goals omega

theorem main : ∀ n : ℕ, 5 ≤ n →
      (((n : ℤ)+1)) * a n +
        ((2-7*(n : ℤ))) * a (n - 1) +
        ((19-5*(n : ℤ))) * a (n - 2) +
        ((43*(n : ℤ)-134)) * a (n - 3) +
        (4*(53-13*(n : ℤ))) * a (n - 4) +
        (20*((n : ℤ)-5)) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a177175
