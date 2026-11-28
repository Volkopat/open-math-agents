import Mathlib

/-!
# A177168: a(n+1) = Sum_{p=0..n} (a(p)*a(n-p)+k) + l for n >= 1, a(0)=1, a(1)=6, k=0, l=-2

Source: https://oeis.org/A177168 (conjecture by R. J. Mathar, Jun 14 2016)

`a(n)` (offset 0) is defined by `a(0) = 1`, `a(1) = 6` and, for `n >= 1`,
`a(n+1) = Sum_{p=0..n} (a(p)*a(n-p) + k) + l` with `k = 0`, `l = -2`; below the recursion
is written for `a(n+2)` with `p` ranging over `Fin (n+2)`.

The conjecture, stated for `n >= 4` (where every index is defined):
Conjecture: (n+1)*a(n) +2*(-3*n+1)*a(n-1) +(-11*n+27)*a(n-2) +2*(22*n-69)*a(n-3) +28*(-n+4)*a(n-4)=0.
-/

namespace OMA.S_oeis_a177168

open PowerSeries

/-- The sequence A177168. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 6
  | n + 2 => (∑ p : Fin (n + 2), (a p * a (n + 1 - p) + 0)) + (-2)
decreasing_by all_goals omega

theorem main : ∀ n : ℕ, 4 ≤ n →
      (((n : ℤ)+1)) * a n +
        (2*(-3*(n : ℤ)+1)) * a (n - 1) +
        ((-11*(n : ℤ)+27)) * a (n - 2) +
        (2*(22*(n : ℤ)-69)) * a (n - 3) +
        (28*(-(n : ℤ)+4)) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a177168
