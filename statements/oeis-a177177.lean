import Mathlib

/-!
# A177177: a(n+1) = Sum_{p=0..n} (a(p)*a(n-p)+k) + l for n >= 1, a(0)=1, a(1)=7, k=1, l=-1

Source: https://oeis.org/A177177 (conjecture by R. J. Mathar, Mar 02 2016)

`a(n)` (offset 0) is defined by `a(0) = 1`, `a(1) = 7` and, for `n >= 1`,
`a(n+1) = Sum_{p=0..n} (a(p)*a(n-p) + k) + l` with `k = 1`, `l = -1`; below the recursion
is written for `a(n+2)` with `p` ranging over `Fin (n+2)`.

The conjecture, stated for `n >= 5` (where every index is defined):
Conjecture: +(n+1)*a(n) +(-7*n+2)*a(n-1) +9*(-n+3)*a(n-2) +5*(11*n-34)*a(n-3) +4*(-16*n+65)*a(n-4) +24*(n-5)*a(n-5)=0.
-/

namespace OMA.S_oeis_a177177

open PowerSeries

/-- The sequence A177177. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 7
  | n + 2 => (∑ p : Fin (n + 2), (a p * a (n + 1 - p) + 1)) + (-1)
decreasing_by all_goals omega

theorem main : ∀ n : ℕ, 5 ≤ n →
      (((n : ℤ)+1)) * a n +
        ((-7*(n : ℤ)+2)) * a (n - 1) +
        (9*(-(n : ℤ)+3)) * a (n - 2) +
        (5*(11*(n : ℤ)-34)) * a (n - 3) +
        (4*(-16*(n : ℤ)+65)) * a (n - 4) +
        (24*((n : ℤ)-5)) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a177177
