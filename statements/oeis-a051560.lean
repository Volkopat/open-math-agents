import Mathlib

/-!
# Mathar's recurrence conjecture for OEIS A051560

Source: https://oeis.org/A051560
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A051/A051560.seq
Credit: @sntntHb

OEIS A051560 (offset 0) is the second unsigned column of triangle A051379, the generalized
Stirling number triangle of the first kind with r = 7:
T(n, k) = [x^k] Product_{m=1..n} (x - m - 7), computed by the recurrence given in A051379,
T(n, m) = T(n-1, m-1) - (n+7)*T(n-1, m) for n >= m >= 0, T(n, m) = 0 for n < m,
T(n, -1) = 0 and T(0, 0) = 1. So a(n) = |T(n, 1)|, with e.g.f. -log(1-x)/(1-x)^8 and
first terms 0, 1, 17, 242, 3382, 48504.

Conjecture (R. J. Mathar, Aug 04 2013, quoted from the entry):
a(n) +(-2*n-13)*a(n-1) +(n+6)^2*a(n-2) = 0.
The recurrence is stated for every n >= 2 (the first index where a(n-2) is defined).
-/

namespace OMA.S_oeis_a051560

/-- The signed triangle A051379, defined by its recurrence (row index first). -/
def T : ℕ → ℕ → ℤ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => -((n + 1 + 7 : ℕ) : ℤ) * T n 0
  | n + 1, m + 1 => T n m - ((n + 1 + 7 : ℕ) : ℤ) * T n (m + 1)

/-- OEIS A051560: the second unsigned column of A051379, a(n) = |T(n, 1)|. -/
def a (n : ℕ) : ℤ := |T n 1|

/-- Mathar's conjectured recurrence, for all n >= 2 (written with n + 2 in place of n). -/
theorem main : ∀ n : ℕ,
    a (n + 2) + (-2 * ((n + 2 : ℕ) : ℤ) - 13) * a (n + 1) + (((n + 2 : ℕ) : ℤ) + 6) ^ 2 * a n = 0 := by
  sorry

end OMA.S_oeis_a051560
