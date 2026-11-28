import Mathlib

/-!
# A392665: Triangle read by rows: T(n,k) (1 <= k <= n) given by T(n,1) = T(n,n) = 1, otherwise T(n,k) = (m*n-m*k+1)*T(n-1,k-1) + (m*k-m+1)*T(n-1,k), where m = -4.

Source: https://oeis.org/A392665
Credit: @agchua

Comment of A392665 (the entry is by Xin Chen and Yudian Chen, Jan 18 2026):
  Conjecture: T(n,k) >= 0 for all even n and all 1 <= k <= n. Verified for even n <= 400. Since
  all entries are nonneg for even n, the roots of R_n(y) lie in the annulus determined by
  consecutive coefficient ratios (Enestrom-Kakeya theorem).
The claim is the first sentence; the rest of the comment is a consequence of it (the
Enestrom-Kakeya theorem) and a report of the computation. The rows are n >= 1 (offset 1). Below,
T (n+1) k is row n+1: 1 for k = 1 and k = n+1, the recurrence with m = -4 for 1 < k < n+1, i.e.
(m*(n+1) - m*k + 1) = -4*(n+1) + 4*k + 1 and (m*k - m + 1) = -4*k + 4 + 1, and 0 outside the
row (never used by the recurrence). T 0 k = 0 (there is no row 0).
-/

namespace OMA.S_oeis_a392665

/-- A392665: T(n,1) = T(n,n) = 1, otherwise T(n,k) = (m*n-m*k+1)*T(n-1,k-1) + (m*k-m+1)*T(n-1,k)
with m = -4, for 1 < k < n. -/
def T : ℕ → ℕ → ℤ
  | 0, _ => 0
  | n + 1, k =>
    if k = 1 ∨ k = n + 1 then 1
    else if 1 < k ∧ k < n + 1 then
      (-4 * ((n : ℤ) + 1) + 4 * (k : ℤ) + 1) * T n (k - 1) + (-4 * (k : ℤ) + 4 + 1) * T n k
    else 0

/-- The comment's conjecture: T(n,k) >= 0 for all even n and all 1 <= k <= n. -/
theorem main : ∀ n k : ℕ, Even n → 1 ≤ k → k ≤ n → 0 ≤ T n k := by
  sorry

end OMA.S_oeis_a392665
