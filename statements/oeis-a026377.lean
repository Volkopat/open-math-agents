import Mathlib

/-!
# A026377: a(n) = number of integer strings s(0),...,s(n) counted by array T in A026374 that have s(n)=4; also a(n) = T(2n,n-2).

Source: https://oeis.org/A026377
Credit: @vivanpoddar

The sequence (offset 2) begins 1, 9, 58, 330, 1770, 9198, 46928, 236736, ...
It is defined as in the name of the entry, a(n) = T(2n,n-2), where T is the triangular array of
A026374: T(n,0) = T(n,n) = 1 for all n >= 0, T(n,k) = T(n-1,k-1) + T(n-1,k) for odd n and
1 <= k <= n-1, T(n,k) = T(n-1,k-1) + T(n-1,k) + T(n-2,k-1) for even n and 1 <= k <= n-1.

Conjecture (R. J. Mathar): n*(n+4)*a(n) - 3*(n+2)*(2*n+3)*a(n-1) + 5*(n+2)*(n+1)*a(n-2) = 0.
It involves a(n-2) and the offset is 2, so it is stated for n >= 4, exactly as printed.

Remark for the reviewer: with the terms of the entry the left-hand side at n = 4 is
4*8*58 - 3*6*11*9 + 5*6*5*1 = 224, so the relation as printed does not hold for this offset (it
does hold when the terms are indexed from 0, that is, with a(n) replaced by a(n+2) throughout).
The statement below keeps the printed form.
-/

namespace OMA.S_oeis_a026377

/-- The triangular array of A026374 (0 outside the triangle). -/
def T : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | 1, k => if k ≤ 1 then 1 else 0
  | (n + 2), k =>
    if k = 0 ∨ k = n + 2 then 1
    else if n + 2 < k then 0
    else if n % 2 = 1 then T (n + 1) (k - 1) + T (n + 1) k
    else T (n + 1) (k - 1) + T (n + 1) k + T n (k - 1)

/-- A026377: a(n) = T(2n, n-2). -/
def a (n : ℕ) : ℕ := T (2 * n) (n - 2)

/-- The conjectured recurrence for A026377, as printed in the entry. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (n : ℤ) * (n + 4) * a n - 3 * ((n : ℤ) + 2) * (2 * n + 3) * a (n - 1)
      + 5 * ((n : ℤ) + 2) * (n + 1) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a026377
