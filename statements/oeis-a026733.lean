import Mathlib

/-!
# OEIS A026733: Mathar's recurrence for the half-row sums of the array A026725

Source: https://oeis.org/A026733 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A026733 (Clark Kimberling), offset 0: a(n) = Sum_{k=0..floor(n/2)} T(n,k), T given by A026725.
Formula section:
Conjecture: (-n+2)*a(n) +(n-2)*a(n-1) +2*(4*n-13)*a(n-2) +8*(-n+4)*a(n-3) +5*(-3*n+14)*a(n-4) +(15*n-94)*a(n-5) +2*(-2*n+9)*a(n-6) +4*(n-6)*a(n-7)=0. - R. J. Mathar, Oct 26 2019

A026725 (Clark Kimberling): Triangular array, T, read by rows: T(n,0) = T(n,n) = 1. For n >= 2 and 1<=k<=n-1, T(n,k) = T(n-1,k-1) + T(n-2,k-1) + T(n-1,k) if n is odd and k=(n-1)/2, otherwise T(n,k) = T(n-1,k-1) + T(n-1,k).

Formalization notes:
* T(n, k) is defined for 0 <= k <= n by the rule of A026725 and is 0 outside the row; the
  definition reproduces the array's data.
* a(n) = T(n, 0) + T(n, 1) + ... + T(n, floor(n/2)) for n >= 0, the entry's offset. The block
  gives no range for the recurrence, so it is stated for every n >= 7, the smallest n for which
  a(n - 7) is a term of the entry, as an identity of integers.
* The definition reproduces the entry's data (1, 1, 3, 5, 13, 23, ... from n = 0); the proof file
  proves all 31 listed terms as controls.
-/

namespace OMA.S_oeis_a026733

/-- A026725 T(n, k), 0 <= k <= n: T(n, 0) = T(n, n) = 1, and for n >= 2 and 1 <= k <= n - 1,
T(n, k) = T(n-1, k-1) + T(n-2, k-1) + T(n-1, k) if n is odd and k = (n-1)/2, and
T(n, k) = T(n-1, k-1) + T(n-1, k) otherwise (0 beyond the row). -/
def T : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | 1, k => if k ≤ 1 then 1 else 0
  | n + 2, k =>
    if n + 2 < k then 0
    else if k = 0 ∨ k = n + 2 then 1
    else if n % 2 = 1 ∧ 2 * k = n + 1 then T (n + 1) (k - 1) + T n (k - 1) + T (n + 1) k
    else T (n + 1) (k - 1) + T (n + 1) k

/-- A026733: a(n) = T(n, 0) + T(n, 1) + ... + T(n, floor(n/2)). -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n / 2 + 1), T n k

/-- Mathar's conjecture. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
      (-(n : ℤ) + 2) * (a n : ℤ) + ((n : ℤ) - 2) * (a (n - 1) : ℤ) + 2 * (4 * (n : ℤ) - 13) * (a (n - 2) : ℤ) + 8 * (-(n : ℤ) + 4) * (a (n - 3) : ℤ) + 5 * (-3 * (n : ℤ) + 14) * (a (n - 4) : ℤ) + (15 * (n : ℤ) - 94) * (a (n - 5) : ℤ) + 2 * (-2 * (n : ℤ) + 9) * (a (n - 6) : ℤ) + 4 * ((n : ℤ) - 6) * (a (n - 7) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a026733
