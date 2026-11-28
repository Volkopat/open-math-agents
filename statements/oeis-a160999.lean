import Mathlib

/-!
# OEIS A160999: Mathar's recurrence for the row sums of the array A027052

Source: https://oeis.org/A160999 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A160999 (R. J. Mathar, Jun 01 2009), offset 0: Row sums of A027052.
Formula section:
a(n) = Sum{k=0..2*n} A027052(n,k).
Conjecture: (-n+2)*a(n) +(6*n-11)*a(n-1) +(-7*n+1)*a(n-2) +2*(-4*n+27)*a(n-3) +(5*n-28)*a(n-4) +(2*n-3)*a(n-5) +3*(n-5)*a(n-6)=0. - R. J. Mathar, May 26 2016

A027052 (Clark Kimberling): Triangular array T read by rows: T(n,0) = T(n,2n) = 1 for n >= 0, T(n,1)=0 for n >= 1, T(n,2)=1 for n >= 2 and for n >= 3, T(n,k) = T(n-1,k-3) + T(n-1, k-2) + T(n-1,k-1) for 3 <= k <= 2n-1. T(n,k)=0 for k < 0 or k > 2n.

Formalization notes:
* T(n, k) is defined for 0 <= k <= 2n by the rule of A027052 and is 0 outside the row. The name's
  recursion is stated for n >= 3, which leaves T(2, 3) open; the definition applies the recursion
  there too, T(2, 3) = T(1, 0) + T(1, 1) + T(1, 2) = 2, which is the array's data (row 2 of
  A027052 is 1, 0, 1, 2, 1).
* a(n) = T(n, 0) + T(n, 1) + ... + T(n, 2n), the sum of row n, for n >= 0, the entry's offset. The
  block gives no range for the recurrence, so it is stated for every n >= 6, the smallest n for
  which a(n - 6) is a term of the entry, as an identity of integers.
* The definition reproduces the entry's data (1, 2, 5, 12, 31, 84, ... from n = 0); the proof file
  proves all 27 listed terms as controls.
-/

namespace OMA.S_oeis_a160999

/-- A027052 T(n, k), 0 <= k <= 2n: T(n, 0) = T(n, 2) = T(n, 2n) = 1, T(n, 1) = 0 for n >= 1, and
T(n, k) = T(n-1, k-3) + T(n-1, k-2) + T(n-1, k-1) for 3 <= k <= 2n - 1 (0 beyond the row). -/
def T : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | n + 1, k =>
    if 2 * (n + 1) < k then 0
    else if k = 1 then 0
    else if k < 3 ∨ k = 2 * (n + 1) then 1
    else T n (k - 3) + T n (k - 2) + T n (k - 1)

/-- A160999: the row sums of A027052, a(n) = T(n, 0) + T(n, 1) + ... + T(n, 2n). -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (2 * n + 1), T n k

/-- Mathar's conjecture. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
      (-(n : ℤ) + 2) * (a n : ℤ) + (6 * (n : ℤ) - 11) * (a (n - 1) : ℤ) + (-7 * (n : ℤ) + 1) * (a (n - 2) : ℤ) + 2 * (-4 * (n : ℤ) + 27) * (a (n - 3) : ℤ) + (5 * (n : ℤ) - 28) * (a (n - 4) : ℤ) + (2 * (n : ℤ) - 3) * (a (n - 5) : ℤ) + 3 * ((n : ℤ) - 5) * (a (n - 6) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a160999
