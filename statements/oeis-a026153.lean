import Mathlib

/-!
# OEIS A026153: Mathar's recurrence for T(n, n - 2) of the array A026148

Source: https://oeis.org/A026153 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A026153 (Clark Kimberling), offset 2: T(n,n-2), where T is the array in A026148.
Formula section:
Conjecture: -(n+8)*(n-118)*a(n) +(-n^2-561*n-2878)*a(n-1) +2*(38*n^2+203*n-1070)*a(n-2) +2*(-116*n^2+781*n+2493)*a(n-3) +(13*n^2-1012*n+3888)*a(n-4) +3*(107*n-423)*(n-4)*a(n-5)=0. - R. J. Mathar, Jun 23 2013

A026148 (Clark Kimberling): Irregular triangular array T read by rows: T(n,0) = 1 for i >= 0, T(1,1) = 1,T(2,1) = 1, T(2,2) = 2, T(2,3) = 1, T(2,4) = 1 and for n >= 3, T(n,1) = n-1,  T(n,k) = T(n-1,k-2) + T(n-1,k-1) + T(n-1,k) for k=2,...,n+1, and T(n, k+2) = T(n-1, k) + T(n-1, k+1).

Formalization notes:
* T(n, k) is defined for 0 <= k <= n + 2 by the rule of A026148 and is 0 outside the rows. The
  name's last clause, T(n, k+2) = T(n-1, k) + T(n-1, k+1), is read as the right end of row n, T(n,
  n + 2) = T(n-1, n) + T(n-1, n + 1): row n has the n + 3 entries k = 0..n+2 and the recursion
  covers k = 2..n+1. With this reading the definition reproduces the array's data.
* a(n) = T(n, n - 2) for n >= 2, the entry's offset (natural subtraction below it). The block
  gives no range for the recurrence, so it is stated for every n >= 7, the smallest n for which
  a(n - 5) is a term of the entry, as an identity of integers.
* The definition reproduces the entry's data (1, 2, 7, 20, 60, 176, ... from n = 2); the proof
  file proves all 27 listed terms as controls.
-/

namespace OMA.S_oeis_a026153

/-- A026148 T(n, k): rows 0 and 1 are 1 and 1, 1; row 2 is 1, 1, 2, 1, 1; for n >= 3 and
0 <= k <= n + 2, T(n, 0) = 1, T(n, 1) = n - 1, T(n, k) = T(n-1, k-2) + T(n-1, k-1) + T(n-1, k) for
2 <= k <= n + 1, and T(n, n + 2) = T(n-1, n) + T(n-1, n + 1) (0 beyond the rows). -/
def T : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | 1, k => if k ≤ 1 then 1 else 0
  | 2, k => if k = 2 then 2 else if k ≤ 4 then 1 else 0
  | n + 3, k =>
    if n + 5 < k then 0
    else if k = 0 then 1
    else if k = 1 then n + 2
    else if k = n + 5 then T (n + 2) (n + 3) + T (n + 2) (n + 4)
    else T (n + 2) (k - 2) + T (n + 2) (k - 1) + T (n + 2) k

/-- A026153: a(n) = T(n, n - 2). -/
def a (n : ℕ) : ℕ := T n (n - 2)

/-- Mathar's conjecture. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
      -((n : ℤ) + 8) * ((n : ℤ) - 118) * (a n : ℤ) + (-(n : ℤ) ^ 2 - 561 * (n : ℤ) - 2878) * (a (n - 1) : ℤ) + 2 * (38 * (n : ℤ) ^ 2 + 203 * (n : ℤ) - 1070) * (a (n - 2) : ℤ) + 2 * (-116 * (n : ℤ) ^ 2 + 781 * (n : ℤ) + 2493) * (a (n - 3) : ℤ) + (13 * (n : ℤ) ^ 2 - 1012 * (n : ℤ) + 3888) * (a (n - 4) : ℤ) + 3 * (107 * (n : ℤ) - 423) * ((n : ℤ) - 4) * (a (n - 5) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a026153
