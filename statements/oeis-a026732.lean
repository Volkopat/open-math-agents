import Mathlib

/-!
# OEIS A026732: Mathar's recurrence for the row sums of the array A026725

Source: https://oeis.org/A026732 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A026732 (Clark Kimberling), offset 0: a(n) = Sum_{k=0..n} T(n,k), T given by A026725.
Formula section:
Conjecture: +(-n+1)*a(n) +2*a(n-1) +3*(3*n-7)*a(n-2) -10*a(n-3) +(-23*n+95)*a(n-4) +6*a(n-5) +(11*n-95)*a(n-6) +2*a(n-7) +4*(n-7)*a(n-8)=0. - R. J. Mathar, Oct 26 2019

A026725 (Clark Kimberling): Triangular array, T, read by rows: T(n,0) = T(n,n) = 1. For n >= 2 and 1<=k<=n-1, T(n,k) = T(n-1,k-1) + T(n-2,k-1) + T(n-1,k) if n is odd and k=(n-1)/2, otherwise T(n,k) = T(n-1,k-1) + T(n-1,k).

Formalization notes:
* T(n, k) is defined for 0 <= k <= n by the rule of A026725 and is 0 outside the row; the
  definition reproduces the array's data.
* a(n) = T(n, 0) + T(n, 1) + ... + T(n, n) for n >= 0, the entry's offset. The block gives no
  range for the recurrence, so it is stated for every n >= 8, the smallest n for which a(n - 8) is
  a term of the entry, as an identity of integers.
* The definition reproduces the entry's data (1, 2, 4, 9, 18, 40, ... from n = 0); the proof file
  proves all 31 listed terms as controls.
-/

namespace OMA.S_oeis_a026732

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

/-- A026732: a(n) = T(n, 0) + T(n, 1) + ... + T(n, n). -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), T n k

/-- Mathar's conjecture. -/
theorem main : ∀ n : ℕ, 8 ≤ n →
      (-(n : ℤ) + 1) * (a n : ℤ) + 2 * (a (n - 1) : ℤ) + 3 * (3 * (n : ℤ) - 7) * (a (n - 2) : ℤ) - 10 * (a (n - 3) : ℤ) + (-23 * (n : ℤ) + 95) * (a (n - 4) : ℤ) + 6 * (a (n - 5) : ℤ) + (11 * (n : ℤ) - 95) * (a (n - 6) : ℤ) + 2 * (a (n - 7) : ℤ) + 4 * ((n : ℤ) - 7) * (a (n - 8) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a026732
