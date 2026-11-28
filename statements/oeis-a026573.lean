import Mathlib

/-!
# OEIS A026573: Mathar's recurrence for T(n, n - 4) of the array A026568

Source: https://oeis.org/A026573 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A026573 (Clark Kimberling), offset 4: a(n)=T(n,n-4), T given by A026568. Also a(n) = number of integer strings s(0),...,s(n) counted by T, such that s(n)=4.
Formula section:
Conjecture: -2*(n-4)*(n+4)*a(n) +(5*n^2-5*n-46)*a(n-1) +(4*n^2+n+18)*a(n-2) +(-11*n^2+24*n-16)*a(n-3) +2*(n-2)*(2*n-5)*a(n-4)=0. - R. J. Mathar, Jun 23 2013

A026568 (Clark Kimberling): Irregular triangular array T read by rows: T(i,0) = T(i,2i) = 1 for i >= 0; T(i,1) = T(i,2i-1) = [ (i+1)/2 ] for i >= 1; and for i >= 2 and 2 <=j <= i - 2, T(i,j) = T(i-1,j-2) + T(i-1,j-1) + T(i-1,j) if i + j is even, T(i,j) = T(i-1,j-2) + T(i-1,j) if i + j is odd.

Formalization notes:
* T(i, j) is defined for 0 <= j <= 2i by the rule of A026568 and is 0 outside the row. The name
  states the parity recursion for i >= 2 and 2 <= j <= i - 2; the definition applies it for 2 <= j
  <= 2i - 2, the range that the companion array A026584 states (j = 2..2i-2) and that the data
  needs: the name's boundary values fix only j <= 1 and j >= 2i - 1, and row 4 of the data is 1,
  2, 7, 7, 13, 7, 7, 2, 1. With this range the definition reproduces the array's data.
* a(n) = T(n, n - 4) for n >= 4, the entry's offset (natural subtraction below it). The title's
  second description, the number of strings s(0), ..., s(n) counted by A026568 with s(n) = 4, is
  the same number by the comment of A026568; the statement uses the first. The block gives no
  range for the recurrence, so it is stated for every n >= 8, the smallest n for which a(n - 4) is
  a term of the entry, as an identity of integers.
* The definition reproduces the entry's data (1, 3, 12, 34, 103, 281, ... from n = 4); the proof
  file proves all 26 listed terms as controls.
-/

namespace OMA.S_oeis_a026573

/-- A026568 T(i, j), 0 <= j <= 2i: T(i, 0) = T(i, 2i) = 1, T(i, 1) = T(i, 2i - 1) = [(i+1)/2] for
i >= 1, and for 2 <= j <= 2i - 2, T(i, j) = T(i-1, j-2) + T(i-1, j-1) + T(i-1, j) if i + j is even
and T(i, j) = T(i-1, j-2) + T(i-1, j) if i + j is odd (0 beyond the row). -/
def T : ℕ → ℕ → ℕ
  | 0, j => if j = 0 then 1 else 0
  | i + 1, j =>
    if 2 * (i + 1) < j then 0
    else if j = 0 ∨ j = 2 * (i + 1) then 1
    else if j = 1 ∨ j = 2 * (i + 1) - 1 then (i + 2) / 2
    else if (i + 1 + j) % 2 = 0 then T i (j - 2) + T i (j - 1) + T i j
    else T i (j - 2) + T i j

/-- A026573: a(n) = T(n, n - 4). -/
def a (n : ℕ) : ℕ := T n (n - 4)

/-- Mathar's conjecture. -/
theorem main : ∀ n : ℕ, 8 ≤ n →
      -2 * ((n : ℤ) - 4) * ((n : ℤ) + 4) * (a n : ℤ) + (5 * (n : ℤ) ^ 2 - 5 * (n : ℤ) - 46) * (a (n - 1) : ℤ) + (4 * (n : ℤ) ^ 2 + (n : ℤ) + 18) * (a (n - 2) : ℤ) + (-11 * (n : ℤ) ^ 2 + 24 * (n : ℤ) - 16) * (a (n - 3) : ℤ) + 2 * ((n : ℤ) - 2) * (2 * (n : ℤ) - 5) * (a (n - 4) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a026573
