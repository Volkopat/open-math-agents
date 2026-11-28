import Mathlib

/-!
# OEIS A026580: Mathar's recurrence for T(n, 0) + ... + T(n, n) of the array A026568

Source: https://oeis.org/A026580 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A026580 (Clark Kimberling), offset 0: T(n,0) + T(n,1) + ... + T(n,n), T given by A026568.
Formula section:
Conjecture: n*a(n) +(n-2)*a(n-1) +(-17*n+28)*a(n-2) +5*(-n+4)*a(n-3) +2*(34*n-107)*a(n-4) +16*(n-5)*a(n-5) +32*(-2*n+9)*a(n-6)=0. - R. J. Mathar, Jun 23 2013

A026568 (Clark Kimberling): Irregular triangular array T read by rows: T(i,0) = T(i,2i) = 1 for i >= 0; T(i,1) = T(i,2i-1) = [ (i+1)/2 ] for i >= 1; and for i >= 2 and 2 <=j <= i - 2, T(i,j) = T(i-1,j-2) + T(i-1,j-1) + T(i-1,j) if i + j is even, T(i,j) = T(i-1,j-2) + T(i-1,j) if i + j is odd.

Formalization notes:
* T(i, j) is defined for 0 <= j <= 2i by the rule of A026568 and is 0 outside the row. The name
  states the parity recursion for i >= 2 and 2 <= j <= i - 2; the definition applies it for 2 <= j
  <= 2i - 2, the range that the companion array A026584 states (j = 2..2i-2) and that the data
  needs: the name's boundary values fix only j <= 1 and j >= 2i - 1, and row 4 of the data is 1,
  2, 7, 7, 13, 7, 7, 2, 1. With this range the definition reproduces the array's data.
* a(n) = T(n, 0) + T(n, 1) + ... + T(n, n), the entries of row n up to its middle, for n >= 0, the
  entry's offset. The block gives no range for the recurrence, so it is stated for every n >= 6,
  the smallest n for which a(n - 6) is a term of the entry, as an identity of integers.
* The definition reproduces the entry's data (1, 2, 5, 12, 30, 75, ... from n = 0); the proof file
  proves all 28 listed terms as controls.
-/

namespace OMA.S_oeis_a026580

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

/-- A026580: a(n) = T(n, 0) + T(n, 1) + ... + T(n, n). -/
def a (n : ℕ) : ℕ := ∑ j ∈ Finset.range (n + 1), T n j

/-- Mathar's conjecture. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
      (n : ℤ) * (a n : ℤ) + ((n : ℤ) - 2) * (a (n - 1) : ℤ) + (-17 * (n : ℤ) + 28) * (a (n - 2) : ℤ) + 5 * (-(n : ℤ) + 4) * (a (n - 3) : ℤ) + 2 * (34 * (n : ℤ) - 107) * (a (n - 4) : ℤ) + 16 * ((n : ℤ) - 5) * (a (n - 5) : ℤ) + 32 * (-2 * (n : ℤ) + 9) * (a (n - 6) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a026580
