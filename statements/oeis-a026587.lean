import Mathlib

/-!
# OEIS A026587: Mathar's recurrence for T(n, n - 2) of the array A026584

Source: https://oeis.org/A026587 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A026587 (Clark Kimberling), offset 2: a(n) = T(n, n-2), T given by A026584. Also a(n) = number of integer strings s(0),...,s(n) counted by T, such that s(n)=2.
Formula section:
a(n) = A026584(n, n-2).
Conjecture: (n+2)*a(n) = (3*n+2)*a(n-1) +(3*n+2)*a(n-2) -(11*n-16)*a(n-3) -2*(n-3)*a(n-4) +4*(2*n-9)*a(n-5). - R. J. Mathar, Jun 23 2013

A026584 (Clark Kimberling): Irregular triangular array T read by rows: T(i,0) = T(i,2i) = 1 for i >= 0; T(i,1) = T(i,2i-1) = floor(i/2) for i >= 1; and for i >= 2 and j = 2..2i-2, T(i,j) = T(i-1,j-2) + T(i-1,j-1) + T(i-1,j) if i+j is odd, and T(i,j) = T(i-1,j-2) + T(i-1,j) if i+j is even.

Formalization notes:
* T(i, j) is defined for 0 <= j <= 2i by the rule of A026584 and is 0 outside the row; the
  definition reproduces the array's data.
* a(n) = T(n, n - 2) for n >= 2, the entry's offset (natural subtraction below it). The title's
  second description, the number of strings s(0), ..., s(n) counted by A026584 with s(n) = 2, is
  the same number by the comment of A026584; the statement uses the first. The block gives no
  range for the recurrence, so it is stated for every n >= 7, the smallest n for which a(n - 5) is
  a term of the entry, as an identity of integers.
* The definition reproduces the entry's data (1, 1, 5, 9, 28, 62, ... from n = 2); the proof file
  proves all 29 listed terms as controls.
-/

namespace OMA.S_oeis_a026587

/-- A026584 T(i, j), 0 <= j <= 2i: T(i, 0) = T(i, 2i) = 1, T(i, 1) = T(i, 2i - 1) = floor(i/2) for
i >= 1, and for 2 <= j <= 2i - 2, T(i, j) = T(i-1, j-2) + T(i-1, j-1) + T(i-1, j) if i + j is odd
and T(i, j) = T(i-1, j-2) + T(i-1, j) if i + j is even (0 beyond the row). -/
def T : ℕ → ℕ → ℕ
  | 0, j => if j = 0 then 1 else 0
  | i + 1, j =>
    if 2 * (i + 1) < j then 0
    else if j = 0 ∨ j = 2 * (i + 1) then 1
    else if j = 1 ∨ j = 2 * (i + 1) - 1 then (i + 1) / 2
    else if (i + 1 + j) % 2 = 1 then T i (j - 2) + T i (j - 1) + T i j
    else T i (j - 2) + T i j

/-- A026587: a(n) = T(n, n - 2). -/
def a (n : ℕ) : ℕ := T n (n - 2)

/-- Mathar's conjecture. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
      ((n : ℤ) + 2) * (a n : ℤ) = (3 * (n : ℤ) + 2) * (a (n - 1) : ℤ) + (3 * (n : ℤ) + 2) * (a (n - 2) : ℤ) - (11 * (n : ℤ) - 16) * (a (n - 3) : ℤ) - 2 * ((n : ℤ) - 3) * (a (n - 4) : ℤ) + 4 * (2 * (n : ℤ) - 9) * (a (n - 5) : ℤ) := by
  sorry

end OMA.S_oeis_a026587
