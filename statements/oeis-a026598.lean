import Mathlib

/-!
# OEIS A026598: Mathar's recurrence for the sums of T(i, j) over 0 <= j <= i <= n of the array A026584

Source: https://oeis.org/A026598 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A026598 (Clark Kimberling), offset 0: a(n) = Sum_{i=0..n} Sum_{j=0..i} T(i,j), T given by A026584.
Formula section:
a(n) = Sum{i=0..n} Sum{j=0..i} A026584(i, j).
Conjecture: n*a(n) - (4*n-3)*a(n-1) - (2*n-3)*a(n-2) + 5*(4*n-9)*a(n-3) - 7*(n-3)*a(n-4) - 6*(4*n-15)*a(n-5) + 8*(2*n-9)*a(n-6) = 0. - R. J. Mathar, Jun 23 2013

A026584 (Clark Kimberling): Irregular triangular array T read by rows: T(i,0) = T(i,2i) = 1 for i >= 0; T(i,1) = T(i,2i-1) = floor(i/2) for i >= 1; and for i >= 2 and j = 2..2i-2, T(i,j) = T(i-1,j-2) + T(i-1,j-1) + T(i-1,j) if i+j is odd, and T(i,j) = T(i-1,j-2) + T(i-1,j) if i+j is even.

Formalization notes:
* T(i, j) is defined for 0 <= j <= 2i by the rule of A026584 and is 0 outside the row; the
  definition reproduces the array's data.
* a(n) = the sum of T(i, j) over 0 <= j <= i and 0 <= i <= n, for n >= 0, the entry's offset. The
  block gives no range for the recurrence, so it is stated for every n >= 6, the smallest n for
  which a(n - 6) is a term of the entry, as an identity of integers.
* The definition reproduces the entry's data (1, 2, 6, 14, 37, 91, ... from n = 0); the proof file
  proves all 28 listed terms as controls.
-/

namespace OMA.S_oeis_a026598

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

/-- A026598: a(n) = the sum of T(i, j) over 0 <= j <= i, 0 <= i <= n. -/
def a (n : ℕ) : ℕ := ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (i + 1), T i j

/-- Mathar's conjecture. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
      (n : ℤ) * (a n : ℤ) - (4 * (n : ℤ) - 3) * (a (n - 1) : ℤ) - (2 * (n : ℤ) - 3) * (a (n - 2) : ℤ) + 5 * (4 * (n : ℤ) - 9) * (a (n - 3) : ℤ) - 7 * ((n : ℤ) - 3) * (a (n - 4) : ℤ) - 6 * (4 * (n : ℤ) - 15) * (a (n - 5) : ℤ) + 8 * (2 * (n : ℤ) - 9) * (a (n - 6) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a026598
