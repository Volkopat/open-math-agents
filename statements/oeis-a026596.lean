import Mathlib

/-!
# OEIS A026596: Mathar's recurrence for T(n, 0) + ... + T(n, n) of the array A026584

Source: https://oeis.org/A026596 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A026596 (Clark Kimberling), offset 0: Row sums of A026584.
Formula section:
a(n) = Sum{k=0..n} A026584(n, k).
Conjecture: n*a(n) -3*(n-1)*a(n-1) -(5*n-6)*a(n-2) +3*(5*n-13)*a(n-3) +2*(4*n-9)*a(n-4) -8*(2*n-9)*a(n-5) = 0. - R. J. Mathar, Jun 23 2013

A026584 (Clark Kimberling): Irregular triangular array T read by rows: T(i,0) = T(i,2i) = 1 for i >= 0; T(i,1) = T(i,2i-1) = floor(i/2) for i >= 1; and for i >= 2 and j = 2..2i-2, T(i,j) = T(i-1,j-2) + T(i-1,j-1) + T(i-1,j) if i+j is odd, and T(i,j) = T(i-1,j-2) + T(i-1,j) if i+j is even.

Formalization notes:
* T(i, j) is defined for 0 <= j <= 2i by the rule of A026584 and is 0 outside the row; the
  definition reproduces the array's data.
* a(n) = T(n, 0) + T(n, 1) + ... + T(n, n), the entries of row n up to its middle, for n >= 0, the
  entry's offset. The entry's own formula line, a(n) = Sum_{k=0..n} A026584(n, k), and its data
  (a(1) = 1, while row 1 is 1, 0, 1) define a(n) as this sum over the first half of row n; the
  name, row sums of A026584, is loose, and the full row sums T(n, 0) + ... + T(n, 2n) are A026597.
  The proof file also proves Mathar's recurrence for the full row sums, as a separate theorem that
  is not part of main. The block gives no range for the recurrence, so it is stated for every n >=
  5, the smallest n for which a(n - 5) is a term of the entry, as an identity of integers.
* The definition reproduces the entry's data (1, 1, 4, 8, 23, 54, ... from n = 0); the proof file
  proves all 29 listed terms as controls.
-/

namespace OMA.S_oeis_a026596

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

/-- A026596: a(n) = T(n, 0) + T(n, 1) + ... + T(n, n). -/
def a (n : ℕ) : ℕ := ∑ j ∈ Finset.range (n + 1), T n j

/-- Mathar's conjecture. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
      (n : ℤ) * (a n : ℤ) - 3 * ((n : ℤ) - 1) * (a (n - 1) : ℤ) - (5 * (n : ℤ) - 6) * (a (n - 2) : ℤ) + 3 * (5 * (n : ℤ) - 13) * (a (n - 3) : ℤ) + 2 * (4 * (n : ℤ) - 9) * (a (n - 4) : ℤ) - 8 * (2 * (n : ℤ) - 9) * (a (n - 5) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a026596
