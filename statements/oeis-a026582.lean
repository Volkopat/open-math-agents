import Mathlib

/-!
# OEIS A026582: Mathar's recurrence for the sums of T(i, j) over 0 <= j <= i <= n of the array A026568

Source: https://oeis.org/A026582 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A026582 (Clark Kimberling), offset 0: a(n) = Sum{T(i,j)}, 0<=j<=i, 0<=i<=n, T given by A026568.
Formula section:
Conjecture: n*a(n) +2*(-2*n+1)*a(n-1) +2*(-n+3)*a(n-2) +20*(n-2)*a(n-3) +(-7*n+6)*a(n-4) +2*(-12*n+41)*a(n-5) +8*(2*n-7)*a(n-6)=0. - R. J. Mathar, Jun 23 2013

A026568 (Clark Kimberling): Irregular triangular array T read by rows: T(i,0) = T(i,2i) = 1 for i >= 0; T(i,1) = T(i,2i-1) = [ (i+1)/2 ] for i >= 1; and for i >= 2 and 2 <=j <= i - 2, T(i,j) = T(i-1,j-2) + T(i-1,j-1) + T(i-1,j) if i + j is even, T(i,j) = T(i-1,j-2) + T(i-1,j) if i + j is odd.

Formalization notes:
* T(i, j) is defined for 0 <= j <= 2i by the rule of A026568 and is 0 outside the row. The name
  states the parity recursion for i >= 2 and 2 <= j <= i - 2; the definition applies it for 2 <= j
  <= 2i - 2, the range that the companion array A026584 states (j = 2..2i-2) and that the data
  needs: the name's boundary values fix only j <= 1 and j >= 2i - 1, and row 4 of the data is 1,
  2, 7, 7, 13, 7, 7, 2, 1. With this range the definition reproduces the array's data.
* a(n) = the sum of T(i, j) over 0 <= j <= i and 0 <= i <= n, for n >= 0, the entry's offset. The
  block gives no range for the recurrence, so it is stated for every n >= 6, the smallest n for
  which a(n - 6) is a term of the entry, as an identity of integers.
* The definition reproduces the entry's data (1, 3, 8, 20, 50, 125, ... from n = 0); the proof
  file proves all 28 listed terms as controls.
-/

namespace OMA.S_oeis_a026582

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

/-- A026582: a(n) = the sum of T(i, j) over 0 <= j <= i, 0 <= i <= n. -/
def a (n : ℕ) : ℕ := ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (i + 1), T i j

/-- Mathar's conjecture. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
      (n : ℤ) * (a n : ℤ) + 2 * (-2 * (n : ℤ) + 1) * (a (n - 1) : ℤ) + 2 * (-(n : ℤ) + 3) * (a (n - 2) : ℤ) + 20 * ((n : ℤ) - 2) * (a (n - 3) : ℤ) + (-7 * (n : ℤ) + 6) * (a (n - 4) : ℤ) + 2 * (-12 * (n : ℤ) + 41) * (a (n - 5) : ℤ) + 8 * (2 * (n : ℤ) - 7) * (a (n - 6) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a026582
