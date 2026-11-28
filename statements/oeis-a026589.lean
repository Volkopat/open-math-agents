import Mathlib

/-!
# OEIS A026589: Mathar's recurrence for T(n, n - 4) of the array A026584

Source: https://oeis.org/A026589 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A026589 (Clark Kimberling), offset 4: a(n) = T(n,n-4), T given by A026584. Also a(n) = number of integer strings s(0),...,s(n) counted by T, such that s(n)=4.
Formula section:
a(n) = A026584(n, n-4).
Conjecture: -(n+4)*(65*n-269)*a(n) +(-65*n^2+140*n+1933)*a(n-1) +(809*n^2-2431*n-4514)*a(n-2) +(-123*n^2+2496*n-205)*a(n-3) +2*(-726*n^2+3737*n-4395)*a(n-4) +8*(56*n-215)*(2*n-9)*a(n-5) = 0. - R. J. Mathar, Jun 23 2013

A026584 (Clark Kimberling): Irregular triangular array T read by rows: T(i,0) = T(i,2i) = 1 for i >= 0; T(i,1) = T(i,2i-1) = floor(i/2) for i >= 1; and for i >= 2 and j = 2..2i-2, T(i,j) = T(i-1,j-2) + T(i-1,j-1) + T(i-1,j) if i+j is odd, and T(i,j) = T(i-1,j-2) + T(i-1,j) if i+j is even.

Formalization notes:
* T(i, j) is defined for 0 <= j <= 2i by the rule of A026584 and is 0 outside the row; the
  definition reproduces the array's data.
* a(n) = T(n, n - 4) for n >= 4, the entry's offset (natural subtraction below it). The title's
  second description, the number of strings s(0), ..., s(n) counted by A026584 with s(n) = 4, is
  the same number by the comment of A026584; the statement uses the first. The block gives no
  range for the recurrence, so it is stated for every n >= 9, the smallest n for which a(n - 5) is
  a term of the entry, as an identity of integers.
* The definition reproduces the entry's data (1, 2, 9, 22, 69, 178, ... from n = 4); the proof
  file proves all 27 listed terms as controls.
-/

namespace OMA.S_oeis_a026589

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

/-- A026589: a(n) = T(n, n - 4). -/
def a (n : ℕ) : ℕ := T n (n - 4)

/-- Mathar's conjecture. -/
theorem main : ∀ n : ℕ, 9 ≤ n →
      -((n : ℤ) + 4) * (65 * (n : ℤ) - 269) * (a n : ℤ) + (-65 * (n : ℤ) ^ 2 + 140 * (n : ℤ) + 1933) * (a (n - 1) : ℤ) + (809 * (n : ℤ) ^ 2 - 2431 * (n : ℤ) - 4514) * (a (n - 2) : ℤ) + (-123 * (n : ℤ) ^ 2 + 2496 * (n : ℤ) - 205) * (a (n - 3) : ℤ) + 2 * (-726 * (n : ℤ) ^ 2 + 3737 * (n : ℤ) - 4395) * (a (n - 4) : ℤ) + 8 * (56 * (n : ℤ) - 215) * (2 * (n : ℤ) - 9) * (a (n - 5) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a026589
