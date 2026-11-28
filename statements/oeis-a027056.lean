import Mathlib

/-!
# OEIS A027056: Mathar's recurrence for T(n, 2n - 1) of the array A027052

Source: https://oeis.org/A027056 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A027056 (Clark Kimberling), offset 1: a(n) = A027052(n, 2n-1).
Formula section:
Conjecture:b D-finite with recurrence (-n+1)*a(n) +2*(3*n-4)*a(n-1) +(-7*n+3)*a(n-2) +4*(-2*n+13)*a(n-3) +(5*n-29)*a(n-4) +2*(n-2)*a(n-5) +3*(n-5)*a(n-6)=0. - R. J. Mathar, Jun 15 2020
a(n) ~ 3^(n + 3/2) / (2 * sqrt(Pi) * n^(3/2)). - Vaclav Kotesovec, Mar 08 2023

A027052 (Clark Kimberling): Triangular array T read by rows: T(n,0) = T(n,2n) = 1 for n >= 0, T(n,1)=0 for n >= 1, T(n,2)=1 for n >= 2 and for n >= 3, T(n,k) = T(n-1,k-3) + T(n-1, k-2) + T(n-1,k-1) for 3 <= k <= 2n-1. T(n,k)=0 for k < 0 or k > 2n.

Formalization notes:
* T(n, k) is defined for 0 <= k <= 2n by the rule of A027052 and is 0 outside the row. The name's
  recursion is stated for n >= 3, which leaves T(2, 3) open; the definition applies the recursion
  there too, T(2, 3) = T(1, 0) + T(1, 1) + T(1, 2) = 2, which is the array's data (row 2 of
  A027052 is 1, 0, 1, 2, 1).
* a(n) = T(n, 2n - 1) for n >= 1, the entry's offset (natural subtraction below it). The block
  gives no range for the recurrence, so it is stated for every n >= 7, the smallest n for which
  a(n - 6) is a term of the entry, as an identity of integers.
* The definition reproduces the entry's data (0, 2, 4, 8, 18, 42, ... from n = 1); the proof file
  proves all 32 listed terms as controls.
-/

namespace OMA.S_oeis_a027056

/-- A027052 T(n, k), 0 <= k <= 2n: T(n, 0) = T(n, 2) = T(n, 2n) = 1, T(n, 1) = 0 for n >= 1, and
T(n, k) = T(n-1, k-3) + T(n-1, k-2) + T(n-1, k-1) for 3 <= k <= 2n - 1 (0 beyond the row). -/
def T : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | n + 1, k =>
    if 2 * (n + 1) < k then 0
    else if k = 1 then 0
    else if k < 3 ∨ k = 2 * (n + 1) then 1
    else T n (k - 3) + T n (k - 2) + T n (k - 1)

/-- A027056: a(n) = T(n, 2n - 1). -/
def a (n : ℕ) : ℕ := T n (2 * n - 1)

/-- Mathar's conjecture. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
      (-(n : ℤ) + 1) * (a n : ℤ) + 2 * (3 * (n : ℤ) - 4) * (a (n - 1) : ℤ) + (-7 * (n : ℤ) + 3) * (a (n - 2) : ℤ) + 4 * (-2 * (n : ℤ) + 13) * (a (n - 3) : ℤ) + (5 * (n : ℤ) - 29) * (a (n - 4) : ℤ) + 2 * ((n : ℤ) - 2) * (a (n - 5) : ℤ) + 3 * ((n : ℤ) - 5) * (a (n - 6) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a027056
