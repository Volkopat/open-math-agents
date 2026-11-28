import Mathlib

/-!
# OEIS A027028: Mathar's recurrence for T(n, 2n - 4) of the tribonacci array A027023

Source: https://oeis.org/A027028 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A027028 (Clark Kimberling), offset 2: a(n) = T(n,2n-4), T given by A027023.
Formula section:
Conjecture D-finite with recurrence -(n+2)*(n-6)*a(n) +3*(n+1)*(2*n-11)*a(n-1) -n*(7*n-31)*a(n-2) -2*(n-3)*(4*n-19)*a(n-3) +(5*n^2-38*n+84)*a(n-4) +(2*n-5)*(n-3)*a(n-5) +3*(n-3)*(n-4)*a(n-6)=0. - R. J. Mathar, Jun 24 2020
a(n) ~ 3^(n + 5/2) / (sqrt(Pi) * n^(3/2)). - Vaclav Kotesovec, Mar 08 2023

A027023 (Clark Kimberling): Tribonacci array: triangular array T read by rows: T(n,0)=1 for n >= 0, T(n,1) = T(n,2n) = 1 for n >= 1, T(n,2)=1 for n >= 2 and for n >= 3, T(n,k) = T(n-1,k-3) + T(n-1,k-2) + T(n-1,k-1) for 3 <= k <= 2n-1.

Formalization notes:
* T(n, k) is defined for 0 <= k <= 2n by the rule of A027023 and is 0 outside the row. The name's
  recursion is stated for n >= 3, which leaves T(2, 3) open; the definition applies the recursion
  there too, T(2, 3) = T(1, 0) + T(1, 1) + T(1, 2) = 3, which is the array's data (row 2 of
  A027023 is 1, 1, 1, 3, 1).
* a(n) = T(n, 2n - 4) for n >= 2, the entry's offset (natural subtraction below it). The block
  gives no range for the recurrence, so it is stated for every n >= 8, the smallest n for which
  a(n - 6) is a term of the entry, as an identity of integers.
* The definition reproduces the entry's data (1, 1, 5, 17, 53, 161, ... from n = 2); the proof
  file proves all 26 listed terms as controls.
-/

namespace OMA.S_oeis_a027028

/-- A027023 T(n, k), 0 <= k <= 2n: T(n, k) = 1 for k < 3 and for k = 2n, and
T(n, k) = T(n-1, k-3) + T(n-1, k-2) + T(n-1, k-1) for 3 <= k <= 2n - 1 (0 beyond the row). -/
def T : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | n + 1, k =>
    if 2 * (n + 1) < k then 0
    else if k < 3 ∨ k = 2 * (n + 1) then 1
    else T n (k - 3) + T n (k - 2) + T n (k - 1)

/-- A027028: a(n) = T(n, 2n - 4). -/
def a (n : ℕ) : ℕ := T n (2 * n - 4)

/-- Mathar's conjecture. -/
theorem main : ∀ n : ℕ, 8 ≤ n →
      - ((n : ℤ) + 2) * ((n : ℤ) - 6) * (a n : ℤ) + 3 * ((n : ℤ) + 1) * (2 * (n : ℤ) - 11) * (a (n - 1) : ℤ) - (n : ℤ) * (7 * (n : ℤ) - 31) * (a (n - 2) : ℤ) - 2 * ((n : ℤ) - 3) * (4 * (n : ℤ) - 19) * (a (n - 3) : ℤ) + (5 * (n : ℤ) ^ 2 - 38 * (n : ℤ) + 84) * (a (n - 4) : ℤ) + (2 * (n : ℤ) - 5) * ((n : ℤ) - 3) * (a (n - 5) : ℤ) + 3 * ((n : ℤ) - 3) * ((n : ℤ) - 4) * (a (n - 6) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a027028
