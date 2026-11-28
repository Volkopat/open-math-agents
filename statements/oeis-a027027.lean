import Mathlib

/-!
# OEIS A027027: Mathar's recurrence for T(n, 2n - 3) of the tribonacci array A027023

Source: https://oeis.org/A027027 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A027027 (Clark Kimberling), offset 2: a(n) = T(n, 2n-3), T given by A027023.
Formula section:
Conjecture: D-finite with recurrence (n+1)*a(n) +(-8*n-1)*a(n-1) +(19*n-14)*a(n-2) +2*(-3*n-1)*a(n-3) +(-21*n+89)*a(n-4) +(8*n-45)*a(n-5) +(n-4)*a(n-6) +6*(n-4)*a(n-7)=0. - R. J. Mathar, Jun 24 2020
a(n) ~ 3^(n + 7/2) / (4*sqrt(Pi)*n^(3/2)). - Vaclav Kotesovec, Mar 08 2023

A027023 (Clark Kimberling): Tribonacci array: triangular array T read by rows: T(n,0)=1 for n >= 0, T(n,1) = T(n,2n) = 1 for n >= 1, T(n,2)=1 for n >= 2 and for n >= 3, T(n,k) = T(n-1,k-3) + T(n-1,k-2) + T(n-1,k-1) for 3 <= k <= 2n-1.

Formalization notes:
* T(n, k) is defined for 0 <= k <= 2n by the rule of A027023 and is 0 outside the row. The name's
  recursion is stated for n >= 3, which leaves T(2, 3) open; the definition applies the recursion
  there too, T(2, 3) = T(1, 0) + T(1, 1) + T(1, 2) = 3, which is the array's data (row 2 of
  A027023 is 1, 1, 1, 3, 1).
* a(n) = T(n, 2n - 3) for n >= 2, the entry's offset (natural subtraction below it). The block
  gives no range for the recurrence, so it is stated for every n >= 9, the smallest n for which
  a(n - 7) is a term of the entry, as an identity of integers.
* The definition reproduces the entry's data (1, 3, 9, 27, 77, 215, ... from n = 2); the proof
  file proves all 27 listed terms as controls.
-/

namespace OMA.S_oeis_a027027

/-- A027023 T(n, k), 0 <= k <= 2n: T(n, k) = 1 for k < 3 and for k = 2n, and
T(n, k) = T(n-1, k-3) + T(n-1, k-2) + T(n-1, k-1) for 3 <= k <= 2n - 1 (0 beyond the row). -/
def T : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | n + 1, k =>
    if 2 * (n + 1) < k then 0
    else if k < 3 ∨ k = 2 * (n + 1) then 1
    else T n (k - 3) + T n (k - 2) + T n (k - 1)

/-- A027027: a(n) = T(n, 2n - 3). -/
def a (n : ℕ) : ℕ := T n (2 * n - 3)

/-- Mathar's conjecture. -/
theorem main : ∀ n : ℕ, 9 ≤ n →
      ((n : ℤ) + 1) * (a n : ℤ) + (-8 * (n : ℤ) - 1) * (a (n - 1) : ℤ) + (19 * (n : ℤ) - 14) * (a (n - 2) : ℤ) + 2 * (-3 * (n : ℤ) - 1) * (a (n - 3) : ℤ) + (-21 * (n : ℤ) + 89) * (a (n - 4) : ℤ) + (8 * (n : ℤ) - 45) * (a (n - 5) : ℤ) + ((n : ℤ) - 4) * (a (n - 6) : ℤ) + 6 * ((n : ℤ) - 4) * (a (n - 7) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a027027
