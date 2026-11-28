import Mathlib

/-!
# OEIS A027087: Mathar's recurrence for T(n, 2n) of the array A027082

Source: https://oeis.org/A027087 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A027087 (Clark Kimberling), offset 0: a(n) = A027082(n, 2n).
Formula section:
Conjecture: D-finite with recurrence +3*n*a(n) +3*(-5*n+3)*a(n-1) +(7*n-4)*a(n-2) +(25*n-67)*a(n-3) +(17*n-44)*a(n-4) +(19*n-97)*a(n-5) +(5*n-32)*a(n-6) +3*(n-7)*a(n-7)=0. - R. J. Mathar, Jun 24 2020

A027082 (Clark Kimberling): Irregular triangular array: T(n,0) = 1 for n >= 1; T(n,1) = T(n,2) = 1 for n >= 1; T(n,k) = T(n-1,k-3) + T(n-1,k-2) + T(n-1,k-1) for 3 <= k <= 2n-1 and n >= 2; and T(n,2n) = T(n-1,2n-3) + T(n-1,2n-2) for n >= 2.

Formalization notes:
* T(n, k) is defined for 0 <= k <= 2n by the rule of A027082 and is 0 outside the row. The name
  states T(n, 0) = T(n, 1) = T(n, 2) = 1 for n >= 1; the definition also sets T(0, 0) = 1, the
  first term of the array's data (its row 0).
* a(n) = T(n, 2n) for n >= 0, the entry's offset. The block gives no range for the recurrence, so
  it is stated for every n >= 7, the smallest n for which a(n - 7) is a term of the entry, as an
  identity of integers.
* The definition reproduces the entry's data (1, 1, 2, 5, 11, 27, ... from n = 0); the proof file
  proves all 29 listed terms as controls.
-/

namespace OMA.S_oeis_a027087

/-- A027082 T(n, k), 0 <= k <= 2n: T(0, 0) = 1; for n >= 1, T(n, k) = 1 for k <= 2; for n >= 2,
T(n, k) = T(n-1, k-3) + T(n-1, k-2) + T(n-1, k-1) for 3 <= k <= 2n - 1 and
T(n, 2n) = T(n-1, 2n-3) + T(n-1, 2n-2) (0 beyond the row). -/
def T : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | n + 1, k =>
    if 2 * (n + 1) < k then 0
    else if k < 3 then 1
    else if k = 2 * (n + 1) then T n (k - 3) + T n (k - 2)
    else T n (k - 3) + T n (k - 2) + T n (k - 1)

/-- A027087: a(n) = T(n, 2n). -/
def a (n : ℕ) : ℕ := T n (2 * n)

/-- Mathar's conjecture. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
      3 * (n : ℤ) * (a n : ℤ) + 3 * (-5 * (n : ℤ) + 3) * (a (n - 1) : ℤ) + (7 * (n : ℤ) - 4) * (a (n - 2) : ℤ) + (25 * (n : ℤ) - 67) * (a (n - 3) : ℤ) + (17 * (n : ℤ) - 44) * (a (n - 4) : ℤ) + (19 * (n : ℤ) - 97) * (a (n - 5) : ℤ) + (5 * (n : ℤ) - 32) * (a (n - 6) : ℤ) + 3 * ((n : ℤ) - 7) * (a (n - 7) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a027087
