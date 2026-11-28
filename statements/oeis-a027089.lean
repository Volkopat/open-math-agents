import Mathlib

/-!
# OEIS A027089: Mathar's recurrence for T(n, 2n - 2) of the array A027082

Source: https://oeis.org/A027089 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A027089 (Clark Kimberling), offset 2: a(n) = A027082(n, 2n-2).
Formula section:
Conjecture: D-finite with recurrence -(n+2)*(244*n-1065)*a(n) +3*(n+1)*(422*n -1703)*a(n-1) +2*(-359*n^2 +1211*n -1420)*a(n-2) +2*(-1174*n^2 +6319*n -7410)*a(n-3) +(-760*n^2 +2173*n +1616)*a(n-4) +(-502*n^2 +2245*n -1123)*a(n-5) +6*(23*n-67) *(n-5)*a(n-6)=0. - R. J. Mathar, Jun 24 2020

A027082 (Clark Kimberling): Irregular triangular array: T(n,0) = 1 for n >= 1; T(n,1) = T(n,2) = 1 for n >= 1; T(n,k) = T(n-1,k-3) + T(n-1,k-2) + T(n-1,k-1) for 3 <= k <= 2n-1 and n >= 2; and T(n,2n) = T(n-1,2n-3) + T(n-1,2n-2) for n >= 2.

Formalization notes:
* T(n, k) is defined for 0 <= k <= 2n by the rule of A027082 and is 0 outside the row. The name
  states T(n, 0) = T(n, 1) = T(n, 2) = 1 for n >= 1; the definition also sets T(0, 0) = 1, the
  first term of the array's data (its row 0).
* a(n) = T(n, 2n - 2) for n >= 2, the entry's offset (natural subtraction below it). The block
  gives no range for the recurrence, so it is stated for every n >= 8, the smallest n for which
  a(n - 6) is a term of the entry, as an identity of integers.
* The definition reproduces the entry's data (1, 5, 14, 39, 108, 299, ... from n = 2); the proof
  file proves all 26 listed terms as controls.
-/

namespace OMA.S_oeis_a027089

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

/-- A027089: a(n) = T(n, 2n - 2). -/
def a (n : ℕ) : ℕ := T n (2 * n - 2)

/-- Mathar's conjecture. -/
theorem main : ∀ n : ℕ, 8 ≤ n →
      - ((n : ℤ) + 2) * (244 * (n : ℤ) - 1065) * (a n : ℤ) + 3 * ((n : ℤ) + 1) * (422 * (n : ℤ) - 1703) * (a (n - 1) : ℤ) + 2 * (-359 * (n : ℤ) ^ 2 + 1211 * (n : ℤ) - 1420) * (a (n - 2) : ℤ) + 2 * (-1174 * (n : ℤ) ^ 2 + 6319 * (n : ℤ) - 7410) * (a (n - 3) : ℤ) + (-760 * (n : ℤ) ^ 2 + 2173 * (n : ℤ) + 1616) * (a (n - 4) : ℤ) + (-502 * (n : ℤ) ^ 2 + 2245 * (n : ℤ) - 1123) * (a (n - 5) : ℤ) + 6 * (23 * (n : ℤ) - 67) * ((n : ℤ) - 5) * (a (n - 6) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a027089
