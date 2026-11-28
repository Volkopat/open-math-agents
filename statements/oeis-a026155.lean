import Mathlib

/-!
# OEIS A026155: Chai Wah Wu's conjectures for T(n, n - 4) of the array A026148

Source: https://oeis.org/A026155 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A026155 (Clark Kimberling), offset 4: T(n,n-4), where T is the array in A026148.
Formula section:
Conjectures from Chai Wah Wu, Mar 23 2020: (Start)
a(n) = 12*a(n-1) - 53*a(n-2) + 90*a(n-3) + 26*a(n-4) - 256*a(n-5) + 160*a(n-6) + 224*a(n-7) - 203*a(n-8) - 84*a(n-9) + 77*a(n-10) + 14*a(n-11) - 7*a(n-12) for n > 15.
G.f.: x^4*(x - 1)^2*(x^6 - 6*x^5 - 13*x^4 + 8*x^3 + 8*x^2 - 6*x + 1)/((7*x^6 + 7*x^5 - 21*x^4 + 14*x^2 - 7*x + 1)*(x^6 - 3*x^5 - 5*x^4 + 8*x^3 + 4*x^2 - 5*x + 1)). (End)

A026148 (Clark Kimberling): Irregular triangular array T read by rows: T(n,0) = 1 for i >= 0, T(1,1) = 1,T(2,1) = 1, T(2,2) = 2, T(2,3) = 1, T(2,4) = 1 and for n >= 3, T(n,1) = n-1,  T(n,k) = T(n-1,k-2) + T(n-1,k-1) + T(n-1,k) for k=2,...,n+1, and T(n, k+2) = T(n-1, k) + T(n-1, k+1).

Formalization notes:
* T(n, k) is defined for 0 <= k <= n + 2 by the rule of A026148 and is 0 outside the rows. The
  name's last clause, T(n, k+2) = T(n-1, k) + T(n-1, k+1), is read as the right end of row n, T(n,
  n + 2) = T(n-1, n) + T(n-1, n + 1): row n has the n + 3 entries k = 0..n+2 and the recursion
  covers k = 2..n+1. With this reading the definition reproduces the array's data.
* a(n) = T(n, n - 4) for n >= 4, the entry's offset (natural subtraction below it).
* The block's two conjectures, the recurrence for n > 15 and the generating function, are stated
  together as main, the recurrence as an identity of integers and the generating function as the
  power series sum_{n >= 4} a(n) x^n (the entry's offset is 4) with the division as multiplication
  by the inverse of the denominator (constant term 1).
* The definition reproduces the entry's data (1, 4, 16, 56, 189, 616, ... from n = 4); the proof
  file proves all 26 listed terms as controls.
-/

namespace OMA.S_oeis_a026155

open PowerSeries

/-- A026148 T(n, k): rows 0 and 1 are 1 and 1, 1; row 2 is 1, 1, 2, 1, 1; for n >= 3 and
0 <= k <= n + 2, T(n, 0) = 1, T(n, 1) = n - 1, T(n, k) = T(n-1, k-2) + T(n-1, k-1) + T(n-1, k) for
2 <= k <= n + 1, and T(n, n + 2) = T(n-1, n) + T(n-1, n + 1) (0 beyond the rows). -/
def T : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | 1, k => if k ≤ 1 then 1 else 0
  | 2, k => if k = 2 then 2 else if k ≤ 4 then 1 else 0
  | n + 3, k =>
    if n + 5 < k then 0
    else if k = 0 then 1
    else if k = 1 then n + 2
    else if k = n + 5 then T (n + 2) (n + 3) + T (n + 2) (n + 4)
    else T (n + 2) (k - 2) + T (n + 2) (k - 1) + T (n + 2) k

/-- A026155: a(n) = T(n, n - 4). -/
def a (n : ℕ) : ℕ := T n (n - 4)

/-- Chai Wah Wu's conjectures. -/
theorem main :
    (∀ n : ℕ, 15 < n →
      (a n : ℤ) = 12 * a (n - 1) - 53 * a (n - 2) + 90 * a (n - 3) + 26 * a (n - 4) -
        256 * a (n - 5) + 160 * a (n - 6) + 224 * a (n - 7) - 203 * a (n - 8) -
        84 * a (n - 9) + 77 * a (n - 10) + 14 * a (n - 11) - 7 * a (n - 12)) ∧
    mk (fun n => if 4 ≤ n then (a n : ℚ) else 0) =
      X ^ 4 * (X - 1) ^ 2 * (X ^ 6 - 6 * X ^ 5 - 13 * X ^ 4 + 8 * X ^ 3 + 8 * X ^ 2 - 6 * X + 1) *
        ((7 * X ^ 6 + 7 * X ^ 5 - 21 * X ^ 4 + 14 * X ^ 2 - 7 * X + 1) *
          (X ^ 6 - 3 * X ^ 5 - 5 * X ^ 4 + 8 * X ^ 3 + 4 * X ^ 2 - 5 * X + 1) : PowerSeries ℚ)⁻¹ := by
  sorry

end OMA.S_oeis_a026155
