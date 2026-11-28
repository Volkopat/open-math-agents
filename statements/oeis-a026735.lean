import Mathlib

/-!
# OEIS A026735: Voznyy's generating function for the antidiagonal sums of the array A026725

Source: https://oeis.org/A026735 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A026735 (Clark Kimberling), offset 0: a(n) = Sum_{k=0..floor(n/2)} T(n-k,k), T given by A026725.
Formula section:
Conjecture: G.f.:-1/2*(2*x^6-5*x^4+8*x^3+x-2+x*(x-1)*(x^2+x+1)*(1-4*x^3)^(1/2))/(x^6+4*x^3-1)/(x^2+x-1). -  Maksym Voznyy (voznyy(AT)mail.ru), Aug 11 2009

A026725 (Clark Kimberling): Triangular array, T, read by rows: T(n,0) = T(n,n) = 1. For n >= 2 and 1<=k<=n-1, T(n,k) = T(n-1,k-1) + T(n-2,k-1) + T(n-1,k) if n is odd and k=(n-1)/2, otherwise T(n,k) = T(n-1,k-1) + T(n-1,k).

Formalization notes:
* T(n, k) is defined for 0 <= k <= n by the rule of A026725 and is 0 outside the row; the
  definition reproduces the array's data.
* a(n) = T(n, 0) + T(n - 1, 1) + ... + T(n - floor(n/2), floor(n/2)), the entry's formula; k <=
  floor(n/2) keeps n - k >= k inside the array.
* The generating function is the formal power series sum_{n >= 0} a(n) x^n (offset 0). The block's
  divisions by x^6 + 4x^3 - 1 and x^2 + x - 1 are multiplications by their inverses in the power
  series ring (both have constant term -1), and (1-4*x^3)^(1/2) is the power series with constant
  term 1, the binomial series (1 + X)^(1/2) evaluated at -4X^3.
* The definition reproduces the entry's data (1, 1, 2, 3, 6, 9, ... from n = 0); the proof file
  proves all 37 listed terms as controls.
-/

namespace OMA.S_oeis_a026735

open PowerSeries

/-- A026725 T(n, k), 0 <= k <= n: T(n, 0) = T(n, n) = 1, and for n >= 2 and 1 <= k <= n - 1,
T(n, k) = T(n-1, k-1) + T(n-2, k-1) + T(n-1, k) if n is odd and k = (n-1)/2, and
T(n, k) = T(n-1, k-1) + T(n-1, k) otherwise (0 beyond the row). -/
def T : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | 1, k => if k ≤ 1 then 1 else 0
  | n + 2, k =>
    if n + 2 < k then 0
    else if k = 0 ∨ k = n + 2 then 1
    else if n % 2 = 1 ∧ 2 * k = n + 1 then T (n + 1) (k - 1) + T n (k - 1) + T (n + 1) k
    else T (n + 1) (k - 1) + T (n + 1) k

/-- A026735: a(n) = T(n, 0) + T(n-1, 1) + ... + T(n - floor(n/2), floor(n/2)). -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n / 2 + 1), T (n - k) k

/-- (1 - 4x^3)^(1/2) with constant term 1: the binomial series (1 + X)^(1/2) evaluated at
-4X^3. -/
noncomputable def S : PowerSeries ℚ :=
  (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (-4 * X ^ 3 : PowerSeries ℚ)

/-- Voznyy's generating function. -/
theorem main :
    mk (fun n => (a n : ℚ)) =
      C (-1 / 2 : ℚ) * (2 * X ^ 6 - 5 * X ^ 4 + 8 * X ^ 3 + X - 2 +
        X * (X - 1) * (X ^ 2 + X + 1) * S) *
        (X ^ 6 + 4 * X ^ 3 - 1 : PowerSeries ℚ)⁻¹ * (X ^ 2 + X - 1 : PowerSeries ℚ)⁻¹ := by
  sorry

end OMA.S_oeis_a026735
