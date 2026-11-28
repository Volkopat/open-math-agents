import Mathlib

/-!
# A301653: Expansion of x*(1 + 2*x)/((1 - x)*(1 + x)*(1 - x - x^2)).

Source: https://oeis.org/A301653
Credit: @jagong-cmu

The entry gives the conjecture (Greg Dresden, May 18 2023)
a(n) = Sum_{k>=0} A051601(n-k,k) (conjectured).

Definitions, as in the OEIS entries:
* A301653 (offset 0, data 0, 1, 3, 5, 10, 16, ...) is the sequence of coefficients of
  `x*(1 + 2*x)/((1 - x)*(1 + x)*(1 - x - x^2))`. Here `a n` is the coefficient of `x^n` of
  this series in `ℚ[[x]]`. The inverse is the power series inverse over `ℚ`; it exists,
  because the denominator has constant coefficient `1`.
* A051601 is the triangle formed with Pascal's rule, except that the `n`-th row begins and ends
  with `n`: `T(n,0) = T(n,n) = n`, `T(n,k) = T(n-1,k) + T(n-1,k-1)` for `0 < k < n`
  (rows `0; 1, 1; 2, 2, 2; 3, 4, 4, 3; ...`). The triangle has no entries with `k > n`; the
  function `T` below gives `0` there, so the sum `Sum_{k>=0} T(n-k,k)` is the finite sum over
  `k = 0..n` (the terms with `k > n-k` are `0`).
* The truncated subtraction `n - k` on `ℕ` is the usual one, since `k ≤ n` in the sum.

The conjecture is stated for every `n ≥ 0`, as an equality in `ℚ`.
-/

namespace OMA.S_oeis_a301653

open PowerSeries

/-- A301653: the coefficients of `x*(1 + 2*x)/((1 - x)*(1 + x)*(1 - x - x^2))`. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n ((X * (1 + 2 * X) : PowerSeries ℚ) * ((1 - X) * (1 + X) * (1 - X - X ^ 2))⁻¹)

/-- A051601: `T(n,0) = T(n,n) = n`, `T(n,k) = T(n-1,k) + T(n-1,k-1)` for `0 < k < n`,
and `0` outside the triangle (`k > n`). -/
def T : ℕ → ℕ → ℕ
  | n, 0 => n
  | 0, _ + 1 => 0
  | n + 1, k + 1 =>
    if k + 1 < n + 1 then T n (k + 1) + T n k else if k + 1 = n + 1 then n + 1 else 0

/-- For every `n ≥ 0`, `a(n) = Sum_{k>=0} A051601(n-k,k)`. -/
theorem main : ∀ n : ℕ, a n = ∑ k ∈ Finset.range (n + 1), (T (n - k) k : ℚ) := by
  sorry

end OMA.S_oeis_a301653
