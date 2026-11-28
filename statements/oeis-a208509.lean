import Mathlib

/-!
# A208509: coefficients of the polynomials v(n,x) jointly generated with A208508

Source: https://oeis.org/A208509 (conjecture by Knud Werner, Jan 11 2022)

The OEIS defines, for n >= 1, u(1,x) = 1, v(1,x) = 1 and
u(n,x) = u(n-1,x) + x*v(n-1,x), v(n,x) = u(n-1,x) + v(n-1,x) + 1.
T(n,k) is the coefficient of x^k in v(n,x) (offset 1, k starting at 0); row n consists of
the entries with 2*k+1 <= n.

Below, `P m = (u(m+1,x), v(m+1,x))` (a shift by one so that the recursion starts at index 0),
and `T n k` is the coefficient of `X^k` in `v(n,x)` for `n >= 1`.

The conjecture: T(n,k) = binomial(n-1,2*k+1) + binomial(n,2*k+1) for every entry of the
triangle, i.e. for n >= 1 and 2*k+1 <= n.
-/

namespace OMA.S_oeis_a208509

open Polynomial

/-- `P m = (u(m+1,x), v(m+1,x))`. -/
noncomputable def P : ℕ → ℕ[X] × ℕ[X]
  | 0 => (1, 1)
  | m + 1 => ((P m).1 + X * (P m).2, (P m).1 + (P m).2 + 1)

/-- `T n k` = coefficient of `x^k` in `v(n,x)`, for `n >= 1`. -/
noncomputable def T (n k : ℕ) : ℕ := (P (n - 1)).2.coeff k

theorem main : ∀ n k : ℕ, 1 ≤ n → 2 * k + 1 ≤ n →
    T n k = Nat.choose (n - 1) (2 * k + 1) + Nat.choose n (2 * k + 1) := by
  sorry

end OMA.S_oeis_a208509
