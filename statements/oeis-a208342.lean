import Mathlib

/-!
# A208342: coefficients of the polynomials u(n,x) jointly generated with A208343
Source: https://oeis.org/A208342 (Werner Schulte, Mar 07 2017)

The polynomials are defined (Formula section) by u(1,x) = 1, v(1,x) = 1 and, for n >= 1,
u(n+1,x) = u(n,x) + x*v(n,x), v(n+1,x) = x*u(n,x) + x*v(n,x).
The triangle (offset 1) lists the coefficients of u(n,x) in increasing powers of x, so for
1 <= k <= n the entry T(n,k) is the coefficient of x^(k-1) in u(n,x).
Below, uv m is the pair (u(m+1,x), v(m+1,x)).

Conjecture: T(n,k) = Sum_{j=0..floor((k-1)/2)} binomial(k-1-j,j)*binomial(n-k+j,j)
for 0 < k <= n.
-/

namespace OMA.S_oeis_a208342

open Polynomial

/-- uv m = (u(m+1,x), v(m+1,x)). -/
noncomputable def uv : ℕ → ℤ[X] × ℤ[X]
  | 0 => (1, 1)
  | m + 1 => ((uv m).1 + X * (uv m).2, X * (uv m).1 + X * (uv m).2)

/-- u(n,x) for n >= 1. -/
noncomputable def u (n : ℕ) : ℤ[X] := (uv (n - 1)).1

/-- A208342: T(n,k) = coefficient of x^(k-1) in u(n,x). -/
noncomputable def T (n k : ℕ) : ℤ := (u n).coeff (k - 1)

theorem main : ∀ n k : ℕ, 0 < k → k ≤ n →
    T n k = ∑ j ∈ Finset.range ((k - 1) / 2 + 1),
      ((k - 1 - j).choose j : ℤ) * ((n - k + j).choose j : ℤ) := by
  sorry

end OMA.S_oeis_a208342
