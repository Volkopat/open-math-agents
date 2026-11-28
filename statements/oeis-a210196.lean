import Mathlib

/-!
# A210196: coefficients of the polynomials v(n,x) jointly generated with A210195

Source: https://oeis.org/A210196
Credit: @ivillar

Clark Kimberling (Mar 18 2012) defines polynomials u(n,x) and v(n,x) for n ≥ 1 by
u(1,x) = 1, v(1,x) = 1 and, for n ≥ 2,
  u(n,x) = u(n-1,x) + v(n-1,x) + 1,
  v(n,x) = 2*x*u(n-1,x) + 2*x*v(n-1,x) + 1.
A210196 is the triangle T(n,k) (n ≥ 1, 0 ≤ k ≤ n-1) of the coefficients of x^k in v(n,x).

Conjecture (Knud Werner, Jan 10 2022): T(n,0) = 1 and T(n,k) = 2^(k+1)*binomial(n-1,k) if k > 0.

The polynomials have integer coefficients, so they are taken in ℤ[X]. The value at n = 0 is a
placeholder outside the OEIS range and is never used by the statement.
-/

namespace OMA.S_oeis_a210196

open Polynomial

mutual
/-- u(n,x) of A210195/A210196 (OEIS indexing from n = 1; the value at 0 is unused). -/
noncomputable def u : ℕ → ℤ[X]
  | 0 => 0
  | 1 => 1
  | n + 2 => u (n + 1) + v (n + 1) + 1
/-- v(n,x) of A210196 (OEIS indexing from n = 1; the value at 0 is unused). -/
noncomputable def v : ℕ → ℤ[X]
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * X * u (n + 1) + 2 * X * v (n + 1) + 1
end

/-- T(n,k): the coefficient of x^k in v(n,x). -/
noncomputable def T (n k : ℕ) : ℤ := (v n).coeff k

/-- Werner's conjecture, for every row n ≥ 1 and every column 0 ≤ k ≤ n-1 of the triangle. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    T n 0 = 1 ∧ ∀ k : ℕ, 0 < k → k ≤ n - 1 → T n k = 2 ^ (k + 1) * ((n - 1).choose k : ℤ) := by
  sorry

end OMA.S_oeis_a210196
