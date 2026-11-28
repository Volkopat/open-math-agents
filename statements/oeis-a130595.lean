import Mathlib

/-!
# A130595: inverse of Pascal's triangle, recurrence of Dale Gerdemann

Source: https://oeis.org/A130595 (conjecture by Dale Gerdemann, Nov 28 2015)

A130595 is the lower triangular matrix inverse to Pascal's triangle A007318.
We realise it by truncation: for each `n`, invert the `(n+1) x (n+1)` matrix
of binomial coefficients `C(i, j)` with `0 <= i, j <= n` over the rationals, and let
`T n k` be its `(n, k)` entry for `k <= n` (and `0` for `k > n`).
Since Pascal's matrix is unitriangular, the inverse of every truncation is the
truncation of the infinite inverse, so this is the OEIS triangle.

Conjecture: `T(n, k) = (n - k + 1) * T(n - 1, k - 1) + (k - 1) * T(n - 1, k)`.
It is stated for `1 <= k <= n` (so that all indices are nonnegative);
`T(n - 1, n) = 0` lies outside the triangle.
-/

namespace OMA.S_oeis_a130595

/-- Pascal's triangle truncated to rows and columns `0..N`, as a lower triangular matrix. -/
def pascal (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ :=
  fun i j => (Nat.choose i j : ℚ)

/-- `T n k` is the `(n, k)` entry of the inverse of Pascal's triangle (rows/columns `0..n`). -/
noncomputable def T (n k : ℕ) : ℚ :=
  if h : k ≤ n then (pascal n)⁻¹ ⟨n, Nat.lt_succ_self n⟩ ⟨k, Nat.lt_succ_of_le h⟩ else 0

theorem main : ∀ n k : ℕ, 1 ≤ k → k ≤ n →
    T n k = ((n : ℚ) - k + 1) * T (n - 1) (k - 1) + ((k : ℚ) - 1) * T (n - 1) k := by
  sorry

end OMA.S_oeis_a130595
