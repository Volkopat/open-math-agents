import Mathlib

/-!
# A059297: Triangle of idempotent numbers binomial(n,k)*k^(n-k), version 1.

Source: https://oeis.org/A059297
Credit: @prasledi

Conjecture (R. J. Mathar, Mar 12 2013, in the COMMENTS of A059297): "the matrix inverse is
A137452."

Formalization notes:
* A059297 is the triangle `T(n, k) = binomial(n, k) * k^(n - k)`, `0 ≤ k ≤ n` (offset 0, so
  `T(0, 0) = 1` with the convention `0^0 = 1`, and `T(n, 0) = 0` for `n > 0`, as in the data
  1; 0, 1; 0, 2, 1; ...). For `k > n` the binomial coefficient vanishes, so the formula gives the
  zero entries above the diagonal of the lower-triangular matrix.
* A137452 is the "triangular array of the coefficients of the sequence of Abel polynomials
  `A(n, x) := x * (x - n)^(n - 1)`": row `n` lists the coefficients of `x^0, ..., x^n`. For
  `n = 0` the polynomial is `x * x^(-1) = 1` (the OEIS data starts with the row `1`); this case is
  written out separately, since `n - 1` is truncated subtraction in Lean. Coefficients beyond the
  degree `n` are zero, again giving the upper part of a lower-triangular matrix.
* Both triangles are infinite lower-triangular integer matrices. Their product is computed by
  finite sums, and two such matrices are inverse to each other exactly when every leading
  principal `N × N` block of one is the inverse of the corresponding block of the other. The
  statement asserts this for every `N`, on both sides.
-/

namespace OMA.S_oeis_a059297

open Polynomial

/-- A059297: `T(n, k) = binomial(n, k) * k^(n - k)`. -/
def A059297 (n k : ℕ) : ℤ := (n.choose k : ℤ) * (k : ℤ) ^ (n - k)

/-- A137452: the coefficient of `x^k` in the Abel polynomial `x * (x - n)^(n - 1)`
(which is `1` for `n = 0`). -/
noncomputable def A137452 (n k : ℕ) : ℤ :=
  if n = 0 then (if k = 0 then 1 else 0) else (X * (X - C (n : ℤ)) ^ (n - 1)).coeff k

/-- The leading principal `N × N` block of an integer triangle. -/
def block (T : ℕ → ℕ → ℤ) (N : ℕ) : Matrix (Fin N) (Fin N) ℤ :=
  Matrix.of fun i j => T i j

/-- Mathar's conjecture: the matrix inverse of A059297 is A137452. -/
theorem main :
    ∀ N : ℕ, block A059297 N * block A137452 N = 1 ∧ block A137452 N * block A059297 N = 1 := by
  sorry

end OMA.S_oeis_a059297
