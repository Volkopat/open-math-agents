import Mathlib

/-!
# A146955: row sums of a functionally symmetric polynomial triangle

Source: https://oeis.org/A146955
Credit: @sntntHb

Row `n` of the triangle lists the coefficients of the polynomial
`p(x, n) = (x + 1)^n + 2^(n-4) * Sum_{m=1..n-1} (2^m + 2*m) * x^m * (1 + x^(n-2*m))` for `n ≥ 1`,
with `p(x, 0) = 1`. The entry records a conjecture of R. J. Mathar (Nov 30 2008):
the row sums are `2^n * (2^n + 6 - n + n^2) / 8` for `n > 0`.

The polynomial is built in `ℚ[X]` (the factor `2^(n-4)` is a rational number for `n < 4`); the
exponent `n-2*m` may be negative, so we multiply out `x^m * (1 + x^(n-2*m)) = x^m + x^(n-m)`,
which is a polynomial since `1 ≤ m ≤ n-1`. `p n` has degree `n`, and the row sum is the sum of
its coefficients of degree `0, ..., n`. This gives rows `1`, `1, 1`, `1, 4, 1`,
`1, 9, 9, 1`, `1, 22, 22, 22, 1`, ... as listed, with row sums `1, 2, 6, 20, 68, 232, ...`.

`main` states the conjecture for every `n ≥ 1`.
-/

namespace OMA.S_oeis_a146955

open Polynomial

/-- The polynomial `p(x, n)` of OEIS A146955, with `x^m * (1 + x^(n-2m)) = x^m + x^(n-m)`. -/
noncomputable def p (n : ℕ) : ℚ[X] :=
  if n = 0 then 1 else
    (X + 1) ^ n + C ((2 : ℚ) ^ ((n : ℤ) - 4)) *
      ∑ m ∈ Finset.Icc 1 (n - 1), C ((2 : ℚ) ^ m + 2 * m) * (X ^ m + X ^ (n - m))

/-- The `n`-th row sum of the triangle: the sum of the coefficients of `p(x, n)`. -/
noncomputable def rowSum (n : ℕ) : ℚ := ∑ i ∈ Finset.range (n + 1), (p n).coeff i

/-- Mathar's conjecture for the row sums of OEIS A146955. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    rowSum n = (2 : ℚ) ^ n * ((2 : ℚ) ^ n + 6 - n + (n : ℚ) ^ 2) / 8 := by
  sorry

end OMA.S_oeis_a146955
