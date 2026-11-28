import Mathlib

/-!
# A214615: a recurrence for the row sums of the Meixner polynomial triangle

Source: https://oeis.org/A214615
Credit: @sntntHb

`a(n)` (offset 0) is the sum of the coefficients of the Meixner polynomial `M_n(x)`, i.e. the
row sums of the triangle A060338 of coefficients of the Meixner polynomials. The entry records
the conjecture (R. J. Mathar)
  `a(n) - a(n-1) + (n-1)^2 * a(n-2) = 0`.

The Meixner polynomials are defined, as in A060338, by the recurrence
`M_(k+1) = x * M_k - k^2 * M_(k-1)` with `M_(-1) = 0`, `M_0 = 1` (so `M_1 = x`), here as
polynomials with integer coefficients. The sum of the coefficients of a polynomial is its value at
`x = 1`, so `a(n) = M_n(1)`. With this definition the first terms are
`1, 1, 0, -4, -4, 60, 160, -2000, ...`, matching the OEIS data. The recurrence is stated for
`n ≥ 2`, where all indices are in range.
-/

namespace OMA.S_oeis_a214615

open Polynomial

/-- The Meixner polynomials: `M 0 = 1`, `M 1 = X`, `M (k+2) = X * M (k+1) - (k+1)^2 * M k`. -/
noncomputable def meixner : ℕ → ℤ[X]
  | 0 => 1
  | 1 => X
  | (k + 2) => X * meixner (k + 1) - C (((k : ℤ) + 1) ^ 2) * meixner k

/-- `a n`: the sum of the coefficients of `M_n`, i.e. its value at `1` (OEIS A214615). -/
noncomputable def a (n : ℕ) : ℤ := (meixner n).eval 1

/-- Mathar's conjecture in OEIS A214615: `a(n) - a(n-1) + (n-1)^2 a(n-2) = 0` for `n ≥ 2`. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    a n - a (n - 1) + ((n : ℤ) - 1) ^ 2 * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a214615
