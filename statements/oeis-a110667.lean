import Mathlib

/-!
# A110667: Sequence is {a(2,n)}, where a(m,n) is defined at sequence A110665.

Source: https://oeis.org/A110667
Credit: @thtsben2

The array of A110665 (offset 0): `a(0, 0) = 0`,
`a(0, n) = n - Sum_{k=0..n-1} binomial(2*n - k - 1, n - 1) * a(0, k)` for `n ≥ 1`,
`a(m, 0) = 0`, and `a(m, n) = a(m - 1, n) + a(m, n - 1)` for `m, n ≥ 1`.
This sequence is row `m = 2`: `0, 1, 2, 0, -6, -12, -12, -5, 2, 0, -12, ...`.

R. J. Mathar (Oct 09 2013) conjectured the g.f.
`-x * (-1 + 2 * x) / ((x - 1) ^ 2 * (x ^ 2 - x + 1) ^ 2)`.
-/

namespace OMA.S_oeis_a110667

open PowerSeries

/-- Row `m = 0` of the array A110665. -/
def row0 : ℕ → ℤ
  | n => (n : ℤ) - ∑ k : Fin n, ((Nat.choose (2 * n - k - 1) (n - 1) : ℕ) : ℤ) * row0 k
decreasing_by exact k.2

/-- Row `m = 1` of the array A110665. -/
def row1 : ℕ → ℤ
  | 0 => 0
  | n + 1 => row0 (n + 1) + row1 n

/-- Row `m = 2` of the array A110665, i.e. A110667. -/
def a : ℕ → ℤ
  | 0 => 0
  | n + 1 => row1 (n + 1) + a n

theorem main :
    (X - 1) ^ 2 * (X ^ 2 - X + 1) ^ 2 * PowerSeries.mk a = -X * (-1 + 2 * X) := by
  sorry

end OMA.S_oeis_a110667
