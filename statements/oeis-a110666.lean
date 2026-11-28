import Mathlib

/-!
# A110666: Sequence is {a(1,n)}, where a(m,n) is defined at sequence A110665.

Source: https://oeis.org/A110666
Credit: @sntntHb

The array of A110665 (offset 0): `a(0,0) = 0`,
`a(0,n) = n - Sum_{k=0..n-1} binomial(2n-k-1, n-1) * a(0,k)`, `a(m,0) = 0` and
`a(m,n) = a(m-1,n) + a(m,n-1)`. This sequence is the row `m = 1`, so
`a(1,n) = a(0,n) + a(1,n-1)`; its terms are 0, 1, 1, -2, -6, -6, 0, 7, 7, -2, ...

R. J. Mathar (Oct 09 2013) conjectured the g.f. `x*(-1+2*x) / ((x-1)*(x^2-x+1)^2)` and
`a(n) = -A010892(n-1) + A165202(n) - 1`, where A010892 has g.f. `1/(1-x+x^2)` and
A165202 has g.f. `(1+x)/(1-x+x^2)^2` (both offset 0). The formula is stated for
`n ≥ 1`, where `A010892(n-1)` is defined. Both parts checked numerically for n < 40.
-/

namespace OMA.S_oeis_a110666

open PowerSeries

/-- Row `m = 0` of the array A110665. -/
def row0 : ℕ → ℤ
  | n => (n : ℤ) - ∑ k : Fin n, ((Nat.choose (2 * n - k - 1) (n - 1) : ℕ) : ℤ) * row0 k
decreasing_by exact k.2

/-- Row `m = 1` of the array A110665, i.e. A110666. -/
def a : ℕ → ℤ
  | 0 => 0
  | n + 1 => row0 (n + 1) + a n

theorem main : ∀ B C : PowerSeries ℤ,
    (1 - X + X ^ 2) * B = 1 → (1 - X + X ^ 2) ^ 2 * C = 1 + X →
    (X - 1) * (X ^ 2 - X + 1) ^ 2 * PowerSeries.mk a = X * (-1 + 2 * X) ∧
      ∀ n : ℕ, 1 ≤ n → a n = -coeff (n - 1) B + coeff n C - 1 := by
  sorry

end OMA.S_oeis_a110666
