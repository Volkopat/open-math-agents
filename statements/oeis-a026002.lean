import Mathlib

/-!
# A026002: a(n) = T(n,n+2), where T = Delannoy triangle (A008288)

Source: https://oeis.org/A026002 (OEIS Foundation, CC BY-SA 4.0).
Credit: @mbilenko03

Offset `1`, data `1, 7, 41, 231, 1289, 7183, ...`: the `±2`-diagonal of the Delannoy numbers
`D(i, j)` (A008288 as a square array, `i, j ≥ 0`), i.e. `a(n) = D(n-1, n+1)`.
`D` is given by `D(i, 0) = D(0, j) = 1` and `D(i, j) = D(i-1, j) + D(i-1, j-1) + D(i, j-1)`.

Conjecture (J. M. Bergot, Apr 24 2013): define an infinite array to have
`m(n,1) = m(1,n) = n*(n-1)+1` in the first row and column, and
`m(i,j) = m(i,j-1) + m(i-1,j-1) + m(i-1,j)`; then `m(n,n) = a(n)`.
The array is indexed from `1` as in the source (`i, j ≥ 1`); `m` below is that array,
computed through the 0-indexed `mm i j = m(i+1, j+1)`.
-/

namespace OMA.S_oeis_a026002

/-- Delannoy numbers `D(i, j)` (A008288 as a square array). -/
def D : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _ + 1, 0 => 1
  | i + 1, j + 1 => D i (j + 1) + D i j + D (i + 1) j

/-- A026002 (offset 1): `a(n) = D(n-1, n+1)`. -/
def a (n : ℕ) : ℕ := D (n - 1) (n + 1)

/-- `mm i j = m(i+1, j+1)`: first row and column `n*(n-1)+1` (with `n = i+1` resp. `j+1`), and the
Delannoy-type recurrence inside. -/
def mm : ℕ → ℕ → ℕ
  | i, 0 => (i + 1) * i + 1
  | 0, j + 1 => (j + 2) * (j + 1) + 1
  | i + 1, j + 1 => mm (i + 1) j + mm i j + mm i (j + 1)

/-- Bergot's array `m(i, j)` for `i, j ≥ 1`. -/
def m (i j : ℕ) : ℕ := mm (i - 1) (j - 1)

/-- Conjecture (J. M. Bergot): `m(n,n) = a(n)` for every `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → m n n = a n := by
  sorry

end OMA.S_oeis_a026002
