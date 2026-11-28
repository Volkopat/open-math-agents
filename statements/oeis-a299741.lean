import Mathlib

/-!
# A299741: Array a(i,0) = 2, a(i,1) = i+2, a(i,j) = (i+2) * a(i,j-1) - a(i,j-2)

Source: https://oeis.org/A299741
Credit: @xor2k

Formalizes the OEIS A299741 conjecture. The entry defines polynomials recursively by
p[0](n) = 2, p[1](n) = n + 2, p[j](n) = p[j-1](n) * p[1](n) - p[j-2](n) for j > 1, n >= 0,
and conjectures: a(i,j) = p[j](i), i,j >= 0.

Conventions: the array (read by antidiagonals upwards in OEIS, offset 0) is the two-argument
function `a i j` for `i j : ℕ`, with integer values. The polynomials `p j` are Mathlib polynomials
`Polynomial ℤ` in one variable, and `p[j](i)` is `Polynomial.eval (i : ℤ) (p j)`.
-/

namespace OMA.S_oeis_a299741

open Polynomial

/-- Row `i` of the array: `a(i,0) = 2`, `a(i,1) = i+2`, `a(i,j) = (i+2) a(i,j-1) - a(i,j-2)`. -/
def a (i : ℕ) : ℕ → ℤ
  | 0 => 2
  | 1 => (i : ℤ) + 2
  | j + 2 => ((i : ℤ) + 2) * a i (j + 1) - a i j

/-- `p[0] = 2`, `p[1] = X + 2`, `p[j] = p[j-1] * p[1] - p[j-2]`. -/
noncomputable def p : ℕ → ℤ[X]
  | 0 => C 2
  | 1 => X + C 2
  | j + 2 => p (j + 1) * (X + C 2) - p j

/-- `a(i,j) = p[j](i)` for all `i, j ≥ 0`. -/
theorem main :
    ∀ i j : ℕ, a i j = (p j).eval (i : ℤ) := by
  sorry

end OMA.S_oeis_a299741
