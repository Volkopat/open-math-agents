import Mathlib

/-!
# A134016: Inverse score permutation of an Fibonacci -anti-Fibonacci zero sum game of 2 X 2 matrices.

Source: https://oeis.org/A134016
Credit: @agchua

Colin Barker (Nov 01 2012), in the formula section of A134016:
  Conjecture: a(n) = 4*a(n-2)+a(n-4). G.f.: x*(x^3-2*x^2-6*x-2)/(x^4+4*x^2-1).
  [_Colin Barker_, Nov 01 2012]
Definition, from the formula and Mathematica lines of the entry (offset 1):
  M = {{0, 1, 0, 0}, {1, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 3, 1}},
  p = {{0, 0, 0, 1}, {0, 0, 1, 0}, {0, 1, 0, 0}, {1, 0, 0, 0}},
  v[1] = {0, 1, 1, 0}, v[n] = p.M.v[n - 1], a(n) = Sum[v[n][[i]], {i, 1, 4}].
Here `v n` is the vector v[n], read as a column vector, so that p.M.v[n - 1] is
`p.mulVec (M.mulVec (v (n - 1)))`; the values are 2, 6, 10, 23, 42, 98, ... as listed.
The entry does not define v[0]; this file sets `v 0 = 0`, so `a 0 = 0`, which is the constant
coefficient 0 of the g.f. (its factor x, offset 1).
The recurrence is stated for n >= 5, where all its indices are at least the offset 1 (at n = 4 it
would use a(0)). The g.f. is stated as an identity of formal power series over ℚ:
(∑ a(n) X^n) * (X^4 + 4X^2 - 1) = X * (X^3 - 2X^2 - 6X - 2).
-/

namespace OMA.S_oeis_a134016

/-- The matrix M of the entry. -/
def M : Matrix (Fin 4) (Fin 4) ℤ := !![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 3, 1]

/-- The permutation matrix p of the entry. -/
def p : Matrix (Fin 4) (Fin 4) ℤ := !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]

/-- v[1] = (0, 1, 1, 0) and v[n] = p.M.v[n - 1] for n >= 2; `v 0 = 0` lies outside the offset. -/
def v : ℕ → Fin 4 → ℤ
  | 0 => 0
  | 1 => ![0, 1, 1, 0]
  | (n + 2) => p.mulVec (M.mulVec (v (n + 1)))

/-- A134016(n): the sum of the four entries of v[n]. -/
def a (n : ℕ) : ℤ := ∑ i, v n i

/-- Colin Barker's conjectures: a(n) = 4a(n-2) + a(n-4) for n >= 5, and the g.f.
x(x^3 - 2x^2 - 6x - 2)/(x^4 + 4x^2 - 1). -/
theorem main : (∀ n : ℕ, 5 ≤ n → a n = 4 * a (n - 2) + a (n - 4)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) * (PowerSeries.X ^ 4 + 4 * PowerSeries.X ^ 2 - 1) =
      PowerSeries.X * (PowerSeries.X ^ 3 - 2 * PowerSeries.X ^ 2 - 6 * PowerSeries.X - 2) := by
  sorry

end OMA.S_oeis_a134016
