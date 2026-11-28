import Mathlib

/-!
# A354672: Numbers x with property that x is not the smallest possible value in the Pellian equation x^2 - D*y^2 = 1 with D = squarefree part of (x^2 - 1).

Source: https://oeis.org/A354672
Credit: @agchua

Comment of A354672 (by Jennifer Buckley, Apr 23 2024):
  Conjecture: this sequence is equivalent to the sorted distinct values of cos(m*arccos(k)),
  where m and k are integers greater than 1.

Offset 1, a(1) = 7. The terms are the numbers x >= 2 such that the Pell equation
X^2 - D*Y^2 = 1, where D is the squarefree part of x^2 - 1, has a solution with 1 < X < x.
Since x itself solves this equation (x^2 - 1 = D*s^2), this says that x is not the smallest
nontrivial solution. The squarefree part of x^2 - 1 is the unique squarefree D with
x^2 - 1 = D*s^2 for some natural number s, so it is written as an existential over such D.
For integers k > 1 the value cos(m*arccos(k)) is read through the identity
cos(m*t) = T_m(cos t) (see `Polynomial.Chebyshev.T_complex_cos`), that is, as the value T_m(k)
of the Chebyshev polynomial of the first kind. Both lists are increasing lists of distinct
numbers, so the conjecture says that the two sets of numbers are equal.
-/

namespace OMA.S_oeis_a354672

/-- `x` is a term of A354672: `x >= 2`, and for the squarefree part `D` of `x^2 - 1` the Pell
equation `X^2 - D*Y^2 = 1` has a solution with `1 < X < x`. -/
def IsTerm (x : ℕ) : Prop :=
  2 ≤ x ∧ ∃ D s : ℕ, Squarefree D ∧ x ^ 2 - 1 = D * s ^ 2 ∧
    ∃ X Y : ℕ, 1 < X ∧ X < x ∧ X ^ 2 = D * Y ^ 2 + 1

/-- The conjecture: `x` is a term if and only if `x = T_m(k)` for some integers `m, k >= 2`,
where `T_m` is the Chebyshev polynomial of the first kind, `T_m(cos t) = cos(m*t)`. -/
theorem main : ∀ x : ℕ, IsTerm x ↔
    ∃ m k : ℕ, 2 ≤ m ∧ 2 ≤ k ∧ (x : ℤ) = (Polynomial.Chebyshev.T ℤ m).eval (k : ℤ) := by
  sorry

end OMA.S_oeis_a354672
