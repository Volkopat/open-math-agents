import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OMA.S_oeis_a166273

/-- OEIS A166050: height at the 1/6 point of the Jacobi-bridge for `12n + 7`. -/
def a166050 (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (2 * n + 2), jacobiSym (i : ℤ) (12 * n + 7)

/-- OEIS A165601: midpoint height of the Jacobi-bridge for `4n + 3`. -/
def a165601 (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (2 * n + 2), jacobiSym (i : ℤ) (4 * n + 3)

/-- OEIS A165605: trisection `3n + 1` of A165601. -/
def a165605 (n : ℕ) : ℤ :=
  a165601 (3 * n + 1)

/-- OEIS A166269: bisection `2n + 1` of A166050. -/
def a166269 (n : ℕ) : ℤ :=
  a166050 (2 * n + 1)

/-- OEIS A166273: bisection `2n + 1` of A165605. -/
def a166273 (n : ℕ) : ℤ :=
  a165605 (2 * n + 1)

/-- OEIS A166273 conjecture: `a(n) = -3 * A166269(n)`. -/
theorem main :
    ∀ n : ℕ, a166273 n = -3 * a166269 n := by
  sorry

end OMA.S_oeis_a166273
