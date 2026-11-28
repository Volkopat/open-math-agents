import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OMA.S_oeis_a166271

/-- OEIS A166050: height at the 1/6 point of the Jacobi-bridge for `12n + 7`. -/
def a166050 (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (2 * n + 2), jacobiSym (i : ℤ) (12 * n + 7)

/-- OEIS A165460: height at the 1/3 point of the Jacobi-bridge for `12n + 7`. -/
def a165460 (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (4 * n + 3), jacobiSym (i : ℤ) (12 * n + 7)

/-- OEIS A166269: bisection `2n + 1` of A166050. -/
def a166269 (n : ℕ) : ℤ :=
  a166050 (2 * n + 1)

/-- OEIS A166271: bisection `2n + 1` of A165460. -/
def a166271 (n : ℕ) : ℤ :=
  a165460 (2 * n + 1)

/-- OEIS A166271 conjecture: `a(n) = -2 * A166269(n)`. -/
theorem main :
    ∀ n : ℕ, a166271 n = -2 * a166269 n := by
  sorry

end OMA.S_oeis_a166271
