import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OMA.S_oeis_a165461

/-- OEIS A165460: height at the 1/3 point of the Jacobi-bridge for `12n + 7`. -/
def a165460 (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (4 * n + 3), jacobiSym (i : ℤ) (12 * n + 7)

/-- OEIS A165601: midpoint height of the Jacobi-bridge for `4n + 3`. -/
def a165601 (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (2 * n + 2), jacobiSym (i : ℤ) (4 * n + 3)

/-- OEIS A165605: trisection `3n + 1` of A165601. -/
def a165605 (n : ℕ) : ℤ :=
  a165601 (3 * n + 1)

/-- OEIS A165461 conjecture (Antti Karttunen, Oct 05 2009):
The positions of zeros in A165460 (A165461) are also the positions of zeros in A165605. -/
theorem main :
    ∀ n : ℕ, a165460 n = 0 ↔ a165605 n = 0 := by
  sorry

end OMA.S_oeis_a165461
