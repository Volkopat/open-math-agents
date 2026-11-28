import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OMA.S_oeis_a165463

/-- OEIS A165460: height at the 1/3 point of the Jacobi-bridge for `12n + 7`. -/
def a165460 (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (4 * n + 3), jacobiSym (i : ℤ) (12 * n + 7)

/-- OEIS A165601: midpoint height of the Jacobi-bridge for `4n + 3`. -/
def a165601 (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (2 * n + 2), jacobiSym (i : ℤ) (4 * n + 3)

/-- Membership in OEIS A165463: numbers of the form `12n + 7` for which `a165460 n = 0`. -/
def IsInA165463 (m : ℕ) : Prop :=
  ∃ n : ℕ, m = 12 * n + 7 ∧ a165460 n = 0

/-- Membership in OEIS A165603: numbers of the form `4k + 3` for which `a165601 k = 0`. -/
def IsInA165603 (m : ℕ) : Prop :=
  ∃ k : ℕ, m = 4 * k + 3 ∧ a165601 k = 0

/-- OEIS A165463 conjecture (Antti Karttunen, Oct 05 2009):
A165463 is a subset of A165603, and in fact consists of precisely those terms of A165603
congruent to `7 (mod 12)`. -/
theorem main :
    (∀ m : ℕ, IsInA165463 m → IsInA165603 m) ∧
    (∀ m : ℕ, IsInA165463 m ↔ IsInA165603 m ∧ m % 12 = 7) := by
  sorry

end OMA.S_oeis_a165463
