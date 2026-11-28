import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OMA.S_oeis_a165462

/-- OEIS A165460: height at the 1/3 point of the Jacobi-bridge for `12n + 7`. -/
def a165460 (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (4 * n + 3), jacobiSym (i : ℤ) (12 * n + 7)

/-- OEIS A165601: midpoint height of the Jacobi-bridge for `4n + 3`. -/
def a165601 (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (2 * n + 2), jacobiSym (i : ℤ) (4 * n + 3)

/-- OEIS A165605: trisection `3n + 1` of A165601. -/
def a165605 (n : ℕ) : ℤ :=
  a165601 (3 * n + 1)

/-- Membership in OEIS A165462: `k = (m - 3) / 4` where `m = 12n + 7 ∈ A165463`
(i.e. `a165460 n = 0`), equivalently `k = 3n + 1` with `a165460 n = 0`. -/
def IsInA165462 (k : ℕ) : Prop :=
  ∃ n : ℕ, k = 3 * n + 1 ∧ a165460 n = 0

/-- Membership in OEIS A165602: positions `k` of zeros in A165601. -/
def IsInA165602 (k : ℕ) : Prop :=
  a165601 k = 0

/-- OEIS A165462 conjecture (Antti Karttunen, Oct 05 2009):
The terms of A165462 are precisely all those terms of A165602 which are `≡ 1 (mod 3)`,
and consequently the zeros of A165460 (A165461) coincide with the zeros of A165605. -/
theorem main :
    (∀ k : ℕ, IsInA165462 k ↔ IsInA165602 k ∧ k % 3 = 1) ∧
    (∀ n : ℕ, a165460 n = 0 ↔ a165605 n = 0) := by
  sorry

end OMA.S_oeis_a165462
