import Mathlib

/-!
# Three proposed formulas for the gcd recurrence (OEIS A355898)

Source: https://oeis.org/A355898 (OEIS Foundation, CC BY-SA 4.0).
Giorgos Kalogeropoulos proposed the three formulas on November 1, 2022.
The sequence convention starts at index 1. Subtractions in the formulas
are in the integers.

Tom Adamczewski reports a disproof in *OEIS Open*, Appendix A
(https://arxiv.org/abs/2608.11941).
-/

namespace OMA.S_oeis_a355898

/-- The sequence step from two consecutive terms. -/
def nextTerm (x y : ℕ) : ℕ :=
  let g := Nat.gcd x y
  g + (x + y) / g

/-- `state n` holds the terms at indices `n + 1` and `n + 2`. -/
def state : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | n + 1 =>
    let pair := state n
    (pair.2, nextTerm pair.1 pair.2)

/-- OEIS A355898 at positive indices. The auxiliary value at zero is unused. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (state n).1

/-- The Fibonacci expression in the third proposed formula. -/
def fibFormula (n : ℕ) : ℤ :=
  ((a 3774 : ℤ) + 1) * Nat.fib (n - 3772) -
    ((a 3772 : ℤ) + 1) * Nat.fib (n - 3774) - 1

theorem main : ∀ n : ℕ, 3775 ≤ n →
    a n = 1 + a (n - 1) + a (n - 2) ∧
      (a n : ℤ) = 2 * (a (n - 1) : ℤ) - a (n - 3) ∧
      (a n : ℤ) = fibFormula n := by
  sorry

end OMA.S_oeis_a355898
