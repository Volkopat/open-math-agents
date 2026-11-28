import Mathlib

/-!
# OEIS A063656: a greedy definition produces the sequence

Source: https://oeis.org/A063656 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry, offset 0: Numbers k such that the truncated square root of k is equal to the rounded
square root of k. Data: 0, 1, 2, 4, 5, 6, 9, 10, 11, 12, 16, ...
Comment (J. Lowell, May 13 2014): Conjecture: the following definition produces a(n) for
n >= 1: a(1) = 1; for n > 1, smallest number > a(n-1) satisfying the condition that a(n) is a
square if and only if n is a triangular number.

Formalization notes:
* The truncated square root of k is `Nat.sqrt k` (the floor of the real square root); the
  rounded square root is `round (Real.sqrt k)`, the nearest integer (no ties occur, since
  (s + 1/2)^2 is never an integer).
* a(n) is the n-th term in increasing order, `Nat.nth IsTerm n`, counted from 0 as the offset
  says (a(0) = 0, a(1) = 1).
* Triangular numbers are t(t+1)/2 for t >= 0.
* The recursive definition determines a unique sequence on n >= 1, so it produces a(n) exactly
  when a itself satisfies it: a(1) = 1, and for every n >= 2, a(n) > a(n-1), a(n) is a square
  iff n is triangular, and no number strictly between a(n-1) and a(n) has that property. This is
  `main`.
* Controls proved in the proof file: a(0) = 0, a(3) = 4, a(6) = 9.
-/

namespace OMA.S_oeis_a063656

/-- k is a term: the truncated square root of k equals the rounded square root of k. -/
def IsTerm (k : ℕ) : Prop := round (Real.sqrt k) = (Nat.sqrt k : ℤ)

/-- A063656(n), offset 0: the n-th term in increasing order. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm n

/-- n is a triangular number. -/
def IsTri (n : ℕ) : Prop := ∃ t, n = t * (t + 1) / 2

/-- Lowell's conjecture: a(1) = 1 and, for n > 1, a(n) is the smallest number > a(n-1) that is
a square if and only if n is triangular. -/
theorem main : a 1 = 1 ∧ ∀ n, 2 ≤ n →
    a (n - 1) < a n ∧ (IsSquare (a n) ↔ IsTri n) ∧
      ∀ m, a (n - 1) < m → m < a n → ¬ (IsSquare m ↔ IsTri n) := by
  sorry

end OMA.S_oeis_a063656
