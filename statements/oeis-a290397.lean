import Mathlib

/-!
# A290397: Least number of nonprime squarefree numbers (A000469) that add up to n

Source: https://oeis.org/A290397

Conjecture (OEIS A290397):
Every positive integer `n` is the sum of at most `5` nonprime squarefree positive
integers (elements of OEIS A000469: `1, 6, 10, 14, 15, 21, 22, 26, ...`).

Conventions:
- Offset: `1`; `n = 5` requires `5` terms (`1 + 1 + 1 + 1 + 1`).
- Elements of A000469 are positive integers `x` that are `Squarefree` and not `Nat.Prime`.
-/

namespace OMA.S_oeis_a290397

/-- Predicate for membership in OEIS A000469 (nonprime squarefree positive integers). -/
def IsA000469 (x : ℕ) : Prop :=
  1 ≤ x ∧ Squarefree x ∧ ¬ Nat.Prime x

/-- Conjecture: every `n ≥ 1` is the sum of at most `5` elements of A000469. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      ∃ l : List ℕ, l.length ≤ 5 ∧ (∀ x ∈ l, IsA000469 x) ∧ l.sum = n := by
  sorry

end OMA.S_oeis_a290397
