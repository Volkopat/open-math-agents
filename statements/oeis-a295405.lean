import Mathlib

/-!
# A295405: Characteristic function of n such that n^2 + 1 is prime

Source: https://oeis.org/A295405

Conjecture (Landau's fourth problem / OEIS A295405):
There are infinitely many natural numbers `n` such that `n^2 + 1` is prime
(equivalently, `a(n) = 1` infinitely often).

Conventions:
- Offset: `0`; `a(n) = 1` for `n = 1, 2, 4, 6, 10, 14, 16, 20, 24, 26, ...`, `0` otherwise.
-/

namespace OMA.S_oeis_a295405

/-- Characteristic function `a(n) = 1` if `n^2 + 1` is prime, `0` otherwise (OEIS A295405). -/
def a (n : ℕ) : ℕ :=
  if Nat.Prime (n ^ 2 + 1) then 1 else 0

/-- Conjecture: `a(n) = 1` (i.e., `n^2 + 1` is prime) for infinitely many `n`. -/
theorem main : Set.Infinite {n : ℕ | a n = 1} := by
  sorry

end OMA.S_oeis_a295405
