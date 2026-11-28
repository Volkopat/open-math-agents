import Mathlib

/-!
# A095237: a(1)=1; then for n even, a(n)=(sum of previous terms times n) plus 1, for n odd, a(n)=(sum of previous terms times n) minus 1.

Source: https://oeis.org/A095237
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: There are infinitely many primes in this sequence.
-/

namespace OMA.S_oeis_a095237

/-- `(a(n), sum_{k=1}^n a(k))` (1-indexed). -/
def state : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | 1 => (1, 1)
  | n + 2 =>
    let s := (state (n + 1)).2
    let val := if Even (n + 2) then s * (n + 2) + 1 else s * (n + 2) - 1
    (val, s + val)

/-- The `n`-th term of A095237 (1-indexed). -/
def a (n : ℕ) : ℕ :=
  (state n).1

theorem main :
    {n : ℕ | 1 ≤ n ∧ (a n).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a095237
