import Mathlib

/-!
# A075343: a(1) = 1, a(n+1) is the smallest number such that there are n composite numbers between a(n) and a(n+1) exclusive.

Source: https://oeis.org/A075343
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: there exists a prime between consecutive terms.
-/

namespace OMA.S_oeis_a075343

/-- The sequence A075343 (1-indexed, with `a 0 = 0`). -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    sInf {m : ℕ | a (n + 1) < m ∧
      ((Finset.Ioo (a (n + 1)) m).filter (fun k => 1 < k ∧ ¬ Nat.Prime k)).card = n + 1}

/-- Conjecture: for every `n ≥ 1`, there is a prime strictly between `a(n)` and `a(n + 1)`. -/
theorem main :
    ∀ n : ℕ, 0 < n → ∃ p : ℕ, Nat.Prime p ∧ a n < p ∧ p < a (n + 1) := by sorry

end OMA.S_oeis_a075343
