import Mathlib

/-!
# A090260: Distinct numbers with a(n+1) || a(n) || a(n+1) prime

Source: https://oeis.org/A090260
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Beginning with 1, distinct positive numbers (chosen greedily to be least) such
that the concatenation a(n+1), a(n), a(n+1) is a prime.
Conjecture: all positive integers coprime to 10 occur in the sequence.
-/

namespace OMA.S_oeis_a090260

/-- Base-10 concatenation of two natural numbers. -/
def concat (x y : ℕ) : ℕ :=
  x * 10 ^ (Nat.digits 10 y).length + y

/-- 0-indexed version of A090260: a 0 = 1, and a (n + 1) is the least positive
integer not occurring in a 0, ..., a n such that concat(x, a n, x) is prime. -/
noncomputable def a : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
    sInf {x : ℕ | 0 < x ∧ (∀ i ≤ n, a i ≠ x) ∧ Nat.Prime (concat (concat x (a n)) x)}

theorem main :
    ∀ m : ℕ, 0 < m → Nat.Coprime m 10 → ∃ n : ℕ, a n = m := by
  sorry

end OMA.S_oeis_a090260
