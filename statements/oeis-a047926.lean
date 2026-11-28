import Mathlib

/-!
# A047926: a(n) = (3^(n+1) + 2*n + 1)/4

Source: https://oeis.org/A047926
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture:
a(n) = (3^(n+1) + 2*n + 1) / 4 equals the number of representations of 3^(2*(n+1)) as a sum
a^2 + b^2 + c^2 with 0 < a <= b <= c.

Conventions:
For n = 0, a(0) = 1 and 3^2 = 1^2 + 2^2 + 2^2 (1 representation).
For n = 1, a(1) = 3 and 3^4 = 1^2 + 4^2 + 8^2 = 3^2 + 6^2 + 6^2 = 4^2 + 4^2 + 7^2 (3 representations).
(The OEIS comment has a 1-based offset typo in its prose example, matching 3^(2*(n+1)) for 0-based n.)
-/

namespace OMA.S_oeis_a047926

/-- a(n) = (3^(n+1) + 2*n + 1) / 4. -/
def a (n : ℕ) : ℕ :=
  (3 ^ (n + 1) + 2 * n + 1) / 4

/-- Representations of m as x^2 + y^2 + z^2 with 0 < x <= y <= z. -/
def reps (m : ℕ) : Set (ℕ × ℕ × ℕ) :=
  {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧
    t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 = m}

/-- Conjecture: The number of positive ordered 3-square representations of 3^(2*(n+1)) is a(n). -/
theorem main : ∀ n : ℕ, (reps (3 ^ (2 * (n + 1)))).ncard = a n := by
  sorry

end OMA.S_oeis_a047926
