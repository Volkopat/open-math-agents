import Mathlib

/-!
# A089001: Numbers k such that 2*k^2 + 1 is prime

Source: https://oeis.org/A089001
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Numbers k such that 2*k^2 + 1 is prime.
Conjecture: these are the positive numbers that cannot be represented as d + t/d
where t is a triangular number (A000217) and d is a divisor of t.
-/

namespace OMA.S_oeis_a089001

theorem main :
    ∀ k : ℕ, 0 < k →
      (Nat.Prime (2 * k ^ 2 + 1) ↔
        ¬ ∃ n d : ℕ, 0 < n ∧ 0 < d ∧ d ∣ n * (n + 1) / 2 ∧
          k = d + (n * (n + 1) / 2) / d) := by
  sorry

end OMA.S_oeis_a089001
