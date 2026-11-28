import Mathlib

/-!
# A073117: Eventual linearity of b(n+1) = b(n) + b(n) mod (n + a)

Source: https://oeis.org/A073117
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

a(n+1) = a(n) + a(n) mod n; a(1) = 1.
Conjecture: More generally let a and b(1) be integers. If b(n+1) = b(n) + b(n) mod (n+a),
there is an integer x(a, b(1)) such that b(n+1) = b(n) + x(a, b(1)) for n sufficiently large.
-/

namespace OMA.S_oeis_a073117

/-- Sequence `b(n)` starting at `b(1) = b1` with `b(n+1) = b(n) + b(n) mod (n + a)`. -/
def b (a b1 : ℤ) : ℕ → ℤ
  | 0 => b1
  | 1 => b1
  | n + 1 => b a b1 n + b a b1 n % ((n : ℤ) + a)

theorem main :
    ∀ a b1 : ℤ, 0 ≤ a → ∃ x : ℤ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → b a b1 (n + 1) = b a b1 n + x := by
  sorry

end OMA.S_oeis_a073117
