import Mathlib

/-!
# A088648: Greedy odd sequence with composite pairwise concatenations

Source: https://oeis.org/A088648
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

a(1) = 1, then the smallest odd number not occurring earlier such that the
concatenation a(r), a(s) is composite for all s > r.
The sequence is infinite with trivial terms of the form 10k+5.
Subsidiary sequence: sequence of nontrivial terms.
Conjecture: the subsidiary sequence is infinite.
-/

namespace OMA.S_oeis_a088648

/-- Base-10 concatenation of two natural numbers. -/
def concat (x y : ℕ) : ℕ :=
  x * 10 ^ (Nat.digits 10 y).length + y

/-- 0-indexed version of A088648: a 0 = 1, and a (n + 1) is the smallest odd
natural number not among a 0, ..., a n such that concat (a r) (a (n + 1)) is
composite for every r ≤ n. -/
noncomputable def a : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
    sInf {x : ℕ |
      x % 2 = 1 ∧
      (∀ r ≤ n, a r ≠ x) ∧
      (∀ r ≤ n, ¬ Nat.Prime (concat (a r) x))}

theorem main :
    Set.Infinite {n : ℕ | a n % 10 ≠ 5} := by
  sorry

end OMA.S_oeis_a088648
