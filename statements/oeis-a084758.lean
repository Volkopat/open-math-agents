import Mathlib

/-!
A084758: The slowest increasing sequence of primes such that difference of successive terms is unique.

Source: https://oeis.org/A084758
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

The sequence of successive differences is 1,2,6,8,4,14,10,12,20,18,16,...
Conjecture: every even number is a term of this sequence. For every even number e
there exists some k such that a(k) - a(k-1) = e.
-/

namespace OMA.S_oeis_a084758

noncomputable def a : ℕ → ℕ
  | 0 => 2
  | n + 1 =>
    sInf {p : ℕ | p.Prime ∧ a n < p ∧ ∀ i < n, p - a n ≠ a (i + 1) - a i}

theorem main : ∀ e : ℕ, 0 < e → Even e → ∃ k : ℕ, 1 ≤ k ∧ a k - a (k - 1) = e := by
  sorry

end OMA.S_oeis_a084758
