import Mathlib

/-!
# A089610: Number of primes between n^2 and (n + 1/2)^2

Source: https://oeis.org/A089610
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Number of primes between n^2 and (n + 1/2)^2 (equivalently, in (n^2, n^2 + n]).
Conjectures:
1. For all n > 17, a(n) > 1.
2. There exists n1 such that a(n) < a(n + 1) for all n >= n1.
3. (Oppermann, 1882) For all n >= 1, a(n) > 0.
-/

namespace OMA.S_oeis_a089610

/-- Number of primes in (n^2, n^2 + n], i.e., between n^2 and (n + 1/2)^2. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Ioc (n ^ 2) (n ^ 2 + n)).filter Nat.Prime).card

theorem main :
    (∀ n : ℕ, 17 < n → 1 < a n) ∧
    (∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n → a n < a (n + 1)) ∧
    (∀ n : ℕ, 0 < n → 0 < a n) := by
  sorry

end OMA.S_oeis_a089610
