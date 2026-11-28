import Mathlib

/-!
# Infinitely many primes of the form `p + q + 1`?

Source: https://math.stackexchange.com/questions/5042058
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question: are there infinitely many primes of the form `p + q + 1` with `p, q` (not necessarily
distinct) primes? `main` states the answer yes.

Conventions:
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer
  no.
-/

namespace OMA.S_mse_5042058

/-- Infinitely many primes are `p + q + 1` with `p, q` prime. -/
theorem main : {r : ℕ | r.Prime ∧ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ r = p + q + 1}.Infinite := by
  sorry

end OMA.S_mse_5042058
