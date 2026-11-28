import Mathlib

/-!
# Infinitely many primes of the form n² + n + 1

Source: https://math.stackexchange.com/questions/2700254
Are there infinitely many positive integers `n` such that `n² + n + 1` is prime? (A case of
Bunyakovsky's conjecture.) `main` states the affirmative answer.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mse_2700254

theorem main : {n : ℕ | 0 < n ∧ (n ^ 2 + n + 1).Prime}.Infinite := by
  sorry

end OMA.S_mse_2700254
