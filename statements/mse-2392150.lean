import Mathlib

/-!
# Odd numbers a + b with a² + b² and a² + (b+2)² prime

Source: https://math.stackexchange.com/questions/2392150
Conjecture (asker): for every odd `n > 159` there are positive integers `a ≤ b` with
`n = a + b` such that `a² + b²` and `a² + (b + 2)²` are both prime.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mse_2392150

theorem main :
    ∀ n : ℕ, Odd n → 159 < n →
      ∃ a b : ℕ, 0 < a ∧ a ≤ b ∧ n = a + b ∧ (a ^ 2 + b ^ 2).Prime ∧
        (a ^ 2 + (b + 2) ^ 2).Prime := by
  sorry

end OMA.S_mse_2392150
