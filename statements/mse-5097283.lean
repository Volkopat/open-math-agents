import Mathlib

/-!
# Remainders of 3^(n+1) modulo 2^n

Source: https://math.stackexchange.com/questions/5097283
Conjecture (asker, checked for `n < 10^5`): the only `n ≥ 1` with
`(3^(n+1) mod 2^n) > 2^n - 1.5^n` are `n = 1, 2, 5, 10`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mse_5097283

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (((3 ^ (n + 1) % 2 ^ n : ℕ) : ℝ) > 2 ^ n - (3 / 2 : ℝ) ^ n ↔
        n = 1 ∨ n = 2 ∨ n = 5 ∨ n = 10) := by
  sorry

end OMA.S_mse_5097283
