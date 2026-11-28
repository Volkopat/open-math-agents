import Mathlib

/-!
# A prime criterion with Fibonacci numbers

Source: https://math.stackexchange.com/questions/4756846
Conjecture (asker): for `m ≥ 1`, `2m + 1` is prime iff there is `n > 1` such that
`(F_n^(2m+1) + F_(n+1)^(2m+1)) / (F_n + F_(n+1))` is prime. (The asker proves the direction
"composite ⇒ always composite".)

Conventions. `F_n = Nat.fib n`. The division is exact since `a + b ∣ a^k + b^k` for odd `k`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mse_4756846

theorem main :
    ∀ m : ℕ, 1 ≤ m →
      ((2 * m + 1).Prime ↔
        ∃ n : ℕ, 1 < n ∧
          ((Nat.fib n ^ (2 * m + 1) + Nat.fib (n + 1) ^ (2 * m + 1)) /
            (Nat.fib n + Nat.fib (n + 1))).Prime) := by
  sorry

end OMA.S_mse_4756846
