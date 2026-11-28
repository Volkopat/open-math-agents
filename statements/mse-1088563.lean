import Mathlib

/-!
# p^(log_q n) is not an integer

Source: https://math.stackexchange.com/questions/1088563
Let `p, q` be distinct primes and `n > 1` an integer with `log_q n` irrational. Conjecture:
`p^(log_q n)` is not an integer.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mse_1088563

open Real

theorem main :
    ∀ p q n : ℕ, p.Prime → q.Prime → p ≠ q → 1 < n → Irrational (logb q n) →
      ¬ ∃ m : ℤ, (p : ℝ) ^ logb q n = m := by
  sorry

end OMA.S_mse_1088563
