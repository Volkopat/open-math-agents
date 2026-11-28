import Mathlib

/-!
# A conjecture about an unlimited path of Gaussian-prime points

Source: https://math.stackexchange.com/questions/2390542
Conjecture (asker): for every prime of the form `a² + b²` there are natural numbers
`s, t, u, v` such that `s² + t²` and `u² + v²` are primes, `a + b = s + t`,
`u + v = s + t + 2` and `|s - u| + |t - v| = 2`.

Conventions. `a, b, s, t, u, v` are natural numbers; the absolute values are taken in `ℤ`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mse_2390542

theorem main :
    ∀ a b : ℕ, (a ^ 2 + b ^ 2).Prime →
      ∃ s t u v : ℕ, (s ^ 2 + t ^ 2).Prime ∧ (u ^ 2 + v ^ 2).Prime ∧ a + b = s + t ∧
        u + v = s + t + 2 ∧ |(s : ℤ) - u| + |(t : ℤ) - v| = 2 := by
  sorry

end OMA.S_mse_2390542
