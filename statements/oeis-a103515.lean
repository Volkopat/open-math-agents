import Mathlib

/-!
# OEIS A103515: primes of the form p_k# · 2^n - 1

Source: https://oeis.org/A103515
Primes of the form `P(k) · 2^n - 1` with minimal `n ≥ 0`, where `P(k)` is the `k`-th primorial
(product of the first `k` primes), `k ≥ 2`. Conjecture: the sequence is defined for all `k ≥ 2`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a103515

theorem main :
    ∀ k : ℕ, 2 ≤ k → ∃ n : ℕ, (primorial (Nat.nth Nat.Prime (k - 1)) * 2 ^ n - 1).Prime := by
  sorry

end OMA.S_oeis_a103515
